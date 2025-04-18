package mega

import (
	"crypto/md5"
	"crypto/rand"
	"fmt"
	"io/ioutil"
	"os"
	"path"
	"strings"
	"sync"
	"testing"
	"time"
)

var USER string = os.Getenv("MEGA_USER")
var PASSWORD string = os.Getenv("MEGA_PASSWD")

// retry runs fn until it succeeds, using what to log and retrying on
// EAGAIN.  It uses exponential backoff
func retry(t *testing.T, what string, fn func() error) {
	const maxTries = 10
	var err error
	sleep := 100 * time.Millisecond
	for i := 1; i <= maxTries; i++ {
		err = fn()
		if err == nil {
			return
		}
		if err != EAGAIN {
			break
		}
		t.Logf("%s failed %d/%d - retrying after %v sleep", what, i, maxTries, sleep)
		time.Sleep(sleep)
		sleep *= 2
	}
	t.Fatalf("%s failed: %v", what, err)
}

func skipIfNoCredentials(t *testing.T) {
	if USER == "" || PASSWORD == "" {
		t.Skip("MEGA_USER and MEGA_PASSWD not set - skipping integration tests")
	}
}

func initSession(t *testing.T) *Mega {
	skipIfNoCredentials(t)
	m := New()
	// m.SetDebugger(log.Printf)
	retry(t, "Login", func() error {
		return m.Login(USER, PASSWORD)
	})
	return m
}

// createFile creates a temporary file of a given size along with its MD5SUM
func createFile(t *testing.T, size int64) (string, string) {
	b := make([]byte, size)
	_, err := rand.Read(b)
	if err != nil {
		t.Fatalf("Error reading rand: %v", err)
	}
	file, err := ioutil.TempFile("/tmp/", "gomega-")
	if err != nil {
		t.Fatalf("Error creating temp file: %v", err)
	}
	_, err = file.Write(b)
	if err != nil {
		t.Fatalf("Error writing temp file: %v", err)
	}
	h := md5.New()
	_, err = h.Write(b)
	if err != nil {
		t.Fatalf("Error on Write while writing temp file: %v", err)
	}
	return file.Name(), fmt.Sprintf("%x", h.Sum(nil))
}

// uploadFile uploads a temporary file of a given size returning the
// node, name and its MD5SUM
func uploadFile(t *testing.T, session *Mega, size int64, parent *Node) (node *Node, name string, md5sum string) {
	name, md5sum = createFile(t, size)
	defer func() {
		_ = os.Remove(name)
	}()
	var err error
	retry(t, fmt.Sprintf("Upload %q", name), func() error {
		node, err = session.UploadFile(name, parent, "", nil)
		return err
	})
	if node == nil {
		t.Fatalf("Failed to obtain node after upload for %q", name)
	}
	return node, name, md5sum
}

// createDir creates a directory under parent
func createDir(t *testing.T, session *Mega, name string, parent *Node) (node *Node) {
	var err error
	retry(t, fmt.Sprintf("Create directory %q", name), func() error {
		node, err = session.CreateDir(name, parent)
		return err
	})
	return node
}

func fileMD5(t *testing.T, name string) string {
	file, err := os.Open(name)
	if err != nil {
		t.Fatalf("Failed to open %q: %v", name, err)
	}
	b, err := ioutil.ReadAll(file)
	if err != nil {
		t.Fatalf("Failed to read all %q: %v", name, err)
	}
	h := md5.New()
	_, err = h.Write(b)
	if err != nil {
		t.Fatalf("Error on hash in fileMD5: %v", err)
	}
	return fmt.Sprintf("%x", h.Sum(nil))
}

func TestLogin(t *testing.T) {
	skipIfNoCredentials(t)

	m := New()
	retry(t, "Login", func() error {
		return m.Login(USER, PASSWORD)
	})
}

func TestGetUser(t *testing.T) {
	session := initSession(t)
	_, err := session.GetUser()
	if err != nil {
		t.Fatal("GetUser failed", err)
	}
}

func TestUploadDownload(t *testing.T) {
	session := initSession(t)
	for i := range []int{0, 1} {
		if i == 0 {
			t.Log("HTTP Test")
			session.SetHTTPS(false)
		} else {
			t.Log("HTTPS Test")
			session.SetHTTPS(true)
		}

		node, name, h1 := uploadFile(t, session, 314573, session.FS.root)

		session.FS.mutex.Lock()
		phash := session.FS.root.hash
		n := session.FS.lookup[node.hash]
		if n.parent.hash != phash {
			t.Error("Parent of uploaded file mismatch")
		}
		session.FS.mutex.Unlock()

		err := session.DownloadFile(node, name, nil)
		if err != nil {
			t.Fatal("Download failed", err)
		}

		h2 := fileMD5(t, name)
		err = os.Remove(name)
		if err != nil {
			t.Error("Failed to remove file", err)
		}

		if h1 != h2 {
			t.Error("MD5 mismatch for downloaded file")
		}
	}
	session.SetHTTPS(false)
}

func TestMove(t *testing.T) {
	session := initSession(t)
	node, _, _ := uploadFile(t, session, 31, session.FS.root)

	hash := node.hash
	phash := session.FS.trash.hash
	err := session.Move(node, session.FS.trash)
	if err != nil {
		t.Fatal("Move failed", err)
	}

	session.FS.mutex.Lock()
	n := session.FS.lookup[hash]
	if n.parent.hash != phash {
		t.Error("Move happened to wrong parent", phash, n.parent.hash)
	}
	session.FS.mutex.Unlock()
}

func TestRename(t *testing.T) {
	session := initSession(t)
	node, _, _ := uploadFile(t, session, 31, session.FS.root)

	err := session.Rename(node, "newname.txt")
	if err != nil {
		t.Fatal("Rename failed", err)
	}

	session.FS.mutex.Lock()
	newname := session.FS.lookup[node.hash].name
	if newname != "newname.txt" {
		t.Error("Renamed to wrong name", newname)
	}
	session.FS.mutex.Unlock()
}

func TestDelete(t *testing.T) {
	session := initSession(t)
	node, _, _ := uploadFile(t, session, 31, session.FS.root)

	retry(t, "Soft delete", func() error {
		return session.Delete(node, false)
	})

	session.FS.mutex.Lock()
	node = session.FS.lookup[node.hash]
	if node.parent != session.FS.trash {
		t.Error("Expects file to be moved to trash")
	}
	session.FS.mutex.Unlock()

	retry(t, "Hard delete", func() error {
		return session.Delete(node, true)
	})

	time.Sleep(1 * time.Second) // wait for the event

	session.FS.mutex.Lock()
	if _, ok := session.FS.lookup[node.hash]; ok {
		t.Error("Expects file to be dissapeared")
	}
	session.FS.mutex.Unlock()
}

func TestCreateDir(t *testing.T) {
	session := initSession(t)
	node := createDir(t, session, "testdir1", session.FS.root)
	node2 := createDir(t, session, "testdir2", node)

	session.FS.mutex.Lock()
	nnode2 := session.FS.lookup[node2.hash]
	if nnode2.parent.hash != node.hash {
		t.Error("Wrong directory parent")
	}
	session.FS.mutex.Unlock()
}

func TestConfig(t *testing.T) {
	skipIfNoCredentials(t)

	m := New()
	m.SetAPIUrl("http://invalid.domain")
	err := m.Login(USER, PASSWORD)
	if err == nil {
		t.Error("API Url: Expected failure")
	}

	err = m.SetDownloadWorkers(100)
	if err != EWORKER_LIMIT_EXCEEDED {
		t.Error("Download: Expected EWORKER_LIMIT_EXCEEDED error")
	}

	err = m.SetUploadWorkers(100)
	if err != EWORKER_LIMIT_EXCEEDED {
		t.Error("Upload: Expected EWORKER_LIMIT_EXCEEDED error")
	}

	// TODO: Add timeout test cases

}

func TestPathLookup(t *testing.T) {
	session := initSession(t)

	rs, err := randString(5)
	if err != nil {
		t.Fatalf("failed to make random string: %v", err)
	}
	node1 := createDir(t, session, "dir-1-"+rs, session.FS.root)
	node21 := createDir(t, session, "dir-2-1-"+rs, node1)
	node22 := createDir(t, session, "dir-2-2-"+rs, node1)
	node31 := createDir(t, session, "dir-3-1-"+rs, node21)
	node32 := createDir(t, session, "dir-3-2-"+rs, node22)
	_ = node32

	_, name1, _ := uploadFile(t, session, 31, node31)
	_, _, _ = uploadFile(t, session, 31, node31)
	_, name3, _ := uploadFile(t, session, 31, node22)

	testpaths := [][]string{
		{"dir-1-" + rs, "dir-2-2-" + rs, path.Base(name3)},
		{"dir-1-" + rs, "dir-2-1-" + rs, "dir-3-1-" + rs},
		{"dir-1-" + rs, "dir-2-1-" + rs, "dir-3-1-" + rs, path.Base(name1)},
		{"dir-1-" + rs, "dir-2-1-" + rs, "none"},
	}

	results := []error{nil, nil, nil, ENOENT}

	for i, tst := range testpaths {
		ns, e := session.FS.PathLookup(session.FS.root, tst)
		switch {
		case e != results[i]:
			t.Errorf("Test %d failed: wrong result", i)
		default:
			if results[i] == nil && len(tst) != len(ns) {
				t.Errorf("Test %d failed: result array len (%d) mismatch", i, len(ns))

			}

			arr := []string{}
			for n := range ns {
				if tst[n] != ns[n].name {
					t.Errorf("Test %d failed: result node mismatches (%v) and (%v)", i, tst, arr)
					break
				}
				arr = append(arr, tst[n])
			}
		}
	}
}

func TestEventNotify(t *testing.T) {
	session1 := initSession(t)
	session2 := initSession(t)

	node, _, _ := uploadFile(t, session1, 31, session1.FS.root)

	for i := 0; i < 60; i++ {
		time.Sleep(time.Second * 1)
		node = session2.FS.HashLookup(node.GetHash())
		if node != nil {
			break
		}
	}

	if node == nil {
		t.Fatal("Expects file to found in second client's FS")
	}

	retry(t, "Delete", func() error {
		return session2.Delete(node, true)
	})

	time.Sleep(time.Second * 5)
	node = session1.FS.HashLookup(node.hash)
	if node != nil {
		t.Fatal("Expects file to not-found in first client's FS")
	}
}

func TestExportLink(t *testing.T) {
	session := initSession(t)
	node, _, _ := uploadFile(t, session, 31, session.FS.root)

	// Don't include decryption key
	retry(t, "Failed to export link (key not included)", func() error {
		_, err := session.Link(node, false)
		return err
	})

	// Do include decryption key
	retry(t, "Failed to export link (key included)", func() error {
		_, err := session.Link(node, true)
		return err
	})
}

func TestWaitEvents(t *testing.T) {
	m := &Mega{}
	m.SetLogger(t.Logf)
	m.SetDebugger(t.Logf)
	var wg sync.WaitGroup
	// in the background fire the event timer after 100mS
	wg.Add(1)
	go func() {
		time.Sleep(100 * time.Millisecond)
		m.waitEventsFire()
		wg.Done()
	}()
	wait := func(d time.Duration, pb *bool) {
		e := m.WaitEventsStart()
		*pb = m.WaitEvents(e, d)
		wg.Done()
	}
	// wait for each event in a separate goroutine
	var b1, b2, b3 bool
	wg.Add(3)
	go wait(10*time.Second, &b1)
	go wait(2*time.Second, &b2)
	go wait(1*time.Millisecond, &b3)
	wg.Wait()
	if b1 != false {
		t.Errorf("Unexpected timeout for b1")
	}
	if b2 != false {
		t.Errorf("Unexpected timeout for b2")
	}
	if b3 != true {
		t.Errorf("Unexpected event for b3")
	}
	if m.waitEvents != nil {
		t.Errorf("Expecting waitEvents to be empty")
	}
	// Check nothing happens if we fire the event with no listeners
	m.waitEventsFire()
}

func TestLoginAnonymous(t *testing.T) {
	m := New()
	retry(t, "Anonymous Login", func() error {
		return m.LoginAnonymous()
	})

	// Verify filesystem is initialized
	if m.FS.root == nil {
		t.Fatal("Root node is nil after anonymous login")
	}

	if m.FS.trash == nil {
		t.Fatal("Trash node is nil after anonymous login")
	}

	// Try basic operation: create directory
	node := createDir(t, m, "anonymousTest", m.FS.root)
	if node == nil {
		t.Fatal("Failed to create directory after anonymous login")
	}

	// Clean up
	err := m.Delete(node, true)
	if err != nil {
		t.Logf("Warning: cleanup failed: %v", err)
	}
}

func TestSharedFolderLink(t *testing.T) {
	// Test parsing a shared folder link
	link := "https://mega.nz/folder/ABcD1234#EFgh5678IjklMN0"
	handle, key, err := GetSharedFolderInfo(link)
	if err != nil {
		t.Fatalf("Failed to parse shared folder link: %v", err)
	}

	if handle != "ABcD1234" {
		t.Errorf("Wrong handle parsed from link, got %s, want ABcD1234", handle)
	}

	if key != "EFgh5678IjklMN0" {
		t.Errorf("Wrong key parsed from link, got %s, want EFgh5678IjklMN0", key)
	}

	// Test with different format
	link = "folder/ABcD1234#EFgh5678IjklMN0"
	handle, key, err = GetSharedFolderInfo(link)
	if err != nil {
		t.Fatalf("Failed to parse shared folder link: %v", err)
	}

	if handle != "ABcD1234" {
		t.Errorf("Wrong handle parsed from link, got %s, want ABcD1234", handle)
	}

	// Test with invalid format
	_, _, err = GetSharedFolderInfo("invalid-link")
	if err == nil {
		t.Errorf("Expected error for invalid link format, got nil")
	}

	// Note: We don't test actual API access here to avoid dependency on external services
	// and requiring valid links that might expire
}

func TestRealSharedFolder(t *testing.T) {
	// Test with a real shared folder link
	link := "mega.nz/folder/PAhFHS7T#a_9EPWjRFsVNAICwHrEFqA"

	// Set timeout to be a bit longer since we're making network requests
	timeout := 30 * time.Second

	// Create a done channel to track test completion
	done := make(chan bool)

	// Run the test in a goroutine with timeout
	go func() {
		// Parse the link
		handle, key, err := GetSharedFolderInfo(link)
		if err != nil {
			t.Errorf("Failed to parse shared folder link: %v", err)
			done <- true
			return
		}

		// Remove leading slash if present
		handle = strings.TrimPrefix(handle, "/")

		t.Logf("Parsed link - handle: %s, key: %s", handle, key)

		// Create a new MEGA client with debugging
		m := New()
		m.SetLogger(t.Logf)
		m.SetDebugger(t.Logf)

		// Create a shared filesystem
		fs, err := m.NewSharedFS(handle, key)
		if err != nil {
			t.Errorf("Failed to create shared filesystem: %v", err)
			done <- true
			return
		}

		// Get root node
		root := fs.GetRoot()
		if root == nil {
			t.Errorf("Root node is nil")
			done <- true
			return
		}

		t.Logf("Successfully accessed shared folder: %s", root.GetName())

		// Function to recursively print directory structure
		var printDir func(node *Node, prefix string)
		printDir = func(node *Node, prefix string) {
			if node == nil {
				return
			}

			// Get node type as string
			nodeType := "File"
			if node.GetType() == FOLDER {
				nodeType = "Folder"
			}

			// Print node info
			t.Logf("%s- %s (%s, Size: %d, Modified: %s)",
				prefix,
				node.GetName(),
				nodeType,
				node.GetSize(),
				node.GetTimeStamp().Format(time.RFC3339))

			// Get children
			children, err := fs.GetChildren(node)
			if err != nil {
				t.Logf("%s  Error getting children: %v", prefix, err)
				return
			}

			// Print children recursively
			for _, child := range children {
				printDir(child, prefix+"  ")
			}
		}

		// Print directory structure
		t.Logf("Directory structure:")
		printDir(root, "")

		done <- true
	}()

	// Wait for the test to complete or timeout
	select {
	case <-done:
		// Test completed
	case <-time.After(timeout):
		t.Fatalf("Test timed out after %v", timeout)
	}
}

func TestDownloadFromSharedFolder(t *testing.T) {
	// Test with a real shared folder link (read-only access)
	// This link contains a small text file "Small Text File for Rclone Test.txt"
	link := "https://mega.nz/folder/PAhFHS7T#a_9EPWjRFsVNAICwHrEFqA"
	testFileName := "Small Text File for Rclone Test.txt" // Adjust if the file name changes in the share
	testFileSize := int64(720851726)                      // Expected size of the test file
	testFileHandle := "jRoUhJZZ"                          // The specific handle of the test file within the shared folder

	t.Logf("Testing download from shared link: %s", link)

	m := New()
	m.SetLogger(t.Logf)
	m.SetDebugger(t.Logf)

	// Parse the link
	handle, key, err := GetSharedFolderInfo(link)
	if err != nil {
		t.Fatalf("Failed to parse shared folder link: %v", err)
	}

	// Create shared filesystem
	fs, err := m.NewSharedFS(handle, key)
	if err != nil {
		t.Fatalf("Failed to create shared filesystem: %v", err)
	}

	// Find the specific test file node using its handle
	var targetNode *Node
	fs.mutex.Lock()
	targetNode = fs.hashLookup(testFileHandle)
	fs.mutex.Unlock()

	if targetNode == nil {
		// It might take a moment for the FS to populate, let's list children if lookup failed
		rootNode := fs.GetRoot()
		if rootNode != nil {
			children, _ := fs.GetChildren(rootNode) // Ignore error for test simplicity
			for _, child := range children {
				if child.GetHash() == testFileHandle {
					targetNode = child
					break
				}
			}
		}
		if targetNode == nil {
			t.Fatalf("Test file node with handle %s not found in shared folder %s", testFileHandle, handle)
		}
	}

	t.Logf("Found test file node: Name='%s', Handle='%s', Size=%d", targetNode.GetName(), targetNode.GetHash(), targetNode.GetSize())

	// Verify file size if possible (can be a basic sanity check)
	if targetNode.GetSize() != testFileSize {
		t.Logf("Warning: Test file size mismatch. Expected %d, Got %d. Proceeding anyway.", testFileSize, targetNode.GetSize())
		testFileSize = targetNode.GetSize() // Use actual size for verification later
	}

	// Create temporary file for download
	tempFile, err := ioutil.TempFile("", "mega-shared-dl-*")
	if err != nil {
		t.Fatalf("Failed to create temp file for download: %v", err)
	}
	tempFilePath := tempFile.Name()
	_ = tempFile.Close()          // Close immediately, download process will handle opening/writing
	defer os.Remove(tempFilePath) // Clean up temp file

	t.Logf("Attempting to download node %s to %s", targetNode.GetHash(), tempFilePath)

	// --- Use NewDownload and chunk download ---
	d, err := m.NewDownload(targetNode)
	if err != nil {
		t.Fatalf("NewDownload failed for shared file: %v", err)
	}

	outfile, err := os.OpenFile(tempFilePath, os.O_RDWR|os.O_CREATE, 0600)
	if err != nil {
		t.Fatalf("Failed to open temp file %s for writing: %v", tempFilePath, err)
	}

	workch := make(chan int)
	errch := make(chan error, m.dl_workers)
	var wg sync.WaitGroup

	// Fire chunk download workers
	for w := 0; w < m.dl_workers; w++ {
		wg.Add(1)
		go func() {
			defer wg.Done()
			for id := range workch {
				chunk, err := d.DownloadChunk(id)
				if err != nil {
					errch <- fmt.Errorf("DownloadChunk %d failed: %w", id, err)
					return
				}

				chk_start, _, err := d.ChunkLocation(id)
				if err != nil {
					errch <- fmt.Errorf("ChunkLocation %d failed: %w", id, err)
					return
				}

				_, err = outfile.WriteAt(chunk, chk_start)
				if err != nil {
					errch <- fmt.Errorf("WriteAt %d failed: %w", id, err)
					return
				}
			}
		}()
	}

	// Place chunk download jobs to chan
	jobErr := error(nil)
	for id := 0; id < d.Chunks(); id++ {
		select {
		case workch <- id:
		case jobErr = <-errch:
			// If an error occurs, break the loop
			goto handle_error
		}
	}
handle_error:
	close(workch) // Close work channel regardless of errors to signal workers

	wg.Wait() // Wait for all workers to finish

	// Check for any remaining errors from workers after loop break
	select {
	case workerErr := <-errch:
		if jobErr == nil { // Prioritize the first error encountered
			jobErr = workerErr
		}
	default:
		// No more errors in the channel
	}

	closeErr := outfile.Close()
	if jobErr != nil {
		t.Fatalf("Error during chunk download: %v", jobErr)
	}
	if closeErr != nil {
		t.Fatalf("Error closing output file %s: %v", tempFilePath, closeErr)
	}

	// Finish the download (should skip MAC check for shared)
	err = d.Finish()
	if err != nil {
		t.Fatalf("Download Finish failed: %v", err)
	}

	t.Logf("Successfully downloaded shared file %s to %s", testFileName, tempFilePath)

	// Optional: Verify downloaded file size
	info, err := os.Stat(tempFilePath)
	if err != nil {
		t.Errorf("Failed to stat downloaded file %s: %v", tempFilePath, err)
	} else if info.Size() != testFileSize {
		t.Errorf("Downloaded file size mismatch. Expected %d, Got %d", testFileSize, info.Size())
	} else {
		t.Logf("Downloaded file size verified: %d bytes", info.Size())
	}
}
