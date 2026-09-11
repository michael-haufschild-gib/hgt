import plistlib
from pathlib import Path
import subprocess
import sys
import tempfile
import unittest
from unittest import mock

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
import lean_research_services as services


class ManagedIndexerTests(unittest.TestCase):
    def setUp(self):
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.directory = Path(self.tmp.name)
        self.plist = self.directory / 'indexer.plist'
        self.target = 'gui/501/com.hgt.test-indexer'
        self.loaded = False
        self.commands = []

        def launchctl(*args, **kwargs):
            self.commands.append(args)
            code = 0
            if args[0] == 'print':
                code = 0 if self.loaded else 1
            elif args[0] == 'bootstrap':
                self.loaded = True
            elif args[0] == 'bootout':
                self.loaded = False
            return subprocess.CompletedProcess(args, code, '', '')

        for patcher in (
            mock.patch.object(services.sys, 'platform', 'darwin'),
            mock.patch.object(services, 'indexer_agent', return_value=('com.hgt.test-indexer', self.plist, self.target)),
            mock.patch.object(services, 'launchctl', side_effect=launchctl),
            mock.patch.object(services, 'stop_indexer'),
            mock.patch.object(services, 'indexer_status', side_effect=lambda root: dict(running=self.loaded, pid=123)),
        ):
            patcher.start()
            self.addCleanup(patcher.stop)

    def test_restart_supervision_and_idempotent_start(self):
        first = services.start_managed_indexer(self.directory)
        definition = plistlib.loads(self.plist.read_bytes())
        self.assertTrue(definition['KeepAlive'])
        self.assertTrue(definition['RunAtLoad'])
        self.assertIn('lean_research_background.py', definition['ProgramArguments'][1])
        second = services.start_managed_indexer(self.directory)
        self.assertEqual(first['pid'], second['pid'])
        self.assertEqual(sum(cmd[0] == 'bootstrap' for cmd in self.commands), 1)
        self.assertNotIn('bootout', [cmd[0] for cmd in self.commands])

    def test_stop_unloads_job_and_removes_login_start(self):
        services.start_managed_indexer(self.directory)
        services.stop_managed_indexer(self.directory)
        self.assertFalse(self.loaded)
        self.assertFalse(self.plist.exists())
        services.start_managed_indexer(self.directory)
        self.assertTrue(self.loaded)
        self.assertTrue(self.plist.exists())

    def test_failed_bootout_preserves_job_for_recovery(self):
        services.start_managed_indexer(self.directory)
        with mock.patch.object(services, 'launchctl', side_effect=[
                subprocess.CompletedProcess([], 0), subprocess.CalledProcessError(5, 'bootout')]):
            with self.assertRaises(subprocess.CalledProcessError):
                services.stop_managed_indexer(self.directory)
        self.assertTrue(self.plist.exists())
