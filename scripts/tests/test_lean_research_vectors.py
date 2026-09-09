from __future__ import annotations

import importlib.util
import sys
import tempfile
import time
import unittest
from unittest.mock import patch
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parents[1]))
from lean_research_corpus import Corpus


@unittest.skipUnless(importlib.util.find_spec('faiss'), 'requires dedicated research runtime')
class VectorTests(unittest.TestCase):
    def setUp(self):
        from lean_research_vectors import Vectors
        self.tmp = tempfile.TemporaryDirectory()
        self.addCleanup(self.tmp.cleanup)
        self.root = Path(self.tmp.name)
        (self.root / 'formal').mkdir()
        (self.root / 'formal/A.lean').write_text('theorem alpha : True := trivial')
        (self.root / 'formal/B.lean').write_text('theorem beta : True := trivial')
        self.db = Corpus(self.root / 'cache')
        self.addCleanup(self.db.close)
        self.db.refresh(self.root)
        self.vectors = Vectors(self.db)
        self.docs = [dict(r) for r in self.db.con.execute("SELECT * FROM documents WHERE view='statement' ORDER BY module")]

    def test_ranking_module_filters_and_stale_source_exclusion(self):
        self.vectors.publish(self.docs, [[1., 0.], [0., 1.]], 'm1')
        query = dict(model='m1', views=('statement',))
        self.assertEqual(self.vectors.search([1., 0.], **query)[0]['module'], 'A')
        self.assertEqual(self.vectors.search([1., 0.], module='B', limit=1, **query)[0]['module'], 'B')
        self.assertFalse(self.vectors.search([1., 0.], model='m2', views=('statement',)))
        (self.root / 'formal/A.lean').write_text('theorem gamma : True := trivial')
        self.db.refresh(self.root)
        self.assertEqual([h['module'] for h in self.vectors.search([1., 0.], **query)], ['B'])

    def test_publish_rejects_changed_document_hash(self):
        stale = {**self.docs[0], 'content_hash': 'outdated'}
        self.assertEqual(self.vectors.publish([stale], [[1., 0.]], 'm1'), 0)
        self.assertFalse(self.vectors.search([1., 0.], model='m1', views=('statement',)))

    def test_edit_reuses_unchanged_chunks_after_old_document_rows_are_deleted(self):
        path = self.root / 'formal/A.lean'
        path.write_text('theorem alpha : True := trivial\ntheorem gamma : True := trivial')
        self.db.refresh(self.root)
        before = [dict(r) for r in self.db.con.execute("SELECT * FROM documents WHERE module='A' AND view='statement' ORDER BY id")]
        self.vectors.publish(before, [[1., 0.], [0., 1.]], 'm1')
        path.write_text('-- inserted line\ntheorem alpha : True := trivial\ntheorem delta : True := trivial')
        self.db.refresh(self.root)
        after = [dict(r) for r in self.db.con.execute("SELECT * FROM documents WHERE module='A' AND view='statement' ORDER BY id")]
        reused = self.vectors.reuse(after, 'm1')
        self.assertEqual(reused, {before[0]['content_hash']: [1., 0.]})
        self.assertEqual(self.vectors.reuse(after, 'm2'), {})
        self.assertEqual(self.vectors.search([0., 1.], model='m1', views=('statement',)), [])
        # Compaction must retain cached vectors even with no active source row.
        self.vectors.compact('m1')
        self.assertEqual(self.vectors.reuse(after, 'm1'), reused)

    def test_compaction_preserves_ranking_and_published_metadata(self):
        self.vectors.publish([self.docs[0]], [[1., 0.]], 'm1')
        self.vectors.publish([self.docs[1]], [[0., 1.]], 'm1')
        before = self.vectors.search([1., .1], model='m1', views=('statement',))
        report = self.vectors.compact('m1')
        after = self.vectors.search([1., .1], model='m1', views=('statement',))
        self.assertEqual([h['id'] for h in before], [h['id'] for h in after])
        self.assertEqual(report['republished'], 2)
        self.assertEqual(self.db.con.execute('SELECT COUNT(*) FROM vector_shards').fetchone()[0], 1)

    def test_deadline_and_invalid_embeddings_are_rejected(self):
        with self.assertRaises(ValueError):
            self.vectors.publish(self.docs, [[1., 0.]], 'm1')
        with self.assertRaises(ValueError):
            self.vectors.publish([self.docs[0]], [[float('nan'), 0.]], 'm1')
        self.vectors.publish([self.docs[0]], [[1., 0.]], 'm1')
        with self.assertRaises(TimeoutError):
            self.vectors.search([1., 0.], model='m1', views=('statement',), deadline=time.monotonic() - 1)

    def test_new_and_existing_pending_work_respects_folder_priority(self):
        for folder in ('HTGeometry', 'RHTower'):
            path = self.root / 'formal' / folder / 'A.lean'
            path.parent.mkdir()
            path.write_text('theorem sample : True := trivial')
        self.db.refresh(self.root)
        pending = self.vectors.pending('m1', limit=64)
        paths = [d['path'] for d in pending]
        self.assertEqual(paths[:2], ['formal/RHTower/A.lean'] * 2)
        self.assertEqual(paths[2:4], ['formal/HTGeometry/A.lean'] * 2)
        # The trigger keeps this order after queue initialization.
        path = self.root / 'formal/RHTower/B.lean'
        path.write_text('theorem newResult : True := trivial')
        self.db.refresh(self.root)
        pending = self.vectors.pending('m1', limit=64)
        self.assertTrue(all('/RHTower/' in d['path'] for d in pending[:4]))

    def test_conflicting_torch_process_is_rejected_before_openmp_initializes(self):
        from lean_research_vectors import Vectors
        with patch.object(sys, 'platform', 'darwin'), patch.dict(sys.modules, {'torch': object()}):
            with self.assertRaisesRegex(ImportError, 'separately from Torch'):
                Vectors(self.db)


if __name__ == '__main__':
    unittest.main()
