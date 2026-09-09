"""Real local Qdrant integration; isolated collections, no production writes."""
import os
from pathlib import Path
import sys
import tempfile
import time
import unittest
from unittest.mock import patch
sys.path.insert(0,str(Path(__file__).resolve().parents[1]))
from lean_research_corpus import Corpus
from lean_research_vectors import Vectors
from lean_research_qdrant import Qdrant, sync, reconcile

@unittest.skipUnless(os.environ.get('HGT_TEST_QDRANT')=='1','requires local Qdrant integration opt-in')
class QdrantTests(unittest.TestCase):
 def setUp(self):
  self.tmp=tempfile.TemporaryDirectory();self.addCleanup(self.tmp.cleanup)
  self.root=Path(self.tmp.name);(self.root/'formal').mkdir()
  for n in ('A','B'):(self.root/'formal'/f'{n}.lean').write_text(f'theorem {n.lower()} : True := trivial')
  self.c=Corpus(self.root/'cache');self.addCleanup(self.c.close);self.c.refresh(self.root)
  self.v=Vectors(self.c);self.q=Qdrant(self.c.directory)
  self.docs=[dict(r) for r in self.c.con.execute("SELECT * FROM documents WHERE view='statement' ORDER BY module")]
  self.addCleanup(lambda:[self.q.request('DELETE','/collections/'+self.q.collection(m),missing_ok=True) for m in ('m1','m2')])
 def flush(self):return sync(self.c,deadline=time.monotonic()+20)
 def search(self,**kw):return self.v.search([1.,0.],model='m1',views=('statement',),deadline=time.monotonic()+3,**kw)
 def test_publish_filters_changed_and_deleted_sources(self):
  self.v.publish(self.docs,[[1.,0.],[0.,1.]],'m1');self.assertEqual(self.flush()['upserted'],2)
  self.assertEqual(self.search(limit=1)[0]['module'],'A')
  self.assertEqual(self.search(module='b',limit=1)[0]['module'],'B')
  self.assertEqual(self.search(exclude_modules=['A'])[0]['module'],'B')
  (self.root/'formal/A.lean').write_text('theorem changed : False := by contradiction')
  self.c.refresh(self.root)
  self.assertTrue(all(r['module']!='A' for r in self.search()))
  (self.root/'formal/B.lean').unlink();self.c.refresh(self.root)
  self.assertEqual(self.search(),[]);self.flush()
  count=self.q.request('POST','/collections/'+self.q.collection('m1')+'/points/count',{'exact':True})
  self.assertEqual(count['count'],0)
 def test_failed_remote_write_keeps_queue_and_retry_is_idempotent(self):
  self.v.publish(self.docs,[[1.,0.],[0.,1.]],'m1')
  original=Qdrant.request
  def fail(client,method,path,*args,**kw):
   if method=='PUT' and '/points?' in path:raise RuntimeError('simulated disconnect')
   return original(client,method,path,*args,**kw)
  with patch.object(Qdrant,'request',fail),self.assertRaisesRegex(RuntimeError,'disconnect'):self.flush()
  self.assertEqual(self.c.con.execute('SELECT COUNT(*) FROM qdrant_queue').fetchone()[0],2)
  self.flush();self.assertEqual(self.flush()['upserted'],0)
  self.assertEqual(len(self.search()),2)
 def test_model_change_removes_old_namespace_and_reconcile_restores_missing_receipts(self):
  self.v.publish(self.docs,[[1.,0.],[0.,1.]],'m1');self.flush()
  self.v.publish([self.docs[0]],[[1.,0.]],'m2');self.flush()
  self.assertEqual([r['module'] for r in self.search()],['B'])
  with self.c.con:self.c.con.execute('DELETE FROM qdrant_points')
  reconcile(self.c);self.flush()
  self.assertEqual(self.c.con.execute('SELECT COUNT(*) FROM qdrant_points').fetchone()[0],2)
 def test_acknowledgement_does_not_drop_newer_queued_update(self):
  self.v.publish([self.docs[0]],[[1.,0.]],'m1')
  original=Qdrant.request;clock=[time.monotonic()];deadline=clock[0]+20
  def replace(client,method,path,*args,**kw):
   result=original(client,method,path,*args,**kw)
   if method=='PUT' and '/points?' in path:
    with self.c.con:self.c.con.execute("INSERT OR REPLACE INTO qdrant_queue(doc_id,model,operation) VALUES(?,'m1','upsert')",(self.docs[0]['id'],))
    clock[0]=deadline+1
   return result
  with patch.object(Qdrant,'request',replace),patch('lean_research_qdrant.time.monotonic',lambda:clock[0]):
   result=sync(self.c,deadline=deadline)
  self.assertEqual(result['pending'],1)
  self.assertEqual(self.flush()['pending'],0)
 def test_expired_deadline_and_server_unavailable_do_not_scan_archives(self):
  with patch('lean_research_vectors.FaissVectors',side_effect=AssertionError('archive loaded')):
   with self.assertRaises(TimeoutError):self.v.search([1.,0.],model='m1',views=('statement',),deadline=time.monotonic()-1)
   with patch.object(Qdrant,'request',side_effect=RuntimeError('offline')),self.assertRaisesRegex(RuntimeError,'offline'):self.search()

if __name__=='__main__':unittest.main()
