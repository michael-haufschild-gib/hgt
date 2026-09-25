"""Test whether continuous production can pay all negative jumps without positive jumps."""
import os
os.environ['OPENBLAS_NUM_THREADS']='1'
import gzip, json
from pathlib import Path
import numpy as np
with gzip.open('entries.csv.gz','rt') as f:
    rows=np.loadtxt(f,delimiter=',',skiprows=1)
jumps=rows[:,8]
flow=np.r_[0.,rows[1:,6]-rows[:-1,7]]
positive=np.cumsum(np.maximum(jumps,0))
negative=np.cumsum(np.maximum(-jumps,0))
production=np.cumsum(flow)
initial=float(rows[0,6])
without_positive=initial+production-negative
failed=np.flatnonzero(without_positive<0)
summary={
 'initial_entry':int(rows[0,0]),'initial_barrier':initial,
 'first_negative_budget_without_positive_jumps':None if not len(failed) else {
   'n':int(rows[failed[0],0]),'budget':float(without_positive[failed[0]]),
   'negative_jump_debt':float(negative[failed[0]]),
   'continuous_production':float(production[failed[0]]),
   'positive_jump_credit':float(positive[failed[0]]),
   'actual_outgoing_barrier':float(rows[failed[0],7])},
 'final_entry':int(rows[-1,0]),
 'total_positive_jump_credit':float(positive[-1]),
 'total_negative_jump_debt':float(negative[-1]),
 'net_jump_credit':float(np.sum(jumps)),
 'total_continuous_production':float(production[-1]),
 'final_outgoing_barrier':float(rows[-1,7]),
 'negative_between_entry_increments':int(np.sum(flow< -1e-7)),
 'maximum_balance_residual':float(np.max(np.abs(initial+production+positive-negative-rows[:,7])))
}
Path('balance_summary.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps(summary,indent=2))
