"""PE4/PE4G reanalysis of stored energies; no channel regeneration or greedy rerun."""
import csv,json,pathlib
base=pathlib.Path(__file__).parent
rows={}
for r in csv.DictReader((base/'subset-states.csv').open()):
    rows.setdefault(int(r['M']),[]).append(r)
res=[]
for M,states in rows.items():
    E=[float(r['energy']) for r in states]
    cost=[0.]*len(E);cost[0]=E[0]
    for mask in range(1,len(E)):
        best=min(cost[mask^(1<<i)] for i in range(mask.bit_length()) if mask>>i&1)
        cost[mask]=max(E[mask],best)
    res.append({'M':M,'initial_energy':E[0],'minimum_path_ceiling':cost[-1],
                'PE4_path_exists':cost[-1]<=E[0]+1e-12*max(1,E[0]),'states':len(E)})
first=None;worst=(0,None);count=0
for r in csv.DictReader((base/'greedy-stages.csv').open()):
    E=float(r['next_energy']);E0=float(r['initial_energy']);ratio=E/E0 if E0 else 0.
    if ratio>worst[0]:worst=(ratio,r)
    if E>E0+1e-12*max(1,E0):
        count+=1
        if first is None:first=r
summary={'full_subset_limit':32,'first_PE4_path_failure':next((x for x in res if not x['PE4_path_exists']),None),
         'first_PE4G_failure':first,'PE4G_failed_stages':count,'max_greedy_ratio':worst,'full_subset_results':res}
(base/'ceiling-reanalysis.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k!='full_subset_results'},indent=2))
