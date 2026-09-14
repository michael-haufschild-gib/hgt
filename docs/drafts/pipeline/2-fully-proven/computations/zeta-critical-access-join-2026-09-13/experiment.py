import json,time,math
from pathlib import Path
start=time.monotonic();access=json.loads(Path('access-input.json').read_text())['rows'];critical=json.loads(Path('critical-input.json').read_text())['rows']
points={}
for r in critical:
    if 'endpoints' in r:points.setdefault(tuple(round(float(x),8) for x in r['critical_point']),r)
edges=[sorted([r['endpoints'][0][0],r['endpoints'][1][0]]) for r in points.values()]
rows=[]
for mode in ['all_observed_edges','adjacent_edges_only']:
    parent={i:i for i in range(1,65)}
    def root(n):
        while parent[n]!=n:n=parent[n]
        return n
    ee=edges if mode=='all_observed_edges' else [e for e in edges if abs(e[0]-e[1])==1]
    for a,b in ee:parent[root(a)]=root(b)
    cc={}
    for n in parent:cc.setdefault(root(n),[]).append(n)
    for angle in [0,-1,1]:
        aa={r['n']:r for r in access if r['angle_thirds_pi']==angle};components=[]
        for labels in cc.values():
            groups={category:[n for n in labels if aa[n].get('category')==category] for category in ['escape_like','finite_like','unresolved']}
            components.append(dict(labels=labels,**groups))
        rows.append(dict(mode=mode,angle_thirds_pi=angle,edge_count=len(ee),components=components,one_escape_components=sum(len(c['escape_like'])==1 for c in components),zero_escape_components=sum(len(c['escape_like'])==0 for c in components),multiple_escape_components=sum(len(c['escape_like'])>1 for c in components)))
changes=[]
for n in range(1,65):
    rr=[r for r in access if r['n']==n];cats={str(r['angle_thirds_pi']):r.get('category','error') for r in rr}
    if len(set(cats.values()))>1:changes.append(dict(n=n,categories=cats))
out=dict(unique_critical_points=len(points),edges=edges,access_counts={str(a):{c:sum(r.get('category')==c and r['angle_thirds_pi']==a for r in access) for c in ['escape_like','finite_like','unresolved']} for a in [0,-1,1]},direction_changes=changes,rows=rows,seconds=time.monotonic()-start)
Path('summary.json').write_text(json.dumps(out,indent=2)+'\n');print(json.dumps(out),flush=True)
