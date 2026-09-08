"""Read independent defining-source audit; compute charge at 80 digits on RunPod."""
import hashlib
import json
import math
from pathlib import Path
import time
import mpmath as mp

mp.mp.dps=80
start=time.monotonic()
source=json.loads(Path('audit.json').read_text())
M=source['M']


def mobius(n):
    sign=1
    p=2
    while p*p<=n:
        if n%p==0:
            n//=p
            sign=-sign
            if n%p==0:
                return 0
        p+=1
    return -sign if n>1 else sign


G={item['r']:mp.mpf(item['G']) for item in source['groups']}
D=mp.mpf(source['diagonal'])
S=mp.mpf(source['head'])
L=mp.fsum(G.values())
J=mp.fsum(mobius(r)*abs(g) for r,g in G.items())
plus=mp.fsum(g for r,g in G.items() if mobius(r)*g>0)
minus=mp.fsum(g for r,g in G.items() if mobius(r)*g<0)
assert max(abs(plus-(L+J)/2),abs(minus-(L-J)/2),abs(L-(S*S-D)))<mp.mpf('1e-65')*D
ratio=(S*S+abs(J))/D
row=next(r for r in json.loads(Path('summary.json').read_text())['rows'] if r['M']==M)
error=abs(ratio-mp.mpf(row['necessary_ratio']))
assert error<mp.mpf('1e-10')
nstr=lambda x:mp.nstr(x,70)
result=dict(M=M,digits=80,seconds=time.monotonic()-start,
            diagonal=nstr(D),head_square=nstr(S*S),signed_cross=nstr(L),parity_charge=nstr(J),
            class_plus=nstr(plus),class_minus=nstr(minus),necessary_ratio=nstr(ratio),
            colour_over_D=nstr((max(plus,0)+max(minus,0))/D),screen_ratio_error=nstr(error),
            source_audit_sha256=hashlib.sha256(Path('audit.json').read_bytes()).hexdigest(),
            script_sha256=hashlib.sha256(Path(__file__).read_bytes()).hexdigest())
Path('charge_audit.json').write_text(json.dumps(result,indent=2))
print(json.dumps(result),flush=True)
