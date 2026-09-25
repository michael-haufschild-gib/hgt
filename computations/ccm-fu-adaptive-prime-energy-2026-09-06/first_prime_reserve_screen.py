"""Frozen extension of first-prime reserve and dilation-ratio questions."""
import csv
import json
import math
from pathlib import Path

BASE = Path(__file__).resolve().parent
LIMIT = 1024
tau = [0]*(LIMIT+1)
squarefree = [True]*(LIMIT+1)
primes = []
for d in range(1, LIMIT+1):
    for n in range(d, LIMIT+1, d):
        tau[n] += 1
for p in range(2, LIMIT+1):
    if tau[p] == 2:
        primes.append(p)
        for n in range(p*p, LIMIT+1, p*p):
            squarefree[n] = False
defect = [0.]*(LIMIT+1)
clock = [0.]*(LIMIT+1)
logs = count = 0.
for n in range(1, LIMIT+1):
    logs += math.log(n)
    count += tau[n]
    defect[n] = logs-count+2*0.5772156649015328606065120900824*n
    if n < LIMIT:
        clock[n+1] = clock[n]+defect[n]/(math.sqrt(n+1)+math.sqrt(n))
with (BASE/'first-prime-unit-clock.csv').open('w') as handle:
    writer = csv.writer(handle)
    writer.writerow(['n','defect','unit_channel'])
    writer.writerows((n,defect[n],clock[n]) for n in range(LIMIT+1))
saved = {row['M']:row['initial'] for row in json.loads((BASE/'greedy-summary.json').read_text())}
ratio_failures = []
reserve_failures = []
max_ratio = None
pair_count = state_count = 0
max_diagonal_error = 0.
records = []
for cutoff in range(33, LIMIT+1):
    channels = {d:math.sqrt(d)*clock[cutoff//d]+
                (math.sqrt(cutoff)-math.sqrt(d*(cutoff//d)))*defect[cutoff//d]
                for d in range(1, cutoff) if squarefree[d]}
    initial = math.fsum(x*x for x in channels.values())
    tolerance = 1e-12*max(1,initial)
    max_diagonal_error = max(max_diagonal_error,abs(initial-saved[cutoff]))
    assert abs(initial-saved[cutoff]) <= tolerance
    for p in primes:
        if p >= cutoff:
            break
        overlap_terms = []
        defects = []
        for d in range(1,(cutoff-1)//p+1):
            if not squarefree[d] or d % p == 0:
                continue
            a,b = channels[d],channels[p*d]
            pair_count += 1
            if b > 2*a+tolerance:
                ratio_failures.append(dict(M=cutoff,p=p,d=d,parent=a,child=b))
            if a > tolerance and (max_ratio is None or b/a > max_ratio['ratio']):
                max_ratio = dict(M=cutoff,p=p,d=d,parent=a,child=b,ratio=b/a)
            overlap_terms.append(a*b)
            defects.append(max(b-a,0)**2)
        release = 2*math.fsum(overlap_terms)
        denergy = math.fsum(defects)
        cost = 2*math.sqrt(initial*denergy)
        record = dict(M=cutoff,p=p,initial=initial,release=release,defect=denergy,cost=cost)
        records.append(record)
        state_count += 1
        if cost > release+tolerance:
            reserve_failures.append(record)
summary = dict(question='Factor-two source dilation and weaker first-prime geometric reserve, M=33..1024',
               states=state_count,pairs=pair_count,max_diagonal_error=max_diagonal_error,
               ratio_failure_count=len(ratio_failures),first_ratio_failure=next(iter(ratio_failures),None),
               reserve_failure_count=len(reserve_failures),first_reserve_failure=next(iter(reserve_failures),None),
               max_ratio=max_ratio,ratio_failures=ratio_failures,reserve_failures=reserve_failures,states_data=records)
(BASE/'first-prime-reserve-screen.json').write_text(json.dumps(summary,indent=2)+'\n')
print(json.dumps({k:v for k,v in summary.items() if k not in ('ratio_failures','reserve_failures','states_data')},indent=2))
