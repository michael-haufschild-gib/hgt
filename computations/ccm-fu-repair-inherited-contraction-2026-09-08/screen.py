"""Frozen inherited-contraction diagnostic; execute only on supplied RunPod."""
import csv
import hashlib
import json
import multiprocessing as mp
import os
from pathlib import Path
import signal
import time


def inspect(job):
    record, rows = job
    cutoff = record['M']
    primes = [int(p) for p in rows[max(rows)]['processed_primes'].split()]
    values = {n: float(row['energy']) for n, row in rows.items()}
    full = (1 << len(primes)) - 1
    assert set(values) == set(range(full + 1))
    bit = {p: 1 << i for i, p in enumerate(primes)}
    budget = values[0]
    tol = 1e-12 * max(1.0, budget)

    def children(mask):
        return [(p, mask | bit[p]) for p in primes if not mask & bit[p]]

    def env(mask):
        return max(values[n] for n in [mask] + [n for _, n in children(mask)])

    comparisons, failed = [], []
    for case in record['cases']:
        state = case['mask']
        q, end = min(children(state), key=lambda x: (values[x[1]], x[0]))
        assert q == case['chosen_prime'] and end == case['chosen_mask']
        assert abs(values[state] - case['energy']) <= tol
        assert env(state) > budget + tol and env(end) <= budget + tol
        for option in case['alternatives']:
            assert abs(values[option['mask']] - option['energy']) <= tol
        for parent in case['parents']:
            start, r = parent['mask'], parent['forced_prime']
            assert state == start | bit[r] and not start & bit[r]
            assert env(start) <= budget + tol
            for s in [None] + [s for s, _ in children(end)]:
                before = start if s is None else start | bit[s]
                after = end if s is None else end | bit[s]
                item = dict(M=cutoff, parent=start, forced=r, repair=q, successor=s,
                    before=before, after=after, before_energy=values[before],
                    after_energy=values[after], increase=values[after]-values[before],
                    inherited_reserve=budget-values[before], final_margin=budget-values[after])
                comparisons.append(item)
                if item['increase'] > tol:
                    failed.append(item)
    audit = direct_audit(cutoff, primes, failed) if failed else None
    return dict(M=cutoff, comparisons=len(comparisons), failures=len(failed),
                records=comparisons, failed_records=failed, direct_audit=audit)


def direct_audit(cutoff, primes, failures):
    import mpmath as m
    m.mp.dps = 80
    bit = {p: 1 << i for i, p in enumerate(primes)}
    defect = [m.mpf(0)] + [m.fsum(m.log(j) for j in range(1,n+1))
        - sum(n//d for d in range(1,n+1)) + 2*m.euler*n for n in range(1,cutoff)]
    coefficients = []
    for d in range(1,cutoff):
        if any(d % (p*p) == 0 for p in primes):
            continue
        support = sum(bit[p] for p in primes if d % p == 0)
        value = (-1)**bin(support).count('1') * m.fsum(
            (m.sqrt(k+1)-m.sqrt(k))*defect[k//d] for k in range(d,cutoff))
        coefficients.append((support,value))
    budget = m.fsum(v*v for _,v in coefficients)
    tol = m.mpf('1e-12')*max(1,budget)
    fields, energies = {}, {}

    def field(mask):
        if mask not in fields:
            grouped = {}
            for support, value in coefficients:
                grouped.setdefault(support & ~mask, []).append(value)
            fields[mask] = {r:m.fsum(v) for r,v in grouped.items()}
            energies[mask] = m.fsum(v*v for v in fields[mask].values())
        return fields[mask]

    def energy(mask):
        field(mask)
        return energies[mask]

    def children(mask):
        return [(p,mask|bit[p]) for p in primes if not mask & bit[p]]

    def env(mask):
        return max(energy(n) for n in [mask]+[n for _,n in children(mask)])

    checked = {}
    audited = []
    show = lambda x:m.nstr(x,82)
    for f in failures:
        parent, r, q = f['parent'], f['forced'], f['repair']
        state = parent | bit[r]
        key = (parent,r)
        if key not in checked:
            options = sorted(children(state), key=lambda x:(energy(x[1]),x[0]))
            selected, endpoint = options[0]
            near = [p for p,n in options if p != selected and abs(energy(n)-energy(endpoint)) <= m.mpf('1e-60')]
            assert env(parent) <= budget+tol and env(state) > budget+tol
            assert selected == q or q in near
            # Evaluate each alternative and all its successors, not just selected endpoint.
            checked[key] = dict(parent=parent,forced=r,selected=selected,unresolved=near,
                parent_margin=show(budget-env(parent)), forced_excess=show(env(state)-budget),
                alternatives=[dict(prime=p,mask=n,energy=show(energy(n)),envelope=show(env(n)))
                              for p,n in options])
        before, after = f['before'], f['after']
        increase = energy(after)-energy(before)
        assert increase > tol
        audited.append(dict(parent=parent,forced=r,repair=q,successor=f['successor'],
            before=before,after=after,increase=show(increase),
            inherited_reserve=show(budget-energy(before)),final_margin=show(budget-energy(after))))
    return dict(budget=show(budget),cases=list(checked.values()),comparisons=audited,
        fields={str(mask):{str(r):show(v) for r,v in field.items()}
                for mask,field in sorted(fields.items())})


def deadline(_signal,_frame):
    raise TimeoutError('50-second frozen experiment deadline')


def initialize_worker():
    signal.signal(signal.SIGALRM,signal.SIG_DFL)
    signal.signal(signal.SIGTERM,signal.SIG_DFL)


if __name__ == '__main__':
    signal.signal(signal.SIGALRM,deadline)
    signal.signal(signal.SIGTERM,deadline)
    signal.alarm(50)
    started = time.monotonic()
    source, csv_path = Path('boundary.json'), Path('subset-states.csv')
    data = json.loads(source.read_bytes())
    rows = {}
    with csv_path.open() as handle:
        for row in csv.DictReader(handle):
            cutoff, mask = int(row['M']),int(row['mask'])
            assert mask not in rows.setdefault(cutoff,{})
            rows[cutoff][mask] = row
    assert set(rows) == {r['M'] for r in data['results']}
    jobs = [(r,rows[r['M']]) for r in data['results']]
    workers = min(8,os.cpu_count() or 1,len(jobs))
    with mp.Pool(workers,initializer=initialize_worker) as pool:
        results = pool.map(inspect,jobs)
    first = next((r['failed_records'][0] for r in results if r['failures']),None)
    report = dict(question='Chosen repair pair contracts energy at parent and every remaining successor.',
        workers=workers,elapsed_seconds=time.monotonic()-started,
        comparisons=sum(r['comparisons'] for r in results),failures=sum(r['failures'] for r in results),
        failing_cutoffs=[r['M'] for r in results if r['failures']], first_failure=first,
        hashes={p.name:hashlib.sha256(p.read_bytes()).hexdigest() for p in (source,csv_path,Path(__file__))},
        results=results)
    Path('summary.json').write_text(json.dumps(report,indent=2)+'\n')
    print(json.dumps({k:v for k,v in report.items() if k != 'results'},indent=2))
    signal.alarm(0)
