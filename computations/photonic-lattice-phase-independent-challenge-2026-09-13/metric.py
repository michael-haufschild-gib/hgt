"""Finite-energy optical lattice geometry. No zeta data or zeta evaluation.

All objects refer to an explicitly chosen metaplectic lift of a local lattice
chart. Code-projector overlaps discard logical basis choice but not physical
rotation. The separately reported Schur complement is an additional reader.
"""
import json
import math
import os
import time
from pathlib import Path
from concurrent.futures import ProcessPoolExecutor, as_completed
import mpmath as mp


def budget():
    if time.monotonic() > float(os.environ.get('CAMPAIGN_DEADLINE', 'inf')):
        raise TimeoutError('whole-family cooperative deadline')


def save(name, data):
    p = Path(name)
    q = p.with_suffix(p.suffix + '.tmp')
    q.write_text(json.dumps(data, indent=2) + '\n')
    q.replace(p)


def enc(z):
    return [str(mp.re(z)), str(mp.im(z))]


def matenc(m):
    return [[enc(m[i, j]) for j in range(m.cols)] for i in range(m.rows)]


class Code:
    phase_a = 0
    phase_b = 0
    def __init__(self, x, y, theta, delta, dim, nmax):
        self.dim, self.nmax = dim, nmax
        self.phase_a, self.phase_b = mp.mpf(type(self).phase_a), mp.mpf(type(self).phase_b)
        self.L = mp.sqrt(2 * mp.pi * dim)
        sy = mp.sqrt(y)
        R = mp.matrix([[mp.cos(theta), mp.sin(theta)],
                       [-mp.sin(theta), mp.cos(theta)]])
        M = R * mp.matrix([[1 / sy, x / sy], [0, sy]])
        # Imaginary-time harmonic oscillator matrix: exp(-delta H0).
        C = mp.matrix([[mp.cosh(delta), -1j * mp.sinh(delta)],
                       [1j * mp.sinh(delta), mp.cosh(delta)]])
        A = C * M
        a, b, d = A[0, 0], A[0, 1], A[1, 1]
        self.pref = 1 / mp.sqrt(2 * mp.pi * 1j * b)
        self.u = 1j * d / (2 * b)
        self.v = -1j / b
        self.w = 1j * a / (2 * b)

    def wave(self, q, j):
        return self.pref * mp.fsum(
            mp.exp(2j*mp.pi*self.phase_b*n + self.u * q*q + self.v * self.L * (n + (mp.mpf(j)+self.phase_a)/self.dim) * q
                   + self.w * self.L**2 * (n + (mp.mpf(j)+self.phase_a)/self.dim)**2)
            for n in range(-self.nmax, self.nmax + 1))


def gaussian_sum(A, B, C, shift, N):
    """Sum exp(A t^2+B t+C), t=n+shift, using quadratic recurrence."""
    t = -N + shift
    term = mp.exp(A*t*t + B*t + C)
    ratio = mp.exp(A*(2*t+1)+B)
    ratio_step = mp.exp(2*A)
    acc = term
    for _ in range(2*N):
        term *= ratio
        ratio *= ratio_step
        acc += term
    return acc


def overlap(a, b, method='recurrence'):
    # Integral of two Gaussian kernels, followed by both comb sums.
    U = mp.conj(a.u) + b.u
    assert mp.re(U) < 0
    al = mp.conj(a.w) - mp.conj(a.v)**2 / (4*U)
    be = b.w - b.v**2 / (4*U)
    ga = -mp.conj(a.v)*b.v / (2*U)
    pref = mp.conj(a.pref)*b.pref*mp.sqrt(mp.pi/(-U))
    out = mp.matrix(a.dim, b.dim)
    for j in range(a.dim):
        budget()
        for k in range(b.dim):
            terms = []
            for n in range(-a.nmax, a.nmax+1):
                r = a.L*(n+(mp.mpf(j)+a.phase_a)/a.dim)
                A, B, C = be*b.L**2, ga*r*b.L, al*r*r
                shift = (mp.mpf(k)+b.phase_a)/b.dim
                B += 2j*mp.pi*b.phase_b
                C -= 2j*mp.pi*(a.phase_b*n+b.phase_b*shift)
                if method == 'theta':
                    # Independent inner comb sum; no finite m truncation.
                    val = mp.exp(A*shift**2+B*shift+C)*mp.jtheta(
                        3, (2*A*shift+B)/(2j), mp.exp(A))
                elif method == 'direct':
                    val = mp.fsum(mp.exp(A*(m+shift)**2+B*(m+shift)+C)
                                  for m in range(-b.nmax,b.nmax+1))
                else:
                    val = gaussian_sum(A, B, C, shift, b.nmax)
                terms.append(val)
            out[j,k] = pref*mp.fsum(terms)
    return out


def trace(m):
    return sum(m[i,i] for i in range(m.rows))


def projector_metric(job):
    dim = int(job.get('dim', 2))
    x, y, delta = [mp.mpf(job[k]) for k in ['x','y','delta']]
    h = mp.mpf(job.get('h','0.00001'))
    N = int(job.get('N', 16))
    method = job.get('method', 'recurrence')
    coords = [x, y, mp.mpf('0')]
    points = []
    labels = []
    for i in range(3):
        for sign in [-1,1]:
            z = coords.copy(); z[i] += sign*h
            points.append(Code(*z, delta, dim, N))
            labels.append((i,sign))
    grams = [overlap(a,a,method) for a in points]
    invs = [G**-1 for G in grams]
    tab = {}
    def pp(a,b):
        if a == b:
            return mp.mpf(dim)
        key = tuple(sorted((a,b)))
        if key not in tab:
            X = overlap(points[key[0]],points[key[1]],method)
            z = trace(invs[key[0]]*X*invs[key[1]]*X.H)
            assert abs(mp.im(z)) < mp.mpf('1e-25')
            tab[key] = mp.re(z)
        return tab[key]
    g = mp.matrix(3,3)
    for i in range(3):
        for j in range(i,3):
            g[i,j] = g[j,i] = (pp(2*i+1,2*j+1)-pp(2*i+1,2*j)
                                -pp(2*i,2*j+1)+pp(2*i,2*j))/(8*h*h)
    Q = mp.matrix(2,2)
    for i in range(2):
        for j in range(2):
            Q[i,j] = g[i,j]-g[i,2]*g[2,j]/g[2,2]
    eig = mp.eigsy(g, eigvals_only=True)
    return dict(metric=matenc(g), rotation_quotient=matenc(Q),
                eigenvalues=[str(v) for v in eig],
                quotient_ratio=str(Q[0,0]/Q[1,1]),
                quotient_cross=str(Q[0,1]/mp.sqrt(Q[0,0]*Q[1,1])),
                quotient_hyperbolic_scale=str(y*y*mp.sqrt(mp.det(Q))),
                full_ratio=str(g[0,0]/g[1,1]),
                rotation_norm=str(g[2,2]),
                grams=[matenc(G) for G in grams],
                projector_overlaps={str(k):str(v) for k,v in tab.items()},
                metric_positive=bool(min(eig)>0))


def work(job):
    start=time.monotonic(); mp.mp.dps=int(job.get('dps',50))
    row=dict(job=job)
    try:
        row.update(projector_metric(job)); row['status']='ok'
    except Exception as e:
        row.update(status='error',error=repr(e))
    row['seconds']=time.monotonic()-start
    save('case-'+str(job['id'])+'.json',row)
    return row


if __name__ == '__main__':
    jobs=json.loads(Path('jobs.json').read_text())
    start=time.monotonic(); rows=[]
    # First case is a sizing pilot, inside the same whole-family guard.
    first=work(jobs[0]);rows.append(first)
    save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start))
    print('pilot',first['status'],first['seconds'],flush=True)
    if first['status']!='ok' or first['seconds']>75:
        raise SystemExit('pilot failed or exceeded sizing allowance; no larger scan')
    with ProcessPoolExecutor(max_workers=14) as ex:
        for f in as_completed([ex.submit(work,j) for j in jobs[1:]]):
            row=f.result();rows.append(row)
            save('summary.json',dict(planned=len(jobs),rows=rows,seconds=time.monotonic()-start))
            print(row['job']['id'],row['status'],row.get('quotient_ratio'),row['seconds'],flush=True)
