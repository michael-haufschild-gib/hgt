import json
import multiprocessing as mp
import os
import time
from pathlib import Path
import mpmath as m

ZERO_STR = {}
for line in Path('zeros.tsv').read_text().splitlines():
    if line.strip() and not line.startswith('#'):
        n, value = line.split()[:2]
        ZERO_STR[int(n)] = value

def encode(z):
    return [m.nstr(m.re(z), m.mp.dps), m.nstr(m.im(z), m.mp.dps)]

def task(args):
    n, sigma, offset, dps = args
    start = time.monotonic()
    m.mp.dps = dps
    t = m.mpf(ZERO_STR[n])
    gap = m.mpf(ZERO_STR[n+1])-t
    rho = m.mpc(sigma, t+m.mpf(offset)*gap)
    arguments = [m.mpf('2.5')*rho-1, rho/2, 1-m.mpf('1.5')*rho]
    powers = [1, 2, 1]
    slopes = [m.mpf('2.5'), m.mpf('.5'), m.mpf('-1.5')]
    data = []
    log_a = -m.log(2)
    stripped = m.mpc(0)
    response = m.mpc(0)
    ar_response = m.mpc(0)
    heights = [(k,m.mpf(v)) for k,v in ZERO_STR.items()]
    for z, power, slope in zip(arguments, powers, slopes):
        value = m.zeta(z)
        dz = m.zeta(z, derivative=1)/value
        lgamma = -z/2*m.log(m.pi)+m.loggamma(z/2)
        dgamma = (m.digamma(z/2)-m.log(m.pi))/2
        log_a += power*(lgamma+m.log(value))
        stripped += power*m.log(value)
        response += power*slope*(dgamma+dz)
        ar_response += power*slope*dz
        k, h = min(heights, key=lambda kh: abs(kh[1]-abs(z.imag)))
        dist = abs(z-m.mpc('.5', m.sign(z.imag)*h))
        data.append(dict(s=encode(z), zeta=encode(value), zeta_logderiv=encode(dz),
                         loggamma_factor=encode(lgamma), nearest_zero_index=k,
                         nearest_zero_distance=m.nstr(dist,dps)))
    return dict(n=n,sigma=sigma,offset=offset,dps=dps, rho=encode(rho),
                gap=m.nstr(gap,dps),factors=data,log_A=encode(log_a),
                stripped_log=encode(stripped),response=encode(response),
                arithmetic_response=encode(ar_response),
                zero_residual=m.nstr(abs(m.zeta(m.mpc('.5',t))),dps),
                seconds=time.monotonic()-start)

if __name__ == '__main__':
    started = time.monotonic()
    count = 0
    with open('raw.jsonl','w',buffering=1) as out, mp.Pool(14) as pool:
        for indices in ([1], range(2,65)):
            jobs = [(n,s,o,50) for n in indices for s in ['.45','.5','.55']
                    for o in ['-.25','0','.25']]
            for row in pool.imap_unordered(task,jobs):
                out.write(json.dumps(row)+'\n')
                count += 1
            print('stage completed',count,'seconds',time.monotonic()-started,flush=True)
            if time.monotonic() > float(os.environ['CAMPAIGN_DEADLINE']): break
    Path('summary.json').write_text(json.dumps(dict(count=count,seconds=time.monotonic()-started),indent=2)+'\n')
