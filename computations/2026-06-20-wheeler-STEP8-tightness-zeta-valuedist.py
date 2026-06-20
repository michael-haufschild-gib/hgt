"""
STEP 8 — MINIMAL Levenshtein edit of the tightness node test, to run for an HT function
and test a VALUE RELATION (distribution of values), not a dependency/deduction.
Harness (W1, uniform-tail loop, verdict) kept verbatim from the node test; ONLY the family
generators changed: family {mu_sigma} = empirical law of log|zeta(sigma+it)| over a t-grid,
indexed by sigma DESCENDING to 1/2. Value relation tested: is the zeta value-distribution
family TIGHT as sigma -> 1/2 (Prokhorov), or does its spread blow up?
"""
import numpy as np
import mpmath as mp
mp.mp.dps = 15

def W1(a, b):
    a = np.sort(a); b = np.sort(b)
    qa = np.interp(np.linspace(0,1,400), np.linspace(0,1,len(a)), a)
    qb = np.interp(np.linspace(0,1,400), np.linspace(0,1,len(b)), b)
    return np.mean(np.abs(qa-qb))

tgrid = np.linspace(10, 400, 600)
def logabs_zeta(sigma):
    return np.array([float(mp.log(abs(mp.zeta(mp.mpf(sigma)+1j*mp.mpf(t))))) for t in tgrid])

# family indexed by sigma descending toward 1/2 (the special line)
sigmas = [1.5, 1.0, 0.75, 0.6, 0.52]
print("="*74)
print(" STEP8 (minimal edit): tightness of zeta value-distribution family {mu_sigma}, sigma->1/2")
print("="*74)
samples = {s: logabs_zeta(s) for s in sigmas}
for s in sigmas:
    xs = samples[s]
    tails = []
    for R in (1, 3, 8):
        tails.append((R, np.mean(np.abs(xs - np.median(xs))>R)))   # tail of CENTERED dist (spread)
    std = np.std(xs)
    print(f"\n sigma={s}: std(log|zeta|)={std:.3f}")
    print(f"   centered tail sup mu(|x-med|>R): " + ", ".join(f"R={R}:{T:.3f}" for R,T in tails))
# subsequential: W1 between consecutive sigma (does the family converge or spread?)
print("\n W1 between consecutive sigma (family Cauchy => tight limit; growing => NOT tight):")
for i in range(len(sigmas)-1):
    w = W1(samples[sigmas[i]], samples[sigmas[i+1]])
    print(f"   W1(mu_{sigmas[i]}, mu_{sigmas[i+1]}) = {w:.3f}")
stds = [np.std(samples[s]) for s in sigmas]
print(f"\n std trend as sigma->1/2: {[f'{x:.3f}' for x in stds]}")
print(" VERDICT: read whether the value-distribution family stays tight (bounded std) or its")
print(" spread blows up as sigma->1/2 (loss of tightness at the special line).")
