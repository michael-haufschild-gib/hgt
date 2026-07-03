# R1 + R2a step 1 — results (2026-07-03, pod 157.157.221.30:28997, engine.py, mp.dps=30)

## R1 — engine validation (VALIDATION run, campaign §R1)

Pre-registered: winding on ζ boxes [−1,2]×[T,T+5] must equal mp.nzeros(T+5)−mp.nzeros(T);
ξ(2)=π/6; ξ FE residual ~0.

```
selfcheck_xi: xi2_vs_pi_over_6 = 9.86e-32, xi_fe_residual = 9.15e-32  PASS
T=10 : w=1 (raw 1.0, ok, 100 evals, 0 unresolved)  expected 1  MATCH
T=50 : w=1                                          expected 1  MATCH
T=100: w=2                                          expected 2  MATCH
T=500: w=4                                          expected 4  MATCH
```

**Verdict: engine trusted.** Adaptive argument tracking clean (no unresolved segments).

## R2a step 1 — banked D–H zero, parity certificate (campaign §R2a)

Pre-registered: winding +1 (odd) at the ledger's banked zero
0.808517182456637386 + 85.6993484853775922i.

```
selfcheck_dh: kappa = 0.28407904384041227, banked_zero_residual = 3.53e-17  PASS
  (18-digit ledger zero reproduced by the implementation — validates both the
   Hurwitz-decomposition L-functions and the kappa constant)
dh-banked: box 0.7885..0.8285 x 85.6793..85.7193, w = +1 (raw 1.0, ok, 84 evals)
  parity_odd = true
```

**Verdict: encouragement — prediction confirmed.** The fake family (FE, no Euler positivity)
realizes a level-1 (odd) defect: the parity-ladder invariant RH_2 is non-vacuous and
discriminating in the family. Seed sweep (R2a step 2) launched over t ∈ [2,102), then [102,202).

Raw outputs: validate + dh-banked JSON in this directory's engine runs (task logs);
sweep outputs archived as sweep-*.out.
