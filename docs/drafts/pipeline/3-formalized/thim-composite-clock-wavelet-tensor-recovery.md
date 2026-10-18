# Composite valuation-clock wavelets and phase recovery

- **ID:** thim-composite-clock-wavelet-tensor-recovery
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Coprime modulus factors separate lag responses; transverse visibility clocks turn composite prime-chain differences into exact two-shell filters.

## Goal
Extend prime-power clock wavelets to every nonzero composite modulus, without a truncation-horizon restriction. Deliver both normalized and Ramanujan tensor identities, exact support, and canonical valuation recovery.

## Plan and gates
- [x] Read field motivation and traps; search current corpus before proving.
- [x] Prove multiplicativity and remove unnecessary lag-coprimality restriction.
- [x] Prove transverse factorization, visibility, and exact shell recovery.
- [x] Audit target with `lake --old env lean`, audit axioms, wire umbrella, regenerate index, run formal lint. Global lint failures outside the new leaf are listed below.
- [x] Persist crisp facts and boundaries in `logs/thim-composite-clock-knowledge.md`.

## Proof design
Write rho(q,h)=mu(q/gcd(q,h))/phi(q/gcd(q,h)). Coprime moduli split the gcd and its quotient. Multiplicativity of mu and phi yields multiplicativity of rho; multiplying by phi(q) yields the Ramanujan law. Cross-coprimality removes the other lag factor from each gcd.

For q=p^b u with p coprime to u and L, both lag responses at p^a L and p^(a-1)L have the same transverse factor. Subtraction therefore tensors the existing prime-power wavelet with that factor. At L=D(u), it is nonzero exactly when u is nonzero, since D(u)|D(u). Also D(u)|u, so p remains coprime to this canonical lag. The existing two-pole response table gives exact support b=a or b=a+1 for a>=1. Canonical decomposition q=p^(q.factorization p) ordCompl[p](q) transfers this to every q!=0.

## Boundaries
Primality, coprimality, positive scale, and nonzero modulus specify the mathematical domain requested by the problem; no conjectural arithmetic or analytic assumption is admitted. At a=0 the natural-subtraction difference is identically zero. At q=0 visibility fails. Normalized differences use rho(u,L), whereas unnormalized differences use c_u(L). No numerical experiments; README read-only. Serena rejects ignored Lean paths, so source reads and patch edits are required. `update_plan` is unavailable; this card persists the plan.

## Dependency-closed paper proof
For coprime q1,q2, gcd(q1 q2,h)=gcd(q1,h)gcd(q2,h). Each quotient ti=qi/gcd(qi,h) divides qi, so t1,t2 are coprime. Thus mu(t1 t2)=mu(t1)mu(t2) and phi(t1 t2)=phi(t1)phi(t2). Division gives rho(q1 q2,h)=rho(q1,h)rho(q2,h), including zero cases by totalized real division and the existing quotient formula. If gcd(q1,h2)=gcd(q2,h1)=1, the respective extra lag factors disappear from their gcds. Multiplying this identity by phi(q1 q2)=phi(q1)phi(q2) proves the Ramanujan version.

Apply the split-lag law with q1=p^b, q2=u, h1=p^a, h2=L, and again with exponent a-1. Coprimality follows from p coprime to u,L. Subtract the identities and factor the common transverse coefficient. For a>=1 the existing prime-power table says the longitudinal multiplier is p/(p-1) when b=a, -1/(p-1) when b=a+1, and zero otherwise. Both displayed nonzero values are nonzero because p is prime. The Ramanujan values are p^a,-p^a,0. Since D(u)|u and rho(u,D(u)),c_u(D(u)) are nonzero for u!=0, exact support is b=a or b=a+1.

For any q!=0 and prime p, put b=q.factorization(p), u=ordCompl[p](q). Canonical prime decomposition gives q=p^b u, u!=0, and gcd(p,u)=1. Substitution proves the exact valuation-shell statement for all nonzero q. Dividing the Ramanujan response by c_u(D(u)) removes transverse amplitude and sign, yielding +p^a,-p^a,0; positive and negative values distinguish the two adjacent shells.

The same mechanism extends to two independent lag differences: four split-lag identities and distributivity give the product of the two one-dimensional differences. This establishes an actual tensor identity without assuming a joint spectral reconstruction theorem.

## Lean certificate and scope audit
- Target: `formal/GaloisForLFunctions/TransHorizonIncidenceMechanics/CompositeClockWaveletTensorAndPhaseRecovery.lean` (25 theorems, 3 definitions; one connected contribution).
- All three requested deliverables are implemented. `sieveLagMultiplier_mul_split` and `ramanujanLagCoefficient_mul_split` give multiplicativity with weaker lag assumptions. Both `compositeClockWavelet*_factor` theorems give transverse factorization. The two `*_valuation_recovery` theorems detect the exact shells of every nonzero modulus at the canonical transverse clock.
- Stronger results: exact support at arbitrary transverse lags, calibrated signed amplitudes, composite Ramanujan dipole conservation, and a two-prime four-corner tensor filter.
- Original dependency and target sources passed direct `lake --old env lean` compilation; target diagnostics are empty. No full build was run.
- All 28 declarations audited by `#print axioms` in a scratch file: exactly `propext`, `Classical.choice`, `Quot.sound`; no added axioms or proof gaps. Scratch name checks and independent multiplicativity examples also passed.
- Umbrella import is unique; generated index includes every one of the 28 declarations. Source and artifact hashes are recorded in `logs/thim-composite-clock-audit.json`.
- `scripts/formal_tools.py lint` exited 1 for five foreign unwired RH leaves and existing package-root registration errors for `ArithmeticPositivityTheory.lean` and `TransHorizonIncidenceMechanics.lean`. It reported no finding in the new leaf. This is a leaf-level proof certificate, not a global-clean claim.
- Evidence: `logs/thim-composite-clock-lean-audit.txt`, `logs/thim-composite-clock-axioms.txt`, `logs/thim-composite-clock-index.txt`, `logs/thim-composite-clock-lint.txt`.
