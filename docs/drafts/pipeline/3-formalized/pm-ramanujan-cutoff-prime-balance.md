# Exact signed Ramanujan balance at a natural cutoff

- **ID:** pm-ramanujan-cutoff-prime-balance
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/pm-paired-cutoff-gram-budget.md; route PM
- **Statement:** The actual signed prime factor has an exact finite-cutoff mean and quadratic decomposition retaining source changes and the cutoff band.

## Goal

Identify the complete signed term that must be bounded in the natural-cutoff
transfer. This is a source identity, not an L2 admission theorem or RH proof.
The actual Mobius-prefix input depends on the averaging index; it is not
permitted to use uncut orthogonality on that input.

## Gates

- [x] 0 → 1: literal Ramanujan weights and natural cutoff; no added analytic premise.
- [x] 1 → 2: complete finite paper proof below, [PROVED HERE].
- [x] 2 → 3: targeted build, direct-file audit, standard-axiom audit, umbrella wiring.
- [ ] 3 → 4: standalone publication audit.

## Statement and paper proof

Let epsilon>0, p prime, b=p^(1+epsilon)-1>1, w(n)=|a_epsilon(n)|, and
psi(n)=1 for p|n and -1/b otherwise. Write E_Q(H)=sum_(0<=n<=Q)w(n)H(n),
B(H)=sum_(Q/p<n<=Q,p does not divide n)w(n)H(n), and

`J(H)=sum_(n<=Q/p,p does not divide n)w(n)*(H(p*n)-H(n))-B(H)`.

For every real sequence H, [PROVED HERE]

`E_Q(psi*H)=J(H)/b`.

Reindex the multiples of p in E_Q by n=p*m. The actual weight recursion
is w(p*m)=0 if p|m and w(m)/b otherwise. Thus the multiple contribution
is sum_(m<=Q/p,p does not divide m)w(m)H(p*m)/b. Subtracting the nonmultiple
contribution gives the displayed identity after splitting its natural band.
All sums are finite; no convergence or invariance assumption is needed.

The pointwise identity psi^2=1/b+(b-1)*psi/b now gives, for arbitrary f,g,

`E_Q[(f+psi*g)^2]
 = E_Q(f^2)+E_Q(g^2)/b+2*J(f*g)/b+(b-1)*J(g^2)/b^2`.

If H(p*n)=H(n), then J(H)=-B(H). In particular E_Q(psi*H^2)<=0.
Products of the other prime factors are p-invariant because multiplication
by p does not change divisibility by a distinct prime. This proves the
nonpositive truncated one-prime cross covariance for the actual prime
products as a concrete corollary.

## Lean certificate

Module: `formal/GaloisForLFunctions/RHTower/PMRamanujanCutoffPrimeBalance.lean`.
Four definitions and seven theorems are exported. Main declarations:

- `pmRamanujanPrimeFeature_cutoff_mean`
- `pmRamanujanPrimeFeature_cutoff_quadratic`
- `pmRamanujanPrimeFeature_cutoff_invariant`
- `pmRamanujanPrimeFeature_cutoff_invariant_square_nonpos`
- `pmRamanujanPrimeFeature_cutoff_product_cross_nonpos`

The complement and prime-product invariance identities also passed the audit.
All eleven exports use only `propext`, `Classical.choice`, and `Quot.sound`.
The final targeted `lake --old build` built only this new leaf. The final
`lake env lean GaloisForLFunctions/RHTower/PMRamanujanCutoffPrimeBalance.lean`
exited zero without diagnostics. The leaf is imported by `RHTower.lean`.
No numerical experiments, added axioms, proof holes, heartbeat changes or
full umbrella builds were used.

## Remaining hard problem

For H(m)=F_(Q/(m*r))(r*t), H(p*m)-H(m) is an actual Mobius prefix band.
Its full signed physical energy, combined across primes and cofactors, is
not bounded here. The uniform natural-denominator energy budget and cofinal
small-damping admission remain open. Auxiliary covariance signs do not
supply this estimate.

## Log

- 2026-10-02 — Formalized and audited. Global formal lint exits one on
  fourteen unrelated unwired leaves; no error names this module. The
  active research card records the exact failures and next producer target.
