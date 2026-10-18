# CTF: signed origin-tail cancellation

Status: in progress. Goal remains one significant unconditional contribution that removes a hard obstacle on the CTF route to RH.

## Task contract

- Use current Lean corpus and its research search; no external search, novelty audit, numerical experiments, or historical research Markdown.
- Frontier map is read-only. Preserve concurrent changes.
- Complete a dependency-closed mathematical proof before formalization. No new axioms, unproved analytic inputs, computational certificates, or heartbeat increases.
- Audit finished leaf modules with `lake --old env lean`; import new leaves into their umbrella without building the umbrella. Run formal lint.

## Plan

1. Establish exact current CTF frontier from Lean source and corpus searches.
2. Conjecture, attack, and revise a source-side cancellation mechanism. Record failures and positive survivors without presenting a receiver as a producer.
3. Prove and formalize a qualifying theorem, then audit its actual contribution to the full route.

## Verified starting evidence

- `ChronologicalRiemannEquivalence`: bounded chronological approximation is already equivalent to RH.
- `ChronologicalDualSamplingCriterion`: dual sampling bound is already equivalent to RH; exchanging pointwise Möbius inversion with arbitrary Hilbert pairing is the missing analytic step.
- `ChronologicalGrowingMomentSource`: unit-bounded rows with a half-length Möbius prefix, zero harmonic charge, and increasing exact moments already exist.
- `ChronologicalGrowingSignedProjection`: their remaining logarithmic boundary window retains signed Mertens and harmonic channels.
- `SignedLcmFractionalDefectAndCompleteFibreCollapse`: exact finite mean square is Selberg diagonal minus signed LCM defect; complete Möbius fibres collapse. Cofinal signed control is not supplied.

## Current search

Initial `research "CTF" --exclude-module Mathlib --json` finished: no partial result; compiler metadata mostly pending/stale, so hits are leads rather than validation.

Deep whole-corpus mechanism query running; result destination `/tmp/hgt_ctf_source_search.json`.

## Completion gate

Not achieved. No new theorem proved or claimed. Convergence of a bounded source, or a substantial independently proved removal of a necessary obstruction, must be demonstrated rather than assumed.

## 2026-10-18: coefficient-mass coercivity — paper proof

Status: dependency-closed paper proof; Lean verification pending. This is an
auxiliary rigidity result, not yet the requested significant CTF advance.

Write `w(n)=μ(n)^2/φ(n)`, `F(n)=n/φ(n)`, and
`Q_N(c)=Σ_{e≤N} φ(e) Y_e²`, where `Y_e=Σ_{e|d≤N} c_d/d`.
For every real finite row, conjectured and now proved on paper:

`(Σ_{d≤N}|c_d|)² ≤ 16384 N² Q_N(c)`.

Proof, including the uniform arithmetic constant:

1. Existing divisor identity: `F(n)=Σ_{d|n}w(d)`. Existing bounds:
   `0≤w≤1`, `Σ_{d≤N}w(d)/d≤4`, `Σ_{d≤N}w(d)/φ(d)≤16`.
2. Put `b(n)=w(n)/φ(n)`. Squarefree multiplicativity and vanishing on
   nonsquarefree products imply `b(dm)≤b(d)b(m)` for all positive `d,m`.
   Divisor swapping gives
   `Σ_{n≤N} b(n)F(n) = Σ_{dm≤N}b(dm)w(d)
    ≤ (Σ_{d≤N}b(d))(Σ_{m≤N}b(m)) ≤256`.
3. Totient supermultiplicativity gives `F(dm)≤F(d)F(m)`.
   If `Σ_{n≤X}F(n)^k≤C X`, divisor swapping gives
   `Σ_{n≤N}F(n)^(k+1) ≤ C N Σ_{d≤N}w(d)F(d)^k/d`.
   Starting at `k=0` produces `ΣF≤4N`, `ΣF²≤64N`, `ΣF³≤16384N`.
4. Existing `σ(n)/n≤F(n)` implies
   `Σ_{n≤N}σ(n)²/φ(n) ≤ Σ_{n≤N}n F(n)³≤16384N²`.
5. Exact finite multiples inversion gives
   `c_d=d Σ_{m≤N/d}μ(m)Y_{dm}`. Triangle inequality and divisor swapping
   give `Σ|c_d|≤Σ_{e≤N}σ(e)|Y_e|`. Weighted Cauchy then gives the claim.

Positive survivor: small Selberg energy forces small mean absolute coefficient
mass, uniformly over cutoff and without a coefficient-budget assumption.
An exact Möbius prefix of fixed positive relative length therefore cannot have
vanishing Selberg energy, using the corpus squarefree-density theorem.
This distinguishes the existing growing-moment half-prefix source from the
Selberg-small-energy strategy. It does not obstruct small chronological L²
error by itself: signed fractional defects still matter.

Additional audited candidates:
- Standard Selberg optimizer and unit coefficient bound: already in corpus.
- Centering at index 1: routine bridge, not significant.
- Centering at the squareful index 4: since the standard Selberg optimizer
  vanishes there, subtracting `4/G_N` preserves the unit box for `G_N≥4`,
  removes harmonic charge, preserves coefficient 1, and costs `4/G_N²` in
  Selberg energy by the optimizer's normal equations. This is a useful source
  normalization, not an origin-window estimate; not claimed as goal completion.
- Oscillatory bounded-tail compactness: no new arithmetic source estimate yet.

Search audit: source, divisor, optimizer, compactness, prefix-mass, and totient
moment searches completed. Source/divisor deep searches reported partial
coverage; optimizer, compactness, prefix-mass, and totient searches completed
without partial status. Retrieved declarations remain source-only leads until
checked against this Lean toolchain. No external search or novelty audit used.

### Stronger finite consequences and a sharp-norm conjecture

The corpus already proves `#{squarefree n≤M}≥M/4` for every cutoff in
`RHTower/SquarefreeLowerDensity.lean`. Thus the preceding mass estimate gives,
without any large-cutoff assumption,
`M²≤262144 N² Q_N(c)` whenever `c_d=μ(d)` for `d≤M≤N`.
For a half-prefix and `N≥2`, it gives `Q_N(c)≥1/2359296`.
This is a dependency-closed strengthening of the same paper proof.

A sharper positive survivor has emerged. Put
`P(e)=Σ_{d|e} d |μ(e/d)|` and `A_N=Σ_{e≤N}P(e)²/φ(e)`.
The exact best constant in `(Σ|c_d|)²≤A_N Q_N(c)` should be `A_N`:
finite inversion gives the upper bound, and the Liouville-aligned coordinates
`Y_e=λ(e)P(e)/φ(e)` attain it. Indeed
`μ(m)λ(dm)=λ(d)μ(m)²`, so each inverse row has a common sign and
both triangle inequality and weighted Cauchy are equalities. The resulting
row has total absolute mass `A_N` and Selberg energy `A_N`.
This sharp-norm statement is proved on paper by those identities; corpus
applicability and Lean verification remain pending. No claim about its
sufficiency for the main CTF goal is made.
