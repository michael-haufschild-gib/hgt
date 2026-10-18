# Exact translation stabilizers and gcd orbit projection

- **ID:** bvi-translation-stabilizers-gcd-projection
- **Stage:** 3-formalized
- **Type:** THEOREM (paper and Lean)
- **Contribution:** 008; verified total **8 / 250**. One connected package.
- **Source:** The field's successor-energy problem; existing literal affine divisor
  Fourier spectrum; contributions 002 and 004's finite multiples-coordinate inverse.
- **Statement:** Determine the full additive stabilizer of every finite real sieve
  signal and construct its translation-orbit projection explicitly on divisor weights.

## Goal and significance test

The field couples valuations to integer addition. Existing results describe unit
successor energy, prefix observation kernels and affine quadratic data. They do not
yet, in the inspected sources, identify exactly which additive translations fix a
signed sieve signal, or give the real coefficient transport induced by averaging
one translation orbit. An exact gcd transport, with its projection/approximation
law and full period classification, would turn prime-divisor incidence into a
constructive tool for additive resonance. Do not count a generic Fourier identity
or a renamed finite inverse as new work.

## Candidate package to audit

For every `N,h:ℕ`, real weight `c`, and positive `e≤N`, propose

`Γ_h c(e) = e * Σ_{1≤d≤N, gcd(d,h)=e} c(d)/d`,

with zero coefficients outside `[1,N]`. Check all of the following symbolically:

1. The existing Selberg multiples coordinates satisfy
   `Y(Γ_h c,q) = 1_{q|h} Y(c,q)`.
2. The actual signal of `Γ_h c` equals the complete finite average of
   `sieveSeq N c(k+j*h)` over a factorial period. This must use actual additive
   translation, not only an abstract diagonal mask.
3. Exact period classification: `Function.Periodic (sieveSeq N c) h` iff every
   active coefficient `c(d)`, `1≤d≤N`, has `d|h`. The true least positive period is
   therefore the lcm of active divisors, with empty support giving period one.
4. `Γ_h Γ_k = Γ_gcd(h,k)`, idempotence, harmonic-mean preservation and exact
   Selberg orthogonal decomposition. Audit the strongest useful best-approximation
   statement rather than stopping at the negative fact that cancellation cannot
   shorten the period.

The dependency-closed paper proof appears below. The arbitrary-phase observation
conjecture from 007 stays open and is not the target of this separate contribution.
No numerical experiments.

## Corpus evidence and plan

- Fully read the current field README, root/formal instructions and formal guide/map.
  The starting ledger contained seven completed contributions.
- Fully read `BiScaleUncertainty/AffineFourierCorrelation.lean` and
  `BiScaleUncertainty/DivisorSieveAffineSpectrum.lean`, including recovered output
  portions. They already prove literal DFT coordinates and affine divisibility
  product/sign-component classification. Reuse these facts; do not duplicate them.
- Deep query `shifted sieve covariance Ramanujan periodic kernel divisibility`:
  all 20 candidate statements, 20 source-argument statements, two proposed proof
  ideas and one ingredient set inspected. It completed without request errors,
  generation 1450116, but reported older coverage snapshot and unavailable semantic
  coverage. The mollifier proof ideas are irrelevant. The periodic Ramanujan/gcd
  ingredient set supplies background, not this projection or converse period law.
- `shifted ramanujan` lexical search has 21 hits, all inspected across both pages.
  Relevant complete-period moment module `TwoLagMomentCone` inspected below.
- `sieve period gcd projection orbit average` deep search completed; every returned
  candidate/source/proof-idea/ingredient section inspected, as recorded below.
- All corpus-search jobs are terminal.
- `update_plan` is unavailable; this card is the durable plan.

1. [x] Finish all corpus sections; inspect relevant existing period/moment machinery
   and verify whether the proposed projection/classification is already present.
2. [x] Close a dependency-closed paper proof and novelty/significance audit before Lean.
3. [x] Verify installed APIs in `/tmp`, then formalize the exact unconditional package.
4. [x] Named original-source check, all public axiom audits, wiring, exhaustive index,
   lint, artifact checks, ledger/memories and cleanup; contribution 008 assigned.

## Boundaries and no-go closure

Local Lean corpus only; no web, no external papers, no RH focus, no `hgtl7`, no
computations. Field README is read-only. All new field Lean belongs in its existing
directory. One owned foreground Lean process at a time; no full/umbrella builds.
Other agents' files remain untouched. Temporary prefix: `/tmp/bvi8-*`.

If any candidate statement fails, record its exact obstruction and strongest
positive survivor before retirement. No count for a bare negation, tautology or
direct reformulation of an already counted theorem.

## Completed corpus audit

All three search jobs listed above are terminal. All 21 shifted-Ramanujan hits and
all 15 `sieve periodic` lexical hits were inspected. The latter supplied the existing
generic support theorem `RHTower.Sieve.dft_eq_zero_of_periodic_nontrivial_phase`;
its full source module was read. Reuse it.

The gcd deep search completed at generation 1450120 with semantic coverage
unavailable; all 20 candidates, 20 source arguments and one ingredient set inspected.
The proposed lattice/periodic-point ingredient set does not establish this arithmetic
projection. `TwoLagSievePeriod` was read fully, and all declarations plus relevant
period-density source in `TwoLagMomentCone` inspected. Their complete two-lag moment
cone already exists and is not this contribution.

The progression-average deep search returned all 20 candidates and 20 source
arguments, all inspected; no proof ideas or ingredient sets. Partial generation
1450132, older coverage snapshot, unavailable semantic coverage, Qdrant timeout and
malformed local-model JSON. Useful hit: `cycleAverage_fracAtom` in
`CausalMobiusThetaUniformCycle`. Relevant source ranges 1–210 and all projection/
average declaration locations were inspected. It already proves the gcd formula
for fractional atoms on a divisible residue period. Do not count that formula as
new. The new target is the explicit original-weight transport, its full additive
stabilizer/least-period classification, and its exact Selberg approximation law.

## Dependency-closed paper proof

Put `P=N!>0`, `Y_c(q)=Σ[1,N;q|d]c(d)/d`, and `Q(c)=Σ[1,N]φ(q)Y_c(q)^2`.
Define `Γ_h c(e)` as above on `[1,N]`, zero outside. All results below are
unconditional for natural `N,h,k` and arbitrary real data; helper positivity and
divisibility conditions follow from membership or the factorial construction.

1. **Normalized mass transport.** For every real test function `F`,
   `Σ[1,N] Γ_h c(e)/e * F(e) = Σ[1,N] c(d)/d * F(gcd(d,h))`.
   Expand, interchange finite sums, and use the unique fibre label `gcd(d,h)`.
   For each positive `d≤N`, that label is positive and at most `d`, even when `h=0`.
   Taking `F(e)=1_{q|e}` gives `Y_Γ(q)=1_{q|h}Y_c(q)` for every natural `q`.
   Taking `q=1` preserves `H`; every nonzero output coefficient divides `h`.
2. **Literal orbit average.** Work temporarily on the same internal cycle `ZMod P`.
   The existing `AffineSieve.dft_residueSignal` gives `DFT(S_c)(r)=P Y_c(ord(r))`.
   For arbitrary finite-cycle `f`, set `A_h f(x)=P^{-1}Σ_j f(x+jh)`.
   Reindex `j` by `j+1` to show `A_h f(x+h)=A_h f(x)`.
   If `hr≠0`, its Fourier coefficient is zero by the existing period-support
   theorem and injectivity of the standard additive character.
   If `hr=0`, interchange the two finite sums and reindex `x` by `x+jh`;
   the character is unchanged, so `DFT(A_h f)(r)=DFT(f)(r)`.
   Since `hr=0` iff `ord(r)|h`, the Fourier coefficients match those of `S_Γ`.
   Injectivity of the finite DFT proves equality. Convert representatives back to
   natural indices to obtain the literal identity
   `sieveSeq N (Γ_h c) k = (Σ_{j=0}^{P-1} sieveSeq N c(k+j*h))/P`.
   No external character family or limiting argument enters this same-sequence average.
3. **Complete period converse.** If `S_c` is `h`-periodic, its cycle realization is
   fixed by `h`. At the frequency `P/q`, for each `1≤q≤N`, additive order is exactly
   `q`. Period-support therefore forces `Y_c(q)=0` whenever `q` does not divide `h`.
   Step 1 says `Y_Γ=Y_c` on the entire finite level. The already proved finite
   multiples-coordinate injectivity implies `Γ_h c=c` on `[1,N]`; output support
   then forces `c(d)=0` whenever `d` does not divide `h`.
   Conversely, each active divisor dividing `h` has an `h`-periodic indicator,
   so their signed sum is periodic. Thus cancellation cannot shorten the period.
   Finset lcm divisibility now gives the exact period set: multiples of the lcm
   of active divisors. That lcm is positive, including empty support (lcm one).
4. **Projection calculus.** Two masks multiply to `1_{q|gcd(h,k)}`. Finite coordinate
   injectivity and the built-in zero extension give exact function equality
   `Γ_h(Γ_k c)=Γ_gcd(h,k)c`. Idempotence follows, including `h=0`; `Γ_0` is level
   truncation and `Γ_1` is the constant harmonic mode. No raw coefficient truncation
   to divisors of `h` is substituted for the true gcd fibre sum.
5. **Pythagoras and unique best approximation.** For arbitrary `c,b`, the coordinate
   of `c-Γ_h b` splits into the complementary masks of `c-Γ_h c` and
   `Γ_h c-Γ_h b`. Their product is zero at each `q`, giving
   `Q(c-Γ_h b)=Q(c-Γ_h c)+Q(Γ_h c-Γ_h b)` exactly.
   The last form is nonnegative. It vanishes exactly when every coefficient of the
   two projected weights agrees within the level, because every positive totient
   is strictly positive and the finite coordinate inverse is injective. Every
   periodic weight is fixed within the level by `Γ_h` from step 3, so this is the
   unique best periodic approximation modulo invisible out-of-level weights.

These statements constitute one connected arithmetic projection/stabilizer result.
No theorem of generic finite Fourier analysis is claimed as novel; the contribution
is the exact original-weight gcd transport and its arithmetic/metric consequences.
Paper and local novelty audit closed. Contribution 008 counts the whole connected
package once. Generic Fourier averaging, the prior finite inverse, special strides,
and direct consequences of this projection calculus are not separate contributions.

## Verification

Source: `formal/GaloisForLFunctions/BezoutValuationIncidence/GcdOrbitProjectionAndExactTranslationPeriods.lean`.

- 468 lines; 31 named declarations: 15 public theorems, two public definitions,
  and 14 private declarations. Every public theorem is unconditional for all
  displayed natural parameters and arbitrary real weights. Empty levels, zero
  stride and unrestricted constant coefficients are included.
- Installed mathlib APIs verified in a scratch Lean file. The final named
  original-source check used `lake --old env lean -j 1` with explicit project
  `--root` and an isolated compiled dependency closure. It exited 0 with no
  diagnostics. No full or umbrella build was run.
- All 17 public declarations were axiom-audited; each closure is exactly
  `propext`, `Classical.choice`, `Quot.sound`. No proof debt or extra axiom.
  Raw audit: `logs/bvi-root-2026-10-18-gcd-projection-axioms.txt`.
- All 31 named declarations matched the complete lexical index by kind, name
  and source line. All 17 public entries matched the cache and generated API.
  The owned module is wired once. At the audit, all 19 field leaves were wired.
- Source SHA-256:
  `d9d550c950ecdc17b985f51e08ac59928139e88444ca80e1a36b9d7d78d303c5`.
  Installed `.olean` SHA-256:
  `4f59a1fed52b8b7fe5dd9a1012296e730ff21e1a63b83c21c0bee86bfb30541c`.
  The 640184-byte artifact was installed atomically, with matching hash and a
  timestamp newer than the unchanged source.
- Global lint exited 1 on two unrelated BiScaleUncertainty umbrella omissions:
  `EulerPoissonChiralDriftAndPrimeShiftRigidity` and `FactorialMuntzZeroReadout`.
  All 381 warnings concern other large Lean files. No owned-module or proof-debt
  finding. This is not a repository-wide passing lint claim.
- Guarded cleanup exited 0: all 26 owned temporary paths removed; source,
  installed artifact and durable axiom log hashes remained unchanged.
  All owned jobs are terminal. The field README was not edited.

## Exact new insight and limits

Additive orbit averaging transports the original normalized divisor mass through
`d ↦ gcd(d,h)`. It simultaneously gives the entire arithmetic stabilizer and the
unique Selberg best approximation. In particular, signed cancellation cannot hide
an active divisor from the exact period. The proof uses the actual sequence on
its internal factorial cycle and does not infer analytic cancellation from an
external averaging family. No asymptotic bound or arbitrary-phase observation
horizon follows from this package. The latter remains the uncounted open extension
of contribution 007.
