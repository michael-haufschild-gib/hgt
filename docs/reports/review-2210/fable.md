# Review 2210 — Fable: is there a way around the walls, and what field would supply the tools?

Date: 2026-10-23. Author: Claude Fable 5.1 (reviewer). Working log: `logs/fable-review-2210.md`.

Scope of evidence. Read in full: `docs/reports/rh-current-frontier-map.md`, `docs/reports/rh-killed-routes.md`,
`docs/reports/review-2110/route-unification-ledger.md`, `docs/reports/review-2210/hard-obstacles.md`,
`docs/reports/review-2210/walls-ledger.md`, and the nine programme READMEs (APT, BiScale, THIM, BVI, ACT, SRT, AIP,
ACCE, SSIC). No other markdown was read. Every "proved" claim below was checked against the Lean corpus with
`scripts/formal_tools.py research` (twenty queries, listed in the log); the declaration names cited are the ones the
search surfaced. The external audit (arXiv, 2026) is listed in §3. No Lean was written and nothing was built.

---

## 0. The answer in one page

**Q1 (new mechanism around the walls).** Not of the kind the corpus has been looking for. The walls are not
obstructions to particular methods; they are closure theorems about *types of statement*. The corpus has proved,
in Lean, that any input which is (i) invariant under a single-Euler-factor deformation, (ii) a function of finitely
many values Λ(n), (iii) an average over a family or over heights, or (iv) reflection-even, cannot imply RH. Every
candidate mechanism I could formulate — including three that are live in the 2026 literature (inertia of finite
compressions, convergence of extremal zeros of finite Euler products, Landau–Widom decay of the ground energy) — is
either a *receiver* (RH-equivalent, produces nothing) or reduces to the same scalar the corpus has already isolated:
the smeared self-pairing of the prime comb against a single test's spectral measure beyond the diagonal threshold.
Section 4 gives each candidate a verdict. The only genuine opening is a change of *type*: from estimates on
truncations to exact structure on an object in which the infinite prime tail, with its sign, is primitive. That is
Q2.

**Q2 (the field).** The missing field is an intersection theory of the "scaling surface" of ℤ whose Hodge index
theorem *is* Weil positivity. Weil's proof of RH for curves has five ingredients: a surface C×C, an intersection
pairing, the fibre classes H and V spanning the unique positive plane, the Frobenius graph Γ with an exact
self-intersection (adjunction), and a dimension count (Riemann–Roch) that forces the Hodge index theorem. The corpus
has, without naming it, built the arithmetic analogues of three of the five (§5.2 gives the dictionary: the pole plane
e^{±u/2} with its Lorentz form, the prime comb as Γ, the theta span as the kernel) and has proved that the remaining
two — the adjunction formula for the smeared Frobenius self-intersection, and a section count — cannot be replaced by
any estimate. The field's objects must be *tail-intrinsic* (defined on all of ℕ, never as limits of truncations),
*unitary by definition* (so that Euler deformations and the shifted pair are not objects of the theory), *Bézout-
carrying* (so that Beurling systems are not objects of the theory), and *signed* (so that Liouville twists are not).
Its central theorem to aim at is an **arithmetic adjunction formula**: an exact, zero-free evaluation of the regularized
self-pairing of the prime comb against the archimedean collar, with a remainder that is positive by construction.
Sections 5.3–5.9 give the questions, viewpoint, objects, language, principles, success criteria and a ranked list of
research topics. Section 6 says how the proposal could be wrong.

---

## 1. What the corpus has established (compressed, with Lean anchors)

The documents are long; the following is the load-bearing residue, each item confirmed by search.

**1.1 RH is one number, read as an exponent.** Δ = sup|Re ρ − 1/2|. RH ⇔ Δ = 0. Every route is a graded unit
(width, aperture, side, damping, quantifier gap) and all are unified by the ground-energy path A ↦ μ(A), the lowest
eigenvalue of the restricted Weil form at aperture A (`ccmRestrictedWeilGroundEnergy`). Proved: μ is antitone and
continuous; μ ≥ 1/5000 through A ≤ 3/10 (full sector) and the odd sector is positive through 181/500; under ¬RH there
is a contact aperture A* ≥ 3/10 with μ(A*) = 0 and μ < 0 beyond (`ccmRestrictedWeilGroundEnergy_contact_eq_zero`,
`ccmRestrictedWeilGroundEnergy_neg_of_contact_lt`); the fall rate is the width whenever off-line depth mass does not
cluster per unit window, and the unconditional per-window bound is 40·Δ²·log(180T)
(`theWidthIsTheGroundEnergyRateWhenTheDepthMassDoesNotCluster`).

**1.2 Positivity singles out Λ.** `weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt`: a weight λ is fully
Weil-positive iff RH holds and λ = Λ. Λ is an extreme point (`eq_zero_of_weilPositiveFull_add_of_sub`). This is the
corpus's rigidity law: there is no slack anywhere in the cone, so no "approximate" positivity argument can exist.

**1.3 The pole is a rank-one (odd) or rank-two (full) subtraction from a positive energy.**
`odd_sourceEnergy_eq_weilForm_add_two_sourcePair_oddPolarVectorAt_sq`: on the odd sector,
sourceEnergy(q) = weilForm(q) + 2⟨q, tanh_L⟩². Equivalently RH ⇔ sup_q 2⟨q,tanh_L⟩²/sourceEnergy(q) ≤ 1 at every L:
the dual norm of the pole functional in the source norm is at most 1/√2. The same shape appears as the BiScale 2×2
pole criterion, SRT's rank-two prime–Gamma inequality on e^{±u/2}, ACCE's "one negative square, the pole plane", and
the AIP ledger `fullZeroForm_eq_incidenceLedger` (pool + crossing + Σ evenGain − Σ oddCost + remainder − pole).

**1.4 The whole obstruction is one scalar.** AIP mechanism 50 reduces the exponential cost of the odd sector to the
mean square of Σ_p w_p p^{−iξ} against the test's spectral measure; mechanism 51 shows its sign hypothesis fails
exactly on multiplicatively aligned bi-lattice trains (`biLatticeTrain`, with `logPrime_pair_independent`). SRT
mechanism 37 says the same at the level of the pole: "finitely many primes below e^{2a} must cancel the pole, which is
the whole infinite prime tail". ACCE says it as a debt: the damping core must cancel exactly log log T, signed.

**1.5 The four invariances (closure law).** Each is a theorem.
- Euler deformation: `deformedDivisorCoeff`, `deformation_factor_ne_zero_at_reflection` (Estermann): a single
  Euler factor can be deformed, preserving functional equation and growth, planting a vertical lattice of off-line
  zeros. Only two facts in the corpus break under this deformation: cone rigidity (1.2) and the temperedness gate of
  APT (Σ Λ(r) r^{−1−ε(L)} ≤ 6(3 + log L), which diverges for ζ(s−a)ζ(s+a)).
- Finite windows: `exists_offLine_lattice_windowed_nonneg` — for every depth δ ≤ 1/2 and every aperture r there is a
  zero configuration of depth δ that is nonnegative on all window tests of aperture r. Readings at aperture r factor
  through {λ(n) : log n < 2r} (KR-APW).
- Beurling: `regular_integers_do_not_constrain_zeros` — for every β ∈ (1/2,1) and γ ≠ 0 there is a regular Beurling
  density whose zeta vanishes at β + iγ. Every multiplicative, spectral or explicit-formula identity holds verbatim
  for such systems.
- Reflection parity: every unconditional identity is pair-even in the depth (CANNOT-182r); reflection-even readers
  cannot see orientation (CANNOT-399).

**1.6 Calibration.** `fqCenteredPrefix_eq`: over F_q[T] the centred prefix is exactly q^{−ε} and the continuation
budget is zero. The number-field difficulty is the absence of exact cancellation beyond degree one.

**1.7 Metrology.** SSIC: a sign at one aperture carries no depth; two band magnitudes carry all of it
(`depth_determined_by_two_bands`, `depthFromBands`); bounded-aperture certificates have width limit 1/2; the rate
reading is faithful but is a receiver. Landau–Widom-type near-degeneracy is unconditional:
`zeta_weil_near_radical_dimension_smooth` exhibits a subspace of dimension ≥ e^{2L−2}/20 on which |W(f,f)| ≤
exp(−e^{2L−2})‖f‖².

---

## 2. The structural diagnosis

Put 1.1–1.7 together. Every route ends at an RH-equivalent receiver. The receiver is always a one-sided bound at the
exponent Δ on a quantity built from Λ or μ(n) through a window of logarithmic length ~T. The proven unconditional
bound always has the exponent of the trivial ℓ¹ bound (1/2 for lags and damping, 1 for deficits) or Vinogradov–Korobov
strength. The missing input is never an identity. It is a signed cancellation of the prime source against itself
across multiplicatively unrelated scales — cross-scale, growing modulus, trans-horizon, cross-nodal, off-diagonal —
read deterministically, one test at a time, at square-root precision.

What is absent is not a method but an **object**: the prime tail as a whole, with its sign. The corpus has exact
finite data (every window), exact limits (every identity) and exact calibration (F_q[T]), but no object that
represents log ζ(s) − Σ_{p ≤ y} p^{−s} at a single s, or "zeros beyond every finite horizon", other than as a limit
of truncations whose constants depend on the truncation. The four invariances in 1.5 are precisely the four ways a
truncation-defined object forgets what distinguishes ζ: it forgets unitarity at one prime, it forgets the tail, it
forgets the single height, it forgets orientation.

---

## 3. External state of the art (2026) against the walls

| Result (2026) | What it does | Where it sits relative to the walls |
|---|---|---|
| Connes, arXiv:2602.04022 (Feb). "Letter to Riemann": extremizing the restricted Weil form with primes < 13 yields the first 50 zeros to 10^{−55}…10^{−3}; proves the extremal values lie exactly on the line; proposes convergence of zeros from finite to infinite Euler products. | Real-rooted extremizers at every finite aperture. | The corpus has the general theorem (`exists_realRooted_fullGround`) and the exact missing input: `riemannHypothesis_of_localizedFullGrounds` needs ∫|u_j| e^{(1/2+η)|t|} ≤ C|∫u_j| uniformly as a_j → ∞. Convergence of the extremal zeros to ζ's zeros is the dyadic prime-window inequality of SRT, a receiver. |
| Alpöge–Furman, arXiv:2608.13637 (Aug). ≥ 2/3 of zeros simple and on the line, ≥ 5/6 distinct, unconditional; Montgomery's RH input replaced by a rank–trace inequality on a finite compression of Weil's Hermitian form with Sylvester inertia handling off-line pairs. Lean-verified (their claim). | First new unconditional theorem obtained from Weil's form by a sign-structure (inertia) argument instead of an estimate. | Consistent with the quantifier-gap wall: inertia plus averaged zero-density yields proportions, never totality. The corpus has the inertia layer (`hermNegIndex_eq_zero_iff_posSemidef`, `inertia_fromBlocks_zero`) and simple-zero density (`separated_simple_critical`). |
| Zhu, arXiv:2608.24827 (Aug). Certified positivity for supp f ⊆ [−0.8, 0.8] (classical (log 2)/2 ≈ 0.347); window ground state simple and even; empirical law −ln λ_min(L) ~ 2π²N(T*)/ln N(T*), T* = 2πe^{2L}; argues one-stroke certificates must resolve frequencies up to 2πe^{A_L}, A_L ~ 4e^L. | Numerical confirmation of the corpus's resolution limits and of the Landau–Widom decay of μ. | The corpus's analytic windows are 3/10 (full) and 181/500 (odd), proved without computation; the near-radical dimension theorem is the unconditional side of Zhu's law. |
| Suzuki, arXiv:2606.09096 (Jun). Screw-function framework for Yoshida/Bombieri/CC/CCM; conjectures the zeros as an a → ∞ limit of self-adjoint nonlocal realizations of d/dx on [−a,a]. | A spectral-realization conjecture at finite aperture. | Same open core as Connes's strategy: the limit a → ∞ is the no-crossing law. |
| Groskin, arXiv:2607.02828. Finite Guinand–Weil dictionary for truncated forms; certification budget B_T. | Exact finite bookkeeping. | A reading, in SSIC's sense; its author states no RH claim. |
| Guth–Maynard, Annals 203 (2026). Zero density 30/13. | Averaged. | Formalized in the corpus; cannot pass density-one → all. |

Nothing in 2026 crosses a wall. Two of the three serious 2026 advances are *type changes* (inertia; extremal
real-rooted zeros) and both stop exactly where the corpus's theorems say they must. This is the strongest external
evidence that the frontier map is correct and that the next step is not another estimate.

---

## 4. Q1 — candidate mechanisms and verdicts

### 4.1 Why no estimate-type mechanism exists

Let S be any statement about ζ that implies RH. By 1.5, S must be (i) Euler-deformation-sensitive, (ii) dependent on
infinitely many Λ(n) in a way that no finite window captures, (iii) a statement about a single test or a single height,
not a family average, (iv) reflection-odd-sensitive. By 1.2, S has no slack: it must hold with the exact weight Λ and
fail for every perturbation summable against n^{−2}. By 1.4, S is equivalent to a bound on one scalar — the smeared
self-pairing of the prime comb against the test's spectral measure beyond the diagonal threshold — and that scalar, at
the resolution needed to see an off-line zero of depth δ at height γ (aperture ≍ (log γ)² log log γ/δ, i.e. primes up
to γ^{c/δ}), reads the pair correlation of primes at lags below the mean-value threshold: there the only available
bounds are mean values over heights, which (iii) forbids. Every "mechanism" that produces an estimate therefore
produces an averaged one, and the walls apply. This is not a heuristic; each clause is a cited theorem.

### 4.2 Candidates attacked (hgtl7 Phase 4)

| Candidate | Statement | Attack | Verdict |
|---|---|---|---|
| (a) Inertia / Morse index of compressions W_a | n₋(W_a) := number of negative eigenvalues of the restricted form; RH ⇔ n₋ ≡ 0; bound n₋ by a spectral-flow or rank–trace argument. | n₋ is finite for each a (off-line part is a compact perturbation of the PSD on-line part) and nondecreasing by Cauchy interlacing. Bounding it needs either zero-density (averaged → proportions only, exactly Alpöge–Furman) or the location of off-line zeros. n₋ ≡ 0 is the no-crossing law. | **BRIDGE.** New unconditional *proportion* theorems are available this way (2026 proves it); RH is not. |
| (b) Ground-state convergence | The lowest eigenvectors u_a of W_a (real-rooted transforms by `exists_realRooted_fullGround`) converge, normalized by mass, to Riemann's Φ (the inverse transform of Ξ) in L¹(e^{(1/2+η)|t|}dt). Implies RH through `riemannHypothesis_of_localizedFullGrounds`. | Under ¬RH the ground state beyond A* is driven by the off-line pair and is edge-concentrated with ratio ∫|u|e^{(1/2+η)|t|}/|∫u| ≳ e^{(1/2+η)a}γ₀: the conjecture is false exactly off RH, as it must be. Under RH, Φ truncated at a is an almost-minimizer (W(Φ_a) ≈ exp(−2πe^{2a})), so the conjecture is plausible. A proof of convergence must show no new negative mode enters between a and 2a: `riemannHypothesis_or_ccmFirstContactTranslationSaturation` says a first contact is a new mode, and excluding it is the dyadic prime-window inequality (SRT), a receiver. | **CIRCULAR as a mechanism; SURVIVES as the cleanest formulation of Connes's 2026 strategy.** [OPEN CORE]: uniform exponential localization of ground states at rate > 1/2. |
| (c) Landau–Widom floor | μ(L) ≥ exp(−C·N(2πe^{2L})) for all L (Zhu's empirical law as a lower bound). Implies RH (μ > 0). | Under RH this is a sampling inequality for Paley–Wiener functions on the zero set, provable from the zero density alone. Unconditionally it cannot be stated on the zero side; on the prime side it is the no-crossing law in quantitative form. | **RH-equivalent shape, no producer.** Worth proving *under RH* as the exact decay law of μ; it is the "band recipe" SSIC asks for, but as a reading, not a certificate. |
| (d) Doubling-ratio / band recipe for ζ | A finite set of band magnitudes of the ζ functional whose ratio is attained exactly on the line (SSIC open problem). | Finite data admits off-line extensions (`exists_offLine_lattice_windowed_nonneg`); any faithful magnitude reading must be unbounded in aperture, and then it is the rate reading, a receiver. | **REDISCOVERED** (= rate reading). |
| (e) Diophantine / Witt | Use the ℚ-independence of {log p} (`linearIndependent_log_primesBelow_rat`, Matveev machinery present) or Witt ghost coordinates (`nativeWittGhost`) to bound the resonant (aligned) part of the mech-50 scalar. | Linear-form bounds are exponentially weak in the number of primes; alignment of P primes needs height exp(cP) and the test's spectral measure has polynomial tails, so alignment is never the dominant contribution; the dominant contribution is the unresolved near-diagonal (primes in short intervals), which Diophantine independence does not touch. Witt structure is a ring structure; no positivity. | **INSIGNIFICANT as stated.** The Diophantine structure matters for the *extremal tests* (resonators), not for the bound. |
| (f) Zero dynamics (de Bruijn–Newman flow) | Mirror Rodgers–Tao (`not_real_rooted_of_neg`): an off-line pair at t = 0 forces an impossible configuration at some t > 0. | The forward flow forgets the Euler product; Davenport–Heilbronn-type functions flow identically and have Λ > 0; selectivity fails unless a ζ-specific input at square-root level is injected. The corpus's heat-transport no-go (no degree-uniform reverse retention) closes the reverse direction. | **FALSE as a selective mechanism** (not deformation-sensitive). |
| (g) Adjunction / positive remainder | Exact evaluation of the smeared self-pairing of the prime comb with a remainder positive by construction. | This is the right *shape* (see §5), but as an analytic statement about ζ it is AIP open problem 7(c): the band charge as a Hankel form with symbol Σ_band Λ(n)n^{−1/2−iξ}, whose fluctuation is ≍ log ξ on the line and larger by e^{(2β−1)r} off it. | **REDISCOVERED** as a statement; **new** only as the organizing target of a field (Q2). |

### 4.3 The opening

The opening is not a seventh estimate. It is the observation that in the one proof of an RH that exists (Weil, curves
over finite fields), the self-intersection of the Frobenius graph is never estimated: it is computed exactly from the
genus and q by the adjunction formula, and positivity is forced by a dimension count. The arithmetic analogue of that
self-intersection is the corpus's mech-50 scalar. The corpus has proved that it cannot be *bounded* by any admissible
input; it has not asked whether it can be *computed*. Computing it is a different kind of question: it needs the
infinite prime tail as a primitive object with an exact pairing, which no existing field provides. That is the field
of Q2. The first concrete conjecture of that field, in the corpus's own terms, is:

> **Arithmetic adjunction conjecture (shape).** There is a tail-intrinsic object 𝔗 (the signed prime tail) and an
> exact pairing ⟨·,·⟩ on tests such that for every odd C² test F of aperture r,
> Σ_{p≠q} w_p w_q A_F(log(q/p)) = ⟨𝔗_F, 𝔗_F⟩ + Σ_p E_p(F), where Σ_p E_p(F) is the exactly summable tower series
> (single-prime Euler envelopes) and ⟨𝔗_F, 𝔗_F⟩ ≥ 0 by construction, with ⟨𝔗_F,𝔗_F⟩ ≤ poly(r)·A_F(0)·Σ_p w_p²
> following from the definition of 𝔗 rather than from an estimate.

It is falsifiable (it fails for ζ(s−a)ζ(s+a), for which the tower series diverges; for Beurling systems, where
multiplicative lags are not tower-supported; for Liouville twists, where the tower series alternates), it is not an
average, and its [OPEN CORE] is the existence of 𝔗 — which is the entire content of Q2.

---

## 5. Q2 — the field

### 5.1 Thesis and name

**Arithmetic Castelnuovo–Severi theory** (working alias: *tail-intrinsic intersection theory*). The intersection theory
of the scaling surface of ℤ in which (a) the cycles are the Weil tests, (b) the pairing is the explicit formula, (c) the
unique positive plane is the pole plane spanned by e^{±u/2}, (d) the Frobenius graph is the prime comb, (e) the kernel
is the theta span, and (f) the Hodge index theorem — negative definiteness off the pole plane — *is* Weil positivity,
hence RH. The field exists to make (f) a theorem by supplying the two ingredients Weil's proof has and the arithmetic
side lacks: an adjunction formula for the Frobenius self-intersection, and a section count.

SSIC, the corpus's existing proposal, is the *metrology* of this field: it says what any reading of the form can and
cannot resolve. The field proposed here is the *geometry*: it says what the form is a pairing *of*, and why its
positivity is a consequence of structure rather than of estimates. The two are complementary; SSIC's resolution limits
become theorems about which cycles are visible at which "degree" (aperture).

### 5.2 The dictionary (Weil's proof ↔ the corpus)

| Weil's proof for a curve C/F_q | Arithmetic analogue | Status in corpus |
|---|---|---|
| Surface C × C | Scaling surface: tests on ℝ^*_+ in log coordinates, pairs (a,b) with the AIP incidence lattice (same-side atoms a\|b prime-power quotient; crossing atoms ab prime power) | Built (AIP ledger, `fullZeroForm_eq_incidenceLedger`); not recognized as a surface |
| Intersection pairing D·D′ | Explicit-formula pairing W(f,g) | Built (five names, APT) |
| Fibre classes H, V; H·V = 1, H² = V² = 0 | Pole directions e^{u/2}, e^{−u/2}; the (1,1) Lorentz form (B² − A²)/2 | Built (ACT full zero form; BiScale 2×2 pole criterion; THIM rank-one polar risk) |
| Diagonal Δ | Archimedean collar (the identity scaling) | Built (collar order 2e^{−s}; collar ratio R(a) > 2) |
| Frobenius graph Γ | Prime comb Σ Λ(n) n^{−1/2} δ_{log n} | Built |
| Γ·Δ = #C(F_q) (Lefschetz) | Prime side of the explicit formula | Built |
| Γ ∘ Γ^T = q·Δ (Frobenius is unitary up to scale) | Scaling is unitary on L²(ℝ^*_+) | Trivially true; carries no information alone |
| Γ·Γ = q(2 − 2g) (adjunction; exact, zero-free) | Smeared self-pairing of the prime comb against the test's spectral measure (mech-50 scalar) | **Missing.** Proved not boundable by admissible inputs; never computed |
| Hodge index: signature (1, ρ−1) on Num | Weil positivity | ⇔ RH |
| Castelnuovo–Severi: D² ≤ 2(D·H)(D·V) | RH (local terms ≤ pole terms) | ⇔ RH |
| Kernel of 2d₁d₂ − D² is ⟨H,V⟩ | Theta span: 𝒲Θ = cosh(x/2); full zero form annihilates it | Built (ACT 3.5, 3.9: criticality with sign-changing null directions) |
| Genus g (finite) | Zero count N(T) ~ (T/2π) log T (infinite genus) | Known; it is why compact tests are never Ξ-divisible |
| Riemann–Roch on C×C; h⁰ ≥ 0 forces the index theorem | Section count on the scaling surface | **Missing.** Connes–Consani have RR for the curve Spec ℤ (2024); nothing for the surface |
| Moving lemma (deform Γ to compute Γ²) | Translate calculus (AIP tower and bi-tower laws, resonant trains) | Built; moving reveals the resonators |
| Γ is an algebraic cycle with integer degrees | log p are ℚ-independent reals: Frobenius has no integral degree | Wall 14.2 ("integral Frobenius / orientation") |
| F_q-points of C | Primes | — |
| Exactness: all intersection numbers are integers | Exact only on multiplicative lags (towers); archimedean smearing turns Γ·Γ into prime pair correlation | 1.6 (F_q[T] calibration) |

Reading the table: the corpus has built the surface, its pairing, its pole plane, its Frobenius graph and its kernel,
and has proved that the one missing intersection number cannot be obtained by bounding. Weil's proof never bounds it.

### 5.3 Central questions

1. **Adjunction.** Is there an exact, zero-free formula for the regularized self-pairing of the prime comb against the
   archimedean collar, valid one test at a time, whose structure (not its size) makes the remainder nonnegative? What
   plays the role of the genus and of q? (Candidates: the archimedean Gamma datum, which is the zero density, and the
   aperture, which is the degree.)
2. **Section count.** What is the space of "sections" of a line bundle on the scaling surface, and what exact count
   (an integer, a volume, a Fredholm index, a covolume) is nonnegative by definition and equals a combination of
   pairings? Connes–Consani's RR for Spec ℤ is the one-dimensional case; the field needs the two-dimensional one.
3. **Integral Frobenius.** In what structure do the degrees log p become exact? (Not integers; but perhaps classes in a
   group where the pairing is exact — e.g. the Big Witt ring, whose ghost coordinates the corpus has as the sieve
   receiver, `norm_wittSieveReceiver_sq`.)
4. **Tail as primitive.** Define 𝔗 so that log ζ(s) − Σ_{p ≤ y} p^{−s} at a single s is a *value* of 𝔗, not a limit;
   what are its exact pairings with the pole plane and with the comb?
5. **Why the pole pays at PNT level and not beyond.** AIP: prime density and polar density agree at e^{t/2}; archimedean
   surplus is e^{−t/2}. The rate-1 floor is "prime charge versus pole charge at PNT level". What exact structure makes
   the deficit at rate < 1 the self-pairing of the tail?
6. **Resonators as special cycles.** The extremal tests are {p,q}-smooth boxes. In the geometry, special cycles have
   computable self-intersections. Is the self-pairing on resonators exactly the sum of two Euler envelopes plus a
   positive form? (AIP mechanism 51 says the sum is positive; the field asks for the exact decomposition.)
7. **Kronecker rank.** Beurling systems whose log-primes lie in a lattice are periodic and function-field-like; ζ has
   infinite Kronecker rank. Is there a continuity principle from lattice systems (where the adjunction formula is
   exact) to ζ?

### 5.4 Point of view

- **Compute, don't bound.** The target intersection number is to be evaluated exactly, as Γ·Γ is in Weil's proof.
  Any inequality must be a corollary of an identity whose terms have signs by construction.
- **The tail is primitive; truncations are derived.** Objects are defined on all of ℕ (or on the adeles); a window is a
  *reading* of an object, never its definition. This single rule defeats the finite-window, family-average and
  Euler-deformation invariances at once, because a tail-intrinsic object changes when one Euler factor changes.
- **Signature (0 | pole plane).** The fundamental form has one Lorentz plane and is to be shown definite on its
  complement. All bookkeeping is in Pontryagin-space language: the form is a Π₂ (or Π₁ after parity) Hermitian form
  and RH says the number of negative squares is exactly the pole index.
- **Two operations at one modulus.** The surface carries the additive structure of ℕ through Bézout (gcd(n,n+1) = 1,
  the pronic weight 1/(n(n+1)) that telescopes) and the multiplicative structure through the incidence lattice; the
  F_q[T] model is where both are exact.
- **Readings are coordinates along orbits; RH is transverse.** SSIC's dilation-orbit picture is kept as the semantic
  layer: a reading is a coordinate on an orbit, depth is the complete transverse invariant, and only a transverse
  (reflection-odd) object can carry it.

### 5.5 Objects

Definitions are chosen so that the corpus's criteria are automatic, not checked afterwards.

1. **Unitary Euler data.** The only admissible arithmetic data are Euler products with |α_p| = 1 at every prime and a
   functional equation. Euler deformations with |a| > 1, the shifted pair ζ(s−a)ζ(s+a), and non-Euler Dirichlet series
   are not objects. (Selectivity against KR-DEF and the shifted pair by definition. The temperedness gate of APT is the
   first place where the corpus met this criterion by an identified input.)
2. **The scaling surface 𝒮.** The product of the scaling group with itself, in log coordinates, with the incidence
   lattice of pairs (a,b) and the Bézout structure of consecutive integers built into its cycles. Beurling systems
   do not have a Bézout structure, so they do not define a surface. (Selectivity against Beurling by definition.)
3. **Cycles.** Reflection-odd and reflection-even tests, graded by aperture (degree). The odd sector carries the
   content (THIM: the even sector's polar risk is rank one and a gauge).
4. **The pole plane P = span(e^{u/2}, e^{−u/2})** with its Lorentz form; the kernel K = theta span.
5. **The Frobenius cycle Γ** = prime comb, and its **smearings** Γ_F against tests.
6. **The signed tail 𝔗.** The object whose pairings with the pole plane and with Γ reproduce log ζ(s) − Σ_{p≤y}p^{−s}
   as values and whose self-pairing is the mech-50 scalar. Candidates to be tested: the regularized Frobenius
   self-intersection current; the Möbius row as the dual of Γ (BVI: the Möbius row annihilates the resonant mode,
   Σ_{d|q} μ(d) = 0); the Witt-vector class of ζ in the Big Witt ring with Frobenius and Verschiebung as the two
   operations.
7. **Resonators** (multiplicatively aligned trains, {p,q}-smooth boxes): the special cycles on which self-pairings
   are expected to be exactly computable.
8. **Readings** (from SSIC): maps from the object space to observables, with their shadows and resolution limits.

### 5.6 Language

Units (width, aperture, side, damping), grading (deficit C e^{2σr} ⇒ strip 1/2 + σ), ledger (paid/unpaid, pool,
crossing, gain, cost, remainder, pole), degree (aperture), index (number of negative squares), reading/shadow/
resolution, criticality (the least admissible rate), tower (single-prime Euler envelope), resonance (alignment on a
log-lattice), tail (the primitive object), adjunction (exact self-intersection). Every statement carries its unit and
its grading; a statement without an exponent is an identity and counts as zero (the ledger's rule).

### 5.7 Foundational principles

P1 *Exactness before inequality.* Every inequality is the positivity of a term in an identity whose terms are signed
by construction.
P2 *Tail-intrinsic definitions.* No object is defined through a truncation and a limit.
P3 *Unitarity as typing.* Non-unitary Euler data are not objects; this is where Euler-deformation sensitivity lives.
P4 *Both operations at one modulus.* Bézout and the incidence lattice are part of the surface, not of a proof.
P5 *One Lorentz plane.* The fundamental form's indefiniteness is exactly the pole plane; the theory's theorems count
negative squares.
P6 *No archimedean subsidy.* A gain that grows with frequency is a reading artefact; constants and linear-in-aperture
terms are allowed (ACCE criterion).
P7 *Calibration.* Every construction is first run over F_q[T], where the adjunction formula and the section count are
classical, and must reduce to Weil's proof there.
P8 *Metrology is separate from geometry.* What a reading can resolve (SSIC) is never confused with what an object is.

### 5.8 Criteria for success

The ACCE/SSIC criteria are adopted as axioms (selectivity, no family average, square-root precision beyond the
diagonal, every scale, node criticality log 4 vs log 6, signs read, no subsidy, units, grading, F_q[T], pairs). In
addition:
- C1 The four selectivity tests are passed *by the definitions* (unitary typing, Bézout surface, signed tail,
  reflection-odd sector), not by a sign that appears in a proof.
- C2 The field produces at least one new unconditional theorem about ζ that cannot be obtained by averaging: for
  instance an exact formula for a self-pairing on a resonator class, or an unconditional lower bound on μ(A) at a
  rate better than the current exponent-1 floor μ₀(A) ≥ −(10 + 68e^A) on some sector.
- C3 Over F_q[T] the constructions reduce verbatim to the Castelnuovo–Severi inequality.
- C4 The theory is Lean-formalizable unconditionally at every step; a gap is recorded on a card, never as a hypothesis.
- C5 It explains, from structure, the three 2026 facts: why inertia yields 2/3 and no more, why finite-prime extremizers
  are real-rooted, and why the Landau–Widom rate is 2π²N(T*)/ln N(T*).

### 5.9 Research topics, ranked

1. **The adjunction formula on resonators.** Compute exactly, for bi-lattice trains, Σ_{p≠q} w_p w_q A_F(log(q/p)) −
   Σ_p E_p(F); decide whether the remainder is a positive form in the train's coefficients. The corpus's translate
   calculus and `biLatticeTrain` are the starting point; AIP mechanism 51 says the total is positive. First target: a
   closed form for two primes, then the general smooth box. This is a finite, unconditional computation and would be a
   new theorem.
2. **Landau–Widom law for μ under RH.** Prove −ln μ(L) = 2π²N(2πe^{2L})/ln N(2πe^{2L})·(1 + o(1)) assuming RH, as a
   sampling inequality for Paley–Wiener functions on the zero set, and identify the unconditional part (the corpus's
   near-radical theorem gives one side). This is the exact "band recipe" of SSIC and the first test of C5.
3. **Pontryagin-space formulation.** State Weil positivity as: the explicit-formula form on odd tests is a Π₁ form
   whose single negative square is the pole; prove Krein–Langer-type structure theorems (negative squares are exactly
   the off-line pairs, `hermNegIndex_eq_zero_iff_posSemidef` is the finite case) and derive the inertia theorems of
   2026 as corollaries.
4. **The signed tail as a Witt class.** Test whether the Big Witt ring with Frobenius/Verschiebung (`nativeWittGhost`,
   Deninger ghost coordinates) gives an exact pairing of ζ's class with the pole plane; the corpus records this as an
   open question and has the coordinates.
5. **Section count on the scaling surface.** Starting from Connes–Consani's RR for Spec ℤ, formulate h⁰ for the product
   with the pole plane as the ample class; the target is an identity h⁰ − h¹ + h² = (pairing) whose h^i ≥ 0 by
   definition. This is the hardest item and is the one that would make Hodge index a theorem.
6. **Kronecker-rank continuity.** Classify Beurling systems by the rank of the ℚ-span of their log-primes; prove the
   adjunction formula for lattice systems (periodic, function-field-like, `exists_offLine_lattice_windowed_nonneg` is
   their hiding law) and study the limit of growing rank. This is where the Diophantine structure of {log p} enters
   correctly: through the extremal cycles, not through linear-form bounds.
7. **Pronic calculus as the additive input.** Make the telescoping weight 1/(n(n+1)) and Bézout coupling (BVI) part of
   the surface's definition; prove that the F_q[T] calibration is the case where the pronic and the incidence
   structures coincide.
8. **Metrology integration.** Re-derive SSIC's resolution limits as statements about which cycles are visible at which
   degree, so that the two theories share one language.

### 5.10 Relation to existing programmes, and what is new

The programme "ℤ as a curve over 𝔽₁ with a Hodge index theorem" is Connes–Consani's and Deninger's (and Borger's in
Witt language). What is new here is not the aim but the specification, which the corpus has earned:
- the precise identification of each ingredient of Weil's proof with a corpus object, and of the two missing
  ingredients as the adjunction formula and the section count (§5.2);
- the theorem-level proof (1.5) that the missing intersection number cannot be *bounded* by any admissible input, so
  that only exact computation is left;
- the identification of the resonators as the special cycles on which exactness is to be tested first;
- the requirement that selectivity be a matter of typing (P3, P4) rather than of a sign found inside a proof;
- the separation of metrology (SSIC) from geometry, with the Landau–Widom law as the bridge.

---

## 6. How this could be wrong

- The adjunction conjecture may have no exact form because the smeared self-pairing genuinely encodes the pair
  correlation of primes at short lags, which is conjecturally random (Montgomery, Goldston–Montgomery). If so, the
  "exact" formula would have to absorb that randomness into a positive form, which is a Hodge-index statement of its
  own. Topic 1 decides this on resonators.
- The section count may not exist: the near-radical has dimension ~ e^{2L}, so any "h⁰" would be astronomically
  degenerate, and the index theorem would have to control exponentially small eigenvalues exactly. Topic 2 measures
  this under RH.
- The whole field might be a receiver in disguise: every object may turn out to be definable only through a limit of
  truncations after all. P2 is the test; the first object to fail P2 kills the proposal.
- The 2026 external results were checked by abstract only; Alpöge–Furman's Lean verification is their claim.

---

## Appendix — declarations cited (all surfaced by `formal_tools.py research`)

`ccmRestrictedWeilGroundEnergy_contact_eq_zero`, `ccmRestrictedWeilGroundEnergy_neg_of_contact_lt`,
`strictAnti_ccmRestrictedWeilPolarGroundEnergy`, `riemannHypothesis_or_ccmFirstContactTranslationSaturation`,
`ccmFirstContact_no_narrow_translate`, `exists_realRooted_fullGround`, `riemannHypothesis_of_localizedFullGrounds`,
`weilPositiveFull_iff_riemannHypothesis_and_eq_vonMangoldt`, `eq_zero_of_weilPositiveFull_add_of_sub`,
`theWidthIsTheGroundEnergyRateWhenTheDepthMassDoesNotCluster`, `exists_offLine_lattice_windowed_nonneg`,
`regular_integers_do_not_constrain_zeros`, `deformedDivisorCoeff`, `deformation_factor_ne_zero_at_reflection`,
`fqCenteredPrefix_eq`, `fullZeroForm_eq_incidenceLedger`, `GlobalIncidenceAllocation`,
`odd_sourceEnergy_eq_weilForm_add_two_sourcePair_oddPolarVectorAt_sq`, `sourcePair_oddPolarVectorAt_eq_inner_tanhL`,
`depth_determined_by_two_bands`, `depthFromBands`, `zeta_weil_near_radical_dimension_smooth`, `not_real_rooted_of_neg`,
`riemannHeat_zeros_real`, `riemannHypothesis_iff_forall_closedBall_zetaDiscStronglyRecurrentOn`,
`linearIndependent_log_primesBelow_rat`, `logPrime_pair_independent`, `biLatticeTrain`, `primeLog_linearIndependent_fin`,
`nativeWittGhost`, `norm_wittSieveReceiver_sq`, `hermNegIndex_eq_zero_iff_posSemidef`, `inertia_fromBlocks_zero`,
`separated_simple_critical`, `eventually_superlinear_xiSimpleCriticalZeroCount`,
`actual_zeta_finiteOffLine_detected_by_gridTentPattern_at_aperture`, `CCMRationalAdelicScaling`,
`fieldOneFiniteStageIdeleClassAction`, `deningerBigWittPairPartial_ghost_coeff`.
