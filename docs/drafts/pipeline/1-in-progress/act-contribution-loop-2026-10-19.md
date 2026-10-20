# ACT contribution loop (goal: 100 field-native contributions)

- **ID:** act-loop-1019
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) per contribution; CONJECTURE for open items
- **Source:** formal/GaloisForLFunctions/ArithmeticCriticalityTheory/README.md (read-only)
- **Statement:** Develop Arithmetic Criticality Theory by a conjecture loop; each accepted
  contribution is an unconditional Lean theorem native to the field (its objects: the folded and
  two-sided generators, shifted ground states, collar masses, the energies S, P, D, X, the profile
  variance, the pole moment, the shift-averaged kernels).

## Goal
100 significant contributions: native to ACT, expanding what the field explains or solves
(README §5 frontier, or discharging a premise elsewhere in the corpus). No RH hypotheses in Lean:
consequences of positivity are stated as equivalences or as limits of unconditional identities.

## Coordination
Programme card: `act-arithmetic-criticality-theory-2026-10-19.md` (status of the first 35 modules).
THIM (`TransHorizonIncidenceMechanics/`) owns overlapping objects in `oddProfile` coordinates; check
`ls ArithmeticCriticalityTheory/` and search before naming a module.

## Conjecture queue
1. Frontier 3: every finite signed superposition `Σ c_j ω_{a_j}` that is nonnegative on the half
   line and nonzero fails the folded test at infinity; the decisive coefficient is the pole moment
   `σ = Σ c_j sinh(a_j/2) = 2∫_0^∞ M sinh(x/2)`, positive on the cone.
2. Single-shift completeness: RH ⟺ the (pole-free) variation inequality at one fixed shift `a`.
3. Origin polarity: the even form stays supercritical on even tests vanishing near `0`; the folded
   test is the even-sector test with a polar Dirichlet point (soft no-go for all folded
   supersolutions).
4. Sharp coupling: `Q − ε ρ` is negative on odd tests for every `ε > 0` (no Hardy weight
   comparable to the potential); constraint `∫ W ω_a² ≤ sinh²(a/2)` on Hardy weights.
5. Weight criterion of the monotone cone (README 3.9): decide it; positive survivor.
6. Selectivity: which statements survive for an abstract even kernel with an abstract harmonic
   identity (pole-driven vs prime-driven parts of the theory).

## Log
- 2026-10-19 — loop started; README read in full; programme card and modules surveyed; queue seeded.

## Contribution ledger (append-only)
- **C1 · Signed superpositions fail at infinity (README frontier 3)** —
  `SignedSuperpositionInfinityFailure`. For `ω = Σ_j c_j ω_{a_j}` (arbitrary real `c_j`, `a_j > 0`)
  with test coordinate `M = Σ c_j m_{a_j} ≥ 0` on the half line: `foldedDefect_spanGroundState`
  (`𝓛_N ω − Φcosh ω = 2Φ[σ sinh(x/2) − Σ c_j C_{a_j}]`, `σ = Σ c_j sinh(a_j/2)`);
  `sum_mul_max_shiftDifference_eq` (positive parts are additive on the cone, so the combined collar
  is the collar of `M`); `abs_signedPrimeShift_sub_le` (two-sided harmonic-identity evaluation
  `|Σ Λ n^{−1/2} m_a(log n − x) − 2 sinh(a/2) sinh(x/2)| ≤ K`, `0 ≤ a ≤ x`);
  `foldedDefect_spanGroundState_le` (defect `≤ −2Φ(x)[σ sinh(x/2) − K Σ|c_j|]` for `x ≥ max a_j`);
  `integral_Ioi_spanShiftDifference_mul_sinh_half` (`σ = 2∫_{x>0} M sinh(x/2)`, the pole moment);
  `spanSourceCoefficient_pos`; `exists_infinity_window_spanGroundState_foldedGenerator_lt_potential`:
  every nonzero nonnegative finite signed superposition is a strict folded subsolution on `[X, ∞)`.
  Insight: the per-shift collar bounds do not combine under mixed signs, but on the cone the collar
  is linear and the obstruction coefficient is the pole moment, positive on the cone — the same
  quantity that makes wide plateaus positive directions forbids supersolutions in the span at
  infinity. No PNT. Standard axioms.
- **C2 · Single-shift completeness (frontier problems 1 and 2 are RH at every shift)** —
  `SingleShiftCompleteness`. `shiftQuotient a F = F/m_a`: every odd `C²_c` test vanishing on
  `(−ε, ε)` is `m_a u` with `u` even `C²_c` vanishing there (`contDiff_shiftQuotient`,
  `phiDoobTest_shiftedGroundState_mul_shiftQuotient`); the corpus half-line witness gives, without
  RH, one such test with negative energy, the same for all shifts
  (`exists_profile_vanishing_markovEnergy_neg_of_not_riemannHypothesis`). For every fixed `a > 0`:
  RH ⟺ `Q(m_a u) ≥ 0 ∀u` (`riemannHypothesis_iff_forall_shiftedGroundState_markovEnergy_nonneg`)
  ⟺ the same on profiles vanishing near `0`
  (`riemannHypothesis_iff_forall_vanishing_profile_markovEnergy_nonneg`) ⟺ variation inequality
  (`…_forall_variationInequality`) ⟺ pole-free variation inequality `D ≤ 2S + V_a`
  (`…_forall_poleFreeVariationInequality`) ⟺ remainder dominates defect
  (`…_forall_remainder_dominates_defect`); ∃ shift ⟺ ∀ shifts
  (`riemannHypothesis_iff_exists_shift_markovEnergy_nonneg`). Insight: the shift is a gauge — the
  frontier inequalities are not weaker consequences of RH but RH itself at each shift; the origin
  (site of every folded-supersolution failure) carries no zero information; shift averaging can
  only reweight, never enlarge, the test class. Standard axioms.
- **C3 · The Markov energy is the weak form of the two-sided generator** —
  `TwoSidedGeneratorWeakForm`. For every `z ∈ C²_c(ℝ)`:
  `markovEnergy(Φz) = ∫ z(x)[(𝓛_D z)(x) − Φ(x)cosh(x/2)z(x)] dx`
  (`markovEnergy_phiDoob_eq_integral_mul_twoSidedGenerator_sub_potential`). Per shift it is
  summation by parts (`integral_phiDoobArchShiftJump_eq_integral_mul_twoSidedShiftGenerator`);
  archimedean shifts by Fubini with `|𝓛_D^t z| ≤ 2Φ(0)²Lip(z)t`
  (`abs_twoSidedShiftGenerator_le_lipschitz`); prime shifts by `Φ(x ± log n) ≤ Φ(0)/Φ(R)·Φ(log n − R)`
  on the support (`riemannKernelReal_add_add_sub_le`) and `integral_tsum`. Insight: the theory's
  generator calculus — every ground-state representation is this identity on a factorised test;
  source equations enter only through `𝓛_D`. It makes general (non-single-shift, sign-changing)
  Doob gauges accessible. Standard axioms.
- **C4 · On the span of the shifted ground states the Markov form is the pole form** —
  `ShiftedGroundStateSpanPlateauLaw`. For every finite superposition `ω = Σ c_j ω_{a_j}` (any real
  coefficients and shifts), test coordinate `M`, pole coefficient `σ = Σ c_j sinh(a_j/2) = ∫_ℝ M sinh(x/2)`:
  `|markovEnergy(Φ(ω u_L)) − 2σ²| ≤ K e^{−8L}` (`exists_abs_markovEnergy_spanPlateauProfile_sub_le`,
  `tendsto_markovEnergy_spanPlateauProfile`). Tools: span source equation
  `𝓛_D ω − ρω = 2σ sinh(x/2)Φ` (`twoSidedGenerator_spanGroundState_sub_potential`), Leibniz rule
  `𝓛_D(ωu) = u𝓛_Dω + Φ·Comm` (`twoSidedGenerator_mul`), commutator localisation
  `|u_L M Comm| ≤ C²(2ΛA₁ + 2P₈)e^{−8L}e^{−8|x|}` (`abs_smoothPlateau_mul_mul_plateauCommutator_le`).
  Consequence: `σ = 0` superpositions are null directions, `|Q| ≤ Ke^{−8L}`
  (`exists_abs_markovEnergy_spanPlateauProfile_le_of_poleFree`). Insight: in the limit the Markov
  form restricted to the span is the square of ONE linear functional (rank one): `ω_a`, `ω_b` are
  correlated by exactly `2 sinh(a/2) sinh(b/2)`; the zeros are invisible on the whole span and the span
  carries no positivity beyond the pole. Standard axioms.
- **C5 · The odd arithmetic form is never subcritical (README frontier 5 answered)** —
  `OddFormCriticality`. `exists_odd_markovEnergy_lt_integral_weight_mul_sq`: for every locally
  integrable `W ≥ 0` positive on a set of positive measure there is an odd `v ∈ C²_c` with
  `markovEnergy(Φv) < ∫ W (Φv)²` — no Hardy weight exists. `riemannHypothesis_iff_nonneg_and_no_hardyWeight`:
  RH ⟺ the odd form is nonnegative and critical (criticality unconditional). Null sequences: plateau
  truncations of the pole-free pairs `M_n = sinh(n/2) m_1 − sinh(1/2) m_n` (σ = 0, C4), which
  separate points (`exists_nat_nullPair_ne_zero`). Insight: Pinchover's trichotomy collapses to
  supercritical (¬RH) / critical (RH); the critical form has an infinite-dimensional family of
  approximate ground states (the pole-free theta span = CHMD's odd critical band), unlike Schrödinger
  forms whose critical ground state is unique and positive — a new, arithmetic type of criticality.
  Standard axioms.
- **C6 · On the translates of Φ the Markov form is Lorentzian** — `TranslateGroundStateLorentzLaw`
  (+ refactor of C4 into the gauge-generic `abs_markovEnergy_plateau_sub_integral_le`). Translate
  ground state `τ_b = Φ(·−b)/Φ`, exact source equation
  `𝓛_D τ_b − Φcosh(x/2)τ_b = −Φ(x)cosh((x−b)/2)` for all `b, x`
  (`twoSidedGenerator_translateGroundState_sub_potential`; `ω_a = τ_a − τ_{−a}`, `τ_0 = 1`). For
  `ω = Σ α_j τ_{b_j}`, `A = Σα_j cosh(b_j/2)`, `B = Σα_j sinh(b_j/2)`:
  `|markovEnergy(Φ(ωu_L)) − (B² − A²)/2| ≤ Ke^{−8L}` (`exists_abs_markovEnergy_translatePlateau_sub_le`).
  Corollary `tendsto_markovEnergy_phiDoob_smoothPlateau`: `Q(Φu_L) → −1/2` (the README's `Q(1) = −1/2`
  as a theorem on compactly supported tests). Insight: on the theta span the Markov form is the
  Minkowski form of signature (1,1) in the (cosh, sinh) pole coordinates — one negative (even pole),
  one positive (odd pole), infinite-dimensional null space; the explicit formula with all zeros
  erased; the even/odd split of the sign problem is the light-cone split. Standard axioms.
- **C7 · The harmonic theta span is the radical of the Markov form** — `HarmonicThetaSpanRadical`.
  Generator calculus completed: bilinear summation by parts, mixed integrability, symmetry
  `∫ v 𝓛_D z = ∫ z 𝓛_D v` (`integral_mul_twoSidedGenerator_comm`), additivity of `𝓛_D` on `C²_c`,
  polarisation `markovEnergy(Φ(a+b)) = Q(Φa) + Q(Φb) + 2∫ b(𝓛_D a − ρa)` (`markovEnergy_phiDoob_add`);
  pairing law `|∫ v(𝓛_D(ωu_L) − ρωu_L) − ∫ vΦg| ≤ Ke^{−8L}` for any gauge with source `Φg`
  (`abs_integral_mul_generator_plateau_sub_le`). Main: for a HARMONIC gauge (`𝓛_D ω = ρω`, decay
  `e^{−24|·|}`) and every test `v ∈ C²_c`: `|Q(Φ(ωu_L + v)) − Q(Φv)| ≤ Ke^{−8L}` for `L ≥ R_v`
  (`abs_markovEnergy_add_harmonicPlateau_sub_le`); instances: pole-free odd superpositions (σ = 0) and
  translate combinations with `A = B = 0`. Insight: the pole-free theta span consists of exact
  sign-changing solutions of the two-sided arithmetic Schrödinger equation (zero-energy states),
  infinite-dimensional; the Markov form on EVERY test descends to the quotient by it — the precise
  sense in which the theta span is zero-blind, and the structural reason for criticality (C5).
  Standard axioms.
- **C8 · The zero form: gauge invariance of the pole-free form** — `ZeroFormGaugeInvariance`.
  `zeroForm F = markovEnergy F − 2(∫F sinh(x/2))²`. (i) `poleFreeForm_eq_zeroForm`:
  `2S_a(u) − D_a(u) + V_a(u) = Z(m_a u)` for every shift — the frontier form depends only on the test,
  not the gauge; `poleFreeForm_shiftQuotient_eq`: `PF_a(F/m_a) = PF_b(F/m_b)`. (ii)
  `abs_zeroForm_add_spanPlateau_sub_le`: `|Z(Φ(ωu_L + v)) − Z(Φv)| ≤ Ke^{−8L}` for EVERY finite odd
  superposition ω (any σ): Z annihilates the whole odd theta span. (iii)
  `riemannHypothesis_iff_forall_odd_zeroForm_nonneg`: RH ⟺ Z ≥ 0 on odd `C²_c` tests (⇒ by cancelling
  the pole moment with `λ m_1 u_L`, invisible to Z). Insight: the content of RH in ACT is the sign of one
  form on the quotient (odd tests)/(odd theta span); shift, gauge and pole are bookkeeping. Standard axioms.
- **C9 · The archimedean place is Z-type; every obstruction is prime** — `ArchimedeanZTypeLaw`.
  Midpoint folding of the reflected collar (`integral_Ioo_reflectedDifferenceJump_eq_two_mul_half`),
  Fubini on `(0,∞)²`, and the translation `t = s + 2x` give the exact representations
  `D_arch(ω_a,u) = 2∫_{x>0}∫_{s>0} ω(s+2x) J_s(x)` and `S_arch(ω_a,u) = ∫_{x>0}∫_{s>0} ω(s) J_s(x)`
  (`archReflectedDifferenceEnergy_eq`, `archSameSideEnergy_eq`); since the Lévy density decreases,
  `D_arch ≤ 2S_arch` for every shift and profile (`archReflectedDifferenceEnergy_le_two_mul_archSameSideEnergy`).
  `riemannHypothesis_iff_forall_prime_variationInequality`: RH ⟺ `D_prime ≤ (2S_arch − D_arch) + 2S_prime + V_a`
  with nonnegative archimedean surplus. Insight: the archimedean variation inequality holds with no
  source; non-Z-type behaviour of the odd sector is exactly the non-monotonicity of the prime jump
  measure (anti-diagonal atoms `x + y = log n`). Standard axioms.
- **C10 · The full zero form: the Markov form modulo the whole theta span** —
  `FullZeroFormWeilPositivity`. `Ẑ(F) = Q(F) − 2(∫F sinh(x/2))² + 2(∫F cosh(x/2))²` subtracts exactly
  the Lorentz form of C6. `tendsto_fullZeroForm_add_translatePlateau`: for every finite translate
  combination ω (both parities, any A, B) and every `v ∈ C²_c`, `Ẑ(Φ(ωu_L + v)) → Ẑ(Φv)` — the full
  theta span is the radical of Ẑ. `riemannHypothesis_iff_forall_fullZeroForm_nonneg`: RH ⟺ Ẑ ≥ 0 on
  all real `C²_c` tests (even part: cosh moment cancelled by `λ_L Φu_L`, invisible to Ẑ, then the
  primitive-hyperplane criterion; odd part: C8). Tools: generator homogeneity
  (`twoSidedGenerator_const_mul`, `markovEnergy_phiDoob_const_mul`), moment additivity, plateau
  moment rates, τ_0-pairing `∫v(𝓛u_L − ρu_L) → −∫Φv cosh` (`tendsto_pairing_smoothPlateau`).
  Insight: the explicit formula's pole part is, inside ACT, the Lorentz form of the theta span; RH is
  positivity of the Markov form on (all tests)/(theta span), with no parity restriction. Standard axioms.
- **C11 · The Markov form is never subcritical on the primitive hyperplane** —
  `PrimitiveHyperplaneCriticality`. `exists_primitive_markovEnergy_lt_integral_weight_mul_sq`: for every
  locally integrable `W ≥ 0` positive on a set of positive measure there is a real `F ∈ C²_c` with
  `∫F cosh(x/2) = 0` and `markovEnergy(F) < ∫WF²`; `riemannHypothesis_iff_primitive_nonneg_and_no_hardyWeight`:
  RH ⟺ the form on the primitive hyperplane (Q-orthogonal complement of Φ) is nonnegative and critical.
  Null sequences: even harmonic pairs `τ_b + τ_{−b} − 2cosh(b/2)τ_0` (A = B = 0), corrected onto the
  hyperplane by a vanishing multiple of `Φu_0`; they separate every point including the origin
  (`exists_nat_evenNull_ne_zero`). Insight: the one-negative-square structure (Hodge index form) and
  criticality fit together — wherever RH makes the form nonnegative it is critical, with
  infinite-dimensional sign-changing null families of both parities. Standard axioms.

## Overlap audit (2026-10-20, after C11)
Checked against `RHTower/WeilMarkovOneBoundState` (M = W − P, P of signature (1,1), Φ̂ = Ξ makes the
truncated kernel almost W-null) and `RHTower/CHMDOddProfileArchAbsorptionAndPrimeChainBridge`
(per-x archimedean absorption kernel `(ω(s) − ω(2x+s))·jump ≥ 0` in oddProfile coordinates).
- C6 (Lorentz law) and C10 (`Ẑ = W` on real tests, RH ⟺ Ẑ ≥ 0) restate the Weil form/pole term in ACT
  coordinates; ACT-new parts: proofs from the harmonic identity alone (no zero sums), the exact
  translate source equation, `Q(Φu_L) → −1/2` as a compact-support limit. Count as PARTIAL.
- C8: zero form on odd tests = W; ACT-new: gauge invariance `PF_a(F/m_a) = Z(F)` for all shifts. PARTIAL.
- C7: radical statement is the Weil-language fact that Θ-span tests are W-null; ACT-new: generator
  calculus (symmetry, polarisation, pairing law), harmonic gauges = exact zero-energy solutions. PARTIAL.
- C9: per-x absorption mechanism already in CHMD; ACT-new: global integrated law in ACT energies and the
  RH ⟺ prime anti-diagonal inequality. PARTIAL.
- C1, C2, C3, C5, C11: no overlap found (search: Hardy weight / subcritical / single-shift / weak form).
Rule from now on: run a corpus search against the Weil-form lanes before claiming a contribution.
- **C12 · The ground-state representation in an arbitrary gauge** —
  `GeneralGaugeGroundStateRepresentation`. For any gauge ω with `|Φω| ≤ Ce^{−24|·|}`, convergent
  generator and source `𝓛_Dω − ρω = Φg`, and every profile `u ∈ C²_c` of any parity:
  `markovEnergy(Φ(ωu)) = J_M(u) + ∫u²Mg`, `J_M(u) = ∫dm(t)∫_ℝ M(x)M(x+t)(u(x) − u(x+t))²` a SIGNED jump
  energy with conductances `M(x)M(x+t)` (`markovEnergy_phiDoob_mul_eq_signedJump_add_source`).
  Harmonic gauges: no potential at all, `Q = J_M(u)` (`markovEnergy_phiDoob_mul_harmonic_eq_signedJump`);
  instances for every translate combination and every harmonic one. Tool: summation by parts of
  the commutator `∫ uM Comm(M,u) = J_M(u)` (`integral_mul_mul_plateauCommutator_eq_signedJumpEnergy`).
  Novelty check: corpus has only the finite-model version (`jumpEnergy_groundState`) and the
  ω_a-specific folded/two-sided representations. Insight: in a harmonic gauge every sign question is
  about negative conductances across the nodes of M (generalising "reflected jumps cross the origin");
  contains the two-sided representation (M = m_a) and the definition of Q (M = Φ). Standard axioms.
- **C13 · Theta convolutions: the continuous span of translate ground states** — `ThetaConvolutionGauges`.
  For `φ ∈ C²_c`, the gauge `ω_φ = (Φ∗φ)/Φ = ∫φ(b)τ_b db` (outside every finite span) satisfies
  `𝓛_Dω_φ − ρω_φ = −Φ(x)∫φ(b)cosh((x−b)/2)db = −Φ(A_φcosh(x/2) − B_φsinh(x/2))`
  (`twoSidedGenerator_convGauge_sub_potential`; superposition exchanged uniformly in `b` via the
  gamma source bound for arch, kernel-tail domination for primes). Lorentz law
  `markovEnergy(Φ(ω_φu_L)) → (B_φ² − A_φ²)/2` at rate `e^{−8L}` (`tendsto_markovEnergy_convPlateau`);
  harmonic convolutions (`A_φ = B_φ = 0`) lie in the radical and satisfy `Q(Φ(ω_φu)) = J_{Φ∗φ}(u)`.
  Insight: the plateau-limit energy of the whole convolution family factors through the 2-dim pole
  quotient `φ ↦ (A_φ, B_φ)` with the Lorentz form; frontier 4 ("outside the span") answered for the
  continuous span. Novelty check: `research "convolution riemannKernelReal gauge markovEnergy plateau"`
  — only unrelated `PaperThetaConvolutionGauge` (Meyer source jets). Standard axioms.
  Honest overlap note on C13: on the Weil side `Φ̂ = Ξ`, so `(Φ∗φ)^ = Ξ·φ̂` vanishes at every zero and
  the radical/Lorentz statements are the ACT-coordinate form of "Ξ-multiples are W-null, pole term
  = −F̂(i/2)F̂(−i/2)" (cf. `WeilMarkovOneBoundState`, `markovEnergy_translate`). PARTIAL overlap; the new
  content is the generator superposition and the gauge representation with conductances `(Φ∗φ)⊗(Φ∗φ)`.
- **C14 · Odd theta convolutions fail at infinity (no folded supersolution outside the span)** —
  `ThetaConvolutionFoldedInfinityFailure`. For odd `φ ∈ C²_c` with `M = Φ∗φ ≥ 0` on `(0,∞)`:
  exact folded defect `𝓛_Nω_φ − ρω_φ = Φ(x)[B_φ sinh(x/2) − 2C_φ(x)]` (`foldedDefect_convGauge`; the
  folded/two-sided relation proved for every odd ω ≥ 0 on the half line, all x); the prime sum of a
  theta convolution is a superposition of harmonic sums, `Σ Λ(n)n^{−1/2}M(log n − x) = ∫φ(b)P(x+b)db`
  (`tsum_atom_thetaConv_log_sub_eq`), hence `≥ A cosh + B sinh − K∫|φ|` beyond supp φ; quantitative
  `defect ≤ −Φ(x)[B_φ sinh(x/2) − 2K∫|φ|]`; pole moment `∫Msinh(x/2) = B_φ/2 > 0` on the nonzero cone;
  conclusion `exists_infinity_window_convGauge_foldedGenerator_lt_potential`. Insight: README 3.5's
  heuristic for general odd profiles ("reflected prime mass = twice the source + O(1)") is EXACT and
  PNT-free on the convolution class, because that class is precisely where the prime sum is a
  superposition of the harmonic identity (Weil side: M̂ = Ξφ̂ kills the zero terms of the explicit
  formula). Native: the folded generator has no Weil-side counterpart. Novelty: C1 covers finite
  spans only; corpus has no folded-defect statement for convolution gauges. Standard axioms.
- **C15 · Rate-criticality: the jump measure has no slack** — `JumpRateCriticality`. With the
  single-length Doob jump energy `J_ℓ(v) = ∫Φ(x)Φ(x+ℓ)(v(x)−v(x+ℓ))²`: for every `ℓ > 0`, `ε > 0` some
  odd `v ∈ C²_c` has `Q(Φv) < εJ_ℓ(v)` (`exists_odd_markovEnergy_lt_shiftJumpEnergy`); same for the
  archimedean density on any interval, `Q(Φv) < ε∫_{t₁}^{t₂}J_t(v)dt`
  (`exists_odd_markovEnergy_lt_integral_shiftJumpEnergy`); every prime-power rate is needed in full;
  **RH ⟺ Λ(n)n^{−1/2} is the least admissible rate at log n** for any single n ≥ 2
  (`riemannHypothesis_iff_isLeast_primeRate`); RH ⟺ nonneg ∧ rate-critical
  (`riemannHypothesis_iff_nonneg_and_rateCritical`). Mechanism: pole-free pair ω with ω(ℓ/2) ≠ 0 (odd ⇒
  jump across −ℓ/2 ↦ ℓ/2 is −2ω(ℓ/2)), window energy κ > 0 survives plateau truncation, Q = O(e^{−8L}).
  Insight (frontier 6, selectivity): under RH the von Mangoldt rates are minimal — the primes enter the
  odd form at exactly critical strength, prime by prime, and so does the Gamma density; companion of C5
  (potential side). Novelty check: `research "prime rate removal jump measure perturbation ..."` — none.
  Standard axioms.
  Corollary note: odd tests are primitive (`∫F cosh = 0`), so rate-criticality holds verbatim on the
  primitive hyperplane. Overlap correction: for the same reason C11's main statement already follows from
  C5; C11's distinct content is only the even null directions (they also separate the origin).
- **C16 · The zero form is a jump form in every odd gauge; gauge freedom of RH** —
  `ZeroFormJumpKernelGaugeFreedom`. For any gauge with source `σ sinh(x/2)Φ` and pole mass
  `∫Φω sinh = σ/2`: `Z(Φ(ωu)) = J_M(u) + V_μ(u)`, `V_μ(u) = ∫∫(u(x)−u(y))²μ(x)μ(y)`, `μ = M sinh(x/2)`
  (`zeroForm_phiDoob_mul_eq_signedJump_add_varianceEnergy`; algebra `varianceEnergy_eq`); instance for
  every odd theta convolution. Smeared shifted ground states `M = ∫ν(c)m_c dc` (ν ≥ 0 on (0,∞)) are
  positive on (0,∞) (`thetaConv_smearedProfile_pos`) and COMPLETE: RH ⟺ `J_M(u) + V_μ(u) ≥ 0` ∀ even
  `u ∈ C²_c` (`riemannHypothesis_iff_forall_smearedGauge_jumpForm_nonneg`), exact, no plateau limit.
  Insight: conductances are `M(x)M(y)·k(x,y)` with the gauge-free kernel `k = dm(|x−y|) + sinh(x/2)
  sinh(y/2)`; the variance part is positive for EVERY pair (μ ≥ 0), so the only negative conductances
  are crossing pairs where `dm(|x|+y) > sinh(|x|/2)sinh(y/2)`: near the axes (one point near the origin)
  for the Gamma density, and on every prime anti-diagonal `|x| + y = log n`. Generalises README 3.7's
  variance V_a to a continuum of gauges. Standard axioms.
- **C17 · The reflected prime mass at infinity (README 3.4 heuristic and frontier-4 reflected-mass
  asymptotic made exact via the PNT)** — `ReflectedPrimeMassAsymptotics`. For any `M ∈ C¹` with
  `M(0) = 0`, `|M|,|M'| ≤ Ce^{−2r}` on `[0,∞)`: `e^{−x/2}Σ_{log n>x}Λ(n)n^{−1/2}M(log n − x) →
  ∫_0^∞e^{r/2}M(r)dr` (`tendsto_exp_neg_half_mul_reflectedPrimeMass`; Abel summation + substitution
  `t = e^{x+r}` give the exact identity `= −∫_0^∞G'(r)e^{−x}ψ(e^{x+r})dr`, `G = e^{−r/2}M`; PNT
  `ψ(y)/y → 1` (corpus `RHTower.Sieve.tendsto_sum_vonMangoldt_div`) + dominated convergence). For
  shifted ground states: `e^{−x/2}C_a(x) → κ_a`, and **`C_a(x)/(sinh(a/2)sinh(x/2)) → R(a) = 2 +
  2∫_0^∞e^{−r/2}m_a/sinh(a/2)`** (`tendsto_shiftedCollarMass_div_source`), `R(a) > 2`
  (`two_lt_collarRatio`), `R(a) → 2` as `a → ∞` (`tendsto_collarRatio_atTop`); folded defect over
  source → `1 − R(a) < −1` (`tendsto_foldedDefect_shiftedGroundState_div_source`). New infrastructure:
  `|Φ'(u)| ≤ Ce^{−2|u|}`, `HasDerivAt Φ`, decay of `m_a, m_a'`. Insight: the collar reads the profile
  through `e^{r/2} = 2sinh(r/2) + e^{−r/2}` — "twice the source" is the sinh part, the exact excess is
  the moment at the OTHER pole (`s = 0`, weight `e^{−r/2}`). Small-shift end also proved:
  `R(a) → 1 + 8Φ(0) + 4σ` as `a → 0⁺` (`tendsto_collarRatio_nhdsGT_zero`; mean-value domination of
  `m_a/a → −2Φ'`, integration by parts `∫e^{−u/2}(−Φ') = Φ(0) − ½∫e^{−u/2}Φ`, `∫_0^∞e^{−u/2}Φ = 1/4 − σ`).
  README 3.4's heuristic sharpening is now a theorem at both ends. Standard axioms.
- **C18 · The cosh-moment law of folded failure** — `ThetaConvolutionCoshMomentLaw`. For every odd
  `φ ∈ C²_c` with `M = Φ∗φ ≥ 0` on `(0,∞)`: `(𝓛_Nω_φ − ρω_φ)(x)/(Φ(x)e^{x/2}) → −2∫_0^∞M(r)cosh(r/2)dr`
  (`tendsto_foldedDefect_convGauge_div`), negative for every nonzero profile
  (`integral_Ioi_thetaConv_mul_cosh_pos`); collar `e^{−x/2}C_φ(x) → ∫_0^∞e^{r/2}M`
  (`tendsto_exp_neg_half_mul_convCollarMass`). Tools: `(Φ∗φ)' = Φ∗φ'`, decay of `M, M'`, arch-collar
  bound. Insight: folding converts the odd profile's failure into its HALF-LINE COSH MOMENT — the sinh
  (odd-pole) parts of the exact two-sided source `B sinh(x/2)` and of the collar cancel to leading
  order, leaving the full `e^{±r/2}` average (even-pole quantity); exact quantitative form of frontier 4
  for the whole convolution class; reproduces `1 − R(a)` of C17 for `ω_a`. Standard axioms.
- **C19 · The weight criterion of fold domination fails for every large shift (README frontier 1 /
  3.9 question answered)** — `FoldExcessWeightCriterionFailure`. For every `x` with `0 < 2x < log 2`,
  `W_a(x) > 2sinh(a/2)sinh(x/2)` for all large `a` (`exists_foldExcessWeight_gt_criterion`); hence
  `exists_not_weightCriterion`: the criterion `W_a ≤ 2sinh(a/2)sinh(x/2)` ∀x>0 is false for all large
  shifts. Mechanism: `m_a(t−x) − m_a(t+x) = m_x(t−a) − m_x(t+a)` — the fold excess of `ω_a` at `x` is
  the reflected prime mass of the profile `m_x` read at `a`; by C17 it is `e^{a/2}(κ_x + o(1))`,
  `κ_x = sinh(x/2) + ∫_0^∞e^{−r/2}m_x`, while the criterion is `e^{a/2}(sinh(x/2) + o(1))`. The criterion
  fails by exactly the other-pole moment `∫_0^∞e^{−r/2}m_x > 0` (same excess as R(a)). No numerics;
  README's heuristic ("slope comparison fails for large a") made rigorous and strengthened (fails at
  every small x, not only in slope). What replaces it must absorb the other-pole moment. Standard axioms.
- **C20 · The variance is indispensable: criticality of the pure-jump RH form in every smeared gauge**
  — `SmearedGaugeVarianceCriticality`. In every smeared shifted ground state `M = ∫ν(c)m_c dc` (ν ≥ 0
  smooth on (0,∞)): ∀ε>0 ∃ even `u ∈ C²_c`, `Z(Φ(ω_νu)) < εV_μ(u)` (`exists_zeroForm_lt_mul_varianceEnergy`),
  so `J_M + (1−ε)V_μ` takes negative values and the signed jump energy alone is negative somewhere,
  unconditionally (`exists_signedJumpEnergy_add_lt`, `exists_signedJumpEnergy_neg`). Mechanism: pole-free
  pair `M'` divided by the gauge (corpus Hadamard division `smoothCoordinateQuotient`, cross-lane reuse
  from HTGeometry); slope at the origin `M'(0) = 2∫ν(−Φ') > 0` (integration by parts + MVT on strictly
  decreasing Φ, `deriv_thetaConv_smearedProfile_zero_pos`); quotient non-constant since `M' = cM` forces
  `0 = σ' = cB/2`; window variance lemma `setIntegral_setIntegral_sq_sub_pos`. Insight: no positive odd
  gauge makes the conductance form positive — the all-pairs variance (the pole-free source) is exactly
  critical; with C5 (potential) and C15 (rates) the RH form has no slack in any of its terms. Standard
  axioms. (Compile was delayed by another agent's cascade build; no interference.)
- **C21 · APT frontier answered: the odd-sector capacity ratio is asymptotically critical in the
  aperture** — `CapacityRatioApertureCriticality`. Bridge: APT's Markov part at any prime aperture
  beyond the autocorrelation support IS the ACT Markov energy (`markovForm_eq_markovEnergy`); RH ⟺ the
  odd capacity inequality `S(Φv)² ≤ 2M(Φv)` (`riemannHypothesis_iff_forall_odd_capacity_le`, = zero form);
  plateau truncations of every shifted-ground-state superposition with `σ ≠ 0` have
  `S²/(2M) → 1` (`tendsto_capacityRatio_spanPlateau`, `S → 2σ`, `M → 2σ²`, rate `e^{−8L}`); hence for every
  ε, at every large aperture R, some odd test supported in [−R,R] has capacity ratio > 1 − ε, for APT's
  own `markovForm` at every prime aperture `N ≥ e^{2R}` (`exists_odd_capacityRatio_markovForm_gt`).
  Answers APT README §5 "All apertures … the odd-sector capacity ratio S(g)²/(2M_N(g)) as the support
  aperture grows": it tends to its critical value 1 (no uniform margin); extremal directions = plateau
  truncations of positive odd gauges (capacity defect = zero form J_M + V_μ → 0). Cross-field (APT). Std axioms.
- **C22 · The pole-free Weil operator is the Doob source of every gauge; every positive profile
  fails at infinity (README 3.5 "at infinity" and frontier 4 for general profiles)** —
  `PoleFreeWeilOperatorAndProfileInfinityFailure`. Operator `𝒲M = Σ_nΛ(n)n^{−1/2}(M(·+log n)+M(·−log n))
  − ∫_0^∞[2ν(u)M − ω(u)(M(·+u)+M(·−u))]du + (γ+log π)M`; harmonic identity = `𝒲Φ = cosh(x/2)`
  (`poleFreeWeilOperator_riemannKernelReal`). EXACT for every profile with convergent prime sum and
  archimedean integral: `𝓛_D(M/Φ) − Φcosh(x/2)(M/Φ) = −Φ·𝒲M` (`twoSidedGenerator_profileGauge_sub_potential`;
  the potential is absorbed by the harmonic identity — C12/C16's source hypothesis is now explicit,
  `g = −𝒲M`). Folding: `𝓛_N ω = 𝓛_D(ω∘|·|)` on `x ≥ 0` (`foldedGenerator_eq_twoSidedGenerator_abs`), so the
  folded source is `−Φ𝒲(M∘|·|)`, all reflected points with + sign. In `𝒲(M∘|·|)` all prime terms are ≥ 0
  and the only negative part (archimedean second difference) is LOCAL, ≤ 2C(e⁸+1)J e^{−8x}
  (`integral_profileArchTerm_abs_le`). Main: every differentiable `M ≥ 0` on [0,∞) with `M(y₀) > 0`,
  `|M|,|M'| ≤ Ce^{−8|y|}` is a strict folded subsolution on a half line
  (`exists_infinity_window_profileGauge_foldedGenerator_lt_potential`; PNT supplies a prime power in every
  window (y, e^δ y], `exists_vonMangoldt_pos_mem_window`); PNT-free: every prime p ≥ N forces failure at
  `log p + y₀` (`profileGauge_foldedGenerator_lt_potential_at_prime_shift`); even positive profiles are strict
  two-sided subsolutions on a half line (`exists_infinity_window_even_profileGauge_twoSidedGenerator_lt_potential`,
  local strengthening of the trap "no even positive supersolution"). Insight: in test coordinates the
  supersolution question is the sign of one operator, and a single reflected prime atom `Λ(p)p^{−1/2}M(y₀)`
  (size `e^{−x/2}`) beats every local term (size `e^{−8x}`); the general-profile failure at infinity needs
  no collar asymptotics and no span structure (C1/C14/C18 were special cases). Novelty: corpus had only
  span (C1), convolution (C14) and origin (Θ-dominated) failures. Standard axioms.
- **C23 · The Doob source at infinity is a pole moment (frontier 4: the exact statement for every
  profile)** — `DoobSourcePoleMomentLawAtInfinity`. For every `M ∈ C¹`, `M(0) = 0`, `|M|,|M'| ≤ Ce^{−8|y|}`,
  NO sign condition: folded law `(𝓛_Nω − Φcosh(x/2)ω)/(Φe^{x/2}) → −2∫_0^∞M cosh(r/2)`
  (`tendsto_foldedSource_div`); for odd M two-sided law `(𝓛_Dω − Φcosh ω)/(Φe^{x/2}) → 2∫_0^∞M sinh(r/2)`
  (`tendsto_twoSidedSource_div`; reproduces `ω_a`'s exact source and C18's convolution law). New PNT
  piece: the DIRECT prime mass `e^{−x/2}Σ_{log n≤x}Λ(n)n^{−1/2}M(x−log n) → ∫_0^∞e^{−r/2}M`
  (`tendsto_exp_neg_half_mul_directPrimeMass`; Abel summation on [1,e^x], substitution t = e^{x−s}, DCT with
  `ψ(y) ≤ Ky` (`exists_psiSum_le_mul`)); with C17's reflected mass and the bounded archimedean term
  (`abs_integral_profileArchTerm_le`) and vanishing forward terms, via C22's exact source `−Φ𝒲`.
  Corollaries: ∫_0^∞Mcosh > 0 ⇒ strict folded subsolution on a half line; ∫_0^∞Mcosh < 0 ⇒ strict folded
  SUPERsolution on a half line (`exists_infinity_window_potential_lt_foldedGenerator_of_coshMoment_neg`).
  Insight: at infinity the arithmetic generator sees a profile ONLY through its moments at the pole
  `e^{±r/2}`; two-sided reads the odd pole moment (sinh), folding reads the half-line cosh moment; the
  folded supersolution inequality at infinity is exactly the sign of −∫_0^∞Mcosh — positive gauges can
  never satisfy it, sign-changing ones with negative cosh moment always do (so the obstruction to
  folded supersolutions is positivity + the cosh moment, not decay or regularity). Standard axioms.
- **C24 · The folded source at the origin is the jump-measure moment; two-moment necessary
  conditions for folded supersolutions** — `FoldedSourceOriginJumpMomentLaw`. For every `M ∈ C¹`,
  `M(0) = 0`, `|M|,|M'| ≤ Ce^{−8|y|}`, no sign condition: `(𝓛_Nω − Φcosh(x/2)ω)(x)/Φ(x) → −2∫M dm =
  −2[∫_0^∞ω(t)M(t)dt + Σ_nΛ(n)n^{−1/2}M(log n)]` as `x → 0⁺` (`tendsto_foldedSource_div_nhdsGT_zero`;
  = −𝒲(M∘|·|)(0⁺), series DCT + archimedean DCT with the Lipschitz majorant). With C23: a folded
  supersolution near the origin has `∫M dm ≤ 0` (`jumpMeasureMoment_nonpos_of_foldedSupersolution_near_zero`),
  near infinity has `∫_0^∞M cosh ≤ 0` (`coshMoment_nonpos_of_foldedSupersolution_near_infinity`). For
  nonnegative profiles both moments are positive (`jumpMeasureMoment_pos`, `coshMoment_pos`) ⇒ strict folded
  subsolution on (0,δ) AND on [X,∞) (`exists_origin_and_infinity_windows_foldedGenerator_lt_potential`) —
  README 3.5 in full generality: no Θ-domination, no ω(log 2) > 0 (the corpus origin theorem needed both).
  Insight: the folded generator reads a profile through exactly two linear functionals — the jump measure
  at the origin, the pole weight e^{±r/2} at infinity; the supersolution question at both ends is a sign
  condition on these moments. Standard axioms.
- **C25 · RH on the nonnegative cone: a criterion with no signed term** —
  `NonnegativeConeZeroFormCriterion`. Exact factorisation `Ẑ(F) = Q(F) + 2(∫Fe^{x/2})(∫Fe^{−x/2})`
  (`fullZeroForm_eq_markovEnergy_add_expMoments`) and the cone form
  `Ẑ(Φv) = E_arch(v) + E_prime(v) + 2E₊(Φv)E₋(Φv) − ∫Φcosh(x/2)v²` (`fullZeroForm_phiDoob_eq_cone`).
  **RH ⟺ ∀ v ∈ C²_c, v ≥ 0: ∫Φcosh(x/2)v² ≤ E_arch(v) + E_prime(v) + 2(∫Φve^{x/2})(∫Φve^{−x/2})**
  (`riemannHypothesis_iff_forall_nonneg_cone`): every term is a nonnegative functional of v; any test is
  lifted into the cone by `max|v|·u_L` (a theta-span plateau, invisible to Ẑ by C10's radical theorem).
  Sharpness: along u_L → 1 the jump energy → 0 and pole product, potential → 1/2
  (`tendsto_cone_terms_smoothPlateau`); for every ε > 0 the (1+ε)-strengthened inequality fails on the cone
  (`exists_nonneg_cone_violation`). Insight: the sign problem needs no signed quantity — on positive
  profiles the potential is paid by the Markov (Beurling–Deny) jump energy plus the PRODUCT of the two
  pole moments, the constant being the exact ground state; the cone is RH-complete because the radical
  contains a strictly positive element (Φ), unlike the half-line-nonneg odd cone (no positive pole-free odd
  span element), which the corpus (`WeilMarkovThinNonnegativeOddPositivity`) leaves open. Novelty: corpus
  one-sided cones are about values at ±log n of Weil tests, not positivity of the profile. Standard axioms.
