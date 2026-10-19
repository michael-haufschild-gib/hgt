# Arithmetic Criticality Theory: positive supersolutions for the odd-sector arithmetic jump form

- **ID:** act-2026-10-19
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean) for M1–M3 exact parts; CONJECTURE for M4–M5
- **Source:** docs/reports/review-1910/fable.md §4; receiver `riemannHypothesis_iff_odd_primeChain_poincare` (THIM) and `riemannHypothesis_iff_forall_odd_phiDoob_dirichlet_poincare` (RHTower)
- **Statement:** RH ⟺ the odd-sector form `E_arch + E_prime − ∫ Θ cosh(x/2) v²` is not supercritical. A positive odd `ω` with `𝓛_N ω ≥ Θ cosh(x/2) ω` on `(0,∞)` implies RH through the folded ground-state representation; the shifted ground states `ω_a = (Θ(·−a) − Θ(·+a))/Θ` are exact `𝓛_D`-supersolutions with source `2 sinh(a/2) sinh(x/2) Θ` and fail the `𝓛_N` condition by the reflected collar mass.

## Goal
Replace the sign problem (a bound) by an existence problem (one positive function). The identities are
unconditional; RH content enters only through the equation of motion of Riemann's kernel
(`theta_harmonic_identity`). Not circular: no positivity is assumed; a supersolution is a hypothesis
of an implication whose other direction (M5) is the open research question.

## Gates
- [x] 0 → 1  in-progress: well-posed (Section 3 of the README), source-pure (Doob coordinates of the literal Weil form), attack idea (ground-state representation with the folded generator), Door passport: the receiver is the existing odd Poincaré criterion.
- [ ] 1 → 2  fully-proven: M3 asymptotic failure of `ω_a` (paper), M4 superposition extremal problem.
- [ ] 2 → 3  formalized: M1 modules (see Log), M2, M3 exact identities.
- [ ] 3 → 4  not applicable (no stage 4; RH only).

## Approach
1. Pointwise ground-state identities; finite jump form; finite Allegretto–Piepenbrink both directions
   (Rayleigh minimiser + absolute value).
2. Folded ground-state representation of `markovEnergy (Θ v)` for odd `v = ω u`: nonnegative
   remainder plus `2∫_{x>0} u² ω (𝓛_N ω − Θ cosh(x/2) ω)`.
3. Sufficiency: folded supersolution ⟹ `markovEnergy (Θ v) ≥ 0` ⟹ RH.
4. Shifted ground states: source equation via `oddProfile_harmonic_identity`; folded defect
   `2Θ(x)[sinh(a/2) sinh(x/2) − C_a(x)]`.
5. Paper: PNT asymptotics of `C_a(x)`; ratio `2∫_0^∞ e^{s/2}(Θ(s−a)−Θ(s+a)) ds / sinh(a/2) > 1`.
6. M4/M5 as in README §5.

## Lean modules (formal/GaloisForLFunctions/ArithmeticCriticalityTheory/)
- `GroundStateRepresentationAlgebra.lean` — pointwise identities, finite GSR, easy direction.
- `FiniteJumpFormAllegrettoPiepenbrink.lean` — Schrödinger matrix, Rayleigh form, hard direction, connectivity.
- `DoobJumpFoldedGroundStateRepresentation.lean` — folded shift GSR for the Doob forms.
- `OddSupersolutionCriterion.lean` — total GSR and the sufficiency theorem.
- `ShiftedGroundStateSourceEquation.lean`, `ShiftedGroundStateReflectedCollarDefect.lean` — source
  equation and reflected collar defect of `ω_a`.
- `EvenSectorPoleCalibration.lean`, `ShiftedGroundStateSuperposition.lean`,
  `ShiftedGroundStateOriginFailure.lean` — even-sector calibration, linearity on the span, origin failure.
- `ShiftedGroundStateKernelBounds.lean`, `ShiftedGroundStatePotentialBounds.lean`,
  `ShiftedGroundStateRemainderBounds.lean`, `ShiftedGroundStateAdmissibility.lean` — the admissibility
  of `(ω_a, u)` for all `u ∈ C¹_c` and the unconditional remainder-dominates-defect identity.
- `ShiftedGroundStateInfinityFailure.lean` — P1 in Lean: `C_a(x) ≥ 2 sinh(a/2) sinh(x/2) − K` for
  `x ≥ a` and the strict folded subsolution window `[X, ∞)`.

## No-go closure (mandatory when falsified)
- **Exact killing theorem/mechanism:** (open)
- **Strongest positive survivor:** (open)
- **New insight:** (open)
- **Status:** (open)

## Log
- 2026-10-19 — created in 1-in-progress from docs/reports/review-1910/fable.md §4; README written; module 1 drafted.

## Paper results (19 October 2026)

**P1 (M3, asymptotic failure of the shifted ground states).** Fix `a > 0`. Write
`m̃_a(s) = Θ(s−a) − Θ(s+a)` (positive for `s > 0`) and `C_a(x) = A_a(x) + P_a(x)` with
`A_a(x) = ∫_0^∞ ω(x+s) m̃_a(s) ds` and `P_a(x) = Σ_{log n > x} Λ(n) n^{−1/2} m̃_a(log n − x)`
(this is `shiftedCollarMass a x` in Lean). Claim: `C_a(x) > sinh(a/2) sinh(x/2)` for all large `x`.
Proof. (i) `A_a(x) ≤ ω(x) ∫_0^∞ m̃_a = O(e^{−x/2})` since `ω` is decreasing on `(0,∞)`.
(ii) Stieltjes form `P_a(x) = ∫_{e^x}^∞ y^{−1/2} m̃_a(log y − x) dψ(y)`. Replace `dψ(y)` by `dy`:
`∫ y^{−1/2} m̃_a(log y − x) dy = e^{x/2} κ(a)` with `κ(a) = ∫_0^∞ e^{s/2} m̃_a(s) ds` (substitute
`y = e^{x+s}`). The remainder is `−∫_{e^x}^∞ (ψ(y) − y) d[y^{−1/2} m̃_a(log y − x)]` (boundary terms
vanish since `m̃_a(0) = 0` and `Θ` decays super-exponentially); with `|ψ(y) − y| ≤ ε(y) y`, `ε → 0`
(prime number theorem), it is bounded by `sup_{y ≥ e^x} ε(y) · e^{x/2} ∫_0^∞ e^{s/2}(|m̃_a| + |m̃_a'|)(s) ds
= o(e^{x/2})`. So `C_a(x) = e^{x/2}(κ(a) + o(1))` while `sinh(a/2) sinh(x/2) = e^{x/2}(sinh(a/2)/2 + o(1))`.
(iii) `2κ(a) > sinh(a/2)`: with `I(a) = ∫_a^∞ e^{u/2}Θ`, `J(a) = ∫_a^∞ e^{−u/2}Θ`,
`κ(a) = e^{a/2}(1/2 − J(a)) − e^{−a/2} I(a)` (because `∫_ℝ e^{u/2}Θ = 1/2`, Lean
`integral_riemannKernelReal_exp_half`), hence
`2κ(a) − sinh(a/2) = ½[e^{a/2}(1 − 4J(a)) − e^{−a/2}(4I(a) − 1)]`. Since `I(0) + J(0) = 1/2` and
`I(0) − J(0) = 2σ`, `σ = ∫_0^∞ Θ sinh(u/2) > 0`, we have `J(a) ≤ 1/4 − σ`, `I(a) ≤ 1/4 + σ`, so
`e^{a}(1 − 4J(a)) ≥ 4σ e^{a} > 4σ ≥ 4I(a) − 1` for `a > 0`. The limiting ratio
`R(a) = 2κ(a)/sinh(a/2)` tends to `1 + 8Θ(0) + 4σ` as `a → 0` (from `κ(a) = a(2Θ(0) + I(0)) + O(a²)`)
and to `2` as `a → ∞`. ∎ (Paper; Lean: identities done, window PNT transport open.)

**P2 (M4, positive superpositions).** On the cone of odd `ω` with `ω > 0` on `(0,∞)`, the reflected
collar `2Φ(x)Φ(t−x) ω(t−x)⁺` equals `2Φ(x)Φ(t−x) ω(t−x) 1_{t>x}` and is linear in `ω`; the two-sided
generator is linear. Hence for `c_j ≥ 0` the folded defect of `Σ c_j ω_{a_j}` is
`2Φ(x) Σ c_j [sinh(a_j/2) sinh(x/2) − C_{a_j}(x)]`, eventually negative by P1. No positive finite
superposition of shifted ground states is a folded supersolution near infinity. Signed superpositions
and supersolutions outside this span remain open (M4 continued, M5).

**Selectivity gate.** The identities (ground-state representations, generator comparison) hold for
any even positive kernel. The arithmetic enters only through `theta_harmonic_identity`, which encodes
the explicit formula for `ζ`; for `ζ(s−a)ζ(s+a)` the potential has two poles and the source equation
changes. The P1 failure uses the prime number theorem only.

## Log (continued)
- 2026-10-19 — Lean modules compiled and wired: `GroundStateRepresentationAlgebra`,
  `FiniteJumpFormAllegrettoPiepenbrink`, `DoobJumpFoldedGroundStateRepresentation`,
  `OddSupersolutionCriterion` (sufficiency theorem `riemannHypothesis_of_foldedSupersolution`).
  `ShiftedGroundStateSourceEquation`, `ShiftedGroundStateReflectedCollarDefect`,
  `EvenSectorPoleCalibration` written; compile in progress. Paper results P1, P2 recorded.
- 2026-10-19 — All seven modules compile (`lake --old env lean -j 1`, one at a time), umbrella
  `GaloisForLFunctions/ArithmeticCriticalityTheory.lean` audited with `lake env lean`, wired into
  `MainTheorems.lean` and registered as theorem area `arithmetic_criticality_theory` in
  `scripts/formal_tools.py`. `#print axioms` on the ten main theorems: `propext`, `Classical.choice`,
  `Quot.sound` only. Gate 2 → 3 for M1, M2 and the exact part of M3 is met; M3 asymptotic (P1) and
  M4/M5 remain paper or open.
- 2026-10-19 — `ShiftedGroundStateSuperposition` added and wired: the folded defect is linear on the
  span of the shifted ground states, and a nonnegative nonzero combination of two of them is a folded
  supersolution at `x` only if one constituent is (`exists_constituent_supersolution_of_combination`).
  Together with paper result P1 this is P2 in Lean form for two constituents (general finite sums are
  the same induction). Eight modules total; umbrella audited; lint gate passes for this area; index
  regenerated. Remaining open: P1 in Lean (window prime number theorem transport), signed
  superpositions, discharging `FoldedAdmissible` for explicit `ω`, M5.

## No-go closure of the folded sufficiency route (19 October 2026, evening)

**Exact killing mechanism.** Write `g = Θω` (test coordinate, odd, `g ≥ 0` on `(0,∞)`). Using
`theta_harmonic_identity` to replace the prime rate, the folded defect at `x > 0` is exactly

    𝓛_N ω − Θ cosh(x/2) ω = Θ(x) · [ 𝒜g(x) − 2c g(x) − Σ_n Λ(n) n^{−1/2} ( g(x + log n) + g(|x − log n|) ) ],

with `c = (γ + log π)/2` and the regularised archimedean term
`𝒜g(x) = ∫_0^∞ [2ν(u) g(x) − ω(u)(g(x+u) + g(|x−u|))] du` (the diagonal densities `ν` cancel against
the Lévy density; only differences converge). Consequences:

- **At the origin:** `g(0) = 0`, so `𝒜g(0+) = −2∫_0^∞ ω(u) g(u) du < 0` while the prime sum tends to
  `2 Σ_n Λ(n) n^{−1/2} g(log n) > 0`. Hence the folded defect is strictly negative on a right
  neighbourhood of `0` for **every** odd continuous profile with `g ≥ 0`, `g ≢ 0` on `(0,∞)`. For
  `ω = ω_a` this is proved in Lean with the single prime `2`
  (`ShiftedGroundStateOriginFailure`): `C_a(x) ≥ Λ(2) 2^{−1/2} (Θ(log 2 − x − a) − Θ(log 2 − x + a))`,
  which stays positive as `x → 0` while the source `sinh(a/2) sinh(x/2) → 0`.
- **At infinity:** the reflected prime term `Σ_{log n > x} Λ(n) n^{−1/2} g(log n − x)` is, by the
  prime number theorem in a window (corpus: `ChebyshevShortWindowLowerBound`,
  `ChebyshevMultiplicativeWindowZeroSum`, `LogWindowPrimeNumberTheorem`), asymptotic to
  `e^{x/2} ∫_0^∞ e^{r/2} g(r) dr`; the term below `x` is asymptotic to `e^{x/2}∫_0^x e^{−r/2} g`; both are
  positive, while `𝒜g(x) − 2c g(x) = O(g(x) + ‖g''‖_{[x−1,x+1]} + e^{−x/2})`. For every admissible `g`
  (bounded with bounded second derivative, `∫_0^∞ e^{r/2} g < ∞`, which is what finiteness of the
  generator requires) the folded defect is asymptotically `−e^{x/2} Θ(x) · 2∫_0^∞ cosh(r/2) g(r) dr`,
  strictly negative. For `g = Θ(·−a) − Θ(·+a)` this is P1.

**Verdict.** The hypothesis of `riemannHypothesis_of_foldedSupersolution` is never satisfied: there is
no folded supersolution, near `0` for any profile and near `∞` for any admissible profile. The folded
Allegretto–Piepenbrink hard direction fails for the odd arithmetic form, and the reason is concrete:
the reflected prime mass returns with weight `e^{x/2} e^{±r/2}` while the potential sees `g` only at
`x`. This is the exact meaning of "the odd form is not of Z-type".

**Strongest positive survivor.** The folded ground-state representation itself:
`markovEnergy (Θ (ω u)) = R_N(ω,u) − 2∫_{x>0} u² ω |defect_ω|` wherever the defect is negative, so RH is
equivalent (for each fixed admissible `ω`, over all even `u`) to the **remainder-dominates-defect
inequality** `R_N(ω,u) ≥ 2∫_{x>0} u(x)² ω(x) |defect_ω(x)| dx`, in which both sides are explicit. For
`ω = ω_a` the right side is `4∫ u² ω_a Θ(x)(C_a(x) − sinh(a/2) sinh(x/2))` (Lean:
`markovEnergy_phiDoob_shiftedGroundState_eq`), and the left side is the sum of the same-side squares
`(u(x) − u(x+t))²` and the reflected squares `(u(x) + u(t−x))²`. This is THIM's absorption problem in
closed form; the two-sided representation (GSR-D, with `ω_a` an exact strict supersolution) trades the
negative potential for a negative reflected remainder `−Θ(x)Θ(t−x)ω(x)ω(t−x)(u(x) − u(t−x))²`.

**New insight.** Positivity, if RH holds, is carried entirely by the remainder, never by the
potential; a supersolution-based proof must therefore be a *subsolution-plus-remainder* proof. The
quantity that decides is the comparison of two explicit nonnegative functionals of `u`, not the sign
of a generator defect.

**Status.** Origin failure for `ω_a`: Lean. Infinity failure for `ω_a`: Lean
(`ShiftedGroundStateInfinityFailure`, no prime number theorem: the theta harmonic identity gives
`C_a(x) ≥ 2 sinh(a/2) sinh(x/2) − K` for `x ≥ a`); the general asymptotic for arbitrary admissible
profiles remains paper. M5 answered negatively for the folded operator; M4's remaining
question (signed superpositions) is moot for the folded route. Programme continues on the
remainder-dominates-defect inequality.
- 2026-10-19 (late) — `ShiftedGroundStateOriginFailure` added and wired (nine modules): Lean proof that
  every shifted ground state is a strict folded subsolution on a right neighbourhood of `0`
  (`exists_origin_window_foldedGenerator_lt_potential`, prime `2` only), the
  remainder-dominates-defect identity `markovEnergy_phiDoob_shiftedGroundState_eq` and its
  nonnegativity criterion. The folded sufficiency route is closed as a no-go (section above); the
  programme's live object is the remainder-dominates-defect inequality and its two-sided twin.
- 2026-10-19 (night) — `FoldedAdmissible (ω_a) u` discharged in Lean for every `a > 0` and every
  `u ∈ C¹_c(ℝ)` (`foldedAdmissible_shiftedGroundState`, four new modules, thirteen in total, umbrella
  audited, axioms `propext`/`Classical.choice`/`Quot.sound` only, lint passes, index regenerated).
  Mechanism: in test coordinates the potential density is `u(x)² K_a(t,x)` with
  `|K_a(t,x)| ≤ K t` (Lipschitz bounds of `Φ` and of the shift difference on `[−R−1, R+1]`) and
  `|K_a(t,x)| ≤ K Φ(t − R − a)` (antitonicity of `Φ`), for `0 < x ≤ R`; the ground remainder obeys
  `|rem_a(t)| ≤ C t` and `|rem_a(t)| ≤ 16Φ(0)M_u²R Φ(t − R − a)` because the reflected jump on the
  collar lives on two intervals of length `≤ R`. Integrability against the Lévy density uses
  `∫_0^∞ ω(t) t dt < ∞`; summability against the von Mangoldt atoms uses
  `Σ Λ(n) n^{−1/2} Φ(log n − c) < ∞` (corpus `summable_primeShift_left`); measurability of
  `t ↦ rem_a(t)` by Fubini-type strong measurability of parametric integrals, and of the prime
  generator by a.e. limits of partial sums. Consequence: the remainder-dominates-defect identity and
  its nonnegativity criterion hold for every even `u ∈ C²_c` with no side hypothesis
  (`markovEnergy_phiDoob_shiftedGroundState_eq_of_contDiff`,
  `markovEnergy_phiDoob_shiftedGroundState_nonneg_iff_of_contDiff`). Remaining Lean gap of the no-go
  closure: P1 (infinity failure) via the window prime number theorem.
- 2026-10-19 (night, 2) — **P1 in Lean, without the prime number theorem.**
  `ShiftedGroundStateInfinityFailure` (fourteen modules, umbrella audited): for `x ≥ a ≥ 0`,
  `shiftedCollarMass a x ≥ 2 sinh(a/2) sinh(x/2) − K` with the universal constant
  `K = 2|c|Φ(0) + 4∫_0^∞ gammaSourceBound + Σ Λ(n)n^{−1/2}Φ(log n)`
  (`two_mul_source_sub_le_shiftedCollarMass`), hence the folded defect of `ω_a` is at most
  `−2Φ(x)(sinh(a/2) sinh(x/2) − K)` (`foldedDefect_shiftedGroundState_le`) and `ω_a` is a strict
  folded subsolution on a half line `[X, ∞)` (`exists_infinity_window_foldedGenerator_lt_potential`).
  Mechanism: `m_a(log n − x) = Φ(x+a−log n) − Φ(x−a−log n)`, so the signed prime shift sum is
  `P(x+a) − P(x−a)` with `P(y) = Σ Λ(n)n^{−1/2}Φ(y − log n) = primeKernelSum y − Q(y)`; the corpus's
  `theta_harmonic_identity` gives `primeKernelSum y = cosh(y/2) − 2cΦ(y) + ∫_0^∞ symArchTerm y`, the
  cosh difference is exactly `2 sinh(a/2) sinh(x/2)`, `Q(y) ∈ [0, Q(0)]` for `y ≥ 0`, and
  `|∫ symArchTerm y| ≤ 2∫ gammaSourceBound` uniformly in `y` (corpus `abs_gammaSourceTerm_le_bound`).
  The collar mass keeps only the positive parts, so it dominates the signed sum. This supersedes the
  window-PNT plan: the earlier paper estimate `2κ(a)/sinh(a/2) > 1` is replaced by the exact lower
  bound with ratio `≥ 2 − o(1)`, consistent with `κ(a) > sinh(a/2)` from the closed form
  `κ(a) = e^{a/2}(1/2 − G(a)) − e^{−a/2}F(a)`. Axioms: `propext`, `Classical.choice`, `Quot.sound`.
  M3 is now fully in Lean; M5's negative answer for `ω_a` is in Lean at both ends.
- 2026-10-19 (night, 3) — `ShiftedGroundStateCombinationFailure` (fifteen modules): a nonnegative
  nonzero combination `c₁ω_a + c₂ω_b` is a strict folded subsolution on a right neighbourhood of `0`
  and on a half line `[X, ∞)` (from `exists_constituent_supersolution_of_combination` and the two
  single-profile windows). This is P2 in Lean at both ends for two constituents; finite sums are the
  same induction. README rewritten as mathematics only (user: the README is not a diary); status and
  logs live here.
- 2026-10-19 (night, 4) — **Two-sided representation in Lean** (`ShiftedGroundStateCollarFubini`,
  `ShiftedGroundStateTwoSidedRepresentation`; seventeen modules). Collar Fubini:
  `∫dm(t)∫_0^t m_a(x)m_a(t−x)u(x)² = ∫_{x>0} u² m_a C_a` (product integrability from
  `m_a(x)m_a(t−x)⁺ ≤ Φ(0)max(L,Φ(0)) t` and `∫ω(t)t < ∞`; prime side from the decay
  `m_a(y−x)⁺ ≤ (Φ(0)/Φ(R+a))Φ(y−R−a)`). With `reflectedGroundJump + reflectedDifferenceJump =
  2ΦΦωω(u(x)² + u(t−x)²)` and the reflection of the collar, `P + D = 4∫u² m_a C_a`, hence for every
  `a > 0` and even `u ∈ C²_c`: `markovEnergy(Φ(ω_a u)) = 2S − D + 4 sinh(a/2)∫_{x>0} u² m_a sinh(x/2)`
  (`markovEnergy_phiDoob_shiftedGroundState_eq_twoSided`), Markov positivity ⟺ the variation
  inequality `D ≤ 2S + 4 sinh(a/2)∫u² m_a sinh(x/2)`
  (`markovEnergy_phiDoob_shiftedGroundState_nonneg_iff_variation`), and RH ⟹ it
  (`reflectedDifferenceEnergy_le_of_riemannHypothesis`). Corpus audit before building: CHMD/THIM own
  the pointwise pieces in `oddProfile` coordinates (`oddProfileCollarDiffSq`, `oddProfileShiftJump`,
  `oddProfileCollarMixed`, `oddSinhPotential`, THIM Obstacle B bounds on `3t/2 ≤ a`) but not the
  exact global identity; in their coordinates it reads
  `markovEnergy(oddProfileTest a w) = 2·direct − collar + oddSinhPotential a w` (coefficient exactly
  `1` on the sinh potential, no support radius). The bridge in corpus coordinates needs a scaling
  lemma for `markovEnergy` (none found by grep) and is left to THIM.
- 2026-10-19 (night, 5) — **Monotone fold domination** (`ShiftedGroundStateMonotoneFoldDomination`,
  eighteen modules). For `u` even, nonnegative, nonincreasing on `[0,∞)`: on `0 < x < t/2`,
  `0 ≤ u(x) − u(t−x) ≤ u(x) − u(x+t) ≤ u(x)`, so with the collar symmetry
  `D(t) ≤ 2S(t) + 2E_a(t)`, `E_a(t) = ∫_0^{t/2} m_a(x)(m_a(t−x) − m_a(x+t))⁺u(x)²`
  (`integral_reflectedDifference_le_two_sameSide_add_two_foldExcess`); fold-excess Fubini
  `∫dm E_a = ∫_{x>0} u² m_a W_a` with `W_a(x) = ∫_{t>2x} dm(t)(m_a(t−x) − m_a(x+t))⁺`; hence
  `markovEnergy(Φ(ω_a u)) ≥ 4 sinh(a/2)∫u² m_a sinh(x/2) − 2∫u² m_a W_a`
  (`markovEnergy_phiDoob_shiftedGroundState_ge_of_antitone`) and the weight criterion
  `W_a(x) ≤ 2 sinh(a/2) sinh(x/2) ∀x>0 ⟹ Markov positivity on all such u`
  (`markovEnergy_phiDoob_shiftedGroundState_nonneg_of_antitone_of_weight_le`). `foldExcessDensity`
  vanishes for `x + t ≤ a` (`m_a` increasing on `[0,a]`). Paper analysis of the criterion (not
  formalised): both sides vanish at `x = 0`; slopes compare as
  `J_a := ∫_{t>t_a} dm |m_a'| ≤ sinh(a/2)/2`; for large `a`, under the prime number theorem
  `J_a ≈ e^{a/2}∫_0^∞ e^{s/2}|Θ'| = e^{a/2}(Θ(0) + 1/8 + σ/2)` versus `e^{a/2}/4`, so the pointwise
  criterion fails at the origin unless `Θ(0) + σ/2 ≤ 1/8` (it does not: the `n = 1` term of `Θ(0)`
  is `(4π² − 6π)e^{−π} > 1/8`); the deficit sits exactly at the origin, where the monotone bound is
  tight, and would have to be paid by the dropped same-side terms `x > t/2`. So the monotone cone
  does not close by a pointwise weight; the exact statement is the lower bound above.
- 2026-10-20 — **Bridge to THIM coordinates** (`ShiftedGroundStateOddProfileCoordinates`, nineteen
  modules): `markovEnergy ((c:ℂ) • f) = c² markovEnergy f` (scaling of `EF.weilTest`,
  `weilFullFunctional_smul`, `weilPoleTerm`), `m_a = 2 sinh(a/2) oddProfile a`,
  `oddProfileTest a w = Φ(ω_a w)/(2 sinh(a/2))`, hence
  `markovEnergy(oddProfileTest a w) = (2S − D)/(4 sinh²(a/2)) + 2∫_{x>0} oddProfile a · sinh(x/2) · w²`
  (`markovEnergy_oddProfileTest_eq_twoSided`) and Markov positivity on `oddProfileTest a w` ⟺
  `D ≤ 2S + 8 sinh²(a/2)∫ oddProfile sinh w²` (`markovEnergy_oddProfileTest_nonneg_iff_variation`).
  The right side's integral is THIM's `oddSinhPotential a w` by `oddSinhPotential_eq_halfLine`; THIM's
  Obstacle B (collar ≤ direct + absorbed arch on `3t/2 ≤ a`) is a partial case of this exact identity.
- 2026-10-20 — **General origin failure in Lean** (`OddProfileOriginFailure`,
  `SignedCombinationOriginFailure`; twenty-one modules). For every odd continuous `ω ≥ 0` on
  `[0,∞)` with `ω(log 2) > 0`, Lipschitz on `[−1,1]` and `Φω ≤ CΦ(·−b)` on the half line, the folded
  defect is negative on a right neighbourhood of `0`
  (`exists_origin_window_foldedGenerator_lt_potential_of_profile`). Mechanism: prime-`2` term
  `→ −2Λ₂Φ(0)Φ(log 2)ω(log 2)`; archimedean part `≤ 3Φ(0)²L√x ∫(t^{−1/2}1_{t≤1} + e^{−t/2}1_{t>1})`
  (Lipschitz for `t ≤ x`, drop `−Φ(x±t)ω(·) ≤ 0` for `t > x`); other primes
  `≤ Φ(x)ω(x)·primeKernelSum x ≤ Φ(0)Lx(cosh(x/2) + 2|c|Φ(0) + 2∫gammaSourceBound)`; potential
  `≥ 0`; non-integrable/non-summable cases handled by the Bochner convention or excluded by the
  domination hypothesis. Instances: `ω_a` (`shiftedGroundState_origin_failure_of_profile`) and every
  signed combination `c₁ω_a + c₂ω_b` nonnegative on `(0,∞)`, positive at `log 2`
  (`exists_origin_window_signedCombination_foldedGenerator_lt_potential`), using
  `Φ(y−a) ≤ (Φ(0)/Φ(b))Φ(y−b)`. M4 (signed superpositions) and M5 (every profile) are now closed at
  the origin in Lean; the infinity side for signed combinations remains open.
- 2026-10-20 — Parallel agent: `ShiftedGroundStateFoldExcessThresholdAndOddProfileDomination.lean`
  (not mine, not yet wired; lint reports it unreachable until its author wires it): fold-excess
  density vanishes for `t ≤ max(2x, a − x)`, hence all primes with `log n ≤ 2a/3` (prime `2` for
  `a ≥ (3/2) log 2`) drop out of `W_a`; support-localised weight criterion; odd-profile transfer.
  Left untouched per the shared-repo discipline.
