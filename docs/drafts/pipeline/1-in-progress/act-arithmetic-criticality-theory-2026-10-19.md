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
- `ShiftedGroundStateFoldedDefect.lean` — source equation and reflected collar defect of `ω_a`.

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

**Status.** Origin failure for `ω_a`: Lean. Infinity failure: paper (P1 and the general asymptotic),
Lean open (window PNT transport). M5 answered negatively for the folded operator; M4's remaining
question (signed superpositions) is moot for the folded route. Programme continues on the
remainder-dominates-defect inequality.
- 2026-10-19 (late) — `ShiftedGroundStateOriginFailure` added and wired (nine modules): Lean proof that
  every shifted ground state is a strict folded subsolution on a right neighbourhood of `0`
  (`exists_origin_window_foldedGenerator_lt_potential`, prime `2` only), the
  remainder-dominates-defect identity `markovEnergy_phiDoob_shiftedGroundState_eq` and its
  nonnegativity criterion. The folded sufficiency route is closed as a no-go (section above); the
  programme's live object is the remainder-dominates-defect inequality and its two-sided twin.
