import GaloisForLFunctions.TransHorizonIncidenceMechanics.FourthRootPrimeWindowSieveAndGallagherLinearTransfer
import GaloisForLFunctions.ArithmeticCriticalityTheory.DoobJumpFoldedGroundStateRepresentation
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateTwoSidedRepresentation
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateCombinationFailure
import GaloisForLFunctions.HilbertMetric.HorizontalLamzouriMixedRangeSharp
import GaloisForLFunctions.HilbertMetric.HorizontalLamzouriRouteToMultiple

/-!
# Shifted Ground-State Collar Duality, Doob Half-Line Folding, and Lamzouri Four-Trace Bounds

This module connects `TransHorizonIncidenceMechanics` across the Lean corpus to
`ArithmeticCriticalityTheory` and `HilbertMetric`:

1. **Doob $h$-Transform Half-Line Folding and Reflected Collar Generator Split
   (`doob_halfLine_folding_and_collar_generator_split`):**
   Connects `twoSidedShiftGenerator_eq_folded_add_collar` and
   `integral_phiDoobArchShiftJump_groundState` (`DoobJumpFoldedGroundStateRepresentation.lean:60, 126`):
   for an odd ground state $\omega$ ($\omega > 0$ on $(0, \infty)$) and an even test $u \in C_c(\mathbb{R})$,
   the two-sided Dirichlet generator and the folded Neumann generator differ by the reflected collar
   $2 \Phi(x) \Phi(t-x) \max(\omega(t-x), 0)$, and the full-line Doob jump folds onto $(0, \infty)$
   as twice the same-side jump plus the reflected collar sum jump on $(0, t)$ plus twice the folded
   generator pairing.

2. **Two-Sided Shifted Ground-State Representation, Collar Duality, and Variation Inequality
   (`shiftedGroundState_collar_duality_and_twoSided_variation`):**
   Connects `reflectedSumEnergy_add_reflectedDifferenceEnergy_shiftedGroundState`,
   `markovEnergy_phiDoob_shiftedGroundState_eq_twoSided`, and
   `markovEnergy_phiDoob_shiftedGroundState_nonneg_iff_variation`
   (`ShiftedGroundStateTwoSidedRepresentation.lean:287, 331, 366`):
   collar reflection duality $R_a(u) + D_a(u) = 4 \int_{x>0} u^2 m_a C_a$ turns the folded
   representation of the shifted ground state $\omega_a$ ($a > 0$) into the two-sided identity
   $$\operatorname{markovEnergy}(\Phi(\omega_a u)) =
     2 S_a(u) - D_a(u) + 4 \sinh(a/2) \int_{x>0} u(x)^2 m_a(x) \sinh(x/2)\,dx,$$
   so nonnegativity of the Markov energy is equivalent to the variation inequality
   $D_a(u) \le 2 S_a(u) + 4 \sinh(a/2) \int_{x>0} u^2 m_a \sinh(x/2)$.

3. **Origin and Infinity Subsolution Obstruction for Shifted Ground-State Combinations
   (`shiftedGroundState_combination_origin_and_infinity_obstruction`):**
   Connects `exists_origin_window_combination_foldedGenerator_lt_potential` and
   `exists_infinity_window_combination_foldedGenerator_lt_potential`
   (`ShiftedGroundStateCombinationFailure.lean:21, 40`): every nonnegative nonzero combination
   $c_1 \omega_a + c_2 \omega_b$ ($a, b > 0$) is a strict folded subsolution both on an origin collar
   $(0, x_0)$ and on an asymptotic half-line $[X, \infty)$.

4. **Hilbert-Metric Horizontal Lamzouri Four-Trace Bound with Quadratic Mixed Gain and Pair Routing
   (`lamzouri_fourTrace_quadratic_mixedGain_and_pair_routing`):**
   Connects `HorizontalPacket.four_mass_sub_energy_le_sharp`
   (`HorizontalLamzouriMixedRangeSharp.lean:119`) and
   `HorizontalPacket.four_mass_sub_energy_route_eq` / `four_mass_sub_energy_le_route`
   (`HorizontalLamzouriRouteToMultiple.lean:119, 138`): bounds the four-trace discrepancy
   $4 \cdot \mathrm{mass} - E - 2N$ with the Cauchy–Schwarz quadratic mixed-range gain
   $(\#M - S)^2 / \#M$, and provides the exact identity and inequality when routing a subset $S$ of
   conjugate pairs $(2m_q, g_q), (-2m_q, h_q)$ to multiple real points.
-/

open MeasureTheory Set Filter Topology Finset Module
open scoped Real BigOperators RealInnerProductSpace
open _root_.RHTower _root_.RHTower.CHMDPolar
open GaloisForLFunctions.ArithmeticCriticalityTheory
open GaloisForLFunctions.HilbertMetric

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ## §1. Doob Half-Line Folding and Reflected Collar Generator Split -/

/-- **Doob Half-Line Folding and Reflected Collar Generator Split
(`doob_halfLine_folding_and_collar_generator_split`):**
For any continuous odd ground state $\omega : \mathbb{R} \to \mathbb{R}$ positive on $(0, \infty)$,
any continuous compactly supported even test $u : \mathbb{R} \to \mathbb{R}$, and any shift $t \ge 0$:
1. The two-sided and folded shift generators differ by the reflected collar
   $2 \Phi(x) \Phi(t-x) \max(\omega(t-x), 0)$.
2. The full-line Doob jump $\int_{\mathbb{R}} \Phi(x)\Phi(x+t)(v(x) - v(x+t))^2\,dx$ ($v = \omega u$)
   equals twice the same-side ground jump on $(0, \infty)$ plus the reflected ground jump on $(0, t)$
   plus $2 \int_{x>0} u(x)^2 \omega(x) \operatorname{foldedShiftGenerator}(\omega, t, x)\,dx$. -/
theorem doob_halfLine_folding_and_collar_generator_split
    {ω u : ℝ → ℝ} (hω : Continuous ω) (hodd : ∀ x, ω (-x) = -ω x)
    (hpos : ∀ x, 0 < x → 0 < ω x) (hu : Continuous u) (huc : HasCompactSupport u)
    (heven : ∀ x, u (-x) = u x) {t : ℝ} (ht : 0 ≤ t) (x : ℝ) :
    (twoSidedShiftGenerator ω t x =
      foldedShiftGenerator ω t x +
        2 * riemannKernelReal x * riemannKernelReal (t - x) * max (ω (t - x)) 0) ∧
    ((∫ y : ℝ, phiDoobArchShiftJump (fun z => ω z * u z) t y) =
      2 * (∫ y in Ioi (0 : ℝ), sameSideGroundJump ω u t y) +
        (∫ y in Ioo (0 : ℝ) t, reflectedGroundJump ω u t y) +
        2 * ∫ y in Ioi (0 : ℝ), u y ^ 2 * ω y * foldedShiftGenerator ω t y) :=
  ⟨twoSidedShiftGenerator_eq_folded_add_collar hodd hpos t x,
   integral_phiDoobArchShiftJump_groundState hω hodd hu huc heven ht⟩

/-! ## §2. Two-Sided Shifted Ground-State Representation and Collar Duality -/

/-- **Two-Sided Shifted Ground-State Representation, Collar Duality, and Variation Inequality
(`shiftedGroundState_collar_duality_and_twoSided_variation`):**
For every shift parameter $a > 0$ and every even $u \in C^2_c(\mathbb{R})$:
1. The reflected sum energy and reflected difference energy satisfy the collar duality identity
   $R_a(u) + D_a(u) = 4 \int_{x>0} u(x)^2 m_a(x) C_a(x)\,dx$.
2. The Markov energy on $\Phi(\omega_a u)$ satisfies the exact two-sided representation
   $\operatorname{markovEnergy}(\Phi(\omega_a u)) = 2 S_a(u) - D_a(u) + 4 \sinh(a/2) \int_{x>0} u^2 m_a \sinh(x/2)$.
3. Nonnegativity of $\operatorname{markovEnergy}(\Phi(\omega_a u))$ is equivalent to the variation
   inequality $D_a(u) \le 2 S_a(u) + 4 \sinh(a/2) \int_{x>0} u^2 m_a \sinh(x/2)$. -/
theorem shiftedGroundState_collar_duality_and_twoSided_variation
    {a : ℝ} (ha : 0 < a) {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u)
    (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    (reflectedSumEnergy (shiftedGroundState a) u +
        reflectedDifferenceEnergy (shiftedGroundState a) u =
      4 * ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * shiftedCollarMass a x) ∧
    (markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) =
      2 * sameSideEnergy (shiftedGroundState a) u -
        reflectedDifferenceEnergy (shiftedGroundState a) u +
        4 * Real.sinh (a / 2) *
          ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) ∧
    (0 ≤ markovEnergy (fun x => (phiDoobTest (fun y => shiftedGroundState a y * u y) x : ℂ)) ↔
      reflectedDifferenceEnergy (shiftedGroundState a) u ≤
        2 * sameSideEnergy (shiftedGroundState a) u +
          4 * Real.sinh (a / 2) *
            ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) :=
  ⟨reflectedSumEnergy_add_reflectedDifferenceEnergy_shiftedGroundState ha (hu.of_le (by norm_num)) huc,
   markovEnergy_phiDoob_shiftedGroundState_eq_twoSided ha hu huc heven,
   markovEnergy_phiDoob_shiftedGroundState_nonneg_iff_variation ha hu huc heven⟩

/-! ## §3. Origin and Infinity Subsolution Obstruction for Shifted Ground-State Combinations -/

/-- **Origin and Infinity Subsolution Obstruction for Shifted Ground-State Combinations
(`shiftedGroundState_combination_origin_and_infinity_obstruction`):**
For any $a, b > 0$ and nonnegative $c_1, c_2 \ge 0$ with $c_1 > 0 \vee c_2 > 0$, the combination
$c_1 \omega_a + c_2 \omega_b$ is a strict folded subsolution both on a right neighbourhood $(0, x_0)$
of the origin and on an asymptotic half-line $[X, \infty)$. -/
theorem shiftedGroundState_combination_origin_and_infinity_obstruction
    {a b : ℝ} (ha : 0 < a) (hb : 0 < b) {c₁ c₂ : ℝ}
    (hc₁ : 0 ≤ c₁) (hc₂ : 0 ≤ c₂) (hc : 0 < c₁ ∨ 0 < c₂) :
    (∃ x₀ : ℝ, 0 < x₀ ∧ ∀ x, 0 < x → x < x₀ →
      foldedGenerator (fun y => c₁ * shiftedGroundState a y + c₂ * shiftedGroundState b y) x <
        riemannKernelReal x * Real.cosh (x / 2) *
          (c₁ * shiftedGroundState a x + c₂ * shiftedGroundState b x)) ∧
    (∃ X : ℝ, 0 < X ∧ ∀ x, X ≤ x →
      foldedGenerator (fun y => c₁ * shiftedGroundState a y + c₂ * shiftedGroundState b y) x <
        riemannKernelReal x * Real.cosh (x / 2) *
          (c₁ * shiftedGroundState a x + c₂ * shiftedGroundState b x)) :=
  ⟨exists_origin_window_combination_foldedGenerator_lt_potential ha hb hc₁ hc₂ hc,
   exists_infinity_window_combination_foldedGenerator_lt_potential ha hb hc₁ hc₂ hc⟩

/-! ## §4. Hilbert-Metric Horizontal Lamzouri Four-Trace Bound with Quadratic Mixed Gain and Routing -/

/-- **Horizontal Lamzouri Four-Trace Bound with Quadratic Mixed Gain and Pair Routing
(`lamzouri_fourTrace_quadratic_mixedGain_and_pair_routing`):**
For any `HorizontalPacket` $P$ with $m_2 \ge 2$, $m_P \ge 1$, and $\|f_M\| \le 1$:
1. The four-trace functional $4 \cdot \mathrm{mass} - E - 2N$ plus the Cauchy–Schwarz quadratic
   mixed-range gain $(\#M - S)^2 / \#M$ ($S = \sum_M (\|f_M\|^2 - \|P_A f_M\|^2)$) is bounded by $\#H$.
2. For any subset $S \subseteq \iota_P$ of conjugate pairs routed to multiple real points via
   `P.routeToMultiple S`, the four-trace discrepancy satisfies the exact quadratic expansion
   `four_mass_sub_energy_route_eq` and the upper bound `four_mass_sub_energy_le_route`. -/
theorem lamzouri_fourTrace_quadratic_mixedGain_and_pair_routing
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    {ι₂ ιH ιM ιP : Type*} [Fintype ι₂] [Fintype ιH] [Fintype ιM] [Fintype ιP] [DecidableEq ιP]
    (P : HorizontalPacket V ι₂ ιH ιM ιP) (S : Finset ιP)
    (hm₂ : ∀ i, 2 ≤ P.m₂ i) (hmP : ∀ p, 1 ≤ P.mP p) (hMn : ∀ i, ‖P.fM i‖ ≤ 1) :
    (4 * P.mass - P.energy - 2 * P.count + 2 * ∑ i, (1 - ‖P.fH i‖ ^ 2)
      + ∑ i, (1 + 2 * ‖P.absorbing.starProjection (P.fM i)‖ ^ 2 - 2 * ‖P.fM i‖ ^ 2)
      + (Fintype.card ιM - ∑ i, (‖P.fM i‖ ^ 2 - ‖P.absorbing.starProjection (P.fM i)‖ ^ 2)) ^ 2
          / Fintype.card ιM
      ≤ Fintype.card ιH) ∧
    ((4 * P.mass - P.energy - 2 * P.count =
        4 * (P.routeToMultiple S).mass - (P.routeToMultiple S).energy -
            2 * (P.routeToMultiple S).count -
          ∑ q : {q // q ∈ S}, 2 * P.mP q *
            (4 * ‖P.h q‖ ^ 2 - 2 * (P.routeToMultiple S).diagForm (P.h q)) -
          ∑ q : {q // q ∈ S}, ∑ q' : {q // q ∈ S},
            2 * P.mP q * (2 * P.mP q') * ⟪P.h q, P.h q'⟫ ^ 2) ∧
      (4 * P.mass - P.energy - 2 * P.count ≤
        4 * (P.routeToMultiple S).mass - (P.routeToMultiple S).energy -
            2 * (P.routeToMultiple S).count +
          ∑ q : {q // q ∈ S}, 4 * P.mP q *
            ((P.routeToMultiple S).diagForm (P.h q) - 2 * ‖P.h q‖ ^ 2))) :=
  ⟨P.four_mass_sub_energy_le_sharp hm₂ hmP hMn,
   ⟨P.four_mass_sub_energy_route_eq S, P.four_mass_sub_energy_le_route S hmP⟩⟩

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
