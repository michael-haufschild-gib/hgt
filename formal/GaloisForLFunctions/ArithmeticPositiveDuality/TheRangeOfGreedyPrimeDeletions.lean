import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.PrimeWindowsBelowTheOutermostZero

/-!
# The range of the half-dimension law for greedy prime deletions

Short prime windows control the error in the greedy Chebyshev mass.
The square contribution is the second Weyl term; its odd coefficient
forces the deleted-integer counting error to have exponent at least
half the dimension. The window exponent may be chosen close to one
when the deletion dimension is small.
-/

noncomputable section
open Filter Asymptotics
open _root_.RHTower _root_.RHTower.PrimeDeletion
open GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

namespace GaloisForLFunctions.ArithmeticPositiveDuality

/-- Two-term prime-power mass and the corresponding sharp obstruction
to a smaller exponent for the count of surviving integers. -/
def greedyHalfDimensionLaw (κ : ℝ) : Prop :=
  (∃ η < κ/2, (fun x : ℝ => deletedChebyshev (greedyDeletion κ) x -
    (1/κ)*(x^κ+x^(κ/2))) =O[atTop] fun x => x^η) ∧
  ∀ a θ : ℝ, 0 ≤ θ → θ < κ/2 →
    ¬(fun x : ℝ => qFreeCount (greedyDeletion κ) x-a*x) =O[atTop] fun x => x^θ

private theorem greedy_law_of_windows {g κ : ℝ} (hκ : 0 < κ) (hκ1 : κ < 1)
    (hg : g < 1-κ/2) (hw : ∀ α : ℝ, max g (1-κ) < α → α < 1 →
      ∃ X : ℝ, 1 ≤ X ∧ ∀ y L : ℝ, X ≤ y → 0 ≤ L →
        (L-(y+L)^α)/2 ≤ Chebyshev.theta (y+L)-Chebyshev.theta y) :
    greedyHalfDimensionLaw κ := by
  obtain ⟨α,ha,hακ⟩ := exists_between (max_lt hg (by linarith only [hκ] : 1-κ < 1-κ/2))
  have ha1 : α < 1 := by linarith only [hακ,hκ]
  obtain ⟨X,hX,hwindow⟩ := hw α ha ha1
  obtain ⟨η,hη,hO⟩ := greedy_chebyshev_expansion hκ hκ1 ha1
    (by linarith only [(le_max_right g (1-κ)).trans_lt ha]) (by linarith only [hακ])
    (by norm_num : (0:ℝ)<2) (zero_le_one.trans hX) hwindow
  refine ⟨⟨η,hη,hO⟩,fun a θ hθ hθκ => ?_⟩
  exact not_isBigO_qFreeCount_of_odd (greedyDeletion κ) (l:=1) odd_one hθ hθκ hη hκ hκ1
    (by simpa only [Nat.cast_one] using hO)

/-- Unconditional range for the actual greedy deletion, including all
positive dimensions below one half. -/
theorem greedy_half_dimension_below_thirteen_fifteenths {κ : ℝ} (hκ : 0 < κ) (h : κ < 13/15) :
    greedyHalfDimensionLaw κ :=
  greedy_law_of_windows (g:=17/30) hκ (by linarith only [h]) (by linarith only [h])
    (fun _ ha ha1 => exists_theta_window_lower_seventeenThirtieths
      ((le_max_left _ _).trans_lt ha) ha1)

private theorem chained_window {α : ℝ} (ha : 0 ≤ α)
    (h : ∀ᶠ x : ℝ in atTop, x^α/2/2 ≤ Chebyshev.theta (x+x^α/2)-Chebyshev.theta x) :
    ∃ X : ℝ, 1 ≤ X ∧ ∀ y L : ℝ, X ≤ y → 0 ≤ L →
      (L-(y+L)^α)/2 ≤ Chebyshev.theta (y+L)-Chebyshev.theta y := by
  obtain ⟨X,hX⟩ := eventually_atTop.mp h
  exact ⟨max 1 X,le_max_left _ _,theta_window_lower_of_step ha (by norm_num)
    (le_max_left _ _) fun y hy => hX y ((le_max_right _ _).trans hy)⟩

/-- Each zero strip through z improves the admissible deletion dimension
according to its truncated density slope. -/
theorem greedy_half_dimension_of_density_strip {z s κ : ℝ} (hz : zetaZeroAbscissa ≤ z)
    (hz0 : 1/2 < z) (hz1 : z ≤ 3/4) (hs : 1 ≤ s) (hs1 : s < 4/3)
    (hκ : 0 < κ) (hκ1 : κ < 1) (hk : 1-(1-z)/(1-s*(z-1/2)) < 1-κ/2) :
    greedyHalfDimensionLaw κ := by
  apply greedy_law_of_windows hκ hκ1 hk
  intro α ha ha1
  exact chained_window (by linarith only [(le_max_right _ _).trans_lt ha,hκ1])
    (prime_window_from_truncated_density hz hz0 hz1 hs hs1 ((le_max_left _ _).trans_lt ha) ha1)

/-- RH gives the two-term deletion law and the half-dimension floor at
every dimension strictly between zero and one. -/
theorem rh_gives_all_greedy_half_dimensions (h : RiemannHypothesis) :
    ∀ κ : ℝ, 0 < κ → κ < 1 → greedyHalfDimensionLaw κ := by
  intro κ hk hk1
  let d := min (1/8:ℝ) ((1-κ)/4)
  have dp : 0 < d := lt_min (by norm_num) (by linarith only [hk1])
  have dsmall : d ≤ (1-κ)/4 := min_le_right _ _
  have dz : d ≤ 1/8 := min_le_left _ _
  have edge := zetaZeroAbscissa_eq_half_iff_riemannHypothesis.mpr h
  apply greedy_half_dimension_of_density_strip (z:=1/2+d) (s:=1)
    (by linarith only [edge,dp]) (by linarith only [dp]) (by linarith only [dz])
    le_rfl (by norm_num) hk hk1
  rw [show 1-1*(1/2+d-1/2)=1-d by ring]
  have hp : 0 < 1-d := by linarith only [dz]
  have hratio : κ/2 < (1-(1/2+d))/(1-d) := (lt_div_iff₀ hp).mpr (by
    nlinarith only [hk1,dsmall,mul_nonneg hk.le dp.le])
  linarith only [hratio]

#print axioms greedy_half_dimension_below_thirteen_fifteenths
#print axioms greedy_half_dimension_of_density_strip
#print axioms rh_gives_all_greedy_half_dimensions
end GaloisForLFunctions.ArithmeticPositiveDuality
