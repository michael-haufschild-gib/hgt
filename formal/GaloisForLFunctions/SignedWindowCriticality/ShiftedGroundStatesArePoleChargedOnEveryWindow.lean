import GaloisForLFunctions.SignedWindowCriticality.ThePoleChargesTheSupersolution
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStateTwoSidedRepresentation
import GaloisForLFunctions.ArithmeticCriticalityTheory.ShiftedGroundStatePlateauPositivity

/-!
# Shifted ground states are pole-charged on every window

ACT's shifted ground states `ω_a = m_a/Φ`, `m_a = Φ(· − a) − Φ(· + a)`, are odd, positive on the
half-line, and solve the exact source equation `𝓛_Dω_a − Φcosh(x/2)ω_a = 2sinh(a/2) sinh(x/2) Φ`;
on even profiles `M(Φω_au) = 2S_a(u) − D_a(u) + 4sinh(a/2)∫_{x>0}u²m_a sinh(x/2)` (ACT). The source
carries the whole sinh charge of the gauge on the line, `∫_{x>0} m_a sinh(x/2) = sinh(a/2)/2`. On a
window `(−c, c)` the pole's negative square only reads the charge inside the window, so the gauge
is a **strict** pole-charged supersolution there, with slack the charge outside the window.

* **Exact window identity** (`fullZeroForm_shiftedGroundState_window`). For `a > 0`, every `c` and
  every even `u ∈ C²_c`,
  `Ẑ(Φω_au) = 2S_a(u) − D_a(u) + 8V_c(u) + 8τ_c(a)∫_{x>0}u²m_a sinh(x/2)`, with the half-line charge
  variance `V_c(u) = (∫_0^c m_a sinh)(∫_{x>0}u²m_a sinh) − (∫_{x>0}u m_a sinh)² ≥ 0` and the outside
  charge `τ_c(a) = sinh(a/2)/2 − ∫_0^c m_a sinh(x/2)dx`.
* **The outside charge is positive** (`outsideCharge_pos`): `τ_c(a) = ∫_{x≥c} m_a sinh > 0`.
* **Window slack** (`fullZeroForm_shiftedGroundState_ge`): for `u` vanishing for `|x| ≥ c`,
  `Ẑ(Φω_au) ≥ 2S_a(u) − D_a(u) + 8τ_c(a)∫_{x>0}u²m_a sinh(x/2)`.

On the whole line the slack vanishes (ACT: `Z(m_au) = 2S − D + V_a`, the critical case). On a window
every shifted ground state is subcritical by the outside charge, and the odd window form is
bounded below by the signed Dirichlet form `2S_a − D_a` — the light cone plus same-side prime
jumps minus the reflected (anti-diagonal) prime jumps — plus that slack.
-/

open MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.SignedWindowCriticality

open _root_.RHTower _root_.RHTower.CHMDPolar
open GaloisForLFunctions.ArithmeticCriticalityTheory

/-- The sinh charge of `m_a` outside the half-window `(0, c)`: `sinh(a/2)/2 − ∫_0^c m_a sinh(x/2)`. -/
def outsideCharge (a c : ℝ) : ℝ :=
  Real.sinh (a / 2) / 2 - ∫ x in Ioo (0 : ℝ) c, shiftDifference a x * Real.sinh (x / 2)

/-- Cauchy–Schwarz on an interval for a nonnegative weight. -/
theorem sq_setIntegral_mul_le {m u : ℝ → ℝ} {p q : ℝ} (hm : Continuous m)
    (hm0 : ∀ x ∈ Ioo p q, 0 ≤ m x) (hu : Continuous u) :
    (∫ x in Ioo p q, u x * m x) ^ 2 ≤ (∫ x in Ioo p q, m x) * ∫ x in Ioo p q, u x ^ 2 * m x := by
  set σ := ∫ x in Ioo p q, m x
  set A₁ := ∫ x in Ioo p q, u x * m x
  set A₂ := ∫ x in Ioo p q, u x ^ 2 * m x
  have hi1 : IntegrableOn (fun x => u x ^ 2 * m x) (Ioo p q) :=
    integrableOn_Ioo_of_continuous ((hu.pow 2).mul hm)
  have hi2 : IntegrableOn (fun x => u x * m x) (Ioo p q) := integrableOn_Ioo_of_continuous (hu.mul hm)
  have hi3 : IntegrableOn m (Ioo p q) := integrableOn_Ioo_of_continuous hm
  have hq : ∀ t : ℝ, 0 ≤ σ * (t * t) + (-2 * A₁) * t + A₂ := by
    intro t
    have h0 : 0 ≤ ∫ x in Ioo p q, m x * (u x - t) ^ 2 :=
      setIntegral_nonneg measurableSet_Ioo fun x hx => mul_nonneg (hm0 x hx) (sq_nonneg _)
    have h1 : (∫ x in Ioo p q, ((u x ^ 2 * m x - (2 * t) * (u x * m x)) + t ^ 2 * m x)) =
        (∫ x in Ioo p q, (u x ^ 2 * m x - (2 * t) * (u x * m x))) + ∫ x in Ioo p q, t ^ 2 * m x :=
      integral_add (hi1.sub (hi2.const_mul _)) (hi3.const_mul _)
    have h2 : (∫ x in Ioo p q, (u x ^ 2 * m x - (2 * t) * (u x * m x))) =
        A₂ - ∫ x in Ioo p q, (2 * t) * (u x * m x) := integral_sub hi1 (hi2.const_mul _)
    have hexp : (∫ x in Ioo p q, m x * (u x - t) ^ 2) = A₂ - 2 * t * A₁ + t ^ 2 * σ := by
      rw [show (fun x => m x * (u x - t) ^ 2) =
          fun x => (u x ^ 2 * m x - (2 * t) * (u x * m x)) + t ^ 2 * m x by funext x; ring,
        h1, h2, integral_const_mul, integral_const_mul]
    nlinarith
  have hd := discrim_le_zero hq
  unfold discrim at hd
  nlinarith

theorem integral_eq_two_mul_Ioi_of_even' {g : ℝ → ℝ} (hg : Integrable g)
    (heven : ∀ x, g (-x) = g x) : ∫ x, g x = 2 * ∫ x in Ioi (0 : ℝ), g x := by
  have h := integral_add_compl (s := Ioi (0 : ℝ)) measurableSet_Ioi hg
  rw [compl_Ioi] at h
  have hneg := integral_comp_neg_Ioi (0 : ℝ) g
  rw [neg_zero] at hneg
  simp_rw [heven] at hneg
  rw [← h, ← hneg]
  ring

theorem shiftDifference_mul_sinh_nonneg {a : ℝ} (ha : 0 < a) (x : ℝ) :
    0 ≤ shiftDifference a x * Real.sinh (x / 2) := by
  rcases le_or_gt 0 x with hx | hx
  · exact mul_nonneg (shiftDifference_nonneg_of_nonneg ha.le hx)
      (Real.sinh_nonneg_iff.mpr (by linarith))
  · have h1 : shiftDifference a x < 0 := by
      have := shiftDifference_pos ha (show 0 < -x by linarith)
      rw [shiftDifference_neg] at this; linarith
    have h2 : Real.sinh (x / 2) < 0 := Real.sinh_neg_iff.mpr (by linarith)
    exact (mul_pos_of_neg_of_neg h1 h2).le

/-- **The outside charge is positive.** -/
theorem outsideCharge_pos {a c : ℝ} (ha : 0 < a) (hc : 0 < c) : 0 < outsideCharge a c := by
  have hint := (integrable_shiftDifference_mul_sinh_half a).integrableOn (s := Ioi (0 : ℝ))
  have hcont : Continuous fun x => shiftDifference a x * Real.sinh (x / 2) :=
    (continuous_shiftDifference a).mul (Real.continuous_sinh.comp (continuous_id.div_const 2))
  have hsplit : (∫ x in Ioi (0 : ℝ), shiftDifference a x * Real.sinh (x / 2)) =
      (∫ x in Ioo (0 : ℝ) c, shiftDifference a x * Real.sinh (x / 2)) +
        ∫ x in Ici c, shiftDifference a x * Real.sinh (x / 2) := by
    have hset : Ioi (0 : ℝ) = Ioo 0 c ∪ Ici c := by
      ext x; simp only [mem_Ioi, mem_union, mem_Ioo, mem_Ici]
      constructor
      · intro hx; by_cases h : x < c
        · exact Or.inl ⟨hx, h⟩
        · exact Or.inr (not_lt.mp h)
      · rintro (h | h)
        · exact h.1
        · exact lt_of_lt_of_le hc h
    rw [hset, setIntegral_union (Set.disjoint_left.mpr fun x hx hx' =>
        absurd hx.2 (not_lt.mpr hx')) measurableSet_Ici
      (hint.mono_set (hset ▸ subset_union_left)) (hint.mono_set (hset ▸ subset_union_right))]
  have hpos : 0 < ∫ x in Ici c, shiftDifference a x * Real.sinh (x / 2) := by
    have hsub : (∫ x in Icc c (c + 1), shiftDifference a x * Real.sinh (x / 2)) ≤
        ∫ x in Ici c, shiftDifference a x * Real.sinh (x / 2) :=
      setIntegral_mono_set (hint.mono_set fun x hx => lt_of_lt_of_le hc hx)
        (ae_restrict_of_forall_mem measurableSet_Ici fun x _ => shiftDifference_mul_sinh_nonneg ha x)
        (Eventually.of_forall Icc_subset_Ici_self)
    have hIcc : 0 < ∫ x in Icc c (c + 1), shiftDifference a x * Real.sinh (x / 2) := by
      rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith)]
      exact intervalIntegral.intervalIntegral_pos_of_pos_on (hcont.intervalIntegrable c (c + 1))
        (fun x hx => mul_pos (shiftDifference_pos ha (by linarith [hx.1]))
          (Real.sinh_pos_iff.mpr (by linarith [hx.1]))) (by linarith)
    linarith
  unfold outsideCharge
  rw [← integral_Ioi_shiftDifference_mul_sinh_half a, hsplit]
  linarith

/-- **Exact window identity of a shifted ground state.** -/
theorem fullZeroForm_shiftedGroundState_window {a : ℝ} (ha : 0 < a) (c : ℝ)
    {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x) :
    fullZeroForm (phiDoobTest fun y => shiftedGroundState a y * u y) =
      2 * sameSideEnergy (shiftedGroundState a) u -
          reflectedDifferenceEnergy (shiftedGroundState a) u +
        8 * ((∫ x in Ioo (0 : ℝ) c, shiftDifference a x * Real.sinh (x / 2)) *
            (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) -
          (∫ x in Ioi (0 : ℝ), u x * shiftDifference a x * Real.sinh (x / 2)) ^ 2) +
        8 * outsideCharge a c *
          ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) := by
  set F := phiDoobTest fun y => shiftedGroundState a y * u y
  have hF : ∀ x, F x = shiftDifference a x * u x := fun x => by
    simp only [F, phiDoobTest, ← mul_assoc, riemannKernelReal_mul_shiftedGroundState]
  have hFodd : ∀ x, F (-x) = -F x := fun x => by
    rw [hF, hF, shiftDifference_neg, heven]; ring
  have hE : evenPoleMoment F = 0 := evenPoleMoment_eq_zero_of_odd hFodd
  have hcont : Continuous fun x => u x * shiftDifference a x * Real.sinh (x / 2) :=
    (hu.continuous.mul (continuous_shiftDifference a)).mul
      (Real.continuous_sinh.comp (continuous_id.div_const 2))
  have hint : Integrable fun x => u x * shiftDifference a x * Real.sinh (x / 2) :=
    hcont.integrable_of_hasCompactSupport (huc.mul_right.mul_right)
  have hO : oddPoleMoment F = 2 * ∫ x in Ioi (0 : ℝ), u x * shiftDifference a x * Real.sinh (x / 2) := by
    unfold oddPoleMoment
    rw [← integral_eq_two_mul_Ioi_of_even' hint fun x => by
      rw [heven, shiftDifference_neg, show -x / 2 = -(x / 2) by ring, Real.sinh_neg]; ring]
    exact integral_congr_ae (Eventually.of_forall fun x => by simp only [hF]; ring)
  have hM := markovEnergy_phiDoob_shiftedGroundState_eq_twoSided ha hu huc heven
  unfold fullZeroForm
  rw [hM, hO, hE]
  unfold outsideCharge
  ring

/-- **Window slack of a shifted ground state.** -/
theorem fullZeroForm_shiftedGroundState_ge {a c : ℝ} (ha : 0 < a) (hc : 0 < c)
    {u : ℝ → ℝ} (hu : ContDiff ℝ 2 u) (huc : HasCompactSupport u) (heven : ∀ x, u (-x) = u x)
    (hsupp : ∀ x, c ≤ |x| → u x = 0) :
    2 * sameSideEnergy (shiftedGroundState a) u -
        reflectedDifferenceEnergy (shiftedGroundState a) u +
        8 * outsideCharge a c *
          ∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2) ≤
      fullZeroForm (phiDoobTest fun y => shiftedGroundState a y * u y) := by
  rw [fullZeroForm_shiftedGroundState_window ha c hu huc heven]
  set m : ℝ → ℝ := fun x => shiftDifference a x * Real.sinh (x / 2)
  have hm : Continuous m :=
    (continuous_shiftDifference a).mul (Real.continuous_sinh.comp (continuous_id.div_const 2))
  have hcs := sq_setIntegral_mul_le (p := 0) (q := c) hm
    (fun x _ => shiftDifference_mul_sinh_nonneg ha x) hu.continuous
  have hoff : ∀ x, c ≤ x → u x = 0 := fun x hx => hsupp x (by rw [abs_of_pos (by linarith)]; exact hx)
  have e1 : (∫ x in Ioi (0 : ℝ), u x * shiftDifference a x * Real.sinh (x / 2)) =
      ∫ x in Ioo (0 : ℝ) c, u x * m x := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioo_subset_Ioi_self
      fun x hx => by
        have : c ≤ x := not_lt.mp fun h => hx.2 ⟨hx.1, h⟩
        simp [hoff x this]]
    exact setIntegral_congr_fun measurableSet_Ioo fun x _ => by simp only [m]; ring
  have e2 : (∫ x in Ioi (0 : ℝ), u x ^ 2 * shiftDifference a x * Real.sinh (x / 2)) =
      ∫ x in Ioo (0 : ℝ) c, u x ^ 2 * m x := by
    rw [setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Ioo_subset_Ioi_self
      fun x hx => by
        have : c ≤ x := not_lt.mp fun h => hx.2 ⟨hx.1, h⟩
        simp [hoff x this]]
    exact setIntegral_congr_fun measurableSet_Ioo fun x _ => by simp only [m]; ring
  have hσ : (∫ x in Ioo (0 : ℝ) c, shiftDifference a x * Real.sinh (x / 2)) =
      ∫ x in Ioo (0 : ℝ) c, m x := rfl
  rw [e1, e2, hσ]
  nlinarith

end GaloisForLFunctions.SignedWindowCriticality

end
