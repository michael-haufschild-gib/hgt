import Mathlib

/-!
# The singular Laplace source cocycle and its observer line

On the weighted space `L²((0,1), c s^{β-1} ds)` the multiplication semigroup `T_V f = e^{-Vs} f`
produces the source cochain `b_V(s) = e^{-Vs} − 1`.  This file proves the elementary layer of the
spectral terminal-horizon model:

* `b_V` is square integrable against the weight exactly because `β > −2`;
* the semigroup cocycle identity `b_{V+W} = b_V + T_V b_W`;
* `b_V` is a coboundary inside the weighted space exactly when `β > 0`, since the only candidate
  primitive is the constant function `1`;
* the admissible observer line, the stable death region, and the horizon width
  `𝔡_β + β/2 = max(0, −β/2)`.
-/

namespace GaloisForLFunctions.HTGeometry.Interfinity

open MeasureTheory Set Filter Topology

noncomputable section

/-! ## The source cochain -/

/-- The singular Laplace source cochain `b_V(s) = e^{-Vs} − 1`. -/
def laplaceCochain (V s : ℝ) : ℝ := Real.exp (-(V * s)) - 1

/-- The multiplication semigroup `T_V f = e^{-Vs} f`. -/
def laplaceMul (V : ℝ) (f : ℝ → ℝ) : ℝ → ℝ := fun s => Real.exp (-(V * s)) * f s

@[simp] theorem laplaceCochain_zero (s : ℝ) : laplaceCochain 0 s = 0 := by
  simp [laplaceCochain]

/-- **The semigroup cocycle identity.** -/
theorem laplaceCochain_add (V W s : ℝ) :
    laplaceCochain (V + W) s = laplaceCochain V s + laplaceMul V (laplaceCochain W) s := by
  simp only [laplaceCochain, laplaceMul]
  rw [show -((V + W) * s) = -(V * s) + -(W * s) by ring, Real.exp_add]
  ring

/-- The source cochain is bounded by the linear model. -/
theorem abs_laplaceCochain_le {V s : ℝ} (hV : 0 ≤ V) (hs : 0 ≤ s) :
    |laplaceCochain V s| ≤ V * s := by
  have h1 : Real.exp (-(V * s)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
  have h2 : 1 - V * s ≤ Real.exp (-(V * s)) := by
    have := Real.add_one_le_exp (-(V * s))
    linarith
  rw [laplaceCochain, abs_le]
  constructor <;> nlinarith

/-! ## Square integrability against the singular weight -/

/-- **The source cochain lies in the weighted space exactly because `β > −2`.** -/
theorem integrableOn_laplaceCochain_sq {β : ℝ} (hβ : -2 < β) {V : ℝ} (hV : 0 ≤ V) :
    IntegrableOn (fun s : ℝ => (laplaceCochain V s) ^ 2 * s ^ (β - 1)) (Ioo 0 1) := by
  have hdom : IntegrableOn (fun s : ℝ => V ^ 2 * s ^ (β + 1)) (Ioo 0 1) := by
    refine Integrable.const_mul ?_ _
    exact (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)
  refine Integrable.mono' hdom ?_ ?_
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    refine ContinuousOn.mul (Continuous.continuousOn ?_) ?_
    · exact ((Real.continuous_exp.comp (by fun_prop)).sub continuous_const).pow 2
    · exact continuousOn_id.rpow_const fun x hx => Or.inl (ne_of_gt hx.1)
  · filter_upwards [ae_restrict_mem measurableSet_Ioo] with s hs
    have hs0 : (0 : ℝ) < s := hs.1
    have hpow : s ^ (2 : ℝ) * s ^ (β - 1) = s ^ (β + 1) := by
      rw [← Real.rpow_add hs0]
      ring_nf
    have hsq : (s : ℝ) ^ (2 : ℝ) = s ^ 2 := by
      rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    have hb : |laplaceCochain V s| ≤ V * s := abs_laplaceCochain_le hV hs0.le
    have hwpos : (0 : ℝ) < s ^ (β - 1) := Real.rpow_pos_of_pos hs0 _
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hwpos, abs_pow]
    calc |laplaceCochain V s| ^ 2 * s ^ (β - 1) ≤ (V * s) ^ 2 * s ^ (β - 1) := by
          have h1 : |laplaceCochain V s| ^ 2 ≤ (V * s) ^ 2 := by
            have := abs_nonneg (laplaceCochain V s)
            nlinarith
          nlinarith
      _ = V ^ 2 * (s ^ (2 : ℝ) * s ^ (β - 1)) := by rw [hsq]; ring
      _ = V ^ 2 * s ^ (β + 1) := by rw [hpow]

/-! ## The coboundary threshold -/

/-- The only candidate primitive of the source cochain is the constant function `1`. -/
theorem eq_one_of_isPrimitive {η : ℝ → ℝ} {V : ℝ} (hV : 0 < V)
    (h : ∀ s ∈ Ioo (0 : ℝ) 1, laplaceCochain V s = (Real.exp (-(V * s)) - 1) * η s)
    {s : ℝ} (hs : s ∈ Ioo (0 : ℝ) 1) : η s = 1 := by
  have hs0 : (0 : ℝ) < s := hs.1
  have hne : Real.exp (-(V * s)) - 1 ≠ 0 := by
    have : Real.exp (-(V * s)) < 1 := Real.exp_lt_one_iff.2 (by nlinarith)
    linarith
  have := h s hs
  rw [laplaceCochain] at this
  field_simp at this
  exact this.symm

/-- **The coboundary threshold.**  The source cochain is a coboundary inside the weighted space
exactly when `β > 0`. -/
theorem isCoboundary_iff {β : ℝ} :
    (∃ η : ℝ → ℝ, IntegrableOn (fun s : ℝ => (η s) ^ 2 * s ^ (β - 1)) (Ioo 0 1) ∧
        ∀ V : ℝ, 0 < V → ∀ s ∈ Ioo (0 : ℝ) 1,
          laplaceCochain V s = (Real.exp (-(V * s)) - 1) * η s) ↔ 0 < β := by
  constructor
  · rintro ⟨η, hint, hprim⟩
    have hone : IntegrableOn (fun s : ℝ => s ^ (β - 1)) (Ioo 0 1) := by
      refine hint.congr_fun (fun s hs => ?_) measurableSet_Ioo
      show η s ^ 2 * s ^ (β - 1) = s ^ (β - 1)
      rw [eq_one_of_isPrimitive one_pos (hprim 1 one_pos) hs]
      ring
    have := (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).1 hone
    linarith
  · intro hβ
    refine ⟨fun _ => 1, ?_, fun V _ s _ => by simp [laplaceCochain]⟩
    have : IntegrableOn (fun s : ℝ => s ^ (β - 1)) (Ioo 0 1) :=
      (intervalIntegral.integrableOn_Ioo_rpow_iff zero_lt_one).2 (by linarith)
    refine this.congr_fun (fun s _ => ?_) measurableSet_Ioo
    show s ^ (β - 1) = (1 : ℝ) ^ 2 * s ^ (β - 1)
    ring

/-! ## The observer line and the death region -/

/-- The admissible observer line `𝒪_β = (−β/2, ∞)`. -/
def observerLine (β : ℝ) : Set ℝ := Ioi (-β / 2)

/-- The stable death cut `𝔡_β = max(−β/2, −β)`. -/
def deathCut (β : ℝ) : ℝ := max (-β / 2) (-β)

/-- The stable death region `D_β = (𝔡_β, ∞)`. -/
def stableRegion (β : ℝ) : Set ℝ := Ioi (deathCut β)

theorem mem_observerLine_iff (β ρ : ℝ) : ρ ∈ observerLine β ↔ 0 < 2 * ρ + β := by
  rw [observerLine, mem_Ioi]
  constructor <;> intro h <;> linarith

theorem mem_stableRegion_iff (β ρ : ℝ) :
    ρ ∈ stableRegion β ↔ 0 < 2 * ρ + β ∧ 0 < ρ + β := by
  rw [stableRegion, mem_Ioi, deathCut, max_lt_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩
  · rintro ⟨h1, h2⟩
    exact ⟨by linarith, by linarith⟩

theorem stableRegion_subset_observerLine (β : ℝ) : stableRegion β ⊆ observerLine β := by
  intro ρ hρ
  rw [mem_stableRegion_iff] at hρ
  rw [mem_observerLine_iff]
  exact hρ.1

/-- **The horizon width.** -/
theorem deathCut_add (β : ℝ) : deathCut β + β / 2 = max 0 (-β / 2) := by
  rw [deathCut]
  rcases le_total (-β / 2) (-β) with h | h
  · rw [max_eq_right h, max_eq_right (by linarith : (0 : ℝ) ≤ -β / 2)]
    linarith
  · rw [max_eq_left h, max_eq_left (by linarith : (-β / 2 : ℝ) ≤ 0)]
    linarith

/-- The death region exhausts the observer line exactly when the weight is not singular. -/
theorem deathCut_eq_iff (β : ℝ) : deathCut β = -β / 2 ↔ 0 ≤ β := by
  rw [deathCut, max_eq_left_iff]
  constructor <;> intro h <;> linarith

end

end GaloisForLFunctions.HTGeometry.Interfinity
