import GaloisForLFunctions.RHTower.DeBruijnNewmanNonnegative
import GaloisForLFunctions.RHTower.KiKimLeeFiniteness
import GaloisForLFunctions.RHTower.LindelofCosineFiniteDefectDepth

/-!
# The heat flow confines the zeros of `Ξ` exactly from time zero on

Let `H_t(z) = ∫ Φ(x) e^{tx²} e^{izx} dx` be the de Bruijn–Newman deformation of
`Ξ(z) = ξ(½ + iz)`, so that `Im z = ½ − Re ρ` at a zero `z = −i(ρ − ½)` of `H_0`.

* **Strip threshold** (`exists_abs_im_le_of_riemannHeat_iff`).  The zeros of `H_t` lie in some
  horizontal strip iff `t ≥ 0`.  For `t ≥ 0` they satisfy `|Im z| ≤ ½` (the critical strip, then
  de Bruijn's contraction).  For `t = −τ < 0` there are zeros with `Re z` arbitrarily large and
  `−Im z ≥ τ log(Re z) − C` (`exists_riemannHeat_neg_zero_deep`): the backward flow pushes zeros to
  logarithmic depth, near the zeros of the Gaussian-damped series `F_τ` translated by
  `τ log(T/2π)`.
* **Large-height threshold** (`heatZerosApproachAxis_iff`).  Say that the zeros of `H_t` approach
  the real axis if for every `h > 0` only finitely many zeros have `|Im z| > h`.  This holds for
  every `t > 0` (Ki–Kim–Lee: finitely many non-real zeros), fails for every `t < 0`, and at `t = 0`
  it is exactly the statement that the zeros of `ξ` approach the critical line
  (`heatZerosApproachAxis_zero_iff`).

* **Counting** (`exists_finset_nonreal_riemannHeat_neg_card_ge`).  For `t = −τ < 0` there are at
  least `cX` distinct non-real zeros with real part in `[0, X]`, one in each window of almost
  periods of `F_τ` (`exists_riemannHeat_neg_zero_near_model_dense`).

So both confinement thresholds of the flow sit at `t = 0`, unconditionally: `Ξ` is the first member
of the family whose zeros stay in a strip, and the only member whose large-height behaviour is not
decided by the sign of `t`.  The de Bruijn–Newman constant `Λ ≥ 0` is the real-rootedness
threshold, and RH says that it equals these two thresholds.  In the split
RH ⟺ (zeros approach the line) ∧ (asymptotic abscissa law), the first factor is the boundary value,
at the threshold, of a property that holds on one side and fails on the other.
-/

open Complex Set

namespace RHTower.DeBruijn

open RHTower.BacklundConverse RHTower.CosineDefectBudget

noncomputable section

/-- Every zero of `H_t`, `t ≥ 0`, has `|Im z| ≤ ½`. -/
theorem abs_im_le_half_of_riemannHeat_eq_zero_of_nonneg {t : ℝ} (ht : 0 ≤ t) {z : ℂ}
    (hz : riemannHeat t z = 0) : |z.im| ≤ 1 / 2 := by
  have h2 : z.im ^ 2 ≤ (1 / 2) ^ 2 := by
    rcases ht.eq_or_lt with rfl | ht
    · rw [riemannHeat_zero, ← cosTransform_riemannKernel] at hz
      have := riemannKernel_zeros_im_sq_le z hz
      linarith
    · exact (riemannHeat_zeros_im_sq_le ht hz).trans (max_le (by linarith) (by norm_num))
  exact abs_le.mpr (abs_le_of_sq_le_sq' h2 (by norm_num))

/-- **At negative time the depth of the zeros is unbounded.** -/
theorem exists_riemannHeat_zero_abs_im_gt_of_neg {t : ℝ} (ht : t < 0) (D R : ℝ) :
    ∃ z : ℂ, riemannHeat t z = 0 ∧ R ≤ z.re ∧ D < |z.im| := by
  obtain ⟨C, hC⟩ := exists_riemannHeat_neg_zero_deep (τ := -t) (by linarith)
  obtain ⟨z, hz, hR, hlog⟩ := hC (max R (Real.exp ((D + C + 1) / -t)))
  rw [neg_neg] at hz
  refine ⟨z, hz, (le_max_left _ _).trans hR, ?_⟩
  have h1 : (D + C + 1) / -t ≤ Real.log z.re := by
    rw [← Real.log_exp ((D + C + 1) / -t)]
    exact Real.log_le_log (Real.exp_pos _) ((le_max_right _ _).trans hR)
  rw [div_le_iff₀ (by linarith)] at h1
  linarith [neg_le_abs z.im, mul_comm (-t) (Real.log z.re)]

/-- **The strip threshold.**  The zeros of `H_t` lie in a horizontal strip iff `t ≥ 0`. -/
theorem exists_abs_im_le_of_riemannHeat_iff (t : ℝ) :
    (∃ D : ℝ, ∀ z : ℂ, riemannHeat t z = 0 → |z.im| ≤ D) ↔ 0 ≤ t := by
  refine ⟨fun ⟨D, hD⟩ => ?_, fun ht => ⟨1 / 2, fun z hz =>
    abs_im_le_half_of_riemannHeat_eq_zero_of_nonneg ht hz⟩⟩
  by_contra ht
  obtain ⟨z, hz, -, hlt⟩ := exists_riemannHeat_zero_abs_im_gt_of_neg (not_le.mp ht) D 0
  linarith [hD z hz]

/-- The zeros of `H_t` approach the real axis: for every `h > 0` only finitely many zeros have
`|Im z| > h`. -/
def HeatZerosApproachAxis (t : ℝ) : Prop :=
  ∀ h : ℝ, 0 < h → {z : ℂ | riemannHeat t z = 0 ∧ h < |z.im|}.Finite

/-- At positive time the zeros approach the axis (Ki–Kim–Lee). -/
theorem heatZerosApproachAxis_of_pos {t : ℝ} (ht : 0 < t) : HeatZerosApproachAxis t :=
  fun h hh => (riemannHeat_nonreal_zeros_finite ht).subset fun z ⟨hz, hlt⟩ =>
    ⟨hz, fun h0 => by rw [h0, abs_zero] at hlt; linarith⟩

/-- At negative time they do not. -/
theorem not_heatZerosApproachAxis_of_neg {t : ℝ} (ht : t < 0) : ¬ HeatZerosApproachAxis t := by
  intro hA
  obtain ⟨B, hB⟩ := ((hA 1 one_pos).image Complex.re).bddAbove
  obtain ⟨z, hz, hR, hlt⟩ := exists_riemannHeat_zero_abs_im_gt_of_neg ht 1 (B + 1)
  linarith [hB ⟨z, ⟨hz, hlt⟩, rfl⟩]

/-- The spectral point `−i(ρ − ½)` of a zero copy is a zero of `H_0`. -/
theorem riemannHeat_zero_xiSpectralPoint_eq_zero (q : XiZeroCopy) :
    riemannHeat 0 (xiSpectralPoint q) = 0 := by
  rw [riemannHeat_zero]
  have e : 1 / 2 + I * xiSpectralPoint q = (q.1 : ℂ) := by
    unfold xiSpectralPoint
    linear_combination (-((q.1 : ℂ) - 1 / 2)) * Complex.I_sq
  rw [e]
  exact xi_xiZeroCopy_eq_zero q

/-- Every zero of `H_0` is the spectral point of a zero copy. -/
theorem exists_xiZeroCopy_spectral_eq_of_riemannHeat_zero {z : ℂ} (hz : riemannHeat 0 z = 0) :
    ∃ q : XiZeroCopy, xiSpectralPoint q = z := by
  rw [riemannHeat_zero] at hz
  obtain ⟨q, hq⟩ := exists_xiZeroCopy_of_xi_eq_zero hz
  refine ⟨q, ?_⟩
  unfold xiSpectralPoint
  rw [hq]
  linear_combination (-z) * Complex.I_sq

/-- **At the threshold the approach property is the approach of the zeros of `ξ` to the line.** -/
theorem heatZerosApproachAxis_zero_iff : HeatZerosApproachAxis 0 ↔ ZerosApproachLine := by
  constructor
  · intro hA h hh
    obtain ⟨B, hB⟩ := ((hA h hh).image fun z : ℂ => ‖z‖).bddAbove
    refine (xiZeroBall ⌈B⌉₊).finite_toSet.subset fun q hq => ?_
    rw [Finset.mem_coe, mem_xiZeroBall]
    have hmem : xiSpectralPoint q ∈ {z : ℂ | riemannHeat 0 z = 0 ∧ h < |z.im|} :=
      ⟨riemannHeat_zero_xiSpectralPoint_eq_zero q, lt_of_lt_of_le hq (le_abs_self _)⟩
    exact (hB ⟨_, hmem, rfl⟩).trans (Nat.le_ceil B)
  · intro hZ h hh
    have hF := (hZ h hh).image xiSpectralPoint
    refine (hF.union (hF.image Neg.neg)).subset fun z ⟨hz, hlt⟩ => ?_
    obtain ⟨q, rfl⟩ := exists_xiZeroCopy_spectral_eq_of_riemannHeat_zero hz
    rcases lt_abs.mp hlt with h1 | h1
    · exact Or.inl ⟨q, h1, rfl⟩
    · refine Or.inr ⟨xiSpectralPoint (xiZeroCopyReflectEquiv.symm q), ⟨_, ?_, rfl⟩, ?_⟩
      · show h < (xiSpectralPoint (xiZeroCopyReflectEquiv.symm q)).im
        rw [xiSpectralPoint_reflect_symm, Complex.neg_im]
        exact h1
      · rw [xiSpectralPoint_reflect_symm, neg_neg]

/-- **The large-height threshold.**  The zeros of `H_t` approach the real axis iff `t > 0`, or
`t = 0` and the zeros of `ξ` approach the critical line. -/
theorem heatZerosApproachAxis_iff (t : ℝ) :
    HeatZerosApproachAxis t ↔ 0 < t ∨ (t = 0 ∧ ZerosApproachLine) := by
  constructor
  · intro hA
    rcases lt_trichotomy t 0 with ht | rfl | ht
    · exact absurd hA (not_heatZerosApproachAxis_of_neg ht)
    · exact Or.inr ⟨rfl, heatZerosApproachAxis_zero_iff.mp hA⟩
    · exact Or.inl ht
  · rintro (ht | ⟨rfl, hZ⟩)
    · exact heatZerosApproachAxis_of_pos ht
    · exact heatZerosApproachAxis_zero_iff.mpr hZ

/-- **The strip threshold as a set.**  The heat times whose zeros lie in a strip are exactly
`[0, ∞)`. -/
theorem setOf_exists_abs_im_le_riemannHeat :
    {t : ℝ | ∃ D : ℝ, ∀ z : ℂ, riemannHeat t z = 0 → |z.im| ≤ D} = Ici 0 := by
  ext t
  exact exists_abs_im_le_of_riemannHeat_iff t

/-- **The large-height threshold as a set.**  The heat times at which the zeros approach the axis
contain `(0, ∞)` and lie in `[0, ∞)`; the endpoint `0` belongs iff the zeros of `ξ` approach the
critical line. -/
theorem Ioi_subset_setOf_heatZerosApproachAxis :
    Ioi (0 : ℝ) ⊆ {t | HeatZerosApproachAxis t} :=
  fun _ ht => heatZerosApproachAxis_of_pos ht

theorem setOf_heatZerosApproachAxis_subset_Ici :
    {t | HeatZerosApproachAxis t} ⊆ Ici (0 : ℝ) := fun _ ht =>
  le_of_not_gt fun hneg => not_heatZerosApproachAxis_of_neg hneg ht

theorem zero_mem_setOf_heatZerosApproachAxis_iff :
    (0 : ℝ) ∈ {t | HeatZerosApproachAxis t} ↔ ZerosApproachLine :=
  heatZerosApproachAxis_zero_iff

/-- **Quantitative Newman conjecture.**  For `τ > 0` there are `c > 0` and `X₀` such that for
every `X ≥ X₀`, `H_{−τ}` has at least `cX` distinct non-real zeros with real part in `[0, X]`.
Each window `[R₁ + k(L+2), R₁ + k(L+2) + L]` of almost periods of `F_τ` carries one model zero,
at depth `> 1`. -/
theorem exists_finset_nonreal_riemannHeat_neg_card_ge {τ : ℝ} (hτ : 0 < τ) :
    ∃ c X₀ : ℝ, 0 < c ∧ ∀ X : ℝ, X₀ ≤ X → ∃ S : Finset ℂ,
      (∀ z ∈ S, riemannHeat (-τ) z = 0 ∧ z.im ≠ 0 ∧ 0 ≤ z.re ∧ z.re ≤ X) ∧
        c * X ≤ S.card := by
  classical
  obtain ⟨w₀, hw₀⟩ := exists_gaussDirichlet_eq_zero hτ
  obtain ⟨L, R₀, hL, hdense⟩ := exists_riemannHeat_neg_zero_near_model_dense hτ hw₀
    (ε := 1 / 2) (by norm_num)
  have hτπ : 0 ≤ τ * (Real.pi / 2) := by positivity
  set E : ℝ := 2 * Real.pi * Real.exp ((|w₀.re| + 2) / τ) with hE
  set R₁ : ℝ := max R₀ (max E (|w₀.im| + 1)) with hR₁
  have hR₁0 : R₀ ≤ R₁ := le_max_left _ _
  have hR₁E : E ≤ R₁ := (le_max_left _ _).trans (le_max_right _ _)
  have hR₁w : |w₀.im| + 1 ≤ R₁ := (le_max_right _ _).trans (le_max_right _ _)
  -- one deep zero in each window `[R₁ + k(L + 2), R₁ + k(L + 2) + L]`
  have hk : ∀ k : ℕ, ∃ z : ℂ, riemannHeat (-τ) z = 0 ∧ z.im ≠ 0 ∧
      R₁ + k * (L + 2) + w₀.im + τ * (Real.pi / 2) - 1 / 2 ≤ z.re ∧
      z.re ≤ R₁ + k * (L + 2) + L + w₀.im + τ * (Real.pi / 2) + 1 / 2 := by
    intro k
    have hk0 : (0 : ℝ) ≤ k * (L + 2) := by positivity
    obtain ⟨T, hT1, hT2, z, hz, hzm⟩ := hdense (R₁ + k * (L + 2)) (by linarith)
    have hTE : E ≤ T := by linarith
    have hTpos : 0 < T := lt_of_lt_of_le (by positivity) hTE
    have hre_m : (-I * (discPoint τ T w₀ - 1 / 2)).re = w₀.im + T + τ * (Real.pi / 2) := by
      simp [discPoint, horizontalSlope, Complex.mul_re]; ring
    have him_m : (-I * (discPoint τ T w₀ - 1 / 2)).im =
        -(w₀.re + τ * Real.log (T / (2 * Real.pi)) - 1 / 2) := by
      have e : (-I * (discPoint τ T w₀ - 1 / 2)).im = -((discPoint τ T w₀).re - 1 / 2) := by
        simp [Complex.mul_im]
      have hsre : (discPoint τ T w₀).re = w₀.re + 2 * τ * (horizontalSlope T).re := by
        simp [discPoint]
      rw [e, hsre, horizontalSlope_re]; ring
    have hre := abs_le.mp ((Complex.abs_re_le_norm _).trans hzm)
    have him := abs_le.mp ((Complex.abs_im_le_norm _).trans hzm)
    rw [Complex.sub_re, hre_m] at hre
    rw [Complex.sub_im, him_m] at him
    -- the model depth exceeds `|Re w₀| + 2 − ½`
    have hlog : |w₀.re| + 2 ≤ τ * Real.log (T / (2 * Real.pi)) := by
      have h1 : Real.exp ((|w₀.re| + 2) / τ) ≤ T / (2 * Real.pi) := by
        rw [le_div_iff₀ (by positivity)]; linarith
      have h2 := Real.log_le_log (Real.exp_pos _) h1
      rw [Real.log_exp, div_le_iff₀ hτ] at h2
      linarith
    have him1 : z.im ≤ -1 := by linarith [him.2, neg_abs_le w₀.re]
    exact ⟨z, hz, by linarith, by linarith [hre.1], by linarith [hre.2]⟩
  choose z hz using hk
  have hL2 : 0 < L + 2 := by linarith
  -- different windows give different zeros
  have hinj : Function.Injective z := by
    intro i j hij
    by_contra hne
    have key : ∀ a b : ℕ, a < b → z a ≠ z b := by
      intro a b hab heq
      have ha := (hz a).2.2.2
      have hb := (hz b).2.2.1
      rw [heq] at ha
      have hab' : (a : ℝ) + 1 ≤ b := by exact_mod_cast hab
      nlinarith
    rcases lt_or_gt_of_ne hne with h | h
    · exact key i j h hij
    · exact key j i h hij.symm
  set C₀ : ℝ := R₁ + L + |w₀.im| + τ * (Real.pi / 2) + 1 with hC₀
  have hC₀pos : 0 < C₀ := by
    have : 0 ≤ |w₀.im| := abs_nonneg _
    linarith
  refine ⟨1 / (2 * (L + 2)), 2 * C₀, by positivity, fun X hX => ?_⟩
  have hXC : 0 ≤ (X - C₀) / (L + 2) := div_nonneg (by linarith) hL2.le
  set K : ℕ := ⌊(X - C₀) / (L + 2)⌋₊ + 1 with hK
  refine ⟨(Finset.range K).image z, fun w hw => ?_, ?_⟩
  · obtain ⟨k, hkK, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨h1, h2, h3, h4⟩ := hz k
    have hk0 : (0 : ℝ) ≤ k * (L + 2) := by positivity
    have hkle : (k : ℝ) ≤ (X - C₀) / (L + 2) := by
      have : k ≤ ⌊(X - C₀) / (L + 2)⌋₊ := Nat.lt_succ_iff.mp (Finset.mem_range.mp hkK)
      exact (Nat.cast_le.mpr this).trans (Nat.floor_le hXC)
    have hkL : (k : ℝ) * (L + 2) ≤ X - C₀ := by
      rwa [le_div_iff₀ hL2] at hkle
    refine ⟨h1, h2, by linarith [neg_abs_le w₀.im], by linarith [le_abs_self w₀.im]⟩
  · rw [Finset.card_image_of_injective _ hinj, Finset.card_range, hK]
    have hlt := Nat.lt_floor_add_one ((X - C₀) / (L + 2))
    push_cast
    have h1 : 1 / (2 * (L + 2)) * X ≤ (X - C₀) / (L + 2) := by
      rw [div_mul_eq_mul_div, one_mul, div_le_div_iff₀ (by positivity) hL2]
      nlinarith
    linarith

end

end RHTower.DeBruijn
