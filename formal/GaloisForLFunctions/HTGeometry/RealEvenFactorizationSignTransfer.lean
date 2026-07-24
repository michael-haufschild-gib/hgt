import Mathlib

open Set

namespace HTGeometry

/-- A real function factors on `[a,b]` through finitely many even-multiplicity roots, all lying
in `[a,b)`, and a continuous nowhere-zero cofactor.  The left endpoint is deliberately allowed
as a root; this is the form needed to transport nonnegativity without separately proving central
nonvanishing. -/
def RealEvenFactorizationOn (f : ℝ → ℝ) (a b : ℝ) : Prop :=
  ∃ (zs : Finset ℝ) (m : ℝ → ℕ) (u : ℝ → ℝ),
    (∀ z ∈ zs, a ≤ z ∧ z < b) ∧
      ContinuousOn u (Icc a b) ∧
      (∀ x ∈ Icc a b, u x ≠ 0) ∧
      (∀ x ∈ Icc a b,
        f x = (∏ z ∈ zs, (x - z) ^ m z) * u x) ∧
      (∀ z ∈ zs, Even (m z))

/-- A continuous nowhere-zero real function has endpoint values of the same strict sign. -/
theorem continuousOn_nonzero_endpoint_product_pos {u : ℝ → ℝ} {a b : ℝ}
    (hab : a ≤ b) (hu : ContinuousOn u (Icc a b))
    (hne : ∀ x ∈ Icc a b, u x ≠ 0) :
    0 < u a * u b := by
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab
  have hsign : 0 < u a ↔ 0 < u b := by
    constructor
    · intro hua
      by_contra hub
      have hub' : u b < 0 := lt_of_le_of_ne (not_lt.mp hub) (hne b hb)
      obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc' hab hu ⟨hub'.le, hua.le⟩
      exact hne c hc hc0
    · intro hub
      by_contra hua
      have hua' : u a < 0 := lt_of_le_of_ne (not_lt.mp hua) (hne a ha)
      obtain ⟨c, hc, hc0⟩ := intermediate_value_Icc hab hu ⟨hua'.le, hub.le⟩
      exact hne c hc hc0
  rcases lt_or_gt_of_ne (hne a ha) with hua | hua
  · have hub : u b < 0 := by
      by_contra h
      have hub : 0 < u b := lt_of_le_of_ne (not_lt.mp h) (Ne.symm (hne b hb))
      exact (not_lt_of_ge hua.le) (hsign.mpr hub)
    exact mul_pos_of_neg_of_neg hua hub
  · exact mul_pos hua (hsign.mp hua)

/-- **Even-factor sign transfer.**  A positive right anchor and a finite even-root
factorization force nonnegativity at the left endpoint.  A zero at the left endpoint is allowed,
so no independent endpoint-nonvanishing input is needed. -/
theorem nonneg_left_of_realEvenFactorizationOn_of_right_pos {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hfac : RealEvenFactorizationOn f a b) (hpos : 0 < f b) :
    0 ≤ f a := by
  obtain ⟨zs, m, u, hzs, hu, hune, hfact, heven⟩ := hfac
  have ha : a ∈ Icc a b := left_mem_Icc.mpr hab.le
  have hb : b ∈ Icc a b := right_mem_Icc.mpr hab.le
  let Pa : ℝ := ∏ z ∈ zs, (a - z) ^ m z
  let Pb : ℝ := ∏ z ∈ zs, (b - z) ^ m z
  have hPa : 0 ≤ Pa := by
    dsimp [Pa]
    exact Finset.prod_nonneg fun z hz => (heven z hz).pow_nonneg (a - z)
  have hPb : 0 < Pb := by
    dsimp [Pb]
    apply Finset.prod_pos
    intro z hz
    exact (heven z hz).pow_pos (sub_ne_zero.mpr (ne_of_gt (hzs z hz).2))
  have huab : 0 < u a * u b :=
    continuousOn_nonzero_endpoint_product_pos hab.le hu hune
  have hfb : f b = Pb * u b := by simpa [Pb] using hfact b hb
  have hub : 0 < u b := by
    have hp : 0 < Pb * u b := hfb ▸ hpos
    rcases (mul_pos_iff.mp hp) with h | h
    · exact h.2
    · exact (not_lt_of_ge hPb.le h.1).elim
  have hua : 0 < u a := by
    rcases (mul_pos_iff.mp huab) with h | h
    · exact h.1
    · exact (not_lt_of_ge hub.le h.2).elim
  have hfa : f a = Pa * u a := by simpa [Pa] using hfact a ha
  rw [hfa]
  exact mul_nonneg hPa hua.le

/-- Negating the nowhere-zero cofactor preserves an even-root factorization. -/
theorem RealEvenFactorizationOn.neg {f : ℝ → ℝ} {a b : ℝ}
    (hfac : RealEvenFactorizationOn f a b) :
    RealEvenFactorizationOn (-f) a b := by
  obtain ⟨zs, m, u, hzs, hu, hune, hfact, heven⟩ := hfac
  refine ⟨zs, m, fun x => -u x, hzs, hu.neg, ?_, ?_, heven⟩
  · intro x hx
    exact neg_ne_zero.mpr (hune x hx)
  · intro x hx
    rw [Pi.neg_apply, hfact x hx]
    ring

/-- A finite even-root factorization cannot cross strictly from positive to negative between its
ordered endpoints. -/
theorem not_realEvenFactorizationOn_of_left_pos_of_right_neg
    {f : ℝ → ℝ} {a b : ℝ}
    (hab : a < b) (hleft : 0 < f a) (hright : f b < 0) :
    ¬ RealEvenFactorizationOn f a b := by
  intro hfac
  have hnonneg :
      0 ≤ (-f) a :=
    nonneg_left_of_realEvenFactorizationOn_of_right_pos
      hab hfac.neg (by simpa using neg_pos.mpr hright)
  simp only [Pi.neg_apply, neg_nonneg] at hnonneg
  exact (not_le_of_gt hleft) hnonneg

end HTGeometry
