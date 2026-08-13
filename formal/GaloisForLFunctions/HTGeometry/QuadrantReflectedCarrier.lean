import GaloisForLFunctions.HTGeometry.QuadrantHolomorphic

/-!
# Rectangular carriers in the critical quadrant and their conjugate doubles

Every compact subset of the critical quadrant sits inside a closed rectangle which is still
contained in the quadrant: the four extreme values of the real and imaginary parts on the compact
set are attained, and they inherit the strict inequalities defining the quadrant.

Doubling such a rectangle by complex conjugation produces a conjugation-symmetric compact set whose
real parts still lie in the open interval `(0, 1)`, whose complement contains the horizontal strip
`|Im| < c`, and whose two halves are separated by that strip.  The complement of a single rectangle
is preconnected, being covered by four half-planes chained through common points.

* `GaloisForLFunctions.HTGeometry.rect`, `GaloisForLFunctions.HTGeometry.doubledRect`;
* `GaloisForLFunctions.HTGeometry.exists_rect_of_isCompact_subset_criticalQuadrant`;
* `GaloisForLFunctions.HTGeometry.isPreconnected_compl_rect`.
-/

noncomputable section

open Complex Set

namespace GaloisForLFunctions.HTGeometry

open _root_.HTGeometry

/-- The closed rectangle with real part in `[a, b]` and imaginary part in `[c, d]`. -/
def rect (a b c d : ℝ) : Set ℂ := Icc a b ×ℂ Icc c d

@[simp] theorem mem_rect {a b c d : ℝ} {z : ℂ} :
    z ∈ rect a b c d ↔ (a ≤ z.re ∧ z.re ≤ b) ∧ c ≤ z.im ∧ z.im ≤ d := by
  simp [rect, Complex.mem_reProdIm]

theorem isClosed_rect (a b c d : ℝ) : IsClosed (rect a b c d) := by
  have h : rect a b c d
      = (Complex.re ⁻¹' Icc a b) ∩ (Complex.im ⁻¹' Icc c d) := rfl
  rw [h]
  exact (isClosed_Icc.preimage Complex.continuous_re).inter
    (isClosed_Icc.preimage Complex.continuous_im)

theorem isBounded_rect (a b c d : ℝ) : Bornology.IsBounded (rect a b c d) := by
  refine (Metric.isBounded_iff_subset_closedBall 0).2
    ⟨(|a| + |b|) + (|c| + |d|), fun z hz => ?_⟩
  rw [mem_rect] at hz
  obtain ⟨⟨h1, h2⟩, h3, h4⟩ := hz
  have hre : |z.re| ≤ |a| + |b| := by
    rcases le_or_gt 0 z.re with h | h
    · rw [abs_of_nonneg h]
      have : z.re ≤ |b| := le_trans h2 (le_abs_self b)
      have : (0:ℝ) ≤ |a| := abs_nonneg a
      linarith [le_trans h2 (le_abs_self b), abs_nonneg a]
    · rw [abs_of_neg h]
      have h5 : -z.re ≤ -a := by linarith
      have h6 : -a ≤ |a| := neg_le_abs a
      linarith [abs_nonneg b]
  have him : |z.im| ≤ |c| + |d| := by
    rcases le_or_gt 0 z.im with h | h
    · rw [abs_of_nonneg h]
      linarith [le_trans h4 (le_abs_self d), abs_nonneg c]
    · rw [abs_of_neg h]
      have h5 : -z.im ≤ -c := by linarith
      have h6 : -c ≤ |c| := neg_le_abs c
      linarith [abs_nonneg d]
  have := Complex.norm_le_abs_re_add_abs_im z
  simp only [Metric.mem_closedBall, dist_zero_right]
  linarith

theorem isCompact_rect (a b c d : ℝ) : IsCompact (rect a b c d) :=
  Metric.isCompact_of_isClosed_isBounded (isClosed_rect a b c d) (isBounded_rect a b c d)

/-- **Every compact subset of the critical quadrant lies in a rectangle inside the quadrant.** -/
theorem exists_rect_of_isCompact_subset_criticalQuadrant {K₀ : Set ℂ} (hK : IsCompact K₀)
    (hsub : K₀ ⊆ criticalQuadrant) :
    ∃ a b c d : ℝ, 1 / 2 < a ∧ a ≤ b ∧ b < 1 ∧ 0 < c ∧ c ≤ d ∧
      K₀ ⊆ rect a b c d ∧ rect a b c d ⊆ criticalQuadrant := by
  rcases K₀.eq_empty_or_nonempty with hempty | hne
  · refine ⟨3 / 4, 3 / 4, 1, 1, by norm_num, le_refl _, by norm_num, by norm_num, le_refl _,
      by simp [hempty], ?_⟩
    intro z hz
    rw [mem_rect] at hz
    rw [_root_.HTGeometry.mem_criticalQuadrant]
    exact ⟨by linarith [hz.1.1], by linarith [hz.1.2], by linarith [hz.2.1]⟩
  · obtain ⟨p, hp, hpmin⟩ := hK.exists_isMinOn hne Complex.continuous_re.continuousOn
    obtain ⟨q, hq, hqmax⟩ := hK.exists_isMaxOn hne Complex.continuous_re.continuousOn
    obtain ⟨r, hr, hrmin⟩ := hK.exists_isMinOn hne Complex.continuous_im.continuousOn
    obtain ⟨t, ht, htmax⟩ := hK.exists_isMaxOn hne Complex.continuous_im.continuousOn
    have hpmin' : ∀ z ∈ K₀, p.re ≤ z.re := fun z hz => hpmin hz
    have hqmax' : ∀ z ∈ K₀, z.re ≤ q.re := fun z hz => hqmax hz
    have hrmin' : ∀ z ∈ K₀, r.im ≤ z.im := fun z hz => hrmin hz
    have htmax' : ∀ z ∈ K₀, z.im ≤ t.im := fun z hz => htmax hz
    have hpq : p.re ≤ q.re := hpmin' q hq
    have hrt : r.im ≤ t.im := hrmin' t ht
    have hpa : 1 / 2 < p.re := (_root_.HTGeometry.mem_criticalQuadrant.mp (hsub hp)).1
    have hqb : q.re < 1 := (_root_.HTGeometry.mem_criticalQuadrant.mp (hsub hq)).2.1
    have hrc : 0 < r.im := (_root_.HTGeometry.mem_criticalQuadrant.mp (hsub hr)).2.2
    refine ⟨p.re, q.re, r.im, t.im, hpa, hpq, hqb, hrc, hrt, ?_, ?_⟩
    · intro z hz
      rw [mem_rect]
      exact ⟨⟨hpmin' z hz, hqmax' z hz⟩, hrmin' z hz, htmax' z hz⟩
    · intro z hz
      rw [mem_rect] at hz
      rw [_root_.HTGeometry.mem_criticalQuadrant]
      exact ⟨by linarith [hz.1.1], by linarith [hz.1.2], by linarith [hz.2.1]⟩

/-! ## The conjugation-symmetric double -/

/-- The conjugation-symmetric double of a rectangle in the upper half plane. -/
def doubledRect (a b c d : ℝ) : Set ℂ := Icc a b ×ℂ (Icc (-d) (-c) ∪ Icc c d)

@[simp] theorem mem_doubledRect {a b c d : ℝ} {z : ℂ} :
    z ∈ doubledRect a b c d ↔
      (a ≤ z.re ∧ z.re ≤ b) ∧ ((-d ≤ z.im ∧ z.im ≤ -c) ∨ (c ≤ z.im ∧ z.im ≤ d)) := by
  simp [doubledRect, Complex.mem_reProdIm]

theorem rect_subset_doubledRect (a b c d : ℝ) : rect a b c d ⊆ doubledRect a b c d := by
  intro z hz
  rw [mem_rect] at hz
  rw [mem_doubledRect]
  exact ⟨hz.1, Or.inr hz.2⟩

theorem isClosed_doubledRect (a b c d : ℝ) : IsClosed (doubledRect a b c d) := by
  have h : doubledRect a b c d
      = (Complex.re ⁻¹' Icc a b) ∩ (Complex.im ⁻¹' (Icc (-d) (-c) ∪ Icc c d)) := rfl
  rw [h]
  exact (isClosed_Icc.preimage Complex.continuous_re).inter
    ((isClosed_Icc.union isClosed_Icc).preimage Complex.continuous_im)

theorem doubledRect_subset_rect (a b : ℝ) {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) :
    doubledRect a b c d ⊆ rect a b (-d) d := by
  intro z hz
  rw [mem_doubledRect] at hz
  rw [mem_rect]
  refine ⟨hz.1, ?_⟩
  rcases hz.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1, by linarith⟩
  · exact ⟨by linarith, h2⟩

theorem isCompact_doubledRect (a b : ℝ) {c d : ℝ} (hc : 0 ≤ c) (hcd : c ≤ d) :
    IsCompact (doubledRect a b c d) :=
  (isCompact_rect a b (-d) d).of_isClosed_subset (isClosed_doubledRect a b c d)
    (doubledRect_subset_rect a b hc hcd)

theorem conj_mem_doubledRect {a b c d : ℝ} {z : ℂ} (hz : z ∈ doubledRect a b c d) :
    (starRingEnd ℂ) z ∈ doubledRect a b c d := by
  rw [mem_doubledRect] at hz ⊢
  refine ⟨by simpa using hz.1, ?_⟩
  rcases hz.2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · right
    constructor <;> simp <;> linarith
  · left
    constructor <;> simp <;> linarith

/-! ## Connectivity of the complements -/

theorem compl_rect_eq {a b c d : ℝ} :
    (rect a b c d)ᶜ
      = (({z : ℂ | z.re < a} ∪ {z : ℂ | z.im < c}) ∪ {z : ℂ | b < z.re}) ∪ {z : ℂ | d < z.im} := by
  ext z
  simp only [Set.mem_compl_iff, mem_rect, Set.mem_union, Set.mem_setOf_eq, not_and_or, not_le]
  tauto

/-- **The complement of a closed rectangle is preconnected**, being four half-planes chained
through common points. -/
theorem isPreconnected_compl_rect (a b c d : ℝ) : IsPreconnected ((rect a b c d)ᶜ) := by
  have h1 : IsPreconnected {z : ℂ | z.re < a} := (convex_halfSpace_re_lt a).isPreconnected
  have h2 : IsPreconnected {z : ℂ | z.im < c} := (convex_halfSpace_im_lt c).isPreconnected
  have h3 : IsPreconnected {z : ℂ | b < z.re} := (convex_halfSpace_re_gt b).isPreconnected
  have h4 : IsPreconnected {z : ℂ | d < z.im} := (convex_halfSpace_im_gt d).isPreconnected
  have p12 : IsPreconnected ({z : ℂ | z.re < a} ∪ {z : ℂ | z.im < c}) := by
    refine IsPreconnected.union (((a - 1 : ℝ) : ℂ) + ((c - 1 : ℝ) : ℂ) * I) ?_ ?_ h1 h2 <;>
      · simp only [Set.mem_setOf_eq, Complex.add_re, Complex.add_im, Complex.ofReal_re,
          Complex.ofReal_im, Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im]
        linarith
  have p123 : IsPreconnected (({z : ℂ | z.re < a} ∪ {z : ℂ | z.im < c}) ∪ {z : ℂ | b < z.re}) := by
    refine IsPreconnected.union (((b + 1 : ℝ) : ℂ) + ((c - 1 : ℝ) : ℂ) * I) ?_ ?_ p12 h3
    · right
      simp only [Set.mem_setOf_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im]
      linarith
    · simp only [Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      linarith
  have p1234 : IsPreconnected
      ((({z : ℂ | z.re < a} ∪ {z : ℂ | z.im < c}) ∪ {z : ℂ | b < z.re}) ∪ {z : ℂ | d < z.im}) := by
    refine IsPreconnected.union (((b + 1 : ℝ) : ℂ) + ((d + 1 : ℝ) : ℂ) * I) ?_ ?_ p123 h4
    · right
      simp only [Set.mem_setOf_eq, Complex.add_re, Complex.ofReal_re, Complex.mul_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]
      linarith
    · simp only [Set.mem_setOf_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im,
        Complex.ofReal_re, Complex.I_re, Complex.I_im]
      linarith
  rw [compl_rect_eq]
  exact p1234

/-- The horizontal strip separating the two halves of the doubled rectangle. -/
def midStrip (c : ℝ) : Set ℂ := {z : ℂ | -c < z.im ∧ z.im < c}

theorem isOpen_midStrip (c : ℝ) : IsOpen (midStrip c) :=
  (isOpen_lt continuous_const Complex.continuous_im).inter
    (isOpen_lt Complex.continuous_im continuous_const)

theorem convex_midStrip (c : ℝ) : Convex ℝ (midStrip c) :=
  (convex_halfSpace_im_gt (-c)).inter (convex_halfSpace_im_lt c)

theorem midStrip_subset_compl_doubledRect {a b c d : ℝ} :
    midStrip c ⊆ (doubledRect a b c d)ᶜ := by
  intro z hz hcon
  rw [mem_doubledRect] at hcon
  rcases hcon.2 with ⟨_, h2⟩ | ⟨h1, _⟩
  · exact absurd hz.1 (not_lt.mpr h2)
  · exact absurd hz.2 (not_lt.mpr h1)

theorem midStrip_subset_compl_rect {a b c d : ℝ} : midStrip c ⊆ (rect a b c d)ᶜ :=
  fun _ hz => fun hcon => (midStrip_subset_compl_doubledRect hz)
    (rect_subset_doubledRect a b c d hcon)

end GaloisForLFunctions.HTGeometry
