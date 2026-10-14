import GaloisForLFunctions.HTGeometry.ClampedBeamPositivity

/-!
# Clamped beams under a load with nonnegative cumulative moment

Let `u` be a deflection on `[a, b]`, clamped at both ends (`u = u' = 0`), and let the bending
moment `M = E u''` with stiffness `E > 0` have derivative `Φ = M'`.  The load is not assumed to be
nonnegative.  It is enough that the shear `Φ` is `≤ 0` on `(a, c]` and `≥ 0` on `[c, b)` for some
`c ∈ (a, b)`: the bending moment is then antitone on the left and monotone on the right, its negative
set is an interval, and `u'' = M / E` has the sign pattern `(+, −, +)`.

**Theorem** (`nonneg_of_clampedBeam_of_cumulativeLoad`).  Under these hypotheses `u ≥ 0` on
`[a, b]`.

All regularity is required only on the open interval `(a, b)`, with `u` and `u'` continuous on
`[a, b]`.  This admits loads that are singular at the ends, as long as the slope stays continuous.

For the stiffness `cosh²` this applies to the spherical bi-Laplacian `𝔐²`, `𝔐 = cosh² s · ∂_s²`
(`nonneg_of_coshSq_clampedBeam_of_cumulativeLoad`).  For a load symmetric about `c = 0`, the shear
`Φ(s) = ∫₀ˢ σ` is the cumulative load from the centre.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

/-- **The sign-pattern lemma with interior regularity.**  If `u, u'` are continuous on `[a, b]`,
differentiable on `(a, b)` with `u'' = g`, `g` has the sign pattern `(+, −, +)` on
`(a, s₁), (s₁, s₂), (s₂, b)`, and `u(a) = u'(a) = u(b) = u'(b) = 0`, then `u ≥ 0` on `[a, b]`. -/
theorem nonneg_of_clamped_of_signPattern_Ioo {a s₁ s₂ b : ℝ} (h1 : a ≤ s₁) (h2 : s₁ ≤ s₂)
    (h3 : s₂ ≤ b) {u u' g : ℝ → ℝ} (cu : ContinuousOn u (Icc a b))
    (cu' : ContinuousOn u' (Icc a b)) (hu : ∀ x ∈ Ioo a b, HasDerivAt u (u' x) x)
    (hu' : ∀ x ∈ Ioo a b, HasDerivAt u' (g x) x) (hpos1 : ∀ x ∈ Ioo a s₁, 0 ≤ g x)
    (hneg : ∀ x ∈ Ioo s₁ s₂, g x ≤ 0) (hpos2 : ∀ x ∈ Ioo s₂ b, 0 ≤ g x)
    (ha : u a = 0) (ha' : u' a = 0) (hb : u b = 0) (hb' : u' b = 0) :
    ∀ x ∈ Icc a b, 0 ≤ u x := by
  have sub : ∀ {p q : ℝ}, a ≤ p → q ≤ b → Icc p q ⊆ Icc a b := fun hp hq =>
    Icc_subset_Icc hp hq
  have isub : ∀ {p q : ℝ}, a ≤ p → q ≤ b → Ioo p q ⊆ Ioo a b := fun hp hq =>
    Ioo_subset_Ioo hp hq
  have du : ∀ {p q : ℝ}, a ≤ p → q ≤ b → DifferentiableOn ℝ u (interior (Icc p q)) :=
    fun hp hq x hx => by
      rw [interior_Icc] at hx
      exact (hu x (isub hp hq hx)).differentiableAt.differentiableWithinAt
  have du' : ∀ {p q : ℝ}, a ≤ p → q ≤ b → DifferentiableOn ℝ u' (interior (Icc p q)) :=
    fun hp hq x hx => by
      rw [interior_Icc] at hx
      exact (hu' x (isub hp hq hx)).differentiableAt.differentiableWithinAt
  have hb1 : s₁ ≤ b := h2.trans h3
  have ha2 : a ≤ s₂ := h1.trans h2
  -- the left piece
  have left : ∀ x ∈ Icc a s₁, 0 ≤ u x := by
    have hm' : MonotoneOn u' (Icc a s₁) :=
      monotoneOn_of_deriv_nonneg (convex_Icc a s₁) (cu'.mono (sub le_rfl hb1)) (du' le_rfl hb1)
        (fun x hx => by
          rw [interior_Icc] at hx
          rw [(hu' x (isub le_rfl hb1 hx)).deriv]; exact hpos1 x hx)
    have hm : MonotoneOn u (Icc a s₁) :=
      monotoneOn_of_deriv_nonneg (convex_Icc a s₁) (cu.mono (sub le_rfl hb1)) (du le_rfl hb1)
        (fun x hx => by
          rw [interior_Icc] at hx
          rw [(hu x (isub le_rfl hb1 hx)).deriv, ← ha']
          exact hm' ⟨le_rfl, h1⟩ (Ioo_subset_Icc_self hx) hx.1.le)
    intro x hx
    rw [← ha]
    exact hm ⟨le_rfl, h1⟩ hx hx.1
  -- the right piece
  have right : ∀ x ∈ Icc s₂ b, 0 ≤ u x := by
    have hm' : MonotoneOn u' (Icc s₂ b) :=
      monotoneOn_of_deriv_nonneg (convex_Icc s₂ b) (cu'.mono (sub ha2 le_rfl)) (du' ha2 le_rfl)
        (fun x hx => by
          rw [interior_Icc] at hx
          rw [(hu' x (isub ha2 le_rfl hx)).deriv]; exact hpos2 x hx)
    have hm : AntitoneOn u (Icc s₂ b) :=
      antitoneOn_of_deriv_nonpos (convex_Icc s₂ b) (cu.mono (sub ha2 le_rfl)) (du ha2 le_rfl)
        (fun x hx => by
          rw [interior_Icc] at hx
          rw [(hu x (isub ha2 le_rfl hx)).deriv, ← hb']
          exact hm' (Ioo_subset_Icc_self hx) ⟨h3, le_rfl⟩ hx.2.le)
    intro x hx
    rw [← hb]
    exact hm hx ⟨h3, le_rfl⟩ hx.2
  -- the middle piece
  have hconc : ConcaveOn ℝ (Icc s₁ s₂) u := by
    refine AntitoneOn.concaveOn_of_deriv (convex_Icc s₁ s₂) (cu.mono (sub h1 h3)) (du h1 h3) ?_
    have ha'' : AntitoneOn u' (Icc s₁ s₂) :=
      antitoneOn_of_deriv_nonpos (convex_Icc s₁ s₂) (cu'.mono (sub h1 h3)) (du' h1 h3)
        (fun x hx => by
          rw [interior_Icc] at hx
          rw [(hu' x (isub h1 h3 hx)).deriv]; exact hneg x hx)
    intro x hx y hy hxy
    rw [interior_Icc] at hx hy
    rw [(hu x (isub h1 h3 hx)).deriv, (hu y (isub h1 h3 hy)).deriv]
    exact ha'' (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hy) hxy
  intro x hx
  rcases le_total x s₁ with hx1 | hx1
  · exact left x ⟨hx.1, hx1⟩
  rcases le_total s₂ x with hx2 | hx2
  · exact right x ⟨hx2, hx.2⟩
  have e1 := left s₁ ⟨h1, le_rfl⟩
  have e2 := right s₂ ⟨le_rfl, h3⟩
  have hmin := hconc.min_le_of_mem_Icc (left_mem_Icc.mpr h2) (right_mem_Icc.mpr h2) ⟨hx1, hx2⟩
  exact le_trans (le_min e1 e2) hmin

/-- **A function whose negative set in `(a, b)` is order-connected has sign pattern `(+, −, +)`.** -/
theorem exists_signPattern_of_ordConnected {a b : ℝ} (hab : a ≤ b) {M : ℝ → ℝ}
    (hN : OrdConnected {x | x ∈ Ioo a b ∧ M x < 0}) :
    ∃ s₁ s₂, a ≤ s₁ ∧ s₁ ≤ s₂ ∧ s₂ ≤ b ∧ (∀ x ∈ Ioo a s₁, 0 ≤ M x) ∧
      (∀ x ∈ Ioo s₁ s₂, M x ≤ 0) ∧ ∀ x ∈ Ioo s₂ b, 0 ≤ M x := by
  set N := {x | x ∈ Ioo a b ∧ M x < 0} with hNdef
  by_cases hne : N.Nonempty
  · have hbdd : BddBelow N := ⟨a, fun x hx => hx.1.1.le⟩
    have hbdd' : BddAbove N := ⟨b, fun x hx => hx.1.2.le⟩
    have hs12 : sInf N ≤ sSup N := csInf_le_csSup hne hbdd hbdd'
    have ha1 : a ≤ sInf N := le_csInf hne fun x hx => hx.1.1.le
    have hb2 : sSup N ≤ b := csSup_le hne fun x hx => hx.1.2.le
    refine ⟨sInf N, sSup N, ha1, hs12, hb2, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · by_contra hlt
      have hxN : x ∈ N := ⟨⟨hx.1, hx.2.trans_le (hs12.trans hb2)⟩, lt_of_not_ge hlt⟩
      exact absurd (csInf_le hbdd hxN) (not_le.mpr hx.2)
    · obtain ⟨p, hp, hpx⟩ := exists_lt_of_csInf_lt hne hx.1
      obtain ⟨q, hq, hxq⟩ := exists_lt_of_lt_csSup hne hx.2
      exact (hN.out hp hq ⟨hpx.le, hxq.le⟩).2.le
    · by_contra hlt
      have hxN : x ∈ N := ⟨⟨(ha1.trans hs12).trans_lt hx.1, hx.2⟩, lt_of_not_ge hlt⟩
      exact absurd (le_csSup hbdd' hxN) (not_le.mpr hx.1)
  · refine ⟨a, a, le_rfl, le_rfl, hab, fun x hx => absurd hx.2 (not_lt.mpr hx.1.le),
      fun x hx => absurd hx.2 (not_lt.mpr hx.1.le), fun x hx => ?_⟩
    by_contra hlt
    exact hne ⟨x, hx, lt_of_not_ge hlt⟩

/-- **A moment that is antitone left of `c` and monotone right of `c` has an order-connected
negative set.** -/
theorem ordConnected_neg_of_antitone_monotone {a c b : ℝ} {M : ℝ → ℝ}
    (hl : AntitoneOn M (Ioc a c)) (hr : MonotoneOn M (Ico c b)) :
    OrdConnected {x | x ∈ Ioo a b ∧ M x < 0} := by
  refine ⟨fun x hx y hy z hz => ⟨⟨hx.1.1.trans_le hz.1, hz.2.trans_lt hy.1.2⟩, ?_⟩⟩
  rcases le_total z c with hzc | hzc
  · have hxc : x ≤ c := hz.1.trans hzc
    exact (hl ⟨hx.1.1, hxc⟩ ⟨hx.1.1.trans_le hz.1, hzc⟩ hz.1).trans_lt hx.2
  · have hyc : c ≤ y := hzc.trans hz.2
    exact (hr ⟨hzc, hz.2.trans_lt hy.1.2⟩ ⟨hyc, hy.1.2⟩ hz.2).trans_lt hy.2

/-- **Monotonicity of a function from the sign of its derivative on an open interval.**  If
`HasDerivAt M (Φ x) x` on `(a, b)` and `Φ ≥ 0` on `[x, y] ⊆ (a, b)`, then `M x ≤ M y`. -/
theorem clampedBeam_le_of_hasDerivAt_nonneg {a b x y : ℝ} {M Φ : ℝ → ℝ}
    (hdM : ∀ z ∈ Ioo a b, HasDerivAt M (Φ z) z) (hx : a < x) (hy : y < b) (hxy : x ≤ y)
    (hΦ : ∀ z ∈ Icc x y, 0 ≤ Φ z) : M x ≤ M y := by
  have hin : ∀ z ∈ Icc x y, z ∈ Ioo a b := fun z hz => ⟨hx.trans_le hz.1, hz.2.trans_lt hy⟩
  have hmono : MonotoneOn M (Icc x y) :=
    monotoneOn_of_deriv_nonneg (convex_Icc x y)
      (fun z hz => (hdM z (hin z hz)).continuousAt.continuousWithinAt)
      (fun z hz => by
        rw [interior_Icc] at hz
        exact (hdM z (hin z (Ioo_subset_Icc_self hz))).differentiableAt.differentiableWithinAt)
      (fun z hz => by
        rw [interior_Icc] at hz
        rw [(hdM z (hin z (Ioo_subset_Icc_self hz))).deriv]
        exact hΦ z (Ioo_subset_Icc_self hz))
  exact hmono ⟨le_rfl, hxy⟩ ⟨hxy, le_rfl⟩ hxy

/-- **Clamped beams under a load with nonnegative cumulative moment are positivity preserving.**
Let `a < c < b`, `E > 0` on `(a, b)` and `M = E u''` with `M' = Φ` on `(a, b)`, where `Φ ≤ 0` on
`(a, c]` and `Φ ≥ 0` on `[c, b)`.  If `u, u'` are continuous on `[a, b]` and
`u(a) = u'(a) = u(b) = u'(b) = 0`, then `u ≥ 0` on `[a, b]`. -/
theorem nonneg_of_clampedBeam_of_cumulativeLoad {a c b : ℝ} (hac : a < c) (hcb : c < b)
    {u u' g E M Φ : ℝ → ℝ} (cu : ContinuousOn u (Icc a b)) (cu' : ContinuousOn u' (Icc a b))
    (hu : ∀ x ∈ Ioo a b, HasDerivAt u (u' x) x) (hu' : ∀ x ∈ Ioo a b, HasDerivAt u' (g x) x)
    (hE : ∀ x ∈ Ioo a b, 0 < E x) (hM : ∀ x ∈ Ioo a b, M x = E x * g x)
    (hdM : ∀ x ∈ Ioo a b, HasDerivAt M (Φ x) x) (hΦl : ∀ x ∈ Ioc a c, Φ x ≤ 0)
    (hΦr : ∀ x ∈ Ico c b, 0 ≤ Φ x)
    (ha : u a = 0) (ha' : u' a = 0) (hb : u b = 0) (hb' : u' b = 0) :
    ∀ x ∈ Icc a b, 0 ≤ u x := by
  have hab : a ≤ b := (hac.trans hcb).le
  have hl : AntitoneOn M (Ioc a c) := by
    intro x hx y hy hxy
    have h := clampedBeam_le_of_hasDerivAt_nonneg (M := fun z => -M z) (Φ := fun z => -Φ z)
      (fun z hz => (hdM z hz).neg) hx.1 (hy.2.trans_lt hcb) hxy
      (fun z hz => neg_nonneg.mpr (hΦl z ⟨hx.1.trans_le hz.1, hz.2.trans hy.2⟩))
    simpa using h
  have hr : MonotoneOn M (Ico c b) := fun x hx y hy hxy =>
    clampedBeam_le_of_hasDerivAt_nonneg hdM (hac.trans_le hx.1) hy.2 hxy
      (fun z hz => hΦr z ⟨hx.1.trans hz.1, hz.2.trans_lt hy.2⟩)
  obtain ⟨s₁, s₂, h1, h2, h3, p1, n, p2⟩ :=
    exists_signPattern_of_ordConnected hab (ordConnected_neg_of_antitone_monotone hl hr)
  have pos : ∀ x ∈ Ioo a b, 0 ≤ M x → 0 ≤ g x := fun x hx h => by
    rw [hM x hx] at h
    exact nonneg_of_mul_nonneg_right (by linarith [mul_comm (E x) (g x)]) (hE x hx)
  have neg : ∀ x ∈ Ioo a b, M x ≤ 0 → g x ≤ 0 := fun x hx h => by
    rw [hM x hx] at h
    by_contra hg
    exact absurd h (not_le.mpr (mul_pos (hE x hx) (lt_of_not_ge hg)))
  refine nonneg_of_clamped_of_signPattern_Ioo h1 h2 h3 cu cu' hu hu'
    (fun x hx => pos x ⟨hx.1, hx.2.trans_le (h2.trans h3)⟩ (p1 x hx))
    (fun x hx => neg x ⟨h1.trans_lt hx.1, hx.2.trans_le h3⟩ (n x hx))
    (fun x hx => pos x ⟨(h1.trans h2).trans_lt hx.1, hx.2⟩ (p2 x hx)) ha ha' hb hb'

/-- **The spherical bi-Laplacian under a load with nonnegative cumulative moment.**  In
`s = log tan(α/2)`, `𝔐 = cosh² s · ∂_s²`.  If `κ` is clamped at both ends of `[a, b]`, its bending
moment `M = cosh² · κ''` has shear `M' = Φ` with `Φ ≤ 0` on `(a, c]` and `Φ ≥ 0` on `[c, b)`, then
`κ ≥ 0` on `[a, b]`. -/
theorem nonneg_of_coshSq_clampedBeam_of_cumulativeLoad {a c b : ℝ} (hac : a < c) (hcb : c < b)
    {κ κ' g M Φ : ℝ → ℝ} (cκ : ContinuousOn κ (Icc a b)) (cκ' : ContinuousOn κ' (Icc a b))
    (hκ : ∀ x ∈ Ioo a b, HasDerivAt κ (κ' x) x) (hκ' : ∀ x ∈ Ioo a b, HasDerivAt κ' (g x) x)
    (hM : ∀ x ∈ Ioo a b, M x = Real.cosh x ^ 2 * g x)
    (hdM : ∀ x ∈ Ioo a b, HasDerivAt M (Φ x) x) (hΦl : ∀ x ∈ Ioc a c, Φ x ≤ 0)
    (hΦr : ∀ x ∈ Ico c b, 0 ≤ Φ x)
    (ha : κ a = 0) (ha' : κ' a = 0) (hb : κ b = 0) (hb' : κ' b = 0) :
    ∀ x ∈ Icc a b, 0 ≤ κ x :=
  nonneg_of_clampedBeam_of_cumulativeLoad hac hcb cκ cκ' hκ hκ'
    (fun x _ => pow_pos (Real.cosh_pos x) 2) hM hdM hΦl hΦr ha ha' hb hb'

end GaloisForLFunctions.HTGeometry
