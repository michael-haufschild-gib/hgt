import Mathlib

/-!
# Clamped beams of variable stiffness are positivity preserving

Let `E > 0` be a stiffness on `[a, b]` and `u` a deflection with clamped ends,
`u(a) = u'(a) = u(b) = u'(b) = 0`, under a nonnegative load: `(E u'')'' = q ≥ 0`.
Then `u ≥ 0` on `[a, b]` (`nonneg_of_clampedBeam`).

The proof is elementary.  The bending moment `M = E u''` has `M'' = q ≥ 0`, so it is convex and
`{M < 0}` is an interval (`exists_signPattern_of_convexOn`).  Hence `u''` has the sign pattern
`(+, −, +)` on `[a, s₁] ∪ [s₁, s₂] ∪ [s₂, b]` (each piece possibly degenerate), and
`nonneg_of_clamped_of_signPattern` concludes:

* on `[a, s₁]` the slope `u'` increases from `u'(a) = 0`, so `u` increases from `u(a) = 0`;
* on `[s₂, b]` the slope increases up to `u'(b) = 0`, so `u` decreases to `u(b) = 0`;
* on `[s₁, s₂]` the function `u` is concave, hence at least `min(u(s₁), u(s₂)) ≥ 0`.

No orthogonality, Gantmacher–Krein theory or smallness of the stiffness variation is needed.

Application: in `s = log tan(α/2)` the spherical Laplacian `𝔐 = (sin α)^{−1} ∂_α sin α ∂_α`
becomes `cosh² s · ∂_s²`, so `𝔐² κ = σ` is the clamped beam with stiffness `cosh² s` and load
`σ / cosh² s` (`nonneg_of_coshSq_clampedBeam`): the clamped Green function of `𝔐²` on any arc is
positivity preserving.
-/

open Set

namespace GaloisForLFunctions.HTGeometry

/-- **The sign-pattern lemma.**  If `u'' ≥ 0` on `(a, s₁)` and `(s₂, b)`, `u'' ≤ 0` on `(s₁, s₂)`,
and `u(a) = u'(a) = u(b) = u'(b) = 0`, then `u ≥ 0` on `[a, b]`. -/
theorem nonneg_of_clamped_of_signPattern {a s₁ s₂ b : ℝ} (h1 : a ≤ s₁) (h2 : s₁ ≤ s₂)
    (h3 : s₂ ≤ b) {u u' g : ℝ → ℝ} (hu : ∀ x, HasDerivAt u (u' x) x)
    (hu' : ∀ x, HasDerivAt u' (g x) x) (hpos1 : ∀ x ∈ Ioo a s₁, 0 ≤ g x)
    (hneg : ∀ x ∈ Ioo s₁ s₂, g x ≤ 0) (hpos2 : ∀ x ∈ Ioo s₂ b, 0 ≤ g x)
    (ha : u a = 0) (ha' : u' a = 0) (hb : u b = 0) (hb' : u' b = 0) :
    ∀ x ∈ Icc a b, 0 ≤ u x := by
  have hdu : ∀ x, deriv u x = u' x := fun x => (hu x).deriv
  have hdu' : ∀ x, deriv u' x = g x := fun x => (hu' x).deriv
  have cu : Continuous u := continuous_iff_continuousAt.mpr fun x => (hu x).continuousAt
  have cu' : Continuous u' := continuous_iff_continuousAt.mpr fun x => (hu' x).continuousAt
  have du : Differentiable ℝ u := fun x => (hu x).differentiableAt
  have du' : Differentiable ℝ u' := fun x => (hu' x).differentiableAt
  -- the left piece
  have left : ∀ x ∈ Icc a s₁, 0 ≤ u x := by
    have hm' : MonotoneOn u' (Icc a s₁) :=
      monotoneOn_of_deriv_nonneg (convex_Icc a s₁) cu'.continuousOn du'.differentiableOn
        (fun x hx => by rw [interior_Icc] at hx; rw [hdu']; exact hpos1 x hx)
    have hm : MonotoneOn u (Icc a s₁) :=
      monotoneOn_of_deriv_nonneg (convex_Icc a s₁) cu.continuousOn du.differentiableOn
        (fun x hx => by
          rw [interior_Icc] at hx
          rw [hdu, ← ha']
          exact hm' ⟨le_rfl, h1⟩ (Ioo_subset_Icc_self hx) hx.1.le)
    intro x hx
    rw [← ha]
    exact hm ⟨le_rfl, h1⟩ hx hx.1
  -- the right piece
  have right : ∀ x ∈ Icc s₂ b, 0 ≤ u x := by
    have hm' : MonotoneOn u' (Icc s₂ b) :=
      monotoneOn_of_deriv_nonneg (convex_Icc s₂ b) cu'.continuousOn du'.differentiableOn
        (fun x hx => by rw [interior_Icc] at hx; rw [hdu']; exact hpos2 x hx)
    have hm : AntitoneOn u (Icc s₂ b) :=
      antitoneOn_of_deriv_nonpos (convex_Icc s₂ b) cu.continuousOn du.differentiableOn
        (fun x hx => by
          rw [interior_Icc] at hx
          rw [hdu, ← hb']
          exact hm' (Ioo_subset_Icc_self hx) ⟨h3, le_rfl⟩ hx.2.le)
    intro x hx
    rw [← hb]
    exact hm hx ⟨h3, le_rfl⟩ hx.2
  -- the middle piece
  have hconc : ConcaveOn ℝ (Icc s₁ s₂) u := by
    refine AntitoneOn.concaveOn_of_deriv (convex_Icc s₁ s₂) cu.continuousOn du.differentiableOn ?_
    have ha'' : AntitoneOn u' (Icc s₁ s₂) :=
      antitoneOn_of_deriv_nonpos (convex_Icc s₁ s₂) cu'.continuousOn du'.differentiableOn
        (fun x hx => by rw [interior_Icc] at hx; rw [hdu']; exact hneg x hx)
    intro x hx y hy hxy
    rw [hdu, hdu]
    rw [interior_Icc] at hx hy
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

/-- **A convex function has sign pattern `(+, −, +)`.** -/
theorem exists_signPattern_of_convexOn {a b : ℝ} (hab : a ≤ b) {M : ℝ → ℝ}
    (hM : ConvexOn ℝ (Icc a b) M) :
    ∃ s₁ s₂, a ≤ s₁ ∧ s₁ ≤ s₂ ∧ s₂ ≤ b ∧ (∀ x ∈ Ioo a s₁, 0 ≤ M x) ∧
      (∀ x ∈ Ioo s₁ s₂, M x ≤ 0) ∧ ∀ x ∈ Ioo s₂ b, 0 ≤ M x := by
  set N := {x | x ∈ Icc a b ∧ M x < 0} with hN
  by_cases hne : N.Nonempty
  · have hNc : Convex ℝ N := hM.convex_lt 0
    have hbdd : BddBelow N := ⟨a, fun x hx => hx.1.1⟩
    have hbdd' : BddAbove N := ⟨b, fun x hx => hx.1.2⟩
    have hs12 : sInf N ≤ sSup N := csInf_le_csSup hne hbdd hbdd'
    have ha1 : a ≤ sInf N := le_csInf hne fun x hx => hx.1.1
    have hb2 : sSup N ≤ b := csSup_le hne fun x hx => hx.1.2
    refine ⟨sInf N, sSup N, ha1, hs12, hb2, fun x hx => ?_, fun x hx => ?_, fun x hx => ?_⟩
    · by_contra hlt
      have hxN : x ∈ N := ⟨⟨hx.1.le, hx.2.le.trans (hs12.trans hb2)⟩, lt_of_not_ge hlt⟩
      exact absurd (csInf_le hbdd hxN) (not_le.mpr hx.2)
    · obtain ⟨p, hp, hpx⟩ := exists_lt_of_csInf_lt hne hx.1
      obtain ⟨q, hq, hxq⟩ := exists_lt_of_lt_csSup hne hx.2
      have hxN : x ∈ N := hNc.ordConnected.out hp hq ⟨hpx.le, hxq.le⟩
      exact hxN.2.le
    · by_contra hlt
      have hxN : x ∈ N := ⟨⟨ha1.trans (hs12.trans hx.1.le), hx.2.le⟩, lt_of_not_ge hlt⟩
      exact absurd (le_csSup hbdd' hxN) (not_le.mpr hx.1)
  · refine ⟨a, a, le_rfl, le_rfl, hab, fun x hx => absurd hx.2 (not_lt.mpr hx.1.le),
      fun x hx => absurd hx.2 (not_lt.mpr hx.1.le), fun x hx => ?_⟩
    by_contra hlt
    exact hne ⟨x, ⟨hx.1.le, hx.2.le⟩, lt_of_not_ge hlt⟩

/-- **Clamped beams are positivity preserving.**  If `E > 0` on `[a, b]`, the moment `M = E u''`
satisfies `M'' = q ≥ 0` on `[a, b]`, and `u(a) = u'(a) = u(b) = u'(b) = 0`, then `u ≥ 0` on
`[a, b]`. -/
theorem nonneg_of_clampedBeam {a b : ℝ} (hab : a ≤ b) {u u' g E M M' q : ℝ → ℝ}
    (hu : ∀ x, HasDerivAt u (u' x) x) (hu' : ∀ x, HasDerivAt u' (g x) x)
    (hE : ∀ x ∈ Icc a b, 0 < E x) (hM : ∀ x ∈ Icc a b, M x = E x * g x)
    (hdM : ∀ x, HasDerivAt M (M' x) x) (hdM' : ∀ x, HasDerivAt M' (q x) x)
    (hq : ∀ x ∈ Icc a b, 0 ≤ q x)
    (ha : u a = 0) (ha' : u' a = 0) (hb : u b = 0) (hb' : u' b = 0) :
    ∀ x ∈ Icc a b, 0 ≤ u x := by
  have cM : Continuous M := continuous_iff_continuousAt.mpr fun x => (hdM x).continuousAt
  have cM' : Continuous M' := continuous_iff_continuousAt.mpr fun x => (hdM' x).continuousAt
  have hconv : ConvexOn ℝ (Icc a b) M := by
    refine MonotoneOn.convexOn_of_deriv (convex_Icc a b) cM.continuousOn
      (fun x _ => (hdM x).differentiableAt.differentiableWithinAt) ?_
    have hmon : MonotoneOn M' (Icc a b) :=
      monotoneOn_of_deriv_nonneg (convex_Icc a b) cM'.continuousOn
        (fun x _ => (hdM' x).differentiableAt.differentiableWithinAt)
        (fun x hx => by
          rw [interior_Icc] at hx
          rw [(hdM' x).deriv]; exact hq x (Ioo_subset_Icc_self hx))
    intro x hx y hy hxy
    rw [interior_Icc] at hx hy
    rw [(hdM x).deriv, (hdM y).deriv]
    exact hmon (Ioo_subset_Icc_self hx) (Ioo_subset_Icc_self hy) hxy
  obtain ⟨s₁, s₂, h1, h2, h3, p1, n, p2⟩ := exists_signPattern_of_convexOn hab hconv
  have sign : ∀ x ∈ Icc a b, (0 ≤ M x ↔ 0 ≤ g x) := fun x hx => by
    rw [hM x hx]
    exact ⟨fun h => nonneg_of_mul_nonneg_right (by linarith [mul_comm (E x) (g x)])
      (hE x hx), fun h => mul_nonneg (hE x hx).le h⟩
  have sign' : ∀ x ∈ Icc a b, (M x ≤ 0 ↔ g x ≤ 0) := fun x hx => by
    rw [hM x hx]
    constructor
    · intro h
      by_contra hg
      exact absurd h (not_le.mpr (mul_pos (hE x hx) (lt_of_not_ge hg)))
    · intro h; exact mul_nonpos_of_nonneg_of_nonpos (hE x hx).le h
  refine nonneg_of_clamped_of_signPattern h1 h2 h3 hu hu' (fun x hx => ?_) (fun x hx => ?_)
    (fun x hx => ?_) ha ha' hb hb'
  · exact (sign x ⟨hx.1.le, hx.2.le.trans (h2.trans h3)⟩).mp (p1 x hx)
  · exact (sign' x ⟨h1.trans hx.1.le, hx.2.le.trans h3⟩).mp (n x hx)
  · exact (sign x ⟨h1.trans (h2.trans hx.1.le), hx.2.le⟩).mp (p2 x hx)

/-- **The clamped Green function of `𝔐²` is positivity preserving.**  In `s = log tan(α/2)` the
spherical Laplacian is `𝔐 = cosh² s · ∂_s²`.  If `𝔐κ = M` (i.e. `M = cosh² · κ''`) and
`𝔐M = cosh² · M'' = σ ≥ 0` on `[a, b]`, with `κ` clamped at both ends, then `κ ≥ 0`. -/
theorem nonneg_of_coshSq_clampedBeam {a b : ℝ} (hab : a ≤ b) {κ κ' g M M' q : ℝ → ℝ}
    (hκ : ∀ x, HasDerivAt κ (κ' x) x) (hκ' : ∀ x, HasDerivAt κ' (g x) x)
    (hM : ∀ x, M x = Real.cosh x ^ 2 * g x) (hdM : ∀ x, HasDerivAt M (M' x) x)
    (hdM' : ∀ x, HasDerivAt M' (q x) x) (hσ : ∀ x ∈ Icc a b, 0 ≤ Real.cosh x ^ 2 * q x)
    (ha : κ a = 0) (ha' : κ' a = 0) (hb : κ b = 0) (hb' : κ' b = 0) :
    ∀ x ∈ Icc a b, 0 ≤ κ x :=
  nonneg_of_clampedBeam hab hκ hκ' (fun x _ => by positivity) (fun x _ => hM x) hdM hdM'
    (fun x hx => (mul_nonneg_iff_of_pos_left (pow_pos (Real.cosh_pos x) 2)).mp (hσ x hx))
    ha ha' hb hb'

end GaloisForLFunctions.HTGeometry
