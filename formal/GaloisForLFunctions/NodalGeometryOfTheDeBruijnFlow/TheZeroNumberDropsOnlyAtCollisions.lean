import GaloisForLFunctions.RHTower.DeBruijnCollisionJumpLaw

/-!
# The zero number drops only at collisions

`u(x, t) = H_t(x)` solves `∂_t u = −∂_x² u`, so decreasing `t` is forward parabolic time. Let `Z(t)` be the
number of real zeros of `H_t` in a window `[a(t), b(t)]`, with multiplicity (`realZeroCount`), and `M(t)` the
collision mass of the window (`windowCollisionMass`): `Σ 2⌊m/2⌋` over its real zeros of order `m`.

* **Local law** (`exists_local_realZeroCount`). If `H_{s₀}` does not vanish at the two endpoints, then just
  after `s₀`, for all nearby endpoints, `Z = Z(s₀)`; just before `s₀`, `Z + M(s₀) = Z(s₀)`.
* **Sturm drop law** (`realZeroCount_eq_add_sum_windowCollisionMass`, `monotoneOn_realZeroCount`). If the
  boundary curves stay off the zeros of the flow on `[t₁, t₂] ⊂ (0, ∞)`, then
  `Z(t₂) = Z(t₁) + Σ_{t₁ < s ≤ t₂} M(s)`: the zero number falls only at collisions as `t` decreases, by exactly
  the order of each collision, rounded down to an even number.
* **Nodal structure** (`exists_real_zero_near_forward`, `no_real_zero_near_backward_of_even`). Every nodal
  point continues upward. A nodal point of even order is a local minimum of `t` on the nodal set: just
  below it no real zero remains nearby. There are no caps.

The boundary curves are essential: zeros cross fixed vertical lines, and the count on an unbuffered
window is not monotone.
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry RHTower RHTower.DeBruijn

namespace GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow

noncomputable section

/-- The real zeros of `H_s` in `[a, b]`. -/
def realZeroSet (s a b : ℝ) : Set ℝ := {x | x ∈ Icc a b ∧ riemannHeat s (x : ℂ) = 0}

theorem realZeroSet_finite {s : ℝ} (hs : 0 ≤ s) (a b : ℝ) : (realZeroSet s a b).Finite := by
  have han : AnalyticOnNhd ℂ (riemannHeat s) (closedBall 0 (|a| + |b| + 1)) := fun z _ =>
    (differentiable_riemannHeat hs).analyticAt z
  have hfin := finite_zeros_closedBall han (fun z _ h =>
    analyticOrderAt_riemannHeat_ne_top hs z (analyticOrderAt_eq_top.mpr h))
  refine Set.Finite.of_finite_image (f := fun x : ℝ => (x : ℂ)) (hfin.subset ?_)
    (fun x _ y _ h => Complex.ofReal_injective h)
  rintro _ ⟨x, ⟨hx, hx0⟩, rfl⟩
  refine ⟨?_, hx0⟩
  rw [mem_closedBall, dist_zero_right, Complex.norm_real, Real.norm_eq_abs]
  have h1 := le_abs_self b
  have h2 := neg_abs_le a
  have h3 := neg_le_abs a
  have h4 := abs_nonneg b
  have h5 := neg_abs_le b
  have h6 := abs_nonneg a
  rw [abs_le]
  constructor <;> linarith only [hx.1, hx.2, h1, h2, h3, h4, h5, h6]

/-- The finite set of real zeros of `H_s` in `[a, b]`, for `s ≥ 0`. -/
def realZeroFinset (s a b : ℝ) : Finset ℝ :=
  if hs : 0 ≤ s then (realZeroSet_finite hs a b).toFinset else ∅

theorem mem_realZeroFinset {s : ℝ} (hs : 0 ≤ s) {a b x : ℝ} :
    x ∈ realZeroFinset s a b ↔ x ∈ Icc a b ∧ riemannHeat s (x : ℂ) = 0 := by
  rw [realZeroFinset, dif_pos hs, Set.Finite.mem_toFinset]
  rfl

/-- The **zero number**: real zeros of `H_s` in `[a, b]` with multiplicity. -/
def realZeroCount (s a b : ℝ) : ℕ :=
  ∑ x ∈ realZeroFinset s a b, zeroMult (riemannHeat s) (x : ℂ)

/-- The **collision mass of the window**: `Σ 2⌊m/2⌋` over the real zeros of `H_s` in `[a, b]`. -/
def windowCollisionMass (s a b : ℝ) : ℕ :=
  ∑ x ∈ realZeroFinset s a b,
    (zeroMult (riemannHeat s) (x : ℂ) - zeroMult (riemannHeat s) (x : ℂ) % 2)

/-! ## The local law -/

/-- **The local law of the zero number.** -/
theorem exists_local_realZeroCount {s₀ a b : ℝ} (hs₀ : 0 < s₀) (hab : a < b)
    (ha : riemannHeat s₀ (a : ℂ) ≠ 0) (hb : riemannHeat s₀ (b : ℂ) ≠ 0) :
    ∃ δ > 0, ∀ a' b' s : ℝ, |a' - a| < δ → |b' - b| < δ → |s - s₀| < δ → 0 < s ∧
      (s₀ ≤ s → realZeroCount s a' b' = realZeroCount s₀ a b) ∧
      (s < s₀ → realZeroCount s a' b' + windowCollisionMass s₀ a b = realZeroCount s₀ a b) := by
  classical
  have hdiff₀ := differentiable_riemannHeat hs₀.le
  set E := realZeroFinset s₀ a b with hE
  have hmemE (x : ℝ) : x ∈ E ↔ x ∈ Icc a b ∧ riemannHeat s₀ (x : ℂ) = 0 := mem_realZeroFinset hs₀.le
  -- the zeros are interior
  have hint (x : ℝ) (hx : x ∈ E) : a < x ∧ x < b := by
    obtain ⟨hI, h0⟩ := (hmemE x).mp hx
    refine ⟨lt_of_le_of_ne hI.1 ?_, lt_of_le_of_ne hI.2 ?_⟩
    · rintro rfl; exact ha h0
    · rintro rfl; exact hb h0
  -- radii
  choose ρ₀ hρ₀ hρ₀prop using fun x : ℝ => eventually_zeroSumBall_riemannHeat_eq hs₀ (x : ℂ)
  choose ρ₁ hρ₁ hρ₁prop using fun x : ℝ => exists_ball_nonreal_count_backward hs₀ x
  choose ρ₂ hρ₂ hρ₂prop using fun x : ℝ => exists_ball_real_zeros_forward hs₀ x
  obtain ⟨d, hd, hdsep⟩ := exists_pos_sep (E.image fun x : ℝ => (x : ℂ))
  have hdsep' (x y : ℝ) (hx : x ∈ E) (hy : y ∈ E) (hxy : x ≠ y) : d ≤ dist (x : ℂ) (y : ℂ) :=
    hdsep _ (Finset.mem_image_of_mem _ hx) _ (Finset.mem_image_of_mem _ hy)
      (fun h => hxy (Complex.ofReal_injective h))
  set r : ℝ → ℝ := fun x => min (ρ₀ x) (min (ρ₁ x) (min (ρ₂ x) (min (d / 3)
    (min ((x - a) / 2) ((b - x) / 2))))) with hr
  have hrpos (x : ℝ) (hx : x ∈ E) : 0 < r x := by
    obtain ⟨h1, h2⟩ := hint x hx
    exact lt_min (hρ₀ x) (lt_min (hρ₁ x) (lt_min (hρ₂ x) (lt_min (by positivity)
      (lt_min (by linarith only [h1]) (by linarith only [h2])))))
  have hr0 (x : ℝ) : r x ≤ ρ₀ x := min_le_left _ _
  have hr1 (x : ℝ) : r x ≤ ρ₁ x := (min_le_right _ _).trans (min_le_left _ _)
  have hr2 (x : ℝ) : r x ≤ ρ₂ x := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrd (x : ℝ) : r x ≤ d / 3 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hra (x : ℝ) : r x ≤ (x - a) / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hrb (x : ℝ) : r x ≤ (b - x) / 2 := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  -- discs are disjoint, and their real slices are interior
  have hdisj (x y : ℝ) (hx : x ∈ E) (hy : y ∈ E) (hxy : x ≠ y) :
      Disjoint (ball (x : ℂ) (r x)) (ball (y : ℂ) (r y)) := by
    refine Set.disjoint_left.mpr fun w hw hw' => ?_
    have h1 := hdsep' x y hx hy hxy
    have h2 : dist (x : ℂ) (y : ℂ) ≤ dist (x : ℂ) w + dist w (y : ℂ) := dist_triangle _ _ _
    rw [mem_ball] at hw hw'
    rw [dist_comm] at hw
    linarith only [hrd x, hrd y, h1, h2, hw, hw', hd]
  have hslice (x y : ℝ) (hy : (y : ℂ) ∈ ball (x : ℂ) (r x)) :
      (x + a) / 2 < y ∧ y < (x + b) / 2 := by
    rw [mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs,
      abs_lt] at hy
    constructor <;> linarith only [hy.1, hy.2, hra x, hrb x]
  -- neighbourhoods of the endpoints
  have hcont_a : ContinuousAt (fun x : ℝ => riemannHeat s₀ (x : ℂ)) a :=
    (hdiff₀.continuous.comp Complex.continuous_ofReal).continuousAt
  have hcont_b : ContinuousAt (fun x : ℝ => riemannHeat s₀ (x : ℂ)) b :=
    (hdiff₀.continuous.comp Complex.continuous_ofReal).continuousAt
  obtain ⟨η₁, hη₁, hna⟩ := Metric.eventually_nhds_iff.mp (hcont_a.eventually_ne ha)
  obtain ⟨η₂, hη₂, hnb⟩ := Metric.eventually_nhds_iff.mp (hcont_b.eventually_ne hb)
  set η := min (η₁ / 2) (η₂ / 2) with hη
  have hηpos : 0 < η := lt_min (by positivity) (by positivity)
  -- the compact complement of the discs
  set K : Set ℂ := ((fun x : ℝ => (x : ℂ)) '' Icc (a - η) (b + η)) \
    ⋃ x ∈ E, ball (x : ℂ) (r x) with hK
  have hKc : IsCompact K := (isCompact_Icc.image Complex.continuous_ofReal).diff
    (isOpen_biUnion fun _ _ => isOpen_ball)
  have hKfree : ∀ z ∈ K, riemannHeat s₀ z ≠ 0 := by
    rintro _ ⟨⟨x, hx, rfl⟩, hnot⟩ h0
    by_cases hxI : x ∈ Icc a b
    · have hxE : x ∈ E := (hmemE x).mpr ⟨hxI, h0⟩
      exact hnot (mem_biUnion hxE (mem_ball_self (hrpos x hxE)))
    · rcases lt_or_ge x a with hxa | hxa
      · have hd' : dist x a < η₁ := by
          rw [Real.dist_eq, abs_of_neg (by linarith only [hxa])]
          linarith only [hx.1, min_le_left (η₁ / 2) (η₂ / 2), hη₁]
        exact hna hd' h0
      · have hxb : b < x := lt_of_not_ge fun h => hxI ⟨hxa, h⟩
        have hd' : dist x b < η₂ := by
          rw [Real.dist_eq, abs_of_pos (by linarith only [hxb])]
          linarith only [hx.2, min_le_right (η₁ / 2) (η₂ / 2), hη₂]
        exact hnb hd' h0
  obtain ⟨μ, hμ, hμmin⟩ := hKc.exists_forall_le' hdiff₀.continuous.norm.continuousOn
    (fun z hz => norm_pos_iff.mpr (hKfree z hz))
  have hunif := (Metric.tendstoUniformlyOn_iff.mp
    ((tendstoLocallyUniformly_iff_forall_isCompact.mp
      (tendstoLocallyUniformly_riemannHeat_nhds hs₀)) K hKc)) μ hμ
  obtain ⟨δK, hδK, hKnear⟩ := Metric.eventually_nhds_iff.mp hunif
  -- time scales of the discs
  have hδ0 (x : ℝ) (hx : x ∈ E) : ∃ δ > 0, ∀ s, |s - s₀| < δ →
      zeroSumBall (riemannHeat s) (x : ℂ) (r x) = (zeroMult (riemannHeat s₀) (x : ℂ) : ℂ) ∧
        ∀ w ∈ sphere (x : ℂ) (r x), riemannHeat s w ≠ 0 := by
    obtain ⟨-, -, hev⟩ := hρ₀prop x (r x) (hrpos x hx) (hr0 x)
    obtain ⟨δ, hδ, hprop⟩ := Metric.eventually_nhds_iff.mp hev
    exact ⟨δ, hδ, fun s hs => hprop (by rwa [Real.dist_eq])⟩
  have hδ1 (x : ℝ) (hx : x ∈ E) : ∃ δ > 0, ∀ s, s₀ - δ < s → s < s₀ →
      0 < s ∧ ∀ Z : Finset ℂ, (∀ z ∈ ball (x : ℂ) (r x), riemannHeat s z = 0 ↔ z ∈ Z) →
        (∀ z ∈ Z, z ∈ ball (x : ℂ) (r x)) →
        ∑ z ∈ Z.filter (fun z => z.im ≠ 0), zeroMult (riemannHeat s) z =
          zeroMult (riemannHeat s₀) (x : ℂ) - zeroMult (riemannHeat s₀) (x : ℂ) % 2 := by
    obtain ⟨δ, hδ, hprop⟩ := hρ₁prop x (r x) (hrpos x hx) (hr1 x)
    exact ⟨δ, hδ, fun s h1 h2 => ⟨(hprop s h1 h2).1, (hprop s h1 h2).2.2⟩⟩
  have hδ2 (x : ℝ) (hx : x ∈ E) : ∃ δ > 0, ∀ s, s₀ < s → s < s₀ + δ →
      ∀ w ∈ ball (x : ℂ) (r x), riemannHeat s w = 0 → w.im = 0 :=
    hρ₂prop x (r x) (hrpos x hx) (hr2 x)
  choose! δ0 hδ0pos hδ0p using hδ0
  choose! δ1 hδ1pos hδ1p using hδ1
  choose! δ2 hδ2pos hδ2p using hδ2
  obtain ⟨δ₀, hδ₀, hδ₀le⟩ := exists_pos_le_finset_of_pos E hδ0pos
  obtain ⟨δ₁, hδ₁, hδ₁le⟩ := exists_pos_le_finset_of_pos E hδ1pos
  obtain ⟨δ₂, hδ₂, hδ₂le⟩ := exists_pos_le_finset_of_pos E hδ2pos
  obtain ⟨δa, hδa, hδale⟩ := exists_pos_le_finset_of_pos E (g := fun x => (x - a) / 2)
    (fun x hx => by have := (hint x hx).1; linarith only [this])
  obtain ⟨δb, hδb, hδble⟩ := exists_pos_le_finset_of_pos E (g := fun x => (b - x) / 2)
    (fun x hx => by have := (hint x hx).2; linarith only [this])
  set δ := min s₀ (min δK (min δ₀ (min δ₁ (min δ₂ (min δa (min δb η)))))) with hδdef
  have hδpos : 0 < δ := lt_min hs₀ (lt_min hδK (lt_min hδ₀ (lt_min hδ₁ (lt_min hδ₂
    (lt_min hδa (lt_min hδb hηpos))))))
  have hδs₀ : δ ≤ s₀ := min_le_left _ _
  have hδKle : δ ≤ δK := (min_le_right _ _).trans (min_le_left _ _)
  have hδ₀l : δ ≤ δ₀ := (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ₁l : δ ≤ δ₁ := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans (min_le_left _ _)))
  have hδ₂l : δ ≤ δ₂ := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hδal : δ ≤ δa := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))))
  have hδbl : δ ≤ δb := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _))))))
  have hδη : δ ≤ η := (min_le_right _ _).trans ((min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _))))))
  refine ⟨δ, hδpos, fun a' b' s hya hyb hs => ?_⟩
  rw [abs_lt] at hya hyb
  have hspos : 0 < s := by
    have := (abs_lt.mp hs).1
    linarith only [this, hδs₀]
  have hdiffs := differentiable_riemannHeat hspos.le
  have hsabs := abs_lt.mp hs
  -- the zero sets of `H_s` in the discs
  have hZ (x : ℝ) (hx : x ∈ E) : ∃ Z : Finset ℂ, (∀ ρ ∈ Z, ρ ∈ ball (x : ℂ) (r x)) ∧
      (∀ z ∈ ball (x : ℂ) (r x), riemannHeat s z = 0 ↔ z ∈ Z) ∧
      ∑ ρ ∈ Z, zeroMult (riemannHeat s) ρ = zeroMult (riemannHeat s₀) (x : ℂ) := by
    obtain ⟨hcount, hsph⟩ := hδ0p x hx s (hs.trans_le (hδ₀l.trans (hδ₀le x hx)))
    obtain ⟨Z, h1, h2, h3⟩ := exists_zeroSet_zeroSumBall (hrpos x hx)
      (by linarith only [hrpos x hx] : r x < 2 * r x) isOpen_univ (subset_univ _)
      hdiffs.differentiableOn hsph
    refine ⟨Z, h1, h2, ?_⟩
    rw [hcount] at h3
    exact_mod_cast h3.symm
  choose! Z hZball hZzero hZsum using hZ
  -- every real zero in the window lies in a disc, and each disc lies in the window
  have hcover (y : ℝ) (hy : y ∈ Icc a' b') (h0 : riemannHeat s (y : ℂ) = 0) :
      ∃ x ∈ E, (y : ℂ) ∈ ball (x : ℂ) (r x) := by
    by_contra hn
    push Not at hn
    have hyK : (y : ℂ) ∈ K := by
      refine ⟨⟨y, ⟨?_, ?_⟩, rfl⟩, ?_⟩
      · linarith only [hy.1, hya.1, hδη]
      · linarith only [hy.2, hyb.2, hδη]
      · simp only [mem_iUnion, not_exists]
        exact fun x hx => hn x hx
    have hnear := hKnear (y := s) (by rw [Real.dist_eq]; exact hs.trans_le hδKle) (y : ℂ) hyK
    rw [dist_eq_norm, h0, sub_zero] at hnear
    exact absurd (hμmin _ hyK) (not_le.mpr hnear)
  have hinside (x y : ℝ) (hx : x ∈ E) (hy : (y : ℂ) ∈ ball (x : ℂ) (r x)) : y ∈ Icc a' b' := by
    obtain ⟨h1, h2⟩ := hslice x y hy
    have h3 := hδale x hx
    have h4 := hδble x hx
    constructor
    · linarith only [h1, h3, hya.2, hδal]
    · linarith only [h2, h4, hyb.1, hδbl]
  have hEmemS (y : ℝ) : y ∈ realZeroFinset s a' b' ↔ y ∈ Icc a' b' ∧ riemannHeat s (y : ℂ) = 0 :=
    mem_realZeroFinset hspos.le
  -- the count as a sum of real parts of the discs
  have hcount : realZeroCount s a' b' =
      ∑ x ∈ E, ∑ z ∈ (Z x).filter (fun z => z.im = 0), zeroMult (riemannHeat s) z := by
    have hpd : (E : Set ℝ).PairwiseDisjoint (fun x => (Z x).filter (fun z => z.im = 0)) := by
      intro x hx y hy hxy
      refine Finset.disjoint_left.mpr fun z hz hz' => ?_
      exact Set.disjoint_left.mp (hdisj x y hx hy hxy)
        (hZball x hx z (Finset.mem_filter.mp hz).1) (hZball y hy z (Finset.mem_filter.mp hz').1)
    rw [← Finset.sum_biUnion hpd, realZeroCount, ← Finset.sum_image (s := realZeroFinset s a' b')
      (g := fun y : ℝ => (y : ℂ)) (f := fun z => zeroMult (riemannHeat s) z)
      (fun x _ y _ h => Complex.ofReal_injective h)]
    refine Finset.sum_congr ?_ fun _ _ => rfl
    ext z
    simp only [Finset.mem_image, Finset.mem_biUnion, Finset.mem_filter]
    constructor
    · rintro ⟨y, hy, rfl⟩
      obtain ⟨hyI, hy0⟩ := (hEmemS y).mp hy
      obtain ⟨x, hx, hyx⟩ := hcover y hyI hy0
      exact ⟨x, hx, (hZzero x hx _ hyx).mp hy0, by simp⟩
    · rintro ⟨x, hx, hzZ, him⟩
      have hzb := hZball x hx z hzZ
      have hz : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
      have hzb' : ((z.re : ℝ) : ℂ) ∈ ball (x : ℂ) (r x) := by rwa [← hz]
      refine ⟨z.re, (hEmemS _).mpr ⟨hinside x _ hx hzb', ?_⟩, hz.symm⟩
      rw [← hz]
      exact (hZzero x hx z hzb).mpr hzZ
  refine ⟨hspos, fun hle => ?_, fun hlt => ?_⟩
  · -- at and after `s₀` all disc zeros are real
    rw [hcount, realZeroCount]
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [← hZsum x hx]
    refine Finset.sum_congr (Finset.filter_true_of_mem fun z hz => ?_) fun _ _ => rfl
    rcases hle.eq_or_lt with rfl | hlt
    · -- at `s₀`, the disc holds only its centre
      have hxzero : riemannHeat s₀ (x : ℂ) = 0 := ((hmemE x).mp hx).2
      have hxZ : (x : ℂ) ∈ Z x := (hZzero x hx _ (mem_ball_self (hrpos x hx))).mp hxzero
      by_contra him
      have hne : z ≠ (x : ℂ) := by
        rintro rfl
        exact him (Complex.ofReal_im x)
      have hsum := hZsum x hx
      have hsplit := Finset.add_sum_erase (Z x) (fun w => zeroMult (riemannHeat s₀) w) hxZ
      have h1 : 1 ≤ zeroMult (riemannHeat s₀) z :=
        one_le_zeroMult_riemannHeat hs₀.le ((hZzero x hx z (hZball x hx z hz)).mpr hz)
      have h2 := Finset.single_le_sum (f := fun w => zeroMult (riemannHeat s₀) w)
        (fun _ _ => Nat.zero_le _) (Finset.mem_erase.mpr ⟨hne, hz⟩)
      omega
    · exact hδ2p x hx s hlt (by linarith only [hsabs.2, hδ₂l, hδ₂le x hx]) z (hZball x hx z hz)
        ((hZzero x hx z (hZball x hx z hz)).mpr hz)
  · -- before `s₀` the disc keeps the parity of the order on the real axis
    rw [hcount, realZeroCount, windowCollisionMass, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun x hx => ?_
    have hback := (hδ1p x hx s (by linarith only [hsabs.1, hδ₁l, hδ₁le x hx]) hlt).2 (Z x)
      (hZzero x hx) (hZball x hx)
    have hsplit := Finset.sum_filter_add_sum_filter_not (Z x) (fun z => z.im = 0)
      (fun w => zeroMult (riemannHeat s) w)
    rw [hZsum x hx] at hsplit
    have hle : zeroMult (riemannHeat s₀) (x : ℂ) % 2 ≤ zeroMult (riemannHeat s₀) (x : ℂ) :=
      Nat.mod_le _ _
    simp only [ne_eq] at hback
    omega

/-! ## The drop law on a buffered window -/

/-- A nonzero window mass is a collision of the flow. -/
theorem collisionMass_ne_zero_of_windowCollisionMass_ne_zero {s a b : ℝ} (hs : 0 < s)
    (h : windowCollisionMass s a b ≠ 0) : collisionMass s ≠ 0 := by
  classical
  obtain ⟨x, hx, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  obtain ⟨-, h0⟩ := (mem_realZeroFinset hs.le).mp hx
  have hm2 : 2 ≤ zeroMult (riemannHeat s) (x : ℂ) := by omega
  have hd : deriv (riemannHeat s) (x : ℂ) = 0 := by
    by_contra hd
    have := zeroMult_riemannHeat_eq_one hs.le h0 hd
    omega
  have hs8 : s ≤ 1 / 8 := by
    by_contra hs8
    exact (riemannHeat_zeros_real_simple_of_eighth_le (not_le.mp hs8).le h0).2 hd
  have hmem : (x : ℂ) ∈ realMultipleZeros s :=
    (mem_realMultipleZeros hs hs8).mpr ⟨h0, Complex.ofReal_im x, hd⟩
  have hle := Finset.single_le_sum (f := fun z => zeroMult (riemannHeat s) z -
    zeroMult (riemannHeat s) z % 2) (fun _ _ => Nat.zero_le _) hmem
  rw [collisionMass]
  omega

/-- A window `[a(s), b(s)]`, `s ∈ [t₁, t₂]`, whose boundary curves stay off the zeros of the flow. -/
structure BufferedWindow (t₁ t₂ : ℝ) (a b : ℝ → ℝ) : Prop where
  pos : 0 < t₁
  le : t₁ ≤ t₂
  continuous_left : ContinuousOn a (Icc t₁ t₂)
  continuous_right : ContinuousOn b (Icc t₁ t₂)
  lt : ∀ s ∈ Icc t₁ t₂, a s < b s
  left_ne : ∀ s ∈ Icc t₁ t₂, riemannHeat s (a s : ℂ) ≠ 0
  right_ne : ∀ s ∈ Icc t₁ t₂, riemannHeat s (b s : ℂ) ≠ 0

namespace BufferedWindow

variable {t₁ t₂ : ℝ} {a b : ℝ → ℝ}

/-- A sub-interval of a buffered window is buffered. -/
theorem mono (hW : BufferedWindow t₁ t₂ a b) {u v : ℝ} (hu : t₁ ≤ u) (huv : u ≤ v) (hv : v ≤ t₂) :
    BufferedWindow u v a b where
  pos := hW.pos.trans_le hu
  le := huv
  continuous_left := hW.continuous_left.mono (Icc_subset_Icc hu hv)
  continuous_right := hW.continuous_right.mono (Icc_subset_Icc hu hv)
  lt := fun s hs => hW.lt s ⟨hu.trans hs.1, hs.2.trans hv⟩
  left_ne := fun s hs => hW.left_ne s ⟨hu.trans hs.1, hs.2.trans hv⟩
  right_ne := fun s hs => hW.right_ne s ⟨hu.trans hs.1, hs.2.trans hv⟩

/-- The local law along the boundary curves. -/
theorem exists_local (hW : BufferedWindow t₁ t₂ a b) {u : ℝ} (hu : u ∈ Icc t₁ t₂) :
    ∃ δ > 0, ∀ s ∈ Icc t₁ t₂, |s - u| < δ →
      (u ≤ s → realZeroCount s (a s) (b s) = realZeroCount u (a u) (b u)) ∧
      (s < u → realZeroCount s (a s) (b s) + windowCollisionMass u (a u) (b u) =
        realZeroCount u (a u) (b u)) := by
  obtain ⟨δ, hδ, hlaw⟩ := exists_local_realZeroCount (hW.pos.trans_le hu.1) (hW.lt u hu)
    (hW.left_ne u hu) (hW.right_ne u hu)
  have hca := hW.continuous_left u hu
  have hcb := hW.continuous_right u hu
  obtain ⟨δa, hδa, hna⟩ := Metric.continuousWithinAt_iff.mp hca δ hδ
  obtain ⟨δb, hδb, hnb⟩ := Metric.continuousWithinAt_iff.mp hcb δ hδ
  refine ⟨min δ (min δa δb), lt_min hδ (lt_min hδa hδb), fun s hs hsu => ?_⟩
  have h1 : |a s - a u| < δ := by
    have := hna hs (by rw [Real.dist_eq]; exact hsu.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
    rwa [Real.dist_eq] at this
  have h2 : |b s - b u| < δ := by
    have := hnb hs (by rw [Real.dist_eq]; exact hsu.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    rwa [Real.dist_eq] at this
  obtain ⟨-, hf, hb⟩ := hlaw (a s) (b s) s h1 h2 (hsu.trans_le (min_le_left _ _))
  exact ⟨hf, hb⟩

/-- The collision times of the window. -/
theorem finite_times (hW : BufferedWindow t₁ t₂ a b) :
    {s : ℝ | s ∈ Ioc t₁ t₂ ∧ windowCollisionMass s (a s) (b s) ≠ 0}.Finite :=
  (finite_collisionTimes hW.pos).subset fun _ hs => ⟨hs.1.1,
    collisionMass_ne_zero_of_windowCollisionMass_ne_zero (hW.pos.trans hs.1.1) hs.2⟩

/-- **The Sturm drop law.** On a buffered window, `Z(t₂) = Z(t₁) + Σ_{t₁ < s ≤ t₂} M(s)`. -/
theorem realZeroCount_eq_add_sum_windowCollisionMass (hW : BufferedWindow t₁ t₂ a b) :
    realZeroCount t₂ (a t₂) (b t₂) = realZeroCount t₁ (a t₁) (b t₁) +
      ∑ s ∈ hW.finite_times.toFinset, windowCollisionMass s (a s) (b s) := by
  classical
  set P := hW.finite_times.toFinset with hP
  have hmemP (s : ℝ) : s ∈ P ↔ s ∈ Ioc t₁ t₂ ∧ windowCollisionMass s (a s) (b s) ≠ 0 := by
    rw [hP, Set.Finite.mem_toFinset]
    rfl
  set Z : ℝ → ℕ := fun s => realZeroCount s (a s) (b s) with hZ
  set M : ℝ → ℕ := fun s => windowCollisionMass s (a s) (b s) with hM
  set F : ℝ → ℕ := fun u => Z u + ∑ p ∈ P.filter (u < ·), M p with hF
  have hFt₁ : F t₁ = Z t₁ + ∑ p ∈ P, M p := by
    simp only [hF]
    rw [Finset.filter_true_of_mem fun p hp => ((hmemP p).mp hp).1.1]
  have hFt₂ : F t₂ = Z t₂ := by
    simp only [hF]
    rw [Finset.filter_false_of_mem fun p hp => not_lt.mpr ((hmemP p).mp hp).1.2, Finset.sum_empty,
      add_zero]
  have hright : ∀ u ∈ Ico t₁ t₂, ∃ δ > 0, ∀ s, u < s → s < u + δ → F s = F u := by
    intro u hu
    have huI : u ∈ Icc t₁ t₂ := ⟨hu.1, hu.2.le⟩
    obtain ⟨δ₁, hδ₁, hlaw⟩ := hW.exists_local huI
    obtain ⟨δ₂, hδ₂, hgap⟩ := exists_pos_le_finset_of_pos (P.filter (u < ·))
      (g := fun p => p - u) fun p hp => sub_pos.mpr (Finset.mem_filter.mp hp).2
    refine ⟨min (min δ₁ δ₂) (t₂ - u), lt_min (lt_min hδ₁ hδ₂) (sub_pos.mpr hu.2),
      fun s h1 h2 => ?_⟩
    have hm1 := (min_le_left (min δ₁ δ₂) (t₂ - u)).trans (min_le_left δ₁ δ₂)
    have hm2 := (min_le_left (min δ₁ δ₂) (t₂ - u)).trans (min_le_right δ₁ δ₂)
    have hm3 := min_le_right (min δ₁ δ₂) (t₂ - u)
    have hsI : s ∈ Icc t₁ t₂ := ⟨hu.1.trans h1.le, by linarith only [h2, hm3]⟩
    have hfil : P.filter (s < ·) = P.filter (u < ·) := by
      refine Finset.filter_congr fun p hp => ⟨fun h => h1.trans h, fun hup => ?_⟩
      have h3 := hgap p (Finset.mem_filter.mpr ⟨hp, hup⟩)
      linarith only [h2, h3, hm2]
    have hs := (hlaw s hsI (by rw [abs_of_pos (by linarith only [h1])]; linarith only [h2, hm1])).1 h1.le
    simp only [hF, hfil, hZ]
    rw [hs]
  have hleft : ∀ u ∈ Ioc t₁ t₂, ∃ δ > 0, ∀ s, u - δ < s → s < u → F s = F u := by
    intro u hu
    have huI : u ∈ Icc t₁ t₂ := ⟨hu.1.le, hu.2⟩
    obtain ⟨δ₁, hδ₁, hlaw⟩ := hW.exists_local huI
    obtain ⟨δ₂, hδ₂, hgap⟩ := exists_pos_le_finset_of_pos (P.filter (· < u))
      (g := fun p => u - p) fun p hp => sub_pos.mpr (Finset.mem_filter.mp hp).2
    refine ⟨min (min δ₁ δ₂) (u - t₁), lt_min (lt_min hδ₁ hδ₂) (sub_pos.mpr hu.1), fun s h1 h2 => ?_⟩
    have hm1 := (min_le_left (min δ₁ δ₂) (u - t₁)).trans (min_le_left δ₁ δ₂)
    have hm2 := (min_le_left (min δ₁ δ₂) (u - t₁)).trans (min_le_right δ₁ δ₂)
    have hm3 := min_le_right (min δ₁ δ₂) (u - t₁)
    have hsI : s ∈ Icc t₁ t₂ := ⟨by linarith only [h1, hm3], h2.le.trans hu.2⟩
    have hs := (hlaw s hsI (by rw [abs_sub_comm, abs_of_pos (by linarith only [h2])]; linarith only [h1, hm1])).2 h2
    have hsplit : ∑ p ∈ P.filter (s < ·), M p = ∑ p ∈ P.filter (u < ·), M p + M u := by
      rw [← Finset.sum_filter_add_sum_filter_not (P.filter (s < ·)) (u < ·),
        Finset.filter_filter, Finset.filter_filter]
      congr 1
      · exact Finset.sum_congr (Finset.filter_congr fun p _ =>
          ⟨fun h => h.2, fun h => ⟨h2.trans h, h⟩⟩) fun _ _ => rfl
      · refine Finset.sum_eq_single u (fun q hq hqu => ?_) (fun hu' => ?_)
        · exfalso
          obtain ⟨hqP, hsq, huq⟩ := Finset.mem_filter.mp hq
          have hqlt : q < u := lt_of_le_of_ne (not_lt.mp huq) hqu
          have h3 := hgap q (Finset.mem_filter.mpr ⟨hqP, hqlt⟩)
          linarith only [h1, hsq, h3, hm2]
        · by_contra hJ
          exact hu' (Finset.mem_filter.mpr ⟨(hmemP u).mpr ⟨hu, hJ⟩, h2, lt_irrefl u⟩)
    simp only [hF, hZ]
    rw [hsplit]
    simp only [hM] at hs ⊢
    omega
  have h := eq_of_locally_const_Icc hW.le hright hleft
  rw [hFt₁, hFt₂] at h
  exact h

/-- **Monotonicity of the zero number.** On a buffered window `Z` is nondecreasing in `t`. -/
theorem monotoneOn_realZeroCount (hW : BufferedWindow t₁ t₂ a b) :
    MonotoneOn (fun s => realZeroCount s (a s) (b s)) (Icc t₁ t₂) := by
  intro u hu v hv huv
  have h := (hW.mono hu.1 huv hv.2).realZeroCount_eq_add_sum_windowCollisionMass
  simp only
  omega

/-- Without collisions in the window the zero number is constant. -/
theorem realZeroCount_eq_of_no_collision (hW : BufferedWindow t₁ t₂ a b)
    (hno : ∀ s ∈ Ioc t₁ t₂, windowCollisionMass s (a s) (b s) = 0) :
    realZeroCount t₂ (a t₂) (b t₂) = realZeroCount t₁ (a t₁) (b t₁) := by
  rw [hW.realZeroCount_eq_add_sum_windowCollisionMass]
  rw [Finset.sum_eq_zero fun s hs => hno s ((Set.Finite.mem_toFinset _).mp hs).1, add_zero]

end BufferedWindow

/-! ## The nodal set near one of its points -/

/-- **The local zero number at a nodal point.** Around a real zero of order `m` of `H_{s₀}`, small windows
hold `m` real zeros at and just above `s₀`, and `m mod 2` just below it. -/
theorem exists_local_realZeroCount_at_point {s₀ : ℝ} (hs₀ : 0 < s₀) (x₀ : ℝ)
    (h0 : riemannHeat s₀ (x₀ : ℂ) = 0) :
    ∃ ε₀ > 0, ∀ ε, 0 < ε → ε ≤ ε₀ → ∃ δ > 0, ∀ s, |s - s₀| < δ → 0 < s ∧
      (s₀ ≤ s → realZeroCount s (x₀ - ε) (x₀ + ε) = zeroMult (riemannHeat s₀) (x₀ : ℂ)) ∧
      (s < s₀ → realZeroCount s (x₀ - ε) (x₀ + ε) = zeroMult (riemannHeat s₀) (x₀ : ℂ) % 2) := by
  classical
  obtain ⟨ρ, hρ, hiso⟩ := exists_ball_riemannHeat_ne_zero hs₀.le (x₀ : ℂ)
  refine ⟨ρ / 2, by positivity, fun ε hε hερ => ?_⟩
  have hne (y : ℝ) (hy : |y - x₀| ≤ ε) (hyx : y ≠ x₀) : riemannHeat s₀ (y : ℂ) ≠ 0 := by
    refine hiso (y : ℂ) ?_ (fun h => hyx (Complex.ofReal_injective h))
    rw [mem_ball, Complex.dist_eq, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
    linarith only [hy, hερ, hρ]
  have hfin : realZeroFinset s₀ (x₀ - ε) (x₀ + ε) = {x₀} := by
    ext y
    rw [mem_realZeroFinset hs₀.le, Finset.mem_singleton]
    constructor
    · rintro ⟨hI, hy⟩
      by_contra hyx
      exact hne y (abs_le.mpr ⟨by linarith only [hI.1], by linarith only [hI.2]⟩) hyx hy
    · rintro rfl
      exact ⟨⟨by linarith only [hε], by linarith only [hε]⟩, h0⟩
  have hc : realZeroCount s₀ (x₀ - ε) (x₀ + ε) = zeroMult (riemannHeat s₀) (x₀ : ℂ) := by
    rw [realZeroCount, hfin, Finset.sum_singleton]
  have hM : windowCollisionMass s₀ (x₀ - ε) (x₀ + ε) =
      zeroMult (riemannHeat s₀) (x₀ : ℂ) - zeroMult (riemannHeat s₀) (x₀ : ℂ) % 2 := by
    rw [windowCollisionMass, hfin, Finset.sum_singleton]
  obtain ⟨δ, hδ, hlaw⟩ := exists_local_realZeroCount hs₀ (by linarith only [hε] : x₀ - ε < x₀ + ε)
    (hne (x₀ - ε) (by rw [show x₀ - ε - x₀ = -ε by ring, abs_neg, abs_of_pos hε])
      (by linarith only [hε] : x₀ - ε < x₀).ne)
    (hne (x₀ + ε) (by rw [show x₀ + ε - x₀ = ε by ring, abs_of_pos hε])
      (by linarith only [hε] : x₀ < x₀ + ε).ne')
  refine ⟨δ, hδ, fun s hs => ?_⟩
  obtain ⟨hpos, hf, hb⟩ := hlaw (x₀ - ε) (x₀ + ε) s (by simpa using hδ) (by simpa using hδ) hs
  refine ⟨hpos, fun h => (hf h).trans hc, fun h => ?_⟩
  have := hb h
  have hle : zeroMult (riemannHeat s₀) (x₀ : ℂ) % 2 ≤ zeroMult (riemannHeat s₀) (x₀ : ℂ) :=
    Nat.mod_le _ _
  omega

/-- A positive zero number gives a real zero in the window. -/
theorem exists_real_zero_of_realZeroCount_pos {s a b : ℝ} (h : 0 < realZeroCount s a b) :
    ∃ y, y ∈ Icc a b ∧ riemannHeat s (y : ℂ) = 0 ∧ 0 ≤ s := by
  classical
  by_cases hs : 0 ≤ s
  · obtain ⟨y, hy, -⟩ := Finset.exists_ne_zero_of_sum_ne_zero h.ne'
    obtain ⟨hI, h0⟩ := (mem_realZeroFinset hs).mp hy
    exact ⟨y, hI, h0, hs⟩
  · rw [realZeroCount, realZeroFinset, dif_neg hs] at h
    simp at h

/-- A vanishing zero number leaves no real zero in the window. -/
theorem riemannHeat_ne_zero_of_realZeroCount_eq_zero {s a b y : ℝ} (hs : 0 ≤ s)
    (h : realZeroCount s a b = 0) (hy : y ∈ Icc a b) : riemannHeat s (y : ℂ) ≠ 0 := by
  intro h0
  have hmem : y ∈ realZeroFinset s a b := (mem_realZeroFinset hs).mpr ⟨hy, h0⟩
  have hle := Finset.single_le_sum (f := fun x : ℝ => zeroMult (riemannHeat s) (x : ℂ))
    (fun _ _ => Nat.zero_le _) hmem
  have := one_le_zeroMult_riemannHeat hs h0
  rw [realZeroCount] at h
  omega

/-- **Every nodal point continues upward**: nearby real zeros exist just above it. -/
theorem exists_real_zero_near_forward {s₀ : ℝ} (hs₀ : 0 < s₀) (x₀ : ℝ)
    (h0 : riemannHeat s₀ (x₀ : ℂ) = 0) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ > 0, ∀ s, s₀ < s → s < s₀ + δ → ∃ y, |y - x₀| ≤ ε ∧ riemannHeat s (y : ℂ) = 0 := by
  obtain ⟨ε₀, hε₀, hlaw⟩ := exists_local_realZeroCount_at_point hs₀ x₀ h0
  obtain ⟨δ, hδ, hprop⟩ := hlaw (min ε ε₀) (lt_min hε hε₀) (min_le_right _ _)
  refine ⟨δ, hδ, fun s h1 h2 => ?_⟩
  have hs : |s - s₀| < δ := by rw [abs_of_pos (by linarith only [h1])]; linarith only [h2]
  have hcount := (hprop s hs).2.1 h1.le
  have hpos : 0 < realZeroCount s (x₀ - min ε ε₀) (x₀ + min ε ε₀) := by
    rw [hcount]
    exact one_le_zeroMult_riemannHeat hs₀.le h0
  obtain ⟨y, hy, hy0, -⟩ := exists_real_zero_of_realZeroCount_pos hpos
  refine ⟨y, abs_le.mpr ⟨?_, ?_⟩, hy0⟩
  · linarith only [hy.1, min_le_left ε ε₀]
  · linarith only [hy.2, min_le_left ε ε₀]

/-- **Even order is a turning point.** A nodal point of even order is a strict local minimum of `t` on the
nodal set: just below it no real zero remains nearby. The nodal set has no caps. -/
theorem no_real_zero_near_backward_of_even {s₀ : ℝ} (hs₀ : 0 < s₀) (x₀ : ℝ)
    (h0 : riemannHeat s₀ (x₀ : ℂ) = 0) (heven : Even (zeroMult (riemannHeat s₀) (x₀ : ℂ))) :
    ∃ ε > 0, ∃ δ > 0, ∀ s, s₀ - δ < s → s < s₀ → ∀ y, |y - x₀| ≤ ε → riemannHeat s (y : ℂ) ≠ 0 := by
  obtain ⟨ε₀, hε₀, hlaw⟩ := exists_local_realZeroCount_at_point hs₀ x₀ h0
  obtain ⟨δ, hδ, hprop⟩ := hlaw ε₀ hε₀ le_rfl
  refine ⟨ε₀, hε₀, δ, hδ, fun s h1 h2 y hy => ?_⟩
  have hs : |s - s₀| < δ := by rw [abs_sub_comm, abs_of_pos (by linarith only [h2])]; linarith only [h1]
  obtain ⟨hpos, -, hb⟩ := hprop s hs
  have hcount := hb h2
  rw [Nat.even_iff.mp heven] at hcount
  exact riemannHeat_ne_zero_of_realZeroCount_eq_zero hpos.le hcount
    ⟨by linarith only [(abs_le.mp hy).1], by linarith only [(abs_le.mp hy).2]⟩

/-- A nodal point of odd order continues downward along exactly one real zero. -/
theorem exists_real_zero_near_backward_of_odd {s₀ : ℝ} (hs₀ : 0 < s₀) (x₀ : ℝ)
    (h0 : riemannHeat s₀ (x₀ : ℂ) = 0) (hodd : Odd (zeroMult (riemannHeat s₀) (x₀ : ℂ))) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ δ > 0, ∀ s, s₀ - δ < s → s < s₀ → ∃ y, |y - x₀| ≤ ε ∧ riemannHeat s (y : ℂ) = 0 := by
  obtain ⟨ε₀, hε₀, hlaw⟩ := exists_local_realZeroCount_at_point hs₀ x₀ h0
  obtain ⟨δ, hδ, hprop⟩ := hlaw (min ε ε₀) (lt_min hε hε₀) (min_le_right _ _)
  refine ⟨δ, hδ, fun s h1 h2 => ?_⟩
  have hs : |s - s₀| < δ := by rw [abs_sub_comm, abs_of_pos (by linarith only [h2])]; linarith only [h1]
  have hcount := (hprop s hs).2.2 h2
  rw [Nat.odd_iff.mp hodd] at hcount
  obtain ⟨y, hy, hy0, -⟩ := exists_real_zero_of_realZeroCount_pos (by omega :
    0 < realZeroCount s (x₀ - min ε ε₀) (x₀ + min ε ε₀))
  refine ⟨y, abs_le.mpr ⟨?_, ?_⟩, hy0⟩
  · linarith only [hy.1, min_le_left ε ε₀]
  · linarith only [hy.2, min_le_left ε ε₀]

end

end GaloisForLFunctions.NodalGeometryOfTheDeBruijnFlow
