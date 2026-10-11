import GaloisForLFunctions.RHTower.XiCosineShiftExceptionalPointWindow
import GaloisForLFunctions.RHTower.DeBruijnNonrealCountAntitone

/-!
# The exceptional-point index of a shadow-free window

Fix shadow-free heights `T₁ < T₂`. For a depth `h`, let `D(h)` count with multiplicity the
non-real zeros of `A_h = cos(hD)Ξ` with real part in `[T₁, T₂]`. Let `M(h)` count with
multiplicity the multiple real zeros of `A_h` in `[T₁, T₂]`, i.e. the exceptional points at depth
`h`.

* `exists_local_windowDefectCount`: near any depth `h ≥ 0`, `D(h) ≤ D(h')`; for `h > 0` also
  `D(h') ≤ D(h) + M(h)`. Defects persist (Hurwitz). New defects can only be shed by multiple real
  zeros, because a simple real zero stays real (conjugation symmetry). The window's sides carry
  neither defects nor multiple zeros (shadow-freeness).
* `le_sum_of_local_jumps`: real induction. An `ℕ`-valued function that vanishes at `b`, is lower
  semicontinuous, and can rise by at most `M(t)` across `t` satisfies `D(a) ≤ Σ M`, the sum taken
  over the finitely many `t ∈ [a, b]` with `M(t) ≠ 0`.

**Theorem** (`windowDefectCount_zero_le_exceptional_mass`). Either infinitely many depths
`0 < h ≤ ½` carry an exceptional point in `[T₁, T₂]`, or their exceptional masses `M(h)` add up to
at least `D(0)`. Here `D(0)` is the number of non-real zeros of `Ξ` in the window, i.e. twice the
number of zeros of `ζ` right of the critical line with ordinate in `[T₁, T₂]`.

So the exceptional points of the PTR producer count the off-line zeros. With the transport law
(`twoPort_zeroCount_le`) and the shadow confinement, the off-line zeros, the producer's defects,
and its exceptional points carry the same information, window by window.
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

theorem cosProducer_zero (z : ℂ) : cosProducer 0 z = XiC z := by
  unfold cosProducer; simp

theorem cosProducer_neg_depth (h : ℝ) (z : ℂ) : cosProducer (-h) z = cosProducer h z := by
  unfold cosProducer
  rw [show z + ((-h : ℝ) : ℂ) * I = z - h * I by push_cast; ring,
    show z - ((-h : ℝ) : ℂ) * I = z + h * I by push_cast; ring, add_comm]

/-- Zeros of every `cos(hD)Ξ` lie in `|Im z| ≤ ½`. -/
theorem abs_im_le_half_of_cosProducer_eq_zero' {h : ℝ} {z : ℂ} (hz : cosProducer h z = 0) :
    |z.im| ≤ 1 / 2 := by
  rcases lt_trichotomy h 0 with hneg | rfl | hpos
  · rw [← cosProducer_neg_depth h] at hz
    exact abs_im_le_half_of_cosProducer_eq_zero (by linarith) hz
  · rw [cosProducer_zero] at hz
    exact (abs_im_lt_half_of_XiC_eq_zero hz).le
  · exact abs_im_le_half_of_cosProducer_eq_zero hpos hz

/-! ## Window counts -/

/-- The non-real zeros of `cos(hD)Ξ` with real part in `[T₁, T₂]`. -/
def windowDefectSet (T₁ T₂ h : ℝ) : Set ℂ :=
  {z | z.re ∈ Icc T₁ T₂ ∧ z.im ≠ 0 ∧ cosProducer h z = 0}

/-- The multiple real zeros of `cos(hD)Ξ` in `[T₁, T₂]`. -/
def windowEPSet (T₁ T₂ h : ℝ) : Set ℝ :=
  {x | x ∈ Icc T₁ T₂ ∧ cosProducer h x = 0 ∧ deriv (cosProducer h) x = 0}

theorem finite_zeros_cosProducer_closedBall (h : ℝ) (c : ℂ) (R : ℝ) :
    {z ∈ closedBall c R | cosProducer h z = 0}.Finite :=
  finite_zeros_closedBall (fun z _ => (differentiable_cosProducer h).analyticAt z)
    (fun z _ hz => analyticOrderAt_cosProducer_ne_top h z (analyticOrderAt_eq_top.mpr hz))

/-- The window box lies in the disc of radius `(T₂ − T₁)/2 + 1` about the window centre. -/
theorem dist_center_lt_of_window {T₁ T₂ : ℝ} {z : ℂ} (hz : z.re ∈ Icc T₁ T₂)
    (him : |z.im| ≤ 1 / 2) :
    dist z (((T₁ + T₂) / 2 : ℝ) : ℂ) < (T₂ - T₁) / 2 + 1 := by
  rw [dist_eq_norm]
  have h1 := Complex.norm_le_abs_re_add_abs_im (z - (((T₁ + T₂) / 2 : ℝ) : ℂ))
  have h2 : |(z - (((T₁ + T₂) / 2 : ℝ) : ℂ)).re| ≤ (T₂ - T₁) / 2 := by
    simp only [Complex.sub_re, Complex.ofReal_re]
    rw [abs_le]; constructor <;> linarith [hz.1, hz.2]
  have h3 : |(z - (((T₁ + T₂) / 2 : ℝ) : ℂ)).im| ≤ 1 / 2 := by simpa using him
  linarith

theorem windowDefectSet_finite (T₁ T₂ h : ℝ) : (windowDefectSet T₁ T₂ h).Finite := by
  refine (finite_zeros_cosProducer_closedBall h (((T₁ + T₂) / 2 : ℝ) : ℂ)
    ((T₂ - T₁) / 2 + 1)).subset ?_
  rintro z ⟨hz, -, h0⟩
  exact ⟨(dist_center_lt_of_window hz (abs_im_le_half_of_cosProducer_eq_zero' h0)).le, h0⟩

theorem windowEPSet_finite (T₁ T₂ h : ℝ) : (windowEPSet T₁ T₂ h).Finite := by
  have hfin := finite_zeros_cosProducer_closedBall h (((T₁ + T₂) / 2 : ℝ) : ℂ)
    ((T₂ - T₁) / 2 + 1)
  refine (hfin.preimage (fun a _ b _ hab => Complex.ofReal_inj.mp hab)).subset ?_
  rintro x ⟨hx, h0, -⟩
  refine ⟨(dist_center_lt_of_window (z := (x : ℂ)) (by simpa using hx) (by simp)).le, h0⟩

/-- The defect count `D(h)`. -/
def windowDefectCount (T₁ T₂ h : ℝ) : ℕ :=
  ∑ z ∈ (windowDefectSet_finite T₁ T₂ h).toFinset, zeroMult (cosProducer h) z

/-- The exceptional mass `M(h)`. -/
def windowEPMass (T₁ T₂ h : ℝ) : ℕ :=
  ∑ x ∈ (windowEPSet_finite T₁ T₂ h).toFinset, zeroMult (cosProducer h) (x : ℂ)

/-! ## Real induction with jumps -/

/-- **Real induction with jumps.** Let `D, M : ℝ → ℕ` with `D b = 0`, `D` lower semicontinuous on
`[a, b]`, and `D` rising by at most `M(t)` across each `t ∈ [a, b]`. If `F` contains every
`t ∈ [a, b]` with `M t ≠ 0`, then `D a ≤ Σ_{f ∈ F} M f`. -/
theorem le_sum_of_local_jumps {D M : ℝ → ℕ} {a b : ℝ} (hab : a ≤ b) (F : Finset ℝ)
    (hF : ∀ t ∈ Icc a b, M t ≠ 0 → t ∈ F) (hb : D b = 0)
    (hlsc : ∀ t ∈ Icc a b, ∃ δ > 0, ∀ s, |s - t| < δ → D t ≤ D s)
    (hjump : ∀ t ∈ Icc a b, ∃ δ > 0, ∀ s, |s - t| < δ → D s ≤ D t + M t) :
    D a ≤ ∑ f ∈ F, M f := by
  classical
  set J : ℝ → ℕ := fun t => ∑ f ∈ F.filter (fun f => t < f), M f with hJ
  have hJanti : ∀ s t, s ≤ t → J t ≤ J s := by
    intro s t hst
    refine Finset.sum_le_sum_of_subset fun f hf => ?_
    obtain ⟨hfF, hft⟩ := Finset.mem_filter.mp hf
    exact Finset.mem_filter.mpr ⟨hfF, lt_of_le_of_lt hst hft⟩
  have hJjump : ∀ s t, t ∈ Icc a b → s < t → J t + M t ≤ J s := by
    intro s t ht hst
    by_cases hM : M t = 0
    · rw [hM, add_zero]; exact hJanti s t hst.le
    · have htF := hF t ht hM
      have hsub : insert t (F.filter (fun f => t < f)) ⊆ F.filter (fun f => s < f) := by
        intro f hf
        rcases Finset.mem_insert.mp hf with rfl | hf
        · exact Finset.mem_filter.mpr ⟨htF, hst⟩
        · obtain ⟨hfF, hft⟩ := Finset.mem_filter.mp hf
          exact Finset.mem_filter.mpr ⟨hfF, hst.trans hft⟩
      have hnot : t ∉ F.filter (fun f => t < f) := by simp
      have := Finset.sum_le_sum_of_subset (f := M) hsub
      rw [Finset.sum_insert hnot] at this
      simp only [hJ]; omega
  set S := {t ∈ Icc a b | ∀ u ∈ Icc t b, D u ≤ J u} with hS
  have hbS : b ∈ S := ⟨⟨hab, le_rfl⟩, fun u hu => by
    rw [le_antisymm hu.2 hu.1, hb]; exact Nat.zero_le _⟩
  have hbdd : BddBelow S := ⟨a, fun t ht => ht.1.1⟩
  set c := sInf S with hc
  have hcb : c ≤ b := csInf_le hbdd hbS
  have hac : a ≤ c := le_csInf ⟨b, hbS⟩ fun t ht => ht.1.1
  have habove : ∀ u ∈ Ioc c b, D u ≤ J u := by
    intro u hu
    obtain ⟨t, htS, htu⟩ := exists_lt_of_csInf_lt ⟨b, hbS⟩ hu.1
    exact htS.2 u ⟨htu.le, hu.2⟩
  have hcQ : D c ≤ J c := by
    rcases lt_or_eq_of_le hcb with hlt | heq
    · obtain ⟨δ, hδ, hl⟩ := hlsc c ⟨hac, hcb⟩
      set s := min b (c + δ / 2)
      have hcs : c < s := lt_min hlt (by linarith)
      have hsδ : |s - c| < δ := by
        rw [abs_of_pos (by linarith)]
        have : s ≤ c + δ / 2 := min_le_right _ _
        linarith
      exact (hl s hsδ).trans ((habove s ⟨hcs, min_le_left _ _⟩).trans (hJanti c s hcs.le))
    · rw [heq]; exact hbS.2 b ⟨le_rfl, le_rfl⟩
  have hcS : c ∈ S := ⟨⟨hac, hcb⟩, fun u hu => by
    rcases eq_or_lt_of_le hu.1 with h | h
    · rw [← h]; exact hcQ
    · exact habove u ⟨h, hu.2⟩⟩
  rcases eq_or_lt_of_le hac with heq | hlt
  · rw [heq]
    exact hcQ.trans (Finset.sum_le_sum_of_subset (Finset.filter_subset _ _))
  · exfalso
    obtain ⟨δ, hδ, hj⟩ := hjump c ⟨hac, hcb⟩
    set t := max a (c - δ / 2)
    have htc : t < c := max_lt hlt (by linarith)
    have hleft : ∀ u ∈ Ico t c, D u ≤ J u := by
      intro u hu
      have huδ : |u - c| < δ := by
        rw [abs_sub_comm, abs_of_pos (by linarith [hu.2])]
        have : c - δ / 2 ≤ t := le_max_right _ _
        linarith [hu.1]
      exact (hj u huδ).trans ((Nat.add_le_add_right hcQ _).trans
        (hJjump u c ⟨hac, hcb⟩ hu.2))
    have htS : t ∈ S := ⟨⟨le_max_left _ _, htc.le.trans hcb⟩, fun u hu => by
      rcases lt_or_ge u c with h | h
      · exact hleft u ⟨hu.1, h⟩
      · exact hcS.2 u ⟨h, hu.2⟩⟩
    have := csInf_le hbdd htS
    linarith

/-! ## The local behaviour of the window counts -/

/-- Defects never sit at a shadow-free height, at any depth `h ≥ 0`. -/
theorem cosProducer_nonreal_re_ne_of_shadowFree' {T h : ℝ} (hh : 0 ≤ h)
    (hg : ∀ v, XiC v = 0 → v.im ^ 2 < (T - v.re) ^ 2) {z : ℂ} (hz : z.im ≠ 0)
    (h0 : cosProducer h z = 0) : z.re ≠ T := by
  rcases eq_or_lt_of_le hh with rfl | hpos
  · rw [cosProducer_zero] at h0
    intro hre
    have := hg z h0
    rw [hre, sub_self] at this
    nlinarith [sq_nonneg z.im]
  · exact cosProducer_nonreal_re_ne_of_shadowFree hpos hg hz h0

/-- Defects never sit at a shadow-free height, at any real depth. -/
theorem cosProducer_nonreal_re_ne_of_shadowFree_any {T h : ℝ}
    (hg : ∀ v, XiC v = 0 → v.im ^ 2 < (T - v.re) ^ 2) {z : ℂ} (hz : z.im ≠ 0)
    (h0 : cosProducer h z = 0) : z.re ≠ T := by
  rcases le_or_gt 0 h with hh | hh
  · exact cosProducer_nonreal_re_ne_of_shadowFree' hh hg hz h0
  · rw [← cosProducer_neg_depth h] at h0
    exact cosProducer_nonreal_re_ne_of_shadowFree' (by linarith) hg hz h0

/-- **Local behaviour of the window counts.** Near any depth `h ≥ 0`, `D(h) ≤ D(h')`; for `h > 0`
also `D(h') ≤ D(h) + M(h)`. -/
theorem exists_local_windowDefectCount {T₁ T₂ h : ℝ} (hT : T₁ < T₂) (hh : 0 ≤ h)
    (hg₁ : ∀ v, XiC v = 0 → v.im ^ 2 < (T₁ - v.re) ^ 2)
    (hg₂ : ∀ v, XiC v = 0 → v.im ^ 2 < (T₂ - v.re) ^ 2) :
    ∃ δ > 0, ∀ h', |h' - h| < δ →
      windowDefectCount T₁ T₂ h ≤ windowDefectCount T₁ T₂ h' ∧
      (0 < h → windowDefectCount T₁ T₂ h' ≤
        windowDefectCount T₁ T₂ h + windowEPMass T₁ T₂ h) := by
  classical
  set f := cosProducer h with hfdef
  have hfd : Differentiable ℂ f := differentiable_cosProducer h
  have hfin : ∀ z, analyticOrderAt f z ≠ ⊤ := analyticOrderAt_cosProducer_ne_top h
  have hconv := tendstoLocallyUniformly_cosProducer h
  set c₀ : ℂ := (((T₁ + T₂) / 2 : ℝ) : ℂ) with hc₀
  set X : ℝ := (T₂ - T₁) / 2 + 1 with hX
  have hXpos : 0 < X := by rw [hX]; linarith
  -- (1) a zero-free circle about the window centre
  have hfinB := finite_zeros_cosProducer_closedBall h c₀ (X + 1)
  obtain ⟨R, hRI, hRn⟩ := (Set.Ioo_infinite (by linarith : X < X + 1)).exists_notMem_finset
    (hfinB.toFinset.image (fun z => dist z c₀))
  have hRX : X < R := hRI.1
  have hR1 : R < X + 1 := hRI.2
  have hRpos : 0 < R := by linarith
  have hsphR : ∀ w ∈ sphere c₀ R, f w ≠ 0 := by
    intro w hw h0
    apply hRn
    refine Finset.mem_image.mpr ⟨w, ?_, mem_sphere.mp hw⟩
    rw [Set.Finite.mem_toFinset]
    exact ⟨by rw [mem_closedBall, mem_sphere.mp hw]; linarith, h0⟩
  -- (2) the zeros of `f` in the disc
  set E := hfinB.toFinset.filter (fun z => dist z c₀ < R) with hE
  have hmemE : ∀ z, z ∈ E ↔ f z = 0 ∧ dist z c₀ < R := by
    intro z
    rw [hE, Finset.mem_filter, Set.Finite.mem_toFinset]
    constructor
    · rintro ⟨⟨-, h0⟩, hz⟩; exact ⟨h0, hz⟩
    · rintro ⟨h0, hz⟩; exact ⟨⟨by rw [mem_closedBall]; linarith, h0⟩, hz⟩
  have hwinR : ∀ z, z.re ∈ Icc T₁ T₂ → |z.im| ≤ 1 / 2 → dist z c₀ < R := fun z hz him =>
    (dist_center_lt_of_window hz him).trans hRX
  -- (3) radii
  choose ρ₀ hρ₀ hiso using fun e => exists_radius_zeroSumBall_eq_zeroMult hfd hfin e
  obtain ⟨d, hd, hdsep⟩ := DeBruijn.exists_pos_sep E
  set B : ℂ → ℝ := fun e => if e.im = 0 then 1 else |e.im| / 2 with hBdef
  set C₁ : ℂ → ℝ := fun e => if e.re = T₁ then 1 else |e.re - T₁| / 2 with hC₁def
  set C₂ : ℂ → ℝ := fun e => if e.re = T₂ then 1 else |e.re - T₂| / 2 with hC₂def
  set r : ℂ → ℝ := fun e => min (min (ρ₀ e) (d / 3))
    (min ((R - dist e c₀) / 2) (min (B e) (min (C₁ e) (C₂ e)))) with hrdef
  have hBpos : ∀ e, 0 < B e := by
    intro e; simp only [hBdef]; split_ifs with h
    · exact one_pos
    · have := abs_pos.mpr h; linarith
  have hC₁pos : ∀ e, 0 < C₁ e := by
    intro e; simp only [hC₁def]; split_ifs with h
    · exact one_pos
    · have := abs_pos.mpr (sub_ne_zero.mpr h); linarith
  have hC₂pos : ∀ e, 0 < C₂ e := by
    intro e; simp only [hC₂def]; split_ifs with h
    · exact one_pos
    · have := abs_pos.mpr (sub_ne_zero.mpr h); linarith
  have hrpos : ∀ e ∈ E, 0 < r e := by
    intro e he
    have hR := ((hmemE e).mp he).2
    exact lt_min (lt_min (hρ₀ e) (by positivity))
      (lt_min (by linarith) (lt_min (hBpos e) (lt_min (hC₁pos e) (hC₂pos e))))
  have hr₀ : ∀ e, r e ≤ ρ₀ e := fun e => (min_le_left _ _).trans (min_le_left _ _)
  have hrd : ∀ e, r e ≤ d / 3 := fun e => (min_le_left _ _).trans (min_le_right _ _)
  have hrR : ∀ e, r e ≤ (R - dist e c₀) / 2 := fun e => (min_le_right _ _).trans (min_le_left _ _)
  have hrB : ∀ e, r e ≤ B e := fun e =>
    (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hrC₁ : ∀ e, r e ≤ C₁ e := fun e => (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have hrC₂ : ∀ e, r e ≤ C₂ e := fun e => (min_le_right _ _).trans
    ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _)))
  -- (4) geometry of the discs
  have hdisj : ∀ e ∈ E, ∀ e' ∈ E, e ≠ e' → Disjoint (ball e (r e)) (ball e' (r e')) := by
    intro e he e' he' hne
    refine Set.disjoint_left.mpr fun w hw hw' => ?_
    have h1 := hdsep e he e' he' hne
    have h2 : dist e e' ≤ dist e w + dist w e' := dist_triangle _ _ _
    rw [mem_ball] at hw hw'
    rw [dist_comm] at hw
    linarith [hrd e, hrd e']
  have hre_close : ∀ e, ∀ w ∈ ball e (r e), |w.re - e.re| < r e := by
    intro e w hw
    rw [mem_ball, dist_eq_norm] at hw
    have := Complex.abs_re_le_norm (w - e)
    rw [Complex.sub_re] at this; linarith
  have havoid : ∀ e, e.im ≠ 0 → ∀ w ∈ ball e (r e), w.im ≠ 0 := by
    intro e h w hw hw0
    have h1 : |(w - e).im| ≤ ‖w - e‖ := Complex.abs_im_le_norm _
    rw [Complex.sub_im, hw0, zero_sub, abs_neg] at h1
    rw [mem_ball, dist_eq_norm] at hw
    have hB : r e ≤ |e.im| / 2 := by
      have := hrB e; simp only [hBdef, if_neg h] at this; exact this
    have hpos := abs_pos.mpr h
    linarith
  have hside_lt : ∀ e, ∀ T : ℝ, e.re ≠ T → (r e ≤ |e.re - T| / 2) →
      ∀ w ∈ ball e (r e), (w.re < T ↔ e.re < T) := by
    intro e T hne hrT w hw
    have hc := hre_close e w hw
    have hpos := abs_pos.mpr (sub_ne_zero.mpr hne)
    constructor
    · intro hw'
      by_contra hge; push Not at hge
      have : e.re - T = |e.re - T| := (abs_of_nonneg (by linarith)).symm
      rw [abs_lt] at hc; linarith [hc.1]
    · intro he'
      have : |e.re - T| = T - e.re := by rw [abs_of_neg (by linarith)]; ring
      rw [abs_lt] at hc; linarith [hc.2]
  have hrT₁ : ∀ e, e.re ≠ T₁ → r e ≤ |e.re - T₁| / 2 := by
    intro e h; have := hrC₁ e; simp only [hC₁def, if_neg h] at this; exact this
  have hrT₂ : ∀ e, e.re ≠ T₂ → r e ≤ |e.re - T₂| / 2 := by
    intro e h; have := hrC₂ e; simp only [hC₂def, if_neg h] at this; exact this
  have hinR : ∀ e ∈ E, ∀ w ∈ ball e (r e), w ∈ ball c₀ R := by
    intro e he w hw
    have hR := ((hmemE e).mp he).2
    rw [mem_ball] at hw ⊢
    have := dist_triangle w e c₀
    linarith [hrR e]
  -- (5) counts near `h`
  have hbig : ∀ᶠ h' in 𝓝 h, zeroSumBall (cosProducer h') c₀ R = zeroSumBall f c₀ R ∧
      ∀ w ∈ sphere c₀ R, cosProducer h' w ≠ 0 :=
    (eventually_zeroSumBall_eq_of_tendstoLocallyUniformly (fun h' => differentiable_cosProducer h')
      hfd hconv hRpos (by linarith : R < 2 * R) hsphR).and
      (LeeYangCount.eventually_ne_zero_on_sphere hfd.continuous hconv hsphR)
  have hsmall : ∀ᶠ h' in 𝓝 h, ∀ e ∈ E,
      zeroSumBall (cosProducer h') e (r e) = (zeroMult f e : ℂ) ∧
        ∀ w ∈ sphere e (r e), cosProducer h' w ≠ 0 := by
    refine (Filter.eventually_all_finset E).mpr fun e he => ?_
    obtain ⟨hsph, hcount⟩ := hiso e (r e) (hrpos e he) (hr₀ e)
    filter_upwards [eventually_zeroSumBall_eq_of_tendstoLocallyUniformly
      (fun h' => differentiable_cosProducer h') hfd hconv (hrpos e he)
      (by linarith [hrpos e he] : r e < 2 * r e) hsph,
      LeeYangCount.eventually_ne_zero_on_sphere hfd.continuous hconv hsph] with h' h1 h2
    exact ⟨h1.trans hcount, h2⟩
  have hcountE : zeroSumBall f c₀ R = ∑ e ∈ E, (zeroMult f e : ℂ) := by
    obtain ⟨Z, hZb, hZz, hZs⟩ := exists_zeroSet_zeroSumBall hRpos (by linarith : R < 2 * R)
      isOpen_univ (subset_univ _) hfd.differentiableOn hsphR
    have hZE : Z = E := by
      ext z
      constructor
      · intro hz
        have hb := hZb z hz
        exact (hmemE z).mpr ⟨(hZz z hb).mpr hz, mem_ball.mp hb⟩
      · intro hz
        obtain ⟨h0, hR⟩ := (hmemE z).mp hz
        exact (hZz z (mem_ball.mpr hR)).mp h0
    rw [hZs, hZE]
  -- (6) the window sets at `h` inside `E`
  set Enw := E.filter (fun e => e.im ≠ 0 ∧ e.re ∈ Icc T₁ T₂) with hEnw
  set Eep := E.filter (fun e => e.im = 0 ∧ e.re ∈ Icc T₁ T₂ ∧ deriv f e = 0) with hEep
  have hD : windowDefectCount T₁ T₂ h = ∑ e ∈ Enw, zeroMult f e := by
    unfold windowDefectCount
    congr 1
    ext z
    rw [Set.Finite.mem_toFinset, hEnw, Finset.mem_filter, hmemE]
    simp only [windowDefectSet, Set.mem_setOf_eq]
    constructor
    · rintro ⟨hre, him, h0⟩
      exact ⟨⟨h0, hwinR z hre (abs_im_le_half_of_cosProducer_eq_zero' h0)⟩, him, hre⟩
    · rintro ⟨⟨h0, -⟩, him, hre⟩; exact ⟨hre, him, h0⟩
  have hM : windowEPMass T₁ T₂ h = ∑ e ∈ Eep, zeroMult f e := by
    unfold windowEPMass
    have himg : (windowEPSet_finite T₁ T₂ h).toFinset.image (fun x : ℝ => (x : ℂ)) = Eep := by
      ext z
      rw [Finset.mem_image, hEep, Finset.mem_filter, hmemE]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [Set.Finite.mem_toFinset] at hx
        obtain ⟨hxI, hx0, hxd⟩ := hx
        exact ⟨⟨hx0, hwinR _ (by simpa using hxI) (by simp)⟩, by simp, by simpa using hxI, hxd⟩
      · rintro ⟨⟨h0, -⟩, him, hre, hdz⟩
        have hz : z = ((z.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [him])
        refine ⟨z.re, ?_, hz.symm⟩
        rw [Set.Finite.mem_toFinset]
        refine ⟨hre, ?_, ?_⟩
        · rw [← hz]; exact h0
        · rw [← hz]; exact hdz
    rw [← himg, Finset.sum_image (fun a _ b _ hab => Complex.ofReal_inj.mp hab)]
  -- (7) the local estimates
  obtain ⟨δ, hδ, hδev⟩ := Metric.eventually_nhds_iff.mp (hbig.and hsmall)
  refine ⟨δ, hδ, fun h' hh' => ?_⟩
  obtain ⟨⟨hbs, hbsph⟩, hsm⟩ := hδev (by rw [Real.dist_eq]; exact hh')
  have hdiff' := differentiable_cosProducer h'
  have hZe : ∀ e ∈ E, ∃ Z : Finset ℂ, (∀ ρ ∈ Z, ρ ∈ ball e (r e)) ∧
      (∀ z ∈ ball e (r e), cosProducer h' z = 0 ↔ z ∈ Z) ∧
      zeroSumBall (cosProducer h') e (r e) = ∑ ρ ∈ Z, (zeroMult (cosProducer h') ρ : ℂ) :=
    fun e he => exists_zeroSet_zeroSumBall (hrpos e he) (by linarith [hrpos e he] : r e < 2 * r e)
      isOpen_univ (subset_univ _) hdiff'.differentiableOn (hsm e he).2
  choose! W hWb hWz hWs using hZe
  have hWmass : ∀ e ∈ E, ∑ z ∈ W e, zeroMult (cosProducer h') z = zeroMult f e := by
    intro e he
    have h1 := hWs e he
    rw [(hsm e he).1] at h1
    exact_mod_cast h1.symm
  have hWdisj : (E : Set ℂ).PairwiseDisjoint W := by
    intro e he e' he' hne
    refine Finset.disjoint_left.mpr fun z hz hz' => ?_
    exact (Set.disjoint_left.mp (hdisj e he e' he' hne)) (hWb e he z hz) (hWb e' he' z hz')
  set D' := (windowDefectSet_finite T₁ T₂ h').toFinset with hD'
  have hD'eq : windowDefectCount T₁ T₂ h' = ∑ z ∈ D', zeroMult (cosProducer h') z := rfl
  have hnw_side : ∀ e ∈ Enw, e.re ∈ Ioo T₁ T₂ := by
    intro e he
    obtain ⟨heE, him, hre⟩ := Finset.mem_filter.mp he
    have h0 := ((hmemE e).mp heE).1
    exact ⟨lt_of_le_of_ne hre.1 (cosProducer_nonreal_re_ne_of_shadowFree' hh hg₁ him h0).symm,
      lt_of_le_of_ne hre.2 (cosProducer_nonreal_re_ne_of_shadowFree' hh hg₂ him h0)⟩
  constructor
  · -- lower semicontinuity: defects persist
    have hsub : ∀ e ∈ Enw, W e ⊆ D' := by
      intro e he z hz
      obtain ⟨heE, him, -⟩ := Finset.mem_filter.mp he
      have hb := hWb e heE z hz
      have hIoo := hnw_side e he
      rw [hD', Set.Finite.mem_toFinset]
      refine ⟨⟨?_, ?_⟩, havoid e him z hb, (hWz e heE z hb).mpr hz⟩
      · have := (hside_lt e T₁ (ne_of_gt hIoo.1) (hrT₁ e (ne_of_gt hIoo.1)) z hb).not
        push Not at this; exact this.mpr hIoo.1.le
      · have h2 := (hside_lt e T₂ (ne_of_lt hIoo.2) (hrT₂ e (ne_of_lt hIoo.2)) z hb).mpr hIoo.2
        exact h2.le
    have hdisjnw : (Enw : Set ℂ).PairwiseDisjoint W :=
      hWdisj.subset (by intro e he; exact (Finset.mem_filter.mp he).1)
    rw [hD, hD'eq]
    calc ∑ e ∈ Enw, zeroMult f e = ∑ e ∈ Enw, ∑ z ∈ W e, zeroMult (cosProducer h') z :=
          Finset.sum_congr rfl fun e he => (hWmass e (Finset.mem_filter.mp he).1).symm
      _ = ∑ z ∈ Enw.biUnion W, zeroMult (cosProducer h') z := (Finset.sum_biUnion hdisjnw).symm
      _ ≤ ∑ z ∈ D', zeroMult (cosProducer h') z :=
          Finset.sum_le_sum_of_subset (Finset.biUnion_subset.mpr hsub)
  · -- the jump bound
    intro hpos
    -- every zero of `A_{h'}` in the disc lies in one of the small discs
    obtain ⟨Zb, hZbb, hZbz, hZbs⟩ := exists_zeroSet_zeroSumBall hRpos (by linarith : R < 2 * R)
      isOpen_univ (subset_univ _) hdiff'.differentiableOn hbsph
    have hWsub : ∀ e ∈ E, W e ⊆ Zb := by
      intro e he z hz
      have hb := hWb e he z hz
      exact (hZbz z (hinR e he z hb)).mp ((hWz e he z hb).mpr hz)
    have hsumN : ∑ z ∈ Zb, zeroMult (cosProducer h') z =
        ∑ e ∈ E, ∑ z ∈ W e, zeroMult (cosProducer h') z := by
      have h1 : ((∑ z ∈ Zb, zeroMult (cosProducer h') z : ℕ) : ℂ) =
          ((∑ e ∈ E, ∑ z ∈ W e, zeroMult (cosProducer h') z : ℕ) : ℂ) := by
        push_cast
        rw [← hZbs, hbs, hcountE]
        refine Finset.sum_congr rfl fun e he => ?_
        rw [← hWs e he, (hsm e he).1]
      exact_mod_cast h1
    have hcov := DeBruijn.subset_biUnion_of_sum_eq (fun z hz =>
      one_le_zeroMult_of_eq_zero hdiff' (analyticOrderAt_cosProducer_ne_top h')
        ((hZbz z (hZbb z hz)).mpr hz)) hWsub hWdisj hsumN
    -- the relevant discs
    have hrel : D' ⊆ (Enw ∪ Eep).biUnion W := by
      intro w hw
      rw [hD', Set.Finite.mem_toFinset] at hw
      obtain ⟨hwre, hwim, hw0⟩ := hw
      have hwb : w ∈ ball c₀ R := mem_ball.mpr (hwinR w hwre
        (abs_im_le_half_of_cosProducer_eq_zero' hw0))
      obtain ⟨e, he, hwe⟩ := Finset.mem_biUnion.mp (hcov ((hZbz w hwb).mp hw0))
      have hweb := hWb e he w hwe
      have h0e := ((hmemE e).mp he).1
      refine Finset.mem_biUnion.mpr ⟨e, ?_, hwe⟩
      -- `e` lies in the window
      have hereI : e.re ∈ Icc T₁ T₂ := by
        constructor
        · by_contra hlt; push Not at hlt
          have := (hside_lt e T₁ (ne_of_lt hlt) (hrT₁ e (ne_of_lt hlt)) w hweb).mpr hlt
          linarith [hwre.1]
        · by_contra hlt; push Not at hlt
          have h1 := hside_lt e T₂ (ne_of_gt hlt) (hrT₂ e (ne_of_gt hlt)) w hweb
          have h2 : ¬ w.re < T₂ := fun h => absurd (h1.mp h) (not_lt.mpr hlt.le)
          push Not at h2
          rcases eq_or_lt_of_le h2 with h3 | h3
          · exact cosProducer_nonreal_re_ne_of_shadowFree_any hg₂ hwim hw0 h3.symm
          · linarith [hwre.2]
      by_cases heim : e.im = 0
      · -- a real centre must be a multiple zero
        refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨he, heim, hereI, ?_⟩)
        by_contra hdne
        have he' : e = ((e.re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [heim])
        have hm1 : zeroMult f e = 1 := by
          rw [he'] at h0e hdne ⊢
          exact zeroMult_eq_one_of_deriv_ne_zero hfd h0e hdne
        have hwc0 : cosProducer h' ((starRingEnd ℂ) w) = 0 := by
          rw [cosProducer_conj, hw0, map_zero]
        have hwcb : (starRingEnd ℂ) w ∈ ball e (r e) := by
          rw [mem_ball, dist_eq_norm] at hweb ⊢
          have hce : (starRingEnd ℂ) e = e := by rw [he', Complex.conj_ofReal]
          have : (starRingEnd ℂ) w - e = (starRingEnd ℂ) (w - e) := by rw [map_sub, hce]
          rw [this, Complex.norm_conj]; exact hweb
        have hwcW : (starRingEnd ℂ) w ∈ W e := (hWz e he _ hwcb).mp hwc0
        have hne : w ≠ (starRingEnd ℂ) w := by
          intro heq; have := congrArg Complex.im heq; rw [Complex.conj_im] at this
          exact hwim (by linarith)
        have hpair : ({w, (starRingEnd ℂ) w} : Finset ℂ) ⊆ W e := by
          intro y hy
          rcases Finset.mem_insert.mp hy with rfl | hy
          · exact hwe
          · rw [Finset.mem_singleton.mp hy]; exact hwcW
        have hge : 2 ≤ ∑ z ∈ W e, zeroMult (cosProducer h') z := by
          calc 2 = ∑ z ∈ ({w, (starRingEnd ℂ) w} : Finset ℂ), 1 := by
                rw [Finset.sum_const, Finset.card_pair hne]; rfl
            _ ≤ ∑ z ∈ ({w, (starRingEnd ℂ) w} : Finset ℂ), zeroMult (cosProducer h') z := by
                refine Finset.sum_le_sum fun z hz => ?_
                refine one_le_zeroMult_of_eq_zero hdiff' (analyticOrderAt_cosProducer_ne_top h') ?_
                rcases Finset.mem_insert.mp hz with rfl | hz
                · exact hw0
                · rw [Finset.mem_singleton.mp hz]; exact hwc0
            _ ≤ ∑ z ∈ W e, zeroMult (cosProducer h') z :=
                Finset.sum_le_sum_of_subset_of_nonneg hpair fun _ _ _ => Nat.zero_le _
        rw [hWmass e he, hm1] at hge
        omega
      · exact Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨he, heim, hereI⟩)
    have hdisjU : Disjoint Enw Eep := by
      rw [Finset.disjoint_left]
      intro e h1 h2
      exact (Finset.mem_filter.mp h1).2.1 (Finset.mem_filter.mp h2).2.1
    have hdisjrel : ((Enw ∪ Eep : Finset ℂ) : Set ℂ).PairwiseDisjoint W :=
      hWdisj.subset (by
        intro e he
        rcases Finset.mem_union.mp he with h | h
        · exact (Finset.mem_filter.mp h).1
        · exact (Finset.mem_filter.mp h).1)
    rw [hD'eq, hD, hM]
    calc ∑ z ∈ D', zeroMult (cosProducer h') z
        ≤ ∑ z ∈ (Enw ∪ Eep).biUnion W, zeroMult (cosProducer h') z :=
          Finset.sum_le_sum_of_subset hrel
      _ = ∑ e ∈ Enw ∪ Eep, ∑ z ∈ W e, zeroMult (cosProducer h') z :=
          Finset.sum_biUnion hdisjrel
      _ = ∑ e ∈ Enw ∪ Eep, zeroMult f e := by
          refine Finset.sum_congr rfl fun e he => hWmass e ?_
          rcases Finset.mem_union.mp he with h | h
          · exact (Finset.mem_filter.mp h).1
          · exact (Finset.mem_filter.mp h).1
      _ = ∑ e ∈ Enw, zeroMult f e + ∑ e ∈ Eep, zeroMult f e := Finset.sum_union hdisjU

/-! ## The index law -/

/-- At depth `½` there are no defects. -/
theorem windowDefectCount_half (T₁ T₂ : ℝ) : windowDefectCount T₁ T₂ (1 / 2) = 0 := by
  unfold windowDefectCount
  refine Finset.sum_eq_zero fun z hz => ?_
  rw [Set.Finite.mem_toFinset] at hz
  obtain ⟨-, hzim, h0⟩ := hz
  exfalso
  obtain ⟨w, hw, hdisk⟩ := DeBruijn.cosineShift_nonreal_zero_mem_defectDisk
    (by norm_num : (0 : ℝ) < 1 / 2) hzim h0
  have h1 := abs_im_lt_half_of_XiC_eq_zero hw
  have h2 : w.im ^ 2 < (1 / 2) ^ 2 := by
    have := sq_lt_sq' (by linarith [(abs_lt.mp h1).1]) (abs_lt.mp h1).2
    linarith
  have h3 : 0 < z.im ^ 2 := by positivity
  nlinarith [sq_nonneg (w.re - z.re)]

/-- **The exceptional-point index law.** In a window between shadow-free heights, either infinitely
many depths `0 < h ≤ ½` carry an exceptional point, or the exceptional masses of finitely many
such depths add up to at least the number of non-real zeros of `Ξ` in the window. -/
theorem windowDefectCount_zero_le_exceptional_mass {T₁ T₂ : ℝ} (hT : T₁ < T₂)
    (hg₁ : ∀ v, XiC v = 0 → v.im ^ 2 < (T₁ - v.re) ^ 2)
    (hg₂ : ∀ v, XiC v = 0 → v.im ^ 2 < (T₂ - v.re) ^ 2) :
    {h : ℝ | h ∈ Ioc 0 (1 / 2) ∧ windowEPMass T₁ T₂ h ≠ 0}.Infinite ∨
      ∃ F : Finset ℝ, (∀ h ∈ F, h ∈ Ioc 0 (1 / 2) ∧ windowEPMass T₁ T₂ h ≠ 0) ∧
        windowDefectCount T₁ T₂ 0 ≤ ∑ h ∈ F, windowEPMass T₁ T₂ h := by
  classical
  by_cases hinf : {h : ℝ | h ∈ Ioc 0 (1 / 2) ∧ windowEPMass T₁ T₂ h ≠ 0}.Infinite
  · exact Or.inl hinf
  right
  have hfin : {h : ℝ | h ∈ Ioc 0 (1 / 2) ∧ windowEPMass T₁ T₂ h ≠ 0}.Finite :=
    Set.not_infinite.mp hinf
  set F := hfin.toFinset with hF
  refine ⟨F, fun h hh => by rw [hF, Set.Finite.mem_toFinset] at hh; exact hh, ?_⟩
  obtain ⟨δ₀, hδ₀, h0loc⟩ := exists_local_windowDefectCount (h := 0) hT le_rfl hg₁ hg₂
  set a : ℝ := min (δ₀ / 2) (1 / 4) with ha
  have hapos : 0 < a := lt_min (by linarith) (by norm_num)
  have hab : a ≤ 1 / 2 := (min_le_right _ _).trans (by norm_num)
  have h0a : windowDefectCount T₁ T₂ 0 ≤ windowDefectCount T₁ T₂ a :=
    (h0loc a (by rw [sub_zero, abs_of_pos hapos]; linarith [min_le_left (δ₀ / 2) (1 / 4)])).1
  refine h0a.trans (le_sum_of_local_jumps (M := windowEPMass T₁ T₂) hab F ?_
    (windowDefectCount_half T₁ T₂) ?_ ?_)
  · intro t ht hM
    rw [hF, Set.Finite.mem_toFinset]
    exact ⟨⟨lt_of_lt_of_le hapos ht.1, ht.2⟩, hM⟩
  · intro t ht
    obtain ⟨δ, hδ, hloc⟩ := exists_local_windowDefectCount hT (lt_of_lt_of_le hapos ht.1).le hg₁ hg₂
    exact ⟨δ, hδ, fun s hs => (hloc s hs).1⟩
  · intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hapos ht.1
    obtain ⟨δ, hδ, hloc⟩ := exists_local_windowDefectCount hT htpos.le hg₁ hg₂
    exact ⟨δ, hδ, fun s hs => (hloc s hs).2 htpos⟩

end

end RHTower
