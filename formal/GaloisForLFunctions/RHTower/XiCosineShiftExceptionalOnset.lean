import GaloisForLFunctions.RHTower.XiCosineShiftExceptionalPointIndex
import GaloisForLFunctions.RHTower.XiTwoPortProducerTransport

/-!
# The onset of exceptional points

Fix shadow-free heights `T₁ < T₂` and a depth `h > 0` such that no depth in `(0, h]` carries an
exceptional point of `cos(hD)Ξ` in `[T₁, T₂]`, and `Re ξ(½ + h + iT_j) ≠ 0`.

**Theorem** (`offline_mass_below_onset_le_one`). Then at most one zero of `ξ` (with
multiplicity) with ordinate in `[T₁, T₂]` lies in the shallow layer `½ < Re ρ < ½ + h`.

So the first exceptional depth of a window is at most the second smallest depth of the
off-line zeros in it. Exceptional points start before the off-line zeros run out of depth.

**Proof.**
* Without exceptional points in `(0, h]` the defect count `D` is locally constant there
  (`exists_local_windowDefectCount`). Lower semicontinuity at `0` gives
  `D(0) ≤ D(h)` (`windowDefectCount_zero_le_of_no_exceptional`).
* `D(0)` counts the non-real zeros of `Ξ` in the window, i.e. twice the zeros of `ξ` right of the
  critical line (`two_mul_sum_le_windowDefectCount_zero`).
* The transport law at depth `h` (`twoPort_zeroCount_le`), transported to `cos(hD)Ξ`, gives
  `D(h) ≤ 2·#{ξ = 0, Re ρ ≥ ½ + h} + 2` (`windowDefectCount_le_transport`).
-/

open Complex Filter Topology Set Metric
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

/-! ## Orders under the coordinate changes -/

/-- For a real entire function, `ord_{z̄} f = ord_z f`. -/
theorem analyticOrderAt_conj_eq {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hconj : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z))
    (hfin : ∀ z, analyticOrderAt f z ≠ ⊤) (z : ℂ) :
    analyticOrderAt f ((starRingEnd ℂ) z) = analyticOrderAt f z := by
  have key : ∀ z : ℂ, analyticOrderAt f z ≤ analyticOrderAt f ((starRingEnd ℂ) z) := by
    intro z
    obtain ⟨n, hn⟩ := ENat.ne_top_iff_exists.mp (hfin z)
    rw [← hn]
    obtain ⟨g, hg, hfac⟩ := (natCast_le_analyticOrderAt (hf.analyticAt z)).mp hn.le
    refine (natCast_le_analyticOrderAt (hf.analyticAt _)).mpr
      ⟨fun w => (starRingEnd ℂ) (g ((starRingEnd ℂ) w)), ?_, ?_⟩
    · obtain ⟨V, hV, hgV⟩ := hg.exists_mem_nhds_analyticOnNhd
      obtain ⟨U, hUV, hUo, hzU⟩ := _root_.mem_nhds_iff.mp hV
      have hcont : Continuous fun w : ℂ => (starRingEnd ℂ) w := Complex.continuous_conj
      refine DifferentiableOn.analyticAt (s := (fun w : ℂ => (starRingEnd ℂ) w) ⁻¹' U) ?_
        ((hUo.preimage hcont).mem_nhds (by simpa using hzU))
      intro w hw
      have hgw : DifferentiableAt ℂ g ((starRingEnd ℂ) w) :=
        ((hgV.mono hUV) _ hw).differentiableAt
      have hd := hgw.hasDerivAt.conj_conj
      rw [Complex.conj_conj] at hd
      exact hd.differentiableAt.differentiableWithinAt
    · have hcl : Filter.Tendsto (fun w : ℂ => (starRingEnd ℂ) w) (𝓝 ((starRingEnd ℂ) z)) (𝓝 z) := by
        have := Complex.continuous_conj.tendsto ((starRingEnd ℂ) z)
        rwa [Complex.conj_conj] at this
      filter_upwards [hcl.eventually hfac] with w hw
      simp only [smul_eq_mul] at hw ⊢
      have := congrArg (starRingEnd ℂ) hw
      rw [← hconj, Complex.conj_conj, map_mul, map_pow, map_sub, Complex.conj_conj] at this
      exact this
  refine le_antisymm ?_ (key z)
  have := key ((starRingEnd ℂ) z)
  rwa [Complex.conj_conj] at this

theorem cosProducer_conj' (h : ℝ) (z : ℂ) :
    cosProducer h ((starRingEnd ℂ) z) = (starRingEnd ℂ) (cosProducer h z) :=
  cosProducer_conj h z

/-- `ord_w Ξ = ord_{½ + iw} ξ`. -/
theorem analyticOrderAt_XiC_eq (w : ℂ) :
    analyticOrderAt XiC w = analyticOrderAt xi (1 / 2 + w * I) := by
  have hg : AnalyticAt ℂ (fun w : ℂ => 1 / 2 + w * I) w := by fun_prop
  have hd : deriv (fun w : ℂ => 1 / 2 + w * I) w ≠ 0 := by
    have : HasDerivAt (fun w : ℂ => 1 / 2 + w * I) I w := by
      simpa using ((hasDerivAt_id w).mul_const I).const_add (1 / 2 : ℂ)
    rw [this.deriv]; exact Complex.I_ne_zero
  have := analyticOrderAt_comp_of_deriv_ne_zero (f := xi) hg hd
  rw [← this]
  rfl

/-- `ord_z cos(hD)Ξ = ord_{½ + h + iz} B_h`. -/
theorem analyticOrderAt_cosProducer_eq (h : ℝ) (z : ℂ) :
    analyticOrderAt (cosProducer h) z = analyticOrderAt (twoPort h) (1 / 2 + h + z * I) := by
  have hfun : cosProducer h = fun z => (1 / 2 : ℂ) * (twoPort h ∘ fun z => 1 / 2 + h + z * I) z := by
    funext z
    simp only [Function.comp]
    rw [twoPort_eq_cosProducer]; ring
  have hg : AnalyticAt ℂ (fun z : ℂ => 1 / 2 + h + z * I) z := by fun_prop
  have hd : deriv (fun z : ℂ => 1 / 2 + h + z * I) z ≠ 0 := by
    have : HasDerivAt (fun z : ℂ => 1 / 2 + h + z * I) I z := by
      simpa using ((hasDerivAt_id z).mul_const I).const_add (1 / 2 + (h : ℂ))
    rw [this.deriv]; exact Complex.I_ne_zero
  have hcomp := analyticOrderAt_comp_of_deriv_ne_zero (f := twoPort h) hg hd
  have hBan : AnalyticAt ℂ (twoPort h ∘ fun z => 1 / 2 + h + z * I) z :=
    ((differentiable_twoPort h).analyticAt _).comp hg
  rw [hfun, show (fun z => (1 / 2 : ℂ) * (twoPort h ∘ fun z => 1 / 2 + h + z * I) z) =
      (fun _ => (1 / 2 : ℂ)) * (twoPort h ∘ fun z => 1 / 2 + h + z * I) from rfl,
    analyticOrderAt_mul analyticAt_const hBan,
    (analyticAt_const.analyticOrderAt_eq_zero).mpr (by norm_num), zero_add, hcomp]

/-! ## The three counting steps -/

theorem cosProducer_zero_eq : cosProducer 0 = XiC := funext cosProducer_zero

/-- **`D(0)` counts the off-line zeros of `ξ` twice.** -/
theorem two_mul_sum_le_windowDefectCount_zero {T₁ T₂ : ℝ} (S : Finset ℂ)
    (hS : ∀ ρ ∈ S, xi ρ = 0 ∧ 1 / 2 < ρ.re ∧ ρ.im ∈ Icc T₁ T₂) :
    2 * ∑ ρ ∈ S, (analyticOrderAt xi ρ).toNat ≤ windowDefectCount T₁ T₂ 0 := by
  classical
  set φ : ℂ → ℂ := fun ρ => -I * (ρ - 1 / 2) with hφ
  have hφinv : ∀ ρ, 1 / 2 + φ ρ * I = ρ := by
    intro ρ; simp only [hφ]; ring_nf; rw [Complex.I_sq]; ring
  have hφre : ∀ ρ, (φ ρ).re = ρ.im := by intro ρ; simp [hφ]
  have hφim : ∀ ρ, (φ ρ).im = 1 / 2 - ρ.re := by intro ρ; simp [hφ]
  have hφinj : Set.InjOn φ (S : Set ℂ) := by
    intro a _ b _ hab
    have := congrArg (fun w => 1 / 2 + w * I) hab
    rwa [hφinv, hφinv] at this
  set L := S.image φ with hL
  set U := L.image (starRingEnd ℂ) with hU
  have hconjinj : Set.InjOn (starRingEnd ℂ) (L : Set ℂ) :=
    fun a _ b _ hab => (starRingEnd ℂ).injective hab
  have hXfin : ∀ z, analyticOrderAt XiC z ≠ ⊤ := analyticOrderAt_XiC_ne_top
  have hXconj : ∀ z, XiC ((starRingEnd ℂ) z) = (starRingEnd ℂ) (XiC z) := DeBruijn.XiC_conj'
  -- the defects of `Ξ`
  set Dset := (windowDefectSet_finite T₁ T₂ 0).toFinset with hDset
  have hmemD : ∀ w, w ∈ Dset ↔ w.re ∈ Icc T₁ T₂ ∧ w.im ≠ 0 ∧ XiC w = 0 := by
    intro w
    rw [hDset, Set.Finite.mem_toFinset]
    simp only [windowDefectSet, Set.mem_setOf_eq, cosProducer_zero]
  have hLsub : ∀ w ∈ L, w ∈ Dset ∧ w.im < 0 := by
    intro w hw
    obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨h0, hre, him⟩ := hS ρ hρ
    have hneg : (φ ρ).im < 0 := by rw [hφim]; linarith
    refine ⟨(hmemD _).mpr ⟨by rw [hφre]; exact him, hneg.ne, ?_⟩, hneg⟩
    rw [XiC, hφinv]; exact h0
  have hUsub : ∀ w ∈ U, w ∈ Dset ∧ 0 < w.im := by
    intro w hw
    obtain ⟨v, hv, rfl⟩ := Finset.mem_image.mp hw
    obtain ⟨hvD, hvim⟩ := hLsub v hv
    obtain ⟨hvre, -, hv0⟩ := (hmemD v).mp hvD
    refine ⟨(hmemD _).mpr ⟨by simpa using hvre, by simp; exact hvim.ne, ?_⟩, by simp; linarith⟩
    rw [hXconj, hv0, map_zero]
  have hdisj : Disjoint L U := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    linarith [(hLsub w h1).2, (hUsub w h2).2]
  have hsumL : ∑ w ∈ L, zeroMult XiC w = ∑ ρ ∈ S, (analyticOrderAt xi ρ).toNat := by
    rw [hL, Finset.sum_image hφinj]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    unfold zeroMult
    rw [analyticOrderAt_XiC_eq, hφinv]
  have hsumU : ∑ w ∈ U, zeroMult XiC w = ∑ w ∈ L, zeroMult XiC w := by
    rw [hU, Finset.sum_image hconjinj]
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold zeroMult
    rw [analyticOrderAt_conj_eq differentiable_XiC hXconj hXfin]
  unfold windowDefectCount
  rw [← hDset, cosProducer_zero_eq]
  calc 2 * ∑ ρ ∈ S, (analyticOrderAt xi ρ).toNat
      = ∑ w ∈ L, zeroMult XiC w + ∑ w ∈ U, zeroMult XiC w := by rw [hsumU, hsumL]; ring
    _ = ∑ w ∈ L ∪ U, zeroMult XiC w := (Finset.sum_union hdisj).symm
    _ ≤ ∑ w ∈ Dset, zeroMult XiC w := Finset.sum_le_sum_of_subset (Finset.union_subset
        (fun w hw => (hLsub w hw).1) (fun w hw => (hUsub w hw).1))

/-- **The transport law for `cos(hD)Ξ`.** -/
theorem windowDefectCount_le_transport {h T₁ T₂ : ℝ} (hh : 0 < h) (hT : T₁ < T₂)
    (hg₁ : ∀ w, XiC w = 0 → w.im ^ 2 < (T₁ - w.re) ^ 2)
    (hg₂ : ∀ w, XiC w = 0 → w.im ^ 2 < (T₂ - w.re) ^ 2)
    (hA₁ : (xi (((1 / 2 + h : ℝ) : ℂ) + T₁ * I)).re ≠ 0)
    (hA₂ : (xi (((1 / 2 + h : ℝ) : ℂ) + T₂ * I)).re ≠ 0) :
    ∃ Zξ : Finset ℂ,
      (∀ w, w ∈ Zξ ↔ (w ∈ (Icc (1 / 2 + h) (1 + 2 * h) ×ℂ Icc T₁ T₂) ∧ xi w = 0 ∧
        1 / 2 + h ≤ w.re)) ∧
      windowDefectCount T₁ T₂ h ≤ 2 * ∑ w ∈ Zξ, (analyticOrderAt xi w).toNat + 2 := by
  classical
  obtain ⟨ZB, Zξ, hZB, hZξ, hle⟩ := twoPort_zeroCount_le hh hT hg₁ hg₂ hA₁ hA₂
  refine ⟨Zξ, hZξ, ?_⟩
  set f := cosProducer h with hf
  have hfd : Differentiable ℂ f := differentiable_cosProducer h
  have hfin : ∀ z, analyticOrderAt f z ≠ ⊤ := analyticOrderAt_cosProducer_ne_top h
  have hfconj : ∀ z, f ((starRingEnd ℂ) z) = (starRingEnd ℂ) (f z) := cosProducer_conj h
  set Dset := (windowDefectSet_finite T₁ T₂ h).toFinset with hDset
  have hmemD : ∀ w, w ∈ Dset ↔ w.re ∈ Icc T₁ T₂ ∧ w.im ≠ 0 ∧ f w = 0 := by
    intro w; rw [hDset, Set.Finite.mem_toFinset]; rfl
  set Dlow := Dset.filter (fun w => w.im < 0) with hDlow
  set Dup := Dset.filter (fun w => 0 < w.im) with hDup
  have hsplit : Dset = Dlow ∪ Dup := by
    ext w
    rw [Finset.mem_union, hDlow, hDup, Finset.mem_filter, Finset.mem_filter]
    constructor
    · intro hw
      rcases lt_or_gt_of_ne ((hmemD w).mp hw).2.1 with h1 | h1
      · exact Or.inl ⟨hw, h1⟩
      · exact Or.inr ⟨hw, h1⟩
    · rintro (⟨hw, -⟩ | ⟨hw, -⟩) <;> exact hw
  have hdisj : Disjoint Dlow Dup := by
    rw [Finset.disjoint_left]
    intro w h1 h2
    linarith [(Finset.mem_filter.mp h1).2, (Finset.mem_filter.mp h2).2]
  have hUeq : Dup = Dlow.image (starRingEnd ℂ) := by
    ext w
    rw [Finset.mem_image]
    constructor
    · intro hw
      obtain ⟨hwD, hwim⟩ := Finset.mem_filter.mp hw
      obtain ⟨hre, -, h0⟩ := (hmemD w).mp hwD
      refine ⟨(starRingEnd ℂ) w, Finset.mem_filter.mpr ⟨(hmemD _).mpr ⟨by simpa using hre,
        by simp; exact hwim.ne', by rw [hfconj, h0, map_zero]⟩, by simp; exact hwim⟩, by simp⟩
    · rintro ⟨v, hv, rfl⟩
      obtain ⟨hvD, hvim⟩ := Finset.mem_filter.mp hv
      obtain ⟨hre, -, h0⟩ := (hmemD v).mp hvD
      exact Finset.mem_filter.mpr ⟨(hmemD _).mpr ⟨by simpa using hre, by simp; exact hvim.ne,
        by rw [hfconj, h0, map_zero]⟩, by simp; exact hvim⟩
  have hsumUp : ∑ w ∈ Dup, zeroMult f w = ∑ w ∈ Dlow, zeroMult f w := by
    rw [hUeq, Finset.sum_image (fun a _ b _ hab => (starRingEnd ℂ).injective hab)]
    refine Finset.sum_congr rfl fun w _ => ?_
    unfold zeroMult
    rw [analyticOrderAt_conj_eq hfd hfconj hfin]
  -- the lower defects map into the zeros of `B_h` right of the line
  set ψ : ℂ → ℂ := fun z => 1 / 2 + h + z * I with hψ
  have hψinj : Set.InjOn ψ (Dlow : Set ℂ) := by
    intro a _ b _ hab
    have h1 := hab
    simp only [hψ] at h1
    have h2 : a * I = b * I := add_left_cancel h1
    exact mul_right_cancel₀ Complex.I_ne_zero h2
  have hψsub : Dlow.image ψ ⊆ ZB := by
    intro s hs
    obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp hs
    obtain ⟨hzD, hzim⟩ := Finset.mem_filter.mp hz
    obtain ⟨hre, -, h0⟩ := (hmemD z).mp hzD
    have himz := abs_im_le_half_of_cosProducer_eq_zero hh h0
    rw [hZB]
    refine ⟨?_, ?_, ?_⟩
    · rw [mem_reProdIm]
      simp only [hψ, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero,
        Complex.ofReal_re, Complex.add_im, Complex.mul_im, Complex.ofReal_im, mul_one]
      norm_num
      refine ⟨⟨by linarith, by linarith [(abs_le.mp himz).1]⟩, hre⟩
    · simp only [hψ]; rw [twoPort_eq_cosProducer, ← hf, h0, mul_zero]
    · simp only [hψ, Complex.add_re, Complex.mul_re, Complex.I_re, Complex.I_im, mul_zero,
        Complex.ofReal_re]
      norm_num; linarith
  have hsumLow : ∑ w ∈ Dlow, zeroMult f w ≤ ∑ w ∈ ZB, (analyticOrderAt (twoPort h) w).toNat := by
    calc ∑ w ∈ Dlow, zeroMult f w
        = ∑ w ∈ Dlow, (analyticOrderAt (twoPort h) (ψ w)).toNat := by
          refine Finset.sum_congr rfl fun w _ => ?_
          unfold zeroMult
          rw [hf, analyticOrderAt_cosProducer_eq]
      _ = ∑ s ∈ Dlow.image ψ, (analyticOrderAt (twoPort h) s).toNat :=
          (Finset.sum_image (f := fun s => (analyticOrderAt (twoPort h) s).toNat) hψinj).symm
      _ ≤ ∑ w ∈ ZB, (analyticOrderAt (twoPort h) w).toNat := Finset.sum_le_sum_of_subset hψsub
  unfold windowDefectCount
  rw [← hDset, ← hf, hsplit, Finset.sum_union hdisj, hsumUp]
  omega

/-- **Without exceptional points the defect count does not drop.** -/
theorem windowDefectCount_zero_le_of_no_exceptional {T₁ T₂ h : ℝ} (hT : T₁ < T₂) (hh : 0 < h)
    (hg₁ : ∀ v, XiC v = 0 → v.im ^ 2 < (T₁ - v.re) ^ 2)
    (hg₂ : ∀ v, XiC v = 0 → v.im ^ 2 < (T₂ - v.re) ^ 2)
    (hnoEP : ∀ h' ∈ Ioc 0 h, windowEPMass T₁ T₂ h' = 0) :
    windowDefectCount T₁ T₂ 0 ≤ windowDefectCount T₁ T₂ h := by
  obtain ⟨δ₀, hδ₀, h0loc⟩ := exists_local_windowDefectCount (h := 0) hT le_rfl hg₁ hg₂
  set a : ℝ := min (δ₀ / 2) h with ha
  have hapos : 0 < a := lt_min (by linarith) hh
  have hah : a ≤ h := min_le_right _ _
  have h0a : windowDefectCount T₁ T₂ 0 ≤ windowDefectCount T₁ T₂ a :=
    (h0loc a (by rw [sub_zero, abs_of_pos hapos]; linarith [min_le_left (δ₀ / 2) h])).1
  have hcont : ContinuousOn (windowDefectCount T₁ T₂) (Icc a h) := by
    intro t ht
    have htpos : 0 < t := lt_of_lt_of_le hapos ht.1
    obtain ⟨δ, hδ, hloc⟩ := exists_local_windowDefectCount hT htpos.le hg₁ hg₂
    have hM : windowEPMass T₁ T₂ t = 0 := hnoEP t ⟨htpos, ht.2⟩
    have hev : ∀ᶠ s in 𝓝 t, windowDefectCount T₁ T₂ t = windowDefectCount T₁ T₂ s := by
      filter_upwards [Metric.ball_mem_nhds t hδ] with s hs
      rw [mem_ball, Real.dist_eq] at hs
      obtain ⟨h1, h2⟩ := hloc s hs
      have := h2 htpos
      rw [hM, add_zero] at this
      exact le_antisymm h1 this
    exact ContinuousAt.continuousWithinAt (f := windowDefectCount T₁ T₂)
      (tendsto_const_nhds.congr' hev)
  have := isPreconnected_Icc.constant hcont ⟨le_rfl, hah⟩ ⟨hah, le_rfl⟩
  rw [this] at h0a
  exact h0a

/-! ## The onset law -/

/-- **Onset of exceptional points.** If no depth in `(0, h]` carries an exceptional point in the
shadow-free window `[T₁, T₂]` (and `Re ξ(½ + h + iT_j) ≠ 0`), then the zeros of `ξ` with ordinate in
the window and `½ < Re ρ < ½ + h` have total multiplicity at most one. -/
theorem offline_mass_below_onset_le_one {T₁ T₂ h : ℝ} (hT : T₁ < T₂) (hh : 0 < h)
    (hg₁ : ∀ v, XiC v = 0 → v.im ^ 2 < (T₁ - v.re) ^ 2)
    (hg₂ : ∀ v, XiC v = 0 → v.im ^ 2 < (T₂ - v.re) ^ 2)
    (hnoEP : ∀ h' ∈ Ioc 0 h, windowEPMass T₁ T₂ h' = 0)
    (hA₁ : (xi (((1 / 2 + h : ℝ) : ℂ) + T₁ * I)).re ≠ 0)
    (hA₂ : (xi (((1 / 2 + h : ℝ) : ℂ) + T₂ * I)).re ≠ 0)
    (Z : Finset ℂ)
    (hZ : ∀ ρ ∈ Z, xi ρ = 0 ∧ 1 / 2 < ρ.re ∧ ρ.re < 1 / 2 + h ∧ ρ.im ∈ Icc T₁ T₂) :
    ∑ ρ ∈ Z, (analyticOrderAt xi ρ).toNat ≤ 1 := by
  classical
  obtain ⟨Zξ, hZξ, hD⟩ := windowDefectCount_le_transport hh hT hg₁ hg₂ hA₁ hA₂
  have hdisj : Disjoint Z Zξ := by
    rw [Finset.disjoint_left]
    intro ρ h1 h2
    have := ((hZξ ρ).mp h2).2.2
    linarith [(hZ ρ h1).2.2.1]
  have hS : ∀ ρ ∈ Z ∪ Zξ, xi ρ = 0 ∧ 1 / 2 < ρ.re ∧ ρ.im ∈ Icc T₁ T₂ := by
    intro ρ hρ
    rcases Finset.mem_union.mp hρ with h1 | h1
    · obtain ⟨h0, hre, -, him⟩ := hZ ρ h1
      exact ⟨h0, hre, him⟩
    · obtain ⟨hR, h0, hre⟩ := (hZξ ρ).mp h1
      exact ⟨h0, by linarith, (mem_reProdIm.mp hR).2⟩
  have h1 := two_mul_sum_le_windowDefectCount_zero (T₁ := T₁) (T₂ := T₂) (Z ∪ Zξ) hS
  have h2 := windowDefectCount_zero_le_of_no_exceptional hT hh hg₁ hg₂ hnoEP
  rw [Finset.sum_union hdisj] at h1
  omega

end

end RHTower
