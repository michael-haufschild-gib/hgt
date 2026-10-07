import GaloisForLFunctions.HTGeometry.ImStripTranslateCompactness
import GaloisForLFunctions.HTGeometry.UniformZeroCountBound

/-!
# Real zeros of almost periodic functions on a horizontal strip

Let `f` be holomorphic on the strip `|Im z| < η` and have relatively compact real translates on a
closed substrip `|Im z| ≤ r` (`HasCompactImStripTranslates`), with `0 < r < η`.

* **Absolutely convergent exponential series** (`hasCompactImStripTranslates_tsum`).  A series
  `Σ (c_i e^{iλ_i z} + d_i e^{iμ_i z})` with `Σ (|c_i| e^{|λ_i| r} + |d_i| e^{|μ_i| r}) < ∞` has
  relatively compact translates on `|Im z| ≤ r`: a finite part is controlled by compactness of the
  torus of phases `(e^{iλ_i t}, e^{iμ_i t})`, the tail by the weights.
* **Uniform large values** (`HasCompactImStripTranslates.exists_window_lowerBound`).  If `f ≢ 0` on
  `|Im z| < r`, then for each `L > 0` there is `m > 0` such that every real window `[x, x + L]`
  contains a point `t` with `|f(t)| ≥ m`.  Otherwise translates that are small on windows have a
  uniformly convergent subsequence whose limit vanishes on a real segment, hence on the strip, and
  translation invariance of the strip returns `f ≡ 0`.
* **Linear real-zero count** (`HasCompactImStripTranslates.exists_linear_realZero_count`).  Jensen's
  inequality on discs of radius `r` centred at the large values bounds the zeros in each window of
  length `r/2` by one constant, so a nonzero `f` has `O(T)` real zeros in `[0, T]`.

This is the strip form of the Jessen–Tornehave zero-density principle, in the one-sided form needed
to compare with superlinear zero counts.
-/

open Complex Filter Topology Metric Set

namespace GaloisForLFunctions.HTGeometry

/-! ## Absolutely convergent exponential series -/

theorem norm_cexp_I_mul_le {lam r : ℝ} {z : ℂ} (hz : |z.im| ≤ r) :
    ‖cexp (I * lam * z)‖ ≤ Real.exp (|lam| * r) := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have hre : (I * (lam : ℂ) * z).re = -(lam * z.im) := by
    simp [Complex.mul_re, Complex.mul_im]
  rw [hre]
  calc -(lam * z.im) ≤ |lam * z.im| := neg_le_abs _
    _ = |lam| * |z.im| := abs_mul _ _
    _ ≤ |lam| * r := mul_le_mul_of_nonneg_left hz (abs_nonneg _)

theorem norm_cexp_I_mul_ofReal (lam t : ℝ) : ‖cexp (I * lam * t)‖ = 1 := by
  rw [show I * (lam : ℂ) * (t : ℂ) = ((lam * t : ℝ) : ℂ) * I by push_cast; ring]
  exact Complex.norm_exp_ofReal_mul_I _

theorem cexp_I_mul_add (lam : ℝ) (z w : ℂ) :
    cexp (I * lam * (z + w)) = cexp (I * lam * z) * cexp (I * lam * w) := by
  rw [← Complex.exp_add]; ring_nf

/-- **Absolutely convergent exponential series have relatively compact translates.** -/
theorem hasCompactImStripTranslates_tsum {ι : Type*} (c d : ι → ℂ) (lam mu : ι → ℝ) {r : ℝ}
    (hs : Summable fun i => ‖c i‖ * Real.exp (|lam i| * r) + ‖d i‖ * Real.exp (|mu i| * r)) :
    HasCompactImStripTranslates
      (fun z => ∑' i, (c i * cexp (I * lam i * z) + d i * cexp (I * mu i * z))) r := by
  classical
  intro ε hε
  set w : ι → ℝ := fun i => ‖c i‖ * Real.exp (|lam i| * r) + ‖d i‖ * Real.exp (|mu i| * r)
    with hw
  have hw0 : ∀ i, 0 ≤ w i := fun i => by positivity
  set S := ∑' i, w i with hS
  have hS0 : 0 ≤ S := tsum_nonneg hw0
  -- a finite set carrying all but `ε/8` of the weight
  obtain ⟨F, hF⟩ : ∃ F : Finset ι, ‖∑' x : {x // x ∉ F}, w x‖ < ε / 8 := by
    have h := (tendsto_tsum_compl_atTop_zero w).norm
    rw [norm_zero] at h
    exact (h.eventually (gt_mem_nhds (by linarith))).exists
  have htail : ∑' x : {x // x ∉ F}, w x ≤ ε / 8 := (le_abs_self _).trans hF.le
  -- the torus of phases of the finite part
  set ε' : ℝ := ε / (4 * (S + 1)) with hε'
  have hε'0 : 0 < ε' := by positivity
  let τ : ℝ → (F → ℂ × ℂ) := fun t i =>
    (cexp (I * lam (i : ι) * t), cexp (I * mu (i : ι) * t))
  have hτb : Bornology.IsBounded (range τ) := by
    refine (isBounded_closedBall (x := (0 : F → ℂ × ℂ)) (r := 1)).subset ?_
    rintro _ ⟨t, rfl⟩
    rw [mem_closedBall, dist_zero_right, pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    rw [Prod.norm_def, norm_cexp_I_mul_ofReal, norm_cexp_I_mul_ofReal, max_self]
  have htb : TotallyBounded (range τ) :=
    hτb.isCompact_closure.totallyBounded.subset subset_closure
  obtain ⟨T₀, hT₀sub, hT₀fin, hcover⟩ := finite_approx_of_totallyBounded htb ε' hε'0
  let sel : (F → ℂ × ℂ) → ℝ := fun y => if hy : y ∈ range τ then hy.choose else 0
  have hsel : ∀ y ∈ T₀, τ (sel y) = y := by
    intro y hy
    have hy' : y ∈ range τ := hT₀sub hy
    simp only [sel, dif_pos hy']
    exact hy'.choose_spec
  refine ⟨hT₀fin.toFinset.image sel, fun t => ?_⟩
  obtain ⟨y, hyT, hty⟩ := mem_iUnion₂.mp (hcover (mem_range_self t))
  refine ⟨sel y, Finset.mem_image.mpr ⟨y, hT₀fin.mem_toFinset.mpr hyT, rfl⟩, fun z hz => ?_⟩
  set s := sel y with hsdef
  have hts : dist (τ t) (τ s) < ε' := by rw [hsdef, hsel y hyT]; exact hty
  -- phase differences
  have hphase : ∀ i ∈ F, ‖cexp (I * lam i * t) - cexp (I * lam i * s)‖ ≤ ε' ∧
      ‖cexp (I * mu i * t) - cexp (I * mu i * s)‖ ≤ ε' := by
    intro i hi
    have h := (dist_le_pi_dist (τ t) (τ s) ⟨i, hi⟩).trans hts.le
    rw [dist_eq_norm] at h
    have h1 := (norm_fst_le (τ t ⟨i, hi⟩ - τ s ⟨i, hi⟩)).trans h
    have h2 := (norm_snd_le (τ t ⟨i, hi⟩ - τ s ⟨i, hi⟩)).trans h
    exact ⟨h1, h2⟩
  have hphase2 : ∀ (lam' : ℝ), ‖cexp (I * lam' * t) - cexp (I * lam' * s)‖ ≤ 2 := by
    intro lam'
    calc ‖cexp (I * lam' * t) - cexp (I * lam' * s)‖
        ≤ ‖cexp (I * lam' * t)‖ + ‖cexp (I * lam' * s)‖ := norm_sub_le _ _
      _ = 2 := by rw [norm_cexp_I_mul_ofReal, norm_cexp_I_mul_ofReal]; norm_num
  -- termwise bound
  set h : ι → ℝ := fun i => if i ∈ F then ε' else 2 with hh
  have hh0 : ∀ i, 0 ≤ h i := fun i => by simp only [hh]; split_ifs <;> positivity
  have hh2 : ∀ i, h i ≤ ε' + 2 := fun i => by
    simp only [hh]; split_ifs <;> linarith
  have hgle : ∀ i, ‖(c i * cexp (I * lam i * (z + t)) + d i * cexp (I * mu i * (z + t))) -
      (c i * cexp (I * lam i * (z + s)) + d i * cexp (I * mu i * (z + s)))‖ ≤ w i * h i := by
    intro i
    have hdl : ‖cexp (I * lam i * t) - cexp (I * lam i * s)‖ ≤ h i := by
      by_cases hi : i ∈ F
      · simp only [hh, if_pos hi]; exact (hphase i hi).1
      · simp only [hh, if_neg hi]; exact hphase2 _
    have hdm : ‖cexp (I * mu i * t) - cexp (I * mu i * s)‖ ≤ h i := by
      by_cases hi : i ∈ F
      · simp only [hh, if_pos hi]; exact (hphase i hi).2
      · simp only [hh, if_neg hi]; exact hphase2 _
    have hexp : (c i * cexp (I * lam i * (z + t)) + d i * cexp (I * mu i * (z + t))) -
        (c i * cexp (I * lam i * (z + s)) + d i * cexp (I * mu i * (z + s))) =
        c i * cexp (I * lam i * z) * (cexp (I * lam i * t) - cexp (I * lam i * s)) +
          d i * cexp (I * mu i * z) * (cexp (I * mu i * t) - cexp (I * mu i * s)) := by
      simp only [cexp_I_mul_add]; ring
    rw [hexp]
    calc _ ≤ ‖c i * cexp (I * lam i * z) * (cexp (I * lam i * t) - cexp (I * lam i * s))‖ +
          ‖d i * cexp (I * mu i * z) * (cexp (I * mu i * t) - cexp (I * mu i * s))‖ :=
          norm_add_le _ _
      _ = ‖c i‖ * ‖cexp (I * lam i * z)‖ * ‖cexp (I * lam i * t) - cexp (I * lam i * s)‖ +
          ‖d i‖ * ‖cexp (I * mu i * z)‖ * ‖cexp (I * mu i * t) - cexp (I * mu i * s)‖ := by
          rw [norm_mul, norm_mul, norm_mul, norm_mul]
      _ ≤ ‖c i‖ * Real.exp (|lam i| * r) * h i + ‖d i‖ * Real.exp (|mu i| * r) * h i := by
          gcongr
          · exact norm_cexp_I_mul_le hz
          · exact norm_cexp_I_mul_le hz
      _ = w i * h i := by simp only [hw]; ring
  -- summability on the closed strip
  have hsum : ∀ u : ℂ, |u.im| ≤ r →
      Summable fun i => c i * cexp (I * lam i * u) + d i * cexp (I * mu i * u) := by
    intro u hu
    refine Summable.of_norm_bounded hs fun i => ?_
    calc _ ≤ ‖c i * cexp (I * lam i * u)‖ + ‖d i * cexp (I * mu i * u)‖ := norm_add_le _ _
      _ ≤ ‖c i‖ * Real.exp (|lam i| * r) + ‖d i‖ * Real.exp (|mu i| * r) := by
        rw [norm_mul, norm_mul]
        gcongr
        · exact norm_cexp_I_mul_le hu
        · exact norm_cexp_I_mul_le hu
  have hzt : |(z + t).im| ≤ r := by simpa using hz
  have hzs : |(z + s).im| ≤ r := by simpa using hz
  have hbs : Summable fun i => w i * h i :=
    Summable.of_nonneg_of_le (fun i => mul_nonneg (hw0 i) (hh0 i))
      (fun i => mul_le_mul_of_nonneg_left (hh2 i) (hw0 i)) (hs.mul_right (ε' + 2))
  have hSF : ∑ i ∈ F, w i ≤ S := hs.sum_le_tsum F (fun i _ => hw0 i)
  have hεS : ε' * S ≤ ε / 4 := by
    rw [hε', div_mul_eq_mul_div, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith
  show ‖(∑' i, (c i * cexp (I * lam i * (z + t)) + d i * cexp (I * mu i * (z + t)))) -
      ∑' i, (c i * cexp (I * lam i * (z + s)) + d i * cexp (I * mu i * (z + s)))‖ ≤ ε
  rw [← (hsum _ hzt).tsum_sub (hsum _ hzs)]
  calc _ ≤ ∑' i, ‖(c i * cexp (I * lam i * (z + t)) + d i * cexp (I * mu i * (z + t))) -
        (c i * cexp (I * lam i * (z + s)) + d i * cexp (I * mu i * (z + s)))‖ :=
        norm_tsum_le_tsum_norm (Summable.of_nonneg_of_le (fun i => norm_nonneg _) hgle hbs)
    _ ≤ ∑' i, w i * h i :=
        Summable.tsum_le_tsum hgle
          (Summable.of_nonneg_of_le (fun i => norm_nonneg _) hgle hbs) hbs
    _ = ∑ i ∈ F, w i * h i + ∑' x : {x // x ∉ F}, w x * h x :=
        (hbs.sum_add_tsum_subtype_compl F).symm
    _ = ε' * ∑ i ∈ F, w i + 2 * ∑' x : {x // x ∉ F}, w x := by
        congr 1
        · rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun i hi => by simp only [hh, if_pos hi]; ring
        · rw [← tsum_mul_left]
          congr 1
          funext x
          simp only [hh, if_neg x.2]; ring
    _ ≤ ε' * S + 2 * (ε / 8) := by gcongr
    _ ≤ ε := by linarith

/-! ## Uniform large values on real windows -/

/-- **Uniform large values.**  A function with relatively compact translates that does not vanish
identically on the open strip is uniformly large somewhere in every real window of length `L`. -/
theorem HasCompactImStripTranslates.exists_window_lowerBound {f : ℂ → ℂ} {r η L : ℝ}
    (h : HasCompactImStripTranslates f r) (hr0 : 0 < r) (hrη : r < η)
    (hf : DifferentiableOn ℂ f (imStrip η)) (hL : 0 < L) {z₀ : ℂ} (hz₀ : z₀ ∈ imStrip r)
    (hfz₀ : f z₀ ≠ 0) :
    ∃ m : ℝ, 0 < m ∧ ∀ x : ℝ, ∃ t ∈ Icc x (x + L), m ≤ ‖f t‖ := by
  by_contra hcon
  push Not at hcon
  have hx : ∀ n : ℕ, ∃ x : ℝ, ∀ t ∈ Icc x (x + L), ‖f t‖ < 1 / ((n : ℝ) + 1) :=
    fun n => hcon _ (by positivity)
  choose x hx using hx
  have hc : ContinuousOn f (closedImStrip r) :=
    hf.continuousOn.mono (closedImStrip_subset_imStrip hrη)
  obtain ⟨φ, hφ, g, hg⟩ := h.exists_subseq_tendstoUniformlyOn hc x
  have hgo : TendstoUniformlyOn (fun n z => f (z + x (φ n))) g atTop (imStrip r) :=
    hg.mono (imStrip_subset_closedImStrip r)
  have hgd : DifferentiableOn ℂ g (imStrip r) := by
    refine TendstoLocallyUniformlyOn.differentiableOn hgo.tendstoLocallyUniformlyOn
      (Eventually.of_forall fun n => ?_) (isOpen_imStrip r)
    intro z hz
    have hzη : z + x (φ n) ∈ imStrip η := imStrip_mono hrη.le (add_ofReal_mem_imStrip hz _)
    exact ((hf.differentiableAt ((isOpen_imStrip η).mem_nhds hzη)).comp z
      (differentiableAt_id.add_const _)).differentiableWithinAt
  have hreal : ∀ t : ℝ, (t : ℂ) ∈ imStrip r := fun t => by simp [mem_imStrip, hr0]
  -- the limit vanishes on the real segment `[0, L]`
  have hg0 : ∀ t ∈ Icc (0 : ℝ) L, g t = 0 := by
    intro t ht
    have hlim := hgo.tendsto_at (hreal t)
    have hzero : Tendsto (fun n => f ((t : ℂ) + x (φ n))) atTop (𝓝 0) := by
      rw [tendsto_zero_iff_norm_tendsto_zero]
      refine squeeze_zero (fun n => norm_nonneg _) (fun n => ?_)
        ((tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).comp hφ.tendsto_atTop)
      have hmem : t + x (φ n) ∈ Icc (x (φ n)) (x (φ n) + L) :=
        ⟨by linarith [ht.1], by linarith [ht.2]⟩
      have h1 := hx (φ n) _ hmem
      push_cast at h1
      exact h1.le
    exact tendsto_nhds_unique hlim hzero
  -- hence on the strip
  have hgan : AnalyticOnNhd ℂ g (imStrip r) := hgd.analyticOnNhd (isOpen_imStrip r)
  have hfreq : ∃ᶠ z in 𝓝[≠] ((L / 2 : ℝ) : ℂ), g z = 0 := by
    have h1 : Tendsto (fun n : ℕ => L / 2 / ((n : ℝ) + 2)) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop (tendsto_atTop_add_const_right _ 2 tendsto_natCast_atTop_atTop)
    have hu_lim : Tendsto (fun n : ℕ => L / 2 + L / 2 / ((n : ℝ) + 2)) atTop (𝓝 (L / 2)) := by
      simpa using (tendsto_const_nhds (x := L / 2)).add h1
    have hpos : ∀ n : ℕ, 0 < L / 2 / ((n : ℝ) + 2) := fun n => by positivity
    have hU : Tendsto (fun n : ℕ => ((L / 2 + L / 2 / ((n : ℝ) + 2) : ℝ) : ℂ)) atTop
        (𝓝[≠] ((L / 2 : ℝ) : ℂ)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        ((Complex.continuous_ofReal.tendsto _).comp hu_lim)
        (Eventually.of_forall fun n => by
          simp only [mem_compl_iff, mem_singleton_iff]
          intro heq
          have := Complex.ofReal_injective heq
          linarith [hpos n])
    refine hU.frequently (Frequently.of_forall fun n => hg0 _ ⟨by linarith [hpos n], ?_⟩)
    have : L / 2 / ((n : ℝ) + 2) ≤ L / 2 :=
      div_le_self (by positivity) (by have := Nat.cast_nonneg (α := ℝ) n; linarith)
    linarith
  have hgz := hgan.eqOn_zero_of_preconnected_of_frequently_eq_zero (isPreconnected_imStrip r)
    (hreal (L / 2)) hfreq
  -- translation invariance of the strip returns `f z₀ = 0`
  apply hfz₀
  have hε : ∀ ε > 0, ‖f z₀‖ < ε := by
    intro ε hε
    obtain ⟨n, hn⟩ := ((Metric.tendstoUniformlyOn_iff.mp hgo) ε hε).exists
    have hw : z₀ - x (φ n) ∈ imStrip r := by simpa [mem_imStrip] using hz₀
    have h1 := hn _ hw
    rw [hgz hw, Pi.zero_apply, sub_add_cancel, dist_zero_left] at h1
    exact h1
  by_contra hne
  exact lt_irrefl _ (hε _ (norm_pos_iff.mpr hne))

/-! ## Linear count of real zeros -/

/-- Distinct zeros in a closed ball contribute at least their number to the divisor of a function
analytic on the ball and nonzero at its centre. -/
theorem card_le_sum_divisor_of_analyticOnNhd {f : ℂ → ℂ} {c : ℂ} {R : ℝ} (hR : 0 ≤ R)
    (hf : AnalyticOnNhd ℂ f (closedBall c R)) (hfc : f c ≠ 0) (s : Finset ℂ)
    (hball : ∀ u ∈ s, u ∈ closedBall c R) (hzero : ∀ u ∈ s, f u = 0) :
    (s.card : ℤ) ≤ ∑ᶠ u, (MeromorphicOn.divisor f (closedBall c R)) u := by
  classical
  set d := MeromorphicOn.divisor f (closedBall c R) with hd
  have hcmem : c ∈ closedBall c R := mem_closedBall_self hR
  have horderC : meromorphicOrderAt f c ≠ ⊤ := by
    rw [(hf c hcmem).meromorphicOrderAt_eq, (hf c hcmem).analyticOrderAt_eq_zero.mpr hfc]
    simp
  have horder : ∀ u : closedBall c R, meromorphicOrderAt f u ≠ ⊤ := fun u =>
    hf.meromorphicOn.meromorphicOrderAt_ne_top_of_isPreconnected
      (convex_closedBall c R).isPreconnected hcmem u.2 horderC
  have hsupport : closedBall c R ∩ f ⁻¹' {0} = Function.support d :=
    hf.meromorphicNFOn.zero_set_eq_divisor_support horder
  have hsub : (s : Set ℂ) ⊆ Function.support d := by
    intro u hu
    rw [← hsupport]
    exact ⟨hball u hu, hzero u hu⟩
  have hdnonneg : ∀ u : ℂ, 0 ≤ d u := MeromorphicOn.AnalyticOnNhd.divisor_nonneg hf
  have hdfin : (Function.support d).Finite := d.finiteSupport (isCompact_closedBall c R)
  calc (s.card : ℤ) = ∑ u ∈ s, (1 : ℤ) := by simp
    _ ≤ ∑ u ∈ s, d u := Finset.sum_le_sum fun u hu => by
        have hne : d u ≠ 0 := hsub hu
        have := hdnonneg u
        omega
    _ ≤ ∑ u ∈ hdfin.toFinset, d u := Finset.sum_le_sum_of_subset_of_nonneg
        (fun u hu => hdfin.mem_toFinset.mpr (hsub hu)) (fun u _ _ => hdnonneg u)
    _ = ∑ᶠ u, d u := (finsum_eq_sum_of_support_subset _ (fun u hu => by simpa using hu)).symm

/-- **Linear count of real zeros.**  A function with relatively compact translates on `|Im z| ≤ r`
that does not vanish identically on `|Im z| < r` has at most `K (T + 1)` distinct real zeros in
`[0, T]`. -/
theorem HasCompactImStripTranslates.exists_linear_realZero_count {f : ℂ → ℂ} {r η : ℝ}
    (h : HasCompactImStripTranslates f r) (hr0 : 0 < r) (hrη : r < η)
    (hf : DifferentiableOn ℂ f (imStrip η)) {z₀ : ℂ} (hz₀ : z₀ ∈ imStrip r) (hfz₀ : f z₀ ≠ 0) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ T : ℝ, 0 ≤ T → ∀ s : Finset ℝ, (∀ t ∈ s, 0 ≤ t ∧ t ≤ T ∧ f t = 0) →
      (s.card : ℝ) ≤ K * (T + 1) := by
  classical
  set L := r / 2 with hL
  have hL0 : 0 < L := by positivity
  obtain ⟨m, hm0, hlarge⟩ := h.exists_window_lowerBound hr0 hrη hf hL0 hz₀ hfz₀
  have hc : ContinuousOn f (closedImStrip r) :=
    hf.continuousOn.mono (closedImStrip_subset_imStrip hrη)
  obtain ⟨B, hB⟩ := h.exists_bound hc
  set M := max B 1 with hM
  have hM1 : 1 ≤ M := le_max_right _ _
  set N₀ := Real.log (M / m) / Real.log 2 with hN₀
  choose ctr hctr hctrm using fun k : ℕ => hlarge (k * L)
  have him : ∀ (c : ℂ) (z : ℂ), c.im = 0 → |z.im| ≤ ‖z - c‖ := by
    intro c z hc0
    have : z.im = (z - c).im := by simp [hc0]
    rw [this]
    exact abs_im_le_norm _
  -- one window: Jensen at a large value
  have hwin : ∀ k : ℕ, ∀ u : Finset ℝ, (∀ t ∈ u, |t - ctr k| ≤ L ∧ f t = 0) →
      (u.card : ℝ) ≤ N₀ := by
    intro k u hu
    set c : ℂ := (ctr k : ℂ) with hcdef
    have hc0 : c.im = 0 := by simp [hcdef]
    have hcne : f c ≠ 0 := by
      intro h0
      have := hctrm k
      rw [← hcdef, h0, norm_zero] at this
      linarith
    have hanal : AnalyticOnNhd ℂ f (closedBall c |r|) := by
      intro z hz
      apply hf.analyticAt
      apply (isOpen_imStrip η).mem_nhds
      apply closedImStrip_subset_imStrip hrη
      rw [mem_closedImStrip]
      rw [mem_closedBall, abs_of_pos hr0, dist_eq_norm] at hz
      exact (him c z hc0).trans hz
    have hLr : |L| ≤ |r| := by rw [abs_of_pos hL0, abs_of_pos hr0, hL]; linarith
    have hcount := card_le_sum_divisor_of_analyticOnNhd (abs_nonneg L)
      (hanal.mono (closedBall_subset_closedBall hLr)) hcne (u.image (fun t : ℝ => (t : ℂ)))
      (by
        intro z hz
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
        rw [mem_closedBall, dist_eq_norm, abs_of_pos hL0]
        have e : (t : ℂ) - c = ((t - ctr k : ℝ) : ℂ) := by rw [hcdef]; push_cast; rfl
        rw [e, Complex.norm_real, Real.norm_eq_abs]
        exact (hu t ht).1)
      (by
        intro z hz
        obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hz
        exact (hu t ht).2)
    have hjensen := hanal.sum_divisor_le (r := L) (R := r) (M := M)
      (by rw [abs_of_pos hL0]; exact hL0) (by rw [abs_of_pos hL0, abs_of_pos hr0, hL]; linarith)
      hM1 hcne (by
        intro z hz
        refine (hB z ?_).trans (le_max_left _ _)
        rw [mem_sphere, abs_of_pos hr0, dist_eq_norm] at hz
        exact (him c z hc0).trans hz.le)
    rw [Finset.card_image_of_injective _ Complex.ofReal_injective] at hcount
    have hRr : r / L = 2 := by rw [hL]; field_simp
    rw [hRr] at hjensen
    have hcountR : (u.card : ℝ) ≤
        ((∑ᶠ z, (MeromorphicOn.divisor f (closedBall c |L|)) z : ℤ) : ℝ) := by
      exact_mod_cast hcount
    refine hcountR.trans (hjensen.trans ?_)
    apply div_le_div_of_nonneg_right _ (Real.log_nonneg (by norm_num))
    apply Real.log_le_log (div_pos (by linarith) (norm_pos_iff.mpr hcne))
    exact div_le_div_of_nonneg_left (by linarith) hm0 (hctrm k)
  have hN₀0 : 0 ≤ N₀ := by
    apply div_nonneg _ (Real.log_nonneg (by norm_num))
    apply Real.log_nonneg
    rw [le_div_iff₀ hm0, one_mul]
    have h1 := hctrm 0
    have h2 := hB (ctr 0) (by simp [hr0.le])
    exact h1.trans (h2.trans (le_max_left _ _))
  refine ⟨N₀ * (2 / r + 1), by positivity, fun T hT s hs => ?_⟩
  -- distribute the zeros over windows of length `L`
  have himg : s.image (fun t : ℝ => ⌊t / L⌋₊) ⊆ Finset.range (⌊T / L⌋₊ + 1) := by
    intro k hk
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.mp hk
    rw [Finset.mem_range, Nat.lt_succ_iff]
    exact Nat.floor_le_floor (div_le_div_of_nonneg_right (hs t ht).2.1 hL0.le)
  have hfib : ∀ k ∈ s.image (fun t : ℝ => ⌊t / L⌋₊),
      (s.filter fun t => ⌊t / L⌋₊ = k).card ≤ ⌊N₀⌋₊ := by
    intro k _
    apply Nat.le_floor
    apply hwin k
    intro t ht
    obtain ⟨hts, hkt⟩ := Finset.mem_filter.mp ht
    obtain ⟨ht0, -, hft⟩ := hs t hts
    refine ⟨?_, hft⟩
    have hq0 : 0 ≤ t / L := div_nonneg ht0 hL0.le
    have h1 : (k : ℝ) ≤ t / L := by rw [← hkt]; exact Nat.floor_le hq0
    have h2 : t / L < k + 1 := by rw [← hkt]; exact Nat.lt_floor_add_one _
    have h1' : k * L ≤ t := by rwa [le_div_iff₀ hL0] at h1
    have h2' : t < (k + 1) * L := by rwa [div_lt_iff₀ hL0] at h2
    obtain ⟨hc1, hc2⟩ := hctr k
    rw [abs_le]
    constructor <;> linarith
  have hcard := Finset.card_le_mul_card_image s ⌊N₀⌋₊ hfib
  have hcardimg : ((s.image (fun t : ℝ => ⌊t / L⌋₊)).card : ℝ) ≤ T / L + 1 := by
    have h1 := Finset.card_le_card himg
    rw [Finset.card_range] at h1
    have h2 : ((s.image (fun t : ℝ => ⌊t / L⌋₊)).card : ℝ) ≤ (⌊T / L⌋₊ : ℝ) + 1 := by
      exact_mod_cast h1
    exact h2.trans (by linarith [Nat.floor_le (div_nonneg hT hL0.le)])
  have hfloor : (⌊N₀⌋₊ : ℝ) ≤ N₀ := Nat.floor_le hN₀0
  have hTL : T / L = 2 / r * T := by rw [hL]; field_simp
  calc (s.card : ℝ) ≤ (⌊N₀⌋₊ : ℝ) * (s.image (fun t : ℝ => ⌊t / L⌋₊)).card := by
        exact_mod_cast hcard
    _ ≤ N₀ * (T / L + 1) := mul_le_mul hfloor hcardimg (by positivity) hN₀0
    _ ≤ N₀ * (2 / r + 1) * (T + 1) := by
        rw [mul_assoc]
        apply mul_le_mul_of_nonneg_left _ hN₀0
        rw [hTL]
        have : 0 ≤ 2 / r := by positivity
        nlinarith

end GaloisForLFunctions.HTGeometry
