import GaloisForLFunctions.RHTower.XiRealRootedEigenLimitRH

/-!
# Real-rooted weights with an asymptotic eigen-equation force RH

Let `G_j` be holomorphic on the strip `|Im z| < 1/2 + η`, uniformly bounded there, with only real
zeros in the strip and `G_j(0) = 1`. Fix a smooth bump `b` supported in `[-1, 1]` with
`b̂(0) ≠ 0`. Suppose that for every modulation `c` and shift `u` the zero-side eigen-equation holds
asymptotically on the test transforms `z ↦ b̂(c - z) e^{-izu}`:

`‖∑_q G_j(γ_q) b̂(c - γ_q) e^{-iγ_q u} - κ_j ∫_ℝ G_j(s) b̂(c - s) e^{-isu} ds‖ ≤ (1 + ‖κ_j‖) δ_j`

with `δ_j → 0`. Then the Riemann hypothesis holds.

The proof is that of `riemannHypothesis_of_realRootedEigen`, with the error terms carried through.
The errors are allowed to grow with `‖κ_j‖`; the eigenvalues are shown to be bounded first.
-/

open Complex MeasureTheory Set Filter Topology Metric
open scoped FourierTransform
open GaloisForLFunctions.HTGeometry

namespace RHTower

noncomputable section

theorem nonneg_of_norm_le_one_add_mul {E : Type*} [SeminormedAddCommGroup E] {x : E} {k : ℂ}
    {δ : ℝ} (h : ‖x‖ ≤ (1 + ‖k‖) * δ) : 0 ≤ δ := by
  by_contra hneg
  push Not at hneg
  have : (1 + ‖k‖) * δ < 0 := mul_neg_of_pos_of_neg (by positivity) hneg
  linarith [norm_nonneg x]

/-- **Real-rooted weights with an asymptotic eigen-equation force RH.** -/
theorem riemannHypothesis_of_realRootedApproxEigen
    {η C : ℝ} (hη : 0 < η)
    {G : ℕ → ℂ → ℂ} {κ : ℕ → ℂ}
    (b : SuzukiSmoothCompactTest 1) (hb0 : suzukiSmoothFourier b 0 ≠ 0)
    (hGdiff : ∀ j, DifferentiableOn ℂ (G j) (xiOneSidedStrip η))
    (hGbound : ∀ j, ∀ z ∈ xiOneSidedStrip η, ‖G j z‖ ≤ C)
    (hGreal : ∀ j, ∀ z ∈ xiOneSidedStrip η, G j z = 0 → z.im = 0)
    (hG0 : ∀ j, G j 0 = 1)
    (heig : ∀ c u : ℝ, ∃ δ : ℕ → ℝ, Tendsto δ atTop (𝓝 0) ∧ ∀ j,
      ‖(∑' q : XiZeroCopy, G j (xiSpectralPoint q) *
          (suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q) *
            cexp (-(I * xiSpectralPoint q) * u))) -
        κ j * ∫ s : ℝ, G j (s : ℂ) *
          (suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * u))‖ ≤
        (1 + ‖κ j‖) * δ j) :
    RiemannHypothesis := by
  classical
  set U := xiOneSidedStrip η with hUdef
  have hUopen : IsOpen U := isOpen_xiOneSidedStrip η
  have h0U : (0 : ℂ) ∈ U := by
    show |(0 : ℂ).im| < 1 / 2 + η
    simp; linarith
  have hC : 0 ≤ C := le_trans (norm_nonneg _) (hGbound 0 0 h0U)
  set Y : ℝ := 1 / 2 + η with hYdef
  have hY : 0 ≤ Y := by rw [hYdef]; linarith
  have hγhalf : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| < 1 / 2 := by
    intro q
    have := xiSpectralPoint_im_mem_openHalf q
    rw [abs_lt]; constructor <;> linarith [this.1, this.2]
  have hγU : ∀ q : XiZeroCopy, xiSpectralPoint q ∈ U := by
    intro q
    show |(xiSpectralPoint q).im| < 1 / 2 + η
    linarith [hγhalf q]
  have hγY : ∀ q : XiZeroCopy, |(xiSpectralPoint q).im| ≤ Y := by
    intro q; rw [hYdef]; linarith [hγhalf q]
  have hsU : ∀ s : ℝ, (s : ℂ) ∈ U := by
    intro s
    show |((s : ℂ)).im| < 1 / 2 + η
    simp; linarith
  set K₀ : ℝ := suzukiTestDecayConst b Y with hK₀
  have hK₀ : 0 ≤ K₀ := suzukiTestDecayConst_nonneg b Y
  have hbdiff : Differentiable ℂ (suzukiSmoothFourier b) :=
    differentiable_suzukiSmoothFourier zero_le_one b
  -- dominations
  have hdomq : ∀ (H : ℂ → ℂ), (∀ z ∈ U, ‖H z‖ ≤ C) → ∀ (c u : ℝ) (q : XiZeroCopy),
      ‖H (xiSpectralPoint q) * (suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q) *
          cexp (-(I * xiSpectralPoint q) * u))‖ ≤
        C * (2 * (1 + c ^ 2) * K₀) * Real.exp (|u| / 2) *
          (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
    intro H hH c u q
    have hq0 : xiSpectralPoint q ≠ 0 := xiSpectralPoint_ne_zero q
    have hpos : 0 < ‖xiSpectralPoint q‖ ^ 2 := by positivity
    have hb := norm_suzukiSmoothFourier_sub_le b hY c (hγY q)
    have hexp : ‖cexp (-(I * xiSpectralPoint q) * u)‖ ≤ Real.exp (|u| / 2) := by
      rw [norm_cexp_neg_I_mul_ofReal]
      apply Real.exp_le_exp.mpr
      calc u * (xiSpectralPoint q).im ≤ |u * (xiSpectralPoint q).im| := le_abs_self _
        _ = |u| * |(xiSpectralPoint q).im| := abs_mul _ _
        _ ≤ |u| * (1 / 2) := by gcongr; exact (hγhalf q).le
        _ = |u| / 2 := by ring
    have hinv : 2 * (1 + c ^ 2) * K₀ / (1 + ‖xiSpectralPoint q‖ ^ 2) ≤
        2 * (1 + c ^ 2) * K₀ * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by
      rw [div_eq_mul_one_div]
      gcongr
      linarith
    rw [norm_mul, norm_mul]
    calc ‖H (xiSpectralPoint q)‖ * (‖suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q)‖ *
          ‖cexp (-(I * xiSpectralPoint q) * u)‖)
        ≤ C * ((2 * (1 + c ^ 2) * K₀ * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ))) *
            Real.exp (|u| / 2)) := by
          gcongr
          · exact hH _ (hγU q)
          · exact hb.trans hinv
      _ = C * (2 * (1 + c ^ 2) * K₀) * Real.exp (|u| / 2) *
          (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) := by ring
  have hsumq : ∀ (c u : ℝ), Summable fun q : XiZeroCopy =>
      C * (2 * (1 + c ^ 2) * K₀) * Real.exp (|u| / 2) * (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) :=
    fun c u => xiSpectralPoint_inv_sq_summable.mul_left _
  have hdoms : ∀ (H : ℂ → ℂ), (∀ z ∈ U, ‖H z‖ ≤ C) → ∀ (c u s : ℝ),
      ‖H (s : ℂ) * (suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * u))‖ ≤
        C * (2 * (1 + c ^ 2) * K₀) * (1 + s ^ 2)⁻¹ := by
    intro H hH c u s
    have hb := norm_suzukiSmoothFourier_sub_le b hY c (z := (s : ℂ)) (by simpa using hY)
    have hexp : ‖cexp (-(I * (s : ℂ)) * u)‖ = 1 := by
      rw [norm_cexp_neg_I_mul_ofReal]; simp
    rw [norm_mul, norm_mul, hexp, mul_one]
    have hs2 : ‖(s : ℂ)‖ ^ 2 = s ^ 2 := by simp [sq_abs]
    rw [hs2] at hb
    calc ‖H (s : ℂ)‖ * ‖suzukiSmoothFourier b ((c : ℂ) - (s : ℂ))‖
        ≤ C * (2 * (1 + c ^ 2) * K₀ / (1 + s ^ 2)) := by
          gcongr
          exact hH _ (hsU s)
      _ = C * (2 * (1 + c ^ 2) * K₀) * (1 + s ^ 2)⁻¹ := by ring
  have hintdom : ∀ c : ℝ, Integrable fun s : ℝ => C * (2 * (1 + c ^ 2) * K₀) * (1 + s ^ 2)⁻¹ :=
    fun c => integrable_inv_one_add_sq.const_mul _
  have hcontline : ∀ (H : ℂ → ℂ), DifferentiableOn ℂ H U → ∀ (c u : ℝ),
      Continuous fun s : ℝ =>
        H (s : ℂ) * (suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * u)) := by
    intro H hH c u
    rw [continuous_iff_continuousAt]
    intro s
    have hHc : ContinuousAt H (s : ℂ) := (hH.differentiableAt (hUopen.mem_nhds (hsU s))).continuousAt
    have h1 : ContinuousAt (fun s : ℝ => H (s : ℂ)) s :=
      ContinuousAt.comp (g := H) hHc Complex.continuous_ofReal.continuousAt
    have h2 : Continuous fun s : ℝ => suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) :=
      hbdiff.continuous.comp (by fun_prop)
    have h3 : Continuous fun s : ℝ => cexp (-(I * (s : ℂ)) * u) := by fun_prop
    exact h1.mul (h2.mul h3).continuousAt
  -- Montel on the strip
  obtain ⟨φ₁, hφ₁, Glim, hconv⟩ := exists_tendstoLocallyUniformlyOn_subseq_of_bounded hUopen
    (F := G) (C := C) hGdiff (fun n z hz => hGbound n z hz)
  have hpt : ∀ z ∈ U, Tendsto (fun k => G (φ₁ k) z) atTop (𝓝 (Glim z)) :=
    fun z hz => hconv.tendsto_at hz
  have hGlim0 : Glim 0 = 1 := by
    have := hpt 0 h0U
    simp only [hG0] at this
    exact tendsto_nhds_unique this tendsto_const_nhds
  have hGlimdiff : DifferentiableOn ℂ Glim U :=
    hconv.differentiableOn (Eventually.of_forall fun k => hGdiff _) hUopen
  have hGlimbound : ∀ z ∈ U, ‖Glim z‖ ≤ C := by
    intro z hz
    exact le_of_tendsto' ((hpt z hz).norm) fun k => hGbound _ z hz
  -- limits of the two sides along any further subsequence
  have hlimsum : ∀ (ψ : ℕ → ℕ), Tendsto ψ atTop atTop → ∀ (c u : ℝ),
      Tendsto (fun k => ∑' q : XiZeroCopy, G (φ₁ (ψ k)) (xiSpectralPoint q) *
          (suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q) *
            cexp (-(I * xiSpectralPoint q) * u))) atTop
        (𝓝 (∑' q : XiZeroCopy, Glim (xiSpectralPoint q) *
          (suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q) *
            cexp (-(I * xiSpectralPoint q) * u)))) := by
    intro ψ hψ c u
    refine tendsto_tsum_of_dominated_convergence (hsumq c u) (fun q => ?_)
      (Eventually.of_forall fun k q => hdomq _ (fun z hz => hGbound _ z hz) c u q)
    exact ((hpt _ (hγU q)).comp hψ).mul_const _
  have hlimint : ∀ (ψ : ℕ → ℕ), Tendsto ψ atTop atTop → ∀ (c u : ℝ),
      Tendsto (fun k => ∫ s : ℝ, G (φ₁ (ψ k)) (s : ℂ) *
          (suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * u))) atTop
        (𝓝 (∫ s : ℝ, Glim (s : ℂ) *
          (suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * u)))) := by
    intro ψ hψ c u
    refine tendsto_integral_of_dominated_convergence _
      (fun k => (hcontline _ (hGdiff _) c u).aestronglyMeasurable) (hintdom c)
      (fun k => ae_of_all _ fun s => hdoms _ (fun z hz => hGbound _ z hz) c u s)
      (ae_of_all _ fun s => ?_)
    exact ((hpt _ (hsU s)).comp hψ).mul_const _
  -- the eigenvalues are bounded
  have hκbdd : ∃ M : ℝ, ∀ k, ‖κ (φ₁ k)‖ ≤ M := by
    by_contra hnot
    push Not at hnot
    have hfreq : ∀ n : ℕ, ∃ᶠ k in atTop, (n : ℝ) + 1 < ‖κ (φ₁ k)‖ := by
      intro n
      rw [Filter.frequently_atTop]
      intro N
      obtain ⟨k, hk⟩ := hnot ((n : ℝ) + 1 + ∑ i ∈ Finset.range N, ‖κ (φ₁ i)‖)
      have hsum0 : 0 ≤ ∑ i ∈ Finset.range N, ‖κ (φ₁ i)‖ :=
        Finset.sum_nonneg fun i _ => norm_nonneg _
      refine ⟨k, ?_, by linarith⟩
      by_contra hlt
      push Not at hlt
      have hle : ‖κ (φ₁ k)‖ ≤ ∑ i ∈ Finset.range N, ‖κ (φ₁ i)‖ :=
        Finset.single_le_sum (f := fun i => ‖κ (φ₁ i)‖) (fun i _ => norm_nonneg _)
          (Finset.mem_range.mpr hlt)
      have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
      linarith
    obtain ⟨ψ, hψ, hψk⟩ := extraction_forall_of_frequently hfreq
    have hzero : ∀ u : ℝ, ∫ s : ℝ, Glim (s : ℂ) *
        (suzukiSmoothFourier b (((0 : ℝ) : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * u)) = 0 := by
      intro u
      set S : ℝ := ∑' q : XiZeroCopy, C * (2 * (1 + (0 : ℝ) ^ 2) * K₀) * Real.exp (|u| / 2) *
        (1 / ‖xiSpectralPoint q‖ ^ (2 : ℕ)) with hS
      obtain ⟨δ, hδ, hδb⟩ := heig 0 u
      have hδsub : Tendsto (fun k => δ (φ₁ (ψ k))) atTop (𝓝 0) :=
        (hδ.comp hφ₁.tendsto_atTop).comp hψ.tendsto_atTop
      have hbound : ∀ᶠ k in atTop, ‖∫ s : ℝ, G (φ₁ (ψ k)) (s : ℂ) *
          (suzukiSmoothFourier b (((0 : ℝ) : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * u))‖ ≤
            (S + 1) / ((k : ℝ) + 1) + δ (φ₁ (ψ k)) := by
        filter_upwards [hδsub.eventually (eventually_le_nhds one_pos)] with k hk1
        have hκpos : (k : ℝ) + 1 < ‖κ (φ₁ (ψ k))‖ := hψk k
        have hsumbd : ‖∑' q : XiZeroCopy, G (φ₁ (ψ k)) (xiSpectralPoint q) *
            (suzukiSmoothFourier b (((0 : ℝ) : ℂ) - xiSpectralPoint q) *
              cexp (-(I * xiSpectralPoint q) * u))‖ ≤ S := by
          refine (norm_tsum_le_tsum_norm ?_).trans ?_
          · exact (hsumq 0 u).of_nonneg_of_le (fun q => norm_nonneg _)
              (fun q => hdomq _ (fun z hz => hGbound _ z hz) 0 u q)
          · exact Summable.tsum_le_tsum (fun q => hdomq _ (fun z hz => hGbound _ z hz) 0 u q)
              ((hsumq 0 u).of_nonneg_of_le (fun q => norm_nonneg _)
                (fun q => hdomq _ (fun z hz => hGbound _ z hz) 0 u q)) (hsumq 0 u)
        have herr := hδb (φ₁ (ψ k))
        have hδ0 := nonneg_of_norm_le_one_add_mul herr
        set Sk := ∑' q : XiZeroCopy, G (φ₁ (ψ k)) (xiSpectralPoint q) *
            (suzukiSmoothFourier b (((0 : ℝ) : ℂ) - xiSpectralPoint q) *
              cexp (-(I * xiSpectralPoint q) * u)) with hSk
        set Ik := ∫ s : ℝ, G (φ₁ (ψ k)) (s : ℂ) *
            (suzukiSmoothFourier b (((0 : ℝ) : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * u))
          with hIk
        set κk := κ (φ₁ (ψ k)) with hκk
        set δk := δ (φ₁ (ψ k)) with hδk
        have hκI : ‖κk‖ * ‖Ik‖ ≤ S + (1 + ‖κk‖) * δk := by
          have h1 : κk * Ik = Sk - (Sk - κk * Ik) := by ring
          rw [← norm_mul, h1]
          exact (norm_sub_le _ _).trans (add_le_add hsumbd herr)
        have hS0 : 0 ≤ S := tsum_nonneg fun q => by positivity
        have hk0 : (0 : ℝ) < (k : ℝ) + 1 := by positivity
        have hmain : (‖Ik‖ - δk) * ((k : ℝ) + 1) ≤ S + 1 := by
          rcases le_or_gt (‖Ik‖ - δk) 0 with hneg | hpos
          · nlinarith
          · calc (‖Ik‖ - δk) * ((k : ℝ) + 1) ≤ (‖Ik‖ - δk) * ‖κk‖ := by gcongr
              _ ≤ S + δk := by nlinarith
              _ ≤ S + 1 := by linarith
        have : ‖Ik‖ - δk ≤ (S + 1) / ((k : ℝ) + 1) := by rw [le_div_iff₀ hk0]; exact hmain
        linarith
      have hto0 : Tendsto (fun k => ∫ s : ℝ, G (φ₁ (ψ k)) (s : ℂ) *
          (suzukiSmoothFourier b (((0 : ℝ) : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * u)))
          atTop (𝓝 0) := by
        rw [tendsto_zero_iff_norm_tendsto_zero]
        refine squeeze_zero' (Eventually.of_forall fun k => norm_nonneg _) hbound ?_
        have h1 : Tendsto (fun k : ℕ => (S + 1) * ((k : ℝ) + 1)⁻¹) atTop (𝓝 ((S + 1) * 0)) :=
          tendsto_const_nhds.mul
            (tendsto_inv_atTop_zero.comp (tendsto_natCast_atTop_atTop.atTop_add tendsto_const_nhds))
        have h2 := h1.add hδsub
        simpa [div_eq_mul_inv] using h2
      exact tendsto_nhds_unique (hlimint ψ hψ.tendsto_atTop 0 u) hto0
    set Hf : ℝ → ℂ := fun s => Glim (s : ℂ) * suzukiSmoothFourier b (((0 : ℝ) : ℂ) - (s : ℂ))
      with hHf
    have hHcont : Continuous Hf := by
      have := hcontline Glim hGlimdiff 0 0
      simp only [ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at this
      simpa [hHf] using this
    have hHint : Integrable Hf := by
      refine (hintdom 0).mono' hHcont.aestronglyMeasurable (ae_of_all _ fun s => ?_)
      have := hdoms Glim hGlimbound 0 0 s
      simp only [ofReal_zero, mul_zero, Complex.exp_zero, mul_one] at this
      simpa [hHf] using this
    have hH0 : Hf = 0 := eq_zero_of_integral_mul_cexp_eq_zero hHcont hHint (fun u => by
      have := hzero u
      simpa [hHf, mul_assoc] using this)
    have hval := congrFun hH0 0
    simp only [hHf, ofReal_zero, sub_zero, hGlim0, one_mul, Pi.zero_apply] at hval
    exact hb0 hval
  -- a convergent subsequence of eigenvalues
  obtain ⟨M, hM⟩ := hκbdd
  obtain ⟨κlim, -, ψ, hψ, hκlim⟩ := tendsto_subseq_of_bounded (Metric.isBounded_closedBall
    (x := (0 : ℂ)) (r := M)) (x := fun k => κ (φ₁ k))
    (fun k => by rw [mem_closedBall, dist_zero_right]; exact hM k)
  -- the one-sided limit identity for every modulation
  have hAzero : ∀ (c : ℝ) (q : XiZeroCopy),
      Glim (xiSpectralPoint q) * suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q) = 0 := by
    intro c q
    have hlimid : ∀ u : ℝ, 0 < u →
        ∑' q : XiZeroCopy, (fun z => Glim z * suzukiSmoothFourier b ((c : ℂ) - z))
            (xiSpectralPoint q) * cexp (-(I * xiSpectralPoint q) * u) =
          ∫ t : ℝ, (fun z => κlim * (Glim z * suzukiSmoothFourier b ((c : ℂ) - z))) (t : ℂ) *
            cexp (-(I * (t : ℂ)) * u) := by
      intro u _
      have hL := hlimsum ψ hψ.tendsto_atTop c u
      have hR := (hκlim.mul (hlimint ψ hψ.tendsto_atTop c u))
      have hdiff0 : Tendsto (fun k => (∑' q : XiZeroCopy, G (φ₁ (ψ k)) (xiSpectralPoint q) *
          (suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q) *
            cexp (-(I * xiSpectralPoint q) * u))) -
          ((fun k => κ (φ₁ k)) ∘ ψ) k * ∫ s : ℝ, G (φ₁ (ψ k)) (s : ℂ) *
            (suzukiSmoothFourier b ((c : ℂ) - (s : ℂ)) * cexp (-(I * (s : ℂ)) * u)))
          atTop (𝓝 0) := by
        obtain ⟨δ, hδ, hδb⟩ := heig c u
        have hδsub : Tendsto (fun k => δ (φ₁ (ψ k))) atTop (𝓝 0) :=
          (hδ.comp hφ₁.tendsto_atTop).comp hψ.tendsto_atTop
        rw [tendsto_zero_iff_norm_tendsto_zero]
        refine squeeze_zero (g := fun k => (1 + M) * δ (φ₁ (ψ k))) (fun k => norm_nonneg _)
          (fun k => (hδb (φ₁ (ψ k))).trans ?_) ?_
        · have hδ0 := nonneg_of_norm_le_one_add_mul (hδb (φ₁ (ψ k)))
          gcongr
          exact hM (ψ k)
        · simpa using hδsub.const_mul (1 + M)
      have hfin0 := tendsto_nhds_unique (hL.sub hR) hdiff0
      have hfin := sub_eq_zero.mp hfin0
      rw [← integral_const_mul] at hfin
      convert hfin using 1
      · exact tsum_congr fun q => by ring
      · exact integral_congr_ae (ae_of_all _ fun t => by ring)
    have hdiffB : ∀ z : ℂ, |z.im| < 1 / 2 + η →
        DifferentiableAt ℂ (fun z => κlim * (Glim z * suzukiSmoothFourier b ((c : ℂ) - z))) z := by
      intro z hz
      have hzU : z ∈ U := hz
      exact ((hGlimdiff.differentiableAt (hUopen.mem_nhds hzU)).mul
        ((hbdiff _).comp z (by fun_prop))).const_mul _
    set Kc : ℝ := (max 1 ‖κlim‖) * (C * (2 * (1 + c ^ 2) * K₀)) with hKc
    have hdomA : StripInvSqDominated η Kc (fun z => Glim z * suzukiSmoothFourier b ((c : ℂ) - z)) := by
      intro z hz
      have hzU : z ∈ U := hz
      have hb := norm_suzukiSmoothFourier_sub_le b hY c (z := z) (by rw [hYdef]; exact hz.le)
      rw [norm_mul]
      calc ‖Glim z‖ * ‖suzukiSmoothFourier b ((c : ℂ) - z)‖
          ≤ C * (2 * (1 + c ^ 2) * K₀ / (1 + ‖z‖ ^ 2)) := by
            gcongr
            exact hGlimbound z hzU
        _ ≤ Kc / (1 + ‖z‖ ^ 2) := by
            have hle : C * (2 * (1 + c ^ 2) * K₀) ≤ Kc := by
              rw [hKc]
              calc C * (2 * (1 + c ^ 2) * K₀) = 1 * (C * (2 * (1 + c ^ 2) * K₀)) := by ring
                _ ≤ max 1 ‖κlim‖ * (C * (2 * (1 + c ^ 2) * K₀)) := by
                    gcongr; exact le_max_left _ _
            rw [← mul_div_assoc]
            gcongr
    have hdomB : StripInvSqDominated η Kc
        (fun z => κlim * (Glim z * suzukiSmoothFourier b ((c : ℂ) - z))) := by
      intro z hz
      have hA := hdomA z hz
      have hzU : z ∈ U := hz
      have hb := norm_suzukiSmoothFourier_sub_le b hY c (z := z) (by rw [hYdef]; exact hz.le)
      rw [norm_mul, norm_mul]
      calc ‖κlim‖ * (‖Glim z‖ * ‖suzukiSmoothFourier b ((c : ℂ) - z)‖)
          ≤ max 1 ‖κlim‖ * (C * (2 * (1 + c ^ 2) * K₀ / (1 + ‖z‖ ^ 2))) := by
            gcongr
            · exact le_max_right _ _
            · exact hGlimbound z hzU
        _ = Kc / (1 + ‖z‖ ^ 2) := by rw [hKc]; ring
    exact eq_zero_of_xiOneSidedIdentity hη hdiffB hdomA hdomB hlimid q
  -- choose a modulation off the zeros of the bump transform
  have hGzero : ∀ q : XiZeroCopy, Glim (xiSpectralPoint q) = 0 := by
    intro q
    by_contra hne
    have hvan : ∀ c : ℝ, suzukiSmoothFourier b ((c : ℂ) - xiSpectralPoint q) = 0 := by
      intro c
      exact (mul_eq_zero.mp (hAzero c q)).resolve_left hne
    have han : AnalyticOnNhd ℂ (suzukiSmoothFourier b) univ :=
      hbdiff.differentiableOn.analyticOnNhd isOpen_univ
    set z₀ : ℂ := -xiSpectralPoint q with hz₀
    have hfreq : ∃ᶠ w in 𝓝[≠] z₀, suzukiSmoothFourier b w = 0 := by
      have hseq : Tendsto (fun n : ℕ => z₀ + ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop (𝓝[≠] z₀) := by
        apply tendsto_nhdsWithin_iff.mpr
        constructor
        · have h1 : Tendsto (fun n : ℕ => (1 / ((n : ℝ) + 1) : ℝ)) atTop (𝓝 0) :=
            tendsto_one_div_add_atTop_nhds_zero_nat
          have h2 : Tendsto (fun n : ℕ => ((1 / ((n : ℝ) + 1) : ℝ) : ℂ)) atTop
              (𝓝 ((0 : ℝ) : ℂ)) :=
            (Complex.continuous_ofReal.tendsto 0).comp h1
          rw [ofReal_zero] at h2
          simpa using (tendsto_const_nhds (x := z₀)).add h2
        · refine Eventually.of_forall fun n => ?_
          simp only [mem_compl_iff, mem_singleton_iff, add_eq_left, ofReal_eq_zero]
          positivity
      refine hseq.frequently (Frequently.of_forall fun n => ?_)
      have := hvan (1 / ((n : ℝ) + 1))
      rw [hz₀]
      convert this using 2
      ring
    have hall := han.eqOn_zero_of_preconnected_of_frequently_eq_zero isPreconnected_univ
      (mem_univ z₀) hfreq (mem_univ 0)
    exact hb0 hall
  -- the limit has only real zeros in the strip
  apply riemannHypothesis_of_xiSpectralPoint_real
  intro q
  have hS : IsClosed {w : ℂ | w.im = 0} := isClosed_eq Complex.continuous_im continuous_const
  have him := CCMXiStrip.zero_mem_closed_of_tendstoLocallyUniformlyOn (S := {w : ℂ | w.im = 0})
    hUopen (convex_xiOneSidedStrip η).isPreconnected hconv (hGlimdiff.analyticOnNhd hUopen)
    (Eventually.of_forall fun k => hGdiff _) hS
    (Eventually.of_forall fun k w hw hzero => hGreal _ w hw hzero)
    h0U (by rw [hGlim0]; exact one_ne_zero) (hγU q) (hGzero q)
  refine ⟨(xiSpectralPoint q).re, ?_⟩
  apply Complex.ext
  · simp
  · simpa using him

end

end RHTower
