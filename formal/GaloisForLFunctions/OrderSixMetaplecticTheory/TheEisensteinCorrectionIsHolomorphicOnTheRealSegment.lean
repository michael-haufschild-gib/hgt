import GaloisForLFunctions.OrderSixMetaplecticTheory.TheCubicResolventHasSimplePolesOnTheRealSegment
import GaloisForLFunctions.OrderSixMetaplecticTheory.TheSeedDefectReadsTheConstantTerm
import GaloisForLFunctions.SpectralTheoryOfTheCubicCover.TheConstantTermContinuesAcrossFourThirds

/-!
# The Eisenstein correction is holomorphic on the real segment

The cubic Eisenstein series is continued as `E(s) = seed(s) − Corr(s)`,
`Corr(s) = R(s(2 − s)) defect(s)` (MMD), analytic off the real axis. On the real segment the resolvent
has simple poles at the eigenvalues `μ = s₀(2 − s₀) ∈ [0, 1)` with residue the eigenprojection `Π_μ`
(`TheCubicResolventHasSimplePolesOnTheRealSegment`). None of them is seen by the correction except at
`4/3`:

* `inner_seedDefect_correction_eq`: on `Re s > 1`, `Im s > 0`, `⟨defect(s₀), Corr(s)⟩ = Ψ(s)`, the explicit
  pairing of the seed defect with the constant term `v^s + (π/(s − 1))φ(s)v^{2−s}` of `E(s)` on heights
  `[5, 6]`; `Ψ` is holomorphic on `Re s > 1` off `4/3`, the only pole of the scattering coefficient `φ`.
* `eigenProjection_seedDefect_eq_zero`: for real `1 < s₀ ≤ 2`, `s₀ ≠ 4/3`, `Π_μ defect(s₀) = 0`:
  `(μ − s(2 − s))⟨defect(s₀), Corr(s)⟩` tends to `(μ + 1)⟨defect(s₀), Π_μ defect(s₀)⟩` and to
  `0 · Ψ(s₀)` as `s → s₀` from above.
* `correction_removable`: for real `s₀ > 1`, `s₀ ≠ 4/3`, `Corr` agrees near `s₀` (off `s₀`) with a function
  analytic at `s₀`; for `s₀ > 2` the pencil is coercive.

So the eigenvalues of the cubic cover in `[0, 1)` other than `8/9` are invisible to the seed: the
continued Eisenstein series has no singularity on the real segment `s > 1` except `4/3`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators Classical InnerProductSpace ComplexConjugate MatrixGroups

namespace GaloisForLFunctions.OrderSixMetaplecticTheory

open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein MetaplecticMobiusDescent.CubicKubota
  MetaplecticMobiusDescent.CubicEisenstein SpectralTheoryOfTheCubicCover

/-- The seed defect with cutoff `[5, 6]`. -/
abbrev seedDefect (s : ℂ) : KernelQuotientL2 := kernelL2Defect 5 6 (by norm_num) (by norm_num) s

/-- The `L²` correction `R(s(2 − s)) defect(s)` with cutoff `[5, 6]`. -/
abbrev correction (s : ℂ) : KernelQuotientL2 :=
  kernelEisensteinL2Correction 5 6 (by norm_num) (by norm_num) s

theorem correction_eq (s : ℂ) :
    correction s = kernelSpectralResolvent (kernelEisensteinSpectralParameter s) (seedDefect s) := rfl

/-! ### Mellin integrals over compact intervals are entire -/

/-- `s ↦ ∫_a^b h(v) v^s dv` is entire for `h` continuous on `[a, b]`, `0 < a`. -/
theorem differentiable_integral_Icc_cpow {a b : ℝ} (ha : 0 < a) (h : ℝ → ℂ)
    (hh : ContinuousOn h (Set.Icc a b)) :
    Differentiable ℂ (fun s : ℂ => ∫ v in Set.Icc a b, h v * (v : ℂ) ^ s) := by
  intro s₀
  have hpos : ∀ v ∈ Set.Icc a b, 0 < v := fun v hv => lt_of_lt_of_le ha hv.1
  have hslit : ∀ v ∈ Set.Icc a b, ((v : ℝ) : ℂ) ∈ Complex.slitPlane := fun v hv =>
    Complex.ofReal_mem_slitPlane.mpr (hpos v hv)
  -- the derivative `h(v) v^s log v` is jointly continuous on `closedBall s₀ 1 × [a, b]`
  have hjoint : ContinuousOn (fun p : ℂ × ℝ => h p.2 * ((p.2 : ℂ) ^ p.1 * Complex.log p.2))
      (Metric.closedBall s₀ 1 ×ˢ Set.Icc a b) := by
    intro p hp
    refine ContinuousWithinAt.mul ((hh p.2 hp.2).comp continuousWithinAt_snd fun q hq => hq.2) ?_
    refine ContinuousAt.continuousWithinAt (ContinuousAt.mul ?_ ?_)
    · exact (Complex.continuous_ofReal.continuousAt.comp continuousAt_snd).cpow continuousAt_fst
        (hslit p.2 hp.2)
    · exact (Complex.continuous_ofReal.continuousAt.comp continuousAt_snd).clog (hslit p.2 hp.2)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall s₀ 1).prod isCompact_Icc).exists_bound_of_continuousOn hjoint
  have hcont : ∀ s : ℂ, ContinuousOn (fun v : ℝ => h v * (v : ℂ) ^ s) (Set.Icc a b) := fun s =>
    hh.mul fun v hv => ((continuousAt_cpow_const (hslit v hv)).comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hderiv : ContinuousOn (fun v : ℝ => h v * ((v : ℂ) ^ s₀ * Complex.log v)) (Set.Icc a b) := by
    intro v hv
    have := hjoint (s₀, v) ⟨Metric.mem_closedBall_self zero_le_one, hv⟩
    exact this.comp (Continuous.continuousWithinAt (by fun_prop)) fun w hw =>
      ⟨Metric.mem_closedBall_self zero_le_one, hw⟩
  haveI : IsFiniteMeasure (volume.restrict (Set.Icc a b)) := isFiniteMeasure_restrict.mpr (by simp)
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := volume.restrict (Set.Icc a b))
    (F := fun s v => h v * (v : ℂ) ^ s) (x₀ := s₀) (s := Metric.ball s₀ 1)
    (bound := fun _ => C) (Metric.ball_mem_nhds s₀ one_pos)
    (Eventually.of_forall fun s => (hcont s).aestronglyMeasurable measurableSet_Icc)
    ((hcont s₀).integrableOn_compact isCompact_Icc)
    (hderiv.aestronglyMeasurable measurableSet_Icc)
    ((ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun v hv s hs =>
      hC (s, v) ⟨Metric.ball_subset_closedBall hs, hv⟩))
    (integrable_const C)
    ((ae_restrict_iff' measurableSet_Icc).mpr (Eventually.of_forall fun v hv s _ => by
      have hv0 : ((v : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (hpos v hv).ne'
      exact ((Complex.hasStrictDerivAt_const_cpow (Or.inl hv0)).hasDerivAt).const_mul (h v)))
  exact key.2.differentiableAt

/-! ### The explicit pairing `Ψ` -/

/-- The seed-defect profile on `[5, 6]` is continuous. -/
theorem continuousOn_cuspSeedDefectProfile (s₀ : ℂ) :
    ContinuousOn (cuspSeedDefectProfile 5 6 s₀) (Set.Icc (5 : ℝ) 6) := by
  rw [continuousOn_iff_continuous_restrict]
  have he : (Set.Icc (5 : ℝ) 6).restrict (cuspSeedDefectProfile 5 6 s₀) =
      compactDefectProfile 5 6 (by norm_num) s₀ := by
    funext v
    exact (compactDefectProfile_apply 5 6 (by norm_num) s₀ v).symm
  rw [he]
  exact (compactDefectProfile 5 6 (by norm_num) s₀).continuous

theorem continuousOn_inv_cube : ContinuousOn (fun v : ℝ => ((v : ℂ) ^ 3)⁻¹) (Set.Icc (5 : ℝ) 6) := by
  intro v hv
  have hv0 : ((v : ℝ) : ℂ) ^ 3 ≠ 0 := pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr (by linarith [hv.1]))
  exact ((Complex.continuous_ofReal.pow 3).continuousAt.inv₀ hv0).continuousWithinAt

/-- The incoming part `A(s) = ∫_5^6 star(d_{s₀}(v)) (v^s − χ(v)v^s) v^{−3} dv`. -/
def incomingPairing (s₀ s : ℂ) : ℂ :=
  ∫ v in Set.Icc (5 : ℝ) 6, star (cuspSeedDefectProfile 5 6 s₀ v) *
    ((v : ℂ) ^ s - cuspSeedProfile 5 6 s v) / (v : ℂ) ^ 3

/-- The outgoing part `B(s) = ∫_5^6 star(d_{s₀}(v)) v^{2−s} v^{−3} dv`. -/
def outgoingPairing (s₀ s : ℂ) : ℂ :=
  ∫ v in Set.Icc (5 : ℝ) 6, star (cuspSeedDefectProfile 5 6 s₀ v) * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3

theorem incomingPairing_differentiable (s₀ : ℂ) : Differentiable ℂ (incomingPairing s₀) := by
  have hd := differentiable_integral_Icc_cpow (a := 5) (b := 6) (by norm_num)
    (fun v => star (cuspSeedDefectProfile 5 6 s₀ v) * (1 - (cuspTransition 5 6 v : ℂ)) * ((v : ℂ) ^ 3)⁻¹)
    (((continuousOn_cuspSeedDefectProfile s₀).star.mul
      (continuousOn_const.sub (Complex.continuous_ofReal.comp
        (cuspTransition_contDiff 5 6).continuous).continuousOn)).mul continuousOn_inv_cube)
  convert hd using 1
  funext s
  refine setIntegral_congr_fun (measurableSet_Icc : MeasurableSet (Set.Icc (5 : ℝ) 6)) fun v hv => ?_
  have hp : 0 < v := by linarith [hv.1]
  have hv0 : ((v : ℝ) : ℂ) ^ 3 ≠ 0 := pow_ne_zero 3 (Complex.ofReal_ne_zero.mpr hp.ne')
  simp only [cuspSeedProfile, positiveHeightPower_eq_cpow s v hp]
  field_simp

theorem outgoingPairing_differentiable (s₀ : ℂ) : Differentiable ℂ (outgoingPairing s₀) := by
  have hd := differentiable_integral_Icc_cpow (a := 5) (b := 6) (by norm_num)
    (fun v => star (cuspSeedDefectProfile 5 6 s₀ v) * ((v : ℂ) ^ 3)⁻¹)
    ((continuousOn_cuspSeedDefectProfile s₀).star.mul continuousOn_inv_cube)
  have hc : Differentiable ℂ (fun s : ℂ => 2 - s) := by fun_prop
  have he : outgoingPairing s₀ = (fun t : ℂ => ∫ v in Set.Icc (5 : ℝ) 6,
      star (cuspSeedDefectProfile 5 6 s₀ v) * ((v : ℂ) ^ 3)⁻¹ * (v : ℂ) ^ t) ∘ (fun s : ℂ => 2 - s) := by
    funext s
    simp only [Function.comp_apply]
    refine setIntegral_congr_fun (measurableSet_Icc : MeasurableSet (Set.Icc (5 : ℝ) 6)) fun v hv => ?_
    simp only [div_eq_mul_inv]
    ring
  rw [he]
  exact hd.comp hc

/-- The continued scattering factor `(π/(s − 1)) φ(s)`, `φ(s) = clearedScattering(s)/(s − 4/3)`. -/
def scatteringFactorCont (s : ℂ) : ℂ := (Real.pi : ℂ) / (s - 1) * (clearedScattering s / (s - 4 / 3))

theorem scatteringFactorCont_analyticAt {s : ℂ} (hs : 1 < s.re) (h43 : s ≠ 4 / 3) :
    AnalyticAt ℂ scatteringFactorCont s := by
  have hs1 : s - 1 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hc : AnalyticAt ℂ clearedScattering s :=
    clearedScattering_differentiableOn.analyticAt
      ((isOpen_lt continuous_const Complex.continuous_re).mem_nhds hs)
  have h43' : s - 4 / 3 ≠ 0 := sub_ne_zero.mpr h43
  unfold scatteringFactorCont
  exact (analyticAt_const.div (analyticAt_id.sub analyticAt_const) hs1).mul
    (hc.div (analyticAt_id.sub analyticAt_const) h43')

/-- The number of sheets of the kernel cover. -/
abbrev sheets : ℂ := (Nat.card (IntegralCoverCosets globalKubotaKernel levelThree) : ℂ)

/-- **The explicit pairing** `Ψ(s) = K |P| (A(s) + B(s) (π/(s − 1)) φ(s))`. -/
def defectPairing (s₀ s : ℂ) : ℂ :=
  sheets * periodArea * (incomingPairing s₀ s + outgoingPairing s₀ s * scatteringFactorCont s)

theorem defectPairing_analyticAt (s₀ : ℂ) {s : ℂ} (hs : 1 < s.re) (h43 : s ≠ 4 / 3) :
    AnalyticAt ℂ (defectPairing s₀) s := by
  unfold defectPairing
  exact analyticAt_const.mul (((incomingPairing_differentiable s₀).analyticAt s).add
    (((outgoingPairing_differentiable s₀).analyticAt s).mul (scatteringFactorCont_analyticAt hs h43)))

/-- For `Re s > 2` the pairing of the defect with `E(s) − seed(s)` is `Ψ(s)`. -/
theorem integral_star_defect_eisensteinRemainder_eq_defectPairing (s₀ s : ℂ) (hs : 2 < s.re) :
    (∫ q, star (kernelQuotientDefect 5 6 s₀ q) *
        kernelLift (eisensteinRemainder s) (eisensteinRemainder_automorphy s hs) q
        ∂integralQuotientVolume globalKubotaKernel) = defectPairing s₀ s := by
  rw [integral_star_defect_eisensteinRemainder s₀ s hs]
  have h43 : s - 4 / 3 ≠ 0 := by
    intro h
    have := congrArg Complex.re h
    simp at this
    linarith
  have hsc : scatteringCoefficient s 0 = clearedScattering s / (s - 4 / 3) := by
    rw [eq_div_iff h43, mul_comm]
    exact sub_mul_scatteringCoefficient (by linarith : (4 : ℝ) / 3 < s.re)
  have hcI : ∀ f : ℝ → ℂ, ContinuousOn f (Set.Icc (5 : ℝ) 6) →
      IntegrableOn f (Set.Icc (5 : ℝ) 6) volume := fun f hf => hf.integrableOn_compact isCompact_Icc
  have hpow : ∀ t : ℂ, ContinuousOn (fun v : ℝ => (v : ℂ) ^ t) (Set.Icc (5 : ℝ) 6) := fun t v hv =>
    ((continuousAt_cpow_const (Complex.ofReal_mem_slitPlane.mpr (by linarith [hv.1]))).comp
      Complex.continuous_ofReal.continuousAt).continuousWithinAt
  have hprof : ContinuousOn (fun v : ℝ => cuspSeedProfile 5 6 s v) (Set.Icc (5 : ℝ) 6) := by
    have : Set.EqOn (fun v : ℝ => cuspSeedProfile 5 6 s v)
        (fun v => (cuspTransition 5 6 v : ℂ) * (v : ℂ) ^ s) (Set.Icc (5 : ℝ) 6) := fun v hv => by
      simp only [cuspSeedProfile, positiveHeightPower_eq_cpow s v (by linarith [hv.1])]
    exact ContinuousOn.congr ((Complex.continuous_ofReal.comp
      (cuspTransition_contDiff 5 6).continuous).continuousOn.mul (hpow s)) this
  have hD := (continuousOn_cuspSeedDefectProfile s₀).star
  have h1 : IntegrableOn (fun v : ℝ => star (cuspSeedDefectProfile 5 6 s₀ v) *
      ((v : ℂ) ^ s - cuspSeedProfile 5 6 s v) / (v : ℂ) ^ 3) (Set.Icc (5 : ℝ) 6) volume := by
    apply hcI
    have := (hD.mul ((hpow s).sub hprof)).mul continuousOn_inv_cube
    exact this.congr fun v _ => by simp [div_eq_mul_inv]
  have h2 : IntegrableOn (fun v : ℝ => star (cuspSeedDefectProfile 5 6 s₀ v) * (v : ℂ) ^ (2 - s) /
      (v : ℂ) ^ 3) (Set.Icc (5 : ℝ) 6) volume := by
    apply hcI
    have := (hD.mul (hpow (2 - s))).mul continuousOn_inv_cube
    exact this.congr fun v _ => by simp [div_eq_mul_inv]
  have hsplit : (fun v : ℝ => star (cuspSeedDefectProfile 5 6 s₀ v) *
      (((v : ℂ) ^ s - cuspSeedProfile 5 6 s v) +
        (v : ℂ) ^ (2 - s) * ((Real.pi : ℂ) / (s - 1) * scatteringCoefficient s 0)) / (v : ℂ) ^ 3) =
      fun v => star (cuspSeedDefectProfile 5 6 s₀ v) * ((v : ℂ) ^ s - cuspSeedProfile 5 6 s v) /
          (v : ℂ) ^ 3 +
        star (cuspSeedDefectProfile 5 6 s₀ v) * (v : ℂ) ^ (2 - s) / (v : ℂ) ^ 3 *
          ((Real.pi : ℂ) / (s - 1) * scatteringCoefficient s 0) := by
    funext v
    ring
  rw [hsplit, integral_add h1 (h2.mul_const _), integral_mul_const]
  unfold defectPairing incomingPairing outgoingPairing scatteringFactorCont
  rw [hsc]

/-! ### The pairing with the correction -/

/-- For `Re s > 4`, `Im s > 0`: `⟨defect(s₀), Corr(s)⟩` is the pairing with `E(s) − seed(s)`. -/
theorem inner_seedDefect_correction_initial (s₀ s : ℂ) (hs : 4 < s.re) (hi : 0 < s.im) :
    inner ℂ (seedDefect s₀) (correction s) = defectPairing s₀ s := by
  rw [← integral_star_defect_eisensteinRemainder_eq_defectPairing s₀ s (by linarith), L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [kernelL2Defect_ae_eq 5 6 (by norm_num) (by norm_num) s₀,
    kernelEisensteinL2Correction_initial_overlap 5 6 (by norm_num) (by norm_num) s hs hi] with q hd hc
  rw [hd, hc, RCLike.inner_apply, starRingEnd_apply]
  rw [mul_comm]
  congr 1
  induction q using Quotient.inductionOn with
  | _ w => rfl

/-- The open set `Re s > 1`, `Im s > 0`. -/
def upperStrip : Set ℂ := {s | 1 < s.re ∧ 0 < s.im}

theorem upperStrip_isOpen : IsOpen upperStrip :=
  (isOpen_lt continuous_const Complex.continuous_re).inter (isOpen_lt continuous_const Complex.continuous_im)

/-- A convex combination of two numbers above `c` is above `c`. -/
theorem lt_convex_comb {a b x y c : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hab : a + b = 1) (hx : c < x)
    (hy : c < y) : c < a * x + b * y := by
  rcases ha.eq_or_lt with h | h
  · subst h
    have hb1 : b = 1 := by linarith
    subst hb1
    simpa using hy
  · have h1 : a * c < a * x := mul_lt_mul_of_pos_left hx h
    have h2 : b * c ≤ b * y := mul_le_mul_of_nonneg_left hy.le hb
    have hc : a * c + b * c = c := by rw [← add_mul, hab, one_mul]
    linarith

theorem upperStrip_isPreconnected : IsPreconnected upperStrip := by
  apply Convex.isPreconnected
  intro x hx y hy a b ha hb hab
  refine ⟨?_, ?_⟩
  · simp only [Complex.add_re, Complex.smul_re, smul_eq_mul]
    exact lt_convex_comb ha hb hab hx.1 hy.1
  · simp only [Complex.add_im, Complex.smul_im, smul_eq_mul]
    exact lt_convex_comb ha hb hab hx.2 hy.2

/-- **The pairing continues.** On `Re s > 1`, `Im s > 0`: `⟨defect(s₀), Corr(s)⟩ = Ψ(s)`. -/
theorem inner_seedDefect_correction_eq (s₀ : ℂ) :
    Set.EqOn (fun s => inner ℂ (seedDefect s₀) (correction s)) (defectPairing s₀) upperStrip := by
  have hf : AnalyticOnNhd ℂ (fun s => inner ℂ (seedDefect s₀) (correction s)) upperStrip := by
    intro s hs
    have hre : s.re ≠ 1 := ne_of_gt hs.1
    exact ((innerSL ℂ (seedDefect s₀)).analyticAt _).comp
      (kernelEisensteinL2Correction_analyticAt_nonreal 5 6 (by norm_num) (by norm_num) s hre
        (ne_of_gt hs.2))
  have hg : AnalyticOnNhd ℂ (defectPairing s₀) upperStrip := by
    intro s hs
    refine defectPairing_analyticAt s₀ hs.1 ?_
    intro h
    have := hs.2
    rw [h] at this
    simp at this
  have h₀ : (5 + Complex.I : ℂ) ∈ upperStrip := by
    refine ⟨?_, ?_⟩ <;> simp
  refine hf.eqOn_of_preconnected_of_eventuallyEq hg upperStrip_isPreconnected h₀ ?_
  have hopen : IsOpen {s : ℂ | 4 < s.re ∧ 0 < s.im} :=
    (isOpen_lt continuous_const Complex.continuous_re).inter
      (isOpen_lt continuous_const Complex.continuous_im)
  filter_upwards [hopen.mem_nhds (show (5 + Complex.I : ℂ) ∈ {s : ℂ | 4 < s.re ∧ 0 < s.im} by
    refine ⟨?_, ?_⟩ <;> norm_num)] with s hs
  exact inner_seedDefect_correction_initial s₀ s hs.1 hs.2

/-! ### The cancellation on the real segment -/

/-- `s₀(2 − s₀) − s(2 − s) = (s − s₀)(s + s₀ − 2)`. -/
theorem spectralParameter_sub (s₀ s : ℂ) :
    s₀ * (2 - s₀) - kernelEisensteinSpectralParameter s = (s - s₀) * (s + s₀ - 2) := by
  unfold kernelEisensteinSpectralParameter
  ring

theorem spectralParameter_continuous : Continuous kernelEisensteinSpectralParameter := by
  unfold kernelEisensteinSpectralParameter
  fun_prop

theorem spectralParameter_analyticAt (s : ℂ) : AnalyticAt ℂ kernelEisensteinSpectralParameter s := by
  unfold kernelEisensteinSpectralParameter
  fun_prop

theorem upper_nhdsWithin_neBot (s₀ : ℝ) : (𝓝[{s : ℂ | 0 < s.im}] (s₀ : ℂ)).NeBot := by
  rw [← mem_closure_iff_nhdsWithin_neBot, Metric.mem_closure_iff]
  intro ε hε
  refine ⟨(s₀ : ℂ) + ((ε / 2 : ℝ) : ℂ) * Complex.I, ?_, ?_⟩
  · simp only [Set.mem_setOf_eq, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_im,
      Complex.I_re, Complex.ofReal_re, mul_one, mul_zero, zero_add, add_zero]
    linarith
  · rw [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_mul, Complex.norm_I, mul_one,
      Complex.norm_real, Real.norm_of_nonneg (by linarith)]
    linarith

/-- Off `s₀`, near `s₀ > 1`, the spectral parameter `s(2 − s)` avoids `s₀(2 − s₀)`. -/
theorem spectralParameter_eventually_ne (s₀ : ℝ) (h1 : 1 < s₀) :
    ∀ᶠ s in 𝓝[≠] (s₀ : ℂ), kernelEisensteinSpectralParameter s ≠ ((s₀ * (2 - s₀) : ℝ) : ℂ) := by
  have hne : ∀ᶠ s in 𝓝 (s₀ : ℂ), s + (s₀ : ℂ) - 2 ≠ 0 := by
    have hc : ContinuousAt (fun s : ℂ => s + (s₀ : ℂ) - 2) (s₀ : ℂ) := by fun_prop
    refine hc.eventually_ne ?_
    have : (2 * s₀ - 2 : ℝ) ≠ 0 := by linarith
    intro h
    apply this
    have h' := congrArg Complex.re h
    simp at h'
    linarith
  filter_upwards [hne.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs hs0 h
  have hsub := spectralParameter_sub s₀ s
  rw [h] at hsub
  push_cast at hsub
  rw [sub_self] at hsub
  exact (mul_ne_zero (sub_ne_zero.mpr hs0) hs) hsub.symm

theorem spectralParameter_tendsto (s₀ : ℝ) (h1 : 1 < s₀) :
    Tendsto kernelEisensteinSpectralParameter (𝓝[≠] (s₀ : ℂ)) (𝓝[≠] ((s₀ * (2 - s₀) : ℝ) : ℂ)) := by
  have hval : kernelEisensteinSpectralParameter (s₀ : ℂ) = ((s₀ * (2 - s₀) : ℝ) : ℂ) := by
    unfold kernelEisensteinSpectralParameter
    push_cast
    ring
  refine tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _ ?_
    (spectralParameter_eventually_ne s₀ h1)
  rw [← hval]
  exact (spectralParameter_continuous.tendsto _).mono_left nhdsWithin_le_nhds

/-- **The decomposition near a real point.** For `1 < s₀ ≤ 2`, `μ = s₀(2 − s₀)`, off `s₀`:
`Corr(s) = ((μ + 1)/(μ − s(2 − s))) Π_μ defect(s) + R_reg(s(2 − s)) defect(s)`. -/
theorem correction_eventually_eq (s₀ : ℝ) (h1 : 1 < s₀) (h2 : s₀ ≤ 2) :
    ∀ᶠ s in 𝓝[≠] (s₀ : ℂ), correction s =
      ((((s₀ * (2 - s₀) : ℝ) : ℂ) + 1) / (((s₀ * (2 - s₀) : ℝ) : ℂ) - kernelEisensteinSpectralParameter s)) •
          eigenProjection (s₀ * (2 - s₀)) (seedDefect s) +
        regularResolvent (s₀ * (2 - s₀)) (kernelEisensteinSpectralParameter s) (seedDefect s) := by
  have hμ0 : 0 ≤ s₀ * (2 - s₀) := mul_nonneg (by linarith) (by linarith)
  have hμ1 : s₀ * (2 - s₀) < 1 := by nlinarith [sq_pos_of_pos (sub_pos.mpr h1)]
  filter_upwards [(spectralParameter_tendsto s₀ h1).eventually
    (resolvent_eventually_eq (s₀ * (2 - s₀)) hμ0 hμ1)] with s hs
  rw [correction_eq, hs]
  rfl

/-- **The eigenvalues on the real segment are invisible to the seed.** For `1 < s₀ ≤ 2`, `s₀ ≠ 4/3`,
`μ = s₀(2 − s₀)`: `Π_μ defect(s₀) = 0`. -/
theorem eigenProjection_seedDefect_eq_zero (s₀ : ℝ) (h1 : 1 < s₀) (h2 : s₀ ≤ 2) (h43 : s₀ ≠ 4 / 3) :
    eigenProjection (s₀ * (2 - s₀)) (seedDefect s₀) = 0 := by
  set μ : ℝ := s₀ * (2 - s₀) with hμdef
  have hμ0 : 0 ≤ μ := mul_nonneg (by linarith) (by linarith)
  have hμ1 : μ < 1 := by nlinarith [sq_pos_of_pos (sub_pos.mpr h1)]
  have hval : kernelEisensteinSpectralParameter (s₀ : ℂ) = (μ : ℂ) := by
    unfold kernelEisensteinSpectralParameter
    rw [hμdef]
    push_cast
    ring
  set g := seedDefect (s₀ : ℂ)
  set L := 𝓝[{s : ℂ | 0 < s.im}] (s₀ : ℂ)
  haveI : L.NeBot := upper_nhdsWithin_neBot s₀
  have hL : L ≤ 𝓝[≠] (s₀ : ℂ) := nhdsWithin_mono _ fun s hs h => by
    rw [Set.mem_singleton_iff] at h
    rw [Set.mem_setOf_eq, h, Complex.ofReal_im] at hs
    exact lt_irrefl 0 hs
  have hdefect : Continuous seedDefect := (kernelL2Defect_entire 5 6 (by norm_num) (by norm_num)).continuous
  -- the limit through the explicit pairing `Ψ`
  have hlim1 : Tendsto (fun s => ((μ : ℂ) - kernelEisensteinSpectralParameter s) *
      inner ℂ g (correction s)) L (𝓝 0) := by
    have hre : (1 : ℝ) < (s₀ : ℂ).re := by simpa using h1
    have hΨ : ContinuousAt (defectPairing (s₀ : ℂ)) (s₀ : ℂ) :=
      (defectPairing_analyticAt _ hre (fun h => h43 (by
        have := congrArg Complex.re h
        norm_num at this
        exact this))).continuousAt
    have h0 : Tendsto (fun s => ((μ : ℂ) - kernelEisensteinSpectralParameter s) * defectPairing s₀ s)
        (𝓝 (s₀ : ℂ)) (𝓝 (((μ : ℂ) - kernelEisensteinSpectralParameter s₀) * defectPairing s₀ s₀)) :=
      ((continuous_const.sub spectralParameter_continuous).continuousAt.mul hΨ).tendsto
    rw [hval, sub_self, zero_mul] at h0
    refine (h0.mono_left nhdsWithin_le_nhds).congr' ?_
    have hre' : ∀ᶠ s in 𝓝 (s₀ : ℂ), 1 < s.re :=
      (isOpen_lt continuous_const Complex.continuous_re).mem_nhds hre
    filter_upwards [hre'.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with s hs1 hs2
    rw [show inner ℂ g (correction s) = defectPairing s₀ s from
      inner_seedDefect_correction_eq (s₀ : ℂ) ⟨hs1, hs2⟩]
  -- the limit through the resolvent decomposition
  have hR : ContinuousAt (fun s => regularResolvent μ (kernelEisensteinSpectralParameter s) (seedDefect s))
      (s₀ : ℂ) :=
    ((regularResolvent_analyticAt μ hμ0 hμ1).continuousAt.comp_of_eq
      spectralParameter_continuous.continuousAt hval).clm_apply hdefect.continuousAt
  have hP : ContinuousAt (fun s => eigenProjection μ (seedDefect s)) (s₀ : ℂ) :=
    ((eigenProjection μ).continuous.comp hdefect).continuousAt
  have hlim2 : Tendsto (fun s => ((μ : ℂ) - kernelEisensteinSpectralParameter s) *
      inner ℂ g (correction s)) L (𝓝 (((μ : ℂ) + 1) * inner ℂ g (eigenProjection μ g))) := by
    have h0 : Tendsto (fun s => ((μ : ℂ) + 1) * inner ℂ g (eigenProjection μ (seedDefect s)) +
        ((μ : ℂ) - kernelEisensteinSpectralParameter s) *
          inner ℂ g (regularResolvent μ (kernelEisensteinSpectralParameter s) (seedDefect s)))
        (𝓝 (s₀ : ℂ)) (𝓝 (((μ : ℂ) + 1) * inner ℂ g (eigenProjection μ (seedDefect s₀)) +
          ((μ : ℂ) - kernelEisensteinSpectralParameter s₀) *
            inner ℂ g (regularResolvent μ (kernelEisensteinSpectralParameter s₀) (seedDefect s₀)))) :=
      ((continuousAt_const.mul (continuousAt_const.inner hP)).add
        ((continuous_const.sub spectralParameter_continuous).continuousAt.mul
          (continuousAt_const.inner hR))).tendsto
    rw [hval, sub_self, zero_mul, add_zero] at h0
    refine (h0.mono_left (hL.trans nhdsWithin_le_nhds)).congr' ?_
    filter_upwards [hL (correction_eventually_eq s₀ h1 h2), hL (spectralParameter_eventually_ne s₀ h1)]
      with s hs hne
    rw [hs, inner_add_right, inner_smul_right, mul_add, ← mul_assoc,
      mul_div_cancel₀ _ (sub_ne_zero.mpr (Ne.symm hne))]
  have huniq := tendsto_nhds_unique hlim2 hlim1
  have hμ1' : (μ : ℂ) + 1 ≠ 0 := by
    have : (μ + 1 : ℝ) ≠ 0 := by linarith
    exact_mod_cast this
  exact eigenProjection_eq_zero_of_inner μ g ((mul_eq_zero.mp huniq).resolve_left hμ1')

/-- **The Eisenstein correction is holomorphic on the real segment.** For real `s₀ > 1`,
`s₀ ≠ 4/3`, the correction agrees on a punctured neighbourhood of `s₀` with a function analytic at
`s₀`. -/
theorem correction_removable (s₀ : ℝ) (h1 : 1 < s₀) (h43 : s₀ ≠ 4 / 3) :
    ∃ C : ℂ → KernelQuotientL2, AnalyticAt ℂ C (s₀ : ℂ) ∧
      ∀ᶠ s in 𝓝[≠] (s₀ : ℂ), C s = correction s := by
  by_cases h2 : s₀ ≤ 2
  · have hμ0 : 0 ≤ s₀ * (2 - s₀) := mul_nonneg (by linarith) (by linarith)
    have hμ1 : s₀ * (2 - s₀) < 1 := by nlinarith [sq_pos_of_pos (sub_pos.mpr h1)]
    have hval : kernelEisensteinSpectralParameter (s₀ : ℂ) = ((s₀ * (2 - s₀) : ℝ) : ℂ) := by
      unfold kernelEisensteinSpectralParameter
      push_cast
      ring
    have hPi := eigenProjection_seedDefect_eq_zero s₀ h1 h2 h43
    have hden : ((s₀ : ℂ) + (s₀ : ℂ) - 2) ≠ 0 := by
      have : (s₀ + s₀ - 2 : ℝ) ≠ 0 := by linarith
      exact_mod_cast this
    have hdiff : Differentiable ℂ seedDefect := kernelL2Defect_entire 5 6 (by norm_num) (by norm_num)
    have hdslope : AnalyticAt ℂ (dslope seedDefect (s₀ : ℂ)) (s₀ : ℂ) :=
      ((Complex.differentiableOn_dslope Filter.univ_mem).mpr hdiff.differentiableOn).analyticAt
        Filter.univ_mem
    refine ⟨fun s : ℂ => ((((s₀ * (2 - s₀) : ℝ) : ℂ) + 1) •
        eigenProjection (s₀ * (2 - s₀)) ((s + (s₀ : ℂ) - 2)⁻¹ • dslope seedDefect (s₀ : ℂ) s) +
      regularResolvent (s₀ * (2 - s₀)) (kernelEisensteinSpectralParameter s) (seedDefect s)), ?_, ?_⟩
    · have hinv : AnalyticAt ℂ (fun s : ℂ => (s + (s₀ : ℂ) - 2)⁻¹) (s₀ : ℂ) :=
        ((analyticAt_id.add analyticAt_const).sub analyticAt_const).inv hden
      have hin : AnalyticAt ℂ (fun s : ℂ => (s + (s₀ : ℂ) - 2)⁻¹ • dslope seedDefect (s₀ : ℂ) s)
          (s₀ : ℂ) := hinv.smul hdslope
      have h1' : AnalyticAt ℂ (fun s : ℂ => ((((s₀ * (2 - s₀) : ℝ) : ℂ) + 1) •
          eigenProjection (s₀ * (2 - s₀)) ((s + (s₀ : ℂ) - 2)⁻¹ • dslope seedDefect (s₀ : ℂ) s)))
          (s₀ : ℂ) :=
        ((((((s₀ * (2 - s₀) : ℝ) : ℂ) + 1) • eigenProjection (s₀ * (2 - s₀))).analyticAt _).comp hin :)
      have hRreg : AnalyticAt ℂ (fun s => regularResolvent (s₀ * (2 - s₀))
          (kernelEisensteinSpectralParameter s)) (s₀ : ℂ) :=
        (regularResolvent_analyticAt _ hμ0 hμ1).comp_of_eq (spectralParameter_analyticAt _) hval
      have h2' : AnalyticAt ℂ (fun s => regularResolvent (s₀ * (2 - s₀))
          (kernelEisensteinSpectralParameter s) (seedDefect s)) (s₀ : ℂ) :=
        ((ContinuousLinearMap.apply ℂ KernelQuotientL2).analyticAt_bilinear
          (seedDefect s₀, regularResolvent (s₀ * (2 - s₀)) (kernelEisensteinSpectralParameter s₀))).comp₂
            (hdiff.analyticAt _) hRreg
      exact h1'.add h2'
    · filter_upwards [correction_eventually_eq s₀ h1 h2, self_mem_nhdsWithin] with s hs hs0
      rw [hs]
      congr 1
      have hs0' : s ≠ (s₀ : ℂ) := hs0
      rw [dslope_of_ne _ hs0', slope_def_module, smul_smul, map_smul, map_sub, hPi, sub_zero,
        smul_smul]
      congr 1
      have hsub := spectralParameter_sub (s₀ : ℂ) s
      have hμc : ((s₀ * (2 - s₀) : ℝ) : ℂ) = (s₀ : ℂ) * (2 - s₀) := by push_cast; ring
      rw [hμc, hsub]
      have hne1 : s - s₀ ≠ 0 := sub_ne_zero.mpr hs0'
      by_cases hne2 : s + s₀ - 2 = 0
      · rw [hne2]
        simp
      · field_simp
  · have h2' : 2 < s₀ := lt_of_not_ge h2
    have hneg : s₀ * (2 - s₀) < 0 := mul_neg_of_pos_of_neg (by linarith) (by linarith)
    refine ⟨correction, ?_, Eventually.of_forall fun _ => rfl⟩
    have hval : kernelEisensteinSpectralParameter (s₀ : ℂ) = ((s₀ * (2 - s₀) : ℝ) : ℂ) := by
      unfold kernelEisensteinSpectralParameter
      push_cast
      ring
    have hU := isUnit_spectralForm_of_neg hneg
    have hinv : AnalyticAt ℂ (fun z => Ring.inverse (kernelSpectralFormOperator z))
        ((s₀ * (2 - s₀) : ℝ) : ℂ) := kernelSpectralFormInverse_analyticAt_of_isUnit _ hU
    have hR : AnalyticAt ℂ kernelSpectralResolvent ((s₀ * (2 - s₀) : ℝ) : ℂ) := by
      change AnalyticAt ℂ (⇑kernelL2SandwichCLM ∘ fun z => Ring.inverse (kernelSpectralFormOperator z)) _
      exact (kernelL2SandwichCLM.analyticAt _).comp hinv
    have hE : AnalyticAt ℂ kernelEisensteinResolvent (s₀ : ℂ) :=
      hR.comp_of_eq (spectralParameter_analyticAt _) hval
    exact ((ContinuousLinearMap.apply ℂ KernelQuotientL2).analyticAt_bilinear
      (seedDefect s₀, kernelEisensteinResolvent s₀)).comp₂
        ((kernelL2Defect_entire 5 6 (by norm_num) (by norm_num)).analyticAt _) hE

end GaloisForLFunctions.OrderSixMetaplecticTheory
