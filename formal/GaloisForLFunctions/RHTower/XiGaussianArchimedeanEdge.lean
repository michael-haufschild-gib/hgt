import GaloisForLFunctions.RHTower.XiGaussianPrimeEdge
import GaloisForLFunctions.RHTower.XiMassArchimedeanUniformBound
import GaloisForLFunctions.RHTower.HardyZ

/-!
# Exact archimedean edge for Gaussian--Hermite tests

The completed archimedean logarithmic derivative is transported from every absolute-Euler line
to the critical line against the centered Gaussian--Hermite test.  The only crossed zero is the
simple factor at `s = 1`, so the infinite contour shift has one exact residue.  Gaussian decay
absorbs the uniform linear digamma bound on both vertical sides.
-/

open Complex Filter MeasureTheory Set Topology intervalIntegral

namespace RHTower

noncomputable section

/-- Completed archimedean source on one horizontal line in centered coordinates. -/
def xiGaussianArchHorizontalIntegrand
    (t : ℝ) (k : ℕ) (y x : ℝ) : ℂ :=
  xiGaussianTestC t k ((x : ℂ) + (y : ℂ) * I) *
    logDeriv archFactor
      (xiMassCenteredArchPoint ((x : ℂ) + (y : ℂ) * I))

/-- Bottom absolute-Euler archimedean source. -/
def xiGaussianBottomArchIntegrand
    (t : ℝ) (k : ℕ) (c x : ℝ) : ℂ :=
  xiGaussianArchHorizontalIntegrand t k (-c) x

/-- Centered critical-line archimedean source. -/
def xiGaussianCenteredArchIntegrand
    (t : ℝ) (k : ℕ) (x : ℝ) : ℂ :=
  xiGaussianArchHorizontalIntegrand t k 0 x

theorem continuous_xiGaussianArchLogDeriv_horizontal
    {y : ℝ} (hy : y < 1 / 2) (hyPole : y ≠ -(1 / 2)) :
    Continuous (fun x : ℝ =>
      logDeriv archFactor
        (xiMassCenteredArchPoint ((x : ℂ) + (y : ℂ) * I))) := by
  let s : ℝ → ℂ := fun x =>
    xiMassCenteredArchPoint ((x : ℂ) + (y : ℂ) * I)
  have hs : Continuous s := by
    dsimp only [s, xiMassCenteredArchPoint]
    fun_prop
  have hsre : ∀ x : ℝ, (s x).re = 1 / 2 - y := by
    intro x
    simp [s, xiMassCenteredArchPoint, Complex.mul_re]
    ring
  have hmaps : MapsTo s univ {z : ℂ | 0 < z.re} := by
    intro x _
    simp only [mem_setOf_eq, hsre]
    linarith
  have hderiv : Continuous (fun x : ℝ => archFactorDeriv (s x)) :=
    continuousOn_archFactorDeriv.comp_continuous hs (fun x => hmaps (mem_univ x))
  have hfactor : Continuous (fun x : ℝ => archFactor (s x)) :=
    archFactor_analyticOnNhd_re_pos.continuousOn.comp_continuous hs
      (fun x => hmaps (mem_univ x))
  have hfactor0 : ∀ x : ℝ, archFactor (s x) ≠ 0 := by
    intro x
    have hs0 : s x ≠ 0 := by
      intro h
      have hre := congrArg Complex.re h
      rw [hsre, Complex.zero_re] at hre
      linarith
    have hs1 : s x ≠ 1 := by
      intro h
      have hre := congrArg Complex.re h
      rw [hsre, Complex.one_re] at hre
      apply hyPole
      linarith
    exact archFactor_ne_zero hs0 hs1
      (Gammaℝ_ne_zero_of_re_pos (by rw [hsre]; linarith))
  rw [show (fun x : ℝ => logDeriv archFactor
      (xiMassCenteredArchPoint ((x : ℂ) + (y : ℂ) * I))) =
      fun x : ℝ => archFactorDeriv (s x) / archFactor (s x) by
    funext x
    rw [logDeriv_apply, (hasDerivAt_archFactor_of_re_pos
      (by rw [hsre]; linarith)).deriv]]
  exact hderiv.div hfactor hfactor0

theorem continuous_xiGaussianArchHorizontalIntegrand
    (t : ℝ) (k : ℕ) {y : ℝ} (hy : y < 1 / 2)
    (hyPole : y ≠ -(1 / 2)) :
    Continuous (xiGaussianArchHorizontalIntegrand t k y) := by
  unfold xiGaussianArchHorizontalIntegrand
  have hprofile : Continuous (fun x : ℝ =>
      xiGaussianTestC t k ((x : ℂ) + (y : ℂ) * I)) := by
    unfold xiGaussianTestC
    fun_prop
  exact hprofile.mul (continuous_xiGaussianArchLogDeriv_horizontal hy hyPole)

/-- Gaussian absorption makes the completed archimedean source integrable on every pole-free
horizontal line between an absolute-Euler line and the critical line. -/
theorem integrable_xiGaussianArchHorizontalIntegrand
    {t c : ℝ} (ht : 0 < t) (hc : 1 / 2 < c) (k : ℕ)
    {y : ℝ} (hy : -c ≤ y ∧ y ≤ 0) (hyPole : y ≠ -(1 / 2)) :
    Integrable (xiGaussianArchHorizontalIntegrand t k y) := by
  let K : ℝ :=
    Real.exp (t * ((1 / 2 - y) - 1 / 2) ^ (2 : ℕ)) *
      Real.exp (t / 2 * ((1 / 2 - y) - 1 / 2) ^ (2 : ℕ)) *
        ((k.factorial : ℝ) / (t / 2) ^ k)
  let C : ℝ := xiMassArchVerticalGrowthConstant
  let M : ℝ := max 2 (1 / 2 + c)
  let S : Set ℝ := {x : ℝ | M ≤ |x|}
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  have hhalf : 0 < t / 2 := by linarith
  have hK : 0 ≤ K := by
    dsimp only [K]
    positivity
  have hC : 0 ≤ C := by
    exact xiMassArchVerticalGrowthConstant_nonneg
  have hzero : Integrable (fun x : ℝ => Real.exp (-(t / 2 * x ^ (2 : ℕ)))) :=
    by simpa [neg_mul] using integrable_exp_neg_mul_sq hhalf
  have honeRaw : Integrable (fun x : ℝ =>
      x * Real.exp (-(t / 2 * x ^ (2 : ℕ)))) :=
    by simpa [neg_mul] using integrable_mul_exp_neg_mul_sq hhalf
  have hone : Integrable (fun x : ℝ =>
      |x| * Real.exp (-(t / 2 * x ^ (2 : ℕ)))) := by
    simpa [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)] using honeRaw.norm
  have hmajor : Integrable (fun x : ℝ =>
      K * Real.exp (-(t / 2 * x ^ (2 : ℕ))) * (C + |x| / 2)) := by
    have hsum := (hzero.const_mul (K * C)).add (hone.const_mul (K / 2))
    apply hsum.congr
    filter_upwards with x
    simp only [Pi.add_apply]
    ring
  have hS : MeasurableSet S := by
    dsimp only [S]
    exact measurableSet_le measurable_const continuous_abs.measurable
  have htail : IntegrableOn (xiGaussianArchHorizontalIntegrand t k y) S := by
    refine hmajor.integrableOn.mono'
      (continuous_xiGaussianArchHorizontalIntegrand t k (by linarith) hyPole).aestronglyMeasurable.restrict
      ?_
    filter_upwards [self_mem_ae_restrict hS] with x hx
    have hprofile0 := norm_xiGaussianTest_vertical_le ht k (1 / 2 - y) x
    have hprofile :
        ‖xiGaussianTestC t k ((x : ℂ) + (y : ℂ) * I)‖ ≤
          K * Real.exp (-(t / 2 * x ^ (2 : ℕ))) := by
      rw [norm_xiGaussianTestC_eq_norm_rotated]
      simpa only [K] using hprofile0
    have harch := norm_logDeriv_archFactor_xiMassArchVertical_le
      (c := c) (R := x) (y := y) hy
      (show max 2 (1 / 2 + c) ≤ |x| by simpa only [M, S, mem_setOf_eq] using hx)
    have hpoint :
        xiMassCenteredArchPoint ((x : ℂ) + (y : ℂ) * I) =
          xiMassArchVerticalEulerPoint x y := by
      rfl
    rw [xiGaussianArchHorizontalIntegrand, norm_mul, hpoint]
    exact mul_le_mul hprofile harch (norm_nonneg _)
      (mul_nonneg hK (Real.exp_pos _).le)
  have hcompact : IntegrableOn (xiGaussianArchHorizontalIntegrand t k y)
      (Icc (-M) M) :=
    (continuous_xiGaussianArchHorizontalIntegrand t k (by linarith) hyPole).integrableOn_Icc
  have hcover : Icc (-M) M ∪ S = univ := by
    ext x
    simp only [mem_union, mem_Icc, mem_univ, iff_true, S, mem_setOf_eq]
    by_cases h : |x| ≤ M
    · exact Or.inl (abs_le.mp h)
    · exact Or.inr (by linarith)
  rw [← integrableOn_univ, ← hcover]
  exact hcompact.union htail

private theorem xiGaussianArchRectangle_subset_domain
    {c R : ℝ} (hc : 1 / 2 < c) (hR : 0 < R) :
    (uIcc ((((-R : ℝ) : ℂ) - c * I)).re ((R : ℂ)).re ×ℂ
      uIcc ((((-R : ℝ) : ℂ) - c * I)).im ((R : ℂ)).im) ⊆
      xiMassArchShiftDomain (c + 1) := by
  intro z hz
  have hre : -R ≤ z.re ∧ z.re ≤ R := by
    have h := (Complex.mem_reProdIm.mp hz).1
    rw [show ((((-R : ℝ) : ℂ) - c * I)).re = -R by simp [Complex.mul_re],
      show ((R : ℂ)).re = R by simp, uIcc_of_le (by linarith)] at h
    exact h
  have him : -c ≤ z.im ∧ z.im ≤ 0 := by
    have h := (Complex.mem_reProdIm.mp hz).2
    rw [show ((((-R : ℝ) : ℂ) - c * I)).im = -c by simp [Complex.mul_im],
      show ((R : ℂ)).im = 0 by simp, uIcc_of_le (by linarith)] at h
    exact h
  change z ∈ xiMassStrip (c + 1) ∧ z.im < 1 / 2
  constructor
  · change |z.im| < c + 1
    rw [abs_lt]
    constructor <;> linarith
  · linarith

/-- Finite Gaussian rectangle extracts exactly the crossed completed archimedean zero. -/
theorem rectIntegral_xiGaussian_mul_archLogDeriv
    {t c R : ℝ} (hc : 1 / 2 < c) (hR : 0 < R) (k : ℕ) :
    rectIntegral
      (fun z => xiGaussianTestC t k z *
        logDeriv archFactor (xiMassCenteredArchPoint z))
      (((-R : ℝ) : ℂ) - c * I) (R : ℂ) =
        2 * Real.pi * xiGaussianTestC t k xiMassArchPole := by
  let z₁ : ℂ := (((-R : ℝ) : ℂ) - c * I)
  let z₂ : ℂ := (R : ℂ)
  let U : Set ℂ := xiMassArchShiftDomain (c + 1)
  let ρ : Unit → ℂ := fun _ => xiMassArchPole
  let m : Unit → ℕ := fun _ => 1
  let h : ℂ → ℂ := xiMassCenteredArchCofactor
  have hsub : (uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im) ⊆ U := by
    simpa only [z₁, z₂, U] using xiGaussianArchRectangle_subset_domain hc hR
  have hin : ∀ i ∈ ({()} : Finset Unit),
      z₁.re < (ρ i).re ∧ (ρ i).re < z₂.re ∧
        z₁.im < (ρ i).im ∧ (ρ i).im < z₂.im := by
    intro i _
    have hi : i = () := Subsingleton.elim _ _
    subst i
    have hz₁re : z₁.re = -R := by simp [z₁, Complex.mul_re]
    have hz₂re : z₂.re = R := by simp [z₂]
    have hz₁im : z₁.im = -c := by simp [z₁, Complex.mul_im]
    have hz₂im : z₂.im = 0 := by simp [z₂]
    have hρre : (ρ ()).re = 0 := by
      simp [ρ, xiMassArchPole]
    have hρim : (ρ ()).im = -(1 / 2) := by
      norm_num [ρ, xiMassArchPole, Complex.div_im, Complex.normSq]
    rw [hz₁re, hz₂re, hz₁im, hz₂im, hρre, hρim]
    constructor
    · linarith
    constructor
    · exact hR
    constructor <;> linarith
  have hres := rectIntegral_mul_logDeriv_boxCount_of_analyticOnNhd
    ({()} : Finset Unit) ρ m
    (f := fun z => archFactor (xiMassCenteredArchPoint z))
    (g := xiGaussianTestC t k) (h := h) (z₁ := z₁) (z₂ := z₂) (U := U)
    (isOpen_xiMassArchShiftDomain (c + 1))
    ((analyticOnNhd_xiGaussianTestC t k).mono (fun _ _ => mem_univ _))
    hin hsub analyticOnNhd_xiMassCenteredArchCofactor
    (fun z hz => xiMassCenteredArchCofactor_ne_zero hz)
    (fun z _ => by
      rw [archFactor_centered_factorization]
      simp only [Finset.prod_singleton, m, ρ, h, pow_one])
  have hcomp : rectIntegral
      (fun z => xiGaussianTestC t k z *
        logDeriv archFactor (xiMassCenteredArchPoint z)) z₁ z₂ =
      (-I) * rectIntegral
        (fun z => xiGaussianTestC t k z *
          logDeriv (fun w => archFactor (xiMassCenteredArchPoint w)) z) z₁ z₂ := by
    let S : Set ℂ := uIcc z₁.re z₂.re ×ℂ uIcc z₁.im z₂.im
    have hsubS : S ⊆ U := by simpa only [S] using hsub
    have hedges : rectIntegral
        (fun z => xiGaussianTestC t k z *
          logDeriv archFactor (xiMassCenteredArchPoint z)) z₁ z₂ =
        rectIntegral
          (fun z => (-I) * (xiGaussianTestC t k z *
            logDeriv (fun w => archFactor (xiMassCenteredArchPoint w)) z)) z₁ z₂ := by
      apply rectIntegral_congr (S := S)
      · intro z hz
        rw [logDeriv_centeredArchFactor_eq_I_mul z
          (xiMassCenteredArchPoint_re_pos (hsubS hz))]
        calc
          xiGaussianTestC t k z * logDeriv archFactor (xiMassCenteredArchPoint z) =
              (-I * I) * (xiGaussianTestC t k z *
                logDeriv archFactor (xiMassCenteredArchPoint z)) := by
            rw [neg_mul, Complex.I_mul_I]
            ring
          _ = -I * (xiGaussianTestC t k z *
                (I * logDeriv archFactor (xiMassCenteredArchPoint z))) := by ring
      · intro x hx
        apply Complex.mem_reProdIm.mpr
        exact ⟨by simpa [Complex.mul_re] using hx,
          by simp [Complex.mul_im]⟩
      · intro x hx
        apply Complex.mem_reProdIm.mpr
        exact ⟨by simpa [Complex.mul_re] using hx,
          by simp [Complex.mul_im]⟩
      · intro y hy
        apply Complex.mem_reProdIm.mpr
        exact ⟨by simp [Complex.mul_re],
          by simpa [Complex.mul_im] using hy⟩
      · intro y hy
        apply Complex.mem_reProdIm.mpr
        exact ⟨by simp [Complex.mul_re],
          by simpa [Complex.mul_im] using hy⟩
    rw [hedges, rectIntegral_const_mul]
  rw [show (((-R : ℝ) : ℂ) - c * I) = z₁ by rfl,
    show (R : ℂ) = z₂ by rfl, hcomp]
  rw [show rectIntegral
      (fun z => xiGaussianTestC t k z *
        logDeriv (fun w => archFactor (xiMassCenteredArchPoint w)) z) z₁ z₂ =
      2 * Real.pi * I * xiGaussianTestC t k xiMassArchPole by
    simpa only [ρ, m, Finset.sum_singleton, Nat.cast_one, one_mul] using hres]
  calc
    -I * (2 * Real.pi * I * xiGaussianTestC t k xiMassArchPole) =
        2 * Real.pi * (-I * I) * xiGaussianTestC t k xiMassArchPole := by ring
    _ = 2 * Real.pi * xiGaussianTestC t k xiMassArchPole := by
      rw [neg_mul, Complex.I_mul_I]
      ring

private theorem abs_le_abs_add_abs_of_mem_uIoc_arch
    {a b y : ℝ} (hy : y ∈ Set.uIoc a b) :
    |y| ≤ |a| + |b| := by
  have hy' : min a b ≤ y ∧ y ≤ max a b := by
    change y ∈ Set.uIcc a b
    exact Set.uIoc_subset_uIcc hy
  rw [abs_le]
  constructor
  · calc
      -(|a| + |b|) ≤ min a b := by
        apply le_min <;> linarith [neg_abs_le a, neg_abs_le b, abs_nonneg a, abs_nonneg b]
      _ ≤ y := hy'.1
  · calc
      y ≤ max a b := hy'.2
      _ ≤ |a| + |b| := by
        apply max_le <;> linarith [le_abs_self a, le_abs_self b, abs_nonneg a, abs_nonneg b]

private theorem norm_xiGaussianTestC_le_on_horizontal_strip_arch
    {t : ℝ} (ht : 0 < t) (n : ℕ) {a b x y : ℝ}
    (hy : y ∈ Set.uIoc a b) :
    ‖xiGaussianTestC t n ((x : ℂ) + (y : ℂ) * I)‖ ≤
      (|a| + |b| + |x|) ^ (2 * n) * Real.exp (t * (|a| + |b|) ^ (2 : ℕ)) *
        Real.exp (-(t * x ^ (2 : ℕ))) := by
  rw [norm_xiGaussianTestC_eq_norm_rotated]
  have hyabs := abs_le_abs_add_abs_of_mem_uIoc_arch hy
  have hbound := norm_xiGaussianTest_le_of_strip ht n
    (show 0 ≤ |a| + |b| by positivity)
    (s := (((1 / 2 - y : ℝ) : ℂ) + (x : ℂ) * I))
    (by simpa using hyabs)
  simpa [add_assoc, add_comm, add_left_comm] using hbound

/-- Gaussian majorant for a finite completed-archimedean vertical edge. -/
def xiGaussianArchVerticalMajorant
    (t : ℝ) (k : ℕ) (c R : ℝ) : ℝ :=
  c * Real.exp (t * c ^ (2 : ℕ)) *
    (xiMassArchVerticalGrowthConstant *
        ((c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ (2 : ℕ)))) +
      (1 / 2 : ℝ) *
        ((c + |R|) ^ (2 * k + 1) * Real.exp (-(t * R ^ (2 : ℕ)))))

theorem xiGaussianArchVerticalMajorant_nonneg
    {t c : ℝ} (hc : 0 ≤ c) (k : ℕ) (R : ℝ) :
    0 ≤ xiGaussianArchVerticalMajorant t k c R := by
  unfold xiGaussianArchVerticalMajorant
  have hbase : 0 ≤ c + |R| := add_nonneg hc (abs_nonneg R)
  have hC := xiMassArchVerticalGrowthConstant_nonneg
  positivity

theorem norm_integral_xiGaussianArchVertical_le
    {t c R : ℝ} (ht : 0 < t) (hc : 1 / 2 < c) (k : ℕ)
    (hR : max 2 (1 / 2 + c) ≤ |R|) :
    ‖∫ y in -c..0,
      xiGaussianTestC t k ((R : ℂ) + (y : ℂ) * I) *
        logDeriv archFactor (xiMassArchVerticalEulerPoint R y)‖ ≤
      xiGaussianArchVerticalMajorant t k c R := by
  have hc0 : 0 < c := lt_trans (by norm_num) hc
  have hpoint : ∀ y ∈ uIoc (-c) 0,
      ‖xiGaussianTestC t k ((R : ℂ) + (y : ℂ) * I) *
        logDeriv archFactor (xiMassArchVerticalEulerPoint R y)‖ ≤
      Real.exp (t * c ^ (2 : ℕ)) *
        (xiMassArchVerticalGrowthConstant *
            ((c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ (2 : ℕ)))) +
          (1 / 2 : ℝ) *
            ((c + |R|) ^ (2 * k + 1) * Real.exp (-(t * R ^ (2 : ℕ))))) := by
    intro y hy
    have hyIoc : y ∈ Ioc (-c) 0 := by
      simpa [uIoc_of_le (by linarith : -c ≤ 0)] using hy
    have hprofile0 := norm_xiGaussianTestC_le_on_horizontal_strip_arch ht k
      (a := -c) (b := 0) (x := R) hy
    have hprofile :
        ‖xiGaussianTestC t k ((R : ℂ) + (y : ℂ) * I)‖ ≤
          (c + |R|) ^ (2 * k) * Real.exp (t * c ^ (2 : ℕ)) *
            Real.exp (-(t * R ^ (2 : ℕ))) := by
      simpa [abs_of_pos hc0] using hprofile0
    have harch := norm_logDeriv_archFactor_xiMassArchVertical_le
      (c := c) (R := R) (y := y) ⟨hyIoc.1.le, hyIoc.2⟩ hR
    rw [norm_mul]
    refine (mul_le_mul hprofile harch (norm_nonneg _)
      (mul_nonneg (mul_nonneg (pow_nonneg (by positivity) _)
        (Real.exp_pos _).le) (Real.exp_pos _).le)).trans ?_
    have hbase : 0 ≤ c + |R| := by positivity
    have hRbase : |R| ≤ c + |R| := by linarith
    have hpow : 0 ≤ (c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ (2 : ℕ))) := by positivity
    have hmul :
        |R| * ((c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ (2 : ℕ)))) ≤
          (c + |R|) ^ (2 * k + 1) * Real.exp (-(t * R ^ (2 : ℕ))) := by
      calc
        |R| * ((c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ (2 : ℕ)))) ≤
            (c + |R|) *
              ((c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ (2 : ℕ)))) :=
          mul_le_mul_of_nonneg_right hRbase hpow
        _ = (c + |R|) ^ (2 * k + 1) * Real.exp (-(t * R ^ (2 : ℕ))) := by
          rw [pow_succ']
          ring
    have hC := xiMassArchVerticalGrowthConstant_nonneg
    calc
      (c + |R|) ^ (2 * k) * Real.exp (t * c ^ (2 : ℕ)) *
          Real.exp (-(t * R ^ (2 : ℕ))) *
          (xiMassArchVerticalGrowthConstant + |R| / 2) =
        Real.exp (t * c ^ (2 : ℕ)) *
          (((c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ (2 : ℕ)))) *
            (xiMassArchVerticalGrowthConstant + |R| / 2)) := by ring
      _ ≤ Real.exp (t * c ^ (2 : ℕ)) *
        (xiMassArchVerticalGrowthConstant *
            ((c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ (2 : ℕ)))) +
          (1 / 2 : ℝ) *
            ((c + |R|) ^ (2 * k + 1) * Real.exp (-(t * R ^ (2 : ℕ))))) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_pos _).le
        calc
          ((c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ (2 : ℕ)))) *
          (xiMassArchVerticalGrowthConstant + |R| / 2) =
            xiMassArchVerticalGrowthConstant *
                ((c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ (2 : ℕ)))) +
              (1 / 2 : ℝ) *
                (|R| * ((c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ (2 : ℕ))))) := by ring
          _ ≤ xiMassArchVerticalGrowthConstant *
                ((c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ (2 : ℕ)))) +
              (1 / 2 : ℝ) *
                ((c + |R|) ^ (2 * k + 1) * Real.exp (-(t * R ^ (2 : ℕ)))) := by
            exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hmul (by norm_num))
  calc
    ‖∫ y in -c..0,
      xiGaussianTestC t k ((R : ℂ) + (y : ℂ) * I) *
        logDeriv archFactor (xiMassArchVerticalEulerPoint R y)‖ ≤
      (Real.exp (t * c ^ (2 : ℕ)) *
        (xiMassArchVerticalGrowthConstant *
            ((c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ (2 : ℕ)))) +
          (1 / 2 : ℝ) *
            ((c + |R|) ^ (2 * k + 1) * Real.exp (-(t * R ^ (2 : ℕ)))))) *
        |0 - (-c)| :=
      intervalIntegral.norm_integral_le_of_norm_le_const hpoint
    _ = xiGaussianArchVerticalMajorant t k c R := by
      rw [abs_of_nonneg (by linarith : 0 ≤ 0 - -c)]
      unfold xiGaussianArchVerticalMajorant
      ring

theorem tendsto_xiGaussianArchVerticalMajorant_atTop
    {t c : ℝ} (ht : 0 < t) (k : ℕ) :
    Tendsto (xiGaussianArchVerticalMajorant t k c) atTop (nhds 0) := by
  have h0 := tendsto_polyGaussian_atTop ht (2 * k) c
  have h1 := tendsto_polyGaussian_atTop ht (2 * k + 1) c
  have hsum :=
    (h0.const_mul xiMassArchVerticalGrowthConstant).add
      (h1.const_mul (1 / 2 : ℝ))
  have hscaled := hsum.const_mul (c * Real.exp (t * c ^ (2 : ℕ)))
  change Tendsto (fun R : ℝ =>
    c * Real.exp (t * c ^ (2 : ℕ)) *
      (xiMassArchVerticalGrowthConstant *
          ((c + |R|) ^ (2 * k) * Real.exp (-(t * R ^ (2 : ℕ)))) +
        (1 / 2 : ℝ) *
          ((c + |R|) ^ (2 * k + 1) * Real.exp (-(t * R ^ (2 : ℕ)))))) atTop (nhds 0)
  simpa only [mul_zero, add_zero] using hscaled

theorem tendsto_integral_xiGaussianArchVertical_right_atTop
    {t c : ℝ} (ht : 0 < t) (hc : 1 / 2 < c) (k : ℕ) :
    Tendsto (fun R : ℝ => ∫ y in -c..0,
      xiGaussianTestC t k ((R : ℂ) + (y : ℂ) * I) *
        logDeriv archFactor (xiMassArchVerticalEulerPoint R y))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (tendsto_xiGaussianArchVerticalMajorant_atTop (c := c) ht k)
  filter_upwards [eventually_ge_atTop (max 2 (1 / 2 + c))] with R hR
  have hR0 : 0 ≤ R := by
    linarith [le_trans (le_max_left 2 (1 / 2 + c)) hR]
  exact norm_integral_xiGaussianArchVertical_le (c := c) ht hc k
    (by simpa [abs_of_nonneg hR0] using hR)

theorem tendsto_integral_xiGaussianArchVertical_left_atTop
    {t c : ℝ} (ht : 0 < t) (hc : 1 / 2 < c) (k : ℕ) :
    Tendsto (fun R : ℝ => ∫ y in -c..0,
      xiGaussianTestC t k ((-R : ℂ) + (y : ℂ) * I) *
        logDeriv archFactor (xiMassArchVerticalEulerPoint (-R) y))
      atTop (nhds 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (tendsto_xiGaussianArchVerticalMajorant_atTop (c := c) ht k)
  filter_upwards [eventually_ge_atTop (max 2 (1 / 2 + c))] with R hR
  have hR0 : 0 ≤ R := by
    linarith [le_trans (le_max_left 2 (1 / 2 + c)) hR]
  have hb := norm_integral_xiGaussianArchVertical_le ht hc k
    (R := -R) (by simpa [abs_neg, abs_of_nonneg hR0] using hR)
  simpa [xiGaussianArchVerticalMajorant, abs_neg, neg_sq] using hb

theorem tendsto_integral_xiGaussianArchHorizontal_atTop
    {t c : ℝ} (ht : 0 < t) (hc : 1 / 2 < c) (k : ℕ)
    {y : ℝ} (hy : -c ≤ y ∧ y ≤ 0) (hyPole : y ≠ -(1 / 2)) :
    Tendsto (fun R : ℝ => ∫ x in -R..R,
      xiGaussianArchHorizontalIntegrand t k y x) atTop
      (nhds (∫ x : ℝ, xiGaussianArchHorizontalIntegrand t k y x)) := by
  exact intervalIntegral_tendsto_integral
    (integrable_xiGaussianArchHorizontalIntegrand ht hc k hy hyPole)
    (tendsto_neg_atBot_iff.mpr tendsto_id) tendsto_id

/-- Exact infinite Gaussian archimedean shift.  The bottom absolute-Euler source is the centered
critical-line source plus the literal crossed `s = 1` residue. -/
theorem integral_xiGaussianBottomArch_eq_centered_add_residue
    {t c : ℝ} (ht : 0 < t) (hc : 1 / 2 < c) (k : ℕ) :
    (∫ x : ℝ, xiGaussianBottomArchIntegrand t k c x) =
      (∫ x : ℝ, xiGaussianCenteredArchIntegrand t k x) +
        2 * Real.pi * xiGaussianTestC t k xiMassArchPole := by
  let F : ℂ → ℂ := fun z => xiGaussianTestC t k z *
    logDeriv archFactor (xiMassCenteredArchPoint z)
  have hbottom := tendsto_integral_xiGaussianArchHorizontal_atTop
    ht hc k (y := -c) ⟨le_rfl, by linarith⟩ (by linarith)
  have hcentered := tendsto_integral_xiGaussianArchHorizontal_atTop
    ht hc k (y := 0) ⟨by linarith, le_rfl⟩ (by norm_num)
  have hright := tendsto_integral_xiGaussianArchVertical_right_atTop ht hc k
  have hleft := tendsto_integral_xiGaussianArchVertical_left_atTop ht hc k
  have hlim := ((hbottom.sub hcentered).add (hright.const_smul I)).sub
    (hleft.const_smul I)
  have hlim' : Tendsto (fun R : ℝ =>
      rectIntegral F (((-R : ℝ) : ℂ) - c * I) (R : ℂ)) atTop
      (nhds ((∫ x : ℝ, xiGaussianBottomArchIntegrand t k c x) -
        (∫ x : ℝ, xiGaussianCenteredArchIntegrand t k x))) := by
    simpa [rectIntegral, F, xiGaussianBottomArchIntegrand,
      xiGaussianCenteredArchIntegrand, xiGaussianArchHorizontalIntegrand,
      xiMassArchVerticalEulerPoint, smul_eq_mul, sub_eq_add_neg] using hlim
  have heventually : ∀ᶠ R : ℝ in atTop,
      rectIntegral F (((-R : ℝ) : ℂ) - c * I) (R : ℂ) =
        2 * Real.pi * xiGaussianTestC t k xiMassArchPole := by
    filter_upwards [eventually_gt_atTop (0 : ℝ)] with R hR
    exact rectIntegral_xiGaussian_mul_archLogDeriv hc hR k
  have hconst : Tendsto (fun _ : ℝ =>
      2 * Real.pi * xiGaussianTestC t k xiMassArchPole) atTop
      (nhds (2 * Real.pi * xiGaussianTestC t k xiMassArchPole)) :=
    tendsto_const_nhds
  have heventually' : ∀ᶠ R : ℝ in atTop,
      2 * Real.pi * xiGaussianTestC t k xiMassArchPole =
        rectIntegral F (((-R : ℝ) : ℂ) - c * I) (R : ℂ) :=
    heventually.mono fun _ h => h.symm
  have htarget := tendsto_nhds_unique hlim' (hconst.congr' heventually')
  exact sub_eq_iff_eq_add'.mp htarget

/-- Real Gaussian--Hermite density on the critical line. -/
def xiGaussianHermiteProfile (t : ℝ) (k : ℕ) (x : ℝ) : ℝ :=
  x ^ (2 * k) * Real.exp (-(t * x ^ (2 : ℕ)))

theorem xiGaussianTestC_ofReal (t : ℝ) (k : ℕ) (x : ℝ) :
    xiGaussianTestC t k (x : ℂ) = (xiGaussianHermiteProfile t k x : ℂ) := by
  rw [xiGaussianTestC, xiGaussianHermiteProfile]
  push_cast
  congr 2
  ring

/-- The real part of the completed archimedean logarithmic derivative on the critical line is
exactly the corpus's Hardy Gamma phase rate; the two rational polar terms cancel radially. -/
theorem re_logDeriv_archFactor_centered_eq_gammaHardyPhaseRate (x : ℝ) :
    (logDeriv archFactor (xiMassCenteredArchPoint (x : ℂ))).re =
      gammaHardyPhaseRate x := by
  have hs : xiMassCenteredArchPoint (x : ℂ) = linePt x := by
    unfold xiMassCenteredArchPoint linePt
    norm_num [add_comm]
  rw [hs]
  have h0 : linePt x ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    rw [linePt_re, Complex.zero_re] at hre
    norm_num at hre
  have h1 : linePt x ≠ 1 := by
    intro h
    have hre := congrArg Complex.re h
    rw [linePt_re, Complex.one_re] at hre
    norm_num at hre
  rw [logDeriv_archFactor_closed (linePt_re_pos x) h0 h1]
  unfold GaloisForLFunctions.gammaRealLogConnection gammaHardyPhaseRate
  simp [linePt, Complex.normSq]
  ring

theorem re_xiGaussianCenteredArchIntegrand
    (t : ℝ) (k : ℕ) (x : ℝ) :
    (xiGaussianCenteredArchIntegrand t k x).re =
      xiGaussianHermiteProfile t k x * gammaHardyPhaseRate x := by
  rw [xiGaussianCenteredArchIntegrand, xiGaussianArchHorizontalIntegrand]
  simp only [ofReal_zero, zero_mul, add_zero]
  rw [xiGaussianTestC_ofReal, Complex.mul_re,
    re_logDeriv_archFactor_centered_eq_gammaHardyPhaseRate]
  simp

/-- Exact critical-line landing of the completed archimedean edge. -/
theorem re_integral_xiGaussianCenteredArch_eq_gammaHardyPhaseRate
    {t c : ℝ} (ht : 0 < t) (hc : 1 / 2 < c) (k : ℕ) :
    (∫ x : ℝ, xiGaussianCenteredArchIntegrand t k x).re =
      ∫ x : ℝ, xiGaussianHermiteProfile t k x * gammaHardyPhaseRate x := by
  have hint : Integrable (xiGaussianCenteredArchIntegrand t k) := by
    exact integrable_xiGaussianArchHorizontalIntegrand ht hc k
      (y := 0) ⟨by linarith, le_rfl⟩ (by norm_num)
  change RCLike.re (∫ x : ℝ, xiGaussianCenteredArchIntegrand t k x) = _
  rw [← integral_re hint]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with x
  exact re_xiGaussianCenteredArchIntegrand t k x

/-- Real bottom archimedean source: exact Hardy Gamma integral plus exact crossed polar mass. -/
theorem re_xiGaussianTestC_archPole (t : ℝ) (k : ℕ) :
    (xiGaussianTestC t k xiMassArchPole).re =
      (-(1 / 4 : ℝ)) ^ k * Real.exp (t / 4) := by
  rw [xiMassArchPole, xiGaussianTestC_neg_I_half]
  rw [show ((-1 : ℂ) / 4) = ((-(1 / 4 : ℝ)) : ℂ) by norm_num]
  rw [← Complex.ofReal_exp]
  norm_cast

/-- Real bottom archimedean source: exact Hardy Gamma integral plus exact crossed polar mass. -/
theorem re_integral_xiGaussianBottomArch_eq_gamma_add_polar
    {t c : ℝ} (ht : 0 < t) (hc : 1 / 2 < c) (k : ℕ) :
    (∫ x : ℝ, xiGaussianBottomArchIntegrand t k c x).re =
      (∫ x : ℝ, xiGaussianHermiteProfile t k x * gammaHardyPhaseRate x) +
        2 * Real.pi * ((-(1 / 4 : ℝ)) ^ k * Real.exp (t / 4)) := by
  have hshift := integral_xiGaussianBottomArch_eq_centered_add_residue ht hc k
  have hre := congrArg Complex.re hshift
  rw [Complex.add_re, Complex.mul_re,
    re_integral_xiGaussianCenteredArch_eq_gammaHardyPhaseRate ht hc k] at hre
  have hscalarRe : (2 * (Real.pi : ℂ)).re = 2 * Real.pi := by norm_num
  have hscalarIm : (2 * (Real.pi : ℂ)).im = 0 := by norm_num
  rw [hscalarRe, hscalarIm, zero_mul, sub_zero,
    re_xiGaussianTestC_archPole] at hre
  exact hre

end

end RHTower
