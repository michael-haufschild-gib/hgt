import GaloisForLFunctions.RHTower.ZetaFractLaplace
import GaloisForLFunctions.RHTower.PutnamJump
import GaloisForLFunctions.RHTower.PeriodicityDichotomy
import GaloisForLFunctions.BlackHoleRingdown.TheInverseXiContour
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.TheScalingSurfaceOfACurve
import Mathlib.Analysis.Fourier.AddCircle

/-!
# The zeros contain no conjugacy class of one Frobenius

Over one Frobenius `q` the conjugates of a mode `ρ` are the modes with the same eigenvalue `q^ρ`:
the vertical progression `ρ + 2πik/log q`. The zeros of a curve over a finite field are a finite
union of such classes. This module shows that the zeros of `ζ` contain none, at any real part.

* `endpoint_limits_eq_of_summable_fourierCoeffOn`: a square integrable function on a period whose
  Fourier coefficients are absolutely summable agrees almost everywhere with a continuous periodic
  function, so its one-sided limits at the two ends of the period coincide.
* `fourierCoeffOn_ladderDefect`: for `0 < Re s < 1` the forward periodization
  `Σ_{k ≥ 0} {e^{y+kP}} e^{-s(y+kP)}` of the Laplace kernel of `ζ`, with its polar part
  `e^{(1-s)y}/(e^{(1-s)P} - 1)` added, has the Fourier coefficients `-ζ(s_n)/(P s_n)` at
  `s_n = s + 2πin/P`.
* `tsum_jumpTerm_ne_zero`: across the period this function jumps by
  `Σ {e^{-skP} : e^{kP} ∈ ℕ}`, a geometric series over the multiples of the least such `k`, which
  never vanishes.
* `not_summable_norm_riemannZeta_div`: hence `Σ_{n ∈ ℤ} |ζ(ρ + inT)|/|ρ + inT| = ∞` for every `ρ` in
  the open strip and every step `T > 0`.
* `exists_riemannZeta_ne_zero_progression`, `not_forall_xi_progression`: every vertical progression
  in the strip has infinitely many points that are not zeros.
* `exists_conjugate_not_zero`, `exists_zero_localFactor_not_zero`, `exists_curve_zero_not_zero`:
  no class of a Frobenius `q > 1` lies in the zero set, `ξ` vanishes on the zero set of no local
  factor `q^{-s} - u`, and on the zeros of no eigenvalue of a curve over a finite field.
* `periodicityDichotomy_zeta_iff_riemannHypothesis`: the periodicity dichotomy of `ζ` is the
  Riemann hypothesis, with no hypothesis on progressions off the line.
-/

open Complex MeasureTheory Set Filter Topology
open scoped Real

noncomputable section

namespace GaloisForLFunctions.InfiniteRankPurityTheory

open _root_.RHTower GaloisForLFunctions.BlackHoleRingdown

/-! ### Summable Fourier coefficients leave no jump across the period -/

/-- A function agreeing almost everywhere on `(a, b]` with a continuous one has the value of the
latter at `a` as its right limit there. -/
theorem eq_of_tendsto_right_of_ae_eq {f φ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (h : ∀ᵐ x ∂volume.restrict (Ioc a b), f x = φ x) (hφ : Continuous φ) {L : ℂ}
    (hL : Tendsto f (𝓝[>] a) (𝓝 L)) : L = φ a := by
  by_contra hne
  have hφa : Tendsto φ (𝓝[>] a) (𝓝 (φ a)) := hφ.continuousAt.continuousWithinAt
  have hev : ∀ᶠ x in 𝓝[>] a, f x ≠ φ x :=
    (hL.prodMk_nhds hφa).eventually
      ((isOpen_ne_fun continuous_fst continuous_snd).mem_nhds (show (L, φ a).1 ≠ (L, φ a).2 from hne))
  obtain ⟨u, hu, hsub⟩ := mem_nhdsGT_iff_exists_Ioo_subset.mp hev
  have hnull : volume {x | ¬(x ∈ Ioc a b → f x = φ x)} = 0 :=
    ae_iff.mp ((ae_restrict_iff' measurableSet_Ioc).mp h)
  have hsub' : Ioo a (min u b) ⊆ {x | ¬(x ∈ Ioc a b → f x = φ x)} := by
    intro x hx
    simp only [mem_setOf_eq, Classical.not_imp]
    exact ⟨⟨hx.1, (hx.2.trans_le (min_le_right _ _)).le⟩,
      hsub ⟨hx.1, hx.2.trans_le (min_le_left _ _)⟩⟩
  have h0 := measure_mono_null hsub' hnull
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h0
  have : a < min u b := lt_min hu hab
  linarith

/-- The same at the right end, from the left. -/
theorem eq_of_tendsto_left_of_ae_eq {f φ : ℝ → ℂ} {a b : ℝ} (hab : a < b)
    (h : ∀ᵐ x ∂volume.restrict (Ioc a b), f x = φ x) (hφ : Continuous φ) {L : ℂ}
    (hL : Tendsto f (𝓝[<] b) (𝓝 L)) : L = φ b := by
  by_contra hne
  have hφb : Tendsto φ (𝓝[<] b) (𝓝 (φ b)) := hφ.continuousAt.continuousWithinAt
  have hev : ∀ᶠ x in 𝓝[<] b, f x ≠ φ x :=
    (hL.prodMk_nhds hφb).eventually
      ((isOpen_ne_fun continuous_fst continuous_snd).mem_nhds (show (L, φ b).1 ≠ (L, φ b).2 from hne))
  obtain ⟨l, hl, hsub⟩ := mem_nhdsLT_iff_exists_Ioo_subset.mp hev
  have hnull : volume {x | ¬(x ∈ Ioc a b → f x = φ x)} = 0 :=
    ae_iff.mp ((ae_restrict_iff' measurableSet_Ioc).mp h)
  have hsub' : Ioo (max l a) b ⊆ {x | ¬(x ∈ Ioc a b → f x = φ x)} := by
    intro x hx
    simp only [mem_setOf_eq, Classical.not_imp]
    exact ⟨⟨(le_max_right _ _).trans_lt hx.1, hx.2.le⟩,
      hsub ⟨(le_max_left _ _).trans_lt hx.1, hx.2⟩⟩
  have h0 := measure_mono_null hsub' hnull
  rw [Real.volume_Ioo, ENNReal.ofReal_eq_zero] at h0
  have : max l a < b := max_lt hl hab
  linarith

/-- **Absolutely summable Fourier coefficients leave no jump across the period.** The Fourier series
converges uniformly to a continuous periodic function, which equals `f` almost everywhere by the
`L²` theory; the one-sided limits of `f` at the two ends are its values there. -/
theorem endpoint_limits_eq_of_summable_fourierCoeffOn {a b : ℝ} (hab : a < b) {f : ℝ → ℂ}
    (hf : MemLp f 2 (volume.restrict (Ioc a b)))
    (hsum : Summable fun n : ℤ => ‖fourierCoeffOn hab f n‖) {La Lb : ℂ}
    (hLa : Tendsto f (𝓝[>] a) (𝓝 La)) (hLb : Tendsto f (𝓝[<] b) (𝓝 Lb)) : La = Lb := by
  haveI : Fact (0 < b - a) := ⟨sub_pos.mpr hab⟩
  have hf' : MemLp f 2 (volume.restrict (Ioc a (a + (b - a)))) := by rwa [add_sub_cancel]
  have hF := hf'.memLp_liftIoc.haarAddCircle
  have hcoef : ∀ n : ℤ, fourierCoeff (hF.toLp _) n = fourierCoeffOn hab f n := fun n => by
    rw [fourierCoeff_congr_ae hF.coeFn_toLp]
    rfl
  have hL2 := hasSum_fourier_series_L2 (hF.toLp _)
  simp_rw [hcoef] at hL2
  -- the uniformly convergent series and its image in `L²`
  have hsumC : Summable fun n : ℤ =>
      fourierCoeffOn hab f n • (fourier n : C(AddCircle (b - a), ℂ)) := by
    refine Summable.of_norm ?_
    simpa only [norm_smul, fourier_norm, mul_one] using hsum
  set g : C(AddCircle (b - a), ℂ) := ∑' n : ℤ, fourierCoeffOn hab f n • fourier n with hg
  have hgL := (ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ).hasSum hsumC.hasSum
  have hterm : ∀ n : ℤ, ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ
      (fourierCoeffOn hab f n • (fourier n : C(AddCircle (b - a), ℂ)))
        = fourierCoeffOn hab f n • fourierLp 2 n := fun n => map_smul _ _ _
  simp_rw [hterm] at hgL
  have heq := hgL.unique hL2
  have hae : ∀ᵐ t ∂(AddCircle.haarAddCircle : Measure (AddCircle (b - a))),
      AddCircle.liftIoc (b - a) a f t = g t := by
    have h2 := ContinuousMap.coeFn_toLp (E := ℂ) (p := 2) (𝕜 := ℂ) AddCircle.haarAddCircle g
    rw [show ContinuousMap.toLp (E := ℂ) 2 AddCircle.haarAddCircle ℂ g = _ from heq] at h2
    filter_upwards [hF.coeFn_toLp, h2] with t ht1 ht2
    rw [← ht1, ht2]
  -- back to the line
  have hvol : ∀ᵐ t ∂(volume : Measure (AddCircle (b - a))),
      AddCircle.liftIoc (b - a) a f t = g t := by
    rw [AddCircle.volume_eq_smul_haarAddCircle]
    exact Measure.ae_smul_measure hae _
  have hreal := (AddCircle.measurePreserving_mk (b - a) a).quasiMeasurePreserving.ae hvol
  rw [add_sub_cancel] at hreal
  have hreal' : ∀ᵐ x ∂volume.restrict (Ioc a b), f x = g (x : AddCircle (b - a)) := by
    filter_upwards [hreal, ae_restrict_mem measurableSet_Ioc] with x hx hmem
    rw [← hx, AddCircle.liftIoc_coe_apply (by rwa [add_sub_cancel])]
  have hφ : Continuous fun x : ℝ => g (x : AddCircle (b - a)) :=
    g.continuous.comp (AddCircle.continuous_mk' (b - a))
  have hper : ((b : ℝ) : AddCircle (b - a)) = (a : AddCircle (b - a)) := by
    have h := AddCircle.coe_add_period (b - a) a
    rwa [add_sub_cancel] at h
  rw [eq_of_tendsto_right_of_ae_eq hab hreal' hφ hLa, eq_of_tendsto_left_of_ae_eq hab hreal' hφ hLb,
    hper]

/-! ### The Laplace kernel of `ζ` and its forward periodization -/

/-- The kernel `{e^x} e^{-sx}` of the Laplace representation of `ζ`. -/
def ladderKernel (s : ℂ) (x : ℝ) : ℂ :=
  ((Int.fract (Real.exp x) : ℝ) : ℂ) * Complex.exp (-s * (x : ℂ))

theorem norm_ladderKernel_le (s : ℂ) (x : ℝ) : ‖ladderKernel s x‖ ≤ Real.exp (-(s.re * x)) := by
  rw [ladderKernel, norm_mul, Complex.norm_real, Real.norm_of_nonneg (Int.fract_nonneg _),
    Complex.norm_exp]
  have hre : (-s * (x : ℂ)).re = -(s.re * x) := by simp
  rw [hre]
  exact mul_le_of_le_one_left (Real.exp_pos _).le (Int.fract_lt_one _).le

theorem norm_ladderKernel_shift_le {s : ℂ} (hs : 0 ≤ s.re) {P y : ℝ} (hy : 0 ≤ y) (k : ℕ) :
    ‖ladderKernel s (y + k * P)‖ ≤ Real.exp (-(s.re * P)) ^ k := by
  refine (norm_ladderKernel_le s _).trans ?_
  rw [← Real.exp_nat_mul]
  refine Real.exp_le_exp.mpr ?_
  have : 0 ≤ s.re * y := mul_nonneg hs hy
  nlinarith

theorem exp_neg_mul_lt_one {s : ℂ} (hs : 0 < s.re) {P : ℝ} (hP : 0 < P) :
    Real.exp (-(s.re * P)) < 1 :=
  Real.exp_lt_one_iff.mpr (neg_neg_of_pos (mul_pos hs hP))

theorem measurable_ladderKernel (s : ℂ) : Measurable (ladderKernel s) :=
  (Complex.measurable_ofReal.comp (measurable_fract.comp Real.measurable_exp)).mul
    (Complex.measurable_exp.comp (by fun_prop))

/-- The Laplace kernel is the difference of a continuous function and the integer part. -/
theorem ladderKernel_eq_floor (s : ℂ) (x : ℝ) :
    ladderKernel s x = ((Real.exp x : ℝ) : ℂ) * Complex.exp (-s * (x : ℂ))
      - ((⌊Real.exp x⌋ : ℤ) : ℂ) * Complex.exp (-s * (x : ℂ)) := by
  rw [ladderKernel, ← sub_mul]
  congr 1
  rw [show Int.fract (Real.exp x) = Real.exp x - (⌊Real.exp x⌋ : ℤ) from rfl]
  push_cast
  ring

theorem integrableOn_ladderKernel_Ioi {s : ℂ} (hs : 0 < s.re) :
    IntegrableOn (ladderKernel s) (Ioi (0 : ℝ)) := by
  refine Integrable.mono' (g := fun x : ℝ => Real.exp (-s.re * x)) (exp_neg_integrableOn_Ioi 0 hs)
    (measurable_ladderKernel s).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
  simpa only [neg_mul] using norm_ladderKernel_le s x

/-- **The Laplace representation**: `∫_0^∞ {e^x} e^{-sx} dx = 1/(s - 1) - ζ(s)/s`. -/
theorem integral_ladderKernel {s : ℂ} (hs : 0 < s.re) (hs1 : s ≠ 1) :
    (∫ x in Ioi (0 : ℝ), ladderKernel s x) = 1 / (s - 1) - riemannZeta s / s :=
  integral_Ioi_zero_fract_exp hs hs1

/-- The forward periodization of the kernel. -/
def ladderSum (s : ℂ) (P : ℝ) (y : ℝ) : ℂ := ∑' k : ℕ, ladderKernel s (y + k * P)

theorem measurable_ladderSum (s : ℂ) (P : ℝ) : Measurable (ladderSum s P) :=
  Measurable.tsum fun _ => (measurable_ladderKernel s).comp (by fun_prop)

theorem norm_ladderSum_le {s : ℂ} (hs : 0 < s.re) {P : ℝ} (hP : 0 < P) {y : ℝ} (hy : 0 ≤ y) :
    ‖ladderSum s P y‖ ≤ (1 - Real.exp (-(s.re * P)))⁻¹ :=
  tsum_of_norm_bounded (hasSum_geometric_of_lt_one (Real.exp_pos _).le (exp_neg_mul_lt_one hs hP))
    (norm_ladderKernel_shift_le hs.le hy)

/-- **Unfolding.** For a kernel on the half-line whose translates by the period are uniformly
summable on a period, the integral over a period of the sum of the translates is the integral of
the kernel over the half-line. -/
theorem integral_tsum_translates {K : ℝ → ℂ} (hK : Measurable K) {P : ℝ} (hP : 0 < P) {u : ℕ → ℝ}
    (hu : Summable u) (hbound : ∀ k : ℕ, ∀ y ∈ Ioc (0 : ℝ) P, ‖K (y + k * P)‖ ≤ u k)
    (hK0 : IntegrableOn K (Ioi (0 : ℝ))) :
    (∫ y in (0 : ℝ)..P, ∑' k : ℕ, K (y + k * P)) = ∫ x in Ioi (0 : ℝ), K x := by
  have hfin : volume (Ioc (0 : ℝ) P) ≠ ⊤ := measure_Ioc_lt_top.ne
  have hint : ∀ k : ℕ, IntegrableOn (fun y : ℝ => K (y + k * P)) (Ioc 0 P) := fun k =>
    Integrable.mono' (g := fun _ : ℝ => u k) (integrableOn_const hfin)
      (hK.comp (by fun_prop)).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun y hy => hbound k y hy))
  have hsum : Summable fun k : ℕ => ∫ y in Ioc (0 : ℝ) P, ‖K (y + k * P)‖ := by
    refine Summable.of_nonneg_of_le (fun k => integral_nonneg fun _ => norm_nonneg _) (fun k => ?_)
      (hu.mul_left P)
    calc (∫ y in Ioc (0 : ℝ) P, ‖K (y + k * P)‖)
        ≤ ∫ _y in Ioc (0 : ℝ) P, u k :=
          setIntegral_mono_on (hint k).norm (integrableOn_const hfin) measurableSet_Ioc
            fun y hy => hbound k y hy
      _ = P * u k := by
          rw [setIntegral_const, Real.volume_real_Ioc_of_le hP.le, smul_eq_mul, sub_zero]
  have hhas := hasSum_integral_of_summable_integral_norm hint hsum
  have hloc : ∀ c d : ℝ, 0 ≤ c → c ≤ d → IntervalIntegrable K volume c d :=
    fun c d hc hcd => (intervalIntegrable_iff_integrableOn_Ioc_of_le hcd).mpr
      (hK0.mono_set fun x hx => hc.trans_lt hx.1)
  -- each translate integrates over one period of the half-line
  have hshift : ∀ k : ℕ, (∫ y in Ioc (0 : ℝ) P, K (y + k * P))
      = ∫ x in ((k : ℕ) : ℝ) * P..((k + 1 : ℕ) : ℝ) * P, K x := by
    intro k
    rw [← intervalIntegral.integral_of_le hP.le,
      intervalIntegral.integral_comp_add_right K ((k : ℝ) * P)]
    congr 1
    · ring
    · push_cast
      ring
  have hpartial : ∀ N : ℕ, ∑ k ∈ Finset.range N, (∫ y in Ioc (0 : ℝ) P, K (y + k * P))
      = ∫ x in (0 : ℝ)..(N : ℝ) * P, K x := by
    intro N
    simp_rw [hshift]
    have h := intervalIntegral.sum_integral_adjacent_intervals (f := K) (μ := volume)
      (a := fun k : ℕ => (k : ℝ) * P) (n := N)
      (fun k _ => hloc _ _ (by positivity) (by push_cast; nlinarith))
    simpa using h
  have hlim : Tendsto (fun N : ℕ => ∫ x in (0 : ℝ)..(N : ℝ) * P, K x) atTop
      (𝓝 (∫ x in Ioi (0 : ℝ), K x)) :=
    intervalIntegral_tendsto_integral_Ioi 0 hK0 (tendsto_natCast_atTop_atTop.atTop_mul_const hP)
  have hlim' := hhas.tendsto_sum_nat
  simp_rw [hpartial] at hlim'
  rw [intervalIntegral.integral_of_le hP.le]
  exact tendsto_nhds_unique hlim' hlim

theorem integral_ladderSum {s : ℂ} (hs : 0 < s.re) {P : ℝ} (hP : 0 < P) :
    (∫ y in (0 : ℝ)..P, ladderSum s P y) = ∫ x in Ioi (0 : ℝ), ladderKernel s x :=
  integral_tsum_translates (measurable_ladderKernel s) hP
    (summable_geometric_of_lt_one (Real.exp_pos _).le (exp_neg_mul_lt_one hs hP))
    (fun k _ hy => norm_ladderKernel_shift_le hs.le hy.1.le k) (integrableOn_ladderKernel_Ioi hs)

/-! ### Fourier coefficients -/

theorem ladderKernel_add_mul_I (s : ℂ) (ω x : ℝ) :
    ladderKernel (s + (ω : ℂ) * I) x
      = ladderKernel s x * Complex.exp (-((ω : ℂ) * I) * (x : ℂ)) := by
  rw [ladderKernel, ladderKernel, mul_assoc, ← Complex.exp_add]
  congr 2
  ring

/-- The characters of the period are constant along its translates. -/
theorem exp_character_shift {P : ℝ} (hP : P ≠ 0) (n : ℤ) (k : ℕ) (y : ℝ) :
    Complex.exp (-(((2 * π * n / P : ℝ) : ℂ) * I) * ((y + k * P : ℝ) : ℂ))
      = Complex.exp (-(((2 * π * n / P : ℝ) : ℂ) * I) * (y : ℂ)) := by
  have hPc : (P : ℂ) ≠ 0 := by exact_mod_cast hP
  have h : -(((2 * π * n / P : ℝ) : ℂ) * I) * ((y + k * P : ℝ) : ℂ)
      = -(((2 * π * n / P : ℝ) : ℂ) * I) * (y : ℂ) + ((-(n * k) : ℤ) : ℂ) * (2 * π * I) := by
    push_cast
    field_simp
    ring
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

theorem ladderSum_add_mul_I (s : ℂ) {P : ℝ} (hP : P ≠ 0) (n : ℤ) (y : ℝ) :
    ladderSum (s + ((2 * π * n / P : ℝ) : ℂ) * I) P y
      = ladderSum s P y * Complex.exp (-(((2 * π * n / P : ℝ) : ℂ) * I) * (y : ℂ)) := by
  rw [ladderSum, ladderSum, ← tsum_mul_right]
  refine tsum_congr fun k => ?_
  rw [ladderKernel_add_mul_I, exp_character_shift hP n k y]

theorem exp_one_sub_mul_sub_one_ne_zero {s : ℂ} (hs : s.re < 1) {P : ℝ} (hP : 0 < P) :
    Complex.exp ((1 - s) * (P : ℂ)) - 1 ≠ 0 := by
  intro h
  have h1 : ‖Complex.exp ((1 - s) * (P : ℂ))‖ = 1 := by rw [sub_eq_zero.mp h, norm_one]
  have hre : ((1 - s) * (P : ℂ)).re = (1 - s.re) * P := by simp
  rw [Complex.norm_exp, hre, Real.exp_eq_one_iff] at h1
  nlinarith

/-- The periodization with its polar part added. -/
def ladderDefect (s : ℂ) (P : ℝ) (y : ℝ) : ℂ :=
  ladderSum s P y + Complex.exp ((1 - s) * (y : ℂ)) / (Complex.exp ((1 - s) * (P : ℂ)) - 1)

/-- The Fourier coefficients of the polar part. -/
theorem integral_polar_mul_exp {s : ℂ} (hs : s.re < 1) {P : ℝ} (hP : 0 < P) (n : ℤ) :
    (∫ y in (0 : ℝ)..P, Complex.exp ((1 - s) * (y : ℂ)) / (Complex.exp ((1 - s) * (P : ℂ)) - 1)
        * Complex.exp (-(((2 * π * n / P : ℝ) : ℂ) * I) * (y : ℂ)))
      = 1 / (1 - (s + ((2 * π * n / P : ℝ) : ℂ) * I)) := by
  have hE := exp_one_sub_mul_sub_one_ne_zero hs hP
  set c : ℂ := 1 - (s + ((2 * π * n / P : ℝ) : ℂ) * I) with hc
  have hc0 : c ≠ 0 := by
    intro h
    have hre := congrArg Complex.re h
    simp [hc] at hre
    linarith
  have hPc : (P : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
  have hpt : ∀ y : ℝ, Complex.exp ((1 - s) * (y : ℂ)) / (Complex.exp ((1 - s) * (P : ℂ)) - 1)
      * Complex.exp (-(((2 * π * n / P : ℝ) : ℂ) * I) * (y : ℂ))
        = (Complex.exp ((1 - s) * (P : ℂ)) - 1)⁻¹ * Complex.exp (c * (y : ℂ)) := by
    intro y
    rw [div_mul_eq_mul_div, ← Complex.exp_add, div_eq_inv_mul]
    congr 2
    rw [hc]
    ring
  have hcP : Complex.exp (c * (P : ℂ)) = Complex.exp ((1 - s) * (P : ℂ)) := by
    have h : c * (P : ℂ) = (1 - s) * (P : ℂ) + ((-n : ℤ) : ℂ) * (2 * π * I) := by
      rw [hc]
      push_cast
      field_simp
      ring
    rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]
  simp_rw [hpt]
  rw [intervalIntegral.integral_const_mul, integral_exp_mul_complex hc0, hcP]
  simp only [Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  field_simp

theorem intervalIntegrable_ladderSum {s : ℂ} (hs : 0 < s.re) {P : ℝ} (hP : 0 < P) :
    IntervalIntegrable (ladderSum s P) volume 0 P :=
  (intervalIntegrable_iff_integrableOn_Ioc_of_le hP.le).mpr
    (Measure.integrableOn_of_bounded measure_Ioc_lt_top.ne
      (measurable_ladderSum s P).aestronglyMeasurable
      ((ae_restrict_iff' measurableSet_Ioc).mpr
        (Eventually.of_forall fun _ hy => norm_ladderSum_le hs hP hy.1.le)))

/-- **The Fourier coefficients of the periodization are the zeta values.** -/
theorem integral_ladderDefect_mul_exp {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) {P : ℝ}
    (hP : 0 < P) (n : ℤ) :
    (∫ y in (0 : ℝ)..P, ladderDefect s P y
        * Complex.exp (-(((2 * π * n / P : ℝ) : ℂ) * I) * (y : ℂ)))
      = -(riemannZeta (s + ((2 * π * n / P : ℝ) : ℂ) * I)
          / (s + ((2 * π * n / P : ℝ) : ℂ) * I)) := by
  set s' : ℂ := s + ((2 * π * n / P : ℝ) : ℂ) * I with hs'
  have hre : s'.re = s.re := by simp [hs']
  have hs'0 : 0 < s'.re := by rw [hre]; exact h0
  have hs'1 : s' ≠ 1 := by
    intro h
    rw [h, Complex.one_re] at hre
    linarith
  have hsub : s' - 1 ≠ 0 := sub_ne_zero.mpr hs'1
  have hpt : ∀ y : ℝ, ladderDefect s P y
      * Complex.exp (-(((2 * π * n / P : ℝ) : ℂ) * I) * (y : ℂ))
        = ladderSum s' P y
          + Complex.exp ((1 - s) * (y : ℂ)) / (Complex.exp ((1 - s) * (P : ℂ)) - 1)
            * Complex.exp (-(((2 * π * n / P : ℝ) : ℂ) * I) * (y : ℂ)) := by
    intro y
    rw [ladderDefect, add_mul, hs', ladderSum_add_mul_I s hP.ne' n y]
  have hcont : Continuous fun y : ℝ =>
      Complex.exp ((1 - s) * (y : ℂ)) / (Complex.exp ((1 - s) * (P : ℂ)) - 1)
        * Complex.exp (-(((2 * π * n / P : ℝ) : ℂ) * I) * (y : ℂ)) := by fun_prop
  simp_rw [hpt]
  rw [intervalIntegral.integral_add (intervalIntegrable_ladderSum hs'0 hP)
      (hcont.intervalIntegrable _ _),
    integral_ladderSum hs'0 hP, integral_ladderKernel hs'0 hs'1, integral_polar_mul_exp h1 hP n,
    ← hs']
  have h1s : (1 : ℂ) - s' ≠ 0 := fun h => hsub (by linear_combination -h)
  field_simp
  ring

/-- The Fourier coefficients on `(0, P]` as integrals against the characters `e^{-2πiny/P}`. -/
theorem fourierCoeffOn_eq_integral_mul_exp {P : ℝ} (hP : 0 < P) (f : ℝ → ℂ) (n : ℤ) :
    fourierCoeffOn hP f n
      = (P : ℂ)⁻¹ * ∫ y in (0 : ℝ)..P,
          f y * Complex.exp (-(((2 * π * n / P : ℝ) : ℂ) * I) * (y : ℂ)) := by
  have hPc : (P : ℂ) ≠ 0 := by exact_mod_cast hP.ne'
  have hpt : ∀ y : ℝ, fourier (-n) (y : AddCircle (P - 0)) • f y
      = f y * Complex.exp (-(((2 * π * n / P : ℝ) : ℂ) * I) * (y : ℂ)) := by
    intro y
    rw [fourier_coe_apply, smul_eq_mul, mul_comm]
    congr 2
    push_cast
    rw [sub_zero]
    field_simp
  rw [fourierCoeffOn_eq_integral]
  simp_rw [hpt]
  rw [Complex.real_smul]
  push_cast
  rw [sub_zero, one_div]

theorem fourierCoeffOn_ladderDefect {s : ℂ} (h0 : 0 < s.re) (h1 : s.re < 1) {P : ℝ}
    (hP : 0 < P) (n : ℤ) :
    fourierCoeffOn hP (ladderDefect s P) n
      = -((P : ℂ)⁻¹ * (riemannZeta (s + ((2 * π * n / P : ℝ) : ℂ) * I)
          / (s + ((2 * π * n / P : ℝ) : ℂ) * I))) := by
  rw [fourierCoeffOn_eq_integral_mul_exp, integral_ladderDefect_mul_exp h0 h1 hP n, mul_neg]

/-! ### The jump across the period -/

/-- The left limit of the kernel: the integer part `⌊e^x⌋` is replaced by `⌈e^x⌉ - 1`. -/
def ladderKernelLeft (s : ℂ) (x : ℝ) : ℂ :=
  ((Real.exp x : ℝ) : ℂ) * Complex.exp (-s * (x : ℂ))
    - ((⌈Real.exp x⌉ - 1 : ℤ) : ℂ) * Complex.exp (-s * (x : ℂ))

/-- The kernel is right-continuous. -/
theorem tendsto_ladderKernel_right (s : ℂ) (x₀ : ℝ) :
    Tendsto (ladderKernel s) (𝓝[>] x₀) (𝓝 (ladderKernel s x₀)) := by
  have hfloor : Tendsto (fun x : ℝ => ((⌊Real.exp x⌋ : ℤ) : ℂ)) (𝓝[>] x₀)
      (𝓝 ((⌊Real.exp x₀⌋ : ℤ) : ℂ)) := by
    have hexp : Tendsto Real.exp (𝓝[>] x₀) (𝓝[≥] (Real.exp x₀)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        Real.continuous_exp.continuousAt.continuousWithinAt
        (by filter_upwards [self_mem_nhdsWithin] with x hx
            exact Real.exp_le_exp.mpr (le_of_lt hx))
    exact (tendsto_pure_nhds (fun n : ℤ => (n : ℂ)) ⌊Real.exp x₀⌋).comp
      ((tendsto_floor_right_pure_floor (α := ℝ) (Real.exp x₀)).comp hexp)
  have h1 : Tendsto (fun x : ℝ => ((Real.exp x : ℝ) : ℂ) * Complex.exp (-s * (x : ℂ))) (𝓝[>] x₀)
      (𝓝 (((Real.exp x₀ : ℝ) : ℂ) * Complex.exp (-s * (x₀ : ℂ)))) :=
    (by fun_prop : Continuous fun x : ℝ =>
      ((Real.exp x : ℝ) : ℂ) * Complex.exp (-s * (x : ℂ))).continuousAt.continuousWithinAt
  have h2 : Tendsto (fun x : ℝ => Complex.exp (-s * (x : ℂ))) (𝓝[>] x₀)
      (𝓝 (Complex.exp (-s * (x₀ : ℂ)))) :=
    (by fun_prop : Continuous fun x : ℝ => Complex.exp (-s * (x : ℂ))).continuousAt.continuousWithinAt
  rw [ladderKernel_eq_floor s x₀]
  exact (h1.sub (hfloor.mul h2)).congr fun x => (ladderKernel_eq_floor s x).symm

/-- The kernel has the left limit `ladderKernelLeft`. -/
theorem tendsto_ladderKernel_left (s : ℂ) (x₀ : ℝ) :
    Tendsto (ladderKernel s) (𝓝[<] x₀) (𝓝 (ladderKernelLeft s x₀)) := by
  have hfloor : Tendsto (fun x : ℝ => ((⌊Real.exp x⌋ : ℤ) : ℂ)) (𝓝[<] x₀)
      (𝓝 ((⌈Real.exp x₀⌉ - 1 : ℤ) : ℂ)) := by
    have hexp : Tendsto Real.exp (𝓝[<] x₀) (𝓝[<] (Real.exp x₀)) :=
      tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
        Real.continuous_exp.continuousAt.continuousWithinAt
        (by filter_upwards [self_mem_nhdsWithin] with x hx
            exact Real.exp_lt_exp.mpr hx)
    exact (tendsto_pure_nhds (fun n : ℤ => (n : ℂ)) (⌈Real.exp x₀⌉ - 1)).comp
      ((tendsto_floor_left_pure_ceil_sub_one (α := ℝ) (Real.exp x₀)).comp hexp)
  have h1 : Tendsto (fun x : ℝ => ((Real.exp x : ℝ) : ℂ) * Complex.exp (-s * (x : ℂ))) (𝓝[<] x₀)
      (𝓝 (((Real.exp x₀ : ℝ) : ℂ) * Complex.exp (-s * (x₀ : ℂ)))) :=
    (by fun_prop : Continuous fun x : ℝ =>
      ((Real.exp x : ℝ) : ℂ) * Complex.exp (-s * (x : ℂ))).continuousAt.continuousWithinAt
  have h2 : Tendsto (fun x : ℝ => Complex.exp (-s * (x : ℂ))) (𝓝[<] x₀)
      (𝓝 (Complex.exp (-s * (x₀ : ℂ)))) :=
    (by fun_prop : Continuous fun x : ℝ => Complex.exp (-s * (x : ℂ))).continuousAt.continuousWithinAt
  exact (h1.sub (hfloor.mul h2)).congr fun x => (ladderKernel_eq_floor s x).symm

theorem norm_ladderKernelLeft_le (s : ℂ) (x₀ : ℝ) :
    ‖ladderKernelLeft s x₀‖ ≤ Real.exp (-(s.re * x₀)) :=
  le_of_tendsto_of_tendsto (tendsto_ladderKernel_left s x₀).norm
    ((by fun_prop : Continuous fun x : ℝ => Real.exp (-(s.re * x))).continuousAt.continuousWithinAt)
    (Eventually.of_forall fun x => norm_ladderKernel_le s x)

/-- The jump of the kernel at `kP`: the indicator of `e^{kP} ∈ ℤ` times `e^{-skP}`. -/
def jumpTerm (s : ℂ) (P : ℝ) (k : ℕ) : ℂ :=
  ((⌊Real.exp ((k : ℝ) * P)⌋ - ⌈Real.exp ((k : ℝ) * P)⌉ + 1 : ℤ) : ℂ)
    * Complex.exp (-s * (((k : ℝ) * P : ℝ) : ℂ))

theorem ladderKernel_sub_ladderKernelLeft (s : ℂ) (P : ℝ) (k : ℕ) :
    ladderKernel s ((k : ℝ) * P) - ladderKernelLeft s ((k : ℝ) * P) = -jumpTerm s P k := by
  rw [ladderKernel_eq_floor, ladderKernelLeft, jumpTerm]
  push_cast
  ring

theorem jumpTerm_zero (s : ℂ) (P : ℝ) : jumpTerm s P 0 = 1 := by
  simp [jumpTerm]

theorem jumpTerm_of_mem {s : ℂ} {P : ℝ} {k : ℕ} (hk : k ∈ expNatSet P) :
    jumpTerm s P k = Complex.exp (-s * (((k : ℝ) * P : ℝ) : ℂ)) := by
  obtain ⟨m, hm⟩ := hk
  have hfl : ⌊Real.exp ((k : ℝ) * P)⌋ = (m : ℤ) := by rw [hm]; simp
  have hce : ⌈Real.exp ((k : ℝ) * P)⌉ = (m : ℤ) := by rw [hm]; simp
  rw [jumpTerm, hfl, hce]
  simp

theorem jumpTerm_of_notMem {s : ℂ} {P : ℝ} {k : ℕ} (hk : k ∉ expNatSet P) :
    jumpTerm s P k = 0 := by
  have hnotint : Real.exp ((k : ℝ) * P) ∉ Set.range ((↑) : ℤ → ℝ) := by
    rintro ⟨n, hn⟩
    have hpos : (0 : ℝ) < Real.exp ((k : ℝ) * P) := Real.exp_pos _
    have hn0 : (0 : ℤ) ≤ n := by
      have : (0 : ℝ) < (n : ℝ) := by rw [hn]; exact hpos
      exact_mod_cast this.le
    refine hk ⟨n.toNat, ?_⟩
    rw [← hn]
    exact_mod_cast (Int.toNat_of_nonneg hn0).symm
  have hce : ⌈Real.exp ((k : ℝ) * P)⌉ = ⌊Real.exp ((k : ℝ) * P)⌋ + 1 :=
    (Int.ceil_eq_floor_add_one_iff_notMem _).mpr hnotint
  rw [jumpTerm, hce]
  simp

theorem norm_jumpTerm_le (s : ℂ) (P : ℝ) (k : ℕ) :
    ‖jumpTerm s P k‖ ≤ Real.exp (-(s.re * P)) ^ k := by
  classical
  by_cases hk : k ∈ expNatSet P
  · rw [jumpTerm_of_mem hk, Complex.norm_exp, ← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr (le_of_eq ?_)
    simp
    ring
  · rw [jumpTerm_of_notMem hk, norm_zero]
    positivity

/-- **The jump never vanishes.** It is a geometric series over the multiples of the least positive
`k` with `e^{kP} ∈ ℕ`, or the single term `1`. -/
theorem tsum_jumpTerm_ne_zero {s : ℂ} (hs : 0 < s.re) {P : ℝ} (hP : 0 < P) :
    (∑' k : ℕ, jumpTerm s P k) ≠ 0 := by
  classical
  by_cases hex : ∃ k : ℕ, 0 < k ∧ k ∈ expNatSet P
  · obtain ⟨k₀, hk₀pos, hk₀mem, hk₀min⟩ :
        ∃ k₀ : ℕ, 0 < k₀ ∧ k₀ ∈ expNatSet P ∧ ∀ j : ℕ, 0 < j → j ∈ expNatSet P → k₀ ≤ j :=
      ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2,
        fun j hj hjmem => Nat.find_min' hex ⟨hj, hjmem⟩⟩
    set w : ℂ := Complex.exp (-s * (((k₀ : ℝ) * P : ℝ) : ℂ)) with hw
    have hwnorm : ‖w‖ < 1 := by
      rw [hw, Complex.norm_exp, Real.exp_lt_one_iff]
      have hk₀R : (0 : ℝ) < (k₀ : ℝ) := by exact_mod_cast hk₀pos
      have hre : (-s * (((k₀ : ℝ) * P : ℝ) : ℂ)).re = -(s.re * ((k₀ : ℝ) * P)) := by simp
      rw [hre]
      exact neg_neg_of_pos (mul_pos hs (mul_pos hk₀R hP))
    have hinj : Function.Injective fun j : ℕ => k₀ * j := fun i j hij =>
      Nat.eq_of_mul_eq_mul_left hk₀pos hij
    have hsupp : Function.support (jumpTerm s P) ⊆ Set.range fun j : ℕ => k₀ * j := by
      intro k hk
      by_contra hcon
      refine hk (jumpTerm_of_notMem fun hmem => hcon ?_)
      obtain ⟨j, hj⟩ := dvd_of_mem_expNatSet hk₀pos hk₀min hmem hk₀mem
      exact ⟨j, hj.symm⟩
    have hterm : ∀ j : ℕ, jumpTerm s P (k₀ * j) = w ^ j := by
      intro j
      rw [jumpTerm_of_mem (mul_mem_expNatSet hk₀mem j), hw, ← Complex.exp_nat_mul]
      congr 1
      push_cast
      ring
    rw [← hinj.tsum_eq hsupp, tsum_congr hterm, tsum_geometric_of_norm_lt_one hwnorm]
    refine inv_ne_zero fun hcon => ?_
    have hw1 : w = 1 := by linear_combination -hcon
    rw [hw1, norm_one] at hwnorm
    exact lt_irrefl _ hwnorm
  · have hsingle : ∀ k : ℕ, k ≠ 0 → jumpTerm s P k = 0 := fun k hk =>
      jumpTerm_of_notMem fun hmem => hex ⟨k, Nat.pos_of_ne_zero hk, hmem⟩
    rw [tsum_eq_single 0 hsingle, jumpTerm_zero]
    exact one_ne_zero

theorem tendsto_add_const_nhdsGT (a c : ℝ) :
    Tendsto (fun y : ℝ => y + c) (𝓝[>] a) (𝓝[>] (a + c)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (continuous_id.add continuous_const).continuousAt.continuousWithinAt
    (by filter_upwards [self_mem_nhdsWithin] with y hy
        exact (add_lt_add_iff_right c).mpr hy)

theorem tendsto_add_const_nhdsLT (a c : ℝ) :
    Tendsto (fun y : ℝ => y + c) (𝓝[<] a) (𝓝[<] (a + c)) :=
  tendsto_nhdsWithin_of_tendsto_nhds_of_eventually_within _
    (continuous_id.add continuous_const).continuousAt.continuousWithinAt
    (by filter_upwards [self_mem_nhdsWithin] with y hy
        exact (add_lt_add_iff_right c).mpr hy)

/-- The right limit of the periodization at the start of the period. -/
theorem tendsto_ladderSum_right {s : ℂ} (hs : 0 < s.re) {P : ℝ} (hP : 0 < P) :
    Tendsto (ladderSum s P) (𝓝[>] 0) (𝓝 (∑' k : ℕ, ladderKernel s (0 + (k : ℝ) * P))) := by
  have hgeo := summable_geometric_of_lt_one (Real.exp_pos _).le (exp_neg_mul_lt_one hs hP)
  refine HTGeometry.tendsto_tsum_of_tendsto_of_norm_bounded_on (s := Ici (0 : ℝ))
    (mem_of_superset self_mem_nhdsWithin Ioi_subset_Ici_self) hgeo
    (fun k y hy => norm_ladderKernel_shift_le hs.le hy k)
    (Summable.of_norm_bounded hgeo fun k => norm_ladderKernel_shift_le hs.le le_rfl k)
    fun k => (tendsto_ladderKernel_right s _).comp (tendsto_add_const_nhdsGT 0 _)

/-- The left limit of the periodization at the end of the period. -/
theorem tendsto_ladderSum_left {s : ℂ} (hs : 0 < s.re) {P : ℝ} (hP : 0 < P) :
    Tendsto (ladderSum s P) (𝓝[<] P) (𝓝 (∑' k : ℕ, ladderKernelLeft s (P + (k : ℝ) * P))) := by
  have hgeo := summable_geometric_of_lt_one (Real.exp_pos _).le (exp_neg_mul_lt_one hs hP)
  have hbound : ∀ k : ℕ, ‖ladderKernelLeft s (P + (k : ℝ) * P)‖ ≤ Real.exp (-(s.re * P)) ^ k := by
    intro k
    refine (norm_ladderKernelLeft_le s _).trans ?_
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    have : 0 ≤ s.re * P := (mul_pos hs hP).le
    nlinarith
  refine HTGeometry.tendsto_tsum_of_tendsto_of_norm_bounded_on (s := Ici (0 : ℝ))
    (mem_nhdsWithin_of_mem_nhds (Ici_mem_nhds hP)) hgeo
    (fun k y hy => norm_ladderKernel_shift_le hs.le hy k)
    (Summable.of_norm_bounded hgeo hbound)
    fun k => (tendsto_ladderKernel_left s _).comp (tendsto_add_const_nhdsLT P _)

/-- **The periodization jumps across the period.** The right limit at `0` minus the left limit at
`P` of `ladderDefect` is minus the jump series. -/
theorem ladderDefect_limits_sub {s : ℂ} (hs : 0 < s.re) (hs1 : s.re < 1) {P : ℝ} (hP : 0 < P) :
    ((∑' k : ℕ, ladderKernel s (0 + (k : ℝ) * P))
        + Complex.exp ((1 - s) * ((0 : ℝ) : ℂ)) / (Complex.exp ((1 - s) * (P : ℂ)) - 1))
      - ((∑' k : ℕ, ladderKernelLeft s (P + (k : ℝ) * P))
        + Complex.exp ((1 - s) * (P : ℂ)) / (Complex.exp ((1 - s) * (P : ℂ)) - 1))
      = -∑' k : ℕ, jumpTerm s P k := by
  have hE := exp_one_sub_mul_sub_one_ne_zero hs1 hP
  have hgeo := summable_geometric_of_lt_one (Real.exp_pos _).le (exp_neg_mul_lt_one hs hP)
  have hK : Summable fun k : ℕ => ladderKernel s (0 + (k : ℝ) * P) :=
    Summable.of_norm_bounded hgeo fun k => norm_ladderKernel_shift_le hs.le le_rfl k
  have hJ : Summable (jumpTerm s P) := Summable.of_norm_bounded hgeo (norm_jumpTerm_le s P)
  have hLsum : Summable fun k : ℕ => ladderKernelLeft s (P + (k : ℝ) * P) := by
    refine Summable.of_norm_bounded hgeo fun k => (norm_ladderKernelLeft_le s _).trans ?_
    rw [← Real.exp_nat_mul]
    refine Real.exp_le_exp.mpr ?_
    have : 0 ≤ s.re * P := (mul_pos hs hP).le
    nlinarith
  have hK0 : ladderKernel s (0 + ((0 : ℕ) : ℝ) * P) = 0 := by simp [ladderKernel]
  have hstep : ∀ k : ℕ, ladderKernel s (0 + ((k + 1 : ℕ) : ℝ) * P)
      - ladderKernelLeft s (P + (k : ℝ) * P) = -jumpTerm s P (k + 1) := by
    intro k
    rw [← ladderKernel_sub_ladderKernelLeft]
    congr 2 <;> push_cast <;> ring
  have hK' : Summable fun k : ℕ => ladderKernel s (0 + ((k + 1 : ℕ) : ℝ) * P) :=
    (summable_nat_add_iff 1).mpr hK
  have hJ' : Summable fun k : ℕ => jumpTerm s P (k + 1) := (summable_nat_add_iff 1).mpr hJ
  rw [hK.tsum_eq_zero_add, hK0, zero_add, hJ.tsum_eq_zero_add, jumpTerm_zero]
  have hdiff : (∑' k : ℕ, ladderKernel s (0 + ((k + 1 : ℕ) : ℝ) * P))
      - ∑' k : ℕ, ladderKernelLeft s (P + (k : ℝ) * P) = -∑' k : ℕ, jumpTerm s P (k + 1) := by
    rw [← hK'.tsum_sub hLsum, ← tsum_neg]
    exact tsum_congr hstep
  have h0 : Complex.exp ((1 - s) * ((0 : ℝ) : ℂ)) = 1 := by simp
  rw [h0]
  have hfrac : (1 : ℂ) / (Complex.exp ((1 - s) * (P : ℂ)) - 1)
      - Complex.exp ((1 - s) * (P : ℂ)) / (Complex.exp ((1 - s) * (P : ℂ)) - 1) = -1 := by
    field_simp
    ring
  linear_combination hdiff + hfrac

/-! ### Divergence along every vertical progression -/

theorem memLp_ladderDefect {s : ℂ} (hs : 0 < s.re) {P : ℝ} (hP : 0 < P) :
    MemLp (ladderDefect s P) 2 (volume.restrict (Ioc (0 : ℝ) P)) := by
  haveI : IsFiniteMeasure (volume.restrict (Ioc (0 : ℝ) P)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_Ioc_lt_top⟩
  have hcont : Continuous fun y : ℝ =>
      Complex.exp ((1 - s) * (y : ℂ)) / (Complex.exp ((1 - s) * (P : ℂ)) - 1) := by fun_prop
  have hmeas : Measurable (ladderDefect s P) := (measurable_ladderSum s P).add hcont.measurable
  refine MemLp.of_bound hmeas.aestronglyMeasurable
    ((1 - Real.exp (-(s.re * P)))⁻¹
      + Real.exp (|1 - s.re| * P) / ‖Complex.exp ((1 - s) * (P : ℂ)) - 1‖)
    ((ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun y hy => ?_))
  refine (norm_add_le _ _).trans (add_le_add (norm_ladderSum_le hs hP hy.1.le) ?_)
  rw [norm_div, Complex.norm_exp]
  refine div_le_div_of_nonneg_right (Real.exp_le_exp.mpr ?_) (norm_nonneg _)
  have hre : ((1 - s) * (y : ℂ)).re = (1 - s.re) * y := by simp
  rw [hre]
  have h1 : (1 - s.re) * y ≤ |1 - s.re| * y := mul_le_mul_of_nonneg_right (le_abs_self _) hy.1.le
  exact h1.trans (mul_le_mul_of_nonneg_left hy.2 (abs_nonneg _))

/-- **Divergence along every vertical progression.** For `ρ` in the open strip and any step
`T > 0`, `Σ_{n ∈ ℤ} |ζ(ρ + inT)| / |ρ + inT| = ∞`: otherwise the periodized Laplace kernel would
have absolutely summable Fourier coefficients and no jump across its period `2π/T`. -/
theorem not_summable_norm_riemannZeta_div {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {T : ℝ}
    (hT : 0 < T) :
    ¬ Summable fun n : ℤ =>
      ‖riemannZeta (ρ + ((n * T : ℝ) : ℂ) * I) / (ρ + ((n * T : ℝ) : ℂ) * I)‖ := by
  intro hsum
  set P : ℝ := 2 * π / T with hPdef
  have hP : 0 < P := by positivity
  have hfreq : ∀ n : ℤ, (2 * π * n / P : ℝ) = n * T := by
    intro n
    rw [hPdef]
    field_simp
  have hcoef : Summable fun n : ℤ => ‖fourierCoeffOn hP (ladderDefect ρ P) n‖ := by
    refine (hsum.mul_left P⁻¹).congr fun n => ?_
    rw [fourierCoeffOn_ladderDefect h0 h1 hP n, hfreq n, norm_neg, norm_mul, norm_inv,
      Complex.norm_real, Real.norm_of_nonneg hP.le]
  have hcontP : Continuous fun y : ℝ =>
      Complex.exp ((1 - ρ) * (y : ℂ)) / (Complex.exp ((1 - ρ) * (P : ℂ)) - 1) := by fun_prop
  have hLa : Tendsto (ladderDefect ρ P) (𝓝[>] 0) (𝓝 ((∑' k : ℕ, ladderKernel ρ (0 + (k : ℝ) * P))
      + Complex.exp ((1 - ρ) * ((0 : ℝ) : ℂ)) / (Complex.exp ((1 - ρ) * (P : ℂ)) - 1))) :=
    (tendsto_ladderSum_right h0 hP).add hcontP.continuousAt.continuousWithinAt
  have hLb : Tendsto (ladderDefect ρ P) (𝓝[<] P)
      (𝓝 ((∑' k : ℕ, ladderKernelLeft ρ (P + (k : ℝ) * P))
        + Complex.exp ((1 - ρ) * (P : ℂ)) / (Complex.exp ((1 - ρ) * (P : ℂ)) - 1))) :=
    (tendsto_ladderSum_left h0 hP).add hcontP.continuousAt.continuousWithinAt
  have heq := endpoint_limits_eq_of_summable_fourierCoeffOn hP (memLp_ladderDefect h0 hP) hcoef
    hLa hLb
  have hjump := ladderDefect_limits_sub h0 h1 hP
  rw [heq, sub_self] at hjump
  exact tsum_jumpTerm_ne_zero h0 hP (neg_eq_zero.mp hjump.symm)

/-- **Infinitely many points of a vertical progression in the strip are not zeros of `ζ`.** -/
theorem exists_riemannZeta_ne_zero_progression {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1) {T : ℝ}
    (hT : 0 < T) (N : ℕ) :
    ∃ n : ℤ, (N : ℤ) ≤ |n| ∧ riemannZeta (ρ + ((n * T : ℝ) : ℂ) * I) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine not_summable_norm_riemannZeta_div h0 h1 hT
    (summable_of_ne_finset_zero (s := Finset.Ioo (-(N : ℤ)) N) fun n hn => ?_)
  have hle : (N : ℤ) ≤ |n| := by
    by_contra hlt
    exact hn (Finset.mem_Ioo.mpr (abs_lt.mp (not_le.mp hlt)))
  rw [hcon n hle, zero_div, norm_zero]

/-- No vertical progression consists of zeros of `ξ`, wherever it lies. -/
theorem not_forall_xi_progression (ρ : ℂ) {T : ℝ} (hT : 0 < T) :
    ¬ ∀ k : ℤ, xi (ρ + ((k * T : ℝ) : ℂ) * I) = 0 := by
  intro h
  have hρ : xi ρ = 0 := by simpa using h 0
  have h0 := re_pos_of_xi_eq_zero hρ
  have h1 := re_lt_one_of_xi_eq_zero hρ
  obtain ⟨n, -, hn⟩ := exists_riemannZeta_ne_zero_progression h0 h1 hT 0
  have hre : (ρ + ((n * T : ℝ) : ℂ) * I).re = ρ.re := by simp
  refine hn ((xi_eq_zero_iff (by rw [hre]; exact h0) fun h1' => ?_).mp (h n))
  rw [h1', Complex.one_re] at hre
  linarith

/-! ### Classes of one Frobenius -/

/-- **No conjugacy class of one Frobenius lies in the zero set.** For a Frobenius `q > 1` and any
`ρ`, some mode with the eigenvalue `q^ρ` is not a zero of `ξ`. -/
theorem exists_conjugate_not_zero {q : ℝ} (hq : 1 < q) (ρ : ℂ) :
    ∃ ρ' : ℂ, (q : ℂ) ^ ρ' = (q : ℂ) ^ ρ ∧ xi ρ' ≠ 0 := by
  have hlog : 0 < Real.log q := Real.log_pos hq
  have hT : 0 < 2 * π / Real.log q := by positivity
  have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hq).ne'
  have hex : ∃ k : ℤ, xi (ρ + ((k * (2 * π / Real.log q) : ℝ) : ℂ) * I) ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact not_forall_xi_progression ρ hT hcon
  obtain ⟨k, hk⟩ := hex
  refine ⟨_, ?_, hk⟩
  rw [Complex.cpow_def_of_ne_zero hqc, Complex.cpow_def_of_ne_zero hqc,
    ← Complex.ofReal_log (zero_lt_one.trans hq).le]
  have hlogc : (Real.log q : ℂ) ≠ 0 := by exact_mod_cast hlog.ne'
  have h : (Real.log q : ℂ) * (ρ + ((k * (2 * π / Real.log q) : ℝ) : ℂ) * I)
      = (Real.log q : ℂ) * ρ + (k : ℂ) * (2 * π * I) := by
    push_cast
    field_simp
  rw [h, Complex.exp_add, Complex.exp_int_mul_two_pi_mul_I, mul_one]

/-- **`ξ` has no local factor at one Frobenius.** For `q > 1` and `u ≠ 0` the function `q^{-s} - u`
has a zero that is not a zero of `ξ`. -/
theorem exists_zero_localFactor_not_zero {q : ℝ} (hq : 1 < q) {u : ℂ} (hu : u ≠ 0) :
    ∃ s : ℂ, (q : ℂ) ^ (-s) = u ∧ xi s ≠ 0 := by
  have hlog : 0 < Real.log q := Real.log_pos hq
  have hqc : (q : ℂ) ≠ 0 := by exact_mod_cast (zero_lt_one.trans hq).ne'
  have hlogc : (Real.log q : ℂ) ≠ 0 := by exact_mod_cast hlog.ne'
  set s₀ : ℂ := -(Complex.log u / (Real.log q : ℂ)) with hs₀
  have hs₀u : (q : ℂ) ^ (-s₀) = u := by
    rw [Complex.cpow_def_of_ne_zero hqc, ← Complex.ofReal_log (zero_lt_one.trans hq).le, hs₀,
      neg_neg, mul_div_cancel₀ _ hlogc, Complex.exp_log hu]
  obtain ⟨s, hs, hxi⟩ := exists_conjugate_not_zero hq s₀
  refine ⟨s, ?_, hxi⟩
  rw [Complex.cpow_neg, hs, ← Complex.cpow_neg, hs₀u]

/-- A polynomial in `q^{-s}` with a nonzero root has a zero that is not a zero of `ξ`: the zeta
polynomial of no curve over a finite field divides `ξ`. -/
theorem exists_zero_polynomial_not_zero {q : ℝ} (hq : 1 < q) {p : Polynomial ℂ} {u : ℂ}
    (hu : u ≠ 0) (hroot : p.eval u = 0) :
    ∃ s : ℂ, p.eval ((q : ℂ) ^ (-s)) = 0 ∧ xi s ≠ 0 := by
  obtain ⟨s, hs, hxi⟩ := exists_zero_localFactor_not_zero hq hu
  exact ⟨s, by rw [hs, hroot], hxi⟩

open GaloisForLFunctions.ArithmeticCastelnuovoSeveri in
/-- The zeros of a curve over a finite field attached to one Frobenius eigenvalue are a full
vertical progression; they are not all zeros of `ξ`. -/
theorem exists_curve_zero_not_zero {ι : Type*} [Fintype ι] (D : CurveDatum ι) (i : ι) :
    ∃ k : ℤ, xi (D.zetaZero i k) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  refine not_forall_xi_progression (D.zetaZero i 0) D.period_pos fun k => ?_
  have h : D.zetaZero i 0 + ((k * D.period : ℝ) : ℂ) * I = D.zetaZero i k := by
    apply Complex.ext
    · simp [CurveDatum.re_zetaZero]
    · simp [CurveDatum.im_zetaZero]
  rw [h]
  exact hcon k

/-! ### The periodicity dichotomy -/

/-- No zero of `ζ` in the open strip lies on a full vertical progression of zeros. -/
theorem aperiodicZeroAt_riemannZeta {ρ : ℂ} (h0 : 0 < ρ.re) (h1 : ρ.re < 1)
    (hρ : riemannZeta ρ = 0) : AperiodicZeroAt riemannZeta ρ := by
  refine ⟨hρ, ?_⟩
  rintro ⟨T, hT, h⟩
  obtain ⟨n, -, hn⟩ := exists_riemannZeta_ne_zero_progression h0 h1 hT 0
  refine hn ?_
  have := h n
  rwa [show ((n : ℂ) * (T : ℂ)) = (((n * T : ℝ)) : ℂ) by push_cast; ring] at this

/-- **The periodicity dichotomy of `ζ` is the Riemann hypothesis.** A zero in the strip is on the
line or on a full vertical progression of zeros exactly when RH holds; the second alternative never
occurs. -/
theorem periodicityDichotomy_zeta_iff_riemannHypothesis :
    PeriodicityDichotomy riemannZeta ↔ RiemannHypothesis := by
  refine RHTower.periodicityDichotomy_zeta_iff_riemannHypothesis fun ρ h0 h1 _ => ?_
  rintro ⟨T, hT, h⟩
  exact (aperiodicZeroAt_riemannZeta h0 h1 (by simpa using h 0)).2 ⟨T, hT, h⟩

end GaloisForLFunctions.InfiniteRankPurityTheory
