import GaloisForLFunctions.HTGeometry.WaveTracePoleDivergence
import GaloisForLFunctions.HTGeometry.WaveTraceConvexRecurrence
import GaloisForLFunctions.RHTower.LandauIntegralTransfer

/-!
# Landau transfer for an eventually one-signed wave trace

An eventually nonnegative wave trace is the density of a positive measure on a time tail. The
complex moment generating function of that measure is the shifted Laplace integral of the wave
trace read backwards from a real base point, so holomorphy of the active-pole transform is
exactly the input Landau's theorem consumes.
-/

open Complex Filter MeasureTheory ProbabilityTheory Set Topology
open GaloisForLFunctions.HTGeometry
open scoped ENNReal NNReal

namespace RHTower

noncomputable section

variable {G : Type*} (S : WaveSpectrum G)

/-- Density of the positive measure carried by an eventually nonnegative wave trace. -/
def traceDensity (P : Polynomial ℝ) (sigma : ℝ) (t : ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (S.realWaveTrace P t * Real.exp (-sigma * t))

/-- The positive measure carried by an eventually nonnegative wave trace. -/
def traceMeasure (P : Polynomial ℝ) (T sigma : ℝ) : Measure ℝ :=
  (volume.restrict (Ioi T)).withDensity (traceDensity S P sigma)

theorem measurable_traceDensity (P : Polynomial ℝ) (sigma : ℝ) :
    Measurable (traceDensity S P sigma) := by
  unfold traceDensity
  exact ENNReal.measurable_ofReal.comp
    (((S.continuous_realWaveTrace P).mul (by fun_prop)).measurable)

theorem traceDensity_lt_top (P : Polynomial ℝ) (sigma : ℝ) (t : ℝ) :
    traceDensity S P sigma t < ⊤ := by
  unfold traceDensity
  exact ENNReal.ofReal_lt_top

theorem toReal_traceDensity_of_nonneg (P : Polynomial ℝ) {sigma t : ℝ}
    (ht : 0 ≤ S.realWaveTrace P t) :
    (traceDensity S P sigma t).toReal = S.realWaveTrace P t * Real.exp (-sigma * t) := by
  unfold traceDensity
  rw [ENNReal.toReal_ofReal]
  positivity

/-- Integrability of an exponential against the trace measure is integrability of the shifted
Laplace integrand on the tail. -/
theorem integrable_exp_traceMeasure_iff (P : Polynomial ℝ) {T sigma : ℝ}
    (hpos : ∀ t, T < t → 0 ≤ S.realWaveTrace P t) (rho : ℝ) :
    Integrable (fun t : ℝ => Real.exp (rho * t)) (traceMeasure S P T sigma) ↔
      IntegrableOn (fun t : ℝ => S.realWaveTrace P t * Real.exp ((rho - sigma) * t))
        (Ioi T) := by
  rw [traceMeasure, integrable_withDensity_iff (measurable_traceDensity S P sigma)
    (Filter.Eventually.of_forall fun t => traceDensity_lt_top S P sigma t)]
  refine integrable_congr ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  rw [toReal_traceDensity_of_nonneg S P (hpos t ht),
    show (rho - sigma) * t = rho * t + -sigma * t by ring, Real.exp_add]
  ring

/-- The complex moment generating function of the trace measure is the shifted Laplace
integral of the wave trace. -/
theorem complexMGF_traceMeasure (P : Polynomial ℝ) {T sigma : ℝ}
    (hpos : ∀ t, T < t → 0 ≤ S.realWaveTrace P t) (z : ℂ) :
    complexMGF (fun t : ℝ => t) (traceMeasure S P T sigma) z =
      ∫ t in Ioi T, S.waveTrace P t * Complex.exp (-((sigma : ℂ) - z) * t) := by
  rw [complexMGF, traceMeasure,
    integral_withDensity_eq_integral_toReal_smul (measurable_traceDensity S P sigma)
      (Filter.Eventually.of_forall fun t => traceDensity_lt_top S P sigma t)]
  refine setIntegral_congr_ae measurableSet_Ioi ?_
  filter_upwards with t ht
  rw [toReal_traceDensity_of_nonneg S P (hpos t ht), real_smul, ← S.ofReal_realWaveTrace P t]
  rw [show -((sigma : ℂ) - z) * (t : ℂ) = z * (t : ℂ) + (-(sigma : ℂ) * (t : ℂ)) by ring,
    Complex.exp_add]
  push_cast
  ring

/-! ## Convergence of the tail Laplace integral -/

/-- Convergence of the Laplace integral of the wave trace on the tail `(T, ∞)`. -/
def TailConv (S : WaveSpectrum G) (P : Polynomial ℝ) (T sigma : ℝ) : Prop :=
  IntegrableOn (fun t : ℝ => S.realWaveTrace P t * Real.exp (-sigma * t)) (Ioi T)

theorem tailConv_mono (P : Polynomial ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t → 0 ≤ S.realWaveTrace P t) {sigma0 sigma : ℝ}
    (h : TailConv S P T sigma0) (hle : sigma0 ≤ sigma) : TailConv S P T sigma := by
  refine Integrable.mono' h
    (((S.continuous_realWaveTrace P).mul (by fun_prop)).aestronglyMeasurable.restrict) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := le_trans hT (le_of_lt ht)
  have hHt : 0 ≤ S.realWaveTrace P t := hpos t ht
  have hexp : Real.exp (-sigma * t) ≤ Real.exp (-sigma0 * t) :=
    Real.exp_le_exp.mpr (by nlinarith)
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  exact mul_le_mul_of_nonneg_left hexp hHt

theorem tailConv_base (P : Polynomial ℝ) {T : ℝ} (hT : 0 ≤ T) :
    TailConv S P T (S.width + 1) := by
  set C : ℝ := polyBallBound P (S.lower⁻¹ ^ 2) * ∑' g : G, ‖S.gamma g‖⁻¹ ^ 3 with hC
  have hCnn : 0 ≤ C := by
    have h1 : 0 ≤ polyBallBound P (S.lower⁻¹ ^ 2) := polyBallBound_nonneg P (by positivity)
    have h2 : 0 ≤ ∑' g : G, ‖S.gamma g‖⁻¹ ^ 3 :=
      tsum_nonneg fun g => by positivity
    rw [hC]; positivity
  refine Integrable.mono' ((integrableOn_exp_mul_Ioi (a := (-1 : ℝ)) (by norm_num) T).const_mul C)
    (((S.continuous_realWaveTrace P).mul (by fun_prop)).aestronglyMeasurable.restrict) ?_
  filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
  have ht0 : 0 ≤ t := le_trans hT (le_of_lt ht)
  have hbound : ‖S.realWaveTrace P t‖ ≤ Real.exp (S.width * t) * C := by
    have h1 : ‖S.realWaveTrace P t‖ ≤ ‖S.waveTrace P t‖ := by
      rw [Real.norm_eq_abs]
      exact Complex.abs_re_le_norm _
    refine le_trans h1 ?_
    have h2 := S.norm_waveTrace_le P t
    rw [abs_of_nonneg ht0] at h2
    rw [hC]
    calc ‖S.waveTrace P t‖
        ≤ Real.exp (S.width * t) * polyBallBound P (S.lower⁻¹ ^ 2) *
            ∑' g : G, ‖S.gamma g‖⁻¹ ^ 3 := h2
      _ = Real.exp (S.width * t) *
            (polyBallBound P (S.lower⁻¹ ^ 2) * ∑' g : G, ‖S.gamma g‖⁻¹ ^ 3) := by ring
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hexpeq : Real.exp (S.width * t) * Real.exp (-(S.width + 1) * t) = Real.exp (-1 * t) := by
    rw [← Real.exp_add]
    congr 1
    ring
  calc |S.realWaveTrace P t| * Real.exp (-(S.width + 1) * t)
      ≤ (Real.exp (S.width * t) * C) * Real.exp (-(S.width + 1) * t) := by
        refine mul_le_mul_of_nonneg_right ?_ (Real.exp_nonneg _)
        rw [← Real.norm_eq_abs]
        exact hbound
    _ = C * Real.exp (-1 * t) := by rw [← hexpeq]; ring

theorem integrableExpSet_traceMeasure (P : Polynomial ℝ) {T sigma : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t → 0 ≤ S.realWaveTrace P t) {sigma0 : ℝ}
    (hconv : TailConv S P T sigma0) :
    Iio (sigma - sigma0) ⊆ integrableExpSet (fun t : ℝ => t) (traceMeasure S P T sigma) := by
  intro rho hrho
  have hkey : TailConv S P T (sigma - rho) :=
    tailConv_mono S P hT hpos hconv (by simp only [mem_Iio] at hrho; linarith)
  refine (integrable_exp_traceMeasure_iff S P hpos rho).mpr ?_
  have heq : ∀ t : ℝ, S.realWaveTrace P t * Real.exp ((rho - sigma) * t) =
      S.realWaveTrace P t * Real.exp (-(sigma - rho) * t) := by
    intro t
    congr 2
    ring
  simp only [heq]
  exact hkey

/-! ## The Landau step -/

theorem abs_im_ge_of_mem_poleSet {rho0 : ℝ} (hre : ∀ g : G, rho0 ≤ |(S.gamma g).re|)
    {s : ℂ} (hs : s ∈ S.poleSet) : rho0 ≤ |s.im| := by
  obtain ⟨g, hg⟩ := hs
  have hfac : (s - Complex.I * S.gamma g) * (s + Complex.I * S.gamma g) = 0 := by
    linear_combination hg - (S.gamma g ^ 2) * Complex.I_sq
  have him : (Complex.I * S.gamma g).im = (S.gamma g).re := by
    simp [Complex.mul_im]
  rcases mul_eq_zero.mp hfac with h | h
  · have hval : s = Complex.I * S.gamma g := by linear_combination h
    rw [hval, him]
    exact hre g
  · have hval : s = -(Complex.I * S.gamma g) := by linear_combination h
    rw [hval, Complex.neg_im, him, abs_neg]
    exact hre g

/-- **One Landau step.** Holomorphy of the active-pole transform on a pole-free disc centred on
the real axis pushes the convergence abscissa strictly left. -/
theorem tailConv_step [Countable G] (hlf : S.IsLocallyFiniteSpectrum) {rho0 : ℝ} (hrho0 : 0 < rho0)
    (hre : ∀ g : G, rho0 ≤ |(S.gamma g).re|) (P : Polynomial ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t → 0 ≤ S.realWaveTrace P t) {sigma0 r : ℝ}
    (hconv : TailConv S P T sigma0) (hr : 0 < r) (hrlt : r < rho0) :
    TailConv S P T (sigma0 - r / 8) := by
  classical
  set sigma : ℝ := sigma0 + r / 4 with hsigmadef
  have hlt : sigma0 < sigma := by rw [hsigmadef]; linarith
  set mu : Measure ℝ := traceMeasure S P T sigma with hmu
  set A : ℂ → ℂ := complexMGF (fun t : ℝ => t) mu with hA
  set Bfun : ℂ → ℂ := fun z => S.poleTransform P T ((sigma : ℂ) - z) with hBfun
  -- pole-freeness of the reflected half-strip
  have hnotpole : ∀ z : ℂ, |z.im| < rho0 → ((sigma : ℂ) - z) ∉ S.poleSet := by
    intro z hz hp
    have hge := abs_im_ge_of_mem_poleSet S hre hp
    have him : ((sigma : ℂ) - z).im = -z.im := by simp
    rw [him, abs_neg] at hge
    linarith
  have hBdiff : ∀ z : ℂ, |z.im| < rho0 → DifferentiableAt ℂ Bfun z := by
    intro z hz
    have hmem : ((sigma : ℂ) - z) ∈ (S.poleSet)ᶜ := hnotpole z hz
    have h1 : DifferentiableAt ℂ (S.poleTransform P T) ((sigma : ℂ) - z) :=
      (S.differentiableOn_poleTransform_compl hlf P T).differentiableAt
        ((S.isOpen_compl_poleSet hlf).mem_nhds hmem)
    exact h1.comp z (by fun_prop)
  -- the convex analyticity domain
  set U : Set ℂ := {z : ℂ | |z.im| < rho0 / 2} ∩ {z : ℂ | z.re < sigma - sigma0} with hU
  have hUopen : IsOpen U :=
    (isOpen_lt (by fun_prop) continuous_const).inter
      (isOpen_lt Complex.continuous_re continuous_const)
  have hUconv : Convex ℝ U := by
    have hlinre : IsLinearMap ℝ (fun z : ℂ => z.re) := ⟨fun x y => by simp, fun c x => by simp⟩
    have hlinim : IsLinearMap ℝ (fun z : ℂ => z.im) := ⟨fun x y => by simp, fun c x => by simp⟩
    have hcre : Convex ℝ {z : ℂ | z.re < sigma - sigma0} := convex_halfSpace_lt hlinre _
    have hcim1 : Convex ℝ {z : ℂ | z.im < rho0 / 2} := convex_halfSpace_lt hlinim _
    have hcim2 : Convex ℝ {z : ℂ | -(rho0 / 2) < z.im} := convex_halfSpace_gt hlinim _
    have hsplit : {z : ℂ | |z.im| < rho0 / 2} =
        {z : ℂ | -(rho0 / 2) < z.im} ∩ {z : ℂ | z.im < rho0 / 2} := by
      ext z
      simp [abs_lt]
    rw [hU, hsplit]
    exact (hcim2.inter hcim1).inter hcre
  have h0U : (0 : ℂ) ∈ U := by
    constructor
    · simp only [Set.mem_setOf_eq, Complex.zero_im, abs_zero]
      linarith
    · simp only [Set.mem_setOf_eq, Complex.zero_re]
      rw [hsigmadef]; linarith
  have hAan : AnalyticOnNhd ℂ A U := by
    refine analyticOnNhd_complexMGF.mono ?_
    rintro z ⟨-, hz2⟩
    exact (interior_maximal (integrableExpSet_traceMeasure S P hT hpos hconv) isOpen_Iio) hz2
  have hBan : AnalyticOnNhd ℂ Bfun U := by
    refine DifferentiableOn.analyticOnNhd (fun z hz => ?_) hUopen
    exact (hBdiff z (by have := hz.1; simp only [Set.mem_setOf_eq] at this; linarith)).differentiableWithinAt
  -- agreement far to the left
  have hAB : ∀ z : ℂ, z.re < sigma - S.width → A z = Bfun z := by
    intro z hz
    have hside : S.width < ((sigma : ℂ) - z).re := by
      simp only [Complex.sub_re, Complex.ofReal_re]
      linarith
    rw [hA, hmu, complexMGF_traceMeasure S P hpos z, hBfun]
    show ∫ t in Ioi T, S.waveTrace P t * Complex.exp (-((sigma : ℂ) - z) * t) =
      S.poleTransform P T ((sigma : ℂ) - z)
    rw [S.poleTransform_eq_integral P (s := (sigma : ℂ) - z) hside hT]
  set c : ℝ := min (sigma - S.width) (sigma - sigma0) - 1 with hc
  set z1 : ℂ := (c : ℂ) with hz1
  have hz1re : z1.re = c := by rw [hz1]; simp
  have hz1im : z1.im = 0 := by rw [hz1]; simp
  have hz1U : z1 ∈ U := by
    constructor
    · simp only [Set.mem_setOf_eq, hz1im, abs_zero]
      linarith
    · simp only [Set.mem_setOf_eq, hz1re, hc]
      have := min_le_right (sigma - S.width) (sigma - sigma0)
      linarith
  have hz1lt : z1.re < sigma - S.width := by
    rw [hz1re, hc]
    have := min_le_left (sigma - S.width) (sigma - sigma0)
    linarith
  have hev : A =ᶠ[nhds z1] Bfun := by
    have hVopen : IsOpen {z : ℂ | z.re < sigma - S.width} :=
      isOpen_lt Complex.continuous_re continuous_const
    filter_upwards [hVopen.mem_nhds hz1lt] with z hz
    exact hAB z hz
  have heq : Set.EqOn A Bfun U :=
    hAan.eqOn_of_preconnected_of_eventuallyEq hBan hUconv.isPreconnected hz1U hev
  have hagree : Bfun =ᶠ[nhds 0] A := by
    filter_upwards [hUopen.mem_nhds h0U] with z hz
    exact (heq hz).symm
  -- Landau transfer
  set R : NNReal := Real.toNNReal (r / 2) with hR
  have hRcoe : (R : ℝ) = r / 2 := by
    rw [hR, Real.coe_toNNReal _ (by linarith)]
  have hGd : DifferentiableOn ℂ Bfun (Metric.closedBall 0 (R : ℝ)) := by
    intro z hz
    refine (hBdiff z ?_).differentiableWithinAt
    have h1 : ‖z‖ ≤ (R : ℝ) := by simpa [Complex.dist_eq] using hz
    have h2 : |z.im| ≤ ‖z‖ := Complex.abs_im_le_norm z
    rw [hRcoe] at h1
    linarith
  have hX0 : ∀ᵐ t ∂mu, 0 ≤ t := by
    rw [hmu, traceMeasure]
    refine Filter.Eventually.filter_mono
      (MeasureTheory.withDensity_absolutelyContinuous _ _).ae_le ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with t ht
    exact le_trans hT (le_of_lt ht)
  have hzero : (0 : ℝ) ∈ interior (integrableExpSet (fun t : ℝ => t) mu) := by
    refine (interior_maximal (integrableExpSet_traceMeasure S P hT hpos hconv) isOpen_Iio) ?_
    simp only [Set.mem_Iio]
    rw [hsigmadef]; linarith
  have hres := landau_complexMGF_integrable_transfer (X := fun t : ℝ => t) (mu := mu)
    hX0 hzero hGd hagree (rho := 3 * r / 8) (by linarith) (by rw [hRcoe]; linarith)
  have hfinal := (integrable_exp_traceMeasure_iff S P hpos (3 * r / 8)).mp hres
  have heqf : ∀ t : ℝ,
      S.realWaveTrace P t * Real.exp ((3 * r / 8 - sigma) * t) =
        S.realWaveTrace P t * Real.exp (-(sigma0 - r / 8) * t) := by
    intro t
    congr 2
    rw [hsigmadef]
    ring
  simp only [heqf] at hfinal
  exact hfinal

/-! ## Marching the abscissa to minus infinity -/

theorem tailConv_iterate [Countable G] (hlf : S.IsLocallyFiniteSpectrum) {rho0 : ℝ}
    (hrho0 : 0 < rho0) (hre : ∀ g : G, rho0 ≤ |(S.gamma g).re|) (P : Polynomial ℝ) {T : ℝ}
    (hT : 0 ≤ T) (hpos : ∀ t, T < t → 0 ≤ S.realWaveTrace P t) {r : ℝ} (hr : 0 < r)
    (hrlt : r < rho0) (n : ℕ) :
    TailConv S P T (S.width + 1 - n * (r / 8)) := by
  induction n with
  | zero => simpa using tailConv_base S P hT
  | succ n ih =>
      have hstep := tailConv_step S hlf hrho0 hre P hT hpos ih hr hrlt
      have heq : S.width + 1 - (n : ℝ) * (r / 8) - r / 8 =
          S.width + 1 - ((n : ℕ) + 1 : ℕ) * (r / 8) := by
        push_cast
        ring
      rwa [heq] at hstep

theorem tailConv_all [Countable G] (hlf : S.IsLocallyFiniteSpectrum)
    (hnoim : ∀ g : G, (S.gamma g).re ≠ 0) (P : Polynomial ℝ) {T : ℝ} (hT : 0 ≤ T)
    (hpos : ∀ t, T < t → 0 ≤ S.realWaveTrace P t) (sigma : ℝ) :
    TailConv S P T sigma := by
  obtain ⟨rho0, hrho0, hre⟩ := S.exists_re_lower_bound hlf hnoim
  set r : ℝ := rho0 / 2 with hrdef
  have hr : 0 < r := by rw [hrdef]; linarith
  have hrlt : r < rho0 := by rw [hrdef]; linarith
  obtain ⟨n, hn⟩ := exists_nat_gt ((S.width + 1 - sigma) / (r / 8))
  have hstep := tailConv_iterate S hlf hrho0 hre P hT hpos hr hrlt n
  refine tailConv_mono S P hT hpos hstep ?_
  have hpos8 : (0 : ℝ) < r / 8 := by linarith
  rw [div_lt_iff₀ hpos8] at hn
  linarith

/-! ## Active frequencies of a nonzero weight -/

theorem exists_active_of_ne_zero (hinf : (Set.range fun g : G => S.gamma g ^ 2).Infinite)
    {P : Polynomial ℝ} (hP : P ≠ 0) : ∃ g : G, S.traceCoeff P g ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  set Q : Polynomial ℂ := P.map (algebraMap ℝ ℂ) with hQ
  have hQne : Q ≠ 0 := by
    rw [hQ]
    exact (Polynomial.map_ne_zero_iff (algebraMap ℝ ℂ).injective).mpr hP
  have hroots : {x : ℂ | Q.IsRoot x}.Finite := Polynomial.finite_setOf_isRoot hQne
  have hmem : ∀ g : G, ((S.gamma g ^ 2)⁻¹ : ℂ) ∈ {x : ℂ | Q.IsRoot x} := by
    intro g
    have hz := hcon g
    rw [WaveSpectrum.traceCoeff, div_eq_zero_iff] at hz
    have hnum : Polynomial.aeval ((S.gamma g ^ 2)⁻¹) P = 0 := by
      rcases hz with h | h
      · exact h
      · exact absurd h (pow_ne_zero 3 (S.gamma_ne_zero g))
    simpa [Polynomial.IsRoot, hQ, Polynomial.eval_map, ← Polynomial.aeval_def] using hnum
  have hsub : (Set.range fun g : G => ((S.gamma g ^ 2)⁻¹ : ℂ)) ⊆ {x : ℂ | Q.IsRoot x} := by
    rintro _ ⟨g, rfl⟩
    exact hmem g
  have hinvinf : (Set.range fun g : G => ((S.gamma g ^ 2)⁻¹ : ℂ)).Infinite := by
    have himg : (Set.range fun g : G => ((S.gamma g ^ 2)⁻¹ : ℂ)) =
        (fun x : ℂ => x⁻¹) '' (Set.range fun g : G => S.gamma g ^ 2) := by
      rw [← Set.range_comp]
      rfl
    rw [himg]
    exact hinf.image (Set.injOn_of_injective inv_injective)
  exact hinvinf (hroots.subset hsub)

/-! ## Cofinal sign escape -/

/-- **Landau sign escape.** A locally finite conjugation-stable spectrum with infinitely many
distinct frequency squares and no purely imaginary frequency drives every nonzero polynomial
wave trace strictly negative after every time. -/
theorem cofinalWaveSignEscape [Countable G] (hlf : S.IsLocallyFiniteSpectrum)
    (hnoim : ∀ g : G, (S.gamma g).re ≠ 0)
    (hinf : (Set.range fun g : G => S.gamma g ^ 2).Infinite) :
    S.CofinalWaveSignEscape := by
  intro P hP T
  by_contra hcon
  push Not at hcon
  set T' : ℝ := max T 0 with hT'
  have hT'nn : 0 ≤ T' := le_max_right _ _
  have hpos : ∀ t, T' < t → 0 ≤ S.realWaveTrace P t := by
    intro t ht
    exact hcon t (lt_of_le_of_lt (le_max_left _ _) ht)
  have hall : ∀ sigma : ℝ, TailConv S P T' sigma :=
    tailConv_all S hlf hnoim P hT'nn hpos
  -- the Laplace transform is entire
  set mu0 : Measure ℝ := traceMeasure S P T' 0 with hmu0
  have hE : integrableExpSet (fun t : ℝ => t) mu0 = Set.univ := by
    refine Set.eq_univ_of_forall fun rho => ?_
    refine (integrable_exp_traceMeasure_iff S P hpos rho).mpr ?_
    have hkey := hall (-rho)
    have heq : ∀ t : ℝ, S.realWaveTrace P t * Real.exp ((rho - 0) * t) =
        S.realWaveTrace P t * Real.exp (-(-rho) * t) := by
      intro t
      congr 2
      ring
    simp only [heq]
    exact hkey
  have hA0 : AnalyticOnNhd ℂ (complexMGF (fun t : ℝ => t) mu0) Set.univ := by
    refine analyticOnNhd_complexMGF.mono ?_
    intro z _
    rw [hE]
    simp
  set L : ℂ → ℂ := fun s => complexMGF (fun t : ℝ => t) mu0 (-s) with hL
  have hLdiff : Differentiable ℂ L := by
    have h1 : Differentiable ℂ (complexMGF (fun t : ℝ => t) mu0) := by
      intro z
      exact (hA0 z (Set.mem_univ z)).differentiableAt
    exact fun s => (h1 (-s)).comp s (by fun_prop)
  have hLan : AnalyticOnNhd ℂ L (S.poleSet)ᶜ :=
    hLdiff.differentiableOn.analyticOnNhd (S.isOpen_compl_poleSet hlf)
  have hPTan : AnalyticOnNhd ℂ (S.poleTransform P T') (S.poleSet)ᶜ :=
    (S.differentiableOn_poleTransform_compl hlf P T').analyticOnNhd
      (S.isOpen_compl_poleSet hlf)
  -- they agree to the right of the horizontal width
  have hLval : ∀ s : ℂ, S.width < s.re → L s = S.poleTransform P T' s := by
    intro s hs
    rw [hL]
    simp only
    rw [hmu0, complexMGF_traceMeasure S P hpos (-s),
      S.poleTransform_eq_integral P (s := s) hs hT'nn]
    refine setIntegral_congr_fun measurableSet_Ioi fun t _ => ?_
    congr 2
    push_cast
    ring
  have hpolere : ∀ s : ℂ, s ∈ S.poleSet → s.re ≤ S.width := by
    intro s hs
    obtain ⟨g, hg⟩ := hs
    have hfac : (s - Complex.I * S.gamma g) * (s + Complex.I * S.gamma g) = 0 := by
      linear_combination hg - (S.gamma g ^ 2) * Complex.I_sq
    have hre : (Complex.I * S.gamma g).re = -(S.gamma g).im := by simp [Complex.mul_re]
    have hbd := S.im_le g
    rcases mul_eq_zero.mp hfac with h | h
    · have hval : s = Complex.I * S.gamma g := by linear_combination h
      rw [hval, hre]
      have := neg_le_abs (S.gamma g).im
      linarith
    · have hval : s = -(Complex.I * S.gamma g) := by linear_combination h
      rw [hval, Complex.neg_re, hre, neg_neg]
      have := le_abs_self (S.gamma g).im
      linarith
  set z0 : ℂ := ((S.width + 1 : ℝ) : ℂ) with hz0
  have hz0np : z0 ∉ S.poleSet := by
    intro hp
    have := hpolere z0 hp
    rw [hz0] at this
    simp at this
    linarith
  have hev : L =ᶠ[nhds z0] S.poleTransform P T' := by
    have hopen : IsOpen {s : ℂ | S.width < s.re} :=
      isOpen_lt continuous_const Complex.continuous_re
    have hz0mem : z0 ∈ {s : ℂ | S.width < s.re} := by
      rw [hz0]
      simp only [Set.mem_setOf_eq, Complex.ofReal_re]
      linarith
    filter_upwards [hopen.mem_nhds hz0mem] with s hs
    exact hLval s hs
  have hEqOn : Set.EqOn L (S.poleTransform P T') (S.poleSet)ᶜ :=
    hLan.eqOn_of_preconnected_of_eventuallyEq hPTan
      (S.isPreconnected_compl_poleSet) hz0np hev
  -- the pole contradicts boundedness
  obtain ⟨g₀, hg₀⟩ := exists_active_of_ne_zero S hinf hP
  obtain ⟨C, hC⟩ :=
    (isCompact_closedBall (Complex.I * S.gamma g₀) 1).exists_bound_of_continuousOn
      hLdiff.continuous.continuousOn
  obtain ⟨s, hsr, hsnp, hgt⟩ := S.exists_norm_poleTransform_gt hlf P T' hg₀ C one_pos
  have hsball : s ∈ Metric.closedBall (Complex.I * S.gamma g₀) 1 := by
    rw [Metric.mem_closedBall, Complex.dist_eq]
    exact le_of_lt hsr
  have hLs : L s = S.poleTransform P T' s := hEqOn hsnp
  have := hC s hsball
  rw [hLs] at this
  linarith

/-- The companion positive half: every nonzero polynomial wave trace also becomes strictly
positive after every time, so it assumes both strict signs cofinally. -/
theorem exists_pos_realWaveTrace [Countable G] (hlf : S.IsLocallyFiniteSpectrum)
    (hnoim : ∀ g : G, (S.gamma g).re ≠ 0)
    (hinf : (Set.range fun g : G => S.gamma g ^ 2).Infinite)
    {P : Polynomial ℝ} (hP : P ≠ 0) (T : ℝ) :
    ∃ t, T < t ∧ 0 < S.realWaveTrace P t := by
  obtain ⟨t, ht, hlt⟩ :=
    cofinalWaveSignEscape S hlf hnoim hinf (-P) (neg_ne_zero.mpr hP) T
  refine ⟨t, ht, ?_⟩
  have hneg : S.realWaveTrace (-P) t = -S.realWaveTrace P t := by
    rw [show (-P : Polynomial ℝ) = (-1 : ℝ) • P by simp, S.realWaveTrace_smul]
    ring
  rw [hneg] at hlt
  linarith

/-- **Cofinal convex recurrence of the wave-trace hierarchy, unconditionally.** For a locally
finite conjugation-stable spectrum with infinitely many distinct frequency squares and no
purely imaginary frequency, after every time at most `K + 1` distinct later times carry a
positive probability weight annihilating the first `K` regularized wave traces exactly. -/
theorem exists_cofinal_positive_quadrature_of_no_imaginary [Countable G]
    (hlf : S.IsLocallyFiniteSpectrum) (hnoim : ∀ g : G, (S.gamma g).re ≠ 0)
    (hinf : (Set.range fun g : G => S.gamma g ^ 2).Infinite) (K : ℕ) (T : ℝ) :
    ∃ (nodes : Finset ℝ) (w : ℝ → ℝ),
      nodes.Nonempty ∧
      nodes.card ≤ K + 1 ∧
      (∀ t ∈ nodes, T < t) ∧
      (∀ t ∈ nodes, 0 < w t) ∧
      (∑ t ∈ nodes, w t) = 1 ∧
      ∀ j : Fin K, (∑ t ∈ nodes, w t * S.realWaveTrace (Polynomial.X ^ (j : ℕ)) t) = 0 :=
  S.exists_cofinal_positive_quadrature_waveTrace (cofinalWaveSignEscape S hlf hnoim hinf) K T

end

end RHTower
