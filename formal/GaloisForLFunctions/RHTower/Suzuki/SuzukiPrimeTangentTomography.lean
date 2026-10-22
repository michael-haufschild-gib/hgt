import GaloisForLFunctions.RHTower.Suzuki.SuzukiFiniteShiftNonClock
import Mathlib.Analysis.Asymptotics.SpecificAsymptotics
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt

namespace GaloisForLFunctions.RHTower

open Complex Filter Finset Set Topology

noncomputable section

/-- Complex Cesàro mean over modes `0,...,N-1`. -/
def suzukiCesaroMean (u : ℕ → ℂ) (N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ range N, u n

theorem tendsto_natCast_inv_complex_zero :
    Tendsto (fun N : ℕ => ((N : ℂ)⁻¹)) atTop (𝓝 0) := by
  have hreal : Tendsto (fun N : ℕ => ((N : ℝ)⁻¹)) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hcast := (Complex.continuous_ofReal.tendsto 0).comp hreal
  simpa [Function.comp_def] using hcast

theorem tendsto_suzukiCesaroMean_geometric_zero
    {q : ℂ} (hqnorm : ‖q‖ = 1) (hq : q ≠ 1) :
    Tendsto (fun N : ℕ => suzukiCesaroMean (fun n => q ^ n) N) atTop (𝓝 0) := by
  have hsum (N : ℕ) : ∑ n ∈ range N, q ^ n = (q ^ N - 1) / (q - 1) := by
    apply (eq_div_iff (sub_ne_zero.mpr hq)).2
    exact geom_sum_mul q N
  have hbounded : IsBoundedUnder (· ≤ ·) atTop
      (norm ∘ fun N : ℕ => (q ^ N - 1) / (q - 1)) := by
    apply isBoundedUnder_of_eventually_le
    exact Filter.Eventually.of_forall (fun N : ℕ => by
      simp only [Function.comp_apply, norm_div]
      apply (div_le_div_iff_of_pos_right (norm_pos_iff.mpr (sub_ne_zero.mpr hq))).2
      calc
        ‖q ^ N - 1‖ ≤ ‖q ^ N‖ + ‖(1 : ℂ)‖ := norm_sub_le _ _
        _ = 2 := by rw [norm_pow, hqnorm]; norm_num)
  have hprod := tendsto_natCast_inv_complex_zero.zero_mul_isBoundedUnder_le hbounded
  simpa only [suzukiCesaroMean, hsum] using hprod

theorem tendsto_suzukiCesaroMean_geometric_one :
    Tendsto (fun N : ℕ => suzukiCesaroMean (fun _ => (1 : ℂ)) N) atTop (𝓝 1) := by
  have heq : (fun N : ℕ => suzukiCesaroMean (fun _ => (1 : ℂ)) N) =ᶠ[atTop]
      fun _ => (1 : ℂ) := by
    filter_upwards [Ici_mem_atTop 1] with N hN
    simp only [suzukiCesaroMean, sum_const, card_range, nsmul_eq_mul, mul_one]
    have hN0 : (N : ℂ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hN)
    exact inv_mul_cancel₀ hN0
  exact tendsto_const_nhds.congr' heq.symm

/-- Finite exponential phase packet. -/
def suzukiFinitePhaseCarrier {ι : Type*} (s : Finset ι) (c q : ι → ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ s, c j * q j ^ n

theorem suzukiCesaroMean_smul (c : ℂ) (u : ℕ → ℂ) (N : ℕ) :
    suzukiCesaroMean (fun n => c * u n) N = c * suzukiCesaroMean u N := by
  simp only [suzukiCesaroMean, ← mul_sum]
  ring

theorem suzukiCesaroMean_sum {ι : Type*} (s : Finset ι) (u : ι → ℕ → ℂ) (N : ℕ) :
    suzukiCesaroMean (fun n => ∑ j ∈ s, u j n) N =
      ∑ j ∈ s, suzukiCesaroMean (u j) N := by
  simp only [suzukiCesaroMean]
  rw [← mul_sum]
  congr 1
  exact Finset.sum_comm

theorem tendsto_suzukiFinitePhaseCarrier_bohrCoefficient
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {c q : ι → ℂ} {m : ι}
    (hm : m ∈ s) (hqnorm : ∀ j ∈ s, ‖q j‖ = 1)
    (hsep : ∀ j ∈ s, j ≠ m → q j ≠ q m) :
    Tendsto
      (fun N => suzukiCesaroMean
        (fun n => suzukiFinitePhaseCarrier s c q n * (q m)⁻¹ ^ n) N)
      atTop (𝓝 (c m)) := by
  have hqmnorm : ‖q m‖ = 1 := hqnorm m hm
  have hqm0 : q m ≠ 0 := norm_ne_zero_iff.mp (by rw [hqmnorm]; norm_num)
  have hrewrite (N : ℕ) :
      suzukiCesaroMean
          (fun n => suzukiFinitePhaseCarrier s c q n * (q m)⁻¹ ^ n) N =
        ∑ j ∈ s, c j * suzukiCesaroMean (fun n => (q j * (q m)⁻¹) ^ n) N := by
    calc
      suzukiCesaroMean
          (fun n => suzukiFinitePhaseCarrier s c q n * (q m)⁻¹ ^ n) N =
        suzukiCesaroMean
          (fun n => ∑ j ∈ s, c j * (q j * (q m)⁻¹) ^ n) N := by
            apply congrArg (fun u : ℕ → ℂ => suzukiCesaroMean u N)
            funext n
            simp only [suzukiFinitePhaseCarrier, sum_mul]
            apply sum_congr rfl
            intro j hj
            rw [mul_assoc, ← mul_pow]
      _ = ∑ j ∈ s, suzukiCesaroMean
          (fun n => c j * (q j * (q m)⁻¹) ^ n) N :=
        suzukiCesaroMean_sum s _ N
      _ = ∑ j ∈ s, c j * suzukiCesaroMean
          (fun n => (q j * (q m)⁻¹) ^ n) N := by
        apply sum_congr rfl
        intro j hj
        exact suzukiCesaroMean_smul _ _ _
  have hterm (j : ι) (hj : j ∈ s) :
      Tendsto
        (fun N => c j * suzukiCesaroMean (fun n => (q j * (q m)⁻¹) ^ n) N)
        atTop (𝓝 (if j = m then c m else 0)) := by
    by_cases hjm : j = m
    · subst j
      have hratio : q m * (q m)⁻¹ = 1 := mul_inv_cancel₀ hqm0
      simpa only [hratio, one_pow, if_pos rfl, mul_one] using!
        tendsto_const_nhds.mul tendsto_suzukiCesaroMean_geometric_one
    · have hratioNorm : ‖q j * (q m)⁻¹‖ = 1 := by
        rw [norm_mul, norm_inv, hqnorm j hj, hqmnorm]
        norm_num
      have hratioNe : q j * (q m)⁻¹ ≠ 1 := by
        intro h
        apply hsep j hj hjm
        calc
          q j = (q j * (q m)⁻¹) * q m := by field_simp
          _ = q m := by rw [h, one_mul]
      simpa only [if_neg hjm, mul_zero] using
        tendsto_const_nhds.mul
          (tendsto_suzukiCesaroMean_geometric_zero hratioNorm hratioNe)
  have hsumlim := tendsto_finsetSum s (fun j hj => hterm j hj)
  rw [show (fun N => suzukiCesaroMean
      (fun n => suzukiFinitePhaseCarrier s c q n * (q m)⁻¹ ^ n) N) =
      (fun N => ∑ j ∈ s, c j *
        suzukiCesaroMean (fun n => (q j * (q m)⁻¹) ^ n) N) from funext hrewrite]
  simpa [sum_ite_eq' s m, hm] using hsumlim

/-- Finite sine packet encoded by a unit complex phase and its inverse. -/
def suzukiFiniteSinePhaseCarrier {ι : Type*}
    (s : Finset ι) (c q : ι → ℂ) (n : ℕ) : ℂ :=
  ∑ j ∈ s, c j * (q j ^ n - (q j)⁻¹ ^ n) / (2 * I)

/-- **Bohr recovery for a finite sine packet.** If the positive phases are distinct and no inverse
phase collides with the target, demodulation recovers exactly the target sine amplitude divided by
`2i`. -/
theorem tendsto_suzukiFiniteSinePhaseCarrier_bohrCoefficient
    {ι : Type*} [DecidableEq ι] {s : Finset ι} {c q : ι → ℂ} {m : ι}
    (hm : m ∈ s) (hqnorm : ∀ j ∈ s, ‖q j‖ = 1)
    (hsep : ∀ j ∈ s, j ≠ m → q j ≠ q m)
    (hminus : ∀ j ∈ s, (q j)⁻¹ ≠ q m) :
    Tendsto
      (fun N => suzukiCesaroMean
        (fun n => suzukiFiniteSinePhaseCarrier s c q n * (q m)⁻¹ ^ n) N)
      atTop (𝓝 (c m / (2 * I))) := by
  have hqmnorm : ‖q m‖ = 1 := hqnorm m hm
  have hqm0 : q m ≠ 0 := norm_ne_zero_iff.mp (by rw [hqmnorm]; norm_num)
  have hrewrite (N : ℕ) :
      suzukiCesaroMean
          (fun n => suzukiFiniteSinePhaseCarrier s c q n * (q m)⁻¹ ^ n) N =
        ∑ j ∈ s,
          ((c j / (2 * I)) *
              suzukiCesaroMean (fun n => (q j * (q m)⁻¹) ^ n) N -
            (c j / (2 * I)) *
              suzukiCesaroMean (fun n => ((q j)⁻¹ * (q m)⁻¹) ^ n) N) := by
    calc
      suzukiCesaroMean
          (fun n => suzukiFiniteSinePhaseCarrier s c q n * (q m)⁻¹ ^ n) N =
        suzukiCesaroMean
          (fun n => ∑ j ∈ s,
            ((c j / (2 * I)) * (q j * (q m)⁻¹) ^ n -
              (c j / (2 * I)) * ((q j)⁻¹ * (q m)⁻¹) ^ n)) N := by
            apply congrArg (fun u : ℕ → ℂ => suzukiCesaroMean u N)
            funext n
            simp only [suzukiFiniteSinePhaseCarrier, sum_mul]
            apply sum_congr rfl
            intro j hj
            rw [mul_pow, mul_pow]
            field_simp
      _ = ∑ j ∈ s, suzukiCesaroMean
          (fun n => (c j / (2 * I)) * (q j * (q m)⁻¹) ^ n -
            (c j / (2 * I)) * ((q j)⁻¹ * (q m)⁻¹) ^ n) N :=
        suzukiCesaroMean_sum s _ N
      _ = _ := by
        apply sum_congr rfl
        intro j hj
        simp only [suzukiCesaroMean, sum_sub_distrib]
        rw [mul_sub]
        congr 1 <;> exact suzukiCesaroMean_smul _ _ _
  have hterm (j : ι) (hj : j ∈ s) :
      Tendsto
        (fun N =>
          (c j / (2 * I)) * suzukiCesaroMean (fun n => (q j * (q m)⁻¹) ^ n) N -
          (c j / (2 * I)) *
            suzukiCesaroMean (fun n => ((q j)⁻¹ * (q m)⁻¹) ^ n) N)
        atTop (𝓝 (if j = m then c m / (2 * I) else 0)) := by
    have hminusNorm : ‖(q j)⁻¹ * (q m)⁻¹‖ = 1 := by
      rw [norm_mul, norm_inv, norm_inv, hqnorm j hj, hqmnorm]
      norm_num
    have hminusNe : (q j)⁻¹ * (q m)⁻¹ ≠ 1 := by
      intro h
      apply hminus j hj
      calc
        (q j)⁻¹ = ((q j)⁻¹ * (q m)⁻¹) * q m := by field_simp
        _ = q m := by rw [h, one_mul]
    have hminusZero : Tendsto
        (fun N : ℕ => (c j / (2 * I)) *
          suzukiCesaroMean (fun n => ((q j)⁻¹ * (q m)⁻¹) ^ n) N)
        atTop (𝓝 0) :=
      by
        simpa using
          (tendsto_const_nhds : Tendsto (fun _ : ℕ => c j / (2 * I)) atTop
            (𝓝 (c j / (2 * I)))).mul
              (tendsto_suzukiCesaroMean_geometric_zero hminusNorm hminusNe)
    by_cases hjm : j = m
    · subst j
      have hratio : q m * (q m)⁻¹ = 1 := mul_inv_cancel₀ hqm0
      have hplusOne : Tendsto
          (fun N : ℕ => (c m / (2 * I)) *
            suzukiCesaroMean (fun _ => (1 : ℂ)) N)
          atTop (𝓝 (c m / (2 * I))) :=
        by
          simpa using
            (tendsto_const_nhds : Tendsto (fun _ : ℕ => c m / (2 * I)) atTop
              (𝓝 (c m / (2 * I)))).mul tendsto_suzukiCesaroMean_geometric_one
      simpa only [hratio, one_pow, if_pos rfl, mul_one, sub_zero] using!
        hplusOne.sub hminusZero
    · have hplusNorm : ‖q j * (q m)⁻¹‖ = 1 := by
        rw [norm_mul, norm_inv, hqnorm j hj, hqmnorm]
        norm_num
      have hplusNe : q j * (q m)⁻¹ ≠ 1 := by
        intro h
        apply hsep j hj hjm
        calc
          q j = (q j * (q m)⁻¹) * q m := by field_simp
          _ = q m := by rw [h, one_mul]
      have hplusZero : Tendsto
          (fun N : ℕ => (c j / (2 * I)) *
            suzukiCesaroMean (fun n => (q j * (q m)⁻¹) ^ n) N)
          atTop (𝓝 0) :=
        by
          simpa using
            (tendsto_const_nhds : Tendsto (fun _ : ℕ => c j / (2 * I)) atTop
              (𝓝 (c j / (2 * I)))).mul
                (tendsto_suzukiCesaroMean_geometric_zero hplusNorm hplusNe)
      simpa only [if_neg hjm, sub_zero] using hplusZero.sub hminusZero
  have hsumlim := tendsto_finsetSum s (fun j hj => hterm j hj)
  rw [show (fun N => suzukiCesaroMean
      (fun n => suzukiFiniteSinePhaseCarrier s c q n * (q m)⁻¹ ^ n) N) =
      (fun N => ∑ j ∈ s,
        ((c j / (2 * I)) *
            suzukiCesaroMean (fun n => (q j * (q m)⁻¹) ^ n) N -
          (c j / (2 * I)) *
            suzukiCesaroMean (fun n => ((q j)⁻¹ * (q m)⁻¹) ^ n) N)) from
        funext hrewrite]
  simpa [sum_ite_eq' s m, hm] using hsumlim

/-! ## Suzuki's prime-step tangent packet -/

/-- Unit phase contributed by the prime-power displacement `log m` at aperture `a`. -/
def suzukiPrimeTangentPhase (a : ℝ) (m : ℕ) : ℂ :=
  Complex.exp (((Real.pi * Real.log m / a : ℝ) : ℂ) * I)

theorem norm_suzukiPrimeTangentPhase (a : ℝ) (m : ℕ) :
    ‖suzukiPrimeTangentPhase a m‖ = 1 := by
  let r : ℝ := Real.pi * Real.log m / a
  rw [suzukiPrimeTangentPhase, Complex.norm_exp]
  change Real.exp (((r : ℂ) * I).re) = 1
  rw [Complex.mul_re]
  simp only [ofReal_re, I_re, mul_zero, ofReal_im, I_im, zero_mul, sub_zero]
  exact Real.exp_zero

/-- Positive geometric scale multiplying `Λ(m)` in Suzuki's reflected pair of prime steps. -/
def suzukiPrimeTangentScale (m : ℕ) : ℝ :=
  Real.sqrt m + 1 / ((m : ℝ) * Real.sqrt m)

theorem suzukiPrimeTangentScale_pos {m : ℕ} (hm : 2 ≤ m) :
    0 < suzukiPrimeTangentScale m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hm)
  have hsqrt : 0 < Real.sqrt m := Real.sqrt_pos.2 hmpos
  simp only [suzukiPrimeTangentScale]
  positivity

/-- The tangent scale is exactly the sum of Suzuki's two reflected step multipliers after the
common `1 / sqrt m` factor is extracted. -/
theorem suzukiPrimeTangentScale_eq_reflected {m : ℕ} (hm : 2 ≤ m) :
    suzukiPrimeTangentScale m =
      ((m : ℝ) + 1 / (m : ℝ)) / Real.sqrt m := by
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 2) hm)
  have hsqrt : Real.sqrt (m : ℝ) ≠ 0 := (Real.sqrt_pos.2 hmpos).ne'
  have hsquare : Real.sqrt (m : ℝ) ^ (2 : ℕ) = m := Real.sq_sqrt hmpos.le
  simp only [suzukiPrimeTangentScale]
  field_simp
  nlinarith

/-- Exact coefficient of the `m`th prime-power sine mode in Suzuki's weighted source tangent. -/
def suzukiPrimeTangentWeight (m : ℕ) : ℝ :=
  ArithmeticFunction.vonMangoldt m * suzukiPrimeTangentScale m

theorem suzukiPrimeTangentWeight_ne_zero_iff {m : ℕ} (hm : 2 ≤ m) :
    suzukiPrimeTangentWeight m ≠ 0 ↔ ArithmeticFunction.vonMangoldt m ≠ 0 := by
  have hfactor : suzukiPrimeTangentScale m ≠ 0 := (suzukiPrimeTangentScale_pos hm).ne'
  rw [suzukiPrimeTangentWeight, mul_ne_zero_iff]
  exact and_iff_left hfactor

theorem suzukiPrimeTangentWeight_ne_zero_iff_primePow {m : ℕ} (hm : 2 ≤ m) :
    suzukiPrimeTangentWeight m ≠ 0 ↔ IsPrimePow m := by
  rw [suzukiPrimeTangentWeight_ne_zero_iff hm]
  simpa only [ne_eq, not_not] using
    not_congr (@ArithmeticFunction.vonMangoldt_eq_zero_iff m)

/-- Finite arithmetic packet exposed by high clock samples of Suzuki's first projective tangent. -/
def suzukiPrimeTangentCarrier (a : ℝ) (s : Finset ℕ) (n : ℕ) : ℂ :=
  suzukiFiniteSinePhaseCarrier s
    (fun m => (suzukiPrimeTangentWeight m : ℂ))
    (suzukiPrimeTangentPhase a) n

/-- Finite aperture phase condition excluding positive-positive and reflected phase collisions. -/
def SuzukiPrimeTangentNonresonant (a : ℝ) (s : Finset ℕ) : Prop :=
  ∀ m ∈ s,
    (∀ j ∈ s, j ≠ m →
      suzukiPrimeTangentPhase a j ≠ suzukiPrimeTangentPhase a m) ∧
    (∀ j ∈ s,
      (suzukiPrimeTangentPhase a j)⁻¹ ≠ suzukiPrimeTangentPhase a m)

/-- If every packet index is at least two and its logarithm is below the aperture, then all
positive phases lie in the open upper semicircle.  Strict injectivity of cosine separates the
positive phases, while the sign of the imaginary part separates every reflected phase. -/
theorem suzukiPrimeTangentNonresonant_of_log_lt_aperture
    {a : ℝ} {s : Finset ℕ}
    (hsupport : ∀ m ∈ s, 2 ≤ m)
    (hlarge : ∀ m ∈ s, Real.log m < a) :
    SuzukiPrimeTangentNonresonant a s := by
  have hangle (m : ℕ) (hm : m ∈ s) :
      Real.pi * Real.log m / a ∈ Set.Icc (0 : ℝ) Real.pi := by
    have hm2 := hsupport m hm
    have hm1 : 1 < (m : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hm2)
    have hlog : 0 < Real.log (m : ℝ) := Real.log_pos hm1
    have ha : 0 < a := hlog.trans (hlarge m hm)
    constructor
    · exact (div_pos (mul_pos Real.pi_pos hlog) ha).le
    · have hratio : Real.log (m : ℝ) / a < 1 :=
        (div_lt_one ha).2 (hlarge m hm)
      have hpi : 0 < Real.pi := Real.pi_pos
      calc
        Real.pi * Real.log m / a =
            Real.pi * (Real.log m / a) := by ring
        _ ≤ Real.pi := by
          simpa only [mul_one] using
            (mul_lt_mul_of_pos_left hratio hpi).le
  have hphaseIm (m : ℕ) (hm : m ∈ s) :
      0 < (suzukiPrimeTangentPhase a m).im := by
    have hm2 := hsupport m hm
    have hm1 : 1 < (m : ℝ) := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hm2)
    have hlog : 0 < Real.log (m : ℝ) := Real.log_pos hm1
    have ha : 0 < a := hlog.trans (hlarge m hm)
    have htheta0 : 0 < Real.pi * Real.log m / a :=
      div_pos (mul_pos Real.pi_pos hlog) ha
    have hthetap : Real.pi * Real.log m / a < Real.pi := by
      have hratio : Real.log (m : ℝ) / a < 1 :=
        (div_lt_one ha).2 (hlarge m hm)
      calc
        Real.pi * Real.log m / a =
            Real.pi * (Real.log m / a) := by ring
        _ < Real.pi * 1 :=
          mul_lt_mul_of_pos_left hratio Real.pi_pos
        _ = Real.pi := mul_one _
    have hformula : (suzukiPrimeTangentPhase a m).im =
        Real.sin (Real.pi * Real.log m / a) := by
      have h := congrArg Complex.im
        (Complex.exp_ofReal_mul_I (Real.pi * Real.log m / a))
      simpa only [suzukiPrimeTangentPhase, Complex.add_im, Complex.ofReal_im,
        Complex.mul_im, Complex.ofReal_re, Complex.I_im, Complex.I_re,
        zero_add, add_zero, mul_one, zero_mul] using h
    rw [hformula]
    exact Real.sin_pos_of_pos_of_lt_pi htheta0 hthetap
  intro m hm
  constructor
  · intro j hj hjne heq
    have hangleEq :
        Real.pi * Real.log j / a = Real.pi * Real.log m / a := by
      apply Real.injOn_cos (hangle j hj) (hangle m hm)
      have hre := congrArg Complex.re heq
      simpa only [suzukiPrimeTangentPhase, Complex.exp_ofReal_mul_I,
        Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re,
        Complex.ofReal_im, Complex.I_im, mul_zero, zero_mul, sub_zero,
        add_zero] using hre
    have hj2 := hsupport j hj
    have hm2 := hsupport m hm
    have hjpos : (0 : ℝ) < j := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hj2)
    have hmpos : (0 : ℝ) < m := by
      exact_mod_cast (lt_of_lt_of_le (by omega : 0 < 2) hm2)
    have hlogm : 0 < Real.log (m : ℝ) :=
      Real.log_pos (by
        exact_mod_cast (lt_of_lt_of_le (by omega : 1 < 2) hm2))
    have ha : 0 < a := hlogm.trans (hlarge m hm)
    have hfac : Real.pi / a ≠ 0 := (div_pos Real.pi_pos ha).ne'
    have hlogEq : Real.log (j : ℝ) = Real.log (m : ℝ) := by
      apply mul_left_cancel₀ hfac
      simpa only [div_mul_eq_mul_div] using hangleEq
    have hcast : (j : ℝ) = (m : ℝ) :=
      Real.strictMonoOn_log.injOn (Set.mem_Ioi.mpr hjpos)
        (Set.mem_Ioi.mpr hmpos) hlogEq
    exact hjne (by exact_mod_cast hcast)
  · intro j hj heq
    have hjim := hphaseIm j hj
    have hmim := hphaseIm m hm
    have hjne : suzukiPrimeTangentPhase a j ≠ 0 :=
      norm_ne_zero_iff.mp (by
        rw [norm_suzukiPrimeTangentPhase]
        norm_num)
    have hnormSq : 0 < Complex.normSq (suzukiPrimeTangentPhase a j) :=
      Complex.normSq_pos.mpr hjne
    have hinvneg : ((suzukiPrimeTangentPhase a j)⁻¹).im < 0 := by
      rw [Complex.inv_im]
      exact div_neg_of_neg_of_pos (neg_neg_of_pos hjim) hnormSq
    have himEq := congrArg Complex.im heq
    linarith

/-- Every finite packet supported on integers at least two is phase-nonresonant at all
sufficiently large apertures. -/
theorem eventually_suzukiPrimeTangentNonresonant
    (s : Finset ℕ) (hsupport : ∀ m ∈ s, 2 ≤ m) :
    ∀ᶠ a : ℝ in atTop, SuzukiPrimeTangentNonresonant a s := by
  have hlarge : ∀ᶠ a : ℝ in atTop, ∀ m ∈ s, Real.log m < a :=
    (s.eventually_all).2 fun m _ => eventually_gt_atTop (Real.log m)
  filter_upwards [hlarge] with a ha
  exact suzukiPrimeTangentNonresonant_of_log_lt_aperture hsupport ha

/-- Cofinal source-selected apertures discharge the nonresonance interface for every finite
packet supported on integers at least two. -/
theorem exists_suzukiPrimeTangentNonresonant_above
    (s : Finset ℕ) (hsupport : ∀ m ∈ s, 2 ≤ m) (B : ℝ) :
    ∃ a : ℝ, 0 < a ∧ B < a ∧ SuzukiPrimeTangentNonresonant a s := by
  let C : ℝ := ∑ m ∈ s, |Real.log m|
  let a : ℝ := max (max B 0) C + 1
  have hbaseNonneg : 0 ≤ max (max B 0) C :=
    le_trans (le_max_right B 0) (le_max_left (max B 0) C)
  have ha0 : 0 < a := by
    dsimp only [a]
    linarith
  have hBa : B < a := by
    have hBbase : B ≤ max (max B 0) C :=
      (le_max_left B 0).trans (le_max_left (max B 0) C)
    dsimp only [a]
    linarith
  have hlarge : ∀ m ∈ s, Real.log m < a := by
    intro m hm
    have hsingle : |Real.log m| ≤ C := by
      dsimp only [C]
      exact Finset.single_le_sum (s := s)
        (f := fun i : ℕ => |Real.log i|)
        (fun (i : ℕ) _ => abs_nonneg (Real.log i)) hm
    have hCbase : C ≤ max (max B 0) C := le_max_right _ _
    calc
      Real.log m ≤ |Real.log m| := le_abs_self _
      _ ≤ C := hsingle
      _ ≤ max (max B 0) C := hCbase
      _ < a := by
        dsimp only [a]
        linarith
  exact ⟨a, ha0, hBa,
    suzukiPrimeTangentNonresonant_of_log_lt_aperture hsupport hlarge⟩

/-- **Prime-power tangent tomography.** At a phase-nonresonant aperture, the Bohr coefficient of
Suzuki's finite tangent packet recovers exactly the target von-Mangoldt source weight. -/
theorem tendsto_suzukiPrimeTangentCarrier_bohrCoefficient
    {a : ℝ} {s : Finset ℕ} {m : ℕ} (hm : m ∈ s)
    (hsep : ∀ j ∈ s, j ≠ m →
      suzukiPrimeTangentPhase a j ≠ suzukiPrimeTangentPhase a m)
    (hminus : ∀ j ∈ s,
      (suzukiPrimeTangentPhase a j)⁻¹ ≠ suzukiPrimeTangentPhase a m) :
    Tendsto
      (fun N => suzukiCesaroMean
        (fun n => suzukiPrimeTangentCarrier a s n *
          (suzukiPrimeTangentPhase a m)⁻¹ ^ n) N)
      atTop (𝓝 ((suzukiPrimeTangentWeight m : ℂ) / (2 * I))) := by
  exact tendsto_suzukiFiniteSinePhaseCarrier_bohrCoefficient hm
    (fun j hj => norm_suzukiPrimeTangentPhase a j) hsep hminus

/-- Divide a recovered Bohr coefficient by the explicit reflected-step scale. -/
def suzukiPrimeTangentNormalize (m : ℕ) (z : ℂ) : ℂ :=
  (2 * I * z) / (suzukiPrimeTangentScale m : ℂ)

/-- **Exact von-Mangoldt reconstruction.** For `m ≥ 2`, normalization of the nonresonant Bohr
coefficient of Suzuki's first tangent converges to `Λ(m)` itself, not merely to its support. -/
theorem tendsto_suzukiPrimeTangentCarrier_normalized_bohrCoefficient
    {a : ℝ} {s : Finset ℕ} {m : ℕ} (hm : m ∈ s) (hm2 : 2 ≤ m)
    (hsep : ∀ j ∈ s, j ≠ m →
      suzukiPrimeTangentPhase a j ≠ suzukiPrimeTangentPhase a m)
    (hminus : ∀ j ∈ s,
      (suzukiPrimeTangentPhase a j)⁻¹ ≠ suzukiPrimeTangentPhase a m) :
    Tendsto
      (fun N => suzukiPrimeTangentNormalize m
        (suzukiCesaroMean
          (fun n => suzukiPrimeTangentCarrier a s n *
            (suzukiPrimeTangentPhase a m)⁻¹ ^ n) N))
      atTop (𝓝 (ArithmeticFunction.vonMangoldt m : ℂ)) := by
  have hbohr := tendsto_suzukiPrimeTangentCarrier_bohrCoefficient hm hsep hminus
  have hscale : (suzukiPrimeTangentScale m : ℂ) ≠ 0 := by
    exact_mod_cast (suzukiPrimeTangentScale_pos hm2).ne'
  have hscaled := (tendsto_const_nhds : Tendsto (fun _ : ℕ => (2 * I : ℂ)) atTop
    (𝓝 (2 * I))).mul hbohr
  have hdiv := hscaled.div_const (suzukiPrimeTangentScale m : ℂ)
  have hlimit :
      2 * I * ((suzukiPrimeTangentWeight m : ℂ) / (2 * I)) /
          (suzukiPrimeTangentScale m : ℂ) =
        (ArithmeticFunction.vonMangoldt m : ℂ) := by
    simp only [suzukiPrimeTangentWeight]
    push_cast
    field_simp [hscale]
  rw [hlimit] at hdiv
  simpa only [suzukiPrimeTangentNormalize] using hdiv

/-- A single nonresonance certificate reconstructs every von-Mangoldt coefficient in the finite
Suzuki aperture packet. -/
theorem tendsto_suzukiPrimeTangentCarrier_normalized_bohrCoefficient_of_nonresonant
    {a : ℝ} {s : Finset ℕ} (hres : SuzukiPrimeTangentNonresonant a s)
    {m : ℕ} (hm : m ∈ s) (hm2 : 2 ≤ m) :
    Tendsto
      (fun N => suzukiPrimeTangentNormalize m
        (suzukiCesaroMean
          (fun n => suzukiPrimeTangentCarrier a s n *
            (suzukiPrimeTangentPhase a m)⁻¹ ^ n) N))
      atTop (𝓝 (ArithmeticFunction.vonMangoldt m : ℂ)) := by
  exact tendsto_suzukiPrimeTangentCarrier_normalized_bohrCoefficient hm hm2
    (hres m hm).1 (hres m hm).2

/-- A source-selected aperture above any prescribed scale recovers every von Mangoldt
coefficient in the finite tangent packet.  No nonresonance hypothesis remains in the interface. -/
theorem exists_suzukiPrimeTangentTomography_above
    (s : Finset ℕ) (hsupport : ∀ m ∈ s, 2 ≤ m) (B : ℝ) :
    ∃ a : ℝ, 0 < a ∧ B < a ∧
      ∀ m : ℕ, m ∈ s →
        Tendsto
          (fun N => suzukiPrimeTangentNormalize m
            (suzukiCesaroMean
              (fun n => suzukiPrimeTangentCarrier a s n *
                (suzukiPrimeTangentPhase a m)⁻¹ ^ n) N))
          atTop (𝓝 (ArithmeticFunction.vonMangoldt m : ℂ)) := by
  obtain ⟨a, ha, hBa, hres⟩ :=
    exists_suzukiPrimeTangentNonresonant_above s hsupport B
  refine ⟨a, ha, hBa, ?_⟩
  intro m hm
  exact tendsto_suzukiPrimeTangentCarrier_normalized_bohrCoefficient_of_nonresonant
    hres hm (hsupport m hm)

end

end GaloisForLFunctions.RHTower
