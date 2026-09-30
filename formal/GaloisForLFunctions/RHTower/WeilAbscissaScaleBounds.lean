import GaloisForLFunctions.RHTower.ZetaNotchAnalyticPairing
import GaloisForLFunctions.RHTower.ZetaNotchDecayingEnvelope

/-!
# Scale bounds for the mixed notch

The mixed notch moment is a scale integral `∫_0^∞ ρ_L(u) u^{−1} M_u du` of notch-window moments.
This file collects the estimates that turn per-scale bounds into bounds on the mixture:

* finite sums over `n` commute with the scale integral (`sum_mul_re_integral_scale`);
* at every scale `u ≥ 16`, with `δ = u^{−(1/2+a)}`, the finite sum `Σ_{n∈F} v(n) Re M_u(log n)` is at
  least `Y_F e_P Re ∫ω_u log t − D Σ_{n∈F} |v(n)| w_u(n)` with
  `w_u(n) = 2u n^{−a} + u²/(u^{1/2−a})^K + u² e^{−u²/32}` (`sum_re_weightedMoment_ge`);
* at small scales `‖M_u‖ ≤ C u` (`exists_norm_weightedMoment_le_small`);
* Gaussian scale integrals: `ρ_L(u) ≤ e^{−L²/8} e^{−(u−L)²/2}` for `u ≤ L/2`, the main scale integral
  `∫_{u>16} ρ_L(u) log u du ≥ 2e^{−1} log(L − 1)`, and polynomial-times-Gaussian bounds.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

namespace RHTower.WeilAbscissa

open RHTower.ZetaNotch RHTower.SmoothNumbers RHTower.WeilFiniteSupport RHTower.WeilLogSummable

variable {P : Finset ℕ}

/-! ## Finite sums against the scale integral -/

theorem integrableOn_scaleMoment (L : ℝ) {q : ℝ → ℝ} (hqc : Continuous q) {CQ : ℝ}
    (hqb : ∀ t, |q t| ≤ CQ) (y : ℝ) :
    IntegrableOn (fun u => ((scaleWeight L u / u : ℝ) : ℂ) * ZetaNotch.weightedMoment u q y)
      (Ioi 0) := by
  obtain ⟨CZ, -, hCZ⟩ := exists_norm_zetaSq_le
  have hI := (integrable_scaleIntegrand L (continuous_momentIntegrand hqc y)
    (norm_momentIntegrand_le hqb hCZ y)).integral_prod_left
  refine hI.congr ?_
  rw [Filter.EventuallyEq, ae_restrict_iff' measurableSet_Ioi]
  refine Eventually.of_forall fun u hu => ?_
  have hu0 : (0 : ℝ) < u := hu
  simp only [Function.uncurry_apply_pair, scaleIntegrand]
  unfold ZetaNotch.weightedMoment
  rw [← integral_const_mul]
  congr 1
  funext t
  rw [notchWindow_eq_notchProfile hu0]
  push_cast
  ring

/-- Finite sums over `n` commute with the scale integral. -/
theorem sum_mul_re_integral_scale (L : ℝ) {q : ℝ → ℝ} (hqc : Continuous q) {CQ : ℝ}
    (hqb : ∀ t, |q t| ≤ CQ) (v : ℕ → ℝ) (F : Finset ℕ) :
    ∑ n ∈ F, v n * (∫ u in Ioi 0, ((scaleWeight L u / u : ℝ) : ℂ) *
        ZetaNotch.weightedMoment u q (Real.log n)).re =
      ∫ u in Ioi 0, scaleWeight L u / u *
        ∑ n ∈ F, v n * (ZetaNotch.weightedMoment u q (Real.log n)).re := by
  have hi := fun n : ℕ => integrableOn_scaleMoment L hqc hqb (Real.log n)
  have e : (fun u => scaleWeight L u / u *
      ∑ n ∈ F, v n * (ZetaNotch.weightedMoment u q (Real.log n)).re) =
      fun u => ∑ n ∈ F, v n * (((scaleWeight L u / u : ℝ) : ℂ) *
        ZetaNotch.weightedMoment u q (Real.log n)).re := by
    funext u
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [Complex.re_ofReal_mul]
    ring
  have hre : ∀ n : ℕ, IntegrableOn (fun u => (((scaleWeight L u / u : ℝ) : ℂ) *
      ZetaNotch.weightedMoment u q (Real.log n)).re) (Ioi 0) := fun n => by
    have h := (hi n).re
    simp only [RCLike.re_to_complex] at h
    exact h
  rw [e, integral_finsetSum _ fun n _ => (hre n).const_mul (v n)]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [integral_const_mul]
  congr 1
  have := integral_re (hi n)
  simp only [RCLike.re_to_complex] at this
  exact this.symm

/-! ## The per-scale lower bound -/

/-- The per-scale weight `w_u(n) = 2u n^{−a} + u²/(u^{1/2−a})^K + u² e^{−u²/32}`. -/
def errWeight (a : ℝ) (K : ℕ) (u : ℝ) (n : ℕ) : ℝ :=
  2 * u * (n : ℝ) ^ (-a) + u ^ 2 / (u ^ (1 / 2 - a)) ^ K + u ^ 2 * Real.exp (-(u ^ 2) / 32)

theorem errWeight_nonneg (a : ℝ) (K : ℕ) {u : ℝ} (hu : 0 ≤ u) (n : ℕ) : 0 ≤ errWeight a K u n := by
  unfold errWeight
  positivity

/-- The choice `δ = u^{−(1/2+a)}` at scale `u ≥ 16`. -/
theorem scale_delta_bounds {u a : ℝ} (hu : 16 ≤ u) (ha0 : 0 ≤ a) :
    0 < u ^ (-(1 / 2 + a)) ∧ u ^ (-(1 / 2 + a)) ≤ 1 / 4 ∧
      u ^ (-(1 / 2 + a)) * u ^ (3 / 2 + a) = u ∧ u * u ^ (-(1 / 2 + a)) = u ^ (1 / 2 - a) := by
  have hu0 : 0 < u := by linarith
  refine ⟨Real.rpow_pos_of_pos hu0 _, ?_, ?_, ?_⟩
  · calc u ^ (-(1 / 2 + a)) ≤ u ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
      _ ≤ (16 : ℝ) ^ (-(1 / 2 : ℝ)) :=
          Real.rpow_le_rpow_of_nonpos (by norm_num) hu (by norm_num)
      _ = 1 / 4 := by
          rw [show (16 : ℝ) = 4 ^ (2 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
          norm_num
  · rw [← Real.rpow_add hu0, show -(1 / 2 + a) + (3 / 2 + a) = (1 : ℝ) by ring, Real.rpow_one]
  · rw [show u * u ^ (-(1 / 2 + a)) = u ^ (1 : ℝ) * u ^ (-(1 / 2 + a)) by rw [Real.rpow_one],
      ← Real.rpow_add hu0]
    ring_nf

/-- **From a pointwise envelope to the paired lower bound.** If
`‖M_u(log n) − c(n) ∫ ω_u log t‖ ≤ D W(n)` for every `n ≠ 0`, then
`Σ_{n∈F} v(n) Re M_u(log n) ≥ (Σ_{n∈F} v(n) c(n)) Re ∫ ω_u log t − D Σ_{n∈F} |v(n)| W(n)`. -/
theorem sum_re_weightedMoment_ge_of_norm_le {u : ℝ} {q : ℝ → ℝ} {c W : ℕ → ℝ} {D : ℝ}
    (hW : ∀ n : ℕ, n ≠ 0 → ‖ZetaNotch.weightedMoment u q (Real.log n) -
      ((c n : ℝ) : ℂ) * logWindow u‖ ≤ D * W n) {v : ℕ → ℝ} (hv0 : v 0 = 0) (F : Finset ℕ) :
    (∑ n ∈ F, v n * c n) * (logWindow u).re - D * ∑ n ∈ F, |v n| * W n ≤
      ∑ n ∈ F, v n * (ZetaNotch.weightedMoment u q (Real.log n)).re := by
  have hpt : ∀ n ∈ F, v n * c n * (logWindow u).re - D * (|v n| * W n) ≤
      v n * (ZetaNotch.weightedMoment u q (Real.log n)).re := by
    intro n _
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hv0]; simp
    have hre : |(ZetaNotch.weightedMoment u q (Real.log n)).re - c n * (logWindow u).re| ≤
        D * W n := by
      have := Complex.abs_re_le_norm (ZetaNotch.weightedMoment u q (Real.log n) -
        ((c n : ℝ) : ℂ) * logWindow u)
      rw [Complex.sub_re, Complex.re_ofReal_mul] at this
      exact this.trans (hW n hn.ne')
    have h1 := abs_le.mp hre
    rcases le_or_gt 0 (v n) with hvn | hvn
    · rw [abs_of_nonneg hvn]
      nlinarith [mul_le_mul_of_nonneg_left h1.1 hvn]
    · rw [abs_of_neg hvn]
      nlinarith [mul_le_mul_of_nonpos_left h1.2 hvn.le]
  calc (∑ n ∈ F, v n * c n) * (logWindow u).re - D * ∑ n ∈ F, |v n| * W n
      = ∑ n ∈ F, (v n * c n * (logWindow u).re - D * (|v n| * W n)) := by
        rw [Finset.sum_sub_distrib, Finset.sum_mul, Finset.mul_sum]
    _ ≤ _ := Finset.sum_le_sum hpt

/-- **The per-scale lower bound.** -/
theorem exists_sum_re_weightedMoment_ge (hP : ∀ p ∈ P, p.Prime) (K : ℕ) (ε : ℝ) {n₀ : ℕ}
    (hn₀ : IsSmoothOver P n₀) {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    ∃ D, 0 ≤ D ∧ ∀ {v : ℕ → ℝ}, v 0 = 0 → ∀ (F : Finset ℕ) {u : ℝ}, 16 ≤ u →
      (∑ n ∈ F, v n * mainWeight P ε n₀ n) * (∏ p : P, (1 - primeHalf p ^ 2)) *
          (logWindow u).re - D * ∑ n ∈ F, |v n| * errWeight a K u n ≤
        ∑ n ∈ F, v n * (ZetaNotch.weightedMoment u (notchWeight P ε n₀) (Real.log n)).re := by
  obtain ⟨D, hD0, hD⟩ := exists_norm_weightedMoment_sub_mainWeight_le_decay hP K ε hn₀ ha0 ha
  refine ⟨D, hD0, fun {v} hv0 F {u} hu => ?_⟩
  obtain ⟨hδ0, hδ4, hδu, huδ⟩ := scale_delta_bounds hu ha0.le
  have h := sum_re_weightedMoment_ge_of_norm_le (u := u) (q := notchWeight P ε n₀)
    (c := fun n => mainWeight P ε n₀ n * ∏ p : P, (1 - primeHalf p ^ 2))
    (W := errWeight a K u) (D := D) (fun n hn => by
      have h := hD hu hδ0 hδ4 (n := n) hn
      rw [hδu, huδ] at h
      refine h.trans (le_of_eq ?_)
      unfold errWeight
      ring) hv0 F
  have e : (∑ n ∈ F, v n * mainWeight P ε n₀ n) * (∏ p : P, (1 - primeHalf p ^ 2)) =
      ∑ n ∈ F, v n * (mainWeight P ε n₀ n * ∏ p : P, (1 - primeHalf p ^ 2)) := by
    rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun n _ => by ring
  rw [e]; exact h

/-! ## Small scales -/

/-- At small scales the notch moment is `O(u)`. -/
theorem exists_norm_weightedMoment_le_small {q : ℝ → ℝ} {CQ : ℝ} (hqb : ∀ t, |q t| ≤ CQ) :
    ∃ C, 0 ≤ C ∧ ∀ {u : ℝ}, 0 < u → u ≤ 16 → ∀ y : ℝ,
      ‖ZetaNotch.weightedMoment u q y‖ ≤ C * u := by
  obtain ⟨CZ, hCZ0, hCZ⟩ := exists_norm_zetaSq_le
  have hCQ0 : 0 ≤ CQ := (abs_nonneg _).trans (hqb 0)
  refine ⟨2 * (CQ * CZ * 41 ^ 2), by positivity, fun {u} hu hu16 y => ?_⟩
  set g : ℝ → ℝ := fun t => notchProfile (t / u) * (CQ * CZ * (1 + |t|) ^ 2) with hg
  have hgc : Continuous g :=
    (continuous_notchProfile.comp (by fun_prop)).mul (by fun_prop)
  have hgs : HasCompactSupport g := by
    refine HasCompactSupport.intro (K := Icc (u / 2) (5 / 2 * u)) isCompact_Icc fun t ht => ?_
    simp only [mem_Icc, not_and_or, not_le] at ht
    have hB : notchProfile (t / u) = 0 := by
      rcases ht with h | h
      · exact notchProfile_eq_zero_of_le (by rw [div_le_iff₀ hu]; linarith)
      · exact notchProfile_eq_zero_of_ge (by rw [le_div_iff₀ hu]; linarith)
    rw [hg]
    simp only [hB, zero_mul]
  unfold ZetaNotch.weightedMoment
  have hbound : ∀ t, ‖notchWindow u t * (q t : ℂ) * zetaSq t * Complex.exp (-(y * t) * I)‖ ≤ g t := by
    intro t
    have h := norm_momentIntegrand_le hqb hCZ y t
    rw [show notchWindow u t * (q t : ℂ) * zetaSq t * Complex.exp (-(y * t) * I) =
      notchWindow u t * ((q t : ℂ) * zetaSq t * Complex.exp (-(y * t) * I)) by ring, norm_mul,
      notchWindow_eq_notchProfile hu, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (notchProfile_nonneg _)]
    exact mul_le_mul_of_nonneg_left h (notchProfile_nonneg _)
  refine (norm_integral_le_of_norm_le (hgc.integrable_of_hasCompactSupport hgs)
    (Eventually.of_forall hbound)).trans ?_
  have h := integral_notchProfile_mul_le hu (f := fun t => CQ * CZ * (1 + |t|) ^ 2)
    (fun t => by positivity) (K := CQ * CZ * 41 ^ 2) (fun t ht => by
      have ht0 : 0 ≤ t := by linarith [ht.1]
      rw [abs_of_nonneg ht0]
      exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (by linarith) (by linarith [ht.2]) 2)
        (by positivity))
  calc ∫ t, g t ≤ 2 * u * (CQ * CZ * 41 ^ 2) := h
    _ = 2 * (CQ * CZ * 41 ^ 2) * u := by ring

/-! ## Gaussian scale integrals -/

theorem scaleWeight_le_half (L u : ℝ) :
    scaleWeight L u ≤ Real.exp (-((u - L) ^ 2 / 2)) :=
  Real.exp_le_exp.mpr (by nlinarith [sq_nonneg (u - L)])

theorem scaleWeight_le_of_le_half {L u : ℝ} (hL : 0 ≤ L) (hu : u ≤ L / 2) :
    scaleWeight L u ≤ Real.exp (-(L ^ 2 / 8)) * Real.exp (-((u - L) ^ 2 / 2)) := by
  rw [scaleWeight, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have : L ^ 2 / 4 ≤ (u - L) ^ 2 := by nlinarith
  linarith

/-- The Gaussian majorant `∫ e^{−(u−L)²/2} du`, independent of `L`. -/
def gaussHalf : ℝ := ∫ w : ℝ, Real.exp (-(1 / 2 * w ^ 2))

theorem gaussHalf_nonneg : 0 ≤ gaussHalf := integral_nonneg fun _ => (Real.exp_pos _).le

theorem integrable_gaussShift (L : ℝ) :
    Integrable (fun u : ℝ => Real.exp (-((u - L) ^ 2 / 2))) := by
  refine ((integrable_exp_neg_mul_sq' (b := 1 / 2) (by norm_num)).comp_sub_right L).congr
    (Eventually.of_forall fun u => ?_)
  simp only
  congr 1
  ring

theorem integral_gaussShift (L : ℝ) : ∫ u : ℝ, Real.exp (-((u - L) ^ 2 / 2)) = gaussHalf := by
  rw [gaussHalf, ← integral_sub_right_eq_self (fun w : ℝ => Real.exp (-(1 / 2 * w ^ 2))) L]
  congr 1
  funext u
  congr 1
  ring

/-- A pointwise majorant `ρ_L(u) f(u) ≤ M e^{−(u−L)²/2}` on `Ioi 16` integrates to `≤ M ∫ e^{…}`. -/
theorem setIntegral_scaleWeight_mul_le {L M : ℝ} (hM : 0 ≤ M) {f : ℝ → ℝ}
    (hf : IntegrableOn (fun u => scaleWeight L u * f u) (Ioi 16))
    (hpt : ∀ u ∈ Ioi (16 : ℝ), scaleWeight L u * f u ≤ M * Real.exp (-((u - L) ^ 2 / 2))) :
    ∫ u in Ioi 16, scaleWeight L u * f u ≤ M * gaussHalf := by
  calc ∫ u in Ioi 16, scaleWeight L u * f u
      ≤ ∫ u in Ioi 16, M * Real.exp (-((u - L) ^ 2 / 2)) :=
        setIntegral_mono_on hf ((integrable_gaussShift L).const_mul M).integrableOn
          measurableSet_Ioi hpt
    _ = M * ∫ u in Ioi 16, Real.exp (-((u - L) ^ 2 / 2)) := integral_const_mul _ _
    _ ≤ M * gaussHalf := by
        refine mul_le_mul_of_nonneg_left ?_ hM
        rw [← integral_gaussShift L]
        exact setIntegral_le_integral (integrable_gaussShift L)
          (Eventually.of_forall fun _ => (Real.exp_pos _).le)

theorem integrableOn_scaleWeight_mul_log (L : ℝ) :
    IntegrableOn (fun u => scaleWeight L u * Real.log u) (Ioi 16) := by
  refine (integrable_scaleWeight_mul_quadratic L 0 1 0).integrableOn.mono' ?_ ?_
  · exact ((Real.continuous_exp.comp (by fun_prop)).continuousOn.mul
      (Real.continuousOn_log.mono fun u hu => by
        have : (16 : ℝ) < u := hu
        exact ne_of_gt (by linarith))).aestronglyMeasurable measurableSet_Ioi
  · rw [ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun u hu => ?_
    have hu16 : (16 : ℝ) < u := hu
    have hlog0 : 0 ≤ Real.log u := Real.log_nonneg (by linarith)
    have hlogu : Real.log u ≤ u := (Real.log_le_sub_one_of_pos (by linarith)).trans (by linarith)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (scaleWeight_pos L u).le hlog0)]
    have := scaleWeight_pos L u
    nlinarith

/-- **The main scale integral**: `∫_{u>16} ρ_L(u) log u du ≥ 2e^{−1} log(L − 1)` for `L ≥ 18`. -/
theorem setIntegral_scaleWeight_mul_log_ge {L : ℝ} (hL : 18 ≤ L) :
    2 * Real.exp (-1) * Real.log (L - 1) ≤ ∫ u in Ioi 16, scaleWeight L u * Real.log u := by
  have hint := integrableOn_scaleWeight_mul_log L
  have hsub : Icc (L - 1) (L + 1) ⊆ Ioi (16 : ℝ) := fun u hu => by
    simp only [mem_Ioi]; linarith [hu.1]
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi 16)] fun u => scaleWeight L u * Real.log u := by
    rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioi]
    refine Eventually.of_forall fun u hu => ?_
    have hu16 : (16 : ℝ) < u := hu
    exact mul_nonneg (scaleWeight_pos L u).le (Real.log_nonneg (by linarith))
  have h1 : ∫ u in Icc (L - 1) (L + 1), scaleWeight L u * Real.log u ≤
      ∫ u in Ioi 16, scaleWeight L u * Real.log u :=
    setIntegral_mono_set hint hnn (Eventually.of_forall hsub)
  have h2 : ∫ u in Icc (L - 1) (L + 1), Real.exp (-1) * Real.log (L - 1) ≤
      ∫ u in Icc (L - 1) (L + 1), scaleWeight L u * Real.log u := by
    refine setIntegral_mono_on (integrableOn_const (by
      rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)) (hint.mono_set hsub) measurableSet_Icc
      fun u hu => ?_
    have hL1 : 0 < L - 1 := by linarith
    have hlog : Real.log (L - 1) ≤ Real.log u := Real.log_le_log hL1 hu.1
    have hlog0 : 0 ≤ Real.log (L - 1) := Real.log_nonneg (by linarith)
    have hρ : Real.exp (-1) ≤ scaleWeight L u := by
      rw [scaleWeight]
      refine Real.exp_le_exp.mpr ?_
      have : (u - L) ^ 2 ≤ 1 := by
        have h1 := hu.1
        have h2 := hu.2
        nlinarith
      linarith
    exact mul_le_mul hρ hlog hlog0 (scaleWeight_pos L u).le
  rw [setIntegral_const, Real.volume_real_Icc_of_le (by linarith), smul_eq_mul] at h2
  have : (L + 1 - (L - 1)) * (Real.exp (-1) * Real.log (L - 1)) =
      2 * Real.exp (-1) * Real.log (L - 1) := by ring
  linarith

/-- `(1 + L)^M e^{−L²/256} ≤ B_M`. -/
theorem exists_pow_mul_exp_neg_le (M : ℕ) :
    ∃ B, 0 ≤ B ∧ ∀ L : ℝ, 0 ≤ L → (1 + L) ^ M * Real.exp (-(L ^ 2 / 256)) ≤ B := by
  refine ⟨512 ^ M * M.factorial * Real.exp (1 / 256), by positivity, fun L hL => ?_⟩
  have h1 : 1 ≤ 1 + L := by linarith
  have hx : 0 ≤ (1 + L) ^ 2 / 512 := by positivity
  have h2 := Real.pow_div_factorial_le_exp _ hx M
  have hf : (0 : ℝ) < M.factorial := by exact_mod_cast M.factorial_pos
  rw [div_le_iff₀ hf, div_pow] at h2
  have h3 : (1 + L) ^ M ≤ ((1 + L) ^ 2) ^ M := pow_le_pow_left₀ (by linarith)
    (by nlinarith) M
  have h4 : ((1 + L) ^ 2) ^ M ≤ 512 ^ M * (Real.exp ((1 + L) ^ 2 / 512) * M.factorial) := by
    rw [div_le_iff₀ (by positivity)] at h2
    linarith
  have h5 : Real.exp ((1 + L) ^ 2 / 512) * Real.exp (-(L ^ 2 / 256)) ≤ Real.exp (1 / 256) := by
    rw [← Real.exp_add]
    refine Real.exp_le_exp.mpr ?_
    nlinarith [sq_nonneg (L - 1)]
  calc (1 + L) ^ M * Real.exp (-(L ^ 2 / 256))
      ≤ (512 ^ M * (Real.exp ((1 + L) ^ 2 / 512) * M.factorial)) * Real.exp (-(L ^ 2 / 256)) :=
        mul_le_mul_of_nonneg_right (h3.trans h4) (Real.exp_pos _).le
    _ = 512 ^ M * M.factorial * (Real.exp ((1 + L) ^ 2 / 512) * Real.exp (-(L ^ 2 / 256))) := by
        ring
    _ ≤ 512 ^ M * M.factorial * Real.exp (1 / 256) :=
        mul_le_mul_of_nonneg_left h5 (by positivity)

end RHTower.WeilAbscissa
