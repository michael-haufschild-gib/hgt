import GaloisForLFunctions.RHTower.ThetaCriticalFluxBernstein


/-!
# The completed theta source is a pure ray of the prime-deletion Bernstein cone

`ThetaPrimeDeletionCone f` collects the continuous sources whose normalized critical flux
`b_f(t) = t^{-3/2} ∫_{[log t/2, ∞)} e^{x/2} f` and every single-prime-deleted flux
`b_{D_p f}(t) = b_f(t) - p² b_f(p² t)` are completely monotone on `(0,∞)`.

* The completed source `k` belongs to the cone, with `b_k(t) = 2π ∑ n² e^{-π n² t}`.
* **Pure ray.**  If `k = f₁ + f₂` with both summands in the cone, then `f₁ = c k`, `f₂ = (1-c) k`
  for some `c ∈ [0,1]`: Bernstein--Widder gives dominated Gaussian-rate weights, prime deletion makes
  both summands saturate the zero faces `a_n = p² a_{n/p}`, hence `a_n = n² a_1`, and the flux
  determines the source.
* **Sharpness.**  For every finite set of primes `P` there are two nonproportional members of the
  `P`-restricted cone adding up to `k`.
-/

open MeasureTheory Set Filter Topology
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- Continuous sources whose critical weight `e^{x/2} f` is integrable on every right ray. -/
def ThetaFluxSource (f : ℝ → ℝ) : Prop :=
  Continuous f ∧ ∀ X : ℝ, IntegrableOn (fun x => Real.exp (x / 2) * f x) (Ioi X)

theorem thetaFluxSource_thetaCuspFullSource : ThetaFluxSource thetaCuspFullSource := by
  refine ⟨continuous_thetaCuspFullSource, fun X => ?_⟩
  have h := HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource (1 / 2)
  exact (h.congr (Eventually.of_forall fun x => by simp only; ring_nf)).integrableOn

theorem ThetaFluxSource.add {f g : ℝ → ℝ} (hf : ThetaFluxSource f) (hg : ThetaFluxSource g) :
    ThetaFluxSource (fun x => f x + g x) :=
  ⟨hf.1.add hg.1, fun X => ((hf.2 X).add (hg.2 X)).congr_fun
    (fun x _ => by simp only [Pi.add_apply]; ring) measurableSet_Ioi⟩

theorem ThetaFluxSource.const_mul {f : ℝ → ℝ} (hf : ThetaFluxSource f) (c : ℝ) :
    ThetaFluxSource (fun x => c * f x) :=
  ⟨continuous_const.mul hf.1, fun X => IntegrableOn.congr_fun ((hf.2 X).const_mul c)
    (fun x _ => by simp only; ring) measurableSet_Ioi⟩

theorem ThetaFluxSource.comp_add {f : ℝ → ℝ} (hf : ThetaFluxSource f) (s : ℝ) :
    ThetaFluxSource (fun x => f (x + s)) := by
  refine ⟨hf.1.comp (continuous_id.add continuous_const), fun X => ?_⟩
  have h := ((measurePreserving_add_right volume s).integrableOn_comp_preimage
    (measurableEmbedding_addRight s)).mpr (hf.2 (X + s))
  have hpre : (fun x : ℝ => x + s) ⁻¹' Ioi (X + s) = Ioi X := by
    ext x
    simp
  rw [hpre] at h
  refine IntegrableOn.congr_fun (h.const_mul (Real.exp (-s / 2))) (fun x _ => ?_) measurableSet_Ioi
  simp only [Function.comp_apply]
  rw [← mul_assoc, ← Real.exp_add]
  ring_nf

/-- **Source recovery (6).**  `d/dx [e^{3x} b_f(e^{2x})] = -e^{x/2} f(x)`. -/
theorem hasDerivAt_exp_mul_thetaNormalizedFlux {f : ℝ → ℝ} (hf : ThetaFluxSource f) (x : ℝ) :
    HasDerivAt (fun y => Real.exp (3 * y) * thetaNormalizedFlux f (Real.exp (2 * y)))
      (-(Real.exp (x / 2) * f x)) x := by
  have heq : (fun y => Real.exp (3 * y) * thetaNormalizedFlux f (Real.exp (2 * y))) =
      fun Y => (∫ z in Ioi 0, Real.exp (z / 2) * f z) -
        ∫ z in (0 : ℝ)..Y, Real.exp (z / 2) * f z := by
    funext Y
    rw [thetaNormalizedFlux_exp, ← mul_assoc, ← Real.exp_add,
      show 3 * Y + -3 * Y = 0 by ring, Real.exp_zero, one_mul,
      ← intervalIntegral.integral_interval_add_Ioi (hf.2 0) (hf.2 Y)]
    ring
  rw [heq]
  have hc : Continuous fun z : ℝ => Real.exp (z / 2) * f z := by
    have := hf.1; fun_prop
  exact (intervalIntegral.integral_hasDerivAt_right (hc.intervalIntegrable _ _)
    (hc.stronglyMeasurableAtFilter _ _) hc.continuousAt).const_sub _

theorem thetaNormalizedFlux_add {f g : ℝ → ℝ} (hf : ThetaFluxSource f) (hg : ThetaFluxSource g)
    (t : ℝ) :
    thetaNormalizedFlux (fun x => f x + g x) t = thetaNormalizedFlux f t + thetaNormalizedFlux g t := by
  unfold thetaNormalizedFlux
  rw [integral_Ici_eq_integral_Ioi, integral_Ici_eq_integral_Ioi, integral_Ici_eq_integral_Ioi,
    ← mul_add, ← integral_add (hf.2 _) (hg.2 _)]
  congr 1
  apply integral_congr_ae
  filter_upwards with x
  ring

theorem thetaNormalizedFlux_const_mul (f : ℝ → ℝ) (c t : ℝ) :
    thetaNormalizedFlux (fun x => c * f x) t = c * thetaNormalizedFlux f t := by
  unfold thetaNormalizedFlux
  have h : (∫ x in Ici (Real.log t / 2), Real.exp (x / 2) * (c * f x)) =
      c * ∫ x in Ici (Real.log t / 2), Real.exp (x / 2) * f x := by
    rw [← integral_const_mul]
    congr 1
    funext x
    ring
  rw [h]
  ring

/-- Flux of a single-prime deletion: `b_{D_p f}(t) = b_f(t) - p² b_f(p² t)`. -/
theorem thetaNormalizedFlux_primeDeletion {f : ℝ → ℝ} (hf : ThetaFluxSource f) {p : ℕ}
    (hp : 0 < p) {t : ℝ} (ht : 0 < t) :
    thetaNormalizedFlux (thetaPrimeDeletion {p} f) t =
      thetaNormalizedFlux f t - (p : ℝ) ^ 2 * thetaNormalizedFlux f ((p : ℝ) ^ 2 * t) := by
  have hpR : (0 : ℝ) < p := by exact_mod_cast hp
  have hD : thetaPrimeDeletion {p} f =
      fun x => f x + (-(p : ℝ) ^ (-(1 / 2 : ℝ))) * f (x + Real.log p) := by
    funext x
    rw [show ({p} : Finset ℕ) = insert p ∅ by rfl, thetaPrimeDeletion_insert hp (by simp)
      (by simp), thetaPrimeDeletion_empty]
    ring
  rw [hD, thetaNormalizedFlux_add hf ((hf.comp_add _).const_mul _),
    thetaNormalizedFlux_const_mul, thetaNormalizedFlux_comp_add f _ ht]
  have h5 : Real.exp (5 * Real.log p / 2) = (p : ℝ) ^ (5 / 2 : ℝ) := by
    rw [Real.rpow_def_of_pos hpR]; ring_nf
  have h2 : Real.exp (2 * Real.log p) = (p : ℝ) ^ 2 := by
    rw [show 2 * Real.log p = Real.log ((p : ℝ) ^ 2) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity)]
  rw [h5, h2]
  have hpow : (p : ℝ) ^ (-(1 / 2 : ℝ)) * (p : ℝ) ^ (5 / 2 : ℝ) = (p : ℝ) ^ 2 := by
    rw [← Real.rpow_add hpR]; norm_num
  rw [← hpow]
  ring


/-! ## The Gaussian rate lattice -/

/-- Gaussian rates `λ_n = π n²`. -/
noncomputable def thetaGaussRate (n : ℕ) : ℝ := Real.pi * (n : ℝ) ^ 2

/-- Theta rate weights `2π n²`. -/
noncomputable def thetaGaussWeight (n : ℕ) : ℝ := 2 * Real.pi * (n : ℝ) ^ 2

theorem thetaGaussRate_nonneg (n : ℕ) : 0 ≤ thetaGaussRate n := by
  unfold thetaGaussRate; positivity

theorem thetaGaussRate_injective : Function.Injective thetaGaussRate := by
  intro a b h
  unfold thetaGaussRate at h
  have h2 : (a : ℝ) ^ 2 = (b : ℝ) ^ 2 := mul_left_cancel₀ Real.pi_ne_zero h
  have := (sq_eq_sq₀ (Nat.cast_nonneg a) (Nat.cast_nonneg b)).mp h2
  exact_mod_cast this

theorem thetaGaussWeight_nonneg (n : ℕ) : 0 ≤ thetaGaussWeight n := by
  unfold thetaGaussWeight; positivity

theorem summable_thetaGaussWeight {t : ℝ} (ht : 0 < t) :
    Summable fun n : ℕ => thetaGaussWeight n * Real.exp (-thetaGaussRate n * t) := by
  have h := (summable_pow_mul_exp_neg_nat_sq 2 (mul_pos Real.pi_pos ht)).mul_left (2 * Real.pi)
  refine h.congr fun n => ?_
  unfold thetaGaussWeight thetaGaussRate
  ring_nf

theorem thetaNormalizedFlux_thetaCuspFullSource_eq {t : ℝ} (ht : 0 < t) :
    thetaNormalizedFlux thetaCuspFullSource t =
      ∑' n : ℕ, thetaGaussWeight n * Real.exp (-thetaGaussRate n * t) := by
  rw [thetaNormalizedFlux_thetaCuspFullSource ht]
  apply tsum_congr
  intro n
  unfold thetaGaussWeight thetaGaussRate
  ring_nf

/-- The dilation `m ↦ p m` transports an exponential sum on the Gaussian rates. -/
theorem tsum_dilate_thetaGaussRate {p : ℕ} (hp : 0 < p) (v : ℕ → ℝ) (t : ℝ) :
    (∑' m : ℕ, v m * Real.exp (-thetaGaussRate m * ((p : ℝ) ^ 2 * t))) =
      ∑' n : ℕ, (if p ∣ n then v (n / p) else 0) * Real.exp (-thetaGaussRate n * t) := by
  have hinj : Function.Injective (fun m : ℕ => p * m) := fun a b h =>
    Nat.eq_of_mul_eq_mul_left hp h
  set F : ℕ → ℝ := fun n => (if p ∣ n then v (n / p) else 0) * Real.exp (-thetaGaussRate n * t)
  have hsupp : Function.support F ⊆ Set.range (fun m : ℕ => p * m) := by
    intro n hn
    by_contra h
    apply hn
    have : ¬ p ∣ n := fun ⟨m, hm⟩ => h ⟨m, hm.symm⟩
    simp [F, this]
  rw [← hinj.tsum_eq hsupp]
  apply tsum_congr
  intro m
  simp only [F, dvd_mul_right, if_true, Nat.mul_div_cancel_left m hp, thetaGaussRate]
  push_cast
  ring_nf

theorem summable_dilate_coeff {p : ℕ} (hp : 0 < p) {v : ℕ → ℝ} {t : ℝ} (ht : 0 < t)
    (hv : ∀ n, |v n| ≤ thetaGaussWeight n) :
    Summable fun n : ℕ => |(if p ∣ n then v (n / p) else 0)| * Real.exp (-thetaGaussRate n * t) := by
  have hinj : Function.Injective (fun m : ℕ => p * m) := fun a b h =>
    Nat.eq_of_mul_eq_mul_left hp h
  have hbase : Summable fun m : ℕ => |v m| * Real.exp (-thetaGaussRate (p * m) * t) := by
    refine Summable.of_nonneg_of_le (fun m => by positivity) (fun m => ?_)
      (summable_thetaGaussWeight (t := (p : ℝ) ^ 2 * t) (by positivity))
    have hrate : thetaGaussRate (p * m) * t = thetaGaussRate m * ((p : ℝ) ^ 2 * t) := by
      unfold thetaGaussRate; push_cast; ring
    rw [show -thetaGaussRate (p * m) * t = -(thetaGaussRate (p * m) * t) by ring, hrate,
      show -(thetaGaussRate m * ((p : ℝ) ^ 2 * t)) = -thetaGaussRate m * ((p : ℝ) ^ 2 * t) by ring]
    exact mul_le_mul_of_nonneg_right (hv m) (Real.exp_pos _).le
  rw [← hinj.summable_iff]
  · refine hbase.congr fun m => ?_
    simp [Nat.mul_div_cancel_left m hp]
  · intro n hn
    have : ¬ p ∣ n := fun ⟨m, hm⟩ => hn ⟨m, hm.symm⟩
    simp [this]


/-! ## Single-prime deletion of an exponential flux -/

/-- If `b_f = ∑ v_n e^{-π n² t}`, then `b_{D_p f} = ∑ (v_n - p² v_{n/p} [p ∣ n]) e^{-π n² t}`. -/
theorem thetaNormalizedFlux_primeDeletion_eq_tsum {f : ℝ → ℝ} (hf : ThetaFluxSource f) {p : ℕ}
    (hp : 0 < p) {v : ℕ → ℝ} (hv : ∀ n, |v n| ≤ thetaGaussWeight n)
    (hrep : ∀ t, 0 < t → thetaNormalizedFlux f t = ∑' n, v n * Real.exp (-thetaGaussRate n * t))
    {t : ℝ} (ht : 0 < t) :
    thetaNormalizedFlux (thetaPrimeDeletion {p} f) t =
      ∑' n, (v n - (p : ℝ) ^ 2 * (if p ∣ n then v (n / p) else 0)) *
        Real.exp (-thetaGaussRate n * t) := by
  have hs1 : Summable fun n => v n * Real.exp (-thetaGaussRate n * t) :=
    Summable.of_norm_bounded (summable_thetaGaussWeight ht) (fun n => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
      exact mul_le_mul_of_nonneg_right (hv n) (Real.exp_pos _).le)
  have hs2' : Summable fun n => (if p ∣ n then v (n / p) else 0) *
      Real.exp (-thetaGaussRate n * t) := by
    apply Summable.of_norm
    refine (summable_dilate_coeff hp ht hv).congr fun n => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hs2 : Summable fun n => (p : ℝ) ^ 2 * ((if p ∣ n then v (n / p) else 0) *
      Real.exp (-thetaGaussRate n * t)) := hs2'.mul_left _
  have hpt : 0 < (p : ℝ) ^ 2 * t := mul_pos (pow_pos (by exact_mod_cast hp) 2) ht
  have e1 := thetaNormalizedFlux_primeDeletion hf hp ht
  have e2 := hrep t ht
  have e3 := hrep _ hpt
  have e4 := tsum_dilate_thetaGaussRate hp v t
  have e5 : (p : ℝ) ^ 2 * (∑' n : ℕ, (if p ∣ n then v (n / p) else 0) *
      Real.exp (-thetaGaussRate n * t)) =
      ∑' n : ℕ, (p : ℝ) ^ 2 * ((if p ∣ n then v (n / p) else 0) *
        Real.exp (-thetaGaussRate n * t)) := (tsum_mul_left).symm
  have e6 := hs1.tsum_sub hs2
  calc thetaNormalizedFlux (thetaPrimeDeletion {p} f) t
      = (∑' n, v n * Real.exp (-thetaGaussRate n * t)) -
          (p : ℝ) ^ 2 * ∑' n : ℕ, (if p ∣ n then v (n / p) else 0) *
            Real.exp (-thetaGaussRate n * t) := by rw [e1, e2, e3, e4]
    _ = ∑' n, (v n * Real.exp (-thetaGaussRate n * t) - (p : ℝ) ^ 2 *
          ((if p ∣ n then v (n / p) else 0) * Real.exp (-thetaGaussRate n * t))) := by
        rw [e5, e6]
    _ = _ := tsum_congr fun n => by ring

/-- Complete monotonicity of a deleted flux forces nonnegative deleted coefficients. -/
theorem primeDeletion_coeff_nonneg {f : ℝ → ℝ} (hf : ThetaFluxSource f) {p : ℕ} (hp : 0 < p)
    {v : ℕ → ℝ} (hv : ∀ n, |v n| ≤ thetaGaussWeight n)
    (hrep : ∀ t, 0 < t → thetaNormalizedFlux f t = ∑' n, v n * Real.exp (-thetaGaussRate n * t))
    (hCM : CompletelyMonotoneOn (thetaNormalizedFlux (thetaPrimeDeletion {p} f))) (n : ℕ) :
    0 ≤ v n - (p : ℝ) ^ 2 * (if p ∣ n then v (n / p) else 0) := by
  set c : ℕ → ℝ := fun n => v n - (p : ℝ) ^ 2 * (if p ∣ n then v (n / p) else 0)
  have hcs : ∀ t, 0 < t → Summable fun n => |c n| * Real.exp (-thetaGaussRate n * t) := by
    intro t ht
    refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
      ((summable_thetaGaussWeight ht).add ((summable_dilate_coeff hp ht hv).mul_left ((p : ℝ) ^ 2)))
    simp only [c]
    have h1 := abs_sub (v n) ((p : ℝ) ^ 2 * (if p ∣ n then v (n / p) else 0))
    rw [abs_mul (((p : ℝ) ^ 2)), abs_of_nonneg (by positivity : (0 : ℝ) ≤ (p : ℝ) ^ 2)] at h1
    have h2 := mul_le_mul_of_nonneg_right h1 (Real.exp_pos (-thetaGaussRate n * t)).le
    have h3 := mul_le_mul_of_nonneg_right (hv n) (Real.exp_pos (-thetaGaussRate n * t)).le
    nlinarith
  have heq : EqOn (thetaNormalizedFlux (thetaPrimeDeletion {p} f))
      (fun t => ∑' n, c n * Real.exp (-thetaGaussRate n * t)) (Ioi 0) := fun t ht =>
    thetaNormalizedFlux_primeDeletion_eq_tsum hf hp hv hrep ht
  have h := tsum_coeff_nonneg_of_completelyMonotoneOn c thetaGaussRate thetaGaussRate_nonneg hcs
    (hCM.congr_Ioi heq) (thetaGaussRate n)
  rwa [tsum_ite_lam_eq c thetaGaussRate thetaGaussRate_injective n] at h

/-! ## The prime-deletion Bernstein cone and its pure ray -/

/-- The cone of continuous sources whose flux and every single-prime-deleted flux are completely
monotone on `(0,∞)`. -/
def ThetaPrimeDeletionCone (f : ℝ → ℝ) : Prop :=
  ThetaFluxSource f ∧ CompletelyMonotoneOn (thetaNormalizedFlux f) ∧
    ∀ p : ℕ, p.Prime → CompletelyMonotoneOn (thetaNormalizedFlux (thetaPrimeDeletion {p} f))

private theorem thetaGaussWeight_dvd {p m : ℕ} :
    thetaGaussWeight (p * m) = (p : ℝ) ^ 2 * thetaGaussWeight m := by
  unfold thetaGaussWeight
  push_cast
  ring

/-- The literal completed theta source belongs to the cone. -/
theorem thetaCuspFullSource_mem_primeDeletionCone : ThetaPrimeDeletionCone thetaCuspFullSource := by
  have hw : ∀ n, |thetaGaussWeight n| ≤ thetaGaussWeight n := fun n =>
    le_of_eq (abs_of_nonneg (thetaGaussWeight_nonneg n))
  have hrep : ∀ t, 0 < t → thetaNormalizedFlux thetaCuspFullSource t =
      ∑' n, thetaGaussWeight n * Real.exp (-thetaGaussRate n * t) := fun t ht =>
    thetaNormalizedFlux_thetaCuspFullSource_eq ht
  refine ⟨thetaFluxSource_thetaCuspFullSource, ?_, fun p hp => ?_⟩
  · exact (completelyMonotoneOn_tsum_exp thetaGaussWeight thetaGaussRate thetaGaussWeight_nonneg
      thetaGaussRate_nonneg fun t ht => summable_thetaGaussWeight ht).congr_Ioi
      (fun t ht => (hrep t ht).symm)
  · set c : ℕ → ℝ := fun n => thetaGaussWeight n -
      (p : ℝ) ^ 2 * (if p ∣ n then thetaGaussWeight (n / p) else 0)
    have hc : ∀ n, c n = if p ∣ n then 0 else thetaGaussWeight n := by
      intro n
      by_cases hn : p ∣ n
      · obtain ⟨m, rfl⟩ := hn
        simp [c, Nat.mul_div_cancel_left m hp.pos, thetaGaussWeight_dvd]
      · simp [c, hn]
    have hc0 : ∀ n, 0 ≤ c n := fun n => by
      rw [hc]; split_ifs <;> simp [thetaGaussWeight_nonneg]
    have hcs : ∀ t, 0 < t → Summable fun n => c n * Real.exp (-thetaGaussRate n * t) :=
      fun t ht => Summable.of_nonneg_of_le (fun n => mul_nonneg (hc0 n) (Real.exp_pos _).le)
        (fun n => by
          rw [hc]
          split_ifs
          · simp only [zero_mul]; exact mul_nonneg (thetaGaussWeight_nonneg n) (Real.exp_pos _).le
          · exact le_rfl) (summable_thetaGaussWeight ht)
    exact (completelyMonotoneOn_tsum_exp c thetaGaussRate hc0 thetaGaussRate_nonneg hcs).congr_Ioi
      (fun t ht => (thetaNormalizedFlux_primeDeletion_eq_tsum thetaFluxSource_thetaCuspFullSource
        hp.pos hw hrep ht).symm)

/-- `v_n = p² v_{n/p}` for every prime `p ∣ n` forces `v_n = n² v_1`. -/
theorem eq_sq_mul_of_prime_recursion {v : ℕ → ℝ}
    (h : ∀ p : ℕ, p.Prime → ∀ n, p ∣ n → v n = (p : ℝ) ^ 2 * v (n / p)) :
    ∀ n, 0 < n → v n = (n : ℝ) ^ 2 * v 1 := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro hn
    rcases eq_or_ne n 1 with rfl | hn1
    · simp
    · have hp := Nat.minFac_prime hn1
      have hdvd := Nat.minFac_dvd n
      have hm : n / n.minFac < n := Nat.div_lt_self hn hp.one_lt
      have hmpos : 0 < n / n.minFac := Nat.div_pos (Nat.minFac_le hn) hp.pos
      rw [h _ hp n hdvd, ih _ hm hmpos]
      have hn' : (n : ℝ) = (n.minFac : ℝ) * ((n / n.minFac : ℕ) : ℝ) := by
        rw [← Nat.cast_mul, Nat.mul_div_cancel' hdvd]
      rw [hn']
      ring

/-- **Pure-ray theorem.**  If `k = f₁ + f₂` with both summands in the prime-deletion Bernstein cone,
then `f₁ = c k` and `f₂ = (1 - c) k` for some `c ∈ [0,1]`. -/
theorem thetaPrimeDeletionCone_pure_ray {f₁ f₂ : ℝ → ℝ} (h₁ : ThetaPrimeDeletionCone f₁)
    (h₂ : ThetaPrimeDeletionCone f₂) (hsum : ∀ x, f₁ x + f₂ x = thetaCuspFullSource x) :
    ∃ c ∈ Icc (0 : ℝ) 1, f₁ = (fun x => c * thetaCuspFullSource x) ∧
      f₂ = (fun x => (1 - c) * thetaCuspFullSource x) := by
  have hadd : ∀ t, 0 < t → thetaNormalizedFlux f₁ t + thetaNormalizedFlux f₂ t =
      ∑' n, thetaGaussWeight n * Real.exp (-thetaGaussRate n * t) := by
    intro t ht
    rw [← thetaNormalizedFlux_add h₁.1 h₂.1, ← thetaNormalizedFlux_thetaCuspFullSource_eq ht]
    congr 1
    funext x
    exact hsum x
  obtain ⟨v, hv, hrep⟩ := exists_dominated_exp_representation thetaGaussWeight thetaGaussRate
    thetaGaussWeight_nonneg thetaGaussRate_nonneg thetaGaussRate_injective
    (fun t ht => summable_thetaGaussWeight ht) h₁.2.1 h₂.2.1 hadd
  set v' : ℕ → ℝ := fun n => thetaGaussWeight n - v n
  have hvabs : ∀ n, |v n| ≤ thetaGaussWeight n := fun n => by
    rw [abs_of_nonneg (hv n).1]; exact (hv n).2
  have hv'abs : ∀ n, |v' n| ≤ thetaGaussWeight n := fun n => by
    simp only [v']; rw [abs_of_nonneg (by linarith [(hv n).2])]; linarith [(hv n).1]
  have hrep' : ∀ t, 0 < t → thetaNormalizedFlux f₂ t = ∑' n, v' n * Real.exp (-thetaGaussRate n * t) := by
    intro t ht
    have hs1 : Summable fun n => thetaGaussWeight n * Real.exp (-thetaGaussRate n * t) :=
      summable_thetaGaussWeight ht
    have hs2 : Summable fun n => v n * Real.exp (-thetaGaussRate n * t) :=
      Summable.of_nonneg_of_le (fun n => mul_nonneg (hv n).1 (Real.exp_pos _).le)
        (fun n => mul_le_mul_of_nonneg_right (hv n).2 (Real.exp_pos _).le) hs1
    have := hadd t ht
    rw [hrep t ht] at this
    rw [show thetaNormalizedFlux f₂ t = (∑' n, thetaGaussWeight n * Real.exp (-thetaGaussRate n * t)) -
      ∑' n, v n * Real.exp (-thetaGaussRate n * t) by linarith, ← hs1.tsum_sub hs2]
    apply tsum_congr
    intro n
    simp only [v']
    ring
  have hrec : ∀ p : ℕ, p.Prime → ∀ n, p ∣ n → v n = (p : ℝ) ^ 2 * v (n / p) := by
    intro p hp n hn
    have c1 := primeDeletion_coeff_nonneg h₁.1 hp.pos hvabs hrep (h₁.2.2 p hp) n
    have c2 := primeDeletion_coeff_nonneg h₂.1 hp.pos hv'abs hrep' (h₂.2.2 p hp) n
    simp only [hn, if_true, v'] at c1 c2
    obtain ⟨m, rfl⟩ := hn
    rw [Nat.mul_div_cancel_left m hp.pos, thetaGaussWeight_dvd] at c2
    rw [Nat.mul_div_cancel_left m hp.pos] at c1 ⊢
    linarith
  have hsq := eq_sq_mul_of_prime_recursion hrec
  have hv0 : v 0 = 0 := le_antisymm (by simpa [thetaGaussWeight] using (hv 0).2) (hv 0).1
  set c : ℝ := v 1 / (2 * Real.pi)
  have hc : c ∈ Icc (0 : ℝ) 1 := by
    have h1 := (hv 1).1
    have h2 := (hv 1).2
    simp only [thetaGaussWeight, Nat.cast_one, one_pow, mul_one] at h2
    refine ⟨div_nonneg h1 (by positivity), ?_⟩
    rw [div_le_one (by positivity)]
    exact h2
  have hflux : ∀ t, 0 < t → thetaNormalizedFlux f₁ t =
      thetaNormalizedFlux (fun x => c * thetaCuspFullSource x) t := by
    intro t ht
    rw [thetaNormalizedFlux_const_mul, thetaNormalizedFlux_thetaCuspFullSource_eq ht, hrep t ht,
      ← tsum_mul_left]
    apply tsum_congr
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hv0, thetaGaussWeight]
    · rw [hsq n hn]
      simp only [c, thetaGaussWeight]
      field_simp
  have hf₁ : f₁ = fun x => c * thetaCuspFullSource x :=
    eq_of_thetaNormalizedFlux_eq h₁.1.1 (continuous_const.mul continuous_thetaCuspFullSource)
      h₁.1.2 (thetaFluxSource_thetaCuspFullSource.const_mul c).2 hflux
  refine ⟨c, hc, hf₁, ?_⟩
  funext x
  have := hsum x
  rw [hf₁] at this
  simp only at this
  linarith


/-! ## Sharpness: no finite list of prime tests suffices -/

/-- The cone restricted to the prime tests in `P`. -/
def ThetaPrimeDeletionConeOn (P : Finset ℕ) (f : ℝ → ℝ) : Prop :=
  ThetaFluxSource f ∧ CompletelyMonotoneOn (thetaNormalizedFlux f) ∧
    ∀ p ∈ P, CompletelyMonotoneOn (thetaNormalizedFlux (thetaPrimeDeletion {p} f))

/-- Flux of `a k + b k(· + log q)` on the Gaussian rate lattice. -/
theorem thetaNormalizedFlux_twoShift {q : ℕ} (hq : 0 < q) (a b : ℝ) {t : ℝ} (ht : 0 < t) :
    thetaNormalizedFlux (fun x => a * thetaCuspFullSource x +
        b * thetaCuspFullSource (x + Real.log q)) t =
      ∑' n, (a + b * Real.sqrt q * (if q ∣ n then 1 else 0)) * thetaGaussWeight n *
        Real.exp (-thetaGaussRate n * t) := by
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq
  have hS := thetaFluxSource_thetaCuspFullSource
  rw [thetaNormalizedFlux_add (hS.const_mul a) ((hS.comp_add _).const_mul b),
    thetaNormalizedFlux_const_mul, thetaNormalizedFlux_const_mul,
    thetaNormalizedFlux_comp_add _ _ ht, thetaNormalizedFlux_thetaCuspFullSource_eq ht,
    thetaNormalizedFlux_thetaCuspFullSource_eq (by positivity)]
  have h5 : Real.exp (5 * Real.log q / 2) = (q : ℝ) ^ (5 / 2 : ℝ) := by
    rw [Real.rpow_def_of_pos hqR]; ring_nf
  have h2 : Real.exp (2 * Real.log q) = (q : ℝ) ^ 2 := by
    rw [show 2 * Real.log q = Real.log ((q : ℝ) ^ 2) by rw [Real.log_pow]; norm_num,
      Real.exp_log (by positivity)]
  rw [h5, h2, tsum_dilate_thetaGaussRate hq thetaGaussWeight t]
  have hs1 := summable_thetaGaussWeight ht
  have hs2 : Summable fun n : ℕ => (if q ∣ n then thetaGaussWeight (n / q) else 0) *
      Real.exp (-thetaGaussRate n * t) := by
    apply Summable.of_norm
    refine (summable_dilate_coeff hq ht (v := thetaGaussWeight)
      (fun n => le_of_eq (abs_of_nonneg (thetaGaussWeight_nonneg n)))).congr fun n => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _)]
  have e1 : a * ∑' n, thetaGaussWeight n * Real.exp (-thetaGaussRate n * t) =
      ∑' n, a * (thetaGaussWeight n * Real.exp (-thetaGaussRate n * t)) := tsum_mul_left.symm
  have e2 : b * ((q : ℝ) ^ (5 / 2 : ℝ) * ∑' n : ℕ, (if q ∣ n then thetaGaussWeight (n / q) else 0) *
        Real.exp (-thetaGaussRate n * t)) =
      ∑' n : ℕ, b * ((q : ℝ) ^ (5 / 2 : ℝ) * ((if q ∣ n then thetaGaussWeight (n / q) else 0) *
        Real.exp (-thetaGaussRate n * t))) := by
    rw [← tsum_mul_left, ← tsum_mul_left]
  rw [e1, e2, ← (hs1.mul_left a).tsum_add ((hs2.mul_left _).mul_left b)]
  apply tsum_congr
  intro n
  by_cases hn : q ∣ n
  · obtain ⟨m, rfl⟩ := hn
    simp only [dvd_mul_right, if_true, Nat.mul_div_cancel_left m hq, thetaGaussWeight_dvd]
    have hsq : (q : ℝ) ^ (5 / 2 : ℝ) = (q : ℝ) ^ 2 * Real.sqrt q := by
      rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_add hqR]
      norm_num
    rw [hsq]
    ring
  · simp only [hn, if_false, mul_zero, add_zero]
    ring

/-- For primes `p ≠ q`, `q ∣ p m ↔ q ∣ m`. -/
private theorem prime_dvd_mul_iff {p q m : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) :
    q ∣ p * m ↔ q ∣ m := by
  constructor
  · intro h
    rcases (Nat.Prime.dvd_mul hq).mp h with h1 | h1
    · exact absurd ((Nat.prime_dvd_prime_iff_eq hq hp).mp h1).symm hpq
    · exact h1
  · exact fun h => h.mul_left p

theorem integral_exp_mul_thetaCuspFullSource_pos (w : ℝ) :
    0 < ∫ x : ℝ, Real.exp (w * x) * thetaCuspFullSource x := by
  have hint := HedenmalmThetaSource.integrable_exp_mul_thetaCuspFullSource w
  rw [integral_pos_iff_support_of_nonneg (fun x => mul_nonneg (Real.exp_pos _).le
    (thetaCuspFullSource_pos_all x).le) hint]
  have : Function.support (fun x : ℝ => Real.exp (w * x) * thetaCuspFullSource x) = Set.univ :=
    Set.eq_univ_of_forall fun x => (mul_pos (Real.exp_pos _) (thetaCuspFullSource_pos_all x)).ne'
  rw [this, Real.volume_univ]
  exact ENNReal.zero_lt_top

/-- **Every prime is needed.**  For every finite set `P` of primes there are two nonproportional
sources in the `P`-restricted cone that add up to the completed source. -/
theorem thetaPrimeDeletionCone_finite_tests_insufficient (P : Finset ℕ)
    (hP : ∀ p ∈ P, p.Prime) :
    ∃ f₁ f₂ : ℝ → ℝ, ThetaPrimeDeletionConeOn P f₁ ∧ ThetaPrimeDeletionConeOn P f₂ ∧
      (∀ x, f₁ x + f₂ x = thetaCuspFullSource x) ∧
      ¬ ∃ c : ℝ, f₁ = fun x => c * thetaCuspFullSource x := by
  obtain ⟨q, hqP, hq⟩ : ∃ q, q ∉ P ∧ q.Prime := by
    obtain ⟨q, hq1, hq2⟩ := Nat.exists_infinite_primes (P.sup id + 1)
    refine ⟨q, fun hmem => ?_, hq2⟩
    have := Finset.le_sup (f := id) hmem
    simp at this
    omega
  have hq0 := hq.pos
  have hqR : (0 : ℝ) < q := by exact_mod_cast hq0
  set b : ℝ := 1 / (4 * Real.sqrt q)
  have hsq : Real.sqrt q * b = 1 / 4 := by
    simp only [b]
    field_simp [(Real.sqrt_pos.mpr hqR).ne']
  set F : ℝ → ℝ → ℝ := fun β x => (1 / 2) * thetaCuspFullSource x +
    β * thetaCuspFullSource (x + Real.log q)
  have hS := thetaFluxSource_thetaCuspFullSource
  have hsrc : ∀ β, ThetaFluxSource (F β) := fun β =>
    (hS.const_mul _).add ((hS.comp_add _).const_mul β)
  -- flux coefficients `r_β(n) w_n` with `r_β(n) = 1/2 + β √q [q ∣ n]`
  have hmem : ∀ β, 0 ≤ 1 / 2 - |β| * Real.sqrt q → ThetaPrimeDeletionConeOn P (F β) := by
    intro β hβ
    set r : ℕ → ℝ := fun n => 1 / 2 + β * Real.sqrt q * (if q ∣ n then 1 else 0)
    have hr0 : ∀ n, 0 ≤ r n := by
      intro n
      simp only [r]
      split_ifs
      · have := neg_abs_le β
        nlinarith [Real.sqrt_nonneg (q : ℝ)]
      · norm_num
    set v : ℕ → ℝ := fun n => r n * thetaGaussWeight n
    have hv0 : ∀ n, 0 ≤ v n := fun n => mul_nonneg (hr0 n) (thetaGaussWeight_nonneg n)
    have hrep : ∀ t, 0 < t → thetaNormalizedFlux (F β) t =
        ∑' n, v n * Real.exp (-thetaGaussRate n * t) := fun t ht =>
      thetaNormalizedFlux_twoShift hq0 (1 / 2) β ht
    have hr1 : ∀ n, r n ≤ 1 := by
      intro n
      simp only [r]
      split_ifs
      · have := le_abs_self β
        nlinarith [Real.sqrt_nonneg (q : ℝ)]
      · norm_num
    have hvabs : ∀ n, |v n| ≤ thetaGaussWeight n := fun n => by
      rw [abs_of_nonneg (hv0 n)]
      exact mul_le_of_le_one_left (thetaGaussWeight_nonneg n) (hr1 n)
    have hvs : ∀ t, 0 < t → Summable fun n => v n * Real.exp (-thetaGaussRate n * t) :=
      fun t ht => Summable.of_nonneg_of_le (fun n => mul_nonneg (hv0 n) (Real.exp_pos _).le)
        (fun n => mul_le_mul_of_nonneg_right (by simpa [abs_of_nonneg (hv0 n)] using hvabs n)
          (Real.exp_pos _).le) (summable_thetaGaussWeight ht)
    refine ⟨hsrc β, ?_, fun p hp => ?_⟩
    · exact (completelyMonotoneOn_tsum_exp v thetaGaussRate hv0 thetaGaussRate_nonneg hvs).congr_Ioi
        (fun t ht => (hrep t ht).symm)
    · have hpp := hP p hp
      have hpq : p ≠ q := fun h => hqP (h ▸ hp)
      set c : ℕ → ℝ := fun n => v n - (p : ℝ) ^ 2 * (if p ∣ n then v (n / p) else 0)
      have hc : ∀ n, c n = if p ∣ n then 0 else v n := by
        intro n
        by_cases hn : p ∣ n
        · obtain ⟨m, rfl⟩ := hn
          simp only [c, v, r, dvd_mul_right, if_true, Nat.mul_div_cancel_left m hpp.pos,
            thetaGaussWeight_dvd, prime_dvd_mul_iff hpp hq hpq]
          ring
        · simp [c, hn]
      have hc0 : ∀ n, 0 ≤ c n := fun n => by rw [hc]; split_ifs; exacts [le_rfl, hv0 n]
      have hcs : ∀ t, 0 < t → Summable fun n => c n * Real.exp (-thetaGaussRate n * t) :=
        fun t ht => Summable.of_nonneg_of_le (fun n => mul_nonneg (hc0 n) (Real.exp_pos _).le)
          (fun n => by
            rw [hc]
            split_ifs
            · rw [zero_mul]; exact mul_nonneg (hv0 n) (Real.exp_pos _).le
            · exact le_rfl) (hvs t ht)
      exact (completelyMonotoneOn_tsum_exp c thetaGaussRate hc0 thetaGaussRate_nonneg hcs).congr_Ioi
        (fun t ht => (thetaNormalizedFlux_primeDeletion_eq_tsum (hsrc β) hpp.pos hvabs hrep ht).symm)
  have hb : 0 ≤ 1 / 2 - |b| * Real.sqrt q := by
    rw [abs_of_nonneg (by positivity), mul_comm, hsq]; norm_num
  have hb' : 0 ≤ 1 / 2 - |-b| * Real.sqrt q := by rwa [abs_neg]
  refine ⟨F b, F (-b), hmem b hb, hmem (-b) hb', fun x => by simp only [F]; ring, ?_⟩
  rintro ⟨c, hc⟩
  have hshift : ∀ x, b * thetaCuspFullSource (x + Real.log q) =
      (c - 1 / 2) * thetaCuspFullSource x := by
    intro x
    have := congrFun hc x
    simp only [F] at this
    linarith
  have hmom : ∀ w : ℝ, b * Real.exp (-(w * Real.log q)) =
      c - 1 / 2 := by
    intro w
    have h := integral_exp_mul_comp_sub w (-Real.log q) thetaCuspFullSource
    simp only [sub_neg_eq_add] at h
    have hl : (∫ x : ℝ, Real.exp (w * x) * (b * thetaCuspFullSource (x + Real.log q))) =
        b * Real.exp (w * -Real.log q) * ∫ x : ℝ, Real.exp (w * x) * thetaCuspFullSource x := by
      rw [mul_assoc, ← h, ← integral_const_mul]
      congr 1; funext x; ring
    have hr : (∫ x : ℝ, Real.exp (w * x) * (b * thetaCuspFullSource (x + Real.log q))) =
        (c - 1 / 2) * ∫ x : ℝ, Real.exp (w * x) * thetaCuspFullSource x := by
      rw [← integral_const_mul]
      congr 1; funext x; rw [hshift x]; ring
    rw [hl] at hr
    have hI := integral_exp_mul_thetaCuspFullSource_pos w
    rw [show w * -Real.log q = -(w * Real.log q) by ring] at hr
    exact mul_right_cancel₀ hI.ne' hr
  have h0 := hmom 0
  have h1 := hmom 1
  simp only [zero_mul, neg_zero, Real.exp_zero, mul_one, one_mul] at h0 h1
  have hbpos : 0 < b := by positivity
  have hexp : Real.exp (-Real.log q) = 1 := by
    have : b * Real.exp (-Real.log q) = b * 1 := by rw [mul_one, h1, ← h0]
    exact mul_left_cancel₀ hbpos.ne' this
  have hlog : Real.log q = 0 := by
    have := Real.exp_eq_one_iff (-Real.log q) |>.mp hexp
    linarith
  have hq1 : (q : ℝ) = 1 := by
    rcases Real.log_eq_zero.mp hlog with h | h | h
    · exact absurd h (by positivity)
    · exact h
    · linarith
  exact hq.one_lt.ne' (by exact_mod_cast hq1)

end RHTower
