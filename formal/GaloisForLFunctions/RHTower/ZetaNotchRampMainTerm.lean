import GaloisForLFunctions.RHTower.ZetaNotchRefinedEnvelope
import GaloisForLFunctions.RHTower.WeilAbsoluteConvergenceRigidity

/-!
# The ramp main term of the refined notch

Let `B` be the notch profile, `ω_u(t) = B(t/u)`, `β₀ = ∫ B` and `β₁ = ∫ B(s) log s`.
* `ŵ_u(0) = u β₀` and `∫ ω_u log t = u (β₀ log u + β₁)` (`windowHat_zero_eq`, `logWindow_eq`). So the
  refined main term of a mode `n ≤ u/(4K₀)` is `u (β₀ (log u − log n) + β₁)`.
* **Ramp lower bound** (`exists_rampSum_ge`). Suppose the partial sums `S(k) = Σ_{n≤k} a(n)` are
  bounded below, `S(k) ≥ c ≥ 0` for `k ≥ T`, and `β₀ log 2 + β₁ ≥ 0` (true for the notch profile,
  `notchProfileLogMass_ge`). Then for every cutoff `N ≥ T` and every `u ≥ 1`,
  `Σ_{n≤N, K₀n≤u/4} a(n) (β₀ (log u − log n) + β₁) ≥ β₀ c log u − C`, with `C` independent of `N`
  and `u`. The proof is Abel summation, `Σ_{n≤M} a(n) log(M/n) = Σ_{k<M} S(k) log((k+1)/k)`.
* **The per-scale ramp inequality** (`exists_sum_re_weightedMoment_ge_ramp`):
  `Σ_{n≤N} v(n) Re M_u(log n) ≥ e_P u · rampSum − D Σ_{n≤N} |v(n)| w_u(n)`.
* **Mixture with a ramp main term** (`exists_sum_re_mixMoment_ge_of_ramp`, any continuous bounded
  weight `q`). Per-scale bounds
  `u (k log u − C₀) − D E(u) ≤ Σ_F v Re M_u` integrate to
  `k 2e^{−1} log(L − 1) − C₀ G − D ∫ ρ_L E/u − small ≤ Σ_F v Re M_Ω`.
* **The refined error integral** (`setIntegral_refErrSum_le`). The refined per-mode weights
  integrate, over the scale mixture, to at most `G (S₁ + 2A + B √c (log L + 1) + 133 C_U T/(1 + L))`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Topology RHTower GaloisForLFunctions.HTGeometry

namespace RHTower.WeilAbscissa

open RHTower.ZetaNotch RHTower.SmoothNumbers RHTower.WeilFiniteSupport RHTower.WeilLogSummable

variable {P : Finset ℕ}

/-! ## The scale identities of the notch window -/

/-- `β₀ = ∫ B`, the mass of the notch profile. -/
def notchProfileMass : ℝ := ∫ s, notchProfile s

/-- `β₁ = ∫ B(s) log s`. -/
def notchProfileLogMass : ℝ := ∫ s, notchProfile s * Real.log s

theorem hasCompactSupport_notchProfile : HasCompactSupport notchProfile := by
  refine HasCompactSupport.intro (K := Icc (1 / 2) (5 / 2)) isCompact_Icc fun s hs => ?_
  simp only [mem_Icc, not_and_or, not_le] at hs
  rcases hs with h | h
  · exact notchProfile_eq_zero_of_le h.le
  · exact notchProfile_eq_zero_of_ge h.le

theorem integrable_notchProfile : Integrable notchProfile :=
  continuous_notchProfile.integrable_of_hasCompactSupport hasCompactSupport_notchProfile

theorem integrable_notchProfile_mul_log : Integrable fun s => notchProfile s * Real.log s := by
  have hc : Continuous fun s => notchProfile s * Real.log (max s (1 / 2)) :=
    continuous_notchProfile.mul (Real.continuousOn_log.comp_continuous
      (continuous_id.max continuous_const) fun s => by
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
        exact (lt_of_lt_of_le (by norm_num) (le_max_right s (1 / 2))).ne')
  have hs : HasCompactSupport fun s => notchProfile s * Real.log (max s (1 / 2)) :=
    hasCompactSupport_notchProfile.mul_right (f' := fun s => Real.log (max s (1 / 2)))
  refine (hc.integrable_of_hasCompactSupport hs).congr (Eventually.of_forall fun s => ?_)
  show notchProfile s * Real.log (max s (1 / 2)) = notchProfile s * Real.log s
  rcases le_or_gt s (1 / 2) with h | h
  · rw [notchProfile_eq_zero_of_le h, zero_mul, zero_mul]
  · rw [max_eq_left h.le]

theorem one_le_notchProfileMass : 1 ≤ notchProfileMass := by
  have hpt : ∀ s, (Icc (1 : ℝ) 2).indicator (fun _ => (1 : ℝ)) s ≤ notchProfile s := by
    intro s
    by_cases hs : s ∈ Icc (1 : ℝ) 2
    · rw [indicator_of_mem hs]
      exact le_of_eq (blockWindow_eq_one (by norm_num) hs.1 hs.2).symm
    · rw [indicator_of_notMem hs]; exact notchProfile_nonneg s
  calc (1 : ℝ) = ∫ s, (Icc (1 : ℝ) 2).indicator (fun _ => (1 : ℝ)) s := by
        rw [integral_indicator measurableSet_Icc, setIntegral_const,
          Real.volume_real_Icc_of_le (by norm_num), smul_eq_mul]
        norm_num
    _ ≤ notchProfileMass := integral_mono ((integrableOn_const (by simp)).integrable_indicator
        measurableSet_Icc) integrable_notchProfile hpt

theorem windowHat_zero_eq {u : ℝ} (hu : 0 < u) : windowHat u 0 = ((u * notchProfileMass : ℝ) : ℂ) := by
  rw [windowHat_zero]
  simp_rw [notchWindow_eq_notchProfile hu]
  rw [integral_complex_ofReal, Measure.integral_comp_div (fun s => notchProfile s) u,
    abs_of_pos hu, smul_eq_mul, notchProfileMass]

theorem logWindow_eq {u : ℝ} (hu : 0 < u) :
    logWindow u = ((u * (notchProfileMass * Real.log u + notchProfileLogMass) : ℝ) : ℂ) := by
  have hreal : ∀ t : ℝ, notchProfile (t / u) * Real.log t =
      notchProfile (t / u) * (Real.log u + Real.log (t / u)) := by
    intro t
    rcases le_or_gt (t / u) (1 / 2) with h | h
    · rw [notchProfile_eq_zero_of_le h, zero_mul, zero_mul]
    · have ht : t = u * (t / u) := by field_simp
      rw [← Real.log_mul hu.ne' (by linarith : (0 : ℝ) < t / u).ne', ← ht]
  have hpt : ∀ t : ℝ, notchWindow u t * (Real.log t : ℂ) =
      ((notchProfile (t / u) * (Real.log u + Real.log (t / u)) : ℝ) : ℂ) := by
    intro t
    rw [notchWindow_eq_notchProfile hu, ← Complex.ofReal_mul, hreal t]
  unfold logWindow
  simp_rw [hpt]
  have hcd := Measure.integral_comp_div (fun s => notchProfile s * (Real.log u + Real.log s)) u
  rw [integral_complex_ofReal, hcd, abs_of_pos hu, smul_eq_mul]
  congr 1
  have e : (fun s => notchProfile s * (Real.log u + Real.log s)) =
      fun s => notchProfile s * Real.log u + notchProfile s * Real.log s := by
    funext s; ring
  rw [e, integral_add (integrable_notchProfile.mul_const _) integrable_notchProfile_mul_log,
    integral_mul_const, notchProfileMass, notchProfileLogMass]

/-- The real part of the refined main term:
`Re(∫ω log t − ω̂(0) log n) = u(β₀(log u − log n) + β₁)`. -/
theorem re_logWindow_sub_eq {u : ℝ} (hu : 0 < u) (x : ℝ) :
    (logWindow u - windowHat u 0 * (x : ℂ)).re =
      u * (notchProfileMass * (Real.log u - x) + notchProfileLogMass) := by
  rw [logWindow_eq hu, windowHat_zero_eq hu, Complex.sub_re, Complex.ofReal_re,
    ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

/-- `β₁ ≥ −(log 2) β₀`: the notch profile lives on `[1/2, 5/2]`, where `log s ≥ −log 2`. -/
theorem notchProfileLogMass_ge : -(Real.log 2 * notchProfileMass) ≤ notchProfileLogMass := by
  have hpt : ∀ s, -(Real.log 2 * notchProfile s) ≤ notchProfile s * Real.log s := by
    intro s
    rcases le_or_gt s (1 / 2) with h | h
    · rw [notchProfile_eq_zero_of_le h]; simp
    · have hlog : -Real.log 2 ≤ Real.log s := by
        rw [← Real.log_inv, show (2 : ℝ)⁻¹ = 1 / 2 by norm_num]
        exact Real.log_le_log (by norm_num) h.le
      have := notchProfile_nonneg s
      nlinarith
  unfold notchProfileMass notchProfileLogMass
  rw [← integral_const_mul, ← integral_neg]
  exact integral_mono (integrable_notchProfile.const_mul _).neg integrable_notchProfile_mul_log hpt

theorem notchProfile_log_two_add_nonneg :
    0 ≤ notchProfileMass * Real.log 2 + notchProfileLogMass := by
  have := notchProfileLogMass_ge; linarith

/-! ## Abel summation for the logarithmic ramp -/

section Ramp

variable (a : ℕ → ℝ)

/-- Partial sums `S(k) = Σ_{n≤k} a(n)`. -/
def rampPartial (k : ℕ) : ℝ := ∑ n ∈ Finset.range (k + 1), a n

/-- **Abel summation for the logarithmic ramp.** -/
theorem sum_mul_log_sub_eq (M : ℕ) :
    ∑ n ∈ Finset.range (M + 1), a n * (Real.log M - Real.log n) =
      ∑ k ∈ Finset.range M, rampPartial a k * (Real.log (k + 1 : ℕ) - Real.log k) := by
  induction M with
  | zero => simp
  | succ M ih =>
    have h1 : ∑ n ∈ Finset.range (M + 1 + 1), a n * (Real.log ((M + 1 : ℕ) : ℝ) - Real.log n) =
        ∑ n ∈ Finset.range (M + 1), a n * (Real.log ((M + 1 : ℕ) : ℝ) - Real.log n) := by
      rw [Finset.sum_range_succ, sub_self, mul_zero, add_zero]
    rw [h1, Finset.sum_range_succ (fun k => rampPartial a k * (Real.log (k + 1 : ℕ) - Real.log k)) M,
      ← ih, rampPartial, Finset.sum_mul, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring

theorem telescope_log (m : ℕ) :
    ∑ k ∈ Finset.range m, (Real.log (k + 1 : ℕ) - Real.log k) = Real.log m := by
  have h := Finset.sum_range_sub (fun k : ℕ => Real.log (k : ℝ)) m
  simp only [Nat.cast_zero, Real.log_zero, sub_zero] at h
  rw [← h]

theorem log_step_nonneg (k : ℕ) : 0 ≤ Real.log (k + 1 : ℕ) - Real.log k := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp
  · exact sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast hk) (by push_cast; linarith))

/-- **Lower bound of the logarithmic ramp.** If `S(k) ≥ −B` for all `k` and `S(k) ≥ c` for `k ≥ T`,
then `Σ_{n≤M} a(n) log(M/n) ≥ c (log M − log T) − B log T` for `M ≥ T`. -/
theorem sum_mul_log_sub_ge {c B : ℝ} {T : ℕ} (hB : ∀ k, -B ≤ rampPartial a k)
    (hc : ∀ k, T ≤ k → c ≤ rampPartial a k) {M : ℕ} (hM : T ≤ M) :
    c * (Real.log M - Real.log T) - B * Real.log T ≤
      ∑ n ∈ Finset.range (M + 1), a n * (Real.log M - Real.log n) := by
  rw [sum_mul_log_sub_eq, ← Finset.sum_range_add_sum_Ico _ hM]
  have h1 : -B * Real.log T ≤ ∑ k ∈ Finset.range T,
      rampPartial a k * (Real.log (k + 1 : ℕ) - Real.log k) := by
    rw [← telescope_log T, Finset.mul_sum]
    exact Finset.sum_le_sum fun k _ => mul_le_mul_of_nonneg_right (hB k) (log_step_nonneg k)
  have h2 : c * (Real.log M - Real.log T) ≤ ∑ k ∈ Finset.Ico T M,
      rampPartial a k * (Real.log (k + 1 : ℕ) - Real.log k) := by
    rw [← telescope_log M, ← telescope_log T, ← Finset.sum_Ico_eq_sub _ hM, Finset.mul_sum]
    exact Finset.sum_le_sum fun k hk => mul_le_mul_of_nonneg_right
      (hc k (Finset.mem_Ico.mp hk).1) (log_step_nonneg k)
  linarith

/-- The ramp sum `Σ_{n≤N, K₀n≤u/4} a(n) (β₀ (log u − log n) + β₁)`. -/
def rampSum (N : ℕ) (K₀ β₀ β₁ u : ℝ) : ℝ :=
  ∑ n ∈ Finset.range (N + 1),
    (if K₀ * n ≤ u / 4 then a n else 0) * (β₀ * (Real.log u - Real.log n) + β₁)

theorem rampSum_eq_range {N : ℕ} {K₀ : ℝ} (hK₀ : 0 < K₀) (β₀ β₁ : ℝ) {u : ℝ} (hu : 0 ≤ u) :
    rampSum a N K₀ β₀ β₁ u = ∑ n ∈ Finset.range (min N ⌊u / (4 * K₀)⌋₊ + 1),
      a n * (β₀ * (Real.log u - Real.log n) + β₁) := by
  unfold rampSum
  have hiff : ∀ n : ℕ, K₀ * n ≤ u / 4 ↔ n ≤ ⌊u / (4 * K₀)⌋₊ := by
    intro n
    have h4 : (0 : ℝ) < 4 * K₀ := by positivity
    rw [Nat.le_floor_iff (by positivity)]
    constructor
    · intro h; rw [le_div_iff₀ h4]; linarith
    · intro h; rw [le_div_iff₀ h4] at h; linarith
  simp only [ite_mul, zero_mul]
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun n _ => rfl
  ext n
  simp only [Finset.mem_filter, Finset.mem_range, hiff]
  omega

/-- **The ramp lower bound.** If `|S(k)| ≤ B` for all `k` and `S(k) ≥ c ≥ 0` for `k ≥ T ≥ 1`, then
`rampSum ≥ β₀ c log u − C` for every cutoff `N ≥ T` and every `u ≥ 1`. -/
theorem exists_rampSum_ge (ha0 : a 0 = 0) {c B β₀ β₁ K₀ : ℝ} (hc0 : 0 ≤ c) (hβ₀ : 0 ≤ β₀)
    (hβ : 0 ≤ β₀ * Real.log 2 + β₁) (hK₀ : 1 ≤ K₀) {T : ℕ} (hT : 1 ≤ T)
    (hB : ∀ k, -B ≤ rampPartial a k) (hc : ∀ k, T ≤ k → c ≤ rampPartial a k) :
    ∃ C, ∀ N : ℕ, T ≤ N → ∀ u : ℝ, 1 ≤ u → β₀ * c * Real.log u - C ≤ rampSum a N K₀ β₀ β₁ u := by
  have hB0 : 0 ≤ B := by
    have h := hB 0
    rw [rampPartial, Finset.sum_range_one, ha0] at h
    linarith
  set A : ℝ := ∑ n ∈ Finset.range T, |a n| with hA
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun n _ => abs_nonneg _
  have hT1 : (1 : ℝ) ≤ T := by exact_mod_cast hT
  have hlogT : 0 ≤ Real.log T := Real.log_nonneg hT1
  have hlog4 : 0 ≤ Real.log (4 * K₀ * T) := Real.log_nonneg (by nlinarith)
  refine ⟨β₀ * (c + B) * Real.log T + c * |β₁| + β₀ * c * Real.log (4 * K₀ * T) +
    (β₀ * Real.log (4 * K₀ * T) + |β₁|) * A, fun N hN u hu => ?_⟩
  have hu0 : 0 < u := by linarith
  have hK0 : 0 < K₀ := by linarith
  rw [rampSum_eq_range a hK0 β₀ β₁ hu0.le]
  set U : ℝ := u / (4 * K₀) with hU
  set M : ℕ := min N ⌊U⌋₊ with hM
  have hMU : (M : ℝ) ≤ U := (Nat.cast_le.mpr (min_le_right _ _)).trans (Nat.floor_le (by positivity))
  have hUu : U ≤ u := by rw [hU, div_le_iff₀ (by positivity)]; nlinarith
  have hc1 : 0 ≤ β₀ * (c + B) * Real.log T := by positivity
  have hc2 : 0 ≤ c * |β₁| := by positivity
  have hc3 : 0 ≤ β₀ * c * Real.log (4 * K₀ * T) := by positivity
  have hc4 : 0 ≤ (β₀ * Real.log (4 * K₀ * T) + |β₁|) * A := by positivity
  rcases le_or_gt T M with hTM | hMT
  · -- the ramp regime
    have hM1 : (1 : ℝ) ≤ M := by exact_mod_cast hT.trans hTM
    have hdecomp : ∑ n ∈ Finset.range (M + 1), a n * (β₀ * (Real.log u - Real.log n) + β₁) =
        β₀ * ∑ n ∈ Finset.range (M + 1), a n * (Real.log M - Real.log n) +
          rampPartial a M * (β₀ * (Real.log u - Real.log M) + β₁) := by
      rw [rampPartial, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun n _ => ?_
      ring
    rw [hdecomp]
    have h1 := sum_mul_log_sub_ge a (B := B) hB hc hTM
    -- `u ≥ 4K₀M ≥ 4M`, so the coefficient of `S(M)` is at least `β₀ log 2 + β₁ ≥ 0`
    have hlogM : Real.log 2 ≤ Real.log u - Real.log M := by
      have hM0 : (0 : ℝ) < M := by linarith
      rw [← Real.log_div hu0.ne' hM0.ne']
      refine Real.log_le_log (by norm_num) ?_
      rw [le_div_iff₀ hM0]
      have : 4 * K₀ * (M : ℝ) ≤ u := by
        have := hMU; rw [hU, le_div_iff₀ (by positivity)] at this; linarith
      nlinarith
    have hcoef : 0 ≤ β₀ * (Real.log u - Real.log M) + β₁ := by
      have := mul_le_mul_of_nonneg_left hlogM hβ₀
      linarith
    have h2 : c * (β₀ * (Real.log u - Real.log M) + β₁) ≤
        rampPartial a M * (β₀ * (Real.log u - Real.log M) + β₁) :=
      mul_le_mul_of_nonneg_right (hc M hTM) hcoef
    have h1' := mul_le_mul_of_nonneg_left h1 hβ₀
    have h3 : -(c * |β₁|) ≤ c * β₁ := by
      have := neg_abs_le β₁; nlinarith
    nlinarith
  · -- small scales: the whole sum is bounded
    have hfloor : ⌊U⌋₊ < T := by
      by_contra h
      push Not at h
      have : T ≤ M := le_min hN h
      omega
    have hUT : U < T := (Nat.floor_lt (by positivity)).mp hfloor
    have hu4 : u < 4 * K₀ * T := by
      rw [hU, div_lt_iff₀ (by positivity)] at hUT; linarith
    have hlogu : Real.log u ≤ Real.log (4 * K₀ * T) := Real.log_le_log hu0 hu4.le
    have hlogu0 : 0 ≤ Real.log u := Real.log_nonneg hu
    have hterm : ∀ n ∈ Finset.range (M + 1),
        -(|a n| * (β₀ * Real.log (4 * K₀ * T) + |β₁|)) ≤
          a n * (β₀ * (Real.log u - Real.log n) + β₁) := by
      intro n hn
      rcases Nat.eq_zero_or_pos n with rfl | hn0
      · rw [ha0]; simp
      have hnM : (n : ℝ) ≤ M := by exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hn)
      have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn0
      have hl1 : 0 ≤ Real.log u - Real.log n :=
        sub_nonneg.mpr (Real.log_le_log (by linarith) (hnM.trans (hMU.trans hUu)))
      have hl2 : Real.log u - Real.log n ≤ Real.log (4 * K₀ * T) := by
        have := Real.log_nonneg hn1; linarith
      have hb : |β₀ * (Real.log u - Real.log n) + β₁| ≤ β₀ * Real.log (4 * K₀ * T) + |β₁| := by
        refine (abs_add_le _ _).trans ?_
        rw [abs_mul, abs_of_nonneg hβ₀, abs_of_nonneg hl1]
        have := mul_le_mul_of_nonneg_left hl2 hβ₀
        linarith
      have := abs_mul (a n) (β₀ * (Real.log u - Real.log n) + β₁)
      have h5 : |a n| * |β₀ * (Real.log u - Real.log n) + β₁| ≤
          |a n| * (β₀ * Real.log (4 * K₀ * T) + |β₁|) :=
        mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      linarith [neg_abs_le (a n * (β₀ * (Real.log u - Real.log n) + β₁))]
    have hsum := Finset.sum_le_sum hterm
    have hAM : ∑ n ∈ Finset.range (M + 1), |a n| ≤ A :=
      Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_subset_range.mpr (by omega))
        fun n _ _ => abs_nonneg _
    have hneg : -((β₀ * Real.log (4 * K₀ * T) + |β₁|) * A) ≤
        ∑ n ∈ Finset.range (M + 1), a n * (β₀ * (Real.log u - Real.log n) + β₁) := by
      rw [Finset.sum_neg_distrib, ← Finset.sum_mul] at hsum
      have := mul_le_mul_of_nonneg_left hAM (by positivity :
        (0 : ℝ) ≤ β₀ * Real.log (4 * K₀ * T) + |β₁|)
      nlinarith
    have hmain : β₀ * c * Real.log u ≤ β₀ * c * Real.log (4 * K₀ * T) :=
      mul_le_mul_of_nonneg_left hlogu (by positivity)
    linarith

end Ramp

/-! ## The per-scale ramp inequality -/

/-- The refined scale error `Σ_{n∈F} |v(n)| w_u(n)`. -/
def refErrSum (v : ℕ → ℝ) (F : Finset ℕ) (c : ℝ) (K : ℕ) (u : ℝ) : ℝ :=
  ∑ n ∈ F, |v n| * refWeight c K u n

/-- **The per-scale ramp inequality.** With `a(n) = v(n) mW(n)`, at every scale `u ≥ 16`,
`Σ_{n≤N} v(n) Re M_u(log n) ≥ e_P u · rampSum(a) − D Σ_{n≤N} |v(n)| w_u(n)`. -/
theorem exists_sum_re_weightedMoment_ge_ramp (hP : ∀ p ∈ P, p.Prime) {K : ℕ} (hK : 2 ≤ K)
    (ε : ℝ) {n₀ : ℕ} (hn₀ : IsSmoothOver P n₀) :
    ∃ D, 0 ≤ D ∧ ∀ {v : ℕ → ℝ}, v 0 = 0 → ∀ (N : ℕ) {u : ℝ}, 16 ≤ u →
      (∏ p : P, (1 - primeHalf p ^ 2)) * u *
          rampSum (fun n => v n * mainWeight P ε n₀ n) N (twistBound P n₀) notchProfileMass
            notchProfileLogMass u -
        D * refErrSum v (Finset.range (N + 1)) (2 * (twistBound P n₀ : ℝ) ^ 3) K u ≤
      ∑ n ∈ Finset.range (N + 1), v n *
        (ZetaNotch.weightedMoment u (notchWeight P ε n₀) (Real.log n)).re := by
  obtain ⟨D, hD0, hD⟩ := exists_norm_weightedMoment_sub_logMain_le hP hK ε hn₀
  refine ⟨D, hD0, fun {v} hv0 N {u} hu => ?_⟩
  have hu0 : 0 < u := by linarith
  set eP : ℝ := ∏ p : P, (1 - primeHalf p ^ 2) with heP
  set K₀ : ℝ := (twistBound P n₀ : ℝ) with hK₀
  unfold rampSum refErrSum
  rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_le_sum fun n _ => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [hv0]
  set cn : ℝ := if K₀ * n ≤ u / 4 then mainWeight P ε n₀ n * eP else 0 with hcn
  have h := hD hu hn.ne'
  have hre : |(ZetaNotch.weightedMoment u (notchWeight P ε n₀) (Real.log n)).re -
      cn * (u * (notchProfileMass * (Real.log u - Real.log n) + notchProfileLogMass))| ≤
      D * refWeight (2 * K₀ ^ 3) K u n := by
    rw [← re_logWindow_sub_eq hu0 (Real.log n), ← Complex.re_ofReal_mul, ← Complex.sub_re]
    exact (Complex.abs_re_le_norm _).trans h
  have hmain : eP * u * ((if K₀ * n ≤ u / 4 then v n * mainWeight P ε n₀ n else 0) *
      (notchProfileMass * (Real.log u - Real.log n) + notchProfileLogMass)) =
      v n * (cn * (u * (notchProfileMass * (Real.log u - Real.log n) + notchProfileLogMass))) := by
    rw [hcn]; split_ifs <;> ring
  rw [hmain]
  have h2 := abs_le.mp hre
  have h3 : v n * (cn * (u * (notchProfileMass * (Real.log u - Real.log n) + notchProfileLogMass))) -
      |v n| * (D * refWeight (2 * K₀ ^ 3) K u n) ≤
      v n * (ZetaNotch.weightedMoment u (notchWeight P ε n₀) (Real.log n)).re := by
    rcases le_total 0 (v n) with hv | hv
    · rw [abs_of_nonneg hv]; nlinarith
    · rw [abs_of_nonpos hv]; nlinarith
  linarith

/-! ## The mixture with a ramp main term -/

theorem integrableOn_scaleWeight (L : ℝ) : IntegrableOn (fun u => scaleWeight L u) (Ioi 16) :=
  ((integrable_scaleWeight_mul_quadratic L 1 0 0).congr (Eventually.of_forall fun u => by
    simp)).integrableOn

theorem setIntegral_scaleWeight_le (L : ℝ) : ∫ u in Ioi 16, scaleWeight L u ≤ gaussHalf := by
  calc ∫ u in Ioi 16, scaleWeight L u ≤ ∫ u in Ioi 16, Real.exp (-((u - L) ^ 2 / 2)) :=
        setIntegral_mono_on (integrableOn_scaleWeight L) (integrable_gaussShift L).integrableOn
          measurableSet_Ioi fun u _ => scaleWeight_le_half L u
    _ ≤ ∫ u, Real.exp (-((u - L) ^ 2 / 2)) := setIntegral_le_integral (integrable_gaussShift L)
          (Eventually.of_forall fun _ => (Real.exp_pos _).le)
    _ = gaussHalf := integral_gaussShift L

/-- **The mixed pairing with a ramp main term.** If at every scale `u ≥ 16` the paired notch moments
over `F` are at least `u (k log u − C₀) − D E(u)`, then the paired mixed moments are at least
`k 2e^{−1} log(L − 1) − C₀ G − D ∫_{u>16} ρ_L(u) u^{−1} E(u) du`, minus the small scales and the
negative half-line. -/
theorem exists_sum_re_mixMoment_ge_of_ramp {q : ℝ → ℝ} (hqc : Continuous q) {CQ : ℝ}
    (hqb : ∀ t, |q t| ≤ CQ) :
    ∃ C₁ C₂, 0 ≤ C₁ ∧ 0 ≤ C₂ ∧ ∀ {v : ℕ → ℝ} (F : Finset ℕ) {L : ℝ}, 32 ≤ L →
      ∀ {D k C₀ : ℝ} {E : ℝ → ℝ}, 0 ≤ D → 0 ≤ k → 0 ≤ C₀ →
      (∀ u, 16 ≤ u → u * (k * Real.log u - C₀) - D * E u ≤
        ∑ n ∈ F, v n * (ZetaNotch.weightedMoment u q (Real.log n)).re) →
      IntegrableOn (fun u => scaleWeight L u / u * E u) (Ioi 16) →
      k * (2 * Real.exp (-1) * Real.log (L - 1)) - C₀ * gaussHalf -
        D * (∫ u in Ioi 16, scaleWeight L u / u * E u) -
        (∑ n ∈ F, |v n|) * (C₁ * Real.exp (-(L - 16) ^ 2) + C₂ * Real.exp (-L ^ 2)) ≤
      ∑ n ∈ F, v n * (mixMoment L q (Real.log n)).re := by
  obtain ⟨Cs, hCs0, hCs⟩ := exists_norm_weightedMoment_le_small hqb
  obtain ⟨CN, hCN0, hCN⟩ := exists_norm_mixMomentNeg_le hqb
  refine ⟨16 * Cs, CN, by positivity, hCN0, fun {v} F {L} hL {D k C₀ E} hD0 hk hC₀ hE hEint => ?_⟩
  set TF : ℝ := ∑ n ∈ F, |v n| with hTF
  have hTF0 : 0 ≤ TF := Finset.sum_nonneg fun n _ => abs_nonneg _
  set X : ℝ → ℝ := fun u => ∑ n ∈ F, v n * (ZetaNotch.weightedMoment u q (Real.log n)).re with hX
  have hL0 : 0 ≤ L := by linarith
  have hsplit : ∑ n ∈ F, v n * (mixMoment L q (Real.log n)).re =
      (∫ u in Ioi 0, scaleWeight L u / u * X u) +
        ∑ n ∈ F, v n * (mixMomentNeg L q (Real.log n)).re := by
    rw [← sum_mul_re_integral_scale L hqc hqb v F, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [mixMoment_eq L hqc hqb, Complex.add_re, mul_add]
  have hXint : IntegrableOn (fun u => scaleWeight L u / u * X u) (Ioi 0) := by
    have e : (fun u => scaleWeight L u / u * X u) = fun u => ∑ n ∈ F, v n *
        (((scaleWeight L u / u : ℝ) : ℂ) * ZetaNotch.weightedMoment u q (Real.log n)).re := by
      funext u
      rw [hX, Finset.mul_sum]
      refine Finset.sum_congr rfl fun n _ => ?_
      rw [Complex.re_ofReal_mul]
      ring
    rw [e]
    refine integrable_finsetSum _ fun n _ => ?_
    have h := (integrableOn_scaleMoment L hqc hqb (Real.log n)).re
    simp only [RCLike.re_to_complex] at h
    exact h.const_mul (v n)
  rw [hsplit, ← Ioc_union_Ioi_eq_Ioi (show (0 : ℝ) ≤ 16 by norm_num),
    setIntegral_union Ioc_disjoint_Ioi' measurableSet_Ioi (hXint.mono_set Ioc_subset_Ioi_self)
      (hXint.mono_set (Ioi_subset_Ioi (by norm_num)))]
  have hsmall : |∫ u in Ioc 0 16, scaleWeight L u / u * X u| ≤
      TF * (16 * Cs * Real.exp (-(L - 16) ^ 2)) := by
    have h := norm_setIntegral_le_of_norm_le_const (s := Ioc (0 : ℝ) 16)
      (f := fun u => scaleWeight L u / u * X u) (C := TF * (Cs * Real.exp (-(L - 16) ^ 2)))
      (by rw [Real.volume_Ioc]; exact ENNReal.ofReal_lt_top) fun u hu => ?_
    · rw [Real.volume_real_Ioc_of_le (by norm_num), Real.norm_eq_abs] at h
      calc |∫ u in Ioc 0 16, scaleWeight L u / u * X u| ≤
            TF * (Cs * Real.exp (-(L - 16) ^ 2)) * (16 - 0) := h
        _ = TF * (16 * Cs * Real.exp (-(L - 16) ^ 2)) := by ring
    · have hu0 : 0 < u := hu.1
      have hXb : |X u| ≤ TF * (Cs * u) := by
        rw [hX, hTF, Finset.sum_mul]
        refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
        rw [abs_mul]
        exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans
          (hCs hu0 hu.2 (Real.log n))) (abs_nonneg _)
      have hρ : scaleWeight L u ≤ Real.exp (-(L - 16) ^ 2) := by
        rw [scaleWeight]
        refine Real.exp_le_exp.mpr ?_
        have : (L - 16) ^ 2 ≤ (u - L) ^ 2 := by nlinarith [hu.2]
        linarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (div_pos (scaleWeight_pos L u) hu0).le]
      calc scaleWeight L u / u * |X u| ≤ scaleWeight L u / u * (TF * (Cs * u)) :=
            mul_le_mul_of_nonneg_left hXb (div_pos (scaleWeight_pos L u) hu0).le
        _ = TF * Cs * scaleWeight L u := by field_simp
        _ ≤ TF * Cs * Real.exp (-(L - 16) ^ 2) :=
            mul_le_mul_of_nonneg_left hρ (mul_nonneg hTF0 hCs0)
        _ = TF * (Cs * Real.exp (-(L - 16) ^ 2)) := by ring
  have hneg : |∑ n ∈ F, v n * (mixMomentNeg L q (Real.log n)).re| ≤
      TF * (CN * Real.exp (-L ^ 2)) := by
    rw [hTF, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun n _ => ?_)
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((Complex.abs_re_le_norm _).trans (hCN L hL0 _))
      (abs_nonneg _)
  have hlarge : k * (2 * Real.exp (-1) * Real.log (L - 1)) - C₀ * gaussHalf -
      D * (∫ u in Ioi 16, scaleWeight L u / u * E u) ≤
      ∫ u in Ioi 16, scaleWeight L u / u * X u := by
    have hmain := setIntegral_scaleWeight_mul_log_ge (show (18 : ℝ) ≤ L by linarith)
    have hlogi := integrableOn_scaleWeight_mul_log L
    have hρi := integrableOn_scaleWeight L
    have hpt : ∀ u ∈ Ioi (16 : ℝ), k * (scaleWeight L u * Real.log u) -
        C₀ * scaleWeight L u - D * (scaleWeight L u / u * E u) ≤ scaleWeight L u / u * X u := by
      intro u hu
      have hu16 : (16 : ℝ) < u := hu
      have hu0 : 0 < u := by linarith
      have h1 := hE u hu16.le
      have hw : 0 ≤ scaleWeight L u / u := (div_pos (scaleWeight_pos L u) hu0).le
      calc k * (scaleWeight L u * Real.log u) - C₀ * scaleWeight L u -
            D * (scaleWeight L u / u * E u)
          = scaleWeight L u / u * (u * (k * Real.log u - C₀) - D * E u) := by
            field_simp
        _ ≤ scaleWeight L u / u * X u := mul_le_mul_of_nonneg_left h1 hw
    have hf1 : IntegrableOn (fun u => k * (scaleWeight L u * Real.log u)) (Ioi 16) :=
      hlogi.const_mul k
    have hf2 : IntegrableOn (fun u => C₀ * scaleWeight L u) (Ioi 16) := hρi.const_mul C₀
    have hf3 : IntegrableOn (fun u => D * (scaleWeight L u / u * E u)) (Ioi 16) :=
      hEint.const_mul D
    have hf12 : IntegrableOn (fun u => k * (scaleWeight L u * Real.log u) -
        C₀ * scaleWeight L u) (Ioi 16) := hf1.sub hf2
    have hf123 : IntegrableOn (fun u => k * (scaleWeight L u * Real.log u) -
        C₀ * scaleWeight L u - D * (scaleWeight L u / u * E u)) (Ioi 16) := hf12.sub hf3
    have hint := setIntegral_mono_on hf123 (hXint.mono_set (Ioi_subset_Ioi (by norm_num)))
      measurableSet_Ioi hpt
    have e : ∫ u in Ioi 16, (k * (scaleWeight L u * Real.log u) - C₀ * scaleWeight L u -
        D * (scaleWeight L u / u * E u)) =
        k * (∫ u in Ioi 16, scaleWeight L u * Real.log u) -
          C₀ * (∫ u in Ioi 16, scaleWeight L u) -
          D * (∫ u in Ioi 16, scaleWeight L u / u * E u) := by
      rw [integral_sub hf12 hf3, integral_sub hf1 hf2, integral_const_mul, integral_const_mul,
        integral_const_mul]
    rw [e] at hint
    have h1 := mul_le_mul_of_nonneg_left hmain hk
    have h2 := mul_le_mul_of_nonneg_left (setIntegral_scaleWeight_le L) hC₀
    linarith
  have h1 := abs_le.mp hsmall
  have h2 := abs_le.mp hneg
  nlinarith

/-! ## The refined error integral -/

theorem measurable_refErrSum (v : ℕ → ℝ) (F : Finset ℕ) (c : ℝ) (K : ℕ) :
    Measurable (refErrSum v F c K) := by
  unfold refErrSum refWeight dualTailFactor
  refine Finset.measurable_sum _ fun n _ => ?_
  have hind : Measurable fun u : ℝ => (if (n : ℝ) ≤ c * u then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_le measurable_const (by fun_prop)) measurable_const
      measurable_const
  exact measurable_const.mul ((((by fun_prop : Measurable fun u : ℝ => u * (Real.sqrt n)⁻¹).add
    ((by fun_prop : Measurable fun u : ℝ => Real.sqrt u * Real.log u).mul hind)).add
    (by fun_prop)).add (by fun_prop))

theorem log_div_sqrt_le {u : ℝ} (hu : 1 ≤ u) : Real.log u * (Real.sqrt u)⁻¹ ≤ 2 := by
  have hs : 0 < Real.sqrt u := Real.sqrt_pos.mpr (by linarith)
  have h1 : Real.log u = 2 * Real.log (Real.sqrt u) := by
    rw [Real.log_sqrt (by linarith)]; ring
  have h2 : Real.log (Real.sqrt u) ≤ Real.sqrt u - 1 := Real.log_le_sub_one_of_pos hs
  rw [h1, ← div_eq_mul_inv, div_le_iff₀ hs]
  linarith

/-- `ρ_L(u) log u ≤ (log L + 1) e^{−(u−L)²/2}` for `u, L ≥ 1`. -/
theorem scaleWeight_mul_log_le {L u : ℝ} (hL : 1 ≤ L) (hu : 1 ≤ u) :
    scaleWeight L u * Real.log u ≤ (Real.log L + 1) * Real.exp (-((u - L) ^ 2 / 2)) := by
  have hL0 : 0 < L := by linarith
  have hu0 : 0 < u := by linarith
  set w := u - L with hw
  have hlog : Real.log u ≤ Real.log L + |w| := by
    have h := Real.log_le_sub_one_of_pos (div_pos hu0 hL0)
    rw [Real.log_div hu0.ne' hL0.ne'] at h
    have h2 : u / L - 1 ≤ |w| := by
      rw [div_sub_one hL0.ne', div_le_iff₀ hL0]
      nlinarith [le_abs_self w, abs_nonneg w]
    linarith
  have hρ : scaleWeight L u = Real.exp (-w ^ 2) := by rw [scaleWeight, hw]
  have hw1 : |w| ≤ Real.exp (w ^ 2 / 2) := by
    have := Real.add_one_le_exp (w ^ 2 / 2)
    nlinarith [sq_abs w, sq_nonneg (|w| - 1)]
  have hG : Real.exp (-w ^ 2) * |w| ≤ Real.exp (-(w ^ 2 / 2)) := by
    calc Real.exp (-w ^ 2) * |w| ≤ Real.exp (-w ^ 2) * Real.exp (w ^ 2 / 2) :=
          mul_le_mul_of_nonneg_left hw1 (Real.exp_pos _).le
      _ = Real.exp (-(w ^ 2 / 2)) := by rw [← Real.exp_add]; ring_nf
  have hρG : Real.exp (-w ^ 2) ≤ Real.exp (-(w ^ 2 / 2)) :=
    Real.exp_le_exp.mpr (by nlinarith [sq_nonneg w])
  have hlogL := Real.log_nonneg hL
  have hlogu := Real.log_nonneg hu
  rw [hρ]
  calc Real.exp (-w ^ 2) * Real.log u ≤ Real.exp (-w ^ 2) * (Real.log L + |w|) :=
        mul_le_mul_of_nonneg_left hlog (Real.exp_pos _).le
    _ = Real.exp (-w ^ 2) * Real.log L + Real.exp (-w ^ 2) * |w| := by ring
    _ ≤ Real.exp (-(w ^ 2 / 2)) * Real.log L + Real.exp (-(w ^ 2 / 2)) := by
        gcongr
    _ = (Real.log L + 1) * Real.exp (-(w ^ 2 / 2)) := by ring

/-- **Pointwise Gaussian envelope of the refined scale error** on `u > 16`. -/
theorem scaleWeight_div_mul_refErrSum_le {L : ℝ} (hL : 32 ≤ L) {v : ℕ → ℝ} {F : Finset ℕ}
    {c : ℝ} (hc : 0 < c) {K : ℕ} {S₁ A B T CU : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hCU : 0 ≤ CU)
    (hS₁ : ∑ n ∈ F, |v n| * (Real.sqrt n)⁻¹ ≤ S₁)
    (hAB : ∀ x : ℝ, 0 ≤ x → ∑ n ∈ F, |v n| * (if (n : ℝ) ≤ x then 1 else 0) ≤ A + B * Real.sqrt x)
    (hT : ∑ n ∈ F, |v n| ≤ T)
    (hU : ∀ u : ℝ, 16 ≤ u → u ^ (5 / 2 : ℝ) * dualTailFactor u K +
      u ^ 2 * Real.exp (-(u ^ 2) / 32) ≤ CU * (u * (u ^ (4 + 1))⁻¹))
    {u : ℝ} (hu : 16 < u) :
    scaleWeight L u / u * refErrSum v F c K u ≤
      (S₁ + 2 * A + B * Real.sqrt c * (Real.log L + 1) + 133 * CU * (T / (1 + L))) *
        Real.exp (-((u - L) ^ 2 / 2)) := by
  have hu0 : 0 < u := by linarith
  have hu1 : 1 ≤ u := by linarith
  have hL1 : 1 ≤ L := by linarith
  set G := Real.exp (-((u - L) ^ 2 / 2)) with hG
  have hG0 : 0 < G := Real.exp_pos _
  have hρ0 := scaleWeight_pos L u
  have hρ : scaleWeight L u ≤ G := scaleWeight_le_half L u
  set W₁ := ∑ n ∈ F, |v n| * (Real.sqrt n)⁻¹ with hW₁
  set W₂ := ∑ n ∈ F, |v n| * (if (n : ℝ) ≤ c * u then 1 else 0) with hW₂
  set W₃ := ∑ n ∈ F, |v n| with hW₃
  set Uu := u ^ (5 / 2 : ℝ) * dualTailFactor u K + u ^ 2 * Real.exp (-(u ^ 2) / 32) with hUu
  have hsum : refErrSum v F c K u = u * W₁ + Real.sqrt u * Real.log u * W₂ + Uu * W₃ := by
    unfold refErrSum refWeight
    rw [hW₁, hW₂, hW₃, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [hUu]; ring
  have hW₂b : W₂ ≤ A + B * (Real.sqrt c * Real.sqrt u) := by
    rw [← Real.sqrt_mul hc.le]; exact hAB (c * u) (by positivity)
  have hW₂0 : 0 ≤ W₂ := Finset.sum_nonneg fun n _ => by
    have : (0 : ℝ) ≤ (if (n : ℝ) ≤ c * u then 1 else 0) := by split_ifs <;> norm_num
    positivity
  have hW₃0 : 0 ≤ W₃ := Finset.sum_nonneg fun n _ => abs_nonneg _
  have hsq : 0 < Real.sqrt u := Real.sqrt_pos.mpr hu0
  have hlogu := Real.log_nonneg hu1
  -- the three pieces
  have hP1 : scaleWeight L u / u * (u * W₁) ≤ S₁ * G := by
    have hW₁0 : 0 ≤ W₁ := Finset.sum_nonneg fun n _ => by positivity
    rw [show scaleWeight L u / u * (u * W₁) = scaleWeight L u * W₁ by field_simp]
    calc scaleWeight L u * W₁ ≤ G * S₁ := mul_le_mul hρ hS₁ hW₁0 hG0.le
      _ = S₁ * G := by ring
  have hP2 : scaleWeight L u / u * (Real.sqrt u * Real.log u * W₂) ≤
      (2 * A + B * Real.sqrt c * (Real.log L + 1)) * G := by
    have e : scaleWeight L u / u * (Real.sqrt u * Real.log u * W₂) =
        scaleWeight L u * (Real.log u * (Real.sqrt u)⁻¹) * W₂ := by
      have hinv : Real.sqrt u / u = (Real.sqrt u)⁻¹ := Real.sqrt_div_self
      calc scaleWeight L u / u * (Real.sqrt u * Real.log u * W₂)
          = scaleWeight L u * (Real.sqrt u / u) * Real.log u * W₂ := by ring
        _ = _ := by rw [hinv]; ring
    rw [e]
    have hld := log_div_sqrt_le hu1
    have hld0 : 0 ≤ Real.log u * (Real.sqrt u)⁻¹ := by positivity
    have h1 : scaleWeight L u * (Real.log u * (Real.sqrt u)⁻¹) * W₂ ≤
        scaleWeight L u * (Real.log u * (Real.sqrt u)⁻¹) * (A + B * (Real.sqrt c * Real.sqrt u)) :=
      mul_le_mul_of_nonneg_left hW₂b (by positivity)
    have e2 : scaleWeight L u * (Real.log u * (Real.sqrt u)⁻¹) *
        (A + B * (Real.sqrt c * Real.sqrt u)) =
        A * (scaleWeight L u * (Real.log u * (Real.sqrt u)⁻¹)) +
          B * Real.sqrt c * (scaleWeight L u * Real.log u) := by
      field_simp
    have h3 : scaleWeight L u * (Real.log u * (Real.sqrt u)⁻¹) ≤ G * 2 :=
      mul_le_mul hρ hld hld0 hG0.le
    have h4 := scaleWeight_mul_log_le hL1 hu1
    have h5 : B * Real.sqrt c * (scaleWeight L u * Real.log u) ≤
        B * Real.sqrt c * ((Real.log L + 1) * G) :=
      mul_le_mul_of_nonneg_left h4 (by positivity)
    have h6 := mul_le_mul_of_nonneg_left h3 hA
    nlinarith
  have hP3 : scaleWeight L u / u * (Uu * W₃) ≤ 133 * CU * (T / (1 + L)) * G := by
    have hpoly := scaleWeight_mul_inv_pow_le (show (2 : ℝ) ≤ L by linarith) 4 hu
    obtain ⟨hsm, -⟩ := inv_one_add_bounds hL
    have hUb : scaleWeight L u / u * Uu ≤ CU * (133 / (1 + L)) * G := by
      calc scaleWeight L u / u * Uu ≤ scaleWeight L u / u * (CU * (u * (u ^ (4 + 1))⁻¹)) :=
            mul_le_mul_of_nonneg_left (hU u hu.le) (div_pos hρ0 hu0).le
        _ = CU * (scaleWeight L u * (u ^ (4 + 1))⁻¹) := by field_simp
        _ ≤ CU * ((((L / 2) ^ (4 + 1))⁻¹ + Real.exp (-(L ^ 2 / 8))) * G) :=
            mul_le_mul_of_nonneg_left hpoly hCU
        _ ≤ CU * (133 / (1 + L) * G) := by
            refine mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right ?_ hG0.le) hCU
            have := Real.exp_pos (-(L ^ 2 / 256))
            linarith
        _ = CU * (133 / (1 + L)) * G := by ring
    have hT0 : 0 ≤ T := hW₃0.trans hT
    calc scaleWeight L u / u * (Uu * W₃) = (scaleWeight L u / u * Uu) * W₃ := by ring
      _ ≤ (CU * (133 / (1 + L)) * G) * T :=
          mul_le_mul hUb hT hW₃0 (by positivity)
      _ = 133 * CU * (T / (1 + L)) * G := by ring
  rw [hsum, mul_add, mul_add]
  nlinarith

/-- **The refined error integral.** Under the hypotheses of the pointwise envelope,
`∫_{u>16} ρ_L(u) u^{−1} Σ_F |v(n)| w_u(n) du ≤ G (S₁ + 2A + B √c (log L + 1) + 133 C_U T/(1 + L))`. -/
theorem setIntegral_refErrSum_le {L : ℝ} (hL : 32 ≤ L) {v : ℕ → ℝ} {F : Finset ℕ}
    {c : ℝ} (hc : 0 < c) {K : ℕ} {S₁ A B T CU : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) (hCU : 0 ≤ CU)
    (hS₁ : ∑ n ∈ F, |v n| * (Real.sqrt n)⁻¹ ≤ S₁)
    (hAB : ∀ x : ℝ, 0 ≤ x → ∑ n ∈ F, |v n| * (if (n : ℝ) ≤ x then 1 else 0) ≤ A + B * Real.sqrt x)
    (hT : ∑ n ∈ F, |v n| ≤ T)
    (hU : ∀ u : ℝ, 16 ≤ u → u ^ (5 / 2 : ℝ) * dualTailFactor u K +
      u ^ 2 * Real.exp (-(u ^ 2) / 32) ≤ CU * (u * (u ^ (4 + 1))⁻¹)) :
    IntegrableOn (fun u => scaleWeight L u / u * refErrSum v F c K u) (Ioi 16) ∧
      ∫ u in Ioi 16, scaleWeight L u / u * refErrSum v F c K u ≤
        (S₁ + 2 * A + B * Real.sqrt c * (Real.log L + 1) + 133 * CU * (T / (1 + L))) *
          gaussHalf := by
  set E := S₁ + 2 * A + B * Real.sqrt c * (Real.log L + 1) + 133 * CU * (T / (1 + L)) with hE
  have hnn : ∀ u : ℝ, 16 < u → 0 ≤ scaleWeight L u / u * refErrSum v F c K u := by
    intro u hu
    refine mul_nonneg (div_pos (scaleWeight_pos L u) (by linarith)).le
      (Finset.sum_nonneg fun n _ => mul_nonneg (abs_nonneg _)
        (refWeight_nonneg c K (by linarith) n))
  have hpt := fun u (hu : u ∈ Ioi (16 : ℝ)) =>
    scaleWeight_div_mul_refErrSum_le hL hc hA hB hCU hS₁ hAB hT hU (u := u) hu
  have hint : IntegrableOn (fun u => scaleWeight L u / u * refErrSum v F c K u) (Ioi 16) := by
    refine ((integrable_gaussShift L).const_mul E).integrableOn.mono' ?_ ?_
    · exact (((Real.continuous_exp.comp (by fun_prop)).measurable.div measurable_id).mul
        (measurable_refErrSum v F c K)).aestronglyMeasurable
    · rw [ae_restrict_iff' measurableSet_Ioi]
      refine Eventually.of_forall fun u hu => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (hnn u hu)]
      exact hpt u hu
  refine ⟨hint, ?_⟩
  have hE0 : 0 ≤ E := by
    have h1 : 0 ≤ ∑ n ∈ F, |v n| * (Real.sqrt n)⁻¹ := Finset.sum_nonneg fun n _ => by positivity
    have h2 : 0 ≤ ∑ n ∈ F, |v n| := Finset.sum_nonneg fun n _ => abs_nonneg _
    have hlogL := Real.log_nonneg (show (1 : ℝ) ≤ L by linarith)
    have hL1 : 0 < 1 + L := by linarith
    have : 0 ≤ T / (1 + L) := div_nonneg (h2.trans hT) hL1.le
    rw [hE]
    have : 0 ≤ S₁ := h1.trans hS₁
    positivity
  calc ∫ u in Ioi 16, scaleWeight L u / u * refErrSum v F c K u
      ≤ ∫ u in Ioi 16, E * Real.exp (-((u - L) ^ 2 / 2)) :=
        setIntegral_mono_on hint ((integrable_gaussShift L).const_mul E).integrableOn
          measurableSet_Ioi hpt
    _ = E * ∫ u in Ioi 16, Real.exp (-((u - L) ^ 2 / 2)) := integral_const_mul _ _
    _ ≤ E * gaussHalf := by
        refine mul_le_mul_of_nonneg_left ?_ hE0
        rw [← integral_gaussShift L]
        exact setIntegral_le_integral (integrable_gaussShift L)
          (Eventually.of_forall fun _ => (Real.exp_pos _).le)
    _ = _ := by rw [hE]

end RHTower.WeilAbscissa
