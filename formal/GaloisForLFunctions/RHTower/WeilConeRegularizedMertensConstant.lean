import GaloisForLFunctions.RHTower.WeilOneSidedConvergenceRigidity

/-!
# Every Weil-positive system has a regularized Mertens constant

Let `lam` be full-cone Weil-positive and `d = lam − Λ` on `n ≥ 2`. The harmonic series
`Σ d(n)/n` is summable by an explicit smooth partition of `log n`
(`exists_tendsto_regularizedMertens`): with the cutoffs `χ_K` below, the sums
`Σ_n d(n) χ_K(log n)/n` converge as `K → ∞`. Their limit is the regularized Mertens constant
`T(lam) = "Σ (lam(n) − Λ(n))/n"`. No sign, density or local-mass condition on `lam` is assumed.

**The partition.** Let `s` be the smooth transition (`0` on `(−∞, 0]`, `1` on `[1, ∞)`) and
`β(x) = s(x/δ + 1) − s(x/δ)`, `δ = 1/8` (`stepBump`). Then `β ≥ 0`, `β` is supported in `[−δ, δ]`,
and `Σ_{k ≤ K} β(x − kδ) = s(x/δ + 1) − s(x/δ − K)` telescopes (`sum_range_stepBump`).

**The exact profile identity.** For `g(u) = e^{−u/2} β(u)` the harmonic profile
`ρ_g(x) e^{x/2}` of the window pinning equals `∫ e^{−v} β(v) β(v + x) dv`
(`harmonicProfile_mertensBump_eq`). Hence
`Σ_{k ≤ K} ρ_g(y − kδ) e^{(y − kδ)/2} = ∫ e^{−v} β(v)(s((v+y)/δ + 1) − s((v+y)/δ − K)) dv`,
which equals the constant `c₀ = ∫ e^{−v} β(v) dv > 0` for `δ ≤ y ≤ (K − 1)δ` and lies in `[0, c₀]`
everywhere (`sum_harmonicProfile_mertensBump_eq`, `…_le`). The harmonic windows of the corpus are an
exact partition of unity in `log n`.

**Summability.** Window pinning plus the smoothed prime number theorem
(`exists_abs_windowSum_sub_vonMangoldt_le`) make the windows `Σ_n d(n) ρ_g(log n − kδ) e^{…}/n`
absolutely summable in `k`. Summing the first `K + 1` windows gives `c₀ Σ_n d(n) χ_K(log n)/n`.
-/

open MeasureTheory Set Filter Topology
open scoped Real

namespace RHTower.WeilOneSided

noncomputable section

/-! ## The telescoping step bump -/

/-- `β_δ(x) = s(x/δ + 1) − s(x/δ)` with `s` the smooth transition. -/
def stepBump (δ x : ℝ) : ℝ := Real.smoothTransition (x / δ + 1) - Real.smoothTransition (x / δ)

theorem stepBump_nonneg (δ x : ℝ) : 0 ≤ stepBump δ x :=
  sub_nonneg.mpr (Real.smoothTransition.monotone (by linarith))

theorem stepBump_le_one (δ x : ℝ) : stepBump δ x ≤ 1 := by
  unfold stepBump
  linarith [Real.smoothTransition.le_one (x / δ + 1), Real.smoothTransition.nonneg (x / δ)]

theorem stepBump_eq_zero {δ : ℝ} (hδ : 0 < δ) {x : ℝ} (hx : δ ≤ |x|) : stepBump δ x = 0 := by
  unfold stepBump
  rcases le_or_gt 0 x with h0 | h0
  · rw [abs_of_nonneg h0] at hx
    have h1 : 1 ≤ x / δ := by rw [le_div_iff₀ hδ]; linarith
    rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.one_of_one_le (by linarith),
      sub_self]
  · rw [abs_of_neg h0] at hx
    have h1 : x / δ + 1 ≤ 0 := by
      have : x / δ ≤ -1 := by rw [div_le_iff₀ hδ]; linarith
      linarith
    rw [Real.smoothTransition.zero_of_nonpos h1, Real.smoothTransition.zero_of_nonpos (by linarith),
      sub_self]

theorem stepBump_zero {δ : ℝ} : stepBump δ 0 = 1 := by
  simp [stepBump, Real.smoothTransition.one_of_one_le le_rfl,
    Real.smoothTransition.zero_of_nonpos le_rfl]

theorem contDiff_stepBump (δ : ℝ) : ContDiff ℝ 2 (stepBump δ) := by
  unfold stepBump
  have hs : ContDiff ℝ 2 Real.smoothTransition := Real.smoothTransition.contDiff
  exact (hs.comp ((contDiff_id.div_const δ).add contDiff_const)).sub
    (hs.comp (contDiff_id.div_const δ))

theorem continuous_stepBump (δ : ℝ) : Continuous (stepBump δ) :=
  (contDiff_stepBump δ).continuous

/-- **Telescoping.** `Σ_{k ≤ K} β(x − kδ) = s(x/δ + 1) − s(x/δ − K)`. -/
theorem sum_range_stepBump {δ : ℝ} (hδ : δ ≠ 0) (x : ℝ) (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), stepBump δ (x - k * δ) =
      Real.smoothTransition (x / δ + 1) - Real.smoothTransition (x / δ - K) := by
  set F : ℕ → ℝ := fun k => Real.smoothTransition (x / δ - k + 1) with hF
  have hterm : ∀ k : ℕ, stepBump δ (x - k * δ) = F k - F (k + 1) := by
    intro k
    simp only [stepBump, hF]
    have e : (x - k * δ) / δ = x / δ - k := by field_simp
    rw [e]; push_cast; ring_nf
  rw [Finset.sum_congr rfl fun k _ => hterm k, Finset.sum_range_sub']
  simp only [hF]; push_cast; ring_nf

/-! ## The Mertens bump and its exact profile -/

/-- The step `δ = 1/8`. -/
def mertensStep : ℝ := 1 / 8

theorem mertensStep_pos : 0 < mertensStep := by norm_num [mertensStep]

/-- The bump `g(u) = e^{−u/2} β(u)`. -/
def mertensBump (u : ℝ) : ℝ := Real.exp (-u / 2) * stepBump mertensStep u

theorem contDiff_mertensBump : ContDiff ℝ 2 mertensBump := by
  unfold mertensBump
  exact (Real.contDiff_exp.comp (contDiff_id.neg.div_const 2)).mul (contDiff_stepBump _)

theorem mertensBump_supp : ∀ u, 1 / 4 < |u| → mertensBump u = 0 := by
  intro u hu
  rw [mertensBump, stepBump_eq_zero mertensStep_pos (by rw [mertensStep]; linarith), mul_zero]

theorem hasCompactSupport_mertensBump : HasCompactSupport mertensBump := by
  refine HasCompactSupport.intro (K := Icc (-(1 / 4)) (1 / 4)) isCompact_Icc fun u hu => ?_
  refine mertensBump_supp u ?_
  by_contra h
  exact hu (abs_le.mp (not_lt.mp h))

/-- The weight `e^{−v} β(v)`. -/
def mertensWeight (v : ℝ) : ℝ := Real.exp (-v) * stepBump mertensStep v

theorem mertensWeight_nonneg (v : ℝ) : 0 ≤ mertensWeight v :=
  mul_nonneg (Real.exp_pos _).le (stepBump_nonneg _ _)

theorem continuous_mertensWeight : Continuous mertensWeight :=
  Real.continuous_exp.comp continuous_neg |>.mul (continuous_stepBump _)

theorem hasCompactSupport_mertensWeight : HasCompactSupport mertensWeight := by
  refine HasCompactSupport.intro (K := Icc (-mertensStep) mertensStep) isCompact_Icc fun v hv => ?_
  rw [mertensWeight, stepBump_eq_zero mertensStep_pos ?_, mul_zero]
  by_contra h
  exact hv (abs_le.mp (not_le.mp h).le)

/-- The normalizing constant `c₀ = ∫ e^{−v} β(v) dv`. -/
def mertensMass : ℝ := ∫ v, mertensWeight v

theorem mertensMass_pos : 0 < mertensMass :=
  continuous_mertensWeight.integral_pos_of_hasCompactSupport_nonneg_nonzero
    hasCompactSupport_mertensWeight mertensWeight_nonneg (x := 0)
    (by simp [mertensWeight, stepBump_zero])

/-- **The exact profile.** `ρ_g(x) e^{x/2} = ∫ e^{−v} β(v) β(v + x) dv`. -/
theorem harmonicProfile_mertensBump_eq (x : ℝ) :
    harmonicProfile mertensBump x =
      ∫ v, mertensWeight v * stepBump mertensStep (v + x) := by
  unfold harmonicProfile autoCorr
  have hsh := integral_add_right_eq_self (μ := volume)
    (fun t => mertensBump t * mertensBump (t - x)) x
  simp only [add_sub_cancel_right] at hsh
  rw [← hsh, ← integral_mul_const]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only [mertensBump, mertensWeight]
  have e : Real.exp (-(v + x) / 2) * Real.exp (-v / 2) * Real.exp (x / 2) = Real.exp (-v) := by
    rw [← Real.exp_add, ← Real.exp_add]; ring_nf
  calc Real.exp (-(v + x) / 2) * stepBump mertensStep (v + x) *
        (Real.exp (-v / 2) * stepBump mertensStep v) * Real.exp (x / 2)
      = (Real.exp (-(v + x) / 2) * Real.exp (-v / 2) * Real.exp (x / 2)) *
          stepBump mertensStep v * stepBump mertensStep (v + x) := by ring
    _ = _ := by rw [e]

theorem integrable_mertensWeight_mul (f : ℝ → ℝ) (hf : Continuous f) :
    Integrable fun v => mertensWeight v * f v :=
  (continuous_mertensWeight.mul hf).integrable_of_hasCompactSupport
    hasCompactSupport_mertensWeight.mul_right

/-- The windowed sum of profiles as one integral against the telescoped bump. -/
theorem sum_harmonicProfile_mertensBump (y : ℝ) (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), harmonicProfile mertensBump (y - k * mertensStep) =
      ∫ v, mertensWeight v * (Real.smoothTransition ((v + y) / mertensStep + 1) -
        Real.smoothTransition ((v + y) / mertensStep - K)) := by
  simp_rw [harmonicProfile_mertensBump_eq]
  rw [← integral_finsetSum (Finset.range (K + 1))
    (f := fun (k : ℕ) (v : ℝ) => mertensWeight v * stepBump mertensStep (v + (y - k * mertensStep)))
    (fun k _ => integrable_mertensWeight_mul _
      ((continuous_stepBump _).comp (continuous_id.add continuous_const)))]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  rw [← Finset.mul_sum, ← sum_range_stepBump mertensStep_pos.ne' (v + y) K]
  congr 1
  exact Finset.sum_congr rfl fun k _ => by ring_nf

/-- **Partition of unity.** On `δ ≤ y ≤ (K − 1)δ` the first `K + 1` profiles sum to `c₀`. -/
theorem sum_harmonicProfile_mertensBump_eq {y : ℝ} {K : ℕ} (hy1 : mertensStep ≤ y)
    (hy2 : y ≤ (K - 1) * mertensStep) :
    ∑ k ∈ Finset.range (K + 1), harmonicProfile mertensBump (y - k * mertensStep) = mertensMass := by
  rw [sum_harmonicProfile_mertensBump, mertensMass]
  refine integral_congr_ae (Eventually.of_forall fun v => ?_)
  simp only
  by_cases hv : mertensStep ≤ |v|
  · simp [mertensWeight, stepBump_eq_zero mertensStep_pos hv]
  · push Not at hv
    have hv' := abs_lt.mp hv
    have hδ := mertensStep_pos
    have h1 : 1 ≤ (v + y) / mertensStep + 1 := by
      have : 0 ≤ (v + y) / mertensStep := div_nonneg (by linarith) hδ.le
      linarith
    have h2 : (v + y) / mertensStep - K ≤ 0 := by
      have : (v + y) / mertensStep ≤ K := by
        rw [div_le_iff₀ hδ]; nlinarith
      linarith
    rw [Real.smoothTransition.one_of_one_le h1, Real.smoothTransition.zero_of_nonpos h2, sub_zero,
      mul_one]

/-- The profile sums lie in `[0, c₀]`. -/
theorem sum_harmonicProfile_mertensBump_mem (y : ℝ) (K : ℕ) :
    0 ≤ ∑ k ∈ Finset.range (K + 1), harmonicProfile mertensBump (y - k * mertensStep) ∧
      ∑ k ∈ Finset.range (K + 1), harmonicProfile mertensBump (y - k * mertensStep) ≤
        mertensMass := by
  rw [sum_harmonicProfile_mertensBump, mertensMass]
  have hb : ∀ v, 0 ≤ Real.smoothTransition ((v + y) / mertensStep + 1) -
      Real.smoothTransition ((v + y) / mertensStep - K) := fun v =>
    sub_nonneg.mpr (Real.smoothTransition.monotone (by
      have : (0 : ℝ) ≤ K := Nat.cast_nonneg K
      linarith))
  have hb1 : ∀ v, Real.smoothTransition ((v + y) / mertensStep + 1) -
      Real.smoothTransition ((v + y) / mertensStep - K) ≤ 1 := fun v => by
    linarith [Real.smoothTransition.le_one ((v + y) / mertensStep + 1),
      Real.smoothTransition.nonneg ((v + y) / mertensStep - K)]
  have hcont : Continuous fun v => Real.smoothTransition ((v + y) / mertensStep + 1) -
      Real.smoothTransition ((v + y) / mertensStep - K) := by
    have hs : Continuous Real.smoothTransition := Real.smoothTransition.continuous
    fun_prop
  constructor
  · exact integral_nonneg fun v => mul_nonneg (mertensWeight_nonneg v) (hb v)
  · refine integral_mono (integrable_mertensWeight_mul _ hcont)
      (continuous_mertensWeight.integrable_of_hasCompactSupport hasCompactSupport_mertensWeight)
      fun v => ?_
    simp only
    nlinarith [mertensWeight_nonneg v, hb1 v]

/-! ## The regularized Mertens constant -/

/-- The cutoff `χ_K(y) = c₀⁻¹ Σ_{k ≤ K} ρ_g(y − kδ) e^{(y−kδ)/2}`: it lies in `[0, 1]` and equals
`1` on `[δ, (K − 1)δ]`. -/
def mertensCutoff (K : ℕ) (y : ℝ) : ℝ :=
  (∑ k ∈ Finset.range (K + 1), harmonicProfile mertensBump (y - k * mertensStep)) / mertensMass

theorem mertensCutoff_eq_one {K : ℕ} {y : ℝ} (hy1 : mertensStep ≤ y)
    (hy2 : y ≤ (K - 1) * mertensStep) : mertensCutoff K y = 1 := by
  rw [mertensCutoff, sum_harmonicProfile_mertensBump_eq hy1 hy2, div_self mertensMass_pos.ne']

theorem mertensCutoff_mem (K : ℕ) (y : ℝ) : 0 ≤ mertensCutoff K y ∧ mertensCutoff K y ≤ 1 := by
  obtain ⟨h0, h1⟩ := sum_harmonicProfile_mertensBump_mem y K
  exact ⟨div_nonneg h0 mertensMass_pos.le, (div_le_one mertensMass_pos).mpr h1⟩

/-- The window of `d` at `kδ`: `Σ_{n < e^{kδ+1}} d(n) ρ_g(log n − kδ) e^{…}/n`. -/
def mertensWindow (lam : ℕ → ℝ) (k : ℕ) : ℝ :=
  ∑ n ∈ Finset.range ⌈Real.exp (k * mertensStep + 1)⌉₊,
    coneDeviation lam n * harmonicProfile mertensBump (Real.log n - k * mertensStep) / n

/-- **The windows are absolutely summable** for every full-cone Weil-positive `lam`. -/
theorem summable_abs_mertensWindow {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    Summable fun k : ℕ => |mertensWindow lam k| := by
  have hg := contDiff_mertensBump
  have hgc := hasCompactSupport_mertensBump
  have hsupp := mertensBump_supp
  set η := mertensStep with hηdef
  have hη : 0 < η := mertensStep_pos
  obtain ⟨C, L₀, hC0, hC⟩ := exists_abs_windowSum_sub_vonMangoldt_le hg hgc hsupp
  set b : ℕ → ℝ := fun k => C * Real.exp (k * (-(η / 2))) +
    C * Real.exp (-(Real.sqrt η / 1920000 * Real.sqrt k)) with hb
  have hbs : Summable b :=
    ((Real.summable_exp_nat_mul_iff.mpr (by linarith)).mul_left C).add
      ((GaloisForLFunctions.HTGeometry.summable_exp_neg_mul_sqrt
        (a := Real.sqrt η / 1920000) (by positivity)).mul_left C)
  refine Summable.of_norm_bounded_eventually hbs ?_
  rw [Nat.cofinite_eq_atTop, Filter.eventually_atTop]
  refine ⟨⌈max L₀ 1 / η⌉₊, fun k hk => ?_⟩
  have hkη : max L₀ 1 ≤ k * η := by
    have := Nat.ceil_le.mp hk
    rwa [div_le_iff₀ hη] at this
  have hL1 : 1 ≤ (k : ℝ) * η := (le_max_right _ _).trans hkη
  have hLL : L₀ ≤ (k : ℝ) * η := (le_max_left _ _).trans hkη
  rw [Real.norm_eq_abs, abs_abs]
  have hid := sum_harmonicProfile_eq_windowSum hg hgc hsupp
    (fun n => lam n - ArithmeticFunction.vonMangoldt n) hL1
    (N := ⌈Real.exp (k * η + 1)⌉₊) (Nat.le_ceil _)
  have hcd : ∀ n, coneDeviation lam n * harmonicProfile mertensBump (Real.log n - k * η) / n =
      (if 2 ≤ n then lam n - ArithmeticFunction.vonMangoldt n else 0) *
        harmonicProfile mertensBump (Real.log n - k * η) / n := fun n => rfl
  unfold mertensWindow
  rw [← hηdef]
  simp_rw [hcd]
  rw [hid, abs_mul, abs_of_pos (Real.exp_pos _)]
  have hw := hC lam hW _ hLL
  have hsq : Real.sqrt (k * η) = Real.sqrt k * Real.sqrt η :=
    Real.sqrt_mul (Nat.cast_nonneg k) η
  have e1 : Real.exp (-(k * η / 2)) * Real.exp (k * η / 2) = 1 := by
    rw [← Real.exp_add]; simp
  calc Real.exp (-(k * η / 2)) *
        |windowSum hg hgc hsupp (fun n => lam n - ArithmeticFunction.vonMangoldt n) (k * η)|
      ≤ Real.exp (-(k * η / 2)) *
          (C * (1 + Real.exp (k * η / 2) * Real.exp (-(Real.sqrt (k * η) / 1920000)))) :=
        mul_le_mul_of_nonneg_left hw (Real.exp_pos _).le
    _ = C * Real.exp (-(k * η / 2)) +
          C * (Real.exp (-(k * η / 2)) * Real.exp (k * η / 2)) *
            Real.exp (-(Real.sqrt (k * η) / 1920000)) := by ring
    _ = b k := by
        have a1 : -((k : ℝ) * η / 2) = k * -(η / 2) := by ring
        have a2 : -(Real.sqrt k * Real.sqrt η / 1920000) =
            -(Real.sqrt η / 1920000 * Real.sqrt k) := by ring
        simp only [hb]
        rw [e1, hsq, a1, a2]; ring

/-- The first `K + 1` windows add up to `c₀ Σ_n d(n) χ_K(log n)/n`. -/
theorem sum_range_mertensWindow (lam : ℕ → ℝ) (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), mertensWindow lam k =
      mertensMass * ∑ n ∈ Finset.range ⌈Real.exp (K * mertensStep + 1)⌉₊,
        coneDeviation lam n * mertensCutoff K (Real.log n) / n := by
  set N := ⌈Real.exp (K * mertensStep + 1)⌉₊ with hN
  have hext : ∀ k ∈ Finset.range (K + 1), mertensWindow lam k =
      ∑ n ∈ Finset.range N, coneDeviation lam n *
        harmonicProfile mertensBump (Real.log n - k * mertensStep) / n := by
    intro k hk
    have hkK : k ≤ K := Nat.lt_succ_iff.mp (Finset.mem_range.mp hk)
    unfold mertensWindow
    refine Finset.sum_subset (Finset.range_subset_range.mpr (Nat.ceil_mono (Real.exp_le_exp.mpr
      (by have : (k : ℝ) ≤ K := by exact_mod_cast hkK
          nlinarith [mertensStep_pos])))) fun n hnN hn => ?_
    rw [Finset.mem_range, not_lt] at hn
    have hn1 : Real.exp (k * mertensStep + 1) ≤ n := Nat.ceil_le.mp hn
    have hn0 : (0 : ℝ) < n := lt_of_lt_of_le (Real.exp_pos _) hn1
    have hlog : k * mertensStep + 1 ≤ Real.log n := by
      rw [Real.le_log_iff_exp_le hn0]; exact hn1
    unfold harmonicProfile
    rw [autoCorr_eq_zero mertensBump_supp (by rw [abs_of_pos (by linarith)]; linarith),
      zero_mul, mul_zero, zero_div]
  rw [Finset.sum_congr rfl hext, Finset.sum_comm, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [mertensCutoff, ← Finset.sum_div, ← Finset.mul_sum]
  set S := ∑ k ∈ Finset.range (K + 1),
    harmonicProfile mertensBump (Real.log n - k * mertensStep) with hS
  field_simp [mertensMass_pos.ne']

/-- **Regularized Mertens constant.** For every full-cone Weil-positive `lam` the smoothed harmonic
sums `Σ_n (lam(n) − Λ(n)) χ_K(log n)/n` converge as `K → ∞`. -/
theorem exists_tendsto_regularizedMertens {lam : ℕ → ℝ} (hW : WeilPositiveFull lam) :
    ∃ T : ℝ, Tendsto (fun K : ℕ => ∑ n ∈ Finset.range ⌈Real.exp (K * mertensStep + 1)⌉₊,
      coneDeviation lam n * mertensCutoff K (Real.log n) / n) atTop (𝓝 T) := by
  have hs : Summable (mertensWindow lam) := (summable_abs_mertensWindow hW).of_abs
  refine ⟨(∑' k, mertensWindow lam k) / mertensMass, ?_⟩
  have hlim := (hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)).div_const mertensMass
  refine hlim.congr fun K => ?_
  simp only [Function.comp_apply]
  rw [sum_range_mertensWindow]
  field_simp [mertensMass_pos.ne']

end

end RHTower.WeilOneSided
