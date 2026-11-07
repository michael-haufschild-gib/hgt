import GaloisForLFunctions.PrimeTorusTheory.LargeValueHeightsFormAnApproximateGroup

/-!
# The near-diagonal energy of the orbit

Read the moment of the orbit against a Fejér clock. For `P(t) = Σ a_i e^{itℓ_i}`, `A_u = Π a_{u_s}` and
`λ_u = Σ ℓ_{u_s}` over `k`-tuples, the clocked moment at height `T₀` and width `H` is exactly

`(1/H) ∫ (1 − |t − T₀|/H)₊ |P(t)|^{2k} dt = Σ_{u,v} A_u A_v cos(T₀(λ_u − λ_v)) sinc²(H(λ_u − λ_v)/2)`

(`clockedMoment_eq`). At `T₀ = 0` this is the *near-diagonal energy*, a positive count of pairs of `k`-fold products at
log-distance `≲ 1/H`. At `T₀ ≠ 0` the same pairs carry an oscillating phase: this is the corpus sinc spectrum
(`RHTower.evenMoment_window_kernel`) with a positive window.

* **The energy counts returns** (`card_mul_le_clockedMoment`). Every height at level `θ` in the window contributes
  `w (θS)^{2k}/(2H)`, with `w = θ/(4kΛ)`, `Λ ≥ max |ℓ_i|`. So the number of separated large values is bounded by the
  energy, and a bound for the oscillating energy excludes large values at the height `T₀`
  (`not_mem_largeValue_of_shiftedEnergy_lt`).
* **The start of the orbit is the mixing term** (`energy_ge_start`). The point `t = 0` alone contributes
  `S^{2k}/(8kΛH)`. This is the shape of the term forced by Cauchy–Schwarz past the diagonal range: `M²/(T log M)` for
  `M` products in `T log M` boxes. It is not a statistical term, it is the pole.
* **Absolute values see nothing** (`abs_shiftedEnergy_le_energy`, `energy_ge_start`). Every bound for the oscillating
  energy got by putting absolute values on the pairs is at least `S^{2k}/(8kΛH)`, which is size up to a factor
  `(8kΛH)^{1/2k} → 1`. So no estimate on near-diagonal *counts* proves a saving against size: non-alignment lives in
  the cancellation of the near-diagonal sum.
* **Interpolation** (`clockedMoment_succ_le`). Past the diagonal range the energy is bounded by size: `E_{k+1} ≤ S² E_k`.
-/

open Finset MeasureTheory

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- `|cos x − cos y| ≤ |x − y|`. -/
theorem abs_cos_sub_cos_le (x y : ℝ) : |Real.cos x - Real.cos y| ≤ |x - y| := by
  have h := abs_cos_sub_cos_le_chord x y
  refine h.trans ?_
  unfold chord
  have := Real.abs_sin_le_abs (x := (x - y) / 2)
  rw [abs_div, abs_of_pos (by norm_num : (0 : ℝ) < 2)] at this
  linarith

/-! ### The clock -/

theorem integral_clock_right (T₀ : ℝ) {H ν : ℝ} (hH : 0 < H) (hν : ν ≠ 0) :
    ∫ t in T₀..T₀ + H, (1 - (t - T₀) / H) * Real.cos (t * ν) =
      -(Real.cos ((T₀ + H) * ν) / (H * ν ^ 2)) - Real.sin (T₀ * ν) / ν +
        Real.cos (T₀ * ν) / (H * ν ^ 2) := by
  have hderiv : ∀ t ∈ Set.uIcc T₀ (T₀ + H), HasDerivAt
      (fun t => (1 - (t - T₀) / H) * Real.sin (t * ν) / ν - Real.cos (t * ν) / (H * ν ^ 2))
      ((1 - (t - T₀) / H) * Real.cos (t * ν)) t := by
    intro t _
    have h1 : HasDerivAt (fun t => 1 - (t - T₀) / H) (-(1 / H)) t :=
      (((hasDerivAt_id' t).sub_const T₀).div_const H).const_sub 1
    have h2 : HasDerivAt (fun t : ℝ => t * ν) ν t := by
      simpa using (hasDerivAt_id' t).mul_const ν
    exact (((h1.mul h2.sin).div_const ν).sub (h2.cos.div_const (H * ν ^ 2))).congr_deriv
      (by field_simp; ring)
  have hcont : Continuous fun t : ℝ => (1 - (t - T₀) / H) * Real.cos (t * ν) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  have e : (T₀ + H - T₀) / H = 1 := by field_simp; ring
  simp only [e, sub_self, zero_div, sub_zero, zero_mul]
  ring

theorem integral_clock_left (T₀ : ℝ) {H ν : ℝ} (hH : 0 < H) (hν : ν ≠ 0) :
    ∫ t in T₀ - H..T₀, (1 + (t - T₀) / H) * Real.cos (t * ν) =
      Real.sin (T₀ * ν) / ν + Real.cos (T₀ * ν) / (H * ν ^ 2) -
        Real.cos ((T₀ - H) * ν) / (H * ν ^ 2) := by
  have hderiv : ∀ t ∈ Set.uIcc (T₀ - H) T₀, HasDerivAt
      (fun t => (1 + (t - T₀) / H) * Real.sin (t * ν) / ν + Real.cos (t * ν) / (H * ν ^ 2))
      ((1 + (t - T₀) / H) * Real.cos (t * ν)) t := by
    intro t _
    have h1 : HasDerivAt (fun t => 1 + (t - T₀) / H) (1 / H) t :=
      (((hasDerivAt_id' t).sub_const T₀).div_const H).const_add 1
    have h2 : HasDerivAt (fun t : ℝ => t * ν) ν t := by
      simpa using (hasDerivAt_id' t).mul_const ν
    exact (((h1.mul h2.sin).div_const ν).add (h2.cos.div_const (H * ν ^ 2))).congr_deriv
      (by field_simp; ring)
  have hcont : Continuous fun t : ℝ => (1 + (t - T₀) / H) * Real.cos (t * ν) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hcont.intervalIntegrable _ _)]
  have e : (T₀ - H - T₀) / H = -1 := by field_simp; ring
  simp only [e, sub_self, zero_div, add_zero, one_mul]
  ring

/-- The clock on a window is a difference of two ramps. -/
theorem integral_clock_split (f : ℝ → ℝ) (hf : Continuous f) (T₀ : ℝ) {H : ℝ} (hH : 0 < H) :
    ∫ t in T₀ - H..T₀ + H, (1 - |t - T₀| / H) * f t =
      (∫ t in T₀ - H..T₀, (1 + (t - T₀) / H) * f t) +
        ∫ t in T₀..T₀ + H, (1 - (t - T₀) / H) * f t := by
  have hcont : Continuous fun t : ℝ => (1 - |t - T₀| / H) * f t := by fun_prop
  rw [← intervalIntegral.integral_add_adjacent_intervals (b := T₀)
    (hcont.intervalIntegrable _ _) (hcont.intervalIntegrable _ _)]
  congr 1
  · refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by linarith)] at ht
    rw [abs_of_nonpos (by linarith [ht.2])]
    ring
  · refine intervalIntegral.integral_congr fun t ht => ?_
    rw [Set.uIcc_of_le (by linarith)] at ht
    rw [abs_of_nonneg (by linarith [ht.1])]

/-- **The clock integral.** `∫ (1 − |t − T₀|/H)₊ cos(tν) dt = H cos(T₀ν) sinc²(Hν/2)`. -/
theorem integral_clock_cos (T₀ : ℝ) {H : ℝ} (hH : 0 < H) (ν : ℝ) :
    ∫ t in T₀ - H..T₀ + H, (1 - |t - T₀| / H) * Real.cos (t * ν) =
      H * Real.cos (T₀ * ν) * Real.sinc (H * ν / 2) ^ 2 := by
  rw [integral_clock_split _ (by fun_prop) T₀ hH]
  by_cases hν : ν = 0
  · subst hν
    simp only [mul_zero, Real.cos_zero, mul_one, zero_div, Real.sinc_zero, one_pow]
    have hR : ∀ t ∈ Set.uIcc T₀ (T₀ + H), HasDerivAt (fun t => t - (t - T₀) * (t - T₀) / (2 * H))
        (1 - (t - T₀) / H) t := by
      intro t _
      have h := (((hasDerivAt_id' t).sub_const T₀).mul ((hasDerivAt_id' t).sub_const T₀)).div_const
        (2 * H)
      exact ((hasDerivAt_id' t).sub h).congr_deriv (by field_simp; ring)
    have hL : ∀ t ∈ Set.uIcc (T₀ - H) T₀, HasDerivAt (fun t => t + (t - T₀) * (t - T₀) / (2 * H))
        (1 + (t - T₀) / H) t := by
      intro t _
      have h := (((hasDerivAt_id' t).sub_const T₀).mul ((hasDerivAt_id' t).sub_const T₀)).div_const
        (2 * H)
      exact ((hasDerivAt_id' t).add h).congr_deriv (by field_simp; ring)
    have c1 : Continuous fun t : ℝ => 1 - (t - T₀) / H := by fun_prop
    have c2 : Continuous fun t : ℝ => 1 + (t - T₀) / H := by fun_prop
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hR (c1.intervalIntegrable _ _),
      intervalIntegral.integral_eq_sub_of_hasDerivAt hL (c2.intervalIntegrable _ _)]
    field_simp
    ring
  · rw [integral_clock_left T₀ hH hν, integral_clock_right T₀ hH hν]
    have hx : H * ν / 2 ≠ 0 := by positivity
    rw [Real.sinc_of_ne_zero hx]
    have hcos : Real.cos ((T₀ + H) * ν) + Real.cos ((T₀ - H) * ν) =
        2 * Real.cos (T₀ * ν) * Real.cos (H * ν) := by
      rw [add_mul, sub_mul, Real.cos_add, Real.cos_sub]
      ring
    have hsin : Real.sin (H * ν / 2) ^ 2 = (1 - Real.cos (H * ν)) / 2 := by
      have := Real.cos_two_mul (H * ν / 2)
      rw [show 2 * (H * ν / 2) = H * ν by ring, Real.cos_sq'] at this
      linarith
    have hν' : ν ^ 2 ≠ 0 := pow_ne_zero 2 hν
    have e1 : H * Real.cos (T₀ * ν) * (Real.sin (H * ν / 2) / (H * ν / 2)) ^ 2 =
        Real.cos (T₀ * ν) * (4 * Real.sin (H * ν / 2) ^ 2) / (H * ν ^ 2) := by
      field_simp
      ring
    rw [e1, hsin]
    have e2 : Real.cos ((T₀ - H) * ν) = 2 * Real.cos (T₀ * ν) * Real.cos (H * ν) -
        Real.cos ((T₀ + H) * ν) := by linarith
    rw [e2]
    field_simp
    ring

namespace PhaseSystem

variable {ι : Type*} [Fintype ι] (S : PhaseSystem ι)

/-- The orbit polynomial `P(t) = Σ a_i e^{itℓ_i}`. -/
def poly (t : ℝ) : ℂ :=
  ∑ i, (S.weight i : ℂ) * Complex.exp (((t * S.step i : ℝ) : ℂ) * Complex.I)

theorem continuous_poly : Continuous S.poly := by
  unfold poly
  fun_prop

theorem re_poly (t : ℝ) : (S.poly t).re = S.column t := by
  unfold poly column
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

theorem column_le_norm_poly (t : ℝ) : S.column t ≤ ‖S.poly t‖ := by
  rw [← re_poly]
  exact Complex.re_le_norm _

theorem norm_poly_le (t : ℝ) : ‖S.poly t‖ ≤ S.size := by
  unfold poly size
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (S.weight_nonneg i)]

/-- The weight `A_u = Π a_{u_s}` of a tuple. -/
def tupleWeight {k : ℕ} (u : Fin k → ι) : ℝ := ∏ s, S.weight (u s)

/-- The step `λ_u = Σ ℓ_{u_s}` of a tuple. -/
def tupleStep {k : ℕ} (u : Fin k → ι) : ℝ := ∑ s, S.step (u s)

omit [Fintype ι] in
theorem tupleWeight_nonneg {k : ℕ} (u : Fin k → ι) : 0 ≤ S.tupleWeight u :=
  Finset.prod_nonneg fun s _ => S.weight_nonneg (u s)

/-- The total weight of the `k`-tuples is the `k`-th power of the size. -/
theorem sum_tupleWeight [DecidableEq ι] (k : ℕ) : ∑ u : Fin k → ι, S.tupleWeight u = S.size ^ k := by
  unfold tupleWeight size
  have := Finset.prod_univ_sum (fun _ : Fin k => (Finset.univ : Finset ι))
    (fun _ i => S.weight i)
  rw [Fintype.piFinset_univ] at this
  rw [← this, Finset.prod_const]
  simp

/-- The `k`-th power of the orbit polynomial as a sum over tuples. -/
theorem poly_pow [DecidableEq ι] (k : ℕ) (t : ℝ) :
    S.poly t ^ k = ∑ u : Fin k → ι,
      (S.tupleWeight u : ℂ) * Complex.exp (((t * S.tupleStep u : ℝ) : ℂ) * Complex.I) := by
  have h := Finset.prod_univ_sum (fun _ : Fin k => (Finset.univ : Finset ι))
    (fun _ i => (S.weight i : ℂ) * Complex.exp (((t * S.step i : ℝ) : ℂ) * Complex.I))
  rw [Fintype.piFinset_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  unfold poly
  rw [h]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.prod_mul_distrib, ← Complex.exp_sum]
  unfold tupleWeight tupleStep
  push_cast
  congr 2
  rw [Finset.mul_sum, Finset.sum_mul]

/-- The moment of the orbit polynomial as a cosine sum over pairs of tuples. -/
theorem norm_poly_pow_eq [DecidableEq ι] (k : ℕ) (t : ℝ) :
    ‖S.poly t‖ ^ (2 * k) = ∑ u : Fin k → ι, ∑ v : Fin k → ι,
      S.tupleWeight u * S.tupleWeight v * Real.cos (t * (S.tupleStep u - S.tupleStep v)) := by
  have h1 : ‖S.poly t‖ ^ (2 * k) = (S.poly t ^ k * (starRingEnd ℂ) (S.poly t ^ k)).re := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq, norm_pow, ← pow_mul,
      mul_comm k 2]
  rw [h1, poly_pow, map_sum, Finset.sum_mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [map_mul, Complex.conj_ofReal, ← Complex.exp_conj]
  have e : (S.tupleWeight u : ℂ) * Complex.exp (((t * S.tupleStep u : ℝ) : ℂ) * Complex.I) *
      ((S.tupleWeight v : ℂ) * Complex.exp ((starRingEnd ℂ)
        (((t * S.tupleStep v : ℝ) : ℂ) * Complex.I))) =
      ((S.tupleWeight u * S.tupleWeight v : ℝ) : ℂ) *
        Complex.exp (((t * (S.tupleStep u - S.tupleStep v) : ℝ) : ℂ) * Complex.I) := by
    have hc : (starRingEnd ℂ) (((t * S.tupleStep v : ℝ) : ℂ) * Complex.I) =
        -(((t * S.tupleStep v : ℝ) : ℂ) * Complex.I) := by
      rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
      ring
    rw [hc, mul_mul_mul_comm, ← Complex.exp_add]
    push_cast
    congr 2
    ring
  rw [e, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re]

/-- The moment at height `T₀` and width `H`, read against the Fejér clock. -/
def clockedMoment (k : ℕ) (T₀ H : ℝ) : ℝ :=
  (1 / H) * ∫ t in T₀ - H..T₀ + H, (1 - |t - T₀| / H) * ‖S.poly t‖ ^ (2 * k)

/-- The oscillating near-diagonal sum at height `T₀`. -/
def shiftedEnergy [DecidableEq ι] (k : ℕ) (T₀ H : ℝ) : ℝ :=
  ∑ u : Fin k → ι, ∑ v : Fin k → ι, S.tupleWeight u * S.tupleWeight v *
    Real.cos (T₀ * (S.tupleStep u - S.tupleStep v)) *
      Real.sinc (H * (S.tupleStep u - S.tupleStep v) / 2) ^ 2

/-- The near-diagonal energy: a positive count of pairs of `k`-fold products at log-distance `≲ 1/H`. -/
def energy [DecidableEq ι] (k : ℕ) (H : ℝ) : ℝ :=
  ∑ u : Fin k → ι, ∑ v : Fin k → ι, S.tupleWeight u * S.tupleWeight v *
    Real.sinc (H * (S.tupleStep u - S.tupleStep v) / 2) ^ 2

/-- **Moment = energy.** The clocked moment is exactly the oscillating near-diagonal sum. -/
theorem clockedMoment_eq [DecidableEq ι] (k : ℕ) (T₀ : ℝ) {H : ℝ} (hH : 0 < H) :
    S.clockedMoment k T₀ H = S.shiftedEnergy k T₀ H := by
  unfold clockedMoment shiftedEnergy
  simp_rw [norm_poly_pow_eq, Finset.mul_sum]
  have hterm : ∀ u v : Fin k → ι, Continuous fun t : ℝ => (1 - |t - T₀| / H) *
      (S.tupleWeight u * S.tupleWeight v * Real.cos (t * (S.tupleStep u - S.tupleStep v))) := by
    intro u v
    fun_prop
  have hterm2 : ∀ u : Fin k → ι, Continuous fun t : ℝ => ∑ v : Fin k → ι, (1 - |t - T₀| / H) *
      (S.tupleWeight u * S.tupleWeight v * Real.cos (t * (S.tupleStep u - S.tupleStep v))) :=
    fun u => continuous_finsetSum _ fun v _ => hterm u v
  rw [intervalIntegral.integral_finsetSum fun u _ => (hterm2 u).intervalIntegrable _ _,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [intervalIntegral.integral_finsetSum fun v _ => (hterm u v).intervalIntegrable _ _,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  have e : ∫ t in T₀ - H..T₀ + H, (1 - |t - T₀| / H) *
      (S.tupleWeight u * S.tupleWeight v * Real.cos (t * (S.tupleStep u - S.tupleStep v))) =
      S.tupleWeight u * S.tupleWeight v * ∫ t in T₀ - H..T₀ + H, (1 - |t - T₀| / H) *
        Real.cos (t * (S.tupleStep u - S.tupleStep v)) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  rw [e, integral_clock_cos T₀ hH]
  field_simp

theorem shiftedEnergy_zero [DecidableEq ι] (k : ℕ) (H : ℝ) :
    S.shiftedEnergy k 0 H = S.energy k H := by
  unfold shiftedEnergy energy
  simp

/-- **Absolute values.** The oscillating sum is dominated by the positive count. -/
theorem abs_shiftedEnergy_le_energy [DecidableEq ι] (k : ℕ) (T₀ H : ℝ) :
    |S.shiftedEnergy k T₀ H| ≤ S.energy k H := by
  unfold shiftedEnergy energy
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun u _ => ?_)
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun v _ => ?_)
  have h0 : 0 ≤ S.tupleWeight u * S.tupleWeight v :=
    mul_nonneg (S.tupleWeight_nonneg u) (S.tupleWeight_nonneg v)
  have h1 := Real.abs_cos_le_one (T₀ * (S.tupleStep u - S.tupleStep v))
  have h2 := sq_nonneg (Real.sinc (H * (S.tupleStep u - S.tupleStep v) / 2))
  rw [abs_mul, abs_mul, abs_of_nonneg h0, abs_of_nonneg h2]
  nlinarith [mul_nonneg h0 h2, mul_le_mul_of_nonneg_left h1 (mul_nonneg h0 h2)]

/-- Disjoint windows inside an interval: the integral of a nonnegative function dominates the sum. -/
theorem sum_window_integral_le {f : ℝ → ℝ} (hf : Continuous f) {a b w : ℝ} (hab : a ≤ b)
    (hnn : ∀ t ∈ Set.Icc a b, 0 ≤ f t) (R : Finset ℝ) (hw : 0 ≤ w)
    (hsub : ∀ τ ∈ R, a ≤ τ - w ∧ τ + w ≤ b) (hsep : ∀ τ ∈ R, ∀ σ ∈ R, τ ≠ σ → 2 * w ≤ |τ - σ|) :
    ∑ τ ∈ R, ∫ t in τ - w..τ + w, f t ≤ ∫ t in a..b, f t := by
  have hle : ∀ τ : ℝ, τ - w ≤ τ + w := fun τ => by linarith
  have hset : ∀ τ ∈ R, ∫ t in τ - w..τ + w, f t = ∫ t in Set.Ioc (τ - w) (τ + w), f t :=
    fun τ _ => intervalIntegral.integral_of_le (hle τ)
  rw [Finset.sum_congr rfl hset, intervalIntegral.integral_of_le hab,
    ← MeasureTheory.integral_biUnion_finset R (fun τ _ => measurableSet_Ioc) ?_
      (fun τ _ => (hf.integrableOn_Ioc))]
  · refine MeasureTheory.setIntegral_mono_set hf.integrableOn_Ioc ?_ ?_
    · refine (MeasureTheory.ae_restrict_iff' measurableSet_Ioc).mpr (Filter.Eventually.of_forall ?_)
      intro t ht
      exact hnn t ⟨ht.1.le, ht.2⟩
    · refine LE.le.eventuallyLE fun t ht => ?_
      obtain ⟨τ, hτ, ht⟩ := Set.mem_iUnion₂.mp ht
      exact ⟨lt_of_le_of_lt (hsub τ hτ).1 ht.1, ht.2.trans (hsub τ hτ).2⟩
  · intro τ hτ σ hσ hne
    refine Set.disjoint_left.mpr fun t ht ht' => ?_
    have h := hsep τ (Finset.mem_coe.mp hτ) σ (Finset.mem_coe.mp hσ) hne
    have h1 : |τ - σ| < 2 * w := by
      rw [abs_lt]
      constructor <;> linarith [ht.1, ht.2, ht'.1, ht'.2]
    linarith

variable {S}

/-- The column moves by at most `S|s|Λ` in time `s`. -/
theorem column_add_ge {Λ : ℝ} (hΛ : ∀ i, |S.step i| ≤ Λ) (τ s : ℝ) :
    S.column τ - S.size * (|s| * Λ) ≤ S.column (τ + s) := by
  have h : |S.column τ - S.column (τ + s)| ≤ S.size * (|s| * Λ) := by
    unfold column size
    rw [← Finset.sum_sub_distrib, Finset.sum_mul]
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    rw [← mul_sub, abs_mul, abs_of_nonneg (S.weight_nonneg i)]
    refine mul_le_mul_of_nonneg_left ?_ (S.weight_nonneg i)
    refine (abs_cos_sub_cos_le _ _).trans ?_
    have e : τ * S.step i - (τ + s) * S.step i = -(s * S.step i) := by ring
    rw [e, abs_neg, abs_mul]
    exact mul_le_mul_of_nonneg_left (hΛ i) (abs_nonneg s)
  have := (abs_le.mp h).2
  linarith

/-- Bernoulli's bound for the loss on a window. -/
theorem half_le_pow_window {k : ℕ} (hk : 1 ≤ k) : 1 / 2 ≤ (1 - 1 / (4 * (k : ℝ))) ^ (2 * k) := by
  have hk' : (1 : ℝ) ≤ k := by exact_mod_cast hk
  have h := one_add_mul_le_pow (a := -(1 / (4 * (k : ℝ)))) (n := 2 * k) (by
    have : 1 / (4 * (k : ℝ)) ≤ 1 / 4 := by
      apply div_le_div_of_nonneg_left (by norm_num) (by norm_num) (by linarith)
    linarith)
  have e : (1 + ((2 * k : ℕ) : ℝ) * -(1 / (4 * (k : ℝ)))) = 1 / 2 := by
    push_cast
    field_simp
    ring
  rw [e] at h
  have e2 : 1 + -(1 / (4 * (k : ℝ))) = 1 - 1 / (4 * (k : ℝ)) := by ring
  rwa [e2] at h

/-- **The energy counts large values.** A separated family of heights at level `θ` in the middle of the clock contributes
`|R| w (θS)^{2k}/(2H)`, with `w = θ/(4kΛ)`. -/
theorem card_mul_le_clockedMoment {Λ θ T₀ H : ℝ} {k : ℕ} (hk : 1 ≤ k) (hΛ0 : 0 < Λ)
    (hΛ : ∀ i, |S.step i| ≤ Λ) (hθ0 : 0 < θ) (hH : 0 < H) (R : Finset ℝ)
    (hmid : ∀ τ ∈ R, |τ - T₀| + θ / (4 * k * Λ) ≤ H / 2) (hR : ∀ τ ∈ R, τ ∈ S.largeValue θ)
    (hsep : ∀ τ ∈ R, ∀ σ ∈ R, τ ≠ σ → 2 * (θ / (4 * k * Λ)) ≤ |τ - σ|) :
    (R.card : ℝ) * (θ / (4 * k * Λ)) * (θ * S.size) ^ (2 * k) / (2 * H) ≤
      S.clockedMoment k T₀ H := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  set w := θ / (4 * k * Λ) with hw
  have hw0 : 0 < w := by positivity
  have hS0 := S.size_nonneg
  set f : ℝ → ℝ := fun t => (1 - |t - T₀| / H) * ‖S.poly t‖ ^ (2 * k) with hf
  have hfc : Continuous f := by
    have := S.continuous_poly
    simp only [hf]
    fun_prop
  have hfnn : ∀ t ∈ Set.Icc (T₀ - H) (T₀ + H), 0 ≤ f t := by
    intro t ht
    refine mul_nonneg ?_ (by positivity)
    have : |t - T₀| ≤ H := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    rw [sub_nonneg, div_le_one hH]
    exact this
  -- On each window `f` is at least a quarter of `(θS)^{2k}`.
  have hwindow : ∀ τ ∈ R, ∀ t ∈ Set.Icc (τ - w) (τ + w), (θ * S.size) ^ (2 * k) / 4 ≤ f t := by
    intro τ hτ t ht
    have hs : |t - τ| ≤ w := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
    have hclock : 1 / 2 ≤ 1 - |t - T₀| / H := by
      have h1 : |t - T₀| ≤ |t - τ| + |τ - T₀| := by
        have := abs_sub_le t τ T₀
        linarith
      have h2 := hmid τ hτ
      have h3 : |t - T₀| / H ≤ 1 / 2 := by
        rw [div_le_iff₀ hH]
        linarith
      linarith
    have hcol := column_add_ge hΛ τ (t - τ)
    rw [add_sub_cancel] at hcol
    have hlv : θ * S.size ≤ S.column τ := hR τ hτ
    have hmove : S.size * (|t - τ| * Λ) ≤ θ * S.size * (1 / (4 * k)) := by
      have h4 : |t - τ| * Λ ≤ w * Λ := mul_le_mul_of_nonneg_right hs hΛ0.le
      have h5 : w * Λ = θ * (1 / (4 * k)) := by
        rw [hw]
        field_simp
      rw [h5] at h4
      calc
        S.size * (|t - τ| * Λ) ≤ S.size * (θ * (1 / (4 * k))) :=
          mul_le_mul_of_nonneg_left h4 hS0
        _ = _ := by ring
    have hnorm : θ * S.size * (1 - 1 / (4 * (k : ℝ))) ≤ ‖S.poly t‖ := by
      have := S.column_le_norm_poly t
      nlinarith
    have hbase : 0 ≤ θ * S.size * (1 - 1 / (4 * (k : ℝ))) := by
      have hk1 : (1 : ℝ) ≤ k := by exact_mod_cast hk
      have : 1 / (4 * (k : ℝ)) ≤ 1 := by
        rw [div_le_one (by positivity)]
        linarith
      exact mul_nonneg (by positivity) (by linarith)
    have hpow := pow_le_pow_left₀ hbase hnorm (2 * k)
    rw [mul_pow] at hpow
    have hB := half_le_pow_window hk
    have hTS : 0 ≤ (θ * S.size) ^ (2 * k) := by positivity
    have h6 : (θ * S.size) ^ (2 * k) / 2 ≤ ‖S.poly t‖ ^ (2 * k) := by
      nlinarith
    have h7 : 0 ≤ ‖S.poly t‖ ^ (2 * k) := by positivity
    simp only [hf]
    nlinarith
  -- Each window integrates to at least `w (θS)^{2k}/2`.
  have hint : ∀ τ ∈ R, w * (θ * S.size) ^ (2 * k) / 2 ≤ ∫ t in τ - w..τ + w, f t := by
    intro τ hτ
    have hconst : ∫ _t in τ - w..τ + w, (θ * S.size) ^ (2 * k) / 4 = 2 * w * ((θ * S.size) ^ (2 * k) / 4) := by
      rw [intervalIntegral.integral_const, smul_eq_mul]
      ring
    have hmono : ∫ _t in τ - w..τ + w, (θ * S.size) ^ (2 * k) / 4 ≤ ∫ t in τ - w..τ + w, f t :=
      intervalIntegral.integral_mono_on (by linarith) intervalIntegrable_const
        (hfc.intervalIntegrable _ _) fun t ht => hwindow τ hτ t ht
    rw [hconst] at hmono
    linarith
  have hsub : ∀ τ ∈ R, T₀ - H ≤ τ - w ∧ τ + w ≤ T₀ + H := by
    intro τ hτ
    have h := hmid τ hτ
    have h2 := abs_le.mp (le_trans (le_add_of_nonneg_right hw0.le) h : |τ - T₀| ≤ H / 2)
    constructor <;> linarith [h2.1, h2.2, (show |τ - T₀| + w ≤ H / 2 from h),
      le_abs_self (τ - T₀), neg_abs_le (τ - T₀)]
  have htotal := sum_window_integral_le hfc (a := T₀ - H) (b := T₀ + H) (by linarith) hfnn R hw0.le
    hsub hsep
  have hsum : (R.card : ℝ) * (w * (θ * S.size) ^ (2 * k) / 2) ≤ ∑ τ ∈ R, ∫ t in τ - w..τ + w, f t := by
    have := Finset.card_nsmul_le_sum R (fun τ => ∫ t in τ - w..τ + w, f t) _ hint
    simpa [nsmul_eq_mul] using this
  unfold clockedMoment
  rw [div_le_iff₀ (by positivity)]
  have h8 := hsum.trans htotal
  have e : 1 / H * (∫ t in T₀ - H..T₀ + H, f t) * (2 * H) = 2 * ∫ t in T₀ - H..T₀ + H, f t := by
    field_simp
  simp only [hf] at e h8 ⊢
  rw [e]
  nlinarith

/-- **The start of the orbit is the mixing term.** The point `t = 0` alone contributes `S^{2k}/(8kΛH)` to the energy. -/
theorem energy_ge_start [DecidableEq ι] {Λ H : ℝ} {k : ℕ} (hk : 1 ≤ k) (hΛ0 : 0 < Λ)
    (hΛ : ∀ i, |S.step i| ≤ Λ) (hH : 0 < H) (hHΛ : 1 / (2 * k * Λ) ≤ H) :
    S.size ^ (2 * k) / (8 * k * Λ * H) ≤ S.energy k H := by
  have hk' : (0 : ℝ) < k := by exact_mod_cast hk
  have hmid : ∀ τ ∈ ({0} : Finset ℝ), |τ - 0| + 1 / (4 * k * Λ) ≤ H / 2 := by
    intro τ hτ
    rw [Finset.mem_singleton.mp hτ, sub_zero, abs_zero, zero_add]
    have : 1 / (4 * k * Λ) = 1 / (2 * k * Λ) / 2 := by
      field_simp
      ring
    rw [this]
    linarith
  have hR : ∀ τ ∈ ({0} : Finset ℝ), τ ∈ S.largeValue 1 := by
    intro τ hτ
    rw [Finset.mem_singleton.mp hτ, mem_largeValue, column_zero, one_mul]
  have h := card_mul_le_clockedMoment (S := S) (T₀ := 0) hk hΛ0 hΛ one_pos hH {0} hmid hR
    (by
      intro τ hτ σ hσ hne
      rw [Finset.mem_singleton.mp hτ, Finset.mem_singleton.mp hσ] at hne
      exact absurd rfl hne)
  rw [clockedMoment_eq _ _ _ hH, shiftedEnergy_zero] at h
  refine le_trans (le_of_eq ?_) h
  simp only [Finset.card_singleton, Nat.cast_one, one_mul]
  field_simp
  ring

/-- **A bound on the oscillating sum excludes alignment at that height.** -/
theorem not_mem_largeValue_of_shiftedEnergy_lt [DecidableEq ι] {Λ θ T₀ H τ : ℝ} {k : ℕ}
    (hk : 1 ≤ k) (hΛ0 : 0 < Λ) (hΛ : ∀ i, |S.step i| ≤ Λ) (hθ0 : 0 < θ) (hH : 0 < H)
    (hmid : |τ - T₀| + θ / (4 * k * Λ) ≤ H / 2)
    (hlt : S.shiftedEnergy k T₀ H < θ / (4 * k * Λ) * (θ * S.size) ^ (2 * k) / (2 * H)) :
    τ ∉ S.largeValue θ := by
  intro hτ
  have h := card_mul_le_clockedMoment (S := S) hk hΛ0 hΛ hθ0 hH {τ}
    (fun σ hσ => by rw [Finset.mem_singleton.mp hσ]; exact hmid)
    (fun σ hσ => by rw [Finset.mem_singleton.mp hσ]; exact hτ)
    (by
      intro σ hσ ρ hρ hne
      rw [Finset.mem_singleton.mp hσ, Finset.mem_singleton.mp hρ] at hne
      exact absurd rfl hne)
  rw [clockedMoment_eq _ _ _ hH] at h
  simp only [Finset.card_singleton, Nat.cast_one, one_mul] at h
  linarith

/-- The clock has mass one. -/
theorem integral_clock_one (T₀ : ℝ) {H : ℝ} (hH : 0 < H) :
    ∫ t in T₀ - H..T₀ + H, (1 - |t - T₀| / H) = H := by
  have := integral_clock_cos T₀ hH 0
  simpa using this

/-- **Interpolation.** Past the diagonal range the moment grows at most by the square of the size. -/
theorem clockedMoment_succ_le (k : ℕ) (T₀ : ℝ) {H : ℝ} (hH : 0 < H) :
    S.clockedMoment (k + 1) T₀ H ≤ S.size ^ 2 * S.clockedMoment k T₀ H := by
  unfold clockedMoment
  have hcp := S.continuous_poly
  have hc1 : Continuous fun t : ℝ => (1 - |t - T₀| / H) * ‖S.poly t‖ ^ (2 * (k + 1)) := by fun_prop
  have hc2 : Continuous fun t : ℝ => (1 - |t - T₀| / H) * ‖S.poly t‖ ^ (2 * k) := by fun_prop
  have hint : ∫ t in T₀ - H..T₀ + H, (1 - |t - T₀| / H) * ‖S.poly t‖ ^ (2 * (k + 1)) ≤
      S.size ^ 2 * ∫ t in T₀ - H..T₀ + H, (1 - |t - T₀| / H) * ‖S.poly t‖ ^ (2 * k) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_mono_on (by linarith) (hc1.intervalIntegrable _ _)
      ((continuous_const.mul hc2).intervalIntegrable _ _) fun t ht => ?_
    have hclock : 0 ≤ 1 - |t - T₀| / H := by
      have : |t - T₀| ≤ H := abs_le.mpr ⟨by linarith [ht.1], by linarith [ht.2]⟩
      rw [sub_nonneg, div_le_one hH]
      exact this
    have hp : ‖S.poly t‖ ^ 2 ≤ S.size ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (S.norm_poly_le t) 2
    have e : ‖S.poly t‖ ^ (2 * (k + 1)) = ‖S.poly t‖ ^ 2 * ‖S.poly t‖ ^ (2 * k) := by
      rw [← pow_add]
      congr 1
      ring
    rw [e]
    have h0 : 0 ≤ ‖S.poly t‖ ^ (2 * k) := by positivity
    calc
      (1 - |t - T₀| / H) * (‖S.poly t‖ ^ 2 * ‖S.poly t‖ ^ (2 * k))
          ≤ (1 - |t - T₀| / H) * (S.size ^ 2 * ‖S.poly t‖ ^ (2 * k)) := by gcongr
      _ = S.size ^ 2 * ((1 - |t - T₀| / H) * ‖S.poly t‖ ^ (2 * k)) := by ring
  have hH' : 0 ≤ 1 / H := by positivity
  calc
    1 / H * ∫ t in T₀ - H..T₀ + H, (1 - |t - T₀| / H) * ‖S.poly t‖ ^ (2 * (k + 1))
        ≤ 1 / H * (S.size ^ 2 * ∫ t in T₀ - H..T₀ + H, (1 - |t - T₀| / H) * ‖S.poly t‖ ^ (2 * k)) :=
      mul_le_mul_of_nonneg_left hint hH'
    _ = _ := by ring

end PhaseSystem

end

end GaloisForLFunctions.PrimeTorusTheory
