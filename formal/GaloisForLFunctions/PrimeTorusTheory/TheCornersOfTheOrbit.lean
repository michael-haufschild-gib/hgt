import GaloisForLFunctions.PrimeTorusTheory.TheEnergyOfTheOrbit

/-!
# The corners of the orbit

Translate the orbit by a torus point `z`: `P_z(t) = Σ a_i z_i e^{itℓ_i}`. The Liouville twin is the translate by the corner `z = −1`.
What separates a point from its translates?

* **Long-time means are blind** (`abs_integral_columnAt_le`). The time mean of the column of any translate is `O(1/T)`.
* **Absolute moments are blind to the twin** (`norm_twist_neg_one`, `clockedMoment` depends on `‖P_z‖`). `|P_{−1}| = |P|`, so every
  moment and every near-diagonal energy is the same for a system and its twin. In general
  `energy` dominates the translated moments (`clockedMomentAt_le_energy`): the start of the orbit is an extremal point of the torus
  for the positive count.
* **The start of the orbit sees the sign** (`clockedColumn_eq`, `clockedColumn_nonneg`, `clockedColumn_neg_one`). The Fejér mean of the
  column around `t = 0` is `Σ a_i sinc²(Hℓ_i/2) ≥ 0` at the true orbit and its negative at the twin, at every finite `H`. At
  `T₀ ≠ 0` the same mean is `Σ a_i cos(T₀ℓ_i) sinc²(Hℓ_i/2)`, with no sign. So parity is a statement about a signed functional at the
  start of the orbit: `ω_0 = 1`, the pole.
* **Corners and doubling** (`defect_twist_neg_one`). The defect of the twin is the anti-defect of the system, so
  `defect_two_mul_le_antiDefect` reads: a visit of the orbit near `−1` at time `t` is a visit near `+1` at time `2t`. The twin's large values are
  paid by the true orbit at double height.

A functional that separates ζ from its Liouville twin must be signed, and it must see the start of the orbit.
-/

open Finset

namespace GaloisForLFunctions.PrimeTorusTheory

noncomputable section

/-- The sine companion of `integral_clock_cos`, by a quarter-period shift of the clock. -/
theorem integral_clock_sin (T₀ : ℝ) {H : ℝ} (hH : 0 < H) (ν : ℝ) :
    ∫ t in T₀ - H..T₀ + H, (1 - |t - T₀| / H) * Real.sin (t * ν) =
      H * Real.sin (T₀ * ν) * Real.sinc (H * ν / 2) ^ 2 := by
  by_cases hν : ν = 0
  · subst hν
    simp
  · set d : ℝ := -(Real.pi / (2 * ν)) with hd
    have hdν : d * ν = -(Real.pi / 2) := by
      rw [hd]
      field_simp
    have hs : ∀ x : ℝ, Real.cos ((x + d) * ν) = Real.sin (x * ν) := by
      intro x
      rw [add_mul, hdν, ← sub_eq_add_neg, Real.cos_sub_pi_div_two]
    have hshift := intervalIntegral.integral_comp_add_right
      (a := T₀ - H) (b := T₀ + H)
      (fun x : ℝ => (1 - |x - (T₀ + d)| / H) * Real.cos (x * ν)) d
    have hcongr : ∫ t in T₀ - H..T₀ + H, (1 - |t + d - (T₀ + d)| / H) * Real.cos ((t + d) * ν) =
        ∫ t in T₀ - H..T₀ + H, (1 - |t - T₀| / H) * Real.sin (t * ν) := by
      refine intervalIntegral.integral_congr fun t _ => ?_
      rw [hs, show t + d - (T₀ + d) = t - T₀ by ring]
    rw [← hcongr, hshift]
    have e1 : T₀ - H + d = T₀ + d - H := by ring
    have e2 : T₀ + H + d = T₀ + d + H := by ring
    rw [e1, e2, integral_clock_cos (T₀ + d) hH ν, hs]

namespace PhaseSystem

variable {ι : Type*} [Fintype ι] (S : PhaseSystem ι)

/-- The orbit polynomial translated by a torus point. -/
def polyAt (z : ι → ℂ) (t : ℝ) : ℂ :=
  ∑ i, (S.weight i : ℂ) * (z i * Complex.exp (((t * S.step i : ℝ) : ℂ) * Complex.I))

/-- The column of a translate. -/
def columnAt (z : ι → ℂ) (t : ℝ) : ℝ := (S.polyAt z t).re

theorem polyAt_one (t : ℝ) : S.polyAt (fun _ => 1) t = S.poly t := by
  simp [polyAt, poly]

theorem columnAt_one (t : ℝ) : S.columnAt (fun _ => 1) t = S.column t := by
  rw [columnAt, polyAt_one, re_poly]

/-- The Liouville twin of the column is its negative. -/
theorem columnAt_neg_one (t : ℝ) : S.columnAt (fun _ => -1) t = -S.column t := by
  have h : S.polyAt (fun _ => -1) t = -S.poly t := by
    simp only [polyAt, poly, neg_mul, one_mul, mul_neg, Finset.sum_neg_distrib]
  rw [columnAt, h, Complex.neg_re, re_poly]

/-- `|P_{−1}| = |P|`: absolute moments and energies cannot see the twin. -/
theorem norm_twist_neg_one (t : ℝ) : ‖S.polyAt (fun _ => -1) t‖ = ‖S.poly t‖ := by
  have h : S.polyAt (fun _ => -1) t = -S.poly t := by
    simp only [polyAt, poly, neg_mul, one_mul, mul_neg, Finset.sum_neg_distrib]
  rw [h, norm_neg]

/-- The defect of the twin is the anti-defect of the system. -/
theorem defect_twist_neg_one (t : ℝ) : S.size - S.columnAt (fun _ => -1) t = S.antiDefect t := by
  rw [columnAt_neg_one, antiDefect]
  ring

/-- The value of a translate on the unit circle is bounded by its size. -/
theorem norm_polyAt_le {z : ι → ℂ} (hz : ∀ i, ‖z i‖ = 1) (t : ℝ) : ‖S.polyAt z t‖ ≤ S.size := by
  unfold polyAt size
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
  rw [norm_mul, norm_mul, hz, Complex.norm_exp_ofReal_mul_I, one_mul, mul_one, Complex.norm_real,
    Real.norm_of_nonneg (S.weight_nonneg i)]

/-- The column of a translate in real form. -/
theorem columnAt_eq (z : ι → ℂ) (t : ℝ) :
    S.columnAt z t = ∑ i, S.weight i *
      ((z i).re * Real.cos (t * S.step i) - (z i).im * Real.sin (t * S.step i)) := by
  unfold columnAt polyAt
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Complex.re_ofReal_mul, Complex.mul_re, Complex.exp_ofReal_mul_I_re,
    Complex.exp_ofReal_mul_I_im]

/-- The window integral of `cos(tν)` and `sin(tν)` is `O(1/|ν|)`. -/
theorem abs_integral_cos_le {ν : ℝ} (hν : ν ≠ 0) (a b : ℝ) :
    |∫ t in a..b, Real.cos (t * ν)| ≤ 2 / |ν| := by
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun t => Real.sin (t * ν) / ν) (Real.cos (t * ν)) t := by
    intro t _
    have h2 : HasDerivAt (fun t : ℝ => t * ν) ν t := by
      simpa using (hasDerivAt_id' t).mul_const ν
    exact (h2.sin.div_const ν).congr_deriv (by field_simp)
  have hc : Continuous fun t : ℝ => Real.cos (t * ν) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hc.intervalIntegrable _ _), ← sub_div,
    abs_div, div_le_div_iff_of_pos_right (abs_pos.mpr hν)]
  have h1 := Real.abs_sin_le_one (b * ν)
  have h2 := Real.abs_sin_le_one (a * ν)
  have := abs_sub (Real.sin (b * ν)) (Real.sin (a * ν))
  linarith

theorem abs_integral_sin_le {ν : ℝ} (hν : ν ≠ 0) (a b : ℝ) :
    |∫ t in a..b, Real.sin (t * ν)| ≤ 2 / |ν| := by
  have hderiv : ∀ t ∈ Set.uIcc a b, HasDerivAt (fun t => -(Real.cos (t * ν) / ν)) (Real.sin (t * ν)) t := by
    intro t _
    have h2 : HasDerivAt (fun t : ℝ => t * ν) ν t := by
      simpa using (hasDerivAt_id' t).mul_const ν
    exact ((h2.cos.div_const ν).neg).congr_deriv (by field_simp)
  have hc : Continuous fun t : ℝ => Real.sin (t * ν) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv (hc.intervalIntegrable _ _)]
  have e : -(Real.cos (b * ν) / ν) - -(Real.cos (a * ν) / ν) =
      (Real.cos (a * ν) - Real.cos (b * ν)) / ν := by ring
  rw [e, abs_div, div_le_div_iff_of_pos_right (abs_pos.mpr hν)]
  have h1 := Real.abs_cos_le_one (b * ν)
  have h2 := Real.abs_cos_le_one (a * ν)
  have := abs_sub (Real.cos (a * ν)) (Real.cos (b * ν))
  linarith

/-- **Long-time means are blind.** The time integral of the column of any translate is bounded uniformly in the window. -/
theorem abs_integral_columnAt_le {z : ι → ℂ} (hz : ∀ i, ‖z i‖ = 1) {ℓ₀ : ℝ} (hℓ₀ : 0 < ℓ₀)
    (hstep : ∀ i, ℓ₀ ≤ |S.step i|) (a b : ℝ) :
    |∫ t in a..b, S.columnAt z t| ≤ 4 * S.size / ℓ₀ := by
  have hint : ∫ t in a..b, S.columnAt z t = ∑ i, S.weight i *
      ((z i).re * (∫ t in a..b, Real.cos (t * S.step i)) -
        (z i).im * ∫ t in a..b, Real.sin (t * S.step i)) := by
    simp_rw [columnAt_eq]
    rw [intervalIntegral.integral_finsetSum fun i _ =>
      ((by fun_prop : Continuous fun t : ℝ => S.weight i * ((z i).re * Real.cos (t * S.step i) -
        (z i).im * Real.sin (t * S.step i))).intervalIntegrable _ _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_sub
      ((by fun_prop : Continuous fun t : ℝ => (z i).re * Real.cos (t * S.step i)).intervalIntegrable _ _)
      ((by fun_prop : Continuous fun t : ℝ => (z i).im * Real.sin (t * S.step i)).intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul]
  rw [hint]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hterm : ∀ i ∈ (Finset.univ : Finset ι),
      |S.weight i * ((z i).re * (∫ t in a..b, Real.cos (t * S.step i)) -
        (z i).im * ∫ t in a..b, Real.sin (t * S.step i))| ≤ S.weight i * (4 / ℓ₀) := by
    intro i _
    have hne : S.step i ≠ 0 := by
      intro h0
      have := hstep i
      rw [h0, abs_zero] at this
      linarith
    have hν0 : 0 < |S.step i| := abs_pos.mpr hne
    have hre : |(z i).re| ≤ 1 := by
      have := Complex.abs_re_le_norm (z i)
      rwa [hz i] at this
    have him : |(z i).im| ≤ 1 := by
      have := Complex.abs_im_le_norm (z i)
      rwa [hz i] at this
    have h2 : 2 / |S.step i| ≤ 2 / ℓ₀ := div_le_div_of_nonneg_left (by norm_num) hℓ₀ (hstep i)
    rw [abs_mul, abs_of_nonneg (S.weight_nonneg i)]
    refine mul_le_mul_of_nonneg_left ?_ (S.weight_nonneg i)
    have hc := (abs_integral_cos_le hne a b).trans h2
    have hs := (abs_integral_sin_le hne a b).trans h2
    calc
      |(z i).re * (∫ t in a..b, Real.cos (t * S.step i)) - (z i).im * ∫ t in a..b, Real.sin (t * S.step i)|
          ≤ |(z i).re * (∫ t in a..b, Real.cos (t * S.step i))| +
            |(z i).im * ∫ t in a..b, Real.sin (t * S.step i)| := abs_sub _ _
      _ = |(z i).re| * |∫ t in a..b, Real.cos (t * S.step i)| +
            |(z i).im| * |∫ t in a..b, Real.sin (t * S.step i)| := by
          rw [abs_mul, abs_mul]
      _ ≤ 1 * (2 / ℓ₀) + 1 * (2 / ℓ₀) := by
          gcongr
      _ = 4 / ℓ₀ := by ring
  have := Finset.sum_le_sum hterm
  rw [← Finset.sum_mul] at this
  refine this.trans (le_of_eq ?_)
  unfold size
  ring

/-- The Fejér mean of the column at height `T₀` and width `H`. -/
def clockedColumn (T₀ H : ℝ) : ℝ :=
  (1 / H) * ∫ t in T₀ - H..T₀ + H, (1 - |t - T₀| / H) * S.column t

/-- **The sign at the start.** The Fejér mean of the column is the sum `Σ a_i cos(T₀ℓ_i) sinc²(Hℓ_i/2)`. -/
theorem clockedColumn_eq (T₀ : ℝ) {H : ℝ} (hH : 0 < H) :
    S.clockedColumn T₀ H = ∑ i, S.weight i * Real.cos (T₀ * S.step i) *
      Real.sinc (H * S.step i / 2) ^ 2 := by
  unfold clockedColumn column
  simp_rw [Finset.mul_sum]
  have hc : ∀ i, Continuous fun t : ℝ => (1 - |t - T₀| / H) * (S.weight i * Real.cos (t * S.step i)) := by
    intro i
    fun_prop
  rw [intervalIntegral.integral_finsetSum fun i _ => (hc i).intervalIntegrable _ _, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have e : ∫ t in T₀ - H..T₀ + H, (1 - |t - T₀| / H) * (S.weight i * Real.cos (t * S.step i)) =
      S.weight i * ∫ t in T₀ - H..T₀ + H, (1 - |t - T₀| / H) * Real.cos (t * S.step i) := by
    rw [← intervalIntegral.integral_const_mul]
    refine intervalIntegral.integral_congr fun t _ => ?_
    ring
  rw [e, integral_clock_cos T₀ hH]
  field_simp

/-- At the start of the orbit the Fejér mean is nonnegative, at every width. -/
theorem clockedColumn_nonneg {H : ℝ} (hH : 0 < H) : 0 ≤ S.clockedColumn 0 H := by
  rw [clockedColumn_eq _ _ hH]
  refine Finset.sum_nonneg fun i _ => ?_
  simp only [zero_mul, Real.cos_zero, mul_one]
  exact mul_nonneg (S.weight_nonneg i) (sq_nonneg _)

/-- The Fejér mean of a translate. -/
def clockedColumnAt (z : ι → ℂ) (T₀ H : ℝ) : ℝ :=
  (1 / H) * ∫ t in T₀ - H..T₀ + H, (1 - |t - T₀| / H) * S.columnAt z t

/-- **The twin has the opposite sign at the start.** -/
theorem clockedColumn_neg_one (T₀ H : ℝ) :
    S.clockedColumnAt (fun _ => -1) T₀ H = -S.clockedColumn T₀ H := by
  unfold clockedColumnAt clockedColumn
  simp_rw [columnAt_neg_one, mul_neg]
  rw [intervalIntegral.integral_neg, mul_neg]

/-- The moment of a translate, against the clock. -/
def clockedMomentAt (z : ι → ℂ) (k : ℕ) (T₀ H : ℝ) : ℝ :=
  (1 / H) * ∫ t in T₀ - H..T₀ + H, (1 - |t - T₀| / H) * ‖S.polyAt z t‖ ^ (2 * k)

/-- The `k`-th power of a translated polynomial as a sum over tuples. -/
theorem polyAt_pow [DecidableEq ι] (z : ι → ℂ) (k : ℕ) (t : ℝ) :
    S.polyAt z t ^ k = ∑ u : Fin k → ι, ((S.tupleWeight u : ℂ) * ∏ s, z (u s)) *
      Complex.exp (((t * S.tupleStep u : ℝ) : ℂ) * Complex.I) := by
  have h := Finset.prod_univ_sum (fun _ : Fin k => (Finset.univ : Finset ι))
    (fun _ i => (S.weight i : ℂ) * (z i * Complex.exp (((t * S.step i : ℝ) : ℂ) * Complex.I)))
  rw [Fintype.piFinset_univ, Finset.prod_const, Finset.card_univ, Fintype.card_fin] at h
  unfold polyAt
  rw [h]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, ← Complex.exp_sum]
  unfold tupleWeight tupleStep
  push_cast
  rw [mul_assoc]
  congr 3
  rw [Finset.mul_sum, Finset.sum_mul]

/-- The translated moment as a phase-weighted near-diagonal sum, and its absolute bound. -/
theorem norm_polyAt_pow_eq [DecidableEq ι] (z : ι → ℂ) (k : ℕ) (t : ℝ) :
    ‖S.polyAt z t‖ ^ (2 * k) = ∑ u : Fin k → ι, ∑ v : Fin k → ι,
      (((S.tupleWeight u : ℂ) * ∏ s, z (u s)) *
        (starRingEnd ℂ) ((S.tupleWeight v : ℂ) * ∏ s, z (v s)) *
        Complex.exp (((t * (S.tupleStep u - S.tupleStep v) : ℝ) : ℂ) * Complex.I)).re := by
  have h1 : ‖S.polyAt z t‖ ^ (2 * k) = (S.polyAt z t ^ k * (starRingEnd ℂ) (S.polyAt z t ^ k)).re := by
    rw [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq, norm_pow, ← pow_mul,
      mul_comm k 2]
  rw [h1, polyAt_pow, map_sum, Finset.sum_mul_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun u _ => ?_
  rw [Complex.re_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  congr 1
  rw [map_mul, ← Complex.exp_conj]
  have hc : (starRingEnd ℂ) (((t * S.tupleStep v : ℝ) : ℂ) * Complex.I) =
      -(((t * S.tupleStep v : ℝ) : ℂ) * Complex.I) := by
    rw [map_mul, Complex.conj_ofReal, Complex.conj_I]
    ring
  rw [hc, mul_mul_mul_comm, ← Complex.exp_add]
  push_cast
  congr 2
  ring

/-- **The start of the orbit is extremal.** The clocked moment of every translate at every height is at most the
near-diagonal energy of the system. -/
theorem clockedMomentAt_le_energy [DecidableEq ι] {z : ι → ℂ} (hz : ∀ i, ‖z i‖ = 1) (k : ℕ) (T₀ : ℝ)
    {H : ℝ} (hH : 0 < H) : S.clockedMomentAt z k T₀ H ≤ S.energy k H := by
  have hexp : ∀ t : ℝ, Continuous fun x : ℝ =>
      Complex.exp (((x * t : ℝ) : ℂ) * Complex.I) := fun t => by fun_prop
  unfold clockedMomentAt
  simp_rw [norm_polyAt_pow_eq, Finset.mul_sum]
  have hterm : ∀ u v : Fin k → ι, Continuous fun t : ℝ => (1 - |t - T₀| / H) *
      (((S.tupleWeight u : ℂ) * ∏ s, z (u s)) *
        (starRingEnd ℂ) ((S.tupleWeight v : ℂ) * ∏ s, z (v s)) *
        Complex.exp (((t * (S.tupleStep u - S.tupleStep v) : ℝ) : ℂ) * Complex.I)).re := by
    intro u v
    have := hexp (S.tupleStep u - S.tupleStep v)
    fun_prop
  have hterm2 : ∀ u : Fin k → ι, Continuous fun t : ℝ => ∑ v : Fin k → ι, (1 - |t - T₀| / H) *
      (((S.tupleWeight u : ℂ) * ∏ s, z (u s)) *
        (starRingEnd ℂ) ((S.tupleWeight v : ℂ) * ∏ s, z (v s)) *
        Complex.exp (((t * (S.tupleStep u - S.tupleStep v) : ℝ) : ℂ) * Complex.I)).re :=
    fun u => continuous_finsetSum _ fun v _ => hterm u v
  rw [intervalIntegral.integral_finsetSum fun u _ => (hterm2 u).intervalIntegrable _ _,
    Finset.mul_sum]
  unfold energy
  refine Finset.sum_le_sum fun u _ => ?_
  rw [intervalIntegral.integral_finsetSum fun v _ => (hterm u v).intervalIntegrable _ _,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun v _ => ?_
  -- Each pair: a unimodular coefficient against the clock transform.
  set c : ℂ := ((S.tupleWeight u : ℂ) * ∏ s, z (u s)) *
    (starRingEnd ℂ) ((S.tupleWeight v : ℂ) * ∏ s, z (v s)) with hc
  set ν := S.tupleStep u - S.tupleStep v with hν
  have hcnorm : ‖c‖ = S.tupleWeight u * S.tupleWeight v := by
    have hprod : ∀ w : Fin k → ι, ‖∏ s, z (w s)‖ = 1 := fun w => by
      rw [norm_prod]
      exact Finset.prod_eq_one fun s _ => hz _
    rw [hc, norm_mul, Complex.norm_conj, norm_mul, norm_mul, hprod, hprod, mul_one, mul_one,
      Complex.norm_real, Complex.norm_real, Real.norm_of_nonneg (S.tupleWeight_nonneg u),
      Real.norm_of_nonneg (S.tupleWeight_nonneg v)]
  have hre : ∀ t : ℝ, (c * Complex.exp (((t * ν : ℝ) : ℂ) * Complex.I)).re =
      c.re * Real.cos (t * ν) - c.im * Real.sin (t * ν) := by
    intro t
    rw [Complex.mul_re, Complex.exp_ofReal_mul_I_re, Complex.exp_ofReal_mul_I_im]
  simp_rw [hre]
  have hsplit : ∫ t in T₀ - H..T₀ + H, (1 - |t - T₀| / H) *
      (c.re * Real.cos (t * ν) - c.im * Real.sin (t * ν)) =
      c.re * (H * Real.cos (T₀ * ν) * Real.sinc (H * ν / 2) ^ 2) -
        c.im * (H * Real.sin (T₀ * ν) * Real.sinc (H * ν / 2) ^ 2) := by
    have h1 : Continuous fun t : ℝ => c.re * ((1 - |t - T₀| / H) * Real.cos (t * ν)) := by fun_prop
    have h2 : Continuous fun t : ℝ => c.im * ((1 - |t - T₀| / H) * Real.sin (t * ν)) := by fun_prop
    have e : ∀ t : ℝ, (1 - |t - T₀| / H) * (c.re * Real.cos (t * ν) - c.im * Real.sin (t * ν)) =
        c.re * ((1 - |t - T₀| / H) * Real.cos (t * ν)) -
          c.im * ((1 - |t - T₀| / H) * Real.sin (t * ν)) := fun t => by ring
    simp_rw [e]
    rw [intervalIntegral.integral_sub (h1.intervalIntegrable _ _) (h2.intervalIntegrable _ _),
      intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
      integral_clock_cos T₀ hH, integral_clock_sin T₀ hH]
  rw [hsplit]
  have hval : 1 / H * (c.re * (H * Real.cos (T₀ * ν) * Real.sinc (H * ν / 2) ^ 2) -
      c.im * (H * Real.sin (T₀ * ν) * Real.sinc (H * ν / 2) ^ 2)) =
      (c.re * Real.cos (T₀ * ν) - c.im * Real.sin (T₀ * ν)) * Real.sinc (H * ν / 2) ^ 2 := by
    field_simp
  rw [hval, ← hcnorm]
  refine mul_le_mul_of_nonneg_right ?_ (sq_nonneg _)
  rw [← hre T₀]
  have := Complex.re_le_norm (c * Complex.exp (((T₀ * ν : ℝ) : ℂ) * Complex.I))
  rwa [norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one] at this

end PhaseSystem

end

end GaloisForLFunctions.PrimeTorusTheory
