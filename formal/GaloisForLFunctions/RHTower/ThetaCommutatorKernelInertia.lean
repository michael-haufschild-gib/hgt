import GaloisForLFunctions.RHTower.ThetaQuadratureDefectSpectralKernel
import GaloisForLFunctions.RHTower.HardyTheorem
import GaloisForLFunctions.PNTPlus.Consequences

/-!
# Infinite positive and negative inertia of the commutator kernel at prime scales

The kernel `K(a, b) = 4 sinh(a/4) sinh(b/4) + B(a - b) - B(a + b)` of the prime-deletion /
modular-inversion commutator is pointwise positive on `(0, ∞)²`, yet its Gram matrices have
unbounded positive and negative index, already on the scales `a_p = 2 log p` of actual primes.

*Negative index.*  Hardy's sign change gives `Ξ(2τ₀) < 0`, so the spectral weight
`w(τ) = Ξ(2τ)/(τ² + 1/16) = B̂(τ)` is negative at `τ₀`.  Poisson summation of `x ↦ B(hx) e^{iθx}`
gives `Σ_n B(nh) cos(nθ) = Σ_k h⁻¹ w((2πk - θ)/h)`; at `θ = hτ₀` the aliased terms are
`O(h²)`, so the lattice symbol is negative for small `h`.  Toeplitz counting
`Σ_{j,k<N} g(j - k) = Σ_n max(N - |n|, 0) g(n)` and the Cesàro limit produce a finite block
`u` with `Σ u_j u_k B((j - k)h) < 0`.  Far-separated translated copies of this block, moved to
nearby prime scales (prime number theorem in short multiplicative intervals, uniform continuity
of `B`), have a Gram matrix with dominant negative diagonal; intersecting its span with the
kernel of the rank-one vacuum functional `c ↦ Σ c_i sinh(a_i/4)` leaves a negative definite
subspace of any prescribed dimension.

*Positive index.*  Single far-separated prime scales have Gram matrix `≈ B(0) I`, and the
rank-one vacuum term is nonnegative.
-/
open Complex Filter Topology Set MeasureTheory

noncomputable section

namespace RHTower

/-! ## Sign changes of the spectral weight -/

/-- Hardy's sign change: `Ξ` takes negative values at arbitrarily large real arguments. -/
theorem exists_Xi_neg (T : ℝ) : ∃ t, T < t ∧ Xi t < 0 := by
  by_contra h
  simp only [not_exists, not_and, not_lt] at h
  have hpi := Real.pi_pos
  set T' := max T 1 with hT'
  have hT'1 : 1 ≤ T' := le_max_right _ _
  refine false_of_hardyXiDensity_tail_sign (W := T' / (4 * Real.pi) + 1) (σ := -1)
    (by positivity) (by norm_num) ?_
  intro w hw
  have habs : hardyXiDensity w = hardyXiDensity |w| := by
    rcases abs_cases w with ⟨h1, _⟩ | ⟨h1, _⟩
    · rw [h1]
    · rw [h1, hardyXiDensity_neg]
  have hbig : T < 4 * Real.pi * |w| := by
    have h1 : T' / (4 * Real.pi) < |w| := by linarith
    rw [div_lt_iff₀ (by positivity)] at h1
    have : T ≤ T' := le_max_left _ _
    nlinarith
  have hXi := h (4 * Real.pi * |w|) hbig
  rw [habs, hardyXiDensity]
  have hden : (0 : ℝ) < (4 * Real.pi * |w|) ^ 2 + 1 / 4 := by positivity
  rw [show -1 * (-2 * Xi (4 * Real.pi * |w|) / ((4 * Real.pi * |w|) ^ 2 + 1 / 4)) =
    2 * Xi (4 * Real.pi * |w|) / ((4 * Real.pi * |w|) ^ 2 + 1 / 4) by ring]
  positivity

/-- The spectral weight is negative somewhere on `(0, ∞)`. -/
theorem exists_commutatorSpectralWeight_neg : ∃ τ, 0 < τ ∧ commutatorSpectralWeight τ < 0 := by
  obtain ⟨t, ht, hXi⟩ := exists_Xi_neg 0
  refine ⟨t / 2, by linarith, ?_⟩
  rw [commutatorSpectralWeight, show 2 * (t / 2) = t by ring]
  exact div_neg_of_neg_of_pos hXi (by positivity)

/-! ## Toeplitz sums and their Cesàro limit -/

/-- The Toeplitz multiplicity `max(N - |n|, 0)` of the difference `n` in `[0, N)²`. -/
def toeplitzWeight (N : ℕ) (n : ℤ) : ℝ := max ((N : ℝ) - |(n : ℝ)|) 0

theorem toeplitzWeight_succ (N : ℕ) (n : ℤ) :
    toeplitzWeight (N + 1) n = toeplitzWeight N n + if |n| ≤ (N : ℤ) then 1 else 0 := by
  unfold toeplitzWeight
  have habs : |(n : ℝ)| = ((|n| : ℤ) : ℝ) := by push_cast; rfl
  rw [habs]
  split_ifs with h
  · have h' : ((|n| : ℤ) : ℝ) ≤ N := by exact_mod_cast h
    push_cast
    rw [max_eq_left (by linarith), max_eq_left (by linarith)]
    ring
  · have h' : (N : ℝ) + 1 ≤ ((|n| : ℤ) : ℝ) := by
      have : (N : ℤ) + 1 ≤ |n| := by omega
      exact_mod_cast this
    push_cast
    rw [max_eq_right (by linarith), max_eq_right (by linarith)]
    ring

theorem toeplitzWeight_eq_zero {N : ℕ} {n : ℤ} (hn : n ∉ Finset.Icc (-(N : ℤ)) N) :
    toeplitzWeight N n = 0 := by
  unfold toeplitzWeight
  have h : (N : ℤ) < |n| := by
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn
    rw [lt_abs]; omega
  have h' : (N : ℝ) < |(n : ℝ)| := by
    have : ((N : ℤ) : ℝ) < ((|n| : ℤ) : ℝ) := by exact_mod_cast h
    push_cast at this; exact this
  exact max_eq_right (by linarith)

theorem summable_toeplitzWeight_mul (N : ℕ) (g : ℤ → ℝ) :
    Summable fun n => toeplitzWeight N n * g n :=
  summable_of_ne_finset_zero (s := Finset.Icc (-(N : ℤ)) N) fun n hn => by
    rw [toeplitzWeight_eq_zero hn, zero_mul]

theorem sum_Icc_neg_eq (g : ℤ → ℝ) (N : ℕ) :
    ∑ n ∈ Finset.Icc (-(N : ℤ)) N, g n =
      g 0 + ∑ i ∈ Finset.range N, (g ((i : ℤ) + 1) + g (-((i : ℤ) + 1))) := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hset : Finset.Icc (-((N + 1 : ℕ) : ℤ)) ((N + 1 : ℕ) : ℤ) =
        insert ((N : ℤ) + 1) (insert (-((N : ℤ) + 1)) (Finset.Icc (-(N : ℤ)) N)) := by
      ext n; simp only [Finset.mem_Icc, Finset.mem_insert]; push_cast; omega
    rw [hset, Finset.sum_insert (by simp; omega), Finset.sum_insert (by simp), ih,
      Finset.sum_range_succ]
    ring

theorem tsum_abs_le_indicator (g : ℤ → ℝ) (N : ℕ) :
    (∑' n : ℤ, if |n| ≤ (N : ℤ) then g n else 0) =
      g 0 + ∑ i ∈ Finset.range N, (g ((i : ℤ) + 1) + g (-((i : ℤ) + 1))) := by
  rw [tsum_eq_sum (s := Finset.Icc (-(N : ℤ)) N) (fun n hn => by
    rw [if_neg]
    simp only [Finset.mem_Icc, not_and_or, not_le] at hn
    rw [abs_le]; omega),
    ← sum_Icc_neg_eq]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [if_pos]
  simp only [Finset.mem_Icc] at hn
  rw [abs_le]; exact hn

/-- **Toeplitz counting.** `Σ_{j,k<N} g(j - k) = Σ_n max(N - |n|, 0) g(n)`. -/
theorem sum_range_sum_range_sub (g : ℤ → ℝ) (N : ℕ) :
    ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, g ((j : ℤ) - k) =
      ∑' n : ℤ, toeplitzWeight N n * g n := by
  induction N with
  | zero => simp [toeplitzWeight]
  | succ N ih =>
    have hrefl1 : ∑ k ∈ Finset.range N, g ((N : ℤ) - k) =
        ∑ i ∈ Finset.range N, g ((i : ℤ) + 1) := by
      rw [← Finset.sum_range_reflect (fun i => g ((i : ℤ) + 1)) N]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      congr 1; omega
    have hrefl2 : ∑ j ∈ Finset.range N, g ((j : ℤ) - N) =
        ∑ i ∈ Finset.range N, g (-((i : ℤ) + 1)) := by
      rw [← Finset.sum_range_reflect (fun i => g (-((i : ℤ) + 1))) N]
      refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      congr 1; omega
    have hL : ∑ j ∈ Finset.range (N + 1), ∑ k ∈ Finset.range (N + 1), g ((j : ℤ) - k) =
        (∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, g ((j : ℤ) - k)) +
          ∑ j ∈ Finset.range N, g ((j : ℤ) - N) + ∑ k ∈ Finset.range N, g ((N : ℤ) - k) + g 0 := by
      simp only [Finset.sum_range_succ, Finset.sum_add_distrib, sub_self]
      ring
    have hR : (∑' n : ℤ, toeplitzWeight (N + 1) n * g n) =
        (∑' n : ℤ, toeplitzWeight N n * g n) + ∑' n : ℤ, if |n| ≤ (N : ℤ) then g n else 0 := by
      rw [← (summable_toeplitzWeight_mul N g).tsum_add (summable_of_ne_finset_zero
        (s := Finset.Icc (-(N : ℤ)) N) fun n hn => by
          rw [if_neg]
          simp only [Finset.mem_Icc, not_and_or, not_le] at hn
          rw [abs_le]; omega)]
      refine tsum_congr fun n => ?_
      rw [toeplitzWeight_succ]
      split_ifs <;> ring
    rw [hL, hR, ih, tsum_abs_le_indicator, hrefl1, hrefl2, Finset.sum_add_distrib]
    ring

/-- **Cesàro limit.** `(1/N) Σ_{j,k<N} g(j - k) → Σ_n g(n)` for summable `g`. -/
theorem tendsto_toeplitz_average {g : ℤ → ℝ} (hg : Summable g) :
    Tendsto (fun N : ℕ => (∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, g ((j : ℤ) - k)) / N)
      atTop (𝓝 (∑' n, g n)) := by
  simp only [sum_range_sum_range_sub, div_eq_mul_inv, ← tsum_mul_right]
  refine tendsto_tsum_of_dominated_convergence (bound := fun n => |g n|) hg.abs
    (fun n => ?_) ?_
  · have h : Tendsto (fun N : ℕ => toeplitzWeight N n * (N : ℝ)⁻¹) atTop (𝓝 1) := by
      have h1 : Tendsto (fun N : ℕ => 1 - |(n : ℝ)| * (N : ℝ)⁻¹) atTop (𝓝 (1 - |(n : ℝ)| * 0)) :=
        tendsto_const_nhds.sub (tendsto_const_nhds.mul tendsto_inv_atTop_nhds_zero_nat)
      rw [mul_zero, sub_zero] at h1
      refine h1.congr' ?_
      filter_upwards [eventually_ge_atTop (⌈|(n : ℝ)|⌉₊ + 1)] with N hN
      have hN' : |(n : ℝ)| < N := by
        have := Nat.le_ceil |(n : ℝ)|
        have : ((⌈|(n : ℝ)|⌉₊ + 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast hN
        push_cast at this; linarith
      have hN0 : (0 : ℝ) < N := lt_of_le_of_lt (abs_nonneg _) hN'
      rw [toeplitzWeight, max_eq_left (by linarith)]
      field_simp
    have := h.mul_const (g n)
    rw [one_mul] at this
    refine this.congr fun N => ?_
    ring
  · filter_upwards [eventually_ge_atTop 1] with N hN n
    have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (le_max_right _ _),
      abs_of_pos (inv_pos.2 hN0)]
    have hw : toeplitzWeight N n ≤ N := by
      unfold toeplitzWeight
      exact max_le (by linarith [abs_nonneg (n : ℝ)]) hN0.le
    calc toeplitzWeight N n * |g n| * (N : ℝ)⁻¹ ≤ N * |g n| * (N : ℝ)⁻¹ := by gcongr
      _ = |g n| := by field_simp

/-! ## Poisson summation for the lattice symbol of the defect -/

theorem summable_int_exp_neg_mul_abs {c : ℝ} (hc : 0 < c) :
    Summable fun n : ℤ => Real.exp (-(c * |(n : ℝ)|)) := by
  have hg : Summable fun n : ℕ => Real.exp (-(c * n)) := by
    have := summable_geometric_of_lt_one (Real.exp_pos (-c)).le (Real.exp_lt_one_iff.2 (by linarith))
    refine this.congr fun n => ?_
    rw [← Real.exp_nat_mul]; ring_nf
  rw [summable_int_iff_summable_nat_and_neg]
  refine ⟨hg.congr fun n => ?_, hg.congr fun n => ?_⟩
  · simp
  · simp

theorem inv_one_add_sq_sub_le (x c : ℝ) :
    (1 + (x - c) ^ 2)⁻¹ ≤ 2 * (1 + c ^ 2) * (1 + x ^ 2)⁻¹ := by
  have h1 : 0 < 1 + (x - c) ^ 2 := by positivity
  have h2 : 0 < 1 + x ^ 2 := by positivity
  rw [show 2 * (1 + c ^ 2) * (1 + x ^ 2)⁻¹ = 2 * (1 + c ^ 2) / (1 + x ^ 2) by ring,
    inv_eq_one_div, div_le_div_iff₀ h1 h2]
  nlinarith [sq_nonneg (x - 2 * c), sq_nonneg c, sq_nonneg (x - c), mul_nonneg (sq_nonneg c)
    (sq_nonneg (x - c))]

theorem summable_int_inv_one_add_sq_mul {a : ℝ} (ha : a ≠ 0) :
    Summable fun n : ℤ => (1 + (a * n) ^ 2)⁻¹ := by
  have hb : Summable fun n : ℤ => (a ^ 2)⁻¹ * (1 / (n : ℝ) ^ 2) + if n = 0 then 1 else 0 :=
    ((Real.summable_one_div_int_pow.2 one_lt_two).mul_left _).add
      (summable_of_ne_finset_zero (s := {0}) fun n hn => by
        simp only [Finset.mem_singleton] at hn; simp [hn])
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_) hb
  by_cases hn : n = 0
  · subst hn; simp
  · rw [if_neg hn, add_zero]
    have hn' : (n : ℝ) ≠ 0 := by exact_mod_cast hn
    have hpos : 0 < (a * n) ^ 2 := by positivity
    rw [one_div, ← mul_inv, ← mul_pow]
    exact inv_anti₀ hpos (by linarith)

/-- The rescaled modulated defect `φ(x) = B(hx) e^{iθx}`. -/
def latticeProbe (h θ x : ℝ) : ℂ := (quadratureDefect (h * x) : ℂ) * cexp ((θ * x : ℝ) * I)

theorem continuous_latticeProbe (h θ : ℝ) : Continuous (latticeProbe h θ) := by
  have := continuous_quadratureDefect
  unfold latticeProbe
  fun_prop

theorem norm_latticeProbe_le (h θ x : ℝ) :
    ‖latticeProbe h θ x‖ ≤ Real.exp (-(|h * x| / 4)) := by
  rw [latticeProbe, norm_mul, Complex.norm_exp_ofReal_mul_I, mul_one, Complex.norm_real,
    Real.norm_eq_abs]
  exact abs_quadratureDefect_le _

theorem isBigO_latticeProbe {h : ℝ} (hh : 0 < h) (θ : ℝ) :
    latticeProbe h θ =O[cocompact ℝ] fun x => |x| ^ (-2 : ℝ) := by
  have key : ∀ x : ℝ, 1 ≤ |x| → ‖latticeProbe h θ x‖ ≤ 32 / h ^ 2 * ‖|x| ^ (-2 : ℝ)‖ := by
    intro x hx
    have hx0 : 0 < |x| := by linarith
    have hnorm : ‖|x| ^ (-2 : ℝ)‖ = (|x| ^ 2)⁻¹ := by
      rw [Real.norm_eq_abs, abs_of_nonneg (Real.rpow_nonneg (abs_nonneg x) _),
        Real.rpow_neg (abs_nonneg x), show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
    rw [hnorm]
    refine (norm_latticeProbe_le h θ x).trans ?_
    rw [abs_mul, abs_of_pos hh]
    have hexp := Real.pow_div_factorial_le_exp (h * |x| / 4) (by positivity) 2
    have hfac : (h * |x| / 4) ^ 2 / (Nat.factorial 2 : ℝ) = h ^ 2 * |x| ^ 2 / 32 := by
      rw [Nat.factorial_two]; push_cast; ring
    rw [hfac] at hexp
    have hpos : 0 < h ^ 2 * |x| ^ 2 / 32 := by positivity
    calc Real.exp (-(h * |x| / 4)) = 1 / Real.exp (h * |x| / 4) := by rw [Real.exp_neg, one_div]
      _ ≤ 1 / (h ^ 2 * |x| ^ 2 / 32) := one_div_le_one_div_of_le hpos hexp
      _ = 32 / h ^ 2 * (|x| ^ 2)⁻¹ := by field_simp
  refine Asymptotics.IsBigO.of_bound (32 / h ^ 2) ?_
  rw [cocompact_eq_atBot_atTop, eventually_sup]
  refine ⟨?_, ?_⟩
  · filter_upwards [eventually_le_atBot (-1)] with x hx
    exact key x (by rw [abs_of_neg (by linarith)]; linarith)
  · filter_upwards [eventually_ge_atTop 1] with x hx
    exact key x (by rw [abs_of_pos (by linarith)]; linarith)

theorem fourier_latticeProbe {h : ℝ} (hh : 0 < h) (θ ξ : ℝ) :
    FourierTransform.fourier (latticeProbe h θ) ξ =
      ((h⁻¹ * commutatorSpectralWeight ((2 * Real.pi * ξ - θ) / h) : ℝ) : ℂ) := by
  rw [Real.fourier_real_eq_integral_exp_smul]
  set τ := (2 * Real.pi * ξ - θ) / h
  have hcomp := Measure.integral_comp_mul_left
    (fun t : ℝ => cexp (-((τ : ℂ) * t * I)) * (quadratureDefect t : ℂ)) h
  have hL : (∫ v : ℝ, cexp (((-2 * Real.pi * v * ξ : ℝ) : ℂ) * I) • latticeProbe h θ v) =
      ∫ v : ℝ, cexp (-((τ : ℂ) * ((h * v : ℝ) : ℂ) * I)) * (quadratureDefect (h * v) : ℂ) := by
    refine integral_congr_ae (Eventually.of_forall fun v => ?_)
    simp only [latticeProbe, smul_eq_mul]
    rw [show ∀ A B D : ℂ, A * (B * D) = (A * D) * B from fun A B D => by ring, ← Complex.exp_add]
    congr 2
    simp only [τ]
    have hh' : (h : ℂ) ≠ 0 := by exact_mod_cast hh.ne'
    push_cast
    field_simp
    ring
  rw [hL, hcomp, fourier_quadratureDefect_eq_weight, abs_of_pos (inv_pos.2 hh), Complex.real_smul]
  push_cast
  ring

theorem summable_fourier_latticeProbe {h : ℝ} (hh : 0 < h) (θ : ℝ) :
    Summable fun n : ℤ => FourierTransform.fourier (latticeProbe h θ) n := by
  simp only [fourier_latticeProbe hh]
  refine Summable.of_norm_bounded ((summable_int_inv_one_add_sq_mul
    (show 8 * Real.pi / h ≠ 0 by positivity)).mul_left
      (h⁻¹ * (16 * thetaSourceMass) * (2 * (1 + (4 * θ / h) ^ 2)))) fun n => ?_
  rw [Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_pos (inv_pos.2 hh)]
  have hW := abs_commutatorSpectralWeight_le ((2 * Real.pi * n - θ) / h)
  have hsh : 4 * ((2 * Real.pi * n - θ) / h) = 8 * Real.pi / h * n - 4 * θ / h := by
    field_simp; ring
  rw [hsh] at hW
  have hq := inv_one_add_sq_sub_le (8 * Real.pi / h * n) (4 * θ / h)
  have hM : 0 ≤ thetaSourceMass := integral_nonneg fun t => norm_nonneg _
  calc h⁻¹ * |commutatorSpectralWeight ((2 * Real.pi * n - θ) / h)|
      ≤ h⁻¹ * (16 * thetaSourceMass * (1 + (8 * Real.pi / h * n - 4 * θ / h) ^ 2)⁻¹) :=
        mul_le_mul_of_nonneg_left hW (inv_pos.2 hh).le
    _ ≤ h⁻¹ * (16 * thetaSourceMass * (2 * (1 + (4 * θ / h) ^ 2) *
          (1 + (8 * Real.pi / h * n) ^ 2)⁻¹)) := by gcongr
    _ = _ := by ring

theorem summable_latticeProbe {h : ℝ} (hh : 0 < h) (θ : ℝ) :
    Summable fun n : ℤ => latticeProbe h θ n :=
  Summable.of_norm_bounded (summable_int_exp_neg_mul_abs (show 0 < h / 4 by positivity))
    fun n => (norm_latticeProbe_le h θ n).trans (le_of_eq (by
      rw [abs_mul, abs_of_pos hh]; ring_nf))

/-- **Poisson summation for the lattice symbol.**
`Σ_n B(nh) cos(nθ) = Σ_k h⁻¹ w((2πk - θ)/h)`. -/
theorem tsum_quadratureDefect_lattice {h : ℝ} (hh : 0 < h) (θ : ℝ) :
    ∑' n : ℤ, quadratureDefect (n * h) * Real.cos (n * θ) =
      ∑' k : ℤ, h⁻¹ * commutatorSpectralWeight ((2 * Real.pi * k - θ) / h) := by
  have hP := Real.tsum_eq_tsum_fourier_of_rpow_decay_of_summable (continuous_latticeProbe h θ)
    one_lt_two (isBigO_latticeProbe hh θ) (summable_fourier_latticeProbe hh θ) 0
  simp only [zero_add, QuotientAddGroup.mk_zero, fourier_eval_zero, mul_one,
    fourier_latticeProbe hh, ← Complex.ofReal_tsum] at hP
  have hre := congrArg Complex.re hP
  rw [Complex.re_tsum (summable_latticeProbe hh θ), Complex.ofReal_re] at hre
  rw [← hre]
  refine tsum_congr fun n => ?_
  rw [latticeProbe, Complex.re_ofReal_mul, Complex.exp_ofReal_mul_I_re, mul_comm h, mul_comm θ]

/-- **A negative lattice symbol.** There are `h > 0` and `θ` with `Σ_n B(nh) cos(nθ) < 0`. -/
theorem exists_lattice_symbol_neg :
    ∃ h θ : ℝ, 0 < h ∧ ∑' n : ℤ, quadratureDefect (n * h) * Real.cos (n * θ) < 0 := by
  obtain ⟨τ₀, hτ₀, hW₀⟩ := exists_commutatorSpectralWeight_neg
  set ε := -commutatorSpectralWeight τ₀ with hε
  have hε0 : 0 < ε := by rw [hε]; linarith
  set Z := ∑' k : ℤ, 1 / (k : ℝ) ^ 2
  have hZ : 0 ≤ Z := tsum_nonneg fun k => by positivity
  have hM : 0 ≤ thetaSourceMass := integral_nonneg fun t => norm_nonneg _
  set C := thetaSourceMass * Z / Real.pi ^ 2
  have hC : 0 ≤ C := by positivity
  set h := min (Real.pi / τ₀) (Real.sqrt (ε / (C + 1)))
  have hh : 0 < h := lt_min (by positivity) (Real.sqrt_pos.2 (by positivity))
  have hhτ : h * τ₀ ≤ Real.pi := by
    have := min_le_left (Real.pi / τ₀) (Real.sqrt (ε / (C + 1)))
    rw [le_div_iff₀ hτ₀] at this; linarith
  have hCh : C * h ^ 2 < ε := by
    have h1 : h ^ 2 ≤ ε / (C + 1) := by
      have := min_le_right (Real.pi / τ₀) (Real.sqrt (ε / (C + 1)))
      calc h ^ 2 ≤ Real.sqrt (ε / (C + 1)) ^ 2 := pow_le_pow_left₀ hh.le this 2
        _ = ε / (C + 1) := Real.sq_sqrt (by positivity)
    calc C * h ^ 2 ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left h1 hC
      _ < ε := by
        rw [mul_div_assoc', div_lt_iff₀ (by linarith)]
        nlinarith
  refine ⟨h, h * τ₀, hh, ?_⟩
  rw [tsum_quadratureDefect_lattice hh]
  -- the aliased weights
  set a : ℤ → ℝ := fun k => commutatorSpectralWeight ((2 * Real.pi * k - h * τ₀) / h)
  have ha_bound : ∀ k : ℤ, k ≠ 0 → |a k| ≤ thetaSourceMass * h ^ 2 / Real.pi ^ 2 * (1 / (k : ℝ) ^ 2) := by
    intro k hk
    have hk1 : (1 : ℝ) ≤ |(k : ℝ)| := by
      have : (1 : ℤ) ≤ |k| := Int.one_le_abs hk
      exact_mod_cast this
    have harg : (2 * Real.pi * k - h * τ₀) / h = 2 * Real.pi * k / h - τ₀ := by field_simp
    have hlow : Real.pi * |(k : ℝ)| / h ≤ |(2 * Real.pi * k - h * τ₀) / h| := by
      rw [harg]
      have hτ : τ₀ ≤ Real.pi / h := by rw [le_div_iff₀ hh]; linarith
      have h2 : |2 * Real.pi * k / h| = 2 * Real.pi * |(k : ℝ)| / h := by
        rw [abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi), abs_of_pos hh]
      have h3 := abs_sub_abs_le_abs_sub (2 * Real.pi * k / h) τ₀
      rw [h2, abs_of_pos hτ₀] at h3
      have h4 : Real.pi / h ≤ Real.pi * |(k : ℝ)| / h := by
        rw [div_le_div_iff_of_pos_right hh]; nlinarith [Real.pi_pos]
      have e : 2 * Real.pi * |(k : ℝ)| / h = 2 * (Real.pi * |(k : ℝ)| / h) := by ring
      linarith
    have hW := abs_Xi_le_thetaSourceMass (2 * ((2 * Real.pi * k - h * τ₀) / h))
    simp only [a, commutatorSpectralWeight]
    rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < ((2 * Real.pi * k - h * τ₀) / h) ^ 2 + 1 / 16)]
    set y := (2 * Real.pi * k - h * τ₀) / h
    have hy2 : (Real.pi * |(k : ℝ)| / h) ^ 2 ≤ y ^ 2 := by
      rw [← sq_abs y]; exact pow_le_pow_left₀ (by positivity) hlow 2
    have hkpos : 0 < (k : ℝ) ^ 2 := by positivity
    rw [div_le_iff₀ (by positivity)]
    calc |Xi (2 * y)| ≤ thetaSourceMass := hW
      _ ≤ thetaSourceMass * h ^ 2 / Real.pi ^ 2 * (1 / (k : ℝ) ^ 2) * (y ^ 2 + 1 / 16) := by
        have hkey : 1 ≤ h ^ 2 / Real.pi ^ 2 * (1 / (k : ℝ) ^ 2) * (y ^ 2 + 1 / 16) := by
          have e : (Real.pi * |(k : ℝ)| / h) ^ 2 = Real.pi ^ 2 * (k : ℝ) ^ 2 / h ^ 2 := by
            rw [div_pow, mul_pow, sq_abs]
          rw [e] at hy2
          have : h ^ 2 / Real.pi ^ 2 * (1 / (k : ℝ) ^ 2) * y ^ 2 ≥ 1 := by
            rw [ge_iff_le, show h ^ 2 / Real.pi ^ 2 * (1 / (k : ℝ) ^ 2) * y ^ 2 =
              y ^ 2 / (Real.pi ^ 2 * (k : ℝ) ^ 2 / h ^ 2) by field_simp, le_div_iff₀ (by positivity)]
            linarith
          have : 0 ≤ h ^ 2 / Real.pi ^ 2 * (1 / (k : ℝ) ^ 2) * (1 / 16) := by positivity
          nlinarith
        calc thetaSourceMass = thetaSourceMass * 1 := (mul_one _).symm
          _ ≤ thetaSourceMass * (h ^ 2 / Real.pi ^ 2 * (1 / (k : ℝ) ^ 2) * (y ^ 2 + 1 / 16)) :=
            mul_le_mul_of_nonneg_left hkey hM
          _ = _ := by ring
  have hsumma : Summable a := by
    refine Summable.of_norm_bounded (((Real.summable_one_div_int_pow.2 one_lt_two).mul_left
      (thetaSourceMass * h ^ 2 / Real.pi ^ 2)).add (summable_of_ne_finset_zero (s := {0})
        (f := fun k : ℤ => if k = 0 then |a 0| else 0) fun n hn => by
          simp only [Finset.mem_singleton] at hn; simp [hn])) fun k => ?_
    by_cases hk : k = 0
    · subst hk; simp
    · rw [Real.norm_eq_abs, if_neg hk, add_zero]; exact ha_bound k hk
  have hsplit := hsumma.tsum_eq_add_tsum_ite 0
  have hrest : |∑' k : ℤ, if k = 0 then 0 else a k| ≤ C * h ^ 2 := by
    have hs2 : Summable fun k : ℤ => if k = 0 then (0 : ℝ) else a k :=
      hsumma.congr_cofinite (by
        filter_upwards [(Set.finite_singleton (0 : ℤ)).compl_mem_cofinite] with k hk
        simp only [Set.mem_compl_iff, Set.mem_singleton_iff] at hk
        simp [hk]) |>.congr fun k => rfl
    have hs3 : Summable fun k : ℤ => thetaSourceMass * h ^ 2 / Real.pi ^ 2 * (1 / (k : ℝ) ^ 2) :=
      (Real.summable_one_div_int_pow.2 one_lt_two).mul_left _
    calc |∑' k : ℤ, if k = 0 then 0 else a k| ≤ ∑' k : ℤ, |if k = 0 then 0 else a k| := by
          have := norm_tsum_le_tsum_norm hs2.norm
          simpa only [Real.norm_eq_abs] using this
      _ ≤ ∑' k : ℤ, thetaSourceMass * h ^ 2 / Real.pi ^ 2 * (1 / (k : ℝ) ^ 2) := by
          refine hs2.abs.tsum_le_tsum (fun k => ?_) hs3
          by_cases hk : k = 0
          · subst hk; simp
          · rw [if_neg hk]; exact ha_bound k hk
      _ = C * h ^ 2 := by rw [tsum_mul_left]; simp only [C, Z]; ring
  have ha0 : a 0 = commutatorSpectralWeight τ₀ := by
    simp only [a, Int.cast_zero, mul_zero, zero_sub]
    rw [show -(h * τ₀) / h = -τ₀ by field_simp, commutatorSpectralWeight_neg]
  have htot : ∑' k : ℤ, a k < 0 := by
    rw [hsplit, ha0]
    have := (abs_le.mp hrest).2
    linarith
  rw [tsum_mul_left]
  exact mul_neg_of_pos_of_neg (inv_pos.2 hh) htot

/-! ## A negative Toeplitz block -/

/-- There is a finite lattice block on which the defect form is negative:
`Σ_{j,k<N} u_j u_k B((j - k) h) < 0` with `|u_j| ≤ 1`. -/
theorem exists_negative_block :
    ∃ h : ℝ, 0 < h ∧ ∃ N : ℕ, ∃ u : ℕ → ℝ, (∀ j, |u j| ≤ 1) ∧
      ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N,
        u j * u k * quadratureDefect (((j : ℝ) - k) * h) < 0 := by
  obtain ⟨h, θ, hh, hneg⟩ := exists_lattice_symbol_neg
  set g : ℤ → ℝ := fun n => quadratureDefect (n * h) * Real.cos (n * θ)
  have hg : Summable g := by
    refine Summable.of_norm_bounded (summable_int_exp_neg_mul_abs
      (show 0 < h / 4 by positivity)) fun n => ?_
    rw [Real.norm_eq_abs, abs_mul]
    calc |quadratureDefect (n * h)| * |Real.cos (n * θ)| ≤ Real.exp (-(|(n : ℝ) * h| / 4)) * 1 :=
          mul_le_mul (abs_quadratureDefect_le _) (Real.abs_cos_le_one _) (abs_nonneg _)
            (Real.exp_pos _).le
      _ = Real.exp (-(h / 4 * |(n : ℝ)|)) := by rw [abs_mul, abs_of_pos hh]; ring_nf
  have hlim := tendsto_toeplitz_average hg
  obtain ⟨N, hN⟩ := ((hlim.eventually (gt_mem_nhds hneg)).and (eventually_ge_atTop 1)).exists
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN.2
  have hsum : ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, g ((j : ℤ) - k) < 0 := by
    have h1 := hN.1
    by_contra hc
    push Not at hc
    have : 0 ≤ (∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, g ((j : ℤ) - k)) / N :=
      div_nonneg hc hN0.le
    linarith
  have hsplit : ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, g ((j : ℤ) - k) =
      (∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, Real.cos (j * θ) * Real.cos (k * θ) *
        quadratureDefect (((j : ℝ) - k) * h)) +
      ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, Real.sin (j * θ) * Real.sin (k * θ) *
        quadratureDefect (((j : ℝ) - k) * h) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [g]
    push_cast
    rw [show ((j : ℝ) - k) * θ = j * θ - k * θ by ring, Real.cos_sub]
    ring
  rw [hsplit] at hsum
  refine ⟨h, hh, N, ?_⟩
  by_cases hc : ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, Real.cos (j * θ) * Real.cos (k * θ) *
      quadratureDefect (((j : ℝ) - k) * h) < 0
  · exact ⟨fun j => Real.cos (j * θ), fun j => Real.abs_cos_le_one _, hc⟩
  · exact ⟨fun j => Real.sin (j * θ), fun j => Real.abs_sin_le_one _, by linarith⟩

/-! ## Gram matrices with dominant negative diagonal -/

theorem quadratic_neg_of_gram {M : ℕ} (G : Fin M → Fin M → ℝ) {η : ℝ} (hη : 0 < η)
    (hdiag : ∀ r, G r r ≤ -η) (hoff : ∀ r s, r ≠ s → |G r s| ≤ η / (4 * M))
    {y : Fin M → ℝ} (hy : y ≠ 0) : ∑ r, ∑ s, y r * y s * G r s < 0 := by
  have hM : 0 < M := by
    rcases Nat.eq_zero_or_pos M with h0 | h0
    · subst h0; exact absurd (funext fun i => i.elim0) hy
    · exact h0
  have hMr : (0 : ℝ) < M := by exact_mod_cast hM
  have hterm : ∀ r s, y r * y s * G r s ≤
      (if r = s then -η * y r ^ 2 else 0) + η / (4 * M) * (y r ^ 2 + y s ^ 2) := by
    intro r s
    by_cases hrs : r = s
    · subst hrs
      rw [if_pos rfl]
      have := mul_le_mul_of_nonneg_left (hdiag r) (sq_nonneg (y r))
      have h2 : 0 ≤ η / (4 * M) * (y r ^ 2 + y r ^ 2) := by positivity
      nlinarith
    · rw [if_neg hrs, zero_add]
      have h1 : y r * y s * G r s ≤ |y r| * |y s| * |G r s| := by
        rw [← abs_mul, ← abs_mul]; exact le_abs_self _
      have h2 : |y r| * |y s| ≤ (y r ^ 2 + y s ^ 2) / 2 := by
        nlinarith [sq_nonneg (|y r| - |y s|), sq_abs (y r), sq_abs (y s)]
      have h3 := hoff r s hrs
      calc y r * y s * G r s ≤ |y r| * |y s| * |G r s| := h1
        _ ≤ (y r ^ 2 + y s ^ 2) / 2 * (η / (4 * M)) :=
            mul_le_mul h2 h3 (abs_nonneg _) (by positivity)
        _ ≤ η / (4 * M) * (y r ^ 2 + y s ^ 2) := by
            have : 0 ≤ (y r ^ 2 + y s ^ 2) * (η / (4 * M)) := by positivity
            nlinarith
  have hS : 0 < ∑ r, y r ^ 2 := by
    obtain ⟨i, hi⟩ := Function.ne_iff.mp hy
    exact Finset.sum_pos' (fun r _ => sq_nonneg _)
      ⟨i, Finset.mem_univ _, lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hi))⟩
  calc ∑ r, ∑ s, y r * y s * G r s
      ≤ ∑ r, ∑ s, ((if r = s then -η * y r ^ 2 else 0) + η / (4 * M) * (y r ^ 2 + y s ^ 2)) :=
        Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s _ => hterm r s
    _ = -η * ∑ r, y r ^ 2 + η / (4 * M) * (2 * M * ∑ r, y r ^ 2) := by
        simp only [Finset.sum_add_distrib, Finset.sum_ite_eq, Finset.mem_univ, if_true,
          ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring
    _ = -(η / 2) * ∑ r, y r ^ 2 := by field_simp; ring
    _ < 0 := by nlinarith

/-! ## Uniform continuity of the defect -/

theorem tendsto_quadratureDefect_cocompact : Tendsto quadratureDefect (cocompact ℝ) (𝓝 0) := by
  have h0 : Tendsto (fun t : ℝ => Real.exp (-(|t| / 4))) (cocompact ℝ) (𝓝 0) := by
    rw [cocompact_eq_atBot_atTop]
    refine Tendsto.sup ?_ ?_
    · have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
        ((tendsto_neg_atBot_atTop).atTop_div_const (show (0 : ℝ) < 4 by norm_num))
      refine this.congr' ?_
      filter_upwards [eventually_le_atBot 0] with t ht
      simp only [Function.comp, abs_of_nonpos ht]
    · have := Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_id.atTop_div_const (show (0 : ℝ) < 4 by norm_num))
      refine this.congr' ?_
      filter_upwards [eventually_ge_atTop 0] with t ht
      simp only [Function.comp, id, abs_of_nonneg ht]
  exact squeeze_zero_norm (fun t => by rw [Real.norm_eq_abs]; exact abs_quadratureDefect_le t) h0

theorem uniformContinuous_quadratureDefect : UniformContinuous quadratureDefect :=
  continuous_quadratureDefect.uniformContinuous_of_tendsto_cocompact
    tendsto_quadratureDefect_cocompact

/-! ## Prime scales near prescribed targets -/

/-- For `ρ > 0`, every sufficiently large target `t` has a prime with `t < 2 log p < t + ρ`. -/
theorem exists_prime_log_near {ρ : ℝ} (hρ : 0 < ρ) :
    ∃ T₀ : ℝ, ∀ t, T₀ ≤ t → ∃ p : ℕ, p.Prime ∧ t < 2 * Real.log p ∧ 2 * Real.log p < t + ρ := by
  have hε : 0 < Real.exp (ρ / 2) - 1 := by
    have := Real.one_lt_exp_iff.2 (show 0 < ρ / 2 by positivity); linarith
  obtain ⟨X₀, hX₀⟩ := eventually_atTop.1 (prime_between hε)
  refine ⟨2 * Real.log (max X₀ 1), fun t ht => ?_⟩
  have hmax : 0 < max X₀ 1 := lt_max_of_lt_right one_pos
  have hX : X₀ ≤ Real.exp (t / 2) := by
    have : Real.log (max X₀ 1) ≤ t / 2 := by linarith
    calc X₀ ≤ max X₀ 1 := le_max_left _ _
      _ = Real.exp (Real.log (max X₀ 1)) := (Real.exp_log hmax).symm
      _ ≤ Real.exp (t / 2) := Real.exp_le_exp.mpr this
  obtain ⟨p, hp, hlo, hhi⟩ := hX₀ _ hX
  refine ⟨p, hp, ?_, ?_⟩
  · have := Real.log_lt_log (Real.exp_pos _) hlo
    rw [Real.log_exp] at this; linarith
  · have hpos : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have := Real.log_lt_log hpos hhi
    rw [show (1 + (Real.exp (ρ / 2) - 1)) * Real.exp (t / 2) = Real.exp (ρ / 2 + t / 2) by
      rw [Real.exp_add]; ring, Real.log_exp] at this
    linarith

/-! ## The kernel form on blocks -/

/-- The kernel form splits into the rank-one vacuum term and the defect form. -/
theorem kernelForm_eq {ι : Type*} [Fintype ι] (x c : ι → ℝ) :
    ∑ i, ∑ j, c i * c j * deletionInversionKernel (x i) (x j) =
      4 * (∑ i, c i * Real.sinh (x i / 4)) ^ 2 +
        ∑ i, ∑ j, c i * c j * (quadratureDefect (x i - x j) - quadratureDefect (x i + x j)) := by
  rw [sq, Finset.sum_mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [deletionInversionKernel_eq_sinh]; ring

/-- The Gram matrix of the block vectors `(y, j) ↦ u_j` of the defect form. -/
def blockGram {M N : ℕ} (x : Fin M × Fin N → ℝ) (u : Fin N → ℝ) (r s : Fin M) : ℝ :=
  ∑ j, ∑ k, u j * u k * (quadratureDefect (x (r, j) - x (s, k)) - quadratureDefect (x (r, j) + x (s, k)))

theorem defectForm_block {M N : ℕ} (x : Fin M × Fin N → ℝ) (u : Fin N → ℝ) (y : Fin M → ℝ) :
    ∑ i, ∑ i', (y i.1 * u i.2) * (y i'.1 * u i'.2) *
        (quadratureDefect (x i - x i') - quadratureDefect (x i + x i')) =
      ∑ r, ∑ s, y r * y s * blockGram x u r s := by
  simp only [Fintype.sum_prod_type, blockGram, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun j _ =>
    Finset.sum_congr rfl fun k _ => ?_
  ring

/-- The block embedding `y ↦ ((r, j) ↦ y_r u_j)`. -/
def blockEmbedding (M N : ℕ) (u : Fin N → ℝ) : (Fin M → ℝ) →ₗ[ℝ] (Fin M × Fin N → ℝ) where
  toFun y i := y i.1 * u i.2
  map_add' y z := by funext i; simp only [Pi.add_apply]; ring
  map_smul' a y := by funext i; simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/-- If the defect form is negative on the image of an injective-by-negativity linear map from
`ℝ^M`, the kernel form has a negative definite subspace of dimension `M - 1`. -/
theorem negIndex_of_block {ι : Type*} [Fintype ι] {M : ℕ} (x : ι → ℝ)
    (T : (Fin M → ℝ) →ₗ[ℝ] (ι → ℝ))
    (hT : ∀ y, y ≠ 0 → ∑ i, ∑ j, T y i * T y j *
      (quadratureDefect (x i - x j) - quadratureDefect (x i + x j)) < 0) :
    ∃ V : Submodule ℝ (ι → ℝ), M - 1 ≤ Module.finrank ℝ V ∧
      ∀ c ∈ V, c ≠ 0 → ∑ i, ∑ j, c i * c j * deletionInversionKernel (x i) (x j) < 0 := by
  have hinj : Function.Injective T := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    by_contra hne
    have := hT y hne
    rw [hy] at this
    simp at this
  set ℓ : (ι → ℝ) →ₗ[ℝ] ℝ := ∑ i, Real.sinh (x i / 4) • LinearMap.proj i
  have hℓ : ∀ c, ℓ c = ∑ i, c i * Real.sinh (x i / 4) := by
    intro c; simp [ℓ, mul_comm]
  refine ⟨LinearMap.range T ⊓ LinearMap.ker ℓ, ?_, ?_⟩
  · have h1 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.range T) (LinearMap.ker ℓ)
    have h2 := LinearMap.finrank_range_of_inj hinj
    rw [Module.finrank_fintype_fun_eq_card, Fintype.card_fin] at h2
    have h3 := LinearMap.finrank_range_add_finrank_ker ℓ
    have h4 : Module.finrank ℝ (LinearMap.range ℓ) ≤ 1 :=
      (Submodule.finrank_le _).trans (by simp)
    have h5 := Submodule.finrank_le (LinearMap.range T ⊔ LinearMap.ker ℓ)
    rw [Module.finrank_fintype_fun_eq_card] at h3 h5
    omega
  · intro c hc hc0
    obtain ⟨⟨y, rfl⟩, hker⟩ := Submodule.mem_inf.1 hc
    have hy : y ≠ 0 := by rintro rfl; exact hc0 (map_zero T)
    rw [kernelForm_eq]
    have h0 : ℓ (T y) = 0 := hker
    rw [hℓ] at h0
    rw [h0]
    simpa using hT y hy

/-! ## Separation of the block targets -/

theorem one_le_abs_natCast_sub {a b : ℕ} (hab : a ≠ b) : (1 : ℝ) ≤ |(a : ℝ) - b| := by
  rcases Nat.lt_or_gt_of_ne hab with h | h
  · have : (a : ℝ) + 1 ≤ b := by exact_mod_cast h
    rw [abs_of_neg (by linarith)]; linarith
  · have : (b : ℝ) + 1 ≤ a := by exact_mod_cast h
    rw [abs_of_pos (by linarith)]; linarith

theorem abs_natCast_sub_le {N : ℕ} (j k : Fin N) : |((j : ℕ) : ℝ) - (k : ℕ)| ≤ N - 1 := by
  have hj : ((j : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast j.2
  have hk : ((k : ℕ) : ℝ) + 1 ≤ N := by exact_mod_cast k.2
  have hj0 : (0 : ℝ) ≤ (j : ℕ) := Nat.cast_nonneg _
  have hk0 : (0 : ℝ) ≤ (k : ℕ) := Nat.cast_nonneg _
  rw [abs_le]; constructor <;> linarith

/-- The block target `t(r, j) = A + r D + j h`. -/
def blockTarget {M N : ℕ} (A D h : ℝ) (i : Fin M × Fin N) : ℝ :=
  A + ((i.1 : ℕ) : ℝ) * D + ((i.2 : ℕ) : ℝ) * h

theorem blockTarget_sep {M N : ℕ} {A D h : ℝ} (hh : 0 < h) (hD : (N : ℝ) * h ≤ D)
    {i i' : Fin M × Fin N} (hr : i.1 ≠ i'.1) :
    D - (N - 1) * h ≤ |blockTarget A D h i - blockTarget A D h i'| := by
  have hrs : (1 : ℝ) ≤ |((i.1 : ℕ) : ℝ) - (i'.1 : ℕ)| :=
    one_le_abs_natCast_sub (fun h' => hr (Fin.ext h'))
  have hjk := abs_natCast_sub_le i.2 i'.2
  have hD0 : 0 ≤ D := le_trans (by positivity) hD
  have e : blockTarget A D h i - blockTarget A D h i' =
      (((i.1 : ℕ) : ℝ) - (i'.1 : ℕ)) * D + (((i.2 : ℕ) : ℝ) - (i'.2 : ℕ)) * h := by
    simp only [blockTarget]; ring
  rw [e]
  have h1 : D ≤ |(((i.1 : ℕ) : ℝ) - (i'.1 : ℕ)) * D| := by
    rw [abs_mul, abs_of_nonneg hD0]; nlinarith
  have h2 : |(((i.2 : ℕ) : ℝ) - (i'.2 : ℕ)) * h| ≤ (N - 1) * h := by
    rw [abs_mul, abs_of_pos hh]; exact mul_le_mul_of_nonneg_right hjk hh.le
  have h3 := abs_sub_abs_le_abs_sub ((((i.1 : ℕ) : ℝ) - (i'.1 : ℕ)) * D)
    (-((((i.2 : ℕ) : ℝ) - (i'.2 : ℕ)) * h))
  rw [abs_neg, sub_neg_eq_add] at h3
  linarith

theorem abs_quadratureDefect_le_exp_neg {t L : ℝ} (ht : 4 * L ≤ |t|) :
    |quadratureDefect t| ≤ Real.exp (-L) :=
  (abs_quadratureDefect_le t).trans (Real.exp_le_exp.mpr (by linarith))

/-- **Gram bounds for perturbed blocks.**  Points within `ρ` above the block targets give
a diagonal within `N²(ε + e^{-L})` of the lattice form and off-diagonal entries at most
`2N² e^{-L}`. -/
theorem blockGram_bounds {M N : ℕ} {h ε δ ρ L A D : ℝ} (hh : 0 < h) (u : Fin N → ℝ)
    (hu : ∀ j, |u j| ≤ 1)
    (hUC : ∀ a b : ℝ, dist a b < δ → dist (quadratureDefect a) (quadratureDefect b) < ε)
    (hρδ : ρ ≤ δ) (hρh : ρ ≤ h / 2) (hL : 0 ≤ L) (hA : 2 * L ≤ A)
    (hD : ((N : ℝ) + 2) * h + 4 * L ≤ D) (x : Fin M × Fin N → ℝ)
    (hx : ∀ i, blockTarget A D h i < x i ∧ x i < blockTarget A D h i + ρ) :
    (∀ r, |blockGram x u r r - ∑ j, ∑ k, u j * u k *
        quadratureDefect ((((j : ℕ) : ℝ) - (k : ℕ)) * h)| ≤ N ^ 2 * (ε + Real.exp (-L))) ∧
      ∀ r s, r ≠ s → |blockGram x u r s| ≤ N ^ 2 * (2 * Real.exp (-L)) := by
  have hD0 : 0 ≤ D := le_trans (by positivity) hD
  have htA : ∀ i : Fin M × Fin N, A ≤ blockTarget A D h i := fun i => by
    simp only [blockTarget]
    have := mul_nonneg (Nat.cast_nonneg (i.1 : ℕ)) hD0
    have := mul_nonneg (Nat.cast_nonneg (i.2 : ℕ)) hh.le
    linarith
  have hsum_le : ∀ (f : Fin N → Fin N → ℝ) (c : ℝ), (∀ j k, |f j k| ≤ c) →
      |∑ j, ∑ k, f j k| ≤ N ^ 2 * c := by
    intro f c hf
    calc |∑ j, ∑ k, f j k| ≤ ∑ j, ∑ k, |f j k| :=
          (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun j _ =>
            Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _j : Fin N, ∑ _k : Fin N, c := Finset.sum_le_sum fun j _ =>
            Finset.sum_le_sum fun k _ => hf j k
      _ = N ^ 2 * c := by simp [Finset.sum_const, Finset.card_univ]; ring
  have huu : ∀ j k, |u j * u k| ≤ 1 := fun j k => by
    rw [abs_mul]; exact mul_le_one₀ (hu j) (abs_nonneg _) (hu k)
  have hplus : ∀ i i' : Fin M × Fin N, |quadratureDefect (x i + x i')| ≤ Real.exp (-L) := by
    intro i i'
    refine abs_quadratureDefect_le_exp_neg ?_
    have h1 := (hx i).1; have h2 := (hx i').1
    have h3 := htA i; have h4 := htA i'
    rw [abs_of_pos (by linarith)]; linarith
  refine ⟨fun r => ?_, fun r s hrs => ?_⟩
  · have e : blockGram x u r r - ∑ j, ∑ k, u j * u k *
        quadratureDefect ((((j : ℕ) : ℝ) - (k : ℕ)) * h) =
        ∑ j, ∑ k, u j * u k * ((quadratureDefect (x (r, j) - x (r, k)) -
          quadratureDefect ((((j : ℕ) : ℝ) - (k : ℕ)) * h)) -
            quadratureDefect (x (r, j) + x (r, k))) := by
      simp only [blockGram, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => ?_
      ring
    rw [e]
    refine hsum_le _ _ fun j k => ?_
    have hdist : dist (x (r, j) - x (r, k)) ((((j : ℕ) : ℝ) - (k : ℕ)) * h) < δ := by
      rw [Real.dist_eq]
      have h1 := hx (r, j); have h2 := hx (r, k)
      have e2 : blockTarget A D h (r, j) - blockTarget A D h (r, k) =
          (((j : ℕ) : ℝ) - (k : ℕ)) * h := by simp only [blockTarget]; ring
      rw [abs_lt]; constructor <;> linarith
    have hB := hUC _ _ hdist
    rw [Real.dist_eq] at hB
    rw [abs_mul]
    calc |u j * u k| * |quadratureDefect (x (r, j) - x (r, k)) -
          quadratureDefect ((((j : ℕ) : ℝ) - (k : ℕ)) * h) - quadratureDefect (x (r, j) + x (r, k))|
        ≤ 1 * (ε + Real.exp (-L)) := by
          refine mul_le_mul (huu j k) ((abs_sub _ _).trans ?_) (abs_nonneg _) zero_le_one
          linarith [hplus (r, j) (r, k)]
      _ = ε + Real.exp (-L) := one_mul _
  · refine hsum_le _ _ fun j k => ?_
    have hsep := blockTarget_sep (A := A) (i := (r, j)) (i' := (s, k)) hh
      (by nlinarith) hrs
    have hminus : |quadratureDefect (x (r, j) - x (s, k))| ≤ Real.exp (-L) := by
      refine abs_quadratureDefect_le_exp_neg ?_
      have h1 := hx (r, j); have h2 := hx (s, k)
      have h3 : |blockTarget A D h (r, j) - blockTarget A D h (s, k)| ≤
          |x (r, j) - x (s, k)| + ρ := by
        have := abs_sub (x (r, j) - x (s, k))
          ((x (r, j) - blockTarget A D h (r, j)) - (x (s, k) - blockTarget A D h (s, k)))
        have h4 : |(x (r, j) - blockTarget A D h (r, j)) - (x (s, k) - blockTarget A D h (s, k))|
            < ρ := by rw [abs_lt]; constructor <;> linarith
        have e3 : x (r, j) - x (s, k) - ((x (r, j) - blockTarget A D h (r, j)) -
            (x (s, k) - blockTarget A D h (s, k))) =
            blockTarget A D h (r, j) - blockTarget A D h (s, k) := by ring
        rw [e3] at this
        linarith
      nlinarith
    rw [abs_mul]
    calc |u j * u k| * |quadratureDefect (x (r, j) - x (s, k)) -
          quadratureDefect (x (r, j) + x (s, k))| ≤ 1 * (2 * Real.exp (-L)) := by
          refine mul_le_mul (huu j k) ((abs_sub _ _).trans ?_) (abs_nonneg _) zero_le_one
          linarith [hplus (r, j) (s, k)]
      _ = 2 * Real.exp (-L) := one_mul _

/-- Distinct block targets stay apart: primes chosen within `ρ ≤ h/2` above them are distinct. -/
theorem blockTarget_injective {M N : ℕ} {A D h ρ : ℝ} (hh : 0 < h) (hρh : ρ ≤ h / 2)
    (hD : ((N : ℝ) + 2) * h ≤ D) (x : Fin M × Fin N → ℝ)
    (hx : ∀ i, blockTarget A D h i < x i ∧ x i < blockTarget A D h i + ρ) :
    Function.Injective x := by
  intro i i' hxx
  have hclose : |blockTarget A D h i - blockTarget A D h i'| < ρ := by
    have h1 := hx i; have h2 := hx i'
    rw [hxx] at h1
    rw [abs_lt]; constructor <;> linarith
  by_cases hr : i.1 = i'.1
  · by_contra hne
    have hj : i.2 ≠ i'.2 := fun hj => hne (Prod.ext hr hj)
    have h1 : (1 : ℝ) ≤ |((i.2 : ℕ) : ℝ) - (i'.2 : ℕ)| :=
      one_le_abs_natCast_sub (fun h' => hj (Fin.ext h'))
    have e : blockTarget A D h i - blockTarget A D h i' = (((i.2 : ℕ) : ℝ) - (i'.2 : ℕ)) * h := by
      simp only [blockTarget, hr]; ring
    rw [e, abs_mul, abs_of_pos hh] at hclose
    nlinarith
  · have hND : (N : ℝ) * h ≤ D := le_trans (by nlinarith) hD
    have := blockTarget_sep (A := A) hh hND hr
    nlinarith

theorem exp_neg_log_max_le {c : ℝ} (hc : 0 < c) :
    Real.exp (-max (Real.log c) 0) ≤ c⁻¹ := by
  calc Real.exp (-max (Real.log c) 0) ≤ Real.exp (-Real.log c) :=
        Real.exp_le_exp.mpr (by linarith [le_max_left (Real.log c) 0])
    _ = c⁻¹ := by rw [Real.exp_neg, Real.exp_log hc]

/-! ## Infinite inertia at prime scales -/

/-- **Negative index at prime scales.** For every `m` there are distinct primes `p_i` such that
the matrix `K(2 log p_i, 2 log p_j)` is negative definite on a subspace of dimension `≥ m`. -/
theorem exists_primes_negative_index (m : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℕ), Function.Injective p ∧ (∀ i, (p i).Prime) ∧
      ∃ V : Submodule ℝ (ι → ℝ), m ≤ Module.finrank ℝ V ∧
        ∀ c ∈ V, c ≠ 0 → ∑ i, ∑ j, c i * c j *
          deletionInversionKernel (2 * Real.log (p i)) (2 * Real.log (p j)) < 0 := by
  obtain ⟨h, hh, N, u₀, hu₀, hneg⟩ := exists_negative_block
  set M := m + 1
  set u : Fin N → ℝ := fun j => u₀ j
  have hfin : (∑ j : Fin N, ∑ k : Fin N, u j * u k *
      quadratureDefect ((((j : ℕ) : ℝ) - (k : ℕ)) * h)) =
      ∑ j ∈ Finset.range N, ∑ k ∈ Finset.range N, u₀ j * u₀ k *
        quadratureDefect (((j : ℝ) - k) * h) := by
    rw [Finset.sum_range]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_range]
  set η₀ := -(∑ j : Fin N, ∑ k : Fin N, u j * u k *
    quadratureDefect ((((j : ℕ) : ℝ) - (k : ℕ)) * h))
  have hη₀ : 0 < η₀ := by simp only [η₀]; rw [hfin]; linarith
  have hN : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · subst h0; simp at hneg
    · exact h0
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hMr : (1 : ℝ) ≤ M := by simp only [M]; push_cast; linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)]
  set ε := η₀ / (4 * (N : ℝ) ^ 2)
  obtain ⟨δ, hδ, hUC⟩ := Metric.uniformContinuous_iff.1 uniformContinuous_quadratureDefect ε
    (by positivity)
  set ρ := min δ (h / 2)
  have hρ : 0 < ρ := lt_min hδ (by positivity)
  set L := max (Real.log (16 * M * (N : ℝ) ^ 2 / η₀)) 0
  have hL : 0 ≤ L := le_max_right _ _
  have heL : Real.exp (-L) ≤ η₀ / (16 * M * (N : ℝ) ^ 2) := by
    have := exp_neg_log_max_le (show 0 < 16 * (M : ℝ) * (N : ℝ) ^ 2 / η₀ by positivity)
    rwa [inv_div] at this
  obtain ⟨T₀, hT₀⟩ := exists_prime_log_near hρ
  set A := max T₀ 0 + 2 * L
  set D := ((N : ℝ) + 2) * h + 4 * L
  have hD0 : 0 ≤ D := by positivity
  have ht : ∀ i : Fin M × Fin N, T₀ ≤ blockTarget A D h i := by
    intro i
    simp only [blockTarget, A]
    have := mul_nonneg (Nat.cast_nonneg (i.1 : ℕ)) hD0
    have := mul_nonneg (Nat.cast_nonneg (i.2 : ℕ)) hh.le
    linarith [le_max_left T₀ 0, le_max_right T₀ 0]
  choose p hp using fun i => hT₀ _ (ht i)
  set x : Fin M × Fin N → ℝ := fun i => 2 * Real.log (p i)
  have hx : ∀ i, blockTarget A D h i < x i ∧ x i < blockTarget A D h i + ρ :=
    fun i => ⟨(hp i).2.1, (hp i).2.2⟩
  have hinj : Function.Injective p := by
    intro i i' hpp
    refine blockTarget_injective hh (min_le_right _ _) (by simp only [D]; linarith) x hx ?_
    simp only [x, hpp]
  obtain ⟨hdiag, hoff⟩ := blockGram_bounds hh u (fun j => hu₀ j) hUC (min_le_left _ _)
    (min_le_right _ _) hL (by simp only [A]; linarith [le_max_right T₀ 0]) le_rfl x hx
  have hNe : (N : ℝ) ^ 2 * Real.exp (-L) ≤ η₀ / (16 * M) := by
    calc (N : ℝ) ^ 2 * Real.exp (-L) ≤ (N : ℝ) ^ 2 * (η₀ / (16 * M * (N : ℝ) ^ 2)) :=
          mul_le_mul_of_nonneg_left heL (by positivity)
      _ = η₀ / (16 * M) := by field_simp
  have hNε : (N : ℝ) ^ 2 * ε = η₀ / 4 := by simp only [ε]; field_simp
  have hG : ∀ y : Fin M → ℝ, y ≠ 0 → ∑ r, ∑ s, y r * y s * blockGram x u r s < 0 := by
    intro y hy
    refine quadratic_neg_of_gram (blockGram x u) (η := η₀ / 2) (by positivity) (fun r => ?_)
      (fun r s hrs => ?_) hy
    · have h1 := (abs_le.mp (hdiag r)).2
      have h2 : η₀ / (16 * M) ≤ η₀ / 16 := by
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      have h3 : (N : ℝ) ^ 2 * (ε + Real.exp (-L)) ≤ η₀ / 4 + η₀ / 16 := by
        rw [mul_add, hNε]; linarith
      simp only [η₀] at h1 ⊢
      linarith
    · have h1 := hoff r s hrs
      calc |blockGram x u r s| ≤ (N : ℝ) ^ 2 * (2 * Real.exp (-L)) := h1
        _ = 2 * ((N : ℝ) ^ 2 * Real.exp (-L)) := by ring
        _ ≤ 2 * (η₀ / (16 * M)) := by linarith
        _ = η₀ / 2 / (4 * M) := by field_simp; ring
  obtain ⟨V, hV, hVneg⟩ := negIndex_of_block x (blockEmbedding M N u) fun y hy => by
    have := defectForm_block x u y
    simp only [blockEmbedding, LinearMap.coe_mk, AddHom.coe_mk]
    rw [this]
    exact hG y hy
  exact ⟨Fin M × Fin N, inferInstance, p, hinj, fun i => (hp i).1, V,
    by simpa [M] using hV, hVneg⟩

/-- **Positive index at prime scales.** For every `m` there are distinct primes on which the
matrix `K(2 log p_i, 2 log p_j)` is positive definite on a subspace of dimension `≥ m`. -/
theorem exists_primes_positive_index (m : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (p : ι → ℕ), Function.Injective p ∧ (∀ i, (p i).Prime) ∧
      ∃ V : Submodule ℝ (ι → ℝ), m ≤ Module.finrank ℝ V ∧
        ∀ c ∈ V, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j *
          deletionInversionKernel (2 * Real.log (p i)) (2 * Real.log (p j)) := by
  set M := m
  set u : Fin 1 → ℝ := fun _ => 1
  set β := quadratureDefect 0
  have hβ : 0 < β := quadratureDefect_pos 0
  set ε := β / 4
  obtain ⟨δ, hδ, hUC⟩ := Metric.uniformContinuous_iff.1 uniformContinuous_quadratureDefect ε
    (by positivity)
  set ρ := min δ (1 / 2 : ℝ)
  have hρ : 0 < ρ := lt_min hδ (by norm_num)
  set L := max (Real.log (16 * ((M : ℝ) + 1) / β)) 0
  have hL : 0 ≤ L := le_max_right _ _
  have heL : Real.exp (-L) ≤ β / (16 * ((M : ℝ) + 1)) := by
    have := exp_neg_log_max_le (show 0 < 16 * ((M : ℝ) + 1) / β by positivity)
    rwa [inv_div] at this
  obtain ⟨T₀, hT₀⟩ := exists_prime_log_near hρ
  set A := max T₀ 0 + 2 * L
  set D := (((1 : ℕ) : ℝ) + 2) * 1 + 4 * L
  have hD0 : 0 ≤ D := by positivity
  have ht : ∀ i : Fin M × Fin 1, T₀ ≤ blockTarget A D 1 i := by
    intro i
    simp only [blockTarget, A]
    have := mul_nonneg (Nat.cast_nonneg (i.1 : ℕ)) hD0
    have : (0 : ℝ) ≤ ((i.2 : ℕ) : ℝ) * 1 := by positivity
    linarith [le_max_left T₀ 0, le_max_right T₀ 0]
  choose p hp using fun i => hT₀ _ (ht i)
  set x : Fin M × Fin 1 → ℝ := fun i => 2 * Real.log (p i)
  have hx : ∀ i, blockTarget A D 1 i < x i ∧ x i < blockTarget A D 1 i + ρ :=
    fun i => ⟨(hp i).2.1, (hp i).2.2⟩
  have hinj : Function.Injective p := by
    intro i i' hpp
    refine blockTarget_injective one_pos (min_le_right _ _) (by simp only [D]; linarith) x hx ?_
    simp only [x, hpp]
  obtain ⟨hdiag, hoff⟩ := blockGram_bounds one_pos u (fun j => by simp [u]) hUC (min_le_left _ _)
    (min_le_right _ _) hL (by simp only [A]; linarith [le_max_right T₀ 0]) le_rfl x hx
  have hlat : (∑ j : Fin 1, ∑ k : Fin 1, u j * u k *
      quadratureDefect ((((j : ℕ) : ℝ) - (k : ℕ)) * 1)) = β := by
    simp [u, β]
  have hG : ∀ y : Fin M → ℝ, y ≠ 0 → 0 < ∑ r, ∑ s, y r * y s * blockGram x u r s := by
    intro y hy
    have hneg := quadratic_neg_of_gram (fun r s => -blockGram x u r s) (η := β / 2)
      (by positivity) (fun r => ?_) (fun r s hrs => ?_) hy
    · have e : (∑ r, ∑ s, y r * y s * -blockGram x u r s) =
          -∑ r, ∑ s, y r * y s * blockGram x u r s := by
        simp only [mul_neg, Finset.sum_neg_distrib]
      rw [e] at hneg; linarith
    · have h1 := (abs_le.mp (hdiag r)).1
      rw [hlat] at h1
      have h2 : Real.exp (-L) ≤ β / 16 := by
        refine heL.trans ?_
        rw [div_le_div_iff₀ (by positivity) (by norm_num)]
        nlinarith [(Nat.cast_nonneg M : (0 : ℝ) ≤ M)]
      simp only [Nat.cast_one, one_pow, one_mul] at h1
      simp only [ε] at h1
      linarith
    · have hM : (1 : ℝ) ≤ M := by
        have : 0 < M := Fin.pos r
        exact_mod_cast this
      have h1 := hoff r s hrs
      simp only [Nat.cast_one, one_pow, one_mul] at h1
      rw [abs_neg]
      calc |blockGram x u r s| ≤ 2 * Real.exp (-L) := h1
        _ ≤ 2 * (β / (16 * ((M : ℝ) + 1))) := by linarith
        _ ≤ β / 2 / (4 * M) := by
            rw [div_div, show 2 * (β / (16 * ((M : ℝ) + 1))) = β / (8 * ((M : ℝ) + 1)) by
              field_simp; ring]
            exact div_le_div_of_nonneg_left hβ.le (by positivity) (by nlinarith)
  have hT : ∀ y : Fin M → ℝ, y ≠ 0 → 0 < ∑ i, ∑ j, blockEmbedding M 1 u y i *
      blockEmbedding M 1 u y j * (quadratureDefect (x i - x j) - quadratureDefect (x i + x j)) := by
    intro y hy
    have := defectForm_block x u y
    simp only [blockEmbedding, LinearMap.coe_mk, AddHom.coe_mk]
    rw [this]
    exact hG y hy
  have hinjT : Function.Injective (blockEmbedding M 1 u) := by
    rw [injective_iff_map_eq_zero]
    intro y hy
    by_contra hne
    have := hT y hne
    rw [hy] at this
    simp at this
  refine ⟨Fin M × Fin 1, inferInstance, p, hinj, fun i => (hp i).1,
    LinearMap.range (blockEmbedding M 1 u), ?_, ?_⟩
  · rw [LinearMap.finrank_range_of_inj hinjT, Module.finrank_fintype_fun_eq_card, Fintype.card_fin]
  · rintro c ⟨y, rfl⟩ hc
    have hy : y ≠ 0 := by rintro rfl; exact hc (map_zero _)
    rw [kernelForm_eq]
    have := hT y hy
    have h4 : 0 ≤ 4 * (∑ i, blockEmbedding M 1 u y i * Real.sinh (x i / 4)) ^ 2 := by positivity
    simp only [x] at this h4 ⊢
    linarith

/-- On the full continuum of positive scales the kernel has infinite negative index. -/
theorem exists_positive_scales_negative_index (m : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (a : ι → ℝ), (∀ i, 0 < a i) ∧
      ∃ V : Submodule ℝ (ι → ℝ), m ≤ Module.finrank ℝ V ∧
        ∀ c ∈ V, c ≠ 0 → ∑ i, ∑ j, c i * c j * deletionInversionKernel (a i) (a j) < 0 := by
  obtain ⟨ι, hι, p, -, hp, V, hV, hneg⟩ := exists_primes_negative_index m
  refine ⟨ι, hι, fun i => 2 * Real.log (p i), fun i => ?_, V, hV, hneg⟩
  have : (1 : ℝ) < p i := by exact_mod_cast (hp i).one_lt
  have := Real.log_pos this
  positivity

/-- On the full continuum of positive scales the kernel has infinite positive index. -/
theorem exists_positive_scales_positive_index (m : ℕ) :
    ∃ (ι : Type) (_ : Fintype ι) (a : ι → ℝ), (∀ i, 0 < a i) ∧
      ∃ V : Submodule ℝ (ι → ℝ), m ≤ Module.finrank ℝ V ∧
        ∀ c ∈ V, c ≠ 0 → 0 < ∑ i, ∑ j, c i * c j * deletionInversionKernel (a i) (a j) := by
  obtain ⟨ι, hι, p, -, hp, V, hV, hpos⟩ := exists_primes_positive_index m
  refine ⟨ι, hι, fun i => 2 * Real.log (p i), fun i => ?_, V, hV, hpos⟩
  have : (1 : ℝ) < p i := by exact_mod_cast (hp i).one_lt
  have := Real.log_pos this
  positivity

end RHTower
