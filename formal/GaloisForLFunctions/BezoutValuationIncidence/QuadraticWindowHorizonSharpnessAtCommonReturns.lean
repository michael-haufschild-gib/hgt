import GaloisForLFunctions.BezoutValuationIncidence.PhaseUniformWindowSandwichAndQuadraticObservabilityHorizon

/-!
# The window–period transfer horizon is quadratic

A window sandwich constant at level `N` is a number `S` with
`|Σ_{A<k≤A+K} (s(k) - κ)² - K Q| ≤ S Q`, `Q = (H - κ)² + V`, for every row, phase, length and
offset. The observability constant `S_N ≤ (27/4) N² (1 + log N)` is one. Conversely every
sandwich constant satisfies `(N - 1 - log N)² ≤ (1 + S)(1 + log N)³`.

The obstruction is a divisor spike at a common return. The all-ones row has response
`d_N(k) = #{d ≤ N : d ∣ k}`, period mean square at most `(1 + log N)³` (Selberg coordinates
`Y(e) ≤ H_N / e`), and value `N` at every common multiple of `1, …, N`. A single sample there
already carries `(N - H)²`. The same row shows that the inverse inequality `‖c‖₁² ≤ C Q_Sel(c)`
needs `C ≥ N² / (1 + log N)³`.

So quantitative window–period transfer starts at length `N^{2+o(1)}`, and no improvement of the
constant in the window sandwich can reach the conjectured linear observability horizon `2N - 3`.
Linear observability, if true, is a qualitative incidence phenomenon that no window mean-square
comparison sees.
-/

open Finset ArithmeticFunction GaloisForLFunctions.BiScaleUncertainty RHTower
open scoped BigOperators

namespace GaloisForLFunctions.BezoutValuationIncidence
noncomputable section
set_option autoImplicit false

/-- `S` is a window sandwich constant at level `N`: the phase-uniform window mean square of every
row agrees with `K` times its period mean square up to `S` times that period mean square. -/
def IsWindowSandwichConstant (N : ℕ) (S : ℝ) : Prop :=
  ∀ (A K : ℕ) (c : ℕ → ℝ) (κ : ℝ),
    |(∑ k ∈ Icc (A + 1) (A + K), (sieveSeq N c k - κ) ^ 2) -
        (K : ℝ) * ((finiteHarmonicSum N c - κ) ^ 2 + sieveVariance N c)| ≤
      S * ((finiteHarmonicSum N c - κ) ^ 2 + sieveVariance N c)

theorem isWindowSandwichConstant_observabilityConstant {N : ℕ} (hN : 1 ≤ N) :
    IsWindowSandwichConstant N (sieveWindowObservabilityConstant N) :=
  fun A K c κ => abs_window_sum_sq_sub_le_observabilityConstant hN A K c κ

/-! ## The all-ones row: a divisor spike over a small period mean square -/

/-- The all-ones row, whose response is the truncated divisor function. -/
def sieveOnesRow : ℕ → ℝ := fun _ => 1

/-- At a common multiple of `1, …, N` the truncated divisor function equals `N`. -/
theorem sieveSeq_sieveOnesRow_factorial (N : ℕ) :
    sieveSeq N sieveOnesRow N.factorial = N := by
  unfold sieveSeq sieveOnesRow
  rw [filter_true_of_mem fun d hd =>
    Nat.dvd_factorial (mem_Icc.mp hd).1 (mem_Icc.mp hd).2]
  simp

private theorem harmonic_cast_nonneg (N : ℕ) : (0 : ℝ) ≤ harmonic N := by
  rw [_root_.harmonic_eq_sum_Icc]
  push_cast
  exact sum_nonneg fun i _ => by positivity

private theorem sum_filter_dvd_inv_le (N e : ℕ) (he : 0 < e) :
    (∑ d ∈ (Icc 1 N).filter (fun d => e ∣ d), (1 : ℝ) / d) ≤ (harmonic N : ℝ) / e := by
  have hreindex : (∑ d ∈ (Icc 1 N).filter (fun d => e ∣ d), (1 : ℝ) / d) =
      ∑ m ∈ Icc 1 (N / e), (1 : ℝ) / ((e * m : ℕ) : ℝ) := by
    refine (sum_nbij' (i := fun m => e * m) (j := fun n => n / e) ?_ ?_ ?_ ?_ ?_).symm
    · intro m hm
      rw [mem_Icc] at hm
      refine mem_filter.mpr ⟨mem_Icc.mpr ⟨?_, ?_⟩, ⟨m, rfl⟩⟩
      · exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
      · have := (Nat.le_div_iff_mul_le he).mp hm.2
        linarith [Nat.mul_comm e m]
    · intro n hn
      obtain ⟨hn, ⟨m, rfl⟩⟩ := mem_filter.mp hn
      rw [mem_Icc] at hn ⊢
      rw [Nat.mul_div_cancel_left m he]
      refine ⟨Nat.pos_of_ne_zero fun h => by simp [h] at hn, ?_⟩
      exact (Nat.le_div_iff_mul_le he).mpr (by rw [Nat.mul_comm]; exact hn.2)
    · intro m _
      exact Nat.mul_div_cancel_left m he
    · intro n hn
      obtain ⟨_, ⟨m, rfl⟩⟩ := mem_filter.mp hn
      rw [Nat.mul_div_cancel_left m he]
    · intro m _
      rfl
  rw [hreindex]
  have heR : (0 : ℝ) < e := by exact_mod_cast he
  have hterm : ∀ m ∈ Icc 1 (N / e), (1 : ℝ) / ((e * m : ℕ) : ℝ) = (1 / (e : ℝ)) * (1 / m) :=
    fun m _ => by push_cast; rw [one_div_mul_one_div]
  rw [sum_congr rfl hterm, ← mul_sum]
  have hsum : (∑ m ∈ Icc 1 (N / e), (1 : ℝ) / m) ≤ harmonic N := by
    rw [_root_.harmonic_eq_sum_Icc]
    push_cast
    refine (sum_le_sum fun m _ => by rw [one_div]).trans
      (sum_le_sum_of_subset_of_nonneg (Icc_subset_Icc_right (Nat.div_le_self N e))
        fun m _ _ => inv_nonneg.mpr (Nat.cast_nonneg m))
  calc 1 / (e : ℝ) * ∑ m ∈ Icc 1 (N / e), (1 : ℝ) / m ≤ 1 / (e : ℝ) * harmonic N :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (harmonic N : ℝ) / e := by ring

/-- The period mean square of the truncated divisor function is at most `H_N³`. -/
theorem selbergTotientDiagonalForm_sieveOnesRow_le (N : ℕ) :
    selbergTotientDiagonalForm N sieveOnesRow ≤ (harmonic N : ℝ) ^ 3 := by
  unfold selbergTotientDiagonalForm
  have hH : (0 : ℝ) ≤ harmonic N := harmonic_cast_nonneg N
  have hpt : ∀ e ∈ Icc 1 N, (Nat.totient e : ℝ) * selbergMultiplesCoord N sieveOnesRow e ^ 2 ≤
      (harmonic N : ℝ) ^ 2 * (1 / (e : ℝ)) := by
    intro e he
    have he1 := (mem_Icc.mp he).1
    have heR : (0 : ℝ) < e := by exact_mod_cast he1
    have hY : selbergMultiplesCoord N sieveOnesRow e ≤ (harmonic N : ℝ) / e := by
      unfold selbergMultiplesCoord sieveOnesRow
      exact sum_filter_dvd_inv_le N e he1
    have hY0 : 0 ≤ selbergMultiplesCoord N sieveOnesRow e := by
      unfold selbergMultiplesCoord sieveOnesRow
      exact sum_nonneg fun d _ => div_nonneg zero_le_one (Nat.cast_nonneg d)
    have hφ : (Nat.totient e : ℝ) ≤ e := by exact_mod_cast Nat.totient_le e
    calc (Nat.totient e : ℝ) * selbergMultiplesCoord N sieveOnesRow e ^ 2
        ≤ (e : ℝ) * ((harmonic N : ℝ) / e) ^ 2 :=
          mul_le_mul hφ (pow_le_pow_left₀ hY0 hY 2) (sq_nonneg _) heR.le
      _ = (harmonic N : ℝ) ^ 2 * (1 / (e : ℝ)) := by field_simp
  refine (sum_le_sum hpt).trans ?_
  rw [← mul_sum, _root_.harmonic_eq_sum_Icc]
  push_cast
  rw [show (∑ i ∈ Icc 1 N, (1 : ℝ) / i) = ∑ i ∈ Icc 1 N, ((i : ℝ))⁻¹ from
    sum_congr rfl fun i _ => one_div _]
  ring_nf
  exact le_refl _

theorem finiteHarmonicSum_sieveOnesRow (N : ℕ) :
    finiteHarmonicSum N sieveOnesRow = harmonic N := by
  unfold finiteHarmonicSum sieveOnesRow
  rw [_root_.harmonic_eq_sum_Icc]
  push_cast
  exact sum_congr rfl fun i _ => one_div _

/-! ## Lower bounds for every sandwich and every inverse `ℓ¹` constant -/

/-- **Sharpness of the quadratic horizon.** Every window sandwich constant at level `N ≥ 1`
satisfies `(N - 1 - log N)² ≤ (1 + S) (1 + log N)³`; so `S ≥ N^{2-o(1)}`. -/
theorem isWindowSandwichConstant_lower_bound {N : ℕ} (hN : 1 ≤ N) {S : ℝ}
    (hS : IsWindowSandwichConstant N S) :
    ((N : ℝ) - 1 - Real.log N) ^ 2 ≤ (1 + S) * (1 + Real.log N) ^ 3 := by
  have h := hS (N.factorial - 1) 1 sieveOnesRow (finiteHarmonicSum N sieveOnesRow)
  have hP : N.factorial - 1 + 1 = N.factorial := Nat.sub_add_cancel (Nat.factorial_pos N)
  rw [sub_self, zero_pow two_ne_zero, zero_add, hP, Icc_self, sum_singleton,
    sieveSeq_sieveOnesRow_factorial, finiteHarmonicSum_sieveOnesRow] at h
  have hHlog : (harmonic N : ℝ) ≤ 1 + Real.log N := harmonic_le_one_add_log N
  have hH0 : (0 : ℝ) ≤ harmonic N := harmonic_cast_nonneg N
  have hlog0 : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hlogN : Real.log N ≤ (N : ℝ) - 1 := by
    have := Real.log_le_sub_one_of_pos (by exact_mod_cast hN : (0 : ℝ) < N)
    exact this
  have hV : sieveVariance N sieveOnesRow ≤ (1 + Real.log N) ^ 3 := by
    have hsel := selberg_eq_harmonic_sq_add_variance N sieveOnesRow
    have hQ := selbergTotientDiagonalForm_sieveOnesRow_le N
    have hpow : (harmonic N : ℝ) ^ 3 ≤ (1 + Real.log N) ^ 3 := pow_le_pow_left₀ hH0 hHlog 3
    nlinarith [sq_nonneg (finiteHarmonicSum N sieveOnesRow)]
  have hV0 : 0 ≤ sieveVariance N sieveOnesRow :=
    sum_nonneg fun _ _ => mul_nonneg (Nat.cast_nonneg _) (sq_nonneg _)
  have hS0 : 0 ≤ S := by
    have h0 := hS 0 0 (fun _ => 0) 1
    have hH : finiteHarmonicSum N (fun _ => 0) = 0 := by simp [finiteHarmonicSum]
    have hVz : sieveVariance N (fun _ => 0) = 0 := by
      simp [sieveVariance, selbergMultiplesCoord]
    rw [hH, hVz] at h0
    simpa using h0
  rw [abs_le] at h
  push_cast at h
  have hHN : (harmonic N : ℝ) ≤ N := by
    rw [_root_.harmonic_eq_sum_Icc]
    push_cast
    calc (∑ i ∈ Icc 1 N, ((i : ℝ))⁻¹) ≤ ∑ _i ∈ Icc 1 N, (1 : ℝ) :=
          sum_le_sum fun i hi => inv_le_one_of_one_le₀ (by exact_mod_cast (mem_Icc.mp hi).1)
      _ = N := by simp
  have hspike : ((N : ℝ) - 1 - Real.log N) ^ 2 ≤ ((N : ℝ) - harmonic N) ^ 2 :=
    pow_le_pow_left₀ (by linarith) (by linarith) 2
  nlinarith [h.2, mul_le_mul_of_nonneg_left hV (by linarith : (0 : ℝ) ≤ 1 + S)]

/-- Every constant in the inverse inequality `‖c‖₁² ≤ C Q_Sel(c)` satisfies
`N² ≤ C (1 + log N)³`. -/
theorem inverse_l1_constant_lower_bound (N : ℕ) {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ c : ℕ → ℝ, (∑ d ∈ Icc 1 N, |c d|) ^ 2 ≤ C * selbergTotientDiagonalForm N c) :
    (N : ℝ) ^ 2 ≤ C * (1 + Real.log N) ^ 3 := by
  have h := hC sieveOnesRow
  have hsum : (∑ d ∈ Icc 1 N, |sieveOnesRow d|) = N := by simp [sieveOnesRow]
  rw [hsum] at h
  have hH0 : (0 : ℝ) ≤ harmonic N := harmonic_cast_nonneg N
  have hpow : (harmonic N : ℝ) ^ 3 ≤ (1 + Real.log N) ^ 3 :=
    pow_le_pow_left₀ hH0 (harmonic_le_one_add_log N) 3
  calc (N : ℝ) ^ 2 ≤ C * selbergTotientDiagonalForm N sieveOnesRow := h
    _ ≤ C * (harmonic N : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_left (selbergTotientDiagonalForm_sieveOnesRow_le N) hC0
    _ ≤ C * (1 + Real.log N) ^ 3 := mul_le_mul_of_nonneg_left hpow hC0

end

end GaloisForLFunctions.BezoutValuationIncidence
