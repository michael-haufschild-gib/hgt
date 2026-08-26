import GaloisForLFunctions.RHTower.Sieve.NatDivLogEndpointError

namespace RHTower.Sieve

private theorem log_natDiv_endpoint_bounds
    {N q : ℕ} (hN : 0 < N) (hq : 0 < q) (hqN : q ≤ N) :
    let x : ℝ := (N : ℝ) / (q : ℝ)
    let y : ℝ := ((N / q + 1 : ℕ) : ℝ)
    0 ≤ Real.log x ∧ Real.log x ≤ Real.log ((N + 1 : ℕ) : ℝ) ∧
      0 ≤ Real.log y ∧ Real.log y ≤ Real.log ((N + 1 : ℕ) : ℝ) := by
  dsimp
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hNR : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  have hqone : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hxone : (1 : ℝ) ≤ (N : ℝ) / (q : ℝ) := by
    rw [le_div_iff₀ hqR]
    norm_num
    exact_mod_cast hqN
  have hxle : (N : ℝ) / (q : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
    push_cast
    rw [div_le_iff₀ hqR]
    nlinarith
  have hyone : (1 : ℝ) ≤ ((N / q + 1 : ℕ) : ℝ) := by
    exact_mod_cast Nat.succ_le_succ (Nat.zero_le (N / q))
  have hyNat : N / q + 1 ≤ N + 1 := Nat.add_le_add_right (Nat.div_le_self N q) 1
  have hyle : ((N / q + 1 : ℕ) : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by exact_mod_cast hyNat
  exact ⟨Real.log_nonneg hxone,
    Real.log_le_log (by positivity) hxle,
    Real.log_nonneg hyone,
    Real.log_le_log (by positivity) hyle⟩

theorem abs_log_natDiv_add_one_sq_sub_log_div_sq_le
    {N q : ℕ} (hN : 0 < N) (hq : 0 < q) (hqN : q ≤ N) :
    |Real.log ((N / q + 1 : ℕ) : ℝ) ^ 2 -
        Real.log ((N : ℝ) / (q : ℝ)) ^ 2| ≤
      2 * Real.log ((N + 1 : ℕ) : ℝ) * ((q : ℝ) / (N : ℝ)) := by
  let x : ℝ := Real.log ((N : ℝ) / (q : ℝ))
  let y : ℝ := Real.log ((N / q + 1 : ℕ) : ℝ)
  let K : ℝ := Real.log ((N + 1 : ℕ) : ℝ)
  obtain ⟨hx0, hxK, hy0, hyK⟩ := log_natDiv_endpoint_bounds hN hq hqN
  have hgap : |y - x| ≤ (q : ℝ) / (N : ℝ) := by
    simpa [x, y] using abs_log_natDiv_add_one_sub_log_div_le hN hq
  have hsum0 : 0 ≤ y + x := add_nonneg hy0 hx0
  have hsumK : y + x ≤ 2 * K := by dsimp [K] at ⊢; linarith
  change |y ^ 2 - x ^ 2| ≤ 2 * K * ((q : ℝ) / (N : ℝ))
  rw [show y ^ 2 - x ^ 2 = (y - x) * (y + x) by ring, abs_mul,
    abs_of_nonneg hsum0]
  calc
    |y - x| * (y + x) ≤ ((q : ℝ) / (N : ℝ)) * (2 * K) :=
      mul_le_mul hgap hsumK hsum0 (by positivity)
    _ = 2 * K * ((q : ℝ) / (N : ℝ)) := by ring

theorem abs_log_natDiv_add_one_cube_sub_log_div_cube_le
    {N q : ℕ} (hN : 0 < N) (hq : 0 < q) (hqN : q ≤ N) :
    |Real.log ((N / q + 1 : ℕ) : ℝ) ^ 3 -
        Real.log ((N : ℝ) / (q : ℝ)) ^ 3| ≤
      3 * Real.log ((N + 1 : ℕ) : ℝ) ^ 2 * ((q : ℝ) / (N : ℝ)) := by
  let x : ℝ := Real.log ((N : ℝ) / (q : ℝ))
  let y : ℝ := Real.log ((N / q + 1 : ℕ) : ℝ)
  let K : ℝ := Real.log ((N + 1 : ℕ) : ℝ)
  obtain ⟨hx0, hxK, hy0, hyK⟩ := log_natDiv_endpoint_bounds hN hq hqN
  have hK0 : 0 ≤ K := by
    dsimp [K]
    exact Real.log_nonneg (by exact_mod_cast (by omega : 1 ≤ N + 1))
  have hgap : |y - x| ≤ (q : ℝ) / (N : ℝ) := by
    simpa [x, y] using abs_log_natDiv_add_one_sub_log_div_le hN hq
  have hxy0 : 0 ≤ y ^ 2 + y * x + x ^ 2 := by positivity
  have hyxK : y * x ≤ K * K := mul_le_mul hyK hxK hx0 hK0
  have hy2K : y ^ 2 ≤ K ^ 2 := by
    have hyy : y * y ≤ y * K := mul_le_mul_of_nonneg_left hyK hy0
    have hyK' : y * K ≤ K * K := mul_le_mul_of_nonneg_right hyK hK0
    nlinarith
  have hx2K : x ^ 2 ≤ K ^ 2 := by
    have hxx : x * x ≤ x * K := mul_le_mul_of_nonneg_left hxK hx0
    have hxK' : x * K ≤ K * K := mul_le_mul_of_nonneg_right hxK hK0
    nlinarith
  have hfactor : y ^ 2 + y * x + x ^ 2 ≤ 3 * K ^ 2 := by
    nlinarith
  change |y ^ 3 - x ^ 3| ≤ 3 * K ^ 2 * ((q : ℝ) / (N : ℝ))
  rw [show y ^ 3 - x ^ 3 = (y - x) * (y ^ 2 + y * x + x ^ 2) by ring,
    abs_mul, abs_of_nonneg hxy0]
  calc
    |y - x| * (y ^ 2 + y * x + x ^ 2) ≤
        ((q : ℝ) / (N : ℝ)) * (3 * K ^ 2) :=
      mul_le_mul hgap hfactor hxy0 (by positivity)
    _ = 3 * K ^ 2 * ((q : ℝ) / (N : ℝ)) := by ring

end RHTower.Sieve
