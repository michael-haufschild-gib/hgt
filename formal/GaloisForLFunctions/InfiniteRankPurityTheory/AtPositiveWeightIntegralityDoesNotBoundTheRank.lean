import GaloisForLFunctions.InfiniteRankPurityTheory.CesaroMeansReadTheModesOfASummableTower

/-!
# At positive weight integrality does not bound the rank

Kronecker's theorem for one Frobenius needs weight zero. The **limit-periodic tower** has, for every
`k ≥ 0`, the `2^k` modes `2 ω`, `ω^{2^k} = 1`, each of weight `4^{−k}`.

* Every mode has modulus `2`: the tower is pure of weight one over `𝔽₄` (`norm_lpMode`).
* The weights are summable (`summable_norm_lpWeight`).
* The level sums are integers at every level `ν ≥ 1`:
  `S(ν) = Σ_{k : 2^k ∣ ν} 2^{ν − k}` (`lp_levelSum_eq`, `exists_int_lp_levelSum`).
* Infinitely many points carry weight: the rank is infinite (`lp_infinite_rank`).

So for one Frobenius purity and integrality of the traces leave the rank free as soon as the weight is
positive; the normalized level sums `2^{−ν} S(ν) = Σ_{2^k ∣ ν} 2^{−k}` form a limit-periodic sequence.
With the Frobenii at all integers the same hypotheses force Tate twists
(`tate_of_integral_trace`): two Frobenii with incommensurable logarithms do what one cannot.
-/

open Filter Topology Finset

namespace GaloisForLFunctions.InfiniteRankPurityTheory

noncomputable section

/-- The index of the limit-periodic tower: a level `k` and a residue `j` modulo `2^k`. -/
abbrev LPIndex : Type := Σ k : ℕ, Fin (2 ^ k)

/-- The primitive `2^k`-th root of unity `e^{2πi/2^k}`. -/
def lpRoot (k : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / ((2 ^ k : ℕ) : ℂ))

theorem isPrimitiveRoot_lpRoot (k : ℕ) : IsPrimitiveRoot (lpRoot k) (2 ^ k) :=
  Complex.isPrimitiveRoot_exp _ (by positivity)

/-- The mode `2 ω`, `ω = e^{2πi j/2^k}`. -/
def lpMode (i : LPIndex) : ℂ := 2 * lpRoot i.1 ^ (i.2 : ℕ)

/-- The weight `4^{−k}` of the modes of level `k`. -/
def lpWeight (i : LPIndex) : ℂ := ((4 : ℂ)⁻¹) ^ i.1

theorem norm_lpRoot (k : ℕ) : ‖lpRoot k‖ = 1 :=
  (isPrimitiveRoot_lpRoot k).norm'_eq_one (by positivity)

/-- **Purity.** Every mode has modulus `2`. -/
theorem norm_lpMode (i : LPIndex) : ‖lpMode i‖ = 2 := by
  rw [lpMode, norm_mul, norm_pow, norm_lpRoot, one_pow, mul_one, Complex.norm_ofNat]

theorem norm_lp_term (ν : ℕ) (i : LPIndex) :
    ‖lpWeight i * lpMode i ^ ν‖ = (1 / 4 : ℝ) ^ i.1 * 2 ^ ν := by
  rw [norm_mul, norm_pow, norm_lpMode, lpWeight, norm_pow, norm_inv, Complex.norm_ofNat]
  norm_num

theorem summable_lp_bound (ν : ℕ) : Summable fun i : LPIndex => (1 / 4 : ℝ) ^ i.1 * 2 ^ ν := by
  rw [summable_sigma_of_nonneg (fun _ => by positivity)]
  refine ⟨fun k => (hasSum_fintype _).summable, ?_⟩
  have h : (fun k : ℕ => ∑' _j : Fin (2 ^ k), (1 / 4 : ℝ) ^ k * 2 ^ ν) =
      fun k : ℕ => 2 ^ ν * (1 / 2 : ℝ) ^ k := by
    funext k
    rw [tsum_fintype, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    rw [show (1 / 4 : ℝ) = 1 / 2 * (1 / 2) by norm_num, mul_pow]
    have h2 : (2 : ℝ) ^ k * (1 / 2 : ℝ) ^ k = 1 := by
      rw [← mul_pow]
      norm_num
    linear_combination ((1 / 2 : ℝ) ^ k * 2 ^ ν) * h2
  rw [h]
  exact summable_geometric_two.mul_left _

/-- **Trace class.** The weights are summable. -/
theorem summable_norm_lpWeight : Summable fun i : LPIndex => ‖lpWeight i‖ := by
  have h := summable_lp_bound 0
  refine h.congr fun i => ?_
  rw [← norm_lp_term 0 i]
  simp

theorem summable_lp_term (ν : ℕ) : Summable fun i : LPIndex => lpWeight i * lpMode i ^ ν :=
  Summable.of_norm_bounded (summable_lp_bound ν) fun i => (norm_lp_term ν i).le

/-- The power sums of the `n`-th roots of unity. -/
theorem sum_range_root_pow {ζ : ℂ} {n : ℕ} (hζ : IsPrimitiveRoot ζ n) (ν : ℕ) :
    ∑ j ∈ range n, (ζ ^ j) ^ ν = if n ∣ ν then (n : ℂ) else 0 := by
  have hcomm : ∀ j, (ζ ^ j) ^ ν = (ζ ^ ν) ^ j := fun j => by
    rw [← pow_mul, ← pow_mul, mul_comm]
  simp_rw [hcomm]
  split_ifs with h
  · rw [(hζ.pow_eq_one_iff_dvd ν).mpr h]
    simp
  · have hne : ζ ^ ν ≠ 1 := fun h1 => h ((hζ.pow_eq_one_iff_dvd ν).mp h1)
    have hpow : (ζ ^ ν) ^ n = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
    rw [geom_sum_eq hne, hpow, sub_self, zero_div]

/-- The level sum of one level `k`. -/
theorem sum_lp_level (ν k : ℕ) :
    ∑ j : Fin (2 ^ k), lpWeight ⟨k, j⟩ * lpMode ⟨k, j⟩ ^ ν =
      if 2 ^ k ∣ ν then (2 : ℂ) ^ ν / 2 ^ k else 0 := by
  have h1 : ∀ j : Fin (2 ^ k), lpWeight ⟨k, j⟩ * lpMode ⟨k, j⟩ ^ ν =
      ((4 : ℂ)⁻¹) ^ k * 2 ^ ν * (lpRoot k ^ (j : ℕ)) ^ ν := by
    intro j
    simp only [lpWeight, lpMode]
    rw [mul_pow]
    ring
  simp_rw [h1]
  rw [← Finset.mul_sum, Fin.sum_univ_eq_sum_range (fun j => (lpRoot k ^ j) ^ ν),
    sum_range_root_pow (isPrimitiveRoot_lpRoot k)]
  split_ifs with h
  · push_cast
    have h2 : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
    have h4 : ((4 : ℂ)⁻¹) ^ k = ((2 : ℂ) ^ k)⁻¹ * ((2 : ℂ) ^ k)⁻¹ := by
      rw [← mul_inv, ← mul_pow, inv_pow]
      norm_num
    rw [h4]
    field_simp
  · rw [mul_zero]

/-- **The level sums.** `S(ν) = Σ_{k : 2^k ∣ ν} 2^ν / 2^k`. -/
theorem lp_levelSum_eq (ν : ℕ) :
    ∑' i : LPIndex, lpWeight i * lpMode i ^ ν =
      ∑' k : ℕ, if 2 ^ k ∣ ν then (2 : ℂ) ^ ν / 2 ^ k else 0 := by
  rw [(summable_lp_term ν).tsum_sigma' fun k => (hasSum_fintype _).summable]
  refine tsum_congr fun k => ?_
  rw [tsum_fintype, sum_lp_level]

/-- **Integrality.** At every level `ν ≥ 1` the level sum is an integer. -/
theorem exists_int_lp_levelSum {ν : ℕ} (hν : 1 ≤ ν) :
    ∃ n : ℤ, ∑' i : LPIndex, lpWeight i * lpMode i ^ ν = n := by
  refine ⟨∑ k ∈ range ν, if 2 ^ k ∣ ν then (2 : ℤ) ^ (ν - k) else 0, ?_⟩
  rw [lp_levelSum_eq, tsum_eq_sum (s := range ν)]
  · push_cast
    refine Finset.sum_congr rfl fun k hk => ?_
    have hkν : k ≤ ν := (Finset.mem_range.mp hk).le
    split_ifs
    · rw [pow_sub₀ _ two_ne_zero hkν, div_eq_mul_inv]
    · rfl
  · intro k hk
    have hkν : ν ≤ k := not_lt.mp (Finset.mem_range.not.mp hk)
    have hnd : ¬ 2 ^ k ∣ ν := by
      intro hd
      have h1 := Nat.le_of_dvd (by omega) hd
      have h2 : k < 2 ^ k := Nat.lt_two_pow_self
      omega
    rw [if_neg hnd]

/-- The point `2 e^{2πi/2^{k+1}}` carries positive weight. -/
theorem lp_merged_ne_zero (k : ℕ) :
    (∑' i : LPIndex, if lpMode i = 2 * lpRoot (k + 1) then lpWeight i else 0) ≠ 0 := by
  classical
  set g : LPIndex → ℝ := fun i => if lpMode i = 2 * lpRoot (k + 1) then (1 / 4 : ℝ) ^ i.1 else 0
    with hg
  have hg0 : ∀ i, 0 ≤ g i := by
    intro i
    rw [hg]
    simp only
    split_ifs <;> positivity
  have hgs : Summable g := by
    refine Summable.of_nonneg_of_le hg0 (fun i => ?_) (summable_lp_bound 0)
    rw [hg]
    simp only
    split_ifs
    · simp
    · positivity
  have hcast : (∑' i : LPIndex, if lpMode i = 2 * lpRoot (k + 1) then lpWeight i else 0) =
      ((∑' i, g i : ℝ) : ℂ) := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun i => ?_
    rw [hg]
    simp only [lpWeight]
    split_ifs
    · push_cast
      norm_num
    · simp
  rw [hcast]
  have h1lt : 1 < 2 ^ (k + 1) := Nat.one_lt_two_pow (by omega)
  set i₀ : LPIndex := ⟨k + 1, ⟨1, h1lt⟩⟩ with hi₀
  have hi₀pos : 0 < g i₀ := by
    rw [hg]
    simp only
    have : lpMode i₀ = 2 * lpRoot (k + 1) := by
      rw [lpMode, hi₀]
      simp
    rw [if_pos this]
    positivity
  have hpos : 0 < ∑' i, g i := hgs.tsum_pos hg0 i₀ hi₀pos
  exact_mod_cast hpos.ne'

theorem lpRoot_injective : Function.Injective lpRoot := by
  intro k l h
  have hk := isPrimitiveRoot_lpRoot k
  have hl := isPrimitiveRoot_lpRoot l
  rw [h] at hk
  exact Nat.pow_right_injective (le_refl 2) (hk.unique hl)

/-- **Infinite rank.** Infinitely many points carry nonzero weight. -/
theorem lp_infinite_rank :
    {w : ℂ | (∑' i : LPIndex, if lpMode i = w then lpWeight i else 0) ≠ 0}.Infinite := by
  refine Set.infinite_of_injective_forall_mem (f := fun k : ℕ => 2 * lpRoot (k + 1)) ?_
    fun k => lp_merged_ne_zero k
  intro k l h
  have h1 : lpRoot (k + 1) = lpRoot (l + 1) := mul_left_cancel₀ two_ne_zero h
  have := lpRoot_injective h1
  omega

/-- **At positive weight integrality does not bound the rank.** There is a summable tower, pure of
modulus `2`, with integer level sums at every level `ν ≥ 1`, and of infinite rank. -/
theorem exists_pure_integral_tower_of_infinite_rank :
    ∃ (ι : Type) (c z : ι → ℂ), Summable (fun i => ‖c i‖) ∧ (∀ i, ‖z i‖ = 2) ∧
      (∀ ν : ℕ, 1 ≤ ν → ∃ n : ℤ, ∑' i, c i * z i ^ ν = n) ∧
      {w : ℂ | (∑' i, if z i = w then c i else 0) ≠ 0}.Infinite :=
  ⟨LPIndex, lpWeight, lpMode, summable_norm_lpWeight, norm_lpMode,
    fun _ hν => exists_int_lp_levelSum hν, lp_infinite_rank⟩

end

end GaloisForLFunctions.InfiniteRankPurityTheory
