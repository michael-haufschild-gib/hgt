import GaloisForLFunctions.RHTower.SymmetricPowerArchimedeanExponents

/-!
# Exact degree requirements for symmetric-power amplification

A real exponent passes the degree-`d` half-strip test precisely when `d * |ν| < 1/2`.
For an arbitrary set of degrees, the common admissible locus is `{0}` exactly when the degree
set is infinite. Every finite set of tests still admits a positive complementary exponent and
its associated scalar eigenvalue strictly between zero and one quarter.

These are exact statements about the explicit exponent packets. They do not construct
automorphic lifts or identify scalar eigenvalues with the congruence cuspidal spectrum.
-/

namespace GaloisForLFunctions.RHTower

/-- The endpoint exponent controls the whole packet, including degree zero. -/
theorem mem_genericUnitarySymPowerLocus_iff_mul_abs (ν : ℝ) (d : ℕ) :
    ν ∈ genericUnitarySymPowerLocus d ↔ (d : ℝ) * |ν| < 1 / 2 := by
  constructor
  · intro h
    have hzero := h ⟨0, Nat.zero_lt_succ d⟩
    simpa only [symmetricPowerArchimedeanExponent_zero, abs_mul,
      abs_of_nonneg (show (0 : ℝ) ≤ (d : ℝ) from Nat.cast_nonneg d)] using hzero
  · intro h j
    rw [symmetricPowerArchimedeanExponent, abs_mul]
    exact lt_of_le_of_lt
      (mul_le_mul_of_nonneg_right (abs_symmetricPower_coefficient_le d j) (abs_nonneg ν)) h

/-- A nonzero real parameter passes the half-strip test in only finitely many degrees. -/
theorem finite_genericUnitarySymPower_degrees_iff (ν : ℝ) :
    {d : ℕ | ν ∈ genericUnitarySymPowerLocus d}.Finite ↔ ν ≠ 0 := by
  constructor
  · intro hfinite hzero
    subst ν
    have heq : {d : ℕ | (0 : ℝ) ∈ genericUnitarySymPowerLocus d} = Set.univ := by
      ext d
      simp [mem_genericUnitarySymPowerLocus_iff_mul_abs]
    rw [heq] at hfinite
    exact Set.infinite_univ hfinite
  · intro hν
    have hpos : 0 < |ν| := abs_pos.mpr hν
    obtain ⟨N, hN⟩ := exists_nat_gt ((1 / 2 : ℝ) / |ν|)
    refine (Set.finite_Iio N).subset ?_
    intro d hd
    have hd' := (mem_genericUnitarySymPowerLocus_iff_mul_abs ν d).mp hd
    have hN' : (1 / 2 : ℝ) < (N : ℝ) * |ν| := (div_lt_iff₀ hpos).mp hN
    have hdN : (d : ℝ) < (N : ℝ) := by nlinarith
    exact Nat.cast_lt.mp hdN

/-- Every bounded initial segment of degrees admits a positive complementary parameter. -/
theorem exists_positive_exponent_in_genericUnitarySymPower_initial_segment (N : ℕ) :
    ∃ ν : ℝ, ν ∈ Set.Ioo 0 (1 / 2) ∧
      ∀ d : ℕ, d ≤ N → ν ∈ genericUnitarySymPowerLocus d := by
  let ν : ℝ := (1 / 2) / ((N : ℝ) + 2)
  have hden : (0 : ℝ) < (N : ℝ) + 2 := by positivity
  have hνpos : 0 < ν := by dsimp [ν]; positivity
  have hνhalf : ν < 1 / 2 := by
    dsimp [ν]
    apply (div_lt_iff₀ hden).mpr
    have hN : (0 : ℝ) ≤ N := Nat.cast_nonneg N
    linarith
  refine ⟨ν, ⟨hνpos, hνhalf⟩, ?_⟩
  intro d hd
  rw [mem_genericUnitarySymPowerLocus_iff_mul_abs, abs_of_pos hνpos]
  have hdR : (d : ℝ) ≤ N := by exact_mod_cast hd
  calc
    (d : ℝ) * ν < ((N : ℝ) + 2) * ν :=
      mul_lt_mul_of_pos_right (by linarith) hνpos
    _ = 1 / 2 := by dsimp [ν]; field_simp

/-- An arbitrary degree family isolates zero exactly when that family is infinite. -/
theorem genericUnitarySymPower_degree_family_eq_singleton_iff (D : Set ℕ) :
    {ν : ℝ | ∀ d ∈ D, ν ∈ genericUnitarySymPowerLocus d} = {0} ↔ D.Infinite := by
  constructor
  · intro heq
    by_contra hD
    have hfinite : D.Finite := Set.not_infinite.mp hD
    obtain ⟨N, hN⟩ := hfinite.bddAbove
    obtain ⟨ν, hν, hadmit⟩ :=
      exists_positive_exponent_in_genericUnitarySymPower_initial_segment N
    have hmem : ν ∈ {ν : ℝ | ∀ d ∈ D, ν ∈ genericUnitarySymPowerLocus d} :=
      fun d hd => hadmit d (hN hd)
    rw [heq] at hmem
    have hzero : ν = 0 := hmem
    linarith [hν.1]
  · intro hD
    ext ν
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · intro hadmit
      by_contra hν
      have hfinite := (finite_genericUnitarySymPower_degrees_iff ν).mpr hν
      exact hD (hfinite.subset hadmit)
    · rintro rfl
      intro d _
      simp [mem_genericUnitarySymPowerLocus_iff_mul_abs]

/-- Every finite collection of strip tests admits a scalar eigenvalue strictly below one quarter. -/
theorem exists_exceptional_scalar_in_finite_genericUnitarySymPower_family (D : Finset ℕ) :
    ∃ ν : ℝ, ν ∈ Set.Ioo 0 (1 / 2) ∧
      (∀ d ∈ D, ν ∈ genericUnitarySymPowerLocus d) ∧
      eigenvalueOfComplementaryExponent ν ∈ Set.Ioo 0 (1 / 4) := by
  obtain ⟨N, hN⟩ := D.bddAbove
  obtain ⟨ν, hν, hadmit⟩ :=
    exists_positive_exponent_in_genericUnitarySymPower_initial_segment N
  refine ⟨ν, hν, fun d hd => hadmit d (hN hd), ?_⟩
  have hsquare : ν ^ 2 < (1 / 2 : ℝ) ^ 2 :=
    (sq_lt_sq₀ hν.1.le (by positivity)).mpr hν.2
  have hpositive : 0 < ν ^ 2 := sq_pos_of_pos hν.1
  constructor <;> dsimp [eigenvalueOfComplementaryExponent] <;> linarith

end GaloisForLFunctions.RHTower
