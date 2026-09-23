import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic

/-!
# Archimedean exponents under symmetric power

For a rank-two self-dual parameter with real exponents `(ν, -ν)`, its degree-`d` symmetric power
has exponents `(d - 2j)ν`, `0 ≤ j ≤ d`.  This file formalizes that packet and computes exactly
the locus where every exponent lies in the open generic-unitary strip `(-1/2, 1/2)`.

The resulting all-degree locus is the singleton `{0}`.  This is the scalar end of the
symmetric-power route to Selberg's quarter conjecture; it does not assert existence or local
compatibility of any automorphic symmetric-power lift.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

/-- Degree-`d` symmetric-power exponents of the self-dual rank-two packet `(ν, -ν)`. -/
def symmetricPowerArchimedeanExponent (ν : ℝ) (d : ℕ) (j : Fin (d + 1)) : ℝ :=
  ((d : ℝ) - 2 * ((j : ℕ) : ℝ)) * ν

@[simp]
theorem symmetricPowerArchimedeanExponent_zero (ν : ℝ) (d : ℕ) :
    symmetricPowerArchimedeanExponent ν d ⟨0, Nat.zero_lt_succ d⟩ = (d : ℝ) * ν := by
  simp [symmetricPowerArchimedeanExponent]

@[simp]
theorem symmetricPowerArchimedeanExponent_last (ν : ℝ) (d : ℕ) :
    symmetricPowerArchimedeanExponent ν d ⟨d, Nat.lt_succ_self d⟩ = -(d : ℝ) * ν := by
  simp [symmetricPowerArchimedeanExponent]
  ring

/-- Reflection of the weight index negates the corresponding exponent. -/
theorem symmetricPowerArchimedeanExponent_reflect (ν : ℝ) (d : ℕ)
    (j : Fin (d + 1)) :
    symmetricPowerArchimedeanExponent ν d
        ⟨d - (j : ℕ), by omega⟩ =
      -symmetricPowerArchimedeanExponent ν d j := by
  have hj : (j : ℕ) ≤ d := Nat.le_of_lt_succ j.isLt
  simp only [symmetricPowerArchimedeanExponent]
  push_cast [Nat.cast_sub hj]
  ring

/-- Every degree-`d` symmetric-power coefficient `d - 2j` has absolute value at most `d`. -/
theorem abs_symmetricPower_coefficient_le (d : ℕ) (j : Fin (d + 1)) :
    |(d : ℝ) - 2 * ((j : ℕ) : ℝ)| ≤ d := by
  have hj : (j : ℕ) ≤ d := Nat.le_of_lt_succ j.isLt
  have hj0 : (0 : ℝ) ≤ ((j : ℕ) : ℝ) := by positivity
  have hjd : (((j : ℕ) : ℝ)) ≤ d := by exact_mod_cast hj
  rw [abs_le]
  constructor <;> linarith

/-- The locus where every exponent of the degree-`d` packet lies in `(-1/2, 1/2)`. -/
def genericUnitarySymPowerLocus (d : ℕ) : Set ℝ :=
  {ν | ∀ j : Fin (d + 1), |symmetricPowerArchimedeanExponent ν d j| < 1 / 2}

/-- Exact generic-unitary locus in every positive degree. -/
theorem mem_genericUnitarySymPowerLocus_succ_iff (ν : ℝ) (d : ℕ) :
    ν ∈ genericUnitarySymPowerLocus (d + 1) ↔
      |ν| < (1 / 2 : ℝ) / (d + 1) := by
  have hD0 : (0 : ℝ) < (d + 1 : ℕ) := by positivity
  constructor
  · intro h
    have hzero := h ⟨0, Nat.zero_lt_succ (d + 1)⟩
    rw [symmetricPowerArchimedeanExponent_zero, abs_mul,
      abs_of_nonneg (Nat.cast_nonneg (d + 1))] at hzero
    rw [mul_comm] at hzero
    have hr : |ν| < (1 / 2 : ℝ) / (((d + 1 : ℕ) : ℝ)) :=
      (lt_div_iff₀ hD0).2 hzero
    simpa only [Nat.cast_add, Nat.cast_one] using hr
  · intro h j
    rw [symmetricPowerArchimedeanExponent, abs_mul]
    have hcoeff := abs_symmetricPower_coefficient_le (d + 1) j
    calc
      |((d + 1 : ℕ) : ℝ) - 2 * ((j : ℕ) : ℝ)| * |ν| ≤
          ((d + 1 : ℕ) : ℝ) * |ν| :=
        mul_le_mul_of_nonneg_right hcoeff (abs_nonneg ν)
      _ < ((d + 1 : ℕ) : ℝ) * ((1 / 2 : ℝ) / (d + 1)) :=
        mul_lt_mul_of_pos_left h hD0
      _ = 1 / 2 := by
        rw [Nat.cast_add, Nat.cast_one]
        field_simp

/-- The positive-degree generic-unitary locus is the expected symmetric open interval. -/
theorem genericUnitarySymPowerLocus_succ (d : ℕ) :
    genericUnitarySymPowerLocus (d + 1) =
      Set.Ioo (-((1 / 2 : ℝ) / (d + 1))) ((1 / 2 : ℝ) / (d + 1)) := by
  ext ν
  rw [mem_genericUnitarySymPowerLocus_succ_iff]
  exact abs_lt

/-- Requiring the generic-unitary strip for symmetric powers of every positive degree forces the
original real exponent to vanish. -/
theorem all_degree_genericUnitarySymPowerLocus :
    {ν : ℝ | ∀ d : ℕ, ν ∈ genericUnitarySymPowerLocus (d + 1)} = {0} := by
  ext ν
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hν
    have habs : 0 < |ν| := abs_pos.mpr hν
    obtain ⟨d, hd⟩ := exists_nat_one_div_lt (show (0 : ℝ) < 2 * |ν| by positivity)
    have hbound := (mem_genericUnitarySymPowerLocus_succ_iff ν d).mp (h d)
    have hhalf : (1 / 2 : ℝ) / (d + 1) < |ν| := by
      have hd' : 1 / ((d + 1 : ℕ) : ℝ) < 2 * |ν| := by simpa using hd
      calc
        (1 / 2 : ℝ) / (d + 1) = (1 / ((d + 1 : ℕ) : ℝ)) / 2 := by
          rw [Nat.cast_add, Nat.cast_one]
          ring
        _ < (2 * |ν|) / 2 := div_lt_div_of_pos_right hd' (by norm_num)
        _ = |ν| := by ring
    linarith
  · intro hν
    subst ν
    intro d j
    simp [symmetricPowerArchimedeanExponent]

/-- Even symmetric-power degrees already force the original real exponent to vanish.  This avoids
any parity issue at the archimedean place in the standard amplification argument. -/
theorem all_even_degree_genericUnitarySymPowerLocus :
    {ν : ℝ | ∀ d : ℕ, ν ∈ genericUnitarySymPowerLocus (2 * (d + 1))} = {0} := by
  ext ν
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    by_contra hν
    have habs : 0 < |ν| := abs_pos.mpr hν
    obtain ⟨d, hd⟩ := exists_nat_one_div_lt (show (0 : ℝ) < 4 * |ν| by positivity)
    have hmem : ν ∈ genericUnitarySymPowerLocus ((2 * d + 1) + 1) := by
      simpa [Nat.mul_add, Nat.mul_one, Nat.add_assoc] using h d
    have hbound := (mem_genericUnitarySymPowerLocus_succ_iff ν (2 * d + 1)).mp hmem
    have hcontra : (1 / 2 : ℝ) / ((2 * d + 1 : ℕ) + 1) < |ν| := by
      have hd' : 1 / ((d + 1 : ℕ) : ℝ) < 4 * |ν| := by simpa using hd
      have hcast : (((2 * d + 1 : ℕ) : ℝ) + 1) = 2 * ((d + 1 : ℕ) : ℝ) := by
        push_cast
        ring
      rw [hcast]
      calc
        (1 / 2 : ℝ) / (2 * ((d + 1 : ℕ) : ℝ)) =
            (1 / ((d + 1 : ℕ) : ℝ)) / 4 := by ring
        _ < (4 * |ν|) / 4 := div_lt_div_of_pos_right hd' (by norm_num)
        _ = |ν| := by ring
    linarith
  · intro hν
    subst ν
    intro d j
    simp [symmetricPowerArchimedeanExponent]

/-- Eigenvalue attached to a real complementary exponent in Selberg normalization. -/
def eigenvalueOfComplementaryExponent (ν : ℝ) : ℝ :=
  1 / 4 - ν ^ (2 : ℕ)

@[simp]
theorem eigenvalueOfComplementaryExponent_zero :
    eigenvalueOfComplementaryExponent 0 = 1 / 4 := by
  simp [eigenvalueOfComplementaryExponent]

/-- The all-degree local strip locus maps to the singleton quarter eigenvalue. -/
theorem image_eigenvalue_all_degree_genericUnitary_locus :
    eigenvalueOfComplementaryExponent ''
        {ν : ℝ | ∀ d : ℕ, ν ∈ genericUnitarySymPowerLocus (d + 1)} =
      {(1 / 4 : ℝ)} := by
  rw [all_degree_genericUnitarySymPowerLocus]
  simp [eigenvalueOfComplementaryExponent]

/-- The fixed-degree generic-unitary strip gives the corresponding strict spectral lower bound. -/
theorem image_eigenvalue_genericUnitarySymPowerLocus_succ_subset (d : ℕ) :
    eigenvalueOfComplementaryExponent '' genericUnitarySymPowerLocus (d + 1) ⊆
      Set.Ioc
        (1 / 4 - ((1 / 2 : ℝ) / (d + 1)) ^ (2 : ℕ))
        (1 / 4) := by
  rintro x ⟨ν, hν, rfl⟩
  have hbound := (mem_genericUnitarySymPowerLocus_succ_iff ν d).mp hν
  have hright : (0 : ℝ) < (1 / 2 : ℝ) / (d + 1) := by positivity
  have hsq : ν ^ (2 : ℕ) < ((1 / 2 : ℝ) / (d + 1)) ^ (2 : ℕ) := by
    rw [← sq_abs ν]
    exact (sq_lt_sq₀ (abs_nonneg ν) hright.le).2 hbound
  constructor
  · simp only [eigenvalueOfComplementaryExponent]
    linarith
  · simp only [eigenvalueOfComplementaryExponent]
    nlinarith [sq_nonneg ν]

end

end GaloisForLFunctions.RHTower
