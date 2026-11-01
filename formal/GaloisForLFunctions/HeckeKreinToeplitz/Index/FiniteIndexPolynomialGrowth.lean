import GaloisForLFunctions.HeckeKreinToeplitz.Index.CyclicKernelFilter
import GaloisForLFunctions.HeckeKreinToeplitz.Index.HermitianCyclicGrowth
import GaloisForLFunctions.HTGeometry.PolynomialTwistedDifferences

/-!
# Polynomial cyclic growth from finite negative index

Subexponential cyclic growth excludes nonunitary eigenvalues in the
completed column representation. A unitary second-difference filter then
lowers the negative index. Induction and two discrete integrations per
negative square give degree at most twice the index, on any group.
-/

noncomputable section
set_option autoImplicit false
open Complex
open scoped ComplexConjugate
open GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HeckeKreinToeplitz

private theorem cyclicKernelFilter_subexponential {k : Multiplicative ℤ → ℂ}
    (hsub : HasSubexponentialIntegerGrowth (fun z => k (Multiplicative.ofAdd z))) (a : ℂ) :
    HasSubexponentialIntegerGrowth (fun z => cyclicKernelFilter k a (Multiplicative.ofAdd z)) := by
  have hp := (hsub.translate 1).smul (conj a)
  have hn := (hsub.translate (-1)).smul a
  have h := ((hsub.smul (2 : ℂ)).sub hn).sub hp
  simpa only [cyclicKernelFilter, smul_eq_mul, add_comm 1] using h

private theorem cyclicKernelFilter_second_difference (k : Multiplicative ℤ → ℂ)
    {a : ℂ} (ha : ‖a‖ = 1) (n : ℕ) :
    cyclicKernelFilter k a (Multiplicative.ofAdd ((n + 1 : ℕ) : ℤ)) =
      -conj a * (k (Multiplicative.ofAdd ((n + 2 : ℕ) : ℤ)) -
        a * k (Multiplicative.ofAdd ((n + 1 : ℕ) : ℤ)) -
        a * (k (Multiplicative.ofAdd ((n + 1 : ℕ) : ℤ)) -
          a * k (Multiplicative.ofAdd (n : ℤ)))) := by
  have hl : (Multiplicative.ofAdd 1)⁻¹ * Multiplicative.ofAdd ((n + 1 : ℕ) : ℤ) =
      Multiplicative.ofAdd (n : ℤ) := by
    change Multiplicative.ofAdd (-1 + ((n + 1 : ℕ) : ℤ)) = Multiplicative.ofAdd (n : ℤ)
    congr 1
    omega
  have hr : Multiplicative.ofAdd ((n + 1 : ℕ) : ℤ) * Multiplicative.ofAdd 1 =
      Multiplicative.ofAdd ((n + 2 : ℕ) : ℤ) := by
    change Multiplicative.ofAdd (((n + 1 : ℕ) : ℤ) + 1) = _
    congr 1
    omega
  rw [cyclicKernelFilter, hl, hr]
  have hc := conj_mul_self_of_norm_eq_one ha
  linear_combination (a * k (Multiplicative.ofAdd (n : ℤ)) -
    2 * k (Multiplicative.ofAdd ((n + 1 : ℕ) : ℤ))) * hc

private theorem polynomial_bound_of_posDef (k : Multiplicative ℤ → ℂ)
    (hk : IsPosDefKernel k) (d : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ‖k (Multiplicative.ofAdd (n : ℤ))‖ ≤ C * ((n : ℝ) + 1) ^ d := by
  have hC : 0 ≤ (k 1).re := (norm_nonneg _).trans (hk.norm_le 1)
  refine ⟨(k 1).re, hC, fun n => (hk.norm_le _).trans ?_⟩
  have hp : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ d := by
    simpa only [one_pow] using pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1)
      (by linarith only [Nat.cast_nonneg n] : (1 : ℝ) ≤ n + 1) d
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hp hC

/-- A subexponential integer kernel of negative index at most `r` has growth degree at most `2r`. -/
theorem polynomial_growth_of_finite_index_integer {r : ℕ} {k : Multiplicative ℤ → ℂ}
    (hk : IsHermKernel k) (hi : negIndex k ≤ r)
    (hsub : HasSubexponentialIntegerGrowth (fun z => k (Multiplicative.ofAdd z))) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ,
      ‖k (Multiplicative.ofAdd (n : ℤ))‖ ≤ C * ((n : ℝ) + 1) ^ (2 * r) := by
  induction r generalizing k with
  | zero =>
    have hp : IsPosDefKernel k := (isPosDefKernel_iff hk).mpr (by
      simpa only [Nat.cast_zero, nonpos_iff_eq_zero] using hi)
    exact polynomial_bound_of_posDef k hp 0
  | succ r ih =>
    rcases isPosDef_or_exists_unitary_cyclic_filter hk (by
      simpa only [Nat.cast_add, Nat.cast_one] using hi) hsub with hp | ⟨a, ha, hq, hqi⟩
    · exact polynomial_bound_of_posDef k hp (2 * (r + 1))
    · obtain ⟨C, hC, hb⟩ := ih hq hqi (cyclicKernelFilter_subexponential hsub a)
      have hd (n : ℕ) :
          ‖k (Multiplicative.ofAdd ((n + 2 : ℕ) : ℤ)) -
            a * k (Multiplicative.ofAdd ((n + 1 : ℕ) : ℤ)) -
            a * (k (Multiplicative.ofAdd ((n + 1 : ℕ) : ℤ)) -
              a * k (Multiplicative.ofAdd (n : ℤ)))‖ ≤
            (C * 2 ^ (2 * r)) * ((n : ℝ) + 1) ^ (2 * r) := by
        have he := cyclicKernelFilter_second_difference k ha n
        have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
        have hp : ((n : ℝ) + 2) ^ (2 * r) ≤ (2 * ((n : ℝ) + 1)) ^ (2 * r) :=
          pow_le_pow_left₀ (by linarith only [hn]) (by linarith only [hn]) _
        calc
          _ = ‖cyclicKernelFilter k a (Multiplicative.ofAdd ((n + 1 : ℕ) : ℤ))‖ := by
            rw [he, norm_mul, norm_neg, Complex.norm_conj, ha, one_mul]
          _ ≤ C * (((n + 1 : ℕ) : ℝ) + 1) ^ (2 * r) := hb (n + 1)
          _ = C * ((n : ℝ) + 2) ^ (2 * r) := by push_cast; ring
          _ ≤ C * (2 * ((n : ℝ) + 1)) ^ (2 * r) := mul_le_mul_of_nonneg_left hp hC
          _ = _ := by rw [mul_pow, mul_assoc]
      obtain ⟨D, hD, hd⟩ := polynomial_bound_of_unitary_second_difference
        (fun n => k (Multiplicative.ofAdd (n : ℤ))) ha
        (mul_nonneg hC (pow_nonneg (by norm_num) _)) hd
      refine ⟨D, hD, fun n => ?_⟩
      simpa only [Nat.mul_add, Nat.mul_one] using hd n

/-- Finite negative index upgrades cyclic subexponential growth to a degree bound on every group. -/
theorem cyclic_polynomial_growth_of_finite_index {G : Type*} [Group G]
    {k : G → ℂ} {r : ℕ} (hk : IsHermKernel k) (hi : negIndex k ≤ r)
    (hsub : ∀ (g : G) (ε : ℝ), 0 < ε →
      ∃ C : ℝ, ∀ n : ℕ, ‖k (g ^ n)‖ ≤ C * Real.exp (ε * n)) (g : G) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, ‖k (g ^ n)‖ ≤ C * ((n : ℝ) + 1) ^ (2 * r) := by
  let f : Multiplicative ℤ →* G := zpowersHom G g
  let q : Multiplicative ℤ → ℂ := k ∘ f
  have hq : IsHermKernel q := hk.comp f
  have hqi : negIndex q ≤ r := (negIndex_comp_le k f).trans hi
  have he (n : ℕ) : q (Multiplicative.ofAdd (n : ℤ)) = k (g ^ n) := by
    change k (g ^ (n : ℤ)) = _
    rw [zpow_natCast]
  have hqs : HasSubexponentialIntegerGrowth (fun z => q (Multiplicative.ofAdd z)) := by
    apply integerGrowth_of_hermitian_natural_bound hq
    intro ε hε
    obtain ⟨C, hC⟩ := hsub g ε hε
    exact ⟨C, fun n => by rw [he]; exact hC n⟩
  obtain ⟨C, hC, hb⟩ := polynomial_growth_of_finite_index_integer hq hqi hqs
  exact ⟨C, hC, fun n => by rw [← he]; exact hb n⟩

#print axioms polynomial_growth_of_finite_index_integer
#print axioms cyclic_polynomial_growth_of_finite_index

end GaloisForLFunctions.HeckeKreinToeplitz
