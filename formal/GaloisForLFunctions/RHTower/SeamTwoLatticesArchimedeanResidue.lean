import GaloisForLFunctions.HTGeometry.MultiplierDichotomyDegreeObstruction
import GaloisForLFunctions.RHTower.BohrGeneratorAxisMode
import GaloisForLFunctions.RHTower.SeamDivisionSourceSplit

/-!
# The seam on two lattices: `∂_s` is a prime relation on the spectral lattice and a new
generator on the CC-class lattice
-/

namespace GaloisForLFunctions.SeamTwoLattices

open Complex GaloisForLFunctions GaloisForLFunctions.OrbitBalanceComplete
open GaloisForLFunctions.MultiplierDichotomyComplete

noncomputable section

/-! ## (L2) The CC class is a subgroup of the multiplier group -/

theorem isCC_mul {a b : RatFunc ℂ} (ha : IsCC a) (hb : IsCC b) : IsCC (a * b) := by
  obtain ⟨c, g, hc, hg, rfl⟩ := ha
  obtain ⟨d, h, hd, hh, rfl⟩ := hb
  refine ⟨c * d, g * h, mul_ne_zero hc hd, mul_ne_zero hg hh, ?_⟩
  rw [map_mul, map_mul]
  field_simp

theorem isCC_inv {a : RatFunc ℂ} (ha : IsCC a) : IsCC a⁻¹ := by
  obtain ⟨c, g, hc, hg, rfl⟩ := ha
  refine ⟨c⁻¹, g⁻¹, inv_ne_zero hc, inv_ne_zero hg, ?_⟩
  rw [map_inv₀, map_inv₀]
  field_simp

theorem isCC_one : IsCC (1 : RatFunc ℂ) := by
  refine ⟨1, 1, one_ne_zero, one_ne_zero, ?_⟩
  rw [map_one, map_one, div_one, mul_one]

theorem isCC_pow {a : RatFunc ℂ} (ha : IsCC a) : ∀ n : ℕ, IsCC (a ^ n)
  | 0 => by simpa using isCC_one
  | (n + 1) => by
      rw [pow_succ]
      exact isCC_mul (isCC_pow ha n) ha

theorem isCC_zpow {a : RatFunc ℂ} (ha : IsCC a) (k : ℤ) : IsCC (a ^ k) := by
  rcases k with n | n
  · rw [Int.ofNat_eq_natCast, zpow_natCast]
    exact isCC_pow ha n
  · rw [zpow_negSucc]
    exact isCC_inv (isCC_pow ha (n + 1))

theorem isCC_finsetProd {ι : Type*} (S : Finset ι) (f : ι → RatFunc ℂ)
    (hf : ∀ i ∈ S, IsCC (f i)) : IsCC (∏ i ∈ S, f i) := by
  classical
  induction S using Finset.induction with
  | empty => simpa using isCC_one
  | insert i S hi ih =>
      rw [Finset.prod_insert hi]
      exact isCC_mul (hf i (Finset.mem_insert_self i S))
        (ih fun j hj => hf j (Finset.mem_insert_of_mem hj))

end

end GaloisForLFunctions.SeamTwoLattices

namespace GaloisForLFunctions.SeamTwoLattices

open Complex GaloisForLFunctions GaloisForLFunctions.OrbitBalanceComplete
open GaloisForLFunctions.MultiplierDichotomyComplete

noncomputable section

/-! ## The archimedean multiplier -/

/-- The archimedean shift multiplier `a(s) = s/(2π)` of the `Γ_ℝ`-recurrence. -/
def gammaMultiplier : RatFunc ℂ := RatFunc.C (1 / (2 * (Real.pi : ℂ))) * RatFunc.X

theorem twoPi_ne_zero : (2 * (Real.pi : ℂ)) ≠ 0 := by
  refine mul_ne_zero two_ne_zero ?_
  exact_mod_cast Real.pi_ne_zero

/-- **The `Γ_ℝ`-recurrence.**  `Γ_ℝ(s+2) = (s/2π)·Γ_ℝ(s)`: the archimedean place is a rank-one
difference module whose multiplier is the non-constant polynomial `s/2π`. -/
theorem GammaR_recurrence {s : ℂ} (hs : s ≠ 0) :
    Complex.Gammaℝ (s + 2) = (s / (2 * (Real.pi : ℂ))) * Complex.Gammaℝ s := by
  have hpi : (Real.pi : ℂ) ≠ 0 := by exact_mod_cast Real.pi_ne_zero
  have hhalf : s / 2 ≠ 0 := div_ne_zero hs two_ne_zero
  rw [Complex.Gammaℝ_def, Complex.Gammaℝ_def,
    show (s + 2) / 2 = s / 2 + 1 by ring, Complex.Gamma_add_one _ hhalf,
    show -(s + 2) / 2 = -s / 2 + (-1 : ℂ) by ring, Complex.cpow_add _ _ hpi,
    Complex.cpow_neg_one]
  field_simp

theorem intDegree_ratFuncC (c : ℂ) : (RatFunc.C c : RatFunc ℂ).intDegree = 0 :=
  MultiplierDichotomyComplete.intDegree_ratFuncC c

theorem intDegree_gammaMultiplier : gammaMultiplier.intDegree = 1 := by
  have hc : (RatFunc.C (1 / (2 * (Real.pi : ℂ))) : RatFunc ℂ) ≠ 0 := by
    simp
  have hX : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  rw [gammaMultiplier, RatFunc.intDegree_mul hc hX, intDegree_ratFuncC,
    MultiplierDichotomyComplete.intDegree_ratFuncX, zero_add]

/-- **The archimedean multiplier is not constant-up-to-coboundary.** -/
theorem not_isCC_gammaMultiplier : ¬ IsCC gammaMultiplier := by
  refine not_isCC_of_intDegree_ne_zero ?_
  rw [intDegree_gammaMultiplier]
  exact one_ne_zero

/-- **The lift defect.**  The archimedean class is not any finite product of powers of prime
(constant) multiplier classes: the product-formula relation available on the spectral lattice has
no counterpart on the multiplier-class lattice. -/
theorem gammaMultiplier_ne_prime_product {ι : Type*} (S : Finset ι) (m : ι → ℂ)
    (hm : ∀ i ∈ S, m i ≠ 0) (k : ι → ℤ) :
    gammaMultiplier ≠ ∏ i ∈ S, (RatFunc.C (m i) : RatFunc ℂ) ^ (k i) := by
  intro heq
  refine not_isCC_gammaMultiplier ?_
  rw [heq]
  exact isCC_finsetProd S _ fun i hi => isCC_zpow (isCC_ratFuncC (hm i hi)) (k i)

end

end GaloisForLFunctions.SeamTwoLattices

namespace GaloisForLFunctions.SeamTwoLattices

open Complex GaloisForLFunctions GaloisForLFunctions.OrbitBalanceComplete
open GaloisForLFunctions.MultiplierDichotomyComplete GaloisForLFunctions.BohrGeneratorAxis

noncomputable section

/-! ## (L1) The spectral lattice -/

/-- **The archimedean eigenvalue is an integer combination of the prime-log eigenvalues.** -/
theorem archimedean_eigenvalue_in_prime_span (m : PrimeMode) :
    dsMult m = -∑ p ∈ m.support, ((m p : ℤ) : ℂ) * ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) := by
  rw [dsMult_eq_neg_sum m]
  congr 1
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [thetaMult]
  ring

/-- **The eigenvalue is `−log n` for the positive rational `n = ∏ p^{m_p}`.** -/
theorem prime_log_sum_eq_log_prod (m : Nat.Primes →₀ ℕ) :
    ∑ p ∈ m.support, ((m p : ℕ) : ℝ) * Real.log ((p : ℕ) : ℝ)
      = Real.log (∏ p ∈ m.support, (((p : ℕ) : ℝ)) ^ (m p)) := by
  rw [Real.log_prod]
  · refine Finset.sum_congr rfl fun p _ => ?_
    rw [Real.log_pow]
  · intro p _
    have hp : 0 < ((p : ℕ) : ℝ) := by exact_mod_cast p.2.pos
    positivity

/-! ## The settlement -/

/-- **The two-lattice settlement.**

On the spectral (eigenvalue) lattice the archimedean generator is exactly the log-weighted sum of
the prime Euler operators — a relation, adding no new direction.  On the multiplier-class (CC)
lattice the archimedean shift is not in the group generated by the prime shifts, because CC is a
subgroup, every prime multiplier is CC, and the `Γ_ℝ`-recurrence multiplier `s/2π` is not.  The
discrepancy between the two readings is carried by the archimedean residue `−½logπ + ½ψ(s/2)`. -/
theorem seam_two_lattices_settlement :
    (∀ m : PrimeMode,
        dsOp (mode m) = -∑ p ∈ m.support, ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ) • thetaOp p (mode m)) ∧
      (∀ m : PrimeMode,
        dsMult m = -∑ p ∈ m.support, ((m p : ℤ) : ℂ) * ((Real.log ((p : ℕ) : ℝ) : ℝ) : ℂ)) ∧
      (∀ c : ℂ, c ≠ 0 → IsCC (RatFunc.C c)) ∧
      (∀ a b : RatFunc ℂ, IsCC a → IsCC b → IsCC (a * b)) ∧
      (∀ a : RatFunc ℂ, IsCC a → IsCC a⁻¹) ∧
      ¬ IsCC gammaMultiplier ∧
      (∀ (ι : Type) (S : Finset ι) (m : ι → ℂ), (∀ i ∈ S, m i ≠ 0) → ∀ k : ι → ℤ,
        gammaMultiplier ≠ ∏ i ∈ S, (RatFunc.C (m i) : RatFunc ℂ) ^ (k i)) ∧
      (∀ s : ℂ, (∀ n : ℕ, s / 2 ≠ -(n : ℂ)) →
        logDeriv Complex.Gammaℝ s
          = -((Real.log Real.pi : ℝ) : ℂ) / 2 + Complex.digamma (s / 2) / 2) :=
  ⟨dsOp_mode_eq_neg_sum, archimedean_eigenvalue_in_prime_span,
    fun _ hc => isCC_ratFuncC hc, fun _ _ ha hb => isCC_mul ha hb,
    fun _ ha => isCC_inv ha, not_isCC_gammaMultiplier,
    fun _ S m hm k => gammaMultiplier_ne_prime_product S m hm k,
    fun s hs => BohrGeneratorAxis.logDeriv_GammaR s hs⟩

end

end GaloisForLFunctions.SeamTwoLattices

namespace GaloisForLFunctions.SeamTwoLattices

open Complex GaloisForLFunctions GaloisForLFunctions.OrbitBalanceComplete
open GaloisForLFunctions.MultiplierDichotomyComplete

noncomputable section

/-! ## The orbit-degree reading of the two lattices -/

theorem ratOrder_gammaMultiplier (c : ℂ) :
    HTGeometry.ratOrder gammaMultiplier c
      = HTGeometry.ratOrder (RatFunc.X : RatFunc ℂ) c := by
  have hc : (RatFunc.C (1 / (2 * (Real.pi : ℂ))) : RatFunc ℂ) ≠ 0 := by simp
  have hX : (RatFunc.X : RatFunc ℂ) ≠ 0 := RatFunc.X_ne_zero
  rw [gammaMultiplier, HTGeometry.ratOrder_mul hc hX, HTGeometry.ratOrder_C, zero_add]

/-- **The archimedean multiplier is orbit-unbalanced on the single orbit `ℤ`.** -/
theorem orbitDegree_gammaMultiplier_zero :
    OrbitBalanceComplete.orbitDegree gammaMultiplier 0 = 1 := by
  rw [← OrbitBalanceComplete.orbitDegree_ratFuncX_zero, OrbitBalanceComplete.orbitDegree,
    OrbitBalanceComplete.orbitDegree]
  exact finsum_congr fun k => ratOrder_gammaMultiplier _

/-- **Every constant (prime-lane) multiplier is orbit-balanced on every orbit.** -/
theorem orbitDegree_constant (c : ℂ) (β : ℂ) :
    OrbitBalanceComplete.orbitDegree (RatFunc.C c) β = 0 := by
  rw [OrbitBalanceComplete.orbitDegree]
  refine finsum_eq_zero_of_forall_eq_zero fun k => ?_
  exact HTGeometry.ratOrder_C c _

/-- **The lift defect in orbit-degree coordinates.**  Constant multipliers are balanced on every
orbit; the archimedean multiplier carries degree `+1` on the orbit of `0`. -/
theorem two_lattice_orbitDegree_separation :
    (∀ c β : ℂ, OrbitBalanceComplete.orbitDegree (RatFunc.C c) β = 0) ∧
      OrbitBalanceComplete.orbitDegree gammaMultiplier 0 = 1 :=
  ⟨orbitDegree_constant, orbitDegree_gammaMultiplier_zero⟩

end

end GaloisForLFunctions.SeamTwoLattices
