import GaloisForLFunctions.HTGeometry.RittLogDerivativeEigen
import GaloisForLFunctions.HTGeometry.RittPrefixFieldStability

/-!
# The affine jet tower of a logarithmic seed

The linearizing coordinate `τ` and its derivative are multiplicative shift coordinates, so their
ratio `v = d τ / τ` satisfies `σ v = ρ^{-1} v`, and the logarithmic derivative

`u = d v / v = d²τ / dτ − dτ / τ`

solves the *affine* equation `σ u = ρ^{-1} u − (dρ)/ρ²`.  Differentiating repeatedly turns this into
a triangular affine system: the `k`-th jet of `u` satisfies

`σ (d^[k] u) = ∑_{j ≤ k} a_{k,j} · d^[j] u + b_k`,

with diagonal coefficient `a_{k,k} = ρ^{-(k+1)}`, subdiagonal coefficient
`a_{k,k−1} = −C(k+1,2)·ρ^{-(k+2)}·dρ`, and a base constant `b_k`.

Unlike the jets of `τ`, none of the coordinates of this tower is a pure eigenvector: every level
carries a genuine inhomogeneity, and every diagonal multiplier is a negative power of the chain-rule
factor.  Both features are used by the classification of the tower.
-/

namespace GaloisForLFunctions.HTGeometry

namespace RittFrame

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

theorem dK_add (Fr : RittFrame K L) (a b : K) : Fr.dK (a + b) = Fr.dK a + Fr.dK b := by
  refine (algebraMap K L).injective ?_
  rw [map_add, ← Fr.d_base, ← Fr.d_base, ← Fr.d_base, map_add, Fr.d_add]

/-- The coefficient matrix of the affine jet tower. -/
noncomputable def logCoeff (Fr : RittFrame K L) : ℕ → ℕ → K
  | 0, 0 => Fr.ρ⁻¹
  | 0, (_ + 1) => 0
  | (k + 1), 0 => Fr.ρ⁻¹ * Fr.dK (logCoeff Fr k 0)
  | (k + 1), (j + 1) => Fr.ρ⁻¹ * (logCoeff Fr k j + Fr.dK (logCoeff Fr k (j + 1)))

/-- The base constants of the affine jet tower. -/
noncomputable def logConst (Fr : RittFrame K L) (b : K) : ℕ → K
  | 0 => b
  | (k + 1) => Fr.ρ⁻¹ * Fr.dK (logConst Fr b k)

theorem logCoeff_zero_zero (Fr : RittFrame K L) : Fr.logCoeff 0 0 = Fr.ρ⁻¹ := rfl

theorem logCoeff_zero_succ (Fr : RittFrame K L) (j : ℕ) : Fr.logCoeff 0 (j + 1) = 0 := rfl

theorem logCoeff_succ_zero (Fr : RittFrame K L) (k : ℕ) :
    Fr.logCoeff (k + 1) 0 = Fr.ρ⁻¹ * Fr.dK (Fr.logCoeff k 0) := rfl

theorem logCoeff_succ_succ (Fr : RittFrame K L) (k j : ℕ) :
    Fr.logCoeff (k + 1) (j + 1)
      = Fr.ρ⁻¹ * (Fr.logCoeff k j + Fr.dK (Fr.logCoeff k (j + 1))) := rfl

/-- Above the diagonal the coefficient matrix vanishes. -/
theorem logCoeff_eq_zero_of_lt (Fr : RittFrame K L) :
    ∀ (k j : ℕ), k < j → Fr.logCoeff k j = 0
  | 0, 0, h => absurd h (by omega)
  | 0, (_ + 1), _ => rfl
  | (k + 1), 0, h => absurd h (by omega)
  | (k + 1), (j + 1), h => by
      rw [logCoeff_succ_succ, Fr.logCoeff_eq_zero_of_lt k j (by omega),
        Fr.logCoeff_eq_zero_of_lt k (j + 1) (by omega), dK_zero Fr]
      ring

/-- The diagonal of the coefficient matrix is a negative power of the chain-rule factor. -/
theorem logCoeff_diag (Fr : RittFrame K L) : ∀ k : ℕ, Fr.logCoeff k k = (Fr.ρ ^ (k + 1))⁻¹
  | 0 => by rw [logCoeff_zero_zero]; norm_num
  | (k + 1) => by
      rw [logCoeff_succ_succ, Fr.logCoeff_diag k, Fr.logCoeff_eq_zero_of_lt k (k + 1) (by omega),
        dK_zero Fr, add_zero,
        show Fr.ρ ^ (k + 1 + 1) = Fr.ρ * Fr.ρ ^ (k + 1) by ring, mul_inv]

end RittFrame

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

namespace RittFrame

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The subdiagonal of the coefficient matrix is a nonzero multiple of the logarithmic derivative
of the chain-rule factor. -/
theorem logCoeff_subdiag (Fr : RittFrame K L) :
    ∀ k : ℕ, Fr.logCoeff (k + 1) k
      = -((((k + 2).choose 2 : ℕ) : K)) * (Fr.ρ ^ (k + 3))⁻¹ * Fr.dK Fr.ρ
  | 0 => by
      have hρ : Fr.ρ ≠ 0 := Fr.ρ_ne
      rw [logCoeff_succ_zero, logCoeff_zero_zero, Fr.dK_inv hρ]
      norm_num
      field_simp
  | (k + 1) => by
      have hρ : Fr.ρ ≠ 0 := Fr.ρ_ne
      have hpow : (Fr.ρ ^ (k + 2)) ≠ 0 := pow_ne_zero _ hρ
      have hdiag : Fr.dK ((Fr.ρ ^ (k + 2))⁻¹)
          = -(((k : K) + 2)) * (Fr.ρ ^ (k + 3))⁻¹ * Fr.dK Fr.ρ := by
        rw [Fr.dK_inv hpow,
          show (k + 2) = ((k + 1) + 1) from rfl, Fr.dK_pow_succ]
        push_cast
        field_simp
        ring
      rw [logCoeff_succ_succ, Fr.logCoeff_subdiag k, Fr.logCoeff_diag (k + 1),
        show (k + 1 + 1) = (k + 2) from rfl, hdiag,
        show ((k + 1 + 2).choose 2 : ℕ) = (k + 2).choose 2 + (k + 2) by
          rw [show (k + 1 + 2) = (k + 2) + 1 from rfl, Nat.choose_succ_succ (k + 2) 1]
          simp [Nat.choose_one_right, add_comm]]
      push_cast
      field_simp
      ring

/-- **The affine jet tower.**  The jets of a solution of `σ u = ρ^{-1} u + b` satisfy a triangular
affine system with coefficient matrix `logCoeff` and base constants `logConst`. -/
theorem sigma_affineJet (Fr : RittFrame K L) {u : L} {b : K}
    (hu : Fr.σ u = algebraMap K L Fr.ρ⁻¹ * u + algebraMap K L b) (k : ℕ) :
    Fr.σ (Fr.d^[k] u)
      = (∑ j ∈ Finset.range (k + 1), algebraMap K L (Fr.logCoeff k j) * Fr.d^[j] u)
        + algebraMap K L (Fr.logConst b k) := by
  induction k with
  | zero => simpa [logCoeff, logConst] using hu
  | succ k ih =>
      have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
      have hρ : algebraMap K L Fr.ρ ≠ 0 :=
        (map_ne_zero_iff _ (algebraMap K L).injective).mpr hρ0
      have hstep : ∀ j : ℕ, Fr.d (Fr.d^[j] u) = Fr.d^[j + 1] u := fun j =>
        (Function.iterate_succ_apply' Fr.d j u).symm
      have hchain := Fr.chain (Fr.d^[k] u)
      rw [hstep k] at hchain
      have hd : Fr.d (Fr.σ (Fr.d^[k] u))
          = (∑ j ∈ Finset.range (k + 1),
              algebraMap K L (Fr.dK (Fr.logCoeff k j)) * Fr.d^[j] u)
            + (∑ j ∈ Finset.range (k + 1),
              algebraMap K L (Fr.logCoeff k j) * Fr.d^[j + 1] u)
            + algebraMap K L (Fr.dK (Fr.logConst b k)) := by
        rw [ih, Fr.d_add, d_sum, Fr.d_base, ← Finset.sum_add_distrib]
        congr 1
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Fr.d_mul, Fr.d_base, hstep j]
      -- both sides, reindexed so that the `j = 0` term is separate
      have hleft : (∑ j ∈ Finset.range (k + 1),
            algebraMap K L (Fr.dK (Fr.logCoeff k j)) * Fr.d^[j] u)
          = (∑ i ∈ Finset.range (k + 1),
              algebraMap K L (Fr.dK (Fr.logCoeff k (i + 1))) * Fr.d^[i + 1] u)
            + algebraMap K L (Fr.dK (Fr.logCoeff k 0)) * Fr.d^[0] u := by
        rw [Finset.sum_range_succ' (fun j => algebraMap K L (Fr.dK (Fr.logCoeff k j))
          * Fr.d^[j] u) k, Finset.sum_range_succ
          (fun i => algebraMap K L (Fr.dK (Fr.logCoeff k (i + 1))) * Fr.d^[i + 1] u) k,
          Fr.logCoeff_eq_zero_of_lt k (k + 1) (by omega), dK_zero Fr, map_zero, zero_mul,
          add_zero]
      have hgoal : (∑ j ∈ Finset.range (k + 1 + 1),
            algebraMap K L (Fr.logCoeff (k + 1) j) * Fr.d^[j] u)
          = (∑ i ∈ Finset.range (k + 1),
              algebraMap K L (Fr.logCoeff (k + 1) (i + 1)) * Fr.d^[i + 1] u)
            + algebraMap K L (Fr.logCoeff (k + 1) 0) * Fr.d^[0] u :=
        Finset.sum_range_succ' (fun j => algebraMap K L (Fr.logCoeff (k + 1) j)
          * Fr.d^[j] u) (k + 1)
      rw [hgoal]
      have hcomb : (∑ i ∈ Finset.range (k + 1),
            algebraMap K L (Fr.logCoeff (k + 1) (i + 1)) * Fr.d^[i + 1] u)
          = algebraMap K L Fr.ρ⁻¹ *
            ((∑ i ∈ Finset.range (k + 1),
              algebraMap K L (Fr.dK (Fr.logCoeff k (i + 1))) * Fr.d^[i + 1] u)
              + (∑ j ∈ Finset.range (k + 1),
                algebraMap K L (Fr.logCoeff k j) * Fr.d^[j + 1] u)) := by
        rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [logCoeff_succ_succ, map_mul, map_add]
        ring
      have hzero : algebraMap K L (Fr.logCoeff (k + 1) 0) * Fr.d^[0] u
          = algebraMap K L Fr.ρ⁻¹ * (algebraMap K L (Fr.dK (Fr.logCoeff k 0)) * Fr.d^[0] u) := by
        rw [logCoeff_succ_zero, map_mul]
        ring
      have hconst : algebraMap K L (Fr.logConst b (k + 1))
          = algebraMap K L Fr.ρ⁻¹ * algebraMap K L (Fr.dK (Fr.logConst b k)) := by
        rw [logConst, map_mul]
      rw [hcomb, hzero, hconst]
      have hfinal : algebraMap K L Fr.ρ * Fr.σ (Fr.d^[k + 1] u)
          = algebraMap K L Fr.ρ *
            (algebraMap K L Fr.ρ⁻¹ *
              ((∑ i ∈ Finset.range (k + 1),
                algebraMap K L (Fr.dK (Fr.logCoeff k (i + 1))) * Fr.d^[i + 1] u)
                + (∑ j ∈ Finset.range (k + 1),
                  algebraMap K L (Fr.logCoeff k j) * Fr.d^[j + 1] u))
            + algebraMap K L Fr.ρ⁻¹ * (algebraMap K L (Fr.dK (Fr.logCoeff k 0)) * Fr.d^[0] u)
            + algebraMap K L Fr.ρ⁻¹ * algebraMap K L (Fr.dK (Fr.logConst b k))) := by
        rw [← hchain, hd, hleft, map_inv₀]
        field_simp
        ring
      exact mul_left_cancel₀ hρ hfinal

end RittFrame

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

namespace RittFrame

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- The logarithmic seed of a linearizer: the logarithmic derivative of the jet ratio. -/
noncomputable def affineLogSeed (Fr : RittFrame K L) (τ : L) : L :=
  Fr.d (Fr.d τ) / Fr.d τ - Fr.d τ / τ

/-- **The logarithmic seed solves an affine transport equation** with multiplier `ρ^{-1}` and
inhomogeneity minus the logarithmic derivative of the chain-rule factor. -/
theorem sigma_affineLogSeed (Fr : RittFrame K L) {τ : L} {q : K} (hτ : τ ≠ 0) (hdτ : Fr.d τ ≠ 0)
    (hq : q ≠ 0) (hqconst : Fr.dK q = 0) (hshift : Fr.σ τ = algebraMap K L q * τ) :
    Fr.σ (Fr.affineLogSeed τ)
      = algebraMap K L Fr.ρ⁻¹ * Fr.affineLogSeed τ
        + algebraMap K L (-(Fr.dK Fr.ρ) / Fr.ρ ^ (2 : ℕ)) := by
  have hρ0 : Fr.ρ ≠ 0 := Fr.ρ_ne
  have hρL : algebraMap K L Fr.ρ ≠ 0 :=
    (map_ne_zero_iff _ (algebraMap K L).injective).mpr hρ0
  have hqL : algebraMap K L q ≠ 0 := (map_ne_zero_iff _ (algebraMap K L).injective).mpr hq
  have hd1 := Fr.sigma_d_eq_of_shift hqconst hshift
  have hd2 := Fr.sigma_second_jet hqconst hshift
  have hdq : Fr.dK (q / Fr.ρ) = -(q * Fr.dK Fr.ρ) / Fr.ρ ^ (2 : ℕ) := by
    rw [Fr.dK_div hρ0, hqconst]
    ring
  have hdτL : Fr.σ (Fr.d τ) ≠ 0 := by
    rw [hd1]
    exact mul_ne_zero ((map_ne_zero_iff _ (algebraMap K L).injective).mpr
      (div_ne_zero hq hρ0)) hdτ
  have hτL : Fr.σ τ ≠ 0 := by
    rw [hshift]
    exact mul_ne_zero hqL hτ
  simp only [affineLogSeed]
  rw [map_sub, map_div₀, map_div₀, hd1, hd2, hshift, hdq]
  simp only [map_div₀, map_neg, map_mul, map_pow, map_inv₀]
  field_simp
  ring

end RittFrame

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

namespace RittFrame

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

/-- **Shift stability of the jet prefix field of an affine tower.** -/
theorem sigma_mem_affineJetPrefixField (Fr : RittFrame K L) {u : L} {b : K}
    (hu : Fr.σ u = algebraMap K L Fr.ρ⁻¹ * u + algebraMap K L b) (n : ℕ) :
    ∀ x ∈ Fr.jetPrefixField u n, Fr.σ x ∈ Fr.jetPrefixField u n := by
  refine Fr.sigma_mem_of_mem_adjoin ?_
  rintro x ⟨k, hk, rfl⟩
  rw [Fr.sigma_affineJet hu k]
  refine add_mem (sum_mem fun j hj => ?_) (IntermediateField.algebraMap_mem _ _)
  exact mul_mem (IntermediateField.algebraMap_mem _ _)
    (Fr.jet_mem_jetPrefixField (by simp only [Finset.mem_range] at hj; omega))

/-- The shift defect of the affine tower at level `k` lies in the previous prefix field. -/
theorem affineJet_defect_mem (Fr : RittFrame K L) {u : L} {b : K}
    (hu : Fr.σ u = algebraMap K L Fr.ρ⁻¹ * u + algebraMap K L b) (k : ℕ) :
    Fr.σ (Fr.d^[k] u) - algebraMap K L (Fr.logCoeff k k) * Fr.d^[k] u
      ∈ Fr.jetPrefixField u k := by
  rw [Fr.sigma_affineJet hu k, Finset.sum_range_succ]
  have hrw : ∀ x y z : L, x + y + z - z = x + y := fun x y z => by ring
  rw [add_right_comm, hrw]
  refine add_mem (sum_mem fun j hj => ?_) (IntermediateField.algebraMap_mem _ _)
  exact mul_mem (IntermediateField.algebraMap_mem _ _)
    (Fr.jet_mem_jetPrefixField (by simpa only [Finset.mem_range] using hj))

end RittFrame

end GaloisForLFunctions.HTGeometry
