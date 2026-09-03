import GaloisForLFunctions.HTGeometry.GenericJetAlgebra
import GaloisForLFunctions.HTGeometry.ReciprocalFiberEquation
import GaloisForLFunctions.HTGeometry.TailParameterChange

/-!
# Exact power-series inverse of the generic reciprocal jet

The recursively defined generic reciprocal coefficients form the full formal inverse of the
generic raw series, not merely an inverse modulo a finite horizon.  Applying the closed reciprocal
fibre equation then expresses the top reciprocal coefficient in the triangular tail coordinates.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

/-- Reindex a natural-number antidiagonal sum by its first coordinate. -/
theorem sum_antidiagonal_nat_eq_range {M : Type*} [AddCommMonoid M]
    (f : ℕ → ℕ → M) (n : ℕ) :
    ∑ p ∈ (Finset.HasAntidiagonal.antidiagonal n : Finset (ℕ × ℕ)), f p.1 p.2 =
      ∑ i ∈ Finset.range (n + 1), f i (n - i) := by
  refine Finset.sum_bij (fun p _ => p.1) ?_ ?_ ?_ ?_
  · intro p hp
    rw [Finset.mem_range]
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    omega
  · intro p hp q hq hpq
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp hq
    apply Prod.ext hpq
    omega
  · intro i hi
    refine ⟨(i, n - i), ?_, rfl⟩
    rw [Finset.HasAntidiagonal.mem_antidiagonal]
    rw [Finset.mem_range] at hi
    omega
  · intro p hp
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    congr 2
    omega

/-- Formal series of the generic raw coefficients, extended by zero past the horizon. -/
noncomputable def genericRawPowerSeries
    (K : Type*) [Field K] (N : ℕ) : PowerSeries (genericJetAlgebra K N) :=
  PowerSeries.mk (genericRaw K N)

/-- Formal series of all recursively defined generic reciprocal coefficients. -/
noncomputable def genericRecipPowerSeries
    (K : Type*) [Field K] (N : ℕ) : PowerSeries (genericJetAlgebra K N) :=
  PowerSeries.mk (genericRecip K N)

/-- The generic reciprocal recursion is the exact formal inverse of the generic raw series. -/
theorem genericRawPowerSeries_mul_genericRecipPowerSeries
    (K : Type*) [Field K] (N : ℕ) :
    genericRawPowerSeries K N * genericRecipPowerSeries K N = 1 := by
  apply PowerSeries.ext
  intro k
  rw [PowerSeries.coeff_mul]
  rw [sum_antidiagonal_nat_eq_range
    (fun i j => PowerSeries.coeff i (genericRawPowerSeries K N) *
      PowerSeries.coeff j (genericRecipPowerSeries K N)) k]
  rw [genericRawPowerSeries, genericRecipPowerSeries]
  simp only [PowerSeries.coeff_mk]
  rcases k with _ | k
  · rw [Finset.sum_range_one, Nat.zero_sub, genericRecip,
      genericRaw_zero_mul_inv, PowerSeries.coeff_one, if_pos rfl]
  · rw [Finset.sum_range_succ']
    simp only [Nat.sub_zero]
    have hsum :
        (∑ x ∈ Finset.range (k + 1),
            genericRaw K N (x + 1) * genericRecip K N (k + 1 - (x + 1))) =
          ∑ x ∈ Finset.range (k + 1),
            genericRaw K N (x + 1) * genericRecip K N (k - x) := by
      apply Finset.sum_congr rfl
      intro x hx
      congr 2
      omega
    rw [hsum, genericRecip]
    have hmul := genericRaw_zero_mul_inv K N
    rw [PowerSeries.coeff_one, if_neg (by omega)]
    calc
      (∑ x ∈ Finset.range (k + 1),
          genericRaw K N (x + 1) * genericRecip K N (k - x)) +
          genericRaw K N 0 *
            (-genericInv K N * ∑ x ∈ Finset.range (k + 1),
              genericRaw K N (x + 1) * genericRecip K N (k - x))
          = -(genericRaw K N 0 * genericInv K N) *
              (∑ x ∈ Finset.range (k + 1),
                genericRaw K N (x + 1) * genericRecip K N (k - x)) +
              ∑ x ∈ Finset.range (k + 1),
                genericRaw K N (x + 1) * genericRecip K N (k - x) := by ring
      _ = 0 := by rw [hmul]; ring

/-- Generic tail polynomial whose coefficient of degree `i` is the raw coordinate of degree
`i + 1`. -/
noncomputable def genericTailPolynomial
    (K : Type*) [Field K] (N : ℕ) : Polynomial (genericJetAlgebra K N) :=
  (tailPoly K N).map
    (MvPolynomial.aeval (fun i : Fin N => genericRaw K N ((i : ℕ) + 1))).toRingHom

theorem genericTailPolynomial_coeff
    (K : Type*) [Field K] (N j : ℕ) :
    (genericTailPolynomial K N).coeff j =
      if _h : j < N then genericRaw K N (j + 1) else 0 := by
  rw [genericTailPolynomial, Polynomial.coeff_map, coeff_tailPoly]
  split_ifs
  · simp
  · rw [map_zero]

/-- The raw generic series is its constant term plus `X` times the generic tail polynomial. -/
theorem genericRawPowerSeries_eq_const_add_X_mul_tail
    (K : Type*) [Field K] (N : ℕ) :
    genericRawPowerSeries K N =
      (PowerSeries.C (genericRaw K N 0) : PowerSeries (genericJetAlgebra K N)) +
        PowerSeries.X * (genericTailPolynomial K N : PowerSeries (genericJetAlgebra K N)) := by
  apply PowerSeries.ext
  intro k
  rw [genericRawPowerSeries, PowerSeries.coeff_mk, map_add, PowerSeries.coeff_C,
    PowerSeries.coeff_mul]
  rw [sum_antidiagonal_nat_eq_range
    (fun i j => PowerSeries.coeff i (PowerSeries.X : PowerSeries (genericJetAlgebra K N)) *
      PowerSeries.coeff j (genericTailPolynomial K N :
        PowerSeries (genericJetAlgebra K N))) k]
  rcases k with _ | k
  · simp [PowerSeries.coeff_X]
  · rw [Finset.sum_eq_single 1]
    · rw [PowerSeries.coeff_X, if_pos rfl, one_mul, Polynomial.coeff_coe,
        genericTailPolynomial_coeff]
      simp only [Nat.succ_sub_succ_eq_sub, Nat.sub_zero]
      by_cases hk : k < N
      · rw [dif_pos hk, if_neg (by omega), zero_add]
      · rw [dif_neg hk, if_neg (by omega), zero_add,
          genericRaw, dif_neg (by omega)]
    · intro b hb hb1
      rw [PowerSeries.coeff_X, if_neg hb1, zero_mul]
    · intro h1
      exact (h1 (by simp)).elim

/-- Closed top reciprocal-coefficient equation in generic tail-polynomial coordinates. -/
theorem genericRecip_mul_pow_eq_tailCoeff_sum
    (K : Type*) [Field K] (N : ℕ) (hN : 0 < N) :
    genericRecip K N N * genericRaw K N 0 ^ (N + 1) =
      ∑ j ∈ Finset.range N,
        (-1 : genericJetAlgebra K N) ^ (N - j) *
          (genericTailPolynomial K N ^ (N - j)).coeff j *
          genericRaw K N 0 ^ j := by
  simpa [genericRecipPowerSeries] using
    coeff_mul_pow_eq_polynomial_tail_sum
      (genericRaw_zero_mul_inv K N)
      (genericTailPolynomial K N)
      (genericRecipPowerSeries K N)
      (by
        rw [← genericRawPowerSeries_eq_const_add_X_mul_tail]
        exact genericRawPowerSeries_mul_genericRecipPowerSeries K N)
      hN

/-- Fin-indexed form of the closed generic reciprocal-coefficient equation. -/
theorem genericRecip_mul_pow_eq_tailCoeff_fin_sum
    (K : Type*) [Field K] (N : ℕ) (hN : 0 < N) :
    genericRecip K N N * genericRaw K N 0 ^ (N + 1) =
      ∑ j : Fin N,
        (-1 : genericJetAlgebra K N) ^ (N - (j : ℕ)) *
          (genericTailPolynomial K N ^ (N - (j : ℕ))).coeff (j : ℕ) *
          genericRaw K N 0 ^ (j : ℕ) := by
  calc
    _ = ∑ j ∈ Finset.range N,
        (-1 : genericJetAlgebra K N) ^ (N - j) *
          (genericTailPolynomial K N ^ (N - j)).coeff j *
          genericRaw K N 0 ^ j :=
      genericRecip_mul_pow_eq_tailCoeff_sum K N hN
    _ = _ := (Fin.sum_univ_eq_sum_range
      (fun j : ℕ =>
        (-1 : genericJetAlgebra K N) ^ (N - j) *
          (genericTailPolynomial K N ^ (N - j)).coeff j *
          genericRaw K N 0 ^ j) N).symm

/-- Generic tail-polynomial power coefficients are evaluations of the triangular tail
coordinates. -/
theorem genericTailPolynomial_pow_coeff_eq_aeval_tailCoeff
    (K : Type*) [Field K] (N : ℕ) (j : Fin N) :
    (genericTailPolynomial K N ^ (N - (j : ℕ))).coeff (j : ℕ) =
      MvPolynomial.aeval (fun i : Fin N => genericRaw K N ((i : ℕ) + 1))
        (tailCoeff K N j) := by
  rw [genericTailPolynomial, ← Polynomial.map_pow, Polynomial.coeff_map, tailCoeff]
  rfl

/-- Specializing the generic identity to any truncated inverse pair gives the closed top
coefficient equation in evaluated tail coordinates. -/
theorem coeff_mul_pow_eq_aeval_tailCoeff_of_dvd
    {K M : Type*} [Field K] [CommRing M] [Algebra K M]
    (N : ℕ) (hN : 0 < N) {Z W : M[X]}
    (hZW : (X : M[X]) ^ (N + 1) ∣ Z * W - 1)
    (hunit : IsUnit (Z.coeff 0)) :
    W.coeff N * Z.coeff 0 ^ (N + 1) =
      ∑ j : Fin N,
        (-1 : M) ^ (N - (j : ℕ)) *
          MvPolynomial.aeval (fun i : Fin N => Z.coeff ((i : ℕ) + 1))
            (tailCoeff K N j) *
          Z.coeff 0 ^ (j : ℕ) := by
  let a : Fin (N + 1) → M := fun j => Z.coeff (j : ℕ)
  have hu : IsUnit (a 0) := by simpa [a] using hunit
  let φ : genericJetAlgebra K N →+* M := jetLift a hu
  have hhom :
      (jetLiftₐ a hu).comp
          (MvPolynomial.aeval
            (fun i : Fin N => genericRaw K N ((i : ℕ) + 1))) =
        MvPolynomial.aeval (fun i : Fin N => Z.coeff ((i : ℕ) + 1)) := by
    apply MvPolynomial.algHom_ext
    intro i
    rw [AlgHom.comp_apply, MvPolynomial.aeval_X, MvPolynomial.aeval_X,
      jetLiftₐ_apply, jetLift_genericRaw a hu (by omega)]
  have htail (j : Fin N) :
      φ ((genericTailPolynomial K N ^ (N - (j : ℕ))).coeff (j : ℕ)) =
        MvPolynomial.aeval (fun i : Fin N => Z.coeff ((i : ℕ) + 1))
          (tailCoeff K N j) := by
    rw [genericTailPolynomial_pow_coeff_eq_aeval_tailCoeff]
    change (jetLiftₐ a hu)
        (MvPolynomial.aeval (fun i : Fin N => genericRaw K N ((i : ℕ) + 1))
          (tailCoeff K N j)) = _
    exact DFunLike.congr_fun hhom (tailCoeff K N j)
  have hclosed := congrArg φ (genericRecip_mul_pow_eq_tailCoeff_fin_sum K N hN)
  rw [map_mul, map_pow,
    jetLift_genericRecip hZW hunit N (le_refl N),
    jetLift_genericRaw a hu (by omega : 0 < N + 1), map_sum] at hclosed
  dsimp only [a] at hclosed
  have hraw0 : φ (genericRaw K N 0) = Z.coeff 0 := by
    exact jetLift_genericRaw a hu (by omega : 0 < N + 1)
  simpa only [map_mul, map_pow, map_neg, map_one, htail, hraw0] using hclosed

end GaloisForLFunctions.HTGeometry
