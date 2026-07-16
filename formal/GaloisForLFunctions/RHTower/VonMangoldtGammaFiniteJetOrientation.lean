import GaloisForLFunctions.RHTower.VonMangoldtGammaFiniteApertureOrientation

/-!
# Full finite-aperture jet orientation of the von Mangoldt--Gamma anomaly

The singleton all-coordinate orientation is supplied by `VonMangoldtGammaOrientedAnomaly`.
This file proves the missing aggregation theorem: every coordinate of the actual nonempty finite
von Mangoldt aperture remains strictly in the same depth-oriented cone.  It also lifts the
first-prime aperture-independent floor from coordinate zero to the complete finite jet.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

open GaloisForLFunctions.HTGeometry

/-- Finite real source aggregation is coordinatewise the sum of singleton anomalies. -/
theorem finiteExponentialGammaAnomaly_real_apply_eq_sum_singleton
    {P : Type*} [Fintype P]
    (weight rate : P → ℝ) (x : ℝ) (N : ℕ) (i : Fin N) :
    finiteExponentialGammaAnomaly
        (fun p ↦ (weight p : ℂ)) (fun p ↦ (rate p : ℂ))
        (x : ℂ) N (fun _ ↦ 1) i =
      ∑ p : P, finiteExponentialGammaAnomaly
        (fun _ : Fin 1 ↦ (weight p : ℂ))
        (fun _ : Fin 1 ↦ (rate p : ℂ)) (x : ℂ) N
        (fun _ ↦ 1) i := by
  rw [finiteExponentialGammaAnomaly, clockDescentAnomaly_apply]
  simp only [gammaClockTranslation, finiteExponentialJetObservation,
    finiteExponentialSourceShift, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Pi.sub_apply, mul_one]
  have hswap :
      (∑ j : Fin N, gammaClockTranslationCoefficient (i : ℕ) (j : ℕ) *
          ∑ p : P, (weight p : ℂ) * (-(rate p : ℂ)) ^ (j : ℕ) *
            Complex.exp (-(x : ℂ) * (rate p : ℂ))) =
        ∑ p : P, ∑ j : Fin N,
          gammaClockTranslationCoefficient (i : ℕ) (j : ℕ) *
            ((weight p : ℂ) * (-(rate p : ℂ)) ^ (j : ℕ) *
              Complex.exp (-(x : ℂ) * (rate p : ℂ))) := by
    calc
      _ = ∑ j : Fin N, ∑ p : P,
          gammaClockTranslationCoefficient (i : ℕ) (j : ℕ) *
            ((weight p : ℂ) * (-(rate p : ℂ)) ^ (j : ℕ) *
              Complex.exp (-(x : ℂ) * (rate p : ℂ))) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.mul_sum]
      _ = _ := Finset.sum_comm
  rw [hswap, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [finiteExponentialGammaAnomaly, clockDescentAnomaly_apply]
  simp only [gammaClockTranslation, finiteExponentialJetObservation,
    finiteExponentialSourceShift, LinearMap.coe_mk, AddHom.coe_mk,
    Fin.sum_univ_one, Fin.isValue, Pi.sub_apply, mul_one]

/-- Nonnegative singleton weights preserve the common coordinate orientation. -/
theorem finiteExponentialGammaAnomaly_singleton_oriented_re_nonneg
    (weight rate x : ℝ) (hweight : 0 ≤ weight) (hrate : 0 < rate)
    (N : ℕ) (i : Fin N) :
    0 ≤ (-1 : ℝ) ^ (N + 1) *
      (finiteExponentialGammaAnomaly
        (fun _ : Fin 1 ↦ (weight : ℂ))
        (fun _ : Fin 1 ↦ (rate : ℂ)) (x : ℂ) N
        (fun _ ↦ 1) i).re := by
  rcases hweight.eq_or_lt with rfl | hweight
  · rw [finiteExponentialGammaAnomaly_singleton_oriented_re_eq]
    simp
  · exact le_of_lt
      (finiteExponentialGammaAnomaly_singleton_oriented_re_pos
        weight rate x hweight hrate N i)

/-- Exact coordinatewise singleton decomposition for the actual finite von Mangoldt source. -/
theorem finiteVonMangoldtGammaAnomaly_apply_eq_sum_singleton
    (M : ℕ) (x : ℝ) (N : ℕ) (i : Fin N) :
    finiteVonMangoldtGammaAnomaly M (x : ℂ) N (fun _ ↦ 1) i =
      ∑ p : Fin M, finiteExponentialGammaAnomaly
        (fun _ : Fin 1 ↦
          ((ArithmeticFunction.vonMangoldt ((p : ℕ) + 2) / ((p : ℕ) + 2) : ℝ) : ℂ))
        (fun _ : Fin 1 ↦ (Real.log ((p : ℕ) + 2) : ℂ))
        (x : ℂ) N (fun _ ↦ 1) i := by
  rw [finiteVonMangoldtGammaAnomaly]
  have hweight :
      (fun p : Fin M ↦ finiteVonMangoldtWeight ((p : ℕ) + 2)) =
        (fun p : Fin M ↦
          ((ArithmeticFunction.vonMangoldt ((p : ℕ) + 2) / ((p : ℕ) + 2) : ℝ) : ℂ)) := by
    funext p
    simpa only [Nat.cast_add, Nat.cast_ofNat] using
      finiteVonMangoldtWeight_eq_ofReal
        (n := (p : ℕ) + 2) (Nat.ne_of_gt (by omega))
  have hfrequency :
      (fun p : Fin M ↦ finiteVonMangoldtFrequency ((p : ℕ) + 2)) =
        (fun p : Fin M ↦ (Real.log ((p : ℕ) + 2) : ℂ)) := by
    funext p
    simp [finiteVonMangoldtFrequency]
  rw [hweight, hfrequency]
  exact finiteExponentialGammaAnomaly_real_apply_eq_sum_singleton
    (fun p : Fin M ↦
      ArithmeticFunction.vonMangoldt ((p : ℕ) + 2) / ((p : ℕ) + 2))
    (fun p : Fin M ↦ Real.log ((p : ℕ) + 2)) x N i

/-- Every coordinate of every nonempty finite von Mangoldt aperture has the same strict
orientation.  The entire aggregated source jet therefore lies in one open orthant. -/
theorem finiteVonMangoldtGammaAnomaly_apply_oriented_re_pos
    (M : ℕ) (hM : 0 < M) (x : ℝ) (N : ℕ) (i : Fin N) :
    0 < (-1 : ℝ) ^ (N + 1) *
      (finiteVonMangoldtGammaAnomaly M (x : ℂ) N (fun _ ↦ 1) i).re := by
  rw [finiteVonMangoldtGammaAnomaly_apply_eq_sum_singleton M x N i]
  rw [← Complex.reCLM_apply, map_sum]
  change 0 < (-1 : ℝ) ^ (N + 1) *
    ∑ p : Fin M,
      (finiteExponentialGammaAnomaly
        (fun _ : Fin 1 ↦
          ((ArithmeticFunction.vonMangoldt ((p : ℕ) + 2) / ((p : ℕ) + 2) : ℝ) : ℂ))
        (fun _ : Fin 1 ↦ (Real.log ((p : ℕ) + 2) : ℂ))
        (x : ℂ) N (fun _ ↦ 1) i).re
  rw [Finset.mul_sum]
  apply Finset.sum_pos'
  · intro p hp
    apply finiteExponentialGammaAnomaly_singleton_oriented_re_nonneg
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    · exact Real.log_pos (by exact_mod_cast (show 1 < (p : ℕ) + 2 by omega))
  · let p : Fin M := ⟨0, hM⟩
    refine ⟨p, Finset.mem_univ p, ?_⟩
    have hstrict := finiteExponentialGammaAnomaly_singleton_oriented_re_pos
      (ArithmeticFunction.vonMangoldt 2 / (2 : ℝ)) (Real.log 2) x
      (by rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]; positivity)
      (Real.log_pos (by norm_num)) N i
    simpa [p] using hstrict

/-- In every jet coordinate the first prime supplies a positive floor independent of the
nonempty aperture size. -/
theorem firstVonMangoldtGammaAtom_apply_le_finiteAnomaly
    (M : ℕ) (hM : 0 < M) (x : ℝ) (N : ℕ) (i : Fin N) :
    (-1 : ℝ) ^ (N + 1) *
        (finiteExponentialGammaAnomaly
          (fun _ : Fin 1 ↦
            ((ArithmeticFunction.vonMangoldt 2 / (2 : ℝ) : ℝ) : ℂ))
          (fun _ : Fin 1 ↦ (Real.log 2 : ℂ)) (x : ℂ) N
          (fun _ ↦ 1) i).re ≤
      (-1 : ℝ) ^ (N + 1) *
        (finiteVonMangoldtGammaAnomaly M (x : ℂ) N (fun _ ↦ 1) i).re := by
  rw [finiteVonMangoldtGammaAnomaly_apply_eq_sum_singleton M x N i]
  let atom : Fin M → ℂ := fun p =>
    finiteExponentialGammaAnomaly
      (fun _ : Fin 1 ↦
        ((ArithmeticFunction.vonMangoldt ((p : ℕ) + 2) /
          ((p : ℕ) + 2) : ℝ) : ℂ))
      (fun _ : Fin 1 ↦ (Real.log ((p : ℕ) + 2) : ℂ))
      (x : ℂ) N (fun _ ↦ 1) i
  have hre : (∑ p : Fin M, atom p).re = ∑ p : Fin M, (atom p).re := by
    rw [← Complex.reCLM_apply, map_sum]
    rfl
  change
    (-1 : ℝ) ^ (N + 1) *
        (finiteExponentialGammaAnomaly
          (fun _ : Fin 1 ↦
            ((ArithmeticFunction.vonMangoldt 2 / (2 : ℝ) : ℝ) : ℂ))
          (fun _ : Fin 1 ↦ (Real.log 2 : ℂ)) (x : ℂ) N
          (fun _ ↦ 1) i).re ≤
      (-1 : ℝ) ^ (N + 1) * (∑ p : Fin M, atom p).re
  rw [hre]
  change
    (-1 : ℝ) ^ (N + 1) *
        (finiteExponentialGammaAnomaly
          (fun _ : Fin 1 ↦
            ((ArithmeticFunction.vonMangoldt 2 / (2 : ℝ) : ℝ) : ℂ))
          (fun _ : Fin 1 ↦ (Real.log 2 : ℂ)) (x : ℂ) N
          (fun _ ↦ 1) i).re ≤
      (-1 : ℝ) ^ (N + 1) *
        ∑ p : Fin M,
          (finiteExponentialGammaAnomaly
            (fun _ : Fin 1 ↦
              ((ArithmeticFunction.vonMangoldt ((p : ℕ) + 2) /
                ((p : ℕ) + 2) : ℝ) : ℂ))
            (fun _ : Fin 1 ↦ (Real.log ((p : ℕ) + 2) : ℂ))
            (x : ℂ) N (fun _ ↦ 1) i).re
  rw [Finset.mul_sum]
  let p : Fin M := ⟨0, hM⟩
  have hp : p ∈ (Finset.univ : Finset (Fin M)) := Finset.mem_univ p
  have hnonneg : ∀ q ∈ (Finset.univ : Finset (Fin M)),
      0 ≤ (-1 : ℝ) ^ (N + 1) *
        (finiteExponentialGammaAnomaly
          (fun _ : Fin 1 ↦
            ((ArithmeticFunction.vonMangoldt ((q : ℕ) + 2) /
              ((q : ℕ) + 2) : ℝ) : ℂ))
          (fun _ : Fin 1 ↦ (Real.log ((q : ℕ) + 2) : ℂ))
          (x : ℂ) N (fun _ ↦ 1) i).re := by
    intro q hq
    apply finiteExponentialGammaAnomaly_singleton_oriented_re_nonneg
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    · exact Real.log_pos (by exact_mod_cast (show 1 < (q : ℕ) + 2 by omega))
  have hsingle := Finset.single_le_sum hnonneg hp
  simpa [p] using hsingle

/-- Combined full-jet aperture floor: the first-prime coordinate is strictly positive and lies
below the corresponding coordinate of every nonempty finite aperture. -/
theorem finiteVonMangoldtGammaAnomaly_apply_uniform_firstAtom_floor
    (M : ℕ) (hM : 0 < M) (x : ℝ) (N : ℕ) (i : Fin N) :
    0 < (-1 : ℝ) ^ (N + 1) *
          (finiteExponentialGammaAnomaly
            (fun _ : Fin 1 ↦
              ((ArithmeticFunction.vonMangoldt 2 / (2 : ℝ) : ℝ) : ℂ))
            (fun _ : Fin 1 ↦ (Real.log 2 : ℂ)) (x : ℂ) N
            (fun _ ↦ 1) i).re ∧
      (-1 : ℝ) ^ (N + 1) *
          (finiteExponentialGammaAnomaly
            (fun _ : Fin 1 ↦
              ((ArithmeticFunction.vonMangoldt 2 / (2 : ℝ) : ℝ) : ℂ))
            (fun _ : Fin 1 ↦ (Real.log 2 : ℂ)) (x : ℂ) N
            (fun _ ↦ 1) i).re ≤
        (-1 : ℝ) ^ (N + 1) *
          (finiteVonMangoldtGammaAnomaly M (x : ℂ) N (fun _ ↦ 1) i).re := by
  constructor
  · exact finiteExponentialGammaAnomaly_singleton_oriented_re_pos
      (ArithmeticFunction.vonMangoldt 2 / (2 : ℝ)) (Real.log 2) x
      (by rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]; positivity)
      (Real.log_pos (by norm_num)) N i
  · exact firstVonMangoldtGammaAtom_apply_le_finiteAnomaly M hM x N i

end

end RHTower
