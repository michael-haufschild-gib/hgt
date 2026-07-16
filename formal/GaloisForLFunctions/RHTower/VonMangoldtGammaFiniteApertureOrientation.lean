import GaloisForLFunctions.RHTower.VonMangoldtGammaOrientedAnomaly

/-!
# Finite-aperture orientation of the von Mangoldt--Gamma anomaly

Every resolved von Mangoldt atom has the same alternating Taylor-tail orientation.  This file
proves that the sign survives the actual finite source aperture and that the first prime supplies
a positive lower floor independent of the aperture size.

The result is entirely before continuation or critical renormalization.  It therefore isolates
the remaining RH-facing problem sharply: any loss of orientation must occur in the completed
prime--Gamma comparison or its counterterm, not in aggregation of the finite Euler source.
-/

open scoped BigOperators

namespace RHTower

noncomputable section

open Polynomial
open GaloisForLFunctions.HTGeometry

/-- The zeroth Gamma-anomaly coordinate of a finite real exponential packet is the sum of its
oriented scalar Taylor-tail atoms. -/
theorem finiteExponentialGammaAnomaly_real_zero_apply_eq_sum
    {P : Type*} [Fintype P]
    (weight rate : P → ℝ) (x : ℝ) (N : ℕ) (hN : 0 < N) :
    finiteExponentialGammaAnomaly
        (fun p ↦ (weight p : ℂ)) (fun p ↦ (rate p : ℂ))
        (x : ℂ) N (fun _ ↦ 1) ⟨0, hN⟩ =
      ∑ p : P, singletonExponentialGammaAnomalyAtom (weight p) (rate p) x N := by
  rw [finiteExponentialGammaAnomaly, clockDescentAnomaly_apply]
  simp only [gammaClockTranslation, finiteExponentialJetObservation,
    finiteExponentialSourceShift, LinearMap.coe_mk, AddHom.coe_mk]
  simp only [Pi.sub_apply, pow_zero, mul_one]
  have hswap :
      (∑ j : Fin N, gammaClockTranslationCoefficient 0 (j : ℕ) *
          ∑ p : P, (weight p : ℂ) * (-(rate p : ℂ)) ^ (j : ℕ) *
            Complex.exp (-(x : ℂ) * (rate p : ℂ))) =
        ∑ p : P, ∑ j : Fin N, gammaClockTranslationCoefficient 0 (j : ℕ) *
          ((weight p : ℂ) * (-(rate p : ℂ)) ^ (j : ℕ) *
            Complex.exp (-(x : ℂ) * (rate p : ℂ))) := by
    calc
      _ = ∑ j : Fin N, ∑ p : P, gammaClockTranslationCoefficient 0 (j : ℕ) *
          ((weight p : ℂ) * (-(rate p : ℂ)) ^ (j : ℕ) *
            Complex.exp (-(x : ℂ) * (rate p : ℂ))) := by
            apply Finset.sum_congr rfl
            intro j hj
            rw [Finset.mul_sum]
      _ = _ := Finset.sum_comm
  rw [hswap]
  rw [← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro p hp
  rw [singletonExponentialGammaAnomalyAtom]
  rw [eval_expNegTruncPoly]
  simp only [gammaClockTranslationCoefficient, Nat.zero_le, ↓reduceIte, Nat.sub_zero]
  push_cast
  have hsum :
      (∑ j : Fin N,
        ((j : ℕ).factorial : ℂ)⁻¹ *
          ((weight p : ℂ) * (-(rate p : ℂ)) ^ (j : ℕ) *
            Complex.exp (-(x : ℂ) * (rate p : ℂ)))) =
        ∑ j ∈ Finset.range N,
          (j.factorial : ℂ)⁻¹ *
            ((weight p : ℂ) * (-(rate p : ℂ)) ^ j *
              Complex.exp (-(x : ℂ) * (rate p : ℂ))) := by
    simpa using Fin.sum_univ_eq_sum_range
      (fun j : ℕ => (j.factorial : ℂ)⁻¹ *
        ((weight p : ℂ) * (-(rate p : ℂ)) ^ j *
          Complex.exp (-(x : ℂ) * (rate p : ℂ)))) N
  simp only [one_div]
  rw [hsum]
  change
    (∑ j ∈ Finset.range N,
      ((j.factorial : ℂ)⁻¹ *
        ((weight p : ℂ) * (-(rate p : ℂ)) ^ j *
          Complex.exp (-(x : ℂ) * (rate p : ℂ))))) -
      (weight p : ℂ) * Complex.exp (-(rate p : ℂ)) *
        Complex.exp (-(x : ℂ) * (rate p : ℂ)) = _
  ring_nf
  congr 1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j hj
  ring

/-- Nonnegative weights preserve the common alternating Taylor-tail orientation. -/
theorem singletonExponentialGammaAnomalyAtom_oriented_re_nonneg
    (weight rate x : ℝ) (hweight : 0 ≤ weight) (hrate : 0 < rate)
    (N : ℕ) (hN : 0 < N) :
    0 ≤ (-1 : ℝ) ^ (N + 1) *
      (singletonExponentialGammaAnomalyAtom weight rate x N).re := by
  rcases hweight.eq_or_lt with rfl | hweight
  · simp [singletonExponentialGammaAnomalyAtom]
  · exact le_of_lt
      (singletonExponentialGammaAnomalyAtom_oriented_re_pos
        weight rate x hweight hrate N hN)

/-- Exact scalar-atom decomposition of the actual finite von Mangoldt--Gamma anomaly. -/
theorem finiteVonMangoldtGammaAnomaly_zero_apply_eq_sum
    (M : ℕ) (x : ℝ) (N : ℕ) (hN : 0 < N) :
    finiteVonMangoldtGammaAnomaly M (x : ℂ) N (fun _ ↦ 1) ⟨0, hN⟩ =
      ∑ p : Fin M,
        singletonExponentialGammaAnomalyAtom
          (ArithmeticFunction.vonMangoldt ((p : ℕ) + 2) / ((p : ℕ) + 2))
          (Real.log ((p : ℕ) + 2)) x N := by
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
  rw [hweight]
  rw [hfrequency]
  exact
    finiteExponentialGammaAnomaly_real_zero_apply_eq_sum
      (fun p : Fin M ↦
        ArithmeticFunction.vonMangoldt ((p : ℕ) + 2) / ((p : ℕ) + 2))
      (fun p : Fin M ↦ Real.log ((p : ℕ) + 2)) x N hN

/-- Every nonempty finite von Mangoldt aperture has strict all-depth alternating orientation. -/
theorem finiteVonMangoldtGammaAnomaly_zero_oriented_re_pos
    (M : ℕ) (hM : 0 < M) (x : ℝ) (N : ℕ) (hN : 0 < N) :
    0 < (-1 : ℝ) ^ (N + 1) *
      (finiteVonMangoldtGammaAnomaly M (x : ℂ) N
        (fun _ ↦ 1) ⟨0, hN⟩).re := by
  rw [finiteVonMangoldtGammaAnomaly_zero_apply_eq_sum M x N hN]
  rw [← Complex.reCLM_apply, map_sum]
  change 0 < (-1 : ℝ) ^ (N + 1) *
    ∑ p : Fin M,
      (singletonExponentialGammaAnomalyAtom
        (ArithmeticFunction.vonMangoldt ((p : ℕ) + 2) / ((p : ℕ) + 2))
        (Real.log ((p : ℕ) + 2)) x N).re
  rw [Finset.mul_sum]
  apply Finset.sum_pos'
  · intro p hp
    apply singletonExponentialGammaAnomalyAtom_oriented_re_nonneg
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    · exact Real.log_pos (by exact_mod_cast (show 1 < (p : ℕ) + 2 by omega))
    · exact hN
  · let p : Fin M := ⟨0, hM⟩
    refine ⟨p, Finset.mem_univ p, ?_⟩
    have hstrict := singletonExponentialGammaAnomalyAtom_oriented_re_pos
      (ArithmeticFunction.vonMangoldt 2 / (2 : ℝ)) (Real.log 2) x
      (by rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]; positivity)
      (Real.log_pos (by norm_num)) N hN
    simpa [p] using hstrict

/-- The first prime supplies a positive floor independent of the nonempty aperture size. -/
theorem firstVonMangoldtGammaAtom_le_finiteAnomaly
    (M : ℕ) (hM : 0 < M) (x : ℝ) (N : ℕ) (hN : 0 < N) :
    (-1 : ℝ) ^ (N + 1) *
        (singletonExponentialGammaAnomalyAtom
          (ArithmeticFunction.vonMangoldt 2 / (2 : ℝ)) (Real.log 2) x N).re ≤
      (-1 : ℝ) ^ (N + 1) *
        (finiteVonMangoldtGammaAnomaly M (x : ℂ) N
          (fun _ ↦ 1) ⟨0, hN⟩).re := by
  rw [finiteVonMangoldtGammaAnomaly_zero_apply_eq_sum M x N hN]
  let atom : Fin M → ℂ := fun p =>
    singletonExponentialGammaAnomalyAtom
      (ArithmeticFunction.vonMangoldt ((p : ℕ) + 2) / ((p : ℕ) + 2))
      (Real.log ((p : ℕ) + 2)) x N
  have hre : (∑ p : Fin M, atom p).re = ∑ p : Fin M, (atom p).re := by
    rw [← Complex.reCLM_apply, map_sum]
    rfl
  change
    (-1 : ℝ) ^ (N + 1) *
        (singletonExponentialGammaAnomalyAtom
          (ArithmeticFunction.vonMangoldt 2 / (2 : ℝ)) (Real.log 2) x N).re ≤
      (-1 : ℝ) ^ (N + 1) * (∑ p : Fin M, atom p).re
  rw [hre]
  change
    (-1 : ℝ) ^ (N + 1) *
        (singletonExponentialGammaAnomalyAtom
          (ArithmeticFunction.vonMangoldt 2 / (2 : ℝ)) (Real.log 2) x N).re ≤
      (-1 : ℝ) ^ (N + 1) *
        ∑ p : Fin M,
          (singletonExponentialGammaAnomalyAtom
            (ArithmeticFunction.vonMangoldt ((p : ℕ) + 2) / ((p : ℕ) + 2))
            (Real.log ((p : ℕ) + 2)) x N).re
  rw [Finset.mul_sum]
  let p : Fin M := ⟨0, hM⟩
  have hp : p ∈ (Finset.univ : Finset (Fin M)) := Finset.mem_univ p
  have hnonneg : ∀ q ∈ (Finset.univ : Finset (Fin M)),
      0 ≤ (-1 : ℝ) ^ (N + 1) *
        (singletonExponentialGammaAnomalyAtom
          (ArithmeticFunction.vonMangoldt ((q : ℕ) + 2) / ((q : ℕ) + 2))
          (Real.log ((q : ℕ) + 2)) x N).re := by
    intro q hq
    apply singletonExponentialGammaAnomalyAtom_oriented_re_nonneg
    · exact div_nonneg ArithmeticFunction.vonMangoldt_nonneg (by positivity)
    · exact Real.log_pos (by exact_mod_cast (show 1 < (q : ℕ) + 2 by omega))
    · exact hN
  have hsingle := Finset.single_le_sum hnonneg hp
  simpa [p] using hsingle

/-- Combined all-aperture source floor: the first-prime contribution is strictly positive and
lies below every nonempty finite von Mangoldt--Gamma anomaly. -/
theorem finiteVonMangoldtGammaAnomaly_uniform_firstAtom_floor
    (M : ℕ) (hM : 0 < M) (x : ℝ) (N : ℕ) (hN : 0 < N) :
    0 < (-1 : ℝ) ^ (N + 1) *
          (singletonExponentialGammaAnomalyAtom
            (ArithmeticFunction.vonMangoldt 2 / (2 : ℝ)) (Real.log 2) x N).re ∧
      (-1 : ℝ) ^ (N + 1) *
          (singletonExponentialGammaAnomalyAtom
            (ArithmeticFunction.vonMangoldt 2 / (2 : ℝ)) (Real.log 2) x N).re ≤
        (-1 : ℝ) ^ (N + 1) *
          (finiteVonMangoldtGammaAnomaly M (x : ℂ) N
            (fun _ ↦ 1) ⟨0, hN⟩).re := by
  constructor
  · exact singletonExponentialGammaAnomalyAtom_oriented_re_pos
      (ArithmeticFunction.vonMangoldt 2 / (2 : ℝ)) (Real.log 2) x
      (by rw [ArithmeticFunction.vonMangoldt_apply_prime Nat.prime_two]; positivity)
      (Real.log_pos (by norm_num)) N hN
  · exact firstVonMangoldtGammaAtom_le_finiteAnomaly M hM x N hN

end

end RHTower
