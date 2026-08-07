import GaloisForLFunctions.HTGeometry.AdicCriticalFibreExact
import Mathlib.RingTheory.AdicCompletion.Completeness
import Mathlib.RingTheory.PowerSeries.NoZeroDivisors

/-!
# One-parameter critical deformation

All critical observation parameters are placed in the principal ideal `(T)` of a one-variable
power-series ring.  Their residues are the pure tails `X^m` and `X^n`, so the abstract adic theorem
gives the exact binomial fibre count.
-/

namespace GaloisForLFunctions.HTGeometry

open Polynomial

noncomputable def powerSeriesDeformParam {E : Type*} [Field E] (a : E) : PowerSeries E :=
  PowerSeries.X * PowerSeries.C a

noncomputable def powerSeriesRawDeformation
    (E : Type*) [Field E] (m n : ℕ) (u : Fin n → E) : (PowerSeries E)[X] :=
  ∑ i : Fin n, Polynomial.C (powerSeriesDeformParam (u i)) * X ^ (m + (i : ℕ))

noncomputable def powerSeriesReciprocalDeformation
    (E : Type*) [Field E] (m n : ℕ) (v : Fin m → E) : (PowerSeries E)[X] :=
  ∑ j : Fin m, Polynomial.C (powerSeriesDeformParam (v j)) * X ^ (n + (j : ℕ))

noncomputable abbrev powerSeriesDeformIdeal (E : Type*) [Field E] : Ideal (PowerSeries E) :=
  Ideal.span {PowerSeries.X}

theorem powerSeriesDeformIdeal_eq_ker_constantCoeff (E : Type*) [Field E] :
    powerSeriesDeformIdeal E = RingHom.ker PowerSeries.constantCoeff := by
  ext f
  rw [RingHom.mem_ker, Ideal.mem_span_singleton, PowerSeries.X_dvd_iff]

theorem coeffMem_powerSeriesRawDeformation
    (E : Type*) [Field E] (m n : ℕ) (u : Fin n → E) :
    CoeffMem (powerSeriesDeformIdeal E) (powerSeriesRawDeformation E m n u) := by
  intro k
  rw [powerSeriesRawDeformation, Polynomial.finsetSum_coeff]
  refine Submodule.sum_mem _ fun i _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  split_ifs
  · rw [mul_one, Ideal.mem_span_singleton]
    exact ⟨PowerSeries.C (u i), by simp [powerSeriesDeformParam]⟩
  · rw [mul_zero]
    exact Submodule.zero_mem _

theorem coeffMem_powerSeriesReciprocalDeformation
    (E : Type*) [Field E] (m n : ℕ) (v : Fin m → E) :
    CoeffMem (powerSeriesDeformIdeal E) (powerSeriesReciprocalDeformation E m n v) := by
  intro k
  rw [powerSeriesReciprocalDeformation, Polynomial.finsetSum_coeff]
  refine Submodule.sum_mem _ fun j _ => ?_
  rw [Polynomial.coeff_C_mul, Polynomial.coeff_X_pow]
  split_ifs
  · rw [mul_one, Ideal.mem_span_singleton]
    exact ⟨PowerSeries.C (v j), by simp [powerSeriesDeformParam]⟩
  · rw [mul_zero]
    exact Submodule.zero_mem _

theorem polynomial_X_pow_dvd_powerSeriesRawDeformation
    (E : Type*) [Field E] (m n : ℕ) (u : Fin n → E) :
    (X : (PowerSeries E)[X]) ^ m ∣ powerSeriesRawDeformation E m n u := by
  classical
  rw [powerSeriesRawDeformation]
  refine Finset.dvd_sum fun i _ => ?_
  refine ⟨Polynomial.C (powerSeriesDeformParam (u i)) * X ^ (i : ℕ), ?_⟩
  rw [pow_add]
  ring

theorem polynomial_X_pow_dvd_powerSeriesReciprocalDeformation
    (E : Type*) [Field E] (m n : ℕ) (v : Fin m → E) :
    (X : (PowerSeries E)[X]) ^ n ∣ powerSeriesReciprocalDeformation E m n v := by
  classical
  rw [powerSeriesReciprocalDeformation]
  refine Finset.dvd_sum fun j _ => ?_
  refine ⟨Polynomial.C (powerSeriesDeformParam (v j)) * X ^ (j : ℕ), ?_⟩
  rw [pow_add]
  ring

/-- One-variable power-series instance of a critical adic deformation. -/
noncomputable def powerSeriesCriticalDeformation
    (E : Type*) [Field E] (m n : ℕ) (u : Fin n → E) (v : Fin m → E) :
    CriticalAdicDeformation E (PowerSeries E) m n where
  ideal := powerSeriesDeformIdeal E
  residue := PowerSeries.constantCoeff
  constants := PowerSeries.C
  residue_constants := by ext; simp
  raw := powerSeriesRawDeformation E m n u
  reciprocal := powerSeriesReciprocalDeformation E m n v
  ideal_eq_ker := powerSeriesDeformIdeal_eq_ker_constantCoeff E
  coeffMem_raw := coeffMem_powerSeriesRawDeformation E m n u
  coeffMem_reciprocal := coeffMem_powerSeriesReciprocalDeformation E m n v
  X_pow_dvd_raw := polynomial_X_pow_dvd_powerSeriesRawDeformation E m n u
  X_pow_dvd_reciprocal := polynomial_X_pow_dvd_powerSeriesReciprocalDeformation E m n v

noncomputable abbrev powerSeriesDeformedRawTail
    (E : Type*) [Field E] (m n : ℕ) (u : Fin n → E) : (PowerSeries E)[X] :=
  (powerSeriesCriticalDeformation E m n u (fun _ => 0)).rawTail

noncomputable abbrev powerSeriesDeformedReciprocalTail
    (E : Type*) [Field E] (m n : ℕ) (v : Fin m → E) : (PowerSeries E)[X] :=
  (powerSeriesCriticalDeformation E m n (fun _ => 0) v).reciprocalTail

theorem nat_card_powerSeriesCriticalFibre
    (E : Type*) [Field E] [CharZero E] [IsAlgClosed E]
    {m n : ℕ} (hm : 0 < m) (hn : 0 < n) (u : Fin n → E) (v : Fin m → E) :
    Nat.card (criticalFibre (PowerSeries E) m n
      (X ^ m + powerSeriesRawDeformation E m n u)
      (X ^ n + powerSeriesReciprocalDeformation E m n v)) =
      criticalHorizonMultiplicity m n := by
  let D := powerSeriesCriticalDeformation E m n u v
  letI : IsAdicComplete D.ideal (PowerSeries E) := inferInstanceAs
    (IsAdicComplete (Ideal.span {PowerSeries.X}) (PowerSeries E))
  exact D.nat_card hm hn

end GaloisForLFunctions.HTGeometry
