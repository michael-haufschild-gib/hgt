import GaloisForLFunctions.RHTower.Sieve.DirichletRow
import GaloisForLFunctions.RHTower.Sieve.HuxleyLogPhase

/-!
# Dyadic Dirichlet rows with Huxley's two-regime correlation bound

The ordinary `dirRow` starts at one.  Huxley's large-values argument instead needs a row on one
dyadic block `[N,2N)`.  This file constructs that row, identifies its Gram entries with logarithmic
phase sums, and attaches the Kuzmin--Landau and second-derivative estimates from
`HuxleyLogPhase.lean`.
-/

namespace RHTower.Sieve

open Finset
open scoped InnerProductSpace

/-- Unweighted logarithmic phase sum on `[N,2N)`. -/
noncomputable def dyadicLogSum (N : ℕ) (t : ℝ) : ℂ :=
  ∑ j ∈ Finset.range N,
    Complex.exp ((((t * Real.log ((N + j : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I))

/-- Dirichlet row supported on the dyadic block `[N,2N)`. -/
noncomputable def dyadicDirRow (N : ℕ) (t : ℝ) : EuclideanSpace ℂ (Fin N) :=
  WithLp.toLp 2 (fun j : Fin N =>
    Complex.exp ((((t * Real.log ((N + (j : ℕ) : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)))

theorem norm_dyadicDirRow_coord (N : ℕ) (t : ℝ) (j : Fin N) :
    ‖(dyadicDirRow N t) j‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

theorem norm_dyadicDirRow_sq (N : ℕ) (t : ℝ) : ‖dyadicDirRow N t‖ ^ 2 = (N : ℝ) := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (by positivity)]
  have hone : ∀ j : Fin N, ‖(dyadicDirRow N t) j‖ ^ 2 = 1 := by
    intro j
    rw [norm_dyadicDirRow_coord]
    norm_num
  rw [Finset.sum_congr rfl (fun j _ => hone j), Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, mul_one]

/-- Gram entries are the dyadic logarithmic phase sums at the frequency difference. -/
theorem inner_dyadicDirRow (N : ℕ) (t u : ℝ) :
    ⟪dyadicDirRow N t, dyadicDirRow N u⟫_ℂ = dyadicLogSum N (u - t) := by
  rw [PiLp.inner_apply]
  simp only [dyadicDirRow, RCLike.inner_apply]
  rw [dyadicLogSum, ← Fin.sum_univ_eq_sum_range
    (fun j : ℕ => Complex.exp (((((u - t) * Real.log ((N + j : ℕ) : ℝ) : ℝ) : ℂ)
      * Complex.I))) N]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hconj : (starRingEnd ℂ)
      (Complex.exp ((((t * Real.log ((N + j : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I)))
      = Complex.exp ((((-(t * Real.log ((N + j : ℕ) : ℝ)) : ℝ) : ℂ)
          * Complex.I)) := by
    rw [← Complex.exp_conj]
    congr 1
    rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
    push_cast
    ring
  rw [hconj, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- The norm depends only on the absolute frequency, in the negative-phase normalisation used by
`logPhase`. -/
theorem norm_dyadicLogSum_eq_logPhase_abs (N : ℕ) (t : ℝ) :
    ‖dyadicLogSum N t‖ =
      ‖∑ j ∈ Finset.range N,
        Complex.exp (((2 * Real.pi * logPhase |t| ((N : ℝ) + j) : ℝ) : ℂ) * Complex.I)‖ := by
  rcases le_total 0 t with ht | ht
  · have habs : |t| = t := abs_of_nonneg ht
    rw [habs]
    have hneg := norm_phase_sum_neg (logPhase t) (N : ℝ) N
    rw [dyadicLogSum]
    calc
      ‖∑ j ∈ Finset.range N,
          Complex.exp ((((t * Real.log ((N + j : ℕ) : ℝ) : ℝ) : ℂ) * Complex.I))‖
          = ‖∑ j ∈ Finset.range N,
              Complex.exp (((2 * Real.pi * -(logPhase t ((N : ℝ) + j)) : ℝ) : ℂ)
                * Complex.I)‖ := by
              congr 2 with j
              have hcast : ((N + j : ℕ) : ℝ) = (N : ℝ) + (j : ℝ) := by push_cast; ring
              rw [hcast]
              simp only [logPhase]
              congr 1
              push_cast
              field_simp [Real.pi_ne_zero]
      _ = _ := hneg
  · have habs : |t| = -t := abs_of_nonpos ht
    rw [habs, dyadicLogSum]
    congr 2 with j
    have hcast : ((N + j : ℕ) : ℝ) = (N : ℝ) + (j : ℝ) := by push_cast; ring
    rw [hcast]
    simp only [logPhase]
    congr 1
    push_cast
    field_simp [Real.pi_ne_zero]

/-- Reciprocal-frequency Gram bound in the non-resonant first-derivative range. -/
theorem norm_dyadicLogSum_le_kuzminLandau {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : t ≠ 0)
    (htN : 3 * |t| ≤ 4 * Real.pi * (N : ℝ)) :
    ‖dyadicLogSum N t‖ ≤ 6 * Real.pi * (N : ℝ) / |t| + 1 := by
  rw [norm_dyadicLogSum_eq_logPhase_abs]
  exact norm_logPhase_dyadic_le_kuzminLandau |t| (abs_pos.mpr ht) N hN htN

/-- Second-derivative Gram bound, valid for either sign of the frequency. -/
theorem norm_dyadicLogSum_le_secondDerivative {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : t ≠ 0)
    (hlam : logDyadicLambda N |t| ≤ 1) :
    ‖dyadicLogSum N t‖ ≤ logDyadicSecondBound N |t| := by
  rw [norm_dyadicLogSum_eq_logPhase_abs]
  have hphase : ∀ j ∈ Finset.range N,
      Complex.exp (((2 * Real.pi * logPhase |t| ((N : ℝ) + j) : ℝ) : ℂ) * Complex.I)
        = ((N + j : ℕ) : ℂ) ^ (-(Complex.I * ((|t| : ℝ) : ℂ))) := by
    intro j hj
    have hcast : ((N + j : ℕ) : ℝ) = (N : ℝ) + (j : ℝ) := by push_cast; ring
    rw [← hcast]
    exact (natCast_cpow_neg_I_mul |t| (N + j) (by omega)).symm
  rw [Finset.sum_congr rfl hphase]
  exact norm_logPhase_dyadic_le_secondDerivative |t| (abs_pos.mpr ht) N hN hlam

/-- Uniform second-derivative bound throughout a frequency window. -/
theorem norm_dyadicLogSum_le_secondEnvelope {N : ℕ} (hN : 1 ≤ N)
    {U T t : ℝ} (hU : 0 < U) (hUt : U ≤ |t|) (htT : |t| ≤ T)
    (hlamT : logDyadicLambda N T ≤ 1) :
    ‖dyadicLogSum N t‖ ≤ logDyadicSecondEnvelope N U T := by
  have ht : t ≠ 0 := by
    intro h
    rw [h, abs_zero] at hUt
    linarith
  have hlam : logDyadicLambda N |t| ≤ 1 :=
    (logDyadicLambda_mono hN htT).trans hlamT
  exact (norm_dyadicLogSum_le_secondDerivative hN ht hlam).trans
    (logDyadicSecondBound_le_envelope hN hU hUt htT)

end RHTower.Sieve
