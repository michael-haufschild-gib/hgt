import GaloisForLFunctions.OrderSixMetaplecticTheory.CharacterChannels.WeilCubicProjection
import GaloisForLFunctions.HilbertMetric.Spectral.ClippedRankOne

/-!
# Spectral blindness and the signed Weil–cubic pairing

On residues modulo four the actual phase `Γχ₂` has zero mean and is nonzero
at the principal class. Replacing it by its modulus gives a positive mean but
preserves every spectral sum of its rank-one covariance. The signed first
moment is instead the constant-vector pairing of that covariance. Applied to
the inverse cubic projection of class masses, this gives an exact identity
for finite order-six row sums.
-/

open scoped BigOperators Classical NNReal
namespace GaloisForLFunctions.OrderSixMetaplecticTheory.RamifiedCharacterChannel
open MetaplecticMobiusDescent MetaplecticMobiusDescent.Eisenstein
  MetaplecticMobiusDescent.CubicJacobi MetaplecticMobiusDescent.CubicEisenstein
open HilbertMetric.Clipped
noncomputable section

local instance : Finite ResidueFour :=
  (Ideal.span {(4 : O)}).finiteQuotientOfFreeOfNeBot
    (fun h => (by norm_num : (4 : O) ≠ 0) (Ideal.span_singleton_eq_bot.mp h))
local instance : Fintype ResidueFour := Fintype.ofFinite _

/-- The principal residue class supplies a nonzero phase. -/
theorem phase_one : phase (1 : ResidueFour) = 1 := by
  rw [← map_one (Ideal.Quotient.mk (Ideal.span {(4 : O)})), phase_mk,
    fixedDualAverage_one, one_mul, cubicTwoChar,
    symbol_one_numerator (-2) primary_neg_two, map_one, one_pow]

/-- The actual conductor-four phase has zero first moment. -/
theorem sum_phase_eq_zero : ∑ r : ResidueFour, phase r = 0 :=
  sum_fixedDualAverage_mul_cubicTwoChar

/-- Its modulus has positive first moment: the principal class alone contributes one. -/
theorem sum_abs_phase_pos : 0 < ∑ r : ResidueFour, ‖phase r‖ := by
  have h := Finset.single_le_sum (fun r _ => norm_nonneg (phase r))
    (Finset.mem_univ (1 : ResidueFour))
  rw [phase_one, norm_one] at h
  exact lt_of_lt_of_le zero_lt_one h

/-- Every covariance spectral statistic identifies the cancelling arithmetic phase
with its positively aligned modulus. -/
theorem phase_covariance_spectral_eq_abs (f : ℝ → ℝ) :
    spectralSum f (columnCovariance phase) =
      spectralSum f (columnCovariance (fun r : ResidueFour => (‖phase r‖ : ℂ))) :=
  spectralSum_columnCovariance_abs phase f

/-- In particular no spectral cutoff distinguishes these two local phase choices. -/
theorem phase_covariance_clipped_eq_abs (c : ℝ) :
    energy c (columnCovariance phase) =
      energy c (columnCovariance (fun r : ResidueFour => (‖phase r‖ : ℂ))) :=
  phase_covariance_spectral_eq_abs (quadratic c)

/-- Equal covariance spectra coexist with zero and nonzero first moments, witnessed
by the actual Weil–cubic phase and its modulus on residues modulo four. -/
theorem phase_covariance_does_not_determine_firstMoment :
    (∀ f : ℝ → ℝ, spectralSum f (columnCovariance phase) =
      spectralSum f (columnCovariance (fun r : ResidueFour => (‖phase r‖ : ℂ)))) ∧
    (∑ r : ResidueFour, phase r) = 0 ∧
    (∑ r : ResidueFour, (‖phase r‖ : ℂ)) ≠ 0 := by
  refine ⟨phase_covariance_spectral_eq_abs, sum_phase_eq_zero, ?_⟩
  rw [← Complex.ofReal_sum]
  exact_mod_cast ne_of_gt sum_abs_phase_pos

/-- Even the entire clipped-energy curve cannot recover squared first moments
for all data on residues modulo four. -/
theorem no_clipped_firstMoment_norm_decoder :
    ¬ ∃ decode : (ℝ → ℝ) → ℝ, ∀ u : ResidueFour → ℂ,
      decode (fun c => energy c (columnCovariance u)) = Complex.normSq (∑ r, u r) := by
  rintro ⟨decode, hdecode⟩
  have he : (fun c => energy c (columnCovariance phase)) =
      (fun c => energy c (columnCovariance (fun r : ResidueFour => (‖phase r‖ : ℂ)))) :=
    funext phase_covariance_clipped_eq_abs
  have h := congrArg decode he
  rw [hdecode, hdecode, sum_phase_eq_zero, map_zero] at h
  exact phase_covariance_does_not_determine_firstMoment.2.2
    (Complex.normSq_eq_zero.mp h.symm)

/-- The oriented covariance pairing retains precisely the projected signed sum. -/
theorem projected_pairing_normSq (f : ResidueFour → ℂ) :
    (Complex.normSq (weightedSum f) : ℂ) =
      ∑ r, ∑ s, columnCovariance (fun r => phase r * cubicProjection f r) r s := by
  rw [sum_columnCovariance]
  change (Complex.normSq (weightedSum f) : ℂ) =
    (Complex.normSq (weightedSum (cubicProjection f)) : ℂ)
  rw [weightedSum_eq_projected]

/-- The finite arithmetic first moment is recovered by its oriented covariance,
after the inverse cubic projection; all local phases are retained. -/
theorem finite_row_sum_normSq_eq_projected_covariance (S : Finset O) (w : O → ℂ) :
    (Complex.normSq (∑ c ∈ S,
      fixedDualAverage c * cubicTwoChar c * normalizedCubicUnitGauss c ^ 2 * w c) : ℂ) =
      ∑ r, ∑ s, columnCovariance
        (fun r => phase r * cubicProjection (gaussSquareClassMass S w) r) r s := by
  rw [finite_row_sum_eq_projected, weightedSum_eq_projected]
  exact projected_pairing_normSq (gaussSquareClassMass S w)

#print axioms phase_covariance_does_not_determine_firstMoment
#print axioms phase_covariance_clipped_eq_abs
#print axioms no_clipped_firstMoment_norm_decoder
#print axioms finite_row_sum_normSq_eq_projected_covariance

end
end GaloisForLFunctions.OrderSixMetaplecticTheory.RamifiedCharacterChannel
