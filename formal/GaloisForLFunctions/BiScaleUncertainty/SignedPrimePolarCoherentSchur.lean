import GaloisForLFunctions.BiScaleUncertainty.AnnularCorrelationSource
import GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolarHalfLineTransport

/-!
# Coherent collar and source-Schur control of signed Chebyshev work

The entire annular source is paired with the actual signed prime–polar packet.
Its double Gram energy retains all collar cross-correlations. Removing the
component of both sources parallel to the original source gives a joint Schur
constraint on the signed scalar pairing and its exact Chebyshev work.
-/

open MeasureTheory Set
open scoped BigOperators CompactlySupported

namespace GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
open RHTower.ArchimedeanAnomaly RHTower.ArchimedeanExactForm RHTower.WeilMarkovPole
noncomputable section
set_option autoImplicit false

private def sourcePair (p q : C_c(ℝ, ℝ)) : ℝ := ∫ u, p u * q u

private theorem sourcePair_self (p : C_c(ℝ, ℝ)) : sourcePair p p = autocorr p 0 := by
  simp only [sourcePair, autocorr, add_zero]

private theorem sourcePair_comm (p q : C_c(ℝ, ℝ)) : sourcePair p q = sourcePair q p := by
  unfold sourcePair
  simp only [mul_comm]

private theorem sourcePair_sq_le (p q : C_c(ℝ, ℝ)) :
    sourcePair p q ^ 2 ≤ autocorr p 0 * autocorr q 0 := by
  have hs := HTGeometry.sq_integral_mul_le (f := (p : ℝ → ℝ)) (g := (q : ℝ → ℝ))
    p.continuous.aestronglyMeasurable q.continuous.aestronglyMeasurable
    (integrable_sq p.continuous p.hasCompactSupport)
    (integrable_sq q.continuous q.hasCompactSupport)
  rwa [integral_sq_eq_autocorr_zero, integral_sq_eq_autocorr_zero] at hs

private def sourceResidual (p f : C_c(ℝ, ℝ)) (c : ℝ) : C_c(ℝ, ℝ) :=
  ⟨⟨fun u => p u - c * f u, p.continuous.sub (continuous_const.mul f.continuous)⟩,
    p.hasCompactSupport.sub f.hasCompactSupport.mul_left⟩

private theorem sourcePair_sub_right (p q f : C_c(ℝ, ℝ)) (c : ℝ) :
    sourcePair p (sourceResidual q f c) = sourcePair p q - c * sourcePair p f := by
  have hiq : Integrable (fun u => p u * q u) :=
    (p.continuous.mul q.continuous).integrable_of_hasCompactSupport p.hasCompactSupport.mul_right
  have hif : Integrable (fun u => p u * f u) :=
    (p.continuous.mul f.continuous).integrable_of_hasCompactSupport p.hasCompactSupport.mul_right
  have he : (fun u => p u * sourceResidual q f c u) =
      fun u => p u * q u - c * (p u * f u) := by
    funext u
    change p u * (q u - c * f u) = _
    ring
  unfold sourcePair
  rw [he, integral_sub hiq (hif.const_mul c), integral_const_mul]

private theorem sourceResidual_energy (p f : C_c(ℝ, ℝ)) (c : ℝ) :
    autocorr (sourceResidual p f c) 0 =
      autocorr p 0 - 2 * c * sourcePair p f + c ^ 2 * autocorr f 0 := by
  rw [← sourcePair_self, sourcePair_sub_right,
    sourcePair_comm (sourceResidual p f c) p, sourcePair_sub_right,
    sourcePair_comm (sourceResidual p f c) f, sourcePair_sub_right,
    sourcePair_self, sourcePair_self, sourcePair_comm f p]
  ring

private theorem projected_source_energy (p f : C_c(ℝ, ℝ)) :
    autocorr (sourceResidual p f (sourcePair p f / autocorr f 0)) 0 =
      autocorr p 0 - sourcePair p f ^ 2 / autocorr f 0 := by
  rw [sourceResidual_energy]
  by_cases hR : autocorr f 0 = 0
  · simp [hR]
  · field_simp
    ring

private theorem projected_source_pair (p q f : C_c(ℝ, ℝ)) :
    sourcePair (sourceResidual p f (sourcePair p f / autocorr f 0))
      (sourceResidual q f (sourcePair q f / autocorr f 0)) =
        sourcePair p q - sourcePair p f * sourcePair q f / autocorr f 0 := by
  rw [sourcePair_sub_right, sourcePair_comm (sourceResidual p f _) q,
    sourcePair_sub_right, sourcePair_comm (sourceResidual p f _) f,
    sourcePair_sub_right, sourcePair_self, sourcePair_comm q p, sourcePair_comm f p]
  by_cases hR : autocorr f 0 = 0
  · simp [hR]
  · field_simp
    ring

private theorem sourcePair_schur (p q f : C_c(ℝ, ℝ)) :
    (sourcePair p q - sourcePair p f * sourcePair q f / autocorr f 0) ^ 2 ≤
      (autocorr p 0 - sourcePair p f ^ 2 / autocorr f 0) *
        (autocorr q 0 - sourcePair q f ^ 2 / autocorr f 0) := by
  have hs := sourcePair_sq_le
    (sourceResidual p f (sourcePair p f / autocorr f 0))
    (sourceResidual q f (sourcePair q f / autocorr f 0))
  rwa [projected_source_pair, projected_source_energy, projected_source_energy] at hs

private theorem sourcePair_collar_source (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    sourcePair (collarSource f a b) f = correlationAverage f a b 0 :=
  integral_collarSource_mul_source f a b

private theorem sourcePair_source_packet (f : C_c(ℝ, ℝ)) (N : ℕ) :
    sourcePair f (signedSource f N) = pairing N (autocorr f) :=
  integral_source_signedSource f N

private theorem sourcePair_collar_packet (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) :
    sourcePair (collarSource f a b) (signedSource f N) = chebyshevWork f a b N :=
  integral_collarSource_signedSource f a b N

/-- Signed packet energy after removing its actual source-parallel component. -/
def signedPacketSchurEnergy (f : C_c(ℝ, ℝ)) (N : ℕ) : ℝ :=
  packetEnergy f N - pairing N (autocorr f) ^ 2 / autocorr f 0

/-- Collar energy after removing its actual source-parallel component. -/
def collarSchurEnergy (f : C_c(ℝ, ℝ)) (a b : ℝ) : ℝ :=
  collarEnergy f a b - correlationAverage f a b 0 ^ 2 / autocorr f 0

theorem signedPacketSchurEnergy_nonneg (f : C_c(ℝ, ℝ)) (N : ℕ) :
    0 ≤ signedPacketSchurEnergy f N := by
  have he := projected_source_energy (signedSource f N) f
  rw [sourcePair_comm, sourcePair_source_packet] at he
  rw [signedPacketSchurEnergy, packetEnergy, ← he]
  exact autocorr_zero_nonneg _

theorem signedPacketSchurEnergy_le_packetEnergy (f : C_c(ℝ, ℝ)) (N : ℕ) :
    signedPacketSchurEnergy f N ≤ packetEnergy f N :=
  sub_le_self _ (div_nonneg (sq_nonneg _) (autocorr_zero_nonneg f))

theorem collarSchurEnergy_nonneg (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    0 ≤ collarSchurEnergy f a b := by
  have he := projected_source_energy (collarSource f a b) f
  rw [sourcePair_collar_source] at he
  rw [collarSchurEnergy, collarEnergy, ← he]
  exact autocorr_zero_nonneg _

theorem collarSchurEnergy_le_collarEnergy (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    collarSchurEnergy f a b ≤ collarEnergy f a b :=
  sub_le_self _ (div_nonneg (sq_nonneg _) (autocorr_zero_nonneg f))

/-- Joint signed scalar constraint from both actual source-orthogonal residuals. -/
theorem chebyshevWork_schur (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) :
    (chebyshevWork f a b N -
      correlationAverage f a b 0 * pairing N (autocorr f) / autocorr f 0) ^ 2 ≤
        collarSchurEnergy f a b * signedPacketSchurEnergy f N := by
  have hs := sourcePair_schur (collarSource f a b) (signedSource f N) f
  rw [sourcePair_collar_packet, sourcePair_collar_source,
    sourcePair_comm (signedSource f N) f, sourcePair_source_packet] at hs
  exact hs

/-- Two observed signed scalar values force this much actual packet energy. -/
theorem packetEnergy_lower_bound_from_work (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) :
    pairing N (autocorr f) ^ 2 / autocorr f 0 +
      (chebyshevWork f a b N -
        correlationAverage f a b 0 * pairing N (autocorr f) / autocorr f 0) ^ 2 /
          collarSchurEnergy f a b ≤ packetEnergy f N := by
  have hS := signedPacketSchurEnergy_nonneg f N
  have hB := collarSchurEnergy_nonneg f a b
  have hs := chebyshevWork_schur f a b N
  by_cases hz : collarSchurEnergy f a b = 0
  · rw [hz, div_zero, add_zero]
    dsimp [signedPacketSchurEnergy] at hS
    linarith only [hS]
  · have hp : 0 < collarSchurEnergy f a b := lt_of_le_of_ne hB (Ne.symm hz)
    have hd : (chebyshevWork f a b N -
        correlationAverage f a b 0 * pairing N (autocorr f) / autocorr f 0) ^ 2 /
          collarSchurEnergy f a b ≤ signedPacketSchurEnergy f N :=
      (div_le_iff₀ hp).mpr (by simpa only [mul_comm] using hs)
    dsimp [signedPacketSchurEnergy] at hd
    linarith only [hd]

/-- Coherent displacement energy, retaining every collar cross-correlation. -/
def collarChordEnergy (f : C_c(ℝ, ℝ)) (a b : ℝ) : ℝ :=
  autocorr f 0 + collarEnergy f a b - 2 * correlationAverage f a b 0

private theorem collarChordEnergy_eq_source (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    collarChordEnergy f a b = autocorr (sourceResidual f (collarSource f a b) 1) 0 := by
  rw [sourceResidual_energy, sourcePair_comm f, sourcePair_collar_source]
  dsimp [collarChordEnergy, collarEnergy]
  ring

theorem collarChordEnergy_nonneg (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    0 ≤ collarChordEnergy f a b := by
  rw [collarChordEnergy_eq_source]
  exact autocorr_zero_nonneg _

theorem collarChordEnergy_le_averaged_deficit (f : C_c(ℝ, ℝ)) (a b : ℝ) :
    collarChordEnergy f a b ≤ 2 * (autocorr f 0 - correlationAverage f a b 0) := by
  have h := collarEnergy_le_origin f a b
  dsimp [collarChordEnergy]
  linarith only [h]

/-- Transport through the entire collar spends its coherent squared norm. -/
theorem pairing_sub_chebyshevWork_sq_le_coherent (f : C_c(ℝ, ℝ)) (a b : ℝ) (N : ℕ) :
    (pairing N (autocorr f) - chebyshevWork f a b N) ^ 2 ≤
      packetEnergy f N * collarChordEnergy f a b := by
  have hs := sourcePair_sq_le (sourceResidual f (collarSource f a b) 1) (signedSource f N)
  rw [sourcePair_comm, sourcePair_sub_right,
    sourcePair_comm (signedSource f N) f, sourcePair_source_packet,
    sourcePair_comm (signedSource f N) (collarSource f a b), sourcePair_collar_packet,
    one_mul, ← collarChordEnergy_eq_source] at hs
  simpa only [packetEnergy, mul_comm] using hs

/-- The Schur constraint transfers to the admitted literal half-line scalars. -/
theorem fullChebyshevWork_schur (f : C_c(ℝ, ℝ)) (a b : ℝ) (K : ℕ) :
    (fullChebyshevWork f a b -
      correlationAverage f a b 0 * fullPairing (autocorr f) / autocorr f 0) ^ 2 ≤
        collarSchurEnergy f a b *
          (packetEnergy f (sourceCutoff f + K) - fullPairing (autocorr f) ^ 2 / autocorr f 0) := by
  have hs := chebyshevWork_schur f a b (sourceCutoff f + K)
  unfold signedPacketSchurEnergy at hs
  rw [chebyshevWork_eq_full f a b _ (Nat.le_add_right _ _),
    ← fullPairing_autocorr_eq f _ (Nat.le_add_right _ _)] at hs
  exact hs

/-- Global Chebyshev work forces the packet's source-orthogonal energy as well. -/
theorem packetEnergy_lower_bound_from_fullWork (f : C_c(ℝ, ℝ)) (a b : ℝ) (K : ℕ) :
    fullPairing (autocorr f) ^ 2 / autocorr f 0 +
      (fullChebyshevWork f a b -
        correlationAverage f a b 0 * fullPairing (autocorr f) / autocorr f 0) ^ 2 /
          collarSchurEnergy f a b ≤ packetEnergy f (sourceCutoff f + K) := by
  have hs := packetEnergy_lower_bound_from_work f a b (sourceCutoff f + K)
  rw [chebyshevWork_eq_full f a b _ (Nat.le_add_right _ _),
    ← fullPairing_autocorr_eq f _ (Nat.le_add_right _ _)] at hs
  exact hs

/-- Coherent global signed transport at every source-admitted packet cutoff. -/
theorem fullPairing_sub_work_sq_le_coherent (f : C_c(ℝ, ℝ)) (a b : ℝ) (K : ℕ) :
    (fullPairing (autocorr f) - fullChebyshevWork f a b) ^ 2 ≤
      packetEnergy f (sourceCutoff f + K) * collarChordEnergy f a b := by
  have hs := pairing_sub_chebyshevWork_sq_le_coherent f a b (sourceCutoff f + K)
  rw [chebyshevWork_eq_full f a b _ (Nat.le_add_right _ _),
    ← fullPairing_autocorr_eq f _ (Nat.le_add_right _ _)] at hs
  exact hs

end
end GaloisForLFunctions.BiScaleUncertainty.SignedPrimePolar
