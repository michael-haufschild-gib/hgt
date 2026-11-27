import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.EnergySpread
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.PhaseStability
import GaloisForLFunctions.HTGeometry.RiemannGaussian.HermitianRankTrace.VonNeumann

/-! # Finite-time phase prediction from the diagonal in a frozen eigenbasis -/

open Matrix Finset
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields
open SpectralGapMass.Bulk
open _root_.RiemannGaussian.HermitianRankTrace
open private phase_lipschitz from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.Bulk.PhaseStability
noncomputable section
variable {I : Type*} [Fintype I] [DecidableEq I]
private abbrev Mat (I : Type*) := Matrix I I ℂ

/-- Diagonal expectation of the generator in the specified orthonormal frame. -/
def diagonalEnergy (U : unitaryGroup I ℂ) (B : Mat I) (j : I) : ℝ :=
  ((U.valᴴ*B*U.val) j j).re

private def wave (t x : ℝ) : ℂ := Complex.exp (-(Complex.I*((t:ℂ)*x)))

/-- Evolution obtained by retaining the diagonal energies in one fixed frame. -/
def diagonalPrediction (U : unitaryGroup I ℂ) (B : Mat I) (t : ℝ) : Mat I :=
  U.val*diagonal (fun j => wave t (diagonalEnergy U B j))*U.valᴴ

private theorem sq_chord (t x y : ℝ) :
    ‖wave t x-wave t y‖^2 ≤ 2*|t| *|x-y| := by
  have hu (a : ℝ) : ‖wave t a‖=1 := by simp [wave,Complex.norm_exp]
  have h₂ : ‖wave t x-wave t y‖ ≤ 2 := by
    simpa only [hu,show (1:ℝ)+1=2 by norm_num] using norm_sub_le (wave t x) (wave t y)
  have ht : ‖wave t x-wave t y‖ ≤ |t| *|x-y| := by
    simpa only [wave,←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs] using phase_lipschitz t x y
  rw [sq,mul_assoc]
  exact mul_le_mul h₂ ht (norm_nonneg _) (by norm_num)

private theorem diagonalEnergy_spectral (U : unitaryGroup I ℂ) {B : Mat I} (hB : B.IsHermitian) :
    let V := hB.eigenvectorUnitary
    let W := U⁻¹*V
    diagonalEnergy U B = rowMean (normSqMatrix W.val) hB.eigenvalues := by
  intro V W
  have he : U.valᴴ*B*U.val =
      W.val*diagonal (fun i => (hB.eigenvalues i:ℂ))*W.valᴴ := by
    conv_lhs => rw [isHermitian_eq_conj_diagonal hB]
    change _=(U.valᴴ*V.val)*_*(U.valᴴ*V.val)ᴴ
    rw [conjTranspose_mul,conjTranspose_conjTranspose]
    simp only [mul_assoc,V,Matrix.star_eq_conjTranspose]
  funext j
  unfold diagonalEnergy
  rw [he,Matrix.mul_apply,Complex.re_sum]
  apply sum_congr rfl
  intro i _
  rw [mul_diagonal,conjTranspose_apply]
  have h : W.val j i * (hB.eigenvalues i:ℂ) * star (W.val j i) =
      (((‖W.val j i‖^2 * hB.eigenvalues i:ℝ)):ℂ) := by
    rw [show W.val j i * (hB.eigenvalues i:ℂ) * star (W.val j i) =
      (W.val j i * star (W.val j i)) * hB.eigenvalues i by ring,Complex.star_def,Complex.mul_conj']
    push_cast
    ring
  rw [h,Complex.ofReal_re]
  rfl

/-- Dropping off-diagonal entries costs at most the loss of pairwise
spectral spread times twice the elapsed time in squared Frobenius distance. -/
theorem diagonal_prediction_error (U : unitaryGroup I ℂ) (B : selfAdjoint (Mat I)) (t : ℝ) :
    hsNormSq (unitaryEvolution B.val t-diagonalPrediction U B.val t) ≤
      2*|t| *(spread B.2.isHermitian.eigenvalues-spread (diagonalEnergy U B.val)) := by
  let V := B.2.isHermitian.eigenvectorUnitary
  let W := U⁻¹*V
  let p := normSqMatrix W.val
  let e := B.2.isHermitian.eigenvalues
  let b := diagonalEnergy U B.val
  have he : unitaryEvolution B.val t=V.val*diagonal (fun i => wave t (e i))*V.valᴴ :=
    unitaryEvolution_spectral B.2.isHermitian t
  have hmean : b=rowMean p e := diagonalEnergy_spectral U B.2.isHermitian
  have hDS := normSqMatrix_mem_doublyStochastic_of_unitary W.2
  rw [mem_doublyStochastic_iff_sum] at hDS
  obtain ⟨hn,hr,hc⟩ := hDS
  have hd := deviation_le_spread_loss (p:=p) hn hr hc e
  rw [←hmean] at hd
  have hQ : V.valᴴ*U.val=W.valᴴ := by
    change _=(U.valᴴ*V.val)ᴴ
    rw [conjTranspose_mul,conjTranspose_conjTranspose]
  rw [he,diagonalPrediction,spectral_displacement V.val U.val V.2 U.2,hQ]
  calc
    _ ≤ 2*|t| *(∑ j, rowMean p (fun i => |e i-b j|) j) := by
      simp only [rowMean,mul_sum]
      apply sum_le_sum
      intro j _
      apply sum_le_sum
      intro i _
      rw [conjTranspose_apply,norm_star]
      exact (mul_le_mul_of_nonneg_right (sq_chord t (e i) (b j)) (sq_nonneg _)).trans_eq (by
        change _=(2*|t|)*(‖W.val j i‖^2*|e i-b j|)
        ring)
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith only [hd]) (by positivity)

/-- The generator's energy spread, with each ordered pair counted once. -/
def spectralSpread (B : selfAdjoint (Mat I)) := spread B.2.isHermitian.eigenvalues

/-- Squared error for evolving the perturbed generator using phases linear
in that generator and the eigenvectors of the base Hamiltonian. -/
def predictionError (H B : selfAdjoint (Mat I)) (t : ℝ) :=
  hsNormSq (unitaryEvolution B.val t-diagonalPrediction H.2.isHermitian.eigenvectorUnitary B.val t)

/-- Opposite field changes share one error bound at all physical dates.
Eigenvalue multiplicities and arbitrarily small gaps are allowed. -/
theorem paired_prediction_error (H B C : selfAdjoint (Mat I)) {a : ℝ} (ha : 0≤a)
    (hm : B.val+C.val=(2*a) • H.val) (t : ℝ) :
    predictionError H B t + predictionError H C t ≤
      2*|t| *(spectralSpread B+spectralSpread C-2*a*spectralSpread H) := by
  let U := H.2.isHermitian.eigenvectorUnitary
  let e := H.2.isHermitian.eigenvalues
  have hdiag : U.valᴴ*H.val*U.val=diagonal (fun i => (e i:ℂ)) := by
    conv_lhs => rw [isHermitian_eq_conj_diagonal H.2.isHermitian]
    change U.valᴴ*(U.val*diagonal _*U.valᴴ)*U.val=_
    have hu : U.valᴴ*U.val=1 := U.property.1
    simp only [mul_assoc]
    rw [hu,mul_one,←mul_assoc,hu,one_mul]
  have hmid (j : I) : diagonalEnergy U B.val j+diagonalEnergy U C.val j=2*a*e j := by
    have h : U.valᴴ*B.val*U.val+U.valᴴ*C.val*U.val=(2*a) • (U.valᴴ*H.val*U.val) := by
      rw [←add_mul,←mul_add,hm,Matrix.mul_smul,Matrix.smul_mul]
    have hj := congrArg (fun M : Mat I => (M j j).re) h
    simpa only [diagonalEnergy,hdiag,Matrix.add_apply,Complex.add_re,Matrix.smul_apply,
      diagonal_apply_eq,Complex.real_smul,Complex.re_ofReal_mul,Complex.ofReal_re] using hj
  have hs := paired_spread e _ _ a ha hmid
  have h₁ := diagonal_prediction_error U B t
  have h₂ := diagonal_prediction_error U C t
  change hsNormSq (unitaryEvolution B.val t-diagonalPrediction U B.val t)+
      hsNormSq (unitaryEvolution C.val t-diagonalPrediction U C.val t) ≤
      2*|t| *(spread B.2.isHermitian.eigenvalues+spread C.2.isHermitian.eigenvalues-2*a*spread e)
  linarith only [h₁,h₂,mul_le_mul_of_nonneg_left hs (show 0≤2*|t| by positivity)]

#print axioms paired_prediction_error
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields
