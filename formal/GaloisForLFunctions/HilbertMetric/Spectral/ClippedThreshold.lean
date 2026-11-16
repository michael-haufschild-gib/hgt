import GaloisForLFunctions.HilbertMetric.Spectral.ClippedFunctionalCalculus
import GaloisForLFunctions.HTGeometry.RiemannGaussian.HermitianRankTrace.RankTrace

/-!
# Clipped energy under Hermitian perturbations

Subtracting a positive matrix pays a linear trace cost. Splitting a Hermitian
perturbation into its orthogonal positive and negative parts then charges only
its positive index. This is the threshold inequality of arXiv:2609.33043, Lemma 4.
-/

open Matrix RiemannGaussian.HermitianRankTrace
open scoped ComplexOrder NNReal
namespace GaloisForLFunctions.HilbertMetric.Clipped
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- A positive subtraction cannot remove clipped energy for less than its trace cost. -/
theorem energy_le_sub_square {P Z : Matrix ι ι ℂ} (hP : P.IsHermitian)
    (hZ : Z.PosSemidef) (c : ℝ) :
    energy c P ≤ (trace ((P - Z) * (P - Z))).re + 2 * c * (trace Z).re := by
  let C := certificate hP c
  have hC := certificate_hermitian hP c
  have hcap := certificate_cap hP c
  have hatt := certificate_attains hP c
  have hs : 0 ≤ (trace ((P - Z - C) * (P - Z - C))).re := by
    rw [trace_square ((hP.sub hZ.isHermitian).sub hC)]
    exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => Complex.normSq_nonneg _
  have hp : 0 ≤ (trace (((c : ℂ) • (1 : Matrix ι ι ℂ) - C) * Z)).re :=
    trace_mul_nonneg_of_posSemidef hcap hZ
  have hid : (trace ((P - Z) * (P - Z))).re + 2 * c * (trace Z).re -
      (2 * (trace (C * P)).re - (trace (C * C)).re) =
      (trace ((P - Z - C) * (P - Z - C))).re +
        2 * (trace (((c : ℂ) • (1 : Matrix ι ι ℂ) - C) * Z)).re := by
    simp only [Matrix.sub_mul, Matrix.mul_sub, Matrix.smul_mul, Matrix.one_mul,
      Matrix.trace_sub, Matrix.trace_smul, Complex.sub_re, smul_eq_mul,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [Matrix.trace_mul_comm P C, Matrix.trace_mul_comm Z C]
    ring
  change 2 * (trace (C * P)).re - (trace (C * C)).re = energy c P at hatt
  linarith only [hs, hp, hid, hatt]

/-- Positive spectral modes pay a square penalty once per mode. -/
theorem positive_part_square_bound {Q : Matrix ι ι ℂ} (hQ : Q.IsHermitian) (c : ℝ) :
    2 * c * (trace (hermPosPart hQ)).re - c ^ 2 * posIndex hQ ≤
      (trace (hermPosPart hQ * hermPosPart hQ)).re := by
  have hb : (Finset.univ.filter (fun i => (hQ.eigenvalues i)⁺ ≠ 0)).card ≤ posIndex hQ := by
    simp only [posIndex, ne_eq, posPart_eq_zero, not_le]
    exact le_rfl
  have h := sum_sq_lower_of_card_pos_le hb c
  rw [← rtrace_hermPosPart, ← frobSq_hermPosPart] at h
  simpa only [rtrace, frobSq, (hermPosPart_posSemidef hQ).isHermitian.eq] using h

/-- A Hermitian perturbation costs only its number of positive eigenvalues. -/
theorem threshold {P Q : Matrix ι ι ℂ} (hP : P.PosSemidef) (hQ : Q.IsHermitian)
    (c : ℝ) :
    2 * c * (trace Q).re + energy c P - c ^ 2 * posIndex hQ ≤
      (trace ((P + Q) * (P + Q))).re := by
  let Qp := hermPosPart hQ
  let Qm := hermNegPart hQ
  have hm := hermNegPart_posSemidef hQ
  have hp := hermPosPart_posSemidef hQ
  have hdec : Q = Qp - Qm := (hermPosPart_sub_hermNegPart hQ).symm
  have horth : Qm * Qp = 0 := hermNegPart_mul_hermPosPart hQ
  have horth' : Qp * Qm = 0 := hermPosPart_mul_hermNegPart hQ
  have hcross : 0 ≤ (trace (P * Qp)).re := trace_mul_nonneg_of_posSemidef hP hp
  have hsub := energy_le_sub_square hP.isHermitian hm c
  have hpos := positive_part_square_bound hQ c
  have hid : (trace ((P + Q) * (P + Q))).re =
      (trace ((P - Qm) * (P - Qm))).re + (trace (Qp * Qp)).re +
        2 * (trace (P * Qp)).re := by
    rw [hdec]
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub,
      horth, horth', Matrix.trace_add, Matrix.trace_sub, Matrix.trace_zero,
      Complex.add_re, Complex.sub_re, Complex.zero_re, sub_zero]
    rw [Matrix.trace_mul_comm Qp P]
    ring
  have ht : (trace Q).re = (trace Qp).re - (trace Qm).re := by
    rw [hdec, Matrix.trace_sub, Complex.sub_re]
  change energy c P ≤ (trace ((P - Qm) * (P - Qm))).re + 2 * c * (trace Qm).re at hsub
  change 2 * c * (trace Qp).re - c ^ 2 * posIndex hQ ≤ (trace (Qp * Qp)).re at hpos
  rw [ht]
  linarith only [hsub, hpos, hid, hcross]

end
end GaloisForLFunctions.HilbertMetric.Clipped
