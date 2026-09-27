import GaloisForLFunctions.RHTower.XiCriticalPairSourceReserve
import GaloisForLFunctions.HTGeometry.WeightedVandermondeSamplingEnergy

/-!
# A paired critical-node floor retaining every cofactor and heat weight

Both Schwarz partners of each positive critical node contribute the same
complete polynomial sample. Weighted interpolation retains all node rates
and cofactor norms. The resulting coefficient-independent floor is at least
twice the previous common-cap, largest-node floor for the same nodes.
-/

open scoped Real BigOperators
open Complex GaloisForLFunctions.HTGeometry
noncomputable section

namespace RHTower

def xiCriticalSamplingHeatFloor {N : ℕ} (γ : Fin N → ℝ) (t : ℝ) : ℝ :=
  2 * ‖(Matrix.vandermonde (fun i => (γ i : ℂ) ^ 2)).det‖ ^ 2 /
    polynomialSamplingHeatCapacity (fun i => (γ i : ℂ) ^ 2) (fun i => γ i ^ 2) t

/-- Actual critical nodes give a strictly positive all-time floor, uniformly in every
coefficient. The improved floor dominates twice the previous floor for these same nodes. -/
theorem exists_xiGaussianRealChannel_paired_weighted_floor (n : ℕ) :
    ∃ (γ : Fin (n + 1) → ℝ) (q : Fin (n + 1) → XiZeroCopy)
      (iMax : Fin (n + 1)) (c : ℝ),
      0 < c ∧ Function.Injective (fun i => (γ i : ℂ) ^ 2) ∧
      (∀ i, 0 < γ i ∧ xiSpectralPoint (q i) = (γ i : ℂ)) ∧
      (∀ i, γ i ^ 2 ≤ γ iMax ^ 2) ∧
      c = ‖(Matrix.vandermonde (fun i => (γ i : ℂ) ^ 2)).det‖ ^ 2 /
        (((n + 1 : ℕ) : ℝ) ^ 2 * polynomialSamplingCap (fun i => (γ i : ℂ) ^ 2) ^ 2) ∧
      ∀ t : {t : ℝ // 0 < t},
        0 < xiCriticalSamplingHeatFloor γ t ∧
        2 * c * Real.exp (-(γ iMax ^ 2 * (t : ℝ))) ≤ xiCriticalSamplingHeatFloor γ t ∧
        ∀ a : ℕ → ℝ,
          xiCriticalSamplingHeatFloor γ t * (∑ j ∈ Finset.range (n + 1), a j ^ 2) ≤
            xiGaussianRealChannelEnergy
              (∑ j ∈ Finset.range (n + 1), Polynomial.C (a j) * Polynomial.X ^ j) t := by
  classical
  let N := n + 1
  obtain ⟨γ, q, iMax, c, hc, hinj, hq, hmax, hcdef, _⟩ :=
    exists_xiGaussianRealChannel_maxNode_floor n
  let z : Fin N → ℂ := fun i => (γ i : ℂ) ^ 2
  let rate : Fin N → ℝ := fun i => γ i ^ 2
  let C := polynomialSamplingCap z
  let A : ℝ := (N : ℝ) ^ 2 * C ^ 2
  let D : ℝ := ‖(Matrix.vandermonde z).det‖ ^ 2
  have hD : 0 < D := pow_pos
    (norm_pos_iff.mpr (Matrix.det_vandermonde_ne_zero_iff.mpr hinj)) _
  have hC : 0 < C := by
    unfold C polynomialSamplingCap
    exact mul_pos (by positivity)
      (pow_pos (pow_pos (lt_of_lt_of_le zero_lt_one (one_le_phaseFrequencyScale z)) _) _)
  have hA : 0 < A := by dsimp only [A, N]; positivity
  have hqinj : Function.Injective q := by
    intro i j hij
    apply hinj
    change (γ i : ℂ) ^ 2 = (γ j : ℂ) ^ 2
    rw [← (hq i).2, ← (hq j).2, hij]
  let S := Finset.univ.image q
  let T := Finset.univ.image (fun i => xiZeroCopyConjEquiv (q i))
  have hCinj : Function.Injective (fun i => xiZeroCopyConjEquiv (q i)) :=
    xiZeroCopyConjEquiv.injective.comp hqinj
  have hdisj : Disjoint S T := by
    apply Finset.disjoint_left.mpr
    intro p hpS hpT
    obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hpS
    obtain ⟨j, _, hj⟩ := Finset.mem_image.mp hpT
    have he : q i = xiZeroCopyConjEquiv (q j) := hi.trans hj.symm
    have hre := congrArg (fun r : XiZeroCopy => (xiSpectralPoint r).re) he
    rw [(hq i).2, xiSpectralPoint_copyConj, (hq j).2,
      Complex.neg_re, Complex.conj_re, Complex.ofReal_re, Complex.ofReal_re] at hre
    linarith only [hre, (hq i).1, (hq j).1]
  refine ⟨γ, q, iMax, c, hc, hinj, hq, hmax, hcdef, ?_⟩
  intro t
  let B := polynomialSamplingHeatCapacity z rate t
  have hB : 0 < B := polynomialSamplingHeatCapacity_pos n ⟨z, hinj⟩ rate t
  have hBupper : B ≤ A * Real.exp (γ iMax ^ 2 * (t : ℝ)) := by
    have he : (∑ i : Fin N, Real.exp ((t : ℝ) * rate i)) ≤
        (N : ℝ) * Real.exp (γ iMax ^ 2 * (t : ℝ)) := by
      have h := Finset.sum_le_sum (s := Finset.univ) (fun i _ =>
        Real.exp_le_exp.mpr (show (t : ℝ) * rate i ≤ γ iMax ^ 2 * (t : ℝ) by
          dsimp only [rate]
          nlinarith only [mul_le_mul_of_nonneg_right (hmax i) t.property.le]))
      simpa only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] using h
    have h := (polynomialSamplingHeatCapacity_le_common_cap z rate t).trans
      (mul_le_mul_of_nonneg_left he (show 0 ≤ (N : ℝ) * C ^ 2 by positivity))
    change B ≤ _ at h
    calc
      B ≤ _ := h
      _ = _ := by dsimp only [A]; ring
  have hpos : 0 < xiCriticalSamplingHeatFloor γ t := div_pos (mul_pos (by positivity) hD) hB
  refine ⟨hpos, ?_, ?_⟩
  · have hdiv := div_le_div_of_nonneg_left (show 0 ≤ 2 * D by positivity) hB hBupper
    have hc' : c = D / A := hcdef
    change 2 * c * Real.exp (-(γ iMax ^ 2 * (t : ℝ))) ≤ 2 * D / B
    calc
      _ = 2 * D / (A * Real.exp (γ iMax ^ 2 * (t : ℝ))) := by
        rw [hc', Real.exp_neg]
        field_simp
      _ ≤ _ := hdiv
  · intro a
    let Q : Polynomial ℝ := ∑ j ∈ Finset.range N, Polynomial.C (a j) * Polynomial.X ^ j
    let v : Fin N → ℂ := fun j => (a j : ℂ)
    let J := xiGaussianRealChannelEnergy Q t
    let f : XiZeroCopy → ℝ := fun p =>
      (‖xiPolynomialGaussianHeatTerm Q t p‖ + (xiPolynomialGaussianHeatTerm Q t p).re) / 2
    have heval (i : Fin N) : ‖polynomialSample v (z i)‖ ^ 2 = (Q.eval (γ i ^ 2)) ^ 2 := by
      have he : evalRealPolynomial Q (z i) = polynomialSample v (z i) := by
        rw [evalRealPolynomial_rangeSum, ← Fin.sum_univ_eq_sum_range]
        rfl
      rw [← he]
      simp only [z, ← Complex.ofReal_pow, evalRealPolynomial_ofReal,
        Complex.norm_real, Real.norm_eq_abs, sq_abs]
    have hpair (i : Fin N) : f (xiZeroCopyConjEquiv (q i)) = f (q i) := by
      have hpartner : xiSpectralPoint (xiZeroCopyConjEquiv (q i)) = ((-γ i : ℝ) : ℂ) := by
        rw [xiSpectralPoint_copyConj, (hq i).2, Complex.conj_ofReal, Complex.ofReal_neg]
      dsimp only [f]
      rw [xiGaussianRealChannel_atom_at_real Q t (-γ i) ⟨_, hpartner⟩,
        xiGaussianRealChannel_atom_at_real Q t (γ i) ⟨q i, (hq i).2⟩, neg_sq]
    have hsum : 2 * (∑ i : Fin N, ‖polynomialSample v (z i)‖ ^ 2 *
        Real.exp (-((t : ℝ) * rate i))) ≤ J := by
      have h := (summable_xiGaussianRealChannel_atom Q t).sum_le_tsum (S ∪ T)
        (fun p _ => xiGaussianRealChannel_atom_nonneg Q t p)
      change (∑ p ∈ S ∪ T, f p) ≤ J at h
      rw [Finset.sum_union hdisj] at h
      dsimp only [S, T] at h
      rw [Finset.sum_image (fun i _ j _ hij => hqinj hij),
        Finset.sum_image (fun i _ j _ hij => hCinj hij)] at h
      simp only [hpair, f, xiGaussianRealChannel_atom_at_real Q t (γ _) ⟨q _, (hq _).2⟩] at h
      simp only [heval, rate]
      linarith only [h]
    have hsamp := polynomialSample_heat_weighted_energy_bound z v rate t
    have hcoeff : (∑ j : Fin N, ‖v j‖ ^ 2) = ∑ j ∈ Finset.range N, a j ^ 2 := by
      simp only [v, Complex.norm_real, Real.norm_eq_abs, sq_abs]
      exact Fin.sum_univ_eq_sum_range (fun j => a j ^ 2) N
    rw [hcoeff] at hsamp
    have hdiv : D / B * (∑ j ∈ Finset.range N, a j ^ 2) ≤
        ∑ i : Fin N, ‖polynomialSample v (z i)‖ ^ 2 * Real.exp (-((t : ℝ) * rate i)) := by
      rw [div_mul_eq_mul_div, div_le_iff₀ hB]
      simpa only [mul_comm] using hsamp
    change (2 * D / B) * (∑ j ∈ Finset.range N, a j ^ 2) ≤ J
    nlinarith only [hdiv, hsum]

/-- The exact same independent paired floor also bounds the complete positive norm energy. -/
theorem exists_xiGaussianEnergy_paired_weighted_floor (n : ℕ) :
    ∃ γ : Fin (n + 1) → ℝ,
      (∃ q : Fin (n + 1) → XiZeroCopy,
        ∀ i, 0 < γ i ∧ xiSpectralPoint (q i) = (γ i : ℂ)) ∧
      ∀ t : {t : ℝ // 0 < t}, 0 < xiCriticalSamplingHeatFloor γ t ∧
        ∀ a : ℕ → ℝ,
          xiCriticalSamplingHeatFloor γ t * (∑ j ∈ Finset.range (n + 1), a j ^ 2) ≤
            ∑' q : XiZeroCopy, ‖xiPolynomialGaussianHeatTerm
              (∑ j ∈ Finset.range (n + 1), Polynomial.C (a j) * Polynomial.X ^ j) t q‖ := by
  obtain ⟨γ, q, _, _, _, _, hq, _, _, hfloor⟩ :=
    exists_xiGaussianRealChannel_paired_weighted_floor n
  refine ⟨γ, ⟨q, hq⟩, ?_⟩
  intro t
  exact ⟨(hfloor t).1, fun a =>
    ((hfloor t).2.2 a).trans (xiGaussianRealChannelEnergy_le_energy _ t)⟩

end RHTower
