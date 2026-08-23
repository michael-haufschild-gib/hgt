import GaloisForLFunctions.HTGeometry.DirectionalVandermondePhaseJet
import GaloisForLFunctions.HTGeometry.VandermondeSign

open Complex
open scoped BigOperators Matrix

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Crude but dimension-explicit determinant bound in entrywise norm. -/
theorem norm_det_le_factorial_mul_pow
    {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) {B : ℝ}
    (_hB : 0 ≤ B) (hentry : ∀ i j, ‖M i j‖ ≤ B) :
    ‖M.det‖ ≤ r.factorial * B ^ r := by
  classical
  rw [Matrix.det_apply']
  calc
    ‖∑ σ : Equiv.Perm (Fin r),
        ((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M (σ i) i‖ ≤
        ∑ σ : Equiv.Perm (Fin r),
          ‖((Equiv.Perm.sign σ : ℤ) : ℂ) * ∏ i, M (σ i) i‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _σ : Equiv.Perm (Fin r), B ^ r := by
      apply Finset.sum_le_sum
      intro σ hσ
      have hsign : ‖((Equiv.Perm.sign σ : ℤ) : ℂ)‖ = 1 := by
        rw [Complex.norm_intCast]
        norm_num [← Int.cast_abs, Equiv.Perm.sign_abs]
      rw [norm_mul, hsign, one_mul, norm_prod]
      simpa using
        (Finset.prod_le_prod
          (s := Finset.univ)
          (fun i _hi => norm_nonneg (M (σ i) i))
          (fun i _hi => hentry (σ i) i))
    _ = r.factorial * B ^ r := by
      simp [Fintype.card_perm, nsmul_eq_mul]

/-- Every adjugate coefficient obeys the same determinant bound after one
row is replaced by a coordinate row. -/
theorem norm_adjugate_apply_le_factorial_mul_pow
    {r : ℕ} (M : Matrix (Fin r) (Fin r) ℂ) {B : ℝ}
    (hB : 1 ≤ B) (hentry : ∀ i j, ‖M i j‖ ≤ B) (i j : Fin r) :
    ‖M.adjugate i j‖ ≤ r.factorial * B ^ r := by
  rw [Matrix.adjugate_apply]
  apply norm_det_le_factorial_mul_pow _ (le_trans zero_le_one hB)
  intro a b
  simp only [Matrix.updateRow_apply]
  split_ifs with ha
  · subst a
    by_cases hbi : b = i
    · subst b
      simpa using hB
    · simp [Pi.single, hbi, le_trans zero_le_one hB]
  · exact hentry a b

/-- Entrywise norm cap for a Vandermonde matrix from a common frequency cap. -/
theorem norm_vandermonde_apply_le_pow
    {r : ℕ} {lam : Fin r → ℂ} {B : ℝ}
    (hB : 1 ≤ B) (hlam : ∀ j, ‖lam j‖ ≤ B) (i j : Fin r) :
    ‖Matrix.vandermonde lam i j‖ ≤ B ^ (r - 1) := by
  rw [Matrix.vandermonde_apply, norm_pow]
  exact (pow_le_pow_left₀ (norm_nonneg _) (hlam i) (j : ℕ)).trans
    (pow_le_pow_right₀ hB (by omega : (j : ℕ) ≤ r - 1))

/-- **Quantitative phase-jet discriminant law.**  The full spectral
discriminant, rather than the minimum gap, controls a complete phase jet.
For every coefficient coordinate, its evolved amplitude times the
Vandermonde determinant is bounded by an explicit factorial/polynomial cap
times the `ℓ1` mass of the first `r` time derivatives. -/
theorem vandermondeDet_mul_evolvedCoefficient_le_phaseJet_l1
    {r : ℕ} {lam c : Fin r → ℂ} {B : ℝ}
    (hB : 1 ≤ B) (hlam : ∀ j, ‖lam j‖ ≤ B)
    (t : ℂ) (j : Fin r) :
    ‖(Matrix.vandermonde lam).det‖ *
        ‖c j * Complex.exp (lam j * t)‖ ≤
      r.factorial * (B ^ (r - 1)) ^ r *
        ∑ k : Fin r, ‖iteratedDeriv (k : ℕ) (phasePolynomial lam c) t‖ := by
  classical
  let V : Matrix (Fin r) (Fin r) ℂ := (Matrix.vandermonde lam)ᵀ
  let a : Fin r → ℂ := fun i => c i * Complex.exp (lam i * t)
  let y : Fin r → ℂ := V.mulVec a
  have hy (k : Fin r) :
      y k = iteratedDeriv (k : ℕ) (phasePolynomial lam c) t := by
    rw [iteratedDeriv_phasePolynomial]
    change (∑ i, lam i ^ (k : ℕ) *
      (c i * Complex.exp (lam i * t))) = _
    apply Finset.sum_congr rfl
    intro i hi
    ring
  have hcramer : V.adjugate.mulVec y = V.det • a := by
    change V.adjugate.mulVec (V.mulVec a) = V.det • a
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul]
    rw [Matrix.smul_mulVec, Matrix.one_mulVec]
  have hcoord := congrArg (fun z : Fin r → ℂ => z j) hcramer
  have hVentry : ∀ i k, ‖V i k‖ ≤ B ^ (r - 1) := by
    intro i k
    exact norm_vandermonde_apply_le_pow hB hlam k i
  have hBadj : 1 ≤ B ^ (r - 1) := one_le_pow₀ hB
  calc
    ‖(Matrix.vandermonde lam).det‖ *
        ‖c j * Complex.exp (lam j * t)‖ =
        ‖V.det * a j‖ := by
      rw [norm_mul]
      simp [V, a]
    _ = ‖∑ k, V.adjugate j k * y k‖ := by
      rw [show V.det * a j = V.adjugate.mulVec y j by
        simpa [Pi.smul_apply, smul_eq_mul] using hcoord.symm]
      rfl
    _ ≤ ∑ k, ‖V.adjugate j k * y k‖ := norm_sum_le _ _
    _ ≤ ∑ k, (r.factorial * (B ^ (r - 1)) ^ r) * ‖y k‖ := by
      gcongr with k
      rw [norm_mul]
      exact mul_le_mul_of_nonneg_right
        (norm_adjugate_apply_le_factorial_mul_pow V hBadj hVentry j k)
        (norm_nonneg _)
    _ = r.factorial * (B ^ (r - 1)) ^ r *
        ∑ k : Fin r, ‖iteratedDeriv (k : ℕ) (phasePolynomial lam c) t‖ := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k hk
      rw [hy k]

/-- Intrinsic phase-frequency scale.  Adding one makes it nondegenerate at
zero frequency and removes every external cap from the quantitative law. -/
def phaseFrequencyScale {r : ℕ} (lam : Fin r → ℂ) : ℝ :=
  1 + ∑ j : Fin r, ‖lam j‖

theorem one_le_phaseFrequencyScale {r : ℕ} (lam : Fin r → ℂ) :
    1 ≤ phaseFrequencyScale lam := by
  rw [phaseFrequencyScale]
  exact le_add_of_nonneg_right (Finset.sum_nonneg fun _ _ => norm_nonneg _)

theorem norm_le_phaseFrequencyScale {r : ℕ} (lam : Fin r → ℂ) (j : Fin r) :
    ‖lam j‖ ≤ phaseFrequencyScale lam := by
  rw [phaseFrequencyScale]
  exact (Finset.single_le_sum (fun i _ => norm_nonneg (lam i))
    (Finset.mem_univ j)).trans (le_add_of_nonneg_left zero_le_one)

/-- **Unconditional quantitative phase-jet discriminant law.**  No spacing,
injectivity, or spectral-cap premise is required.  The full Vandermonde
product controls every evolved modal coefficient through the first `r`
derivatives, at the intrinsic frequency scale.  Collision automatically
sets the discriminant side to zero; away from collision the conclusion is a
quantitative same-draw observability bound. -/
theorem universal_vandermondeDiscriminant_phaseJet_l1
    {r : ℕ} (lam c : Fin r → ℂ) (t : ℂ) (j : Fin r) :
    ‖vandermondeProd lam‖ * ‖c j * Complex.exp (lam j * t)‖ ≤
      r.factorial * (phaseFrequencyScale lam ^ (r - 1)) ^ r *
        ∑ k : Fin r, ‖iteratedDeriv (k : ℕ) (phasePolynomial lam c) t‖ := by
  rw [← det_vandermonde_eq_vandermondeProd]
  exact vandermondeDet_mul_evolvedCoefficient_le_phaseJet_l1
    (one_le_phaseFrequencyScale lam) (norm_le_phaseFrequencyScale lam) t j

/-- **Single-jet spectral-action law.**  At every time and for every chosen
occupied spectral coordinate, one derivative of order below spectral rank
captures the discriminant-weighted modal mass.  This is the endpoint-count-
free maximum form needed before a circuit union. -/
theorem exists_phaseJet_discriminant_response
    {r : ℕ} (lam c : Fin r → ℂ) (t : ℂ) (j : Fin r) :
    ∃ k : Fin r,
      ‖vandermondeProd lam‖ * ‖c j * Complex.exp (lam j * t)‖ ≤
        (r.factorial * (phaseFrequencyScale lam ^ (r - 1)) ^ r * r) *
          ‖iteratedDeriv (k : ℕ) (phasePolynomial lam c) t‖ := by
  let d : Fin r → ℝ := fun k =>
    ‖iteratedDeriv (k : ℕ) (phasePolynomial lam c) t‖
  obtain ⟨k, _hk, hkmax⟩ := Finset.exists_max_image Finset.univ d
    ⟨j, Finset.mem_univ j⟩
  refine ⟨k, (universal_vandermondeDiscriminant_phaseJet_l1 lam c t j).trans ?_⟩
  have hsum : ∑ q : Fin r, d q ≤ r * d k := by
    simpa [nsmul_eq_mul] using
      Finset.sum_le_card_nsmul Finset.univ d (d k)
        (fun q hq => hkmax q hq)
  have hC : 0 ≤ r.factorial * (phaseFrequencyScale lam ^ (r - 1)) ^ r := by
    exact mul_nonneg (Nat.cast_nonneg _)
      (pow_nonneg (pow_nonneg
        (le_trans zero_le_one (one_le_phaseFrequencyScale lam)) _) _)
  calc
    r.factorial * (phaseFrequencyScale lam ^ (r - 1)) ^ r *
          ∑ q : Fin r, ‖iteratedDeriv (q : ℕ) (phasePolynomial lam c) t‖ =
        (r.factorial * (phaseFrequencyScale lam ^ (r - 1)) ^ r) * ∑ q, d q := rfl
    _ ≤ (r.factorial * (phaseFrequencyScale lam ^ (r - 1)) ^ r) * (r * d k) :=
      mul_le_mul_of_nonneg_left hsum hC
    _ = (r.factorial * (phaseFrequencyScale lam ^ (r - 1)) ^ r * r) *
          ‖iteratedDeriv (k : ℕ) (phasePolynomial lam c) t‖ := by
      simp [d]
      ring

/-- Frequencies generated by a time-independent self-adjoint Hamiltonian
with real energy list `E`. -/
def realSpectrumFrequency {r : ℕ} (E : Fin r → ℝ) : Fin r → ℂ :=
  fun j => -Complex.I * (E j : ℂ)

@[simp] theorem phaseFrequencyScale_realSpectrumFrequency
    {r : ℕ} (E : Fin r → ℝ) :
    phaseFrequencyScale (realSpectrumFrequency E) = 1 + ∑ j : Fin r, |E j| := by
  simp [phaseFrequencyScale, realSpectrumFrequency]

@[simp] theorem norm_exp_realSpectrumFrequency_mul_real
    {r : ℕ} (E : Fin r → ℝ) (j : Fin r) (t : ℝ) :
    ‖Complex.exp (realSpectrumFrequency E j * (t : ℂ))‖ = 1 := by
  rw [Complex.norm_exp]
  simp [realSpectrumFrequency]

/-- **Static-Hamiltonian discriminant response law.**  For every finite real
spectrum, every coefficient family, every laboratory time, and every occupied
coordinate, one time derivative below spectral rank carries an explicit
fraction of its modal mass.  No gap premise appears: the controlling invariant
is the full spectral discriminant. -/
theorem exists_staticHamiltonian_discriminant_response
    {r : ℕ} (E : Fin r → ℝ) (c : Fin r → ℂ) (t : ℝ) (j : Fin r) :
    ∃ k : Fin r,
      ‖vandermondeProd (realSpectrumFrequency E)‖ * ‖c j‖ ≤
        (r.factorial *
          ((1 + ∑ i : Fin r, |E i|) ^ (r - 1)) ^ r * r) *
          ‖iteratedDeriv (k : ℕ)
            (phasePolynomial (realSpectrumFrequency E) c) (t : ℂ)‖ := by
  obtain ⟨k, hk⟩ := exists_phaseJet_discriminant_response
    (realSpectrumFrequency E) c (t : ℂ) j
  refine ⟨k, ?_⟩
  simpa [norm_mul] using hk

end

end GaloisForLFunctions.HTGeometry
