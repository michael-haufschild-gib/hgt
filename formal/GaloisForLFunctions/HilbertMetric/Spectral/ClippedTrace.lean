import GaloisForLFunctions.HilbertMetric.Spectral.ClippedScalar
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.HermitianFunctionalCalculus
import Mathlib.Tactic.Positivity

/-!
# Clipped matrix traces and dual certificates

Spectral sums are defined from characteristic roots, so their statements do not
depend on a chosen eigenbasis. On Hermitian matrices they are ordinary real
eigenvalue sums. A bounded Hermitian test matrix gives the dual certificate
`2 tr(B A) - tr(B²) ≤ tr φ_c(A)`.
-/

open Matrix
open scoped ComplexOrder NNReal
namespace GaloisForLFunctions.HilbertMetric.Clipped
noncomputable section
variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- Sum a real observable over the real parts of all characteristic roots. -/
def spectralSum (f : ℝ → ℝ) (A : Matrix ι ι ℂ) : ℝ :=
  (A.charpoly.roots.map (fun z => f z.re)).sum

def energy (c : ℝ) (A : Matrix ι ι ℂ) : ℝ := spectralSum (quadratic c) A

def defectEnergy (τ : ℝ) (A : Matrix ι ι ℂ) : ℝ := spectralSum (defect τ) A

theorem spectralSum_eq {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (f : ℝ → ℝ) :
    spectralSum f A = ∑ i, f (hA.eigenvalues i) := by
  rw [spectralSum, hA.roots_charpoly_eq_eigenvalues, Multiset.map_map]
  rfl

/-- Unitary conjugation preserves every spectral observable. -/
theorem spectralSum_unitary (f : ℝ → ℝ) (V : Matrix.unitaryGroup ι ℂ)
    (A : Matrix ι ι ℂ) :
    spectralSum f ((V : Matrix ι ι ℂ) * A * star (V : Matrix ι ι ℂ)) = spectralSum f A := by
  unfold spectralSum
  rw [Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, Unitary.coe_star_mul_self, Matrix.one_mul]

theorem spectralSum_diagonal (f : ℝ → ℝ) (x : ι → ℝ) :
    spectralSum f (diagonal fun i => (x i : ℂ)) = ∑ i, f (x i) := by
  rw [spectralSum, Matrix.charpoly_diagonal, Polynomial.roots_prod]
  · simp
  · exact Finset.prod_ne_zero_iff.mpr fun i _ => Polynomial.X_sub_C_ne_zero _

/-- Rectangular products have the same spectrum after adding the missing zero roots. -/
theorem spectralSum_rectangular {κ : Type*} [Fintype κ] [DecidableEq κ]
    (f : ℝ → ℝ) (A : Matrix ι κ ℂ) (B : Matrix κ ι ℂ) :
    spectralSum f (A * B) + Fintype.card κ * f 0 =
      spectralSum f (B * A) + Fintype.card ι * f 0 := by
  have hl : Polynomial.X ^ Fintype.card κ * (A * B).charpoly ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Matrix.charpoly_monic _).ne_zero
  have hr : Polynomial.X ^ Fintype.card ι * (B * A).charpoly ≠ 0 :=
    mul_ne_zero (pow_ne_zero _ Polynomial.X_ne_zero) (Matrix.charpoly_monic _).ne_zero
  have h := congrArg Polynomial.roots (Matrix.charpoly_mul_comm' A B)
  rw [Polynomial.roots_mul hl, Polynomial.roots_mul hr,
    Polynomial.roots_X_pow, Polynomial.roots_X_pow] at h
  have hs := congrArg (fun s : Multiset ℂ => (s.map (fun z => f z.re)).sum) h
  have hz (n : ℕ) : (n • ({f 0} : Multiset ℝ)).sum = (n : ℝ) * f 0 := by
    induction n with
    | zero => simp
    | succ n ih => simp [succ_nsmul, ih, Nat.cast_add, add_mul]
  simpa [Multiset.map_nsmul, hz, spectralSum, add_comm] using hs

/-- Clipped energy is unchanged on exchanging source and target Gram matrices. -/
theorem energy_gram {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (c : ℝ≥0) : energy c (A * Aᴴ) = energy c (Aᴴ * A) := by
  have hz : quadratic c 0 = 0 := by rw [quadratic_of_le c.coe_nonneg]; ring
  simpa only [energy, hz, mul_zero, add_zero] using
    spectralSum_rectangular (quadratic c) A Aᴴ

/-- Unit-centered defects retain exactly the difference of ambient dimensions. -/
theorem defectEnergy_gram {κ : Type*} [Fintype κ] [DecidableEq κ]
    (A : Matrix ι κ ℂ) (τ : ℝ≥0) :
    defectEnergy τ (A * Aᴴ) - Fintype.card ι =
      defectEnergy τ (Aᴴ * A) - Fintype.card κ := by
  have hz : defect τ 0 = 1 := by
    rw [defect_eq_square (show (0 : ℝ) ≤ 1 + τ by positivity)]
    ring
  have h := spectralSum_rectangular (defect τ) A Aᴴ
  simp only [hz, mul_one] at h
  unfold defectEnergy
  linarith only [h]

/-- A spectral square in any unitary eigenbasis has its usual scalar trace. -/
theorem trace_conjugate_diagonal_product (V : Matrix.unitaryGroup ι ℂ)
    (x y : ι → ℂ) :
    trace (((V : Matrix ι ι ℂ) * diagonal x * star (V : Matrix ι ι ℂ)) *
      ((V : Matrix ι ι ℂ) * diagonal y * star (V : Matrix ι ι ℂ))) = ∑ i, x i * y i := by
  have hm : ((V : Matrix ι ι ℂ) * diagonal x * star (V : Matrix ι ι ℂ)) *
      ((V : Matrix ι ι ℂ) * diagonal y * star (V : Matrix ι ι ℂ)) =
      (V : Matrix ι ι ℂ) * (diagonal x * diagonal y) * star (V : Matrix ι ι ℂ) := by
    simp only [Matrix.mul_assoc]
    rw [← Matrix.mul_assoc (star (V : Matrix ι ι ℂ)) (V : Matrix ι ι ℂ),
      Unitary.coe_star_mul_self, Matrix.one_mul]
  rw [hm, Matrix.trace_mul_cycle, Unitary.coe_star_mul_self, Matrix.one_mul,
    Matrix.diagonal_mul_diagonal, Matrix.trace_diagonal]

theorem square_spectral {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (trace (A * A)).re = ∑ i, (hA.eigenvalues i) ^ 2 := by
  conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
  rw [trace_conjugate_diagonal_product]
  simp [pow_two]

/-- Centering at the identity subtracts twice the trace and adds the dimension. -/
theorem centered_square_spectral {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (∑ i, (hA.eigenvalues i - 1) ^ 2) =
      (trace (A * A)).re - 2 * (trace A).re + Fintype.card ι := by
  have ht : (trace A).re = ∑ i, hA.eigenvalues i := by
    rw [hA.trace_eq_sum_eigenvalues]
    simp
  rw [square_spectral hA, ht]
  have hi (i : ι) : (hA.eigenvalues i - 1) ^ 2 =
      (hA.eigenvalues i) ^ 2 - 2 * hA.eigenvalues i + 1 := by ring
  simp only [hi, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]

theorem defectEnergy_nonneg {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (τ : ℝ≥0) :
    0 ≤ defectEnergy τ A := by
  rw [defectEnergy, spectralSum_eq hA]
  exact Finset.sum_nonneg fun i _ => defect_nonneg τ.coe_nonneg _

/-- Every Hermitian block retains its full centered energy up to the cutoff square. -/
theorem defectEnergy_min_bound {A : Matrix ι ι ℂ} (hA : A.IsHermitian) (τ : ℝ≥0) :
    min ((trace (A * A)).re - 2 * (trace A).re + Fintype.card ι) ((τ : ℝ) ^ 2) ≤
      defectEnergy τ A := by
  rw [defectEnergy, spectralSum_eq hA, ← centered_square_spectral hA]
  exact block_min_bound hA.eigenvalues τ.coe_nonneg

omit [DecidableEq ι] in
/-- Hermitian square energy is the sum of entrywise squared magnitudes. -/
theorem trace_square {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (trace (A * A)).re = ∑ i, ∑ j, Complex.normSq (A i j) := by
  simp only [trace, diag, mul_apply, Complex.re_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  rw [← hA.apply j i]
  simp only [Complex.star_def, Complex.mul_conj, Complex.ofReal_re]

omit [DecidableEq ι] in
theorem diagonal_square_le {A : Matrix ι ι ℂ} (hA : A.IsHermitian) :
    (∑ i, (A i i).re ^ 2) ≤ (trace (A * A)).re := by
  rw [trace_square hA]
  apply Finset.sum_le_sum
  intro i _
  calc
    (A i i).re ^ 2 ≤ Complex.normSq (A i i) := by
      rw [Complex.normSq_apply]
      nlinarith only [sq_nonneg (A i i).im]
    _ ≤ ∑ j, Complex.normSq (A i j) :=
      Finset.single_le_sum (fun j _ => Complex.normSq_nonneg _) (Finset.mem_univ i)

theorem trace_square_unitary (V : Matrix.unitaryGroup ι ℂ) (B : Matrix ι ι ℂ) :
    trace ((star (V : Matrix ι ι ℂ) * B * (V : Matrix ι ι ℂ)) *
      (star (V : Matrix ι ι ℂ) * B * (V : Matrix ι ι ℂ))) = trace (B * B) := by
  have hv : (V : Matrix ι ι ℂ) * star (V : Matrix ι ι ℂ) = 1 :=
    Unitary.coe_mul_star_self V
  simp only [Matrix.mul_assoc]
  rw [← Matrix.mul_assoc (V : Matrix ι ι ℂ) (star (V : Matrix ι ι ℂ)),
    hv, Matrix.one_mul]
  calc
    _ = trace (star (V : Matrix ι ι ℂ) * (B * B) * (V : Matrix ι ι ℂ)) := by
      simp only [Matrix.mul_assoc]
    _ = _ := by rw [Matrix.trace_mul_cycle, hv, Matrix.one_mul]

/-- Matrix form of the clipped quadratic dual bound. -/
theorem dual_bound {A B : Matrix ι ι ℂ} (hA : A.IsHermitian)
    (hB : B.IsHermitian) (c : ℝ)
    (hcap : ((c : ℂ) • (1 : Matrix ι ι ℂ) - B).PosSemidef) :
    2 * (trace (B * A)).re - (trace (B * B)).re ≤ energy c A := by
  let V := hA.eigenvectorUnitary
  let T : Matrix ι ι ℂ := star (V : Matrix ι ι ℂ) * B * (V : Matrix ι ι ℂ)
  have hT : T.IsHermitian := by
    simpa only [T, star_eq_conjTranspose, Matrix.mul_assoc] using
      Matrix.isHermitian_conjTranspose_mul_mul (V : Matrix ι ι ℂ) hB
  have hTc : ((c : ℂ) • (1 : Matrix ι ι ℂ) - T).PosSemidef := by
    have h := hcap.conjTranspose_mul_mul_same (V : Matrix ι ι ℂ)
    simpa only [← star_eq_conjTranspose, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one,
      Unitary.coe_star_mul_self, T] using h
  have hdiag (i : ι) : (T i i).re ≤ c := by
    have h := (Complex.nonneg_iff.mp (hTc.diag_nonneg (i := i))).1
    simpa using h
  have hpair : (trace (B * A)).re = ∑ i, (T i i).re * hA.eigenvalues i := by
    conv_lhs => rw [hA.spectral_theorem, Unitary.conjStarAlgAut_apply]
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.trace_mul_comm]
    simp [V, T, ← Matrix.mul_assoc, Matrix.mul_diagonal, trace, diag]
  have hsquare : (trace (T * T)).re = (trace (B * B)).re :=
    congrArg Complex.re (trace_square_unitary V B)
  have hdiagonal := diagonal_square_le hT
  rw [hsquare] at hdiagonal
  rw [hpair, energy, spectralSum_eq hA]
  calc
    _ ≤ 2 * (∑ i, (T i i).re * hA.eigenvalues i) - ∑ i, (T i i).re ^ 2 :=
      sub_le_sub_left hdiagonal _
    _ = ∑ i, (2 * (T i i).re * hA.eigenvalues i - (T i i).re ^ 2) := by
      simp only [Finset.sum_sub_distrib, Finset.mul_sum, mul_assoc]
    _ ≤ _ := Finset.sum_le_sum fun i _ => scalar_dual (hdiag i) _

end
end GaloisForLFunctions.HilbertMetric.Clipped
