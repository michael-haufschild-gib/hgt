import GaloisForLFunctions.ArithmeticLorentzianGeometry.TheAtomicFormIsMetzlerBelowTheSpacing
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheRenormalizedPrimeEnergyControlsTheDefect

/-!
# The actual complete Weil matrix on the integer horizon

Adding both exponential pole rows to the Markov Gram gives the quadratic form
of the actual synthesized Weil test. The explicit finite-index bijection places
that matrix on the same Euclidean carrier as the prime matrix.
-/

noncomputable section

open MeasureTheory Finset Matrix
open scoped RealInnerProductSpace

namespace GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

open ArithmeticCastelnuovoSeveri ArithmeticLorentzianGeometry
  SpacingScaleHarmonicAnalysis

/-- The Markov Gram with both actual pole outer products restored. -/
def atomicWeilGram (g : ℝ → ℝ) (N : ℕ) : Matrix (Fin N) (Fin N) ℝ :=
  fun i j => atomicMarkovGram g N i j +
    atomPoleRow g N 0 i * atomPoleRow g N 1 j +
    atomPoleRow g N 1 i * atomPoleRow g N 0 j

theorem atomicWeilGram_isHermitian (g : ℝ → ℝ) (N : ℕ) :
    (atomicWeilGram g N).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro i j
  change atomicWeilGram g N j i = atomicWeilGram g N i j
  have h : atomicMarkovGram g N j i = atomicMarkovGram g N i j := by
    simp only [atomicMarkovGram, Matrix.of_apply, markovPair_comm]
  simp only [atomicWeilGram, h]
  ring

/-- Restoring the two pole rows is exactly the existing polar defect. -/
theorem qf_atomicWeilGram_eq_polarDefect (g : ℝ → ℝ) (N : ℕ) (d : Fin N → ℝ) :
    qf (atomicWeilGram g N) d =
      polarDefect (atomPoleRow g N) (-atomicMarkovGram g N) d := by
  have hneg : qf (-atomicMarkovGram g N) d = -qf (atomicMarkovGram g N) d := by
    rw [qf_eq_sum, qf_eq_sum, ← sum_neg_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_neg_distrib]
    exact sum_congr rfl fun j _ => by simp only [Matrix.neg_apply]; ring
  have hform : qf (atomicWeilGram g N) d = qf (atomicMarkovGram g N) d +
      (∑ i, atomPoleRow g N 0 i * d i) * (∑ j, atomPoleRow g N 1 j * d j) +
      (∑ i, atomPoleRow g N 1 i * d i) * (∑ j, atomPoleRow g N 0 j * d j) := by
    rw [qf_eq_sum, qf_eq_sum, sum_mul_sum, sum_mul_sum,
      ← sum_add_distrib, ← sum_add_distrib]
    refine sum_congr rfl fun i _ => ?_
    rw [← sum_add_distrib, ← sum_add_distrib]
    exact sum_congr rfl fun j _ => by dsimp only [atomicWeilGram]; ring
  rw [hform, polarDefect, hneg]
  simp only [mulVec, dotProduct]
  ring

/-- The complete atom matrix represents the literal Weil functional. -/
theorem qf_atomicWeilGram_eq_weilQuad {g : ℝ → ℝ} {w : ℝ}
    (hg : ContDiff ℝ 2 g) (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (hw : 0 ≤ w) (N : ℕ) (d : Fin N → ℝ) :
    qf (atomicWeilGram g N) d = weilQuad (finAtomicTest g N d) := by
  rw [qf_atomicWeilGram_eq_polarDefect, polarDefect_atomic hg hsupp hw]

/-- The exact index shift from positive horizon integers to `Fin N`. -/
def primeHorizonFinEquiv (N : ℕ) : PrimeHorizonIndex N ≃ Fin N where
  toFun n := ⟨(n : ℕ) - 1, by have h := mem_Icc.mp n.property; omega⟩
  invFun i := ⟨(i : ℕ) + 1, mem_Icc.mpr ⟨by omega, by omega⟩⟩
  left_inv n := by
    apply Subtype.ext
    have h := mem_Icc.mp n.property
    change (n : ℕ) - 1 + 1 = n
    omega
  right_inv i := by
    apply Fin.ext
    change (i : ℕ) + 1 - 1 = i
    omega

/-- The full Weil matrix on precisely the carrier of the prime matrix. -/
def fullWeilHorizonMatrix (g : ℝ → ℝ) (N : ℕ) :
    Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ :=
  fun n j => atomicWeilGram g N (primeHorizonFinEquiv N n) (primeHorizonFinEquiv N j)

theorem fullWeilHorizonMatrix_isHermitian (g : ℝ → ℝ) (N : ℕ) :
    (fullWeilHorizonMatrix g N).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro n j
  exact (atomicWeilGram_isHermitian g N).apply
    (primeHorizonFinEquiv N n) (primeHorizonFinEquiv N j)

theorem qf_fullWeilHorizonMatrix (g : ℝ → ℝ) (N : ℕ)
    (x : PrimeHorizonIndex N → ℝ) :
    qf (fullWeilHorizonMatrix g N) x =
      qf (atomicWeilGram g N) (fun i => x ((primeHorizonFinEquiv N).symm i)) := by
  rw [qf_eq_sum, qf_eq_sum]
  refine Fintype.sum_equiv (primeHorizonFinEquiv N) _ _ fun n => ?_
  refine Fintype.sum_equiv (primeHorizonFinEquiv N) _ _ fun j => ?_
  simp only [fullWeilHorizonMatrix, Equiv.symm_apply_apply]

theorem finAtomicTest_primeHorizonFinEquiv (g : ℝ → ℝ) (N : ℕ)
    (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    finAtomicTest g N (fun i => x ((primeHorizonFinEquiv N).symm i)) =
      ArithmeticElectrostatics.atomicTest N (primeHorizonExtension x) g := by
  funext u
  rw [ArithmeticElectrostatics.atomicTest,
    ← sum_coe_sort (Icc 1 N) (fun n => primeHorizonExtension x n * g (u - Real.log n))]
  symm
  refine Fintype.sum_equiv (primeHorizonFinEquiv N) _ _ fun n => ?_
  have hn : ((primeHorizonFinEquiv N n : Fin N) : ℕ) + 1 = n := by
    change (n : ℕ) - 1 + 1 = n
    have h := mem_Icc.mp n.property
    omega
  simp only [Equiv.symm_apply_apply, primeHorizonExtension_coe,
    atom, hn]

/-- The actual Euclidean matrix form is the actual complete Weil test form. -/
theorem fullWeilHorizonMatrix_inner_eq_weilQuad {g : ℝ → ℝ} {w : ℝ}
    (hg : ContDiff ℝ 2 g) (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (hw : 0 ≤ w) (N : ℕ) (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪Matrix.toEuclideanLin (fullWeilHorizonMatrix g N) x, x⟫ =
      weilQuad (ArithmeticElectrostatics.atomicTest N (primeHorizonExtension x) g) := by
  have hq : ⟪Matrix.toEuclideanLin (fullWeilHorizonMatrix g N) x, x⟫ =
      qf (fullWeilHorizonMatrix g N) (fun n => x n) := by
    rw [EuclideanSpace.inner_eq_star_dotProduct, qf, bil]
    rfl
  rw [hq, qf_fullWeilHorizonMatrix, qf_atomicWeilGram_eq_weilQuad hg hsupp hw,
    finAtomicTest_primeHorizonFinEquiv]

/-- Divide the complete Weil matrix by the mass of its common atom. -/
def normalizedFullWeilHorizonMatrix (g : ℝ → ℝ) (N : ℕ) :
    Matrix (PrimeHorizonIndex N) (PrimeHorizonIndex N) ℝ :=
  fun n j => fullWeilHorizonMatrix g N n j / (∫ u, g u ^ 2)

theorem normalizedFullWeilHorizonMatrix_isHermitian (g : ℝ → ℝ) (N : ℕ) :
    (normalizedFullWeilHorizonMatrix g N).IsHermitian := by
  apply Matrix.IsHermitian.ext
  intro n j
  change fullWeilHorizonMatrix g N j n / (∫ u, g u ^ 2) =
    fullWeilHorizonMatrix g N n j / (∫ u, g u ^ 2)
  congr 1
  exact (fullWeilHorizonMatrix_isHermitian g N).apply n j

/-- Atom-mass normalization preserves the exact complete Weil functional. -/
theorem normalizedFullWeilHorizonMatrix_inner_eq_weilQuad {g : ℝ → ℝ} {w : ℝ}
    (hg : ContDiff ℝ 2 g) (hsupp : ∀ u, u ∉ Set.Icc 0 w → g u = 0)
    (hw : 0 ≤ w) (N : ℕ) (x : EuclideanSpace ℝ (PrimeHorizonIndex N)) :
    ⟪Matrix.toEuclideanLin (normalizedFullWeilHorizonMatrix g N) x, x⟫ =
      weilQuad (ArithmeticElectrostatics.atomicTest N (primeHorizonExtension x) g) /
        (∫ u, g u ^ 2) := by
  rw [← fullWeilHorizonMatrix_inner_eq_weilQuad hg hsupp hw N x,
    EuclideanSpace.inner_eq_star_dotProduct, EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ n, x n * (∑ j, (fullWeilHorizonMatrix g N n j / (∫ u, g u ^ 2)) * x j)) =
    (∑ n, x n * (∑ j, fullWeilHorizonMatrix g N n j * x j)) / (∫ u, g u ^ 2)
  simp only [div_mul_eq_mul_div, ← sum_div, ← mul_div_assoc]

end GaloisForLFunctions.RenormalizedArithmeticPotentialTheory

