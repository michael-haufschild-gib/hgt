import GaloisForLFunctions.HyperbolicArakelovTheory.TheLocalGreenKernelOnAdelicVertices
import GaloisForLFunctions.ArithmeticIntersectionTheory.TheDifferentOfATorsionOrbit
import Mathlib.Algebra.BigOperators.Finprod

/-!
# The different as a marked Green potential

The harmonic local Green diagonal supplies the tame correction to radial
distance. Summing this corrected distance over finite places recovers the
normalized cyclotomic different on the degree configuration. The construction
uses a pair of marked vertices and is invariant under their simultaneous action.
-/

set_option autoImplicit false
noncomputable section
open Matrix
open scoped Classical BigOperators

namespace GaloisForLFunctions.HyperbolicArakelovTheory.MarkedGreen
open FullAdelic AdelicRadial AdelicGreen ArithmeticIntersectionTheory

local instance (p : {p : ℕ // p.Prime}) : Fact p.1.Prime := ⟨p.2⟩

/-- Harmonic Green excess is exactly the tame local correction. -/
theorem harmonic_excess (p : {p : ℕ // p.Prime}) (v : LocalVertex p) :
    ((p.1 : ℝ) + 1) * localGreen p 1 v v - 1 = 1 / ((p.1 : ℝ) - 1) := by
  have hp : (1 : ℝ) < p.1 := by exact_mod_cast p.2.one_lt
  have hm : (p.1 : ℝ) - 1 ≠ 0 := by linarith
  have hs : (p.1 : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith only [hp]
  rw [localGreen_self]
  simp only [treeGreen, pow_zero, mul_one, Real.rpow_one, mul_one,
    Real.rpow_two]
  field_simp [hm, hs]
  ring

/-- Corrected radial separation; coincident vertices contribute no place. -/
def localDifferent (p : {p : ℕ // p.Prime}) (v w : LocalVertex p) : ℝ :=
  if v = w then 0 else
    -Real.log (localRatio p v w) - Real.log p.1 *
      (((p.1 : ℝ) + 1) * localGreen p 1 v v - 1)

@[simp] theorem localDifferent_self (p : {p : ℕ // p.Prime}) (v : LocalVertex p) :
    localDifferent p v v = 0 := by simp only [localDifferent, if_true]

theorem localDifferent_symm (p : {p : ℕ // p.Prime}) (v w : LocalVertex p) :
    localDifferent p v w = localDifferent p w v := by
  simp only [localDifferent, harmonic_excess, localRatio_symm p v w, eq_comm]

theorem localDifferent_smul (p : {p : ℕ // p.Prime}) (a : LocalPGL p)
    (v w : LocalVertex p) : localDifferent p (a • v) (a • w) = localDifferent p v w := by
  simp only [localDifferent, (MulAction.injective a).eq_iff, localRatio_smul,
    localGreen_smul]

/-- Extend by zero at nonprime indices, so finite sums use natural prime factors. -/
def localTerm (v w : FiniteVertices) (p : ℕ) : ℝ :=
  if hp : p.Prime then localDifferent ⟨p, hp⟩ (v.1 ⟨p, hp⟩) (w.1 ⟨p, hp⟩) else 0

/-- Only finitely many finite places separate two restricted-product vertices. -/
theorem localTerm_finite_support (v w : FiniteVertices) :
    (Function.support (localTerm v w)).Finite := by
  apply (((v.2.union w.2).image Subtype.val)).subset
  intro p hp
  by_cases hprime : p.Prime
  · refine ⟨⟨p, hprime⟩, ?_, rfl⟩
    by_contra h
    have hvw : v.1 ⟨p, hprime⟩ = w.1 ⟨p, hprime⟩ := by
      have hh : v.1 ⟨p, hprime⟩ = baseVertex ⟨p, hprime⟩ ∧
          w.1 ⟨p, hprime⟩ = baseVertex ⟨p, hprime⟩ := by
        simpa only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] using h
      exact hh.1.trans hh.2.symm
    exact hp (by simp only [localTerm, dif_pos hprime, hvw, localDifferent_self])
  · exact (hp (by simp only [localTerm, dif_neg hprime])).elim

/-- Finite sum of local Green corrections for a marked pair. -/
def markedDifferent (v w : FiniteVertices) : ℝ := ∑ᶠ p, localTerm v w p

theorem markedDifferent_symm (v w : FiniteVertices) :
    markedDifferent v w = markedDifferent w v := by
  apply finsum_congr
  intro p
  by_cases hp : p.Prime
  · simp only [localTerm, dif_pos hp]
    exact localDifferent_symm ⟨p, hp⟩ (v.1 ⟨p, hp⟩) (w.1 ⟨p, hp⟩)
  · simp only [localTerm, dif_neg hp]

/-- Both marked vertices move together; fixing one would discard this invariance. -/
theorem markedDifferent_smul (a : FiniteAdelicGroup) (v w : FiniteVertices) :
    markedDifferent (a • v) (a • w) = markedDifferent v w := by
  apply finsum_congr
  intro p
  by_cases hp : p.Prime
  · simp only [localTerm, dif_pos hp]
    exact localDifferent_smul ⟨p, hp⟩ (a ⟨p, hp⟩) (v.1 ⟨p, hp⟩) (w.1 ⟨p, hp⟩)
  · simp only [localTerm, dif_neg hp]

/-- The original degree configuration has radial ratio equal to the local norm of its degree. -/
theorem localRatio_degree (p : {p : ℕ // p.Prime}) (n : ℕ+) :
    localRatio p (baseVertex p) (principalVertex (upperDegree n) p) =
      ‖((n : ℕ) : ℚ_[p.1])‖ := by
  rw [localRatio_base, principalVertex, vertexRatio_mk, projectiveRatio_mk]
  have hv : (localGLMap p (upperDegree n)).val =
      !![((n : ℕ) : ℚ_[p.1]), 0; 0, 1] := by
    ext i j
    rw [localGLMap_apply]
    fin_cases i <;> fin_cases j <;> simp [upperDegree]
  have hs : entrySize p (localGLMap p (upperDegree n)).val = 1 := by
    rw [hv]
    change max (max ‖((n : ℕ) : ℚ_[p.1])‖ ‖(0 : ℚ_[p.1])‖)
      (max ‖(0 : ℚ_[p.1])‖ ‖(1 : ℚ_[p.1])‖) = 1
    rw [norm_zero, norm_one, max_eq_left (norm_nonneg _), max_eq_right zero_le_one]
    exact max_eq_right ((n : ℕ) : ℤ_[p.1]).2
  rw [matrixRatio, hs, hv]
  simp [Matrix.det_fin_two]

private theorem degree_separation (p : {p : ℕ // p.Prime}) (n : ℕ+) :
    baseVertex p ≠ principalVertex (upperDegree n) p ↔ p.1 ∣ (n : ℕ) := by
  have he := localRatio_eq_one_iff p (baseVertex p) (principalVertex (upperDegree n) p)
  rw [localRatio_degree] at he
  constructor
  · intro h
    have hn : ‖((n : ℕ) : ℚ_[p.1])‖ ≠ 1 := fun hh => h (he.mp hh)
    exact Padic.norm_natCast_lt_one_iff.mp
      ((lt_or_eq_of_le (((n : ℕ) : ℤ_[p.1]).2)).resolve_right hn)
  · intro h hh
    exact (ne_of_lt (Padic.norm_natCast_lt_one_iff.mpr h)) (he.mpr hh)

private theorem norm_degree (p : {p : ℕ // p.Prime}) (n : ℕ+) :
    ‖((n : ℕ) : ℚ_[p.1])‖ = ((p.1 : ℝ) ^ (n : ℕ).factorization p.1)⁻¹ := by
  change ‖(((n : ℕ) : ℚ) : ℚ_[p.1])‖ = _
  rw [Padic.eq_padicNorm, padicNorm.eq_zpow_of_nonzero (by exact_mod_cast n.ne_zero),
    padicValRat.of_nat, _root_.zpow_neg, zpow_natCast, Nat.factorization_def (n : ℕ) p.2]
  simp only [Rat.cast_inv, Rat.cast_pow, Rat.cast_natCast]

theorem localTerm_degree (n : ℕ+) (p : ℕ) :
    localTerm finiteBase (finitePoint (upperDegree n)) p =
      if p ∈ (n : ℕ).primeFactors then
        (((n : ℕ).factorization p : ℝ) - 1 / ((p : ℝ) - 1)) * Real.log p else 0 := by
  by_cases hp : p ∈ (n : ℕ).primeFactors
  · have hprime := Nat.prime_of_mem_primeFactors hp
    have hdvd := Nat.dvd_of_mem_primeFactors hp
    have hne := (degree_separation ⟨p, hprime⟩ n).mpr hdvd
    rw [localTerm, dif_pos hprime]
    change localDifferent ⟨p, hprime⟩ (baseVertex ⟨p, hprime⟩)
      (principalVertex (upperDegree n) ⟨p, hprime⟩) = _
    rw [localDifferent, if_neg hne, if_pos hp, harmonic_excess, localRatio_degree,
      norm_degree, Real.log_inv, Real.log_pow]
    ring
  · rw [if_neg hp]
    by_cases hprime : p.Prime
    · have hndvd : ¬p ∣ (n : ℕ) := fun h =>
        hp (Nat.mem_primeFactors.mpr ⟨hprime, h, n.ne_zero⟩)
      have he : baseVertex ⟨p, hprime⟩ = principalVertex (upperDegree n) ⟨p, hprime⟩ :=
        not_ne_iff.mp (fun h => hndvd ((degree_separation ⟨p, hprime⟩ n).mp h))
      simp only [localTerm, dif_pos hprime, finiteBase, finitePoint, localDifferent, if_pos he]
    · simp only [localTerm, dif_neg hprime]

/-- The marked Green potential recovers the normalized cyclotomic different. -/
theorem markedDifferent_degree (n : ℕ+) :
    markedDifferent finiteBase (finitePoint (upperDegree n)) = selfIntersection (n : ℕ) := by
  have hs : Function.support (localTerm finiteBase (finitePoint (upperDegree n))) ⊆
      ((n : ℕ).primeFactors : Set ℕ) := by
    intro p hp
    by_contra h
    change p ∉ (n : ℕ).primeFactors at h
    exact hp (by rw [localTerm_degree, if_neg h])
  rw [markedDifferent, finsum_eq_sum_of_support_subset _ hs,
    selfIntersection_eq_sum_local n.pos]
  apply Finset.sum_congr rfl
  intro p hp
  rw [localTerm_degree, if_pos hp]

/-- The finite marked potential is invariant under the full simultaneous adelic action. -/
theorem markedDifferent_global_smul (a : AdelicGroup) (x y : GlobalSpace) :
    markedDifferent (a • x).2 (a • y).2 = markedDifferent x.2 y.2 :=
  markedDifferent_smul a.2 x.2 y.2

/-- The degree-one mark recovers the discriminant on the original degree configuration. -/
theorem markedDifferent_originalDegree (n : ℕ+) :
    markedDifferent (originalDegreePoint 1).2 (originalDegreePoint n).2 =
      selfIntersection (n : ℕ) := by
  have hbase : (originalDegreePoint 1).2 = finiteBase := by
    apply Subtype.ext
    funext p
    exact ((localRatio_eq_one_iff p (baseVertex p)
      (principalVertex (upperDegree 1) p)).mp (by rw [localRatio_degree]; norm_num)).symm
  rw [hbase]
  exact markedDifferent_degree n

#print axioms localTerm_finite_support
#print axioms markedDifferent_smul
#print axioms markedDifferent_symm
#print axioms markedDifferent_degree
#print axioms markedDifferent_originalDegree

end GaloisForLFunctions.HyperbolicArakelovTheory.MarkedGreen
