import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Finite Hilbert spaces with positive coordinate weights

Positive weights define a Hilbert norm on a finite coordinate space. Keeping
the weights in the inner product avoids square-root rescaling of coordinates.
-/

noncomputable section
set_option autoImplicit false
open Complex Finset
open scoped InnerProductSpace ComplexConjugate

namespace GaloisForLFunctions.HTGeometry.FiniteWeightedHilbert

variable {ι : Type*} [Fintype ι]

/-- The diagonal Hermitian form with real coordinate weights. -/
def weightedPairing (w : ι → ℝ) (x y : ι → ℂ) : ℂ :=
  ∑ i, (w i : ℂ) * conj (x i) * y i

theorem weightedPairing_self_re (w : ι → ℝ) (x : ι → ℂ) :
    (weightedPairing w x x).re = ∑ i, w i * normSq (x i) := by
  unfold weightedPairing
  simp only [mul_assoc, ← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_mul,
    Complex.re_sum, Complex.ofReal_re]

/-- A finite coordinate space equipped with the positive weighted form. -/
def Space (w : ι → ℝ) (_hw : ∀ i, 0 < w i) := ι → ℂ

variable (w : ι → ℝ) (hw : ∀ i, 0 < w i)

instance : AddCommGroup (Space w hw) := inferInstanceAs (AddCommGroup (ι → ℂ))
instance : Module ℂ (Space w hw) := inferInstanceAs (Module ℂ (ι → ℂ))
instance : FiniteDimensional ℂ (Space w hw) :=
  inferInstanceAs (FiniteDimensional ℂ (ι → ℂ))

instance core : InnerProductSpace.Core ℂ (Space w hw) where
  inner := weightedPairing w
  conj_inner_symm x y := by
    simp only [weightedPairing, map_sum, map_mul, Complex.conj_ofReal,
      RingHomCompTriple.comp_apply, RingHom.id_apply]
    apply Finset.sum_congr rfl
    intro i _
    ring
  re_inner_nonneg x := by
    calc
      0 ≤ ∑ i, w i * normSq (x i) :=
        Finset.sum_nonneg fun i _ => mul_nonneg (hw i).le (normSq_nonneg _)
      _ = (weightedPairing w x x).re := (weightedPairing_self_re w x).symm
  add_left x y z := by
    change weightedPairing w (fun i => x i + y i) z =
      weightedPairing w x z + weightedPairing w y z
    simp only [weightedPairing, map_add, mul_add, add_mul, Finset.sum_add_distrib]
  smul_left x y c := by
    change weightedPairing w (fun i => c * x i) y = conj c * weightedPairing w x y
    simp only [weightedPairing, map_mul, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  definite x hx := by
    have hs : ∑ i, w i * normSq (x i) = 0 := by
      simpa only [weightedPairing_self_re, Complex.zero_re] using congrArg Complex.re hx
    funext i
    have hle : w i * normSq (x i) ≤ ∑ j, w j * normSq (x j) :=
      Finset.single_le_sum (fun j _ => mul_nonneg (hw j).le (normSq_nonneg _)) (mem_univ i)
    rw [hs] at hle
    have hz : w i * normSq (x i) = 0 :=
      le_antisymm hle (mul_nonneg (hw i).le (normSq_nonneg _))
    exact normSq_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left (ne_of_gt (hw i)))

instance : NormedAddCommGroup (Space w hw) := (core w hw).toNormedAddCommGroup
instance : InnerProductSpace ℂ (Space w hw) := InnerProductSpace.ofCore _
instance : CompleteSpace (Space w hw) := FiniteDimensional.complete ℂ _

theorem inner_def (x y : Space w hw) : inner ℂ x y = weightedPairing w x y := rfl

/-- The weighted norm changes no algebraic coordinates. -/
def coordinates : Space w hw ≃ₗ[ℂ] (ι → ℂ) := LinearEquiv.refl ℂ _

#print axioms core

end GaloisForLFunctions.HTGeometry.FiniteWeightedHilbert
