import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.PhaseBoundary.FiniteCertificates.DistanceGraph

/-! # Rational equations in the actual matrix entries at circuit-distance contacts -/

open Set Metric Topology Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates
noncomputable section

/-- Real and imaginary coordinates of a register matrix. -/
abbrev EntryPolynomial (N : ℕ) (R : Type*) [CommRing R] := MvPolynomial (Bits N × Bits N × Bool) R

variable {R : Type*} [CommRing R] (κ : R →+* ℝ)

def entryEval {N : ℕ} (M : Square (Bits N)) : EntryPolynomial N R →+* ℝ :=
  MvPolynomial.eval₂Hom κ fun ⟨i,j,b⟩ => if b then (M i j).im else (M i j).re

private theorem continuous_entryEval {N : ℕ} {X : Type*} [TopologicalSpace X]
    {U : X → Square (Bits N)} (hu : Continuous U) (p : EntryPolynomial N R) :
    Continuous fun x => entryEval κ (U x) p := by
  have coord (i : Bits N × Bits N × Bool) : Continuous fun x => entryEval κ (U x) (MvPolynomial.X i) := by
    obtain ⟨i,j,b⟩ := i
    have hij : Continuous (fun x => U x i j) :=
      (continuous_apply j).comp ((continuous_apply i).comp hu)
    cases b
    · simpa only [entryEval,MvPolynomial.eval₂Hom_X',Bool.false_eq_true,if_false,Function.comp_def] using Complex.continuous_re.comp hij
    · simpa only [entryEval,MvPolynomial.eval₂Hom_X',if_true,Function.comp_def] using Complex.continuous_im.comp hij
  induction p using MvPolynomial.induction_on with
  | C r => simpa only [entryEval,MvPolynomial.eval₂Hom_C] using (continuous_const (y := (κ r)))
  | add p q hp hq => simpa only [map_add,Pi.add_def] using hp.add hq
  | mul_X p i hp => simpa only [map_mul,Pi.mul_def] using hp.mul (coord i)

/-- The same finite family works for every contact with a represented level.
Each polynomial is nonzero somewhere on the given matrix family, even
when the whole family satisfies other polynomial identities. -/
theorem matrix_level_equations {N : ℕ} {X : Type*} [TopologicalSpace X] (U : X → Square (Bits N))
    (hu : Continuous U) (s : ℕ) (r : R) :
    let d (x : X) := infDist (U x) (phaseCircuitMatrixImageAtMost N s)
    ∃ F : Finset (EntryPolynomial N R), (∀ p∈F, ∃ y, entryEval κ (U y) p≠0) ∧
      ∀ x, d x=(κ r) → x∈closure {y | 0<d y ∧ d y≠(κ r)} → ∃ p∈F, entryEval κ (U x) p=0 := by
  classical
  intro d
  let φ : EntryPolynomial N R →+* (X → ℝ) := RingHom.pi fun x => entryEval κ (U x)
  let ρ (x : X) : φ.range →+* ℝ := (Pi.evalRingHom (fun _ : X => ℝ) x).comp φ.range.subtype
  have hrep (p : EntryPolynomial N R) (x : X) : ρ x (φ.rangeRestrict p)=entryEval κ (U x) p := rfl
  have hc (b : φ.range) : Continuous (fun x => ρ x b) := by
    obtain ⟨p,hp⟩ := b.property
    change Continuous (fun x => b.val x)
    rw [←hp]
    exact continuous_entryEval κ hu p
  have hm : MatrixRep ρ U := by
    intro i j
    exact ⟨⟨φ.rangeRestrict (MvPolynomial.X (i,j,false)),fun x => (hrep _ x).trans (MvPolynomial.eval₂Hom_X' ..)⟩,
      ⟨φ.rangeRestrict (MvPolynomial.X (i,j,true)),fun x => (hrep _ x).trans (MvPolynomial.eval₂Hom_X' ..)⟩⟩
  let a := φ.rangeRestrict (MvPolynomial.C r)
  have ha (x : X) : ρ x a=(κ r) := (hrep _ x).trans (MvPolynomial.eval₂Hom_C ..)
  obtain ⟨B,hB,hzero⟩ := distance_level_equations ρ hc U hm hu s a
  choose P hP using fun b : φ.range => b.property
  have he (b : φ.range) (x : X) : entryEval κ (U x) (P b)=ρ x b := congrFun (hP b) x
  refine ⟨B.image P,?_,?_⟩
  · intro p hp
    obtain ⟨b,hb,rfl⟩ := Finset.mem_image.mp hp
    by_contra! hz
    have hb0 : b=0 := Subtype.ext (funext fun x => (he b x).symm.trans (hz x))
    exact hB (hb0 ▸ hb)
  · intro x hx hlim
    obtain ⟨b,hb,heq⟩ := hzero x (hx.trans (ha x).symm) (by simpa only [ha] using hlim)
    exact ⟨P b,Finset.mem_image_of_mem P hb,(he b x).trans heq⟩

#print axioms matrix_level_equations
end
end GaloisForLFunctions.HTGeometry.PhaseBoundary.FiniteCertificates
