import GaloisForLFunctions.RepresentationLifting.ModularTrace
import Mathlib.Algebra.Group.Conj
import Mathlib.LinearAlgebra.Dimension.Constructions

/-!
# Central kernels on the regular bimodule

The formal algebra in Braverman–Kazhdan, Corollary 1.2 (arXiv:2312.07138),
identifies bimodule endomorphisms with central convolutions. On several copies
of the regular representation this is a matrix of class functions. No
division by the group order enters, so the dimension survives in modular
characteristic, including where every scalar trace vanishes.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
variable (ι G R : Type*) [Group G] [CommRing R]
local notation "M" => Matrix (ι × G) (ι × G) R

/-- Matrices invariant under the left and right diagonal regular translations. -/
def regularBimoduleKernels : Submodule R M where
  carrier := {T | ∀ (x y a b : G) (i j : ι), T (i,a*x*b) (j,a*y*b) = T (i,x) (j,y)}
  zero_mem' := by intros; rfl
  add_mem' h k x y a b i j := congrArg₂ (· + ·) (h x y a b i j) (k x y a b i j)
  smul_mem' r _ h x y a b i j := congrArg (r • ·) (h x y a b i j)

variable {ι G R}

/-- The regular kernel obeys right translation exactly when its coefficients are class functions. -/
theorem regularKernelMatrix_right_iff (K : ι → ι → G → R) :
    (∀ (g x y : G) (i j : ι), regularKernelMatrix K (i,x*g) (j,y*g) =
      regularKernelMatrix K (i,x) (j,y)) ↔
    ∀ i j x y, IsConj x y → K i j x = K i j y := by
  constructor
  · rintro h i j x y hxy
    obtain ⟨g, rfl⟩ := isConj_iff.mp hxy
    simpa [regularKernelMatrix, mul_assoc] using (h g⁻¹ 1 x i j).symm
  · intro h g x y i j
    apply (h i j _ _ ?_).symm
    apply isConj_iff.mpr
    exact ⟨g⁻¹, by simp [mul_assoc]⟩

/-- Lift a table of orbital coefficients to simultaneous left/right invariant matrices. -/
def regularOrbitalMatrix (K : ι × ι × ConjClasses G → R) :
    regularBimoduleKernels ι G R :=
  ⟨regularKernelMatrix (fun i j g => K (i,j,ConjClasses.mk g)), by
    intro x y a b i j
    have hc : ∀ i j x y, IsConj x y →
      K (i,j,ConjClasses.mk x) = K (i,j,ConjClasses.mk y) :=
      fun i j _ _ h => congrArg (fun c => K (i,j,c)) (ConjClasses.mk_eq_mk_iff_isConj.2 h)
    exact ((regularKernelMatrix_right_iff _).2 hc b (a*x) (a*y) i j).trans
      (regularKernelMatrix_translate _ a x y i j)⟩

private theorem regularOrbitalMatrix_injective :
    Function.Injective (regularOrbitalMatrix (ι := ι) (G := G) (R := R)) := by
  intro K L h
  funext ⟨i,j,c⟩
  obtain ⟨g, rfl⟩ := ConjClasses.mk_surjective c
  have he := congrArg (fun T : regularBimoduleKernels ι G R => T.val (i,1) (j,g)) h
  simpa [regularOrbitalMatrix, regularKernelMatrix] using he

private theorem regularOrbitalMatrix_surjective :
    Function.Surjective (regularOrbitalMatrix (ι := ι) (G := G) (R := R)) := by
  intro T
  obtain ⟨K,hK,_⟩ := (regularKernelMatrix_classification T.val).1
    (fun a x y i j => by simpa only [mul_one] using T.property x y a 1 i j)
  have hclass := (regularKernelMatrix_right_iff K).1 (fun g x y i j => by
    rw [hK]
    simpa only [one_mul] using T.property x y 1 g i j)
  let L (i j : ι) : ConjClasses G → R := Quotient.lift (K i j) (hclass i j)
  exact ⟨fun z => L z.1 z.2.1 z.2.2, Subtype.ext hK⟩

/-- The full regular bimodule commutant is a linear space of tables on conjugacy classes. -/
def regularOrbitalEquiv :
    (ι × ι × ConjClasses G → R) ≃ₗ[R] regularBimoduleKernels ι G R :=
  LinearEquiv.ofBijective
    { toFun := regularOrbitalMatrix
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
    ⟨regularOrbitalMatrix_injective, regularOrbitalMatrix_surjective⟩

/-- The trace of a central orbital kernel retains just the diagonal identity classes. -/
theorem regularOrbitalMatrix_trace [Fintype ι] [Fintype G] (K : ι × ι × ConjClasses G → R) :
    (regularOrbitalMatrix K).val.trace = (Fintype.card G : R) * ∑ i, K (i,i,ConjClasses.mk 1) :=
  trace_regularKernelMatrix _

/-- Finite regular bimodule commutants have one dimension per ordered copy-pair and conjugacy class. -/
theorem regularBimoduleKernels_finrank {k : Type*} [Field k] [Fintype ι] [Fintype (ConjClasses G)] :
    Module.finrank k (regularBimoduleKernels ι G k) =
      Fintype.card ι ^ 2 * Fintype.card (ConjClasses G) := by
  rw [← (regularOrbitalEquiv (ι := ι) (G := G) (R := k)).finrank_eq, Module.finrank_pi]
  simp only [Fintype.card_prod, pow_two, mul_assoc]

end GaloisForLFunctions.RepresentationLifting
