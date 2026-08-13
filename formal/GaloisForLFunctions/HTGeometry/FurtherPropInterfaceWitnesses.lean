import GaloisForLFunctions.HTGeometry.GammaComplexLatticeCharge
import GaloisForLFunctions.HTGeometry.HermitianWittEigenvalueReality
import GaloisForLFunctions.HTGeometry.InterfinityGeometry.GramNerve
import GaloisForLFunctions.HTGeometry.TracelessPauliIdentityCoordinate
import GaloisForLFunctions.HTGeometry.ConstitutiveControlledNaturalityMechanics
import GaloisForLFunctions.HTGeometry.ShilovCommutativeBoundary
import GaloisForLFunctions.HTGeometry.ConstitutiveFormationReporter
import GaloisForLFunctions.HTGeometry.GammaDatumLexValuation
import GaloisForLFunctions.HTGeometry.ConstitutiveFailureKernelTransversal
import GaloisForLFunctions.HTGeometry.LBitGeometricLocalityLaw

/-!
# Further unconditional witnesses for proposition-valued interfaces

This file turns several structural hypotheses into reusable laws or canonical witnesses.  In
particular, complex gamma commensurability is an equivalence relation, Gram-nerve refinement is a
preorder, equality in the orbit quotient is exactly orbit membership, and failure-kernel incidence
is exactly nonempty finite-set intersection.
-/

namespace GaloisForLFunctions.HTGeometry

/-- Complex gamma commensurability is reflexive. -/
theorem complexGammaCommensurate_refl (lam : ℂ) : ComplexGammaCommensurate lam lam := by
  exact ⟨1, 1, by norm_num, by norm_num, rfl⟩

/-- Complex gamma commensurability is symmetric. -/
theorem complexGammaCommensurate_symm {lam mu : ℂ}
    (h : ComplexGammaCommensurate lam mu) : ComplexGammaCommensurate mu lam := by
  obtain ⟨k, l, hk, hl, hkl⟩ := h
  exact ⟨l, k, hl, hk, hkl.symm⟩

/-- Complex gamma commensurability is transitive. -/
theorem complexGammaCommensurate_trans {lam mu nu : ℂ}
    (h₁ : ComplexGammaCommensurate lam mu)
    (h₂ : ComplexGammaCommensurate mu nu) : ComplexGammaCommensurate lam nu := by
  obtain ⟨k, l, hk, hl, hkl⟩ := h₁
  obtain ⟨m, n, hm, hn, hmn⟩ := h₂
  refine ⟨m * k, l * n, mul_ne_zero hm hk, mul_ne_zero hl hn, ?_⟩
  push_cast
  calc
    (m : ℂ) * (k : ℂ) * lam = (m : ℂ) * ((k : ℂ) * lam) := by ring
    _ = (m : ℂ) * ((l : ℂ) * mu) := congrArg ((m : ℂ) * ·) hkl
    _ = (l : ℂ) * ((m : ℂ) * mu) := by ring
    _ = (l : ℂ) * ((n : ℂ) * nu) := by rw [hmn]
    _ = (l : ℂ) * (n : ℂ) * nu := by ring

namespace ComplexSesquilinearForm

/-- Every sesquilinear form on a subsingleton space has Witt index at most one. -/
theorem wittIndexAtMostOne_of_subsingleton
    {V : Type*} [AddCommGroup V] [Module ℂ V] [Subsingleton V]
    (B : ComplexSesquilinearForm V) : B.WittIndexAtMostOne := by
  intro x y hxx hxy hyx hyy hli
  have hx : x = 0 := Subsingleton.elim _ _
  exact (hli.ne_zero 0) (by simp [hx])

end ComplexSesquilinearForm

namespace Interfinity.GramNerveDatum

/-- Gram-nerve refinement is reflexive. -/
theorem le_refl {A : Type*} (D : GramNerveDatum A) : LE D D := by
  exact ⟨fun a ha => ha, fun n p hp => hp⟩

/-- Gram-nerve refinement is transitive. -/
theorem le_trans {A : Type*} {D₁ D₂ D₃ : GramNerveDatum A}
    (h₁₂ : LE D₁ D₂) (h₂₃ : LE D₂ D₃) : LE D₁ D₃ := by
  exact ⟨fun a ha => h₂₃.1 a (h₁₂.1 a ha),
    fun n p hp => h₂₃.2 n p (h₁₂.2 n p hp)⟩

end Interfinity.GramNerveDatum

/-- A finite nonidentity Pauli label of weight at most `q` always exists for positive `n,q`. -/
theorem exists_isFiniteQTracelessPauliLabel
    (n q : ℕ) [NeZero n] [NeZero q] :
    ∃ P, IsFiniteQTracelessPauliLabel n q P := by
  exact ⟨(Classical.choice (instNonemptyFiniteQTracelessPauliLabel n q)).1,
    (Classical.choice (instNonemptyFiniteQTracelessPauliLabel n q)).2⟩

namespace ControlledNaturalityMechanics

/-- Canonical reporter to the orbit quotient. -/
def orbitQuotientReporter
    {G X : Type*} [Group G] [MulAction G X] :
    X → MulAction.orbitRel.Quotient G X := fun x => Quotient.mk'' x

/-- The canonical orbit-quotient reporter is orbit-complete. -/
theorem orbitCompleteReporter_orbitQuotient
    {G X : Type*} [Group G] [MulAction G X] :
    OrbitCompleteReporter (G := G) (orbitQuotientReporter (G := G) (X := X)) := by
  intro x y
  constructor
  · intro h
    have hxy : MulAction.orbitRel G X x y := Quotient.eq''.mp h
    exact MulAction.orbitRel_apply.mp ((MulAction.orbitRel G X).symm hxy)
  · intro h
    apply Quotient.eq''.mpr
    apply (MulAction.orbitRel G X).symm
    exact MulAction.orbitRel_apply.mpr h

end ControlledNaturalityMechanics

namespace ShilovLocal

/-- Every point of a compact Hausdorff subsingleton is a peak point of the full function space. -/
theorem isPeakPoint_top_of_subsingleton
    {X : Type*} [TopologicalSpace X] [CompactSpace X] [T2Space X] [Subsingleton X]
    (x : X) : IsPeakPoint (⊤ : Submodule ℂ C(X, ℂ)) x := by
  have hone : (1 : C(X, ℂ)) ≠ 0 := by
    intro h
    have hx := DFunLike.congr_fun h x
    simp at hx
  refine ⟨1, by simp, norm_pos_iff.mpr hone, ?_⟩
  intro y hy
  exact (hy (Subsingleton.elim _ _)).elim

end ShilovLocal

/-- Constant reporters are invariant under every constitutive formation. -/
theorem formationReporterInvariant_const
    {α β : Type*} (C : ConstitutiveFormation α) (b : β) :
    FormationReporterInvariant (fun _ : Set α => b) C := by
  intro s
  rfl

/-- A strict primary-coordinate increase implies lexicographic shape dominance. -/
theorem shapeDominates_of_k_lt {k k' : ℤ} (h : k < k') (a b a' b' : ℤ) :
    ShapeDominates k a b k' a' b' := Or.inl h

/-- At equal primary coordinate, a strict decrease in `a` implies shape dominance. -/
theorem shapeDominates_of_a_lt {k a a' : ℤ} (h : a' < a) (b b' : ℤ) :
    ShapeDominates k a b k a' b' := Or.inr (Or.inl ⟨rfl, h⟩)

/-- At equal first two coordinates, a strict decrease in `b` implies shape dominance. -/
theorem shapeDominates_of_b_lt {k a b b' : ℤ} (h : b' < b) :
    ShapeDominates k a b k a b' := Or.inr (Or.inr ⟨rfl, rfl, h⟩)

/-- Failure-kernel incidence is exactly nonempty finite-set intersection. -/
theorem hitsFailureKernel_iff_inter_nonempty
    {α : Type*} [DecidableEq α] (R K : Finset α) :
    HitsFailureKernel R K ↔ (R ∩ K).Nonempty := by
  constructor
  · rintro ⟨x, hxR, hxK⟩
    exact ⟨x, Finset.mem_inter.mpr ⟨hxR, hxK⟩⟩
  · rintro ⟨x, hx⟩
    exact ⟨x, (Finset.mem_inter.mp hx).1, (Finset.mem_inter.mp hx).2⟩

/-- Every support on an `n`-site chain has range at most `n`. -/
theorem lBitSupportRangeAtMost_full (n : ℕ) (S : Finset (Fin n)) :
    LBitSupportRangeAtMost n S := by
  intro i hi j hj
  unfold Nat.dist
  omega

end GaloisForLFunctions.HTGeometry
