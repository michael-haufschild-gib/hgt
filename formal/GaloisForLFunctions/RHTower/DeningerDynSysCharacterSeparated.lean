import GaloisForLFunctions.RHTower.DeningerDynSysCharacterTopology
import Mathlib.AlgebraicGeometry.Properties

/-!
# Character points are separated by evaluations

Deninger, *Dynamical systems for arithmetic schemes* (arXiv:1807.06400v4), §7, the input to
Corollary 7.9 (`t89n`).

Over an affine open a character point is determined by the values of the evaluations at the
sections: the base point is determined because the basic open sets form a basis and a scheme is
`T0`, and the character is determined because every element of the residue field is a ratio of two
evaluations, the stalk being a localisation of the sections.  Hence the trace of `X̂ (C)` over an
affine open embeds into `Γ (X, U) → C` and is Hausdorff whenever `C` is.
-/

namespace RHTower

open AlgebraicGeometry CategoryTheory

universe u

variable {X : Scheme.{u}} {C : Type u} [Field C]

/-- Over an affine open a point is determined by the sections that do not vanish at it. -/
theorem deningerPoint_ext_of_basicOpen {U : X.Opens} (hU : IsAffineOpen U) {x y : X}
    (hx : x ∈ U) (hy : y ∈ U)
    (h : ∀ f : Γ(X, U), x ∈ X.basicOpen f ↔ y ∈ X.basicOpen f) : x = y := by
  have key : ∀ (W : X.Opens) (z w : X), z ∈ U → w ∈ U →
      (∀ f : Γ(X, U), z ∈ X.basicOpen f ↔ w ∈ X.basicOpen f) → z ∈ W → w ∈ W := by
    intro W z w hzU hwU hzw hzW
    obtain ⟨f, hf1, hf2⟩ := hU.exists_basicOpen_le (V := W ⊓ U) ⟨z, ⟨hzW, hzU⟩⟩ hzU
    exact (hf1 ((hzw f).1 hf2)).1
  refine (t0Space_iff_inseparable X).1 inferInstance x y ?_
  rw [inseparable_iff_forall_isOpen]
  intro W hW
  exact ⟨fun hxW => key ⟨W, hW⟩ x y hx hy h hxW,
    fun hyW => key ⟨W, hW⟩ y x hy hx (fun f => (h f).symm) hyW⟩

/-- Over an affine open every element of the residue field is a ratio of two evaluations. -/
theorem deningerResidue_exists_ratio {U : X.Opens} (hU : IsAffineOpen U) (x : U)
    (t : X.residueField (x : X)) :
    ∃ a s : Γ(X, U), X.evaluation U (x : X) x.2 s ≠ 0 ∧
      t * X.evaluation U (x : X) x.2 s = X.evaluation U (x : X) x.2 a := by
  haveI := hU.isLocalization_stalk x
  have halg : (algebraMap Γ(X, U) (X.presheaf.stalk (x : X)))
      = (X.presheaf.germ U (x : X) x.2).hom := RingHom.algebraMap_toAlgebra _
  have heval : ∀ g : Γ(X, U),
      X.residue (x : X) (X.presheaf.germ U (x : X) x.2 g)
        = X.evaluation U (x : X) x.2 g := fun _ => rfl
  obtain ⟨u, hu⟩ := X.residue_surjective (x : X) t
  obtain ⟨⟨a, s⟩, hs⟩ := IsLocalization.surj
    (hU.primeIdealOf x).asIdeal.primeCompl u
  have halg' : ∀ g : Γ(X, U), algebraMap Γ(X, U) (X.presheaf.stalk (x : X)) g
      = X.presheaf.germ U (x : X) x.2 g := fun g => DFunLike.congr_fun halg g
  refine ⟨a, s, ?_, ?_⟩
  · have hunit : IsUnit (X.presheaf.germ U (x : X) x.2 (s : Γ(X, U))) := by
      rw [← halg' (s : Γ(X, U))]
      exact IsLocalization.map_units (X.presheaf.stalk (x : X)) s
    have hres : IsUnit (X.residue (x : X) (X.presheaf.germ U (x : X) x.2 (s : Γ(X, U)))) :=
      hunit.map _
    rw [heval] at hres
    exact hres.ne_zero
  · have h1 := congrArg (X.residue (x : X)) hs
    rw [map_mul, hu, halg' (s : Γ(X, U)), halg' a, heval, heval] at h1
    exact h1

variable [TopologicalSpace C]

omit [TopologicalSpace C] in
/-- **Deninger, §7.**  Over an affine open a character point is determined by the values of the
evaluations at the sections. -/
theorem deningerCharPoints_ext {U : X.Opens} (hU : IsAffineOpen U) {x y : X}
    (hx : x ∈ U) (hy : y ∈ U) (χ : (X.residueField x)ˣ →* Cˣ) (ψ : (X.residueField y)ˣ →* Cˣ)
    (h : ∀ f : Γ(X, U), deningerCharEval U f ⟨x, χ⟩ = deningerCharEval U f ⟨y, ψ⟩) :
    (⟨x, χ⟩ : DeningerCharPoints X C) = ⟨y, ψ⟩ := by
  classical
  have hbase : x = y := by
    refine deningerPoint_ext_of_basicOpen hU hx hy fun f => ?_
    rw [← deningerCharEval_ne_zero_iff U f (⟨x, χ⟩ : DeningerCharPoints X C) hx,
      ← deningerCharEval_ne_zero_iff U f (⟨y, ψ⟩ : DeningerCharPoints X C) hy, h f]
  subst hbase
  refine Sigma.ext rfl (heq_of_eq (MonoidHom.ext fun u => ?_))
  obtain ⟨a, s, hs0, hval⟩ :=
    deningerResidue_exists_ratio hU (⟨x, hx⟩ : U) ((u : X.residueField x))
  have hea : X.evaluation U x hx a ≠ 0 := by
    rw [← hval]
    exact mul_ne_zero u.ne_zero hs0
  have hu : u * Units.mk0 _ hs0 = Units.mk0 _ hea := Units.ext hval
  have hcoord : ∀ (g : Γ(X, U)) (hg : X.evaluation U x hx g ≠ 0),
      χ (Units.mk0 _ hg) = ψ (Units.mk0 _ hg) := by
    intro g hg
    have hg1 : deningerCharEval U g (⟨x, χ⟩ : DeningerCharPoints X C)
        = ((χ (Units.mk0 _ hg) : Cˣ) : C) := by
      rw [deningerCharEval, dif_pos hx, deningerUnitExtend, dif_neg hg]
    have hg2 : deningerCharEval U g (⟨x, ψ⟩ : DeningerCharPoints X C)
        = ((ψ (Units.mk0 _ hg) : Cˣ) : C) := by
      rw [deningerCharEval, dif_pos hx, deningerUnitExtend, dif_neg hg]
    refine Units.ext ?_
    rw [← hg1, ← hg2]
    exact h g
  have hueq : u = Units.mk0 _ hea * (Units.mk0 _ hs0)⁻¹ := eq_mul_inv_of_mul_eq hu
  rw [hueq, map_mul, map_mul, map_inv, map_inv, hcoord a hea, hcoord s hs0]

omit [TopologicalSpace C] in
/-- **Deninger, §7.**  Over an affine open a character point is determined by its evaluations. -/
theorem deningerCharPoints_ext' {U : X.Opens} (hU : IsAffineOpen U)
    {P Q : DeningerCharPoints X C} (hP : P.1 ∈ U) (hQ : Q.1 ∈ U)
    (h : ∀ f : Γ(X, U), deningerCharEval U f P = deningerCharEval U f Q) : P = Q := by
  obtain ⟨x, χ⟩ := P
  obtain ⟨y, ψ⟩ := Q
  exact deningerCharPoints_ext hU hP hQ χ ψ h

/-- **Deninger, §7.**  The trace of `X̂ (C)` over an affine open is Hausdorff. -/
theorem deningerCharOver_t2Space [T2Space C] {U : X.Opens} (hU : IsAffineOpen U) :
    T2Space (DeningerCharOver X C U) := by
  refine Topology.IsEmbedding.t2Space
    (f := fun (P : DeningerCharOver X C U) => fun f : Γ(X, U) => deningerCharEval U f P.val) ?_
  refine ⟨⟨rfl⟩, fun P Q h => ?_⟩
  exact Subtype.ext (deningerCharPoints_ext' hU P.mem Q.mem fun f => congrFun h f)

/-- **Deninger, Corollary 7.9 (`t89n`), main step.**  If any two points of `X` lie in a common
affine open then `X̂ (C)` is Hausdorff. -/
theorem deningerCharPoints_t2Space [T2Space C] [ContinuousMul C] [ContinuousInv₀ C]
    (hcov : ∀ x y : X, ∃ U : X.Opens, IsAffineOpen U ∧ x ∈ U ∧ y ∈ U) :
    T2Space (DeningerCharPoints X C) := by
  refine ⟨fun P Q hPQ => ?_⟩
  obtain ⟨U, hU, hP, hQ⟩ := hcov P.1 Q.1
  haveI ht2 := deningerCharOver_t2Space (C := C) hU
  set P' : DeningerCharOver X C U := ⟨P, hP⟩ with hP'
  set Q' : DeningerCharOver X C U := ⟨Q, hQ⟩ with hQ'
  have hne : P' ≠ Q' := fun h => hPQ (congrArg Subtype.val h)
  obtain ⟨V, W, hV, hW, hPV, hQW, hVW⟩ :=
    @t2_separation (DeningerCharOver X C U) _ ht2 P' Q' hne
  refine ⟨DeningerCharOver.val '' V, DeningerCharOver.val '' W,
    deningerCharOverVal_isOpenMap ⟨U, hU⟩ V hV,
    deningerCharOverVal_isOpenMap ⟨U, hU⟩ W hW, ⟨_, hPV, rfl⟩, ⟨_, hQW, rfl⟩, ?_⟩
  rw [Set.disjoint_left]
  rintro _ ⟨p, hp, rfl⟩ ⟨q, hq, hpq⟩
  have hpq' : q = p := Subtype.ext hpq
  rw [hpq'] at hq
  exact (Set.disjoint_left.1 hVW) hp hq

end RHTower
