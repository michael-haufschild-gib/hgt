import Mathlib.FieldTheory.Fixed
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.LinearIndependent.Lemmas

/-!
# Invariant vectors span a semilinear representation

A finite group acting faithfully on a field has linearly independent scalar
automorphisms. Weighted orbit sums are invariant; their coefficients span
all functions on the group. Applying these coefficients to an orbit recovers
its original vector, so invariant vectors span over the field in every
characteristic. No division by the group order is used.
-/

noncomputable section
namespace GaloisForLFunctions.RepresentationLifting
open Module
open scoped BigOperators
variable (G L V : Type*) [Group G] [Fintype G] [Field L]
  [MulSemiringAction G L] [FaithfulSMul G L]
  [AddCommGroup V] [Module L V] [DistribMulAction G V] [SMulDistribClass G L V]

omit [Fintype G] in
/-- Artin independence applied to a faithful action on a field. -/
theorem faithfulScalarAction_linearIndependent :
    LinearIndependent L (fun g : G => fun a : L => g • a) := by
  let χ : G → L →* L := fun g => (MulSemiringAction.toRingHom G L g).toMonoidHom
  have hχ : Function.Injective χ := by
    intro g h he
    exact eq_of_smul_eq_smul (fun a : L => DFunLike.congr_fun he a)
  exact (linearIndependent_monoidHom L L).comp χ hχ

omit [FaithfulSMul G L] in
/-- The scalar-weighted sum of an orbit is invariant. -/
theorem weightedOrbitSum_fixed (a : L) (v : V) (g : G) :
    g • (∑ h : G, (h • a) • (h • v)) = ∑ h : G, (h • a) • (h • v) := by
  rw [Finset.smul_sum]
  simp only [smul_distrib_smul, smul_smul]
  exact Fintype.sum_equiv (Equiv.mulLeft g)
    (fun h : G => ((g * h) • a) • ((g * h) • v))
    (fun h : G => (h • a) • (h • v)) (fun _ => rfl)

/-- Every vector is a field-linear combination of invariant vectors. -/
theorem semilinear_fixedVectors_span :
    Submodule.span L {v : V | ∀ g : G, g • v = v} = ⊤ := by
  classical
  let S := Submodule.span L {v : V | ∀ g : G, g • v = v}
  have heval : Submodule.span L (Set.range (fun a : L => fun g : G => g • a)) = ⊤ :=
    span_flip_eq_top_iff_linearIndependent.mpr (faithfulScalarAction_linearIndependent G L)
  apply top_unique
  intro v _
  let T : (G → L) →ₗ[L] V :=
    { toFun := fun f => ∑ g : G, f g • (g • v)
      map_add' := by
        intro f h
        simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := by
        intro a f
        simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum,
          RingHom.id_apply] }
  have hle : Submodule.span L (Set.range (fun a : L => fun g : G => g • a)) ≤
      S.comap T := by
    apply Submodule.span_le.mpr
    rintro _ ⟨a, rfl⟩
    exact Submodule.subset_span (weightedOrbitSum_fixed G L V a v)
  rw [heval] at hle
  have hv := hle (show (fun g : G => if g = 1 then (1 : L) else 0) ∈
      (⊤ : Submodule L (G → L)) from trivial)
  change T (fun g : G => if g = 1 then (1 : L) else 0) ∈ S at hv
  simpa only [T, LinearMap.coe_mk, AddHom.coe_mk, ite_smul, one_smul,
    zero_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true] using hv

/-- A finite-dimensional semilinear representation has a basis of invariant vectors. -/
theorem semilinear_exists_fixed_basis [FiniteDimensional L V] :
    ∃ b : Basis (Fin (Module.finrank L V)) L V,
      ∀ (i : Fin (Module.finrank L V)) (g : G), g • b i = b i := by
  obtain ⟨f, hf, hs, hli⟩ := Submodule.exists_fun_fin_finrank_span_eq L
    {v : V | ∀ g : G, g • v = v}
  have hn : Module.finrank L (Submodule.span L {v : V | ∀ g : G, g • v = v}) =
      Module.finrank L V := by
    rw [semilinear_fixedVectors_span G L V]
    exact finrank_top L V
  let b := Basis.mk hli (by rw [hs, semilinear_fixedVectors_span G L V])
  refine ⟨b.reindex (finCongr hn), ?_⟩
  intro i g
  simpa only [Basis.reindex_apply, b, Basis.mk_apply] using hf ((finCongr hn).symm i) g

/-- In invariant-basis coordinates, the action only conjugates the scalar coordinates. -/
theorem semilinear_exists_coordinate_equiv [FiniteDimensional L V] :
    ∃ e : V ≃ₗ[L] (Fin (Module.finrank L V) → L),
      ∀ (g : G) (v : V) (i : Fin (Module.finrank L V)), e (g • v) i = g • e v i := by
  obtain ⟨b, hb⟩ := semilinear_exists_fixed_basis G L V
  refine ⟨b.equivFun, ?_⟩
  intro g v i
  have he : b.equivFun.symm (fun j => g • b.equivFun v j) = g • v := by
    calc
      _ = ∑ j, (g • b.equivFun v j) • b j := b.equivFun_symm_apply _
      _ = ∑ j, g • (b.equivFun v j • b j) := by
        apply Finset.sum_congr rfl
        intro j _
        rw [smul_distrib_smul, hb j g]
      _ = g • (∑ j, b.equivFun v j • b j) := (Finset.smul_sum ..).symm
      _ = g • v := by rw [← b.equivFun_symm_apply, LinearEquiv.symm_apply_apply]
  have h := congrArg (fun w => b.equivFun w i) he
  simpa only [LinearEquiv.apply_symm_apply] using h.symm

end GaloisForLFunctions.RepresentationLifting
