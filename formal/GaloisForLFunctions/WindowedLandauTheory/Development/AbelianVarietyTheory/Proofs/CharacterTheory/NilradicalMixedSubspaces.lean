import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantCharpolyBlocks
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.LinearAlgebra.Isomorphisms

/-! Nilradical averages on subspaces meeting a parabolic subspace nontrivially. -/

namespace GlobalTheory.CuspGL

variable {F V : Type} [Field F] [AddCommGroup V] [Module F V]

private theorem exists_nilRad_extend (A W : Submodule F V) (h : Module.End F W)
    (hh : h ∈ nilRad (A.comap W.subtype)) :
    ∃ L : Module.End F V, L ∈ nilRad A ∧ ∀ x : W, L x = h x := by
  let p : W →ₗ[F] V ⧸ A := A.mkQ ∘ₗ W.subtype
  let f : W →ₗ[F] A := LinearMap.codRestrict A (W.subtype ∘ₗ h) (fun x => hh.1 x)
  have hker : p.ker ≤ f.ker := by
    intro x hx
    have hxA : (x : V) ∈ A := by simpa [p] using hx
    have hz := hh.2 x hxA
    rw [LinearMap.mem_ker]
    ext
    simp [f, hz]
  obtain ⟨k, hk⟩ := LinearMap.exists_extend
    ((p.ker.liftQ f hker) ∘ₗ p.quotKerEquivRange.symm.toLinearMap)
  have he (x : W) : k (p x) = f x := by
    simpa using LinearMap.congr_fun hk ⟨p x, LinearMap.mem_range_self p x⟩
  refine ⟨A.subtype ∘ₗ k ∘ₗ A.mkQ, ⟨fun x => by simp, fun x hx => ?_⟩, fun x => ?_⟩
  · have hx₀ : A.mkQ x = 0 := by simpa using hx
    simp only [LinearMap.comp_apply, hx₀, map_zero]
  · simpa [p, f] using congrArg Subtype.val (he x)

/-- Averaging a primitive function over the restrictions of stabilizing translates gives zero. -/
theorem sum_restrict_eq_zero_of_mixed [Finite F] [FiniteDimensional F V]
    (A W : Submodule F V) (g : Module.End F V) (hg : ∀ x ∈ A, g x ∈ A)
    (hinter : W ⊓ A ≠ ⊥) (hproper : ¬ W ≤ A) (φ : Module.End F W → ℂ) (hφ : IsPrimitive φ) :
    ∑ᶠ h : {h : Module.End F V // h ∈ nilRad A ∧ ∀ x ∈ W, (g + h) x ∈ W},
      φ ((g + h.1).restrict h.2.2) = 0 := by
  classical
  letI : Finite V := Module.finite_of_finite F
  letI : Finite (Module.End F V) := Finite.of_injective _ DFunLike.coe_injective
  letI : Finite (Module.End F W) := Finite.of_injective _ DFunLike.coe_injective
  let A' := A.comap W.subtype
  have hb : A' ≠ ⊥ := by
    intro h
    apply hinter
    rw [eq_bot_iff]
    intro x hx
    have hmem : (⟨x, hx.1⟩ : W) ∈ A' := hx.2
    rw [h, Submodule.mem_bot] at hmem
    simpa using congrArg Subtype.val hmem
  have ht : A' ≠ ⊤ := by
    intro h
    apply hproper
    intro x hx
    have hmem : (⟨x, hx⟩ : W) ∈ A' := h ▸ Submodule.mem_top
    exact hmem
  let S := {h : Module.End F V // h ∈ nilRad A ∧ ∀ x ∈ W, (g + h) x ∈ W}
  letI : Fintype S := Fintype.ofFinite _
  letI : Fintype (nilRad A') := Fintype.ofFinite _
  have inner (h : S) : ∑ h' : nilRad A', φ ((g + h.1).restrict h.2.2 + h'.1) = 0 := by
    have hi := hφ A' hb ht ((g + h.1).restrict h.2.2) (by
      intro x hx
      have hxA : (x : V) ∈ A := hx
      change (g + h.1) x ∈ A
      rw [LinearMap.add_apply]
      exact A.add_mem (hg _ hxA) (h.2.1.1 _))
    rw [← finsum_set_coe_eq_finsum_mem, finsum_eq_sum_of_fintype] at hi
    exact hi
  -- Every shift of the restricted nilradical extends to a permutation of the ambient translates.
  have shift (h' : nilRad A') : ∑ h : S, φ ((g + h.1).restrict h.2.2 + h'.1) =
      ∑ h : S, φ ((g + h.1).restrict h.2.2) := by
    obtain ⟨L, hL, hLW⟩ := exists_nilRad_extend A W h'.1 h'.2
    let T : S → S := fun h => ⟨h.1 + L, ⟨fun x => A.add_mem (h.2.1.1 x) (hL.1 x), fun x hx => by
      rw [LinearMap.add_apply, h.2.1.2 x hx, hL.2 x hx, add_zero]⟩, fun x hx => by
        rw [← add_assoc, LinearMap.add_apply, hLW ⟨x, hx⟩]
        exact W.add_mem (h.2.2 x hx) (h'.1 ⟨x, hx⟩).2⟩
    have hT : Function.Bijective T := by
      apply Finite.injective_iff_bijective.mp
      intro a b hab
      exact Subtype.ext (add_right_cancel (congrArg Subtype.val hab))
    refine Fintype.sum_bijective T hT _ _ fun h => ?_
    congr 1
    ext x
    change (g + h.1) x + (h'.1 x : V) = (g + (h.1 + L)) x
    rw [← add_assoc, LinearMap.add_apply (g + h.1), hLW x]
  have total : ∑ h' : nilRad A', ∑ h : S, φ ((g + h.1).restrict h.2.2 + h'.1) = 0 := by
    rw [Finset.sum_comm]
    exact Finset.sum_eq_zero fun h _ => inner h
  simp only [shift, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_eq_zero] at total
  letI : Nonempty (nilRad A') := ⟨⟨0, fun _ => A'.zero_mem, fun _ _ => rfl⟩⟩
  rw [finsum_eq_sum_of_fintype]
  exact total.resolve_left (Nat.cast_ne_zero.mpr Fintype.card_ne_zero)

end GlobalTheory.CuspGL
