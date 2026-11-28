import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.CompactSmoothInvariants
import Mathlib.LinearAlgebra.Basis.VectorSpace

/-! A finite quotient type splits in the restriction of a smooth
representation when the image of the quotient kernel is compact.
Pass to those coinvariants, then average a linear retraction. -/

noncomputable section

namespace Representation

variable {G K Γ V W : Type*} [Group G] [Group K] [Group Γ] [Fintype Γ]
  [TopologicalSpace G] [IsTopologicalGroup G]
  [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ G V) (ρ : Representation ℂ Γ W)
  (ι : K →* G) (q : K →* Γ)

theorem exists_finite_type_retraction (hπ : ∀ v : V, IsOpen {g : G | π g v = v})
    (hq : Function.Surjective q) (hK : IsCompact ((q.ker.map ι : Subgroup G) : Set G))
    (j : W →ₗ[ℂ] V) (hj : Function.Injective j)
    (h : ∀ k w, j (ρ (q k) w) = π (ι k) (j w)) :
    ∃ P : V →ₗ[ℂ] W, P.comp j = LinearMap.id ∧ ∀ k v, P (π (ι k) v) = ρ (q k) (P v) := by
  classical
  let H := q.ker.map ι
  let qρ : Representation ℂ H V := π.comp H.subtype
  letI : CompactSpace H := isCompact_iff_compactSpace.mp hK
  have hsm (v : V) : IsOpen {g : H | qρ g v = v} := (hπ v).preimage continuous_subtype_val
  have hc := invariants_isCompl_coinvariantKer_of_compact qρ hsm
  let p := Coinvariants.mk qρ
  have hfix (w : W) : j w ∈ qρ.invariants := by
    intro g
    obtain ⟨k, hk, hkg⟩ : ∃ k ∈ q.ker, ι k = g.val := g.2
    change π g.val (j w) = j w
    rw [← hkg, ← h k w, show q k = 1 from hk, map_one, Module.End.one_apply]
  have hjp : LinearMap.ker (p.comp j) = ⊥ := by
    apply LinearMap.ker_eq_bot'.mpr
    intro w hw
    have hp : p (j w) = 0 := hw
    have he := (Coinvariants.mk_eq_zero qρ).mp hp
    have h0 := Submodule.disjoint_def.mp hc.disjoint (j w) (hfix w) he
    exact hj (h0.trans (map_zero j).symm)
  obtain ⟨e, he⟩ := (p.comp j).exists_leftInverse_of_injective hjp
  let f := e.comp p
  have fj (w : W) : f (j w) = w := LinearMap.congr_fun he w
  have hker (k : K) (hk : q k = 1) (v : V) : f (π (ι k) v) = f v := by
    let g : H := ⟨ι k, ⟨k, hk, rfl⟩⟩
    exact congrArg e (Coinvariants.mk_self_apply qρ g v)
  obtain ⟨s, hs⟩ := hq.hasRightInverse
  let c : ℂ := Fintype.card Γ
  have hc0 : c ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  let P := c⁻¹ • ∑ γ : Γ, (ρ γ⁻¹).comp (f.comp (π (ι (s γ))))
  have hP (v : V) : P v = c⁻¹ • ∑ γ : Γ, ρ γ⁻¹ (f (π (ι (s γ)) v)) := by
    simp only [P, LinearMap.smul_apply, LinearMap.sum_apply, LinearMap.comp_apply]
  refine ⟨P, LinearMap.ext fun w => ?_, fun k v => ?_⟩
  · change P (j w) = w
    rw [hP]
    have hterm (γ : Γ) : ρ γ⁻¹ (f (π (ι (s γ)) (j w))) = w := by
      rw [← h (s γ), hs γ, fj, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
        Module.End.one_apply]
    simp only [hterm, Finset.sum_const, Finset.card_univ, ← Nat.cast_smul_eq_nsmul ℂ,
      smul_smul]
    change (c⁻¹ * c) • w = w
    rw [inv_mul_cancel₀ hc0, one_smul]
  · rw [hP, hP, map_smul, map_sum]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulRight (q k)) _ _ fun γ => ?_
    let j := s γ * k * (s (γ * q k))⁻¹
    have hj : q j = 1 := by
      simp only [j, map_mul, map_inv, hs γ, hs (γ * q k), mul_inv_cancel]
    have hprod : s γ * k = j * s (γ * q k) := by simp [j, mul_assoc]
    simp only [Equiv.coe_mulRight]
    rw [← Module.End.mul_apply (π (ι (s γ))) (π (ι k)), ← map_mul π, ← map_mul ι, hprod,
      map_mul ι, map_mul π, Module.End.mul_apply, hker j hj, ← Module.End.mul_apply (ρ (q k)), ← map_mul ρ]
    rw [mul_inv_rev, ← mul_assoc, mul_inv_cancel, one_mul]

end Representation

#print axioms Representation.exists_finite_type_retraction
