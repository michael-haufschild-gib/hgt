import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.PadicDeterminantPrincipalCongruence
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.SmoothRepresentationScalarTwist
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.CompactSmoothInvariants
import Mathlib.Topology.Algebra.Group.Matrix

/-! A determinant twist of a smooth irreducible representation
with principal-congruence fixed vectors has such vectors exactly
when the twisting character kills the first principal units. -/

noncomputable section

open Matrix Representation

namespace GlobalTheory.GLp

variable {p n : ℕ} [Fact p.Prime] {V : Type*} [AddCommGroup V] [Module ℂ V]

private theorem orbit_span_eq_top {G : Type*} [Group G]
    (ρ : Representation ℂ G V) [ρ.IsIrreducible] {v : V} (hv : v ≠ 0) :
    Submodule.span ℂ (Set.range fun g => ρ g v) = ⊤ := by
  let S := Submodule.span ℂ (Set.range fun g => ρ g v)
  let U : Subrepresentation ρ := ⟨S, fun g {w} hw => by
    refine Submodule.span_induction ?_ (by simp) ?_ ?_ hw
    · rintro _ ⟨g', rfl⟩
      exact Submodule.subset_span ⟨g * g', by change ρ (g * g') v = ρ g (ρ g' v); rw [map_mul, Module.End.mul_apply]⟩
    · intro a b _ _ ha hb
      rw [map_add]
      exact S.add_mem ha hb
    · intro c a _ ha
      rw [map_smul]
      exact S.smul_mem c ha⟩
  have hU : U ≠ ⊥ := fun h => hv (by
    have hmem : v ∈ U := Submodule.subset_span ⟨1, by change ρ 1 v = v; rw [map_one, Module.End.one_apply]⟩
    rwa [h] at hmem)
  exact congrArg Subrepresentation.toSubmodule ((eq_bot_or_eq_top U).resolve_left hU)

theorem determinantTwist_principalFixed_ne_bot_iff
    (hn : 0 < n) (ρ : Representation ℂ (GL (Fin n) ℚ_[p]) V) [ρ.IsIrreducible]
    (hρ : ∀ v : V, IsOpen {g | ρ g v = v}) (hfixed : principalFixed ρ ≠ ⊥)
    (χ : ℚ_[p]ˣ →* ℂˣ) (hχ : IsOpen (χ.ker : Set ℚ_[p]ˣ)) :
    principalFixed (ρ.scalarTwist (χ.comp GeneralLinearGroup.det)) ≠ ⊥ ↔
      ∀ u : ℤ_[p]ˣ, Units.map (PadicInt.toZMod (p := p)).toMonoidHom u = 1 →
        χ (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u) = 1 := by
  let G := GL (Fin n) ℚ_[p]
  let K := principalCongruenceOne p (Fin n)
  let σ := ρ.scalarTwist (χ.comp GeneralLinearGroup.det)
  obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hfixed
  constructor
  · intro htw u hu
    by_contra h
    obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot htw
    let c : ℂ := χ (Units.map (algebraMap ℤ_[p] ℚ_[p]).toMonoidHom u)
    have hc : c - 1 ≠ 0 := fun he => h (Units.ext (sub_eq_zero.mp he))
    let r := σ.comp K.subtype
    have horbit (g : G) : ρ g v ∈ Coinvariants.ker r := by
      obtain ⟨x, hx, hconj, hdet⟩ := exists_principal_conjugate_of_determinant ⟨0, hn⟩ g u hu
      have hact : ρ x (ρ g v) = ρ g v := by
        rw [← Module.End.mul_apply, ← map_mul, show x * g = g * (g⁻¹ * x * g) by
            rw [← mul_assoc, ← mul_assoc, mul_inv_cancel, one_mul],
          map_mul, Module.End.mul_apply, (mem_principalFixed_iff ρ v).mp hv _ hconj]
      have hrel := Coinvariants.sub_mem_ker (ρ := r) (⟨x, hx⟩ : K) (ρ g v)
      change (χ (GeneralLinearGroup.det x) : ℂ) • ρ x (ρ g v) - ρ g v ∈ Coinvariants.ker r at hrel
      rw [hdet, hact] at hrel
      have hm : (c - 1) • ρ g v ∈ Coinvariants.ker r := by
        rw [sub_smul, one_smul]
        exact hrel
      have he := (Coinvariants.ker r).smul_mem (c - 1)⁻¹ hm
      change (c - 1)⁻¹ • ((c - 1) • ρ g v) ∈ Coinvariants.ker r at he
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at he
    have hspan : (⊤ : Submodule ℂ V) ≤ Coinvariants.ker r := by
      rw [← orbit_span_eq_top ρ hv0]
      exact Submodule.span_le.mpr (by rintro _ ⟨g, rfl⟩; exact horbit g)
    letI := isCompact_iff_compactSpace.mp (isCompact_principalCongruenceOne p (Fin n))
    have hs (y : V) : IsOpen {k : K | r k y = y} :=
      (scalarTwist_smooth ρ hρ (χ.comp GeneralLinearGroup.det)
        (hχ.preimage GeneralLinearGroup.continuous_det) y).preimage continuous_subtype_val
    have hd := (invariants_isCompl_coinvariantKer_of_compact r hs).disjoint
    exact hw0 (Submodule.disjoint_def.mp hd w hw (hspan Submodule.mem_top))
  · intro ht
    refine (Submodule.ne_bot_iff _).mpr ⟨v, (mem_principalFixed_iff σ v).mpr ?_, hv0⟩
    intro x hx
    obtain ⟨u, hu, hdet⟩ := determinant_of_mem_principal hx
    change (χ (GeneralLinearGroup.det x) : ℂ) • ρ x v = v
    rw [hdet, ht u hu, Units.val_one, one_smul, (mem_principalFixed_iff ρ v).mp hv x hx]

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.determinantTwist_principalFixed_ne_bot_iff
