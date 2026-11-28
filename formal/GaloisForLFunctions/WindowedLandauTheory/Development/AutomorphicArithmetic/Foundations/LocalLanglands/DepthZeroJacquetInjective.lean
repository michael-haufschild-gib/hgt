import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.PadicProjectionTorus
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.PrincipalFixedReduction
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.CompactSmoothInvariants

/-! A vector in the principal-congruence fixed space that is fixed
by the forward residue radical remains nonzero in coinvariants
after all translates by the projection torus. Opposite radical
averaging and one diagonal step give the induction. -/

noncomputable section

open Matrix Representation GlobalTheory.OppRad

namespace GlobalTheory.GLp

variable {p n : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module ℂ V]
  (ρ : Representation ℂ (GL (Fin n) ℚ_[p]) V)

local notation "φ" => RingHom.mapMatrix (m := Fin n) (PadicInt.toZMod (p := p))
local notation "K" => principalCongruenceOne p (Fin n)
local notation "r" => MonoidHom.comp ρ (Subgroup.subtype K)
local notation "σ" => principalFixedReduction ρ
local notation "red" => integralReduction p (Fin n)
local notation "inc" => integralInclusion p (Fin n)

theorem eq_zero_of_projectionTorus_mem_coinvariantKer
    (hρ : ∀ v : V, IsOpen {g : GL (Fin n) ℚ_[p] | ρ g v = v})
    {P : Matrix (Fin n) (Fin n) ℤ_[p]} (hP : P * P = P) (m : ℕ)
    (v : principalFixed ρ)
    (hv : ∀ u ∈ U (φ P) (1 - φ P), σ u v = v)
    (hm : ρ (projectionTorus hP m) v.val ∈ Coinvariants.ker r) :
    v = 0 := by
  have hp : φ P * φ P = φ P := by rw [← map_mul, hP]
  induction m generalizing v with
  | zero =>
    rw [projectionTorus_zero, map_one, Module.End.one_apply] at hm
    haveI : CompactSpace K := isCompact_iff_compactSpace.mp (isCompact_principalCongruenceOne p (Fin n))
    have hr (w : V) : IsOpen {g : K | r g w = w} := (hρ w).preimage continuous_subtype_val
    have hc := (invariants_isCompl_coinvariantKer_of_compact r hr).disjoint
    exact Subtype.ext (Submodule.disjoint_def.mp hc v.val v.2 hm)
  | succ m ih =>
    let t := S σ (U (1 - φ P) (φ P)) v
    let d := projectionTorus hP 1
    have hfix (k : GL (Fin n) ℤ_[p]) (hk : red k ∈ U (φ P) (1 - φ P)) :
        ρ (inc k) (ρ d t.val) = ρ d t.val := by
      obtain ⟨k', hk', he⟩ := conjugate_forward_radical hP hk
      change d * inc k' = inc k * d at he
      rw [← Module.End.mul_apply, ← map_mul, ← he, map_mul, Module.End.mul_apply,
        ← principalFixedReduction_apply ρ k' t]
      rw [show σ (red k') t = t from S_left hk' v]
    have hz : ρ d t.val ∈ principalFixed ρ := by
      apply (mem_principalFixed_iff ρ _).mpr
      rintro _ ⟨k, hk, rfl⟩
      exact hfix k ((show red k = 1 from hk).symm ▸ one_mem _)
    let w : principalFixed ρ := ⟨ρ d t.val, hz⟩
    have hw (u : GL (Fin n) (ZMod p)) (hu : u ∈ U (φ P) (1 - φ P)) : σ u w = w := by
      obtain ⟨k, rfl⟩ := integralReduction_surjective p (Fin n) u
      apply Subtype.ext
      rw [principalFixedReduction_apply]
      exact hfix k hu
    have hw0 : ρ (projectionTorus hP m) w.val ∈ Coinvariants.ker r := by
      let N := U (1 - φ P) (φ P)
      letI := Fintype.ofFinite N
      change ρ (projectionTorus hP m) (ρ d (S σ N v).val) ∈ Coinvariants.ker r
      rw [← Module.End.mul_apply, ← map_mul, ← projectionTorus_succ, S_apply, Submodule.coe_sum, map_sum]
      refine Submodule.sum_mem _ fun u _ => ?_
      obtain ⟨k, k', hk, hk', he⟩ := conjugate_opposite_radical hP u.2 m
      rw [← hk, principalFixedReduction_apply, ← Module.End.mul_apply, ← map_mul, he,
        map_mul, Module.End.mul_apply]
      let a : K := ⟨inc k', ⟨k', hk', rfl⟩⟩
      let x := ρ (projectionTorus hP (m + 1)) v.val
      change r a x ∈ Coinvariants.ker r
      rw [← sub_add_cancel (r a x) x]
      exact (Coinvariants.ker r).add_mem (Coinvariants.sub_mem_ker a x) hm
    have hwz : w = 0 := ih w hw hw0
    have ht : t = 0 := by
      apply Subtype.ext
      have he : ρ d t.val = 0 := congrArg Subtype.val hwz
      have h := congrArg (ρ d⁻¹) he
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply, map_zero] at h
      exact h
    exact oppInj matrix_regular hp
      (by simp only [mul_sub, sub_mul, hp, mul_one, one_mul, sub_self, sub_zero])
      (by rw [mul_sub, hp, mul_one, sub_self])
      (by rw [sub_mul, hp, one_mul, sub_self]) v hv ht

end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.eq_zero_of_projectionTorus_mem_coinvariantKer
