import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.Foundations.LocalLanglands.BlockUnipotentRadicals

/-! Block upper triangular matrices normalize the strict block
unipotent radical. This preserves Jacquet relations under their
action on the representation. -/

noncomputable section

open Matrix Representation

namespace GlobalTheory.GLp

variable {k : Type} [Field k] {n : ℕ} {b : Fin n → ℕ}

private theorem blockTriangular_mul_isStrictBlockUpper {X Y : Matrix (Fin n) (Fin n) k}
    (hX : X.BlockTriangular b) (hY : IsStrictBlockUpper b Y) :
    IsStrictBlockUpper b (X * Y) := by
  intro i j hij
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun s _ => ?_
  by_cases hs : b s < b i
  · rw [hX hs, zero_mul]
  · rw [hY s j (hij.trans (le_of_not_gt hs)), mul_zero]

theorem conj_mem_blockUnipotentRadical_of_blockTriangular
    {g u : GL (Fin n) k} (hg : g.val.BlockTriangular b)
    (hu : u ∈ blockUnipotentRadical k b) :
    g * u * g⁻¹ ∈ blockUnipotentRadical k b := by
  letI := g.invertible
  have hgi : (g⁻¹).val.BlockTriangular b := by
    rw [Matrix.coe_units_inv]
    exact Matrix.blockTriangular_inv_of_blockTriangular hg
  have h : (g * u * g⁻¹).val - 1 = g.val * (u.val - 1) * (g⁻¹).val := by
    rw [mul_sub, sub_mul, mul_one, Units.mul_inv]
    rfl
  change IsStrictBlockUpper b ((g * u * g⁻¹).val - 1)
  rw [h]
  exact (blockTriangular_mul_isStrictBlockUpper hg hu).mul_blockTriangular hgi

theorem apply_mem_coinvariantKer_of_conjugation {G V : Type} [Group G]
    [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) {H H' : Subgroup G}
    {g : G} (hg : ∀ u ∈ H, g * u * g⁻¹ ∈ H') {v : V}
    (hv : v ∈ Coinvariants.ker (ρ.comp H.subtype)) :
    ρ g v ∈ Coinvariants.ker (ρ.comp H'.subtype) := by
  let r : Representation ℂ H' V := ρ.comp H'.subtype
  change ρ g v ∈ Coinvariants.ker r
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨u, w⟩, rfl⟩ := hv
    let x : H' := ⟨g * u.val * g⁻¹, hg u.val u.2⟩
    change ρ g (ρ u.val w - w) ∈ Coinvariants.ker r
    have he : ρ g (ρ u.val w) = r x (ρ g w) := by
      change ρ g (ρ u.val w) = ρ (g * u.val * g⁻¹) (ρ g w)
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right]
    rw [map_sub, he]
    exact Coinvariants.sub_mem_ker x (ρ g w)
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ c hx

theorem blockTriangular_apply_mem_blockCoinvariantKer
    {V : Type} [AddCommGroup V] [Module ℂ V]
    (ρ : Representation ℂ (GL (Fin n) k) V)
    {g : GL (Fin n) k} (hg : g.val.BlockTriangular b) {v : V}
    (hv : v ∈ Coinvariants.ker (ρ.comp (blockUnipotentRadical k b).subtype)) :
    ρ g v ∈ Coinvariants.ker (ρ.comp (blockUnipotentRadical k b).subtype) :=
  apply_mem_coinvariantKer_of_conjugation ρ
    (fun _ hu => conj_mem_blockUnipotentRadical_of_blockTriangular hg hu) hv


end GlobalTheory.GLp

#print axioms GlobalTheory.GLp.blockTriangular_apply_mem_blockCoinvariantKer
