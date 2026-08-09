import Mathlib

/-!
# The finite-dimensional geometric family

For finitely many contracting scalars the family of monomials indexed by occupation vectors is
absolutely summable and sums to the product of the individual geometric sums.  This is the
complex-valued counterpart of the nonnegative identity used for occupation masses; the absolute
summability has to be carried alongside, because the two-factor product rule for sums needs it.
-/

namespace HTGeometry

open Filter Topology
open scoped BigOperators

private theorem hasSum_pi_geometric_fin :
    ∀ (n : ℕ) (u : Fin n → ℂ), (∀ i, ‖u i‖ < 1) →
      HasSum (fun f : Fin n → ℕ => ∏ i, u i ^ f i) (∏ i, (1 - u i)⁻¹) ∧
        Summable (fun f : Fin n → ℕ => ‖∏ i, u i ^ f i‖) := by
  intro n
  induction n with
  | zero =>
      intro u _
      haveI : Unique (Fin 0 → ℕ) := Pi.uniqueOfIsEmpty _
      have hconst : (fun f : Fin 0 → ℕ => ∏ i, u i ^ f i) = fun _ => (1 : ℂ) := by
        funext f
        simp
      have hone : ∏ i : Fin 0, (1 - u i)⁻¹ = (1 : ℂ) := by simp
      have hnconst : (fun f : Fin 0 → ℕ => ‖∏ i, u i ^ f i‖) = fun _ => (1 : ℝ) := by
        funext f
        simp
      refine ⟨?_, ?_⟩
      · rw [hconst, hone]
        exact hasSum_single default (fun b hb => absurd (Subsingleton.elim b default) hb)
      · rw [hnconst]
        exact ⟨1, hasSum_single default (fun b hb => absurd (Subsingleton.elim b default) hb)⟩
  | succ n ih =>
      intro u hu
      obtain ⟨ihsum0, ihnorm0⟩ := ih (fun i => u i.succ) (fun i => hu i.succ)
      have ihsum : HasSum (fun h : Fin n → ℕ => ∏ i : Fin n, u i.succ ^ h i)
          (∏ i : Fin n, (1 - u i.succ)⁻¹) := ihsum0
      have ihnorm : Summable (fun h : Fin n → ℕ => ‖∏ i : Fin n, u i.succ ^ h i‖) := ihnorm0
      have hsplit : ∀ f : Fin (n + 1) → ℕ,
          ∏ i, u i ^ f i = u 0 ^ f 0 * ∏ i : Fin n, u i.succ ^ f i.succ := by
        intro f
        rw [Fin.prod_univ_succ]
      have hgeom : HasSum (fun c : ℕ => u 0 ^ c) (1 - u 0)⁻¹ :=
        hasSum_geometric_of_norm_lt_one (hu 0)
      have hgeomnorm : Summable (fun c : ℕ => ‖u 0 ^ c‖) := by
        have hg : Summable (fun c : ℕ => ‖u 0‖ ^ c) :=
          summable_geometric_of_lt_one (norm_nonneg _) (hu 0)
        exact hg.congr fun c => (norm_pow (u 0) c).symm
      have hpairsum : Summable (fun x : ℕ × (Fin n → ℕ) =>
          u 0 ^ x.1 * ∏ i : Fin n, u i.succ ^ x.2 i) :=
        summable_mul_of_summable_norm (f := fun c : ℕ => u 0 ^ c)
          (g := fun h : Fin n → ℕ => ∏ i : Fin n, u i.succ ^ h i) hgeomnorm ihnorm
      have hpair : HasSum (fun x : ℕ × (Fin n → ℕ) =>
          u 0 ^ x.1 * ∏ i : Fin n, u i.succ ^ x.2 i)
          ((1 - u 0)⁻¹ * ∏ i : Fin n, (1 - u i.succ)⁻¹) :=
        HasSum.mul (f := fun c : ℕ => u 0 ^ c)
          (g := fun h : Fin n → ℕ => ∏ i : Fin n, u i.succ ^ h i) hgeom ihsum hpairsum
      have hpairnorm : Summable (fun x : ℕ × (Fin n → ℕ) =>
          ‖u 0 ^ x.1 * ∏ i : Fin n, u i.succ ^ x.2 i‖) := hpairsum.norm
      constructor
      · have he := (Fin.consEquiv fun _ : Fin (n + 1) => ℕ).hasSum_iff
          (f := fun f : Fin (n + 1) → ℕ => ∏ i, u i ^ f i)
          (a := ∏ i, (1 - u i)⁻¹)
        rw [← he]
        rw [Fin.prod_univ_succ (f := fun i => (1 - u i)⁻¹)]
        refine hpair.congr_fun fun x => ?_
        rw [Function.comp_apply, hsplit]
        simp [Fin.consEquiv]
      · have he := (Fin.consEquiv fun _ : Fin (n + 1) => ℕ).summable_iff
          (f := fun f : Fin (n + 1) → ℕ => ‖∏ i, u i ^ f i‖)
        rw [← he]
        refine hpairnorm.congr fun x => ?_
        rw [Function.comp_apply, hsplit]
        simp [Fin.consEquiv]

/-- **The finite-index geometric identity.**  For finitely many contracting scalars the occupation
monomials sum to the product of the geometric sums. -/
theorem hasSum_pi_geometric {ι : Type*} [Fintype ι] (u : ι → ℂ) (hu : ∀ i, ‖u i‖ < 1) :
    HasSum (fun f : ι → ℕ => ∏ i, u i ^ f i) (∏ i, (1 - u i)⁻¹) := by
  classical
  let e := Fintype.equivFin ι
  let pe : (ι → ℕ) ≃ (Fin (Fintype.card ι) → ℕ) :=
    Equiv.piCongrLeft (fun _ : Fin (Fintype.card ι) => ℕ) e
  obtain ⟨hfin, _⟩ := hasSum_pi_geometric_fin (Fintype.card ι) (fun j => u (e.symm j))
    (fun j => hu _)
  have hval : ∏ j, (1 - u (e.symm j))⁻¹ = ∏ i, (1 - u i)⁻¹ :=
    Fintype.prod_equiv e.symm (fun j => (1 - u (e.symm j))⁻¹) (fun i => (1 - u i)⁻¹) (by simp)
  rw [hval] at hfin
  have hfun : (fun h : Fin (Fintype.card ι) → ℕ => ∏ j, u (e.symm j) ^ h j)
      = (fun f : ι → ℕ => ∏ i, u i ^ f i) ∘ pe.symm := by
    funext h
    rw [Function.comp_apply]
    exact (Fintype.prod_equiv e (fun i => u i ^ (pe.symm h) i)
      (fun j => u (e.symm j) ^ h j) (by simp [pe])).symm
  rw [hfun] at hfin
  exact (Equiv.hasSum_iff pe.symm).mp hfin

/-- Absolute summability of the finite-index geometric family. -/
theorem summable_norm_pi_geometric {ι : Type*} [Fintype ι] (u : ι → ℂ) (hu : ∀ i, ‖u i‖ < 1) :
    Summable (fun f : ι → ℕ => ‖∏ i, u i ^ f i‖) := by
  classical
  let e := Fintype.equivFin ι
  let pe : (ι → ℕ) ≃ (Fin (Fintype.card ι) → ℕ) :=
    Equiv.piCongrLeft (fun _ : Fin (Fintype.card ι) => ℕ) e
  obtain ⟨_, hnorm⟩ := hasSum_pi_geometric_fin (Fintype.card ι) (fun j => u (e.symm j))
    (fun j => hu _)
  have hfun : (fun h : Fin (Fintype.card ι) → ℕ => ‖∏ j, u (e.symm j) ^ h j‖)
      = (fun f : ι → ℕ => ‖∏ i, u i ^ f i‖) ∘ pe.symm := by
    funext h
    rw [Function.comp_apply]
    congr 1
    exact (Fintype.prod_equiv e (fun i => u i ^ (pe.symm h) i)
      (fun j => u (e.symm j) ^ h j) (by simp [pe])).symm
  rw [hfun] at hnorm
  exact (Equiv.summable_iff pe.symm).mp hnorm

end HTGeometry
