import GaloisForLFunctions.HTGeometry.BorsukUlam.Subdivision
import GaloisForLFunctions.HTGeometry.BorsukUlam.CrossPolytope
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Realizations of flag complexes on the ℓ¹-sphere

A `GeoFlag n` is a `FlagComplex n` together with a map of its vertices into
`EuclideanSpace ℝ (Fin (n+1))` which is antipodal, lands on the ℓ¹-unit sphere, sends each face
into a single closed orthant, and has all faces of diameter at most `mesh`.

Barycentric subdivision acts on realizations by sending a face to its barycentre; the mesh is
multiplied by `n / (n + 1)`, so iterating drives it to `0`.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace GaloisForLFunctions.BorsukUlam

open Finset

/-- A flag complex with a symmetric realization on the ℓ¹-sphere of `ℝ^{n+1}`. -/
structure GeoFlag (n : ℕ) where
  /-- The underlying complex. -/
  K : FlagComplex n
  /-- The realization of the vertices. -/
  φ : K.V → EuclideanSpace ℝ (Fin (n + 1))
  φ_neg : ∀ v, φ (K.neg v) = -φ v
  φ_l1 : ∀ v, ∑ i, |φ v i| = 1
  orthant : ∀ σ ∈ K.faces, ∀ i, (∀ v ∈ σ, 0 ≤ φ v i) ∨ (∀ v ∈ σ, φ v i ≤ 0)
  /-- A bound for the diameter of the faces. -/
  mesh : ℝ
  mesh_bound : ∀ σ ∈ K.faces, ∀ u ∈ σ, ∀ v ∈ σ, ‖φ u - φ v‖ ≤ mesh

namespace GeoFlag

variable {n : ℕ} (G : GeoFlag n)

theorem mesh_nonneg : 0 ≤ G.mesh := by
  have h := G.K.base_face
  have := G.mesh_bound _ h G.K.base (mem_singleton_self _) G.K.base (mem_singleton_self _)
  simpa using this

/-- The barycentre of a face. -/
noncomputable def bary (σ : Finset G.K.V) : EuclideanSpace ℝ (Fin (n + 1)) :=
  (σ.card : ℝ)⁻¹ • ∑ v ∈ σ, G.φ v

theorem sum_apply' {κ : Type*} (s : Finset κ) (f : κ → EuclideanSpace ℝ (Fin (n + 1)))
    (i : Fin (n + 1)) : (∑ v ∈ s, f v) i = ∑ v ∈ s, f v i := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, PiLp.add_apply, ih]

theorem bary_apply (σ : Finset G.K.V) (i : Fin (n + 1)) :
    G.bary σ i = (σ.card : ℝ)⁻¹ * ∑ v ∈ σ, G.φ v i := by
  rw [bary, PiLp.smul_apply, sum_apply']
  rfl

theorem bary_l1 {σ : Finset G.K.V} (hσ : σ ∈ G.K.faces) : ∑ i, |G.bary σ i| = 1 := by
  have hne : σ.Nonempty := G.K.faces_nonempty σ hσ
  have hcard : (0 : ℝ) < σ.card := by
    exact_mod_cast card_pos.mpr hne
  have hcoord : ∀ i, |G.bary σ i| = (σ.card : ℝ)⁻¹ * ∑ v ∈ σ, |G.φ v i| := by
    intro i
    rw [bary_apply]
    rcases G.orthant σ hσ i with h | h
    · have hsum : 0 ≤ ∑ v ∈ σ, G.φ v i := Finset.sum_nonneg (fun v hv => h v hv)
      rw [abs_mul, abs_of_nonneg (le_of_lt (inv_pos.mpr hcard)), abs_of_nonneg hsum]
      congr 1
      exact Finset.sum_congr rfl (fun v hv => (abs_of_nonneg (h v hv)).symm)
    · have hsum : ∑ v ∈ σ, G.φ v i ≤ 0 := Finset.sum_nonpos (fun v hv => h v hv)
      rw [abs_mul, abs_of_nonneg (le_of_lt (inv_pos.mpr hcard)), abs_of_nonpos hsum,
        ← Finset.sum_neg_distrib]
      congr 1
      exact Finset.sum_congr rfl (fun v hv => (abs_of_nonpos (h v hv)).symm)
  calc ∑ i, |G.bary σ i| = ∑ i, (σ.card : ℝ)⁻¹ * ∑ v ∈ σ, |G.φ v i| := by
        exact Finset.sum_congr rfl (fun i _ => hcoord i)
    _ = (σ.card : ℝ)⁻¹ * ∑ v ∈ σ, ∑ i, |G.φ v i| := by
        rw [← Finset.mul_sum, Finset.sum_comm]
    _ = 1 := by
        rw [Finset.sum_congr rfl (fun v _ => G.φ_l1 v), Finset.sum_const, nsmul_eq_mul, mul_one]
        field_simp

theorem bary_nonneg {σ : Finset G.K.V} {i : Fin (n + 1)} (h : ∀ v ∈ σ, 0 ≤ G.φ v i) :
    0 ≤ G.bary σ i := by
  rw [bary_apply]
  exact mul_nonneg (by positivity) (Finset.sum_nonneg (fun v hv => h v hv))

theorem bary_nonpos {σ : Finset G.K.V} {i : Fin (n + 1)} (h : ∀ v ∈ σ, G.φ v i ≤ 0) :
    G.bary σ i ≤ 0 := by
  rw [bary_apply]
  exact mul_nonpos_of_nonneg_of_nonpos (by positivity) (Finset.sum_nonpos (fun v hv => h v hv))

theorem bary_negF (σ : Finset G.K.V) : G.bary (G.K.negF σ) = - G.bary σ := by
  have hsum : ∑ v ∈ G.K.negF σ, G.φ v = - ∑ v ∈ σ, G.φ v := by
    rw [FlagComplex.negF, Finset.sum_image (fun x _ y _ h => FlagComplex.neg_injective h)]
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl (fun v _ => G.φ_neg v)
  rw [bary, bary, hsum, FlagComplex.card_negF, smul_neg]

theorem norm_sub_bary_le {σ : Finset G.K.V} (hσ : σ ∈ G.K.faces) {u : G.K.V} (hu : u ∈ σ) :
    ‖G.φ u - G.bary σ‖ ≤ (1 - (σ.card : ℝ)⁻¹) * G.mesh := by
  have hpos : 0 < σ.card := card_pos.mpr ⟨u, hu⟩
  have hposR : (0 : ℝ) < σ.card := by exact_mod_cast hpos
  have hkey : G.φ u - G.bary σ = (σ.card : ℝ)⁻¹ • ∑ v ∈ σ, (G.φ u - G.φ v) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, bary, smul_sub]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (ne_of_gt hposR), one_smul]
  have hsum : ‖∑ v ∈ σ, (G.φ u - G.φ v)‖ ≤ ((σ.card : ℝ) - 1) * G.mesh := by
    refine le_trans (norm_sum_le _ _) ?_
    have hsplit : ∑ v ∈ σ, ‖G.φ u - G.φ v‖ = ∑ v ∈ σ.erase u, ‖G.φ u - G.φ v‖ := by
      rw [← Finset.add_sum_erase _ _ hu]
      simp
    rw [hsplit]
    have hb : ∑ v ∈ σ.erase u, ‖G.φ u - G.φ v‖ ≤ (σ.erase u).card • G.mesh :=
      Finset.sum_le_card_nsmul _ _ _ (fun v hv =>
        G.mesh_bound σ hσ u hu v (mem_of_mem_erase hv))
    rw [card_erase_of_mem hu, nsmul_eq_mul] at hb
    refine le_trans hb (le_of_eq ?_)
    congr 1
    have : ((σ.card - 1 : ℕ) : ℝ) = (σ.card : ℝ) - 1 := by
      have : 1 ≤ σ.card := hpos
      push_cast [Nat.cast_sub this]
      ring
    exact this
  rw [hkey, norm_smul, norm_inv, Real.norm_natCast]
  have hfinal : (σ.card : ℝ)⁻¹ * (((σ.card : ℝ) - 1) * G.mesh) = (1 - (σ.card : ℝ)⁻¹) * G.mesh := by
    field_simp
  calc (σ.card : ℝ)⁻¹ * ‖∑ v ∈ σ, (G.φ u - G.φ v)‖
      ≤ (σ.card : ℝ)⁻¹ * (((σ.card : ℝ) - 1) * G.mesh) := by
        exact mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (1 - (σ.card : ℝ)⁻¹) * G.mesh := hfinal

theorem norm_bary_sub_bary_le {σ τ : Finset G.K.V} (hσ : σ ∈ G.K.faces) (hsub : τ ⊆ σ)
    (hτ : τ.Nonempty) : ‖G.bary τ - G.bary σ‖ ≤ (1 - (σ.card : ℝ)⁻¹) * G.mesh := by
  have hposτ : 0 < τ.card := card_pos.mpr hτ
  have hposτR : (0 : ℝ) < τ.card := by exact_mod_cast hposτ
  have hkey : G.bary τ - G.bary σ = (τ.card : ℝ)⁻¹ • ∑ v ∈ τ, (G.φ v - G.bary σ) := by
    rw [Finset.sum_sub_distrib, Finset.sum_const, bary, smul_sub]
    congr 1
    rw [← Nat.cast_smul_eq_nsmul ℝ, smul_smul, inv_mul_cancel₀ (ne_of_gt hposτR), one_smul]
  have hsum : ‖∑ v ∈ τ, (G.φ v - G.bary σ)‖ ≤ (τ.card : ℝ) * ((1 - (σ.card : ℝ)⁻¹) * G.mesh) := by
    refine le_trans (norm_sum_le _ _) ?_
    have hb : ∑ v ∈ τ, ‖G.φ v - G.bary σ‖ ≤ τ.card • ((1 - (σ.card : ℝ)⁻¹) * G.mesh) := by
      refine Finset.sum_le_card_nsmul _ _ _ (fun v hv => ?_)
      exact norm_sub_bary_le G hσ (hsub hv)
    rw [nsmul_eq_mul] at hb
    exact hb
  rw [hkey, norm_smul, norm_inv, Real.norm_natCast]
  calc (τ.card : ℝ)⁻¹ * ‖∑ v ∈ τ, (G.φ v - G.bary σ)‖
      ≤ (τ.card : ℝ)⁻¹ * ((τ.card : ℝ) * ((1 - (σ.card : ℝ)⁻¹) * G.mesh)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = (1 - (σ.card : ℝ)⁻¹) * G.mesh := by
        field_simp

theorem card_le_succ {σ : Finset G.K.V} (hσ : σ ∈ G.K.faces) : σ.card ≤ n + 1 := by
  have h1 := G.K.card_le σ hσ
  have h2 : G.K.cdim σ ≤ n := FlagComplex.cdim_le σ
  simp only [FlagComplex.cdim] at h2
  omega

theorem bary_pair_bound {σ τ : Finset G.K.V} (hσ : σ ∈ G.K.faces) (hτ : τ ∈ G.K.faces)
    (hsub : τ ⊆ σ) : ‖G.bary τ - G.bary σ‖ ≤ (n : ℝ) / (n + 1) * G.mesh := by
  have hτne : τ.Nonempty := G.K.faces_nonempty τ hτ
  have hbound := norm_bary_sub_bary_le G hσ hsub hτne
  refine le_trans hbound ?_
  refine mul_le_mul_of_nonneg_right ?_ G.mesh_nonneg
  have hcard : σ.card ≤ n + 1 := card_le_succ G hσ
  have hpos : 0 < σ.card := card_pos.mpr (G.K.faces_nonempty σ hσ)
  have hR : (0 : ℝ) < σ.card := by exact_mod_cast hpos
  have hR2 : (σ.card : ℝ) ≤ (n : ℝ) + 1 := by exact_mod_cast hcard
  have hinv : ((n : ℝ) + 1)⁻¹ ≤ (σ.card : ℝ)⁻¹ := by
    have h := one_div_le_one_div_of_le hR hR2
    simpa [one_div] using h
  have hid : (n : ℝ) / (n + 1) = 1 - ((n : ℝ) + 1)⁻¹ := by
    field_simp
    ring
  rw [hid]
  linarith

/-- Barycentric subdivision of a realized flag complex. -/
noncomputable def sdGeo (G : GeoFlag n) : GeoFlag n where
  K := FlagComplex.sd G.K
  φ := fun x => G.bary x.1
  φ_neg := fun x => G.bary_negF x.1
  φ_l1 := fun x => G.bary_l1 x.2
  orthant := by
    intro c hc i
    obtain ⟨hne, hchain⟩ := FlagComplex.mem_sdFaces.mp hc
    obtain ⟨m, hm, hmax⟩ := FlagComplex.sdChain_max hchain hne
    rcases G.orthant m.1 m.2 i with h | h
    · exact Or.inl (fun x hx => G.bary_nonneg (fun v hv => h v (hmax x hx hv)))
    · exact Or.inr (fun x hx => G.bary_nonpos (fun v hv => h v (hmax x hx hv)))
  mesh := (n : ℝ) / (n + 1) * G.mesh
  mesh_bound := by
    intro c hc x hx y hy
    obtain ⟨hne, hchain⟩ := FlagComplex.mem_sdFaces.mp hc
    rcases hchain x hx y hy with h | h
    · exact G.bary_pair_bound y.2 x.2 h
    · rw [norm_sub_rev]
      exact G.bary_pair_bound x.2 y.2 h

/-- Iterated barycentric subdivision. -/
noncomputable def tower (G : GeoFlag n) : ℕ → GeoFlag n
  | 0 => G
  | (m + 1) => sdGeo (tower G m)

theorem tower_mesh (G : GeoFlag n) (m : ℕ) :
    (tower G m).mesh = ((n : ℝ) / (n + 1)) ^ m * G.mesh := by
  induction m with
  | zero => simp [tower]
  | succ m ih =>
    show (n : ℝ) / (n + 1) * (tower G m).mesh = _
    rw [ih]
    ring

end GeoFlag

theorem single_neg' {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (a : ℝ) :
    EuclideanSpace.single i (-a) = -EuclideanSpace.single (𝕜 := ℝ) i a := by
  ext j
  rw [EuclideanSpace.single_apply, PiLp.neg_apply, EuclideanSpace.single_apply]
  by_cases hj : j = i <;> simp [hj]

open CrossPolytope in
/-- The cross-polytope realized by the signed basis vectors. -/
noncomputable def crossGeo (n : ℕ) : GeoFlag n where
  K := cross n
  φ := fun x => EuclideanSpace.single x.1 (if x.2 then (1 : ℝ) else -1)
  φ_neg := by
    intro x
    show EuclideanSpace.single x.1 (if !x.2 then (1 : ℝ) else -1) =
      -EuclideanSpace.single x.1 (if x.2 then (1 : ℝ) else -1)
    rcases Bool.eq_false_or_eq_true x.2 with h | h <;> rw [h]
    · simp only [Bool.not_true, if_false, if_true]
      exact single_neg' x.1 1
    · simp only [Bool.not_false, if_false, if_true]
      rw [show (1 : ℝ) = -(-1) by norm_num, single_neg' x.1 (-1)]
      norm_num
  φ_l1 := by
    intro x
    have hc : |(if x.2 then (1 : ℝ) else -1)| = 1 := by
      rcases Bool.eq_false_or_eq_true x.2 with h | h <;> rw [h] <;> simp
    calc ∑ i, |EuclideanSpace.single x.1 (if x.2 then (1 : ℝ) else -1) i|
        = ∑ i, (if i = x.1 then |(if x.2 then (1 : ℝ) else -1)| else 0) := by
          refine Finset.sum_congr rfl (fun i _ => ?_)
          rw [EuclideanSpace.single_apply]
          by_cases h : i = x.1 <;> simp [h]
      _ = 1 := by simp [hc]
  orthant := by
    intro S hS i
    by_cases hex : ∃ v ∈ S, v.1 = i
    · obtain ⟨v, hv, hvi⟩ := hex
      have hother : ∀ u ∈ S, u ≠ v → EuclideanSpace.single u.1
          (if u.2 then (1 : ℝ) else -1) i = 0 := by
        intro u hu hne
        rw [EuclideanSpace.single_apply, if_neg]
        intro hcon
        exact hne ((mem_faces.mp hS).2 u hu v hv (hcon.symm.trans hvi.symm))
      rcases Bool.eq_false_or_eq_true v.2 with h | h
      · left
        intro u hu
        by_cases hu2 : u = v
        · rw [hu2, EuclideanSpace.single_apply, if_pos hvi.symm, h]
          norm_num
        · rw [hother u hu hu2]
      · right
        intro u hu
        by_cases hu2 : u = v
        · rw [hu2, EuclideanSpace.single_apply, if_pos hvi.symm, h]
          norm_num
        · rw [hother u hu hu2]
    · left
      intro u hu
      push Not at hex
      rw [EuclideanSpace.single_apply, if_neg]
      intro hcon
      exact hex u hu hcon.symm
  mesh := 2
  mesh_bound := by
    intro S hS u hu v hv
    have h1 : ‖EuclideanSpace.single u.1 (if u.2 then (1 : ℝ) else -1)‖ = 1 := by
      rw [EuclideanSpace.norm_single]
      rcases Bool.eq_false_or_eq_true u.2 with h | h <;> rw [h] <;> simp
    have h2 : ‖EuclideanSpace.single v.1 (if v.2 then (1 : ℝ) else -1)‖ = 1 := by
      rw [EuclideanSpace.norm_single]
      rcases Bool.eq_false_or_eq_true v.2 with h | h <;> rw [h] <;> simp
    calc ‖EuclideanSpace.single u.1 (if u.2 then (1 : ℝ) else -1) -
            EuclideanSpace.single v.1 (if v.2 then (1 : ℝ) else -1)‖
        ≤ ‖EuclideanSpace.single u.1 (if u.2 then (1 : ℝ) else -1)‖ +
          ‖EuclideanSpace.single v.1 (if v.2 then (1 : ℝ) else -1)‖ := norm_sub_le _ _
      _ = 2 := by rw [h1, h2]; norm_num

end GaloisForLFunctions.BorsukUlam
