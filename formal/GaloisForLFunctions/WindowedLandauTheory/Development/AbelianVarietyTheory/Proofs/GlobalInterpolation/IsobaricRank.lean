import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.NormalizedTypesCompatibility

/-! Local dimensions add under isobaric sums and are invariant under twists.
The local dimension of each Speh block is its rank times its length. -/

noncomputable section

open NumberField IsDedekindDomain
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.MainNotions
open WindowedLandauTheory.MainNotions.N

namespace WindowedLandauTheory.MainNotions.N

variable {R : Ranks} {H : Host R} {what₂ : Rows.Data R}
variable (N : NData R H what₂) (A : NAut N)

theorem lpDim_spehLoc (p : Part A.CG) (w : PlE H) :
    A.lpDim (spehLoc N A p w) = p.a * p.d := by
  have h (L : List ℝ) :
      A.lpDim (L.foldr (fun (k : ℝ) acc =>
        A.lpSum (A.lpTw (A.locG p.π w) (((p.d : ℝ) - 1) / 2 - k)) acc)
        (A.lpZero w)) = p.a * L.length := by
    induction L with
    | nil => simp only [List.foldr_nil, A.lpDim_zero, List.length_nil, mul_zero]
    | cons k L ih =>
      rw [List.foldr_cons, A.lpDim_sum, A.lpDim_tw, A.locG_dim, ih, List.length_cons,
        Nat.mul_succ, Nat.add_comm]
  have hlen : ((List.range p.d : List ℕ) : List ℝ).length = p.d := by
    change ((List.range p.d).flatMap (pure ∘ fun k : ℕ => (k : ℝ))).length = p.d
    rw [List.flatMap_pure_eq_map, List.length_map, List.length_range]
  rw [spehLoc, h, hlen]

theorem lpDim_isoLoc (P : List (Part A.CG)) (w : PlE H) :
    A.lpDim (isoLoc N A P w) = rankIso N A P := by
  induction P with
  | nil => exact A.lpDim_zero w
  | cons p P ih =>
    change A.lpDim (A.lpSum (spehLoc N A p w) (isoLoc N A P w)) =
      p.a * p.d + rankIso N A P
    rw [A.lpDim_sum, lpDim_spehLoc, ih]

end WindowedLandauTheory.MainNotions.N


namespace WindowedLandauTheory.NormalizedTypes

private theorem isSplitPl_of_not_isConjPl {R : Ranks} {H : Host R}
    (v : HeightOneSpectrum (𝓞 H.E)) (hv : ¬ IsConjPl H v v) : IsSplitPl H v := by
  by_contra h
  apply hv
  let c := RingOfIntegers.mapRingHom (H.conj : H.E →+* H.E)
  have hi : v.asIdeal ≤ v.asIdeal.comap c := by
    intro x hx
    by_contra hx'
    exact h ⟨x, hx, fun y hy => by
      have he : y = c x := RingOfIntegers.ext hy
      rw [he]; exact hx'⟩
  have he := v.isMaximal.eq_of_le (Ideal.comap_ne_top c v.isPrime.ne_top) hi
  intro x y hy
  have hy' : y = c x := RingOfIntegers.ext hy
  rw [hy', ← Ideal.mem_comap, ← he]

/-- The local type matches at all designated places of a regular isobaric
parameter, so its polynomials have the degree and monicity of the row labels. -/
theorem exists_parC_of_hasParamW (D : D7) (i : D.nd.Loc) (σ : D.what₂.FT)
    (P : List (Part D.naut.CG)) (hP : HasParamW D.nd D.naut i σ P)
    (hcsd : ∀ p ∈ P, D.naut.csd p.π)
    (hnd : (P.map fun p => ((⟨p.a, p.π⟩ : Σ a, D.naut.CG a), p.d)).Nodup) :
    ∃ Q : ParC D, Q.val = P ∧ ∀ k v,
      D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut Q.val (D.naut.plGw k v)) =
        D.nd.lab k σ v := by
  have h (k : Fin 2) (v : D.nd.PlG k) :
      D.naut.items₂ k (D.naut.plGw k v) (isoLoc D.nd D.naut P (D.naut.plGw k v)) =
        D.nd.lab k σ v := by
    rw [hP.2.2 _ (isSplitPl_of_not_isConjPl _ (D.naut.plGw_nconj k v v)), ← D.naut.lab_loc i]
  refine ⟨⟨P, ?_⟩, rfl, h⟩
  refine ⟨fun p hp => ⟨(hP.1 p hp).1, (hP.1 p hp).2, hcsd p hp⟩, hnd, hP.2.1, fun k v => ?_⟩
  exact (h k v).symm ▸ D.nd.lab_monic k σ v

end WindowedLandauTheory.NormalizedTypes
