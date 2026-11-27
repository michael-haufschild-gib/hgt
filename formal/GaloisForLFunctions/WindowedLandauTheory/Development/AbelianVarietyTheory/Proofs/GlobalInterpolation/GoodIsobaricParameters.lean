import GaloisForLFunctions.WindowedLandauTheory.CyclotomicNorms.GoodFactorMultiplicity
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.IsobaricRank

/-! At a designated place the inertia polynomial of an isobaric sum is the
product of the polynomials of its cuspidal blocks, with Speh multiplicities.
The common divisor-degree condition forces a single block of multiplicity one. -/

noncomputable section

open Polynomial
open WindowedLandauTheory.BasicNotions WindowedLandauTheory.MainNotions
open WindowedLandauTheory.CyclotomicNorms
open WindowedLandauTheory.MainNotions.N

namespace WindowedLandauTheory.MainNotions.N

private theorem items₂_spehLoc (D : D7) (k : Fin 2) (v : D.nd.PlG k)
    (hTw : ∀ (a : D.naut.LP (D.naut.plGw k v)) (s : ℝ),
      D.naut.items₂ k _ (D.naut.lpTw a s) = D.naut.items₂ k _ a)
    (p : Part D.naut.CG) :
    D.naut.items₂ k _ (spehLoc D.nd D.naut p (D.naut.plGw k v)) =
      D.naut.items₂ k _ (D.naut.locG p.π (D.naut.plGw k v)) ^ p.d := by
  let w := D.naut.plGw k v
  let a := D.naut.locG p.π w
  have h (L : List ℝ) :
      D.naut.items₂ k w (L.foldr (fun (j : ℝ) acc =>
        D.naut.lpSum (D.naut.lpTw a (((p.d : ℝ) - 1) / 2 - j)) acc) (D.naut.lpZero w)) =
      (D.naut.items₂ k w a) ^ L.length := by
    induction L with
    | nil => simp only [List.foldr_nil, D.naut.inertiaCharpoly_zero, List.length_nil, pow_zero]
    | cons j L ih =>
      rw [List.foldr_cons, D.naut.inertiaCharpoly_add, hTw, ih, List.length_cons, pow_succ']
  rw [spehLoc, h, length_range_coe_real]

/-- Twisting leaves the inertia factors unchanged, so the label of an
isobaric sum is the product of the labels of its Speh blocks. -/
theorem items₂_isoLoc (D : D7) (k : Fin 2) (v : D.nd.PlG k)
    (hTw : ∀ (a : D.naut.LP (D.naut.plGw k v)) (s : ℝ),
      D.naut.items₂ k _ (D.naut.lpTw a s) = D.naut.items₂ k _ a)
    (P : List (Part D.naut.CG)) :
    D.naut.items₂ k _ (isoLoc D.nd D.naut P (D.naut.plGw k v)) =
      (P.map fun p => D.naut.items₂ k _ (D.naut.locG p.π (D.naut.plGw k v)) ^ p.d).prod := by
  induction P with
  | nil => exact D.naut.inertiaCharpoly_zero _ _
  | cons p P ih =>
    change D.naut.items₂ k _ (D.naut.lpSum (spehLoc D.nd D.naut p (D.naut.plGw k v))
      (isoLoc D.nd D.naut P (D.naut.plGw k v))) = _
    rw [D.naut.inertiaCharpoly_add, items₂_spehLoc D k v hTw, ih, List.map_cons, List.prod_cons]

/-- A good parameter with full-rank local labels is cuspidal. The degree
bounds become equalities because their weighted sum is the full rank. -/
theorem isCuspIso_of_goodSig (D : D7) (P : List (Part D.naut.CG))
    (hpos : ∀ p ∈ P, 1 ≤ p.a ∧ 1 ≤ p.d) (hrank : rankIso D.nd D.naut P = D.R.r)
    (hg : goodSig D.nd D.naut P)
    (hTw : ∀ (k : Fin 2) (v : D.nd.PlG k) (a : D.naut.LP (D.naut.plGw k v)) (s : ℝ),
      D.naut.items₂ k _ (D.naut.lpTw a s) = D.naut.items₂ k _ a)
    (hdeg : ∀ (k : Fin 2) (v : D.nd.PlG k) (a : D.naut.LP (D.naut.plGw k v)),
      (D.naut.items₂ k _ a).natDegree ≤ D.naut.lpDim a) :
    IsCuspIso D.nd D.naut P := by
  classical
  let k : Fin 2 := 0
  letI : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  let w := D.naut.plGw k
  let f (v : D.nd.PlG k) := D.naut.items₂ k (w v) (isoLoc D.nd D.naut P (w v))
  let F (v : D.nd.PlG k) (j : Fin P.length) := D.naut.items₂ k (w v) (D.naut.locG (P.get j).π (w v))
  let a (j : Fin P.length) := (P.get j).a
  let d (j : Fin P.length) := (P.get j).d
  obtain ⟨hm, -, -, -, hav, -⟩ := (hg k).1
  have hprod (v : D.nd.PlG k) : f v = ∏ j, F v j ^ d j := by
    rw [show f v = _ from items₂_isoLoc D k v (hTw k v) P, ← List.prod_ofFn]
    exact congrArg List.prod (List.ofFn_getElem_eq_map P
      (fun p => D.naut.items₂ k (w v) (D.naut.locG p.π (w v)) ^ p.d)).symm
  have hsum : ∑ j, a j * d j = D.R.r := by
    rw [← List.sum_ofFn, ← hrank]
    exact congrArg List.sum (List.ofFn_getElem_eq_map P (fun p => p.a * p.d))
  have hd (j : Fin P.length) : 0 < d j := (hpos _ (P.get_mem j)).2
  have he (v : D.nd.PlG k) (j : Fin P.length) : (F v j).natDegree = a j := by
    have hnonzero : ∀ j ∈ (Finset.univ : Finset (Fin P.length)), F v j ^ d j ≠ 0 := by
      rw [← Finset.prod_ne_zero_iff, ← hprod]
      exact (hm v).1.ne_zero
    have hsum' : ∑ j, (F v j).natDegree * d j = ∑ j, a j * d j := by
      have hv : (f v).natDegree = D.R.r := (hm v).2.1
      rw [hsum, ← hv, hprod, natDegree_prod _ _ hnonzero]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [natDegree_pow, Nat.mul_comm]
    have hle (j : Fin P.length) (_ : j ∈ Finset.univ) :
        (F v j).natDegree * d j ≤ a j * d j := by
      have h := hdeg k v (D.naut.locG (P.get j).π (w v))
      rw [D.naut.locG_dim] at h
      exact Nat.mul_le_mul_right _ h
    exact Nat.eq_of_mul_eq_mul_right (hd j)
      ((Finset.sum_eq_sum_iff_of_le hle).mp hsum' j (Finset.mem_univ j))
  have hr : 0 < D.R.r := by
    have := D.R.two_le_m
    show 0 < D.R.k + D.R.m - 1
    omega
  obtain ⟨hcard, h⟩ := card_eq_one_of_common_divisor_degrees hr f F a d
    (fun j => (hpos _ (P.get_mem j)).1) hd hsum hprod he hav
  rw [Fintype.card_fin] at hcard
  obtain ⟨p, rfl⟩ := List.length_eq_one_iff.mp hcard
  obtain ⟨hd1, ha1⟩ := h ⟨0, by simp⟩
  rcases p with ⟨a₀, π, d₀⟩
  change d₀ = 1 at hd1
  change a₀ = D.R.r at ha1
  subst d₀ a₀
  exact ⟨π, rfl⟩


/-- The base-change parameter of a point has positive parts of total rank
`r` after removing the rank-one Speh block. -/
theorem parts_pos_and_rank_of_hasParamX (D : D7) (i : D.nd.Loc) (x : D.nd.X i)
    (P : List (Part D.naut.CG)) (hP : HasParamX D.nd D.naut i x P) :
    (∀ p ∈ P, 1 ≤ p.a ∧ 1 ≤ p.d) ∧ rankIso D.nd D.naut P = D.R.r := by
  obtain ⟨Q, -, hQ⟩ := hP
  refine ⟨fun p hp => ?_, ?_⟩
  · let p' : Part D.naut.CG := ⟨p.a, D.naut.tw p.π D.naut.etaTinv, p.d⟩
    have hp' : p' ∈ twistIso D.nd D.naut (P ++ [muPart D.nd D.naut i]) D.naut.etaTinv :=
      List.mem_map.mpr ⟨p, List.mem_append_left _ hp, rfl⟩
    exact ⟨(hQ.1 p' hp').1, (hQ.1 p' hp').2.1⟩
  · have hr := hQ.2.2.1
    have hs : rankIso D.nd D.naut
        (twistIso D.nd D.naut (P ++ [muPart D.nd D.naut i]) D.naut.etaTinv) =
        rankIso D.nd D.naut P + D.R.t := by
      simp [rankIso, twistIso, muPart, List.map_map, Function.comp_def]
    rw [hs, show D.R.nV = D.R.r + D.R.t from rfl] at hr
    exact Nat.add_right_cancel hr

end WindowedLandauTheory.MainNotions.N

namespace WindowedLandauTheory.NormalizedTypes

/-- A good row with a matching isobaric realization has a single cuspidal part. -/
theorem isCuspIso_of_goodRow (D : D7) (i : D.nd.Loc) (σ : D.what₂.FT)
    (P : List (Part D.naut.CG)) (hP : HasParamW D.nd D.naut i σ P) (hg : D.nd.goodRow σ)
    (hTw : ∀ (k : Fin 2) (v : D.nd.PlG k) (a : D.naut.LP (D.naut.plGw k v)) (s : ℝ),
      D.naut.items₂ k _ (D.naut.lpTw a s) = D.naut.items₂ k _ a)
    (hdeg : ∀ (k : Fin 2) (v : D.nd.PlG k) (a : D.naut.LP (D.naut.plGw k v)),
      (D.naut.items₂ k _ a).natDegree ≤ D.naut.lpDim a) :
    IsCuspIso D.nd D.naut P := by
  have hs : goodSig D.nd D.naut P := by
    intro k
    dsimp only
    rw [funext (items₂_isoLoc_eq_lab_of_hasParamW D i σ P hP k)]
    exact hg k
  exact isCuspIso_of_goodSig D P hP.1 hP.2.1 hs hTw hdeg

/-- For a good row, a regular conjugate-self-dual realization identifies its
base-change multiplicities with the single rank-`r` cuspidal part. -/
theorem cuspidal_of_goodRow (D : D7) (i : D.nd.Loc) (σ : D.what₂.FT)
    (P : List (Part D.naut.CG)) (hP : HasParamW D.nd D.naut i σ P) (hg : D.nd.goodRow σ)
    (hcsd : ∀ p ∈ P, D.naut.csd p.π)
    (hreg : ∀ p ∈ P, ∀ τ, (D.naut.infG p.π τ).Nodup ∧
      ∀ z ∈ D.naut.infG p.π τ, ∃ k : ℤ, z = (k : ℂ) + ((D.R.r : ℂ) - (p.d : ℂ)) / 2)
    (hTw : ∀ (k : Fin 2) (v : D.nd.PlG k) (a : D.naut.LP (D.naut.plGw k v)) (s : ℝ),
      D.naut.items₂ k _ (D.naut.lpTw a s) = D.naut.items₂ k _ a)
    (hdeg : ∀ (k : Fin 2) (v : D.nd.PlG k) (a : D.naut.LP (D.naut.plGw k v)),
      (D.naut.items₂ k _ a).natDegree ≤ D.naut.lpDim a) :
    D.ntypes.cuspidal σ := by
  have hbc := D.bc_tie i σ P hP hcsd hreg
  obtain ⟨π, rfl⟩ := isCuspIso_of_goodRow D i σ P hP hg hTw hdeg
  exact hbc

end WindowedLandauTheory.NormalizedTypes
