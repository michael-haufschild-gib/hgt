import GaloisForLFunctions.HTGeometry.Quantum.BoundaryResponse.EdgeGreenVariation
import Mathlib.Tactic.LinearCombination

/-!
# Color spectrum under one edge perturbation

A new parallel boundary edge preserves an old simple color eigenvalue
exactly when the color mode has zero voltage drop on that edge. Every
old color level is preserved when the endpoints share a color and sign.
-/

open Matrix
open scoped Matrix NNReal

namespace GaloisForLFunctions.HTGeometry.BoundaryResponse

open WeightedGraph

noncomputable section

private abbrev seriesVertexDecEq {V : Type*} [DecidableEq V] :
    DecidableEq (V ⊕ SeriesInterior V) := inferInstance

local instance (K N : ℕ) :
    DecidableEq (LayeredBoundary K N ⊕ SeriesInterior (LayeredBoundary K N)) :=
  seriesVertexDecEq

/-- The indicated old color eigenvalue is still an eigenvalue after
adding a boundary edge precisely when its old profile has no edge drop,
or the conductance increment is zero. -/
theorem layeredColorEigenvalue_addBoundaryEdge_iff (K N : ℕ) (i : Fin (N + 1))
    (a b : LayeredBoundary K N) (t : ℝ≥0) :
    (∃ y : LayeredBoundary K N → ℝ, y ≠ 0 ∧ ∀ v,
      ((layeredSeriesNetwork K N).addConductance (.inl a) (.inl b) t).networkFlux
        (seriesMidpointExtension y) (.inl v) = colorEigenvalue K i * y v) ↔
      t = 0 ∨ colorMode i a = colorMode i b := by
  let G := layeredBoundaryGraph K N
  let A := G.networkLaplacian
  let x : LayeredBoundary K N → ℝ := colorMode i
  let μ := colorEigenvalue K i
  let d := edgeDipole a b
  have hx (v : LayeredBoundary K N) : G.networkFlux x v = μ * x v :=
    layeredBoundaryGraph_flux_colorMode K i v
  have hresponse (y : LayeredBoundary K N → ℝ) (v : LayeredBoundary K N) :
      ((layeredSeriesNetwork K N).addConductance (.inl a) (.inl b) t).networkFlux
        (seriesMidpointExtension y) (.inl v) =
        G.networkFlux y v + (t : ℝ) * d v * (y a - y b) :=
    (G.seriesNetwork_addBoundaryEdge_response (layerBoundaryGraph K N) a b t y v).trans
      (G.networkFlux_addConductance a b t y v)
  constructor
  · rintro ⟨y, hnonzero, hy⟩
    by_contra hn
    have ht : (t : ℝ) ≠ 0 := fun h => hn (Or.inl (NNReal.coe_eq_zero.mp h))
    have hdrop : x a - x b ≠ 0 := fun h => hn (Or.inr (sub_eq_zero.mp h))
    have hAx : A *ᵥ x = μ • x := by
      funext v
      exact (G.networkLaplacian_mulVec x v).trans (hx v)
    have hsymm : Aᵀ = A := by
      ext u v
      simpa only [Matrix.transpose_apply, star_trivial] using
        G.isHermitian_networkLaplacian.apply u v
    have hpair : x ⬝ᵥ (A *ᵥ y) = μ * (x ⬝ᵥ y) := by
      rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hsymm, hAx,
        dotProduct_comm (μ • x), dotProduct_smul, smul_eq_mul, dotProduct_comm y]
    have hAy : A *ᵥ y + ((t : ℝ) * (y a - y b)) • d = μ • y := by
      funext v
      have h := (hresponse y v).symm.trans (hy v)
      change (G.networkLaplacian *ᵥ y) v + (t : ℝ) * (y a - y b) * d v = μ * y v
      rw [G.networkLaplacian_mulVec]
      linear_combination h
    have h := congrArg (fun z => x ⬝ᵥ z) hAy
    have hd : d ⬝ᵥ x = x a - x b := edgeDipole_dotProduct a b x
    have hzero : (t : ℝ) * (y a - y b) * (x a - x b) = 0 := by
      simp only [dotProduct_add, dotProduct_smul, smul_eq_mul, hpair, dotProduct_comm x d, hd] at h
      linarith only [h]
    have hab : y a - y b = 0 :=
      (mul_eq_zero.mp ((mul_eq_zero.mp hzero).resolve_right hdrop)).resolve_left ht
    have hyOld (v : LayeredBoundary K N) : G.networkFlux y v = μ * y v := by
      have h := (hresponse y v).symm.trans (hy v)
      simpa only [hab, mul_zero, add_zero] using h
    let level : Set.Ioo (0 : ℝ) (upperBoundaryLevel K N) := ⟨μ, colorEigenvalue_bounds K i⟩
    obtain ⟨j, hj, c, hc, hyc⟩ :=
      (smallPositiveEigenpair_iff K N level y).mp ⟨hnonzero, hyOld⟩
    have hij : i = j := (strictMono_colorEigenvalue K N).injective hj
    subst j
    have hcdrop : c * (x a - x b) = 0 := by
      rw [hyc] at hab
      simpa only [mul_sub] using hab
    exact hdrop ((mul_eq_zero.mp hcdrop).resolve_left hc)
  · intro h
    refine ⟨x, colorMode_ne_zero K i, fun v => ?_⟩
    change ((layeredSeriesNetwork K N).addConductance (.inl a) (.inl b) t).networkFlux
      (seriesMidpointExtension x) (.inl v) = μ * x v
    rw [hresponse x v, hx v]
    rcases h with h | h
    · simp only [h, NNReal.coe_zero, zero_mul, add_zero]
    · change x a = x b at h
      simp only [h, sub_self, mul_zero, add_zero]

/-- The three possible voltage classes of a color mode are inactive,
positive, and negative. -/
theorem colorMode_eq_iff {K N : ℕ} (i : Fin (N + 1)) (a b : LayeredBoundary K N) :
    colorMode i a = colorMode i b ↔
      (a.1 ≠ i ∧ b.1 ≠ i) ∨ (a.1 = i ∧ b.1 = i ∧ a.2.1 = b.2.1) := by
  have hsign (v : LayeredBoundary K N) (hv : v.1 = i) :
      colorMode i v = if v.2.1 then -1 else 1 := by
    rw [colorMode, if_pos hv]
    cases v.2.1 <;> rfl
  by_cases ha : a.1 = i
  · by_cases hb : b.1 = i
    · rw [hsign a ha, hsign b hb]
      cases hs : a.2.1 <;> cases ht : b.2.1 <;> norm_num [ha, hb, hs, ht]
    · rw [hsign a ha]
      cases hs : a.2.1 <;> norm_num [colorMode, ha, hb, hs]
  · by_cases hb : b.1 = i
    · rw [hsign b hb]
      cases ht : b.2.1 <;> norm_num [colorMode, ha, hb, ht]
    · simp [colorMode, ha, hb]

/-- A nonzero edge increment preserves every old color eigenvalue
precisely when the endpoints have the same color and sign. -/
theorem all_layeredColorEigenvalues_addBoundaryEdge_iff (K N : ℕ)
    (a b : LayeredBoundary K N) (t : ℝ≥0) :
    (∀ i : Fin (N + 1), ∃ y : LayeredBoundary K N → ℝ, y ≠ 0 ∧ ∀ v,
      ((layeredSeriesNetwork K N).addConductance (.inl a) (.inl b) t).networkFlux
        (seriesMidpointExtension y) (.inl v) = colorEigenvalue K i * y v) ↔
      t = 0 ∨ (a.1 = b.1 ∧ a.2.1 = b.2.1) := by
  simp only [layeredColorEigenvalue_addBoundaryEdge_iff, colorMode_eq_iff]
  constructor
  · intro h
    rcases h a.1 with ht | ⟨ha, _⟩ | ⟨_, hb, hsign⟩
    · exact Or.inl ht
    · exact (ha rfl).elim
    · exact Or.inr ⟨hb.symm, hsign⟩
  · rintro (ht | ⟨hc, hs⟩) i
    · exact Or.inl ht
    · by_cases h : a.1 = i
      · exact Or.inr (Or.inr ⟨h, hc.symm.trans h, hs⟩)
      · exact Or.inr (Or.inl ⟨h, fun hb => h (hc.trans hb)⟩)

#print axioms layeredColorEigenvalue_addBoundaryEdge_iff
#print axioms all_layeredColorEigenvalues_addBoundaryEdge_iff

end

end GaloisForLFunctions.HTGeometry.BoundaryResponse
