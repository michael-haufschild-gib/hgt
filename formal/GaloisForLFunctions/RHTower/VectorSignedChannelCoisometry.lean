import Mathlib.Analysis.InnerProductSpace.l2Space
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The vector-valued signed channel coisometry

`mobius-signed-channel-coisometry-incidence-law.md`, equations `(5)`--`(10)`, `(22)`, `(25)`--`(27)`.

For a unit scalar amplitude `w` on a countable index set and a Hilbert space `H`, the synthesis

```text
R_w((f_d)) = sum_d conj(w d) • f_d
```

is a coisometry from the Hilbert direct sum `⊕_d H` onto `H`.  Its adjoint

```text
(R_w^* h)_d = w d • h
```

is an isometry, `R_w R_w^* = I`, and `Pi_w = R_w^* R_w` is the orthogonal projection onto the
distinguished source line tensored with the identity of `H`.  In particular

```text
||R_w f|| = ||Pi_w f|| .
```

Finally, every closed operator on `H` commutes with `R_w` on the graph-norm domain of its
channelwise amplification.
-/

open scoped BigOperators ENNReal NNReal

noncomputable section
namespace RHTower

variable {ι : Type*} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- Card `(8)`: the analysis map `h ↦ (w d • h)_d`. -/
def vectorSignedAnalysis (w : lp (fun _ : ι => ℂ) 2) (h : H) : lp (fun _ : ι => H) 2 :=
  ⟨fun d => w d • h, by
    refine (memℓp_gen_iff (by norm_num)).mpr ?_
    have hw : Summable (fun d : ι => ‖(w : ι → ℂ) d‖ ^ (2 : ℝ≥0∞).toReal) :=
      (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).mp (lp.memℓp w)
    have := hw.mul_right (‖h‖ ^ (2 : ℝ≥0∞).toReal)
    refine this.congr fun d => ?_
    rw [norm_smul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]⟩

omit [CompleteSpace H] in
theorem vectorSignedAnalysis_apply (w : lp (fun _ : ι => ℂ) 2) (h : H) (d : ι) :
    (vectorSignedAnalysis w h : ι → H) d = w d • h := rfl

theorem rpow_two_eq_sq (x : ℝ) : x ^ (2 : ℝ) = x ^ (2 : ℕ) := by
  rw [show (2 : ℝ) = ((2 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]

omit [CompleteSpace H] in
theorem norm_vectorSignedAnalysis (w : lp (fun _ : ι => ℂ) 2) (h : H) :
    ‖vectorSignedAnalysis w h‖ = ‖w‖ * ‖h‖ := by
  have h2 : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
  have hlhs := lp.norm_rpow_eq_tsum h2 (vectorSignedAnalysis w h)
  have hrhs := lp.norm_rpow_eq_tsum h2 w
  have htoReal : (2 : ℝ≥0∞).toReal = 2 := by norm_num
  rw [htoReal] at hlhs hrhs
  have hkey : ‖vectorSignedAnalysis w h‖ ^ (2 : ℝ) = (‖w‖ * ‖h‖) ^ (2 : ℝ) := by
    rw [hlhs]
    have hcongr : (∑' d : ι, ‖(vectorSignedAnalysis w h : ι → H) d‖ ^ (2 : ℝ))
        = ∑' d : ι, ‖(w : ι → ℂ) d‖ ^ (2 : ℝ) * ‖h‖ ^ (2 : ℝ) := by
      refine tsum_congr fun d => ?_
      rw [vectorSignedAnalysis_apply, norm_smul,
        Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
    rw [hcongr, tsum_mul_right, ← hrhs, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
  rw [rpow_two_eq_sq, rpow_two_eq_sq] at hkey
  have hnn1 : (0 : ℝ) ≤ ‖vectorSignedAnalysis w h‖ := norm_nonneg _
  have hnn2 : (0 : ℝ) ≤ ‖w‖ * ‖h‖ := by positivity
  nlinarith [hkey, hnn1, hnn2]

/-- Card `(5)`: the synthesis map `(f_d) ↦ ∑_d conj(w d) • f_d`. -/
def vectorSignedSynthesis (w : lp (fun _ : ι => ℂ) 2) (f : lp (fun _ : ι => H) 2) : H :=
  ∑' d : ι, (starRingEnd ℂ) ((w : ι → ℂ) d) • (f : ι → H) d

theorem summable_vectorSignedSynthesisTerm
    (w : lp (fun _ : ι => ℂ) 2) (f : lp (fun _ : ι => H) 2) :
    Summable (fun d : ι => (starRingEnd ℂ) ((w : ι → ℂ) d) • (f : ι → H) d) := by
  apply Summable.of_norm
  have hw : Summable (fun d : ι => ‖(w : ι → ℂ) d‖ ^ (2 : ℝ)) := by
    have := (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).mp (lp.memℓp w)
    simpa using this
  have hf : Summable (fun d : ι => ‖(f : ι → H) d‖ ^ (2 : ℝ)) := by
    have := (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).mp (lp.memℓp f)
    simpa using this
  refine Summable.of_nonneg_of_le (fun d => norm_nonneg _) (fun d => ?_)
    ((hw.add hf).div_const 2)
  rw [norm_smul, RCLike.norm_conj]
  have hsq : (‖(w : ι → ℂ) d‖ - ‖(f : ι → H) d‖) ^ 2 ≥ 0 := sq_nonneg _
  rw [rpow_two_eq_sq, rpow_two_eq_sq]
  nlinarith [hsq]

/-- The adjoint relation between analysis and synthesis. -/
theorem inner_vectorSignedAnalysis
    (w : lp (fun _ : ι => ℂ) 2) (h : H) (f : lp (fun _ : ι => H) 2) :
    inner ℂ (vectorSignedAnalysis w h) f = inner ℂ h (vectorSignedSynthesis w f) := by
  have hsum := lp.hasSum_inner (𝕜 := ℂ) (vectorSignedAnalysis w h) f
  have hleft : inner ℂ (vectorSignedAnalysis w h) f
      = ∑' d : ι, (starRingEnd ℂ) ((w : ι → ℂ) d) * inner ℂ h ((f : ι → H) d) := by
    rw [← hsum.tsum_eq]
    refine tsum_congr fun d => ?_
    rw [vectorSignedAnalysis_apply, inner_smul_left]
  have hright : inner ℂ h (vectorSignedSynthesis w f)
      = ∑' d : ι, (starRingEnd ℂ) ((w : ι → ℂ) d) * inner ℂ h ((f : ι → H) d) := by
    have hmap := (innerSL ℂ h).map_tsum (summable_vectorSignedSynthesisTerm w f)
    simp only [innerSL_apply_apply] at hmap
    rw [vectorSignedSynthesis, hmap]
    refine tsum_congr fun d => ?_
    rw [inner_smul_right]
  rw [hleft, hright]

/-- Card `(9)`: the synthesis is a left inverse of the analysis on a unit amplitude. -/
theorem vectorSignedSynthesis_analysis
    {w : lp (fun _ : ι => ℂ) 2} (hw : ‖w‖ = 1) (h : H) :
    vectorSignedSynthesis w (vectorSignedAnalysis w h) = h := by
  refine ext_inner_left ℂ fun x => ?_
  have h1 := inner_vectorSignedAnalysis w x (vectorSignedAnalysis w h)
  have h2 : inner ℂ (vectorSignedAnalysis w x) (vectorSignedAnalysis w h) = inner ℂ x h := by
    have hsum := lp.hasSum_inner (𝕜 := ℂ) (vectorSignedAnalysis w x) (vectorSignedAnalysis w h)
    rw [← hsum.tsum_eq]
    have hterm : ∀ d : ι,
        inner ℂ ((vectorSignedAnalysis w x : ι → H) d)
          ((vectorSignedAnalysis w h : ι → H) d)
          = (((‖(w : ι → ℂ) d‖ ^ (2 : ℕ) : ℝ)) : ℂ) * inner ℂ x h := by
      intro d
      rw [vectorSignedAnalysis_apply, vectorSignedAnalysis_apply, inner_smul_left,
        inner_smul_right, ← mul_assoc]
      congr 1
      rw [RCLike.conj_mul (K := ℂ)]
      norm_cast
    have hsummableR : Summable (fun d : ι => (‖(w : ι → ℂ) d‖ ^ (2 : ℕ) : ℝ)) := by
      have := (memℓp_gen_iff (p := (2 : ℝ≥0∞)) (by norm_num)).mp (lp.memℓp w)
      simp only [ENNReal.toReal_ofNat] at this
      exact this.congr fun d => rpow_two_eq_sq _
    have hw2 : (∑' d : ι, (‖(w : ι → ℂ) d‖ ^ (2 : ℕ) : ℝ)) = 1 := by
      have h2r : (0 : ℝ) < (2 : ℝ≥0∞).toReal := by norm_num
      have hn := lp.norm_rpow_eq_tsum h2r w
      rw [show (2 : ℝ≥0∞).toReal = 2 by norm_num, hw] at hn
      rw [show (∑' d : ι, (‖(w : ι → ℂ) d‖ ^ (2 : ℕ) : ℝ))
          = ∑' d : ι, (‖(w : ι → ℂ) d‖ ^ (2 : ℝ)) from
        tsum_congr fun d => (rpow_two_eq_sq _).symm, ← hn]
      norm_num
    have hcast := Complex.ofRealCLM.map_tsum hsummableR
    simp only [Complex.ofRealCLM_apply] at hcast
    rw [tsum_congr hterm, tsum_mul_right, ← hcast, hw2]
    simp
  rw [← h1, h2]

/-- Card `(7)`: the synthesis is a contraction. -/
theorem norm_vectorSignedSynthesis_le
    (w : lp (fun _ : ι => ℂ) 2) (f : lp (fun _ : ι => H) 2) :
    ‖vectorSignedSynthesis w f‖ ≤ ‖w‖ * ‖f‖ := by
  set y : H := vectorSignedSynthesis w f with hy
  rcases eq_or_ne y 0 with h0 | h0
  · rw [h0, norm_zero]
    positivity
  · have hpos : 0 < ‖y‖ := norm_pos_iff.mpr h0
    have hkey : (‖y‖ : ℝ) ^ 2 = (inner ℂ (vectorSignedAnalysis w y) f).re := by
      rw [inner_vectorSignedAnalysis w y f, ← hy, inner_self_eq_norm_sq_to_K]
      norm_cast
    have hbound : (inner ℂ (vectorSignedAnalysis w y) f).re
        ≤ ‖vectorSignedAnalysis w y‖ * ‖f‖ := by
      calc (inner ℂ (vectorSignedAnalysis w y) f).re
          ≤ ‖inner ℂ (vectorSignedAnalysis w y) f‖ := Complex.re_le_norm _
        _ ≤ ‖vectorSignedAnalysis w y‖ * ‖f‖ := norm_inner_le_norm _ _
    rw [norm_vectorSignedAnalysis] at hbound
    nlinarith [hkey, hbound, hpos]

/-- Card `(10)`: the channel projection. -/
def vectorSignedProjection (w : lp (fun _ : ι => ℂ) 2) (f : lp (fun _ : ι => H) 2) :
    lp (fun _ : ι => H) 2 :=
  vectorSignedAnalysis w (vectorSignedSynthesis w f)

theorem vectorSignedProjection_idempotent
    {w : lp (fun _ : ι => ℂ) 2} (hw : ‖w‖ = 1) (f : lp (fun _ : ι => H) 2) :
    vectorSignedProjection w (vectorSignedProjection w f) = vectorSignedProjection w f := by
  rw [vectorSignedProjection, vectorSignedProjection, vectorSignedSynthesis_analysis hw]

theorem vectorSignedProjection_selfAdjoint
    (w : lp (fun _ : ι => ℂ) 2) (f g : lp (fun _ : ι => H) 2) :
    inner ℂ (vectorSignedProjection w f) g = inner ℂ f (vectorSignedProjection w g) := by
  have h1 : inner ℂ (vectorSignedProjection w f) g
      = inner ℂ (vectorSignedSynthesis w f) (vectorSignedSynthesis w g) := by
    rw [vectorSignedProjection, inner_vectorSignedAnalysis]
  have h2 : inner ℂ f (vectorSignedProjection w g)
      = inner ℂ (vectorSignedSynthesis w f) (vectorSignedSynthesis w g) := by
    have hbase : inner ℂ (vectorSignedProjection w g) f
        = inner ℂ (vectorSignedSynthesis w g) (vectorSignedSynthesis w f) := by
      rw [vectorSignedProjection, inner_vectorSignedAnalysis]
    calc inner ℂ f (vectorSignedProjection w g)
        = (starRingEnd ℂ) (inner ℂ (vectorSignedProjection w g) f) := by
          rw [inner_conj_symm]
      _ = (starRingEnd ℂ) (inner ℂ (vectorSignedSynthesis w g) (vectorSignedSynthesis w f)) := by
          rw [hbase]
      _ = inner ℂ (vectorSignedSynthesis w f) (vectorSignedSynthesis w g) := inner_conj_symm _ _
  rw [h1, h2]

omit [CompleteSpace H] in
/-- Card `(22)`: the synthesis norm is the norm of the projected component. -/
theorem norm_vectorSignedSynthesis_eq_norm_projection
    {w : lp (fun _ : ι => ℂ) 2} (hw : ‖w‖ = 1) (f : lp (fun _ : ι => H) 2) :
    ‖vectorSignedSynthesis w f‖ = ‖vectorSignedProjection w f‖ := by
  rw [vectorSignedProjection, norm_vectorSignedAnalysis, hw, one_mul]


/-! ### Card `(25)`--`(27)`: closed-operator channel commutation -/

/-- **Card `(27)`.**  Every closed operator on `H` preserves the range of the signed synthesis on
the graph-norm domain of its channelwise amplification, and commutes with the synthesis there. -/
theorem vectorSignedSynthesis_closedOperator
    (w : lp (fun _ : ι => ℂ) 2) (G : H →ₗ.[ℂ] H)
    (hG : IsClosed (G.graph : Set (H × H)))
    (f g : lp (fun _ : ι => H) 2)
    (hdom : ∀ d : ι, (f : ι → H) d ∈ G.domain)
    (hval : ∀ d : ι, G ⟨(f : ι → H) d, hdom d⟩ = (g : ι → H) d) :
    ∃ hmem : vectorSignedSynthesis w f ∈ G.domain,
      G ⟨vectorSignedSynthesis w f, hmem⟩ = vectorSignedSynthesis w g := by
  have hfsum : HasSum (fun d : ι => (starRingEnd ℂ) ((w : ι → ℂ) d) • (f : ι → H) d)
      (vectorSignedSynthesis w f) :=
    (summable_vectorSignedSynthesisTerm w f).hasSum
  have hgsum : HasSum (fun d : ι => (starRingEnd ℂ) ((w : ι → ℂ) d) • (g : ι → H) d)
      (vectorSignedSynthesis w g) :=
    (summable_vectorSignedSynthesisTerm w g).hasSum
  have hpair := hfsum.prodMk hgsum
  have hmemF : ∀ F : Finset ι,
      (∑ d ∈ F, ((starRingEnd ℂ) ((w : ι → ℂ) d) • (f : ι → H) d,
        (starRingEnd ℂ) ((w : ι → ℂ) d) • (g : ι → H) d)) ∈ G.graph := by
    intro F
    refine Submodule.sum_mem _ fun d _ => ?_
    have hbase : ((f : ι → H) d, (g : ι → H) d) ∈ G.graph := by
      have hmg := G.mem_graph ⟨(f : ι → H) d, hdom d⟩
      rw [hval d] at hmg
      exact hmg
    exact G.graph.smul_mem _ hbase
  have hlimit : (vectorSignedSynthesis w f, vectorSignedSynthesis w g) ∈ G.graph :=
    hG.mem_of_tendsto hpair (Filter.Eventually.of_forall hmemF)
  obtain ⟨y, hy1, hy2⟩ := (LinearPMap.mem_graph_iff G).mp hlimit
  simp only at hy1 hy2
  have hmem : vectorSignedSynthesis w f ∈ G.domain := by
    rw [← hy1]
    exact y.2
  refine ⟨hmem, ?_⟩
  have hyeq : (⟨vectorSignedSynthesis w f, hmem⟩ : G.domain) = y := Subtype.ext hy1.symm
  rw [hyeq, hy2]

end RHTower
