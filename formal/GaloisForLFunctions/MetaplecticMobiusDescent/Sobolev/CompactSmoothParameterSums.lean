/-
Compact smooth parameter families adapted from OpenAI's formalization,
Apache-2.0. See LICENSE and NOTICE for source attribution.
-/
import Mathlib.Analysis.Calculus.SmoothSeries
import Mathlib.Analysis.Complex.Basic

/-!
# Smooth sums from compact parameter families

Joint smoothness bounds every partial derivative uniformly on compact
parameter and support sets. An absolutely summable scalar coefficient
sequence then permits a smooth sum of arbitrary sampled family members.
-/
set_option autoImplicit false
noncomputable section
open Filter
open scoped BigOperators Classical Topology ContDiff
namespace GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein

section PartialDerivatives
variable {A E G : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]

/-- Spatial derivatives remain jointly smooth in the parameter and position. -/
lemma partial_iteratedFDeriv_contDiffAt (F : A→E→G) (a : A) (x : E)
    (hF : ContDiffAt ℝ ∞ (Function.uncurry F) (a,x)) (k : ℕ) :
    ContDiffAt ℝ ∞ (fun p : A×E => iteratedFDeriv ℝ k (F p.1) p.2) (a,x) := by
  induction k with
  | zero =>
    exact hF.continuousLinearMap_comp
      ((continuousMultilinearCurryFin0 ℝ E G).symm : G→L[ℝ] E [×0]→L[ℝ]G)
  | succ k ih =>
    have hpair : ContDiffAt ℝ ∞
        (fun p : (A×E)×E => (p.1.1,p.2)) ((a,x),x) :=
      (contDiffAt_fst.fst).prodMk contDiffAt_snd
    have hp := ih.comp ((a,x),x) hpair
    have hd : ContDiffAt ℝ ∞
        (fun p : A×E => fderiv ℝ (fun y => iteratedFDeriv ℝ k (F p.1) y) p.2) (a,x) :=
      hp.fderiv contDiffAt_snd (by simp)
    exact hd.continuousLinearMap_comp
      ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k+1) => E) G).symm :
        (E→L[ℝ] E [×k]→L[ℝ]G)→L[ℝ] E [×(k+1)]→L[ℝ]G)

/-- Compact parameter and support sets bound every spatial derivative uniformly. -/
lemma compact_family_derivative_bound (F : A→E→G)
    (K : Set A) (P : Set E) (hK : IsCompact K) (hP : IsCompact P)
    (hF : ∀a∈K,∀x,ContDiffAt ℝ ∞ (Function.uncurry F) (a,x))
    (hsupp : ∀a∈K,tsupport (F a)⊆P) (k : ℕ) :
    ∃C : ℝ,0≤C ∧ ∀a∈K,∀x,‖iteratedFDeriv ℝ k (F a) x‖≤C := by
  have hc : ContinuousOn (fun p : A×E => iteratedFDeriv ℝ k (F p.1) p.2) (K×ˢP) := by
    intro p hp
    exact (partial_iteratedFDeriv_contDiffAt F p.1 p.2 (hF p.1 hp.1 p.2) k).continuousAt.continuousWithinAt
  obtain ⟨C,hC⟩ := (hK.prod hP).bddAbove_image hc.norm
  refine ⟨max C 0,le_max_right _ _,?_⟩
  intro a ha x
  by_cases hx : x∈P
  · exact (hC ⟨(a,x),⟨ha,hx⟩,rfl⟩).trans (le_max_left _ _)
  · have hz : iteratedFDeriv ℝ k (F a) x=0 := by
      by_contra hn
      exact hx (hsupp a ha (support_iteratedFDeriv_subset k hn))
    rw [hz,norm_zero]
    exact le_max_right _ _

end PartialDerivatives
section

variable {A E ι : Type*}
  [NormedAddCommGroup A] [NormedSpace ℝ A]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma compact_smooth_family_bounds (F : A→E→ℂ)
    (K : Set A) (P : Set E) (hK : IsCompact K) (hP : IsCompact P)
    (hF : ∀a∈K,∀x,ContDiffAt ℝ ∞ (Function.uncurry F) (a,x))
    (hsupp : ∀a∈K,tsupport (F a)⊆P)
    (a : ι→A) (ha : ∀i,a i∈K) (b : ι→ℂ) (hb : Summable (fun i => ‖b i‖)) :
    ∃v : ℕ → ι → ℝ,
      (∀i, ContDiff ℝ ∞ (fun x => b i*F (a i) x)) ∧
      (∀k, Summable (v k)) ∧
      ∀k i x, ‖iteratedFDeriv ℝ k (fun x => b i*F (a i) x) x‖ ≤ v k i := by
  choose C hC hbound using compact_family_derivative_bound F K P hK hP hF hsupp
  have hf (i : ι) : ContDiff ℝ ∞ (F (a i)) := by
    apply contDiff_iff_contDiffAt.mpr
    intro x
    exact (hF (a i) (ha i) x).comp x (contDiffAt_const.prodMk contDiffAt_id)
  have hprod (i : ι) : ContDiff ℝ ∞ (fun x => b i*F (a i) x) :=
    contDiff_const.mul (hf i)
  refine ⟨fun k i => ‖b i‖*C k,hprod,fun k => hb.mul_right (C k),?_⟩
  intro k i x
  have hfk : ContDiffAt ℝ (k : ℕ∞ω) (F (a i)) x :=
    (hf i).contDiffAt.of_le (by exact_mod_cast (le_top : (k : ℕ∞) ≤ ⊤))
  have he : iteratedFDeriv ℝ k (fun x => b i*F (a i) x) x=
      b i • iteratedFDeriv ℝ k (F (a i)) x :=
    by simpa only [smul_eq_mul] using
      (iteratedFDeriv_const_smul_apply' (𝕜 := ℝ) (a := b i) (i := k) (x := x) hfk)
  rw [he,norm_smul]
  exact mul_le_mul_of_nonneg_left (hbound k (a i) (ha i) x) (norm_nonneg _)

theorem compact_smooth_family_tsum (F : A→E→ℂ)
    (K : Set A) (P : Set E) (hK : IsCompact K) (hP : IsCompact P)
    (hF : ∀a∈K,∀x,ContDiffAt ℝ ∞ (Function.uncurry F) (a,x))
    (hsupp : ∀a∈K,tsupport (F a)⊆P)
    (a : ι→A) (ha : ∀i,a i∈K) (b : ι→ℂ) (hb : Summable (fun i => ‖b i‖)) :
    ContDiff ℝ ∞ (fun x => ∑'i,b i*F (a i) x) := by
  obtain ⟨v,hf,hv,hbound⟩ := compact_smooth_family_bounds F K P hK hP hF hsupp a ha b hb
  exact contDiff_tsum hf (fun k _ => hv k) (fun k i x _ => hbound k i x)

/-- Every iterated derivative commutes with the same absolutely weighted family sum. -/
theorem compact_smooth_family_iteratedFDeriv_tsum (F : A→E→ℂ)
    (K : Set A) (P : Set E) (hK : IsCompact K) (hP : IsCompact P)
    (hF : ∀a∈K,∀x,ContDiffAt ℝ ∞ (Function.uncurry F) (a,x))
    (hsupp : ∀a∈K,tsupport (F a)⊆P)
    (a : ι→A) (ha : ∀i,a i∈K) (b : ι→ℂ) (hb : Summable (fun i => ‖b i‖))
    (k : ℕ) (x : E) :
    Summable (fun i => iteratedFDeriv ℝ k (fun y => b i*F (a i) y) x) ∧
    iteratedFDeriv ℝ k (fun y => ∑'i,b i*F (a i) y) x =
      ∑'i,iteratedFDeriv ℝ k (fun y => b i*F (a i) y) x := by
  obtain ⟨v,hf,hv,hbound⟩ := compact_smooth_family_bounds F K P hK hP hF hsupp a ha b hb
  exact ⟨Summable.of_norm_bounded (hv k) (fun i => hbound k i x),
    iteratedFDeriv_tsum_apply hf (fun k _ => hv k) (fun k i x _ => hbound k i x) (by simp) x⟩


end


#print axioms compact_smooth_family_tsum
#print axioms compact_smooth_family_iteratedFDeriv_tsum
end GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein
