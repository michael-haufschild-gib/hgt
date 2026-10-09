import GaloisForLFunctions.HTGeometry.MonicCoefficientRootCovering
import GaloisForLFunctions.HTGeometry.ParametricRootBaseChange
import GaloisForLFunctions.Bottcher.BranchContinuation
import GaloisForLFunctions.Bottcher.ProperLocalHomeoCovering
import Mathlib.Topology.Homotopy.Lifting

open Polynomial Set Topology
open scoped BigOperators
namespace GaloisForLFunctions.HTGeometry
noncomputable section

theorem monic_monicCoeffPolynomial (d : ℕ) (c : Fin d → ℂ) :
    (monicCoeffPolynomial d c).Monic :=
  monic_X_pow_add (degree_sum_fin_lt c)

@[simp] theorem natDegree_monicCoeffPolynomial (d : ℕ) (c : Fin d → ℂ) :
    (monicCoeffPolynomial d c).natDegree = d := by
  unfold monicCoeffPolynomial
  rw [natDegree_add_eq_left_of_degree_lt, natDegree_X_pow]
  simpa only [degree_X_pow] using degree_sum_fin_lt c

/-- Recover a monic polynomial from its complete lower-coefficient vector. -/
theorem monicCoeffPolynomial_coeff_of_monic (p : ℂ[X]) (hp : p.Monic) :
    monicCoeffPolynomial p.natDegree (fun i => p.coeff i) = p := by
  apply Polynomial.funext
  intro z
  rw [← monicCoeffRelation_eq_eval p.natDegree ((fun i => p.coeff i), z), Polynomial.eval_eq_sum_range,
    Finset.sum_range_succ, hp.coeff_natDegree]
  simp only [monicCoeffRelation, one_mul]
  rw [Fin.sum_univ_eq_sum_range (fun i => p.coeff i * z ^ i) p.natDegree]
  ac_rfl

theorem continuous_coeff_monicCoeffPolynomial {X : Type*} [TopologicalSpace X]
    {d : ℕ} {c : X → (Fin d → ℂ)} (hc : Continuous c) (k : ℕ) :
    Continuous fun x => (monicCoeffPolynomial d (c x)).coeff k := by
  simp only [monicCoeffPolynomial, coeff_add, finsetSum_coeff, coeff_C_mul]
  fun_prop

/-- The direct root locus of a continuous monic family over a compact base is compact. -/
theorem isCompact_monicRootBaseChange {X : Type*} [TopologicalSpace X] [CompactSpace X]
    {d : ℕ} (hd : 0 < d) {c : X → (Fin d → ℂ)} (hc : Continuous c) :
    IsCompact (ParametricRootBaseChange (monicCoeffRelation d) c) := by
  let bound : X → ℝ := fun x => max 1
    (∑ k ∈ Finset.range d, ‖(monicCoeffPolynomial d (c x)).coeff k‖)
  have hb : Continuous bound := continuous_const.max
    (continuous_finsetSum _ fun k _ => (continuous_coeff_monicCoeffPolynomial hc k).norm)
  obtain ⟨R, hR⟩ := (isCompact_range hb).bddAbove
  have hrel : Continuous fun q : X × ℂ => monicCoeffRelation d (c q.1, q.2) := by
    have hr : Continuous (monicCoeffRelation d) :=
      continuous_iff_continuousAt.mpr fun q => (analyticAt_monicCoeffRelation d q).continuousAt
    exact hr.comp ((hc.comp continuous_fst).prodMk continuous_snd)
  have hclosed : IsClosed (ParametricRootBaseChange (monicCoeffRelation d) c) :=
    isClosed_eq hrel continuous_const
  apply (isCompact_univ.prod (isCompact_closedBall (0 : ℂ) R)).of_isClosed_subset hclosed
  intro q hq
  refine ⟨Set.mem_univ _, ?_⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  have hz : (monicCoeffPolynomial d (c q.1)).eval q.2 = 0 := by
    rw [← monicCoeffRelation_eq_eval d (c q.1, q.2)]
    exact hq
  have hn := Bottcher.norm_root_le_of_monic (monic_monicCoeffPolynomial d (c q.1)) hz
    (by simpa only [natDegree_monicCoeffPolynomial] using hd)
  rw [natDegree_monicCoeffPolynomial] at hn
  exact hn.trans (hR ⟨q.1, rfl⟩)

/-- Proper projection for a continuous monic family over a compact Hausdorff base. -/
theorem isProperMap_monicRootBaseChangeProj {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] {d : ℕ} (hd : 0 < d)
    {c : X → (Fin d → ℂ)} (hc : Continuous c) :
    IsProperMap (parametricRootBaseChangeProj (f := monicCoeffRelation d) (c := c)) := by
  letI : CompactSpace (ParametricRootBaseChange (monicCoeffRelation d) c) :=
    isCompact_iff_compactSpace.mp (isCompact_monicRootBaseChange hd hc)
  exact (continuous_fst.comp continuous_subtype_val).isProperMap

/-- Simple roots give a covering for every continuous monic family over a compact base. -/
theorem isCoveringMap_monicRootBaseChangeProj {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] {d : ℕ} (hd : 0 < d)
    {c : X → (Fin d → ℂ)} (hc : Continuous c)
    (hsimple : ∀ x z, (monicCoeffPolynomial d (c x)).eval z = 0 →
      (monicCoeffPolynomial d (c x)).derivative.eval z ≠ 0) :
    IsCoveringMap (parametricRootBaseChangeProj (f := monicCoeffRelation d) (c := c)) := by
  apply isCoveringMap_of_isProperMap_of_isLocalHomeomorph
    (hprop := isProperMap_monicRootBaseChangeProj hd hc)
  apply isLocalHomeomorph_parametricRootBaseChangeProj hc
    (fun x z => analyticAt_monicCoeffRelation d (c x, z))
  intro x z hz
  rw [monicCoeffRelation_partial_snd]
  exact hsimple x z ((monicCoeffRelation_eq_eval d (c x, z)) ▸ hz)

/-- Every selected root extends uniquely across a compact simply connected parameter space. -/
theorem existsUnique_monic_root_section {X : Type*} [TopologicalSpace X]
    [CompactSpace X] [T2Space X] [SimplyConnectedSpace X] [LocallyPathConnectedSpace X]
    {d : ℕ} (hd : 0 < d) {c : X → (Fin d → ℂ)} (hc : Continuous c)
    (hsimple : ∀ x z, (monicCoeffPolynomial d (c x)).eval z = 0 →
      (monicCoeffPolynomial d (c x)).derivative.eval z ≠ 0)
    (x₀ : X) (z₀ : ℂ) (hz₀ : (monicCoeffPolynomial d (c x₀)).eval z₀ = 0) :
    ∃! z : C(X, ℂ), z x₀ = z₀ ∧ ∀ x, (monicCoeffPolynomial d (c x)).eval (z x) = 0 := by
  let E := ParametricRootBaseChange (monicCoeffRelation d) c
  let e₀ : E := ⟨(x₀, z₀), by
    change monicCoeffRelation d (c x₀, z₀) = 0
    rwa [monicCoeffRelation_eq_eval]⟩
  let cov := isCoveringMap_monicRootBaseChangeProj hd hc hsimple
  obtain ⟨L, ⟨hL₀, hL⟩, huniq⟩ := cov.existsUnique_continuousMap_lifts
    (ContinuousMap.id X) x₀ e₀ rfl
  have hfirst (x : X) : (L x).val.1 = x := congr_fun hL x
  let z : C(X, ℂ) := ⟨fun x => (L x).val.2,
    continuous_snd.comp (continuous_subtype_val.comp L.continuous)⟩
  have hz (x : X) : (monicCoeffPolynomial d (c x)).eval (z x) = 0 := by
    have h := (L x).property
    change monicCoeffRelation d (c (L x).val.1, (L x).val.2) = 0 at h
    rw [hfirst, monicCoeffRelation_eq_eval] at h
    exact h
  refine ⟨z, ⟨?_, hz⟩, ?_⟩
  · exact congrArg (fun e : E => e.val.2) hL₀
  · intro w hw
    have hW (x : X) : (x, w x) ∈ E := by
      change monicCoeffRelation d (c x, w x) = 0
      rw [monicCoeffRelation_eq_eval]
      exact hw.2 x
    let W : C(X, E) := ⟨fun x => ⟨(x, w x), hW x⟩,
      (continuous_id.prodMk w.continuous).subtype_mk hW⟩
    have hWeq : W = L := huniq W ⟨by apply Subtype.ext; exact Prod.ext rfl hw.1, rfl⟩
    ext x
    exact congrArg (fun F : C(X, E) => (F x).val.2) hWeq

end
end GaloisForLFunctions.HTGeometry
