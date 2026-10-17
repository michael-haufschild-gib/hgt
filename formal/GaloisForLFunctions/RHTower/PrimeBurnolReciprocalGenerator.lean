import GaloisForLFunctions.RHTower.PrimeBurnolAccretiveGenerator

/-! # Bounded prime readings with an actual unbounded generator -/

open Complex Set Filter Topology
noncomputable section
namespace RHTower
open GaloisForLFunctions.HTGeometry _root_.HTGeometry

def burnolReciprocalSymbol : BurnolAccretiveSymbol where
  toFun z := z⁻¹
  analytic z hz := analyticAt_id.inv (by
    intro h
    change z = 0 at h
    have : z.re = 0 := by rw [h]; rfl
    exact (ne_of_gt hz) this)
  nonneg z hz := by
    rw [Complex.inv_re]
    exact div_nonneg (le_of_lt hz) (Complex.normSq_nonneg z)

/-- Every literal prime eigenvalue is bounded by the same explicit constant. -/
theorem burnolReciprocalSymbol_prime_bound (p : Nat.Primes) :
    ‖burnolReciprocalSymbol (Real.log (p : ℝ))‖ ≤ (Real.log 2)⁻¹ := by
  change ‖((Real.log (p : ℝ) : ℝ) : ℂ)⁻¹‖ ≤ _
  rw [norm_inv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (Real.log_pos (by exact_mod_cast p.property.one_lt))]
  simpa only [one_div] using one_div_le_one_div_of_le
    (Real.log_pos (by norm_num : (1 : ℝ) < 2))
    (Real.log_le_log (by norm_num : (0 : ℝ) < 2) (by exact_mod_cast p.property.two_le))

/-- The closed prime graph violates every finite operator bound. -/
theorem burnolReciprocalSymbol_graph_unbounded {B : ℝ} (hB : 0 ≤ B) :
    ∃ u v : BurnolHalfLineL2, (u,v) ∈ burnolReciprocalSymbol.graph ∧ B*‖u‖ < ‖v‖ := by
  let z : ℂ := ((B+1)⁻¹ : ℝ)
  have hz : 0 < z.re := inv_pos.mpr (by linarith)
  let u := burnolComplexFeature z hz
  let v := -burnolReciprocalSymbol z • u
  refine ⟨u,v,burnolReciprocalSymbol.graph_feature z hz,?_⟩
  have hv : burnolReciprocalSymbol z = ((B+1 : ℝ) : ℂ) := by
    change (((B+1)⁻¹ : ℝ) : ℂ)⁻¹ = _
    rw [← Complex.ofReal_inv, inv_inv]
  have hu : 0 < ‖u‖ := norm_pos_iff.mpr (burnolComplexFeature_ne_zero hz)
  change B*‖u‖ < ‖-burnolReciprocalSymbol z • u‖
  rw [norm_smul, norm_neg, hv, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (by linarith : 0 < B+1)]
  nlinarith

/-- No bounded operator can even extend all the specified literal prime actions. -/
theorem burnolReciprocalSymbol_no_bounded_prime_extension :
    ¬ ∃ A : BurnolHalfLineL2 →L[ℂ] BurnolHalfLineL2, ∀ p : Nat.Primes,
      A (primeLogCriticalLaplaceFeatureL2 p) =
        -burnolReciprocalSymbol (Real.log (p : ℝ)) • primeLogCriticalLaplaceFeatureL2 p := by
  rintro ⟨A,hA⟩
  let L : (BurnolHalfLineL2 × BurnolHalfLineL2) →L[ℂ] BurnolHalfLineL2 :=
    A.comp (ContinuousLinearMap.fst ℂ _ _) - ContinuousLinearMap.snd ℂ _ _
  have hs : burnolReciprocalSymbol.primeGraphSpan ≤ L.toLinearMap.ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨p,rfl⟩
    change A (primeLogCriticalLaplaceFeatureL2 p) -
      -burnolReciprocalSymbol (Real.log (p : ℝ)) • primeLogCriticalLaplaceFeatureL2 p = 0
    rw [hA, sub_self]
  have hg : burnolReciprocalSymbol.graph ≤ L.toLinearMap.ker :=
    burnolReciprocalSymbol.primeGraphSpan.topologicalClosure_minimal hs L.isClosed_ker
  obtain ⟨u,v,huv,hbound⟩ := burnolReciprocalSymbol_graph_unbounded (norm_nonneg A)
  have he := hg huv
  change A u-v = 0 at he
  rw [← sub_eq_zero.mp he] at hbound
  exact (not_lt_of_ge (A.le_opNorm u)) hbound

end RHTower
