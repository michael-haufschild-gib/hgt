import GaloisForLFunctions.RHTower.PrimeLogCubicLaplaceGraphFormation

/-!
# Literal profiles on the closed critical prime-log graph

Positive-time source evaluation identifies every closed-graph output almost
everywhere. The profile uses the actual prime coefficient Hilbert space;
no choice of an output representative enters its definition.
-/

noncomputable section
open MeasureTheory Set Filter Topology

namespace RHTower

def primeLogCriticalLaplaceProfile (a : primeLogCriticalSourceL2) (t : ℝ) : ℂ :=
  if ht : 0 < t then inner ℂ (primeLogCriticalEvaluationVector t ht) a else 0

theorem primeLogCriticalLaplaceProfile_pos (a : primeLogCriticalSourceL2)
    {t : ℝ} (ht : 0 < t) :
    primeLogCriticalLaplaceProfile a t =
      inner ℂ (primeLogCriticalEvaluationVector t ht) a := dif_pos ht

theorem continuous_primeLogCriticalLaplaceProfile_source (t : ℝ) :
    Continuous (fun a : primeLogCriticalSourceL2 => primeLogCriticalLaplaceProfile a t) := by
  by_cases ht : 0 < t
  · simp only [primeLogCriticalLaplaceProfile, dif_pos ht]
    exact continuous_const.inner continuous_id
  · simp only [primeLogCriticalLaplaceProfile, dif_neg ht]
    exact continuous_const

theorem primeLogCriticalLaplaceProfile_tsum (a : primeLogCriticalSourceL2)
    {t : ℝ} (ht : 0 < t) :
    primeLogCriticalLaplaceProfile a t =
      ∑' p : Nat.Primes, a p * primeLogCriticalLaplaceFeatureC p t := by
  rw [primeLogCriticalLaplaceProfile_pos _ ht, lp.inner_eq_tsum]
  apply tsum_congr
  intro p
  simp [primeLogCriticalEvaluationVector, RCLike.inner_apply,
    primeLogCriticalLaplaceFeatureC, mul_comm]

theorem primeLogCriticalLaplaceProfile_finite (l : Nat.Primes →₀ ℂ)
    {t : ℝ} (ht : 0 < t) :
    primeLogCriticalLaplaceProfile (HTGeometry.ConstraintMotiveRelativity.srcEmb l) t =
      ∑ p ∈ l.support, l p * primeLogCriticalLaplaceFeatureC p t := by
  rw [primeLogCriticalLaplaceProfile_pos _ ht,
    primeLogCriticalLaplaceMass_pointwise_eq_inner]

theorem primeLogCriticalLaplaceSynthesis_profile_ae
    (x : primeLogCriticalLaplaceSynthesis.domain) :
    (primeLogCriticalLaplaceSynthesis x : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))]
      primeLogCriticalLaplaceProfile x := by
  filter_upwards [primeLogCriticalLaplaceSynthesis_ae x,
    ae_restrict_mem measurableSet_Ioi] with t ht hpos
  rw [ht, primeLogCriticalLaplaceProfile_pos _ hpos,
    primeLogCriticalLaplaceMass_pointwise_eq_inner, srcEmb_primeLogCriticalLaplaceCore]

theorem primeLogCriticalLaplaceProfile_of_graph_tendsto
    (x : ℕ → primeLogCriticalLaplaceSynthesis.domain)
    (a : primeLogCriticalSourceL2) (y : primeLogCriticalHalfLineL2)
    (hx : Tendsto (fun n => (x n : primeLogCriticalSourceL2)) atTop (𝓝 a))
    (hy : Tendsto (fun n => primeLogCriticalLaplaceSynthesis (x n)) atTop (𝓝 y)) :
    (y : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] primeLogCriticalLaplaceProfile a := by
  obtain ⟨ns, hns, hyAE⟩ := GaloisForLFunctions.HTGeometry.exists_subseq_ae_tendsto hy
  have hprofiles : ∀ᵐ t : ℝ ∂(volume.restrict (Ioi (0 : ℝ))), ∀ i : ℕ,
      (primeLogCriticalLaplaceSynthesis (x (ns i)) : ℝ → ℂ) t =
        primeLogCriticalLaplaceProfile (x (ns i)) t := by
    rw [ae_all_iff]
    exact fun i => primeLogCriticalLaplaceSynthesis_profile_ae (x (ns i))
  filter_upwards [hyAE, hprofiles] with t hyt hpt
  have hp := ((continuous_primeLogCriticalLaplaceProfile_source t).tendsto a).comp
    (hx.comp hns.tendsto_atTop)
  have hactual : Tendsto
      (fun i => (primeLogCriticalLaplaceSynthesis (x (ns i)) : ℝ → ℂ) t)
      atTop (𝓝 (primeLogCriticalLaplaceProfile a t)) := by
    apply hp.congr'
    exact Eventually.of_forall fun i => (hpt i).symm
  exact tendsto_nhds_unique hyt hactual

theorem primeLogCriticalLaplaceClosureGraph_ae
    {a : primeLogCriticalSourceL2} {y : primeLogCriticalHalfLineL2}
    (h : (a, y) ∈ primeLogCriticalLaplaceSynthesis.closure.graph) :
    (y : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] primeLogCriticalLaplaceProfile a := by
  rw [← primeLogCriticalLaplaceSynthesis_isClosable.graph_closure_eq_closure_graph] at h
  obtain ⟨w, hwG, hw⟩ := mem_closure_iff_seq_limit.mp h
  have hdom : ∀ n, (w n).fst ∈ primeLogCriticalLaplaceSynthesis.domain :=
    fun n => LinearPMap.mem_domain_of_mem_graph (hwG n)
  let x : ℕ → primeLogCriticalLaplaceSynthesis.domain := fun n => ⟨(w n).fst, hdom n⟩
  have happ : ∀ n, primeLogCriticalLaplaceSynthesis (x n) = (w n).snd := by
    intro n
    obtain ⟨v, hv1, hv2⟩ := primeLogCriticalLaplaceSynthesis.mem_graph_iff.mp (hwG n)
    have hxv : x n = v := Subtype.ext hv1.symm
    rw [hxv]
    exact hv2
  apply primeLogCriticalLaplaceProfile_of_graph_tendsto x a y
  · exact (continuous_fst.tendsto (a, y)).comp hw
  · simpa only [happ, Function.comp_def] using (continuous_snd.tendsto (a, y)).comp hw

theorem primeLogCriticalLaplaceClosureGraph_memLp
    {a : primeLogCriticalSourceL2} {y : primeLogCriticalHalfLineL2}
    (h : (a, y) ∈ primeLogCriticalLaplaceSynthesis.closure.graph) :
    MemLp (primeLogCriticalLaplaceProfile a) 2 (volume.restrict (Ioi (0 : ℝ))) :=
  MemLp.ae_eq (primeLogCriticalLaplaceClosureGraph_ae h) (Lp.memLp y)

end RHTower
