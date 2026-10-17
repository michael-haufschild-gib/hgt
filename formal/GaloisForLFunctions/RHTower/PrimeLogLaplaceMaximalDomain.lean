import GaloisForLFunctions.RHTower.PrimeLogLaplaceClosedGraphLiteral
import GaloisForLFunctions.RHTower.PrimeLogLaplaceDamping
import GaloisForLFunctions.HTGeometry.BurnolWeightedShiftStrongContinuity

/-!
# The maximal literal domain of critical prime-log Laplace synthesis

Prime damping intertwines with the Burnol weighted shift. Positive damping
admits every square-summable source, and both actions tend strongly to the
identity. Consequently the finite-prime graph closes to exactly the maximal
literal L² profile domain, with no extra condition at time zero.
-/

noncomputable section
open MeasureTheory Set Filter Topology
open scoped NNReal
open GaloisForLFunctions.HTGeometry

namespace RHTower

theorem primeLogCriticalLaplaceFeature_damping_shift
    (p : Nat.Primes) (h : ℝ≥0) {t : ℝ} (ht : 0 < t) :
    (p : ℝ) ^ (-(h : ℝ)) * primeLogCriticalLaplaceFeature p t =
      t / (t + h) * primeLogCriticalLaplaceFeature p (t + h) := by
  have hp : (0 : ℝ) < (p : ℝ) := by exact_mod_cast p.property.pos
  have hth : t + (h : ℝ) ≠ 0 := ne_of_gt (add_pos_of_pos_of_nonneg ht h.coe_nonneg)
  rw [Real.rpow_def_of_pos hp]
  unfold primeLogCriticalLaplaceFeature
  rw [show -(Real.log (p : ℝ) * (t + h)) =
      Real.log (p : ℝ) * (-(h : ℝ)) + -(Real.log (p : ℝ) * t) by ring, Real.exp_add]
  field_simp [hth, ne_of_gt (Real.sqrt_pos.2 hp)]
  <;> ring

theorem primeLogCriticalLaplaceProfile_damping
    (h : ℝ≥0) (a : primeLogCriticalSourceL2) {t : ℝ} (ht : 0 < t) :
    primeLogCriticalLaplaceProfile (primeLogLaplaceDamping h a) t =
      ((t / (t + h) : ℝ) : ℂ) * primeLogCriticalLaplaceProfile a (t + h) := by
  have hth : 0 < t + (h : ℝ) := add_pos_of_pos_of_nonneg ht h.coe_nonneg
  rw [primeLogCriticalLaplaceProfile_tsum _ ht,
    primeLogCriticalLaplaceProfile_tsum _ hth, ← tsum_mul_left]
  apply tsum_congr
  intro p
  rw [primeLogLaplaceDamping_apply]
  have hp := congrArg (fun x : ℝ => (x : ℂ)) (primeLogCriticalLaplaceFeature_damping_shift p h ht)
  simp only [Complex.ofReal_mul] at hp
  change primeLogLaplaceDampingWeight h p * a p * (primeLogCriticalLaplaceFeature p t : ℂ) =
    ((t / (t + h) : ℝ) : ℂ) * (a p * (primeLogCriticalLaplaceFeature p (t + h) : ℂ))
  unfold primeLogLaplaceDampingWeight
  calc
    _ = a p * (((p : ℝ) ^ (-(h : ℝ)) : ℝ) : ℂ) * (primeLogCriticalLaplaceFeature p t : ℂ) := by ring
    _ = a p * (((t / (t + h) : ℝ) : ℂ) * (primeLogCriticalLaplaceFeature p (t + h) : ℂ)) := by
      rw [mul_assoc, hp]
    _ = _ := by ring

theorem primeLogLaplaceDampedSynthesis_eq_weightedShift
    (h : ℝ≥0) (hh : 0 < h) (a : primeLogCriticalSourceL2)
    (ha : MemLp (primeLogCriticalLaplaceProfile a) 2 (volume.restrict (Ioi (0 : ℝ)))) :
    primeLogLaplaceDampedSynthesis h hh a =
      burnolWeightedShift h (ha.toLp (primeLogCriticalLaplaceProfile a)) := by
  apply Lp.ext
  have hsource := primeLogCriticalLaplaceClosureGraph_ae
    (primeLogLaplaceDamped_pair_mem_closureGraph h hh a)
  have htranslate := (quasiMeasurePreserving_add_right_Ioi h.coe_nonneg).ae_eq_comp ha.coeFn_toLp
  filter_upwards [hsource,
    burnolWeightedShift_coeFn h (ha.toLp (primeLogCriticalLaplaceProfile a)),
    htranslate, ae_restrict_mem measurableSet_Ioi] with t hS hK hF ht
  simp only [Function.comp_apply] at hF
  rw [hS, hK, hF]
  exact primeLogCriticalLaplaceProfile_damping h a ht

theorem primeLogCriticalLaplaceProfile_pair_mem_closureGraph
    (a : primeLogCriticalSourceL2)
    (ha : MemLp (primeLogCriticalLaplaceProfile a) 2 (volume.restrict (Ioi (0 : ℝ)))) :
    (a, ha.toLp (primeLogCriticalLaplaceProfile a)) ∈
      primeLogCriticalLaplaceSynthesis.closure.graph := by
  let f := ha.toLp (primeLogCriticalLaplaceProfile a)
  have hlim := (tendsto_primeLogLaplaceDamping_zero a).prodMk_nhds
    (tendsto_burnolWeightedShift_zero f)
  apply primeLogCriticalLaplaceSynthesis_closure_isClosed.mem_of_tendsto
    (hlim.mono_left (nhdsWithin_le_nhds (s := Ioi (0 : ℝ≥0))))
  filter_upwards [self_mem_nhdsWithin] with h hh
  change (primeLogLaplaceDamping h a,
    burnolWeightedShift h (ha.toLp (primeLogCriticalLaplaceProfile a))) ∈
      primeLogCriticalLaplaceSynthesis.closure.graph
  rw [← primeLogLaplaceDampedSynthesis_eq_weightedShift h hh a ha]
  exact primeLogLaplaceDamped_pair_mem_closureGraph h hh a

/-- The closed finite-prime operator has exactly its maximal literal L² domain. -/
theorem primeLogCriticalLaplaceClosure_domain_iff (a : primeLogCriticalSourceL2) :
    a ∈ primeLogCriticalLaplaceSynthesis.closure.domain ↔
      MemLp (primeLogCriticalLaplaceProfile a) 2 (volume.restrict (Ioi (0 : ℝ))) := by
  rw [LinearPMap.mem_domain_iff]
  constructor
  · rintro ⟨y, hy⟩
    exact primeLogCriticalLaplaceClosureGraph_memLp hy
  · intro ha
    exact ⟨_, primeLogCriticalLaplaceProfile_pair_mem_closureGraph a ha⟩

/-- Both membership and output are determined by the literal infinite-prime profile. -/
theorem primeLogCriticalLaplaceClosure_graph_iff
    (a : primeLogCriticalSourceL2) (y : primeLogCriticalHalfLineL2) :
    (a, y) ∈ primeLogCriticalLaplaceSynthesis.closure.graph ↔
      (y : ℝ → ℂ) =ᵐ[volume.restrict (Ioi (0 : ℝ))] primeLogCriticalLaplaceProfile a := by
  constructor
  · exact primeLogCriticalLaplaceClosureGraph_ae
  · intro hy
    have ha := MemLp.ae_eq hy (Lp.memLp y)
    have heq : y = ha.toLp (primeLogCriticalLaplaceProfile a) :=
      Lp.ext (hy.trans ha.coeFn_toLp.symm)
    rw [heq]
    exact primeLogCriticalLaplaceProfile_pair_mem_closureGraph a ha

end RHTower
