import GaloisForLFunctions.HTGeometry.HelsonCriterionNecessary
import GaloisForLFunctions.HTGeometry.HelsonCriterionSufficient

/-!
# The continuation stratum is a Borel set

Membership in the continuation stratum is an existential over meromorphic functions on the plane, so
it is not measurable by inspection.  The level certificates replace that existential by a *compact*
one: at each level the pole positions range over a closed polydisc and the Taylor coefficients over
a product of closed balls, and the certificate identity is a closed condition, because the Helson
zeta value is continuous in the phase and the series is continuous in its coefficients on the
coefficient box.

The projection of a closed set along a compact factor is closed, so each level–size stratum is
closed, and the stratum itself is a countable intersection of countable unions of closed sets.
-/

open Complex Filter Topology MeasureTheory

set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 1000000

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-- **The continuation stratum is exactly the set of phases certified at every level.** -/
theorem continuableStratum_eq_setOf_continuationCriterion :
    continuableStratum = {χ : PhaseTorus | ContinuationCriterion χ} := by
  ext χ
  constructor
  · intro hχ N
    exact exists_levelData_of_mem_continuableStratum hχ N
  · exact mem_continuableStratum_of_continuationCriterion

/-- The sum of a power series is continuous in the coefficients on the coefficient box. -/
theorem continuousOn_seriesSum_coeffBox (N B : ℕ) {w : ℂ} (hw : ‖w‖ < levelRadius N) :
    ContinuousOn (fun c : ℕ → ℂ => seriesSum c w)
      (Set.univ.pi fun n => Metric.closedBall (0 : ℂ) ((B : ℝ) / levelRadius N ^ n)) := by
  have hρ : 0 < levelRadius N := levelRadius_pos N
  have hratio : ‖w‖ / levelRadius N < 1 := (div_lt_one hρ).2 hw
  have hgeom : Summable (fun n : ℕ => (B : ℝ) * (‖w‖ / levelRadius N) ^ n) :=
    (summable_geometric_of_lt_one (by positivity) hratio).mul_left _
  have hbound : ∀ n : ℕ, ∀ c ∈ (Set.univ.pi fun n =>
      Metric.closedBall (0 : ℂ) ((B : ℝ) / levelRadius N ^ n)),
      ‖c n * w ^ n‖ ≤ (B : ℝ) * (‖w‖ / levelRadius N) ^ n := by
    intro n c hc
    have hcn : ‖c n‖ ≤ (B : ℝ) / levelRadius N ^ n := by
      have := hc n (Set.mem_univ n)
      simpa [Metric.mem_closedBall, dist_eq_norm] using this
    calc ‖c n * w ^ n‖ = ‖c n‖ * ‖w‖ ^ n := by rw [norm_mul, norm_pow]
      _ ≤ ((B : ℝ) / levelRadius N ^ n) * ‖w‖ ^ n := by
          exact mul_le_mul_of_nonneg_right hcn (by positivity)
      _ = (B : ℝ) * (‖w‖ / levelRadius N) ^ n := by
          rw [div_pow]
          field_simp
  have huni := tendstoUniformlyOn_tsum hgeom hbound
  refine huni.continuousOn (Filter.Eventually.frequently ?_)
  filter_upwards with t
  exact continuousOn_finsetSum t fun n _ =>
    ((continuous_apply n).mul continuous_const).continuousOn

/-- The phases carrying a certificate of a fixed level and fixed data sizes. -/
def levelSet (N B d : ℕ) : Set PhaseTorus :=
  {χ : PhaseTorus | ∃ (u : Fin d → ℂ) (c : ℕ → ℂ), LevelData χ N B u c}

/-- **Each level–size stratum is closed**, by projecting a closed set along a compact factor. -/
theorem isClosed_levelSet (N B d : ℕ) : IsClosed (levelSet N B d) := by
  classical
  have hρ : 0 < levelRadius N := levelRadius_pos N
  set Ku : Set (Fin d → ℂ) := Set.univ.pi fun _ => rootBox N with hKu
  set Kc : Set (ℕ → ℂ) :=
    Set.univ.pi fun n => Metric.closedBall (0 : ℂ) ((B : ℝ) / levelRadius N ^ n) with hKc
  set K : Set ((Fin d → ℂ) × (ℕ → ℂ)) := Ku ×ˢ Kc with hKdef
  have hKucomp : IsCompact Ku := isCompact_univ_pi fun _ => isCompact_rootBox N
  have hKccomp : IsCompact Kc := isCompact_univ_pi fun n => isCompact_closedBall _ _
  have hKcomp : IsCompact K := hKucomp.prod hKccomp
  haveI : CompactSpace ↥K := isCompact_iff_compactSpace.mp hKcomp
  set S : Set (PhaseTorus × ↥K) :=
    {p | ∀ s : ℂ, ‖s - 2‖ < levelRadius N → 1 < s.re →
      rootPoly (p.2 : (Fin d → ℂ) × (ℕ → ℂ)).1 (s - 2) * helsonZetaValue s p.1
        = seriesSum (p.2 : (Fin d → ℂ) × (ℕ → ℂ)).2 (s - 2)} with hS
  have hcoordu : Continuous fun p : PhaseTorus × ↥K => (p.2 : (Fin d → ℂ) × (ℕ → ℂ)).1 :=
    continuous_fst.comp (continuous_subtype_val.comp continuous_snd)
  have hcoordc : Continuous fun p : PhaseTorus × ↥K => (p.2 : (Fin d → ℂ) × (ℕ → ℂ)).2 :=
    continuous_snd.comp (continuous_subtype_val.comp continuous_snd)
  have hSclosed : IsClosed S := by
    have hinter : S = ⋂ s : ℂ, {p : PhaseTorus × ↥K | ‖s - 2‖ < levelRadius N → 1 < s.re →
        rootPoly (p.2 : (Fin d → ℂ) × (ℕ → ℂ)).1 (s - 2) * helsonZetaValue s p.1
          = seriesSum (p.2 : (Fin d → ℂ) × (ℕ → ℂ)).2 (s - 2)} := by
      ext p
      simp [hS, Set.mem_iInter]
    rw [hinter]
    refine isClosed_iInter fun s => ?_
    by_cases hs1 : ‖s - 2‖ < levelRadius N
    · by_cases hs2 : 1 < s.re
      · have hcont1 : Continuous fun p : PhaseTorus × ↥K =>
            rootPoly (p.2 : (Fin d → ℂ) × (ℕ → ℂ)).1 (s - 2) * helsonZetaValue s p.1 := by
          refine Continuous.mul ?_ ((continuous_helsonZetaValue hs2).comp continuous_fst)
          simp only [rootPoly]
          exact continuous_finsetProd _ fun i _ =>
            continuous_const.sub ((continuous_apply i).comp hcoordu)
        have hcont2 : Continuous fun p : PhaseTorus × ↥K =>
            seriesSum (p.2 : (Fin d → ℂ) × (ℕ → ℂ)).2 (s - 2) := by
          refine (continuousOn_seriesSum_coeffBox N B hs1).comp_continuous hcoordc ?_
          intro p
          exact p.2.2.2
        have : {p : PhaseTorus × ↥K | ‖s - 2‖ < levelRadius N → 1 < s.re →
            rootPoly (p.2 : (Fin d → ℂ) × (ℕ → ℂ)).1 (s - 2) * helsonZetaValue s p.1
              = seriesSum (p.2 : (Fin d → ℂ) × (ℕ → ℂ)).2 (s - 2)}
            = {p : PhaseTorus × ↥K |
              rootPoly (p.2 : (Fin d → ℂ) × (ℕ → ℂ)).1 (s - 2) * helsonZetaValue s p.1
                = seriesSum (p.2 : (Fin d → ℂ) × (ℕ → ℂ)).2 (s - 2)} := by
          ext p
          simp [hs1, hs2]
        rw [this]
        exact isClosed_eq hcont1 hcont2
      · have : {p : PhaseTorus × ↥K | ‖s - 2‖ < levelRadius N → 1 < s.re →
            rootPoly (p.2 : (Fin d → ℂ) × (ℕ → ℂ)).1 (s - 2) * helsonZetaValue s p.1
              = seriesSum (p.2 : (Fin d → ℂ) × (ℕ → ℂ)).2 (s - 2)} = Set.univ := by
          ext p
          simp [hs2]
        rw [this]
        exact isClosed_univ
    · have : {p : PhaseTorus × ↥K | ‖s - 2‖ < levelRadius N → 1 < s.re →
          rootPoly (p.2 : (Fin d → ℂ) × (ℕ → ℂ)).1 (s - 2) * helsonZetaValue s p.1
            = seriesSum (p.2 : (Fin d → ℂ) × (ℕ → ℂ)).2 (s - 2)} = Set.univ := by
        ext p
        simp [hs1]
      rw [this]
      exact isClosed_univ
  have himg : levelSet N B d = Prod.fst '' S := by
    ext χ
    constructor
    · rintro ⟨u, c, hbox, hbound, hid⟩
      have humem : u ∈ Ku := by
        intro i _
        exact hbox i
      have hcmem : c ∈ Kc := by
        intro n _
        have := hbound n
        simp only [Metric.mem_closedBall, dist_zero_right]
        rw [le_div_iff₀ (by positivity)]
        exact this
      refine ⟨(χ, ⟨(u, c), ⟨humem, hcmem⟩⟩), ?_, rfl⟩
      intro s hs1 hs2
      exact hid s hs1 hs2
    · rintro ⟨p, hp, rfl⟩
      refine ⟨(p.2 : (Fin d → ℂ) × (ℕ → ℂ)).1, (p.2 : (Fin d → ℂ) × (ℕ → ℂ)).2, ?_, ?_, ?_⟩
      · intro i
        exact p.2.2.1 i (Set.mem_univ i)
      · intro n
        have := p.2.2.2 n (Set.mem_univ n)
        simp only [Metric.mem_closedBall, dist_zero_right] at this
        rw [le_div_iff₀ (by positivity)] at this
        exact this
      · exact hp
  rw [himg]
  exact isClosedMap_fst_of_compactSpace S hSclosed

/-- **The continuation stratum is a Borel set.** -/
theorem measurableSet_continuableStratum : MeasurableSet continuableStratum := by
  rw [continuableStratum_eq_setOf_continuationCriterion]
  have hset : {χ : PhaseTorus | ContinuationCriterion χ}
      = ⋂ N : ℕ, ⋃ B : ℕ, ⋃ d : ℕ, levelSet N B d := by
    ext χ
    simp only [Set.mem_setOf_eq, Set.mem_iInter, Set.mem_iUnion, ContinuationCriterion, levelSet]
  rw [hset]
  exact MeasurableSet.iInter fun N => MeasurableSet.iUnion fun B =>
    MeasurableSet.iUnion fun d => (isClosed_levelSet N B d).measurableSet

end GaloisForLFunctions.HTGeometry

end
