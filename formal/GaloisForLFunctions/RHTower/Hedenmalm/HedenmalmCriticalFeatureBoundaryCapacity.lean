import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureFirstOrderWindingAsymptotic
import GaloisForLFunctions.RHTower.HorizontalSingletonFiberCharging
import GaloisForLFunctions.RHTower.FEOrbitQuotientMoments
import GaloisForLFunctions.RHTower.XiHeightAdaptiveHedenmalmCensusCollision
import GaloisForLFunctions.RHTower.Hedenmalm.HedenmalmCriticalFeatureSevenTenthsCanonicalCensus

/-!
# Exact interior capacity of the phase-averaged HCF boundary lattice

The canonical translated lattice has more structure than the previously used universal upper
bound `2π`.  Averaging its phase tiles the individual unit cells into one long interval.  Hence a
real spectral point a fixed distance from the height boundary receives the HCF mass on every fixed
symmetric core, and those core masses exhaust the exact full mass `2π`.

This is the analytic input for identifying the Plemelj source-boundary average with the complete
critical-line multiplicity up to a fixed-width zero-count edge.  It uses no numerical computation
and no zero or divisor index.
-/

open Complex Filter Topology Set MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped BigOperators

namespace RHTower

noncomputable section

/-- Real-valued form of consecutive unit-cell tiling. -/
theorem intervalIntegral_sum_range_realCells_eq
    {f : ℝ → ℝ} (hf : Continuous f) (K : ℕ) :
    (∫ v : ℝ in (0 : ℝ)..1,
      ∑ m ∈ Finset.range K, f ((m : ℝ) + v)) =
      ∫ y : ℝ in (0 : ℝ)..(K : ℝ), f y := by
  induction K with
  | zero => simp
  | succ K ih =>
      simp_rw [Finset.sum_range_succ]
      have hsumCont : Continuous (fun v : ℝ =>
          ∑ m ∈ Finset.range K, f ((m : ℝ) + v)) := by
        fun_prop
      have hcellCont : Continuous (fun v : ℝ => f ((K : ℝ) + v)) := by
        fun_prop
      rw [intervalIntegral.integral_add
        (hsumCont.intervalIntegrable _ _) (hcellCont.intervalIntegrable _ _)]
      rw [ih]
      have hshift :
          (∫ v : ℝ in (0 : ℝ)..1, f ((K : ℝ) + v)) =
            ∫ y : ℝ in (K : ℝ)..((K : ℝ) + 1), f y := by
        rw [intervalIntegral.integral_comp_add_left f (K : ℝ)]
        simp
      rw [hshift, Nat.cast_succ]
      exact intervalIntegral.integral_add_adjacent_intervals
        (a := (0 : ℝ)) (b := (K : ℝ)) (c := (K : ℝ) + 1)
        (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)

/-- Reindex the asymmetric integer window by increasing physical unit cells. -/
theorem sum_criticalFeatureCanonicalLatticeWindow_reindex
    (n : ℕ) (x theta : ℝ) :
    (∑ k ∈ criticalFeatureCanonicalLatticeWindow n,
      criticalFeatureRealBoundaryWeight (k - theta) x) =
    ∑ m ∈ Finset.range (2 * n + 3),
      criticalFeatureRealBoundaryWeight 0
        ((x - (n : ℝ) - 1) + ((m : ℝ) + theta)) := by
  classical
  rw [criticalFeatureCanonicalLatticeWindow]
  refine Finset.sum_bij (fun k _ => Int.toNat ((n : ℤ) + 1 - k)) ?_ ?_ ?_ ?_
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    simp only [Finset.mem_range]
    omega
  · intro a ha b hb hab
    simp only [Finset.mem_Icc] at ha hb
    have ha0 : 0 ≤ (n : ℤ) + 1 - a := by omega
    have hb0 : 0 ≤ (n : ℤ) + 1 - b := by omega
    have hab' := congrArg (fun m : ℕ => (m : ℤ)) hab
    have hab'' : (n : ℤ) + 1 - a = (n : ℤ) + 1 - b := by
      simpa only [Int.toNat_of_nonneg ha0, Int.toNat_of_nonneg hb0] using hab'
    omega
  · intro m hm
    simp only [Finset.mem_range] at hm
    let k : ℤ := (n : ℤ) + 1 - (m : ℤ)
    have hk : k ∈ Finset.Icc (-(n : ℤ) - 1) ((n : ℤ) + 1) := by
      simp only [Finset.mem_Icc, k]
      constructor <;> omega
    refine ⟨k, hk, ?_⟩
    simp only [k]
    omega
  · intro k hk
    simp only [Finset.mem_Icc] at hk
    have hk0 : 0 ≤ (n : ℤ) + 1 - k := by omega
    have hkCastInt := Int.toNat_of_nonneg hk0
    have hkCastReal :
        ((((n : ℤ) + 1 - k).toNat : ℕ) : ℝ) =
          (((n : ℤ) + 1 - k : ℤ) : ℝ) := by
      exact_mod_cast hkCastInt
    rw [hkCastReal]
    unfold criticalFeatureRealBoundaryWeight
    push_cast
    congr 2
    ring

/-- Exact phase-cell identity: the canonical finite lattice becomes one long HCF mass interval. -/
theorem phaseIntegral_criticalFeatureCanonicalLatticeWindow_eq_longIntegral
    (n : ℕ) (x : ℝ) :
    (∫ theta : ℝ in (0 : ℝ)..1,
      criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight theta
        (criticalFeatureCanonicalLatticeWindow n) x) =
      ∫ y : ℝ in (x - (n : ℝ) - 1)..(x + (n : ℝ) + 2),
        criticalFeatureRealBoundaryWeight 0 y := by
  rw [show (fun theta : ℝ =>
      criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight theta
        (criticalFeatureCanonicalLatticeWindow n) x) =
      fun theta => ∑ m ∈ Finset.range (2 * n + 3),
        criticalFeatureRealBoundaryWeight 0
          ((x - (n : ℝ) - 1) + ((m : ℝ) + theta)) by
    funext theta
    exact sum_criticalFeatureCanonicalLatticeWindow_reindex n x theta]
  let f : ℝ → ℝ := fun y =>
    criticalFeatureRealBoundaryWeight 0 ((x - (n : ℝ) - 1) + y)
  have hf : Continuous f :=
    (continuous_criticalFeatureRealBoundaryWeight 0).comp
      (continuous_const.add continuous_id)
  have htile := intervalIntegral_sum_range_realCells_eq hf (2 * n + 3)
  change (∫ theta : ℝ in (0 : ℝ)..1,
      ∑ m ∈ Finset.range (2 * n + 3), f ((m : ℝ) + theta)) = _
  rw [htile]
  rw [intervalIntegral.integral_comp_add_left
    (criticalFeatureRealBoundaryWeight 0) (x - (n : ℝ) - 1)]
  push_cast
  congr 1 <;> ring

/-- Every point inside the fixed-width edge sees at least the HCF mass of the corresponding
symmetric core. -/
theorem intervalIntegral_criticalFeatureRealBoundaryWeight_le_phaseIntegral_of_interior
    (n : ℕ) (x A : ℝ) (hA : 0 ≤ A)
    (hinterior : |x| + A ≤ (n : ℝ) + 1) :
    (∫ y : ℝ in (-A)..A, criticalFeatureRealBoundaryWeight 0 y) ≤
      ∫ theta : ℝ in (0 : ℝ)..1,
        criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight theta
          (criticalFeatureCanonicalLatticeWindow n) x := by
  rw [phaseIntegral_criticalFeatureCanonicalLatticeWindow_eq_longIntegral]
  apply intervalIntegral.integral_mono_interval
  · linarith [le_abs_self x]
  · linarith
  · linarith [neg_le_abs x]
  · filter_upwards with y
    unfold criticalFeatureRealBoundaryWeight
    positivity
  · exact (continuous_criticalFeatureRealBoundaryWeight 0).intervalIntegrable _ _

/-- Symmetric interior HCF masses exhaust the sharp phase capacity `2π`. -/
theorem tendsto_intervalIntegral_criticalFeatureRealBoundaryWeight_atTop :
    Tendsto
      (fun A : ℝ => ∫ y : ℝ in (-A)..A,
        criticalFeatureRealBoundaryWeight 0 y)
      atTop (𝓝 (2 * Real.pi)) := by
  have h := intervalIntegral_tendsto_integral (μ := volume)
    (l := (atTop : Filter ℝ))
    (a := fun A : ℝ => -A) (b := fun A : ℝ => A)
    (integrable_criticalFeatureRealBoundaryWeight 0)
    tendsto_neg_atTop_atBot tendsto_id
  rwa [integral_criticalFeatureRealBoundaryWeight] at h

/-- Exact capacity decomposition of the source boundary phase average.  Plemelj is used only after
the source statistic has been defined; each real zero is then weighted by its compact cutoff and
its exact finite-lattice phase capacity. -/
theorem exists_criticalFeatureSourceBoundaryPhaseAverage_eq_capacitySum (n : ℕ) :
    ∃ Gamma : Finset ℝ,
      (∀ gamma : ℝ, gamma ∈ Gamma ↔
        ((gamma : ℂ) ∈ Metric.ball (0 : ℂ) ((n : ℝ) + 4) ∧
          XiC (gamma : ℂ) = 0)) ∧
      criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n =
        ∑ gamma ∈ Gamma,
          ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
            SchwartzMap.realCompactIntervalCutoff (n : ℝ) gamma *
              (∫ theta : ℝ in (0 : ℝ)..1,
                criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight theta
                  (criticalFeatureCanonicalLatticeWindow n) gamma) := by
  obtain ⟨Gamma, hGamma, hformula⟩ :=
    exists_criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseFamily_eq_realZeroSums n
  refine ⟨Gamma, hGamma, ?_⟩
  rw [criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage]
  simp_rw [hformula]
  rw [intervalIntegral.integral_finsetSum]
  · apply Finset.sum_congr rfl
    intro gamma hgamma
    rw [intervalIntegral.integral_const_mul]
    simp_rw [criticalFeatureTranslatedLatticeBoundaryCutoffWeight_eq_finite_mul_cutoff]
    rw [intervalIntegral.integral_mul_const]
    ring
  · intro gamma hgamma
    exact (continuous_const.mul
      (continuous_criticalFeatureTranslatedLatticeBoundaryCutoffWeight_phase
        (criticalFeatureCanonicalLatticeWindow n) n gamma)).intervalIntegrable 0 1

/-- Fixed-width interior floor.  Every real zero whose spectral height lies outside the boundary
edge contributes at least the symmetric core mass; all other terms remain nonnegative. -/
theorem exists_criticalFeatureSourceBoundaryPhaseAverage_interior_lower
    (n : ℕ) (A : ℝ) (hA : 0 ≤ A) :
    ∃ Gamma : Finset ℝ,
      (∀ gamma : ℝ, gamma ∈ Gamma ↔
        ((gamma : ℂ) ∈ Metric.ball (0 : ℂ) ((n : ℝ) + 4) ∧
          XiC (gamma : ℂ) = 0)) ∧
      (∫ y : ℝ in (-A)..A, criticalFeatureRealBoundaryWeight 0 y) *
          (∑ gamma ∈ Gamma.filter
              (fun gamma => |gamma| + A ≤ (n : ℝ) + 1),
            ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ)) ≤
        criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n := by
  obtain ⟨Gamma, hGamma, havg⟩ :=
    exists_criticalFeatureSourceBoundaryPhaseAverage_eq_capacitySum n
  refine ⟨Gamma, hGamma, ?_⟩
  let mass : ℝ := ∫ y : ℝ in (-A)..A, criticalFeatureRealBoundaryWeight 0 y
  let cap : ℝ → ℝ := fun gamma =>
    ∫ theta : ℝ in (0 : ℝ)..1,
      criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight theta
        (criticalFeatureCanonicalLatticeWindow n) gamma
  let term : ℝ → ℝ := fun gamma =>
    ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) *
      SchwartzMap.realCompactIntervalCutoff (n : ℝ) gamma * cap gamma
  have hfilter : Gamma.filter
      (fun gamma => |gamma| + A ≤ (n : ℝ) + 1) ⊆ Gamma :=
    Finset.filter_subset _ _
  have hmain :
      mass *
          (∑ gamma ∈ Gamma.filter
              (fun gamma => |gamma| + A ≤ (n : ℝ) + 1),
            ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ)) ≤
        ∑ gamma ∈ Gamma.filter
            (fun gamma => |gamma| + A ≤ (n : ℝ) + 1), term gamma := by
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro gamma hgamma
    have hinterior : |gamma| + A ≤ (n : ℝ) + 1 :=
      (Finset.mem_filter.mp hgamma).2
    have hchi : SchwartzMap.realCompactIntervalCutoff (n : ℝ) gamma = 1 := by
      apply SchwartzMap.realCompactIntervalCutoff_apply_of_abs_le_add_one
      have hnabs : |(n : ℝ)| = (n : ℝ) := abs_of_nonneg (Nat.cast_nonneg n)
      rw [hnabs]
      linarith
    have hcap : mass ≤ cap gamma := by
      exact intervalIntegral_criticalFeatureRealBoundaryWeight_le_phaseIntegral_of_interior
        n gamma A hA hinterior
    have hm : (0 : ℝ) ≤ ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) :=
      Nat.cast_nonneg _
    dsimp only [term]
    rw [hchi, mul_one]
    dsimp only [cap]
    nlinarith
  have hrest :
      (∑ gamma ∈ Gamma.filter
          (fun gamma => |gamma| + A ≤ (n : ℝ) + 1), term gamma) ≤
        ∑ gamma ∈ Gamma, term gamma := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hfilter fun gamma hgamma hnot => by
      have hm : (0 : ℝ) ≤ ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) :=
        Nat.cast_nonneg _
      have hchi := SchwartzMap.realCompactIntervalCutoff_nonnegative (n : ℝ) gamma
      have hcap : 0 ≤ cap gamma := by
        apply intervalIntegral.integral_nonneg (by norm_num)
        intro theta htheta
        exact criticalFeatureTranslatedFiniteRealBoundaryLatticeWeight_nonnegative
          theta (criticalFeatureCanonicalLatticeWindow n) gamma
      dsimp only [term]
      positivity
  rw [havg]
  change mass *
      (∑ gamma ∈ Gamma.filter
          (fun gamma => |gamma| + A ≤ (n : ℝ) + 1),
        ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ)) ≤
    ∑ gamma ∈ Gamma, term gamma
  exact hmain.trans hrest

/-! ## Exact weld to the positive critical-line census -/

/-- Positive-height critical-line Xi zeros, before expanding analytic multiplicity. -/
def criticalFeaturePositiveCriticalZeroPacket (T : ℝ) : Finset ℂ :=
  (stripFinsetPos T).filter (fun z => z.re = 1 / 2)

/-- The two centered real zeros `±γ` belonging to every positive-height critical-line zero. -/
def criticalFeatureRealXiPairPacket (T : ℝ) : Finset ℝ :=
  (criticalFeaturePositiveCriticalZeroPacket T).image Complex.im ∪
    (criticalFeaturePositiveCriticalZeroPacket T).image (fun z => -z.im)

theorem centeredCoordinate_eq_of_re_eq_half {z : ℂ} (hz : z.re = 1 / 2) :
    (z - 1 / 2) * (-I) = (z.im : ℂ) := by
  apply Complex.ext
  · simp [Complex.mul_re, hz]
  · simp [Complex.mul_im, hz]

theorem XiC_ofReal_im_eq_xi_of_re_eq_half {z : ℂ} (hz : z.re = 1 / 2) :
    XiC (z.im : ℂ) = xi z := by
  rw [← centeredCoordinate_eq_of_re_eq_half hz]
  unfold XiC
  congr 1
  rw [mul_assoc, neg_mul, I_mul_I]
  ring

theorem analyticOrderAt_XiC_ofReal_im_eq_xi_of_re_eq_half
    {z : ℂ} (hz : z.re = 1 / 2) :
    analyticOrderAt XiC (z.im : ℂ) = analyticOrderAt xi z := by
  rw [← centeredCoordinate_eq_of_re_eq_half hz]
  exact analyticOrderAt_XiC_centeredCoordinate z

theorem criticalFeaturePositiveCriticalZeroPacket_im_injective (T : ℝ) :
    Set.InjOn Complex.im (criticalFeaturePositiveCriticalZeroPacket T : Set ℂ) := by
  intro z hz w hw hi
  have hzre : z.re = 1 / 2 := (Finset.mem_filter.mp hz).2
  have hwre : w.re = 1 / 2 := (Finset.mem_filter.mp hw).2
  exact Complex.ext (hzre.trans hwre.symm) hi

theorem criticalFeaturePositiveCriticalZeroPacket_neg_im_injective (T : ℝ) :
    Set.InjOn (fun z : ℂ => -z.im)
      (criticalFeaturePositiveCriticalZeroPacket T : Set ℂ) := by
  intro z hz w hw hi
  apply criticalFeaturePositiveCriticalZeroPacket_im_injective T hz hw
  linarith

theorem disjoint_criticalFeatureRealXiPairPacket_images (T : ℝ) :
    Disjoint
      ((criticalFeaturePositiveCriticalZeroPacket T).image Complex.im)
      ((criticalFeaturePositiveCriticalZeroPacket T).image (fun z => -z.im)) := by
  rw [Finset.disjoint_left]
  intro gamma hpos hneg
  obtain ⟨z, hz, hzim⟩ := Finset.mem_image.mp hpos
  obtain ⟨w, hw, hwim⟩ := Finset.mem_image.mp hneg
  have hzpos : 0 < z.im := (mem_stripFinsetPos.mp (Finset.mem_filter.mp hz).1).2.2.1
  have hwpos : 0 < w.im := (mem_stripFinsetPos.mp (Finset.mem_filter.mp hw).1).2.2.1
  linarith

/-- The centered real packet has exactly twice the positive critical-line multiplicity. -/
theorem sum_criticalFeatureRealXiPairPacket_order (T : ℝ) :
    (∑ gamma ∈ criticalFeatureRealXiPairPacket T,
        (analyticOrderAt XiC (gamma : ℂ)).toNat) =
      2 * xiPosCriticalZeroCount T := by
  classical
  rw [criticalFeatureRealXiPairPacket,
    Finset.sum_union (disjoint_criticalFeatureRealXiPairPacket_images T)]
  have hpos :
      (∑ gamma ∈ (criticalFeaturePositiveCriticalZeroPacket T).image Complex.im,
          (analyticOrderAt XiC (gamma : ℂ)).toNat) =
        xiPosCriticalZeroCount T := by
    rw [Finset.sum_image (criticalFeaturePositiveCriticalZeroPacket_im_injective T)]
    unfold criticalFeaturePositiveCriticalZeroPacket xiPosCriticalZeroCount
    apply Finset.sum_congr rfl
    intro z hz
    rw [analyticOrderAt_XiC_ofReal_im_eq_xi_of_re_eq_half
      (Finset.mem_filter.mp hz).2]
  have hneg :
      (∑ gamma ∈ (criticalFeaturePositiveCriticalZeroPacket T).image
          (fun z : ℂ => (-z.im : ℝ)),
          (analyticOrderAt XiC (gamma : ℂ)).toNat) =
        xiPosCriticalZeroCount T := by
    rw [Finset.sum_image (criticalFeaturePositiveCriticalZeroPacket_neg_im_injective T)]
    unfold criticalFeaturePositiveCriticalZeroPacket xiPosCriticalZeroCount
    apply Finset.sum_congr rfl
    intro z hz
    have hcast : (((-z.im : ℝ) : ℂ)) = -((z.im : ℝ) : ℂ) := by simp
    rw [hcast, FEOrbitQuotient.analyticOrderAt_XiC_neg]
    rw [analyticOrderAt_XiC_ofReal_im_eq_xi_of_re_eq_half
      (Finset.mem_filter.mp hz).2]
  rw [hpos, hneg]
  omega

theorem mem_criticalFeatureRealXiPairPacket
    {T gamma : ℝ} (hgamma : gamma ∈ criticalFeatureRealXiPairPacket T) :
    |gamma| ≤ T ∧ XiC (gamma : ℂ) = 0 := by
  rw [criticalFeatureRealXiPairPacket, Finset.mem_union] at hgamma
  rcases hgamma with hgamma | hgamma
  · obtain ⟨z, hz, hzim⟩ := Finset.mem_image.mp hgamma
    have hzpacket := Finset.mem_filter.mp hz
    have hzstrip := mem_stripFinsetPos.mp hzpacket.1
    have hgammaEq : gamma = z.im := hzim.symm
    constructor
    · rw [hgammaEq, abs_of_pos hzstrip.2.2.1]
      exact hzstrip.2.2.2.1
    · rw [hgammaEq, XiC_ofReal_im_eq_xi_of_re_eq_half hzpacket.2]
      exact hzstrip.2.2.2.2
  · obtain ⟨z, hz, hzim⟩ := Finset.mem_image.mp hgamma
    have hzpacket := Finset.mem_filter.mp hz
    have hzstrip := mem_stripFinsetPos.mp hzpacket.1
    have hgammaEq : gamma = -z.im := hzim.symm
    constructor
    · rw [hgammaEq, abs_neg, abs_of_pos hzstrip.2.2.1]
      exact hzstrip.2.2.2.1
    · have hpos : XiC (z.im : ℂ) = 0 := by
        rw [XiC_ofReal_im_eq_xi_of_re_eq_half hzpacket.2]
        exact hzstrip.2.2.2.2
      rw [hgammaEq]
      have hcast : (((-z.im : ℝ) : ℂ)) = -((z.im : ℝ) : ℂ) := by simp
      rw [hcast, XiC_even]
      exact hpos

theorem mem_criticalFeatureRealXiPairPacket_iff
    {T gamma : ℝ} :
    gamma ∈ criticalFeatureRealXiPairPacket T ↔
      |gamma| ≤ T ∧ XiC (gamma : ℂ) = 0 := by
  constructor
  · exact mem_criticalFeatureRealXiPairPacket
  · rintro ⟨hbound, hzero⟩
    have hgamma0 : gamma ≠ 0 := by
      intro h
      subst gamma
      have hne := xi_ne_zero_of_ofReal (1 / 2 : ℝ)
      apply hne
      simpa [XiC] using hzero
    rcases lt_or_gt_of_ne hgamma0 with hneg | hpos
    · let z : ℂ := (1 / 2 : ℂ) + ((-gamma : ℝ) : ℂ) * I
      have hz : z ∈ criticalFeaturePositiveCriticalZeroPacket T := by
        rw [criticalFeaturePositiveCriticalZeroPacket, Finset.mem_filter,
          mem_stripFinsetPos]
        refine ⟨⟨by dsimp [z]; simp, by dsimp [z]; norm_num,
          by dsimp [z]; simp; linarith, ?_, ?_⟩, by dsimp [z]; simp⟩
        · dsimp [z]
          norm_num [Complex.mul_im]
          rw [← abs_of_neg hneg]
          exact hbound
        · have hnegZero : XiC ((-gamma : ℝ) : ℂ) = 0 := by
            have hcast : (((-gamma : ℝ) : ℂ)) = -((gamma : ℝ) : ℂ) := by simp
            rw [hcast, XiC_even]
            exact hzero
          exact hnegZero
      rw [criticalFeatureRealXiPairPacket, Finset.mem_union]
      right
      apply Finset.mem_image.mpr
      refine ⟨z, hz, ?_⟩
      dsimp [z]
      simp
    · let z : ℂ := (1 / 2 : ℂ) + (gamma : ℂ) * I
      have hz : z ∈ criticalFeaturePositiveCriticalZeroPacket T := by
        rw [criticalFeaturePositiveCriticalZeroPacket, Finset.mem_filter,
          mem_stripFinsetPos]
        refine ⟨⟨by dsimp [z]; simp, by dsimp [z]; norm_num,
          by dsimp [z]; simpa, ?_, ?_⟩, by dsimp [z]; simp⟩
        · dsimp [z]
          norm_num [Complex.mul_im]
          rw [← abs_of_pos hpos]
          exact hbound
        · exact hzero
      rw [criticalFeatureRealXiPairPacket, Finset.mem_union]
      left
      apply Finset.mem_image.mpr
      refine ⟨z, hz, ?_⟩
      dsimp [z]
      simp

/-- Any real Xi packet in a centered ball has at most twice the positive critical-line
multiplicity at that height. -/
theorem realZeroMultiplicity_le_two_mul_xiPosCriticalZeroCount
    (T : ℝ) (Gamma : Finset ℝ)
    (hGamma : ∀ gamma : ℝ, gamma ∈ Gamma ↔
      ((gamma : ℂ) ∈ Metric.ball (0 : ℂ) T ∧ XiC (gamma : ℂ) = 0)) :
    (∑ gamma ∈ Gamma,
        ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ)) ≤
      (2 : ℝ) * xiPosCriticalZeroCount T := by
  have hsubset : Gamma ⊆ criticalFeatureRealXiPairPacket T := by
    intro gamma hgamma
    have hg := (hGamma gamma).mp hgamma
    rw [mem_criticalFeatureRealXiPairPacket_iff]
    constructor
    · have hlt : |gamma| < T := by
        simpa only [Metric.mem_ball, Complex.dist_eq, sub_zero, norm_real,
          Real.norm_eq_abs] using hg.1
      exact hlt.le
    · exact hg.2
  have hsum :
      (∑ gamma ∈ Gamma,
          ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ)) ≤
        ∑ gamma ∈ criticalFeatureRealXiPairPacket T,
          ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset fun gamma hgamma hnot =>
      Nat.cast_nonneg _
  have hpairNat := sum_criticalFeatureRealXiPairPacket_order T
  have hpairReal :
      (∑ gamma ∈ criticalFeatureRealXiPairPacket T,
          ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ)) =
        (2 : ℝ) * xiPosCriticalZeroCount T := by
    exact_mod_cast hpairNat
  rwa [hpairReal] at hsum

/-- Universal upper half of the boundary-capacity squeeze, with only the fixed `+4` Plemelj
cutoff edge left. -/
theorem criticalFeatureSourceBoundaryPhaseAverage_le_xiPosCriticalZeroCount_add_four
    (n : ℕ) :
    criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n ≤
      4 * Real.pi * xiPosCriticalZeroCount ((n : ℝ) + 4) := by
  obtain ⟨Gamma, hGamma, hupper⟩ :=
    exists_criticalFeatureSourceBoundaryPhaseAverage_le_realZeroMultiplicity n
  have hcount := realZeroMultiplicity_le_two_mul_xiPosCriticalZeroCount
    ((n : ℝ) + 4) Gamma hGamma
  have hpi : 0 ≤ 2 * Real.pi := by positivity
  have hmul := mul_le_mul_of_nonneg_left hcount hpi
  calc
    criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n ≤
        2 * Real.pi *
          ∑ gamma ∈ Gamma, ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) := hupper
    _ ≤ 2 * Real.pi * ((2 : ℝ) * xiPosCriticalZeroCount ((n : ℝ) + 4)) := hmul
    _ = 4 * Real.pi * xiPosCriticalZeroCount ((n : ℝ) + 4) := by ring

theorem two_mul_xiPosCriticalZeroCount_le_interiorRealZeroMultiplicity
    (n : ℕ) (T A : ℝ) (hA : 0 ≤ A)
    (hTA : T + A ≤ (n : ℝ) + 1)
    (Gamma : Finset ℝ)
    (hGamma : ∀ gamma : ℝ, gamma ∈ Gamma ↔
      ((gamma : ℂ) ∈ Metric.ball (0 : ℂ) ((n : ℝ) + 4) ∧
        XiC (gamma : ℂ) = 0)) :
    (2 : ℝ) * xiPosCriticalZeroCount T ≤
      ∑ gamma ∈ Gamma.filter
          (fun gamma => |gamma| + A ≤ (n : ℝ) + 1),
        ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) := by
  have hsubset : criticalFeatureRealXiPairPacket T ⊆
      Gamma.filter (fun gamma => |gamma| + A ≤ (n : ℝ) + 1) := by
    intro gamma hgamma
    have hg := mem_criticalFeatureRealXiPairPacket hgamma
    rw [Finset.mem_filter]
    refine ⟨(hGamma gamma).mpr ?_, ?_⟩
    · constructor
      · rw [Metric.mem_ball, Complex.dist_eq, sub_zero, norm_real, Real.norm_eq_abs]
        linarith
      · exact hg.2
    · linarith
  have hsum :
      (∑ gamma ∈ criticalFeatureRealXiPairPacket T,
          ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ)) ≤
        ∑ gamma ∈ Gamma.filter
            (fun gamma => |gamma| + A ≤ (n : ℝ) + 1),
          ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ) := by
    exact Finset.sum_le_sum_of_subset_of_nonneg hsubset fun gamma hgamma hnot =>
      Nat.cast_nonneg _
  have hpairNat := sum_criticalFeatureRealXiPairPacket_order T
  have hpairReal :
      (∑ gamma ∈ criticalFeatureRealXiPairPacket T,
          ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ)) =
        (2 : ℝ) * xiPosCriticalZeroCount T := by
    exact_mod_cast hpairNat
  rwa [hpairReal] at hsum

/-- Quantitative boundary-capacity weld.  At every fixed symmetric core, the source boundary pays
twice its HCF mass for every positive critical-line zero below the inner height. -/
theorem criticalFeatureSourceBoundaryPhaseAverage_lower_xiPosCriticalZeroCount
    (n : ℕ) (T A : ℝ) (hA : 0 ≤ A)
    (hTA : T + A ≤ (n : ℝ) + 1) :
    (2 * (∫ y : ℝ in (-A)..A, criticalFeatureRealBoundaryWeight 0 y)) *
        xiPosCriticalZeroCount T ≤
      criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n := by
  obtain ⟨Gamma, hGamma, hfloor⟩ :=
    exists_criticalFeatureSourceBoundaryPhaseAverage_interior_lower n A hA
  have hcount := two_mul_xiPosCriticalZeroCount_le_interiorRealZeroMultiplicity
    n T A hA hTA Gamma hGamma
  have hmass : 0 ≤ ∫ y : ℝ in (-A)..A,
      criticalFeatureRealBoundaryWeight 0 y := by
    apply intervalIntegral.integral_nonneg (by linarith)
    intro y hy
    unfold criticalFeatureRealBoundaryWeight
    positivity
  have hmul := mul_le_mul_of_nonneg_left hcount hmass
  calc
    (2 * (∫ y : ℝ in (-A)..A, criticalFeatureRealBoundaryWeight 0 y)) *
        xiPosCriticalZeroCount T =
      (∫ y : ℝ in (-A)..A, criticalFeatureRealBoundaryWeight 0 y) *
        ((2 : ℝ) * xiPosCriticalZeroCount T) := by ring
    _ ≤ (∫ y : ℝ in (-A)..A, criticalFeatureRealBoundaryWeight 0 y) *
        (∑ gamma ∈ Gamma.filter
            (fun gamma => |gamma| + A ≤ (n : ℝ) + 1),
          ((analyticOrderAt XiC (gamma : ℂ)).toNat : ℝ)) := hmul
    _ ≤ criticalFeatureCompactFiniteLatticeSourceBoundaryPhaseAverage n := hfloor

/-- The support-indexed HCF census and the classical finite-zero census count the same positive
critical-line divisor, with the same analytic multiplicity. -/
theorem criticalFeatureCanonicalCriticalLineCount_eq_xiPosCriticalZeroCount
    (n : ℕ) :
    criticalFeatureCanonicalCriticalLineCount n =
      (xiPosCriticalZeroCount (n : ℝ) : ℝ) := by
  classical
  have hsum :
      (∑ rho ∈ criticalFeatureCanonicalCriticalLineSupportPacket n,
          xiSupportMultiplicity rho) =
        xiPosCriticalZeroCount (n : ℝ) := by
    unfold xiPosCriticalZeroCount
    refine Finset.sum_bij (fun rho _ => (rho : ℂ)) ?_ ?_ ?_ ?_
    · intro rho hrho
      rw [criticalFeatureCanonicalCriticalLineSupportPacket,
        Finset.mem_filter] at hrho
      rw [Finset.mem_filter, mem_stripFinsetPos]
      have hpos := mem_xiSupportsPos.mp hrho.1
      have hstrip := xi_zero_re_mem_open_unit (xi_eq_zero_of_mem_divisor_support rho)
      refine ⟨⟨hstrip.1, hstrip.2, hpos.2, ?_,
        xi_eq_zero_of_mem_divisor_support rho⟩, hrho.2⟩
      rw [abs_of_pos hpos.2] at hpos
      exact hpos.1
    · intro a ha b hb hab
      exact Subtype.ext hab
    · intro z hz
      rw [Finset.mem_filter, mem_stripFinsetPos] at hz
      let rho : XiDivisorSupport :=
        ⟨z, mem_xi_divisor_support_of_eq_zero hz.1.2.2.2.2⟩
      have hrho : rho ∈ criticalFeatureCanonicalCriticalLineSupportPacket n := by
        rw [criticalFeatureCanonicalCriticalLineSupportPacket, Finset.mem_filter,
          mem_xiSupportsPos]
        refine ⟨⟨?_, hz.1.2.2.1⟩, hz.2⟩
        rw [abs_of_pos hz.1.2.2.1]
        exact hz.1.2.2.2.1
      exact ⟨rho, hrho, rfl⟩
    · intro rho hrho
      exact xiSupportMultiplicity_eq_analyticOrderAt_toNat rho
  rw [criticalFeatureCanonicalCriticalLineCount]
  exact_mod_cast hsum

end

end RHTower
