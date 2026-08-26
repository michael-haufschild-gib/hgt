import GaloisForLFunctions.HTGeometry.AnalyticBackgroundOuterCage
import GaloisForLFunctions.HTGeometry.ShiftUniformPowerFreeness
import GaloisForLFunctions.HTGeometry.BohrOrbitClusterSet
import GaloisForLFunctions.HTGeometry.BohrPowerBoundary
import GaloisForLFunctions.HTGeometry.ExponentialSumDA
import GaloisForLFunctions.HTGeometry.AnalyticJetFieldBridge
import GaloisForLFunctions.HTGeometry.LocallyUniformProduct
import GaloisForLFunctions.HTGeometry.NevanlinnaFullRankPhaseGdelta
import GaloisForLFunctions.HTGeometry.LogPrimeExponentialCarrier
import GaloisForLFunctions.HTGeometry.HypertranscendentalAddConst
import GaloisForLFunctions.HTGeometry.EulerQGammaHypertranscendence
import GaloisForLFunctions.HTGeometry.CauchyTransformOpenUniqueness

/-!
# Toral DA boundaries of maximal-HT outer translation orbits

For every positive finite dimension this module constructs one bounded invertible Hardy-outer
function on the upper half-plane. Every finite packet of distinct real translates of every positive
power is differentially algebraically independent. At the same time, each powered orbit has an
exact compact-open boundary homeomorphic to the prescribed finite torus; every boundary function
is differentially algebraic, the orbit and boundary are disjoint, and boundary equals cluster set at
infinity.
-/

open Filter Topology Set MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section


def cmPow (N : ℕ) (f : C(UpperPlane, ℂ)) : C(UpperPlane, ℂ) := f ^ N

theorem continuous_cmPow (N : ℕ) : Continuous (cmPow N) := by
  rw [continuous_iff_continuousAt]
  intro f
  rw [ContinuousAt, ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn]
  intro K hK
  have hid : Tendsto (fun g : C(UpperPlane, ℂ) => g) (nhds f) (nhds f) := tendsto_id
  rw [ContinuousMap.tendsto_iff_forall_isCompact_tendstoUniformlyOn] at hid
  have hidK : TendstoUniformlyOn (fun g z => g z) f (nhds f) K := hid K hK
  change TendstoUniformlyOn (fun g z => g z ^ N) (fun z => f z ^ N) (nhds f) K
  exact TendstoUniformlyOn.pow_of_isCompact hidK hK f.continuous.continuousOn N

theorem tendsto_uniformity_cmPow_of_bound
    {γ : Type*} {l : Filter γ} {F G : γ → C(UpperPlane, ℂ)} {M : ℝ}
    (hM : 0 ≤ M) (hF : ∀ i z, ‖F i z‖ ≤ M) (hG : ∀ i z, ‖G i z‖ ≤ M)
    (h : Tendsto (fun i => (F i, G i)) l (uniformity C(UpperPlane, ℂ))) (N : ℕ) :
    Tendsto (fun i => (cmPow N (F i), cmPow N (G i))) l
      (uniformity C(UpperPlane, ℂ)) := by
  rw [ContinuousMap.hasBasis_compactConvergenceUniformity.tendsto_right_iff] at h ⊢
  rintro ⟨K, V⟩ ⟨hK, hV⟩
  obtain ⟨e, he, heV⟩ := Metric.mem_uniformity_dist.mp hV
  let C : ℝ := N * M ^ (N - 1)
  have hC : 0 ≤ C := mul_nonneg (Nat.cast_nonneg N) (pow_nonneg hM _)
  let delta : ℝ := e / (C + 1)
  have hdelta : 0 < delta := div_pos he (by linarith)
  have hev := h ⟨K, {p : ℂ × ℂ | dist p.1 p.2 < delta}⟩
    ⟨hK, Metric.dist_mem_uniformity hdelta⟩
  filter_upwards [hev] with i hi z hz
  apply heV
  have hd : ‖F i z - G i z‖ < delta := by
    have := hi z hz
    simpa [Complex.dist_eq] using this
  have hp := norm_pow_sub_pow_le_of_norm_le (hF i z) (hG i z) N
  rw [cmPow, Complex.dist_eq]
  refine lt_of_le_of_lt hp ?_
  calc
    (N : ℝ) * M ^ (N - 1) * ‖F i z - G i z‖
        ≤ C * delta := mul_le_mul_of_nonneg_left hd.le hC
    _ < e := by
      dsimp [delta]
      rw [mul_div_assoc']
      rw [div_lt_iff₀ (by linarith)]
      nlinarith

def toralAtom (n : ℕ) : ℝ := n

theorem toralAtom_injective : Function.Injective toralAtom := by
  intro m n h
  simp only [toralAtom] at h
  exact_mod_cast h

def toralMass (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

theorem toralMass_pos (n : ℕ) : 0 < toralMass n := by
  simp [toralMass]

theorem summable_toralMass : Summable toralMass := by
  change Summable fun n : ℕ => (1 / 2 : ℝ) ^ n
  exact summable_geometric_of_norm_lt_one (K := ℝ) (x := (1 / 2 : ℝ)) (by norm_num)

def toralFrequency (d : ℕ) (i : Fin d) : ℝ := logPrimeFrequency i

theorem toralFrequency_pos (d : ℕ) (i : Fin d) : 0 < toralFrequency d i := by
  rw [toralFrequency, logPrimeFrequency]
  exact Real.log_pos (lt_of_lt_of_le one_lt_two (two_le_nth_prime_real i))

theorem rationallyIndependentSequence_toralFrequency (d : ℕ) :
    RationallyIndependentSequence (toralFrequency d) := by
  let p : Fin d → Nat.Primes := fun i =>
    ⟨Nat.nth Nat.Prime i, Nat.prime_nth_prime i⟩
  have hp : Function.Injective p := by
    intro i j hij
    apply Fin.ext
    exact Nat.nth_injective Nat.infinite_setOf_prime (congrArg Subtype.val hij)
  have hlin : LinearIndependent ℤ
      (fun i : Fin d => Real.log (((p i : Nat.Primes) : ℕ) : ℝ)) :=
    GaloisForLFunctions.logPrime_linearIndependent_int.comp p hp
  apply rationallyIndependentSequence_of_linearIndependent_int
  change LinearIndependent ℤ
    (fun i : Fin d => Real.log ((Nat.nth Nat.Prime (i : ℕ) : ℕ) : ℝ))
  simpa [p] using hlin

def toralAmplitude (d : ℕ) (_ : Fin d) : ℂ := 1

theorem toralAmplitude_ne_zero (d : ℕ) (i : Fin d) : toralAmplitude d i ≠ 0 := by
  simp [toralAmplitude]

theorem expSeriesNormallySummable_toral (d : ℕ) :
    ExpSeriesNormallySummable (toralAmplitude d) (toralFrequency d) := by
  intro R
  exact Summable.of_finite

def toralScaleReal (d : ℕ) : ℝ := Real.exp (-1) / (2 * (d + 1))

theorem toralScaleReal_pos (d : ℕ) : 0 < toralScaleReal d := by
  unfold toralScaleReal
  positivity

theorem toralScaleReal_mul_lt (d : ℕ) :
    toralScaleReal d * d < Real.exp (-1) := by
  have he : 0 < Real.exp (-1) := Real.exp_pos _
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  unfold toralScaleReal
  rw [div_mul_eq_mul_div]
  rw [div_lt_iff₀ (by positivity : (0 : ℝ) < 2 * (d + 1))]
  nlinarith

theorem norm_bohrHullMap_toral_le (d : ℕ) (lam : Fin d → Circle) {z : ℂ}
    (hz : 0 ≤ z.im) :
    ‖bohrHullMap (toralAmplitude d) (toralFrequency d)
        (expSeriesNormallySummable_toral d) lam z‖ ≤ d := by
  rw [bohrHullMap_apply, cexpSeriesCarrier, tsum_fintype]
  calc
    ‖∑ i : Fin d, toralAmplitude d i * (lam i : ℂ) * cexpChar (toralFrequency d i) z‖
        ≤ ∑ i : Fin d,
            ‖toralAmplitude d i * (lam i : ℂ) * cexpChar (toralFrequency d i) z‖ :=
      norm_sum_le _ _
    _ ≤ ∑ _i : Fin d, (1 : ℝ) := by
      refine Finset.sum_le_sum fun i _ => ?_
      rw [norm_mul, norm_mul, Circle.norm_coe, norm_cexpChar]
      simp only [toralAmplitude, norm_one, one_mul]
      exact Real.exp_le_one_iff.mpr (neg_nonpos.mpr
        (mul_nonneg (toralFrequency_pos d i).le hz))
    _ = d := by simp

theorem norm_toralCarrier_le (d : ℕ) {z : ℂ} (hz : 0 ≤ z.im) :
    ‖cexpSeriesCarrier (toralAmplitude d) (toralFrequency d) z‖ ≤ d := by
  let lam : Fin d → Circle := fun _ => 1
  simpa [bohrHullMap_apply, lam] using norm_bohrHullMap_toral_le d lam hz

theorem norm_toralBackground_le (d : ℕ) {z : ℂ} (hz : 0 < z.im) :
    ‖(toralScaleReal d : ℂ) *
        cexpSeriesCarrier (toralAmplitude d) (toralFrequency d) z‖
      ≤ toralScaleReal d * d := by
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (toralScaleReal_pos d).le]
  exact mul_le_mul_of_nonneg_left (norm_toralCarrier_le d hz.le) (toralScaleReal_pos d).le

theorem exists_toralGoodMassParameter (d : ℕ) :
    ∃ u : MassParameter,
      ∀ (N : ℕ), N ≠ 0 → ∀ (m' : ℕ) (t : Fin (m' + 1) → ℝ),
        Function.Injective t → ¬ FamilyDifferentiallyAlgebraicOn
          (fun i w => perturbedOuterFamily toralAtom toralMass u (toralScaleReal d : ℂ)
            (cexpSeriesCarrier (toralAmplitude d) (toralFrequency d)) t i w ^ N)
          {z : ℂ | 0 < z.im} := by
  have hdense := dense_shiftUniform_perturbedOuterOrbit_pow toralAtom_injective
    toralMass_pos summable_toralMass (toralScaleReal d : ℂ)
    (expSeriesNormallySummable_toral d)
  exact hdense.nonempty

theorem toralOuterContinuousOn (u : MassParameter) :
    ContinuousOn (massOuterBackground toralAtom toralMass u) {z : ℂ | 0 < z.im} := by
  letI := isFiniteMeasure_massMeasure (x := toralAtom) toralMass_pos summable_toralMass u
  exact continuousOn_outerBackground _

def toralOrbit (d : ℕ) (u : MassParameter) : ℝ → C(UpperPlane, ℂ) :=
  perturbedOrbit (expSeriesNormallySummable_toral d)
    (massOuterBackground toralAtom toralMass u) (toralOuterContinuousOn u)
    (toralScaleReal d : ℂ)

def toralBoundary (d : ℕ) : (Fin d → Circle) → C(UpperPlane, ℂ) :=
  perturbedBoundary (expSeriesNormallySummable_toral d) (Complex.exp (-1))
    (toralScaleReal d : ℂ)

def toralOrbitPow (d : ℕ) (u : MassParameter) (N : ℕ) : ℝ → C(UpperPlane, ℂ) :=
  fun t => cmPow N (toralOrbit d u t)

def toralBoundaryPow (d N : ℕ) : (Fin d → Circle) → C(UpperPlane, ℂ) :=
  fun lam => cmPow N (toralBoundary d lam)

def toralUniformBound (d : ℕ) : ℝ := Real.exp 1 + toralScaleReal d * d

theorem toralUniformBound_nonneg (d : ℕ) : 0 ≤ toralUniformBound d := by
  unfold toralUniformBound
  exact add_nonneg (Real.exp_pos _).le
    (mul_nonneg (toralScaleReal_pos d).le (Nat.cast_nonneg d))

theorem norm_toralOrbit_le (d : ℕ) (u : MassParameter) (t : ℝ) (z : UpperPlane) :
    ‖toralOrbit d u t z‖ ≤ toralUniformBound d := by
  have hB : ∀ w ∈ {z : ℂ | 0 < z.im},
      ‖(toralScaleReal d : ℂ) *
        cexpSeriesCarrier (toralAmplitude d) (toralFrequency d) w‖
        ≤ toralScaleReal d * d := by
    intro w hw
    exact norm_toralBackground_le d hw
  have hz : 0 < ((z : ℂ) + (t : ℂ)).im := upperPlane_add_ofReal z t
  simpa [toralOrbit, perturbedOrbit_apply, massOuterBackground, toralUniformBound] using
    (norm_grafted_le toralMass_pos summable_toralMass u hB hz)

theorem norm_toralBoundary_le (d : ℕ) (lam : Fin d → Circle) (z : UpperPlane) :
    ‖toralBoundary d lam z‖ ≤ toralUniformBound d := by
  have he : ‖Complex.exp (-1)‖ ≤ Real.exp 1 := by
    rw [Complex.norm_exp]
    exact Real.exp_le_exp.mpr (by norm_num)
  have hc := norm_bohrHullMap_toral_le d lam z.2.le
  rw [toralBoundary, perturbedBoundary_apply]
  refine le_trans (norm_add_le _ _) ?_
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (toralScaleReal_pos d).le]
  exact add_le_add he (mul_le_mul_of_nonneg_left hc (toralScaleReal_pos d).le)

theorem tendsto_uniformity_toralOrbitPow (d : ℕ) (u : MassParameter) (N : ℕ) :
    Tendsto (fun t => (toralBoundaryPow d N (circlePhaseFlow (toralFrequency d) t),
        toralOrbitPow d u N t)) (cocompact ℝ) (uniformity C(UpperPlane, ℂ)) := by
  letI := isFiniteMeasure_massMeasure (x := toralAtom) toralMass_pos summable_toralMass u
  have hbase := tendsto_uniformity_perturbedOrbit (eps := (toralScaleReal d : ℂ))
    (expSeriesNormallySummable_toral d) (toralOuterContinuousOn u)
    (fun _ hK hKH => tendstoUniformlyOn_outerBackground_translate
      (massMeasure toralAtom toralMass u) hK hKH)
  exact tendsto_uniformity_cmPow_of_bound (toralUniformBound_nonneg d)
    (fun t z => norm_toralBoundary_le d (circlePhaseFlow (toralFrequency d) t) z)
    (fun t z => norm_toralOrbit_le d u t z) hbase N

theorem continuous_toralBoundaryPow (d N : ℕ) : Continuous (toralBoundaryPow d N) :=
  (continuous_cmPow N).comp
    (continuous_perturbedBoundary (expSeriesNormallySummable_toral d)
      (Complex.exp (-1)) (toralScaleReal d : ℂ))

theorem continuous_toralOrbitPow (d : ℕ) (u : MassParameter) (N : ℕ) :
    Continuous (toralOrbitPow d u N) :=
  (continuous_cmPow N).comp
    (continuous_perturbedOrbit (expSeriesNormallySummable_toral d)
      (toralOuterContinuousOn u) (toralScaleReal d : ℂ))

theorem closure_range_toralOrbitPow (d : ℕ) (u : MassParameter) (N : ℕ) :
    closure (Set.range (toralOrbitPow d u N)) =
      Set.range (toralOrbitPow d u N) ∪ Set.range (toralBoundaryPow d N) :=
  closure_range_eq_union_range (continuous_toralBoundaryPow d N)
    (continuous_toralOrbitPow d u N)
    (dense_forwardOrbit_circlePhaseFlow (rationallyIndependentSequence_toralFrequency d))
    (tendsto_uniformity_toralOrbitPow d u N)

theorem clusterAtInfinity_toralOrbitPow (d : ℕ) (u : MassParameter) (N : ℕ) :
    (⋂ M : ℝ, closure ((toralOrbitPow d u N) '' {t : ℝ | M < |t|})) =
      Set.range (toralBoundaryPow d N) :=
  clusterAtInfinity_eq_range (continuous_toralBoundaryPow d N)
    (dense_forwardOrbit_circlePhaseFlow (rationallyIndependentSequence_toralFrequency d))
    (tendsto_uniformity_toralOrbitPow d u N)

def toralBoundaryEntire (d : ℕ) (lam : Fin d → Circle) (z : ℂ) : ℂ :=
  Complex.exp (-1) + (toralScaleReal d : ℂ) *
    bohrHullMap (toralAmplitude d) (toralFrequency d)
      (expSeriesNormallySummable_toral d) lam z

theorem toralBoundaryEntire_restrict (d : ℕ) (lam : Fin d → Circle) (z : UpperPlane) :
    toralBoundaryEntire d lam z = toralBoundary d lam z := rfl

theorem differentiallyAlgebraic_toralBoundaryEntire (d : ℕ) (lam : Fin d → Circle) :
    DifferentiallyAlgebraic (toralBoundaryEntire d lam) := by
  let coeff : Fin d → ℂ := fun i => (toralScaleReal d : ℂ) * (lam i : ℂ)
  let freq : Fin d → ℂ := fun i => Complex.I * (toralFrequency d i : ℂ)
  have hsum0 := differentiallyAlgebraic_finset_expSum_general (Finset.univ : Finset (Fin d))
    coeff freq
  have hsum : DifferentiallyAlgebraic (fun z =>
      ∑ i : Fin d, (toralScaleReal d : ℂ) * (lam i : ℂ) *
        Complex.exp (Complex.I * z * (toralFrequency d i : ℂ))) := by
    convert hsum0 using 1
    funext z
    apply Finset.sum_congr rfl
    intro i _
    simp only [coeff, freq]
    congr 2
    ring_nf
  have hadd : DifferentiallyAlgebraic (fun z =>
      (∑ i : Fin d, (toralScaleReal d : ℂ) * (lam i : ℂ) *
        Complex.exp (Complex.I * z * (toralFrequency d i : ℂ))) + Complex.exp (-1)) :=
    (differentiallyAlgebraic_add_const_iff (Complex.exp (-1))).2 hsum
  have heq : toralBoundaryEntire d lam = fun z =>
      (∑ i : Fin d, (toralScaleReal d : ℂ) * (lam i : ℂ) *
        Complex.exp (Complex.I * z * (toralFrequency d i : ℂ))) + Complex.exp (-1) := by
    funext z
    simp only [toralBoundaryEntire, bohrHullMap_apply, cexpSeriesCarrier, cexpChar,
      tsum_fintype, toralAmplitude, one_mul]
    rw [Finset.mul_sum]
    rw [add_comm]
    apply congrArg (fun w : ℂ => w + Complex.exp (-1))
    apply Finset.sum_congr rfl
    intro i _
    ring_nf
  rw [heq]
  exact hadd

theorem differentiallyAlgebraic_toralBoundaryEntire_pow (d : ℕ)
    (lam : Fin d → Circle) (N : ℕ) :
    DifferentiallyAlgebraic (fun z => toralBoundaryEntire d lam z ^ N) := by
  have hdiff : Differentiable ℂ (toralBoundaryEntire d lam) := by
    have hphase := expSeriesNormallySummable_phase (expSeriesNormallySummable_toral d)
      fun i => le_of_eq (Circle.norm_coe (lam i))
    have hcarrier : Differentiable ℂ (fun z =>
        bohrHullMap (toralAmplitude d) (toralFrequency d)
          (expSeriesNormallySummable_toral d) lam z) := by
      change Differentiable ℂ
        (cexpSeriesCarrier (fun i => toralAmplitude d i * (lam i : ℂ))
          (toralFrequency d))
      exact differentiable_cexpSeriesCarrier hphase
    exact Differentiable.add (by fun_prop) (Differentiable.mul (by fun_prop) hcarrier)
  exact differentiallyAlgebraic_pow
    (hdiff.differentiableOn.analyticOnNhd isOpen_univ)
    (differentiallyAlgebraic_toralBoundaryEntire d lam) N

theorem toralBoundaryEntire_ne_zero_upper (d : ℕ) (lam : Fin d → Circle)
    {z : ℂ} (hz : 0 < z.im) : toralBoundaryEntire d lam z ≠ 0 := by
  intro hzero
  rw [toralBoundaryEntire] at hzero
  have heq : Complex.exp (-1) = -((toralScaleReal d : ℂ) *
      bohrHullMap (toralAmplitude d) (toralFrequency d)
        (expSeriesNormallySummable_toral d) lam z) := by
    linear_combination hzero
  have hnorm := congrArg norm heq
  rw [norm_neg, Complex.norm_exp] at hnorm
  norm_num at hnorm
  have hle : ‖(toralScaleReal d : ℂ) *
      bohrHullMap (toralAmplitude d) (toralFrequency d)
        (expSeriesNormallySummable_toral d) lam z‖ ≤ toralScaleReal d * d := by
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (toralScaleReal_pos d).le]
    exact mul_le_mul_of_nonneg_left (norm_bohrHullMap_toral_le d lam hz.le)
      (toralScaleReal_pos d).le
  rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (toralScaleReal_pos d).le] at hle
  rw [abs_of_pos (toralScaleReal_pos d)] at hnorm
  linarith [toralScaleReal_mul_lt d]

def toralVerticalPoint (k : ℕ) : UpperPlane :=
  ⟨Complex.I + (k : ℂ) * Complex.I, by simp; positivity⟩

theorem tendsto_toralBoundary_vertical (d : ℕ) (lam : Fin d → Circle) :
    Tendsto (fun k => toralBoundary d lam (toralVerticalPoint k)) atTop
      (nhds (Complex.exp (-1))) := by
  have hphase := expSeriesNormallySummable_phase (expSeriesNormallySummable_toral d)
    fun i => le_of_eq (Circle.norm_coe (lam i))
  rw [Metric.tendsto_atTop]
  intro e he
  let delta : ℝ := e / (toralScaleReal d + 1)
  have hdelta : 0 < delta := div_pos he (by linarith [toralScaleReal_pos d])
  obtain ⟨Y, hY0, hY⟩ := exists_im_bound_norm_cexpSeriesCarrier_le hphase
    (toralFrequency_pos d) hdelta
  obtain ⟨K, hK⟩ := exists_nat_gt Y
  refine ⟨K, fun k hk => ?_⟩
  have hKY : Y ≤ ((toralVerticalPoint k : UpperPlane) : ℂ).im := by
    change Y ≤ (Complex.I + (k : ℂ) * Complex.I).im
    simp only [Complex.add_im, Complex.I_im, Complex.mul_im, Complex.natCast_re,
      Complex.I_re, Complex.natCast_im, mul_one, zero_mul, add_zero]
    have hKR : (K : ℝ) ≤ k := by exact_mod_cast hk
    linarith
  have hcarr := hY ((toralVerticalPoint k : UpperPlane) : ℂ) hKY
  rw [toralBoundary, perturbedBoundary_apply, dist_eq_norm]
  have heq :
      (Complex.exp (-1) + (toralScaleReal d : ℂ) *
        bohrHullMap (toralAmplitude d) (toralFrequency d)
          (expSeriesNormallySummable_toral d) lam (toralVerticalPoint k : ℂ)) -
        Complex.exp (-1) =
      (toralScaleReal d : ℂ) *
        cexpSeriesCarrier (fun i => toralAmplitude d i * (lam i : ℂ))
          (toralFrequency d) (toralVerticalPoint k : ℂ) := by
    rw [bohrHullMap_apply]
    ring_nf
  rw [heq, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (toralScaleReal_pos d).le]
  refine lt_of_le_of_lt (mul_le_mul_of_nonneg_left hcarr (toralScaleReal_pos d).le) ?_
  dsimp [delta]
  rw [mul_div_assoc']
  rw [div_lt_iff₀ (by linarith [toralScaleReal_pos d])]
  nlinarith [he]

theorem injective_toralBoundaryPow (d N : ℕ) (hN : N ≠ 0) :
    Function.Injective (toralBoundaryPow d N) := by
  letI : PreconnectedSpace UpperPlane :=
    Subtype.preconnectedSpace (by
      simpa [upperHalfPlaneSet] using isPreconnected_upperHalfPlaneSet)
  letI : Nonempty UpperPlane := ⟨⟨Complex.I, by simp⟩⟩
  intro lam mu hpow
  have hpoint : ∀ z : UpperPlane,
      toralBoundary d lam z ^ N = toralBoundary d mu z ^ N := by
    intro z
    exact congrArg (fun f : C(UpperPlane, ℂ) => f z) hpow
  have hmu : ∀ z : UpperPlane, toralBoundary d mu z ≠ 0 := by
    intro z
    exact toralBoundaryEntire_ne_zero_upper d mu z.2
  have hratio : Tendsto (fun k =>
      toralBoundary d lam (toralVerticalPoint k) /
        toralBoundary d mu (toralVerticalPoint k)) atTop (nhds 1) := by
    have hdiv := (tendsto_toralBoundary_vertical d lam).div
      (tendsto_toralBoundary_vertical d mu) (Complex.exp_ne_zero _)
    rwa [div_self (Complex.exp_ne_zero _)] at hdiv
  have heqfun : (fun z : UpperPlane => toralBoundary d lam z) =
      fun z : UpperPlane => toralBoundary d mu z :=
    eq_of_pow_eq_of_tendsto_ratio_one hN
      (toralBoundary d lam).continuous (toralBoundary d mu).continuous
      hmu hpoint hratio
  apply injective_perturbedBoundary (expSeriesNormallySummable_toral d)
    (Complex.exp (-1)) (show (toralScaleReal d : ℂ) ≠ 0 by
      exact_mod_cast (toralScaleReal_pos d).ne')
    (toralAmplitude_ne_zero d)
    (injective_of_rationallyIndependentSequence
      (rationallyIndependentSequence_toralFrequency d))
  exact ContinuousMap.ext (congrFun heqfun)

theorem isClosedEmbedding_toralBoundaryPow (d N : ℕ) (hN : N ≠ 0) :
    Topology.IsClosedEmbedding (toralBoundaryPow d N) :=
  (continuous_toralBoundaryPow d N).isClosedEmbedding (injective_toralBoundaryPow d N hN)

theorem isCompact_range_toralBoundaryPow (d N : ℕ) :
    IsCompact (Set.range (toralBoundaryPow d N)) := by
  simpa only [Set.image_univ] using
    (isCompact_univ.image (continuous_toralBoundaryPow d N))

theorem disjoint_toralOrbitPow_toralBoundaryPow (d : ℕ) (u : MassParameter)
    (hu : ∀ (N : ℕ), N ≠ 0 → ∀ (m' : ℕ) (t : Fin (m' + 1) → ℝ),
      Function.Injective t → ¬ FamilyDifferentiallyAlgebraicOn
        (fun i w => perturbedOuterFamily toralAtom toralMass u (toralScaleReal d : ℂ)
          (cexpSeriesCarrier (toralAmplitude d) (toralFrequency d)) t i w ^ N)
        {z : ℂ | 0 < z.im})
    (N : ℕ) (hN : N ≠ 0) :
    Disjoint (Set.range (toralOrbitPow d u N)) (Set.range (toralBoundaryPow d N)) := by
  rw [Set.disjoint_left]
  rintro f ⟨t, rfl⟩ ⟨lam, hlam⟩
  let shift : Fin 1 → ℝ := fun _ => t
  have hshift : Function.Injective shift := fun i j _ => Subsingleton.elim i j
  have hDA := differentiallyAlgebraic_toralBoundaryEntire_pow d lam N
  have hOn : DifferentiallyAlgebraicOn (fun z => toralBoundaryEntire d lam z ^ N)
      {z : ℂ | 0 < z.im} := by
    obtain ⟨n, P, hP, hrel⟩ := hDA
    exact ⟨n, P, hP, fun z _ => hrel z⟩
  have heqOn : Set.EqOn (fun z => toralBoundaryEntire d lam z ^ N)
      (fun z => perturbedOuterFamily toralAtom toralMass u (toralScaleReal d : ℂ)
        (cexpSeriesCarrier (toralAmplitude d) (toralFrequency d)) shift 0 z ^ N)
      {z : ℂ | 0 < z.im} := by
    intro z hz
    have hv := congrArg (fun g : C(UpperPlane, ℂ) => g ⟨z, hz⟩) hlam
    change toralBoundary d lam ⟨z, hz⟩ ^ N = toralOrbit d u t ⟨z, hz⟩ ^ N at hv
    calc
      toralBoundaryEntire d lam z ^ N = toralBoundary d lam ⟨z, hz⟩ ^ N := by rfl
      _ = toralOrbit d u t ⟨z, hz⟩ ^ N := hv
      _ = perturbedOuterFamily toralAtom toralMass u (toralScaleReal d : ℂ)
          (cexpSeriesCarrier (toralAmplitude d) (toralFrequency d)) shift 0 z ^ N := by
        rfl
  have hOne := DifferentiallyAlgebraicOn.congr isOpen_upperHalfSet heqOn hOn
  have hFamilyOne := (familyDifferentiallyAlgebraicOn_one_iff
    (fun z => perturbedOuterFamily toralAtom toralMass u (toralScaleReal d : ℂ)
      (cexpSeriesCarrier (toralAmplitude d) (toralFrequency d)) shift 0 z ^ N)
    {z : ℂ | 0 < z.im}).2 hOne
  have hFamily : FamilyDifferentiallyAlgebraicOn
      (fun i w => perturbedOuterFamily toralAtom toralMass u (toralScaleReal d : ℂ)
        (cexpSeriesCarrier (toralAmplitude d) (toralFrequency d)) shift i w ^ N)
      {z : ℂ | 0 < z.im} := by
    convert hFamilyOne using 1
    funext i w
    congr 2
    exact Subsingleton.elim i 0
  exact hu N hN 0 shift hshift hFamily

def toralAnalyticBackground (d : ℕ) (z : ℂ) : ℂ :=
  (toralScaleReal d : ℂ) *
    cexpSeriesCarrier (toralAmplitude d) (toralFrequency d) z

theorem differentiableOn_toralAnalyticBackground (d : ℕ) :
    DifferentiableOn ℂ (toralAnalyticBackground d) {z : ℂ | 0 < z.im} := by
  exact (Differentiable.mul (by fun_prop)
    (differentiable_cexpSeriesCarrier (expSeriesNormallySummable_toral d))).differentiableOn

theorem norm_toralAnalyticBackground_le (d : ℕ) :
    ∀ z ∈ {w : ℂ | 0 < w.im},
      ‖toralAnalyticBackground d z‖ ≤ toralScaleReal d * d := by
  intro z hz
  exact norm_toralBackground_le d hz

def toralGraftedMultiplier (d : ℕ) (u : MassParameter) : DiskMultiplier :=
  graftedMultiplier toralAtom (ε := toralMass) toralMass_pos summable_toralMass u
    (differentiableOn_toralAnalyticBackground d) (norm_toralAnalyticBackground_le d)

def toralGraftedInvMultiplier (d : ℕ) (u : MassParameter) : DiskMultiplier :=
  graftedInvMultiplier (x := toralAtom) (ε := toralMass) toralAtom_injective toralMass_pos
    summable_toralMass u (differentiableOn_toralAnalyticBackground d)
    (norm_toralAnalyticBackground_le d) (toralScaleReal_mul_lt d)

theorem toralGraftedMultiplier_mul_inv (d : ℕ) (u : MassParameter) {w : ℂ}
    (hw : w ∈ Metric.ball (0 : ℂ) 1) :
    (toralGraftedMultiplier d u).fn w * (toralGraftedInvMultiplier d u).fn w = 1 := by
  exact mul_inv_cancel₀ (graftedDisk_ne_zero toralAtom_injective toralMass_pos
    summable_toralMass u (norm_toralAnalyticBackground_le d) (toralScaleReal_mul_lt d) hw)

/-- Closed card theorem: every positive finite dimension has one bounded invertible Hardy-outer
source whose every positive-power finite translation packet is differentially free, while every
power boundary is a faithfully embedded DA torus, exactly the compact-open boundary and exactly the
cluster set at infinity. -/
theorem toral_da_boundary_maximal_ht_outer_orbit_complete :
    ∀ d : ℕ, d ≠ 0 → ∃ u : MassParameter,
      (∀ w : ℂ, w ∈ Metric.ball (0 : ℂ) 1 →
        (toralGraftedMultiplier d u).fn w * (toralGraftedInvMultiplier d u).fn w = 1) ∧
      cyclicSubspace (hardyOf (toralGraftedMultiplier d u)) = ⊤ ∧
      (∀ z : ℂ, 0 < z.im →
        Real.exp (-1) - toralScaleReal d * d ≤
          ‖massOuterBackground toralAtom toralMass u z + toralAnalyticBackground d z‖ ∧
        ‖massOuterBackground toralAtom toralMass u z + toralAnalyticBackground d z‖ ≤
          toralUniformBound d) ∧
      ∀ N : ℕ, N ≠ 0 →
        (∀ (m' : ℕ) (t : Fin (m' + 1) → ℝ), Function.Injective t →
          ¬ FamilyDifferentiallyAlgebraicOn
            (fun i w => perturbedOuterFamily toralAtom toralMass u (toralScaleReal d : ℂ)
              (cexpSeriesCarrier (toralAmplitude d) (toralFrequency d)) t i w ^ N)
            {z : ℂ | 0 < z.im}) ∧
        (∀ lam : Fin d → Circle,
          DifferentiallyAlgebraic (fun z => toralBoundaryEntire d lam z ^ N)) ∧
        Topology.IsClosedEmbedding (toralBoundaryPow d N) ∧
        IsCompact (Set.range (toralBoundaryPow d N)) ∧
        closure (Set.range (toralOrbitPow d u N)) =
          Set.range (toralOrbitPow d u N) ∪ Set.range (toralBoundaryPow d N) ∧
        Disjoint (Set.range (toralOrbitPow d u N)) (Set.range (toralBoundaryPow d N)) ∧
        (⋂ M : ℝ, closure ((toralOrbitPow d u N) '' {t : ℝ | M < |t|})) =
          Set.range (toralBoundaryPow d N) := by
  intro d _hd
  obtain ⟨u, hu⟩ := exists_toralGoodMassParameter d
  refine ⟨u, (fun w hw => toralGraftedMultiplier_mul_inv d u hw), ?_, ?_, fun N hN => ?_⟩
  · exact cyclicSubspace_hardyOf_graftedMultiplier toralAtom_injective toralMass_pos
      summable_toralMass u (differentiableOn_toralAnalyticBackground d)
      (norm_toralAnalyticBackground_le d) (toralScaleReal_mul_lt d)
  · intro z hz
    constructor
    · exact norm_grafted_ge toralAtom_injective toralMass_pos summable_toralMass u
        (norm_toralAnalyticBackground_le d) hz
    · exact norm_grafted_le toralMass_pos summable_toralMass u
        (norm_toralAnalyticBackground_le d) hz
  · exact ⟨hu N hN,
      (fun lam => differentiallyAlgebraic_toralBoundaryEntire_pow d lam N),
      isClosedEmbedding_toralBoundaryPow d N hN,
      isCompact_range_toralBoundaryPow d N,
      closure_range_toralOrbitPow d u N,
      disjoint_toralOrbitPow_toralBoundaryPow d u hu N hN,
      clusterAtInfinity_toralOrbitPow d u N⟩

end

end GaloisForLFunctions.HTGeometry
