import GaloisForLFunctions.HTGeometry.BernsteinWidder
import GaloisForLFunctions.HTGeometry.RepairedFrequencyDensityLaplace

/-!
# Reservoir density complete-monotonicity / Markov equivalence

This file formalizes the exact three-way classification from the research card:

* compact positive Markov targets in the `y` coordinate;
* finite Laplace measures supported on `[a,∞)` in the `r = y⁻¹ᐟ²` coordinate;
* continuous complete monotonicity of `H` and of one positive exponential shift `exp(a·) H`.

The analytic existence input is the unconditional Bernstein--Widder theorem in
`BernsteinWidder.lean`; all remaining work here is exact support and coordinate transport.
-/

open MeasureTheory Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Condition 2 of the card: finite positive Laplace representation with support bounded away
from zero. -/
def HasLowerSupportedLaplaceProfile (H : ℝ → ℝ) : Prop :=
  ∃ a : ℝ, 0 < a ∧ ∃ tau : Measure ℝ, IsFiniteMeasure tau ∧
    tau (Ici a)ᶜ = 0 ∧
    ∀ t : ℝ, 0 < t → H t = finiteRealLaplace tau t

/-- Condition 3 of the card: complete monotonicity, finite zero limit, and complete monotonicity
after one positive exponential shift. -/
def HasShiftedCompletelyMonotoneProfile (H : ℝ → ℝ) : Prop :=
  CompletelyMonotoneOn H ∧
    ∃ L : ℝ, Tendsto H (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 L) ∧
      ∃ a : ℝ, 0 < a ∧ CompletelyMonotoneOn (fun t => Real.exp (a * t) * H t)

/-- Translate a lower-supported Laplace source down to the nonnegative half-line. -/
def laplaceShiftDown (a : ℝ) (tau : Measure ℝ) : Measure ℝ :=
  Measure.map (fun r : ℝ => r - a) tau

/-- Translate a nonnegative Laplace source up to `[a,∞)`. -/
def laplaceShiftUp (a : ℝ) (sigma : Measure ℝ) : Measure ℝ :=
  Measure.map (fun u : ℝ => u + a) sigma

instance laplaceShiftDown_isFinite (a : ℝ) (tau : Measure ℝ) [IsFiniteMeasure tau] :
    IsFiniteMeasure (laplaceShiftDown a tau) := Measure.isFiniteMeasure_map _ _

instance laplaceShiftUp_isFinite (a : ℝ) (sigma : Measure ℝ) [IsFiniteMeasure sigma] :
    IsFiniteMeasure (laplaceShiftUp a sigma) := Measure.isFiniteMeasure_map _ _

theorem laplaceShiftDown_carried_Ici {a : ℝ} {tau : Measure ℝ}
    (htau : tau (Ici a)ᶜ = 0) : laplaceShiftDown a tau (Ici (0 : ℝ))ᶜ = 0 := by
  rw [laplaceShiftDown, Measure.map_apply (by fun_prop) measurableSet_Ici.compl]
  apply measure_mono_null _ htau
  intro r hr
  simp only [mem_preimage, mem_compl_iff, mem_Ici, not_le] at hr ⊢
  linarith

theorem laplaceShiftUp_carried_Ici {a : ℝ} {sigma : Measure ℝ}
    (hsigma : sigma (Ici (0 : ℝ))ᶜ = 0) : laplaceShiftUp a sigma (Ici a)ᶜ = 0 := by
  rw [laplaceShiftUp, Measure.map_apply (by fun_prop) measurableSet_Ici.compl]
  apply measure_mono_null _ hsigma
  intro u hu
  simp only [mem_preimage, mem_compl_iff, mem_Ici, not_le] at hu ⊢
  linarith

theorem finiteRealLaplace_laplaceShiftDown
    (a : ℝ) (tau : Measure ℝ) [IsFiniteMeasure tau] (t : ℝ) :
    finiteRealLaplace (laplaceShiftDown a tau) t =
      Real.exp (a * t) * finiteRealLaplace tau t := by
  rw [finiteRealLaplace, laplaceShiftDown, integral_map (by fun_prop)]
  · rw [finiteRealLaplace, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with r
    rw [← Real.exp_add]
    congr 1
    ring
  · fun_prop

theorem finiteRealLaplace_laplaceShiftUp
    (a : ℝ) (sigma : Measure ℝ) [IsFiniteMeasure sigma] (t : ℝ) :
    finiteRealLaplace (laplaceShiftUp a sigma) t =
      Real.exp (-a * t) * finiteRealLaplace sigma t := by
  rw [finiteRealLaplace, laplaceShiftUp, integral_map (by fun_prop)]
  · rw [finiteRealLaplace, ← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with u
    rw [← Real.exp_add]
    congr 1
    ring
  · fun_prop

theorem lowerSupportedLaplaceProfile_imp_shiftedCompletelyMonotoneProfile
    {H : ℝ → ℝ} (hH : HasLowerSupportedLaplaceProfile H) :
    HasShiftedCompletelyMonotoneProfile H := by
  obtain ⟨a, ha, tau, htauFinite, htauSupport, hLaplace⟩ := hH
  letI : IsFiniteMeasure tau := htauFinite
  have htau0 : tau (Ici (0 : ℝ))ᶜ = 0 := by
    apply measure_mono_null _ htauSupport
    intro r hr
    simp only [mem_compl_iff, mem_Ici, not_le] at hr ⊢
    linarith
  have hEq : EqOn (finiteRealLaplace tau) H (Ioi 0) := fun t ht =>
    (hLaplace t ht).symm
  have hCM : CompletelyMonotoneOn H :=
    (completelyMonotoneOn_finiteRealLaplace tau htau0).congr_Ioi hEq
  have hlimLaplace := tendsto_finiteRealLaplace_nhdsGT_zero tau htau0
  have hlim : Tendsto H (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 (tau Set.univ).toReal) :=
    hlimLaplace.congr' <| by
      filter_upwards [self_mem_nhdsWithin] with t ht
      exact hEq ht
  let sigma := laplaceShiftDown a tau
  have hsigma0 : sigma (Ici (0 : ℝ))ᶜ = 0 := laplaceShiftDown_carried_Ici htauSupport
  have hShiftEq : EqOn (finiteRealLaplace sigma)
      (fun t => Real.exp (a * t) * H t) (Ioi 0) := by
    intro t ht
    dsimp [sigma]
    rw [finiteRealLaplace_laplaceShiftDown, ← hLaplace t ht]
  have hShiftCM : CompletelyMonotoneOn (fun t => Real.exp (a * t) * H t) :=
    (completelyMonotoneOn_finiteRealLaplace sigma hsigma0).congr_Ioi hShiftEq
  exact ⟨hCM, (tau Set.univ).toReal, hlim, a, ha, hShiftCM⟩

theorem shiftedCompletelyMonotoneProfile_imp_lowerSupportedLaplaceProfile
    {H : ℝ → ℝ} (hH : HasShiftedCompletelyMonotoneProfile H) :
    HasLowerSupportedLaplaceProfile H := by
  obtain ⟨_hCM, L, hlim, a, ha, hShiftCM⟩ := hH
  let G : ℝ → ℝ := fun t => Real.exp (a * t) * H t
  have hexp : Tendsto (fun t : ℝ => Real.exp (a * t))
      (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 1) := by
    have hc : Continuous (fun t : ℝ => Real.exp (a * t)) := by fun_prop
    change Tendsto (fun t : ℝ => Real.exp (a * t))
      (𝓝 (0 : ℝ) ⊓ Filter.principal (Ioi 0)) (𝓝 1)
    simpa using (hc.tendsto 0).mono_left inf_le_left
  have hGlim : Tendsto G (nhdsWithin (0 : ℝ) (Ioi 0)) (𝓝 L) := by
    simpa [G] using hexp.mul hlim
  obtain ⟨sigma, hsigmaFinite, hsigma0, hSigmaLaplace⟩ :=
    exists_finiteLaplaceMeasure_of_completelyMonotoneOn hShiftCM hGlim
  letI : IsFiniteMeasure sigma := hsigmaFinite
  let tau := laplaceShiftUp a sigma
  have htauSupport : tau (Ici a)ᶜ = 0 := laplaceShiftUp_carried_Ici hsigma0
  refine ⟨a, ha, tau, inferInstance, htauSupport, fun t ht => ?_⟩
  dsimp [tau]
  rw [finiteRealLaplace_laplaceShiftUp]
  have hsig : finiteRealLaplace sigma t = G t := by
    simpa [finiteRealLaplace] using (hSigmaLaplace t ht).symm
  rw [hsig]
  dsimp [G]
  rw [← mul_assoc, ← Real.exp_add]
  ring_nf
  simp

/-- Conditions 2 and 3 of the research card are equivalent. -/
theorem lowerSupportedLaplaceProfile_iff_shiftedCompletelyMonotoneProfile (H : ℝ → ℝ) :
    HasLowerSupportedLaplaceProfile H ↔ HasShiftedCompletelyMonotoneProfile H := by
  exact ⟨lowerSupportedLaplaceProfile_imp_shiftedCompletelyMonotoneProfile,
    shiftedCompletelyMonotoneProfile_imp_lowerSupportedLaplaceProfile⟩

/-! ## Compact Markov target / lower-supported Laplace equivalence -/

/-- Condition 1 of the card: the reservoir density of a finite positive target carried by some
compact interval `[0,R]`.  An atom at zero is allowed and is invisible to the positive reservoir
profile, exactly as in the paper statement. -/
def HasCompactMarkovReservoirProfile (h : ℝ → ℝ) : Prop :=
  ∃ R : ℝ, 0 < R ∧ ∃ nu : Measure ℝ, IsFiniteMeasure nu ∧
    nu (Icc 0 R)ᶜ = 0 ∧
    ∀ x : ℝ, 0 < x → h x = factorialMomentDensity nu x

theorem inverseSqrtPushforward_carried_Ici_invSqrt
    {nu : Measure ℝ} {R : ℝ} (hsupp : nu (Icc 0 R)ᶜ = 0) :
    inverseSqrtPushforward nu (Ici (Real.sqrt R)⁻¹)ᶜ = 0 := by
  rw [inverseSqrtPushforward, Measure.map_apply (by fun_prop) measurableSet_Ici.compl]
  rw [Measure.restrict_apply
    (measurableSet_Ici.compl.preimage (by fun_prop : Measurable fun y : ℝ => (Real.sqrt y)⁻¹))]
  apply measure_mono_null _ hsupp
  rintro y ⟨hybad, hypos⟩
  simp only [mem_preimage, mem_compl_iff, mem_Ici, not_le] at hybad
  simp only [mem_compl_iff, mem_Icc, not_and_or, not_le]
  right
  by_contra hyR
  have hyR' : y ≤ R := le_of_not_gt hyR
  have hsqrt : Real.sqrt y ≤ Real.sqrt R := Real.sqrt_le_sqrt hyR'
  have hsy : 0 < Real.sqrt y := Real.sqrt_pos.2 hypos
  have hinv : (Real.sqrt R)⁻¹ ≤ (Real.sqrt y)⁻¹ := inv_anti₀ hsy hsqrt
  exact (not_lt_of_ge hinv) hybad

theorem compactMarkovReservoirProfile_imp_lowerSupportedLaplaceProfile
    {h : ℝ → ℝ} (hh : HasCompactMarkovReservoirProfile h) :
    HasLowerSupportedLaplaceProfile (fun t => 2 * h (t ^ (2 : ℕ))) := by
  obtain ⟨R, hR, nu, hnuFinite, hsupp, hDensity⟩ := hh
  letI : IsFiniteMeasure nu := hnuFinite
  let tau := inverseSqrtPushforward nu
  letI : IsFiniteMeasure tau :=
    Measure.isFiniteMeasure_map (nu.restrict (Ioi 0)) (fun y : ℝ => (Real.sqrt y)⁻¹)
  have ha : 0 < (Real.sqrt R)⁻¹ := inv_pos.mpr (Real.sqrt_pos.2 hR)
  have htauSupport : tau (Ici (Real.sqrt R)⁻¹)ᶜ = 0 :=
    inverseSqrtPushforward_carried_Ici_invSqrt hsupp
  refine ⟨(Real.sqrt R)⁻¹, ha, tau, inferInstance, htauSupport, fun t ht => ?_⟩
  dsimp [tau]
  rw [finiteRealLaplace, ← factorialMomentDensity_laplace_inverseSqrtPushforward nu ht,
    hDensity (t ^ (2 : ℕ)) (sq_pos_of_pos ht)]

theorem inverseSqrtPushforward_map_inverseSquareReconstruction
    {tau : Measure ℝ} {a : ℝ} (ha : 0 < a) (htau : tau (Ici a)ᶜ = 0) :
    inverseSqrtPushforward (Measure.map inverseSquareReconstruction tau) = tau := by
  ext s hs
  rw [inverseSqrtPushforward, Measure.map_apply (by fun_prop) hs,
    Measure.restrict_apply (hs.preimage (by fun_prop)),
    Measure.map_apply measurable_inverseSquareReconstruction
      ((hs.preimage (by fun_prop)).inter measurableSet_Ioi)]
  apply measure_congr
  filter_upwards [ae_iff.mpr htau] with r hr
  have hrpos : 0 < r := lt_of_lt_of_le ha hr
  have hrecpos : 0 < inverseSquareReconstruction r := by
    unfold inverseSquareReconstruction
    positivity
  have hinverse : (Real.sqrt (inverseSquareReconstruction r))⁻¹ = r := by
    unfold inverseSquareReconstruction
    rw [Real.sqrt_sq_eq_abs, abs_of_pos (inv_pos.mpr hrpos), inv_inv]
  change ((((Real.sqrt (inverseSquareReconstruction r))⁻¹ ∈ s) ∧
    0 < inverseSquareReconstruction r) = (r ∈ s))
  apply propext
  simp only [hinverse, hrecpos, and_true]

theorem map_inverseSquareReconstruction_carried_Icc
    {tau : Measure ℝ} {a : ℝ} (ha : 0 < a) (htau : tau (Ici a)ᶜ = 0) :
    Measure.map inverseSquareReconstruction tau (Icc 0 (a⁻¹ ^ (2 : ℕ)))ᶜ = 0 := by
  rw [Measure.map_apply measurable_inverseSquareReconstruction measurableSet_Icc.compl]
  apply measure_mono_null _ htau
  intro r hr
  simp only [mem_preimage, mem_compl_iff, mem_Icc, not_and_or, not_le] at hr ⊢
  rcases hr with hneg | hlarge
  · exact (not_lt_of_ge (sq_nonneg r⁻¹) hneg).elim
  · have hnle : ¬a ≤ r := by
      intro hra
      have hrpos : 0 < r := lt_of_lt_of_le ha hra
      have hinv : r⁻¹ ≤ a⁻¹ := inv_anti₀ ha hra
      have hsquare : r⁻¹ ^ (2 : ℕ) ≤ a⁻¹ ^ (2 : ℕ) :=
        pow_le_pow_left₀ (inv_nonneg.mpr hrpos.le) hinv 2
      exact (not_lt_of_ge hsquare) hlarge
    exact fun hra => hnle hra

theorem lowerSupportedLaplaceProfile_imp_compactMarkovReservoirProfile
    {H : ℝ → ℝ} (hH : HasLowerSupportedLaplaceProfile H) :
    HasCompactMarkovReservoirProfile (fun x => H (Real.sqrt x) / 2) := by
  obtain ⟨a, ha, tau, htauFinite, htauSupport, hLaplace⟩ := hH
  letI : IsFiniteMeasure tau := htauFinite
  let nu := Measure.map inverseSquareReconstruction tau
  letI : IsFiniteMeasure nu := Measure.isFiniteMeasure_map _ _
  have hR : 0 < a⁻¹ ^ (2 : ℕ) := sq_pos_of_pos (inv_pos.mpr ha)
  have hnuSupport : nu (Icc 0 (a⁻¹ ^ (2 : ℕ)))ᶜ = 0 :=
    map_inverseSquareReconstruction_carried_Icc ha htauSupport
  refine ⟨a⁻¹ ^ (2 : ℕ), hR, nu, inferInstance, hnuSupport, fun x hx => ?_⟩
  have hsqrt : 0 < Real.sqrt x := Real.sqrt_pos.2 hx
  have hpush : inverseSqrtPushforward nu = tau := by
    dsimp [nu]
    exact inverseSqrtPushforward_map_inverseSquareReconstruction ha htauSupport
  have hlaplace := factorialMomentDensity_laplace_inverseSqrtPushforward nu hsqrt
  rw [hpush] at hlaplace
  have hHsqrt := hLaplace (Real.sqrt x) hsqrt
  rw [finiteRealLaplace] at hHsqrt
  rw [Real.sq_sqrt hx.le] at hlaplace
  linarith

/-- Conditions 1 and 2 in the card, with `H(t)=2h(t²)`, are equivalent. -/
theorem compactMarkovReservoirProfile_iff_lowerSupportedLaplaceProfile (h : ℝ → ℝ) :
    HasCompactMarkovReservoirProfile h ↔
      HasLowerSupportedLaplaceProfile (fun t => 2 * h (t ^ (2 : ℕ))) := by
  constructor
  · exact compactMarkovReservoirProfile_imp_lowerSupportedLaplaceProfile
  · intro hLaplace
    have hcompact := lowerSupportedLaplaceProfile_imp_compactMarkovReservoirProfile hLaplace
    obtain ⟨R, hR, nu, hnuFinite, hsupp, hDensity⟩ := hcompact
    refine ⟨R, hR, nu, hnuFinite, hsupp, fun x hx => ?_⟩
    have hd := hDensity x hx
    change 2 * h (Real.sqrt x ^ (2 : ℕ)) / 2 = factorialMomentDensity nu x at hd
    rw [Real.sq_sqrt hx.le] at hd
    linarith

/-- Full three-way reservoir-density classification from the research card. -/
theorem compactMarkovReservoirProfile_iff_shiftedCompletelyMonotoneProfile (h : ℝ → ℝ) :
    HasCompactMarkovReservoirProfile h ↔
      HasShiftedCompletelyMonotoneProfile (fun t => 2 * h (t ^ (2 : ℕ))) := by
  rw [compactMarkovReservoirProfile_iff_lowerSupportedLaplaceProfile,
    lowerSupportedLaplaceProfile_iff_shiftedCompletelyMonotoneProfile]

end

end GaloisForLFunctions.HTGeometry
