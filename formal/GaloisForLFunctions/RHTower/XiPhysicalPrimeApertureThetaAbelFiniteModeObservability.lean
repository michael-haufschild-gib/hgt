import GaloisForLFunctions.RHTower.XiPhysicalPrimeApertureThetaAbelModeRateWall
import GaloisForLFunctions.RHTower.ExponentialPolynomialIntervalMoments
import GaloisForLFunctions.HTGeometry.GramPairingCauchySchwarz

/-!
# Finite-mode observability for physical theta--Abel apertures

Strict interval Gram positivity and a dual Cauchy--Schwarz extractor make every coordinate of a
finite distinct exponential packet observable from its coherent aperture `L²` mass. Applied after
the exact theta--Abel factorization, this rules out cancellation among any finite zero packet as a
mechanism for hiding one supercritical mode. Infinite-tail uniformity is deliberately not assumed.
-/

open MeasureTheory Set Filter Topology
open scoped BigOperators ComplexOrder

namespace RHTower

noncomputable section

/-- Finite combination of exponential-polynomial interval features. -/
def exponentialPolynomialIntervalCombination
    {r : ℕ} (lambda : Fin r → ℂ) (mult : Fin r → ℕ)
    (x : Fin (∑ i, mult i) → ℂ) (s : ℝ) : ℂ :=
  ∑ k, x k * exponentialPolynomialRealFeature lambda mult k s

/-- Every coordinate of a finite distinct-node exponential-polynomial packet is uniformly
observable from its `L²` mass on a nondegenerate interval. -/
theorem exists_exponentialPolynomialInterval_coordinate_observability
    {r : ℕ} {lambda : Fin r → ℂ} (hlambda : Function.Injective lambda)
    (mult : Fin r → ℕ) {a b : ℝ} (hab : a < b)
    (j : Fin (∑ i, mult i)) :
    ∃ C : ℝ, 0 < C ∧ ∀ x : Fin (∑ i, mult i) → ℂ,
      ‖x j‖ ^ 2 ≤ C *
        ∫ s : ℝ in Set.Icc a b,
          ‖exponentialPolynomialIntervalCombination lambda mult x s‖ ^ 2 := by
  classical
  let y : Fin (∑ i, mult i) → ℂ := Pi.single j 1
  obtain ⟨d, hd⟩ := Matrix.mulVec_surjective_iff_isUnit.mpr
    (exponentialPolynomialIntervalGram_posDef hlambda mult hab).isUnit y
  let g : ℝ → ℂ := fun s => ∑ k, d k *
    (starRingEnd ℂ) (exponentialPolynomialRealFeature lambda mult k s)
  have hfeature (k : Fin (∑ i, mult i)) :
      Continuous (exponentialPolynomialRealFeature lambda mult k) :=
    (contDiff_exponentialPolynomialMode lambda mult k 1).continuous.comp
      Complex.continuous_ofReal
  have hgcont : Continuous g := by
    dsimp only [g]
    fun_prop
  have hdelta (i : Fin (∑ q, mult q)) :
      (∫ s : ℝ in Set.Icc a b,
        exponentialPolynomialRealFeature lambda mult i s * g s) = y i := by
    have hmoment := congrFun
      (exponentialPolynomialMoment_intervalSynthesis lambda mult a b d) i
    rw [hd] at hmoment
    rw [exponentialPolynomialMoment] at hmoment
    have hindicator :
        (fun s : ℝ => exponentialPolynomialRealFeature lambda mult i s *
          Set.indicator (Set.Icc a b) g s) =
        Set.indicator (Set.Icc a b) (fun s : ℝ =>
          exponentialPolynomialRealFeature lambda mult i s * g s) := by
      funext s
      exact (Set.indicator_mul_right (Set.Icc a b)
        (fun t => exponentialPolynomialRealFeature lambda mult i t) g).symm
    change (∫ s : ℝ, exponentialPolynomialRealFeature lambda mult i s *
      Set.indicator (Set.Icc a b) g s) = y i at hmoment
    rw [hindicator, MeasureTheory.integral_indicator measurableSet_Icc] at hmoment
    exact hmoment
  have hcombcont (x : Fin (∑ i, mult i) → ℂ) :
      Continuous (exponentialPolynomialIntervalCombination lambda mult x) := by
    change Continuous (fun s : ℝ =>
      ∑ k, x k * exponentialPolynomialRealFeature lambda mult k s)
    fun_prop
  have hpair (x : Fin (∑ i, mult i) → ℂ) :
      (∫ s : ℝ in Set.Icc a b,
        exponentialPolynomialIntervalCombination lambda mult x s * g s) = x j := by
    change (∫ s : ℝ in Set.Icc a b,
      (∑ k, x k * exponentialPolynomialRealFeature lambda mult k s) * g s) = x j
    simp_rw [Finset.sum_mul]
    rw [MeasureTheory.integral_finsetSum]
    · calc
        (∑ k, ∫ s : ℝ in Set.Icc a b,
            x k * exponentialPolynomialRealFeature lambda mult k s * g s) =
            ∑ k, x k * y k := by
              apply Finset.sum_congr rfl
              intro k hk
              rw [show (fun s : ℝ =>
                    x k * exponentialPolynomialRealFeature lambda mult k s * g s) =
                  fun s : ℝ => x k *
                    (exponentialPolynomialRealFeature lambda mult k s * g s) by
                    funext s; ring,
                MeasureTheory.integral_const_mul, hdelta]
        _ = x j := by
          rw [Finset.sum_eq_single j]
          · simp [y]
          · intro k hk hkj
            simp [y, hkj]
          · simp
    · intro k hk
      exact ((hfeature k).const_mul (x k) |>.mul hgcont).continuousOn.integrableOn_Icc
  let E : ℝ := ∫ s : ℝ in Set.Icc a b, ‖g s‖ ^ 2
  let C : ℝ := max 1 E
  have hC : 0 < C := lt_of_lt_of_le zero_lt_one (le_max_left 1 E)
  refine ⟨C, hC, fun x => ?_⟩
  have hfsq : Integrable
      (fun s : ℝ => ‖exponentialPolynomialIntervalCombination lambda mult x s‖ ^ 2)
      (volume.restrict (Set.Icc a b)) :=
    (hcombcont x).norm.pow 2 |>.continuousOn.integrableOn_Icc
  have hgsq : Integrable (fun s : ℝ => ‖(starRingEnd ℂ) (g s)‖ ^ 2)
      (volume.restrict (Set.Icc a b)) := by
    have hconj : Continuous (fun s : ℝ => (starRingEnd ℂ) (g s)) := by fun_prop
    exact hconj.norm.pow 2 |>.continuousOn.integrableOn_Icc
  have hcs :=
    GaloisForLFunctions.HTGeometry.norm_integral_mul_conj_sq_le
      (ν := volume.restrict (Set.Icc a b))
      (f := exponentialPolynomialIntervalCombination lambda mult x)
      (g := fun s : ℝ => (starRingEnd ℂ) (g s))
      (hcombcont x).norm.aestronglyMeasurable
      (by fun_prop : Continuous (fun s : ℝ => ‖(starRingEnd ℂ) (g s)‖)).aestronglyMeasurable
      hfsq hgsq
  have hcs' : ‖x j‖ ^ 2 ≤
      (∫ s : ℝ in Set.Icc a b,
        ‖exponentialPolynomialIntervalCombination lambda mult x s‖ ^ 2) * E := by
    have hpair' : (∫ s : ℝ in Set.Icc a b,
        exponentialPolynomialIntervalCombination lambda mult x s *
          (starRingEnd ℂ) ((starRingEnd ℂ) (g s))) = x j := by
      simpa using hpair x
    rw [hpair'] at hcs
    simpa [E] using hcs
  have henergy : 0 ≤ ∫ s : ℝ in Set.Icc a b,
      ‖exponentialPolynomialIntervalCombination lambda mult x s‖ ^ 2 :=
    integral_nonneg fun s => sq_nonneg _
  calc
    ‖x j‖ ^ 2 ≤
        (∫ s : ℝ in Set.Icc a b,
          ‖exponentialPolynomialIntervalCombination lambda mult x s‖ ^ 2) * E := hcs'
    _ ≤ (∫ s : ℝ in Set.Icc a b,
          ‖exponentialPolynomialIntervalCombination lambda mult x s‖ ^ 2) * C :=
      mul_le_mul_of_nonneg_left (le_max_right 1 E) henergy
    _ = C * (∫ s : ℝ in Set.Icc a b,
          ‖exponentialPolynomialIntervalCombination lambda mult x s‖ ^ 2) := mul_comm _ _

/-- Every slot in a unit-multiplicity confluent family has polynomial order zero. -/
@[simp] theorem gammaJetSlotOrder_one
    {r : ℕ} (k : Fin (∑ _i : Fin r, 1)) :
    GaloisForLFunctions.gammaJetSlotOrder (fun _i : Fin r => 1) k = 0 := by
  unfold GaloisForLFunctions.gammaJetSlotOrder
  exact congrArg Fin.val (Fin.eq_zero _)

/-- Unit-multiplicity slots are separated by their node coordinate. -/
theorem gammaJetSlotNode_one_injective {r : ℕ} :
    Function.Injective
      (GaloisForLFunctions.gammaJetSlotNode (fun _i : Fin r => 1)) := by
  intro k l hkl
  apply (GaloisForLFunctions.gammaJetSlotOrderIso (fun _i : Fin r => 1)).injective
  apply Sigma.ext hkl
  have hk0 :
      ((GaloisForLFunctions.gammaJetSlotOrderIso (fun _i : Fin r => 1) k).2) =
        (0 : Fin 1) := Fin.eq_zero _
  have hl0 :
      ((GaloisForLFunctions.gammaJetSlotOrderIso (fun _i : Fin r => 1) l).2) =
        (0 : Fin 1) := Fin.eq_zero _
  exact heq_of_eq (hk0.trans hl0.symm)

/-- Coefficient vector of a finite theta--Abel mode packet after exact response factorization. -/
def xiPhysicalThetaAbelFiniteModeCoefficient
    {r : ℕ} (z a : Fin r → ℂ) (c m : ℝ)
    (k : Fin (∑ _i : Fin r, 1)) : ℂ :=
  let i := GaloisForLFunctions.gammaJetSlotNode (fun _i : Fin r => 1) k
  a i * xiPhysicalLogWindowModeMultiplier c (z i) * ((z i + 1) / z i) *
    Complex.exp (z i * (m : ℂ))

/-- Height-independent coefficient of one selected finite theta--Abel packet mode. -/
def xiPhysicalThetaAbelFiniteModeStaticCoefficient
    {r : ℕ} (z a : Fin r → ℂ) (c : ℝ)
    (k : Fin (∑ _i : Fin r, 1)) : ℂ :=
  let i := GaloisForLFunctions.gammaJetSlotNode (fun _i : Fin r => 1) k
  a i * xiPhysicalLogWindowModeMultiplier c (z i) * ((z i + 1) / z i)

/-- Exact height rate of one coefficient in a finite theta--Abel packet. -/
theorem norm_sq_xiPhysicalThetaAbelFiniteModeCoefficient_eq
    {r : ℕ} (z a : Fin r → ℂ) (c m : ℝ)
    (k : Fin (∑ _i : Fin r, 1)) :
    ‖xiPhysicalThetaAbelFiniteModeCoefficient z a c m k‖ ^ 2 =
      ‖xiPhysicalThetaAbelFiniteModeStaticCoefficient z a c k‖ ^ 2 *
        Real.exp (2 *
          (z (GaloisForLFunctions.gammaJetSlotNode (fun _i : Fin r => 1) k)).re * m) := by
  let i := GaloisForLFunctions.gammaJetSlotNode (fun _i : Fin r => 1) k
  change ‖(a i * xiPhysicalLogWindowModeMultiplier c (z i) * ((z i + 1) / z i)) *
      Complex.exp (z i * (m : ℂ))‖ ^ 2 =
    ‖a i * xiPhysicalLogWindowModeMultiplier c (z i) * ((z i + 1) / z i)‖ ^ 2 *
      Real.exp (2 * (z i).re * m)
  rw [norm_mul, Complex.norm_exp]
  have hre : (z i * (m : ℂ)).re = (z i).re * m := by simp
  rw [hre, mul_pow]
  have hexp : Real.exp ((z i).re * m) ^ 2 =
      Real.exp (2 * (z i).re * m) := by
    rw [pow_two, ← Real.exp_add]
    congr 1
    ring
  rw [hexp]

/-- A selected static packet coefficient is nonzero whenever the source coefficient and exact
theta--Abel mode multiplier are nonzero. -/
theorem xiPhysicalThetaAbelFiniteModeStaticCoefficient_ne_zero
    {r : ℕ} {z a : Fin r → ℂ} {c : ℝ}
    (k : Fin (∑ _i : Fin r, 1)) (hc : 0 < c)
    (hzre : (z (GaloisForLFunctions.gammaJetSlotNode
      (fun _i : Fin r => 1) k)).re < 0)
    (ha : a (GaloisForLFunctions.gammaJetSlotNode
      (fun _i : Fin r => 1) k) ≠ 0)
    (hznegOne : z (GaloisForLFunctions.gammaJetSlotNode
      (fun _i : Fin r => 1) k) ≠ -1) :
    xiPhysicalThetaAbelFiniteModeStaticCoefficient z a c k ≠ 0 := by
  let i := GaloisForLFunctions.gammaJetSlotNode (fun _i : Fin r => 1) k
  have hz : z i ≠ 0 := by
    intro h
    rw [h] at hzre
    simp at hzre
  have hnum : z i + 1 ≠ 0 := by
    intro h
    apply hznegOne
    calc
      z i = (z i + 1) - 1 := by ring
      _ = -1 := by rw [h]; ring
  change a i * xiPhysicalLogWindowModeMultiplier c (z i) * ((z i + 1) / z i) ≠ 0
  exact mul_ne_zero (mul_ne_zero ha
    (xiPhysicalLogWindowModeMultiplier_ne_zero hc hzre)) (div_ne_zero hnum hz)

/-- Coherent finite packet of literal theta--Abel exponential-mode responses. -/
def xiPhysicalThetaAbelFiniteModeResponse
    {r : ℕ} (z a : Fin r → ℂ) (c m u : ℝ) : ℂ :=
  ∑ k : Fin (∑ _i : Fin r, 1),
    let i := GaloisForLFunctions.gammaJetSlotNode (fun _i : Fin r => 1) k
    a i * xiPhysicalThetaAbelExponentialModeResponse c m u (z i)

/-- Exact finite-packet factorization: all height dependence is in coefficients and all aperture
dependence is a distinct exponential feature. -/
theorem xiPhysicalThetaAbelFiniteModeResponse_eq_intervalCombination
    {r : ℕ} {z a : Fin r → ℂ} (hz : ∀ i, z i ≠ 0) (c m u : ℝ) :
    xiPhysicalThetaAbelFiniteModeResponse z a c m u =
      exponentialPolynomialIntervalCombination (fun i => -z i) (fun _i => 1)
        (xiPhysicalThetaAbelFiniteModeCoefficient z a c m) u := by
  rw [xiPhysicalThetaAbelFiniteModeResponse,
    exponentialPolynomialIntervalCombination]
  apply Finset.sum_congr rfl
  intro k hk
  let i := GaloisForLFunctions.gammaJetSlotNode (fun _i : Fin r => 1) k
  change a i *
      xiPhysicalThetaAbelExponentialModeResponse c m u (z i) =
    (a i * xiPhysicalLogWindowModeMultiplier c (z i) * ((z i + 1) / z i) *
      Complex.exp (z i * (m : ℂ))) *
        exponentialPolynomialRealFeature (fun q => -z q) (fun _q => 1) k u
  rw [xiPhysicalThetaAbelExponentialModeResponse_eq (hz i)]
  have hsplit : z i * ((m - u : ℝ) : ℂ) =
      z i * (m : ℂ) + (-z i) * (u : ℂ) := by
    push_cast
    ring
  rw [hsplit, Complex.exp_add]
  rw [exponentialPolynomialRealFeature, exponentialPolynomialMode,
    gammaJetSlotOrder_one]
  change _ = _ * ((u : ℂ) ^ 0 * Complex.exp ((-z i) * (u : ℂ)))
  simp only [pow_zero, one_mul]
  ring

/-- No coordinate of a finite packet of distinct theta--Abel modes can be hidden by coherent
cross-mode cancellation on a positive aperture. -/
theorem exists_xiPhysicalThetaAbelFiniteMode_coordinate_observability
    {r : ℕ} {z : Fin r → ℂ} (hzinj : Function.Injective z)
    (hz : ∀ i, z i ≠ 0) {A : ℝ} (hA : 0 < A) (c : ℝ)
    (j : Fin (∑ _i : Fin r, 1)) :
    ∃ C : ℝ, 0 < C ∧ ∀ (a : Fin r → ℂ) (m : ℝ),
      ‖xiPhysicalThetaAbelFiniteModeCoefficient z a c m j‖ ^ 2 ≤
        C * ∫ u : ℝ in Set.Icc 0 A,
          ‖xiPhysicalThetaAbelFiniteModeResponse z a c m u‖ ^ 2 := by
  have hneginj : Function.Injective (fun i => -z i) :=
    fun i q hiq => hzinj (neg_injective hiq)
  obtain ⟨C, hC, hobs⟩ :=
    exists_exponentialPolynomialInterval_coordinate_observability
      hneginj (fun _i : Fin r => 1) hA j
  refine ⟨C, hC, fun a m => ?_⟩
  have h := hobs (xiPhysicalThetaAbelFiniteModeCoefficient z a c m)
  apply h.trans_eq
  congr 1
  apply MeasureTheory.integral_congr_ae
  exact Filter.Eventually.of_forall fun u => by
    exact congrArg (fun w : ℂ => ‖w‖ ^ 2)
      (xiPhysicalThetaAbelFiniteModeResponse_eq_intervalCombination
        (z := z) (a := a) hz c m u).symm

/-- A supercritical coordinate forces every finite coherent theta--Abel packet energy to beat every
real power after physical `exp(m)` renormalization. -/
theorem tendsto_exp_mul_xiPhysicalThetaAbelFiniteModeEnergy_div_rpow_atTop
    {r : ℕ} {z : Fin r → ℂ} (hzinj : Function.Injective z)
    (hz : ∀ i, z i ≠ 0) {A c : ℝ} (hA : 0 < A) (hc : 0 < c)
    (a : Fin r → ℂ) (j : Fin (∑ _i : Fin r, 1))
    (hzre0 : (z (GaloisForLFunctions.gammaJetSlotNode
      (fun _i : Fin r => 1) j)).re < 0)
    (hzwall : -(1 / 2 : ℝ) < (z (GaloisForLFunctions.gammaJetSlotNode
      (fun _i : Fin r => 1) j)).re)
    (ha : a (GaloisForLFunctions.gammaJetSlotNode
      (fun _i : Fin r => 1) j) ≠ 0)
    (hznegOne : z (GaloisForLFunctions.gammaJetSlotNode
      (fun _i : Fin r => 1) j) ≠ -1)
    (p : ℝ) :
    Tendsto
      (fun m : ℝ => Real.exp m *
        (∫ u : ℝ in Set.Icc 0 A,
          ‖xiPhysicalThetaAbelFiniteModeResponse z a c m u‖ ^ 2) / m ^ p)
      atTop atTop := by
  let i := GaloisForLFunctions.gammaJetSlotNode (fun _i : Fin r => 1) j
  obtain ⟨C, hC, hobs⟩ :=
    exists_xiPhysicalThetaAbelFiniteMode_coordinate_observability
      hzinj hz hA c j
  let B := xiPhysicalThetaAbelFiniteModeStaticCoefficient z a c j
  have hB : B ≠ 0 :=
    xiPhysicalThetaAbelFiniteModeStaticCoefficient_ne_zero j hc hzre0 ha hznegOne
  have hK : 0 < ‖B‖ ^ 2 / C := div_pos (sq_pos_of_pos (norm_pos_iff.mpr hB)) hC
  have hgap : 0 < 1 + 2 * (z i).re := by linarith
  have hbase := (tendsto_exp_mul_div_rpow_atTop p
    (1 + 2 * (z i).re) hgap).const_mul_atTop hK
  refine tendsto_atTop_mono' _ ?_ hbase
  filter_upwards [Filter.eventually_gt_atTop (0 : ℝ)] with m hm
  have hlower : ‖B‖ ^ 2 / C * Real.exp (2 * (z i).re * m) ≤
      ∫ u : ℝ in Set.Icc 0 A,
        ‖xiPhysicalThetaAbelFiniteModeResponse z a c m u‖ ^ 2 := by
    have hcoord := hobs a m
    rw [norm_sq_xiPhysicalThetaAbelFiniteModeCoefficient_eq] at hcoord
    change ‖B‖ ^ 2 * Real.exp (2 * (z i).re * m) ≤ C * _ at hcoord
    rw [show ‖B‖ ^ 2 / C * Real.exp (2 * (z i).re * m) =
      (‖B‖ ^ 2 * Real.exp (2 * (z i).re * m)) / C by ring]
    apply (div_le_iff₀ hC).2
    simpa [mul_assoc, mul_comm, mul_left_comm] using hcoord
  have hmul := mul_le_mul_of_nonneg_left hlower (Real.exp_pos m).le
  have hden : 0 < m ^ p := Real.rpow_pos_of_pos hm p
  rw [show ‖B‖ ^ 2 / C *
      (Real.exp ((1 + 2 * (z i).re) * m) / m ^ p) =
    (‖B‖ ^ 2 / C * Real.exp ((1 + 2 * (z i).re) * m)) / m ^ p by ring]
  apply (div_le_div_iff_of_pos_right hden).2
  have hexp : Real.exp m *
      (‖B‖ ^ 2 / C * Real.exp (2 * (z i).re * m)) =
    ‖B‖ ^ 2 / C * Real.exp ((1 + 2 * (z i).re) * m) := by
      rw [show Real.exp m *
          (‖B‖ ^ 2 / C * Real.exp (2 * (z i).re * m)) =
        ‖B‖ ^ 2 / C * (Real.exp m *
          Real.exp (2 * (z i).re * m)) by ring,
        ← Real.exp_add]
      congr 2
      ring
  rw [← hexp]
  simpa [mul_assoc] using hmul

end

end RHTower
