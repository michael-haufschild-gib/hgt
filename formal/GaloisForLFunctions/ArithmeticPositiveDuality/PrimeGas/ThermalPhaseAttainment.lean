import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.LogarithmicPhaseContinuity
import GaloisForLFunctions.RHTower.FiniteEulerProductKroneckerWeylLimitLaw

/-!
# Saturation of the thermal phase trace

At a trace-class inverse temperature, the Gibbs trace defect is the weighted
squared distance of the observed phase from a Hamiltonian clock. Dense prime
orbits bring every phase arbitrarily close to saturation at arbitrarily late
times. Exact saturation detects a single clock on the entire gas.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open Set Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped ENNReal

abbrev TraceTemperature := {β : ℝ // 1 < β}

/-- The real Gibbs weight on one shell. -/
def thermalWeight (β : TraceTemperature) (n : ℕ+) := Real.exp (-β.val * energy n)

private def halfHeat (β : TraceTemperature) := heat ((β.val : ℂ)/2)

private theorem summable_half (β : TraceTemperature) : Summable (fun n => ‖halfHeat β n‖^2) :=
  (summable_heat_sq_iff _).2 (by rw [Complex.div_ofNat_re, Complex.ofReal_re]; linarith [β.2])

private theorem half_sq (β : TraceTemperature) (n : ℕ+) : ‖halfHeat β n‖^2 = thermalWeight β n := by
  rw [halfHeat, norm_heat, sq, ← Real.exp_add, Complex.div_ofNat_re, Complex.ofReal_re, thermalWeight]
  congr 1
  ring

theorem thermalWeight_summable (β : TraceTemperature) : Summable (thermalWeight β) :=
  (summable_half β).congr (half_sq β)

theorem thermalWeight_pos (β : TraceTemperature) (n : ℕ+) : 0 < thermalWeight β n := Real.exp_pos _

private theorem half_product (β : TraceTemperature) (n : ℕ+) :
    halfHeat β n * halfHeat β n = (thermalWeight β n : ℂ) := by
  rw [halfHeat, ← heat_add, add_halves, heat, thermalWeight, Complex.ofReal_exp, Complex.ofReal_mul,
    Complex.ofReal_neg]

theorem thermalWeight_partition (β : TraceTemperature) :
    ((∑' n, thermalWeight β n : ℝ) : ℂ) = riemannZeta β.val := by
  rw [← partition_eq_zeta ⟨(β.val : ℂ), β.2⟩, gibbsOperator,
    HilbertSchmidt.opTrace_diagOp_comp, Complex.ofReal_tsum]
  exact tsum_congr fun n => (half_product β n).symm

/-- Relative phase in the shell basis followed by Gibbs propagation. -/
def thermalPhaseOperator (β : TraceTemperature) (u : ℕ+ → Circle) : Gas →L[ℂ] Gas :=
  HilbertSchmidt.diagOp (fun n => (u n : ℂ)*halfHeat β n)
    (by simpa only [norm_mul, Circle.norm_coe, one_mul] using summable_half β) ∘L
    HilbertSchmidt.diagOp (halfHeat β) (summable_half β)

theorem thermalPhaseOperator_apply (β : TraceTemperature) (u : ℕ+ → Circle) (f : Gas) (n : ℕ+) :
    thermalPhaseOperator β u f n = ((u n : ℂ)*(thermalWeight β n : ℂ)) * f n := by
  simp only [thermalPhaseOperator, ContinuousLinearMap.comp_apply, HilbertSchmidt.diagOp_apply]
  rw [← half_product]
  ring

/-- Real thermal overlap of the observation with the inverse comparison phase. -/
def thermalReading (β : TraceTemperature) (u : ℕ+ → Circle) :=
  (ContinuousLinearMap.opTrace (thermalPhaseOperator β u)).re

theorem thermalPhaseOperator_trace (β : TraceTemperature) (u : ℕ+ → Circle) :
    ContinuousLinearMap.opTrace (thermalPhaseOperator β u) =
      ∑' n, (u n : ℂ)*(thermalWeight β n : ℂ) := by
  rw [thermalPhaseOperator, HilbertSchmidt.opTrace_diagOp_comp]
  exact tsum_congr fun n => by rw [mul_assoc, half_product]

theorem thermalWeight_twist_summable (β : TraceTemperature) (u : ℕ+ → Circle) :
    Summable (fun n => (u n : ℂ)*(thermalWeight β n : ℂ)) := by
  apply Summable.of_norm
  simpa only [norm_mul, Circle.norm_coe, one_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (thermalWeight_pos β _)] using thermalWeight_summable β

theorem thermalReading_eq (β : TraceTemperature) (u : ℕ+ → Circle) :
    thermalReading β u = ∑' n, thermalWeight β n * (u n : ℂ).re := by
  rw [thermalReading, thermalPhaseOperator_trace, Complex.re_tsum (thermalWeight_twist_summable β u)]
  exact tsum_congr fun n => by simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    mul_zero, sub_zero, mul_comm]

/-- The trace with observation χ and comparison clock t. -/
def clockReading (β : TraceTemperature) (χ : ℕ+ →* Circle) (t : ℝ) :=
  thermalReading β (fun n => χ n / clockPhase t n)

private theorem partition_re (β : TraceTemperature) :
    (riemannZeta β.val).re = ∑' n, thermalWeight β n :=
  (congrArg Complex.re (thermalWeight_partition β)).symm

private theorem summable_real_twist (β : TraceTemperature) (u : ℕ+ → Circle) :
    Summable (fun n => thermalWeight β n * (u n : ℂ).re) := by
  apply (Complex.hasSum_re (thermalWeight_twist_summable β u).hasSum).summable.congr
  intro n
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero, mul_comm]

private theorem circle_distance (a b : Circle) :
    dist a b ^ 2 = 2 * (1 - ((a/b : Circle) : ℂ).re) := by
  have h : (a : ℂ) - (b : ℂ) = (((a/b : Circle) : ℂ)-1) * (b : ℂ) := by
    rw [sub_mul, one_mul, ← Circle.coe_mul, div_mul_cancel]
  change dist (a : ℂ) (b : ℂ) ^ 2 = _
  rw [dist_eq_norm, h, norm_mul, Circle.norm_coe, mul_one, ← Complex.normSq_eq_norm_sq]
  have hz := Circle.normSq_coe (a/b)
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.one_re, Complex.sub_im,
    Complex.one_im, sub_zero] at hz ⊢
  nlinarith only [hz]

/-- The trace defect is the Gibbs-weighted squared phase distance for two shell readouts. -/
theorem relative_phase_defect (β : TraceTemperature) (u v : ℕ+ → Circle) :
    HasSum (fun n => thermalWeight β n * dist (u n) (v n)^2)
      (2 * ((riemannZeta β.val).re - thermalReading β (fun n => u n / v n))) := by
  let r (n : ℕ+) := u n / v n
  rw [partition_re, thermalReading_eq]
  have h := ((thermalWeight_summable β).hasSum.sub (summable_real_twist β r).hasSum).mul_left 2
  have eqfun : (fun n => thermalWeight β n * dist (u n) (v n)^2) =
      (fun n => 2 * (thermalWeight β n - thermalWeight β n * (r n : ℂ).re)) := by
    funext n
    rw [circle_distance]
    dsimp only [r]
    ring
  rw [eqfun]
  exact h

theorem thermal_defect_hasSum (β : TraceTemperature) (χ : ℕ+ →* Circle) (t : ℝ) :
    HasSum (fun n => thermalWeight β n * dist (χ n) (clockPhase t n)^2)
      (2 * ((riemannZeta β.val).re - clockReading β χ t)) :=
  relative_phase_defect β χ (clockPhase t)

/-- A thermal defect bounds the phase error at each individual shell. -/
theorem shell_phase_defect_le (β : TraceTemperature) (χ : ℕ+ →* Circle) (t : ℝ) (n : ℕ+) :
    thermalWeight β n * dist (χ n) (clockPhase t n)^2 ≤
      2 * ((riemannZeta β.val).re - clockReading β χ t) := by
  have hs := thermal_defect_hasSum β χ t
  rw [← hs.tsum_eq]
  exact hs.summable.le_tsum n (fun k _ => mul_nonneg (thermalWeight_pos β k).le (sq_nonneg _))

theorem clockReading_le_zeta (β : TraceTemperature) (χ : ℕ+ →* Circle) (t : ℝ) :
    clockReading β χ t ≤ (riemannZeta β.val).re := by
  have h := (thermal_defect_hasSum β χ t).tsum_eq
  have hz : 0 ≤ ∑' n, thermalWeight β n * dist (χ n) (clockPhase t n)^2 :=
    tsum_nonneg (fun n => mul_nonneg (thermalWeight_pos β n).le (sq_nonneg _))
  linarith

private theorem reading_eq_iff (β : TraceTemperature) (u v : ℕ+ → Circle) :
    thermalReading β (fun n => u n / v n) = (riemannZeta β.val).re ↔ u = v := by
  constructor
  · intro ht
    have hs := relative_phase_defect β u v
    have hsum := hs.tsum_eq
    rw [ht, sub_self, mul_zero] at hsum
    funext n
    have hle := hs.summable.le_tsum n (fun i _ => mul_nonneg (thermalWeight_pos β i).le (sq_nonneg _))
    rw [hsum] at hle
    have hz := nonpos_of_mul_nonpos_right hle (thermalWeight_pos β n)
    exact dist_eq_zero.mp (sq_eq_zero_iff.mp (le_antisymm hz (sq_nonneg _)))
  · rintro rfl
    rw [thermalReading_eq, partition_re]
    exact tsum_congr fun n => by simp

/-- Saturation at a fixed time is equivalent to exact agreement at every shell. -/
theorem clockReading_eq_zeta_iff (β : TraceTemperature) (χ : ℕ+ →* Circle) (t : ℝ) :
    clockReading β χ t = (riemannZeta β.val).re ↔ χ = clockPhase t := by
  rw [clockReading, reading_eq_iff]
  exact DFunLike.coe_injective.eq_iff

/-- Even a magnitude-only trace measurement suffices. The occupied vacuum fixes the common phase. -/
theorem thermal_trace_norm_eq_iff (β : TraceTemperature) (u : ℕ+ → Circle) :
    ‖ContinuousLinearMap.opTrace (thermalPhaseOperator β u)‖ = (riemannZeta β.val).re ↔
      ∀ n, u n = u 1 := by
  let B := (riemannZeta β.val).re
  let z := ContinuousLinearMap.opTrace (thermalPhaseOperator β u)
  have hB : 0 < B := by
    rw [show B = ∑' n, thermalWeight β n from partition_re β]
    exact (thermalWeight_pos β 1).trans_le ((thermalWeight_summable β).le_tsum 1 (fun n _ => (thermalWeight_pos β n).le))
  have rotate (a : Circle) : ContinuousLinearMap.opTrace (thermalPhaseOperator β (fun n => u n / a)) =
      z / (a : ℂ) := by
    unfold z
    rw [thermalPhaseOperator_trace, thermalPhaseOperator_trace, ← tsum_div_const]
    exact tsum_congr fun n => by rw [Circle.coe_div]; ring
  constructor
  · intro hz
    change ‖z‖ = B at hz
    let a : Circle := ⟨z / (B : ℂ), mem_sphere_zero_iff_norm.mpr (by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB, hz, div_self hB.ne'])⟩
    have he : z / (a : ℂ) = (B : ℂ) := by
      apply (div_eq_iff (Circle.coe_ne_zero a)).mpr
      change z = (B : ℂ) * (z / (B : ℂ))
      field_simp [Complex.ofReal_ne_zero.mpr hB.ne']
    have eqc := (rotate a).trans he
    have hre := congrArg Complex.re eqc
    have hu := (reading_eq_iff β u (fun _ => a)).mp hre
    exact fun n => (congrFun hu n).trans (congrFun hu 1).symm
  · intro hu
    have hconst : (fun n => u n / u 1) = (fun _ => (1 : Circle)) := by
      funext n
      rw [hu n, div_self']
    have he : ContinuousLinearMap.opTrace (thermalPhaseOperator β (fun _ => (1 : Circle))) = (B : ℂ) := by
      simp only [thermalPhaseOperator_trace, Circle.coe_one, one_mul, ← Complex.ofReal_tsum]
      exact congrArg Complex.ofReal (partition_re β).symm
    have hr := rotate (u 1)
    rw [hconst, he] at hr
    have hn := congrArg norm hr
    rw [norm_div, Circle.norm_coe, div_one, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hB] at hn
    exact hn.symm

theorem clock_trace_norm_eq_zeta_iff (β : TraceTemperature) (χ : ℕ+ →* Circle) (t : ℝ) :
    ‖ContinuousLinearMap.opTrace (thermalPhaseOperator β (fun n => χ n / clockPhase t n))‖ =
      (riemannZeta β.val).re ↔ χ = clockPhase t := by
  rw [thermal_trace_norm_eq_iff]
  simp only [map_one, div_one, div_eq_one]
  exact ⟨fun h => MonoidHom.ext h, fun h n => DFunLike.congr_fun h n⟩

/-- A single trace-class temperature suffices to test the energy-continuity law. -/
theorem thermal_attainment_iff (β : TraceTemperature) (χ : ℕ+ →* Circle) :
    (∃ t : ℝ, clockReading β χ t = (riemannZeta β.val).re) ↔ energyContinuous χ := by
  constructor
  · rintro ⟨t, h⟩
    rw [(clockReading_eq_zeta_iff β χ t).mp h]
    exact clockPhase_energyContinuous t
  · intro hc
    obtain ⟨t, ht, _⟩ := (energyContinuous_iff_unique_time χ).mp hc
    exact ⟨t, (clockReading_eq_zeta_iff β χ t).mpr ht⟩

private def primeProductPhase (ω : Nat.Primes → Circle) (n : ℕ+) : Circle :=
  (n.factorMultiset.map ω).prod

private theorem primeProductPhase_char (ψ : ℕ+ →* Circle) (n : ℕ+) :
    primeProductPhase (fun p : Nat.Primes => ψ (p : ℕ+)) n = ψ n := by
  have h := ψ.map_multiset_prod (n.factorMultiset.map ((↑) : Nat.Primes → ℕ+))
  rw [Multiset.map_map] at h
  exact h.symm.trans (congrArg ψ n.prod_factorMultiset)

private theorem continuous_primeProductPhase (n : ℕ+) :
    Continuous (fun ω => primeProductPhase ω n) := by
  have hc (s : Multiset Nat.Primes) : Continuous (fun ω : Nat.Primes → Circle => (s.map ω).prod) := by
    induction s using Multiset.induction_on with
    | empty => simpa only [Multiset.map_zero, Multiset.prod_zero] using
        (continuous_const : Continuous (fun _ : Nat.Primes → Circle => (1 : Circle)))
    | cons p s ih =>
      simp only [Multiset.map_cons, Multiset.prod_cons]
      exact (continuous_apply p).mul ih
  exact hc n.factorMultiset

private def torusReading (β : TraceTemperature) (χ : ℕ+ →* Circle) (ω : Nat.Primes → Circle) :=
  thermalReading β (fun n => χ n * primeProductPhase ω n)

private theorem continuous_torusReading (β : TraceTemperature) (χ : ℕ+ →* Circle) :
    Continuous (torusReading β χ) := by
  change Continuous (fun ω => thermalReading β (fun n => χ n * primeProductPhase ω n))
  simp only [thermalReading_eq]
  refine continuous_tsum (u := thermalWeight β) ?_ (thermalWeight_summable β) ?_
  · intro n
    exact continuous_const.mul (Complex.continuous_re.comp (continuous_subtype_val.comp
      (continuous_const.mul (continuous_primeProductPhase n))))
  · intro n ω
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos (thermalWeight_pos β n), Real.norm_eq_abs]
    have hz := Complex.abs_re_le_norm (χ n * primeProductPhase ω n : Circle)
    rw [Circle.norm_coe] at hz
    simpa only [mul_one] using mul_le_mul_of_nonneg_left hz (thermalWeight_pos β n).le

private theorem torusReading_at_inverse (β : TraceTemperature) (χ : ℕ+ →* Circle) :
    torusReading β χ (fun p : Nat.Primes => χ⁻¹ (p : ℕ+)) = (riemannZeta β.val).re := by
  rw [torusReading, thermalReading_eq, partition_re]
  exact tsum_congr fun n => by rw [primeProductPhase_char]; simp

private theorem torusReading_on_orbit (β : TraceTemperature) (χ : ℕ+ →* Circle) (t : ℝ) :
    torusReading β χ (circlePhaseFlow _root_.RHTower.primeFrequency t) = clockReading β χ t := by
  have hw : circlePhaseFlow _root_.RHTower.primeFrequency t =
      fun p : Nat.Primes => (clockPhase t)⁻¹ (p : ℕ+) := by
    funext p
    apply Circle.ext
    rw [HTGeometry.circlePhaseFlow_coe]
    change Complex.exp _ = (((Circle.exp (t * energy (p : ℕ+)))⁻¹ : Circle) : ℂ)
    rw [Circle.coe_inv, Circle.coe_exp, ← Complex.exp_neg]
    congr 1
    simp only [_root_.RHTower.primeFrequency, energy]
    push_cast
    ring
  rw [hw, torusReading, clockReading]
  congr 1
  funext n
  rw [primeProductPhase_char]
  rfl

/-- Every forward time tail approaches the full partition function for every composition phase. -/
theorem clockReading_sup_on_tail (β : TraceTemperature) (χ : ℕ+ →* Circle) (T : ℝ) :
    IsLUB (clockReading β χ '' Ici T) (riemannZeta β.val).re := by
  constructor
  · rintro x ⟨t, _, rfl⟩
    exact clockReading_le_zeta β χ t
  · intro b hb
    by_contra! h
    let U := {ω | b < torusReading β χ ω}
    have hU : IsOpen U := isOpen_lt continuous_const (continuous_torusReading β χ)
    have hn : U.Nonempty := ⟨_, (torusReading_at_inverse β χ).symm ▸ h⟩
    obtain ⟨ω, ⟨t, ht, rfl⟩, hω⟩ := (dense_forwardOrbit_circlePhaseFlow
      _root_.RHTower.rationallyIndependentSequence_primeFrequency T).exists_mem_open hU hn
    exact (not_lt_of_ge (hb ⟨t,ht,rfl⟩)) ((torusReading_on_orbit β χ t) ▸ hω)

/-- Every positive tolerance is reached on a set of times of positive lower density. -/
theorem clockReading_near_zeta_positive_density (β : TraceTemperature) (χ : ℕ+ →* Circle)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ c > 0, ∀ᶠ T : ℝ in atTop, ENNReal.ofReal (c*T) ≤
      volume ({t | (riemannZeta β.val).re - ε < clockReading β χ t} ∩ Icc 0 T) := by
  let U := {ω | (riemannZeta β.val).re - ε < torusReading β χ ω}
  have hU : IsOpen U := isOpen_lt continuous_const (continuous_torusReading β χ)
  have hn : U.Nonempty := by
    refine ⟨fun p => χ⁻¹ (p : ℕ+), ?_⟩
    change _ < torusReading β χ _
    rw [torusReading_at_inverse]
    exact sub_lt_self _ hε
  have hset : circlePhaseFlow _root_.RHTower.primeFrequency ⁻¹' U =
      {t | (riemannZeta β.val).re - ε < clockReading β χ t} := by
    ext t
    change (_ < torusReading β χ (circlePhaseFlow _root_.RHTower.primeFrequency t)) ↔ _ < clockReading β χ t
    rw [torusReading_on_orbit]
  simpa only [hset] using _root_.RHTower.exists_pos_density_preimage_primeFlow hU hn

#print axioms thermalPhaseOperator_apply
#print axioms thermalPhaseOperator_trace
#print axioms thermal_defect_hasSum
#print axioms shell_phase_defect_le
#print axioms clockReading_eq_zeta_iff
#print axioms thermal_trace_norm_eq_iff
#print axioms clock_trace_norm_eq_zeta_iff
#print axioms thermal_attainment_iff
#print axioms clockReading_sup_on_tail
#print axioms clockReading_near_zeta_positive_density

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
