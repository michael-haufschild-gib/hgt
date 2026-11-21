import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ThermalPhaseAttainment
import GaloisForLFunctions.PrimeTorusTheory.TheHullOverTheTorus
import GaloisForLFunctions.HTGeometry.HelsonEulerModification

/-!
# Finite calibration and the zeros of a prime-modified gas

Inserting a single-prime phase in the complex Gibbs trace gives one Euler
correction. It is an analytic unit in the positive half-plane. A phase at an
arbitrarily high prime can therefore preserve the partition zeros and every
low-energy calibration while violating the common-time law.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open Set
open GaloisForLFunctions.HTGeometry

/-- The complex-temperature partition trace with a unit phase inserted on each shell. -/
def insertedPartition (u : ℕ+ → Circle) (s : {z : ℂ // 1 < z.re}) : ℂ :=
  ContinuousLinearMap.opTrace (thermalPhaseOperator ⟨s.val.re,s.property⟩ (fun n => u n / clockPhase s.val.im n))

theorem insertedPartition_eq_series (u : ℕ+ → Circle) (s : {z : ℂ // 1 < z.re}) :
    insertedPartition u s = ∑' n, (u n : ℂ)*heat s.val n := by
  rw [insertedPartition, thermalPhaseOperator_trace]
  apply tsum_congr
  intro n
  rw [Circle.coe_div, div_eq_mul_inv, mul_assoc]
  congr 1
  change (Complex.exp (((s.val.im*energy n : ℝ) : ℂ)*Complex.I))⁻¹ *
    (Real.exp (-s.val.re * energy n) : ℂ) = heat s.val n
  rw [← Complex.exp_neg, Complex.ofReal_exp, ← Complex.exp_add, heat,
    Complex.ofReal_mul, Complex.ofReal_mul, Complex.ofReal_neg]
  congr 1
  calc
    _ = -((s.val.re : ℂ) + (s.val.im : ℂ)*Complex.I)*(energy n : ℂ) := by ring
    _ = _ := by rw [Complex.re_add_im]

theorem insertedPartition_one (s : {z : ℂ // 1 < z.re}) :
    insertedPartition (fun _ => 1) s = riemannZeta s.val := by
  rw [insertedPartition_eq_series, ← partition_eq_zeta s, gibbsOperator, HilbertSchmidt.opTrace_diagOp_comp]
  exact tsum_congr fun n => by rw [← heat_add, add_halves, Circle.coe_one, one_mul]

/-- Extend the positive-integer character by zero at the missing Dirichlet index. -/
private def coefficient (χ : ℕ+ →* Circle) : ℕ →*₀ ℂ where
  toFun n := if h : 0 < n then (χ ⟨n,h⟩ : ℂ) else 0
  map_zero' := by simp
  map_one' := by change (if h : 0 < 1 then (χ ⟨1,h⟩ : ℂ) else 0) = 1; simp
  map_mul' a b := by
    rcases Nat.eq_zero_or_pos a with rfl | ha
    · simp
    rcases Nat.eq_zero_or_pos b with rfl | hb
    · simp
    rw [dif_pos ha, dif_pos hb, dif_pos (Nat.mul_pos ha hb)]
    exact (congrArg ((↑) : Circle → ℂ) (χ.map_mul (⟨a,ha⟩ : ℕ+) (⟨b,hb⟩ : ℕ+))).trans
      (Circle.coe_mul _ _)

private theorem coefficient_apply (χ : ℕ+ →* Circle) (n : ℕ+) :
    coefficient χ n = (χ n : ℂ) := dif_pos n.pos

private theorem coefficient_bound (χ : ℕ+ →* Circle) (n : ℕ) : ‖coefficient χ n‖ ≤ 1 := by
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp
  · have h : coefficient χ n = (χ ⟨n,hn⟩ : ℂ) := coefficient_apply χ ⟨n,hn⟩
    rw [h, Circle.norm_coe]

private theorem insertedPartition_eq_nat_series (χ : ℕ+ →* Circle) (s : {z : ℂ // 1 < z.re}) :
    insertedPartition χ s = ∑' n : ℕ, coefficient χ n * (n : ℂ) ^ (-s.val) := by
  rw [insertedPartition_eq_series]
  have hs : Function.support (fun n : ℕ => coefficient χ n * (n : ℂ)^(-s.val)) ⊆
      Set.range ((↑) : ℕ+ → ℕ) := by
    intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | h
    · exact (hn (by simp)).elim
    · exact ⟨⟨n,h⟩,rfl⟩
  rw [← PNat.coe_injective.tsum_eq hs]
  exact tsum_congr fun n => by rw [coefficient_apply, heat_eq_cpow]

/-- Rotating only the prime p multiplies shell n by z to its p-adic valuation. -/
def primeRotation (p : Nat.Primes) (z : Circle) : ℕ+ →* Circle where
  toFun n := z ^ ((n : ℕ).factorization p)
  map_one' := by change z ^ (1 : ℕ).factorization p = 1; simp
  map_mul' m n := by
    simp only [PNat.mul_coe, Nat.factorization_mul m.ne_zero n.ne_zero, Finsupp.add_apply, pow_add]

theorem primeRotation_self (p : Nat.Primes) (z : Circle) : primeRotation p z (p : ℕ+) = z := by
  change z ^ (p : ℕ).factorization p = z
  rw [p.property.factorization_self, pow_one]

theorem primeRotation_of_not_dvd (p : Nat.Primes) (z : Circle) (n : ℕ+) (h : ¬(p : ℕ) ∣ (n : ℕ)) :
    primeRotation p z n = 1 := by
  change z ^ (n : ℕ).factorization p = 1
  rw [Nat.factorization_eq_zero_of_not_dvd h, pow_zero]

/-- The finite Euler correction on the entire spectral plane. -/
def rotatedPartition (p : Nat.Primes) (z : Circle) (s : ℂ) :=
  riemannZeta s * HTGeometry.eulerFactor ((p : ℕ) : ℂ) (z : ℂ) s

theorem primeRotation_trace (p : Nat.Primes) (z : Circle) (s : {z : ℂ // 1 < z.re}) :
    insertedPartition (primeRotation p z) s = rotatedPartition p z s.val := by
  let χ := primeRotation p z
  let e : ℕ+ →* Circle := 1
  have he (q : Nat.Primes) : coefficient e q = 1 :=
    (coefficient_apply e (q : ℕ+)).trans rfl
  have hp : coefficient χ p = (z : ℂ) := (coefficient_apply χ (p : ℕ+)).trans
    (congrArg ((↑) : Circle → ℂ) (primeRotation_self p z))
  have hdiff (q : Nat.Primes) (hq : q ∉ ({p} : Finset Nat.Primes)) :
      coefficient χ q = coefficient e q := by
    have hne : p ≠ q := fun h => hq (by rw [h]; exact Finset.mem_singleton_self _)
    have hnd : ¬(p : ℕ) ∣ (q : ℕ) := by
      intro h
      exact hne (Subtype.ext ((Nat.prime_dvd_prime_iff_eq p.2 q.2).mp h))
    exact ((coefficient_apply χ (q : ℕ+)).trans
      (congrArg ((↑) : Circle → ℂ) (primeRotation_of_not_dvd p z (q : ℕ+) hnd))).trans (he q).symm
  have h := PrimeTorusTheory.fibre_finite_modification (coefficient_bound χ) (coefficient_bound e)
    {p} hdiff s.2
  rw [← insertedPartition_eq_nat_series χ s, ← insertedPartition_eq_nat_series e s] at h
  change insertedPartition χ s = _
  have htr : insertedPartition e s = riemannZeta s.val := insertedPartition_one s
  simp only [Finset.prod_singleton, hp, he, one_mul, htr] at h
  have hd := _root_.RHTower.one_sub_phase_cpow_ne_zero p z (z := s.val) (lt_trans zero_lt_one s.2)
  unfold rotatedPartition HTGeometry.eulerFactor
  rw [← mul_div_assoc, eq_div_iff hd]
  exact h

theorem meromorphic_rotatedPartition (p : Nat.Primes) (z : Circle) :
    MeromorphicOn (rotatedPartition p z) Set.univ := by
  intro s _
  have hp : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  exact (meromorphicAt_riemannZeta s).mul (meromorphicAt_eulerFactor hp s)

theorem primeCorrection_analytic_unit (p : Nat.Primes) (z : Circle) (s : {w : ℂ // 0 < w.re}) :
    AnalyticAt ℂ (HTGeometry.eulerFactor ((p : ℕ) : ℂ) (z : ℂ)) s.val ∧
      HTGeometry.eulerFactor ((p : ℕ) : ℂ) (z : ℂ) s.val ≠ 0 := by
  have hp : ((p : ℕ) : ℂ) ≠ 0 := by exact_mod_cast p.2.ne_zero
  have hpow := analyticAt_const_cpow_neg hp s.val
  have hd := _root_.RHTower.one_sub_phase_cpow_ne_zero p z s.property
  have hn := _root_.RHTower.one_sub_phase_cpow_ne_zero p 1 s.property
  simp only [Circle.coe_one, one_mul] at hn
  exact ⟨(analyticAt_const.sub hpow).div (analyticAt_const.sub (analyticAt_const.mul hpow)) hd,
    div_ne_zero hn hd⟩

theorem rotatedPartition_zero_iff (p : Nat.Primes) (z : Circle) (s : {w : ℂ // 0 < w.re}) :
    rotatedPartition p z s.val = 0 ↔ riemannZeta s.val = 0 := by
  rw [rotatedPartition, mul_eq_zero, or_iff_left (primeCorrection_analytic_unit p z s).2]

/-- The order agrees at every zero and at the pole in the positive half-plane. -/
theorem rotatedPartition_order (p : Nat.Primes) (z : Circle) (s : {w : ℂ // 0 < w.re}) :
    meromorphicOrderAt (rotatedPartition p z) s.val = meromorphicOrderAt riemannZeta s.val := by
  obtain ⟨ha, hn⟩ := primeCorrection_analytic_unit p z s
  change meromorphicOrderAt (riemannZeta * HTGeometry.eulerFactor ((p : ℕ) : ℂ) (z : ℂ)) _ = _
  rw [mul_comm]
  exact meromorphicOrderAt_mul_of_ne_zero ha hn

private theorem rotation_below (p : Nat.Primes) (z : Circle) (n : ℕ+) (hn : (n : ℕ) < p) :
    primeRotation p z n = 1 :=
  primeRotation_of_not_dvd _ _ _ (fun h => hn.not_ge (Nat.le_of_dvd n.pos h))

/-- A nontrivial modification above 3 cannot be generated by a common time. -/
theorem primeRotation_energyContinuous_iff (p : {p : Nat.Primes // 3 < (p : ℕ)}) (z : Circle) :
    energyContinuous (primeRotation p.val z) ↔ z = 1 := by
  constructor
  · intro hc
    obtain ⟨t, ht, _⟩ := (energyContinuous_iff_unique_time _).mp hc
    have fixed (n : ℕ+) (hn : (n : ℕ) < p.val) :
        _root_.HTGeometry.phaseClockValue (energy n) t = _root_.HTGeometry.phaseClockValue (energy n) 0 := by
      have h := congrArg ((↑) : Circle → ℂ) ((DFunLike.congr_fun ht n).symm.trans (rotation_below _ z n hn))
      change Complex.exp (((t * energy n : ℝ) : ℂ)*Complex.I) = 1 at h
      simpa only [_root_.HTGeometry.phaseClockValue, mul_zero, Complex.ofReal_zero, zero_mul,
        Complex.exp_zero, mul_comm (energy n) t] using h
    have h₂ : (2 : ℕ) < p.val := lt_trans (by norm_num) p.property
    have h₃ : (3 : ℕ) < p.val := p.property
    have hfreq : energy 2 ≠ 0 := (Real.log_pos (by norm_num) : 0 < energy 2).ne'
    have htime : t = 0 := _root_.HTGeometry.phaseClockPair_injective hfreq
      _root_.RHTower.CarrierDepthThree.irrational_log_three_div_log_two
      (Prod.ext (fixed 2 h₂) (fixed 3 h₃))
    have hp := DFunLike.congr_fun ht (p.val : ℕ+)
    rw [primeRotation_self, htime] at hp
    simpa [clockPhase] using hp
  · rintro rfl
    have he : primeRotation p.val 1 = clockPhase 0 := by
      apply MonoidHom.ext
      intro n
      simp [primeRotation, clockPhase]
    rw [he]
    exact clockPhase_energyContinuous 0

/-- Exact thermal saturation is lost at every time after any nontrivial rotation above 3. -/
theorem primeRotation_strict_thermal_iff (β : TraceTemperature)
    (p : {p : Nat.Primes // 3 < (p : ℕ)}) (z : Circle) :
    (∀ t : ℝ, clockReading β (primeRotation p.val z) t < (riemannZeta β.val).re) ↔ z ≠ 1 := by
  have h := (thermal_attainment_iff β (primeRotation p.val z)).trans (primeRotation_energyContinuous_iff p z)
  constructor
  · intro hall hz
    obtain ⟨t, ht⟩ := h.mpr hz
    exact (hall t).ne ht
  · intro hz t
    exact lt_of_le_of_ne (clockReading_le_zeta _ _ _) fun ht => hz (h.mp ⟨t,ht⟩)

/-- Every finite shell cutoff permits a coherent non-clock phase with the same
continued partition zeros and their multiplicities throughout the positive half-plane. -/
theorem finite_calibration_same_divisor (N : ℕ) :
    ∃ p : Nat.Primes, N < (p : ℕ) ∧ coherentRefinement (refinementAmplitude (primeRotation p (-1))) ∧
      (∀ n : ℕ+, (n : ℕ) ≤ N → primeRotation p (-1) n = 1) ∧
      ¬ energyContinuous (primeRotation p (-1)) ∧
      (∀ (β : TraceTemperature) (t : ℝ), clockReading β (primeRotation p (-1)) t < (riemannZeta β.val).re) ∧
      (∀ s : {w : ℂ // 1 < w.re}, insertedPartition (primeRotation p (-1)) s = rotatedPartition p (-1) s.val) ∧
      (∀ s : {w : ℂ // 0 < w.re}, (rotatedPartition p (-1) s.val = 0 ↔ riemannZeta s.val = 0) ∧
        meromorphicOrderAt (rotatedPartition p (-1)) s.val = meromorphicOrderAt riemannZeta s.val) := by
  obtain ⟨q, hN, hq⟩ := Nat.exists_infinite_primes (max N 3 + 1)
  let p : Nat.Primes := ⟨q,hq⟩
  have hqmax : max N 3 < q := hN
  have hlarge : N < q := (le_max_left N 3).trans_lt hqmax
  have h₃ : 3 < q := (le_max_right N 3).trans_lt hqmax
  have hflip : (-1 : Circle) ≠ 1 := Circle.neg_ne_self 1
  exact ⟨p, hlarge, refinementAmplitude_coherent _, fun n hn => rotation_below _ _ _ (hn.trans_lt hlarge),
    fun hc => hflip ((primeRotation_energyContinuous_iff ⟨p,h₃⟩ (-1)).mp hc),
    fun β => (primeRotation_strict_thermal_iff β ⟨p,h₃⟩ (-1)).mpr hflip,
    primeRotation_trace p (-1), fun s => ⟨rotatedPartition_zero_iff _ _ s, rotatedPartition_order _ _ s⟩⟩

#print axioms insertedPartition_eq_series
#print axioms primeRotation_trace
#print axioms meromorphic_rotatedPartition
#print axioms rotatedPartition_zero_iff
#print axioms rotatedPartition_order
#print axioms primeRotation_energyContinuous_iff
#print axioms primeRotation_strict_thermal_iff
#print axioms finite_calibration_same_divisor

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
