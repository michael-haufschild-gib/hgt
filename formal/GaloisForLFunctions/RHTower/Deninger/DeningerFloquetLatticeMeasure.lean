import GaloisForLFunctions.RHTower.Deninger.DeningerFloquetParseval
import GaloisForLFunctions.Core

/-!
# The arithmetic Floquet lattice measure

The half-density Floquet energy is a sum over primes of a sum over the frequency lattice
`{m/log q : m ∈ ℤ}`, weighted by `q^{-2}/log q`.  Packaging those weights as a single Borel measure

`μ_Fl = ∑_q (q^{-2}/log q) ∑_{m ∈ ℤ} δ_{m/log q}`

turns the energy into a genuine `L²` norm.

The measure is purely atomic on the countable node set, no nonzero node is shared by two primes
because the prime logarithms are rationally independent, and its mass grows at most linearly on
symmetric intervals, so it is finite on compacts.

* `deningerFloquetMeasure` : **`μ_Fl`.**
* `lintegral_deningerFloquetMeasure` : integration against `μ_Fl` is the arithmetic double sum.
* `deningerFloquetNode_eq_iff` : **no nonzero node is shared by two primes.**
* `deningerFloquetMeasure_compl_support` : **`μ_Fl` lives on the countable node set.**
* `deningerFloquetMeasure_Icc_le` : **at most linear mass growth.**
-/

namespace RHTower

open MeasureTheory Set
open scoped ENNReal

noncomputable section

/-! ## The lattice, its weights, and the measure -/

/-- The `m`-th frequency node of the prime circle of circumference `log q`. -/
def deningerFloquetNode (q : ℕ) (m : ℤ) : ℝ := (m : ℝ) / Real.log q

/-- The arithmetic weight `q^{-2}/log q` carried by the `q`-lattice. -/
def deningerFloquetWeight (q : ℕ) : ℝ≥0∞ :=
  ENNReal.ofReal (((q : ℝ) ^ 2)⁻¹ / Real.log q)

/-- The counting measure of the `q`-frequency lattice. -/
def deningerFloquetLattice (q : ℕ) : Measure ℝ :=
  Measure.sum fun m : ℤ => Measure.dirac (deningerFloquetNode q m)

/-- **The arithmetic Floquet lattice measure `μ_Fl`.** -/
def deningerFloquetMeasure : Measure ℝ :=
  Measure.sum fun q : Nat.Primes => deningerFloquetWeight (q : ℕ) • deningerFloquetLattice (q : ℕ)

/-- Integration against the lattice counting measure is the sum over the lattice. -/
theorem lintegral_deningerFloquetLattice (q : ℕ) (f : ℝ → ℝ≥0∞) :
    ∫⁻ ξ, f ξ ∂deningerFloquetLattice q = ∑' m : ℤ, f (deningerFloquetNode q m) := by
  rw [deningerFloquetLattice, lintegral_sum_measure]
  exact tsum_congr fun m => lintegral_dirac _ _

/-- **Integration against `μ_Fl` is the arithmetic double sum.** -/
theorem lintegral_deningerFloquetMeasure (f : ℝ → ℝ≥0∞) :
    ∫⁻ ξ, f ξ ∂deningerFloquetMeasure
      = ∑' q : Nat.Primes, deningerFloquetWeight (q : ℕ)
        * ∑' m : ℤ, f (deningerFloquetNode (q : ℕ) m) := by
  rw [deningerFloquetMeasure, lintegral_sum_measure]
  refine tsum_congr fun q => ?_
  rw [lintegral_smul_measure, lintegral_deningerFloquetLattice, smul_eq_mul]

/-! ## Positivity and finiteness of the weights -/

theorem deningerPrimeLog_pos (q : Nat.Primes) : 0 < Real.log ((q : ℕ) : ℝ) :=
  Real.log_pos (by exact_mod_cast q.2.one_lt)

theorem deningerLog_two_le_primeLog (q : Nat.Primes) : Real.log 2 ≤ Real.log ((q : ℕ) : ℝ) :=
  Real.log_le_log two_pos (by exact_mod_cast q.2.two_le)

theorem deningerFloquetWeight_pos (q : Nat.Primes) : 0 < deningerFloquetWeight (q : ℕ) := by
  have hq : (0 : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast q.2.pos
  have hlog := deningerPrimeLog_pos q
  exact ENNReal.ofReal_pos.2 (by positivity)

theorem deningerFloquetWeight_lt_top (q : ℕ) : deningerFloquetWeight q < ⊤ :=
  ENNReal.ofReal_lt_top

/-! ## The nodes -/

/-- **No nonzero node is shared by two distinct primes.**  A coincidence `m/log p = n/log q`
with `m ≠ 0` is a nontrivial rational relation between `log p` and `log q`, and the prime
logarithms are rationally independent. -/
theorem deningerFloquetNode_eq_iff {p q : Nat.Primes} {m n : ℤ}
    (hmn : deningerFloquetNode (p : ℕ) m = deningerFloquetNode (q : ℕ) n) (hm : m ≠ 0) :
    p = q ∧ m = n := by
  classical
  have hlp := deningerPrimeLog_pos p
  have hlq := deningerPrimeLog_pos q
  have hrel : (m : ℝ) * Real.log ((q : ℕ) : ℝ) = (n : ℝ) * Real.log ((p : ℕ) : ℝ) := by
    rw [deningerFloquetNode, deningerFloquetNode, div_eq_div_iff hlp.ne' hlq.ne'] at hmn
    linarith
  have hpq : p = q := by
    by_contra hne
    have hli := GaloisForLFunctions.logPrime_linearIndependent_int
    set c : Nat.Primes →₀ ℤ := Finsupp.single p n - Finsupp.single q m with hc
    have hcval : (Finsupp.linearCombination ℤ
        (fun r : Nat.Primes => Real.log ((r : ℕ) : ℝ))) c = 0 := by
      rw [hc, map_sub, Finsupp.linearCombination_single, Finsupp.linearCombination_single]
      simp only [zsmul_eq_mul]
      linarith
    have hczero : c = 0 := (linearIndependent_iff.1 hli) c hcval
    have hcq : c q = -m := by
      rw [hc]
      simp [hne]
    rw [hczero] at hcq
    exact hm (by simpa using hcq.symm)
  refine ⟨hpq, ?_⟩
  subst hpq
  have : (m : ℝ) = (n : ℝ) := mul_right_cancel₀ hlp.ne' hrel
  exact_mod_cast this

/-- The countable set carrying `μ_Fl`. -/
def deningerFloquetSupport : Set ℝ :=
  Set.range fun x : Nat.Primes × ℤ => deningerFloquetNode (x.1 : ℕ) x.2

theorem deningerFloquetSupport_countable : deningerFloquetSupport.Countable :=
  Set.countable_range _

theorem deningerFloquetNode_mem_support (q : Nat.Primes) (m : ℤ) :
    deningerFloquetNode (q : ℕ) m ∈ deningerFloquetSupport :=
  ⟨(q, m), rfl⟩

/-- **`μ_Fl` lives on the countable node set.** -/
theorem deningerFloquetMeasure_compl_support :
    deningerFloquetMeasure deningerFloquetSupportᶜ = 0 := by
  have hmeas : MeasurableSet deningerFloquetSupportᶜ :=
    deningerFloquetSupport_countable.measurableSet.compl
  rw [deningerFloquetMeasure, Measure.sum_apply _ hmeas]
  refine ENNReal.tsum_eq_zero.2 fun q => ?_
  rw [Measure.smul_apply, deningerFloquetLattice, Measure.sum_apply _ hmeas, smul_eq_mul]
  have hzero : ∀ m : ℤ,
      Measure.dirac (deningerFloquetNode (q : ℕ) m) deningerFloquetSupportᶜ = 0 := by
    intro m
    rw [Measure.dirac_apply' _ hmeas, Set.indicator_of_notMem]
    exact fun hmem => hmem (deningerFloquetNode_mem_support q m)
  rw [tsum_congr hzero, tsum_zero, mul_zero]

/-! ## Local finiteness -/

/-- Each lattice puts at most `2 T log q + 3` unit atoms in `[-T, T]`. -/
theorem deningerFloquetLattice_Icc_le (q : Nat.Primes) {T : ℝ} (hT : 0 ≤ T) :
    deningerFloquetLattice (q : ℕ) (Set.Icc (-T) T)
      ≤ ENNReal.ofReal (2 * T * Real.log ((q : ℕ) : ℝ) + 3) := by
  classical
  have hlog := deningerPrimeLog_pos q
  set L : ℝ := Real.log ((q : ℕ) : ℝ) with hL
  set N : ℕ := ⌈T * L⌉₊ with hN
  have hNle : (N : ℝ) ≤ T * L + 1 := by
    have h := Nat.ceil_lt_add_one (a := T * L) (by positivity)
    linarith
  have hNge : T * L ≤ (N : ℝ) := Nat.le_ceil _
  have hmeas : MeasurableSet (Set.Icc (-T) T) := measurableSet_Icc
  rw [deningerFloquetLattice, Measure.sum_apply _ hmeas]
  have hsupp : ∀ m : ℤ, m ∉ Finset.Icc (-(N : ℤ)) (N : ℤ) →
      Measure.dirac (deningerFloquetNode (q : ℕ) m) (Set.Icc (-T) T) = 0 := by
    intro m hm
    rw [Measure.dirac_apply' _ hmeas, Set.indicator_of_notMem]
    intro hmem
    have h1 : -T ≤ (m : ℝ) / L := hmem.1
    have h2 : (m : ℝ) / L ≤ T := hmem.2
    rw [le_div_iff₀ hlog] at h1
    rw [div_le_iff₀ hlog] at h2
    refine hm (Finset.mem_Icc.2 ⟨?_, ?_⟩)
    · have : (-(N : ℤ) : ℝ) ≤ (m : ℝ) := by push_cast; nlinarith
      exact_mod_cast this
    · have : (m : ℝ) ≤ ((N : ℤ) : ℝ) := by push_cast; nlinarith
      exact_mod_cast this
  rw [tsum_eq_sum hsupp]
  refine le_trans (Finset.sum_le_sum (fun m _ => prob_le_one)) ?_
  rw [Finset.sum_const, nsmul_eq_mul, mul_one, Int.card_Icc]
  have hcard : ((N : ℤ) + 1 - -(N : ℤ)).toNat = 2 * N + 1 := by omega
  rw [hcard]
  have hle : ((2 * N + 1 : ℕ) : ℝ) ≤ 2 * T * L + 3 := by
    push_cast
    nlinarith
  calc (((2 * N + 1 : ℕ) : ℕ) : ℝ≥0∞)
      = ENNReal.ofReal ((2 * N + 1 : ℕ) : ℝ) := by rw [ENNReal.ofReal_natCast]
    _ ≤ ENNReal.ofReal (2 * T * L + 3) := ENNReal.ofReal_le_ofReal hle

theorem deningerPrimeInvSq_summable :
    Summable fun q : Nat.Primes => ((((q : ℕ)) : ℝ) ^ 2)⁻¹ := by
  have hbase : Summable fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ ((2 : ℝ)) := by
    rw [Real.summable_one_div_nat_rpow]
    norm_num
  have hbase' : Summable fun n : ℕ => ((n : ℝ) ^ 2)⁻¹ := by
    refine hbase.congr fun n => ?_
    rw [one_div, ← Real.rpow_natCast (n : ℝ) 2]
    norm_num
  exact hbase'.comp_injective Nat.Primes.coe_nat_injective

/-- The comparison weight `q^{-2}(2T + 3/log q)` of the mass bound is summable. -/
theorem deningerFloquetMassTerm_summable {T : ℝ} (hT : 0 ≤ T) :
    Summable fun q : Nat.Primes =>
      (((q : ℕ) : ℝ) ^ 2)⁻¹ * (2 * T + 3 / Real.log ((q : ℕ) : ℝ)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos one_lt_two
  refine Summable.of_nonneg_of_le (fun q => ?_) (fun q => ?_)
    (deningerPrimeInvSq_summable.mul_right (2 * T + 3 / Real.log 2))
  · have hq : (0 : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast q.2.pos
    have hlog := deningerPrimeLog_pos q
    have : (0 : ℝ) ≤ 2 * T + 3 / Real.log ((q : ℕ) : ℝ) := by positivity
    positivity
  · have hq : (0 : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast q.2.pos
    have hlog := deningerPrimeLog_pos q
    have hdiv : 3 / Real.log ((q : ℕ) : ℝ) ≤ 3 / Real.log 2 :=
      div_le_div_of_nonneg_left (by norm_num) hlog2 (deningerLog_two_le_primeLog q)
    have hpos : (0 : ℝ) < (((q : ℕ) : ℝ) ^ 2)⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_left (by linarith) hpos.le

/-- **At most linear mass growth on bounded frequency intervals.** -/
theorem deningerFloquetMeasure_Icc_le {T : ℝ} (hT : 0 ≤ T) :
    deningerFloquetMeasure (Set.Icc (-T) T)
      ≤ ENNReal.ofReal (∑' q : Nat.Primes,
          (((q : ℕ) : ℝ) ^ 2)⁻¹ * (2 * T + 3 / Real.log ((q : ℕ) : ℝ))) := by
  have hmeas : MeasurableSet (Set.Icc (-T) T) := measurableSet_Icc
  rw [deningerFloquetMeasure, Measure.sum_apply _ hmeas,
    ENNReal.ofReal_tsum_of_nonneg (fun q => ?_) (deningerFloquetMassTerm_summable hT)]
  · refine ENNReal.tsum_le_tsum fun q => ?_
    rw [Measure.smul_apply, smul_eq_mul, deningerFloquetWeight]
    have hstep := deningerFloquetLattice_Icc_le q hT
    have hq : (0 : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast q.2.pos
    have hlog := deningerPrimeLog_pos q
    have hwnn : (0 : ℝ) ≤ ((((q : ℕ)) : ℝ) ^ 2)⁻¹ / Real.log ((q : ℕ) : ℝ) := by positivity
    calc ENNReal.ofReal (((((q : ℕ)) : ℝ) ^ 2)⁻¹ / Real.log ((q : ℕ) : ℝ))
          * deningerFloquetLattice (q : ℕ) (Set.Icc (-T) T)
        ≤ ENNReal.ofReal (((((q : ℕ)) : ℝ) ^ 2)⁻¹ / Real.log ((q : ℕ) : ℝ))
          * ENNReal.ofReal (2 * T * Real.log ((q : ℕ) : ℝ) + 3) := by
          gcongr
      _ = ENNReal.ofReal ((((((q : ℕ)) : ℝ) ^ 2)⁻¹ / Real.log ((q : ℕ) : ℝ))
            * (2 * T * Real.log ((q : ℕ) : ℝ) + 3)) := (ENNReal.ofReal_mul hwnn).symm
      _ = ENNReal.ofReal ((((q : ℕ) : ℝ) ^ 2)⁻¹ * (2 * T + 3 / Real.log ((q : ℕ) : ℝ))) := by
          congr 1
          field_simp
  · have hq : (0 : ℝ) < ((q : ℕ) : ℝ) := by exact_mod_cast q.2.pos
    have hlog := deningerPrimeLog_pos q
    have : (0 : ℝ) ≤ 2 * T + 3 / Real.log ((q : ℕ) : ℝ) := by positivity
    positivity

theorem deningerFloquetMeasure_Icc_lt_top {T : ℝ} (hT : 0 ≤ T) :
    deningerFloquetMeasure (Set.Icc (-T) T) < ⊤ :=
  lt_of_le_of_lt (deningerFloquetMeasure_Icc_le hT) ENNReal.ofReal_lt_top

/-- **`μ_Fl` is locally finite.** -/
instance : IsFiniteMeasureOnCompacts deningerFloquetMeasure := by
  refine ⟨fun K hK => ?_⟩
  obtain ⟨T, hT⟩ := hK.isBounded.subset_closedBall (0 : ℝ)
  have hsub : K ⊆ Set.Icc (-|T|) |T| := by
    intro x hx
    have hx' := hT hx
    rw [Metric.mem_closedBall, Real.dist_eq, sub_zero] at hx'
    have habs : |x| ≤ |T| := le_trans hx' (le_abs_self T)
    rw [abs_le] at habs
    exact ⟨habs.1, habs.2⟩
  exact lt_of_le_of_lt (measure_mono hsub) (deningerFloquetMeasure_Icc_lt_top (abs_nonneg T))

end

end RHTower
