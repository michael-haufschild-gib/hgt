import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.ClockPhaseSectors
import GaloisForLFunctions.RHTower.LiouvilleDirichletSeries
import GaloisForLFunctions.RHTower.ReflectionCocycleClass
import GaloisForLFunctions.RHTower.ZetaRealStrip
import GaloisForLFunctions.HTGeometry.MeromorphicLaurentTranslation
import GaloisForLFunctions.ZeroForcingCalculus.WittMonomialsShiftedConvolutionsAndBrauerCancellation

/-!
# Parity of total prime occupation

Changing the sign of every prime gives an explicit phase sector orthogonal to
all clocks. Its continued partition has the dyadic difference of the original
divisor. A right-half-strip zero appears as a pole of the same multiplicity.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

open Filter Topology GaloisForLFunctions.HTGeometry
open GaloisForLFunctions.ZeroForcingCalculus

/-- The sign of the total number of occupied quanta, counted with multiplicity. -/
def primeParity : ℕ+ →* Circle where
  toFun n := (-1 : Circle) ^ ArithmeticFunction.cardFactors (n : ℕ)
  map_one' := by simp
  map_mul' m n := by rw [PNat.mul_coe, ArithmeticFunction.cardFactors_mul m.ne_zero n.ne_zero, pow_add]

theorem primeParity_prime (p : Nat.Primes) : primeParity (p : ℕ+) = -1 := by
  change (-1 : Circle) ^ ArithmeticFunction.cardFactors (p : ℕ) = -1
  rw [ArithmeticFunction.cardFactors_apply_prime p.property, pow_one]

private theorem primeParity_coeff (n : ℕ+) : (primeParity n : ℂ) = _root_.RHTower.liouvilleC n := by
  rw [_root_.RHTower.liouvilleC_apply, ArithmeticFunction.liouville_apply n.ne_zero]
  change (((-1 : Circle) ^ _ : Circle) : ℂ) = _
  simp only [Circle.coe_pow, Circle.coe_neg, Circle.coe_one, Int.cast_pow, Int.cast_neg, Int.cast_one]

/-- In the two-copy shell of total label n, parity cancels every state except
one net even state exactly when n is a square. -/
theorem parity_composition_shell (n : ℕ+) :
    ∑ d ∈ (n : ℕ).divisors, PNatBlock.extZero (fun m => (primeParity m : ℂ)) d =
      if IsSquare (n : ℕ) then 1 else 0 := by
  change _ = _root_.RHTower.squareIndicator (n : ℕ)
  rw [← _root_.RHTower.sum_divisors_liouvilleC n.ne_zero]
  apply Finset.sum_congr rfl
  intro d hd
  let m : ℕ+ := ⟨d,Nat.pos_of_mem_divisors hd⟩
  exact (PNatBlock.extZero_coe (fun k : ℕ+ => (primeParity k : ℂ)) m).trans (primeParity_coeff m)

/-- Meromorphic parity-inserted partition. -/
def parityPartition (s : ℂ) := riemannZeta (2*s) / riemannZeta s

theorem parity_trace (s : {z : ℂ // 1 < z.re}) : insertedPartition primeParity s = parityPartition s.val := by
  have hser : insertedPartition primeParity s = LSeries (fun n => _root_.RHTower.liouvilleC n) s.val := by
    rw [insertedPartition_eq_series, LSeries, ← PNatBlock.tsum_pnat _ (LSeries.term_zero _ _)]
    apply tsum_congr
    intro n
    rw [primeParity_coeff, heat_eq_cpow, Complex.cpow_neg, LSeries.term_of_ne_zero n.ne_zero, div_eq_mul_inv]
  rw [hser, parityPartition, eq_div_iff (riemannZeta_ne_zero_of_one_lt_re s.property)]
  exact _root_.RHTower.LSeries_liouvilleC_mul_riemannZeta s.property

/-- Composing the parity trace and the ordinary trace gives the double-energy partition. -/
theorem parity_composition_trace (s : {z : ℂ // 1 < z.re}) :
    insertedPartition primeParity s * ContinuousLinearMap.opTrace (gibbsOperator s) = riemannZeta (2*s.val) := by
  rw [parity_trace, partition_eq_zeta, parityPartition, div_mul_cancel₀ _ (riemannZeta_ne_zero_of_one_lt_re s.property)]

theorem parity_clock_overlap (t : ℝ) (β : TraceTemperature) :
    phaseOverlap (clockPhase t) primeParity β =
      parityPartition ((β.val : ℂ)+(t : ℂ)*Complex.I) / riemannZeta β.val := by
  rw [phaseOverlap_clock_inserted, parity_trace]

/-- All Hamiltonian clocks become orthogonal to the coherent parity preparation. -/
theorem parity_clock_overlap_limit (t : ℝ) :
    Tendsto (phaseOverlap (clockPhase t) primeParity) atPartitionPole (𝓝 0) := by
  have hb := tendsto_temperature_punctured.mono_right nhdsWithin_le_nhds
  let q := 1+(t : ℂ)*Complex.I
  have hd : 2*q ≠ 1 := by
    intro h
    have hr := congrArg Complex.re h
    norm_num [q,Complex.mul_re] at hr
  have hq := hb.add_const ((t : ℂ)*Complex.I)
  have hnum := (differentiableAt_riemannZeta hd).continuousAt.tendsto.comp (hq.const_mul 2)
  by_cases ht : t = 0
  · subst t
    have h := (hnum.mul inverse_partition_limit).mul inverse_partition_limit
    rw [mul_zero] at h
    exact h.congr fun β => by simp only [parity_clock_overlap, parityPartition, Complex.ofReal_zero,
      zero_mul, add_zero, div_eq_mul_inv, Function.comp_apply]
  · have hreg : q ≠ 1 := by
      intro h
      have hi := congrArg Complex.im h
      simp [q] at hi
      exact ht hi
    have hden := (differentiableAt_riemannZeta hreg).continuousAt.tendsto.comp hq
    have h := (hnum.div hden (riemannZeta_ne_zero_of_one_le_re (by simp [q] : 1 ≤ q.re))).mul
      inverse_partition_limit
    rw [mul_zero] at h
    exact h.congr fun β => by rw [parity_clock_overlap, parityPartition, div_eq_mul_inv _ (riemannZeta β.val)]; rfl

theorem primeParity_has_no_clock (t : ℝ) : ¬samePhaseSector primeParity (clockPhase t) :=
  fun hs => ((phaseOverlap_zero_iff _ _).mp (parity_clock_overlap_limit t)) ((samePhaseSector_symm _ _).mp hs)

theorem parityPartition_meromorphic (s : ℂ) : MeromorphicAt parityPartition s :=
  (meromorphicOrderAt_riemannZeta_const_mul two_ne_zero s).1.div (ZeroForcingCalculus.meromorphicAt_riemannZeta s)

/-- The parity divisor is the dyadic difference of the ordinary partition divisor. -/
theorem parityPartition_order (s : ℂ) :
    meromorphicOrderAt parityPartition s = meromorphicOrderAt riemannZeta (2*s) - meromorphicOrderAt riemannZeta s := by
  have hd := meromorphicOrderAt_riemannZeta_const_mul (c := 2) two_ne_zero s
  change meromorphicOrderAt ((fun w : ℂ => riemannZeta (2*w)) / riemannZeta) s = _
  rw [meromorphicOrderAt_div hd.1 (ZeroForcingCalculus.meromorphicAt_riemannZeta s), hd.2]

/-- Adding parity orders along successive doublings cancels all intermediate divisors. -/
theorem parityPartition_dyadic_orders (s : ℂ) (k : ℕ) :
    ∑ j ∈ Finset.range k, meromorphicOrderAt parityPartition (2^j*s) =
      meromorphicOrderAt riemannZeta (2^k*s) - meromorphicOrderAt riemannZeta s := by
  let v (z : ℂ) := (meromorphicOrderAt riemannZeta z).untop (meromorphicOrderAt_riemannZeta_ne_top z)
  have h (z : ℂ) : (v z : WithTop ℤ) = meromorphicOrderAt riemannZeta z := WithTop.coe_untop _ _
  have step (z : ℂ) : meromorphicOrderAt parityPartition z = ((v (2*z) - v z : ℤ) : WithTop ℤ) := by
    rw [parityPartition_order, WithTop.LinearOrderedAddCommGroup.coe_sub, h, h]
  rw [← h (2^k*s), ← h s, ← WithTop.LinearOrderedAddCommGroup.coe_sub]
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Finset.sum_range_succ, ih, step]
    have hd : 2*(2^k*s) = 2^(k+1)*s := by rw [pow_succ]; ring
    rw [hd]
    change (((v (2^k*s) - v s) + (v (2^(k+1)*s) - v (2^k*s)) : ℤ) : WithTop ℤ) = _
    congr 1
    abel

/-- Once the doubled argument enters the trace half-plane, finitely many measured
parity orders recover the full multiplicity of the original partition germ. -/
theorem partition_order_from_parity (s : ℂ) (k : {j : ℕ // 1 < (2^j*s).re}) :
    ∑ j ∈ Finset.range k.val, meromorphicOrderAt parityPartition (2^j*s) = -meromorphicOrderAt riemannZeta s := by
  have hn : 2^k.val*s ≠ 1 := fun h => k.property.ne' (by rw [h]; rfl)
  rw [parityPartition_dyadic_orders, meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero
    (HTGeometry.analyticAt_riemannZeta hn) (riemannZeta_ne_zero_of_one_lt_re k.property), zero_sub]

theorem parityPartition_order_right (s : {w : ℂ // 1/2 < w.re}) :
    meromorphicOrderAt parityPartition s.val = -meromorphicOrderAt riemannZeta s.val := by
  have hr : 1 < (2*s.val).re := by rw [two_mul, Complex.add_re]; linarith only [s.property]
  have hn : 2*s.val ≠ 1 := fun h => hr.ne' (by rw [h]; rfl)
  rw [parityPartition_order, meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero
    (HTGeometry.analyticAt_riemannZeta hn) (riemannZeta_ne_zero_of_one_lt_re hr), zero_sub]

theorem rh_iff_parity_has_no_right_strip_pole :
    RiemannHypothesis ↔ ∀ s : {w : ℂ // 1/2 < w.re ∧ w.re < 1}, 0 ≤ meromorphicOrderAt parityPartition s.val := by
  rw [_root_.RHTower.riemannHypothesis_iff_riemannZeta_ne_zero_of_mem_upper_strip]
  constructor
  · intro h s
    have h1 : s.val ≠ 1 := fun he => s.property.2.ne (by rw [he]; rfl)
    rw [parityPartition_order_right ⟨_,s.property.1⟩, meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero
      (HTGeometry.analyticAt_riemannZeta h1) (h _ s.property.1 s.property.2), neg_zero]
  · intro h z hz hz1 hzero
    have h1 : z ≠ 1 := fun h => hz1.ne (by rw [h]; rfl)
    have hp := meromorphicOrderAt_pos_of_analyticAt_eq_zero (HTGeometry.analyticAt_riemannZeta h1) hzero
    have hm := h ⟨z,hz,hz1⟩
    rw [parityPartition_order_right ⟨z,hz⟩] at hm
    lift meromorphicOrderAt riemannZeta z to ℤ using meromorphicOrderAt_riemannZeta_ne_top z with n
    have hp' : (0 : ℤ) < n := by exact_mod_cast hp
    have hm' : (0 : ℤ) ≤ -n := by exact_mod_cast hm
    omega

private theorem positive_real_zeta_order (x : ℝ) (hx : 0 < x) :
    meromorphicOrderAt riemannZeta (x : ℂ) = if x=1 then -1 else 0 := by
  by_cases h : x=1
  · subst x
    rw [Complex.ofReal_one, if_pos rfl]
    exact meromorphicOrderAt_riemannZeta_one.trans (WithTop.LinearOrderedAddCommGroup.coe_neg (1 : ℤ))
  · rw [if_neg h]
    apply meromorphicOrderAt_eq_zero_of_analyticAt_ne_zero (HTGeometry.analyticAt_riemannZeta (by exact_mod_cast h))
    rcases lt_or_ge x 1 with hlt | hge
    · exact _root_.RHTower.riemannZeta_real_strip_ne_zero hx hlt
    · exact riemannZeta_ne_zero_of_one_le_re hge

/-- The signed trace has one positive real pole and one positive real zero, both simple. -/
theorem parityPartition_positive_order (x : {r : ℝ // 0 < r}) :
    meromorphicOrderAt parityPartition (x.val : ℂ) =
      if x.val=1/2 then -1 else if x.val=1 then 1 else 0 := by
  have hd : 2*(x.val : ℂ) = ((2*x.val : ℝ) : ℂ) := by push_cast; rfl
  have he : 2*x.val=1 ↔ x.val=1/2 := by constructor <;> intro h <;> linarith only [h]
  rw [parityPartition_order, hd, positive_real_zeta_order _ (mul_pos zero_lt_two x.property),
    positive_real_zeta_order _ x.property]
  simp only [he]
  by_cases hh : x.val=1/2
  · have h1 : x.val ≠ 1 := by rw [hh]; norm_num
    norm_num [hh,h1]
  · simp only [if_neg hh]
    split_ifs <;> simp

/-- Continuation of parity measured with the Hamiltonian phase at time t. -/
def clockedParityPartition (t : ℝ) (s : ℂ) := parityPartition (s + -((t : ℂ)*Complex.I))

theorem clockedParity_trace (t : ℝ) (s : {z : ℂ // 1 < z.re}) :
    insertedPartition (primeParity * clockPhase t) s = clockedParityPartition t s.val := by
  let w : {z : ℂ // 1 < z.re} := ⟨s.val + -((t : ℂ)*Complex.I), by simpa using s.property⟩
  change _ = parityPartition w.val
  rw [← parity_trace w, insertedPartition_eq_series, insertedPartition_eq_series]
  apply tsum_congr
  intro n
  have hc : heat (-((t : ℂ)*Complex.I)) n = (clockPhase t n : ℂ) := by
    change Complex.exp (-(-((t : ℂ)*Complex.I))*(energy n : ℂ)) = Complex.exp (((t*energy n : ℝ) : ℂ)*Complex.I)
    rw [neg_neg, Complex.ofReal_mul]
    congr 1
    ring
  change ((primeParity n * clockPhase t n : Circle) : ℂ) * heat s.val n =
    (primeParity n : ℂ) * heat (s.val + -((t : ℂ)*Complex.I)) n
  rw [Circle.coe_mul, heat_add, hc]
  ring

/-- At matched Hamiltonian time a parity pole detects precisely the isometry of quantum composition. -/
theorem parity_pole_iff_split_isometric (s : {w : ℂ // 0 < w.re}) :
    meromorphicOrderAt (clockedParityPartition s.val.im) s.val < 0 ↔
      ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s.val f x := by
  have hreal : s.val + -((s.val.im : ℂ)*Complex.I) = (s.val.re : ℂ) := by
    rw [← sub_eq_add_neg, sub_eq_iff_eq_add, Complex.re_add_im]
  rw [split_isometric_iff]
  change meromorphicOrderAt (fun z : ℂ => parityPartition (z + -((s.val.im : ℂ)*Complex.I))) s.val < 0 ↔ _
  rw [HTGeometry.meromorphicOrderAt_comp_add, hreal,
    parityPartition_positive_order ⟨_,s.property⟩]
  by_cases h : s.val.re=1/2
  · rw [if_pos h]
    refine iff_of_true ?_ h
    rw [← WithTop.LinearOrderedAddCommGroup.coe_neg (1 : ℤ)]
    exact WithTop.coe_lt_coe.mpr (neg_one_lt_zero : (-1 : ℤ) < 0)
  · rw [if_neg h]
    refine iff_of_false ?_ h
    split_ifs
    · exact not_lt_of_ge zero_le_one
    · exact lt_irrefl _

#print axioms primeParity_prime
#print axioms parity_composition_shell
#print axioms parity_trace
#print axioms parity_composition_trace
#print axioms parity_clock_overlap_limit
#print axioms primeParity_has_no_clock
#print axioms parityPartition_meromorphic
#print axioms parityPartition_order
#print axioms parityPartition_dyadic_orders
#print axioms partition_order_from_parity
#print axioms parityPartition_order_right
#print axioms rh_iff_parity_has_no_right_strip_pole
#print axioms parityPartition_positive_order
#print axioms clockedParity_trace
#print axioms parity_pole_iff_split_isometric

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
