import GaloisForLFunctions.TransHorizonIncidenceMechanics.APaidReceiverContinuesTheDirichletSeriesAcrossItsAbscissa
import Mathlib.NumberTheory.LSeries.PrimesInAP

/-!
# Residue-class flips and the prime-density laws of the receiver

For `q ≥ 1` and `S ⊆ ZMod q` let `f_{q,S}` be the completely multiplicative `±1` pattern with
`f(p) = −1` exactly at the primes `p` whose residue mod `q` lies in `S` (`residueFlip`). Its flipped
primes have an exact logarithmic Dirichlet density: with `ρ = #(S ∩ (ZMod q)ˣ)/φ(q)`,

`|Σ_{p mod q ∈ S} p^{-w} − ρ log(1/(w − 1))| ≤ B`  on `1 < w < 3/2`

(`exists_abs_tsum_residueFlip_sub_le`). For one unit class `a` this is the integrated form of
`Σ_n Λ_a(n) n^{-x} = φ(q)^{-1}/(x − 1) + O(1)` (Dirichlet's theorem in Mathlib's form,
`ArithmeticFunction.vonMangoldt.eqOn_LFunctionResidueClassAux`): the prime powers contribute
`O(1)`, and `p^{-w} − p^{-3/2} = ∫_w^{3/2} log p · p^{-t} dt` interchanges with the sum by dominated
convergence. Classes of non-units contain only primes dividing `q`.

This discharges the density premise of the two prime-density laws of the receiver:

* **half damping** (`not_receiverBounded_residueFlip_half`): if `4 #(S ∩ (ZMod q)ˣ) < φ(q)`, the
  weight `f_{q,S}(d) d^{-1/2}` is unpaid;
* **below half damping** (`not_receiverBounded_residueFlip`): for `0 < ε < 1/2`, if `ρ ≠ 1/2` and
  `ρ < 1`, the weight `f_{q,S}(d) d^{-ε}` is unpaid.

So for residue-class sign patterns the receiver reads the arithmetic density of the flipped classes:
at half damping every pattern flipping less than a quarter of the classes is unpaid, and below it
only the densities `1/2` and `1` can be paid.
-/

open Filter Topology MeasureTheory Set
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### The residue-class flip -/

/-- The completely multiplicative pattern `n ↦ (−1)^{#(prime factors of n, with multiplicity,
whose residue mod q lies in S)}`. -/
def residueFlip (q : ℕ) (S : Finset (ZMod q)) : ℕ →*₀ ℝ where
  toFun n := if n = 0 then 0 else
    (-1) ^ (n.primeFactorsList.filter (fun p : ℕ => decide ((p : ZMod q) ∈ S))).length
  map_zero' := by simp
  map_one' := by simp
  map_mul' m n := by
    rcases eq_or_ne m 0 with rfl | hm
    · simp
    rcases eq_or_ne n 0 with rfl | hn
    · simp
    simp only [mul_ne_zero hm hn, hm, hn, if_false]
    rw [((Nat.perm_primeFactorsList_mul hm hn).filter _).length_eq, List.filter_append,
      List.length_append, pow_add]

theorem residueFlip_prime (q : ℕ) (S : Finset (ZMod q)) {p : ℕ} (hp : p.Prime) :
    residueFlip q S p = if (p : ZMod q) ∈ S then -1 else 1 := by
  simp only [residueFlip, MonoidWithZeroHom.coe_mk, ZeroHom.coe_mk, hp.ne_zero, if_false,
    Nat.primeFactorsList_prime hp]
  split_ifs with h <;> simp_all

theorem residueFlip_prime_eq_neg_one_iff (q : ℕ) (S : Finset (ZMod q)) {p : ℕ} (hp : p.Prime) :
    residueFlip q S p = -1 ↔ (p : ZMod q) ∈ S := by
  rw [residueFlip_prime q S hp]
  split_ifs with h <;> norm_num [h]

theorem residueFlip_prime_eq_one_or (q : ℕ) (S : Finset (ZMod q)) {p : ℕ} (hp : p.Prime) :
    residueFlip q S p = 1 ∨ residueFlip q S p = -1 := by
  rw [residueFlip_prime q S hp]
  split_ifs <;> simp

/-! ### One unit class: `Σ_{p ≡ a} p^{-w} = φ(q)^{-1} log(1/(w − 1)) + O(1)` -/

section unitClass

open ArithmeticFunction ArithmeticFunction.vonMangoldt

variable {q : ℕ} [NeZero q] {a : ZMod q}

/-- **The residue-class von Mangoldt series**: `Σ_n Λ_a(n) n^{-x} = φ(q)^{-1}/(x − 1) + O(1)` on
`(1, 2]`, two-sided. -/
theorem exists_abs_tsum_residueClass_sub_le (ha : IsUnit a) :
    ∃ C : ℝ, ∀ x : ℝ, 1 < x → x ≤ 2 →
      |∑' n, residueClass a n / (n : ℝ) ^ x - (q.totient : ℝ)⁻¹ / (x - 1)| ≤ C := by
  have H {x : ℝ} (hx : 1 < x) :
      ∑' n, residueClass a n / (n : ℝ) ^ x =
        (LFunctionResidueClassAux a x).re + (q.totient : ℝ)⁻¹ / (x - 1) := by
    refine Complex.ofReal_injective ?_
    simp only [Complex.ofReal_tsum, Complex.ofReal_div, Complex.ofReal_cpow (Nat.cast_nonneg _),
      Complex.ofReal_natCast, Complex.ofReal_add, Complex.ofReal_inv, Complex.ofReal_sub,
      Complex.ofReal_one]
    simp_rw [← LFunctionResidueClassAux_real ha hx,
      eqOn_LFunctionResidueClassAux ha <| Set.mem_setOf.mpr (Complex.ofReal_re x ▸ hx),
      sub_add_cancel, LSeries, LSeries.term]
    refine tsum_congr fun n ↦ ?_
    split_ifs with hn
    · simp only [hn, residueClass_apply_zero, Complex.ofReal_zero, zero_div]
    · rfl
  have hc : ContinuousOn (fun x : ℝ ↦ (LFunctionResidueClassAux a x).re) (Set.Icc 1 2) :=
    Complex.continuous_re.continuousOn.comp (t := Set.univ)
      (continuousOn_LFunctionResidueClassAux a) (fun ⦃x⦄ _ ↦ trivial) |>.comp
      Complex.continuous_ofReal.continuousOn fun x hx ↦ by
        simpa only [Set.mem_setOf_eq, Complex.ofReal_re] using hx.1
  obtain ⟨C, hC⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨C, fun x hx hx2 => ?_⟩
  rw [H hx, add_sub_cancel_right]
  exact hC x ⟨hx.le, hx2⟩

/-- The prime part `g(n) = [n prime, n ≡ a] log n` of `Λ_a`. -/
def primeResidueLog (a : ZMod q) (n : ℕ) : ℝ := if n.Prime then residueClass a n else 0

omit [NeZero q] in
theorem primeResidueLog_nonneg (n : ℕ) : 0 ≤ primeResidueLog a n := by
  unfold primeResidueLog; split_ifs
  · exact residueClass_nonneg a n
  · exact le_rfl

omit [NeZero q] in
theorem primeResidueLog_le (n : ℕ) : primeResidueLog a n ≤ Real.log n := by
  unfold primeResidueLog; split_ifs with hn
  · exact (residueClass_le a n).trans (vonMangoldt_le_log)
  · exact Real.log_natCast_nonneg n

/-- The indicator `[n prime, n ≡ a]`. -/
def primeResidueInd (a : ZMod q) (n : ℕ) : ℝ := if n.Prime ∧ (n : ZMod q) = a then 1 else 0

omit [NeZero q] in
theorem primeResidueLog_eq (n : ℕ) : primeResidueLog a n = primeResidueInd a n * Real.log n := by
  unfold primeResidueLog primeResidueInd residueClass
  by_cases hp : n.Prime
  · by_cases hn : (n : ZMod q) = a
    · simp [hp, hn, vonMangoldt_apply_prime hp]
    · simp [hp, hn]
  · simp [hp]

theorem summable_log_div_rpow {x : ℝ} (hx : 1 < x) :
    Summable (fun n : ℕ => Real.log n / (n : ℝ) ^ x) := by
  -- `log n ≤ n^{(x−1)/2} · 2/(x−1)` against `Σ n^{-(x+1)/2}`
  set ε : ℝ := (x - 1) / 2
  have hε : 0 < ε := by simp only [ε]; linarith
  refine ((Real.summable_nat_rpow.mpr (show -(x - ε) < -1 by simp only [ε]; linarith)).mul_left
    (1 / ε)).of_nonneg_of_le (fun n => by positivity) fun n => ?_
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp only [Nat.cast_zero, Real.log_zero, zero_div]
    exact mul_nonneg (by positivity) (Real.rpow_nonneg le_rfl _)
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hlog := Real.log_le_rpow_div hn0.le hε
  rw [div_le_iff₀ (Real.rpow_pos_of_pos hn0 _)]
  calc Real.log n ≤ (n : ℝ) ^ ε / ε := hlog
    _ = 1 / ε * (n : ℝ) ^ (-(x - ε)) * (n : ℝ) ^ x := by
        rw [mul_assoc, ← Real.rpow_add hn0]; ring_nf

omit [NeZero q] in
theorem summable_primeResidueLog_div {x : ℝ} (hx : 1 < x) :
    Summable (fun n : ℕ => primeResidueLog a n / (n : ℝ) ^ x) :=
  (summable_log_div_rpow hx).of_nonneg_of_le
    (fun n => div_nonneg (primeResidueLog_nonneg n) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
    fun n => div_le_div_of_nonneg_right (primeResidueLog_le n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- **The prime part of the residue-class series**: `Σ_{p ≡ a} log p · p^{-x} = φ(q)^{-1}/(x − 1)
+ O(1)` on `(1, 2]`; the prime powers contribute at most `Σ_{n not prime} Λ_a(n)/n`. -/
theorem exists_abs_tsum_primeResidueLog_sub_le (ha : IsUnit a) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, 1 < x → x ≤ 2 →
      |∑' n, primeResidueLog a n / (n : ℝ) ^ x - (q.totient : ℝ)⁻¹ / (x - 1)| ≤ C := by
  obtain ⟨C₁, hC₁⟩ := exists_abs_tsum_residueClass_sub_le ha
  set C₀ := ∑' n : ℕ, (if n.Prime then 0 else residueClass a n) / n
  have hC₀ : 0 ≤ C₀ := tsum_nonneg fun n => by positivity [residueClass_nonneg a n]
  refine ⟨|C₁| + C₀, by positivity, fun x hx hx2 => ?_⟩
  have hsplit : ∀ n : ℕ, residueClass a n / (n : ℝ) ^ x =
      primeResidueLog a n / (n : ℝ) ^ x + (if n.Prime then 0 else residueClass a n) / (n : ℝ) ^ x :=
    fun n => by unfold primeResidueLog; split_ifs <;> ring
  have hnp : Summable (fun n : ℕ => (if n.Prime then 0 else residueClass a n) / (n : ℝ) ^ x) :=
    (summable_residueClass_non_primes_div a).of_nonneg_of_le
      (fun n => by positivity [residueClass_nonneg a n]) fun n => by
        rcases Nat.eq_zero_or_pos n with rfl | hn
        · simp
        refine div_le_div_of_nonneg_left (by positivity [residueClass_nonneg a n])
          (by exact_mod_cast hn) ?_
        calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
          _ ≤ (n : ℝ) ^ x := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hx.le
  have hnp_le : ∑' n : ℕ, (if n.Prime then 0 else residueClass a n) / (n : ℝ) ^ x ≤ C₀ :=
    Summable.tsum_le_tsum (fun n => by
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp
      refine div_le_div_of_nonneg_left (by positivity [residueClass_nonneg a n])
        (by exact_mod_cast hn) ?_
      calc (n : ℝ) = (n : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
        _ ≤ (n : ℝ) ^ x := Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) hx.le)
      hnp (summable_residueClass_non_primes_div a)
  have hnp0 : 0 ≤ ∑' n : ℕ, (if n.Prime then 0 else residueClass a n) / (n : ℝ) ^ x :=
    tsum_nonneg fun n => by positivity [residueClass_nonneg a n]
  have htot : ∑' n, residueClass a n / (n : ℝ) ^ x =
      ∑' n, primeResidueLog a n / (n : ℝ) ^ x +
        ∑' n : ℕ, (if n.Prime then 0 else residueClass a n) / (n : ℝ) ^ x := by
    rw [tsum_congr hsplit, (summable_primeResidueLog_div hx).tsum_add hnp]
  have h1 := hC₁ x hx hx2
  rw [htot] at h1
  rw [abs_le] at h1 ⊢
  constructor <;> linarith [le_abs_self C₁, neg_abs_le C₁]

/-- `∫_w^b log n · n^{-t} dt = n^{-w} − n^{-b}` for `n ≥ 1`. -/
theorem integral_log_mul_rpow_neg {n : ℕ} (hn : 1 ≤ n) (w b : ℝ) :
    ∫ t in w..b, Real.log n * (n : ℝ) ^ (-t) = (n : ℝ) ^ (-w) - (n : ℝ) ^ (-b) := by
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have hderiv : ∀ t ∈ uIcc w b,
      HasDerivAt (fun t : ℝ => -(n : ℝ) ^ (-t)) (Real.log n * (n : ℝ) ^ (-t)) t := by
    intro t _
    have h1 : HasDerivAt (fun t : ℝ => (n : ℝ) ^ (-t)) ((n : ℝ) ^ (-t) * Real.log n * (-1)) t :=
      (Real.hasStrictDerivAt_const_rpow hn0 (-t)).hasDerivAt.comp t (hasDerivAt_neg t)
    exact h1.neg.congr_deriv (by ring)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv]
  · ring
  · exact (continuous_const.mul (continuous_const.rpow continuous_neg
      fun _ => Or.inl hn0.ne')).intervalIntegrable _ _

/-- **One unit class**: `|Σ_{p ≡ a} p^{-w} − φ(q)^{-1} log(1/(w − 1))| ≤ B` on `1 < w < 3/2`. -/
theorem exists_abs_tsum_primeResidueInd_sub_le (ha : IsUnit a) :
    ∃ B : ℝ, ∀ w : ℝ, 1 < w → w < 3 / 2 →
      |∑' n, primeResidueInd a n / (n : ℝ) ^ w - (q.totient : ℝ)⁻¹ * Real.log (1 / (w - 1))| ≤ B := by
  obtain ⟨C, hC0, hC⟩ := exists_abs_tsum_primeResidueLog_sub_le ha
  set Z := ∑' n : ℕ, 1 / (n : ℝ) ^ (3 / 2 : ℝ)
  have hZs : Summable (fun n : ℕ => 1 / (n : ℝ) ^ (3 / 2 : ℝ)) :=
    Real.summable_one_div_nat_rpow.mpr (by norm_num)
  set φ := (q.totient : ℝ)⁻¹
  have hφ : 0 ≤ φ := inv_nonneg.mpr (Nat.cast_nonneg _)
  refine ⟨φ * Real.log 2 + C + Z, fun w hw hw2 => ?_⟩
  have hInd0 : ∀ n, 0 ≤ primeResidueInd a n := fun n => by
    unfold primeResidueInd; split_ifs <;> norm_num
  have hInd1 : ∀ n, primeResidueInd a n ≤ 1 := fun n => by
    unfold primeResidueInd; split_ifs <;> norm_num
  have hsumI : ∀ x : ℝ, 1 < x → Summable (fun n : ℕ => primeResidueInd a n / (n : ℝ) ^ x) :=
    fun x hx => (Real.summable_one_div_nat_rpow.mpr hx).of_nonneg_of_le
      (fun n => div_nonneg (hInd0 n) (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      fun n => div_le_div_of_nonneg_right (hInd1 n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  -- the interchange `Σ_n g(n)(n^{-w} − n^{-3/2}) = ∫_w^{3/2} Σ_n g(n) log n · n^{-t} dt`
  set F : ℕ → ℝ → ℝ := fun n t => primeResidueLog a n * (n : ℝ) ^ (-t)
  set L : ℝ → ℝ := fun t => ∑' n, primeResidueLog a n / (n : ℝ) ^ t
  have hlog0 : primeResidueLog a 0 = 0 := by simp [primeResidueLog, Nat.not_prime_zero]
  have hFdiv : ∀ n t, F n t = primeResidueLog a n / (n : ℝ) ^ t := fun n t => by
    simp only [F]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hlog0]
    · rw [Real.rpow_neg (Nat.cast_nonneg n), div_eq_mul_inv]
  have hint : HasSum (fun n => ∫ t in w..(3 / 2 : ℝ), F n t) (∫ t in w..(3 / 2 : ℝ), L t) := by
    refine intervalIntegral.hasSum_integral_of_dominated_convergence
      (fun n _ => primeResidueLog a n / (n : ℝ) ^ w) (fun n => ?_) (fun n => ?_) ?_
      intervalIntegrable_const ?_
    · exact (measurable_const.mul (measurable_const.pow measurable_neg)).aestronglyMeasurable
    · filter_upwards with t ht
      rw [uIoc_of_le hw2.le] at ht
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (primeResidueLog_nonneg n)
        (Real.rpow_nonneg (Nat.cast_nonneg n) _))]
      rcases Nat.eq_zero_or_pos n with rfl | hn
      · simp [hlog0]
      have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      rw [div_eq_mul_inv, ← Real.rpow_neg hn0.le]
      exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn)
        (by linarith [ht.1])) (primeResidueLog_nonneg n)
    · exact Eventually.of_forall fun _ _ => summable_primeResidueLog_div hw
    · filter_upwards with t ht
      rw [uIoc_of_le hw2.le] at ht
      have ht1 : 1 < t := by linarith [ht.1]
      have hfun : (fun n => F n t) = fun n => primeResidueLog a n / (n : ℝ) ^ t :=
        funext fun n => hFdiv n t
      rw [hfun]
      exact (summable_primeResidueLog_div ht1).hasSum
  have hpiece : ∀ n, ∫ t in w..(3 / 2 : ℝ), F n t =
      primeResidueInd a n / (n : ℝ) ^ w - primeResidueInd a n / (n : ℝ) ^ (3 / 2 : ℝ) := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [F, hlog0, primeResidueInd, Nat.not_prime_zero]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    simp only [F, primeResidueLog_eq, mul_assoc]
    rw [intervalIntegral.integral_const_mul, integral_log_mul_rpow_neg hn,
      Real.rpow_neg hn0.le, Real.rpow_neg hn0.le]
    ring
  have hsw := hsumI w hw
  have hs32 := hsumI (3 / 2) (by norm_num)
  have hdiff : ∑' n, primeResidueInd a n / (n : ℝ) ^ w -
      ∑' n, primeResidueInd a n / (n : ℝ) ^ (3 / 2 : ℝ) = ∫ t in w..(3 / 2 : ℝ), L t := by
    rw [← hsw.tsum_sub hs32, ← hint.tsum_eq]
    exact tsum_congr fun n => (hpiece n).symm
  -- `L(t) = φ/(t − 1) + O(1)` on `[w, 3/2]`
  have hLb : ∀ t ∈ Set.Icc w (3 / 2 : ℝ), |L t - φ / (t - 1)| ≤ C := fun t ht =>
    hC t (by linarith [ht.1]) (by linarith [ht.2])
  have hLanti : AntitoneOn L (uIcc w (3 / 2 : ℝ)) := by
    intro t ht t' ht' htt'
    rw [uIcc_of_le hw2.le] at ht ht'
    refine Summable.tsum_le_tsum (fun n => ?_) (summable_primeResidueLog_div (by linarith [ht'.1]))
      (summable_primeResidueLog_div (by linarith [ht.1]))
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [hlog0]
    have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    exact div_le_div_of_nonneg_left (primeResidueLog_nonneg n) (Real.rpow_pos_of_pos hn0 _)
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hn) htt')
  have hLint : IntervalIntegrable L volume w (3 / 2) := hLanti.intervalIntegrable
  have hpole : IntervalIntegrable (fun t : ℝ => φ / (t - 1)) volume w (3 / 2) := by
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.div (continuousOn_id.sub continuousOn_const) fun t ht => ?_
    rw [uIcc_of_le hw2.le] at ht
    have : 0 < t - 1 := by linarith [ht.1]
    exact this.ne'
  have hpoleval : ∫ t in w..(3 / 2 : ℝ), φ / (t - 1) =
      φ * (Real.log (1 / (w - 1)) - Real.log 2) := by
    have hw1 : 0 < w - 1 := by linarith
    simp_rw [div_eq_mul_inv φ]
    rw [intervalIntegral.integral_const_mul,
      intervalIntegral.integral_comp_sub_right (fun x : ℝ => x⁻¹) (1 : ℝ),
      integral_inv_of_pos hw1 (by norm_num)]
    congr 1
    rw [show (3 / 2 : ℝ) - 1 = 2⁻¹ by norm_num, div_eq_mul_inv, mul_comm, ← div_eq_mul_inv,
      one_div, Real.log_div (by positivity) (by norm_num), Real.log_inv]
  have hup : ∫ t in w..(3 / 2 : ℝ), L t ≤ ∫ t in w..(3 / 2 : ℝ), (φ / (t - 1) + C) := by
    refine intervalIntegral.integral_mono_on hw2.le hLint (hpole.add intervalIntegrable_const)
      fun t ht => ?_
    linarith [(abs_le.mp (hLb t ht)).2]
  have hlo : ∫ t in w..(3 / 2 : ℝ), (φ / (t - 1) - C) ≤ ∫ t in w..(3 / 2 : ℝ), L t := by
    refine intervalIntegral.integral_mono_on hw2.le (hpole.sub intervalIntegrable_const) hLint
      fun t ht => ?_
    linarith [(abs_le.mp (hLb t ht)).1]
  rw [intervalIntegral.integral_add hpole intervalIntegrable_const, intervalIntegral.integral_const,
    smul_eq_mul, hpoleval] at hup
  rw [intervalIntegral.integral_sub hpole intervalIntegrable_const, intervalIntegral.integral_const,
    smul_eq_mul, hpoleval] at hlo
  -- the value at `3/2` lies in `[0, Z]`
  have hP0 : 0 ≤ ∑' n, primeResidueInd a n / (n : ℝ) ^ (3 / 2 : ℝ) :=
    tsum_nonneg fun n => div_nonneg (hInd0 n) (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have hPZ : ∑' n, primeResidueInd a n / (n : ℝ) ^ (3 / 2 : ℝ) ≤ Z :=
    Summable.tsum_le_tsum (fun n => div_le_div_of_nonneg_right (hInd1 n)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)) hs32 hZs
  have hlog2 : 0 ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hφlog : 0 ≤ φ * Real.log 2 := mul_nonneg hφ hlog2
  have hwC : (3 / 2 - w) * C ≤ C := by nlinarith
  have hwC0 : 0 ≤ (3 / 2 - w) * C := mul_nonneg (by linarith) hC0
  rw [abs_le]
  constructor <;> nlinarith

end unitClass

/-! ### Union of classes -/

section union

open ArithmeticFunction.vonMangoldt

variable {q : ℕ} [NeZero q]

/-- A class of non-units contains only primes dividing `q`: `Σ_{p ≡ a} p^{-w} ∈ [0, q + 1]`. -/
theorem tsum_primeResidueInd_mem_of_not_isUnit {a : ZMod q} (ha : ¬ IsUnit a) {w : ℝ}
    (hw : 1 < w) :
    0 ≤ ∑' n, primeResidueInd a n / (n : ℝ) ^ w ∧
      ∑' n, primeResidueInd a n / (n : ℝ) ^ w ≤ q + 1 := by
  have hsupp : ∀ n ∉ Finset.range (q + 1), primeResidueInd a n / (n : ℝ) ^ w = 0 := by
    intro n hn
    unfold primeResidueInd
    split_ifs with h
    · exfalso
      obtain ⟨hp, hna⟩ := h
      apply hn
      rw [Finset.mem_range, Nat.lt_succ_iff]
      -- a prime not dividing `q` is a unit mod `q`
      by_contra hnq
      apply ha
      rw [← hna]
      refine (ZMod.isUnit_iff_coprime n q).mpr ((Nat.Prime.coprime_iff_not_dvd hp).mpr ?_)
      intro hdvd
      exact hnq (Nat.le_of_dvd (Nat.pos_of_ne_zero (NeZero.ne q)) hdvd)
    · simp
  rw [tsum_eq_sum hsupp]
  have h0 : ∀ n, 0 ≤ primeResidueInd a n / (n : ℝ) ^ w := fun n =>
    div_nonneg (by unfold primeResidueInd; split_ifs <;> norm_num)
      (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  have h1 : ∀ n, primeResidueInd a n / (n : ℝ) ^ w ≤ 1 := fun n => by
    unfold primeResidueInd
    split_ifs with h
    · have hn : (1 : ℝ) ≤ n := by exact_mod_cast h.1.one_lt.le
      rw [div_le_one (Real.rpow_pos_of_pos (by linarith) _)]
      exact Real.one_le_rpow hn (by linarith)
    · simp
  refine ⟨Finset.sum_nonneg fun n _ => h0 n, ?_⟩
  calc ∑ n ∈ Finset.range (q + 1), primeResidueInd a n / (n : ℝ) ^ w
      ≤ ∑ _n ∈ Finset.range (q + 1), (1 : ℝ) := Finset.sum_le_sum fun n _ => h1 n
    _ = q + 1 := by simp

/-- Each class: `|Σ_{p ≡ a} p^{-w} − [a unit] φ(q)^{-1} log(1/(w − 1))| ≤ B_a` on `1 < w < 3/2`. -/
theorem exists_abs_tsum_primeResidueInd_sub_le' (a : ZMod q) :
    ∃ B : ℝ, ∀ w : ℝ, 1 < w → w < 3 / 2 →
      |∑' n, primeResidueInd a n / (n : ℝ) ^ w -
        (if IsUnit a then (q.totient : ℝ)⁻¹ else 0) * Real.log (1 / (w - 1))| ≤ B := by
  by_cases ha : IsUnit a
  · obtain ⟨B, hB⟩ := exists_abs_tsum_primeResidueInd_sub_le ha
    exact ⟨B, fun w hw hw2 => by simpa [ha] using hB w hw hw2⟩
  · refine ⟨q + 1, fun w hw hw2 => ?_⟩
    obtain ⟨h0, h1⟩ := tsum_primeResidueInd_mem_of_not_isUnit ha hw
    simp only [ha, if_false, zero_mul, sub_zero]
    rw [abs_of_nonneg h0]
    exact h1

/-- **The residue-class flip has an exact logarithmic prime density**:
`|Σ_{p mod q ∈ S} p^{-w} − ρ log(1/(w − 1))| ≤ B` on `1 < w < 3/2`, `ρ = #(S ∩ (ZMod q)ˣ)/φ(q)`. -/
theorem exists_abs_tsum_residueFlip_sub_le (S : Finset (ZMod q)) :
    ∃ B : ℝ, ∀ w : ℝ, 1 < w → w < 3 / 2 →
      |∑' p : Nat.Primes, (if residueFlip q S p = -1 then ((p : ℕ) : ℝ) ^ (-w) else 0) -
        ((S.filter IsUnit).card / q.totient : ℝ) * Real.log (1 / (w - 1))| ≤ B := by
  choose B hB using fun a : ZMod q => exists_abs_tsum_primeResidueInd_sub_le' a
  refine ⟨∑ a ∈ S, B a, fun w hw hw2 => ?_⟩
  have hsumI : ∀ a : ZMod q, Summable (fun n : ℕ => primeResidueInd a n / (n : ℝ) ^ w) :=
    fun a => (Real.summable_one_div_nat_rpow.mpr hw).of_nonneg_of_le
      (fun n => div_nonneg (by unfold primeResidueInd; split_ifs <;> norm_num)
        (Real.rpow_nonneg (Nat.cast_nonneg n) _))
      fun n => div_le_div_of_nonneg_right (by unfold primeResidueInd; split_ifs <;> norm_num)
        (Real.rpow_nonneg (Nat.cast_nonneg n) _)
  -- the flipped prime sum is the sum of the class sums
  set h : ℕ → ℝ := fun n => if n.Prime ∧ (n : ZMod q) ∈ S then (n : ℝ) ^ (-w) else 0
  have hprimes : ∑' p : Nat.Primes, (if residueFlip q S p = -1 then ((p : ℕ) : ℝ) ^ (-w) else 0) =
      ∑' n, h n := by
    have hsupp : Function.support h ⊆ {n : ℕ | n.Prime} := fun n hn => by
      simp only [h, Function.mem_support, ne_eq, ite_eq_right_iff, not_forall] at hn
      exact hn.1.1
    rw [← tsum_subtype_eq_of_support_subset hsupp]
    refine tsum_congr fun p => ?_
    simp only [h, residueFlip_prime_eq_neg_one_iff q S p.2]
    have hp : ((p : {n : ℕ | n.Prime}) : ℕ).Prime := p.2
    simp [hp]
  have hclass : ∀ n, h n = ∑ a ∈ S, primeResidueInd a n / (n : ℝ) ^ w := by
    intro n
    simp only [h, primeResidueInd]
    by_cases hp : n.Prime
    · simp only [hp, true_and, ite_div, one_div, zero_div]
      rw [Finset.sum_ite_eq]
      split_ifs
      · rw [Real.rpow_neg (Nat.cast_nonneg n)]
      · rfl
    · simp [hp]
  rw [hprimes, tsum_congr hclass, Summable.tsum_finsetSum fun a _ => hsumI a]
  have hmain : ((S.filter IsUnit).card / q.totient : ℝ) * Real.log (1 / (w - 1)) =
      ∑ a ∈ S, (if IsUnit a then (q.totient : ℝ)⁻¹ else 0) * Real.log (1 / (w - 1)) := by
    rw [← Finset.sum_mul, Finset.sum_ite, Finset.sum_const_zero, add_zero, Finset.sum_const,
      nsmul_eq_mul, div_eq_mul_inv]
  rw [hmain, ← Finset.sum_sub_distrib]
  exact (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun a _ => hB a w hw hw2)

end union

/-! ### The receiver laws for residue-class flips -/

/-- **Half damping**: a residue-class flip of less than a quarter of the unit classes is never paid.
If `4 #(S ∩ (ZMod q)ˣ) < φ(q)`, the weight `f_{q,S}(d) d^{-1/2}` has unbounded receiver. -/
theorem not_receiverBounded_residueFlip_half {q : ℕ} [NeZero q] (S : Finset (ZMod q))
    (h4 : 4 * (S.filter IsUnit).card < q.totient) :
    ¬ ReceiverBounded (fun d => residueFlip q S d * (d : ℝ) ^ (-(1 / 2 : ℝ))) := by
  obtain ⟨B, hB⟩ := exists_abs_tsum_residueFlip_sub_le S
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  refine not_receiverBounded_of_flippedDensity_lt_quarter (residueFlip q S)
    (fun p hp => residueFlip_prime_eq_one_or q S hp)
    (δ := ((S.filter IsUnit).card / q.totient : ℝ)) (B := B) ?_ fun w hw hw2 => ?_
  · rw [div_lt_iff₀ hφ]
    have : (4 : ℝ) * (S.filter IsUnit).card < q.totient := by exact_mod_cast h4
    linarith
  · linarith [(abs_le.mp (hB w hw hw2)).2]

/-- **Below half damping**: for `0 < ε < 1/2`, a residue-class flip whose unit density
`ρ = #(S ∩ (ZMod q)ˣ)/φ(q)` is neither `1/2` nor `1` is never paid. -/
theorem not_receiverBounded_residueFlip {q : ℕ} [NeZero q] {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε < 1 / 2) (S : Finset (ZMod q)) (hρ : 2 * (S.filter IsUnit).card ≠ q.totient)
    (hρ1 : (S.filter IsUnit).card < q.totient) :
    ¬ ReceiverBounded (fun d => residueFlip q S d * (d : ℝ) ^ (-ε)) := by
  obtain ⟨B, hB⟩ := exists_abs_tsum_residueFlip_sub_le S
  have hφ : (0 : ℝ) < q.totient := by exact_mod_cast Nat.totient_pos.mpr (NeZero.pos q)
  refine not_receiverBounded_of_flippedDensity hε hε2 (residueFlip q S)
    (fun p hp => residueFlip_prime_eq_one_or q S hp)
    (ρ := ((S.filter IsUnit).card / q.totient : ℝ)) (B := B) ?_ ?_ hB
  · intro h
    rw [div_eq_iff hφ.ne'] at h
    apply hρ
    have : (2 : ℝ) * (S.filter IsUnit).card = q.totient := by linarith
    exact_mod_cast this
  · rw [div_lt_one hφ]
    exact_mod_cast hρ1


end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
