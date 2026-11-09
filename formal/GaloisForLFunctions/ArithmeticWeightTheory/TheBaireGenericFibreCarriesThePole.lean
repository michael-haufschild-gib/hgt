import GaloisForLFunctions.ArithmeticWeightTheory.TheTrivialFibreIsTheJump

/-!
# The Baire-generic fibre carries the pole

In which topology do weights specialize? The gauge family answers for the product topology, the
topology in which the trivial fibre is a limit of the others. Let `C(K, a)` be the fibres whose
window traces at the primes are `≤ K p^a` (`traceConstantSet`).

**Theorem** (`isNowhereDense_traceConstantSet`). For `0 ≤ a < ½` every `C(K, a)` is closed with
empty interior. A basic open set fixes finitely many prime coordinates; resetting all others to the
trivial value reproduces, at every large prime, the window trace of the trivial fibre up to a
bounded error (`norm_fibreTrace_trivial_sub_le`), and the trivial fibre carries the pole
`≫ √p`.

**Theorem** (`residual_and_null_of_traceExponent`). For `0 < a < ½` the fibres with no trace
constant at exponent `a` form a residual, Haar-null set: the Baire-generic fibre has trace
exponent `½` — the size of the pole of `ζ` — while the Haar-generic fibre has exponent `0`
(`TheGenericFibreHasUniformWeights`). In the product topology the generic fibres near the trivial
point look like the special fibre in category and like a pure fibre in measure; weights do not
specialize, constants do (`isClosed_traceConstantSet`), and they blow up at `ζ`
(`trivial_fibre_is_the_jump`).
-/

open MeasureTheory Finset Real Filter Topology

noncomputable section

namespace GaloisForLFunctions.ArithmeticWeightTheory

open ArithmeticCorrelationGeometry

/-- At a prime the twist is the first Fourier mode of the prime coordinate. -/
theorem twist_eq_fourier_of_prime (x : GaugeTorus) {p : ℕ} (hp : p.Prime) :
    twist x p = fourier 1 (x p) := by
  rw [twist, HTGeometry.torusCharacter_apply]
  have hsupp : (expVec p).support = {p} := by
    rw [support_expVec, Nat.support_factorization, hp.primeFactors]
  rw [hsupp, prod_singleton, expVec_apply, hp.factorization_self]
  rfl

/-- The fibre that agrees with `x` on `I` and is trivial elsewhere. -/
def resetOutside (I : Finset ℕ) (x : GaugeTorus) : GaugeTorus := fun i => if i ∈ I then x i else 0

/-- Resetting the coordinates off a finite set moves a window trace from the trivial one by at most
`2 Σ_{q ∈ I} log q`. -/
theorem norm_fibreTrace_trivial_sub_le {g : ℝ → ℝ} (hg : ∀ v, |g v| ≤ 1) (R : ℝ) {u : ℝ}
    (hu : 0 ≤ u) (I : Finset ℕ) (x : GaugeTorus) :
    ‖fibreTrace g R u 0 - fibreTrace g R u (resetOutside I x)‖ ≤ 2 * ∑ q ∈ I, Real.log q := by
  classical
  set W := windowPrimes R u
  set y := resetOutside I x
  have hterm : ∀ q ∈ W, windowWeight g u q * twist 0 q - windowWeight g u q * twist y q =
      if q ∈ I then windowWeight g u q * (1 - twist y q) else 0 := by
    intro q hq
    have hqp := (Nat.mem_primesLE.mp hq).2
    rw [twist_trivial]
    split_ifs with hqI
    · ring
    · have hy : twist y q = 1 := by
        rw [twist_eq_fourier_of_prime y hqp, show y q = (0 : GaugeTorus) q by
          simp [y, resetOutside, hqI], ← twist_eq_fourier_of_prime 0 hqp, twist_trivial]
      rw [hy]; ring
  have hw : ∀ q ∈ W, ‖windowWeight g u q‖ ≤ Real.log q := by
    intro q hq
    have hqp := (Nat.mem_primesLE.mp hq).2
    have hlog : 0 ≤ Real.log q := Real.log_nonneg (by exact_mod_cast hqp.one_lt.le)
    rw [windowWeight, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_mul,
      abs_of_pos (Real.exp_pos _), abs_of_nonneg hlog]
    have he : Real.exp (-(u / 2)) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    calc Real.exp (-(u / 2)) * Real.log q * |g (Real.log q - u)| ≤ 1 * Real.log q * 1 := by
          gcongr
          exact hg _
      _ = Real.log q := by ring
  unfold fibreTrace twistSum
  rw [← Finset.sum_sub_distrib, Finset.sum_congr rfl hterm, Finset.sum_ite, Finset.sum_const_zero,
    add_zero]
  calc ‖∑ q ∈ W.filter (· ∈ I), windowWeight g u q * (1 - twist y q)‖
      ≤ ∑ q ∈ W.filter (· ∈ I), ‖windowWeight g u q * (1 - twist y q)‖ := norm_sum_le _ _
    _ ≤ ∑ q ∈ W.filter (· ∈ I), 2 * Real.log q := by
        refine Finset.sum_le_sum fun q hq => ?_
        have hqW := (Finset.mem_filter.mp hq).1
        rw [norm_mul]
        have h2 : ‖1 - twist y q‖ ≤ 2 := by
          calc ‖1 - twist y q‖ ≤ ‖(1 : ℂ)‖ + ‖twist y q‖ := norm_sub_le _ _
            _ = 2 := by rw [norm_one, norm_twist]; norm_num
        have hl : 0 ≤ Real.log q := Real.log_nonneg (by
          exact_mod_cast (Nat.mem_primesLE.mp hqW).2.one_lt.le)
        nlinarith [hw q hqW, norm_nonneg (windowWeight g u q), norm_nonneg (1 - twist y q)]
    _ ≤ ∑ q ∈ I, 2 * Real.log q := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun q hq => (Finset.mem_filter.mp hq).2)
          fun q _ _ => ?_
        rcases Nat.eq_zero_or_pos q with h | h
        · simp [h]
        · have : (1 : ℝ) ≤ q := by exact_mod_cast h
          linarith [Real.log_nonneg this]
    _ = 2 * ∑ q ∈ I, Real.log q := by rw [Finset.mul_sum]

/-- **The trace-constant sets are nowhere dense** below exponent `½`. -/
theorem isNowhereDense_traceConstantSet {g : ℝ → ℝ} (hg : ∀ v, |g v| ≤ 1) (hg0 : ∀ v, 0 ≤ g v)
    {c : ℝ} (hc : 0 < c) (hgc : ∀ v, |v| ≤ 1 → c ≤ g v) {R : ℝ} (hR : 1 ≤ R) {a : ℝ}
    (ha0 : 0 ≤ a) (ha : a < 1 / 2) (K : ℝ) :
    IsNowhereDense (traceConstantSet g R K a) := by
  rw [(isClosed_traceConstantSet g R K a).isNowhereDense_iff]
  refine Set.eq_empty_iff_forall_notMem.mpr fun x hx => ?_
  obtain ⟨I, u, hIu, hsub⟩ := isOpen_pi_iff.mp isOpen_interior x hx
  set L := ∑ q ∈ I, Real.log q with hL
  have hL0 : 0 ≤ L := Finset.sum_nonneg fun q _ => by
    rcases Nat.eq_zero_or_pos q with h | h
    · simp [h]
    · exact Real.log_nonneg (by exact_mod_cast h)
  set y := resetOutside I x
  have hy : y ∈ traceConstantSet g R K a := by
    refine interior_subset (hsub fun i hi => ?_)
    have : y i = x i := by simp [y, resetOutside, show i ∈ I from hi]
    rw [this]
    exact (hIu i hi).2
  obtain ⟨p, hp, hlt⟩ := exists_prime_mul_rpow_lt_trivial_fibreTrace hg0 hc hgc hR ha (|K| + 2 * L)
  have hu : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_lt.le)
  have hdiff := norm_fibreTrace_trivial_sub_le hg R hu I x
  have hpa : (1 : ℝ) ≤ (p : ℝ) ^ a := Real.one_le_rpow (by exact_mod_cast hp.one_lt.le) ha0
  have htri : ‖fibreTrace g R (Real.log p) 0‖ ≤
      ‖fibreTrace g R (Real.log p) y‖ + 2 * L := by
    have := norm_sub_norm_le (fibreTrace g R (Real.log p) 0) (fibreTrace g R (Real.log p) y)
    linarith
  have hyb := hy p hp
  have hK : K * (p : ℝ) ^ a ≤ |K| * (p : ℝ) ^ a :=
    mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
  have h2L : 2 * L ≤ 2 * L * (p : ℝ) ^ a := le_mul_of_one_le_right (by positivity) hpa
  nlinarith

/-- **Baire-generic fibres carry the pole; Haar-generic fibres are pure.** For `0 < a < ½` the
fibres without a trace constant at exponent `a` form a residual Haar-null set. -/
theorem residual_and_null_of_traceExponent {g : ℝ → ℝ} (hg : ∀ v, |g v| ≤ 1)
    (hg0 : ∀ v, 0 ≤ g v) {c : ℝ} (hc : 0 < c) (hgc : ∀ v, |v| ≤ 1 → c ≤ g v) {R : ℝ} (hR : 1 ≤ R)
    {a : ℝ} (ha0 : 0 < a) (ha : a < 1 / 2) :
    {x : GaugeTorus | ∀ K : ℝ, x ∉ traceConstantSet g R K a} ∈ residual GaugeTorus ∧
      gaugeHaar {x : GaugeTorus | ∀ K : ℝ, x ∉ traceConstantSet g R K a} = 0 := by
  have hset : {x : GaugeTorus | ∀ K : ℝ, x ∉ traceConstantSet g R K a} =
      (⋃ n : ℕ, traceConstantSet g R n a)ᶜ := by
    ext x
    simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    constructor
    · exact fun h n => h n
    · intro h K hK
      obtain ⟨n, hn⟩ := exists_nat_ge K
      exact h n (traceConstantSet_mono g R a hn hK)
  refine ⟨?_, ?_⟩
  · rw [hset]
    exact isMeagre_iUnion fun n =>
      (isNowhereDense_traceConstantSet hg hg0 hc hgc hR ha0.le ha n).isMeagre
  · have hae := ae_exists_mem_traceConstantSet hg (by linarith : (0 : ℝ) ≤ R) ha0
    rw [ae_iff] at hae
    simpa only [not_exists] using hae

end GaloisForLFunctions.ArithmeticWeightTheory
