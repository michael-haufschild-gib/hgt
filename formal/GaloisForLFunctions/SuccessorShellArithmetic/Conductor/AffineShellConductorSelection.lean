import GaloisForLFunctions.SuccessorShellArithmetic.Conductor.RamanujanAutocorrelationWeights

/-!
# The conductor selected by an affine successor shell

A complete-period correlation of conductors `m` and `l` along `n ↦ k*n+h`
vanishes unless `m=l/gcd(l,k)`. In the surviving case it is the period
length times the full conductor-`l` coefficient at the successor shift.
Primitive Fourier roots identify the exact conductor transition.
-/

open Finset
namespace GaloisForLFunctions.SuccessorShellArithmetic
open BezoutValuationIncidence ArithmeticEffectivityTheory TransThresholdPairCorrelation
  RenormalizedBiarithmeticGeometry
noncomputable section

private theorem primitiveRoot_pow_gcd {l : ℕ} (hl : 0 < l) {w : ℂ}
    (hw : IsPrimitiveRoot w l) (k : ℕ) :
    IsPrimitiveRoot (w ^ k) (l / Nat.gcd l k) := by
  apply IsPrimitiveRoot.iff_orderOf.mpr
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · simp only [pow_zero, orderOf_one, Nat.gcd_zero_right, Nat.div_self hl]
  · rw [orderOf_pow' _ hk.ne', ← hw.eq_orderOf]

private theorem sum_range_ramanujanSum_mul_affine {m l M : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hmM : m ∣ M) (hlM : l ∣ M) (k h : ℕ) :
    (∑ n ∈ range M, ramanujanSum m n * ramanujanSum l (k * n + h)) =
      if m = l / Nat.gcd l k then (M : ℂ) * ramanujanSum l h else 0 := by
  have hterm (z w : ℂ) (n : ℕ) :
      z ^ n * w ^ (k * n + h) = (z * w ^ k) ^ n * w ^ h := by
    rw [pow_add, pow_mul, mul_pow]
    ring
  have hperiod : ∀ z ∈ primitiveRoots m ℂ, ∀ w ∈ primitiveRoots l ℂ,
      (z * w ^ k) ^ M = 1 := by
    intro z hz w hw
    have hzM := ((mem_primitiveRoots hm).mp hz).pow_eq_one_iff_dvd M |>.mpr hmM
    have hwM := ((mem_primitiveRoots hl).mp hw).pow_eq_one_iff_dvd M |>.mpr hlM
    rw [mul_pow, hzM, one_mul, ← pow_mul, Nat.mul_comm k M, pow_mul, hwM, one_pow]
  have hexp : (∑ n ∈ range M, ramanujanSum m n * ramanujanSum l (k * n + h)) =
      ∑ w ∈ primitiveRoots l ℂ, ∑ z ∈ primitiveRoots m ℂ,
        (if z * w ^ k = 1 then (M : ℂ) else 0) * w ^ h := by
    calc
      _ = ∑ n ∈ range M, ∑ w ∈ primitiveRoots l ℂ,
          ∑ z ∈ primitiveRoots m ℂ, (z * w ^ k) ^ n * w ^ h := by
        apply sum_congr rfl
        intro n _
        rw [ramanujanSum, ramanujanSum, sum_mul_sum, sum_comm]
        exact sum_congr rfl fun w _ => sum_congr rfl fun z _ => hterm z w n
      _ = ∑ w ∈ primitiveRoots l ℂ, ∑ z ∈ primitiveRoots m ℂ,
          ∑ n ∈ range M, (z * w ^ k) ^ n * w ^ h := by
        rw [sum_comm]
        exact sum_congr rfl fun w _ => by rw [sum_comm]
      _ = _ := by
        apply sum_congr rfl
        intro w hw
        apply sum_congr rfl
        intro z hz
        rw [← sum_mul, sum_range_pow_of_pow_eq_one (hperiod z hz w hw)]
  rw [hexp]
  by_cases hml : m = l / Nat.gcd l k
  · rw [if_pos hml, ramanujanSum, mul_sum]
    apply sum_congr rfl
    intro w hw
    have hw' := (mem_primitiveRoots hl).mp hw
    have hwk := primitiveRoot_pow_gcd hl hw' k
    have hw0 : w ^ k ≠ 0 := pow_ne_zero k (hw'.ne_zero hl.ne')
    rw [sum_eq_single (w ^ k)⁻¹]
    · rw [if_pos (inv_mul_cancel₀ hw0)]
    · intro z _ hne
      rw [if_neg, zero_mul]
      intro hz
      exact hne (eq_inv_of_mul_eq_one_right (by simpa only [mul_comm] using hz))
    · intro hn
      apply False.elim
      apply hn
      apply (mem_primitiveRoots hm).mpr
      simpa only [hml] using hwk.inv
  · rw [if_neg hml]
    apply sum_eq_zero
    intro w hw
    apply sum_eq_zero
    intro z hz
    rw [if_neg, zero_mul]
    intro he
    have hz' := (mem_primitiveRoots hm).mp hz
    have hwk := primitiveRoot_pow_gcd hl ((mem_primitiveRoots hl).mp hw) k
    have hzInv : z = (w ^ k)⁻¹ :=
      eq_inv_of_mul_eq_one_right (by simpa only [mul_comm] using he)
    rw [hzInv] at hz'
    exact hml (hz'.unique hwk.inv)

/-- An affine shell selects exactly the conductor left after its dilation. -/
theorem sum_range_ramanujanLagCoefficient_mul_affine {m l M : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hmM : m ∣ M) (hlM : l ∣ M) (k h : ℕ) :
    (∑ n ∈ range M, ramanujanLagCoefficient m n *
      ramanujanLagCoefficient l (k * n + h)) =
      if m = l / Nat.gcd l k then (M : ℝ) * ramanujanLagCoefficient l h else 0 := by
  have he := congrArg Complex.re (sum_range_ramanujanSum_mul_affine hm hl hmM hlM k h)
  simp only [ramanujanSum_eq_ramanujanLagCoefficient hm,
    ramanujanSum_eq_ramanujanLagCoefficient hl, ← Complex.ofReal_mul,
    Complex.re_sum, Complex.ofReal_re] at he
  by_cases hml : m = l / Nat.gcd l k
  · simpa only [if_pos hml, Complex.mul_re, Complex.natCast_re, Complex.natCast_im,
      Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero] using he
  · simpa only [if_neg hml, Complex.zero_re] using he

/-- A dilation coprime to the second conductor preserves shifted orthogonality. -/
theorem sum_range_ramanujanLagCoefficient_mul_affine_of_coprime {m l M k : ℕ}
    (hm : 0 < m) (hl : 0 < l) (hmM : m ∣ M) (hlM : l ∣ M)
    (hlk : Nat.Coprime l k) (h : ℕ) :
    (∑ n ∈ range M, ramanujanLagCoefficient m n *
      ramanujanLagCoefficient l (k * n + h)) =
      if m = l then (M : ℝ) * ramanujanLagCoefficient l h else 0 := by
  simpa only [hlk.gcd_eq_one, Nat.div_one] using
    sum_range_ramanujanLagCoefficient_mul_affine hm hl hmM hlM k h

/-- The complete-period affine form on two finite conductor packets, including every mixed entry. -/
theorem sum_range_ramanujanPacket_mul_affine (S T : Finset ℕ) (a b : ℕ → ℝ) (M k h : ℕ)
    (hS : ∀ m ∈ S, 0 < m) (hT : ∀ l ∈ T, 0 < l)
    (hSM : ∀ m ∈ S, m ∣ M) (hTM : ∀ l ∈ T, l ∣ M) :
    (∑ n ∈ range M, (∑ m ∈ S, a m * ramanujanLagCoefficient m n) *
      (∑ l ∈ T, b l * ramanujanLagCoefficient l (k * n + h))) =
      (M : ℝ) * ∑ l ∈ T, (if l / Nat.gcd l k ∈ S then a (l / Nat.gcd l k) else 0) *
        b l * ramanujanLagCoefficient l h := by
  have hexp : (∑ n ∈ range M, (∑ m ∈ S, a m * ramanujanLagCoefficient m n) *
      (∑ l ∈ T, b l * ramanujanLagCoefficient l (k * n + h))) =
      ∑ l ∈ T, ∑ m ∈ S, a m * b l *
        (∑ n ∈ range M, ramanujanLagCoefficient m n *
          ramanujanLagCoefficient l (k * n + h)) := by
    calc
      _ = ∑ n ∈ range M, ∑ l ∈ T, ∑ m ∈ S,
          a m * b l * (ramanujanLagCoefficient m n *
            ramanujanLagCoefficient l (k * n + h)) := by
        apply sum_congr rfl
        intro n _
        rw [sum_mul_sum, sum_comm]
        exact sum_congr rfl fun l _ => sum_congr rfl fun m _ => by ring
      _ = _ := by
        rw [sum_comm]
        apply sum_congr rfl
        intro l _
        rw [sum_comm]
        simp only [mul_sum]
  rw [hexp, mul_sum]
  apply sum_congr rfl
  intro l hlT
  have hentry : ∀ m ∈ S, a m * b l *
      (∑ n ∈ range M, ramanujanLagCoefficient m n *
        ramanujanLagCoefficient l (k * n + h)) =
      if m = l / Nat.gcd l k then (M : ℝ) * a m * b l * ramanujanLagCoefficient l h else 0 := by
    intro m hmS
    rw [sum_range_ramanujanLagCoefficient_mul_affine (hS m hmS) (hT l hlT)
      (hSM m hmS) (hTM l hlT)]
    split_ifs <;> ring
  rw [sum_congr rfl hentry]
  by_cases hmem : l / Nat.gcd l k ∈ S
  · rw [if_pos hmem, sum_eq_single_of_mem (l / Nat.gcd l k) hmem]
    · simp only [ite_true]
      ring
    · intro m _ hne
      exact if_neg hne
  · rw [if_neg hmem, zero_mul, zero_mul, mul_zero]
    apply sum_eq_zero
    intro m hmS
    exact if_neg (fun he : m = l / Nat.gcd l k => hmem (he ▸ hmS))

#print axioms sum_range_ramanujanLagCoefficient_mul_affine
#print axioms sum_range_ramanujanLagCoefficient_mul_affine_of_coprime
#print axioms sum_range_ramanujanPacket_mul_affine

end
end GaloisForLFunctions.SuccessorShellArithmetic
