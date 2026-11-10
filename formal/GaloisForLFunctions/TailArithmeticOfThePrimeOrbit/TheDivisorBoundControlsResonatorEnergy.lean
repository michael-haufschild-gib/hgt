import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheResonatorMeanOfZeta
import GaloisForLFunctions.RHTower.Sieve.DivisorBound
import GaloisForLFunctions.RHTower.Sieve.SubCriticalPowerSum
import GaloisForLFunctions.RHTower.SqrtCarrierCertificate

/-!
# Divisor bounds for growing resonator coefficients

Cauchy–Schwarz is applied on each product fibre, whose cardinality is
bounded by the divisor function. This retains only an arbitrarily small
power of the resonator support in the coefficient energy.
-/

noncomputable section
open Real Finset Filter Topology
open _root_.RHTower

namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

/-- Dilation by a nonzero natural number preserves the sum on its multiples. -/
theorem tsum_multiple_kernel {m : ℕ} (hm : m ≠ 0) (f : ℕ → ℝ) :
    (∑' k : ℕ, if m ∣ k then f (k / m) else 0) = ∑' n : ℕ, f n := by
  classical
  have hinj : Function.Injective (fun n : ℕ => m * n) := fun a b h =>
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm) h
  have hsupp : Function.support (fun k : ℕ => if m ∣ k then f (k / m) else 0) ⊆
      Set.range (fun n : ℕ => m * n) := by
    intro k hk
    have hdiv : m ∣ k := by
      by_contra h
      exact hk (if_neg h)
    exact ⟨k / m, Nat.mul_div_cancel' hdiv⟩
  simpa only [dvd_mul_right, if_true, Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hm)]
    using (hinj.tsum_eq hsupp).symm

/-- Summability is also preserved when a kernel is placed on the multiples. -/
theorem summable_multiple_kernel {m : ℕ} (hm : m ≠ 0) {f : ℕ → ℝ}
    (hf : Summable f) : Summable (fun k : ℕ => if m ∣ k then f (k / m) else 0) := by
  have hinj : Function.Injective (fun n : ℕ => m * n) := fun a b h =>
    Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero hm) h
  refine (hinj.summable_iff fun k hk => ?_).mp ?_
  · rw [if_neg]
    rintro ⟨n, rfl⟩
    exact hk ⟨n, rfl⟩
  · simpa only [Function.comp_apply, dvd_mul_right, if_true,
      Nat.mul_div_cancel_left _ (Nat.pos_of_ne_zero hm)] using hf

/-- Summing over product fibres separates the finite support and the kernel. -/
theorem tsum_finite_multiple_kernels {A : Finset ℕ} (hA : ∀ m ∈ A, m ≠ 0)
    (w : ℕ → ℝ) {f : ℕ → ℝ} (hf : Summable f) :
    (∑' k : ℕ, ∑ m ∈ A, w m * (if m ∣ k then f (k / m) else 0)) =
      (∑ m ∈ A, w m) * ∑' n : ℕ, f n := by
  have hlocal (m : ℕ) (hm : m ∈ A) :
      HasSum (fun k : ℕ => w m * (if m ∣ k then f (k / m) else 0))
        (w m * ∑' n : ℕ, f n) := by
    have h := ((summable_multiple_kernel (hA m hm) hf).mul_left (w m)).hasSum
    simpa only [tsum_mul_left, tsum_multiple_kernel (hA m hm)] using h
  exact (hasSum_sum hlocal).tsum_eq.trans (Finset.sum_mul A w (∑' n : ℕ, f n)).symm

/-- The divisor weight splits into the support weight and the zeta-series weight. -/
theorem weighted_divisor_rpow {ε σ : ℝ} (hε : 0 < ε) (hεσ : ε < 2 * σ)
    {m k : ℕ} (hm : m ≠ 0) (hdiv : m ∣ k) :
    (k : ℝ) ^ ε * ((k / m : ℕ) : ℝ) ^ (-2 * σ) =
      (m : ℝ) ^ ε * ((k / m : ℕ) : ℝ) ^ (ε - 2 * σ) := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp only [Nat.zero_div, Nat.cast_zero, Real.zero_rpow hε.ne', zero_mul,
      Real.zero_rpow (sub_ne_zero.mpr hεσ.ne), mul_zero]
  · have hn : 0 < k / m := Nat.div_pos
      (Nat.le_of_dvd (Nat.pos_of_ne_zero hk) hdiv) (Nat.pos_of_ne_zero hm)
    have hnR : (0 : ℝ) < (k / m : ℕ) := Nat.cast_pos.mpr hn
    have hkr : (k : ℝ) = (m : ℝ) * (k / m : ℕ) := by
      exact_mod_cast (Nat.mul_div_cancel' hdiv).symm
    rw [hkr, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _),
      mul_assoc, ← Real.rpow_add hnR]
    congr 2 <;> ring

/-- The fibre cost is the number of divisors of the product, independently
of the size of the full resonator support. -/
theorem norm_resonator_divisor_sum_sq_le {ε : ℝ} (hε : 0 < ε)
    {k : ℕ} (hk : k ≠ 0) {B : Finset ℕ} (hB : B ⊆ k.divisors)
    (r : ℕ → ℂ) (σ : ℝ) :
    ‖∑ m ∈ B, r m * lineWeight σ (k / m)‖ ^ 2 ≤
      Sieve.divisorBoundConst ε * (k : ℝ) ^ ε *
        ∑ m ∈ B, ‖r m‖ ^ 2 * ((k / m : ℕ) : ℝ) ^ (-2 * σ) := by
  have hcard : (B.card : ℝ) ≤ Sieve.divisorBoundConst ε * (k : ℝ) ^ ε :=
    (Nat.cast_le.mpr (Finset.card_le_card hB)).trans (Sieve.card_divisors_le_rpow hε hk)
  have hterm (m : ℕ) : ‖r m * lineWeight σ (k / m)‖ ^ 2 =
      ‖r m‖ ^ 2 * ((k / m : ℕ) : ℝ) ^ (-2 * σ) := by
    rw [norm_mul, norm_lineWeight, mul_pow]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
    congr 1
    norm_num <;> ring
  calc
    _ ≤ (∑ m ∈ B, ‖r m * lineWeight σ (k / m)‖) ^ 2 := by
      gcongr
      exact norm_sum_le _ _
    _ ≤ (B.card : ℝ) * ∑ m ∈ B, ‖r m * lineWeight σ (k / m)‖ ^ 2 :=
      _root_.sq_sum_le_card_mul_sum_sq
    _ ≤ (Sieve.divisorBoundConst ε * (k : ℝ) ^ ε) *
        ∑ m ∈ B, ‖r m * lineWeight σ (k / m)‖ ^ 2 :=
      mul_le_mul_of_nonneg_right hcard (sum_nonneg fun _ _ => sq_nonneg _)
    _ = _ := by simp_rw [hterm]

/-- Splitting the divisor power isolates the small support factor `m^ε`. -/
theorem norm_resonator_divisor_sum_sq_le_split {ε σ : ℝ} (hε : 0 < ε)
    (hεσ : ε < 2 * σ) {k : ℕ} (hk : k ≠ 0) {B : Finset ℕ}
    (hB : B ⊆ k.divisors) (r : ℕ → ℂ) :
    ‖∑ m ∈ B, r m * lineWeight σ (k / m)‖ ^ 2 ≤
      Sieve.divisorBoundConst ε *
        ∑ m ∈ B, (‖r m‖ ^ 2 * (m : ℝ) ^ ε) *
          ((k / m : ℕ) : ℝ) ^ (ε - 2 * σ) := by
  apply (norm_resonator_divisor_sum_sq_le hε hk hB r σ).trans_eq
  rw [mul_assoc, Finset.mul_sum]
  congr 1
  apply Finset.sum_congr rfl
  intro m hm
  have hdiv := (Nat.mem_divisors.mp (hB hm)).1
  have hm0 : m ≠ 0 := by
    intro h
    subst m
    exact hk (Nat.zero_dvd_iff.mp hdiv)
  calc
    _ = ‖r m‖ ^ 2 * ((k : ℝ) ^ ε * ((k / m : ℕ) : ℝ) ^ (-2 * σ)) := by ring
    _ = _ := by rw [weighted_divisor_rpow hε hεσ hm0 hdiv]; ring

/-- Full convolution coefficients obey the divisor-weighted energy bound. -/
theorem norm_resonatorCoeff_sq_le_divisor_weight {ε : ℝ} (hε : 0 < ε)
    (A : Finset ℕ) (r : ℕ → ℂ) (σ : ℝ) {k : ℕ} (hk : k ≠ 0) :
    ‖resonatorCoeff A r σ k‖ ^ 2 ≤
      Sieve.divisorBoundConst ε * (k : ℝ) ^ ε *
        ∑ m ∈ A.filter (· ∣ k), ‖r m‖ ^ 2 * ((k / m : ℕ) : ℝ) ^ (-2 * σ) := by
  apply norm_resonator_divisor_sum_sq_le hε hk
  intro m hm
  exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hm).2, hk⟩

/-- The same bound holds for every finite zeta truncation. -/
theorem norm_truncResonatorCoeff_sq_le_divisor_weight {ε : ℝ} (hε : 0 < ε)
    (A : Finset ℕ) (r : ℕ → ℂ) (σ : ℝ) (N : ℕ) {k : ℕ} (hk : k ≠ 0) :
    ‖truncResonatorCoeff A r σ N k‖ ^ 2 ≤
      Sieve.divisorBoundConst ε * (k : ℝ) ^ ε *
        ∑ m ∈ A.filter (fun m => m ∣ k ∧ k / m ≤ N),
          ‖r m‖ ^ 2 * ((k / m : ℕ) : ℝ) ^ (-2 * σ) := by
  apply norm_resonator_divisor_sum_sq_le hε hk
  intro m hm
  exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hm).2.1, hk⟩

#print axioms norm_resonatorCoeff_sq_le_divisor_weight

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
