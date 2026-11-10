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

/-- The complementary zeta coefficient kernel has the exact integral-test decay. -/
theorem tsum_rpow_above_le {b : ℝ} (hb : 1 < b) {N : ℕ} (hN : 1 ≤ N) :
    (∑' n : ℕ, if N < n then (n : ℝ) ^ (-b) else 0) ≤
      (N : ℝ) ^ (1 - b) / (b - 1) := by
  have hinj : Function.Injective (fun n : ℕ => n + (N + 1)) := by
    intro i j h
    omega
  have hsupp : Function.support (fun n : ℕ => if N < n then (n : ℝ) ^ (-b) else 0) ⊆
      Set.range (fun n : ℕ => n + (N + 1)) := by
    intro n hn
    have hlt : N < n := by
      by_contra h
      exact hn (if_neg h)
    exact ⟨n - (N + 1), Nat.sub_add_cancel (by omega)⟩
  calc
    _ = ∑' n : ℕ, ((n + (N + 1) : ℕ) : ℝ) ^ (-b) := by
      rw [← hinj.tsum_eq hsupp]
      apply tsum_congr
      intro n
      rw [if_pos (by omega)]
    _ ≤ _ := tsum_add_rpow_neg_le hb hN

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

/-- Any selection of zeta indices has the same separated divisor majorant.
Taking all indices, a finite head, or its complement gives the three energy estimates. -/
theorem resonator_slice_sq_le {ε σ : ℝ} (hε : 0 < ε) (hεσ : ε < 2 * σ)
    (A : Finset ℕ) (r : ℕ → ℂ) (P : ℕ → Prop) [DecidablePred P] (k : ℕ) :
    ‖∑ m ∈ A.filter (fun m => m ∣ k ∧ P (k / m)),
        r m * lineWeight σ (k / m)‖ ^ 2 ≤
      Sieve.divisorBoundConst ε * ∑ m ∈ A,
        (‖r m‖ ^ 2 * (m : ℝ) ^ ε) *
          (if m ∣ k then (if P (k / m) then ((k / m : ℕ) : ℝ) ^ (ε - 2 * σ) else 0)
            else 0) := by
  rcases eq_or_ne k 0 with rfl | hk
  · have hσ : σ ≠ 0 := by linarith only [hε, hεσ]
    have hzero : (∑ m ∈ A.filter (fun m => m ∣ 0 ∧ P (0 / m)),
        r m * lineWeight σ (0 / m)) = 0 := by
      apply Finset.sum_eq_zero
      intro m _
      simp only [Nat.zero_div, lineWeight, Nat.cast_zero,
        Real.zero_rpow (neg_ne_zero.mpr hσ), Complex.ofReal_zero, mul_zero]
    rw [hzero, norm_zero, zero_pow two_ne_zero]
    apply mul_nonneg (Sieve.divisorBoundConst_pos hε).le
    apply Finset.sum_nonneg
    intro m _
    exact mul_nonneg (by positivity) (by split_ifs <;> positivity)
  · have hB : A.filter (fun m => m ∣ k ∧ P (k / m)) ⊆ k.divisors := by
      intro m hm
      exact Nat.mem_divisors.mpr ⟨(Finset.mem_filter.mp hm).2.1, hk⟩
    apply (norm_resonator_divisor_sum_sq_le_split hε hεσ hk hB r).trans_eq
    congr 1
    rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro m _
    by_cases hd : m ∣ k <;> by_cases hp : P (k / m) <;> simp [hd, hp]

/-- Removing the finite zeta head leaves precisely the complementary product fibres. -/
theorem resonatorCoeff_sub_trunc (A : Finset ℕ) (r : ℕ → ℂ) (σ : ℝ) (N k : ℕ) :
    resonatorCoeff A r σ k - truncResonatorCoeff A r σ N k =
      ∑ m ∈ A.filter (fun m => m ∣ k ∧ N < k / m), r m * lineWeight σ (k / m) := by
  classical
  unfold resonatorCoeff truncResonatorCoeff
  rw [Finset.sum_filter, Finset.sum_filter, ← Finset.sum_sub_distrib, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro m _
  by_cases hd : m ∣ k
  · by_cases hN : k / m ≤ N
    · simp [hd, hN, not_lt.mpr hN]
    · simp [hd, hN, Nat.lt_of_not_ge hN]
  · simp [hd]

/-- Summing the fibre estimate costs only the weighted support energy.
The selected zeta kernel remains separate, so its head and tail bounds are uniform. -/
theorem summable_resonator_slice_sq_and_bound {ε σ : ℝ} (hε : 0 < ε)
    (hεσ : ε < 2 * σ - 1) {A : Finset ℕ} (hA : ∀ m ∈ A, m ≠ 0)
    (r : ℕ → ℂ) (P : ℕ → Prop) [DecidablePred P] :
    Summable (fun k : ℕ => ‖∑ m ∈ A.filter (fun m => m ∣ k ∧ P (k / m)),
        r m * lineWeight σ (k / m)‖ ^ 2) ∧
    (∑' k : ℕ, ‖∑ m ∈ A.filter (fun m => m ∣ k ∧ P (k / m)),
        r m * lineWeight σ (k / m)‖ ^ 2) ≤
      Sieve.divisorBoundConst ε * (∑ m ∈ A, ‖r m‖ ^ 2 * (m : ℝ) ^ ε) *
        ∑' n : ℕ, if P n then (n : ℝ) ^ (ε - 2 * σ) else 0 := by
  let f : ℕ → ℝ := fun n => if P n then (n : ℝ) ^ (ε - 2 * σ) else 0
  have hf : Summable f := by
    have hs : Summable (fun n : ℕ => (n : ℝ) ^ (ε - 2 * σ)) :=
      Real.summable_nat_rpow.mpr (by linarith only [hεσ])
    apply hs.of_nonneg_of_le
    · intro n
      dsimp [f]
      split_ifs <;> positivity
    · intro n
      dsimp [f]
      split_ifs
      · exact le_rfl
      · positivity
  have hmajor : Summable (fun k : ℕ => Sieve.divisorBoundConst ε * ∑ m ∈ A,
      (‖r m‖ ^ 2 * (m : ℝ) ^ ε) * (if m ∣ k then f (k / m) else 0)) :=
    (summable_sum fun m hm =>
      (summable_multiple_kernel (hA m hm) hf).mul_left (‖r m‖ ^ 2 * (m : ℝ) ^ ε)).mul_left _
  have hpoint (k : ℕ) := resonator_slice_sq_le hε (by linarith only [hεσ]) A r P k
  have hsmall : Summable (fun k : ℕ =>
      ‖∑ m ∈ A.filter (fun m => m ∣ k ∧ P (k / m)), r m * lineWeight σ (k / m)‖ ^ 2) :=
    hmajor.of_nonneg_of_le (fun _ => sq_nonneg _) hpoint
  refine ⟨hsmall, ?_⟩
  calc
    _ ≤ ∑' k : ℕ, Sieve.divisorBoundConst ε * ∑ m ∈ A,
        (‖r m‖ ^ 2 * (m : ℝ) ^ ε) * (if m ∣ k then f (k / m) else 0) :=
      Summable.tsum_le_tsum hpoint hsmall hmajor
    _ = _ := by
      rw [tsum_mul_left, tsum_finite_multiple_kernels hA _ hf]
      exact (mul_assoc _ _ _).symm

/-- A support cutoff bounds its weighted energy independently of the coefficients. -/
theorem sum_resonator_weighted_energy_le {ε : ℝ} (hε : 0 ≤ ε)
    {A : Finset ℕ} {M : ℕ} (hM : ∀ m ∈ A, m ≤ M) (r : ℕ → ℂ) :
    (∑ m ∈ A, ‖r m‖ ^ 2 * (m : ℝ) ^ ε) ≤
      (M : ℝ) ^ ε * ∑ m ∈ A, ‖r m‖ ^ 2 := by
  calc
    _ ≤ ∑ m ∈ A, ‖r m‖ ^ 2 * (M : ℝ) ^ ε := by
      apply Finset.sum_le_sum
      intro m hm
      exact mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast hM m hm) hε)
        (sq_nonneg _)
    _ = _ := by rw [Finset.sum_mul]; ring

/-- The full coefficient energy has only a subpower support cost. -/
theorem tsum_norm_resonatorCoeff_sq_le {ε σ : ℝ} (hε : 0 < ε)
    (hεσ : ε < 2 * σ - 1) {A : Finset ℕ} (hA : ∀ m ∈ A, m ≠ 0)
    (r : ℕ → ℂ) :
    (∑' k : ℕ, ‖resonatorCoeff A r σ k‖ ^ 2) ≤
      Sieve.divisorBoundConst ε * (∑ m ∈ A, ‖r m‖ ^ 2 * (m : ℝ) ^ ε) *
        ∑' n : ℕ, (n : ℝ) ^ (ε - 2 * σ) := by
  simpa only [resonatorCoeff, and_true, if_true] using
    (summable_resonator_slice_sq_and_bound hε hεσ hA r (fun _ => True)).2

/-- The coefficient tail has a uniform power rate in the zeta cutoff. -/
theorem tsum_norm_resonatorCoeff_sub_trunc_sq_le {ε σ : ℝ} (hε : 0 < ε)
    (hεσ : ε < 2 * σ - 1) {A : Finset ℕ} (hA : ∀ m ∈ A, m ≠ 0)
    (r : ℕ → ℂ) {N : ℕ} (hN : 1 ≤ N) :
    (∑' k : ℕ, ‖resonatorCoeff A r σ k - truncResonatorCoeff A r σ N k‖ ^ 2) ≤
      Sieve.divisorBoundConst ε * (∑ m ∈ A, ‖r m‖ ^ 2 * (m : ℝ) ^ ε) *
        ((N : ℝ) ^ (1 + ε - 2 * σ) / (2 * σ - ε - 1)) := by
  simp_rw [resonatorCoeff_sub_trunc]
  apply (summable_resonator_slice_sq_and_bound hε hεσ hA r (fun n => N < n)).2.trans
  apply mul_le_mul_of_nonneg_left _
    (mul_nonneg (Sieve.divisorBoundConst_pos hε).le (by positivity))
  have h := tsum_rpow_above_le (b := 2 * σ - ε) (by linarith only [hεσ]) hN
  rwa [show -(2 * σ - ε) = ε - 2 * σ by ring,
    show 1 - (2 * σ - ε) = 1 + ε - 2 * σ by ring] at h

#print axioms norm_resonatorCoeff_sq_le_divisor_weight
#print axioms summable_resonator_slice_sq_and_bound
#print axioms tsum_norm_resonatorCoeff_sub_trunc_sq_le

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
