import GaloisForLFunctions.TransHorizonIncidenceMechanics.MultiFrequencyPrimePatternsAndGeneralMultiplicativeSpectra
import GaloisForLFunctions.TransHorizonIncidenceMechanics.PretentiousMultiplicativeWeightsAndTheReceiverTrichotomy

/-!
# The higher prime powers are invisible off the two-adic boundary

Let `f'` be multiplicative with `|f'(n)| ≤ 1`, and let `f` be its completely multiplicative
companion, with the same prime values (`primeValueHom`). The kernel `g = f' ⋆ μf` vanishes at the
primes and `|g(p^k)| ≤ 2`; its local factors are `G_p(x) = 1 + Σ_{k ≥ 2} g(p^k) x^k`.

* **Invisibility** (`receiverBounded_half_iff_companion`): if some two-adic step is not extremal,
  `|f'(2^{m+2}) − f'(2) f'(2^{m+1})| < 2`, then `f'(d) d^{-1/2}` is paid iff `f(d) d^{-1/2}` is.
  One direction is the prime-perturbation transfer. For the other, the inverse kernel `h = g⁻¹`
  (`primePowerHom` of the Dirichlet inverse) has local sums
  `Σ_k |h(p^k)| p^{-k} ≤ (1 − r_p)⁻¹`, `r_p = Σ_k |g(p^k)| p^{-k}`
  (`sum_range_abs_mul_pow_le_of_inv`), with `r_p ≤ 3/p²` for odd `p` and `r_2 < 1` exactly off the
  extremal tails; so `h d^{-1/2}` is critical Wiener and `f = h ⋆ f'` carries payment back.
* **The extremal tails** (`twoAdicStep_extremal_iff`): every two-adic step is extremal iff
  `f'(2^k) = −1` for all `k ≥ 1`, or `f'(2^k) = (−1)^{k+1}` for all `k ≥ 1`.
* **A local factor repairs the boundary** (`receiverBounded_twoAdicRepair`,
  `receiverBounded_twoAdicCompanion_iff`): at `t₀ = 2πm/log 2`, `m ≥ 1`, the multiplicative weight
  `f'(n) = (−1)^{[2 ∣ n]} f_{t₀}(n)`, `f_{t₀}(p) = cos(t₀ log p)`, has Dirichlet series
  `(1 − 2^{1−w}) F_{t₀}(w)`; the factor vanishes at `w = 1 + it₀` and cancels the boundary
  singularity, so `f'` is always paid, while its companion is paid iff `ζ(1/2 + it₀) = 0`.
-/

open Filter Topology MeasureTheory Complex Set
open GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### Convolution at prime powers -/

/-- `(F ⋆ G)(p^k) = Σ_{j ≤ k} F(p^j) G(p^{k−j})`. -/
theorem mul_apply_prime_pow_eq (F G : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    (F * G) (p ^ k) = ∑ j ∈ Finset.range (k + 1), F (p ^ j) * G (p ^ (k - j)) := by
  rw [ArithmeticFunction.mul_apply, Nat.sum_divisorsAntidiagonal (fun a b => F a * G b),
    Nat.divisors_prime_pow hp, Finset.sum_map]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Function.Embedding.coeFn_mk]
  rw [Nat.pow_div (by have := Finset.mem_range.mp hj; omega) hp.pos]

/-- `(A ⋆ B)(d) d^{-ε} = (A d^{-ε}) ⋆ (B d^{-ε})`. -/
theorem dampedSignWeight_mul (A B : ArithmeticFunction ℝ) (ε : ℝ) :
    dampedSignWeight ⇑(A * B) ε =
      RHTower.dirichletConv (dampedSignWeight ⇑A ε) (dampedSignWeight ⇑B ε) := by
  funext n
  rw [dampedSignWeight, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => A a * B b), RHTower.dirichletConv, Finset.sum_mul]
  refine Finset.sum_congr rfl fun d hd => ?_
  obtain ⟨k, rfl⟩ := Nat.dvd_of_mem_divisors hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  rw [Nat.mul_div_cancel_left k hd0]
  simp only [dampedSignWeight, Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

/-! ### Inverting a local factor -/

/-- **Inverting a local factor.** If `a₀ = b₀ = 1`, `Σ_{j ≤ k} a_j b_{k−j} = 0` for `k ≥ 1`, and
`Σ_{1 ≤ j ≤ K} |a_j| x^j ≤ r < 1` for every `K`, then `Σ_{k ≤ K} |b_k| x^k ≤ (1 − r)⁻¹`: the
truncations satisfy `S_K ≤ 1 + r S_K`. -/
theorem sum_range_abs_mul_pow_le_of_inv {a b : ℕ → ℝ} {x r : ℝ} (hx : 0 ≤ x) (ha0 : a 0 = 1)
    (hb0 : b 0 = 1) (hinv : ∀ k, 1 ≤ k → ∑ j ∈ Finset.range (k + 1), a j * b (k - j) = 0)
    (hr : ∀ K, ∑ j ∈ Finset.range (K + 1), (if j = 0 then 0 else |a j| * x ^ j) ≤ r)
    (hr1 : r < 1) (K : ℕ) :
    ∑ k ∈ Finset.range (K + 1), |b k| * x ^ k ≤ (1 - r)⁻¹ := by
  set d : ℕ → ℝ := fun j => if j = 0 then 0 else |a j| * x ^ j
  set c : ℕ → ℝ := fun i => |b i| * x ^ i
  have hd0 : ∀ j, 0 ≤ d j := fun j => by simp only [d]; split_ifs <;> positivity
  have hc0 : ∀ i, 0 ≤ c i := fun i => by simp only [c]; positivity
  have hstep : ∀ k, c k ≤ (if k = 0 then 1 else 0) +
      ∑ j ∈ Finset.range (k + 1), d j * c (k - j) := by
    intro k
    rcases Nat.eq_zero_or_pos k with rfl | hk
    · simp [c, d, hb0]
    · have h := hinv k hk
      rw [Finset.sum_range_succ', ha0, one_mul, Nat.sub_zero] at h
      have hbk : b k = -∑ j ∈ Finset.range k, a (j + 1) * b (k - (j + 1)) := by linarith
      rw [if_neg hk.ne', zero_add, Finset.sum_range_succ']
      have hd00 : d 0 = 0 := if_pos rfl
      rw [hd00, zero_mul, add_zero]
      simp only [c]
      rw [hbk, abs_neg]
      calc |∑ j ∈ Finset.range k, a (j + 1) * b (k - (j + 1))| * x ^ k
          ≤ (∑ j ∈ Finset.range k, |a (j + 1)| * |b (k - (j + 1))|) * x ^ k := by
            refine mul_le_mul_of_nonneg_right ((Finset.abs_sum_le_sum_abs _ _).trans
              (le_of_eq ?_)) (pow_nonneg hx k)
            exact Finset.sum_congr rfl fun j _ => abs_mul _ _
        _ = ∑ j ∈ Finset.range k, d (j + 1) * (|b (k - (j + 1))| * x ^ (k - (j + 1))) := by
            rw [Finset.sum_mul]
            refine Finset.sum_congr rfl fun j hj => ?_
            have hjk : j + 1 ≤ k := Finset.mem_range.mp hj
            have hdj : d (j + 1) = |a (j + 1)| * x ^ (j + 1) := if_neg (Nat.succ_ne_zero j)
            have hpow : x ^ k = x ^ (j + 1) * x ^ (k - (j + 1)) := by
              rw [← pow_add]; congr 1; omega
            rw [hdj, hpow]; ring
  have hsum : ∑ k ∈ Finset.range (K + 1), c k ≤ 1 + r * ∑ k ∈ Finset.range (K + 1), c k := by
    calc ∑ k ∈ Finset.range (K + 1), c k
        ≤ ∑ k ∈ Finset.range (K + 1), ((if k = 0 then 1 else 0) +
            ∑ j ∈ Finset.range (k + 1), d j * c (k - j)) := Finset.sum_le_sum fun k _ => hstep k
      _ = 1 + ∑ k ∈ Finset.range (K + 1), ∑ j ∈ Finset.range (k + 1), d j * c (k - j) := by
          rw [Finset.sum_add_distrib]
          congr 1
          simp
      _ = 1 + ∑ j ∈ Finset.range (K + 1), ∑ i ∈ Finset.range (K + 1 - j), d j * c i := by
          rw [Finset.sum_range_diag_flip (K + 1) (fun j i => d j * c i)]
      _ ≤ 1 + ∑ j ∈ Finset.range (K + 1), d j * ∑ k ∈ Finset.range (K + 1), c k := by
          gcongr with j hj
          rw [Finset.mul_sum]
          exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (Nat.sub_le _ _))
            (fun i _ _ => mul_nonneg (hd0 j) (hc0 i))
      _ = 1 + (∑ j ∈ Finset.range (K + 1), d j) * ∑ k ∈ Finset.range (K + 1), c k := by
          rw [Finset.sum_mul]
      _ ≤ 1 + r * ∑ k ∈ Finset.range (K + 1), c k := by
          exact add_le_add le_rfl
            (mul_le_mul_of_nonneg_right (hr K) (Finset.sum_nonneg fun k _ => hc0 k))
  rw [show (1 - r)⁻¹ = 1 / (1 - r) by ring, le_div_iff₀ (by linarith)]
  linarith

/-- The tsum form of the local inversion bound. -/
theorem summable_and_tsum_abs_mul_pow_le_of_inv {a b : ℕ → ℝ} {x r : ℝ} (hx : 0 ≤ x)
    (ha0 : a 0 = 1) (hb0 : b 0 = 1)
    (hinv : ∀ k, 1 ≤ k → ∑ j ∈ Finset.range (k + 1), a j * b (k - j) = 0)
    (hr : ∀ K, ∑ j ∈ Finset.range (K + 1), (if j = 0 then 0 else |a j| * x ^ j) ≤ r)
    (hr1 : r < 1) :
    Summable (fun k => |b k| * x ^ k) ∧ ∑' k, |b k| * x ^ k ≤ (1 - r)⁻¹ := by
  have hS : ∀ n, ∑ k ∈ Finset.range n, |b k| * x ^ k ≤ (1 - r)⁻¹ := by
    intro n
    rcases n with _ | K
    · simp only [Finset.range_zero, Finset.sum_empty]
      exact inv_nonneg.mpr (by linarith)
    · exact sum_range_abs_mul_pow_le_of_inv hx ha0 hb0 hinv hr hr1 K
  have h0 : ∀ k, 0 ≤ |b k| * x ^ k := fun k => by positivity
  exact ⟨summable_of_sum_range_le h0 hS, Real.tsum_le_of_sum_range_le h0 hS⟩

/-! ### Multiplicative functions from prime-power values -/

/-- The multiplicative function with prescribed values `u(p^k)` at prime powers. -/
def primePowerHom (u : ℕ → ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n = 0 then 0 else n.factorization.prod fun p k => u (p ^ k), if_pos rfl⟩

theorem primePowerHom_isMultiplicative (u : ℕ → ℝ) :
    (primePowerHom u).IsMultiplicative := by
  refine ⟨by simp [primePowerHom], fun {m n} hmn => ?_⟩
  simp only [primePowerHom, ArithmeticFunction.coe_mk]
  rcases eq_or_ne m 0 with rfl | hm
  · simp
  rcases eq_or_ne n 0 with rfl | hn
  · simp
  rw [if_neg (mul_ne_zero hm hn), if_neg hm, if_neg hn, Nat.factorization_mul_of_coprime hmn,
    Finsupp.prod_add_index_of_disjoint hmn.disjoint_primeFactors]

theorem primePowerHom_prime_pow {u : ℕ → ℝ} (hu : u 1 = 1) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    primePowerHom u (p ^ k) = u (p ^ k) := by
  simp only [primePowerHom, ArithmeticFunction.coe_mk, if_neg (pow_ne_zero k hp.ne_zero),
    hp.factorization_pow]
  rw [Finsupp.prod_single_index (h := fun p k => u (p ^ k)) (by simpa using hu)]

/-! ### The inverse kernel -/

/-- The defect kernel `g = f' ⋆ μf` of `f'` against its completely multiplicative companion. -/
def companionKernel (f' : ArithmeticFunction ℝ) : ArithmeticFunction ℝ :=
  f' * patternMoebiusAF (primeValueHom fun p => f' p)

theorem companionKernel_isMultiplicative {f' : ArithmeticFunction ℝ} (hf' : f'.IsMultiplicative) :
    (companionKernel f').IsMultiplicative :=
  hf'.mul (isMultiplicative_patternMoebiusAF _)

theorem companionKernel_prime_pow (f' : ArithmeticFunction ℝ) {p : ℕ} (hp : p.Prime) (m : ℕ) :
    companionKernel f' (p ^ (m + 1)) = f' (p ^ (m + 1)) - f' p * f' (p ^ m) := by
  rw [companionKernel, mul_patternMoebiusAF_apply_prime_pow f' _ hp m, primeValueHom_prime _ hp]

theorem companionKernel_prime {f' : ArithmeticFunction ℝ} (hf' : f'.IsMultiplicative) {p : ℕ}
    (hp : p.Prime) : companionKernel f' p = 0 := by
  have h := companionKernel_prime_pow f' hp 0
  rw [zero_add, pow_one, pow_zero, hf'.map_one, mul_one, sub_self] at h
  exact h

theorem abs_companionKernel_prime_pow_le {f' : ArithmeticFunction ℝ} (hf' : f'.IsMultiplicative)
    (hbd : ∀ n, |f' n| ≤ 1) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    |companionKernel f' (p ^ k)| ≤ 2 := by
  rcases k with _ | m
  · rw [pow_zero, (companionKernel_isMultiplicative hf').map_one]; norm_num
  · rw [companionKernel_prime_pow f' hp m]
    calc |f' (p ^ (m + 1)) - f' p * f' (p ^ m)|
        ≤ |f' (p ^ (m + 1))| + |f' p| * |f' (p ^ m)| := by rw [← abs_mul]; exact abs_sub _ _
      _ ≤ 1 + 1 * 1 := add_le_add (hbd _) (mul_le_mul (hbd _) (hbd _) (abs_nonneg _) zero_le_one)
      _ = 2 := by norm_num

theorem companionKernel_one_invertible {f' : ArithmeticFunction ℝ} (hf' : f'.IsMultiplicative) :
    companionKernel f' 1 ≠ 0 := by
  rw [(companionKernel_isMultiplicative hf').map_one]; exact one_ne_zero

/-- The inverse kernel: the Dirichlet inverse of `g`, assembled from its prime-power values. -/
def inverseKernel (f' : ArithmeticFunction ℝ) (hf' : f'.IsMultiplicative) : ArithmeticFunction ℝ :=
  primePowerHom ⇑(ArithmeticFunction.dirichletInverse (companionKernel f')
    (invertibleOfNonzero (companionKernel_one_invertible hf')))

theorem inverseKernel_isMultiplicative {f' : ArithmeticFunction ℝ} (hf' : f'.IsMultiplicative) :
    (inverseKernel f' hf').IsMultiplicative :=
  primePowerHom_isMultiplicative _

/-- `h ⋆ g = 1`. -/
theorem inverseKernel_mul_companionKernel {f' : ArithmeticFunction ℝ} (hf' : f'.IsMultiplicative) :
    inverseKernel f' hf' * companionKernel f' = 1 := by
  have hg := companionKernel_isMultiplicative hf'
  have hh := inverseKernel_isMultiplicative hf'
  set ginv := ArithmeticFunction.dirichletInverse (companionKernel f')
    (invertibleOfNonzero (companionKernel_one_invertible hf'))
  have hginv1 : ginv 1 = 1 := by
    simp only [ginv, ArithmeticFunction.dirichletInverse, ArithmeticFunction.coe_mk,
      ArithmeticFunction.dirichletInverseFun_apply_one]
    rw [invOf_eq_inv, hg.map_one, inv_one]
  have hinv : ginv * companionKernel f' = 1 := ArithmeticFunction.dirichletInverse_mul_self _ _
  refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _ (hh.mul hg) _
    ArithmeticFunction.isMultiplicative_one).mpr fun p i hp => ?_
  have h1 : (1 : ArithmeticFunction ℝ) (p ^ i) = (ginv * companionKernel f') (p ^ i) := by
    rw [hinv]
  rw [mul_apply_prime_pow_eq _ _ hp, h1, mul_apply_prime_pow_eq _ _ hp]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inverseKernel, primePowerHom_prime_pow hginv1 hp]

/-! ### The local sums of the inverse kernel -/

/-- The local mass `r_p = Σ_k |g(p^k)| p^{-k}` (the `k = 0` term omitted). -/
def localKernelMass (f' : ArithmeticFunction ℝ) (p : ℕ) : ℝ :=
  ∑' j : ℕ, if j = 0 then 0 else |companionKernel f' (p ^ j)| * ((p : ℝ) ^ (-1 : ℝ)) ^ j

theorem summable_localKernelMass_terms {f' : ArithmeticFunction ℝ} (hf' : f'.IsMultiplicative)
    (hbd : ∀ n, |f' n| ≤ 1) {p : ℕ} (hp : p.Prime) :
    Summable fun j : ℕ =>
      if j = 0 then (0 : ℝ) else |companionKernel f' (p ^ j)| * ((p : ℝ) ^ (-1 : ℝ)) ^ j := by
  have hx0 : 0 ≤ (p : ℝ) ^ (-1 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hx1 : (p : ℝ) ^ (-1 : ℝ) < 1 := by
    rw [Real.rpow_neg_one]; exact inv_lt_one_of_one_lt₀ (by exact_mod_cast hp.one_lt)
  refine ((summable_geometric_of_lt_one hx0 hx1).mul_left 2).of_nonneg_of_le
    (fun j => by split_ifs <;> positivity) fun j => ?_
  split_ifs
  · positivity
  · exact mul_le_mul_of_nonneg_right (abs_companionKernel_prime_pow_le hf' hbd hp j)
      (pow_nonneg hx0 j)

/-- At odd primes the local mass is at most `3/p²`. -/
theorem localKernelMass_le_of_odd {f' : ArithmeticFunction ℝ} (hf' : f'.IsMultiplicative)
    (hbd : ∀ n, |f' n| ≤ 1) {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) :
    localKernelMass f' p ≤ 3 * ((p : ℝ) ^ (-1 : ℝ)) ^ 2 := by
  set x : ℝ := (p : ℝ) ^ (-1 : ℝ)
  have hx0 : 0 ≤ x := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hx3 : x ≤ 1 / 3 := by
    simp only [x]; rw [Real.rpow_neg_one, one_div]
    exact inv_anti₀ (by norm_num) (by exact_mod_cast hp3)
  have hx1 : x < 1 := by linarith
  have hgeo := hasSum_geometric_of_lt_one hx0 hx1
  set e : ℕ → ℝ := fun j => 2 * x ^ j - (if j = 0 then (2 : ℝ) else 0) - (if j = 1 then 2 * x else 0)
  have he : HasSum e (2 * (1 - x)⁻¹ - 2 - 2 * x) :=
    ((hgeo.mul_left 2).sub (hasSum_ite_eq 0 (2 : ℝ))).sub (hasSum_ite_eq 1 (2 * x))
  have hle : ∀ j, (if j = 0 then (0 : ℝ) else |companionKernel f' (p ^ j)| * x ^ j) ≤ e j := by
    intro j
    simp only [e]
    rcases Nat.lt_or_ge j 2 with hj | hj
    · interval_cases j
      · simp
      · simp [companionKernel_prime hf' hp]
    · rw [if_neg (show j ≠ 0 by omega), if_neg (show j ≠ 0 by omega), if_neg (show j ≠ 1 by omega),
        sub_zero, sub_zero]
      exact mul_le_mul_of_nonneg_right (abs_companionKernel_prime_pow_le hf' hbd hp _)
        (pow_nonneg hx0 _)
  have h := (summable_localKernelMass_terms hf' hbd hp).tsum_le_tsum hle he.summable
  rw [he.tsum_eq] at h
  refine h.trans ?_
  have h1x : 0 < 1 - x := by linarith
  rw [show 2 * (1 - x)⁻¹ - 2 - 2 * x = (2 - 2 * (1 + x) * (1 - x)) / (1 - x) by field_simp; ring,
    div_le_iff₀ h1x]
  nlinarith [mul_nonneg (sq_nonneg x) (show (0 : ℝ) ≤ 1 - 3 * x by linarith)]

/-- **Off the extremal tails the two-adic local mass is below one.** -/
theorem localKernelMass_two_lt_one {f' : ArithmeticFunction ℝ} (hf' : f'.IsMultiplicative)
    (hbd : ∀ n, |f' n| ≤ 1)
    (h2 : ∃ m : ℕ, |f' (2 ^ (m + 2)) - f' 2 * f' (2 ^ (m + 1))| < 2) :
    localKernelMass f' 2 < 1 := by
  obtain ⟨m, hm⟩ := h2
  set x : ℝ := (2 : ℝ) ^ (-1 : ℝ)
  have hx : x = 1 / 2 := by simp only [x]; rw [Real.rpow_neg_one]; norm_num
  have hx0 : 0 ≤ x := by rw [hx]; norm_num
  have hx1 : x < 1 := by rw [hx]; norm_num
  have hgeo := hasSum_geometric_of_lt_one hx0 hx1
  set e : ℕ → ℝ := fun j => 2 * x ^ j - (if j = 0 then (2 : ℝ) else 0) - (if j = 1 then 2 * x else 0)
  have he : HasSum e (2 * (1 - x)⁻¹ - 2 - 2 * x) :=
    ((hgeo.mul_left 2).sub (hasSum_ite_eq 0 (2 : ℝ))).sub (hasSum_ite_eq 1 (2 * x))
  have hle : ∀ j, (if j = 0 then (0 : ℝ) else |companionKernel f' (2 ^ j)| * x ^ j) ≤ e j := by
    intro j
    simp only [e]
    rcases Nat.lt_or_ge j 2 with hj | hj
    · interval_cases j
      · simp
      · simp [companionKernel_prime hf' Nat.prime_two]
    · rw [if_neg (show j ≠ 0 by omega), if_neg (show j ≠ 0 by omega), if_neg (show j ≠ 1 by omega),
        sub_zero, sub_zero]
      exact mul_le_mul_of_nonneg_right (abs_companionKernel_prime_pow_le hf' hbd Nat.prime_two _)
        (pow_nonneg hx0 _)
  have hlt : (if m + 2 = 0 then (0 : ℝ) else |companionKernel f' (2 ^ (m + 2))| * x ^ (m + 2)) <
      e (m + 2) := by
    simp only [e]
    rw [if_neg (show m + 2 ≠ 0 by omega), if_neg (show m + 2 ≠ 0 by omega),
      if_neg (show m + 2 ≠ 1 by omega), sub_zero, sub_zero, show m + 2 = m + 1 + 1 from rfl,
      companionKernel_prime_pow f' Nat.prime_two (m + 1)]
    exact mul_lt_mul_of_pos_right hm (pow_pos (by rw [hx]; norm_num) _)
  have h := (summable_localKernelMass_terms hf' hbd Nat.prime_two).tsum_lt_tsum hle hlt he.summable
  rw [he.tsum_eq] at h
  have hval : 2 * (1 - x)⁻¹ - 2 - 2 * x = 1 := by rw [hx]; norm_num
  have hgoal : localKernelMass f' 2 = ∑' j : ℕ,
      (if j = 0 then (0 : ℝ) else |companionKernel f' (2 ^ j)| * x ^ j) := by
    simp only [localKernelMass, x, Nat.cast_ofNat]
  rw [hgoal]
  exact h.trans_eq hval

theorem localKernelMass_nonneg (f' : ArithmeticFunction ℝ) (p : ℕ) : 0 ≤ localKernelMass f' p :=
  tsum_nonneg fun j => by split_ifs <;> positivity

/-- **The local sums of the inverse kernel**: `Σ_k |h(p^k)| p^{-k} ≤ (1 − r_p)⁻¹` when `r_p < 1`. -/
theorem summable_and_tsum_inverseKernel_le {f' : ArithmeticFunction ℝ}
    (hf' : f'.IsMultiplicative) (hbd : ∀ n, |f' n| ≤ 1) {p : ℕ} (hp : p.Prime)
    (hr : localKernelMass f' p < 1) :
    Summable (fun k => |inverseKernel f' hf' (p ^ k)| * ((p : ℝ) ^ (-1 : ℝ)) ^ k) ∧
      ∑' k, |inverseKernel f' hf' (p ^ k)| * ((p : ℝ) ^ (-1 : ℝ)) ^ k ≤
        (1 - localKernelMass f' p)⁻¹ := by
  have hg := companionKernel_isMultiplicative hf'
  have hh := inverseKernel_isMultiplicative hf'
  have hx0 : 0 ≤ (p : ℝ) ^ (-1 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
  refine summable_and_tsum_abs_mul_pow_le_of_inv (a := fun j => companionKernel f' (p ^ j))
    (b := fun k => inverseKernel f' hf' (p ^ k)) hx0 (by simp [hg.map_one])
    (by simp [hh.map_one]) (fun k hk => ?_) (fun K => ?_) hr
  · have h := congrArg (fun F : ArithmeticFunction ℝ => F (p ^ k))
      (inverseKernel_mul_companionKernel hf')
    rw [mul_comm, mul_apply_prime_pow_eq _ _ hp] at h
    rw [h, ArithmeticFunction.one_apply_ne (by
      intro h1
      rcases Nat.pow_eq_one.mp h1 with h1 | h1
      · exact hp.ne_one h1
      · omega)]
  · exact (summable_localKernelMass_terms hf' hbd hp).sum_le_tsum (Finset.range (K + 1))
      (fun j _ => by split_ifs <;> positivity)

/-- **The inverse kernel is critical Wiener** off the extremal two-adic tails. -/
theorem criticalWiener_inverseKernel {f' : ArithmeticFunction ℝ} (hf' : f'.IsMultiplicative)
    (hbd : ∀ n, |f' n| ≤ 1)
    (h2 : ∃ m : ℕ, |f' (2 ^ (m + 2)) - f' 2 * f' (2 ^ (m + 1))| < 2) :
    CriticalWiener (dampedSignWeight ⇑(inverseKernel f' hf') (1 / 2)) := by
  set h := inverseKernel f' hf'
  have hh : h.IsMultiplicative := inverseKernel_isMultiplicative hf'
  let M : ArithmeticFunction ℝ := ⟨fun n => |h n| * (n : ℝ) ^ (-1 : ℝ), by simp⟩
  have hM : M.IsMultiplicative := by
    refine ⟨by simp [M, hh.map_one], fun {m n} hmn => ?_⟩
    simp only [M, ArithmeticFunction.coe_mk, hh.map_mul_of_coprime hmn, abs_mul, Nat.cast_mul,
      Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring
  have hM0 : ∀ n, 0 ≤ M n := fun n => by simp only [M, ArithmeticFunction.coe_mk]; positivity
  have hr2 := localKernelMass_two_lt_one hf' hbd h2
  have hrp : ∀ {p : ℕ}, p.Prime → localKernelMass f' p < 1 := fun {p} hp => by
    rcases hp.eq_two_or_odd' with rfl | hodd
    · exact hr2
    · have hp3 : 3 ≤ p := by
        rcases hodd with ⟨k, hk⟩
        have := hp.two_le; omega
      have h3 := localKernelMass_le_of_odd hf' hbd hp hp3
      have hx3 : (p : ℝ) ^ (-1 : ℝ) ≤ 1 / 3 := by
        rw [Real.rpow_neg_one, one_div]; exact inv_anti₀ (by norm_num) (by exact_mod_cast hp3)
      have hx0 : 0 ≤ (p : ℝ) ^ (-1 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      nlinarith
  have hMp : ∀ {p : ℕ}, p.Prime → ∀ k, M (p ^ k) =
      |h (p ^ k)| * ((p : ℝ) ^ (-1 : ℝ)) ^ k := fun {p} hp k => by
    have hx : ((p ^ k : ℕ) : ℝ) ^ (-1 : ℝ) = ((p : ℝ) ^ (-1 : ℝ)) ^ k := by
      rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _),
        ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _), mul_comm]
    simp only [M, ArithmeticFunction.coe_mk]
    rw [hx]
  set b : ℕ → ℝ := fun n => if n.Prime then Real.log (1 - localKernelMass f' n)⁻¹ else 0
  have hb0 : ∀ n, 0 ≤ b n := fun n => by
    simp only [b]
    split_ifs with hn
    · exact Real.log_nonneg (one_le_inv₀ (by linarith [hrp hn]) |>.mpr
        (by linarith [localKernelMass_nonneg f' n]))
    · exact le_rfl
  -- `b(p) ≤ 9/(2p²)` at odd primes
  have hbodd : ∀ n : ℕ, n ≠ 2 → b n ≤ 9 / 2 * (n : ℝ) ^ (-2 : ℝ) := by
    intro n hn2
    simp only [b]
    split_ifs with hn
    · have hn3 : 3 ≤ n := by have := hn.two_le; omega
      have h3 := localKernelMass_le_of_odd hf' hbd hn hn3
      have hx0 : 0 ≤ (n : ℝ) ^ (-1 : ℝ) := Real.rpow_nonneg (Nat.cast_nonneg _) _
      have hx3 : (n : ℝ) ^ (-1 : ℝ) ≤ 1 / 3 := by
        rw [Real.rpow_neg_one, one_div]; exact inv_anti₀ (by norm_num) (by exact_mod_cast hn3)
      have hsq : ((n : ℝ) ^ (-1 : ℝ)) ^ 2 = (n : ℝ) ^ (-2 : ℝ) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]; norm_num
      set r := localKernelMass f' n
      have hr0 := localKernelMass_nonneg f' n
      have hr13 : r ≤ 1 / 3 := by nlinarith
      have hlog := Real.log_le_sub_one_of_pos (inv_pos.mpr (show 0 < 1 - r by linarith))
      have hinv : (1 - r)⁻¹ - 1 ≤ 3 / 2 * r := by
        rw [inv_eq_one_div, div_sub_one (by linarith : (0 : ℝ) < 1 - r).ne',
          div_le_iff₀ (by linarith)]
        nlinarith
      rw [← hsq]; nlinarith
    · positivity
  have hb : Summable b := by
    refine (summable_nat_add_iff 3).mp ?_
    refine (((Real.summable_nat_rpow.mpr (by norm_num : (-2 : ℝ) < -1)).comp_injective
      (add_left_injective 3)).mul_left (9 / 2)).of_nonneg_of_le (fun n => hb0 _) fun n => ?_
    exact hbodd (n + 3) (by omega)
  have hloc : ∀ {p : ℕ}, p.Prime → Summable (fun k : ℕ => M (p ^ k)) := fun {p} hp => by
    simpa only [hMp hp] using (summable_and_tsum_inverseKernel_le hf' hbd hp (hrp hp)).1
  have hbound : ∀ {p : ℕ}, p.Prime → (∑' k : ℕ, M (p ^ k)) ≤ Real.exp (b p) := fun {p} hp => by
    simp only [hMp hp, b, if_pos hp]
    rw [Real.exp_log (inv_pos.mpr (by linarith [hrp hp]))]
    exact (summable_and_tsum_inverseKernel_le hf' hbd hp (hrp hp)).2
  have hsum := RHTower.pm_summable_of_multiplicative_local_bound M hM hM0 hloc b hb0 hb hbound
  unfold CriticalWiener
  refine hsum.congr fun n => ?_
  simp only [M, ArithmeticFunction.coe_mk, dampedSignWeight]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow (show (-1 : ℝ) ≠ 0 by norm_num)]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [abs_mul, abs_of_nonneg (Real.rpow_nonneg hn0.le _), mul_assoc, ← Real.rpow_add hn0]
    norm_num

/-! ### Invisibility -/

/-- **Higher prime powers are invisible off the two-adic boundary.** For multiplicative `f'` with
`|f'| ≤ 1` and some non-extremal two-adic step, `f'(d) d^{-1/2}` is paid iff the completely
multiplicative companion `f(d) d^{-1/2}` is. -/
theorem receiverBounded_half_iff_companion {f' : ArithmeticFunction ℝ}
    (hf' : f'.IsMultiplicative) (hbd : ∀ n, |f' n| ≤ 1)
    (h2 : ∃ m : ℕ, |f' (2 ^ (m + 2)) - f' 2 * f' (2 ^ (m + 1))| < 2) :
    ReceiverBounded (dampedSignWeight ⇑f' (1 / 2)) ↔
      ReceiverBounded (dampedSignWeight (primeValueHom fun p => f' p) (1 / 2)) := by
  set f : ℕ →*₀ ℝ := primeValueHom fun p => f' p
  have hf : ∀ p : ℕ, p.Prime → |f p| ≤ 1 := fun p hp => by
    simp only [f]; rw [primeValueHom_prime _ hp]; exact hbd p
  constructor
  · intro hR
    -- `f = h ⋆ f'`
    have hfg : f' = companionKernel f' * patternAF f := by
      rw [companionKernel, mul_assoc, patternMoebiusAF_mul_patternAF, mul_one]
    have hF : patternAF f = inverseKernel f' hf' * f' := by
      have h := congrArg (fun F => inverseKernel f' hf' * F) hfg
      rw [h, ← mul_assoc, inverseKernel_mul_companionKernel, one_mul]
    have hw : dampedSignWeight f (1 / 2) =
        RHTower.dirichletConv (dampedSignWeight ⇑(inverseKernel f' hf') (1 / 2))
          (dampedSignWeight ⇑f' (1 / 2)) := by
      rw [← dampedSignWeight_mul, ← hF]; rfl
    rw [hw]
    exact receiverBounded_dirichletConv (criticalWiener_inverseKernel hf' hbd h2)
      (summable_abs_dampedSign_div_of_abs_le hbd (by norm_num)) hR
  · intro hR
    refine receiverBounded_of_summable_prime_diff hf' hbd hf (by norm_num) ?_ hR
    refine (summable_zero).congr fun p => ?_
    split_ifs with hp
    · simp only [f]; rw [primeValueHom_prime _ hp, sub_self, abs_zero, zero_mul]
    · rfl

/-- **The extremal two-adic tails.** Every two-adic step is extremal iff `f'(2^k) = −1` for all
`k ≥ 1`, or `f'(2^k) = (−1)^{k+1}` for all `k ≥ 1`. -/
theorem twoAdicStep_extremal_iff {f' : ArithmeticFunction ℝ} (hbd : ∀ n, |f' n| ≤ 1) :
    (∀ m : ℕ, |f' (2 ^ (m + 2)) - f' 2 * f' (2 ^ (m + 1))| = 2) ↔
      (∀ k : ℕ, f' (2 ^ (k + 1)) = -1) ∨ (∀ k : ℕ, f' (2 ^ (k + 1)) = (-1) ^ k) := by
  have key : ∀ u v : ℝ, |u| ≤ 1 → |v| ≤ 1 → |u - v| = 2 → u = -v ∧ (v = 1 ∨ v = -1) := by
    intro u v hu hv h
    rw [abs_le] at hu hv
    rcases abs_eq (by norm_num : (0 : ℝ) ≤ 2) |>.mp h with h' | h'
    · exact ⟨by linarith, Or.inr (by linarith)⟩
    · exact ⟨by linarith, Or.inl (by linarith)⟩
  have h2 : f' 2 = f' (2 ^ (0 + 1)) := by norm_num
  constructor
  · intro hext
    set a : ℕ → ℝ := fun k => f' (2 ^ (k + 1))
    have hrec : ∀ m, a (m + 1) = -(a 0 * a m) := fun m => by
      have := key _ _ (hbd _) (by rw [abs_mul]; exact mul_le_one₀ (hbd _) (abs_nonneg _) (hbd _))
        (hext m)
      simp only [a]; rw [← h2]; exact this.1
    have ha0 : a 0 = 1 ∨ a 0 = -1 := by
      have h := key _ _ (hbd _) (by rw [abs_mul]; exact mul_le_one₀ (hbd _) (abs_nonneg _) (hbd _))
        (hext 0)
      rcases h.2 with h1 | h1
      · -- `a₀² = 1`
        have : a 0 * a 0 = 1 := by simp only [a]; rw [← h2]; simpa using h1
        have : (a 0 - 1) * (a 0 + 1) = 0 := by linear_combination this
        rcases mul_eq_zero.mp this with h | h
        · left; linarith
        · right; linarith
      · have : a 0 * a 0 = -1 := by simp only [a]; rw [← h2]; simpa using h1
        exfalso; nlinarith [sq_nonneg (a 0)]
    rcases ha0 with h1 | h1
    · right
      intro k
      induction k with
      | zero => simpa [a] using h1
      | succ n ih =>
        have := hrec n
        simp only [a] at this ih h1
        rw [this, h1, ih, pow_succ]; ring
    · left
      intro k
      induction k with
      | zero => simpa [a] using h1
      | succ n ih =>
        have := hrec n
        simp only [a] at this ih h1
        rw [this, h1, ih]; ring
  · rintro (h | h) m
    · rw [h2, show m + 2 = m + 1 + 1 from rfl, h (m + 1), h m, h 0]; norm_num
    · rw [h2, show m + 2 = m + 1 + 1 from rfl, h (m + 1), h m, h 0, pow_succ]
      rcases neg_one_pow_eq_or ℝ m with h' | h' <;> rw [h'] <;> norm_num

/-! ### A local factor repairs the boundary -/

/-- The two-adic repair `f'(n) = (−1)^{[2 ∣ n]} f_{t₀}(n)` of the boundary pattern. -/
def twoAdicRepair (t₀ : ℝ) : ArithmeticFunction ℝ :=
  ⟨fun n => (if 2 ∣ n then -1 else 1) * oscPattern 1 t₀ n, by simp⟩

theorem twoAdicRepair_apply (t₀ : ℝ) (n : ℕ) :
    twoAdicRepair t₀ n = (if 2 ∣ n then -1 else 1) * oscPattern 1 t₀ n := rfl

theorem twoAdicRepair_isMultiplicative (t₀ : ℝ) : (twoAdicRepair t₀).IsMultiplicative := by
  refine ⟨by simp [twoAdicRepair_apply], fun {m n} hmn => ?_⟩
  simp only [twoAdicRepair_apply, map_mul]
  by_cases hm : 2 ∣ m <;> by_cases hn : 2 ∣ n
  · exact absurd (Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hm hmn) hn)
      (by norm_num)
  · rw [if_pos (dvd_mul_of_dvd_left hm n), if_pos hm, if_neg hn]; ring
  · rw [if_pos (dvd_mul_of_dvd_right hn m), if_neg hm, if_pos hn]; ring
  · rw [if_neg (fun h => by rcases (Nat.prime_two.dvd_mul).mp h with h | h <;> contradiction),
      if_neg hm, if_neg hn]; ring

theorem abs_twoAdicRepair_le (t₀ : ℝ) (n : ℕ) : |twoAdicRepair t₀ n| ≤ 1 := by
  rw [twoAdicRepair_apply, abs_mul]
  have h1 : |(if 2 ∣ n then (-1 : ℝ) else 1)| = 1 := by split_ifs <;> simp
  rw [h1, one_mul]; exact abs_oscPattern_le (by norm_num) t₀ n

theorem oscPattern_two_of_height {t₀ : ℝ} {m : ℕ} (ht : t₀ * Real.log 2 = 2 * Real.pi * m) :
    oscPattern 1 t₀ 2 = 1 := by
  rw [oscPattern_prime 1 t₀ Nat.prime_two, one_mul, show ((2 : ℕ) : ℝ) = 2 by norm_num, ht,
    show 2 * Real.pi * (m : ℝ) = m * (2 * Real.pi) by ring, Real.cos_nat_mul_two_pi]

/-- At `t₀ log 2 ∈ 2πℕ` the repair has the extremal tail `f'(2^k) = −1`. -/
theorem twoAdicRepair_two_pow {t₀ : ℝ} {m : ℕ} (ht : t₀ * Real.log 2 = 2 * Real.pi * m) (k : ℕ) :
    twoAdicRepair t₀ (2 ^ (k + 1)) = -1 := by
  rw [twoAdicRepair_apply, if_pos (dvd_pow_self 2 (Nat.succ_ne_zero k)), map_pow,
    oscPattern_two_of_height ht, one_pow, mul_one]

/-- The shifted Dirichlet series of a half-damped weight `s(d) d^{-1/2}` with `s(0) = 0`. -/
theorem weightDirichletSeries_dampedHalf {s : ℕ → ℝ} (hs0 : s 0 = 0) (z : ℂ) :
    weightDirichletSeries (dampedSignWeight s (1 / 2)) z =
      ∑' n : ℕ, (s n : ℂ) * ((n : ℝ) : ℂ) ^ (-(z + 1 / 2)) := by
  refine tsum_congr fun d => ?_
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · simp [dampedSignWeight, hs0]
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hdC : ((d : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hd0.ne'
  simp only [dampedSignWeight]
  rw [Complex.ofReal_mul, Complex.ofReal_cpow hd0.le, mul_assoc, ← Complex.cpow_add _ _ hdC]
  congr 2
  push_cast
  ring

/-- **The repaired series**: `Σ f'(n) n^{-w} = (1 − 2·2^{-w}) F_{t₀}(w)` on `Re w > 1`. -/
theorem tsum_twoAdicRepair {t₀ : ℝ} {m : ℕ} (ht : t₀ * Real.log 2 = 2 * Real.pi * m) {w : ℂ}
    (hw : 1 < w.re) :
    ∑' n : ℕ, (twoAdicRepair t₀ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w) =
      (1 - 2 * (2 : ℂ) ^ (-w)) * ∑' n : ℕ, (oscPattern 1 t₀ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w) := by
  set T : ℕ → ℂ := fun n => (oscPattern 1 t₀ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w)
  have hTn : ∀ n, ‖T n‖ ≤ (n : ℝ) ^ (-w.re) := fun n => by
    simp only [T, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [Real.zero_rpow (show -w.re ≠ 0 by intro h; linarith)]
    · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
      rw [Complex.norm_cpow_eq_rpow_re_of_pos hn0, Complex.neg_re]
      exact mul_le_of_le_one_left (Real.rpow_nonneg hn0.le _)
        (abs_oscPattern_le (by norm_num) t₀ n)
  have hR : Summable fun n : ℕ => (n : ℝ) ^ (-w.re) :=
    Real.summable_nat_rpow.mpr (show -w.re < -1 by linarith)
  have hTs : Summable T := hR.of_norm_bounded hTn
  set E : ℕ → ℂ := fun n => if 2 ∣ n then T n else 0
  have hEs : Summable E := hR.of_norm_bounded fun n => by
    simp only [E]
    split_ifs
    · exact hTn n
    · rw [norm_zero]; exact Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hpt : ∀ n, (twoAdicRepair t₀ n : ℂ) * ((n : ℝ) : ℂ) ^ (-w) = T n - 2 * E n := fun n => by
    simp only [twoAdicRepair_apply, T, E]
    split_ifs <;> push_cast <;> ring
  have hE : ∑' n, E n = (2 : ℂ) ^ (-w) * ∑' n, T n := by
    have hinj : Function.Injective (fun k : ℕ => 2 * k) := fun a b h => by simpa using h
    have hsupp : Function.support E ⊆ Set.range (fun k : ℕ => 2 * k) := fun n hn => by
      simp only [Function.mem_support, E] at hn
      split_ifs at hn with h2
      · obtain ⟨k, rfl⟩ := h2; exact ⟨k, rfl⟩
      · exact absurd rfl hn
    rw [← hinj.tsum_eq hsupp, ← tsum_mul_left]
    refine tsum_congr fun k => ?_
    simp only [E, T, if_pos (dvd_mul_right 2 k), map_mul, oscPattern_two_of_height ht, one_mul]
    rw [Nat.cast_mul, Complex.ofReal_mul, Complex.mul_cpow_ofReal_nonneg (by norm_num)
      (Nat.cast_nonneg k)]
    push_cast
    ring
  rw [tsum_congr hpt, hTs.tsum_sub (hEs.mul_left 2), tsum_mul_left, hE]
  ring

/-- `|1 − 2·2^{-w}| ≤ 2 min(1, |w − it₀ − 1|)` at `t₀ log 2 ∈ 2πℕ`, `Re w > 1`: the factor vanishes
at `w = 1 + it₀`. -/
theorem norm_one_sub_two_mul_cpow_le {t₀ : ℝ} {m : ℕ} (ht : t₀ * Real.log 2 = 2 * Real.pi * m)
    {w : ℂ} (hw : 1 < w.re) :
    ‖1 - 2 * (2 : ℂ) ^ (-w)‖ ≤ 2 * min 1 ‖w - t₀ * I - 1‖ := by
  set z : ℂ := w - t₀ * I - 1
  have hlog2 : Complex.log 2 = (Real.log 2 : ℂ) := by
    rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num, ← Complex.ofReal_log (by norm_num)]
  have hfac : 2 * (2 : ℂ) ^ (-w) = Complex.exp (-(z * (Real.log 2 : ℂ))) := by
    rw [Complex.cpow_def_of_ne_zero (by norm_num), hlog2]
    have h2 : (2 : ℂ) = Complex.exp (Real.log 2 : ℂ) := by
      rw [← Complex.ofReal_exp, Real.exp_log (by norm_num)]; norm_num
    have hper : Complex.exp (-(((t₀ * Real.log 2 : ℝ) : ℂ) * I)) = 1 := by
      rw [ht]
      rw [show -(((2 * Real.pi * (m : ℝ) : ℝ) : ℂ) * I) = ((-(m : ℤ) : ℤ) : ℂ) * (2 * Real.pi * I) by
        push_cast; ring]
      exact Complex.exp_int_mul_two_pi_mul_I _
    calc 2 * Complex.exp (Real.log 2 * -w)
        = Complex.exp (Real.log 2 : ℂ) * Complex.exp (Real.log 2 * -w) := by rw [← h2]
      _ = Complex.exp (-(z * (Real.log 2 : ℂ))) *
            Complex.exp (-(((t₀ * Real.log 2 : ℝ) : ℂ) * I)) := by
          rw [← Complex.exp_add, ← Complex.exp_add]; congr 1; simp only [z]; push_cast; ring
      _ = Complex.exp (-(z * (Real.log 2 : ℂ))) := by rw [hper, mul_one]
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl21 : Real.log 2 < 1 := by have := Real.log_two_lt_d9; linarith
  rcases le_or_gt ‖z‖ 1 with hz | hz
  · rw [min_eq_right hz, hfac, ← neg_sub, norm_neg]
    have hx : ‖-(z * (Real.log 2 : ℂ))‖ ≤ 1 := by
      rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl2]; nlinarith
    refine (Complex.norm_exp_sub_one_le hx).trans ?_
    rw [norm_neg, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hl2]
    nlinarith [norm_nonneg z]
  · rw [min_eq_left hz.le, mul_one]
    have h2w : ‖(2 : ℂ) ^ (-w)‖ ≤ 1 / 2 := by
      rw [show (2 : ℂ) = ((2 : ℝ) : ℂ) by norm_num,
        Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num : (0 : ℝ) < 2), Complex.neg_re]
      calc (2 : ℝ) ^ (-w.re) ≤ 2 ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 1 / 2 := by rw [Real.rpow_neg_one]; norm_num
    calc ‖1 - 2 * (2 : ℂ) ^ (-w)‖ ≤ ‖(1 : ℂ)‖ + ‖2 * (2 : ℂ) ^ (-w)‖ := norm_sub_le _ _
      _ ≤ 1 + 2 * (1 / 2) := by
          rw [norm_one, norm_mul, show ‖(2 : ℂ)‖ = 2 by norm_num]; linarith
      _ = 2 := by norm_num

/-- **The two-adic repair is paid**, whatever `ζ(1/2 + it₀)` is: on the box the factor
`|1 − 2^{1−w}| ≤ 2 min(1, |z|)` cancels `|F_{t₀}(w)| ≤ B |z|^{-1/2}`, `z = w − it₀ − 1`. -/
theorem receiverBounded_twoAdicRepair {t₀ : ℝ} (ht₀ : 0 < t₀) {m : ℕ}
    (ht : t₀ * Real.log 2 = 2 * Real.pi * m) :
    ReceiverBounded (dampedSignWeight ⇑(twoAdicRepair t₀) (1 / 2)) := by
  obtain ⟨B, hB0, hBs⟩ := exists_norm_oscSeries_le_small (a := 1) zero_le_one le_rfl ht₀
  set T : ℝ := 2 * t₀ + 2
  have hT : 2 ≤ T := by simp only [T]; linarith
  obtain ⟨Z₀, hZ₀, hZ⟩ := exists_norm_zeta_le_on_tall_box T
  set c := dampedSignWeight ⇑(twoAdicRepair t₀) (1 / 2)
  set P : ℝ := ∑' d : ℕ, c d / d
  set A : ℝ := 4 * (Z₀ ^ 2 * (2 * (2 * B) ^ 2 + 2 * P ^ 2))
  have hA0 : 0 ≤ A := by positivity
  have hs0 : twoAdicRepair t₀ 0 = 0 := by simp
  have hwre : ∀ σ y : ℝ, ((σ : ℂ) + y * I + 1 / 2).re = σ + 1 / 2 := fun σ y => by simp
  have hwim : ∀ σ y : ℝ, ((σ : ℂ) + y * I + 1 / 2).im = y := fun σ y => by simp
  have hC : ∀ σ y : ℝ, 1 / 2 < σ → weightDirichletSeries c ((σ : ℂ) + y * I) =
      (1 - 2 * (2 : ℂ) ^ (-((σ : ℂ) + y * I + 1 / 2))) *
        ∑' n : ℕ, (oscPattern 1 t₀ n : ℂ) * ((n : ℝ) : ℂ) ^ (-((σ : ℂ) + y * I + 1 / 2)) := by
    intro σ y hσ
    rw [weightDirichletSeries_dampedHalf hs0]
    exact tsum_twoAdicRepair ht (by rw [hwre]; linarith)
  -- `|C(s)| ≤ 2B` on the box
  have hCbox : ∀ σ y : ℝ, 1 / 2 < σ → σ < 3 / 4 → 0 < y → y ≤ T →
      ‖weightDirichletSeries c ((σ : ℂ) + y * I)‖ ≤ 2 * B := by
    intro σ y hσ hσ' hy hyT
    have hw1 : 1 < ((σ : ℂ) + y * I + 1 / 2).re := by rw [hwre]; linarith
    have hF := hBs ((σ : ℂ) + y * I + 1 / 2) hw1 (by rw [hwre]; linarith) (by rw [hwim]; exact hy)
      (by rw [hwim]; exact hyT)
    have hfac := norm_one_sub_two_mul_cpow_le ht hw1
    set z := ‖(σ : ℂ) + y * I + 1 / 2 - t₀ * I - 1‖
    have hz0 : 0 < z := by
      refine lt_of_lt_of_le ?_ (Complex.abs_re_le_norm ((σ : ℂ) + y * I + 1 / 2 - t₀ * I - 1))
      have : ((σ : ℂ) + y * I + 1 / 2 - t₀ * I - 1).re = σ - 1 / 2 := by simp; ring
      rw [this, abs_of_pos (by linarith)]; linarith
    rw [hC σ y hσ, norm_mul]
    have hkey : min 1 z * z ^ (-(1 / 2 : ℝ)) ≤ 1 := by
      rcases le_or_gt z 1 with h | h
      · rw [min_eq_right h]
        calc z * z ^ (-(1 / 2 : ℝ)) = z ^ ((1 : ℝ) + -(1 / 2)) := by
              rw [Real.rpow_add hz0, Real.rpow_one]
          _ ≤ 1 := Real.rpow_le_one hz0.le h (by norm_num)
      · rw [min_eq_left h.le, one_mul]
        exact Real.rpow_le_one_of_one_le_of_nonpos h.le (by norm_num)
    calc _ ≤ (2 * min 1 z) * (B * z ^ (-(1 / 2 : ℝ))) :=
          mul_le_mul hfac hF (norm_nonneg _) (by positivity)
      _ = 2 * B * (min 1 z * z ^ (-(1 / 2 : ℝ))) := by ring
      _ ≤ 2 * B * 1 := mul_le_mul_of_nonneg_left hkey (by positivity)
      _ = 2 * B := mul_one _
  have hsmall : ∀ σ y : ℝ, 1 / 2 < σ → σ < 3 / 4 → 0 < y → y ≤ T → y ≠ t₀ →
      lineIntegrand c P σ y ≤ (fun _ : ℝ => A) y := by
    intro σ y hσ hσ' hy hyT _
    have hCP : ‖weightDirichletSeries c ((σ : ℂ) + y * I) - (P : ℂ)‖ ≤ 2 * B + |P| :=
      (norm_sub_le _ _).trans (add_le_add (hCbox σ y hσ hσ' hy hyT)
        (by rw [Complex.norm_real, Real.norm_eq_abs]))
    have hsq : ‖weightDirichletSeries c ((σ : ℂ) + y * I) - (P : ℂ)‖ ^ 2 ≤
        2 * (2 * B) ^ 2 + 2 * P ^ 2 := by
      have h := pow_le_pow_left₀ (norm_nonneg _) hCP 2
      nlinarith [sq_nonneg (2 * B - |P|), sq_abs P]
    have hζ2 : ‖riemannZeta ((σ : ℂ) + y * I)‖ ^ 2 ≤ Z₀ ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hZ σ y hσ.le hσ'.le (by rw [abs_of_pos hy]; exact hyT)) 2
    have hsn : σ ≤ ‖(σ : ℂ) + y * I‖ := by
      have := Complex.abs_re_le_norm ((σ : ℂ) + y * I)
      simp only [add_re, ofReal_re, mul_re, I_re, mul_zero, ofReal_im, I_im, mul_one, sub_self,
        add_zero] at this
      linarith [le_abs_self σ]
    have hs2 : (1 / 2 : ℝ) ^ 2 ≤ ‖(σ : ℂ) + y * I‖ ^ 2 :=
      pow_le_pow_left₀ (by norm_num) (by linarith) 2
    have hden : 0 < ‖(σ : ℂ) + y * I‖ ^ 2 := lt_of_lt_of_le (by norm_num) hs2
    show lineIntegrand c P σ y ≤ A
    simp only [lineIntegrand, norm_div, norm_mul, div_pow, mul_pow]
    rw [div_le_iff₀ hden]
    calc _ ≤ Z₀ ^ 2 * (2 * (2 * B) ^ 2 + 2 * P ^ 2) :=
          mul_le_mul hζ2 hsq (sq_nonneg _) (sq_nonneg _)
      _ = A * (1 / 2) ^ 2 := by simp only [A]; ring
      _ ≤ A * ‖(σ : ℂ) + y * I‖ ^ 2 := mul_le_mul_of_nonneg_left hs2 hA0
  have hlarge : ∀ σ y : ℝ, 1 / 2 < σ → σ < 3 / 4 → T < y →
      ‖weightDirichletSeries c ((σ : ℂ) + y * I) - (P : ℂ)‖ ≤
        (20 * Real.exp (2 * primeSquareMass) + |P|) * y ^ (1 / 4 : ℝ) := by
    intro σ y hσ hσ' hy
    have hw1 : 1 < ((σ : ℂ) + y * I + 1 / 2).re := by rw [hwre]; linarith
    have hF := norm_oscSeries_le_large (a := 1) zero_le_one le_rfl ht₀ hw1 (by rw [hwre]; linarith)
      (by rw [hwim]; exact hy)
    rw [hwim] at hF
    have hfac : ‖1 - 2 * (2 : ℂ) ^ (-((σ : ℂ) + y * I + 1 / 2))‖ ≤ 2 :=
      (norm_one_sub_two_mul_cpow_le ht hw1).trans (by
        have := min_le_left 1 ‖(σ : ℂ) + y * I + 1 / 2 - t₀ * I - 1‖; linarith)
    rw [hC σ y hσ]
    refine (norm_sub_le _ _).trans ?_
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have h1 : 1 ≤ y ^ (1 / 4 : ℝ) := Real.one_le_rpow (by linarith) (by norm_num)
    have := mul_le_mul hfac hF (norm_nonneg _) (by norm_num)
    nlinarith [abs_nonneg P, Real.exp_pos (2 * primeSquareMass)]
  have hg : IntegrableOn (fun _ : ℝ => A) (Ioc 0 T) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).mp intervalIntegrable_const
  obtain ⟨M, hM⟩ := exists_lineEnergy_le_of_majorant (g := fun _ : ℝ => A) (t₁ := t₀) hT hg hsmall
    hlarge
  have hcd : DampedClass 1 (1 / 2) c := fun d => by
    simp only [c, dampedSignWeight]
    rw [one_mul, abs_mul, abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg d) _)]
    exact mul_le_of_le_one_left (Real.rpow_nonneg (Nat.cast_nonneg d) _) (abs_twoAdicRepair_le t₀ d)
  exact ⟨3 * M / (4 * Real.pi), weightPronicEnergy_le_of_lineEnergy_le hcd hM⟩

/-- **Its completely multiplicative companion reads the critical zero**: it differs from
`cos(t₀ log p)` only at `p = 2`, so it is paid iff `ζ(1/2 + it₀) = 0`. -/
theorem receiverBounded_twoAdicCompanion_iff {t₀ : ℝ} (ht₀ : 0 < t₀) :
    ReceiverBounded (dampedSignWeight (primeValueHom fun p => twoAdicRepair t₀ p) (1 / 2)) ↔
      riemannZeta (1 / 2 + t₀ * I) = 0 := by
  set f' : ℕ →*₀ ℝ := primeValueHom fun p => twoAdicRepair t₀ p
  have hf' : ∀ p : ℕ, p.Prime → |f' p| ≤ 1 := fun p hp => by
    simp only [f']; rw [primeValueHom_prime _ hp]; exact abs_twoAdicRepair_le t₀ p
  have hf : ∀ p : ℕ, p.Prime → |oscPattern 1 t₀ p| ≤ 1 := fun p _ =>
    abs_oscPattern_le (by norm_num) t₀ p
  have hdiff : Summable (fun p : ℕ => if p.Prime then
      |f' p - oscPattern 1 t₀ p| * (p : ℝ) ^ (-(1 / 2 + 1 / 2 : ℝ)) else 0) := by
    refine summable_of_ne_finset_zero (s := {2}) fun p hp => ?_
    rw [Finset.mem_singleton] at hp
    split_ifs with hpp
    · have hodd : ¬ 2 ∣ p := fun h =>
        hp ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hpp).mp h).symm
      simp only [f']
      rw [primeValueHom_prime _ hpp, twoAdicRepair_apply, if_neg hodd, one_mul, sub_self, abs_zero,
        zero_mul]
    · rfl
  rw [receiverBounded_iff_of_summable_prime_diff hf hf' (by norm_num) hdiff]
  exact receiverBounded_oscWeight_one_iff ht₀.ne'

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
