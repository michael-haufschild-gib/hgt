import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheTailDecouplesFromTheHead

/-!
# The conditional moments of the tail

Let `R(t) = Σ_{m∈A} r_m m^{it}` be a head weight on `y`-smooth integers and `B(t) = Σ_{p∈B} b_p p^{it}` a tail polynomial
on primes `p ≥ y`. Every power `B^k` is a tail polynomial (`headPoly_pow`): it lives on products of `k` tail primes, which
are rough, with coefficients the `k`-fold convolution of `b`. So the decoupling theorem applies to `B^k`.

* **The Steinhaus bound** (`powNorm_le`). The coefficients of `B^k` have squared norm at most `k! (Σ|b_p|²)^k`: a
  product of `k` primes has at most `k` distinct prime factors, so each coefficient of `B^{k+1}` is a sum of at most
  `k + 1` terms, and Cauchy–Schwarz gives `‖B^{k+1}‖² ≤ (k + 1) ‖B^k‖² ‖b‖²`.
* **Gaussian conditional moments** (`integral_head_mul_tail_pow_le`).
  `∫_T^{2T} |R|²|B|^{2k} ≤ (T + 8N(1 + log N)) ‖r‖² k! ‖b‖^{2k}` whenever `N ≥ m Z^k` for the head integers `m` and a
  bound `Z` on the tail primes. Against `∫_T^{2T} |R|² = T‖r‖²(1 + O(N log N/T))` these are the moments of a complex
  Gaussian of variance `‖b‖²`: conditionally on the head, the tail is Gaussian through order `k` as long as
  `log max A + k log Z ≪ log T`.
* **Conditional large deviations** (`setIntegral_head_on_large_tail_le`). The head weight of the heights in `[T, 2T]`
  where `|B| ≥ V` is at most `(T + 8N(1 + log N)) ‖r‖² k! (‖b‖²/V²)^k`.

For a bounded return at a right zero the tail must deviate from its typical size by a definite amount at every cut (see
`TheTailOfAReturnCarriesTheZero`); this is the price of such a deviation, conditionally on the head, in the range where
the head resonator is shorter than the height.
-/

open Finset Real MeasureTheory

namespace GaloisForLFunctions.TailArithmeticOfThePrimeOrbit

noncomputable section

/-- The products `mn`, `m ∈ A`, `n ∈ B`. -/
def mulSupport (A B : Finset ℕ) : Finset ℕ := (A ×ˢ B).image fun x => x.1 * x.2

/-- The convolution of `r` on `A` with `b` on `B`. -/
def convCoeff (A B : Finset ℕ) (r b : ℕ → ℂ) (q : ℕ) : ℂ :=
  ∑ x ∈ (A ×ˢ B).filter (fun x => x.1 * x.2 = q), r x.1 * b x.2

theorem indexedPoly_eq_headPoly_image {J : Type*} [DecidableEq J] (E : Finset J) (k : J → ℕ) (c : J → ℂ)
    (t : ℝ) :
    indexedPoly E k c t = headPoly (E.image k) (fun q => ∑ j ∈ E.filter (fun j => k j = q), c j) t := by
  unfold indexedPoly headPoly
  rw [← Finset.sum_fiberwise_of_maps_to (g := k) (fun j hj => Finset.mem_image_of_mem k hj)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [(Finset.mem_filter.mp hj).2]

theorem headPoly_mul_headPoly {A B : Finset ℕ} (r b : ℕ → ℂ) (hA : ∀ m ∈ A, m ≠ 0) (hB : ∀ n ∈ B, n ≠ 0)
    (t : ℝ) : headPoly A r t * headPoly B b t = headPoly (mulSupport A B) (convCoeff A B r b) t := by
  rw [headPoly_mul A B r b hA hB, indexedPoly_eq_headPoly_image]
  rfl

/-- The support of `B^k`. -/
def powSupport (B : Finset ℕ) : ℕ → Finset ℕ
  | 0 => {1}
  | k + 1 => mulSupport (powSupport B k) B

/-- The coefficients of `B^k`. -/
def powCoeff (B : Finset ℕ) (b : ℕ → ℂ) : ℕ → ℕ → ℂ
  | 0 => fun _ => 1
  | k + 1 => convCoeff (powSupport B k) B (powCoeff B b k) b

theorem mem_powSupport_succ {B : Finset ℕ} {k q : ℕ} :
    q ∈ powSupport B (k + 1) ↔ ∃ m ∈ powSupport B k, ∃ n ∈ B, m * n = q := by
  simp only [powSupport, mulSupport, Finset.mem_image, Finset.mem_product, Prod.exists]
  constructor
  · rintro ⟨m, n, ⟨hm, hn⟩, rfl⟩; exact ⟨m, hm, n, hn, rfl⟩
  · rintro ⟨m, hm, n, hn, rfl⟩; exact ⟨m, n, ⟨hm, hn⟩, rfl⟩

theorem powSupport_ne_zero {B : Finset ℕ} (hB : ∀ n ∈ B, n ≠ 0) : ∀ k, ∀ q ∈ powSupport B k, q ≠ 0
  | 0, q, hq => by simp [powSupport] at hq; omega
  | k + 1, q, hq => by
    obtain ⟨m, hm, n, hn, rfl⟩ := mem_powSupport_succ.mp hq
    exact Nat.mul_ne_zero (powSupport_ne_zero hB k m hm) (hB n hn)

theorem isRough_one (y : ℕ) : IsRough y 1 :=
  ⟨one_ne_zero, fun _ hp h => absurd h hp.not_dvd_one⟩

theorem IsRough.mul {y m n : ℕ} (hm : IsRough y m) (hn : IsRough y n) : IsRough y (m * n) :=
  ⟨Nat.mul_ne_zero hm.1 hn.1, fun p hp h => (hp.dvd_mul.mp h).elim (hm.2 p hp) (hn.2 p hp)⟩

theorem powSupport_rough {y : ℕ} {B : Finset ℕ} (hB : ∀ n ∈ B, IsRough y n) :
    ∀ k, ∀ q ∈ powSupport B k, IsRough y q
  | 0, q, hq => by
    simp [powSupport] at hq
    rw [hq]
    exact isRough_one y
  | k + 1, q, hq => by
    obtain ⟨m, hm, n, hn, rfl⟩ := mem_powSupport_succ.mp hq
    exact (powSupport_rough hB k m hm).mul (hB n hn)

theorem powSupport_le {B : Finset ℕ} {Z : ℕ} (hZ : ∀ n ∈ B, n ≤ Z) : ∀ k, ∀ q ∈ powSupport B k, q ≤ Z ^ k
  | 0, q, hq => by simp [powSupport] at hq; simp [hq]
  | k + 1, q, hq => by
    obtain ⟨m, hm, n, hn, rfl⟩ := mem_powSupport_succ.mp hq
    rw [pow_succ]
    exact Nat.mul_le_mul (powSupport_le hZ k m hm) (hZ n hn)

theorem cardFactors_of_mem_powSupport {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) :
    ∀ k, ∀ q ∈ powSupport B k, ArithmeticFunction.cardFactors q = k
  | 0, q, hq => by
    simp [powSupport] at hq
    rw [hq, ArithmeticFunction.cardFactors_one]
  | k + 1, q, hq => by
    obtain ⟨m, hm, n, hn, rfl⟩ := mem_powSupport_succ.mp hq
    rw [ArithmeticFunction.cardFactors_mul (powSupport_ne_zero (fun p hp => (hB p hp).ne_zero) k m hm)
      (hB n hn).ne_zero, cardFactors_of_mem_powSupport hB k m hm,
      ArithmeticFunction.cardFactors_apply_prime (hB n hn)]

/-- **`B^k` is a tail polynomial.** -/
theorem headPoly_pow {B : Finset ℕ} (b : ℕ → ℂ) (hB : ∀ n ∈ B, n ≠ 0) (t : ℝ) :
    ∀ k, headPoly B b t ^ k = headPoly (powSupport B k) (powCoeff B b k) t
  | 0 => by simp [headPoly, powSupport, powCoeff]
  | k + 1 => by
    rw [pow_succ, headPoly_pow b hB t k, headPoly_mul_headPoly _ b (powSupport_ne_zero hB k) hB]
    rfl

/-- The squared norm of the coefficients of `B^k`. -/
def powNorm (B : Finset ℕ) (b : ℕ → ℂ) (k : ℕ) : ℝ := ∑ q ∈ powSupport B k, ‖powCoeff B b k q‖ ^ 2

/-- A fiber of `(m, p) ↦ mp` over a product of `k + 1` tail primes has at most `k + 1` points. -/
theorem card_fiber_le {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) (k : ℕ) {q : ℕ}
    (hq : q ∈ powSupport B (k + 1)) :
    ((powSupport B k ×ˢ B).filter (fun x => x.1 * x.2 = q)).card ≤ k + 1 := by
  have hq0 : q ≠ 0 := powSupport_ne_zero (fun p hp => (hB p hp).ne_zero) (k + 1) q hq
  have hmaps : ∀ x ∈ (powSupport B k ×ˢ B).filter (fun x => x.1 * x.2 = q), x.2 ∈ q.primeFactors := by
    intro x hx
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    rw [Nat.mem_primeFactors]
    exact ⟨hB x.2 (Finset.mem_product.mp hx1).2, ⟨x.1, by rw [← hx2]; ring⟩, hq0⟩
  have hinj : Set.InjOn (fun x : ℕ × ℕ => x.2) ((powSupport B k ×ˢ B).filter (fun x => x.1 * x.2 = q)) := by
    intro x hx x' hx' h
    obtain ⟨hx1, hx2⟩ := Finset.mem_filter.mp hx
    obtain ⟨hx1', hx2'⟩ := Finset.mem_filter.mp hx'
    simp only at h
    have hp0 : x.2 ≠ 0 := (hB x.2 (Finset.mem_product.mp hx1).2).ne_zero
    have : x.1 = x'.1 := by
      rw [← h] at hx2'
      exact Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hp0) (hx2.trans hx2'.symm)
    exact Prod.ext this h
  have h1 := Finset.card_le_card_of_injOn _ hmaps hinj
  have h2 : q.primeFactors.card ≤ ArithmeticFunction.cardFactors q := by
    rw [ArithmeticFunction.cardFactors_apply, ← Nat.toFinset_factors]
    exact List.toFinset_card_le _
  rw [cardFactors_of_mem_powSupport hB (k + 1) q hq] at h2
  omega

/-- **The Steinhaus bound.** `‖B^k‖² ≤ k! ‖b‖^{2k}` for a prime-supported tail. -/
theorem powNorm_le {B : Finset ℕ} (hB : ∀ p ∈ B, p.Prime) (b : ℕ → ℂ) :
    ∀ k, powNorm B b k ≤ k.factorial * (∑ p ∈ B, ‖b p‖ ^ 2) ^ k
  | 0 => by simp [powNorm, powSupport, powCoeff]
  | k + 1 => by
    have ih := powNorm_le hB b k
    set F : ℕ → Finset (ℕ × ℕ) := fun q => (powSupport B k ×ˢ B).filter (fun x => x.1 * x.2 = q) with hF
    have hterm : ∀ q ∈ powSupport B (k + 1), ‖powCoeff B b (k + 1) q‖ ^ 2 ≤
        (k + 1) * ∑ x ∈ F q, ‖powCoeff B b k x.1‖ ^ 2 * ‖b x.2‖ ^ 2 := by
      intro q hq
      have hcs := sq_sum_le_card_mul_sum_sq (s := F q) (f := fun x => ‖powCoeff B b k x.1 * b x.2‖)
      have hnorm : ‖powCoeff B b (k + 1) q‖ ≤ ∑ x ∈ F q, ‖powCoeff B b k x.1 * b x.2‖ := norm_sum_le _ _
      have hcard : ((F q).card : ℝ) ≤ k + 1 := by exact_mod_cast card_fiber_le hB k hq
      have h0 : 0 ≤ ∑ x ∈ F q, ‖powCoeff B b k x.1 * b x.2‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
      calc ‖powCoeff B b (k + 1) q‖ ^ 2 ≤ (∑ x ∈ F q, ‖powCoeff B b k x.1 * b x.2‖) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hnorm 2
        _ ≤ (F q).card * ∑ x ∈ F q, ‖powCoeff B b k x.1 * b x.2‖ ^ 2 := hcs
        _ ≤ (k + 1) * ∑ x ∈ F q, ‖powCoeff B b k x.1 * b x.2‖ ^ 2 := mul_le_mul_of_nonneg_right hcard h0
        _ = (k + 1) * ∑ x ∈ F q, ‖powCoeff B b k x.1‖ ^ 2 * ‖b x.2‖ ^ 2 := by
            congr 1
            exact Finset.sum_congr rfl fun x _ => by rw [norm_mul, mul_pow]
    have hfib : ∑ q ∈ powSupport B (k + 1), ∑ x ∈ F q, ‖powCoeff B b k x.1‖ ^ 2 * ‖b x.2‖ ^ 2 =
        powNorm B b k * ∑ p ∈ B, ‖b p‖ ^ 2 := by
      rw [hF]
      have hmaps : ∀ x ∈ powSupport B k ×ˢ B, x.1 * x.2 ∈ powSupport B (k + 1) := fun x hx =>
        Finset.mem_image_of_mem _ hx
      rw [Finset.sum_fiberwise_of_maps_to (g := fun x : ℕ × ℕ => x.1 * x.2) hmaps, Finset.sum_product,
        powNorm, Finset.sum_mul_sum]
    have hb0 : 0 ≤ ∑ p ∈ B, ‖b p‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
    calc powNorm B b (k + 1) ≤ ∑ q ∈ powSupport B (k + 1), (k + 1) *
          ∑ x ∈ F q, ‖powCoeff B b k x.1‖ ^ 2 * ‖b x.2‖ ^ 2 := Finset.sum_le_sum hterm
      _ = (k + 1) * (powNorm B b k * ∑ p ∈ B, ‖b p‖ ^ 2) := by rw [← Finset.mul_sum, hfib]
      _ ≤ (k + 1) * (k.factorial * (∑ p ∈ B, ‖b p‖ ^ 2) ^ k * ∑ p ∈ B, ‖b p‖ ^ 2) := by
          gcongr
      _ = ((k + 1).factorial : ℝ) * (∑ p ∈ B, ‖b p‖ ^ 2) ^ (k + 1) := by
          rw [Nat.factorial_succ]
          push_cast
          ring

theorem isRough_of_prime {y p : ℕ} (hp : p.Prime) (hyp : y ≤ p) : IsRough y p :=
  ⟨hp.ne_zero, fun q hq h => by
    rw [(Nat.prime_dvd_prime_iff_eq hq hp).mp h]
    exact hyp⟩

/-- **Gaussian conditional moments of the tail.** -/
theorem integral_head_mul_tail_pow_le {y : ℕ} {A B : Finset ℕ} (hA : ∀ m ∈ A, m ∈ Nat.smoothNumbers y)
    (hB : ∀ p ∈ B, p.Prime ∧ y ≤ p) (r b : ℕ → ℂ) (k : ℕ) {N Z : ℕ} (hZ : ∀ p ∈ B, p ≤ Z)
    (hN : ∀ m ∈ A, m * Z ^ k ≤ N) {T : ℝ} (hT : 0 ≤ T) :
    (∫ t in T..(2 * T), ‖headPoly A r t‖ ^ 2 * ‖headPoly B b t‖ ^ (2 * k)) ≤
      (T + 8 * N * (1 + Real.log N)) * (∑ m ∈ A, ‖r m‖ ^ 2) * (k.factorial * (∑ p ∈ B, ‖b p‖ ^ 2) ^ k) := by
  have hB0 : ∀ n ∈ B, n ≠ 0 := fun n hn => (hB n hn).1.ne_zero
  have hrough : ∀ q ∈ powSupport B k, IsRough y q :=
    powSupport_rough (fun p hp => isRough_of_prime (hB p hp).1 (hB p hp).2) k
  have hN' : ∀ m ∈ A, ∀ q ∈ powSupport B k, m * q ≤ N := fun m hm q hq =>
    (Nat.mul_le_mul_left m (powSupport_le hZ k q hq)).trans (hN m hm)
  have h := integral_head_mul_tail hA hrough r (powCoeff B b k) hN' T
  have e : (fun t => ‖headPoly A r t‖ ^ 2 * ‖headPoly B b t‖ ^ (2 * k)) =
      fun t => ‖headPoly A r t‖ ^ 2 * ‖headPoly (powSupport B k) (powCoeff B b k) t‖ ^ 2 := by
    funext t
    rw [← headPoly_pow b hB0 t k, norm_pow, ← pow_mul, mul_comm k 2]
  rw [e]
  have hR : 0 ≤ ∑ m ∈ A, ‖r m‖ ^ 2 := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hS := powNorm_le (fun p hp => (hB p hp).1) b k
  have hS0 : 0 ≤ powNorm B b k := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hlog : 0 ≤ Real.log N := Real.log_natCast_nonneg N
  have hcoef : 0 ≤ T + 8 * N * (1 + Real.log N) := by positivity
  have hup := (abs_le.mp h).2
  unfold powNorm at hS hS0
  calc (∫ t in T..(2 * T), ‖headPoly A r t‖ ^ 2 * ‖headPoly (powSupport B k) (powCoeff B b k) t‖ ^ 2)
      ≤ (T + 8 * N * (1 + Real.log N)) * ((∑ m ∈ A, ‖r m‖ ^ 2) *
          ∑ q ∈ powSupport B k, ‖powCoeff B b k q‖ ^ 2) := by linarith
    _ ≤ (T + 8 * N * (1 + Real.log N)) * ((∑ m ∈ A, ‖r m‖ ^ 2) *
          (k.factorial * (∑ p ∈ B, ‖b p‖ ^ 2) ^ k)) := by gcongr
    _ = _ := by ring

theorem continuous_headPoly (A : Finset ℕ) (r : ℕ → ℂ) : Continuous (headPoly A r) := by
  unfold headPoly
  exact continuous_finsetSum _ fun m _ => continuous_const.mul (continuous_phase (Real.log m))

/-- **Conditional large deviations of the tail.** -/
theorem setIntegral_head_on_large_tail_le {y : ℕ} {A B : Finset ℕ} (hA : ∀ m ∈ A, m ∈ Nat.smoothNumbers y)
    (hB : ∀ p ∈ B, p.Prime ∧ y ≤ p) (r b : ℕ → ℂ) (k : ℕ) {N Z : ℕ} (hZ : ∀ p ∈ B, p ≤ Z)
    (hN : ∀ m ∈ A, m * Z ^ k ≤ N) {T V : ℝ} (hT : 0 ≤ T) (hV : 0 < V) :
    (∫ t in Set.Icc T (2 * T) ∩ {t | V ≤ ‖headPoly B b t‖}, ‖headPoly A r t‖ ^ 2) ≤
      (T + 8 * N * (1 + Real.log N)) * (∑ m ∈ A, ‖r m‖ ^ 2) *
        (k.factorial * ((∑ p ∈ B, ‖b p‖ ^ 2) / V ^ 2) ^ k) := by
  have hcR := continuous_headPoly A r
  have hcB := continuous_headPoly B b
  set g : ℝ → ℝ := fun t => ‖headPoly A r t‖ ^ 2 * (‖headPoly B b t‖ ^ (2 * k) / V ^ (2 * k)) with hg
  have hgc : Continuous g := (hcR.norm.pow 2).mul ((hcB.norm.pow _).div_const _)
  have hmeas : MeasurableSet (Set.Icc T (2 * T) ∩ {t | V ≤ ‖headPoly B b t‖}) :=
    measurableSet_Icc.inter (isClosed_le continuous_const hcB.norm).measurableSet
  have h1 : (∫ t in Set.Icc T (2 * T) ∩ {t | V ≤ ‖headPoly B b t‖}, ‖headPoly A r t‖ ^ 2) ≤
      ∫ t in Set.Icc T (2 * T) ∩ {t | V ≤ ‖headPoly B b t‖}, g t := by
    have hK : IsCompact (Set.Icc T (2 * T) ∩ {t | V ≤ ‖headPoly B b t‖}) :=
      isCompact_Icc.inter_right (isClosed_le continuous_const hcB.norm)
    refine setIntegral_mono_on ((hcR.norm.pow 2).continuousOn.integrableOn_compact hK)
      (hgc.continuousOn.integrableOn_compact hK) hmeas
      fun t ht => ?_
    have hVt : V ≤ ‖headPoly B b t‖ := ht.2
    have hratio : 1 ≤ ‖headPoly B b t‖ ^ (2 * k) / V ^ (2 * k) := by
      rw [le_div_iff₀ (by positivity), one_mul]
      exact pow_le_pow_left₀ hV.le hVt _
    simp only [hg]
    nlinarith [sq_nonneg ‖headPoly A r t‖]
  have h2 : (∫ t in Set.Icc T (2 * T) ∩ {t | V ≤ ‖headPoly B b t‖}, g t) ≤ ∫ t in Set.Icc T (2 * T), g t :=
    setIntegral_mono_set (hgc.integrableOn_Icc) (Filter.Eventually.of_forall fun t => by
      simp only [hg]; positivity) (Filter.Eventually.of_forall Set.inter_subset_left)
  have h3 : (∫ t in Set.Icc T (2 * T), g t) = (∫ t in T..(2 * T), ‖headPoly A r t‖ ^ 2 *
      ‖headPoly B b t‖ ^ (2 * k)) / V ^ (2 * k) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le (by linarith),
      ← intervalIntegral.integral_div]
    refine intervalIntegral.integral_congr fun t _ => ?_
    simp only [hg]
    ring
  have h4 := integral_head_mul_tail_pow_le hA hB r b k hZ hN hT
  have hV2 : 0 < V ^ (2 * k) := by positivity
  have h5 : (∫ t in T..(2 * T), ‖headPoly A r t‖ ^ 2 * ‖headPoly B b t‖ ^ (2 * k)) / V ^ (2 * k) ≤
      (T + 8 * N * (1 + Real.log N)) * (∑ m ∈ A, ‖r m‖ ^ 2) *
        (k.factorial * (∑ p ∈ B, ‖b p‖ ^ 2) ^ k) / V ^ (2 * k) := div_le_div_of_nonneg_right h4 hV2.le
  have e : (T + 8 * N * (1 + Real.log N)) * (∑ m ∈ A, ‖r m‖ ^ 2) *
      (k.factorial * (∑ p ∈ B, ‖b p‖ ^ 2) ^ k) / V ^ (2 * k) =
      (T + 8 * N * (1 + Real.log N)) * (∑ m ∈ A, ‖r m‖ ^ 2) *
        (k.factorial * ((∑ p ∈ B, ‖b p‖ ^ 2) / V ^ 2) ^ k) := by
    rw [div_pow, pow_mul]
    field_simp
  linarith

end

end GaloisForLFunctions.TailArithmeticOfThePrimeOrbit
