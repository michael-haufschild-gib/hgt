import GaloisForLFunctions.AbsoluteGeometryOfSpecZ.LengtheningTheTreeOfTwoRaisesThePairingBelowTheSquareOfTwo

/-!
# At every prime a contact paid at its price is a monotone path

Change the contact at one integer `n₀ ≥ 2` by `t` and pay its price `2|t|/√n₀` in the
counterterm (the supremum of its symbol). The functional of this pair on a packet is

`Z(f) + (|t|/√n₀) ∫ (f(u + log n₀) − sgn(t) f(u))² du`   (`pairForm_contactAt_price`),

the sum over the zeros plus a square. So for every `n₀`, in particular for every odd prime:

* **The square of the integers is the least member** (`zeroSum_le_pairForm_contactAt_price`),
  and along each of the two rays `t = a t₁`, `a ≥ 0`, the functional increases
  (`priceBezoutAt_mono`).
* **The generator is bounded below by the mass** on packets of a given length `L`: a packet of
  length less than `m log n₀` is a sum of `m` differences of its translates, so
  `∫ f² ≤ m² ∫ (f(u + x) ∓ f(u))²` (`integral_sq_le_mul_integral_shift_sq`,
  `priceGenerator_ge_of_length`).
* **A base point and a threshold** (`exists_priceBezoutAt`, `exists_priceThreshold`). On the
  packets of length `L` the inequality holds without hypothesis for all large `a`, and exactly
  from a threshold on; for the square of the integers it is the statement that the threshold
  is `0`.
* **On all packets** the inequality along the whole path is the Riemann hypothesis
  (`combBezoutWith_contactAt_price_iff`).

The path of the length of a tree, where the counterterm follows the product formula, exists at
the prime `2` only (`exists_not_treeBezoutAt_of_three_le`); the path of the price exists at
every prime.
-/

open Finset Filter Topology MeasureTheory
open Zeta23
open scoped ArithmeticFunction.vonMangoldt

noncomputable section

namespace GaloisForLFunctions.AbsoluteGeometryOfSpecZ

variable {f : ℝ → ℝ} {n₀ : ℕ}

/-! ### Squares of differences of translates -/

/-- `∫ (f(u + x) − s f(u))² = 2(h(0) − s h(x))` for a sign `s`. -/
theorem integral_shift_sub_sq (hcont : Continuous f) (hfc : HasCompactSupport f) {s : ℝ}
    (hs : s * s = 1) (x : ℝ) :
    Integrable (fun u => (f (u + x) - s * f u) ^ 2) ∧
      ∫ u, (f (u + x) - s * f u) ^ 2 = 2 * (packetAutocorr f 0 - s * packetAutocorr f x) := by
  have I1 : Integrable fun u => f u * f u :=
    (hcont.mul hcont).integrable_of_hasCompactSupport hfc.mul_right
  have I2 : Integrable fun u => f (u + x) * f (u + x) := I1.comp_add_right x
  have I3 : Integrable fun u => f u * f (u + x) :=
    (hcont.mul (hcont.comp (continuous_id.add continuous_const))).integrable_of_hasCompactSupport
      hfc.mul_right
  have h2 : ∫ u, f (u + x) * f (u + x) = ∫ u, f u * f u :=
    integral_add_right_eq_self (fun u => f u * f u) x
  have e : (fun u => (f (u + x) - s * f u) ^ 2) =
      fun u => f (u + x) * f (u + x) - 2 * s * (f u * f (u + x)) + f u * f u := by
    funext u
    have : s ^ 2 = 1 := by rw [sq, hs]
    linear_combination (f u) ^ 2 * this
  have i3 : Integrable fun u => 2 * s * (f u * f (u + x)) := I3.const_mul _
  have i23 : Integrable fun u => f (u + x) * f (u + x) - 2 * s * (f u * f (u + x)) := I2.sub i3
  refine ⟨by rw [e]; exact i23.add I1, ?_⟩
  have h0 : packetAutocorr f 0 = ∫ u, f u * f u := by simp only [packetAutocorr, add_zero]
  rw [e, integral_add i23 I1, integral_sub I2 i3, integral_const_mul, h2, h0, packetAutocorr]
  ring

/-- A packet of length at most `m x` through `m` differences of its translates by `x`. -/
theorem sq_le_mul_sum_shift_sq {s x x₀ L : ℝ} (hs : s * s = 1)
    (hlen : ∀ u, u ≤ x₀ ∨ x₀ + L ≤ u → f u = 0) {m : ℕ} (hm : L ≤ m * x) (u : ℝ) :
    f u ^ 2 ≤ m * ∑ k ∈ range m, (f (u + k * x + x) - s * f (u + k * x)) ^ 2 := by
  have hnn : 0 ≤ (m : ℝ) * ∑ k ∈ range m, (f (u + k * x + x) - s * f (u + k * x)) ^ 2 :=
    mul_nonneg (Nat.cast_nonneg m) (Finset.sum_nonneg fun _ _ => sq_nonneg _)
  by_cases hu : u ≤ x₀
  · rw [hlen u (Or.inl hu)]
    simpa using hnn
  -- telescoping
  have htel : ∀ j : ℕ, f u = s ^ j * f (u + j * x) -
      ∑ k ∈ range j, s ^ (k + 1) * (f (u + k * x + x) - s * f (u + k * x)) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [Finset.sum_range_succ]
      have e : u + ((j + 1 : ℕ) : ℝ) * x = u + j * x + x := by
        push_cast
        ring
      rw [e]
      have hpow : s ^ (j + 1) * s = s ^ j := by
        rw [pow_succ, mul_assoc, hs, mul_one]
      linear_combination ih - f (u + ↑j * x) * hpow
  have hzero : f (u + m * x) = 0 := hlen _ (Or.inr (by linarith [not_le.mp hu]))
  have hf : f u = -∑ k ∈ range m, s ^ (k + 1) * (f (u + k * x + x) - s * f (u + k * x)) := by
    rw [htel m, hzero]
    ring
  have hsq : ∀ k : ℕ, (s ^ (k + 1)) ^ 2 = 1 := fun k => by
    rw [← pow_mul, mul_comm, pow_mul, sq, hs, one_pow]
  have hcs := sq_sum_le_card_mul_sum_sq (s := range m)
    (f := fun k => s ^ (k + 1) * (f (u + k * x + x) - s * f (u + k * x)))
  rw [Finset.card_range] at hcs
  rw [hf, neg_sq]
  refine hcs.trans (le_of_eq ?_)
  congr 1
  exact Finset.sum_congr rfl fun k _ => by rw [mul_pow, hsq, one_mul]

/-- **The differences of the translates bound the mass**: `∫ f² ≤ m² ∫ (f(u + x) − s f(u))²` for
a packet of length at most `m x`. -/
theorem integral_sq_le_mul_integral_shift_sq (hcont : Continuous f) (hfc : HasCompactSupport f)
    {s x x₀ L : ℝ} (hs : s * s = 1) (hlen : ∀ u, u ≤ x₀ ∨ x₀ + L ≤ u → f u = 0) {m : ℕ}
    (hm : L ≤ m * x) :
    ∫ u, f u ^ 2 ≤ (m : ℝ) ^ 2 * ∫ u, (f (u + x) - s * f u) ^ 2 := by
  obtain ⟨hI, -⟩ := integral_shift_sub_sq hcont hfc hs x
  have hI2 : Integrable fun u => f u ^ 2 := by
    refine ((hcont.mul hcont).integrable_of_hasCompactSupport hfc.mul_right).congr
      (Eventually.of_forall fun u => ?_)
    show f u * f u = f u ^ 2
    ring
  have hk : ∀ k : ℕ, Integrable fun u => (f (u + k * x + x) - s * f (u + k * x)) ^ 2 :=
    fun k => hI.comp_add_right (k * x)
  have hsum : Integrable fun u =>
      (m : ℝ) * ∑ k ∈ range m, (f (u + k * x + x) - s * f (u + k * x)) ^ 2 :=
    (integrable_finsetSum _ fun k _ => hk k).const_mul _
  have hmono := integral_mono hI2 hsum (sq_le_mul_sum_shift_sq hs hlen hm)
  have hshift : ∀ k : ℕ, ∫ u, (f (u + k * x + x) - s * f (u + k * x)) ^ 2 =
      ∫ u, (f (u + x) - s * f u) ^ 2 := fun k =>
    integral_add_right_eq_self (fun v => (f (v + x) - s * f v) ^ 2) (k * x)
  rw [integral_const_mul, integral_finsetSum _ fun k _ => hk k,
    Finset.sum_congr rfl fun k _ => hshift k, Finset.sum_const, Finset.card_range,
    nsmul_eq_mul] at hmono
  calc ∫ u, f u ^ 2 ≤ (m : ℝ) * ((m : ℝ) * ∫ u, (f (u + x) - s * f u) ^ 2) := hmono
    _ = (m : ℝ) ^ 2 * ∫ u, (f (u + x) - s * f u) ^ 2 := by ring

/-! ### The functional of a contact paid at its price -/

/-- The generator of the path of the price at `n₀` in the direction `t`:
`(2/√n₀)(|t| h(0) − t h(log n₀))`. -/
def priceGenerator (n₀ : ℕ) (t : ℝ) (f : ℝ → ℝ) : ℝ :=
  2 / Real.sqrt n₀ * (|t| * packetAutocorr f 0 - t * packetAutocorr f (Real.log n₀))

theorem priceGenerator_mul (n₀ : ℕ) {a : ℝ} (ha : 0 ≤ a) (t : ℝ) (f : ℝ → ℝ) :
    priceGenerator n₀ (a * t) f = a * priceGenerator n₀ t f := by
  rw [priceGenerator, priceGenerator, abs_mul, abs_of_nonneg ha]
  ring

/-- The generator is a square: `(|t|/√n₀) ∫ (f(u + log n₀) − sgn(t) f(u))²`. -/
theorem priceGenerator_eq (hcont : Continuous f) (hfc : HasCompactSupport f) (n₀ : ℕ) (t : ℝ) :
    ∃ s : ℝ, s * s = 1 ∧ priceGenerator n₀ t f =
      |t| / Real.sqrt n₀ * ∫ u, (f (u + Real.log n₀) - s * f u) ^ 2 := by
  rcases le_or_gt 0 t with ht | ht
  · refine ⟨1, by norm_num, ?_⟩
    rw [(integral_shift_sub_sq hcont hfc (s := 1) (by norm_num) _).2, priceGenerator,
      abs_of_nonneg ht]
    ring
  · refine ⟨-1, by norm_num, ?_⟩
    rw [(integral_shift_sub_sq hcont hfc (s := -1) (by norm_num) _).2, priceGenerator,
      abs_of_neg ht]
    ring

theorem priceGenerator_nonneg (hcont : Continuous f) (hfc : HasCompactSupport f) (n₀ : ℕ)
    (t : ℝ) : 0 ≤ priceGenerator n₀ t f := by
  obtain ⟨s, -, h⟩ := priceGenerator_eq hcont hfc n₀ t
  rw [h]
  exact mul_nonneg (div_nonneg (abs_nonneg _) (Real.sqrt_nonneg _))
    (integral_nonneg fun _ => sq_nonneg _)

/-- **The generator is at least a multiple of the mass** on packets of length at most
`m log n₀`. -/
theorem priceGenerator_ge_of_length (hcont : Continuous f) (hfc : HasCompactSupport f)
    (hn₀ : 2 ≤ n₀) (t : ℝ) {x₀ L : ℝ} (hlen : ∀ u, u ≤ x₀ ∨ x₀ + L ≤ u → f u = 0) {m : ℕ}
    (hm0 : 1 ≤ m) (hm : L ≤ m * Real.log n₀) :
    |t| / (Real.sqrt n₀ * (m : ℝ) ^ 2) * ∫ u, f u ^ 2 ≤ priceGenerator n₀ t f := by
  obtain ⟨s, hs, h⟩ := priceGenerator_eq hcont hfc n₀ t
  have hsq := integral_sq_le_mul_integral_shift_sq hcont hfc hs hlen hm
  have hs0 : 0 < Real.sqrt n₀ := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n₀))
  have hm' : (0 : ℝ) < (m : ℝ) ^ 2 := by
    have : (0 : ℝ) < m := by exact_mod_cast hm0
    positivity
  rw [h, div_mul_eq_mul_div, div_le_iff₀ (mul_pos hs0 hm')]
  have ht : 0 ≤ |t| := abs_nonneg t
  calc |t| * ∫ u, f u ^ 2 ≤ |t| * ((m : ℝ) ^ 2 * ∫ u, (f (u + Real.log n₀) - s * f u) ^ 2) :=
        mul_le_mul_of_nonneg_left hsq ht
    _ = |t| / Real.sqrt n₀ * (∫ u, (f (u + Real.log n₀) - s * f u) ^ 2) *
          (Real.sqrt n₀ * (m : ℝ) ^ 2) := by
        field_simp

/-- **The functional of a contact paid at its price** is the sum over the zeros plus the
generator. -/
theorem pairForm_contactAt_price (hn₀ : 2 ≤ n₀) (t : ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    pairForm (contactAt n₀ t) (2 * |t| / Real.sqrt n₀) f = zeroSum f + priceGenerator n₀ t f := by
  -- a bound for the contacts that the packet sees
  obtain ⟨A, hA⟩ := hfc.isCompact.isBounded.subset_closedBall 0
  have hsupp : ∀ u, f u ≠ 0 → |u| ≤ A := fun u hu => by
    have := hA (subset_tsupport _ hu)
    rwa [Metric.mem_closedBall, Real.dist_eq, sub_zero] at this
  have hauto : ∀ y : ℝ, 2 * |A| < y → packetAutocorr f y = 0 := fun y hy => by
    have h0 : ∀ u : ℝ, f u * f (u + y) = 0 := fun u => by
      by_contra hne
      have h1 := hsupp u (left_ne_zero_of_mul hne)
      have h2 := hsupp (u + y) (right_ne_zero_of_mul hne)
      have hA0 : A ≤ |A| := le_abs_self A
      linarith [(abs_le.mp h1).1, (abs_le.mp h2).2]
    simp [packetAutocorr, h0]
  set Q : ℕ := max n₀ ⌈Real.exp (2 * |A|)⌉₊ with hQdef
  have hQ : ∀ n : ℕ, Q < n → packetAutocorr f (Real.log n) = 0 := fun n hn => by
    refine hauto _ ?_
    have h1 : Real.exp (2 * |A|) < n := by
      have h2 : (⌈Real.exp (2 * |A|)⌉₊ : ℝ) < n := by
        exact_mod_cast lt_of_le_of_lt (le_max_right n₀ _) hn
      exact lt_of_le_of_lt (Nat.le_ceil _) h2
    rw [← Real.log_exp (2 * |A|)]
    exact Real.log_lt_log (Real.exp_pos _) h1
  have h1 := re_weilFullFunctional_packet_of_weight
    (fun n => (Λ n : ℝ) + contactAt n₀ t n) f hQ
  have h2 := re_weilFullFunctional_packet_of_weight (fun n => (Λ n : ℝ)) f hQ
  have hz := zeroSum_eq_weilFullFunctional hf hfc
  have hdev : ∑ k ∈ Icc 2 Q, contactAt n₀ t k / Real.sqrt k * packetAutocorr f (Real.log k) =
      t / Real.sqrt n₀ * packetAutocorr f (Real.log n₀) := by
    rw [Finset.sum_eq_single n₀]
    · rw [contactAt, if_pos rfl]
    · intro k _ hk
      rw [contactAt, if_neg hk, zero_div, zero_mul]
    · intro hnot
      exact absurd (Finset.mem_Icc.mpr ⟨hn₀, le_max_left n₀ _⟩) hnot
  have hsplit : ∑ k ∈ Icc 2 Q,
        ((Λ k : ℝ) + contactAt n₀ t k) / Real.sqrt k * packetAutocorr f (Real.log k) =
      ∑ k ∈ Icc 2 Q, (Λ k : ℝ) / Real.sqrt k * packetAutocorr f (Real.log k) +
        ∑ k ∈ Icc 2 Q, contactAt n₀ t k / Real.sqrt k * packetAutocorr f (Real.log k) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hmass : ∫ u, f u ^ 2 = packetAutocorr f 0 := by
    simp only [packetAutocorr, add_zero]
    exact integral_congr_ae (Eventually.of_forall fun u => sq (f u))
  unfold pairForm priceGenerator
  rw [h1, hsplit, hdev, hz, h2, hmass]
  ring

/-- **The square of the integers is the least member of the path.** -/
theorem zeroSum_le_pairForm_contactAt_price (hn₀ : 2 ≤ n₀) (t : ℝ) (hf : ContDiff ℝ 2 f)
    (hfc : HasCompactSupport f) :
    zeroSum f ≤ pairForm (contactAt n₀ t) (2 * |t| / Real.sqrt n₀) f := by
  rw [pairForm_contactAt_price hn₀ t hf hfc]
  linarith [priceGenerator_nonneg hf.continuous hfc n₀ t]

/-! ### Bézout at a length along the path -/

/-- Bézout on the packets of length `L` for the contact at `n₀` changed by `t` and paid at its
price. -/
def PriceBezoutAt (n₀ : ℕ) (t L : ℝ) : Prop :=
  ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
    (∃ x₀ : ℝ, ∀ u, u ≤ x₀ ∨ x₀ + L ≤ u → g u = 0) →
    0 ≤ pairForm (contactAt n₀ t) (2 * |t| / Real.sqrt n₀) g

/-- Along a ray the functional is affine. -/
theorem priceBezoutAt_iff (hn₀ : 2 ≤ n₀) {a : ℝ} (ha : 0 ≤ a) (t L : ℝ) :
    PriceBezoutAt n₀ (a * t) L ↔ ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      (∃ x₀ : ℝ, ∀ u, u ≤ x₀ ∨ x₀ + L ≤ u → g u = 0) →
      0 ≤ zeroSum g + a * priceGenerator n₀ t g := by
  refine forall₄_congr fun g hg hgc _ => ?_
  rw [pairForm_contactAt_price hn₀ (a * t) hg hgc, priceGenerator_mul n₀ ha]

/-- At the parameter `0` the path is the square of the integers. -/
theorem priceBezoutAt_zero_iff (hn₀ : 2 ≤ n₀) (L : ℝ) :
    PriceBezoutAt n₀ 0 L ↔ ∀ g : ℝ → ℝ, ContDiff ℝ 2 g → HasCompactSupport g →
      (∃ x₀ : ℝ, ∀ u, u ≤ x₀ ∨ x₀ + L ≤ u → g u = 0) → 0 ≤ zeroSum g := by
  have h := priceBezoutAt_iff hn₀ (le_refl (0 : ℝ)) 1 L
  rw [zero_mul] at h
  rw [h]
  exact forall₄_congr fun g _ _ _ => by rw [zero_mul, add_zero]

/-- **The path is monotone**: further along a ray the inequality persists. -/
theorem priceBezoutAt_mono (hn₀ : 2 ≤ n₀) {a a' : ℝ} (ha : 0 ≤ a) (haa : a ≤ a') (t L : ℝ)
    (h : PriceBezoutAt n₀ (a * t) L) : PriceBezoutAt n₀ (a' * t) L := by
  rw [priceBezoutAt_iff hn₀ (ha.trans haa)]
  intro g hg hgc hlen
  have h0 := (priceBezoutAt_iff hn₀ ha t L).mp h g hg hgc hlen
  have hE := priceGenerator_nonneg hg.continuous hgc n₀ t
  nlinarith [mul_le_mul_of_nonneg_right haa hE]

/-- **A base point without hypothesis.** On the packets of a length `L`, far enough along a ray
the inequality holds. -/
theorem exists_priceBezoutAt (hn₀ : 2 ≤ n₀) (L : ℝ) {t : ℝ} (ht : t ≠ 0) :
    ∃ a₀ : ℝ, 0 ≤ a₀ ∧ ∀ a, a₀ ≤ a → PriceBezoutAt n₀ (a * t) L := by
  obtain ⟨C, hC⟩ := exists_zeroSum_ge_of_length L
  have hlog : 0 < Real.log n₀ := Real.log_pos (by exact_mod_cast (by omega : 1 < n₀))
  obtain ⟨m, hm⟩ := exists_nat_ge (|L| / Real.log n₀ + 1)
  have hm1 : (1 : ℝ) ≤ m := le_trans (by linarith [div_nonneg (abs_nonneg L) hlog.le]) hm
  have hm0 : 1 ≤ m := by exact_mod_cast hm1
  have hmL : L ≤ m * Real.log n₀ := by
    have h1 : |L| / Real.log n₀ ≤ m := by linarith
    have h2 := (div_le_iff₀ hlog).mp h1
    linarith [le_abs_self L]
  have hs0 : 0 < Real.sqrt n₀ := Real.sqrt_pos.mpr (by exact_mod_cast (by omega : 0 < n₀))
  have hκ : 0 < |t| / (Real.sqrt n₀ * (m : ℝ) ^ 2) := by
    have : (0 : ℝ) < m := by linarith
    have ht' : 0 < |t| := abs_pos.mpr ht
    positivity
  refine ⟨|C| / (|t| / (Real.sqrt n₀ * (m : ℝ) ^ 2)), div_nonneg (abs_nonneg _) hκ.le,
    fun a ha => ?_⟩
  have ha0 : 0 ≤ a := (div_nonneg (abs_nonneg _) hκ.le).trans ha
  rw [priceBezoutAt_iff hn₀ ha0]
  intro g hg hgc hlen
  have hZ := hC g hg hgc hlen
  obtain ⟨x₀, hx₀⟩ := hlen
  have hE := priceGenerator_ge_of_length hg.continuous hgc hn₀ t hx₀ hm0 hmL
  have hM : 0 ≤ ∫ u, g u ^ 2 := integral_nonneg fun u => sq_nonneg _
  have h2 : |C| ≤ a * (|t| / (Real.sqrt n₀ * (m : ℝ) ^ 2)) := by rwa [div_le_iff₀ hκ] at ha
  have h3 : a * (|t| / (Real.sqrt n₀ * (m : ℝ) ^ 2) * ∫ u, g u ^ 2) ≤
      a * priceGenerator n₀ t g := mul_le_mul_of_nonneg_left hE ha0
  have h4 : |C| * ∫ u, g u ^ 2 ≤ a * (|t| / (Real.sqrt n₀ * (m : ℝ) ^ 2)) * ∫ u, g u ^ 2 :=
    mul_le_mul_of_nonneg_right h2 hM
  have h5 : C * ∫ u, g u ^ 2 ≤ |C| * ∫ u, g u ^ 2 :=
    mul_le_mul_of_nonneg_right (le_abs_self C) hM
  linarith

/-- **The threshold of the path.** On the packets of length `L`, along a ray the inequality
holds exactly from one parameter on. It is `0` iff the square of the integers satisfies Bézout
at the length `L`. -/
theorem exists_priceThreshold (hn₀ : 2 ≤ n₀) (L : ℝ) {t : ℝ} (ht : t ≠ 0) :
    ∃ as : ℝ, 0 ≤ as ∧ ∀ a, 0 ≤ a → (PriceBezoutAt n₀ (a * t) L ↔ as ≤ a) := by
  obtain ⟨a₀, ha₀, hbase⟩ := exists_priceBezoutAt hn₀ L ht
  set S : Set ℝ := {a : ℝ | 0 ≤ a ∧ PriceBezoutAt n₀ (a * t) L} with hS
  have hne : S.Nonempty := ⟨a₀, ha₀, hbase a₀ le_rfl⟩
  have hbdd : BddBelow S := ⟨0, fun a ha => ha.1⟩
  refine ⟨sInf S, le_csInf hne fun a ha => ha.1, fun a ha => ⟨fun h => csInf_le hbdd ⟨ha, h⟩,
    fun h => ?_⟩⟩
  rcases h.lt_or_eq with hlt | heq
  · obtain ⟨a', ha', hlt'⟩ := exists_lt_of_csInf_lt hne hlt
    exact priceBezoutAt_mono hn₀ ha'.1 hlt'.le t L ha'.2
  · -- the infimum is attained: the functional is affine along the ray
    rw [priceBezoutAt_iff hn₀ ha]
    intro g hg hgc hlen
    by_contra hcon
    have hneg := not_le.mp hcon
    have hE0 := priceGenerator_nonneg hg.continuous hgc n₀ t
    rcases hE0.lt_or_eq with hEpos | hEz
    · obtain ⟨a', ha', hlt'⟩ := exists_lt_of_csInf_lt hne
        (show sInf S < a + -(zeroSum g + a * priceGenerator n₀ t g) / priceGenerator n₀ t g by
          rw [heq]
          linarith [div_pos (neg_pos.mpr hneg) hEpos])
      have h0 := (priceBezoutAt_iff hn₀ ha'.1 t L).mp ha'.2 g hg hgc hlen
      have h2 : a' - a < -(zeroSum g + a * priceGenerator n₀ t g) / priceGenerator n₀ t g := by
        linarith
      have h3 := mul_lt_mul_of_pos_right h2 hEpos
      rw [div_mul_cancel₀ _ hEpos.ne'] at h3
      nlinarith
    · obtain ⟨a', ha'⟩ := hne
      have h0 := (priceBezoutAt_iff hn₀ ha'.1 t L).mp ha'.2 g hg hgc hlen
      rw [← hEz, mul_zero] at h0 hneg
      linarith

/-- **On all packets the inequality along the path is the Riemann hypothesis.** -/
theorem combBezoutWith_contactAt_price_iff (hn₀ : 2 ≤ n₀) (t : ℝ) :
    CombBezoutWith (contactAt n₀ t) (2 * |t| / Real.sqrt n₀) ↔ RiemannHypothesis := by
  rw [combBezoutWith_contactAt_iff hn₀]
  exact ⟨fun h => h.1, fun h => ⟨h, le_rfl⟩⟩

end GaloisForLFunctions.AbsoluteGeometryOfSpecZ
