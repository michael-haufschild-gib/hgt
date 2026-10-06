import GaloisForLFunctions.RHTower.Sieve.TwistedSelbergFactorization

/-!
# Mass of the factors of the twisted Selberg coefficient

* `R_q(n) = 1/n` on `q`-smooth `n`: `Σ_n R_q(n) = Π_{p | q} (1 − 1/p)^{−1} ≤ 2^{ω(q)}`
  (`hasSum_smoothRecip`, `tsum_smoothRecip_le`), by the Euler product over `q`-smooth numbers.
* The summable factor `E_{ab} ⋆ R_{b,a}` is absolutely summable with mass at most
  `‖E‖₁ 2^{ω(a)} 2^{ω(b)}` (`sum_abs_twistSummable_le`), since `|E_{ab} ⋆ R| ≤ |E| ⋆ R`.
* The finite factor `Δ_{ab} ⋆ μ_{b,a}` vanishes off `[1, (ab)²]²`, has absolute mass at most
  `d(ab) d(a) d(b)`, and total mass `0` when `ab > 1` (`sum_twistFinite_eq_zero`):
  the total is `Σ_{d | ab} μ(d)/d · Σ_{m | b} μ(m) · Σ_{n | a} μ(n)`.
-/

open ArithmeticFunction Finset Filter Topology
open scoped BigOperators ArithmeticFunction.Moebius

namespace RHTower.Sieve

noncomputable section

/-! ## Smooth reciprocals -/

theorem smoothRecip_eq_indicator (q : ℕ) :
    smoothRecip q = (Nat.factoredNumbers q.primeFactors).indicator (fun n : ℕ => (1 : ℝ) / n) := by
  funext n
  unfold smoothRecip
  simp only [Set.indicator, Nat.mem_factoredNumbers]
  congr 1
  apply propext
  constructor
  · rintro ⟨hn, hs⟩
    exact ⟨hn, fun p hp => hs (List.mem_toFinset.mpr hp)⟩
  · rintro ⟨hn, hs⟩
    exact ⟨hn, fun p hp => hs p (List.mem_toFinset.mp hp)⟩

theorem hasSum_smoothRecip (q : ℕ) :
    HasSum (smoothRecip q) (∏ p ∈ q.primeFactors, (1 - 1 / (p : ℝ))⁻¹) := by
  have hE := (EulerProduct.summable_and_hasSum_factoredNumbers_prod_filter_prime_tsum
    (R := ℝ) (f := fun n : ℕ => (1 : ℝ) / n) (by simp)
    (fun {m n} _ => by push_cast; rw [one_div_mul_one_div])
    (fun {p} hp => by
      have hp1 : (1 / (p : ℝ)) < 1 := by
        rw [div_lt_one (by exact_mod_cast hp.pos)]; exact_mod_cast hp.one_lt
      refine (summable_geometric_of_lt_one (by positivity) hp1).congr fun n => ?_
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      push_cast; rw [one_div_pow])
    q.primeFactors).2
  have hfilter : q.primeFactors.filter Nat.Prime = q.primeFactors :=
    Finset.filter_true_of_mem fun p hp => Nat.prime_of_mem_primeFactors hp
  rw [hfilter] at hE
  have hloc : ∀ p ∈ q.primeFactors, (∑' n : ℕ, (1 : ℝ) / ((p ^ n : ℕ) : ℝ)) = (1 - 1 / (p : ℝ))⁻¹ := by
    intro p hp
    have hpp := Nat.prime_of_mem_primeFactors hp
    have hp1 : (1 / (p : ℝ)) < 1 := by
      rw [div_lt_one (by exact_mod_cast hpp.pos)]; exact_mod_cast hpp.one_lt
    rw [← tsum_geometric_of_lt_one (by positivity) hp1]
    congr 1; funext n; push_cast; rw [one_div_pow]
  rw [Finset.prod_congr rfl hloc] at hE
  rw [smoothRecip_eq_indicator]
  exact (hasSum_subtype_iff_indicator).mp hE

theorem smoothRecip_nonneg (q n : ℕ) : 0 ≤ smoothRecip q n := by
  unfold smoothRecip; split_ifs <;> positivity

theorem summable_smoothRecip (q : ℕ) : Summable (smoothRecip q) := (hasSum_smoothRecip q).summable

theorem tsum_smoothRecip_le (q : ℕ) : ∑' n, smoothRecip q n ≤ 2 ^ q.primeFactors.card := by
  rw [(hasSum_smoothRecip q).tsum_eq, ← Finset.prod_const]
  refine Finset.prod_le_prod (fun p hp => ?_) fun p hp => ?_
  · have hpp := Nat.prime_of_mem_primeFactors hp
    have hp1 : (1 / (p : ℝ)) < 1 := by
      rw [div_lt_one (by exact_mod_cast hpp.pos)]; exact_mod_cast hpp.one_lt
    exact (inv_pos.mpr (by linarith)).le
  · have hpp := Nat.prime_of_mem_primeFactors hp
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hpp.two_le
    have hhalf : 1 / (p : ℝ) ≤ 1 / 2 := by gcongr
    have hpos : 0 < 1 - 1 / (p : ℝ) := by linarith
    rw [inv_le_comm₀ hpos (by norm_num)]
    linarith

/-! ## Convolution bounds -/

theorem abs_bivariateDirichletConvolution_le (f g : ℕ → ℕ → ℝ) (m n : ℕ) :
    |bivariateDirichletConvolution f g m n| ≤
      bivariateDirichletConvolution (fun a b => |f a b|) (fun a b => |g a b|) m n := by
  unfold bivariateDirichletConvolution
  split_ifs
  · simp
  · refine (Finset.abs_sum_le_sum_abs _ _).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [abs_mul]

theorem bivariateDirichletConvolution_nonneg {f g : ℕ → ℕ → ℝ} (hf : ∀ a b, 0 ≤ f a b)
    (hg : ∀ a b, 0 ≤ g a b) (m n : ℕ) : 0 ≤ bivariateDirichletConvolution f g m n := by
  unfold bivariateDirichletConvolution
  split_ifs
  · exact le_rfl
  · exact Finset.sum_nonneg fun x _ => mul_nonneg (hf _ _) (hg _ _)

/-- Finite sums of a nonnegative convolution are bounded by the product of the masses. -/
theorem sum_Icc_bivariateDirichletConvolution_le {f g : ℕ → ℕ → ℝ} (hf : ∀ a b, 0 ≤ f a b)
    {A B : ℝ}
    (hA : ∀ X Y : ℕ, ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 Y, f a b ≤ A)
    (hB : ∀ X Y : ℕ, ∑ r ∈ Finset.Icc 1 X, ∑ s ∈ Finset.Icc 1 Y, g r s ≤ B) (hB0 : 0 ≤ B)
    (X Y : ℕ) :
    ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y, bivariateDirichletConvolution f g m n ≤ A * B := by
  have h := sum_Icc_bivariateDirichletConvolution_mul f g (fun _ _ => 1) X Y
  simp only [mul_one] at h
  rw [h]
  calc ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 Y,
        f a b * ∑ r ∈ Finset.Icc 1 (X / a), ∑ s ∈ Finset.Icc 1 (Y / b), g r s
      ≤ ∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 Y, f a b * B :=
        Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
          mul_le_mul_of_nonneg_left (hB _ _) (hf a b)
    _ = (∑ a ∈ Finset.Icc 1 X, ∑ b ∈ Finset.Icc 1 Y, f a b) * B := by
        rw [Finset.sum_mul]; refine Finset.sum_congr rfl fun a _ => ?_; rw [Finset.sum_mul]
    _ ≤ A * B := mul_le_mul_of_nonneg_right (hA X Y) hB0

/-! ## The summable factor -/

theorem twistSummable_zero_left (a b n : ℕ) : twistSummable a b 0 n = 0 := by
  simp [twistSummable, bivariateDirichletConvolution]

theorem twistSummable_zero_right (a b m : ℕ) : twistSummable a b m 0 = 0 := by
  simp [twistSummable, bivariateDirichletConvolution]

/-- The mass of `R_{b,a}` is at most `2^{ω(b)} 2^{ω(a)}`. -/
theorem sum_Icc_abs_smoothRecipPair_le (a b X Y : ℕ) :
    ∑ r ∈ Finset.Icc 1 X, ∑ s ∈ Finset.Icc 1 Y, |smoothRecipPair a b r s| ≤
      (2 : ℝ) ^ b.primeFactors.card * 2 ^ a.primeFactors.card := by
  calc ∑ r ∈ Finset.Icc 1 X, ∑ s ∈ Finset.Icc 1 Y, |smoothRecipPair a b r s|
      = (∑ r ∈ Finset.Icc 1 X, smoothRecip b r) * ∑ s ∈ Finset.Icc 1 Y, smoothRecip a s := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun s _ => ?_
        unfold smoothRecipPair
        rw [abs_of_nonneg (mul_nonneg (smoothRecip_nonneg _ _) (smoothRecip_nonneg _ _))]
    _ ≤ (2 : ℝ) ^ b.primeFactors.card * 2 ^ a.primeFactors.card := by
        refine mul_le_mul ?_ ?_ (Finset.sum_nonneg fun _ _ => smoothRecip_nonneg _ _)
          (by positivity)
        · exact ((summable_smoothRecip b).sum_le_tsum _ fun _ _ => smoothRecip_nonneg _ _).trans
            (tsum_smoothRecip_le b)
        · exact ((summable_smoothRecip a).sum_le_tsum _ fun _ _ => smoothRecip_nonneg _ _).trans
            (tsum_smoothRecip_le a)

/-- The mass bound `‖E‖₁ 2^{ω(a)} 2^{ω(b)}` for finite sums of `|E_{ab} ⋆ R_{b,a}|`. -/
theorem sum_Icc_abs_twistSummable_le (a b X Y : ℕ) :
    ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y, |twistSummable a b m n| ≤
      (∑' mn : ℕ × ℕ, |selbergEulerCorrectionCoeff mn.1 mn.2|) *
        ((2 : ℝ) ^ b.primeFactors.card * 2 ^ a.primeFactors.card) := by
  have hsumE := summable_abs_selbergEulerCorrectionCoeff
  refine (Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun n _ =>
    abs_bivariateDirichletConvolution_le _ _ m n).trans ?_
  refine sum_Icc_bivariateDirichletConvolution_le (fun _ _ => abs_nonneg _) (fun X Y => ?_)
    (sum_Icc_abs_smoothRecipPair_le a b) (by positivity) X Y
  calc ∑ a' ∈ Finset.Icc 1 X, ∑ b' ∈ Finset.Icc 1 Y, |corrCoprime (a * b) a' b'|
      ≤ ∑ x ∈ Finset.Icc 1 X ×ˢ Finset.Icc 1 Y, |selbergEulerCorrectionCoeff x.1 x.2| := by
        rw [Finset.sum_product]
        refine Finset.sum_le_sum fun a' _ => Finset.sum_le_sum fun b' _ => ?_
        unfold corrCoprime; split_ifs <;> simp
    _ ≤ ∑' mn : ℕ × ℕ, |selbergEulerCorrectionCoeff mn.1 mn.2| :=
        hsumE.sum_le_tsum _ fun _ _ => abs_nonneg _

/-- A function vanishing on the axes whose square box sums of `|G|` are bounded is absolutely
summable. -/
theorem summable_abs_of_sum_Icc_le {G : ℕ → ℕ → ℝ} {c : ℝ} (hG0 : ∀ n, G 0 n = 0)
    (hG0' : ∀ m, G m 0 = 0)
    (h : ∀ X : ℕ, ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 X, |G m n| ≤ c) :
    Summable (fun mn : ℕ × ℕ => |G mn.1 mn.2|) := by
  refine summable_of_sum_le (c := c) (fun _ => abs_nonneg _) fun u => ?_
  obtain ⟨X, hX⟩ : ∃ X : ℕ, ∀ x ∈ u, x.1 ≤ X ∧ x.2 ≤ X :=
    ⟨u.sup (fun x => max x.1 x.2), fun x hx =>
      ⟨(le_max_left _ _).trans (Finset.le_sup (f := fun x => max x.1 x.2) hx),
        (le_max_right _ _).trans (Finset.le_sup (f := fun x => max x.1 x.2) hx)⟩⟩
  calc ∑ x ∈ u, |G x.1 x.2|
      ≤ ∑ x ∈ Finset.Icc 0 X ×ˢ Finset.Icc 0 X, |G x.1 x.2| := by
        refine Finset.sum_le_sum_of_subset_of_nonneg (fun x hx => ?_) fun _ _ _ => abs_nonneg _
        rw [Finset.mem_product, Finset.mem_Icc, Finset.mem_Icc]
        exact ⟨⟨Nat.zero_le _, (hX x hx).1⟩, ⟨Nat.zero_le _, (hX x hx).2⟩⟩
    _ = ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 X, |G m n| := by
        rw [Finset.sum_product]
        have h0 : Finset.Icc 0 X = insert 0 (Finset.Icc 1 X) := by
          ext k; simp only [Finset.mem_insert, Finset.mem_Icc]; omega
        rw [h0, Finset.sum_insert (by simp)]
        simp only [hG0, abs_zero, Finset.sum_const_zero, zero_add]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [Finset.sum_insert (by simp), hG0', abs_zero, zero_add]
    _ ≤ c := h X

theorem summable_abs_twistSummable (a b : ℕ) :
    Summable (fun mn : ℕ × ℕ => |twistSummable a b mn.1 mn.2|) :=
  summable_abs_of_sum_Icc_le (twistSummable_zero_left a b) (twistSummable_zero_right a b)
    fun X => sum_Icc_abs_twistSummable_le a b X X

/-! ## The finite factor -/

theorem sum_Icc_moebiusDvd {q Y : ℕ} (hq : q ≠ 0) (hqY : q ≤ Y) :
    ∑ r ∈ Finset.Icc 1 Y, moebiusDvd q r = ∑ r ∈ q.divisors, ((μ r : ℤ) : ℝ) := by
  unfold moebiusDvd
  rw [← Finset.sum_filter]
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext r
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_divisors]
  constructor
  · rintro ⟨_, hr⟩; exact ⟨hr, hq⟩
  · rintro ⟨hr, _⟩
    exact ⟨⟨Nat.pos_of_dvd_of_pos hr (Nat.pos_of_ne_zero hq), (Nat.le_of_dvd
      (Nat.pos_of_ne_zero hq) hr).trans hqY⟩, hr⟩

theorem sum_divisors_moebius_real_eq_zero {q : ℕ} (hq : q ≠ 1) :
    ∑ r ∈ q.divisors, ((μ r : ℤ) : ℝ) = 0 := by
  have := congrArg (fun f : ArithmeticFunction ℤ => f q) ArithmeticFunction.moebius_mul_coe_zeta
  simp only [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply, if_neg hq] at this
  exact_mod_cast this

/-- **The finite factor has total mass zero when `ab > 1`.** -/
theorem sum_twistFinite_eq_zero {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (hab1 : a ≠ 1 ∨ b ≠ 1) {X : ℕ}
    (hX : a * b * (a * b) ≤ X) :
    ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 X, twistFinite a b m n = 0 := by
  have h := sum_Icc_bivariateDirichletConvolution_mul (diagMoebius (a * b)) (moebiusDvdPair a b)
    (fun _ _ => 1) X X
  simp only [mul_one] at h
  unfold twistFinite
  rw [h]
  refine Finset.sum_eq_zero fun d hd => Finset.sum_eq_zero fun e he => ?_
  unfold diagMoebius
  split_ifs with hde
  · obtain ⟨rfl, hdq⟩ := hde
    have hd0 : 0 < d := (Finset.mem_Icc.mp hd).1
    have hdle : d ≤ a * b := Nat.le_of_dvd (by positivity) hdq
    have hXd : a * b ≤ X / d := by
      rw [Nat.le_div_iff_mul_le hd0]
      calc a * b * d ≤ a * b * (a * b) := Nat.mul_le_mul_left _ hdle
        _ ≤ X := hX
    have hsplit : ∑ r ∈ Finset.Icc 1 (X / d), ∑ s ∈ Finset.Icc 1 (X / d), moebiusDvdPair a b r s =
        (∑ r ∈ Finset.Icc 1 (X / d), moebiusDvd b r) * ∑ s ∈ Finset.Icc 1 (X / d), moebiusDvd a s := by
      rw [Finset.sum_mul]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [Finset.mul_sum]; rfl
    rw [hsplit, sum_Icc_moebiusDvd hb ((Nat.le_mul_of_pos_left b (Nat.pos_of_ne_zero ha)).trans hXd),
      sum_Icc_moebiusDvd ha ((Nat.le_mul_of_pos_right a (Nat.pos_of_ne_zero hb)).trans hXd)]
    rcases hab1 with h1 | h1
    · rw [sum_divisors_moebius_real_eq_zero h1, mul_zero, mul_zero]
    · rw [sum_divisors_moebius_real_eq_zero h1, zero_mul, mul_zero]
  · rw [zero_mul]

/-- The finite factor vanishes outside `[1, (ab)²]²`. -/
theorem twistFinite_eq_zero_of_lt {a b m n : ℕ} (ha : a ≠ 0) (hb : b ≠ 0)
    (h : a * b * (a * b) < m ∨ a * b * (a * b) < n) : twistFinite a b m n = 0 := by
  unfold twistFinite bivariateDirichletConvolution
  split_ifs with h0
  · rfl
  refine Finset.sum_eq_zero fun xy _ => ?_
  obtain ⟨⟨x, hx⟩, ⟨y, hy⟩⟩ := xy
  simp only
  unfold diagMoebius moebiusDvdPair moebiusDvd
  split_ifs with h1 h2 h3 <;> try simp
  obtain ⟨rfl, hxq⟩ := h1
  have hxm := Nat.dvd_of_mem_divisors hx
  have hxn := Nat.dvd_of_mem_divisors hy
  have hm0 : m ≠ 0 := fun h => h0 (Or.inl h)
  have hn0 : n ≠ 0 := fun h => h0 (Or.inr h)
  have hxle : x ≤ a * b := Nat.le_of_dvd (by positivity) hxq
  have hmle : m ≤ a * b * (a * b) := by
    have : m = x * (m / x) := (Nat.mul_div_cancel' hxm).symm
    rw [this]
    exact Nat.mul_le_mul hxle ((Nat.le_of_dvd (Nat.pos_of_ne_zero hb) h2).trans
      (Nat.le_mul_of_pos_left b (Nat.pos_of_ne_zero ha)))
  have hnle : n ≤ a * b * (a * b) := by
    have : n = x * (n / x) := (Nat.mul_div_cancel' hxn).symm
    rw [this]
    exact Nat.mul_le_mul hxle ((Nat.le_of_dvd (Nat.pos_of_ne_zero ha) h3).trans
      (Nat.le_mul_of_pos_right a (Nat.pos_of_ne_zero hb)))
  omega

theorem sum_Icc_indicator_dvd_le {q : ℕ} (hq : q ≠ 0) (Z : ℕ) :
    (∑ r ∈ Finset.Icc 1 Z, if r ∣ q then (1 : ℝ) else 0) ≤ q.divisors.card := by
  rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  exact_mod_cast Finset.card_le_card fun d hd => by
    rw [Finset.mem_filter] at hd
    exact Nat.mem_divisors.mpr ⟨hd.2, hq⟩

/-- The absolute mass of `Δ_q` is at most `d(q)`. -/
theorem sum_Icc_abs_diagMoebius_le {q : ℕ} (hq : q ≠ 0) (X Y : ℕ) :
    ∑ d ∈ Finset.Icc 1 X, ∑ e ∈ Finset.Icc 1 Y, |diagMoebius q d e| ≤ (q.divisors.card : ℝ) := by
  have hpt : ∀ d e : ℕ, 1 ≤ d → |diagMoebius q d e| ≤
      if e = d then (if d ∣ q then (1 : ℝ) else 0) else 0 := by
    intro d e hd
    unfold diagMoebius
    by_cases h : d = e ∧ d ∣ q
    · rw [if_pos h, if_pos h.1.symm, if_pos h.2, abs_div, Nat.abs_cast]
      have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
      rw [div_le_one (by linarith)]
      linarith [abs_moebius_real_le_one d]
    · rw [if_neg h, abs_zero]
      split_ifs <;> norm_num
  calc ∑ d ∈ Finset.Icc 1 X, ∑ e ∈ Finset.Icc 1 Y, |diagMoebius q d e|
      ≤ ∑ d ∈ Finset.Icc 1 X, ∑ e ∈ Finset.Icc 1 Y,
          (if e = d then (if d ∣ q then (1 : ℝ) else 0) else 0) :=
        Finset.sum_le_sum fun d hd => Finset.sum_le_sum fun e _ =>
          hpt d e (Finset.mem_Icc.mp hd).1
    _ ≤ ∑ d ∈ Finset.Icc 1 X, if d ∣ q then (1 : ℝ) else 0 := by
        refine Finset.sum_le_sum fun d _ => ?_
        rw [Finset.sum_ite_eq']
        split_ifs <;> norm_num
    _ ≤ (q.divisors.card : ℝ) := sum_Icc_indicator_dvd_le hq X

/-- The absolute mass of `μ_{b,a}` is at most `d(b) d(a)`. -/
theorem sum_Icc_abs_moebiusDvdPair_le {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (X Y : ℕ) :
    ∑ r ∈ Finset.Icc 1 X, ∑ s ∈ Finset.Icc 1 Y, |moebiusDvdPair a b r s| ≤
      (b.divisors.card : ℝ) * a.divisors.card := by
  calc ∑ r ∈ Finset.Icc 1 X, ∑ s ∈ Finset.Icc 1 Y, |moebiusDvdPair a b r s|
      ≤ ∑ r ∈ Finset.Icc 1 X, ∑ s ∈ Finset.Icc 1 Y,
          (if r ∣ b then (1 : ℝ) else 0) * (if s ∣ a then (1 : ℝ) else 0) := by
        refine Finset.sum_le_sum fun r _ => Finset.sum_le_sum fun s _ => ?_
        unfold moebiusDvdPair moebiusDvd
        rw [abs_mul]
        refine mul_le_mul ?_ ?_ (abs_nonneg _) (by split_ifs <;> norm_num) <;>
        · split_ifs
          · exact abs_moebius_real_le_one _
          · simp
    _ = (∑ r ∈ Finset.Icc 1 X, if r ∣ b then (1 : ℝ) else 0) *
          ∑ s ∈ Finset.Icc 1 Y, if s ∣ a then (1 : ℝ) else 0 := by
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [Finset.mul_sum]
    _ ≤ (b.divisors.card : ℝ) * a.divisors.card :=
        mul_le_mul (sum_Icc_indicator_dvd_le hb X) (sum_Icc_indicator_dvd_le ha Y)
          (Finset.sum_nonneg fun _ _ => by split_ifs <;> norm_num) (by positivity)

/-- The absolute mass of the finite factor is at most `d(ab) d(b) d(a)`. -/
theorem sum_Icc_abs_twistFinite_le {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) (X Y : ℕ) :
    ∑ m ∈ Finset.Icc 1 X, ∑ n ∈ Finset.Icc 1 Y, |twistFinite a b m n| ≤
      ((a * b).divisors.card : ℝ) * ((b.divisors.card : ℝ) * a.divisors.card) := by
  refine (Finset.sum_le_sum fun m _ => Finset.sum_le_sum fun n _ =>
    abs_bivariateDirichletConvolution_le _ _ m n).trans ?_
  exact sum_Icc_bivariateDirichletConvolution_le (fun _ _ => abs_nonneg _)
    (sum_Icc_abs_diagMoebius_le (by positivity)) (sum_Icc_abs_moebiusDvdPair_le ha hb)
    (by positivity) X Y

end

end RHTower.Sieve
