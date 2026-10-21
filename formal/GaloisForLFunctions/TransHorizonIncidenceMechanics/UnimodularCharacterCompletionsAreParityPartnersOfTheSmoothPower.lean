import GaloisForLFunctions.TransHorizonIncidenceMechanics.HorizonLawOfPositiveRows

/-!
# Unimodular completions of real characters are parity partners of the smooth power

A real non-principal character `χ` mod `q` vanishes at the primes dividing `q`. Its **unimodular
completion** `χ̂` is the completely multiplicative function with `χ̂(p) = χ(p)` for `p ∤ q` and
`χ̂(p) = 1` for `p | q`; for `χ₄` it is `(−1)^{Ω₃(n)}`, the parity of the prime factors `≡ 3 mod 4`.
Then `χ̂ = 1_{q-smooth} ⋆ χ`, and the `q`-smooth kernel is a finite Euler product
`∏_{p|q} (1 − p^{-s})^{-1}`, absolutely convergent on `Re s ≥ 1/2`: it lies in the critical Wiener
algebra, so **`χ̂(d)d^{-ε}` has bounded receiver at every damping `ε > 0`**.

`χ̂` is completely multiplicative of modulus one, so its Ramanujan coefficients are
`χ̂(e) e^{-1-ε} L(1+ε, χ̂)` and their amplitudes are those of the **smooth power** `κ d^{-ε}`, whose
receiver diverges for `ε ≤ 1/2`. With `L(1+ε, χ̂) = L(1+ε, χ) ∏_{p|q} (1 − p^{-1-ε})^{-1} ≠ 0` this gives
**an unconditional parity pair at every damping `0 < ε ≤ 1/2` whose bounded member takes only the
values `±1`** and whose positive member is the full-density power: the parity of the inert prime
factors is the whole difference.
-/

open Finset Filter Topology
open GaloisForLFunctions.BezoutValuationIncidence
open scoped BigOperators

namespace GaloisForLFunctions.TransHorizonIncidenceMechanics

noncomputable section
set_option autoImplicit false

/-! ### The smooth twin of a unimodular completely multiplicative sign -/

section SmoothTwin

variable {s : ℕ → ℝ}

/-- The smooth twin `κ d^{-ε}`, `κ = |L_s| / ζ(1+ε)`, of a sign `s`. -/
def smoothTwin (s : ℕ → ℝ) (ε : ℝ) (d : ℕ) : ℝ :=
  |∑' k : ℕ, dampedSignWeight s ε k / k| / (∑' k : ℕ, dampedSignWeight unitSign ε k / k) *
    dampedSignWeight unitSign ε d

theorem smoothTwin_nonneg {ε : ℝ} (hε : 0 < ε) (d : ℕ) : 0 ≤ smoothTwin s ε d := by
  unfold smoothTwin dampedSignWeight unitSign
  have := unitDampedMass_pos hε
  positivity

theorem hasSum_smoothTwin_div {ε : ℝ} (hε : 0 < ε) :
    HasSum (fun d : ℕ => smoothTwin s ε d / d) |∑' k : ℕ, dampedSignWeight s ε k / k| := by
  have hZ := (unitDampedMass_pos hε).ne'
  have h := (summable_unit_weight hε).hasSum.mul_left
    (|∑' k : ℕ, dampedSignWeight s ε k / k| / ∑' k : ℕ, dampedSignWeight unitSign ε k / k)
  rw [div_mul_cancel₀ _ hZ] at h
  exact h.congr_fun fun d => by simp only [smoothTwin, mul_div_assoc]

/-- **Equal amplitudes**: `|W_{twin}(e)| = |W_s(e)| = |L_s| e^{-1-ε}`. -/
theorem abs_weightRamanujanCoeff_smoothTwin (hs : ∀ a b, s (a * b) = s a * s b)
    (habs : ∀ n, n ≠ 0 → |s n| = 1) {ε : ℝ} (hε : 0 < ε) (e : ℕ) :
    |weightRamanujanCoeff (smoothTwin s ε) e| = |weightRamanujanCoeff (dampedSignWeight s ε) e| := by
  set L := ∑' k : ℕ, dampedSignWeight s ε k / k
  set Z := ∑' k : ℕ, dampedSignWeight unitSign ε k / k
  have hZ : Z ≠ 0 := (unitDampedMass_pos hε).ne'
  have hW : ∀ t : ℕ → ℝ, (∀ a b, t (a * b) = t a * t b) →
      weightRamanujanCoeff (dampedSignWeight t ε) e =
        dampedSignWeight t ε e / e * ∑' k : ℕ, dampedSignWeight t ε k / k := fun t ht => by
    unfold weightRamanujanCoeff
    simp_rw [dampedSignWeight_mul_div ht e]
    exact tsum_mul_left
  have htwin : weightRamanujanCoeff (smoothTwin s ε) e =
      |L| / Z * weightRamanujanCoeff (dampedSignWeight unitSign ε) e :=
    weightRamanujanCoeff_smul _ _ e
  rw [htwin, hW unitSign (fun _ _ => by simp [unitSign]), hW s hs]
  have hunit : |dampedSignWeight s ε e / e| = dampedSignWeight unitSign ε e / e := by
    rcases eq_or_ne e 0 with rfl | he
    · simp
    · rw [dampedSignWeight, dampedSignWeight, unitSign, abs_div, abs_mul, habs e he,
        abs_of_nonneg (Real.rpow_nonneg (Nat.cast_nonneg e) _), abs_of_nonneg (Nat.cast_nonneg e)]
  change |(|L| / Z) * (dampedSignWeight unitSign ε e / e * Z)| =
    |dampedSignWeight s ε e / e * L|
  have hu0 : 0 ≤ dampedSignWeight unitSign ε e / e := by
    unfold dampedSignWeight unitSign; positivity
  rw [abs_mul (dampedSignWeight s ε e / e), hunit,
    show |L| / Z * (dampedSignWeight unitSign ε e / e * Z) =
      dampedSignWeight unitSign ε e / e * |L| by field_simp,
    abs_mul, abs_of_nonneg hu0, abs_abs]

theorem smoothTwin_drift_ge {ε : ℝ} (hε : 0 < ε) {n : ℕ} (hn : 1 ≤ n) :
    (|∑' k : ℕ, dampedSignWeight s ε k / k| / (∑' k : ℕ, dampedSignWeight unitSign ε k / k)) / 2 *
      n * (2 * (n : ℝ)) ^ (-ε) ≤ (n : ℝ) * ∑ d ∈ Ioc n (2 * n), smoothTwin s ε d / d := by
  set κ := |∑' k : ℕ, dampedSignWeight s ε k / k| / (∑' k : ℕ, dampedSignWeight unitSign ε k / k)
  have hκ : 0 ≤ κ := div_nonneg (abs_nonneg _) (unitDampedMass_pos hε).le
  have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
  have h2n : (0 : ℝ) < 2 * n := by linarith
  have hterm : ∀ d ∈ Ioc n (2 * n), κ * (2 * (n : ℝ)) ^ (-ε) / (2 * n) ≤ smoothTwin s ε d / d := by
    intro d hd
    have hd := mem_Ioc.mp hd
    have hd0 : (0 : ℝ) < d := by
      have : 0 < d := lt_of_le_of_lt (Nat.zero_le _) hd.1
      exact_mod_cast this
    have hdle : (d : ℝ) ≤ 2 * n := by exact_mod_cast hd.2
    have htw : smoothTwin s ε d / d = κ * (d : ℝ) ^ (-(1 + ε)) := by
      rw [smoothTwin, mul_div_assoc, dampedSignWeight_div hε, unitSign, mul_one]
    rw [htw, mul_div_assoc]
    refine mul_le_mul_of_nonneg_left ?_ hκ
    rw [← Real.rpow_sub_one h2n.ne', show -ε - 1 = -(1 + ε) by ring]
    exact Real.rpow_le_rpow_of_nonpos hd0 hdle (by linarith)
  have hsum := sum_le_sum hterm
  rw [sum_const, Nat.card_Ioc, show 2 * n - n = n by omega, nsmul_eq_mul] at hsum
  have : (n : ℝ) * (κ * (2 * (n : ℝ)) ^ (-ε) / (2 * n)) = κ / 2 * (2 * (n : ℝ)) ^ (-ε) := by
    field_simp
  rw [this] at hsum
  calc κ / 2 * n * (2 * (n : ℝ)) ^ (-ε) = (n : ℝ) * (κ / 2 * (2 * (n : ℝ)) ^ (-ε)) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hsum hn0.le

/-- The smooth twin diverges at every `0 < ε ≤ 1/2` once `L_s ≠ 0`. -/
theorem tendsto_weightPronicEnergy_smoothTwin {ε : ℝ} (hε : 0 < ε) (hε2 : ε ≤ 1 / 2)
    (hL : ∑' k : ℕ, dampedSignWeight s ε k / k ≠ 0) :
    Tendsto (fun T => weightPronicEnergy (smoothTwin s ε) (∑' d : ℕ, smoothTwin s ε d / d) T)
      atTop atTop := by
  rw [(hasSum_smoothTwin_div hε).tsum_eq]
  exact tendsto_weightPronicEnergy_of_drift (smoothTwin_nonneg hε) (hasSum_smoothTwin_div hε)
    (by have := unitDampedMass_pos hε; have := abs_pos.mpr hL; positivity) hε2 1
    fun n hn => smoothTwin_drift_ge hε hn

end SmoothTwin

/-! ### The unimodular completion -/

section Completion

variable {q : ℕ} [NeZero q]

theorem charSign_eq_zero_iff (χ : MulChar (ZMod q) ℤ) (d : ℕ) :
    charSign χ d = 0 ↔ ¬ Nat.Coprime d q := by
  have h := charSign_sq_eq χ d
  rw [← ZMod.isUnit_iff_coprime]
  by_cases hu : IsUnit ((d : ℕ) : ZMod q)
  · rw [if_pos hu] at h
    constructor
    · intro h0; rw [h0] at h; norm_num at h
    · intro h'; exact absurd hu h'
  · rw [if_neg hu] at h
    exact ⟨fun _ => hu, fun _ => pow_eq_zero_iff two_ne_zero |>.mp h⟩

/-- The completed prime value: `χ(p)`, or `1` where `χ(p) = 0`. -/
def completedValue (χ : MulChar (ZMod q) ℤ) (p : ℕ) : ℝ :=
  if charSign χ p = 0 then 1 else charSign χ p

theorem abs_completedValue (χ : MulChar (ZMod q) ℤ) (p : ℕ) : |completedValue χ p| = 1 := by
  unfold completedValue
  split_ifs with h
  · simp
  · rcases charSign_trichotomy χ p with h0 | h1 | hm
    · exact absurd h0 h
    · simp [h1]
    · simp [hm]

/-- **The unimodular completion** `χ̂(n) = ∏_{p^k ∥ n} χ̂(p)^k`. -/
def charCompletion (χ : MulChar (ZMod q) ℤ) (n : ℕ) : ℝ :=
  if n = 0 then 0 else n.factorization.prod fun p k => completedValue χ p ^ k

omit [NeZero q] in
theorem charCompletion_mul (χ : MulChar (ZMod q) ℤ) (a b : ℕ) :
    charCompletion χ (a * b) = charCompletion χ a * charCompletion χ b := by
  rcases eq_or_ne a 0 with rfl | ha
  · simp [charCompletion]
  rcases eq_or_ne b 0 with rfl | hb
  · simp [charCompletion]
  simp only [charCompletion, if_neg ha, if_neg hb, if_neg (mul_ne_zero ha hb),
    Nat.factorization_mul ha hb]
  exact Finsupp.prod_add_index' (fun _ => pow_zero _) (fun _ _ _ => pow_add _ _ _)

theorem abs_charCompletion (χ : MulChar (ZMod q) ℤ) {n : ℕ} (hn : n ≠ 0) :
    |charCompletion χ n| = 1 := by
  simp only [charCompletion, if_neg hn, Finsupp.prod]
  rw [abs_prod]
  exact prod_eq_one fun p _ => by rw [abs_pow, abs_completedValue, one_pow]

omit [NeZero q] in
theorem charCompletion_prime_pow (χ : MulChar (ZMod q) ℤ) {p : ℕ} (hp : p.Prime) (k : ℕ) :
    charCompletion χ (p ^ k) = completedValue χ p ^ k := by
  rw [charCompletion, if_neg (pow_ne_zero k hp.ne_zero), hp.factorization_pow,
    Finsupp.prod_single_index (h := fun p k => completedValue χ p ^ k) (pow_zero _)]

/-- The completion as a multiplicative arithmetic function. -/
def charCompletionAF (χ : MulChar (ZMod q) ℤ) : ArithmeticFunction ℝ :=
  ⟨charCompletion χ, by simp [charCompletion]⟩

omit [NeZero q] in
theorem isMultiplicative_charCompletionAF (χ : MulChar (ZMod q) ℤ) :
    (charCompletionAF χ).IsMultiplicative :=
  ⟨by simp [charCompletionAF, charCompletion], fun {m n} _ => charCompletion_mul χ m n⟩

/-- The indicator of the `q`-smooth numbers. -/
def smoothPart (q : ℕ) : ArithmeticFunction ℝ :=
  ⟨fun n => if n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p ∣ q then 1 else 0, by simp⟩

omit [NeZero q] in
theorem smoothPart_nonneg (n : ℕ) : 0 ≤ smoothPart q n := by
  simp only [smoothPart, ArithmeticFunction.coe_mk]; split_ifs <;> norm_num

omit [NeZero q] in
theorem isMultiplicative_smoothPart : (smoothPart q).IsMultiplicative := by
  refine ⟨by simp [smoothPart], fun {m n} hmn => ?_⟩
  rcases eq_or_ne m 0 with rfl | hm
  · simp [smoothPart]
  rcases eq_or_ne n 0 with rfl | hn
  · simp [smoothPart]
  have hmn0 : m * n ≠ 0 := mul_ne_zero hm hn
  have key : (∀ p ∈ (m * n).primeFactors, p ∣ q) ↔
      (∀ p ∈ m.primeFactors, p ∣ q) ∧ (∀ p ∈ n.primeFactors, p ∣ q) := by
    rw [Nat.Coprime.primeFactors_mul hmn]
    constructor
    · intro h
      exact ⟨fun p hp => h p (mem_union_left _ hp), fun p hp => h p (mem_union_right _ hp)⟩
    · rintro ⟨h1, h2⟩ p hp
      rcases mem_union.mp hp with h | h
      exacts [h1 p h, h2 p h]
  show (if m * n ≠ 0 ∧ ∀ p ∈ (m * n).primeFactors, p ∣ q then (1 : ℝ) else 0) =
    (if m ≠ 0 ∧ ∀ p ∈ m.primeFactors, p ∣ q then (1 : ℝ) else 0) *
      (if n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p ∣ q then (1 : ℝ) else 0)
  by_cases h1 : ∀ p ∈ m.primeFactors, p ∣ q
  · by_cases h2 : ∀ p ∈ n.primeFactors, p ∣ q
    · rw [if_pos ⟨hmn0, key.mpr ⟨h1, h2⟩⟩, if_pos ⟨hm, h1⟩, if_pos ⟨hn, h2⟩, mul_one]
    · rw [if_neg (fun h => h2 (key.mp h.2).2), if_pos ⟨hm, h1⟩,
        if_neg (show ¬(n ≠ 0 ∧ ∀ p ∈ n.primeFactors, p ∣ q) from fun h => h2 h.2), mul_zero]
  · rw [if_neg (fun h => h1 (key.mp h.2).1),
      if_neg (show ¬(m ≠ 0 ∧ ∀ p ∈ m.primeFactors, p ∣ q) from fun h => h1 h.2), zero_mul]

omit [NeZero q] in
theorem smoothPart_prime_pow {p : ℕ} (hp : p.Prime) (k : ℕ) :
    smoothPart q (p ^ k) = if k = 0 ∨ p ∣ q then 1 else 0 := by
  rcases eq_or_ne k 0 with rfl | hk
  · simp [smoothPart]
  simp only [smoothPart, ArithmeticFunction.coe_mk, ne_eq, pow_eq_zero_iff hk, hp.ne_zero,
    not_false_eq_true, true_and, Nat.primeFactors_prime_pow hk hp, mem_singleton, forall_eq,
    hk, false_or]

/-- **`χ̂ = 1_{q-smooth} ⋆ χ`.** -/
theorem charCompletionAF_eq (χ : MulChar (ZMod q) ℤ) :
    charCompletionAF χ = smoothPart q * charAF χ := by
  refine (ArithmeticFunction.IsMultiplicative.eq_iff_eq_on_prime_powers _
    (isMultiplicative_charCompletionAF χ) _
    (isMultiplicative_smoothPart.mul ?_)).mpr fun p i hp => ?_
  · refine ⟨by simp [charAF, charSign_one], fun {m n} _ => ?_⟩
    rcases eq_or_ne m 0 with rfl | hm
    · simp [charAF]
    rcases eq_or_ne n 0 with rfl | hn
    · simp [charAF]
    simp [charAF, hm, hn, charSign_mul]
  rw [show (charCompletionAF χ) (p ^ i) = charCompletion χ (p ^ i) from rfl,
    charCompletion_prime_pow χ hp, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => smoothPart q a * charAF χ b),
    Nat.divisors_prime_pow hp, sum_map]
  simp only [Function.Embedding.coeFn_mk]
  have hchar : ∀ j : ℕ, charAF χ (p ^ j) = charSign χ p ^ j := fun j => by
    simp only [charAF, ArithmeticFunction.coe_mk, pow_ne_zero j hp.ne_zero, if_false]
    simp [charSign, Nat.cast_pow, map_pow]
  by_cases hpq : p ∣ q
  · have h0 : charSign χ p = 0 := (charSign_eq_zero_iff χ p).mpr
      (fun hc => hp.one_lt.ne' (Nat.Coprime.eq_one_of_dvd hc hpq))
    rw [completedValue, if_pos h0, one_pow]
    rw [Finset.sum_eq_single i (fun j hj hji => by
        rw [Nat.pow_div (by have := mem_range.mp hj; omega) hp.pos, hchar, h0,
          zero_pow (by have := mem_range.mp hj; omega), mul_zero])
      (fun h => absurd (mem_range.mpr (Nat.lt_succ_self i)) h)]
    rw [Nat.pow_div le_rfl hp.pos, Nat.sub_self, pow_zero, smoothPart_prime_pow hp,
      if_pos (Or.inr hpq)]
    simp [charAF, charSign_one]
  · have hne : charSign χ p ≠ 0 := fun h0 =>
      (charSign_eq_zero_iff χ p).mp h0 ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpq)
    rw [completedValue, if_neg hne]
    rw [Finset.sum_eq_single 0 (fun j hj hj0 => by
        rw [smoothPart_prime_pow hp, if_neg (by tauto), zero_mul])
      (fun h => absurd (mem_range.mpr (Nat.succ_pos i)) h)]
    rw [smoothPart_prime_pow hp, if_pos (Or.inl rfl), pow_zero, Nat.div_one, hchar, one_mul]

/-- `χ̂ d^{-ε} = 1_{q-smooth} d^{-ε} ⋆ χ d^{-ε}`. -/
theorem dampedCharCompletion_eq_dirichletConv (χ : MulChar (ZMod q) ℤ) (ε : ℝ) (n : ℕ) :
    dampedSignWeight (charCompletion χ) ε n = RHTower.dirichletConv
      (dampedSignWeight ⇑(smoothPart q) ε) (dampedSignWeight (charSign χ) ε) n := by
  have h : charCompletion χ n = (smoothPart q * charAF χ) n :=
    congrArg (fun F : ArithmeticFunction ℝ => F n) (charCompletionAF_eq χ)
  rw [dampedSignWeight, h, ArithmeticFunction.mul_apply,
    Nat.sum_divisorsAntidiagonal (fun a b => smoothPart q a * charAF χ b), RHTower.dirichletConv,
    sum_mul]
  refine sum_congr rfl fun d hd => ?_
  obtain ⟨k, rfl⟩ := Nat.dvd_of_mem_divisors hd
  have hd0 : 0 < d := Nat.pos_of_mem_divisors hd
  have hk0 : k ≠ 0 := by rintro rfl; simp at hd
  rw [Nat.mul_div_cancel_left k hd0]
  simp only [charAF, ArithmeticFunction.coe_mk, if_neg hk0, dampedSignWeight, Nat.cast_mul,
    Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
  ring

/-- The `q`-smooth kernel is critical Wiener: a finite Euler product. -/
theorem criticalWiener_smoothPart {ε : ℝ} (hε : 0 < ε) :
    CriticalWiener (dampedSignWeight ⇑(smoothPart q) ε) := by
  set σ : ℝ := 1 / 2 + ε
  have hσ : 1 / 2 < σ := by simp only [σ]; linarith
  let M : ArithmeticFunction ℝ := ⟨fun n => smoothPart q n * (n : ℝ) ^ (-σ), by simp⟩
  have hM : M.IsMultiplicative := by
    refine ⟨by simp [M, isMultiplicative_smoothPart.map_one], fun {m n} hmn => ?_⟩
    simp only [M, ArithmeticFunction.coe_mk, isMultiplicative_smoothPart.map_mul_of_coprime hmn,
      Nat.cast_mul, Real.mul_rpow (Nat.cast_nonneg _) (Nat.cast_nonneg _)]
    ring
  have hM0 : ∀ n, 0 ≤ M n := fun n => by
    simp only [M, ArithmeticFunction.coe_mk]; exact mul_nonneg (smoothPart_nonneg n) (by positivity)
  have hloc : ∀ {p : ℕ}, p.Prime → Summable (fun k : ℕ => M (p ^ k)) ∧
      ∑' k : ℕ, M (p ^ k) ≤ Real.exp (if p ∣ q then 3 else 0) := by
    intro p hp
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    set x := (p : ℝ) ^ (-σ) with hxdef
    have hx : ∀ k : ℕ, ((p ^ k : ℕ) : ℝ) ^ (-σ) = x ^ k := fun k => by
      rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le, ← Real.rpow_natCast,
        ← Real.rpow_mul hp0.le, mul_comm]
    have hMk : ∀ k : ℕ, M (p ^ k) = (if k = 0 ∨ p ∣ q then 1 else 0) * x ^ k := fun k => by
      simp only [M, ArithmeticFunction.coe_mk, smoothPart_prime_pow hp, hx]
    have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
    have hx0 : 0 ≤ x := Real.rpow_nonneg hp0.le _
    have hxsq : x ^ 2 ≤ 1 / 2 := by
      have : x ^ 2 = (p : ℝ) ^ (-(2 * σ)) := by
        rw [hxdef, ← Real.rpow_natCast, ← Real.rpow_mul hp0.le]; congr 1; push_cast; ring
      rw [this]
      calc (p : ℝ) ^ (-(2 * σ)) ≤ (p : ℝ) ^ (-1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
        _ = 1 / p := by rw [Real.rpow_neg_one, one_div]
        _ ≤ 1 / 2 := by gcongr
    have hx34 : x ≤ 3 / 4 := by nlinarith
    have hxlt : x < 1 := by linarith
    by_cases hpq : p ∣ q
    · have hgeo := hasSum_geometric_of_lt_one hx0 hxlt
      have heq : (fun k : ℕ => M (p ^ k)) = fun k => x ^ k := funext fun k => by
        rw [hMk, if_pos (Or.inr hpq), one_mul]
      rw [heq, if_pos hpq]
      refine ⟨hgeo.summable, ?_⟩
      rw [hgeo.tsum_eq]
      have h1 : (1 - x)⁻¹ ≤ 4 := by
        rw [inv_le_comm₀ (by linarith) (by norm_num)]; linarith
      have h2 : (4 : ℝ) ≤ Real.exp 3 := by linarith [Real.add_one_le_exp (3 : ℝ)]
      linarith
    · have heq : (fun k : ℕ => M (p ^ k)) = fun k => if k = 0 then 1 else 0 := funext fun k => by
        rw [hMk]
        split_ifs with h1 h2 h2 <;> simp_all
      rw [heq, if_neg hpq, Real.exp_zero]
      refine ⟨summable_of_ne_finset_zero (s := {0}) fun k hk => by simp_all, ?_⟩
      rw [tsum_ite_eq]
  set b : ℕ → ℝ := fun n => if n.Prime then (if n ∣ q then 3 else 0) else 0
  have hb0 : ∀ n, 0 ≤ b n := fun n => by simp only [b]; split_ifs <;> norm_num
  have hb : Summable b := summable_of_ne_finset_zero (s := q.divisors) fun n hn => by
    have hnq : ¬ n ∣ q := fun h => hn (Nat.mem_divisors.mpr ⟨h, NeZero.ne q⟩)
    simp [b, hnq]
  have hsum := RHTower.pm_summable_of_multiplicative_local_bound M hM hM0
    (fun hp => (hloc hp).1) b hb0 hb (fun {p} hp => by simpa only [b, if_pos hp] using (hloc hp).2)
  unfold CriticalWiener
  refine hsum.congr fun n => ?_
  simp only [M, ArithmeticFunction.coe_mk, dampedSignWeight]
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · simp [Real.zero_rpow (show -σ ≠ 0 by linarith), Real.zero_rpow (show -ε ≠ 0 by linarith)]
  · have hn0 : (0 : ℝ) < n := by exact_mod_cast hn
    rw [abs_mul, abs_of_nonneg (smoothPart_nonneg n), abs_of_nonneg (Real.rpow_nonneg hn0.le _),
      mul_assoc, ← Real.rpow_add hn0]
    congr 2; simp only [σ]; ring

/-- **The completion has bounded receiver at every damping.** -/
theorem receiverBounded_charCompletion {χ : MulChar (ZMod q) ℤ} (hχ : χ ≠ 1) {ε : ℝ}
    (hε : 0 < ε) : ReceiverBounded (dampedSignWeight (charCompletion χ) ε) := by
  rw [show dampedSignWeight (charCompletion χ) ε = RHTower.dirichletConv
      (dampedSignWeight ⇑(smoothPart q) ε) (dampedSignWeight (charSign χ) ε) from
    funext (dampedCharCompletion_eq_dirichletConv χ ε)]
  exact receiverBounded_dirichletConv (criticalWiener_smoothPart hε)
    (summable_abs_dampedSign_div_of_abs_le (abs_charSign_le χ) hε)
    (exists_weightPronicEnergy_dampedSign_le (Nat.cast_nonneg q) hε (abs_sum_range_charSign_le hχ))

/-- `L(1+ε, χ̂) = L(1+ε, χ) ∏_{p|q}(1 − p^{-1-ε})^{-1} ≠ 0`. -/
theorem charCompletionMass_ne_zero {χ : MulChar (ZMod q) ℤ} {ε : ℝ} (hε : 0 < ε) :
    ∑' d : ℕ, dampedSignWeight (charCompletion χ) ε d / d ≠ 0 := by
  have hW := criticalWiener_smoothPart (q := q) hε
  have hg := hW.summable_abs_div
  have hc := summable_abs_dampedSign_div_of_abs_le (abs_charSign_le χ) hε
  have hmean := hasSum_dirichletConv_div hg.of_abs.hasSum hc.of_abs.hasSum hg hc
  rw [show dampedSignWeight (charCompletion χ) ε = RHTower.dirichletConv
      (dampedSignWeight ⇑(smoothPart q) ε) (dampedSignWeight (charSign χ) ε) from
    funext (dampedCharCompletion_eq_dirichletConv χ ε), hmean.tsum_eq]
  have hg1 : 1 ≤ ∑' n : ℕ, dampedSignWeight ⇑(smoothPart q) ε n / n := by
    have h1 : dampedSignWeight ⇑(smoothPart q) ε 1 / ((1 : ℕ) : ℝ) = 1 := by
      simp [dampedSignWeight, isMultiplicative_smoothPart.map_one]
    rw [← h1]
    exact hg.of_abs.le_tsum 1 fun n _ => by
      rw [dampedSignWeight]
      exact div_nonneg (mul_nonneg (smoothPart_nonneg n) (by positivity)) (Nat.cast_nonneg n)
  exact mul_ne_zero (by linarith) (charDampedMass_ne_zero hε)

/-- **Unimodular completions of real characters are parity partners of the smooth power.** For every
real non-principal `χ` and every `0 < ε ≤ 1/2`: `χ̂(d)d^{-ε}` (values `±1·d^{-ε}`) and the smooth power
`κ d^{-ε}` have equal Ramanujan amplitudes; the first has bounded receiver, the second divergent. -/
theorem charCompletion_parityPair {χ : MulChar (ZMod q) ℤ} (hχ : χ ≠ 1) {ε : ℝ} (hε : 0 < ε)
    (hε2 : ε ≤ 1 / 2) :
    (∀ n : ℕ, n ≠ 0 → |charCompletion χ n| = 1) ∧
    (∀ e : ℕ, |weightRamanujanCoeff (smoothTwin (charCompletion χ) ε) e| =
        |weightRamanujanCoeff (dampedSignWeight (charCompletion χ) ε) e|) ∧
    (∀ d : ℕ, 0 ≤ smoothTwin (charCompletion χ) ε d) ∧
    ReceiverBounded (dampedSignWeight (charCompletion χ) ε) ∧
    Tendsto (fun T => weightPronicEnergy (smoothTwin (charCompletion χ) ε)
      (∑' d : ℕ, smoothTwin (charCompletion χ) ε d / d) T) atTop atTop :=
  ⟨fun _ hn => abs_charCompletion χ hn,
    abs_weightRamanujanCoeff_smoothTwin (charCompletion_mul χ) (fun _ hn => abs_charCompletion χ hn) hε,
    smoothTwin_nonneg hε, receiverBounded_charCompletion hχ hε,
    tendsto_weightPronicEnergy_smoothTwin hε hε2 (charCompletionMass_ne_zero hε)⟩

end Completion

end

end GaloisForLFunctions.TransHorizonIncidenceMechanics
