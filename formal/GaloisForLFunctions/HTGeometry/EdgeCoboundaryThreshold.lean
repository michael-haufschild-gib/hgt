import Mathlib

/-!
# The edge coboundary norm of the prime torus has abscissa `3/4`

A mode of the prime torus `𝕋^∞` is a finitely supported integer vector `m = (m_p)` on the primes.
Its frequency is `m · ℓ = Σ_p m_p log p`, and the explicit-formula coefficient model assigns the
weight

`|ĝ(m)|² = ∏_{p ∈ supp m} (log p)² p^{−2σ|m_p|}`.

Writing `n₊ = ∏_{m_p > 0} p^{m_p}` and `n₋ = ∏_{m_p < 0} p^{−m_p}`, a mode is the same as a pair of
coprime positive integers, `m · ℓ = log n₊ − log n₋` and the weight is `(n₊ n₋)^{−2σ}` up to the
factor `∏ (log p)² = (n₊ n₋)^{o(1)}`.  The edge coboundary norm

`N_∞(σ) = Σ_{m ≠ 0} |ĝ(m)|² / (m · ℓ)²`

is finite exactly when `σ > 3/4`:

* the divisor is controlled by the elementary integer gap `|log(a/b)| ≥ |a − b|/max(a, b)`; balanced
  pairs `b < a < 2b` contribute `≪ a^{2 + 2ε − 4σ} (a − b)^{−2}` and unbalanced pairs are
  bounded by `(log 2)^{−2} (ab)^{ε − 2σ}`, both summable for `σ > 3/4`;
* the consecutive pairs `(M + 1, M)` alone contribute `≫ M^{2 − 4σ}`, which diverges for
  `σ ≤ 3/4`.
-/

noncomputable section

namespace GaloisForLFunctions.HTGeometry.EdgeCoboundary

open Finset Real

/-- An integer mode of the prime torus. -/
def IsPrimeMode (m : ℕ →₀ ℤ) : Prop := ∀ p ∈ m.support, p.Prime

/-- The frequency `m · ℓ = Σ_p m_p log p`. -/
def modeFreq (m : ℕ →₀ ℤ) : ℝ := m.sum fun p k => (k : ℝ) * Real.log p

/-- The explicit-formula weight `∏_{p ∈ supp m} (log p)² p^{−2σ|m_p|}`. -/
def modeWeight (σ : ℝ) (m : ℕ →₀ ℤ) : ℝ :=
  ∏ p ∈ m.support, Real.log p ^ 2 * (p : ℝ) ^ (-(2 * σ) * |(m p : ℝ)|)

/-- The terms `|ĝ(m)|² / (m · ℓ)²` of the edge coboundary norm. -/
def edgeTerm (σ : ℝ) (m : ℕ →₀ ℤ) : ℝ := modeWeight σ m / modeFreq m ^ 2

/-- The positive part `n₊ = ∏_{m_p > 0} p^{m_p}`. -/
def posPart (m : ℕ →₀ ℤ) : ℕ := (m.mapRange Int.toNat rfl).prod fun p k => p ^ k

/-- The negative part `n₋ = ∏_{m_p < 0} p^{−m_p}`. -/
def negPart (m : ℕ →₀ ℤ) : ℕ := ((-m).mapRange Int.toNat rfl).prod fun p k => p ^ k

theorem edgeTerm_nonneg (σ : ℝ) (m : ℕ →₀ ℤ) : 0 ≤ edgeTerm σ m := by
  unfold edgeTerm modeWeight
  refine div_nonneg (prod_nonneg fun p _ => mul_nonneg (sq_nonneg _) ?_) (sq_nonneg _)
  exact Real.rpow_nonneg (Nat.cast_nonneg p) _

/-! ## The dictionary between modes and pairs of integers -/

theorem posPart_eq (m : ℕ →₀ ℤ) : posPart m = ∏ p ∈ m.support, p ^ (m p).toNat := by
  unfold posPart
  rw [Finsupp.prod_mapRange_index (fun p => pow_zero p)]
  rfl

theorem negPart_eq (m : ℕ →₀ ℤ) : negPart m = ∏ p ∈ m.support, p ^ (-(m p)).toNat := by
  unfold negPart
  rw [Finsupp.prod_mapRange_index (fun p => pow_zero p)]
  unfold Finsupp.prod
  rw [Finsupp.support_neg]
  rfl

theorem posPart_pos {m : ℕ →₀ ℤ} (hm : IsPrimeMode m) : 0 < posPart m := by
  rw [posPart_eq]; exact prod_pos fun p hp => pow_pos (hm p hp).pos _

theorem negPart_pos {m : ℕ →₀ ℤ} (hm : IsPrimeMode m) : 0 < negPart m := by
  rw [negPart_eq]; exact prod_pos fun p hp => pow_pos (hm p hp).pos _

theorem factorization_posPart {m : ℕ →₀ ℤ} (hm : IsPrimeMode m) :
    (posPart m).factorization = m.mapRange Int.toNat rfl := by
  unfold posPart
  refine Nat.prod_pow_factorization_eq_self fun p hp => hm p ?_
  exact Finsupp.support_mapRange hp

theorem factorization_negPart {m : ℕ →₀ ℤ} (hm : IsPrimeMode m) :
    (negPart m).factorization = (-m).mapRange Int.toNat rfl := by
  unfold negPart
  refine Nat.prod_pow_factorization_eq_self fun p hp => hm p ?_
  have := Finsupp.support_mapRange hp
  rwa [Finsupp.support_neg] at this

/-- **The dictionary is injective.** -/
theorem eq_of_posPart_negPart {m m' : ℕ →₀ ℤ} (hm : IsPrimeMode m) (hm' : IsPrimeMode m')
    (hpos : posPart m = posPart m') (hneg : negPart m = negPart m') : m = m' := by
  have h1 := factorization_posPart hm
  have h2 := factorization_negPart hm
  rw [hpos, factorization_posPart hm'] at h1
  rw [hneg, factorization_negPart hm'] at h2
  ext p
  have e1 := congrArg (fun f => f p) h1
  have e2 := congrArg (fun f => f p) h2
  simp only [Finsupp.mapRange_apply, Finsupp.coe_neg, Pi.neg_apply] at e1 e2
  rw [← Int.toNat_sub_toNat_neg (m p), ← Int.toNat_sub_toNat_neg (m' p), e1, e2]

theorem posPart_ne_negPart {m : ℕ →₀ ℤ} (hm : IsPrimeMode m) (hm0 : m ≠ 0) :
    posPart m ≠ negPart m := by
  intro h
  apply hm0
  have h1 := factorization_posPart hm
  have h2 := factorization_negPart hm
  rw [h, h2] at h1
  ext p
  have e := congrArg (fun f => f p) h1
  simp only [Finsupp.mapRange_apply, Finsupp.coe_neg, Pi.neg_apply] at e
  rw [Finsupp.coe_zero, Pi.zero_apply, ← Int.toNat_sub_toNat_neg (m p), e, sub_self]

theorem log_posPart {m : ℕ →₀ ℤ} (hm : IsPrimeMode m) :
    Real.log (posPart m) = ∑ p ∈ m.support, ((m p).toNat : ℝ) * Real.log p := by
  rw [posPart_eq, Nat.cast_prod, Real.log_prod]
  · exact sum_congr rfl fun p _ => by rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    have : (p : ℝ) ≠ 0 := by exact_mod_cast (hm p hp).ne_zero
    push_cast; exact pow_ne_zero _ this

theorem log_negPart {m : ℕ →₀ ℤ} (hm : IsPrimeMode m) :
    Real.log (negPart m) = ∑ p ∈ m.support, ((-(m p)).toNat : ℝ) * Real.log p := by
  rw [negPart_eq, Nat.cast_prod, Real.log_prod]
  · exact sum_congr rfl fun p _ => by rw [Nat.cast_pow, Real.log_pow]
  · intro p hp
    have : (p : ℝ) ≠ 0 := by exact_mod_cast (hm p hp).ne_zero
    push_cast; exact pow_ne_zero _ this

/-- **The frequency of a mode is `log n₊ − log n₋`.** -/
theorem modeFreq_eq {m : ℕ →₀ ℤ} (hm : IsPrimeMode m) :
    modeFreq m = Real.log (posPart m) - Real.log (negPart m) := by
  rw [log_posPart hm, log_negPart hm, ← sum_sub_distrib]
  unfold modeFreq Finsupp.sum
  refine sum_congr rfl fun p _ => ?_
  have h' : ((m p : ℤ) : ℝ) = ((m p).toNat : ℝ) - ((-(m p)).toNat : ℝ) := by
    have h := Int.toNat_sub_toNat_neg (m p)
    have := congrArg (fun z : ℤ => (z : ℝ)) h
    push_cast at this
    linarith
  show ((m p : ℤ) : ℝ) * Real.log p = _
  rw [h']; ring

/-- `n₊ n₋ = ∏_{p ∈ supp m} p^{|m_p|}`. -/
theorem posPart_mul_negPart (m : ℕ →₀ ℤ) :
    posPart m * negPart m = ∏ p ∈ m.support, p ^ (m p).natAbs := by
  rw [posPart_eq, negPart_eq, ← prod_mul_distrib]
  exact prod_congr rfl fun p _ => by rw [← pow_add, Int.toNat_add_toNat_neg_eq_natAbs]

/-- `∏_{p ∈ supp m} p^{x|m_p|} = (n₊ n₋)^x`. -/
theorem prod_rpow_eq {m : ℕ →₀ ℤ} (x : ℝ) :
    ∏ p ∈ m.support, (p : ℝ) ^ (x * |(m p : ℝ)|) =
      (((posPart m * negPart m : ℕ) : ℝ)) ^ x := by
  rw [posPart_mul_negPart, Nat.cast_prod, ← Real.finsetProd_rpow _ _ (fun p _ => by positivity)]
  refine prod_congr rfl fun p _ => ?_
  rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg p)]
  congr 1
  rw [Nat.cast_natAbs, Int.cast_abs]
  ring

/-! ## The weight against a power of `n₊ n₋` -/

/-- `(log x)² ≤ x^ε` for large `x`. -/
theorem exists_log_sq_le_rpow {ε : ℝ} (hε : 0 < ε) :
    ∃ P₀ : ℕ, ∀ x : ℝ, (P₀ : ℝ) ≤ x → Real.log x ^ 2 ≤ x ^ ε := by
  set A : ℝ := 16 / ε ^ 2 with hA
  have hA0 : 0 < A := by positivity
  refine ⟨⌈A ^ (2 / ε)⌉₊ + 1, fun x hx => ?_⟩
  have hx1 : A ^ (2 / ε) ≤ x := by
    have := Nat.le_ceil (A ^ (2 / ε)); push_cast at hx; linarith
  have hx0 : 0 < x := lt_of_lt_of_le (by positivity) hx1
  have hxe : A ≤ x ^ (ε / 2) := by
    calc A = (A ^ (2 / ε)) ^ (ε / 2) := by
          rw [← Real.rpow_mul hA0.le]; field_simp; simp
      _ ≤ x ^ (ε / 2) := Real.rpow_le_rpow (by positivity) hx1 (by positivity)
  have hlog := Real.log_le_rpow_div hx0.le (show 0 < ε / 4 by positivity)
  have hx1' : (1 : ℝ) ≤ x := by
    have : (1 : ℝ) ≤ ⌈A ^ (2 / ε)⌉₊ + 1 := by
      have := Nat.cast_nonneg (α := ℝ) ⌈A ^ (2 / ε)⌉₊; linarith
    push_cast at hx; linarith
  have hl0 : 0 ≤ Real.log x := Real.log_nonneg hx1'
  have h4 : (x ^ (ε / 4) / (ε / 4)) ^ 2 = A * x ^ (ε / 2) := by
    rw [div_pow, ← Real.rpow_natCast, ← Real.rpow_mul hx0.le, hA]
    field_simp; ring_nf
  calc Real.log x ^ 2 ≤ (x ^ (ε / 4) / (ε / 4)) ^ 2 := pow_le_pow_left₀ hl0 hlog 2
    _ = A * x ^ (ε / 2) := h4
    _ ≤ x ^ (ε / 2) * x ^ (ε / 2) := mul_le_mul_of_nonneg_right hxe (by positivity)
    _ = x ^ ε := by rw [← Real.rpow_add hx0]; ring_nf

/-- **The weight is `(n₊ n₋)^{ε − 2σ}` up to a constant.** -/
theorem exists_modeWeight_le {ε : ℝ} (hε : 0 < ε) (σ : ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ m : ℕ →₀ ℤ, IsPrimeMode m →
      modeWeight σ m ≤ K * (((posPart m * negPart m : ℕ) : ℝ)) ^ (ε - 2 * σ) := by
  obtain ⟨P₀, hP₀⟩ := exists_log_sq_le_rpow hε
  set K₀ : ℝ := max 1 (Real.log P₀ ^ 2) with hK₀
  have hK₀1 : 1 ≤ K₀ := le_max_left _ _
  refine ⟨K₀ ^ P₀, by positivity, fun m hm => ?_⟩
  -- split each factor
  have hsplit : modeWeight σ m = (∏ p ∈ m.support, Real.log p ^ 2 * (p : ℝ) ^ (-ε * |(m p : ℝ)|)) *
      ∏ p ∈ m.support, (p : ℝ) ^ ((ε - 2 * σ) * |(m p : ℝ)|) := by
    unfold modeWeight
    rw [← prod_mul_distrib]
    refine prod_congr rfl fun p hp => ?_
    have hp0 : (0 : ℝ) < p := by exact_mod_cast (hm p hp).pos
    rw [mul_assoc, ← Real.rpow_add hp0]
    congr 2; ring
  rw [hsplit, prod_rpow_eq]
  refine mul_le_mul_of_nonneg_right ?_ (by positivity)
  have hfac : ∀ p ∈ m.support, Real.log p ^ 2 * (p : ℝ) ^ (-ε * |(m p : ℝ)|) ≤
      if p < P₀ then K₀ else 1 := by
    intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hm p hp).one_lt.le
    have hk : (1 : ℝ) ≤ |(m p : ℝ)| := by
      have : m p ≠ 0 := Finsupp.mem_support_iff.mp hp
      have : (1 : ℤ) ≤ |m p| := Int.one_le_abs this
      exact_mod_cast this
    have hpow : (p : ℝ) ^ (-ε * |(m p : ℝ)|) ≤ (p : ℝ) ^ (-ε) :=
      Real.rpow_le_rpow_of_exponent_le hp1 (by nlinarith)
    have hpow1 : (p : ℝ) ^ (-ε * |(m p : ℝ)|) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hp1 (by nlinarith)
    have hlog0 : 0 ≤ Real.log p ^ 2 := sq_nonneg _
    split_ifs with hlt
    · have hl : Real.log p ^ 2 ≤ Real.log P₀ ^ 2 := by
        have h0 : 0 ≤ Real.log p := Real.log_nonneg hp1
        exact pow_le_pow_left₀ h0 (Real.log_le_log (by linarith)
          (by exact_mod_cast hlt.le)) 2
      calc Real.log p ^ 2 * (p : ℝ) ^ (-ε * |(m p : ℝ)|) ≤ Real.log P₀ ^ 2 * 1 :=
            mul_le_mul hl hpow1 (by positivity) (sq_nonneg _)
        _ ≤ K₀ := by rw [mul_one]; exact le_max_right _ _
    · have hbig := hP₀ p (by exact_mod_cast not_lt.mp hlt)
      have hp0 : (0 : ℝ) < p := by linarith
      calc Real.log p ^ 2 * (p : ℝ) ^ (-ε * |(m p : ℝ)|) ≤ (p : ℝ) ^ ε * (p : ℝ) ^ (-ε) :=
            mul_le_mul hbig hpow (by positivity) (by positivity)
        _ = 1 := by rw [← Real.rpow_add hp0]; simp
  calc ∏ p ∈ m.support, Real.log p ^ 2 * (p : ℝ) ^ (-ε * |(m p : ℝ)|)
      ≤ ∏ p ∈ m.support, (if p < P₀ then K₀ else 1) :=
        prod_le_prod (fun p _ => mul_nonneg (sq_nonneg _) (by positivity)) hfac
    _ = K₀ ^ #(m.support.filter (· < P₀)) := by rw [prod_ite, prod_const_one, mul_one, prod_const]
    _ ≤ K₀ ^ P₀ := by
        refine pow_le_pow_right₀ hK₀1 ?_
        calc #(m.support.filter (· < P₀)) ≤ #(range P₀) := by
              refine card_le_card fun p hp => ?_
              exact mem_range.mpr (mem_filter.mp hp).2
          _ = P₀ := card_range P₀

/-! ## Summability over pairs of integers -/

/-- The balanced contribution `2^{−r} a^{2r+2} (a − b)^{−2}` of a pair `b < a`. -/
def balancedTerm (r : ℝ) (a b : ℕ) : ℝ :=
  if b < a then (2 : ℝ) ^ (-r) * (a : ℝ) ^ (2 * r + 2) * ((a - b : ℕ) : ℝ) ^ (-2 : ℝ) else 0

/-- The majorant of `(ab)^r / (log a − log b)²`. -/
def pairMajorant (r : ℝ) (a b : ℕ) : ℝ :=
  (Real.log 2)⁻¹ ^ 2 * ((a : ℝ) ^ r * (b : ℝ) ^ r) + balancedTerm r a b + balancedTerm r b a

theorem balancedTerm_nonneg (r : ℝ) (a b : ℕ) : 0 ≤ balancedTerm r a b := by
  unfold balancedTerm; split_ifs <;> positivity

theorem pairMajorant_nonneg (r : ℝ) (a b : ℕ) : 0 ≤ pairMajorant r a b := by
  unfold pairMajorant
  have := balancedTerm_nonneg r a b
  have := balancedTerm_nonneg r b a
  positivity

/-- The balanced bound for `b < a ≤ 2b`. -/
theorem div_log_sq_le_balancedTerm {r : ℝ} (hr : r ≤ 0) {a b : ℕ} (hb : 1 ≤ b) (hba : b < a)
    (ha2 : a ≤ 2 * b) :
    ((a * b : ℕ) : ℝ) ^ r / (Real.log a - Real.log b) ^ 2 ≤ balancedTerm r a b := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast (show 0 < a by omega)
  have hb0 : (0 : ℝ) < b := by exact_mod_cast (show 0 < b by omega)
  have hab : (b : ℝ) < a := by exact_mod_cast hba
  have hsub : ((a - b : ℕ) : ℝ) = (a : ℝ) - b := by rw [Nat.cast_sub hba.le]
  have hd0 : (0 : ℝ) < (a : ℝ) - b := by linarith
  -- the integer gap
  have hgap : ((a : ℝ) - b) / a ≤ Real.log a - Real.log b := by
    have h := Real.add_one_le_exp (-(Real.log a - Real.log b))
    rw [Real.exp_neg, Real.exp_sub, Real.exp_log ha0, Real.exp_log hb0, inv_div] at h
    rw [div_le_iff₀ ha0]
    have : (b : ℝ) / a * a = b := by field_simp
    nlinarith [mul_le_mul_of_nonneg_right h ha0.le]
  have hgap0 : 0 < ((a : ℝ) - b) / a := by positivity
  have hinv : 1 / (Real.log a - Real.log b) ^ 2 ≤ (a : ℝ) ^ 2 / ((a : ℝ) - b) ^ 2 := by
    rw [div_le_div_iff₀ (by nlinarith) (by positivity), one_mul]
    have h2 := pow_le_pow_left₀ hgap0.le hgap 2
    rw [div_pow, div_le_iff₀ (by positivity)] at h2
    nlinarith
  -- the size of the pair
  have hsize : ((a * b : ℕ) : ℝ) ^ r ≤ (2 : ℝ) ^ (-r) * (a : ℝ) ^ (2 * r) := by
    have hle : (a : ℝ) ^ 2 / 2 ≤ ((a * b : ℕ) : ℝ) := by
      push_cast
      have : (a : ℝ) ≤ 2 * b := by exact_mod_cast ha2
      nlinarith
    calc ((a * b : ℕ) : ℝ) ^ r ≤ ((a : ℝ) ^ 2 / 2) ^ r :=
          Real.rpow_le_rpow_of_nonpos (by positivity) hle hr
      _ = (2 : ℝ) ^ (-r) * (a : ℝ) ^ (2 * r) := by
          rw [Real.div_rpow (by positivity) (by norm_num), Real.rpow_neg (by norm_num),
            ← Real.rpow_natCast, ← Real.rpow_mul ha0.le]
          push_cast; ring
  unfold balancedTerm
  rw [if_pos hba, hsub]
  calc ((a * b : ℕ) : ℝ) ^ r / (Real.log a - Real.log b) ^ 2
      = ((a * b : ℕ) : ℝ) ^ r * (1 / (Real.log a - Real.log b) ^ 2) := by ring
    _ ≤ (2 : ℝ) ^ (-r) * (a : ℝ) ^ (2 * r) * ((a : ℝ) ^ 2 / ((a : ℝ) - b) ^ 2) :=
        mul_le_mul hsize hinv (by positivity) (by positivity)
    _ = (2 : ℝ) ^ (-r) * (a : ℝ) ^ (2 * r + 2) * ((a : ℝ) - b) ^ (-2 : ℝ) := by
        rw [Real.rpow_add ha0, Real.rpow_neg hd0.le, Real.rpow_two, Real.rpow_two]
        field_simp

/-- **The pair majorant.**  For `a ≠ b` positive, `(ab)^r/(log a − log b)² ≤ pairMajorant`. -/
theorem div_log_sq_le_pairMajorant {r : ℝ} (hr : r ≤ 0) {a b : ℕ} (ha : 1 ≤ a) (hb : 1 ≤ b)
    (hab : a ≠ b) :
    ((a * b : ℕ) : ℝ) ^ r / (Real.log a - Real.log b) ^ 2 ≤ pairMajorant r a b := by
  have ha0 : (0 : ℝ) < a := by exact_mod_cast ha
  have hb0 : (0 : ℝ) < b := by exact_mod_cast hb
  have hl2 := Real.log_pos (show (1 : ℝ) < 2 by norm_num)
  have h0 := balancedTerm_nonneg r a b
  have h0' := balancedTerm_nonneg r b a
  have hx : ((a * b : ℕ) : ℝ) ^ r = (a : ℝ) ^ r * (b : ℝ) ^ r := by
    push_cast; exact Real.mul_rpow ha0.le hb0.le
  have hx0 : 0 ≤ (a : ℝ) ^ r * (b : ℝ) ^ r := by positivity
  -- unbalanced pairs
  have hunb : Real.log 2 ≤ |Real.log a - Real.log b| →
      ((a * b : ℕ) : ℝ) ^ r / (Real.log a - Real.log b) ^ 2 ≤ pairMajorant r a b := by
    intro hgap
    unfold pairMajorant
    have hsq : Real.log 2 ^ 2 ≤ (Real.log a - Real.log b) ^ 2 := by
      rw [← sq_abs (Real.log a - Real.log b)]
      exact pow_le_pow_left₀ hl2.le hgap 2
    have : ((a * b : ℕ) : ℝ) ^ r / (Real.log a - Real.log b) ^ 2 ≤
        (Real.log 2)⁻¹ ^ 2 * ((a : ℝ) ^ r * (b : ℝ) ^ r) := by
      rw [hx, inv_pow, ← div_eq_inv_mul]
      exact div_le_div_of_nonneg_left hx0 (by positivity) hsq
    linarith
  rcases lt_or_gt_of_ne hab with hlt | hgt
  · -- a < b
    by_cases h2 : b ≤ 2 * a
    · have h := div_log_sq_le_balancedTerm hr ha hlt h2
      rw [mul_comm b a] at h
      have hsym : (Real.log b - Real.log a) ^ 2 = (Real.log a - Real.log b) ^ 2 := by ring
      rw [hsym] at h
      unfold pairMajorant
      have : 0 ≤ (Real.log 2)⁻¹ ^ 2 * ((a : ℝ) ^ r * (b : ℝ) ^ r) := by positivity
      linarith
    · refine hunb ?_
      rw [abs_sub_comm, abs_of_nonneg (by
        linarith [Real.log_le_log ha0 (show (a : ℝ) ≤ b by exact_mod_cast hlt.le)])]
      have : (2 : ℝ) * a ≤ b := by exact_mod_cast (show 2 * a ≤ b by omega)
      have hl := Real.log_le_log (by positivity) this
      rw [Real.log_mul (by norm_num) ha0.ne'] at hl
      linarith
  · -- b < a
    by_cases h2 : a ≤ 2 * b
    · have h := div_log_sq_le_balancedTerm hr hb hgt h2
      unfold pairMajorant
      have : 0 ≤ (Real.log 2)⁻¹ ^ 2 * ((a : ℝ) ^ r * (b : ℝ) ^ r) := by positivity
      linarith
    · refine hunb ?_
      rw [abs_of_nonneg (by
        linarith [Real.log_le_log hb0 (show (b : ℝ) ≤ a by exact_mod_cast hgt.le)])]
      have : (2 : ℝ) * b ≤ a := by exact_mod_cast (show 2 * b ≤ a by omega)
      have hl := Real.log_le_log (by positivity) this
      rw [Real.log_mul (by norm_num) hb0.ne'] at hl
      linarith

/-- The balanced terms are summable for `2r + 2 < −1`. -/
theorem summable_balancedTerm {r : ℝ} (hr' : 2 * r + 2 < -1) :
    Summable (fun x : ℕ × ℕ => balancedTerm r x.1 x.2) := by
  have hg : Summable (fun n : ℕ => (n : ℝ) ^ (2 * r + 2)) := Real.summable_nat_rpow.mpr hr'
  have hd : Summable (fun n : ℕ => (n : ℝ) ^ (-2 : ℝ)) := Real.summable_nat_rpow.mpr (by norm_num)
  set G : ℕ × ℕ → ℝ := fun x => (2 : ℝ) ^ (-r) * ((x.1 : ℝ) ^ (2 * r + 2) * (x.2 : ℝ) ^ (-2 : ℝ))
    with hGdef
  have hG : Summable G :=
    (Summable.mul_of_nonneg hg hd (fun n => by positivity) (fun n => by positivity)).mul_left _
  set T : Set (ℕ × ℕ) := {x | x.2 < x.1} with hT
  set e : T → ℕ × ℕ := fun x => ((x : ℕ × ℕ).1, (x : ℕ × ℕ).1 - (x : ℕ × ℕ).2) with he
  have hinj : Function.Injective e := by
    intro x y h
    simp only [he, Prod.mk.injEq] at h
    have hx : (x : ℕ × ℕ).2 < (x : ℕ × ℕ).1 := x.2
    have hy : (y : ℕ × ℕ).2 < (y : ℕ × ℕ).1 := y.2
    apply Subtype.ext
    ext
    · exact h.1
    · omega
  set f : ℕ × ℕ → ℝ := fun x => G (x.1, x.1 - x.2) with hf
  have hfT : Summable (f ∘ (Subtype.val : T → ℕ × ℕ)) := hG.comp_injective hinj
  have hind : Summable (T.indicator f) := summable_subtype_iff_indicator.mp hfT
  refine hind.congr fun x => ?_
  unfold balancedTerm
  by_cases hx : x.2 < x.1
  · rw [Set.indicator_of_mem (show x ∈ T from hx), if_pos hx, hf, hGdef]
    simp only
    ring
  · rw [Set.indicator_of_notMem (show x ∉ T from hx), if_neg hx]

/-- **The pair majorant is summable** for `r < −1` and `2r + 2 < −1`. -/
theorem summable_pairMajorant {r : ℝ} (hr : r < -1) (hr' : 2 * r + 2 < -1) :
    Summable (fun x : ℕ × ℕ => pairMajorant r x.1 x.2) := by
  have hf : Summable (fun n : ℕ => (n : ℝ) ^ r) := Real.summable_nat_rpow.mpr hr
  have h1 : Summable (fun x : ℕ × ℕ => (Real.log 2)⁻¹ ^ 2 * ((x.1 : ℝ) ^ r * (x.2 : ℝ) ^ r)) :=
    (Summable.mul_of_nonneg hf hf (fun n => by positivity) (fun n => by positivity)).mul_left _
  have hB := summable_balancedTerm hr'
  have hB'' : Summable ((fun x : ℕ × ℕ => balancedTerm r x.1 x.2) ∘ Prod.swap) :=
    hB.comp_injective Prod.swap_injective
  have hsum := (h1.add hB).add hB''
  refine hsum.congr fun x => ?_
  simp only [pairMajorant, Function.comp, Prod.fst_swap, Prod.snd_swap]

/-! ## The threshold -/

/-- **Convergence above `3/4`.** -/
theorem summable_edgeTerm {σ : ℝ} (hσ : 3 / 4 < σ) :
    Summable (fun m : {m : ℕ →₀ ℤ // IsPrimeMode m ∧ m ≠ 0} => edgeTerm σ m) := by
  set ε : ℝ := (4 * σ - 3) / 4 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  obtain ⟨K, hK0, hK⟩ := exists_modeWeight_le hε σ
  set r : ℝ := ε - 2 * σ with hrdef
  have hr : r < -1 := by rw [hrdef, hεdef]; linarith
  have hr' : 2 * r + 2 < -1 := by rw [hrdef, hεdef]; linarith
  have hr0 : r ≤ 0 := by linarith
  have hP := summable_pairMajorant hr hr'
  set φ : {m : ℕ →₀ ℤ // IsPrimeMode m ∧ m ≠ 0} → ℕ × ℕ :=
    fun m => (posPart (m : ℕ →₀ ℤ), negPart (m : ℕ →₀ ℤ)) with hφ
  have hinj : Function.Injective φ := by
    intro m m' h
    exact Subtype.ext (eq_of_posPart_negPart m.2.1 m'.2.1 (congrArg Prod.fst h)
      (congrArg Prod.snd h))
  have hS : Summable (fun m : {m : ℕ →₀ ℤ // IsPrimeMode m ∧ m ≠ 0} =>
      K * pairMajorant r (φ m).1 (φ m).2) :=
    (hP.comp_injective hinj).mul_left K
  refine Summable.of_nonneg_of_le (fun m => edgeTerm_nonneg σ m) (fun m => ?_) hS
  obtain ⟨hm, hm0⟩ := m.2
  unfold edgeTerm
  rw [modeFreq_eq hm]
  have hw := hK m hm
  have hmaj := div_log_sq_le_pairMajorant hr0 (posPart_pos hm) (negPart_pos hm)
    (posPart_ne_negPart hm hm0)
  calc modeWeight σ m / (Real.log (posPart m) - Real.log (negPart m)) ^ 2
      ≤ K * (((posPart m * negPart m : ℕ) : ℝ)) ^ r /
          (Real.log (posPart m) - Real.log (negPart m)) ^ 2 :=
        div_le_div_of_nonneg_right hw (sq_nonneg _)
    _ = K * ((((posPart m * negPart m : ℕ) : ℝ)) ^ r /
          (Real.log (posPart m) - Real.log (negPart m)) ^ 2) := by ring
    _ ≤ K * pairMajorant r (posPart m) (negPart m) := mul_le_mul_of_nonneg_left hmaj hK0

/-- Larger `σ` gives smaller terms. -/
theorem edgeTerm_antitone {σ σ' : ℝ} (h : σ ≤ σ') {m : ℕ →₀ ℤ} (hm : IsPrimeMode m) :
    edgeTerm σ' m ≤ edgeTerm σ m := by
  unfold edgeTerm modeWeight
  refine div_le_div_of_nonneg_right (prod_le_prod (fun p _ => by positivity) fun p hp => ?_)
    (sq_nonneg _)
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hm p hp).one_lt.le
  refine mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hp1 ?_) (sq_nonneg _)
  have := abs_nonneg ((m p : ℤ) : ℝ)
  nlinarith

/-- The mode of the consecutive pair `(M + 1, M)`. -/
def consecutiveMode (M : ℕ) : ℕ →₀ ℤ :=
  (M + 1).factorization.mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero -
    M.factorization.mapRange (Nat.cast : ℕ → ℤ) Nat.cast_zero

theorem isPrimeMode_consecutiveMode (M : ℕ) : IsPrimeMode (consecutiveMode M) := by
  intro p hp
  have h := Finsupp.support_sub hp
  rcases Finset.mem_union.mp h with h | h
  · exact Nat.prime_of_mem_primeFactors (Finsupp.support_mapRange h)
  · exact Nat.prime_of_mem_primeFactors (Finsupp.support_mapRange h)

theorem factorization_succ_eq_zero_of_pos {M p : ℕ} (h : 0 < M.factorization p) :
    (M + 1).factorization p = 0 := by
  have hp : p.Prime := Nat.prime_of_mem_primeFactors (Finsupp.mem_support_iff.mpr h.ne')
  have hdvd : p ∣ M := Nat.dvd_of_factorization_pos h.ne'
  refine Nat.factorization_eq_zero_of_not_dvd fun h1 => hp.one_lt.ne' ?_
  exact Nat.dvd_one.mp ((Nat.dvd_add_right hdvd).mp h1)

theorem posPart_consecutiveMode (M : ℕ) : posPart (consecutiveMode M) = M + 1 := by
  have hfac : (consecutiveMode M).mapRange Int.toNat rfl = (M + 1).factorization := by
    ext p
    simp only [Finsupp.mapRange_apply, consecutiveMode, Finsupp.coe_sub, Pi.sub_apply]
    by_cases h : M.factorization p = 0
    · rw [h]; simp
    · rw [factorization_succ_eq_zero_of_pos (Nat.pos_of_ne_zero h)]; simp
  unfold posPart
  rw [hfac, Nat.prod_factorization_pow_eq_self (Nat.succ_ne_zero M)]

theorem negPart_consecutiveMode {M : ℕ} (hM : 1 ≤ M) : negPart (consecutiveMode M) = M := by
  have hfac : (-consecutiveMode M).mapRange Int.toNat rfl = M.factorization := by
    ext p
    simp only [Finsupp.mapRange_apply, consecutiveMode, Finsupp.coe_neg, Finsupp.coe_sub,
      Pi.neg_apply, Pi.sub_apply]
    by_cases h : M.factorization p = 0
    · rw [h]; simp
    · rw [factorization_succ_eq_zero_of_pos (Nat.pos_of_ne_zero h)]; simp
  unfold negPart
  rw [hfac, Nat.prod_factorization_pow_eq_self (by omega)]

theorem consecutiveMode_ne_zero {M : ℕ} (hM : 1 ≤ M) : consecutiveMode M ≠ 0 := by
  intro h
  have h1 := posPart_consecutiveMode M
  rw [h] at h1
  have : posPart (0 : ℕ →₀ ℤ) = 1 := by simp [posPart]
  omega

/-- `∏_{p ∈ supp m} (log p)² ≥ (log 2)²` on a prime mode. -/
theorem log_two_sq_le_prod_log_sq {m : ℕ →₀ ℤ} (hm : IsPrimeMode m) :
    Real.log 2 ^ 2 ≤ ∏ p ∈ m.support, Real.log p ^ 2 := by
  have hl2 := Real.log_two_lt_d9
  have hl20 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have hl21 : Real.log 2 ^ 2 ≤ 1 := by nlinarith
  have hfac : ∀ p ∈ m.support, (if p = 2 then Real.log 2 ^ 2 else 1) ≤ Real.log p ^ 2 := by
    intro p hp
    split_ifs with h
    · rw [h]; norm_num
    · have hp3 : (3 : ℝ) ≤ p := by
        have := (hm p hp).two_le
        exact_mod_cast (show 3 ≤ p by omega)
      have hl3 : 1 ≤ Real.log p := by
        rw [Real.le_log_iff_exp_le (by linarith)]
        linarith [Real.exp_one_lt_d9]
      nlinarith
  calc Real.log 2 ^ 2 ≤ ∏ p ∈ m.support, (if p = 2 then Real.log 2 ^ 2 else 1) := by
        rw [prod_ite_eq']
        split_ifs <;> linarith
    _ ≤ _ := prod_le_prod (fun p _ => by split_ifs <;> positivity) hfac

/-- **The consecutive pairs are `≫ 1/M` at `σ = 3/4`.** -/
theorem le_edgeTerm_consecutiveMode {M : ℕ} (hM : 1 ≤ M) :
    Real.log 2 ^ 2 * (2 : ℝ) ^ (-(3 / 2 : ℝ)) / M ≤ edgeTerm (3 / 4) (consecutiveMode M) := by
  set m := consecutiveMode M with hmdef
  have hm := isPrimeMode_consecutiveMode M
  have hM0 : (0 : ℝ) < M := by exact_mod_cast hM
  -- the weight
  have hW : modeWeight (3 / 4) m = (∏ p ∈ m.support, Real.log p ^ 2) *
      ((((M + 1) * M : ℕ) : ℝ)) ^ (-(3 / 2 : ℝ)) := by
    unfold modeWeight
    rw [prod_mul_distrib]
    congr 1
    have := prod_rpow_eq (m := m) (-(3 / 2 : ℝ))
    rw [posPart_consecutiveMode, negPart_consecutiveMode hM] at this
    rw [← this]
    exact prod_congr rfl fun p _ => by congr 1; ring
  -- the frequency
  have hF : modeFreq m = Real.log (M + 1) - Real.log M := by
    rw [modeFreq_eq hm, posPart_consecutiveMode, negPart_consecutiveMode hM]; push_cast; ring
  have hF0 : 0 < Real.log ((M : ℝ) + 1) - Real.log M := by
    have := Real.log_lt_log hM0 (show (M : ℝ) < M + 1 by linarith); linarith
  have hF1 : Real.log ((M : ℝ) + 1) - Real.log M ≤ 1 / M := by
    rw [← Real.log_div (by positivity) hM0.ne']
    have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < (M + 1) / M by positivity)
    have h : ((M : ℝ) + 1) / M - 1 = 1 / M := by field_simp; ring
    linarith
  have hsq : (Real.log ((M : ℝ) + 1) - Real.log M) ^ 2 ≤ (1 / M) ^ 2 :=
    pow_le_pow_left₀ hF0.le hF1 2
  -- the size
  have hsize : (2 : ℝ) ^ (-(3 / 2 : ℝ)) * (M : ℝ) ^ (-(3 : ℝ)) ≤
      ((((M + 1) * M : ℕ) : ℝ)) ^ (-(3 / 2 : ℝ)) := by
    have hle : ((((M + 1) * M : ℕ) : ℝ)) ≤ 2 * (M : ℝ) ^ 2 := by
      push_cast
      have : (1 : ℝ) ≤ M := by exact_mod_cast hM
      nlinarith
    calc (2 : ℝ) ^ (-(3 / 2 : ℝ)) * (M : ℝ) ^ (-(3 : ℝ)) = (2 * (M : ℝ) ^ 2) ^ (-(3 / 2 : ℝ)) := by
          rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_natCast,
            ← Real.rpow_mul hM0.le]
          norm_num
      _ ≤ _ := Real.rpow_le_rpow_of_nonpos (by positivity) hle (by norm_num)
  have hL := log_two_sq_le_prod_log_sq hm
  unfold edgeTerm
  rw [hW, hF]
  have hpos : 0 < (Real.log ((M : ℝ) + 1) - Real.log M) ^ 2 := by positivity
  rw [le_div_iff₀ hpos]
  have hl20 : 0 ≤ Real.log 2 ^ 2 := sq_nonneg _
  have h2 : (0 : ℝ) ≤ (2 : ℝ) ^ (-(3 / 2 : ℝ)) := by positivity
  calc Real.log 2 ^ 2 * (2 : ℝ) ^ (-(3 / 2 : ℝ)) / M * (Real.log ((M : ℝ) + 1) - Real.log M) ^ 2
      ≤ Real.log 2 ^ 2 * (2 : ℝ) ^ (-(3 / 2 : ℝ)) / M * (1 / M) ^ 2 :=
        mul_le_mul_of_nonneg_left hsq (by positivity)
    _ = Real.log 2 ^ 2 * ((2 : ℝ) ^ (-(3 / 2 : ℝ)) * (M : ℝ) ^ (-(3 : ℝ))) := by
        rw [Real.rpow_neg hM0.le, show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast]
        field_simp
    _ ≤ (∏ p ∈ m.support, Real.log p ^ 2) * ((((M + 1) * M : ℕ) : ℝ)) ^ (-(3 / 2 : ℝ)) :=
        mul_le_mul hL hsize (by positivity) (by positivity)

/-- **Divergence at `σ = 3/4`, from the consecutive pairs alone.** -/
theorem not_summable_edgeTerm_three_quarters :
    ¬ Summable (fun m : {m : ℕ →₀ ℤ // IsPrimeMode m ∧ m ≠ 0} => edgeTerm (3 / 4) m) := by
  intro hS
  set ι : ℕ → {m : ℕ →₀ ℤ // IsPrimeMode m ∧ m ≠ 0} := fun M =>
    ⟨consecutiveMode (M + 1), isPrimeMode_consecutiveMode _, consecutiveMode_ne_zero (by omega)⟩
    with hι
  have hinj : Function.Injective ι := by
    intro M M' h
    have := congrArg (fun m : {m : ℕ →₀ ℤ // IsPrimeMode m ∧ m ≠ 0} => posPart (m : ℕ →₀ ℤ)) h
    simp only [hι, posPart_consecutiveMode] at this
    omega
  have hc := hS.comp_injective hinj
  have hlow : Summable (fun M : ℕ => Real.log 2 ^ 2 * (2 : ℝ) ^ (-(3 / 2 : ℝ)) / ((M + 1 : ℕ) : ℝ)) :=
    Summable.of_nonneg_of_le (fun M => by positivity)
      (fun M => le_edgeTerm_consecutiveMode (M := M + 1) (by omega)) hc
  have hc0 : 0 < Real.log 2 ^ 2 * (2 : ℝ) ^ (-(3 / 2 : ℝ)) := by
    have := Real.log_pos (show (1 : ℝ) < 2 by norm_num); positivity
  have hinv : Summable (fun M : ℕ => ((M + 1 : ℕ) : ℝ)⁻¹) := by
    have := hlow.mul_left (Real.log 2 ^ 2 * (2 : ℝ) ^ (-(3 / 2 : ℝ)))⁻¹
    refine this.congr fun M => ?_
    field_simp
  exact Real.not_summable_natCast_inv ((summable_nat_add_iff 1).mp (by simpa using hinv))

/-- **The edge coboundary norm is finite exactly for `σ > 3/4`.** -/
theorem summable_edgeTerm_iff (σ : ℝ) :
    Summable (fun m : {m : ℕ →₀ ℤ // IsPrimeMode m ∧ m ≠ 0} => edgeTerm σ m) ↔ 3 / 4 < σ := by
  refine ⟨fun hS => ?_, summable_edgeTerm⟩
  by_contra hσ
  push Not at hσ
  exact not_summable_edgeTerm_three_quarters (Summable.of_nonneg_of_le
    (fun m => edgeTerm_nonneg _ _) (fun m => edgeTerm_antitone hσ m.2.1) hS)

/-- **The critical line lies in the non-reducible zone:** `N_∞(1/2) = ∞`. -/
theorem not_summable_edgeTerm_half :
    ¬ Summable (fun m : {m : ℕ →₀ ℤ // IsPrimeMode m ∧ m ≠ 0} => edgeTerm (1 / 2) m) := by
  rw [summable_edgeTerm_iff]; norm_num

/-- **The threshold for every coefficient model comparable to the explicit-formula weight.** -/
theorem summable_div_modeFreq_sq_iff {σ c C : ℝ} (hc : 0 < c) (g : (ℕ →₀ ℤ) → ℝ)
    (hg : ∀ m, IsPrimeMode m → c * modeWeight σ m ≤ g m ∧ g m ≤ C * modeWeight σ m) :
    Summable (fun m : {m : ℕ →₀ ℤ // IsPrimeMode m ∧ m ≠ 0} => g m / modeFreq m ^ 2) ↔
      3 / 4 < σ := by
  rw [← summable_edgeTerm_iff]
  have hw0 : ∀ m : ℕ →₀ ℤ, 0 ≤ modeWeight σ m := fun m =>
    prod_nonneg fun p _ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Nat.cast_nonneg p) _)
  constructor
  · intro hS
    refine (Summable.of_nonneg_of_le (fun m => edgeTerm_nonneg σ m) (fun m => ?_)
      (hS.mul_left c⁻¹))
    have h1 := (hg m m.2.1).1
    unfold edgeTerm
    calc modeWeight σ m / modeFreq m ^ 2 = c⁻¹ * (c * modeWeight σ m / modeFreq m ^ 2) := by
          field_simp
      _ ≤ c⁻¹ * (g m / modeFreq m ^ 2) :=
          mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h1 (sq_nonneg _))
            (inv_nonneg.mpr hc.le)
  · intro hS
    have hC : 0 ≤ C := by
      by_contra hneg
      push Not at hneg
      have := (hg 0 (fun p hp => by simp at hp))
      have hw : modeWeight σ 0 = 1 := by simp [modeWeight]
      rw [hw] at this
      linarith [this.1, this.2]
    refine Summable.of_nonneg_of_le (fun m => div_nonneg ?_ (sq_nonneg _)) (fun m => ?_)
      (hS.mul_left C)
    · exact le_trans (mul_nonneg hc.le (hw0 _)) (hg m m.2.1).1
    · unfold edgeTerm
      calc g m / modeFreq m ^ 2 ≤ C * modeWeight σ m / modeFreq m ^ 2 :=
            div_le_div_of_nonneg_right (hg m m.2.1).2 (sq_nonneg _)
        _ = C * (modeWeight σ m / modeFreq m ^ 2) := by ring

end GaloisForLFunctions.HTGeometry.EdgeCoboundary
