import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.HeatTrace
import GaloisForLFunctions.GaloisTheoryOfZeros.TheMaximalArithmeticQuotientOfTheZeroMotive
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Analysis.Convex.SpecificFunctions.Basic

/-!
# Finite quantum multiplicities quantize the heat exponent

An energy shell with D orthogonal outcomes of common heat amplitude must satisfy
D n^(-2 Re s) = 1 to preserve probability. Three distinct prime tests suffice
to classify every possible exponent. The six exponentials theorem forces
rationality, and the valuation at one of the primes removes the denominator.
-/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas

/-- Conservation of the total Born weight at a shell with D outcomes. -/
def conserves (s : ℂ) (n : ℕ+) (D : ℕ) : Prop := (D : ℝ) * ‖heat s n‖ ^ 2 = 1

theorem conserves_iff_count (s : ℂ) (n : ℕ+) (D : ℕ) :
    conserves s n D ↔ (D : ℝ) = ((n : ℕ) : ℝ) ^ (2 * s.re) := by
  have h : ((n : ℕ) : ℝ) ^ (2 * s.re) * ‖heat s n‖ ^ 2 = 1 := by
    rw [norm_heat, sq, ← Real.exp_add, Real.rpow_def_of_pos (by exact_mod_cast n.pos),
      ← Real.exp_add, Real.exp_eq_one_iff]
    unfold energy
    ring
  unfold conserves
  rw [← h, mul_left_inj' (by rw [norm_heat]; positivity : ‖heat s n‖ ^ 2 ≠ 0)]

/-- Independent phases on the individual outcomes leave the norm criterion unchanged. -/
theorem branch_norm_iff (s : ℂ) (n : ℕ+) (D : ℕ) (phase : Fin D → Circle) :
    ‖(WithLp.toLp 2 (fun i => (phase i : ℂ) * heat s n) : EuclideanSpace ℂ (Fin D))‖ = 1 ↔
      conserves s n D := by
  rw [← sq_eq_sq₀ (norm_nonneg _) zero_le_one, EuclideanSpace.norm_sq_eq, one_pow]
  simp only [norm_mul, Circle.norm_coe, one_mul, Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, conserves]

private theorem algebraic_prime_value (α : ℝ) {p D : ℕ} (hp : 0 < p)
    (h : (D : ℝ) = (p : ℝ) ^ α) :
    IsAlgebraic ℚ (Complex.exp ((α : ℂ) * (Real.log p : ℂ))) := by
  have he : Complex.exp ((α : ℂ) * (Real.log p : ℂ)) = (D : ℂ) := by
    rw [← Complex.ofReal_mul, ← Complex.ofReal_exp, mul_comm, ← Real.rpow_def_of_pos
      (show (0 : ℝ) < p by exact_mod_cast hp), ← h, Complex.ofReal_natCast]
  rw [he]
  exact isAlgebraic_nat D

private theorem rational_exponent_eq_valuation (q : ℚ) {p D : ℕ} (hp : p.Prime)
    (h : (D : ℝ) = (p : ℝ) ^ (q : ℝ)) : (q : ℝ) = (padicValNat p D : ℝ) := by
  letI : Fact p.Prime := ⟨hp⟩
  have hd : (q.den : ℝ) ≠ 0 := by exact_mod_cast q.den_ne_zero
  have hq : (q : ℝ) * q.den = (q.num : ℝ) := by rw [Rat.cast_def, div_mul_cancel₀ _ hd]
  have he : (p : ℝ) ^ q.num = (D : ℝ) ^ q.den := by
    rw [← Real.rpow_intCast, ← hq, Real.rpow_mul (Nat.cast_nonneg p),
      ← h, Real.rpow_natCast]
  have heQ : (p : ℚ) ^ q.num = (D : ℚ) ^ q.den := by
    apply Rat.cast_injective (α := ℝ)
    push_cast
    exact he
  have hv := congrArg (padicValRat p) heQ
  rw [padicValRat.zpow, padicValRat.self hp.one_lt, mul_one,
    padicValRat.pow, padicValRat.of_nat] at hv
  have hvR : (q.num : ℝ) = (q.den : ℝ) * (padicValNat p D : ℝ) := by
    simpa only [Int.cast_mul, Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℝ)) hv
  apply mul_right_cancel₀ hd
  rw [hq, hvR, mul_comm]

/-- Even without prescribing the outcome counts, normalization at any three distinct
prime energies is possible exactly at a nonnegative half-integer real part. -/
theorem three_prime_quantization (s : ℂ) (p q r : Nat.Primes)
    (hpq : p ≠ q) (hpr : p ≠ r) (hqr : q ≠ r) :
    ((∃ D, conserves s ⟨p, p.2.pos⟩ D) ∧ (∃ D, conserves s ⟨q, q.2.pos⟩ D) ∧
      (∃ D, conserves s ⟨r, r.2.pos⟩ D)) ↔ ∃ k : ℕ, 2 * s.re = k := by
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩, ⟨c, hc⟩⟩
    have hA := (conserves_iff_count ..).1 ha
    have hB := (conserves_iff_count ..).1 hb
    have hC := (conserves_iff_count ..).1 hc
    obtain ⟨v, hv⟩ := GaloisTheoryOfZeros.rational_of_three_prime_exponentials
      p.2 q.2 r.2 (fun h => hpq (Subtype.ext h)) (fun h => hpr (Subtype.ext h))
      (fun h => hqr (Subtype.ext h)) (algebraic_prime_value _ p.2.pos hA)
      (algebraic_prime_value _ q.2.pos hB) (algebraic_prime_value _ r.2.pos hC)
    have he : 2 * s.re = (v : ℝ) := by exact_mod_cast hv
    refine ⟨padicValNat p a, he.trans (rational_exponent_eq_valuation v p.2 ?_)⟩
    rw [← he]
    exact hA
  · rintro ⟨k, hk⟩
    have fit (n : ℕ+) : ∃ D, conserves s n D := by
      refine ⟨(n : ℕ) ^ k, (conserves_iff_count ..).2 ?_⟩
      rw [hk, Real.rpow_natCast, Nat.cast_pow]
    exact ⟨fit _, fit _, fit _⟩

/-- A family of integral shell multiplicities is uniquely a tensor power of the
one-residue count. -/
theorem all_shells_quantization (s : ℂ) (D : ℕ+ → ℕ) :
    (∀ n, conserves s n (D n)) ↔ ∃ k : ℕ, 2 * s.re = k ∧ ∀ n : ℕ+, D n = (n : ℕ) ^ k := by
  constructor
  · intro h
    let p : Nat.Primes := ⟨2, Nat.prime_two⟩
    let q : Nat.Primes := ⟨3, Nat.prime_three⟩
    let r : Nat.Primes := ⟨5, Nat.prime_five⟩
    have hneq {a b : Nat.Primes} (hne : (a : ℕ) ≠ b) : a ≠ b := fun hh => hne (congrArg Subtype.val hh)
    obtain ⟨k, hk⟩ := (three_prime_quantization s p q r (hneq (by norm_num [p,q]))
      (hneq (by norm_num [p,r])) (hneq (by norm_num [q,r]))).1
      ⟨⟨_, h _⟩, ⟨_, h _⟩, ⟨_, h _⟩⟩
    refine ⟨k, hk, fun n => ?_⟩
    have hv := (conserves_iff_count ..).1 (h n)
    rw [hk, Real.rpow_natCast] at hv
    exact_mod_cast hv
  · rintro ⟨k, hk, hD⟩ n
    rw [conserves_iff_count, hD, hk, Nat.cast_pow, Real.rpow_natCast]

/-- Throughout the open critical strip, allowing arbitrary finite branch counts
still leaves exactly the classical critical line. -/
theorem strip_resolution_iff (s : {z : ℂ // 0 < z.re ∧ z.re < 1}) :
    (∃ D : ℕ+ → ℕ, ∀ n, conserves s.val n (D n)) ↔ s.val.re = 1 / 2 := by
  constructor
  · rintro ⟨D, h⟩
    obtain ⟨k, hk, _⟩ := (all_shells_quantization s.val D).1 h
    have hpos : 0 < (k : ℝ) := by linarith [s.2.1]
    have hlt : (k : ℝ) < 2 := by linarith [s.2.2]
    have hk1 : k = 1 := by
      have : 0 < k := by exact_mod_cast hpos
      have : k < 2 := by exact_mod_cast hlt
      omega
    rw [hk1, Nat.cast_one] at hk
    linarith
  · intro h
    exact ⟨fun n => (n : ℕ), (all_shells_quantization _ _).2
      ⟨1, by rw [h]; norm_num, fun n => (pow_one (n : ℕ)).symm⟩⟩

private theorem power_midpoint {α x y : ℝ} (hα : 1 < α) (hx : 0 ≤ x) (hy : 0 ≤ y) (hxy : x ≠ y) :
    ((x + y) / 2) ^ α < (x ^ α + y ^ α) / 2 := by
  have h := (strictConvexOn_rpow hα).2 hx hy hxy
    (show (0 : ℝ) < 1/2 by norm_num) (show (0 : ℝ) < 1/2 by norm_num) (by norm_num)
  change (1/2 * x + 1/2 * y) ^ α < 1/2 * x ^ α + 1/2 * y ^ α at h
  rwa [show 1/2 * x + 1/2 * y = (x+y)/2 by ring,
    show 1/2 * x ^ α + 1/2 * y ^ α = (x ^ α + y ^ α)/2 by ring] at h

/-- The first two prime probes already force the critical line inside the open strip.
If the dyadic shell had three channels, strict convexity at 2 and 3 would force
the triadic shell to have strictly between five and six channels. -/
theorem binary_ternary_resolution_iff (s : {z : ℂ // 0 < z.re ∧ z.re < 1}) :
    ((∃ D, conserves s.val 2 D) ∧ (∃ D, conserves s.val 3 D)) ↔ s.val.re = 1 / 2 := by
  let α := 2 * s.val.re
  have hα0 : 0 < α := by dsimp [α]; linarith [s.2.1]
  have hα2 : α < 2 := by dsimp [α]; linarith [s.2.2]
  constructor
  · rintro ⟨⟨a, ha⟩, ⟨b, hb⟩⟩
    have h₂ : (a : ℝ) = (2 : ℝ) ^ α := (conserves_iff_count ..).1 ha
    have h₃ : (b : ℝ) = (3 : ℝ) ^ α := (conserves_iff_count ..).1 hb
    have inc := Real.strictMono_rpow_of_base_gt_one (show (1 : ℝ) < 2 by norm_num)
    have hlo : (2 : ℝ) ^ (0 : ℝ) < 2 ^ α := inc hα0
    have hhi : (2 : ℝ) ^ α < 2 ^ (2 : ℝ) := inc hα2
    rw [Real.rpow_zero, ← h₂] at hlo
    rw [Real.rpow_two, ← h₂] at hhi
    have ha1 : 1 < a := by exact_mod_cast hlo
    have ha4 : a < 4 := by exact_mod_cast (show (a : ℝ) < 4 by linarith)
    rcases (show a = 2 ∨ a = 3 by omega) with h | h
    · have he : α = 1 := inc.injective (by simpa [h] using h₂.symm)
      dsimp [α] at he
      linarith
    · have hd : (2 : ℝ) ^ α = 3 := by simpa [h] using h₂.symm
      have hgt : 1 < α := inc.lt_iff_lt.mp (by rw [Real.rpow_one, hd]; norm_num)
      have hfour : (4 : ℝ) ^ α = 9 := by
        rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.mul_rpow (by norm_num) (by norm_num), hd]
        norm_num
      have left := power_midpoint (x := 1) (y := 3) hgt (by norm_num) (by norm_num) (by norm_num)
      have right := power_midpoint (x := 2) (y := 4) hgt (by norm_num) (by norm_num) (by norm_num)
      rw [show (1 + 3 : ℝ)/2 = 2 by norm_num, hd, Real.one_rpow, ← h₃] at left
      rw [show (2 + 4 : ℝ)/2 = 3 by norm_num, ← h₃, hd, hfour] at right
      have h5 : 5 < b := by exact_mod_cast (show (5 : ℝ) < b by linarith)
      have h6 : b < 6 := by exact_mod_cast (show (b : ℝ) < 6 by linarith)
      omega
  · intro hs
    have fit (n : ℕ+) : conserves s.val n n := by
      rw [conserves_iff_count, hs, show (2 : ℝ) * (1 / 2) = 1 by norm_num, Real.rpow_one]
    exact ⟨⟨_, fit 2⟩, ⟨_, fit 3⟩⟩

/-- With unspecified multiplicities the dyadic probe alone has an off-line realization. -/
theorem dyadic_three_outcomes :
    ∃ s : ℂ, 1/2 < s.re ∧ s.re < 1 ∧ conserves s 2 3 := by
  let α := Real.log 3 / Real.log 2
  have hlog : Real.log 2 ≠ 0 := (Real.log_pos (by norm_num)).ne'
  have hv : (2 : ℝ) ^ α = 3 := by
    rw [Real.rpow_def_of_pos (by norm_num), show Real.log 2 * α = Real.log 3 by
      dsimp [α]; field_simp, Real.exp_log (by norm_num)]
  have inc := Real.strictMono_rpow_of_base_gt_one (show (1 : ℝ) < 2 by norm_num)
  have h₁ : 1 < α := inc.lt_iff_lt.mp (by rw [Real.rpow_one, hv]; norm_num)
  have h₂ : α < 2 := inc.lt_iff_lt.mp (by rw [Real.rpow_two, hv]; norm_num)
  refine ⟨((α / 2 : ℝ) : ℂ), by simp only [Complex.ofReal_re]; linarith,
    by simp only [Complex.ofReal_re]; linarith, ?_⟩
  rw [conserves_iff_count, Complex.ofReal_re, show 2 * (α / 2) = α by ring]
  exact hv.symm

#print axioms branch_norm_iff
#print axioms three_prime_quantization
#print axioms all_shells_quantization
#print axioms strip_resolution_iff
#print axioms binary_ternary_resolution_iff
#print axioms dyadic_three_outcomes

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas
