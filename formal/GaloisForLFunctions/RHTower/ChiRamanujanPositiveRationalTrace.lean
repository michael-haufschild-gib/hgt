import GaloisForLFunctions.RHTower.ChiRamanujanFinsuppTrace
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Nat.Factorization.Defs
import Mathlib.NumberTheory.Padics.PadicVal.Basic
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusRamanujanWeights

/-!
# Positive-rational Ramanujan coefficients and full dilation orthogonality

The explicit prime-valuation equivalence identifies the actual coefficient
with the literal normalized Mobius/Ramanujan denominator weight. Every positive
rational frequency is retained in the absolutely convergent dilation sum.
-/

noncomputable section
open scoped BigOperators
namespace RHTower.BAGTrace

def rationalOfValuations (v : PrimeValuations) : ℚ :=
  v.prod (fun p i => (p : ℚ)^i)

theorem rationalOfValuations_pos (v : PrimeValuations) : 0 < rationalOfValuations v := by
  exact Finset.prod_pos (fun p _ => zpow_pos (by exact_mod_cast p.property.pos) _)

theorem rationalOfValuations_add (v w : PrimeValuations) :
    rationalOfValuations (v+w)=rationalOfValuations v*rationalOfValuations w := by
  exact Finsupp.prod_add_index' (fun p => zpow_zero _)
    (fun p i j => zpow_add₀ (by exact_mod_cast p.property.ne_zero) _ _)

theorem rationalOfValuations_sub (v w : PrimeValuations) :
    rationalOfValuations (v-w)=rationalOfValuations v/rationalOfValuations w := by
  apply (eq_div_iff (rationalOfValuations_pos w).ne').mpr
  rw [← rationalOfValuations_add,sub_add_cancel]

private theorem padicValRat_prime (p q : Nat.Primes) :
    padicValRat p (q : ℚ) = if p=q then 1 else 0 := by
  letI : Fact (Nat.Prime (p : ℕ)) := ⟨p.property⟩
  letI : Fact (Nat.Prime (q : ℕ)) := ⟨q.property⟩
  by_cases h : p=q
  · subst q
    simp [padicValRat.of_nat]
  · have hn : (p : ℕ) ≠ (q : ℕ) := fun he => h (Subtype.ext he)
    simp [padicValRat.of_nat,padicValNat_primes hn,h]

private theorem padicValRat_prime_product (p : Nat.Primes) (P : Finset Nat.Primes)
    (v : Nat.Primes → ℤ) :
    padicValRat p (∏ q ∈ P,(q : ℚ)^(v q)) = ∑ q ∈ P,v q * padicValRat p (q : ℚ) := by
  classical
  letI : Fact (Nat.Prime (p : ℕ)) := ⟨p.property⟩
  induction P using Finset.induction_on with
  | empty => simp
  | @insert q P hq ih =>
    rw [Finset.prod_insert hq,Finset.sum_insert hq,
      padicValRat.mul (zpow_ne_zero _ (by exact_mod_cast q.property.ne_zero))
        (Finset.prod_ne_zero_iff.mpr fun r _ => zpow_ne_zero _ (by exact_mod_cast r.property.ne_zero)),
      padicValRat.zpow,ih]

/-- Prime valuations recover every coordinate of the rational product. -/
theorem padicValRat_rationalOfValuations (v : PrimeValuations) (p : Nat.Primes) :
    padicValRat p (rationalOfValuations v) = v p := by
  classical
  unfold rationalOfValuations Finsupp.prod
  rw [padicValRat_prime_product]
  simp only [padicValRat_prime,mul_ite,mul_one,mul_zero]
  by_cases hp : p ∈ v.support
  · simp [hp]
  · simp [hp,Finsupp.notMem_support_iff.mp hp]

theorem rationalOfValuations_injective : Function.Injective rationalOfValuations := by
  intro v w h
  apply Finsupp.ext
  intro p
  simpa only [padicValRat_rationalOfValuations] using congrArg (padicValRat (p : ℕ)) h

def naturalValuations (n : ℕ) : PrimeValuations :=
  (n.factorization.mapRange (fun k : ℕ => (k : ℤ)) (by simp)).subtypeDomain Nat.Prime

theorem naturalValuations_apply (n : ℕ) (p : Nat.Primes) :
    naturalValuations n p = (n.factorization p : ℤ) := rfl

theorem rationalOfValuations_natural {n : ℕ} (hn : n ≠ 0) :
    rationalOfValuations (naturalValuations n) = (n : ℚ) := by
  let f : ℕ →₀ ℤ := n.factorization.mapRange (fun k : ℕ => (k : ℤ)) (by simp)
  have hf : ∀ p ∈ f.support,Nat.Prime p := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors (Finsupp.support_mapRange hp)
  have h := Finsupp.prod_subtypeDomain_index (p := Nat.Prime) (v := f)
    (h := fun p : ℕ => fun i : ℤ => (p : ℚ)^i) hf
  calc
    rationalOfValuations (naturalValuations n) = f.prod (fun p i => (p : ℚ)^i) := by
      convert h using 1
      rfl
    _ = n.factorization.prod (fun p k => (p : ℚ)^(k : ℤ)) :=
      Finsupp.prod_mapRange_index (fun p : ℕ => zpow_zero (p : ℚ))
    _ = (n : ℚ) := by
      simpa only [Finsupp.prod,Nat.cast_prod,Nat.cast_pow,zpow_natCast] using
        congrArg (fun m : ℕ => (m : ℚ)) (Nat.prod_factorization_pow_eq_self hn)

def positiveRationalValuations (q : {q : ℚ // 0 < q}) : PrimeValuations :=
  naturalValuations q.1.num.natAbs-naturalValuations q.1.den

theorem rationalOfValuations_positive (q : {q : ℚ // 0 < q}) :
    rationalOfValuations (positiveRationalValuations q)=q.1 := by
  have hn : q.1.num.natAbs ≠ 0 := by
    intro h
    exact (Rat.num_pos.mpr q.2).ne' (Int.natAbs_eq_zero.mp h)
  have hnum : (q.1.num.natAbs : ℚ) = (q.1.num : ℚ) := by
    have h : (q.1.num.natAbs : ℤ) = q.1.num := by
      rw [Int.natCast_natAbs,abs_of_nonneg (Rat.num_nonneg.mpr q.2.le)]
    simpa only [Int.cast_natCast] using congrArg (fun z : ℤ => (z : ℚ)) h
  rw [positiveRationalValuations,rationalOfValuations_sub,
    rationalOfValuations_natural hn,rationalOfValuations_natural q.1.den_ne_zero,hnum,
    Rat.num_div_den]

/-- The complete integer prime lattice is exactly the positive rational multiplicative group. -/
def positiveRationalEquiv : PrimeValuations ≃ {q : ℚ // 0 < q} where
  toFun v := ⟨rationalOfValuations v,rationalOfValuations_pos v⟩
  invFun := positiveRationalValuations
  left_inv v := rationalOfValuations_injective
    (rationalOfValuations_positive ⟨rationalOfValuations v,rationalOfValuations_pos v⟩)
  right_inv q := Subtype.ext (rationalOfValuations_positive q)

theorem positiveRationalValuations_mul (q r : {q : ℚ // 0 < q}) :
    positiveRationalValuations ⟨q.1*r.1,mul_pos q.2 r.2⟩ =
      positiveRationalValuations q + positiveRationalValuations r := by
  apply rationalOfValuations_injective
  simp only [rationalOfValuations_positive,rationalOfValuations_add]

theorem valuationWeight_rational (σ : ℝ) (v : PrimeValuations) :
    valuationWeight σ v = (rationalOfValuations v : ℝ)^(-σ) := by
  classical
  calc
    valuationWeight σ v = ∏ p ∈ v.support,((p : ℝ)^(v p))^(-σ) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact Real.rpow_zpow_comm (by exact_mod_cast p.property.pos.le) (-σ) (v p)
    _ = (∏ p ∈ v.support,(p : ℝ)^(v p))^(-σ) :=
      Real.finsetProd_rpow _ _ (fun p _ => (zpow_pos (by exact_mod_cast p.property.pos) _).le) _
    _ = (rationalOfValuations v : ℝ)^(-σ) := by
      congr 1
      simp [rationalOfValuations,Finsupp.prod]

theorem valuationCoefficient_coprime_sub (σ : ℝ) {n d : ℕ} (hcop : n.Coprime d) :
    valuationCoefficient σ (naturalValuations n-naturalValuations d) =
      valuationCoefficient σ (-naturalValuations d) := by
  classical
  apply Finsupp.prod_congr_of_eq_on_union
  · intro p hp
    simp only [Finsupp.sub_apply,Finsupp.neg_apply,naturalValuations_apply]
    by_cases hd : d.factorization p=0
    · have hn : (n.factorization p : ℤ) ≠ -1 := by omega
      simp [hd,coefficient,hn]
    · have hnd : ¬(p : ℕ) ∣ n := fun hpn =>
        Nat.not_coprime_of_dvd_of_dvd p.property.one_lt hpn
          (Nat.dvd_of_factorization_pos hd) hcop
      rw [Nat.factorization_eq_zero_of_not_dvd hnd]
      simp
  · intro p hp
    simp [coefficient]
  · intro p hp
    simp [coefficient]

private theorem coefficient_prime_negative (σ : ℝ) (p : Nat.Primes) {k : ℕ} (hk : 0 < k) :
    coefficient (primeWeight σ p) (-(k : ℤ)) =
      (ArithmeticFunction.moebius ((p : ℕ)^k) : ℝ)/((p : ℝ)^σ-1) := by
  by_cases hk1 : k=1
  · subst k
    simpa only [Nat.cast_one,pow_one,ArithmeticFunction.moebius_apply_prime p.property,
      Int.cast_neg,Int.cast_one] using coefficient_primeWeight_neg_one σ p
  · have hn : -(k : ℤ) ≠ -1 := by omega
    simp [coefficient,hn,hk.ne',ArithmeticFunction.moebius_apply_prime_pow p.property hk.ne',hk1]

theorem valuationCoefficient_neg_natural (σ : ℝ) {n : ℕ} (hn : n ≠ 0) :
    valuationCoefficient σ (-naturalValuations n) =
      (ArithmeticFunction.moebius n : ℝ)/pmPowerDampedRamanujanDenominator (σ-1) n := by
  classical
  let f : ℕ →₀ ℤ := n.factorization.mapRange (fun k : ℕ => (k : ℤ)) (by simp)
  have hf : ∀ p ∈ f.support,Nat.Prime p := by
    intro p hp
    exact Nat.prime_of_mem_primeFactors (Finsupp.support_mapRange hp)
  have hc0 (p : ℕ) : coefficient ((p : ℝ)^(-σ)) (-(0 : ℤ))=1 := by simp [coefficient]
  have hsub := Finsupp.prod_subtypeDomain_index (p := Nat.Prime) (v := f)
    (h := fun p : ℕ => fun i : ℤ => coefficient ((p : ℝ)^(-σ)) (-i)) hf
  have hprod : valuationCoefficient σ (-naturalValuations n) =
      n.factorization.prod (fun p k => coefficient ((p : ℝ)^(-σ)) (-(k : ℤ))) := by
    calc
      _ = (naturalValuations n).prod (fun p i => coefficient (primeWeight σ p) (-i)) :=
        Finsupp.prod_neg_index (fun p => by simp [coefficient])
      _ = f.prod (fun p i => coefficient ((p : ℝ)^(-σ)) (-i)) := by
        convert hsub using 1
        rfl
      _ = _ := Finsupp.prod_mapRange_index hc0
  have hmu : (ArithmeticFunction.moebius n : ℝ) =
      ∏ p ∈ n.primeFactors,(ArithmeticFunction.moebius (p^(n.factorization p)) : ℝ) := by
    have h := ArithmeticFunction.IsMultiplicative.multiplicative_factorization
      ArithmeticFunction.moebius ArithmeticFunction.isMultiplicative_moebius hn
    simpa only [Finsupp.prod,Nat.support_factorization,Int.cast_prod] using
      congrArg (fun z : ℤ => (z : ℝ)) h
  rw [hprod,Finsupp.prod,Nat.support_factorization]
  calc
    (∏ p ∈ n.primeFactors,coefficient ((p : ℝ)^(-σ)) (-(n.factorization p : ℤ))) =
        ∏ p ∈ n.primeFactors,(ArithmeticFunction.moebius (p^(n.factorization p)) : ℝ)/((p : ℝ)^σ-1) := by
      apply Finset.prod_congr rfl
      intro p hp
      exact coefficient_prime_negative σ ⟨p,Nat.prime_of_mem_primeFactors hp⟩
        ((Nat.prime_of_mem_primeFactors hp).factorization_pos_of_dvd hn (Nat.dvd_of_mem_primeFactors hp))
    _ = _ := by
      rw [Finset.prod_div_distrib,← hmu]
      simp only [pmPowerDampedRamanujanDenominator,show 1+(σ-1)=σ by ring]

def rationalRamanujanCoefficient (σ : ℝ) (q : {q : ℚ // 0 < q}) : ℝ :=
  (ArithmeticFunction.moebius q.1.den : ℝ)/pmPowerDampedRamanujanDenominator (σ-1) q.1.den

/-- The prime-lattice coefficient is the literal normalized Ramanujan denominator weight. -/
theorem valuationCoefficient_positiveRational (σ : ℝ) (q : {q : ℚ // 0 < q}) :
    valuationCoefficient σ (positiveRationalValuations q) = rationalRamanujanCoefficient σ q := by
  rw [positiveRationalValuations,valuationCoefficient_coprime_sub σ q.1.reduced,
    valuationCoefficient_neg_natural σ q.1.den_ne_zero]
  rfl

theorem rationalRamanujanCoefficient_source {ε : ℝ} (hε : 0 < ε)
    (q : {q : ℚ // 0 < q}) :
    pmPowerDampedRamanujanWeight ε q.1.den =
      pmPowerDampedDivisorDensity ε * (rationalRamanujanCoefficient (1+ε) q : ℂ) := by
  rw [pmPowerDampedRamanujanWeight_eq_euler ε hε]
  simp only [rationalRamanujanCoefficient,add_sub_cancel_left,Complex.ofReal_div]
  push_cast
  ring

theorem positiveRationalValuations_equiv (v : PrimeValuations) :
    positiveRationalValuations (positiveRationalEquiv v)=v := positiveRationalEquiv.left_inv v

theorem positiveRationalValuations_eq_zero_iff (q : {q : ℚ // 0 < q}) :
    positiveRationalValuations q=0 ↔ q.1=1 := by
  have hz : rationalOfValuations 0=1 := by simp [rationalOfValuations]
  constructor
  · intro h
    have hq := rationalOfValuations_positive q
    rw [h,hz] at hq
    exact hq.symm
  · intro h
    apply rationalOfValuations_injective
    exact ((rationalOfValuations_positive q).trans h).trans hz.symm

def rationalDilation (σ : ℝ) (b a : {q : ℚ // 0 < q}) : ℝ :=
  rationalRamanujanCoefficient σ a *
    rationalRamanujanCoefficient σ ⟨a.1*b.1,mul_pos a.2 b.2⟩ * (a.1 : ℝ)^(-σ)

theorem rationalDilation_eq_valuation (σ : ℝ) (b a : {q : ℚ // 0 < q}) :
    rationalDilation σ b a = valuationDilation σ (positiveRationalValuations b)
      (positiveRationalValuations a) := by
  simp only [rationalDilation,valuationDilation,← valuationCoefficient_positiveRational,
    positiveRationalValuations_mul,valuationWeight_rational,rationalOfValuations_positive]

/-- Complete rational-dilation orthogonality for the literal normalized Ramanujan coefficient.
All positive rational frequencies are included; no summability or cancellation is assumed. -/
theorem rationalDilation_hasSum {σ : ℝ} (hσ : 1 < σ) (b : {q : ℚ // 0 < q}) :
    HasSum (rationalDilation σ b) (if b.1=1 then (riemannZeta (σ : ℂ)).re^2 else 0) := by
  have h := valuationDilation_hasSum hσ (positiveRationalValuations b)
  have ht : HasSum (fun v => rationalDilation σ b (positiveRationalEquiv v))
      (if positiveRationalValuations b=0 then (riemannZeta (σ : ℂ)).re^2 else 0) :=
    h.congr_fun (fun v => by rw [rationalDilation_eq_valuation,positiveRationalValuations_equiv])
  simp only [positiveRationalValuations_eq_zero_iff] at ht
  exact positiveRationalEquiv.hasSum_iff.mp ht

theorem summable_norm_rationalDilation {σ : ℝ} (hσ : 1 < σ) (b : {q : ℚ // 0 < q}) :
    Summable (fun a => ‖rationalDilation σ b a‖) := by
  have h := summable_norm_valuationDilation hσ (positiveRationalValuations b)
  have ht : Summable (fun v => ‖rationalDilation σ b (positiveRationalEquiv v)‖) :=
    h.congr (fun v => by rw [rationalDilation_eq_valuation,positiveRationalValuations_equiv])
  exact positiveRationalEquiv.summable_iff.mp ht

end RHTower.BAGTrace
