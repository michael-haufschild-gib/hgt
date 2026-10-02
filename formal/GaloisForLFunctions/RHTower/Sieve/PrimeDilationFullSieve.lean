import GaloisForLFunctions.RHTower.Sieve.AffinePairFullDensity
import GaloisForLFunctions.RHTower.Sieve.PrimePairAverageSharp
import GaloisForLFunctions.RHTower.Sieve.PrimeDilationPairs

noncomputable section
open Finset
namespace RHTower.Sieve

/-- The actual affine support with the full sifting primorial and its source-derived
local density parameter, including every slope prime. -/
def affinePairFullSieve (M : ℕ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) (h a b c d : ℕ)
    {z : ℝ} (hz : 1 ≤ z) : SelbergSieve :=
  { roughPairSieve (M : ℝ) hP₁ h ((affinePairDiscriminant a b c d).natAbs * a * b) hz with
    support := (Icc 1 M).image (affinePairProduct a b c d) }

private theorem affinePairFullSieve_multSum (M : ℕ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) (h : ℕ)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (c d : ℕ) {z : ℝ} (hz : 1 ≤ z) (e : ℕ) :
    BoundingSieve.multSum (s := (affinePairFullSieve M hP₁ h a b c d hz).toBoundingSieve) e =
      (((Icc 1 M).filter (fun n => e ∣ affinePairProduct a b c d n)).card : ℝ) := by
  have hi : Set.InjOn (affinePairProduct a b c d) ((Icc 1 M : Finset ℕ) : Set ℕ) :=
    (affinePairProduct_injOn ha hb c d).mono (fun _ hn => (mem_Icc.mp hn).1)
  change (∑ v ∈ (Icc 1 M).image (affinePairProduct a b c d), if e ∣ v then (1 : ℝ) else 0) = _
  rw [sum_image hi, sum_boole]

/-- The entire full-primorial remainder follows from actual prime anchors and affine CRT. -/
theorem affinePairFullSieve_remainder_le (M : ℕ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) (h : ℕ)
    {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hc : c.Prime) (hd : d.Prime) (hhc : h < c) (hhd : h < d) {z : ℝ} (hz : 1 ≤ z)
    {e : ℕ} (he : e ∣ rangePrimorial P₁ h) :
    |BoundingSieve.rem (s := (affinePairFullSieve M hP₁ h a b c d hz).toBoundingSieve) e| ≤
      (2 : ℝ) ^ e.primeFactors.card := by
  have hsq := (rangePrimorial_squarefree P₁ h).squarefree_of_dvd he
  change |BoundingSieve.multSum (s := (affinePairFullSieve M hP₁ h a b c d hz).toBoundingSieve) e -
    pairNu ((affinePairDiscriminant a b c d).natAbs * a * b) e * M| ≤ _
  rw [affinePairFullSieve_multSum M hP₁ h ha hb c d hz e,
    affinePair_rootDensity_primeAnchors he hab hc hd hhc hhd]
  exact (affinePair_residue_error_le (Nat.pos_of_ne_zero hsq.ne_zero) M a b c d).trans
    (affinePairRootCount_primeAnchors_le he hab hc hd hhc hhd)

/-- The literal affine sieve has exactly the complete corpus pair denominator at the
extended discriminant. No slope prime has been removed. -/
theorem affinePairFullSieve_boundingSum_eq (M : ℕ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁)
    (h a b c d : ℕ) {z : ℝ} (hz : 1 ≤ z) :
    SelbergSieve.selbergBoundingSum (affinePairFullSieve M hP₁ h a b c d hz) =
      SelbergSieve.selbergBoundingSum
        (roughPairSieve (M : ℝ) hP₁ h ((affinePairDiscriminant a b c d).natAbs * a * b) hz) := rfl

private theorem affinePairFullSieve_siftedSum (M : ℕ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) (h : ℕ)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (c d : ℕ) {z : ℝ} (hz : 1 ≤ z) :
    BoundingSieve.siftedSum (s := (affinePairFullSieve M hP₁ h a b c d hz).toBoundingSieve) =
      (((Icc 1 M).filter (fun n => Nat.Coprime (rangePrimorial P₁ h)
        (affinePairProduct a b c d n))).card : ℝ) := by
  classical
  have hi : Set.InjOn (affinePairProduct a b c d) ((Icc 1 M : Finset ℕ) : Set ℕ) :=
    (affinePairProduct_injOn ha hb c d).mono (fun _ hn => (mem_Icc.mp hn).1)
  change (∑ v ∈ (Icc 1 M).image (affinePairProduct a b c d),
    if Nat.Coprime (rangePrimorial P₁ h) v then (1 : ℝ) else 0) = _
  rw [sum_image hi, sum_boole]

/-- Complete rough affine count at prime anchors, using every sifting prime. -/
theorem card_roughAffinePair_full_le (M : ℕ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) (h : ℕ)
    {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hc : c.Prime) (hd : d.Prime) (hhc : h < c) (hhd : h < d) {z : ℝ} (hz : 1 ≤ z) :
    (((Icc 1 M).filter (fun n => Nat.Coprime (rangePrimorial P₁ h)
      (affinePairProduct a b c d n))).card : ℝ) ≤
      (M : ℝ) / SelbergSieve.selbergBoundingSum
        (roughPairSieve (M : ℝ) hP₁ h ((affinePairDiscriminant a b c d).natAbs * a * b) hz) +
      ∑ e ∈ (rangePrimorial P₁ h).divisors,
        if (e : ℝ) ≤ z then (6 : ℝ) ^ e.primeFactors.card else 0 := by
  have hbnd := SelbergSieve.selberg_bound_simple (affinePairFullSieve M hP₁ h a b c d hz)
  rw [affinePairFullSieve_siftedSum M hP₁ h ha hb c d hz,
    affinePairFullSieve_boundingSum_eq] at hbnd
  apply hbnd.trans
  apply add_le_add le_rfl
  apply sum_le_sum
  intro e he
  have hr := affinePairFullSieve_remainder_le M hP₁ h ha hb hab hc hd hhc hhd hz
    (Nat.mem_divisors.mp he).1
  change (if (e : ℝ) ≤ z then (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors e *
    |BoundingSieve.rem (s := (affinePairFullSieve M hP₁ h a b c d hz).toBoundingSieve) e| else 0) ≤ _
  simp only [cardDistinctFactors_eq]
  split_ifs
  · calc
      _ ≤ (3 : ℝ) ^ e.primeFactors.card * (2 : ℝ) ^ e.primeFactors.card :=
        mul_le_mul_of_nonneg_left hr (by positivity)
      _ = _ := by rw [← mul_pow]; norm_num
  · rfl

/-- Full affine prime-pair count. Prime anchors discharge the actual slope-prime
conditions rather than deleting those primes from the sieve. -/
theorem card_primeAffinePair_full_le (M : ℕ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) (h : ℕ)
    {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hc : c.Prime) (hd : d.Prime) (hhc : h < c) (hhd : h < d) {z : ℝ} (hz : 1 ≤ z) :
    (((Icc 1 M).filter (fun n => (a * n + c).Prime ∧ (b * n + d).Prime ∧
      h < a * n + c ∧ h < b * n + d)).card : ℝ) ≤
      (M : ℝ) / SelbergSieve.selbergBoundingSum
        (roughPairSieve (M : ℝ) hP₁ h ((affinePairDiscriminant a b c d).natAbs * a * b) hz) +
      ∑ e ∈ (rangePrimorial P₁ h).divisors,
        if (e : ℝ) ≤ z then (6 : ℝ) ^ e.primeFactors.card else 0 := by
  apply le_trans _ (card_roughAffinePair_full_le M hP₁ h ha hb hab hc hd hhc hhd hz)
  apply Nat.cast_le.mpr
  apply card_le_card
  intro n hn
  rw [mem_filter] at hn ⊢
  refine ⟨hn.1, ?_⟩
  apply Nat.coprime_prod_left_iff.mpr
  intro p hp
  apply (rangePrimes_prime hp).coprime_iff_not_dvd.mpr
  intro hdiv
  rcases (rangePrimes_prime hp).dvd_mul.mp hdiv with h1 | h2
  · exact not_dvd_of_prime_lt hn.2.1 hn.2.2.2.1 hp h1
  · exact not_dvd_of_prime_lt hn.2.2.1 hn.2.2.2.2 hp h2

/-- Source Mertens/Rankin denominator for the actual full affine count, including
both slope and discriminant singular factors and the entire finite remainder. -/
theorem card_primeAffinePair_full_mertens_le (M : ℕ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) {h : ℕ}
    {a b c d : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : Nat.Coprime a b)
    (hc : c.Prime) (hd : d.Prime) (hhc : h < c) (hhd : h < d) {z : ℝ} (hz : 1 ≤ z)
    (hh2 : 2 ≤ h) (hP₁h : P₁ ≤ h) (hlev : (h : ℝ) ^ (18 : ℝ) ≤ Real.sqrt z)
    (hlog : 20 * mertensFirstConst ≤ Real.log h) :
    (((Icc 1 M).filter (fun n => (a * n + c).Prime ∧ (b * n + d).Prime ∧
      h < a * n + c ∧ h < b * n + d)).card : ℝ) ≤
      (M : ℝ) / ((1 / 2) * (Real.exp (mertensS h - mertensS P₁) ^ (2 : ℕ) *
        ∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ (affinePairDiscriminant a b c d).natAbs * a * b),
          (((p : ℝ) - 1) / p))) +
      ∑ e ∈ (rangePrimorial P₁ h).divisors,
        if (e : ℝ) ≤ z then (6 : ℝ) ^ e.primeFactors.card else 0 := by
  have hbase := card_primeAffinePair_full_le M hP₁ h ha hb hab hc hd hhc hhd hz
  apply hbase.trans
  apply add_le_add _ le_rfl
  have hprod : 0 < ∏ p ∈ (rangePrimes P₁ h).filter
      (fun p => p ∣ (affinePairDiscriminant a b c d).natAbs * a * b), (((p : ℝ) - 1) / p) := by
    apply prod_pos
    intro p hp
    have hpp := rangePrimes_prime (mem_filter.mp hp).1
    have hp1 : (1 : ℝ) < p := by exact_mod_cast hpp.one_lt
    exact div_pos (by linarith) (by linarith)
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg M) (by positivity)
    (selbergBoundingSum_ge_mertens_sharp (M : ℝ) hP₁ _ hz hh2 hP₁h hlev hlog)


/-- Every actual primitive dilation pair obeys the full affine sieve, with all
slope primes retained through the parameter abs(v)*A*B. -/
theorem card_primeDilationPairs_full_le (P Q : ℕ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) (h : ℕ)
    {A B : ℕ} (hA : 0 < A) (hB : 0 < B) (hcop : A.Coprime B) (v : ℤ)
    {z : ℝ} (hz : 1 ≤ z) :
    ((primeDilationPairs P Q A B h v).card : ℝ) ≤
      1 + (P / B : ℕ) / SelbergSieve.selbergBoundingSum
        (roughPairSieve (P / B : ℕ) hP₁ h (v.natAbs * A * B) hz) +
      ∑ e ∈ (rangePrimorial P₁ h).divisors,
        if (e : ℝ) ≤ z then (6 : ℝ) ^ e.primeFactors.card else 0 := by
  classical
  by_cases hne : (primeDilationPairs P Q A B h v).Nonempty
  · obtain ⟨x₀, hx₀, hcard⟩ := exists_primeDilationPairs_anchor_bound P Q A B h hB hcop v hne
    have hx := (mem_filter.mp hx₀).2
    have hb := card_primeAffinePair_full_le (P / B) hP₁ h hB hA hcop.symm
      hx.1 hx.2.1 hx.2.2.1 hx.2.2.2.1 hz
    have hdisc : affinePairDiscriminant B A x₀.1 x₀.2 = -v := by
      unfold affinePairDiscriminant
      linarith only [hx.2.2.2.2]
    have hD : (affinePairDiscriminant B A x₀.1 x₀.2).natAbs * B * A = v.natAbs * A * B := by
      rw [hdisc, Int.natAbs_neg]
      ring
    rw [hD] at hb
    exact hcard.trans (by linarith only [hb])
  · have hS := not_nonempty_iff_eq_empty.mp hne
    rw [hS, card_empty, Nat.cast_zero]
    have hden := SelbergSieve.selbergBoundingSum_pos (roughPairSieve (P / B : ℕ) hP₁ h (v.natAbs * A * B) hz)
    positivity

/-- Full Mertens denominator for literal dilation-pair counts, with all slope and
shift singular factors, the anchor and every finite-level remainder retained. -/
theorem card_primeDilationPairs_full_mertens_le (P Q : ℕ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) {h : ℕ}
    {A B : ℕ} (hA : 0 < A) (hB : 0 < B) (hcop : A.Coprime B) (v : ℤ)
    {z : ℝ} (hz : 1 ≤ z) (hh2 : 2 ≤ h) (hP₁h : P₁ ≤ h)
    (hlev : (h : ℝ) ^ (18 : ℝ) ≤ Real.sqrt z)
    (hlog : 20 * mertensFirstConst ≤ Real.log h) :
    ((primeDilationPairs P Q A B h v).card : ℝ) ≤
      1 + (P / B : ℕ) / ((1 / 2) * (Real.exp (mertensS h - mertensS P₁) ^ (2 : ℕ) *
        ∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ v.natAbs * A * B), (((p : ℝ) - 1) / p))) +
      ∑ e ∈ (rangePrimorial P₁ h).divisors,
        if (e : ℝ) ≤ z then (6 : ℝ) ^ e.primeFactors.card else 0 := by
  apply (card_primeDilationPairs_full_le P Q hP₁ h hA hB hcop v hz).trans
  apply add_le_add _ le_rfl
  apply add_le_add le_rfl
  have hprod : 0 < ∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ v.natAbs * A * B),
      (((p : ℝ) - 1) / p) := by
    apply prod_pos
    intro p hp
    have hp1 : (1 : ℝ) < p := by exact_mod_cast (rangePrimes_prime (mem_filter.mp hp).1).one_lt
    exact div_pos (by linarith) (by linarith)
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg (P / B)) (by positivity)
    (selbergBoundingSum_ge_mertens_sharp (P / B : ℕ) hP₁ _ hz hh2 hP₁h hlev hlog)

/-- Gcd reduction carries the full source denominator to every compatible shift
of arbitrary positive dilation slopes. -/
theorem card_primeDilationPairs_gcd_full_mertens_le (P Q : ℕ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) {h : ℕ}
    {A B : ℕ} (hA : 0 < A) (hB : 0 < B) (w : ℤ) {z : ℝ} (hz : 1 ≤ z)
    (hh2 : 2 ≤ h) (hP₁h : P₁ ≤ h) (hlev : (h : ℝ) ^ (18 : ℝ) ≤ Real.sqrt z)
    (hlog : 20 * mertensFirstConst ≤ Real.log h) :
    let a := A / Nat.gcd A B
    let b := B / Nat.gcd A B
    ((primeDilationPairs P Q A B h ((Nat.gcd A B : ℤ) * w)).card : ℝ) ≤
      1 + (P / b : ℕ) / ((1 / 2) * (Real.exp (mertensS h - mertensS P₁) ^ (2 : ℕ) *
        ∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ w.natAbs * a * b), (((p : ℝ) - 1) / p))) +
      ∑ e ∈ (rangePrimorial P₁ h).divisors,
        if (e : ℝ) ≤ z then (6 : ℝ) ^ e.primeFactors.card else 0 := by
  dsimp only
  have hg : 0 < Nat.gcd A B := Nat.gcd_pos_of_pos_left B hA
  have ha : 0 < A / Nat.gcd A B := Nat.div_pos (Nat.gcd_le_left B hA) hg
  have hb : 0 < B / Nat.gcd A B := Nat.div_pos (Nat.gcd_le_right A hB) hg
  rw [primeDilationPairs_gcd_eq P Q hA h w]
  exact card_primeDilationPairs_full_mertens_le P Q hP₁ ha hb
    (Nat.coprime_div_gcd_div_gcd hg) w hz hh2 hP₁h hlev hlog

/-- A sifting prime dividing a slope and the reduced signed shift forbids an
actual pair of primes above the sifting range. -/
theorem primeDilationPairs_eq_empty_of_slope_prime
    (P Q h : ℕ) {A B p : ℕ} (hcop : A.Coprime B) (hp : p.Prime) (hph : p ≤ h)
    (hpAB : p ∣ A * B) {v : ℤ} (hpv : (p : ℤ) ∣ v) :
    primeDilationPairs P Q A B h v = ∅ := by
  apply eq_empty_iff_forall_notMem.mpr
  intro x hx
  have hx' := (mem_filter.mp hx).2
  have hnA : ¬ p ∣ x.1 := by
    intro hd
    have he := (Nat.prime_dvd_prime_iff_eq hp hx'.1).mp hd
    omega
  have hnB : ¬ p ∣ x.2 := by
    intro hd
    have he := (Nat.prime_dvd_prime_iff_eq hp hx'.2.1).mp hd
    omega
  rcases hp.dvd_mul.mp hpAB with hpa | hpb
  · have hpB : ¬ p ∣ B := by
      intro hpb
      have hd := Nat.dvd_gcd hpa hpb
      rw [hcop.gcd_eq_one] at hd
      exact hp.not_dvd_one hd
    have hdiv : (p : ℤ) ∣ (B : ℤ) * x.2 := by
      have hA : (p : ℤ) ∣ (A : ℤ) := Int.natCast_dvd_natCast.mpr hpa
      have hh := dvd_sub (dvd_mul_of_dvd_left hA (x.1 : ℤ)) hpv
      have he : (A : ℤ) * x.1 - v = B * x.2 := by linarith only [hx'.2.2.2.2]
      rwa [he] at hh
    have hnat : p ∣ B * x.2 := Int.natCast_dvd_natCast.mp (by simpa only [Nat.cast_mul] using hdiv)
    exact (hp.dvd_mul.mp hnat).elim hpB hnB
  · have hpA : ¬ p ∣ A := by
      intro hpa
      have hd := Nat.dvd_gcd hpa hpb
      rw [hcop.gcd_eq_one] at hd
      exact hp.not_dvd_one hd
    have hdiv : (p : ℤ) ∣ (A : ℤ) * x.1 := by
      have hB : (p : ℤ) ∣ (B : ℤ) := Int.natCast_dvd_natCast.mpr hpb
      have hh := dvd_add hpv (dvd_mul_of_dvd_left hB (x.2 : ℤ))
      have he : v + (B : ℤ) * x.2 = A * x.1 := by linarith only [hx'.2.2.2.2]
      rwa [he] at hh
    have hnat : p ∣ A * x.1 := Int.natCast_dvd_natCast.mp (by simpa only [Nat.cast_mul] using hdiv)
    exact (hp.dvd_mul.mp hnat).elim hpA hnA

/-- The literal free-prime threshold can exceed the sifting cutoff. The full
dilation estimate keeps these two scales distinct. -/
theorem card_primeDilationPairs_gcd_sift_le (P Q Y : ℕ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) {h : ℕ}
    (hhY : h ≤ Y) {A B : ℕ} (hA : 0 < A) (hB : 0 < B) (w : ℤ) {z : ℝ} (hz : 1 ≤ z)
    (hh2 : 2 ≤ h) (hP₁h : P₁ ≤ h) (hlev : (h : ℝ) ^ (18 : ℝ) ≤ Real.sqrt z)
    (hlog : 20 * mertensFirstConst ≤ Real.log h) :
    let a := A / Nat.gcd A B
    let b := B / Nat.gcd A B
    ((primeDilationPairs P Q A B Y ((Nat.gcd A B : ℤ) * w)).card : ℝ) ≤
      1 + (P / b : ℕ) / ((1 / 2) * (Real.exp (mertensS h - mertensS P₁) ^ (2 : ℕ) *
        ∏ p ∈ (rangePrimes P₁ h).filter (fun p => p ∣ w.natAbs * a * b), (((p : ℝ) - 1) / p))) +
      ∑ e ∈ (rangePrimorial P₁ h).divisors,
        if (e : ℝ) ≤ z then (6 : ℝ) ^ e.primeFactors.card else 0 := by
  dsimp only
  apply le_trans _ (card_primeDilationPairs_gcd_full_mertens_le P Q hP₁ hA hB w hz hh2 hP₁h hlev hlog)
  apply Nat.cast_le.mpr
  apply card_le_card
  intro x hx
  obtain ⟨hmem, hp, hq, hYp, hYq, heq⟩ := mem_filter.mp hx
  exact mem_filter.mpr ⟨hmem, hp, hq, hhY.trans_lt hYp, hhY.trans_lt hYq, heq⟩

end RHTower.Sieve
