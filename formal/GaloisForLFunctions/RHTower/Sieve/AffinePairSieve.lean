import GaloisForLFunctions.RHTower.Sieve.PrimePairCount

/-!
# Two-affine-form prime sieve for dilation correlations

An invertible affine substitution identifies the actual product roots with the
source reducible quadratic away from slope primes. Exact residue counting supplies
the entire Selberg remainder. The resulting prime-pair bound keeps the discriminant,
every excluded slope prime and the finite level, including merged-root degeneracy.
The large-prime zero-shift diagonal is classified separately.
-/

noncomputable section
open Finset
namespace RHTower.Sieve

/-- Signed discriminant controlling coincidence of the two affine roots. -/
def affinePairDiscriminant (a b c d : ℕ) : ℤ := (a : ℤ) * d - b * c

/-- The actual two-affine-form product, without shifting away its dilation coefficients. -/
def affinePairProduct (a b c d n : ℕ) : ℕ := (a * n + c) * (b * n + d)

/-- Away from the slope primes an invertible affine substitution identifies the complete
root set with the corpus reducible quadratic, including merged roots. -/
theorem affinePair_rootCount_eq {e : ℕ} (he : 0 < e) (a b c d : ℕ)
    (hab : Nat.Coprime (a * b) e) :
    ((Finset.range e).filter (fun n => e ∣ affinePairProduct a b c d n)).card =
      quadraticCongruenceRootCountTotal e (affinePairDiscriminant a b c d) := by
  classical
  letI : NeZero e := ⟨he.ne'⟩
  let u : (ZMod e)ˣ := ZMod.unitOfCoprime (a * b) hab
  let f : ZMod e ≃ ZMod e := {
    toFun := fun x => (u : ZMod e) * x + (b : ZMod e) * c
    invFun := fun y => (↑(u⁻¹) : ZMod e) * (y - (b : ZMod e) * c)
    left_inv := by intro x; simp [← mul_assoc]
    right_inv := by intro y; simp [mul_sub, ← mul_assoc] }
  have hfactor (x : ZMod e) : f x * (f x + (affinePairDiscriminant a b c d : ZMod e)) =
      (u : ZMod e) * (((a : ZMod e) * x + c) * ((b : ZMod e) * x + d)) := by
    dsimp [f, u, affinePairDiscriminant]
    push_cast
    ring
  have hiff (x : ZMod e) : ((a : ZMod e) * x + c) * ((b : ZMod e) * x + d) = 0 ↔
      f x * (f x + (affinePairDiscriminant a b c d : ZMod e)) = 0 := by
    rw [hfactor, Units.mul_right_eq_zero]
  let E : {x : ZMod e // ((a : ZMod e) * x + c) * ((b : ZMod e) * x + d) = 0} ≃
      quadraticCongruenceRoots e (affinePairDiscriminant a b c d) := {
    toFun := fun x => ⟨f x, (hiff x).mp x.property⟩
    invFun := fun y => ⟨f.symm y.val, (hiff (f.symm y.val)).mpr (by
      rw [f.apply_symm_apply]; exact y.property)⟩
    left_inv := by intro x; apply Subtype.ext; exact f.symm_apply_apply x
    right_inv := by intro y; apply Subtype.ext; exact f.apply_symm_apply y.val }
  have hcard : ((Finset.range e).filter (fun n => e ∣ affinePairProduct a b c d n)).card =
      (Finset.univ.filter (fun x : ZMod e =>
        ((a : ZMod e) * x + c) * ((b : ZMod e) * x + d) = 0)).card := by
    refine Finset.card_nbij' (fun n => (n : ZMod e)) (fun x => x.val) ?_ ?_ ?_ ?_
    · intro n hn
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      have h := (ZMod.natCast_eq_zero_iff (affinePairProduct a b c d n) e).mpr hn.2
      simpa only [affinePairProduct, Nat.cast_mul, Nat.cast_add] using h
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and] at hx
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range]
      refine ⟨ZMod.val_lt x, (ZMod.natCast_eq_zero_iff _ _).mp ?_⟩
      simpa only [affinePairProduct, Nat.cast_mul, Nat.cast_add, ZMod.natCast_zmod_val] using hx
    · intro n hn
      simp only [Finset.mem_coe, Finset.mem_filter, Finset.mem_range] at hn
      exact ZMod.val_cast_of_lt hn.1
    · intro x _
      exact ZMod.natCast_zmod_val x
  rw [hcard, ← Fintype.card_subtype]
  rw [quadraticCongruenceRootCountTotal_of_ne_zero he.ne', quadraticCongruenceRootCount]
  exact Fintype.card_congr E

private theorem quadraticRootCount_natAbs {e : ℕ} (hsq : Squarefree e) (v : ℤ) :
    quadraticCongruenceRootCountTotal e v = quadraticCongruenceRootCountTotal e (v.natAbs : ℤ) := by
  have hp : ∀ p ∈ e.primeFactors, p ≠ 0 := fun p hp => (Nat.prime_of_mem_primeFactors hp).ne_zero
  have hc : ((e.primeFactors : Finset ℕ) : Set ℕ).Pairwise Nat.Coprime := by
    intro p hp q hq hne
    exact (Nat.coprime_primes (Nat.prime_of_mem_primeFactors hp) (Nat.prime_of_mem_primeFactors hq)).mpr hne
  have hprod := Nat.prod_primeFactors_of_squarefree hsq
  rw [← hprod, quadraticCongruenceRootCountTotal_prod e.primeFactors hc hp,
    quadraticCongruenceRootCountTotal_prod e.primeFactors hc hp]
  apply Finset.prod_congr rfl
  intro p hp
  rw [quadraticCongruenceRootCountTotal_prime (Nat.prime_of_mem_primeFactors hp),
    quadraticCongruenceRootCountTotal_prime (Nat.prime_of_mem_primeFactors hp)]
  simp only [Int.natCast_dvd, Int.natAbs_natCast]

/-- The actual affine-pair density is exactly the source multiplicative pair density. -/
theorem affinePair_rootDensity_eq {e : ℕ} (hsq : Squarefree e) (a b c d : ℕ)
    (hab : Nat.Coprime (a * b) e) :
    pairNu (affinePairDiscriminant a b c d).natAbs e =
      (((Finset.range e).filter (fun n => e ∣ affinePairProduct a b c d n)).card : ℝ) / e := by
  rw [affinePair_rootCount_eq (Nat.pos_of_ne_zero hsq.ne_zero) a b c d hab,
    quadraticRootCount_natAbs hsq]
  exact pairNu_eq_rootDensity hsq _

/-- Exact interval residue error for the actual two-affine-form product. -/
theorem affinePair_residue_error_le {e : ℕ} (he : 0 < e) (M a b c d : ℕ) :
    |(((Finset.Icc 1 M).filter (fun n => e ∣ affinePairProduct a b c d n)).card : ℝ) -
      (((Finset.range e).filter (fun n => e ∣ affinePairProduct a b c d n)).card : ℝ) / e * M| ≤
        (((Finset.range e).filter (fun n => e ∣ affinePairProduct a b c d n)).card : ℝ) := by
  classical
  let S := (Finset.range e).filter (fun n => e ∣ affinePairProduct a b c d n)
  have hc : ∀ m n : ℕ, m % e = n % e →
      (e ∣ affinePairProduct a b c d m ↔ e ∣ affinePairProduct a b c d n) := by
    intro m n hmn
    have hh : Nat.ModEq e m n := hmn
    exact (((hh.mul_left a).add_right c).mul ((hh.mul_left b).add_right d)).dvd_iff (dvd_refl e)
  have hsplit := card_filter_eq_sum_residues he M (fun n => e ∣ affinePairProduct a b c d n) hc
  have hcast : (((Finset.Icc 1 M).filter (fun n => e ∣ affinePairProduct a b c d n)).card : ℝ) =
      ∑ r ∈ S, (((Finset.Icc 1 M).filter (fun n => n % e = r)).card : ℝ) := by
    exact_mod_cast hsplit
  rw [hcast]
  change |(∑ r ∈ S, _) - (S.card : ℝ) / e * M| ≤ S.card
  have heq : (S.card : ℝ) / e * M = ∑ _r ∈ S, (M : ℝ) / e := by
    rw [Finset.sum_const, nsmul_eq_mul]
    ring
  rw [heq, ← Finset.sum_sub_distrib]
  apply (Finset.abs_sum_le_sum_abs _ _).trans
  calc
    _ ≤ ∑ _r ∈ S, (1 : ℝ) := by
      apply Finset.sum_le_sum
      intro r hr
      have hr' := (Finset.mem_filter.mp hr).1
      have hu := card_residue_class_le he M r
      have hl := card_residue_class_ge he M (Finset.mem_range.mp hr')
      rw [abs_le]
      exact ⟨by linarith only [hl], by linarith only [hu]⟩
    _ = _ := by simp

/-- Sifting primes retain the complete exclusion of primes dividing the dilation slopes. -/
def affinePairSiftingPrimes (P₁ h a b : ℕ) : Finset ℕ :=
  (rangePrimes P₁ h).filter (fun p => ¬ p ∣ a * b)

def affinePairPrimorial (P₁ h a b : ℕ) : ℕ := ∏ p ∈ affinePairSiftingPrimes P₁ h a b, p

private theorem affinePairSifting_prime {P₁ h a b p : ℕ}
    (hp : p ∈ affinePairSiftingPrimes P₁ h a b) : p.Prime :=
  rangePrimes_prime (Finset.mem_filter.mp hp).1

private theorem affinePairPrimorial_squarefree (P₁ h a b : ℕ) :
    Squarefree (affinePairPrimorial P₁ h a b) :=
  _root_.Sieve.prodDistinctPrimes_squarefree _ (fun _ hp => affinePairSifting_prime hp)

private theorem affinePairPrimorial_coprime (P₁ h a b : ℕ) :
    Nat.Coprime (a * b) (affinePairPrimorial P₁ h a b) := by
  apply Nat.coprime_prod_right_iff.mpr
  intro p hp
  exact ((affinePairSifting_prime hp).coprime_iff_not_dvd.mpr (Finset.mem_filter.mp hp).2).symm

/-- Positive affine slopes make the actual product support injective. -/
theorem affinePairProduct_injOn {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (c d : ℕ) :
    Set.InjOn (affinePairProduct a b c d) (Set.Ici 1) := by
  have hm : StrictMonoOn (affinePairProduct a b c d) (Set.Ici 1) := by
    intro m hm n _ hmn
    have h1 : a * m + c < a * n + c := Nat.add_lt_add_right (Nat.mul_lt_mul_of_pos_left hmn ha) _
    have h2 : b * m + d ≤ b * n + d := Nat.add_le_add_right (Nat.mul_le_mul_left b hmn.le) _
    have hp : 0 < b * m + d := by
      have : 0 < b * m := Nat.mul_pos hb (by change 1 ≤ m at hm; omega)
      omega
    exact Nat.mul_lt_mul_of_lt_of_le h1 h2 (hp.trans_le h2)
  exact hm.injOn

/-- Source-built Selberg sieve for two affine prime forms. -/
def affinePairSieve (M : ℕ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) (h a b c d : ℕ)
    {z : ℝ} (hz : 1 ≤ z) : SelbergSieve where
  support := (Finset.Icc 1 M).image (affinePairProduct a b c d)
  prodPrimes := affinePairPrimorial P₁ h a b
  prodPrimes_squarefree := affinePairPrimorial_squarefree P₁ h a b
  weights := fun _ => 1
  weights_nonneg := fun _ => zero_le_one
  totalMass := M
  nu := pairNu (affinePairDiscriminant a b c d).natAbs
  nu_mult := pairNu_isMultiplicative _
  nu_pos_of_prime := fun p hp _ => pairNu_pos_of_prime hp
  nu_lt_one_of_prime := fun p hp hdiv => by
    apply pairNu_lt_one_of_prime hp
    have hmem := mem_of_prime_dvd_prod (fun _ hp => affinePairSifting_prime hp) hp hdiv
    have hr := (Finset.mem_filter.mp hmem).1
    rw [rangePrimes, Finset.mem_filter, Finset.mem_Icc] at hr
    omega
  level := z
  one_le_level := hz

private theorem affinePairSieve_multSum (M : ℕ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) (h : ℕ)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (c d : ℕ) {z : ℝ} (hz : 1 ≤ z) (e : ℕ) :
    BoundingSieve.multSum (s := (affinePairSieve M hP₁ h a b c d hz).toBoundingSieve) e =
      (((Finset.Icc 1 M).filter (fun n => e ∣ affinePairProduct a b c d n)).card : ℝ) := by
  have hi : Set.InjOn (affinePairProduct a b c d) ((Finset.Icc 1 M : Finset ℕ) : Set ℕ) :=
    (affinePairProduct_injOn ha hb c d).mono (fun _ hn => (Finset.mem_Icc.mp hn).1)
  change (∑ v ∈ (Finset.Icc 1 M).image (affinePairProduct a b c d), if e ∣ v then (1 : ℝ) else 0) = _
  rw [Finset.sum_image hi, Finset.sum_boole]

/-- Complete source remainder of the affine sieve; no uniformity premise is supplied. -/
theorem affinePairSieve_remainder_le (M : ℕ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) (h : ℕ)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (c d : ℕ) {z : ℝ} (hz : 1 ≤ z)
    {e : ℕ} (he : e ∣ affinePairPrimorial P₁ h a b) :
    |BoundingSieve.rem (s := (affinePairSieve M hP₁ h a b c d hz).toBoundingSieve) e| ≤
      (2 : ℝ) ^ e.primeFactors.card := by
  have hsq := (affinePairPrimorial_squarefree P₁ h a b).squarefree_of_dvd he
  have he0 : 0 < e := Nat.pos_of_ne_zero hsq.ne_zero
  have hcop := (affinePairPrimorial_coprime P₁ h a b).coprime_dvd_right he
  change |BoundingSieve.multSum (s := (affinePairSieve M hP₁ h a b c d hz).toBoundingSieve) e -
    pairNu (affinePairDiscriminant a b c d).natAbs e * M| ≤ _
  rw [affinePairSieve_multSum M hP₁ h ha hb c d hz e, affinePair_rootDensity_eq hsq a b c d hcop]
  apply (affinePair_residue_error_le he0 M a b c d).trans
  rw [affinePair_rootCount_eq he0 a b c d hcop, quadraticRootCount_natAbs hsq]
  exact rootCount_le_two_pow hsq _

/-- The exact finite Selberg denominator, retaining every excluded slope prime. -/
def affinePairBoundingSum (P₁ h a b c d : ℕ) (z : ℝ) : ℝ :=
  ∑ e ∈ (affinePairPrimorial P₁ h a b).divisors, if (e : ℝ) ^ 2 ≤ z then
    ∏ p ∈ e.primeFactors, pairClassCount (affinePairDiscriminant a b c d).natAbs p /
      ((p : ℝ) - pairClassCount (affinePairDiscriminant a b c d).natAbs p) else 0

private theorem affinePairSieve_boundingSum_eq (M : ℕ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁)
    (h a b c d : ℕ) {z : ℝ} (hz : 1 ≤ z) :
    SelbergSieve.selbergBoundingSum (affinePairSieve M hP₁ h a b c d hz) =
      affinePairBoundingSum P₁ h a b c d z := by
  classical
  apply Finset.sum_congr rfl
  intro e he
  have hediv := (Nat.mem_divisors.mp he).1
  have hesq := (affinePairPrimorial_squarefree P₁ h a b).squarefree_of_dvd hediv
  have hsub : affinePairPrimorial P₁ h a b ∣ rangePrimorial P₁ h := by
    exact Finset.prod_dvd_prod_of_subset _ _ _ (Finset.filter_subset _ _)
  change (if (e : ℝ) ^ 2 ≤ z then _ else 0) = (if (e : ℝ) ^ 2 ≤ z then _ else 0)
  split_ifs
  · calc
      _ = SelbergSieve.selbergTerms
          (roughPairSieve (M : ℝ) hP₁ h (affinePairDiscriminant a b c d).natAbs hz).toBoundingSieve e := by
        simp only [SelbergSieve.selbergTerms_apply]
        rfl
      _ = _ := selbergTerms_roughPairSieve (M : ℝ) hP₁ h _ hz (hediv.trans hsub) hesq.ne_zero
  · rfl

/-- The actual affine denominator is positive for every admissible finite sieve level. -/
theorem affinePairBoundingSum_pos {P₁ : ℕ} (hP₁ : 2 ≤ P₁) (h a b c d : ℕ)
    {z : ℝ} (hz : 1 ≤ z) : 0 < affinePairBoundingSum P₁ h a b c d z := by
  rw [← affinePairSieve_boundingSum_eq 0 hP₁ h a b c d hz]
  exact SelbergSieve.selbergBoundingSum_pos _

private theorem affinePairSieve_siftedSum (M : ℕ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) (h : ℕ)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (c d : ℕ) {z : ℝ} (hz : 1 ≤ z) :
    BoundingSieve.siftedSum (s := (affinePairSieve M hP₁ h a b c d hz).toBoundingSieve) =
      (((Finset.Icc 1 M).filter (fun n => Nat.Coprime (affinePairPrimorial P₁ h a b)
        (affinePairProduct a b c d n))).card : ℝ) := by
  classical
  have hi : Set.InjOn (affinePairProduct a b c d) ((Finset.Icc 1 M : Finset ℕ) : Set ℕ) :=
    (affinePairProduct_injOn ha hb c d).mono (fun _ hn => (Finset.mem_Icc.mp hn).1)
  change (∑ v ∈ (Finset.Icc 1 M).image (affinePairProduct a b c d),
    if Nat.Coprime (affinePairPrimorial P₁ h a b) v then (1 : ℝ) else 0) = _
  rw [Finset.sum_image hi, Finset.sum_boole]

/-- The complete two-affine rough-pair sieve, with exact density and its entire finite remainder. -/
theorem card_roughAffinePair_le (M : ℕ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) (h : ℕ)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (c d : ℕ) {z : ℝ} (hz : 1 ≤ z) :
    (((Finset.Icc 1 M).filter (fun n => Nat.Coprime (affinePairPrimorial P₁ h a b)
      (affinePairProduct a b c d n))).card : ℝ) ≤
      (M : ℝ) / affinePairBoundingSum P₁ h a b c d z +
        ∑ e ∈ (affinePairPrimorial P₁ h a b).divisors,
          if (e : ℝ) ≤ z then (6 : ℝ) ^ e.primeFactors.card else 0 := by
  have hbnd := SelbergSieve.selberg_bound_simple (affinePairSieve M hP₁ h a b c d hz)
  rw [affinePairSieve_siftedSum M hP₁ h ha hb c d hz,
    affinePairSieve_boundingSum_eq M hP₁ h a b c d hz] at hbnd
  apply hbnd.trans
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro e he
  have hr := affinePairSieve_remainder_le M hP₁ h ha hb c d hz (Nat.mem_divisors.mp he).1
  change (if (e : ℝ) ≤ z then (3 : ℝ) ^ ArithmeticFunction.cardDistinctFactors e *
    |BoundingSieve.rem (s := (affinePairSieve M hP₁ h a b c d hz).toBoundingSieve) e| else 0) ≤ _
  simp only [cardDistinctFactors_eq]
  split_ifs
  · calc
      _ ≤ (3 : ℝ) ^ e.primeFactors.card * (2 : ℝ) ^ e.primeFactors.card :=
        mul_le_mul_of_nonneg_left hr (by positivity)
      _ = _ := by rw [← mul_pow]; norm_num
  · rfl

/-- Actual affine prime-pair count. Dilation slope primes remain explicitly excluded,
and the merged-root law uses the exact signed discriminant. -/
theorem card_primeAffinePair_le (M : ℕ) {P₁ : ℕ} (hP₁ : 2 ≤ P₁) (h : ℕ)
    {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (c d : ℕ) {z : ℝ} (hz : 1 ≤ z) :
    (((Finset.Icc 1 M).filter (fun n => (a * n + c).Prime ∧ (b * n + d).Prime ∧
      h < a * n + c ∧ h < b * n + d)).card : ℝ) ≤
      (M : ℝ) / affinePairBoundingSum P₁ h a b c d z +
        ∑ e ∈ (affinePairPrimorial P₁ h a b).divisors,
          if (e : ℝ) ≤ z then (6 : ℝ) ^ e.primeFactors.card else 0 := by
  apply le_trans _ (card_roughAffinePair_le M hP₁ h ha hb c d hz)
  apply Nat.cast_le.mpr
  apply Finset.card_le_card
  intro n hn
  rw [Finset.mem_filter] at hn ⊢
  refine ⟨hn.1, ?_⟩
  apply Nat.coprime_prod_left_iff.mpr
  intro p hp
  have hp' := (Finset.mem_filter.mp hp).1
  apply (affinePairSifting_prime hp).coprime_iff_not_dvd.mpr
  intro hdvd
  rcases (affinePairSifting_prime hp).dvd_mul.mp hdvd with h1 | h2
  · exact not_dvd_of_prime_lt hn.2.1 hn.2.2.2.1 hp' h1
  · exact not_dvd_of_prime_lt hn.2.2.1 hn.2.2.2.2 hp' h2

/-- The zero-shift large-prime dilation diagonal keeps exactly equal cofactors and equal primes. -/
theorem largePrime_dilation_diagonal_iff {A B p q : ℕ} (hB : 0 < B)
    (hp : p.Prime) (hq : q.Prime) (hBp : B < p) :
    A * p = B * q ↔ A = B ∧ p = q := by
  constructor
  · intro heq
    have hdiv : p ∣ B * q := heq ▸ dvd_mul_left p A
    have hpq : p = q := by
      rcases hp.dvd_mul.mp hdiv with h1 | h2
      · exact (Nat.not_dvd_of_pos_of_lt hB hBp h1).elim
      · exact (Nat.prime_dvd_prime_iff_eq hp hq).mp h2
    refine ⟨?_, hpq⟩
    rw [← hpq] at heq
    exact Nat.eq_of_mul_eq_mul_right hp.pos heq
  · rintro ⟨rfl, rfl⟩
    rfl

end RHTower.Sieve
