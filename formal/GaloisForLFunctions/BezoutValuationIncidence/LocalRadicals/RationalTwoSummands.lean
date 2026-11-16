import GaloisForLFunctions.RHTower.ChiRamanujanPositiveRationalTrace
import GaloisForLFunctions.HTGeometry.Arithmetic.ValuationProducts

/-!
# Two power-congruence summands for rational semilocal radicals

For finitely many rational primes, every element of the common maximal ideals
is the sum of two elements whose valuations are positive and congruent to one
modulo any prescribed integer greater than one. A prime product realizes the
valuations: choose exponent `m + 1` where the target has valuation one, and
exponent one elsewhere. The other summand always has valuation one.

This is the normalized rational case of the radical construction in
Guang Hu, *Diophantine definitions of nonsplitting for central simple algebras
over global fields*, Lemmas 6.1–6.2, https://arxiv.org/abs/2611.10924.
-/

noncomputable section
open scoped BigOperators
open GaloisForLFunctions.HTGeometry.Arithmetic RHTower.BAGTrace

namespace GaloisForLFunctions.BezoutValuationIncidence.LocalRadicals

/-- A rational realizing prescribed integer valuations on a finite prime set. -/
def prescribedRational (S : Finset Nat.Primes) (e : Nat.Primes → ℤ) : ℚ :=
  rationalOfValuations (Finsupp.onFinset S (fun p => if p ∈ S then e p else 0)
    (by intro p hp; by_contra h; exact hp (if_neg h)))

theorem prescribedRational_pos (S : Finset Nat.Primes) (e : Nat.Primes → ℤ) :
    0 < prescribedRational S e := rationalOfValuations_pos _

theorem val_prescribedRational (S : Finset Nat.Primes) (e : Nat.Primes → ℤ)
    (p : Nat.Primes) :
    padicValRat p (prescribedRational S e) = if p ∈ S then e p else 0 := by
  exact padicValRat_rationalOfValuations _ p

/-- The intersection of the maximal ideals of the selected rational valuation rings. -/
def rationalRadical (S : Finset Nat.Primes) : Set ℚ :=
  {x | x = 0 ∨ ∀ p ∈ S, 0 < padicValRat p x}

/-- Positive valuations in the residue class one, together with zero. -/
def firstValuationClass (S : Finset Nat.Primes) (m : ℕ) : Set ℚ :=
  {x | x = 0 ∨ ∀ p ∈ S, 0 < padicValRat p x ∧ (m : ℤ) ∣ padicValRat p x - 1}

theorem firstValuationClass_subset (S : Finset Nat.Primes) (m : ℕ) :
    firstValuationClass S m ⊆ rationalRadical S := by
  rintro x (rfl | hx)
  · exact Or.inl rfl
  · exact Or.inr (fun p hp => (hx p hp).1)

theorem rationalRadical_add (S : Finset Nat.Primes) {x y : ℚ}
    (hx : x ∈ rationalRadical S) (hy : y ∈ rationalRadical S) :
    x + y ∈ rationalRadical S := by
  rcases hx with rfl | hx
  · simpa only [zero_add] using hy
  rcases hy with rfl | hy
  · exact Or.inr (by simpa only [add_zero] using hx)
  by_cases hxy : x + y = 0
  · exact Or.inl hxy
  · refine Or.inr (fun p hp => ?_)
    letI : Fact (p : ℕ).Prime := ⟨p.property⟩
    exact lt_of_lt_of_le (lt_min (hx p hp) (hy p hp))
      (padicValRat.min_le_padicValRat_add hxy)

/-- Explicit noncancelling decomposition, valid also at the prime two. -/
theorem rationalRadical_two_summands (S : Finset Nat.Primes) (n : ℕ) (x : ℚ) :
    x ∈ rationalRadical S ↔ ∃ a b : ℚ,
      a ∈ firstValuationClass S (n + 2) ∧
      b ∈ firstValuationClass S (n + 2) ∧ x = a + b := by
  constructor
  · rintro (rfl | hx)
    · exact ⟨0, 0, Or.inl rfl, Or.inl rfl, (add_zero 0).symm⟩
    let e : Nat.Primes → ℤ := fun p =>
      if padicValRat p x = 1 then (n + 2 : ℕ) + 1 else 1
    let a := prescribedRational S e
    have ha0 : a ≠ 0 := (prescribedRational_pos S e).ne'
    have hav (p : Nat.Primes) (hp : p ∈ S) : padicValRat p a = e p := by
      exact (val_prescribedRational S e p).trans (if_pos hp)
    have ha : a ∈ firstValuationClass S (n + 2) := by
      refine Or.inr (fun p hp => ?_)
      rw [hav p hp]
      dsimp [e]
      split_ifs
      · exact ⟨by positivity, by simp only [add_sub_cancel_right, dvd_refl]⟩
      · exact ⟨by omega, by simp only [sub_self, dvd_zero]⟩
    have hb : x - a ∈ firstValuationClass S (n + 2) := by
      by_cases hxa : x - a = 0
      · exact Or.inl hxa
      refine Or.inr (fun p hp => ?_)
      letI : Fact (p : ℕ).Prime := ⟨p.property⟩
      have hx0 : x ≠ 0 := by
        intro h; have := hx p hp; simp [h] at this
      have hv : padicValRat p (x - a) = 1 := by
        have hpos := hx p hp
        by_cases he : padicValRat p x = 1
        · have he' : padicValRat p a = (n + 2 : ℕ) + 1 := by
            rw [hav p hp]; exact if_pos he
          rw [val_sub_eq_min hx0 ha0 (by rw [he, he']; omega), he, he']
          omega
        · have he' : padicValRat p a = 1 := by
            rw [hav p hp]; exact if_neg he
          rw [val_sub_eq_min hx0 ha0 (by rwa [he']), he']
          omega
      exact ⟨by rw [hv]; omega, by rw [hv, sub_self]; exact dvd_zero _⟩
    exact ⟨a, x - a, ha, hb, by ring⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact rationalRadical_add S
      (firstValuationClass_subset S _ ha) (firstValuationClass_subset S _ hb)

/-- Units in the intersection of the selected rational valuation rings. -/
def semilocalUnits (S : Finset Nat.Primes) : Set ℚ :=
  {u | u ≠ 0 ∧ ∀ p ∈ S, padicValRat p u = 0}

/-- Hu's power-and-unit formula with a parameter of valuation one at each selected prime. -/
def normalizedPowerClass (S : Finset Nat.Primes) (m : ℕ) : Set ℚ :=
  {x | x = 0 ∨ ∃ z u w v : ℚ,
    z ≠ 0 ∧ u ∈ semilocalUnits S ∧ w ≠ 0 ∧ v ∈ semilocalUnits S ∧
    x = prescribedRational S (fun _ => 1) * z ^ m * u ∧ 1 - x = w ^ m * v}

private theorem val_one_sub_of_pos (p : Nat.Primes) {x : ℚ}
    (hx : 0 < padicValRat p x) : padicValRat p (1 - x) = 0 := by
  letI : Fact (p : ℕ).Prime := ⟨p.property⟩
  have hx0 : x ≠ 0 := by intro h; simp [h] at hx
  rw [val_sub_eq_min one_ne_zero hx0 (by rw [padicValRat.one]; omega),
    padicValRat.one, min_eq_left hx.le]

/-- The multiplicative formula detects precisely positive valuations congruent to one.
The exclusion of one also handles the empty prime set correctly. -/
theorem normalizedPowerClass_iff (S : Finset Nat.Primes) (n : ℕ) (x : ℚ) :
    x ∈ normalizedPowerClass S (n + 2) ↔
      x ∈ firstValuationClass S (n + 2) ∧ x ≠ 1 := by
  have hm : ¬ ((n + 2 : ℕ) : ℤ) ∣ 1 := by
    intro h; have := Int.le_of_dvd (by omega : (0 : ℤ) < 1) h; omega
  have hbase0 : prescribedRational S (fun _ => 1) ≠ 0 :=
    (prescribedRational_pos S _).ne'
  have hbase (p : Nat.Primes) (hp : p ∈ S) :
      padicValRat p (prescribedRational S (fun _ => 1)) = 1 := by
    rw [val_prescribedRational, if_pos hp]
  constructor
  · rintro (rfl | ⟨z, u, w, v, hz, hu, hw, hv, he, hf⟩)
    · exact ⟨Or.inl rfl, zero_ne_one⟩
    have hx0 : x ≠ 0 := by
      rw [he]
      exact mul_ne_zero (mul_ne_zero hbase0 (pow_ne_zero _ hz)) hu.1
    have hx1 : x ≠ 1 := by
      intro h
      have hfv : w ^ (n + 2) * v ≠ 0 := mul_ne_zero (pow_ne_zero _ hw) hv.1
      exact hfv (by rw [← hf, h, sub_self])
    refine ⟨Or.inr (fun p hp => ?_), hx1⟩
    letI : Fact (p : ℕ).Prime := ⟨p.property⟩
    have hxv : padicValRat p x = 1 + (n + 2 : ℕ) * padicValRat p z := by
      rw [he, padicValRat.mul (mul_ne_zero hbase0 (pow_ne_zero _ hz)) hu.1,
        padicValRat.mul hbase0 (pow_ne_zero _ hz), hbase p hp, padicValRat.pow,
        hu.2 p hp, add_zero]
    have hfv : padicValRat p (1 - x) = (n + 2 : ℕ) * padicValRat p w := by
      rw [hf, padicValRat.mul (pow_ne_zero _ hw) hv.1, padicValRat.pow,
        hv.2 p hp, add_zero]
    have hcong : ((n + 2 : ℕ) : ℤ) ∣ padicValRat p x - 1 := by
      rw [hxv, add_sub_cancel_left]; exact dvd_mul_right _ _
    have hne : padicValRat p x ≠ 0 := by
      intro h
      have h1 := dvd_sub (dvd_zero ((n + 2 : ℕ) : ℤ)) hcong
      apply hm
      simpa only [h, zero_sub, neg_neg] using h1
    have hpos : 0 < padicValRat p x := by
      by_contra h
      have hneg : padicValRat p x < 0 := lt_of_le_of_ne (le_of_not_gt h) hne
      have hsame : padicValRat p (1 - x) = padicValRat p x := by
        rw [val_sub_eq_min one_ne_zero hx0 (by rw [padicValRat.one]; omega),
          padicValRat.one, min_eq_right hneg.le]
      have hdiv : ((n + 2 : ℕ) : ℤ) ∣ padicValRat p x :=
        ⟨padicValRat p w, hsame.symm.trans hfv⟩
      exact hm (by simpa only [sub_sub_cancel] using dvd_sub hdiv hcong)
    exact ⟨hpos, hcong⟩
  · rintro ⟨rfl | hx, hx1⟩
    · exact Or.inl rfl
    by_cases hx0 : x = 0
    · exact Or.inl hx0
    let z := prescribedRational S (fun p => (padicValRat p x - 1) / (n + 2 : ℕ))
    let b := prescribedRational S (fun _ => 1)
    have hz : z ≠ 0 := (prescribedRational_pos S _).ne'
    have hb : b ≠ 0 := hbase0
    have hden : b * z ^ (n + 2) ≠ 0 := mul_ne_zero hb (pow_ne_zero _ hz)
    refine Or.inr ⟨z, x / (b * z ^ (n + 2)), 1, 1 - x, hz,
      ⟨div_ne_zero hx0 hden, ?_⟩, one_ne_zero, ⟨sub_ne_zero.mpr (Ne.symm hx1), ?_⟩,
      ?_, by rw [one_pow, one_mul]⟩
    · intro p hp
      letI : Fact (p : ℕ).Prime := ⟨p.property⟩
      have hzv : padicValRat p z = (padicValRat p x - 1) / (n + 2 : ℕ) := by
        exact (val_prescribedRational S _ p).trans (if_pos hp)
      rw [padicValRat.div hx0 hden, padicValRat.mul hb (pow_ne_zero _ hz),
        hbase p hp, padicValRat.pow, hzv]
      have hd := Int.ediv_mul_cancel (hx p hp).2
      rw [mul_comm] at hd
      rw [hd]
      ring
    · intro p hp
      exact val_one_sub_of_pos p (hx p hp).1
    · change x = (b * z ^ (n + 2)) * (x / (b * z ^ (n + 2)))
      field_simp

/-- The uniform radical formula needs only one power class for a normalized rational parameter. -/
theorem rationalRadical_power_two_summands (S : Finset Nat.Primes) (n : ℕ) (x : ℚ) :
    x ∈ rationalRadical S ↔ ∃ a b : ℚ,
      a ∈ normalizedPowerClass S (n + 2) ∧
      b ∈ normalizedPowerClass S (n + 2) ∧ x = a + b := by
  constructor
  · intro hx
    by_cases hS : S = ∅
    · subst S
      have hc (y : ℚ) (hy : y ≠ 1) : y ∈ normalizedPowerClass ∅ (n + 2) :=
        (normalizedPowerClass_iff ∅ n y).mpr ⟨Or.inr (by simp), hy⟩
      by_cases hx3 : x = 3
      · exact ⟨3, x - 3, hc 3 (by norm_num), hc (x - 3) (by rw [hx3]; norm_num),
          by ring⟩
      · exact ⟨2, x - 2, hc 2 (by norm_num), hc (x - 2) (by
          intro h; apply hx3; linarith), by ring⟩
    · obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hS
      obtain ⟨a, b, ha, hb, hab⟩ := (rationalRadical_two_summands S n x).mp hx
      have hc (y : ℚ) (hy : y ∈ firstValuationClass S (n + 2)) :
          y ∈ normalizedPowerClass S (n + 2) := by
        apply (normalizedPowerClass_iff S n y).mpr
        refine ⟨hy, ?_⟩
        intro he
        rcases hy with rfl | hy
        · exact zero_ne_one he
        · have := (hy p hp).1
          simp only [he, padicValRat.one, lt_self_iff_false] at this
      exact ⟨a, b, hc a ha, hc b hb, hab⟩
  · rintro ⟨a, b, ha, hb, rfl⟩
    exact rationalRadical_add S
      (firstValuationClass_subset S _ ((normalizedPowerClass_iff S n a).mp ha).1)
      (firstValuationClass_subset S _ ((normalizedPowerClass_iff S n b).mp hb).1)

/-- One normalized power-class summand never suffices. For a nonempty prime
set, valuation two is the obstruction; for the empty set, the missing value is one. -/
theorem rationalRadical_requires_two_summands (S : Finset Nat.Primes) (n : ℕ) :
    ∃ x : ℚ, x ∈ rationalRadical S ∧ x ∉ normalizedPowerClass S (n + 2) := by
  by_cases hS : S = ∅
  · subst S
    refine ⟨1, Or.inr (by simp), ?_⟩
    rw [normalizedPowerClass_iff]
    simp
  · obtain ⟨p, hp⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    let x := prescribedRational S (fun _ => 2)
    have hx0 : x ≠ 0 := (prescribedRational_pos S _).ne'
    have hxv (q : Nat.Primes) (hq : q ∈ S) : padicValRat q x = 2 := by
      exact (val_prescribedRational S _ q).trans (if_pos hq)
    refine ⟨x, Or.inr (fun q hq => by rw [hxv q hq]; norm_num), ?_⟩
    intro hx
    rcases ((normalizedPowerClass_iff S n x).mp hx).1 with he | hv
    · exact hx0 he
    · have hd := (hv p hp).2
      rw [hxv p hp] at hd
      have hd' : ((n + 2 : ℕ) : ℤ) ∣ 1 := by simpa using hd
      have := Int.le_of_dvd (by omega : (0 : ℤ) < 1) hd'
      omega

#print axioms rationalRadical_two_summands
#print axioms normalizedPowerClass_iff
#print axioms rationalRadical_power_two_summands
#print axioms rationalRadical_requires_two_summands

end GaloisForLFunctions.BezoutValuationIncidence.LocalRadicals
