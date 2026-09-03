import GaloisForLFunctions.RHTower.Sieve.MaynardZeroExponentTrimming

/-!
# Menon's degree-three Heath--Brown factor-length dichotomy

A surviving degree-three Heath--Brown box has at most six positive factors.  If its exact lower
support edge reaches `P^(7/8)`, one factor therefore has length at least `P^(1/8)`.  It is either
in the medium range through `P^(1/3)`, or is longer than the Möbius cutoff and hence is literally
a zeta or logarithm factor.  This is the algebraic Case-II split in Menon's proof.
-/

namespace RHTower.Sieve

open Finset

noncomputable section

/-- Six nonnegative factors with product at least `X^(7/8)` contain a medium or long factor. -/
theorem exists_medium_or_long_of_six_factor_product
    {ι : Type*} [Fintype ι] (f : ι → ℝ) {X : ℝ}
    (hX : 1 < X) (hcard : Fintype.card ι ≤ 6)
    (hf : ∀ i, 0 ≤ f i)
    (hprod : X ^ (7 / 8 : ℝ) ≤ ∏ i, f i) :
    (∃ i, X ^ (1 / 8 : ℝ) ≤ f i ∧ f i ≤ X ^ (1 / 3 : ℝ)) ∨
      ∃ i, X ^ (1 / 3 : ℝ) < f i := by
  classical
  by_cases hlong : ∃ i, X ^ (1 / 3 : ℝ) < f i
  · exact Or.inr hlong
  by_cases hmedium : ∃ i, X ^ (1 / 8 : ℝ) ≤ f i ∧ f i ≤ X ^ (1 / 3 : ℝ)
  · exact Or.inl hmedium
  have hsmall : ∀ i, f i < X ^ (1 / 8 : ℝ) := by
    intro i
    by_contra hi
    have hlo : X ^ (1 / 8 : ℝ) ≤ f i := le_of_not_gt hi
    have hupper : f i ≤ X ^ (1 / 3 : ℝ) := by
      exact le_of_not_gt (fun hi' => hlong ⟨i, hi'⟩)
    exact hmedium ⟨i, hlo, hupper⟩
  have hroot1 : 1 ≤ X ^ (1 / 8 : ℝ) :=
    Real.one_le_rpow hX.le (by norm_num)
  have hprodle : (∏ i, f i) ≤ (X ^ (1 / 8 : ℝ)) ^ Fintype.card ι := by
    calc
      (∏ i, f i) ≤ ∏ _i : ι, X ^ (1 / 8 : ℝ) := by
        exact Finset.prod_le_prod (fun i _ => hf i) (fun i _ => (hsmall i).le)
      _ = (X ^ (1 / 8 : ℝ)) ^ Fintype.card ι := by simp
  have hcardpow : (X ^ (1 / 8 : ℝ)) ^ Fintype.card ι ≤
      (X ^ (1 / 8 : ℝ)) ^ 6 :=
    pow_le_pow_right₀ hroot1 hcard
  have hrpow : (X ^ (1 / 8 : ℝ)) ^ 6 = X ^ (3 / 4 : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (le_trans (by norm_num) hX.le)]
    congr 1
    norm_num
  have hstrict : X ^ (3 / 4 : ℝ) < X ^ (7 / 8 : ℝ) := by
    exact (Real.strictMono_rpow_of_base_gt_one hX).lt_iff_lt.mpr (by norm_num)
  rw [hrpow] at hcardpow
  linarith

/-- A surviving degree-three Heath--Brown box has either a medium positive factor or a long
factor, once its exact lower support edge reaches `P^(7/8)`. -/
theorem exists_medium_or_long_positive_heathBrown_three
    {L X : ℕ} (box : HeathBrownBoxChoice L X 3) {P : ℝ}
    (hP : 1 < P)
    (hedge : P ^ (7 / 8 : ℝ) ≤
      (groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ)) :
    (∃ i : PositiveHeathBrownBoxFactorIndex box,
        P ^ (1 / 8 : ℝ) ≤
            ((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ) ∧
          ((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ) ≤
            P ^ (1 / 3 : ℝ)) ∨
      ∃ i : PositiveHeathBrownBoxFactorIndex box,
        P ^ (1 / 3 : ℝ) <
          ((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ) := by
  classical
  let f : PositiveHeathBrownBoxFactorIndex box → ℝ := fun i =>
    ((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)
  have hm : box.m < 3 := box.1.isLt
  have hcard : Fintype.card (PositiveHeathBrownBoxFactorIndex box) ≤ 6 := by
    calc
      Fintype.card (PositiveHeathBrownBoxFactorIndex box) ≤
          Fintype.card (HeathBrownBoxFactorIndex 3 box.m) :=
        Fintype.card_subtype_le _
      _ = 2 * (3 - box.m) := card_heathBrownBoxFactorIndex hm
      _ ≤ 6 := by omega
  have hf : ∀ i, 0 ≤ f i := by
    intro i
    dsimp [f]
    positivity
  have hprod : P ^ (7 / 8 : ℝ) ≤ ∏ i, f i := by
    calc
      P ^ (7 / 8 : ℝ) ≤
          (groupedDyadicLower
            (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ) := hedge
      _ = ∏ i : PositiveHeathBrownBoxFactorIndex box, f i := by
        rw [← prod_positive_heathBrownBoxFactorLength_eq_groupedLower box]
        simp [f]
  simpa [f] using
    (exists_medium_or_long_of_six_factor_product f hP hcard hf hprod)

/-- A factor longer than the Möbius cutoff in a literal Heath--Brown box is a zeta or logarithm
factor. -/
theorem heathBrown_factorKind_eq_zeta_or_log_of_length_gt_cutoff
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k) (hL : 1 ≤ L)
    {P : ℝ} (hcut : (L : ℝ) ≤ P ^ (1 / 3 : ℝ))
    (i : HeathBrownBoxFactorIndex k box.m)
    (hlong : P ^ (1 / 3 : ℝ) <
      ((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) :
    heathBrownBoxFactorKind k box.m i = .zeta ∨
      heathBrownBoxFactorKind k box.m i = .log := by
  rcases i with i | i
  · exfalso
    have hai : box.a i ≤ Nat.log 2 L :=
      dyadicChoice_le_log box.2.2.2.2 i
    have hpowNat : 2 ^ box.a i ≤ L :=
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) hai).trans
        (Nat.pow_log_le_self 2 (by omega : L ≠ 0))
    have hpowReal : (((2 ^ box.a i : ℕ) : ℝ)) ≤ (L : ℝ) := by
      exact_mod_cast hpowNat
    exact (not_lt_of_ge (hpowReal.trans hcut)) hlong
  · rcases i with i | i
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- A factor longer than the literal Heath--Brown Mobius cutoff is necessarily a zeta or
logarithm factor.  Unlike the paper-scale corollary above, this form does not compare the cutoff
with the lower endpoint of the selected prime interval. -/
theorem heathBrown_factorKind_eq_zeta_or_log_of_length_gt_L
    {L X k : ℕ} (box : HeathBrownBoxChoice L X k) (hL : 1 ≤ L)
    (i : HeathBrownBoxFactorIndex k box.m)
    (hlong : (L : ℝ) <
      ((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ)) :
    heathBrownBoxFactorKind k box.m i = .zeta ∨
      heathBrownBoxFactorKind k box.m i = .log := by
  rcases i with i | i
  · exfalso
    have hai : box.a i ≤ Nat.log 2 L :=
      dyadicChoice_le_log box.2.2.2.2 i
    have hpowNat : 2 ^ box.a i ≤ L :=
      (Nat.pow_le_pow_right (by norm_num : 0 < 2) hai).trans
        (Nat.pow_log_le_self 2 (by omega : L ≠ 0))
    have hpowReal : (((2 ^ box.a i : ℕ) : ℝ)) ≤ (L : ℝ) := by
      exact_mod_cast hpowNat
    exact (not_lt_of_ge hpowReal) hlong
  · rcases i with i | i
    · exact Or.inl rfl
    · exact Or.inr rfl

/-- Exact degree-three factor classification at the literal Heath--Brown cutoff.  A selected
factor always has length at least `P^(1/8)`; it is either no longer than `L`, or it lies beyond
every Mobius factor and is therefore a zeta/logarithm factor. -/
theorem exists_heathBrown_three_medium_or_long_zeta_log_cutoff
    {L X : ℕ} (box : HeathBrownBoxChoice L X 3) (hL : 1 ≤ L) {P : ℝ}
    (hP : 1 < P)
    (hedge : P ^ (7 / 8 : ℝ) ≤
      (groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ)) :
    (∃ i : PositiveHeathBrownBoxFactorIndex box,
        P ^ (1 / 8 : ℝ) ≤
            ((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ) ∧
          ((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ) ≤
            (L : ℝ)) ∨
      ∃ i : PositiveHeathBrownBoxFactorIndex box,
        P ^ (1 / 8 : ℝ) ≤
            ((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ) ∧
          (L : ℝ) <
            ((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ) ∧
          (heathBrownBoxFactorKind 3 box.m i = .zeta ∨
            heathBrownBoxFactorKind 3 box.m i = .log) := by
  obtain ⟨i, hi⟩ : ∃ i : PositiveHeathBrownBoxFactorIndex box,
      P ^ (1 / 8 : ℝ) ≤
        ((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ) := by
    rcases exists_medium_or_long_positive_heathBrown_three box hP hedge with hmedium | hlong
    · exact ⟨hmedium.choose, hmedium.choose_spec.1⟩
    · have hroot : P ^ (1 / 8 : ℝ) ≤ P ^ (1 / 3 : ℝ) :=
        Real.rpow_le_rpow_of_exponent_le hP.le (by norm_num)
      exact ⟨hlong.choose, hroot.trans hlong.choose_spec.le⟩
  by_cases hshort :
      ((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ) ≤ (L : ℝ)
  · exact Or.inl ⟨i, hi, hshort⟩
  · have hlong : (L : ℝ) <
        ((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ) :=
      lt_of_not_ge hshort
    exact Or.inr ⟨i, hi, hlong,
      heathBrown_factorKind_eq_zeta_or_log_of_length_gt_L box hL i hlong⟩

/-- Exact Case-II length classification for the six factors in the degree-three packet. -/
theorem exists_heathBrown_three_medium_or_long_zeta_log
    {L X : ℕ} (box : HeathBrownBoxChoice L X 3) (hL : 1 ≤ L) {P : ℝ}
    (hP : 1 < P) (hcut : (L : ℝ) ≤ P ^ (1 / 3 : ℝ))
    (hedge : P ^ (7 / 8 : ℝ) ≤
      (groupedDyadicLower
        (heathBrownBoxFactorExponent box.a box.b box.q) : ℝ)) :
    (∃ i : PositiveHeathBrownBoxFactorIndex box,
        P ^ (1 / 8 : ℝ) ≤
            ((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ) ∧
          ((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ) ≤
            P ^ (1 / 3 : ℝ)) ∨
      ∃ i : PositiveHeathBrownBoxFactorIndex box,
        P ^ (1 / 3 : ℝ) <
            ((2 ^ heathBrownBoxFactorExponent box.a box.b box.q i : ℕ) : ℝ) ∧
          (heathBrownBoxFactorKind 3 box.m i = .zeta ∨
            heathBrownBoxFactorKind 3 box.m i = .log) := by
  rcases exists_medium_or_long_positive_heathBrown_three box hP hedge with hmedium | hlong
  · exact Or.inl hmedium
  · rcases hlong with ⟨i, hi⟩
    exact Or.inr ⟨i, hi,
      heathBrown_factorKind_eq_zeta_or_log_of_length_gt_cutoff box hL hcut i hi⟩

end

end RHTower.Sieve
