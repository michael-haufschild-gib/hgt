import GaloisForLFunctions.RHTower.Sieve.MaynardSelectionLabels

/-!
# Canonical all-short cutoff for Heath--Brown Möbius factors

The apparent long-Möbius branch in Route T is absent from the literal finite Heath--Brown packet.
At packet degree `60`, choose the Möbius cutoff at the all-short boundary
`L = floor (T0^(2t))`.  If the ambient analytic cutoff satisfies `X <= T0^(120t)`, this one choice
both reaches the exact Heath--Brown identity range `X < (L+1)^(60 : ℕ)` and makes every Möbius dyadic
atom have logarithmic length at most `2t`.

This is an algebraic classification, not a Möbius-cancellation estimate.  Consequently every
factor violating the all-short admission is necessarily a zeta or logarithm factor.
-/

noncomputable section

namespace RHTower.Sieve

open Finset ArithmeticFunction

/-- Compare an exact dyadic logarithmic exponent by comparing its represented length. -/
theorem dyadicLogExponent_le_of_pow_le_rpow
    {T0 t : ℝ} (hT0 : 1 < T0) {q : ℕ}
    (hpow : (((2 ^ q : ℕ) : ℝ)) ≤ T0 ^ (2 * t)) :
    dyadicLogExponent T0 q ≤ 2 * t := by
  rw [← rpow_dyadicLogExponent hT0 q] at hpow
  exact (Real.strictMono_rpow_of_base_gt_one hT0).le_iff_le.mp hpow

/-- A coordinate of an admissible dyadic tuple is at most the support's binary logarithm. -/
theorem dyadicChoice_le_log
    {r L : ℕ} {a : Fin r → ℕ} (ha : a ∈ dyadicChoiceSet r L) (i : Fin r) :
    a i ≤ Nat.log 2 L := by
  have hi : a i ∈ Finset.range (Nat.log 2 L + 1) := by
    exact Fintype.mem_piFinset.mp ha i
  simp only [Finset.mem_range] at hi
  omega

/-- Every Möbius dyadic atom is all-short once the sharp cutoff itself is all-short. -/
theorem moebius_dyadicLogExponent_le
    {T0 t : ℝ} (hT0 : 1 < T0) {L r : ℕ} (hL : 1 ≤ L)
    (hcut : (L : ℝ) ≤ T0 ^ (2 * t))
    {a : Fin r → ℕ} (ha : a ∈ dyadicChoiceSet r L) (i : Fin r) :
    dyadicLogExponent T0 (a i) ≤ 2 * t := by
  apply dyadicLogExponent_le_of_pow_le_rpow hT0
  have hpowNat : 2 ^ a i ≤ L :=
    (Nat.pow_le_pow_right (by norm_num : 0 < 2)
      (dyadicChoice_le_log ha i)).trans (Nat.pow_log_le_self 2 (by omega : L ≠ 0))
  have hpowReal : (((2 ^ a i : ℕ) : ℝ)) ≤ (L : ℝ) := by exact_mod_cast hpowNat
  exact hpowReal.trans hcut

/-- Canonical cutoff placed exactly at the Route-T all-short boundary. -/
def maynardMoebiusCutoff (T0 t : ℝ) : ℕ :=
  ⌊T0 ^ (2 * t)⌋₊

/-- The canonical cutoff is simultaneously large enough for the degree-`60` Heath--Brown
identity and small enough for all-short grouping. -/
theorem exists_maynardMoebiusCutoff_sixty
    {T0 t : ℝ} (hT0 : 1 < T0) (ht : 0 ≤ t) {X : ℕ}
    (hX : (X : ℝ) ≤ T0 ^ (120 * t)) :
    ∃ L : ℕ, 1 ≤ L ∧ X < (L + 1) ^ 60 ∧ (L : ℝ) ≤ T0 ^ (2 * t) := by
  let root : ℝ := T0 ^ (2 * t)
  let L : ℕ := maynardMoebiusCutoff T0 t
  have hroot1 : (1 : ℝ) ≤ root := by
    dsimp [root]
    exact Real.one_le_rpow hT0.le (by linarith)
  have hL1 : 1 ≤ L := by
    dsimp [L, maynardMoebiusCutoff]
    apply Nat.le_floor
    simpa [root] using hroot1
  have hLroot : (L : ℝ) ≤ root := by
    dsimp [L, maynardMoebiusCutoff]
    exact Nat.floor_le (by positivity)
  have hrootlt : root < (L : ℝ) + 1 := by
    dsimp [L, maynardMoebiusCutoff]
    exact Nat.lt_floor_add_one root
  have hrootpow : root ^ 60 = T0 ^ (120 * t) := by
    dsimp [root]
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by linarith : 0 ≤ T0)]
    congr 1
    ring
  have hpw : root ^ 60 < ((L : ℝ) + 1) ^ 60 :=
    pow_lt_pow_left₀ hrootlt (by positivity) (by norm_num)
  have hXLreal : (X : ℝ) < ((L : ℝ) + 1) ^ 60 := by
    rw [hrootpow] at hpw
    exact hX.trans_lt hpw
  have hXL : X < (L + 1) ^ 60 := by
    exact_mod_cast hXLreal
  exact ⟨L, hL1, hXL, hLroot⟩

/-- Literal heterogeneous-box form: any factor tagged Möbius obeys all-short admission. -/
theorem heathBrown_moebius_factor_dyadicLogExponent_le
    {T0 t : ℝ} (hT0 : 1 < T0) {L k m : ℕ} (hL : 1 ≤ L)
    (hcut : (L : ℝ) ≤ T0 ^ (2 * t))
    {a : Fin (k - m) → ℕ} (ha : a ∈ dyadicChoiceSet (k - m) L)
    (b : Fin (k - m - 1) → ℕ) (q : ℕ)
    (i : HeathBrownBoxFactorIndex k m)
    (hi : heathBrownBoxFactorKind k m i = .moebius) :
    dyadicLogExponent T0 (heathBrownBoxFactorExponent a b q i) ≤ 2 * t := by
  rcases i with i | i
  · exact moebius_dyadicLogExponent_le hT0 hL hcut ha i
  · rcases i with i | i <;> simp [heathBrownBoxFactorKind] at hi

/-- Box-choice specialization of Möbius all-short admission. -/
theorem HeathBrownBoxChoice.moebius_factor_dyadicLogExponent_le
    {T0 t : ℝ} (hT0 : 1 < T0) {L X k : ℕ} (hL : 1 ≤ L)
    (hcut : (L : ℝ) ≤ T0 ^ (2 * t)) (c : HeathBrownBoxChoice L X k)
    (i : HeathBrownBoxFactorIndex k c.m)
    (hi : heathBrownBoxFactorKind k c.m i = .moebius) :
    dyadicLogExponent T0
      (heathBrownBoxFactorExponent c.a c.b c.q i) ≤ 2 * t := by
  exact heathBrown_moebius_factor_dyadicLogExponent_le hT0 hL hcut
    c.2.2.2.2 c.b c.q i hi

/-- With Möbius atoms certified all-short, every factor above the threshold is literally zeta or
logarithm.  This is the exact three-kind classification needed before the derivative-test branch. -/
theorem heathBrown_factorKind_eq_zeta_or_log_of_long
    {L X k : ℕ} {T0 t : ℝ} (c : HeathBrownBoxChoice L X k)
    (hmobius : ∀ i : HeathBrownBoxFactorIndex k c.m,
      heathBrownBoxFactorKind k c.m i = .moebius →
        dyadicLogExponent T0
          (heathBrownBoxFactorExponent c.a c.b c.q i) ≤ 2 * t)
    (i : HeathBrownBoxFactorIndex k c.m)
    (hlong : 2 * t < dyadicLogExponent T0
      (heathBrownBoxFactorExponent c.a c.b c.q i)) :
    heathBrownBoxFactorKind k c.m i = .zeta ∨
      heathBrownBoxFactorKind k c.m i = .log := by
  cases hkind : heathBrownBoxFactorKind k c.m i with
  | moebius => exact (not_le_of_gt hlong (hmobius i hkind)).elim
  | zeta => exact Or.inl rfl
  | log => exact Or.inr rfl

/-- **No long-Möbius classification at degree `60`.**  One canonical cutoff supplies both the
exact identity hypothesis and all-shortness of every Möbius coordinate in every literal box. -/
theorem exists_sixty_cutoff_all_moebius_factors_short
    {T0 t : ℝ} (hT0 : 1 < T0) (ht : 0 ≤ t) {X : ℕ}
    (hX : (X : ℝ) ≤ T0 ^ (120 * t)) :
    ∃ L : ℕ, 1 ≤ L ∧ X < (L + 1) ^ 60 ∧
      ∀ c : HeathBrownBoxChoice L X 60,
        ∀ i : HeathBrownBoxFactorIndex 60 c.m,
          heathBrownBoxFactorKind 60 c.m i = .moebius →
            dyadicLogExponent T0
              (heathBrownBoxFactorExponent c.a c.b c.q i) ≤ 2 * t := by
  obtain ⟨L, hL, hXL, hcut⟩ := exists_maynardMoebiusCutoff_sixty hT0 ht hX
  refine ⟨L, hL, hXL, ?_⟩
  intro c i hi
  exact c.moebius_factor_dyadicLogExponent_le hT0 hL hcut i hi

end RHTower.Sieve
