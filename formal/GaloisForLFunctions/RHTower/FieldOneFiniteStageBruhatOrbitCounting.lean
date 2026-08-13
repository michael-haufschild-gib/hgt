import GaloisForLFunctions.RHTower.FieldOneFiniteStageSUnitCoordinates
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Int.Interval
import Mathlib.Data.Finset.Prod

/-!
# Exact logarithmic counting of finite-stage Bruhat orbits

This file supplies the lattice-point estimate underlying Connes--Marcolli
Lemma 2.29 on the literal finite-stage carrier.  Compact nonarchimedean support
gives a common integer denominator, hence a lower bound on every selected
prime exponent.  The archimedean logarithmic cutoff gives one positive
weighted-sum upper bound.  Each exponent is therefore trapped in an explicit
integer interval, producing a finite coordinate box and an exact cardinal
bound of degree `|S|`.

No abstract lattice, asymptotic premise, or unproved counting assertion is
introduced: sign and prime-exponent coordinates inject actual rational
`S`-units into the displayed finite box.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain
open _root_.RHTower

theorem fieldOneIntegerExponent_nonneg (z : ℤ) (p : ℕ) :
    0 ≤ deningerRatExp (z : ℚ) p := by
  rw [deningerRatExp_apply]
  simp

/-- A common integer denominator gives a coordinatewise lower bound on the
prime exponents of every contributing `S`-unit. -/
theorem fieldOneSUnitExponent_lower_of_integerDenominator
    (S : Finset (HeightOneSpectrum ℤ))
    (d : ℤ) (hd : d ≠ 0) (q : fieldOneSUnitSubgroup S)
    (h : algebraMap ℤ ℚ d * (q.1 : ℚ) ∈ (algebraMap ℤ ℚ).range)
    (v : ↥S) :
    -deningerRatExp (d : ℚ)
        (Rat.HeightOneSpectrum.primesEquiv v.1).1 ≤
      fieldOneSUnitExponent S q v := by
  rcases h with ⟨z, hz⟩
  change (z : ℚ) = (d : ℚ) * (q.1 : ℚ) at hz
  have hdQ : (d : ℚ) ≠ 0 := by exact_mod_cast hd
  have hmul := deningerRatExp_mul hdQ (Units.ne_zero q.1)
  have hcoord := congrArg (fun e : ℕ →₀ ℤ =>
    e (Rat.HeightOneSpectrum.primesEquiv v.1).1) hmul
  have hznonneg := fieldOneIntegerExponent_nonneg z
    (Rat.HeightOneSpectrum.primesEquiv v.1).1
  rw [hz] at hznonneg
  rw [hcoord] at hznonneg
  change 0 ≤ deningerRatExp (d : ℚ) _ +
    fieldOneSUnitExponent S q v at hznonneg
  omega

/-- Logarithm of a rational `S`-unit is the weighted sum of its selected prime
exponents. -/
theorem fieldOneSUnit_log_abs
    (S : Finset (HeightOneSpectrum ℤ))
    (q : fieldOneSUnitSubgroup S) :
    Real.log |(((q.1 : ℚˣ) : ℚ) : ℝ)| =
      ∑ v : ↥S, (fieldOneSUnitExponent S q v : ℝ) *
        Real.log ((Rat.HeightOneSpectrum.primesEquiv v.1).1 : ℝ) := by
  classical
  have hq := fieldOneSUnitProduct_exponent_eq_abs_value S q
  have hqR := congrArg (fun x : ℚ => (x : ℝ)) hq
  have hprod :
      |((((q.1 : ℚˣ) : ℚ) : ℝ))| =
        ∏ v : ↥S,
          ((Rat.HeightOneSpectrum.primesEquiv v.1).1 : ℝ) ^
            fieldOneSUnitExponent S q v := by
    calc
      |((((q.1 : ℚˣ) : ℚ) : ℝ))| =
          ((|((q.1 : ℚˣ) : ℚ)| : ℚ) : ℝ) := by norm_cast
      _ = (((fieldOneSUnitProduct S
          (fieldOneSUnitExponent S q) : ℚˣ) : ℚ) : ℝ) := hqR.symm
      _ = ∏ v : ↥S,
          ((Rat.HeightOneSpectrum.primesEquiv v.1).1 : ℝ) ^
            fieldOneSUnitExponent S q v := by
        simp [fieldOneSUnitProduct]
        apply Finset.prod_congr rfl
        intro v _
        congr 1
  rw [hprod, Real.log_prod]
  · apply Finset.sum_congr rfl
    intro v _
    rw [Real.log_zpow]
  · intro v _
    exact (zpow_pos (by exact_mod_cast
      (Rat.HeightOneSpectrum.primesEquiv v.1).2.pos) _).ne'

/-- Positive logarithmic prime weight of a selected finite place. -/
def fieldOneSUnitLogWeight
    {S : Finset (HeightOneSpectrum ℤ)} (v : ↥S) : ℝ :=
  Real.log ((Rat.HeightOneSpectrum.primesEquiv v.1).1 : ℝ)

theorem fieldOneSUnitLogWeight_pos
    {S : Finset (HeightOneSpectrum ℤ)} (v : ↥S) :
    0 < fieldOneSUnitLogWeight v := by
  rw [fieldOneSUnitLogWeight]
  apply Real.log_pos
  exact_mod_cast (Rat.HeightOneSpectrum.primesEquiv v.1).2.one_lt

/-- Explicit upper endpoint for one exponent after all other exponents are
replaced by their lower bounds. -/
def fieldOneSUnitCoordinateUpper
    (S : Finset (HeightOneSpectrum ℤ))
    (L : ↥S → ℤ) (B : ℝ) (v : ↥S) : ℤ := by
  classical
  exact ⌊(B - ∑ w ∈ (Finset.univ.erase v),
      (L w : ℝ) * fieldOneSUnitLogWeight w) /
        fieldOneSUnitLogWeight v⌋

theorem fieldOneSUnitExponent_le_coordinateUpper
    (S : Finset (HeightOneSpectrum ℤ))
    (L e : ↥S → ℤ) (B : ℝ)
    (hL : ∀ v, L v ≤ e v)
    (hB : (∑ v : ↥S, (e v : ℝ) * fieldOneSUnitLogWeight v) ≤ B)
    (v : ↥S) : e v ≤ fieldOneSUnitCoordinateUpper S L B v := by
  classical
  have hrest :
      (∑ w ∈ (Finset.univ.erase v),
          (L w : ℝ) * fieldOneSUnitLogWeight w) ≤
        ∑ w ∈ (Finset.univ.erase v),
          (e w : ℝ) * fieldOneSUnitLogWeight w := by
    apply Finset.sum_le_sum
    intro w _
    apply mul_le_mul_of_nonneg_right
    · exact_mod_cast hL w
    · exact (fieldOneSUnitLogWeight_pos w).le
  have hsplit :
      (∑ w : ↥S, (e w : ℝ) * fieldOneSUnitLogWeight w) =
        (e v : ℝ) * fieldOneSUnitLogWeight v +
          ∑ w ∈ (Finset.univ.erase v),
            (e w : ℝ) * fieldOneSUnitLogWeight w := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ v)]
  rw [fieldOneSUnitCoordinateUpper]
  apply Int.le_floor.mpr
  apply (le_div_iff₀ (fieldOneSUnitLogWeight_pos v)).2
  rw [hsplit] at hB
  linarith

/-- Finite integer coordinate box containing a weighted exponent simplex. -/
def fieldOneSUnitCoordinateBox
    (S : Finset (HeightOneSpectrum ℤ))
    (L : ↥S → ℤ) (B : ℝ) : Finset (↥S → ℤ) := by
  classical
  exact Fintype.piFinset (fun v =>
    Finset.Icc (L v) (fieldOneSUnitCoordinateUpper S L B v))

theorem fieldOneSUnitExponent_mem_coordinateBox
    (S : Finset (HeightOneSpectrum ℤ))
    (L e : ↥S → ℤ) (B : ℝ) :
    e ∈ fieldOneSUnitCoordinateBox S L B ↔
      ∀ v, L v ≤ e v ∧
        e v ≤ fieldOneSUnitCoordinateUpper S L B v := by
  classical
  simp [fieldOneSUnitCoordinateBox, Fintype.mem_piFinset]

/-- Two sign choices times the finite exponent coordinate box. -/
def fieldOneSUnitSignedCoordinateBox
    (S : Finset (HeightOneSpectrum ℤ))
    (L : ↥S → ℤ) (B : ℝ) : Finset (Bool × (↥S → ℤ)) := by
  classical
  exact (Finset.univ : Finset Bool) ×ˢ
    fieldOneSUnitCoordinateBox S L B

/-- Actual `S`-units with coordinatewise lower bounds and a logarithmic
archimedean cutoff. -/
def fieldOneSUnitLogBox
    (S : Finset (HeightOneSpectrum ℤ))
    (L : ↥S → ℤ) (B : ℝ) : Set (fieldOneSUnitSubgroup S) :=
  {q | (∀ v, L v ≤ fieldOneSUnitExponent S q v) ∧
    Real.log |(((q.1 : ℚˣ) : ℚ) : ℝ)| ≤ B}

theorem fieldOneSUnitSignedExponent_mem_signedCoordinateBox_of_mem_logBox
    (S : Finset (HeightOneSpectrum ℤ))
    (L : ↥S → ℤ) (B : ℝ)
    {q : fieldOneSUnitSubgroup S} (hq : q ∈ fieldOneSUnitLogBox S L B) :
    fieldOneSUnitSignedExponent S q ∈
      fieldOneSUnitSignedCoordinateBox S L B := by
  classical
  rw [fieldOneSUnitSignedCoordinateBox, Finset.mem_product]
  refine ⟨Finset.mem_univ _, ?_⟩
  rw [fieldOneSUnitExponent_mem_coordinateBox]
  intro v
  exact ⟨hq.1 v, fieldOneSUnitExponent_le_coordinateUpper S L
    (fieldOneSUnitExponent S q) B hq.1 (by
      have hlog := hq.2
      rw [fieldOneSUnit_log_abs S q] at hlog
      simpa [fieldOneSUnitLogWeight] using hlog) v⟩

theorem fieldOneSUnitLogBox_finite
    (S : Finset (HeightOneSpectrum ℤ))
    (L : ↥S → ℤ) (B : ℝ) :
    (fieldOneSUnitLogBox S L B).Finite := by
  apply Set.Finite.subset
    (Set.Finite.preimage
      (fieldOneSUnitSignedExponent_injective S).injOn
      (fieldOneSUnitSignedCoordinateBox S L B).finite_toSet)
  intro q hq
  exact fieldOneSUnitSignedExponent_mem_signedCoordinateBox_of_mem_logBox
    S L B hq

theorem fieldOneSUnitLogBox_ncard_le
    (S : Finset (HeightOneSpectrum ℤ))
    (L : ↥S → ℤ) (B : ℝ) :
    (fieldOneSUnitLogBox S L B).ncard ≤
      (fieldOneSUnitSignedCoordinateBox S L B).card := by
  rw [← Set.ncard_coe_finset]
  exact Set.ncard_le_ncard_of_injOn
    (fieldOneSUnitSignedExponent S)
    (fun q hq =>
      fieldOneSUnitSignedExponent_mem_signedCoordinateBox_of_mem_logBox
        S L B hq)
    (fieldOneSUnitSignedExponent_injective S).injOn
    (fieldOneSUnitSignedCoordinateBox S L B).finite_toSet

theorem fieldOneSUnitSignedCoordinateBox_card
    (S : Finset (HeightOneSpectrum ℤ))
    (L : ↥S → ℤ) (B : ℝ) :
    (fieldOneSUnitSignedCoordinateBox S L B).card =
      2 * ∏ v : ↥S,
        (fieldOneSUnitCoordinateUpper S L B v + 1 - L v).toNat := by
  classical
  rw [fieldOneSUnitSignedCoordinateBox, Finset.card_product,
    fieldOneSUnitCoordinateBox, Fintype.card_piFinset]
  simp_rw [Int.card_Icc]
  simp

/-! ## Exact polynomial growth of the logarithmic boxes -/

/-- An explicit positive linear-growth factor for one exponent coordinate.
Its reciprocal-log-prime term is the slope forced by the corresponding
weighted-simplex inequality; the absolute-value term absorbs the fixed lower
bounds in the remaining coordinates. -/
def fieldOneSUnitCoordinatePolynomialFactor
    (S : Finset (HeightOneSpectrum ℤ))
    (L : ↥S → ℤ) (v : ↥S) : ℝ := by
  classical
  exact 1 / fieldOneSUnitLogWeight v +
    |-(∑ w ∈ (Finset.univ.erase v),
        (L w : ℝ) * fieldOneSUnitLogWeight w) /
        fieldOneSUnitLogWeight v + 1 - (L v : ℝ)| + 1

theorem fieldOneSUnitCoordinatePolynomialFactor_pos
    (S : Finset (HeightOneSpectrum ℤ))
    (L : ↥S → ℤ) (v : ↥S) :
    0 < fieldOneSUnitCoordinatePolynomialFactor S L v := by
  rw [fieldOneSUnitCoordinatePolynomialFactor]
  have hw := fieldOneSUnitLogWeight_pos v
  positivity

/-- After casting cardinality to the reals, one coordinate interval grows at
most linearly in a nonnegative logarithmic cutoff. -/
theorem fieldOneSUnitCoordinateCard_cast_le
    (S : Finset (HeightOneSpectrum ℤ))
    (L : ↥S → ℤ) (B : ℝ) (hB : 0 ≤ B) (v : ↥S) :
    (((fieldOneSUnitCoordinateUpper S L B v + 1 - L v).toNat : ℕ) : ℝ) ≤
      fieldOneSUnitCoordinatePolynomialFactor S L v * (B + 1) := by
  classical
  let R : ℝ := ∑ w ∈ (Finset.univ.erase v),
    (L w : ℝ) * fieldOneSUnitLogWeight w
  let W : ℝ := fieldOneSUnitLogWeight v
  let C : ℝ := -R / W + 1 - (L v : ℝ)
  let z : ℤ := fieldOneSUnitCoordinateUpper S L B v + 1 - L v
  have hW : 0 < W := fieldOneSUnitLogWeight_pos v
  have hzreal : (z : ℝ) ≤ B / W + C := by
    have hf := Int.floor_le ((B - R) / W)
    dsimp [z, fieldOneSUnitCoordinateUpper, R, W, C]
    push_cast
    calc
      ((⌊(B - ∑ w ∈ Finset.univ.erase v,
          (L w : ℝ) * fieldOneSUnitLogWeight w) /
            fieldOneSUnitLogWeight v⌋ : ℤ) : ℝ) + 1 - (L v : ℝ) ≤
          (B - ∑ w ∈ Finset.univ.erase v,
            (L w : ℝ) * fieldOneSUnitLogWeight w) /
              fieldOneSUnitLogWeight v + 1 - (L v : ℝ) := by linarith
      _ = B / fieldOneSUnitLogWeight v +
          (-((∑ w ∈ Finset.univ.erase v,
              (L w : ℝ) * fieldOneSUnitLogWeight w)) /
              fieldOneSUnitLogWeight v + 1 - (L v : ℝ)) := by ring
  have hpoly : B / W + C ≤
      fieldOneSUnitCoordinatePolynomialFactor S L v * (B + 1) := by
    have hi : 0 < 1 / W := one_div_pos.mpr hW
    have hC : C ≤ |C| := le_abs_self C
    have hCa : 0 ≤ |C| := abs_nonneg C
    change B / W + C ≤ (1 / W + |C| + 1) * (B + 1)
    calc
      B / W + C ≤ B / W + |C| := by linarith
      _ ≤ (1 / W + |C| + 1) * (B + 1) := by
        simp only [div_eq_mul_inv, one_mul] at hi ⊢
        nlinarith [mul_nonneg hB hi.le, mul_nonneg hB hCa]
  by_cases hz : 0 ≤ z
  · calc
      (((z.toNat : ℕ) : ℝ)) = (z : ℝ) := by
        have hzint : (z.toNat : ℤ) = z := Int.toNat_of_nonneg hz
        exact_mod_cast hzint
      _ ≤ B / W + C := hzreal
      _ ≤ _ := hpoly
  · have hzn : z ≤ 0 := le_of_not_ge hz
    rw [Int.toNat_of_nonpos hzn]
    norm_num
    exact mul_nonneg
      (fieldOneSUnitCoordinatePolynomialFactor_pos S L v).le (by linarith)

/-- Explicit positive leading constant for the degree-`|S|` logarithmic box
bound. -/
def fieldOneSUnitLogBoxPolynomialConstant
    (S : Finset (HeightOneSpectrum ℤ))
    (L : ↥S → ℤ) : ℝ :=
  2 * ∏ v : ↥S, fieldOneSUnitCoordinatePolynomialFactor S L v

theorem fieldOneSUnitLogBoxPolynomialConstant_pos
    (S : Finset (HeightOneSpectrum ℤ))
    (L : ↥S → ℤ) :
    0 < fieldOneSUnitLogBoxPolynomialConstant S L := by
  rw [fieldOneSUnitLogBoxPolynomialConstant]
  exact mul_pos (by norm_num) (Finset.prod_pos fun v _ =>
    fieldOneSUnitCoordinatePolynomialFactor_pos S L v)

/-- Quantitative degree-`|S|` bound for the literal rational `S`-unit log
box.  Here `S` contains only the finite places, so this is exactly the
`m - 1` exponent in Connes--Marcolli's convention that also counts the real
place. -/
theorem fieldOneSUnitLogBox_ncard_cast_le_polynomial
    (S : Finset (HeightOneSpectrum ℤ))
    (L : ↥S → ℤ) (B : ℝ) (hB : 0 ≤ B) :
    ((fieldOneSUnitLogBox S L B).ncard : ℝ) ≤
      fieldOneSUnitLogBoxPolynomialConstant S L *
        (B + 1) ^ Fintype.card ↥S := by
  classical
  have hcard := fieldOneSUnitLogBox_ncard_le S L B
  rw [fieldOneSUnitSignedCoordinateBox_card] at hcard
  calc
    ((fieldOneSUnitLogBox S L B).ncard : ℝ) ≤
        ((2 * ∏ v : ↥S,
          (fieldOneSUnitCoordinateUpper S L B v + 1 - L v).toNat : ℕ) : ℝ) := by
      exact_mod_cast hcard
    _ = 2 * ∏ v : ↥S,
        (((fieldOneSUnitCoordinateUpper S L B v + 1 - L v).toNat : ℕ) : ℝ) := by
      norm_cast
    _ ≤ 2 * ∏ v : ↥S,
        (fieldOneSUnitCoordinatePolynomialFactor S L v * (B + 1)) := by
      gcongr
      exact fieldOneSUnitCoordinateCard_cast_le S L B hB _
    _ = fieldOneSUnitLogBoxPolynomialConstant S L *
        (B + 1) ^ Fintype.card ↥S := by
      rw [fieldOneSUnitLogBoxPolynomialConstant, Finset.prod_mul_distrib,
        Finset.prod_const, Finset.card_univ]
      ring

/-- Asymptotic form of the exact log-box count: literal rational `S`-units
have polynomial counting growth of degree `|S|`. -/
theorem fieldOneSUnitLogBox_ncard_isBigO_atTop
    (S : Finset (HeightOneSpectrum ℤ))
    (L : ↥S → ℤ) :
    (fun B : ℝ => ((fieldOneSUnitLogBox S L B).ncard : ℝ)) =O[Filter.atTop]
      (fun B : ℝ => (B + 1) ^ Fintype.card ↥S) := by
  refine Asymptotics.IsBigO.of_bound
    (fieldOneSUnitLogBoxPolynomialConstant S L) ?_
  refine (Filter.eventually_ge_atTop (0 : ℝ)).mono ?_
  intro B hB
  have h := fieldOneSUnitLogBox_ncard_cast_le_polynomial S L B hB
  have hn : 0 ≤ ((fieldOneSUnitLogBox S L B).ncard : ℝ) := Nat.cast_nonneg _
  have hpow : 0 ≤ (B + 1) ^ Fintype.card ↥S := pow_nonneg (by linarith) _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hn,
    abs_of_nonneg hpow] using h

/-- Coordinatewise lower bound supplied by an integer denominator. -/
def fieldOneFiniteStageDenominatorExponentLower
    (S : Finset (HeightOneSpectrum ℤ)) (d : ℤ) (v : ↥S) : ℤ :=
  -deningerRatExp (d : ℚ)
    (Rat.HeightOneSpectrum.primesEquiv v.1).1

/-- Actual finite-stage `S`-unit orbit selected by nonarchimedean Bruhat
support and an archimedean logarithmic cutoff. -/
def fieldOneFiniteStageFiniteBruhatLogOrbit
    (S : Finset (HeightOneSpectrum ℤ))
    (phi : FieldOneFiniteStageFiniteBruhatSchwartz S)
    (u : FieldOneFiniteStageIdele S) (B : ℝ) :
    Set (fieldOneSUnitSubgroup S) :=
  {q | phi.1 (fun v =>
      algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ) *
        (u.2 v : v.1.adicCompletion ℚ)) ≠ 0 ∧
    Real.log |(((q.1 : ℚˣ) : ℚ) : ℝ)| ≤ B}

theorem fieldOneFiniteStageFiniteBruhatLogOrbit_subset_logBox
    (S : Finset (HeightOneSpectrum ℤ))
    (phi : FieldOneFiniteStageFiniteBruhatSchwartz S)
    (u : FieldOneFiniteStageIdele S) (B : ℝ)
    (d : ℤ) (hd : d ≠ 0)
    (hden : ∀ q : fieldOneSUnitSubgroup S,
      phi.1 (fun v =>
        algebraMap ℚ (v.1.adicCompletion ℚ) (q.1 : ℚ) *
          (u.2 v : v.1.adicCompletion ℚ)) ≠ 0 →
      algebraMap ℤ ℚ d * (q.1 : ℚ) ∈ (algebraMap ℤ ℚ).range) :
    fieldOneFiniteStageFiniteBruhatLogOrbit S phi u B ⊆
      fieldOneSUnitLogBox S
        (fieldOneFiniteStageDenominatorExponentLower S d) B := by
  intro q hq
  refine ⟨fun v => ?_, hq.2⟩
  exact fieldOneSUnitExponent_lower_of_integerDenominator S d hd q
    (hden q hq.1) v

/-- The nonarchimedean-support/log-window portion of every actual Bruhat orbit
is finite. -/
theorem fieldOneFiniteStageFiniteBruhatLogOrbit_finite
    (S : Finset (HeightOneSpectrum ℤ))
    (phi : FieldOneFiniteStageFiniteBruhatSchwartz S)
    (u : FieldOneFiniteStageIdele S) (B : ℝ) :
    (fieldOneFiniteStageFiniteBruhatLogOrbit S phi u B).Finite := by
  obtain ⟨d, hd, hden⟩ :=
    fieldOneFiniteStageFiniteBruhatMulRight_exists_integerDenominator S phi u
  exact (fieldOneSUnitLogBox_finite S
    (fieldOneFiniteStageDenominatorExponentLower S d) B).subset
      (fieldOneFiniteStageFiniteBruhatLogOrbit_subset_logBox
        S phi u B d hd hden)

/-- Exact degree-`|S|` coordinate-box bound for an actual finite-stage Bruhat
orbit in a logarithmic window. -/
theorem fieldOneFiniteStageFiniteBruhatLogOrbit_exists_card_bound
    (S : Finset (HeightOneSpectrum ℤ))
    (phi : FieldOneFiniteStageFiniteBruhatSchwartz S)
    (u : FieldOneFiniteStageIdele S) (B : ℝ) :
    ∃ d : ℤ, d ≠ 0 ∧
      (fieldOneFiniteStageFiniteBruhatLogOrbit S phi u B).ncard ≤
        2 * ∏ v : ↥S,
          (fieldOneSUnitCoordinateUpper S
              (fieldOneFiniteStageDenominatorExponentLower S d) B v + 1 -
            fieldOneFiniteStageDenominatorExponentLower S d v).toNat := by
  obtain ⟨d, hd, hden⟩ :=
    fieldOneFiniteStageFiniteBruhatMulRight_exists_integerDenominator S phi u
  refine ⟨d, hd, ?_⟩
  calc
    (fieldOneFiniteStageFiniteBruhatLogOrbit S phi u B).ncard ≤
        (fieldOneSUnitLogBox S
          (fieldOneFiniteStageDenominatorExponentLower S d) B).ncard :=
      Set.ncard_le_ncard
        (fieldOneFiniteStageFiniteBruhatLogOrbit_subset_logBox
          S phi u B d hd hden)
        (fieldOneSUnitLogBox_finite S
          (fieldOneFiniteStageDenominatorExponentLower S d) B)
    _ ≤ (fieldOneSUnitSignedCoordinateBox S
        (fieldOneFiniteStageDenominatorExponentLower S d) B).card :=
      fieldOneSUnitLogBox_ncard_le S
        (fieldOneFiniteStageDenominatorExponentLower S d) B
    _ = _ := fieldOneSUnitSignedCoordinateBox_card S
      (fieldOneFiniteStageDenominatorExponentLower S d) B

/-- Connes--Marcolli's degree-`|S|` logarithmic orbit count, now for the
actual nonarchimedean support of an arbitrary finite-stage Bruhat--Schwartz
function and an arbitrary finite-stage idele. -/
theorem fieldOneFiniteStageFiniteBruhatLogOrbit_ncard_isBigO_atTop
    (S : Finset (HeightOneSpectrum ℤ))
    (phi : FieldOneFiniteStageFiniteBruhatSchwartz S)
    (u : FieldOneFiniteStageIdele S) :
    (fun B : ℝ =>
        ((fieldOneFiniteStageFiniteBruhatLogOrbit S phi u B).ncard : ℝ))
      =O[Filter.atTop] (fun B : ℝ => (B + 1) ^ Fintype.card ↥S) := by
  obtain ⟨d, hd, hden⟩ :=
    fieldOneFiniteStageFiniteBruhatMulRight_exists_integerDenominator S phi u
  let L := fieldOneFiniteStageDenominatorExponentLower S d
  refine Asymptotics.IsBigO.of_bound
    (fieldOneSUnitLogBoxPolynomialConstant S L) ?_
  refine (Filter.eventually_ge_atTop (0 : ℝ)).mono ?_
  intro B hB
  have hsubset : fieldOneFiniteStageFiniteBruhatLogOrbit S phi u B ⊆
      fieldOneSUnitLogBox S L B :=
    fieldOneFiniteStageFiniteBruhatLogOrbit_subset_logBox
      S phi u B d hd hden
  have hcard :
      (fieldOneFiniteStageFiniteBruhatLogOrbit S phi u B).ncard ≤
        (fieldOneSUnitLogBox S L B).ncard :=
    Set.ncard_le_ncard hsubset (fieldOneSUnitLogBox_finite S L B)
  have hpoly := fieldOneSUnitLogBox_ncard_cast_le_polynomial S L B hB
  have hreal :
      ((fieldOneFiniteStageFiniteBruhatLogOrbit S phi u B).ncard : ℝ) ≤
        fieldOneSUnitLogBoxPolynomialConstant S L *
          (B + 1) ^ Fintype.card ↥S := by
    exact (by exact_mod_cast hcard :
      ((fieldOneFiniteStageFiniteBruhatLogOrbit S phi u B).ncard : ℝ) ≤
        ((fieldOneSUnitLogBox S L B).ncard : ℝ)).trans hpoly
  have hn : 0 ≤
      ((fieldOneFiniteStageFiniteBruhatLogOrbit S phi u B).ncard : ℝ) :=
    Nat.cast_nonneg _
  have hpow : 0 ≤ (B + 1) ^ Fintype.card ↥S := pow_nonneg (by linarith) _
  simpa only [Real.norm_eq_abs, abs_of_nonneg hn,
    abs_of_nonneg hpow] using hreal

end

end GaloisForLFunctions.RHTower
