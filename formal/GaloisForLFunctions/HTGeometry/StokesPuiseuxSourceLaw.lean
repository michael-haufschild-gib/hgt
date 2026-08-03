import GaloisForLFunctions.HTGeometry.AiryTowerStokesRigidity
import Mathlib.RingTheory.RootsOfUnity.Complex

/-!
# Cyclic Puiseux stabilizer coarea source law

This module derives ramified characteristic weights from a genuine complex root-of-unity action
on finitely supported Puiseux polynomials.  It proves stabilizer cardinalities, minimal-denominator
orbit size, first-break degrees, the ordered-sheet endomorphism irregularity and the exact diagonal
Stokes loop formula without assuming the characteristic weight as source data.
-/

namespace GaloisForLFunctions
namespace IrregularStokes

/-- Iterated gcd of a denominator and exponent numerators. -/
def cyclicGcd : ℕ → List ℕ → ℕ
  | R, [] => R
  | R, beta :: rest => cyclicGcd (Nat.gcd R beta) rest

@[simp] theorem cyclicGcd_nil (R : ℕ) : cyclicGcd R [] = R := rfl

@[simp] theorem cyclicGcd_cons (R beta : ℕ) (rest : List ℕ) :
    cyclicGcd R (beta :: rest) = cyclicGcd (Nat.gcd R beta) rest := rfl

theorem cyclicGcd_dvd_start (R : ℕ) (P : List ℕ) : cyclicGcd R P ∣ R := by
  induction P generalizing R with
  | nil => simp
  | cons beta rest ih =>
      exact (ih (Nat.gcd R beta)).trans (Nat.gcd_dvd_left R beta)

theorem dvd_cyclicGcd_iff {d R : ℕ} {P : List ℕ} :
    d ∣ cyclicGcd R P ↔ d ∣ R ∧ ∀ beta ∈ P, d ∣ beta := by
  induction P generalizing R with
  | nil => simp
  | cons beta rest ih =>
      rw [cyclicGcd_cons, ih, Nat.dvd_gcd_iff]
      simp only [List.mem_cons, forall_eq_or_imp]
      tauto

theorem cyclicGcd_append_singleton (R : ℕ) (P : List ℕ) (beta : ℕ) :
    cyclicGcd R (P ++ [beta]) = Nat.gcd (cyclicGcd R P) beta := by
  induction P generalizing R with
  | nil => rfl
  | cons gamma rest ih =>
      simp only [List.cons_append, cyclicGcd_cons]
      exact ih (Nat.gcd R gamma)

/-- Phase of exponent `beta` under the cyclic sheet shift `a`. -/
abbrev FixesExponent {R : ℕ} (a : ZMod R) (beta : ℕ) : Prop := beta • a = 0

theorem fixesExponent_iff_dvd {R beta : ℕ} (hR : 0 < R) (a : ZMod R) :
    FixesExponent a beta ↔ R ∣ a.val * beta := by
  letI : NeZero R := ⟨Nat.ne_of_gt hR⟩
  have hzero : (((beta * a.val : ℕ) : ZMod R) = 0 ↔ R ∣ beta * a.val) := by
    rw [show (0 : ZMod R) = (0 : ℕ) by simp, ZMod.natCast_eq_natCast_iff]
    exact Nat.modEq_zero_iff_dvd
  simpa [FixesExponent, nsmul_eq_mul, Nat.cast_mul, ZMod.natCast_zmod_val,
    Nat.mul_comm] using hzero

theorem cyclicGcd_smul_eq_zero_iff {R : ℕ} (a : ZMod R) (P : List ℕ) :
    cyclicGcd R P • a = 0 ↔ ∀ beta ∈ P, beta • a = 0 := by
  rw [← addOrderOf_dvd_iff_nsmul_eq_zero, dvd_cyclicGcd_iff]
  constructor
  · rintro ⟨_, hP⟩ beta hbeta
    exact addOrderOf_dvd_iff_nsmul_eq_zero.mp (hP beta hbeta)
  · intro hP
    constructor
    · simpa [Nat.card_zmod] using addOrderOf_dvd_natCard a
    · intro beta hbeta
      exact addOrderOf_dvd_iff_nsmul_eq_zero.mpr (hP beta hbeta)

/-- Cyclic sheets fixing all exponent numerators in `P`. -/
def CyclicStabilizer (R : ℕ) (P : List ℕ) : AddSubgroup (ZMod R) :=
  (nsmulAddMonoidHom (cyclicGcd R P)).ker

theorem mem_cyclicStabilizer_iff {R : ℕ} {P : List ℕ} (a : ZMod R) :
    a ∈ CyclicStabilizer R P ↔ ∀ beta ∈ P, FixesExponent a beta := by
  rw [CyclicStabilizer, AddMonoidHom.mem_ker]
  exact cyclicGcd_smul_eq_zero_iff a P

theorem cyclicStabilizer_card {R : ℕ} (hR : 0 < R) (P : List ℕ) :
    Nat.card (CyclicStabilizer R P) = cyclicGcd R P := by
  letI : NeZero R := ⟨Nat.ne_of_gt hR⟩
  calc
    Nat.card (CyclicStabilizer R P) =
        (Nat.card (ZMod R)).gcd (cyclicGcd R P) := by
      exact IsAddCyclic.card_nsmulAddMonoidHom_ker (ZMod R) (cyclicGcd R P)
    _ = Nat.gcd R (cyclicGcd R P) := by rw [Nat.card_zmod]
    _ = cyclicGcd R P := Nat.gcd_eq_right_iff_dvd.mpr (cyclicGcd_dvd_start R P)

/-- Sheets lost when exponent `beta` is adjoined to prefix `P`. -/
def CyclicLayer (R : ℕ) (P : List ℕ) (beta : ℕ) : Set (ZMod R) :=
  (CyclicStabilizer R P : Set (ZMod R)) \
    (CyclicStabilizer R (P ++ [beta]) : Set (ZMod R))

theorem cyclicStabilizer_append_subset (R : ℕ) (P : List ℕ) (beta : ℕ) :
    (CyclicStabilizer R (P ++ [beta]) : Set (ZMod R)) ⊆
      (CyclicStabilizer R P : Set (ZMod R)) := by
  intro a ha
  change a ∈ CyclicStabilizer R (P ++ [beta]) at ha
  change a ∈ CyclicStabilizer R P
  rw [mem_cyclicStabilizer_iff] at ha ⊢
  intro gamma hgamma
  exact ha gamma (List.mem_append_left [beta] hgamma)

theorem mem_cyclicStabilizer_append_iff {R : ℕ} (P : List ℕ) (beta : ℕ)
    (a : ZMod R) :
    a ∈ CyclicStabilizer R (P ++ [beta]) ↔
      a ∈ CyclicStabilizer R P ∧ FixesExponent a beta := by
  simp only [mem_cyclicStabilizer_iff, List.mem_append, List.mem_singleton]
  constructor
  · intro h
    exact ⟨fun gamma hgamma => h gamma (Or.inl hgamma), h beta (Or.inr rfl)⟩
  · rintro ⟨hP, hbeta⟩ gamma (hgamma | rfl)
    · exact hP gamma hgamma
    · exact hbeta

private theorem sum_indicator_nat {α : Type*} [Fintype α] (p : α → Prop)
    [DecidablePred p] (n : ℕ) :
    (∑ a : α, if p a then n else 0) = n * Nat.card {a : α // p a} := by
  classical
  rw [Finset.sum_ite]
  simp [Nat.card_eq_fintype_card, Fintype.card_subtype, Nat.mul_comm]

theorem cyclicLayer_card {R : ℕ} (hR : 0 < R) (P : List ℕ) (beta : ℕ) :
    Nat.card (CyclicLayer R P beta) =
      cyclicGcd R P - Nat.gcd (cyclicGcd R P) beta := by
  letI : NeZero R := ⟨Nat.ne_of_gt hR⟩
  rw [Nat.card_coe_set_eq]
  rw [CyclicLayer, Set.ncard_sdiff (cyclicStabilizer_append_subset R P beta)]
  change Nat.card (CyclicStabilizer R P) -
    Nat.card (CyclicStabilizer R (P ++ [beta])) = _
  rw [cyclicStabilizer_card hR, cyclicStabilizer_card hR,
    cyclicGcd_append_singleton]

/-- Root of unity implementing the actual Puiseux Galois action. -/
noncomputable def sheetRoot (R : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / R)

theorem sheetRoot_isPrimitive {R : ℕ} (hR : 0 < R) :
    IsPrimitiveRoot (sheetRoot R) R := by
  exact Complex.isPrimitiveRoot_exp R (Nat.ne_of_gt hR)

theorem sheetRoot_pow_eq_one_iff {R n : ℕ} (hR : 0 < R) :
    sheetRoot R ^ n = 1 ↔ R ∣ n :=
  (sheetRoot_isPrimitive hR).pow_eq_one_iff_dvd n

theorem sheetRoot_pow_eq_pow_iff_fixes_sub {R j : ℕ} (hR : 0 < R)
    (a b : ZMod R) :
    sheetRoot R ^ (a.val * j) = sheetRoot R ^ (b.val * j) ↔
      FixesExponent (b - a) j := by
  letI : NeZero R := ⟨Nat.ne_of_gt hR⟩
  calc
    sheetRoot R ^ (a.val * j) = sheetRoot R ^ (b.val * j) ↔
        a.val * j ≡ b.val * j [MOD R] := by
      have hroot := sheetRoot_isPrimitive hR
      rw [(hroot.isOfFinOrder (Nat.ne_of_gt hR)).pow_inj_mod, ← hroot.eq_orderOf]
      rfl
    _ ↔ ((a.val * j : ℕ) : ZMod R) = ((b.val * j : ℕ) : ZMod R) := by
      exact (ZMod.natCast_eq_natCast_iff (a.val * j) (b.val * j) R).symm
    _ ↔ j • a = j • b := by
      simp [nsmul_eq_mul, Nat.cast_mul, Nat.mul_comm]
    _ ↔ FixesExponent (b - a) j := by
      simp only [FixesExponent, nsmul_eq_mul, mul_sub, sub_eq_zero, eq_comm]

/-- A genuine finite Puiseux polynomial in `z^(1/R)`. -/
structure PuiseuxPolynomial (R : ℕ) where
  coeff : ℕ →₀ ℂ
  noConstant : coeff 0 = 0

namespace PuiseuxPolynomial

/-- Cyclic Galois translate `z^(1/R) ↦ zeta_R^a z^(1/R)`. -/
noncomputable def galoisTranslate {R : ℕ} (q : PuiseuxPolynomial R) (a : ZMod R) : ℕ →₀ ℂ where
  toFun j := q.coeff j * sheetRoot R ^ (a.val * j)
  support := q.coeff.support
  mem_support_toFun j := by simp [sheetRoot]

@[simp] theorem galoisTranslate_apply {R : ℕ} (q : PuiseuxPolynomial R) (a : ZMod R)
    (j : ℕ) : q.galoisTranslate a j = q.coeff j * sheetRoot R ^ (a.val * j) := rfl

theorem galoisTranslate_eq_iff {R : ℕ} (hR : 0 < R) (q : PuiseuxPolynomial R)
    (a : ZMod R) :
    q.galoisTranslate a = q.coeff ↔
      ∀ j ∈ q.coeff.support, R ∣ a.val * j := by
  constructor
  · intro h j hj
    have hc : q.coeff j ≠ 0 := Finsupp.mem_support_iff.mp hj
    have heq := DFunLike.congr_fun h j
    have hp : sheetRoot R ^ (a.val * j) = 1 := by
      apply (mul_left_cancel₀ hc)
      simpa using heq
    exact (sheetRoot_pow_eq_one_iff hR).mp hp
  · intro h
    ext j
    by_cases hj : j ∈ q.coeff.support
    · have hp := (sheetRoot_pow_eq_one_iff hR).mpr (h j hj)
      simp [hp]
    · have hz : q.coeff j = 0 := by simpa [Finsupp.mem_support_iff] using hj
      simp [hz]

/-- Actual sheets fixing a complex Puiseux polynomial. -/
def FixedSheets {R : ℕ} (q : PuiseuxPolynomial R) :=
  {a : ZMod R // q.galoisTranslate a = q.coeff}

/-- Largest exponent numerator at which a translate differs from the original polynomial. -/
noncomputable def differenceNumerator {R : ℕ} (q : PuiseuxPolynomial R) (a : ZMod R) : ℕ :=
  q.coeff.support.sup fun j => if q.galoisTranslate a j = q.coeff j then 0 else j

/-- Largest exponent numerator at which two genuine Galois sheets differ. -/
noncomputable def pairDifferenceNumerator {R : ℕ} (q : PuiseuxPolynomial R)
    (a b : ZMod R) : ℕ :=
  q.coeff.support.sup fun j => if q.galoisTranslate a j = q.galoisTranslate b j then 0 else j

theorem galoisTranslate_apply_eq_iff {R : ℕ} (hR : 0 < R) (q : PuiseuxPolynomial R)
    (a : ZMod R) {j : ℕ} (hj : j ∈ q.coeff.support) :
    q.galoisTranslate a j = q.coeff j ↔ FixesExponent a j := by
  have hc : q.coeff j ≠ 0 := Finsupp.mem_support_iff.mp hj
  rw [galoisTranslate_apply]
  constructor
  · intro h
    have hp : sheetRoot R ^ (a.val * j) = 1 := by
      apply mul_left_cancel₀ hc
      simpa using h
    exact (fixesExponent_iff_dvd hR a).mpr ((sheetRoot_pow_eq_one_iff hR).mp hp)
  · intro h
    have hp := (sheetRoot_pow_eq_one_iff hR).mpr ((fixesExponent_iff_dvd hR a).mp h)
    simp [hp]

theorem galoisTranslate_apply_eq_translate_iff {R : ℕ} (hR : 0 < R)
    (q : PuiseuxPolynomial R) (a b : ZMod R) {j : ℕ} (hj : j ∈ q.coeff.support) :
    q.galoisTranslate a j = q.galoisTranslate b j ↔ FixesExponent (b - a) j := by
  have hc : q.coeff j ≠ 0 := Finsupp.mem_support_iff.mp hj
  simp only [galoisTranslate_apply]
  constructor
  · intro h
    exact (sheetRoot_pow_eq_pow_iff_fixes_sub hR a b).mp (mul_left_cancel₀ hc h)
  · intro h
    exact congrArg (q.coeff j * ·) ((sheetRoot_pow_eq_pow_iff_fixes_sub hR a b).mpr h)

end PuiseuxPolynomial

namespace Characteristic

/-- Level numerators in strictly decreasing Puiseux order. -/
def levelExponents {R beta : ℕ} : Characteristic R beta → List ℕ
  | .terminal .. => [beta]
  | .step _ _ _ _ _ tail => beta :: tail.levelExponents

theorem levelExponents_pos {R beta : ℕ} (c : Characteristic R beta) :
    ∀ gamma ∈ c.levelExponents, 0 < gamma := by
  induction c with
  | terminal hR hbeta hgcd => simpa [levelExponents] using hbeta
  | step hER hE hbeta hgcd hgamma tail ih =>
      simp only [levelExponents, List.mem_cons, forall_eq_or_imp]
      exact ⟨hbeta, ih⟩

theorem levelExponents_le_first {R beta : ℕ} (c : Characteristic R beta) :
    ∀ gamma ∈ c.levelExponents, gamma ≤ beta := by
  induction c with
  | terminal => simp [levelExponents]
  | @step R E beta gamma hER hE hbeta hgcd hgamma tail ih =>
      intro delta hdelta
      simp only [levelExponents, List.mem_cons] at hdelta
      rcases hdelta with rfl | hdelta
      · exact le_rfl
      · exact (ih delta hdelta).trans (Nat.le_of_lt hgamma)

theorem levelExponents_pairwise {R beta : ℕ} (c : Characteristic R beta) :
    c.levelExponents.Pairwise (· > ·) := by
  induction c with
  | terminal => simp [levelExponents]
  | @step R E beta gamma hER hE hbeta hgcd hgamma tail ih =>
      rw [levelExponents, List.pairwise_cons]
      exact ⟨fun delta hdelta => lt_of_le_of_lt (tail.levelExponents_le_first delta hdelta) hgamma,
        ih⟩

@[simp] theorem cyclicGcd_levelExponents {R beta : ℕ} (c : Characteristic R beta) :
    cyclicGcd R c.levelExponents = 1 := by
  induction c with
  | terminal hR hbeta hgcd => simpa [levelExponents, cyclicGcd] using hgcd
  | step hER hE hbeta hgcd hgamma tail ih =>
      simpa [levelExponents, cyclicGcd, hgcd] using ih

/-- Finsupp with coefficient one on exactly `s`. -/
def unitSupport (s : Finset ℕ) : ℕ →₀ ℂ where
  toFun j := if j ∈ s then 1 else 0
  support := s
  mem_support_toFun j := by simp

@[simp] theorem unitSupport_apply (s : Finset ℕ) (j : ℕ) :
    unitSupport s j = if j ∈ s then 1 else 0 := rfl

@[simp] theorem unitSupport_support (s : Finset ℕ) : (unitSupport s).support = s := rfl

/-- Canonical coefficient-one Puiseux polynomial carrying exactly a characteristic's levels. -/
def canonicalPuiseux {R beta : ℕ} (c : Characteristic R beta) : PuiseuxPolynomial R where
  coeff := unitSupport c.levelExponents.toFinset
  noConstant := by
    have hzero : 0 ∉ c.levelExponents := by
      intro h
      exact (c.levelExponents_pos 0 h).ne' rfl
    simp [unitSupport_apply, hzero]

@[simp] theorem canonicalPuiseux_support {R beta : ℕ} (c : Characteristic R beta) :
    c.canonicalPuiseux.coeff.support = c.levelExponents.toFinset := rfl

theorem canonical_galoisTranslate_eq_iff {R beta : ℕ} (c : Characteristic R beta)
    (a : ZMod R) :
    c.canonicalPuiseux.galoisTranslate a = c.canonicalPuiseux.coeff ↔
      ∀ gamma ∈ c.levelExponents, FixesExponent a gamma := by
  have hR : 0 < R := Nat.zero_lt_one.trans c.ramification_gt_one
  rw [PuiseuxPolynomial.galoisTranslate_eq_iff hR]
  simp only [canonicalPuiseux_support, List.mem_toFinset]
  constructor
  · intro h gamma hgamma
    exact (fixesExponent_iff_dvd hR a).mpr (h gamma hgamma)
  · intro h gamma hgamma
    exact (fixesExponent_iff_dvd hR a).mp (h gamma hgamma)

/-- Fixed complex sheets are exactly the arithmetic cyclic stabilizer. -/
def fixedSheetsEquivStabilizer {R beta : ℕ} (c : Characteristic R beta) :
    c.canonicalPuiseux.FixedSheets ≃ CyclicStabilizer R c.levelExponents where
  toFun a := ⟨a.1, (mem_cyclicStabilizer_iff a.1).2
    ((canonical_galoisTranslate_eq_iff c a.1).1 a.2)⟩
  invFun a := ⟨a.1, (canonical_galoisTranslate_eq_iff c a.1).2
    ((mem_cyclicStabilizer_iff a.1).1 a.2)⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Minimal characteristic denominator gives one actual fixed Galois sheet. -/
theorem canonical_fixedSheets_card {R beta : ℕ} (c : Characteristic R beta) :
    Nat.card c.canonicalPuiseux.FixedSheets = 1 := by
  rw [Nat.card_congr c.fixedSheetsEquivStabilizer]
  rw [cyclicStabilizer_card (Nat.zero_lt_one.trans c.ramification_gt_one)]
  exact c.cyclicGcd_levelExponents

/-- Minimal Puiseux denominator makes the actual cyclic translate map injective. -/
theorem canonical_galoisTranslate_injective {R beta : ℕ} (c : Characteristic R beta) :
    Function.Injective c.canonicalPuiseux.galoisTranslate := by
  intro a b hab
  have hfix : ∀ gamma ∈ c.levelExponents, FixesExponent (b - a) gamma := by
    intro gamma hgamma
    have hsupport : gamma ∈ c.canonicalPuiseux.coeff.support := by
      simpa [canonicalPuiseux_support] using hgamma
    apply (PuiseuxPolynomial.galoisTranslate_apply_eq_translate_iff
      (Nat.zero_lt_one.trans c.ramification_gt_one) c.canonicalPuiseux a b hsupport).mp
    exact DFunLike.congr_fun hab gamma
  have hzero : cyclicGcd R c.levelExponents • (b - a) = 0 :=
    (cyclicGcd_smul_eq_zero_iff (b - a) c.levelExponents).2 hfix
  rw [c.cyclicGcd_levelExponents, one_nsmul] at hzero
  exact (sub_eq_zero.mp hzero).symm

/-- Genuine Galois orbit of the canonical Puiseux polynomial. -/
noncomputable def galoisOrbit {R beta : ℕ} (c : Characteristic R beta) :
    Set (ℕ →₀ ℂ) := Set.range c.canonicalPuiseux.galoisTranslate

/-- Minimal denominator gives exactly `R` distinct complex Puiseux sheets. -/
theorem canonical_galoisOrbit_card {R beta : ℕ} (c : Characteristic R beta) :
    Nat.card c.galoisOrbit = R := by
  rw [galoisOrbit, Nat.card_range_of_injective c.canonical_galoisTranslate_injective,
    Nat.card_zmod]

/-- First level numerator changed by a cyclic sheet shift. -/
def firstBreak {R : ℕ} (a : ZMod R) : List ℕ → ℕ
  | [] => 0
  | gamma :: rest => if FixesExponent a gamma then firstBreak a rest else gamma

private theorem firstBreak_le_of_forall_le {R n : ℕ} (a : ZMod R) (P : List ℕ)
    (hP : ∀ j ∈ P, j ≤ n) : firstBreak a P ≤ n := by
  induction P with
  | nil => simp [firstBreak]
  | cons gamma rest ih =>
      simp only [firstBreak]
      by_cases hfix : FixesExponent a gamma
      · rw [if_pos hfix]
        exact ih (fun j hj => hP j (by simp [hj]))
      · rw [if_neg hfix]
        exact hP gamma (by simp)

private theorem firstBreak_eq_sup {R : ℕ} (a : ZMod R) (P : List ℕ)
    (hP : P.Pairwise (· > ·)) :
    firstBreak a P = P.toFinset.sup (fun j => if FixesExponent a j then 0 else j) := by
  induction P with
  | nil => simp [firstBreak]
  | cons gamma rest ih =>
      rw [List.pairwise_cons] at hP
      simp only [firstBreak, List.toFinset_cons, Finset.sup_insert]
      rw [← ih hP.2]
      by_cases hfix : FixesExponent a gamma
      · rw [if_pos hfix, if_pos hfix, zero_max]
      · rw [if_neg hfix, if_neg hfix, max_eq_left]
        exact firstBreak_le_of_forall_le a rest
          (fun j hj => Nat.le_of_lt (hP.1 j hj))

/-- The actual leading degree of the translated Puiseux difference is the first failed level. -/
theorem canonical_differenceNumerator_eq_firstBreak {R beta : ℕ}
    (c : Characteristic R beta) (a : ZMod R) :
    c.canonicalPuiseux.differenceNumerator a = firstBreak a c.levelExponents := by
  classical
  rw [PuiseuxPolynomial.differenceNumerator, canonicalPuiseux_support,
    firstBreak_eq_sup a c.levelExponents c.levelExponents_pairwise]
  apply Finset.sup_congr rfl
  intro j hj
  have hiff := PuiseuxPolynomial.galoisTranslate_apply_eq_iff
    (Nat.zero_lt_one.trans c.ramification_gt_one) c.canonicalPuiseux a hj
  by_cases hfix : FixesExponent a j
  · have heq := hiff.mpr hfix
    rw [if_pos heq, if_pos hfix]
  · have hne : c.canonicalPuiseux.galoisTranslate a j ≠ c.canonicalPuiseux.coeff j :=
      fun heq => hfix (hiff.mp heq)
    rw [if_neg hne, if_neg hfix]

/-- The actual leading degree between two Galois sheets depends only on their cyclic difference. -/
theorem canonical_pairDifferenceNumerator_eq_firstBreak {R beta : ℕ}
    (c : Characteristic R beta) (a b : ZMod R) :
    c.canonicalPuiseux.pairDifferenceNumerator a b =
      firstBreak (b - a) c.levelExponents := by
  classical
  rw [PuiseuxPolynomial.pairDifferenceNumerator, canonicalPuiseux_support,
    firstBreak_eq_sup (b - a) c.levelExponents c.levelExponents_pairwise]
  apply Finset.sup_congr rfl
  intro j hj
  have hiff := PuiseuxPolynomial.galoisTranslate_apply_eq_translate_iff
    (Nat.zero_lt_one.trans c.ramification_gt_one) c.canonicalPuiseux a b hj
  by_cases hfix : FixesExponent (b - a) j
  · rw [if_pos (hiff.mpr hfix), if_pos hfix]
  · have hne : c.canonicalPuiseux.galoisTranslate a j ≠
        c.canonicalPuiseux.galoisTranslate b j := fun heq => hfix (hiff.mp heq)
    rw [if_neg hne, if_neg hfix]

/-- Arithmetic coarea of successive cyclic stabilizer losses. -/
def cyclicCoarea : ℕ → List ℕ → ℕ
  | _, [] => 0
  | R, gamma :: rest =>
      gamma * (R - Nat.gcd R gamma) + cyclicCoarea (Nat.gcd R gamma) rest

@[simp] theorem cyclicCoarea_levelExponents {R beta : ℕ} (c : Characteristic R beta) :
    cyclicCoarea R c.levelExponents = c.weightedIrregularity := by
  induction c with
  | terminal hR hbeta hgcd => simp [levelExponents, cyclicCoarea, weightedIrregularity, hgcd]
  | step hER hE hbeta hgcd hgamma tail ih =>
      simp [levelExponents, cyclicCoarea, weightedIrregularity, hgcd, ih]

end Characteristic

/-- Coarea written only with cardinalities of actual cyclic sheet-loss sets. -/
noncomputable def galoisCoarea (R : ℕ) (initial : List ℕ) : List ℕ → ℕ
  | [] => 0
  | gamma :: rest => gamma * Nat.card (CyclicLayer R initial gamma) +
      galoisCoarea R (initial ++ [gamma]) rest

/-- Sum of first changed exponents over sheets fixing an initial prefix. -/
noncomputable def restrictedFirstBreakSum {R : ℕ} (hR : 0 < R)
    (initial rest : List ℕ) : ℕ := by
  letI : NeZero R := ⟨Nat.ne_of_gt hR⟩
  classical
  exact ∑ a : ZMod R, if a ∈ CyclicStabilizer R initial then
    Characteristic.firstBreak a rest else 0

private theorem restrictedFirstBreakSum_step {R : ℕ} (hR : 0 < R)
    (initial rest : List ℕ) (gamma : ℕ) :
    restrictedFirstBreakSum hR initial (gamma :: rest) =
      gamma * Nat.card (CyclicLayer R initial gamma) +
        restrictedFirstBreakSum hR (initial ++ [gamma]) rest := by
  letI : NeZero R := ⟨Nat.ne_of_gt hR⟩
  classical
  rw [restrictedFirstBreakSum, restrictedFirstBreakSum]
  simp only [Characteristic.firstBreak]
  calc
    (∑ a : ZMod R, if a ∈ CyclicStabilizer R initial then
        (if FixesExponent a gamma then Characteristic.firstBreak a rest else gamma) else 0) =
        (∑ a : ZMod R, if a ∈ CyclicLayer R initial gamma then gamma else 0) +
          ∑ a : ZMod R, if a ∈ CyclicStabilizer R (initial ++ [gamma]) then
            Characteristic.firstBreak a rest else 0 := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro a _
      have happend := mem_cyclicStabilizer_append_iff initial gamma a
      by_cases hprev : a ∈ CyclicStabilizer R initial
      · by_cases hfix : FixesExponent a gamma
        · have hnext : a ∈ CyclicStabilizer R (initial ++ [gamma]) :=
            happend.mpr ⟨hprev, hfix⟩
          have hnlayer : a ∉ CyclicLayer R initial gamma := fun ha => ha.2 hnext
          simp [hprev, hfix, hnext, hnlayer]
        · have hnnext : a ∉ CyclicStabilizer R (initial ++ [gamma]) :=
            fun ha => hfix (happend.mp ha).2
          have hlayer : a ∈ CyclicLayer R initial gamma := ⟨hprev, hnnext⟩
          simp [hprev, hfix, hnnext, hlayer]
      · have hnnext : a ∉ CyclicStabilizer R (initial ++ [gamma]) :=
          fun ha => hprev (happend.mp ha).1
        have hnlayer : a ∉ CyclicLayer R initial gamma := fun ha => hprev ha.1
        simp [hprev, hnnext, hnlayer]
    _ = gamma * Nat.card (CyclicLayer R initial gamma) +
          ∑ a : ZMod R, if a ∈ CyclicStabilizer R (initial ++ [gamma]) then
            Characteristic.firstBreak a rest else 0 := by
      rw [sum_indicator_nat]

theorem galoisCoarea_eq_cyclicCoarea {R : ℕ} (hR : 0 < R)
    (initial rest : List ℕ) :
    galoisCoarea R initial rest =
      Characteristic.cyclicCoarea (cyclicGcd R initial) rest := by
  induction rest generalizing initial with
  | nil => rfl
  | cons gamma rest ih =>
      rw [galoisCoarea, cyclicLayer_card hR, ih,
        cyclicGcd_append_singleton, Characteristic.cyclicCoarea]

theorem restrictedFirstBreakSum_eq_galoisCoarea {R : ℕ} (hR : 0 < R)
    (initial rest : List ℕ) :
    restrictedFirstBreakSum hR initial rest = galoisCoarea R initial rest := by
  letI : NeZero R := ⟨Nat.ne_of_gt hR⟩
  induction rest generalizing initial with
  | nil =>
      classical
      rw [restrictedFirstBreakSum, galoisCoarea]
      apply Finset.sum_eq_zero
      intro a _
      by_cases h : a ∈ CyclicStabilizer R initial <;> simp [h, Characteristic.firstBreak]
  | cons gamma rest ih =>
      rw [restrictedFirstBreakSum_step hR, galoisCoarea, ih]

/-- **Cyclic stabilizer coarea source law.**  Characteristic irregularity is the weighted loss of
actual Galois-sheet stabilizers of its complex Puiseux polynomial. -/
theorem Characteristic.weightedIrregularity_eq_galoisCoarea {R beta : ℕ}
    (c : Characteristic R beta) :
    c.weightedIrregularity = galoisCoarea R [] c.levelExponents := by
  rw [galoisCoarea_eq_cyclicCoarea (Nat.zero_lt_one.trans c.ramification_gt_one)]
  exact c.cyclicCoarea_levelExponents.symm

/-- Actual sum of leading translated-difference numerators over all cyclic sheets. -/
noncomputable def Characteristic.sheetDifferenceNumeratorSum {R beta : ℕ}
    (c : Characteristic R beta) : ℕ := by
  letI : NeZero R := ⟨Nat.ne_of_gt (Nat.zero_lt_one.trans c.ramification_gt_one)⟩
  exact ∑ a : ZMod R, c.canonicalPuiseux.differenceNumerator a

/-- The actual one-base-sheet difference mass is the weighted characteristic irregularity. -/
theorem Characteristic.sheetDifferenceNumeratorSum_eq_weightedIrregularity {R beta : ℕ}
    (c : Characteristic R beta) :
    c.sheetDifferenceNumeratorSum = c.weightedIrregularity := by
  have hR : 0 < R := Nat.zero_lt_one.trans c.ramification_gt_one
  rw [c.weightedIrregularity_eq_galoisCoarea,
    ← restrictedFirstBreakSum_eq_galoisCoarea hR [] c.levelExponents]
  letI : NeZero R := ⟨Nat.ne_of_gt hR⟩
  classical
  rw [Characteristic.sheetDifferenceNumeratorSum, restrictedFirstBreakSum]
  apply Finset.sum_congr rfl
  intro a _
  rw [if_pos]
  · exact c.canonical_differenceNumerator_eq_firstBreak a
  · exact (mem_cyclicStabilizer_iff a).2 (by simp)

/-- Sum of actual leading-difference numerators over all ordered pairs of Galois sheets. -/
noncomputable def Characteristic.orderedPairDifferenceNumeratorSum {R beta : ℕ}
    (c : Characteristic R beta) : ℕ := by
  letI : NeZero R := ⟨Nat.ne_of_gt (Nat.zero_lt_one.trans c.ramification_gt_one)⟩
  exact ∑ a : ZMod R, ∑ b : ZMod R,
    c.canonicalPuiseux.pairDifferenceNumerator a b

/-- Translation invariance supplies `R` copies of the one-base-sheet numerator mass. -/
theorem Characteristic.orderedPairDifferenceNumeratorSum_eq {R beta : ℕ}
    (c : Characteristic R beta) :
    c.orderedPairDifferenceNumeratorSum = R * c.weightedIrregularity := by
  have hR : 0 < R := Nat.zero_lt_one.trans c.ramification_gt_one
  letI : NeZero R := ⟨Nat.ne_of_gt hR⟩
  classical
  have hinner (a : ZMod R) :
      (∑ b : ZMod R, c.canonicalPuiseux.pairDifferenceNumerator a b) =
        c.sheetDifferenceNumeratorSum := by
    calc
      (∑ b : ZMod R, c.canonicalPuiseux.pairDifferenceNumerator a b) =
          ∑ b : ZMod R, Characteristic.firstBreak (b - a) c.levelExponents := by
        apply Finset.sum_congr rfl
        intro b _
        exact c.canonical_pairDifferenceNumerator_eq_firstBreak a b
      _ = ∑ d : ZMod R, Characteristic.firstBreak d c.levelExponents := by
        exact Equiv.sum_comp (Equiv.subRight a)
          (fun d : ZMod R => Characteristic.firstBreak d c.levelExponents)
      _ = ∑ d : ZMod R, c.canonicalPuiseux.differenceNumerator d := by
        apply Finset.sum_congr rfl
        intro d _
        exact (c.canonical_differenceNumerator_eq_firstBreak d).symm
      _ = c.sheetDifferenceNumeratorSum := by
        rw [Characteristic.sheetDifferenceNumeratorSum]
  rw [Characteristic.orderedPairDifferenceNumeratorSum]
  calc
    (∑ a : ZMod R, ∑ b : ZMod R,
        c.canonicalPuiseux.pairDifferenceNumerator a b) =
        ∑ _a : ZMod R, c.sheetDifferenceNumeratorSum := by
      apply Finset.sum_congr rfl
      intro a _
      exact hinner a
    _ = R * c.sheetDifferenceNumeratorSum := by
      rw [Finset.sum_const, nsmul_eq_mul]
      have hcard : Fintype.card (ZMod R) = R := by
        rw [← Nat.card_eq_fintype_card, Nat.card_zmod]
      exact congrArg (fun n : ℕ => n * c.sheetDifferenceNumeratorSum) hcard
    _ = R * c.weightedIrregularity := by
      rw [c.sheetDifferenceNumeratorSum_eq_weightedIrregularity]

/-- Komatsu--Malgrange irregularity obtained by dividing ordered numerator mass by ramification. -/
noncomputable def Characteristic.endomorphismIrregularityFromSheets {R beta : ℕ}
    (c : Characteristic R beta) : ℕ := c.orderedPairDifferenceNumeratorSum / R

/-- Exact source identity: ordered Galois-sheet slopes equal weighted characteristic irregularity. -/
theorem Characteristic.endomorphismIrregularityFromSheets_eq {R beta : ℕ}
    (c : Characteristic R beta) :
    c.endomorphismIrregularityFromSheets = c.weightedIrregularity := by
  rw [Characteristic.endomorphismIrregularityFromSheets,
    c.orderedPairDifferenceNumeratorSum_eq]
  exact Nat.mul_div_cancel_left _ (Nat.zero_lt_one.trans c.ramification_gt_one)

/-- Diagonal Stokes loop reconstructed from actual ordered Puiseux-sheet differences. -/
noncomputable def Characteristic.diagonalLoopFromSheets {R beta : ℕ}
    (c : Characteristic R beta) : ℤ :=
  (c.endomorphismIrregularityFromSheets : ℤ) - (R : ℤ) ^ 2 + 1

/-- Douçot's loop formula is recovered exactly, not assumed at characteristic level. -/
theorem Characteristic.diagonalLoopFromSheets_eq {R beta : ℕ}
    (c : Characteristic R beta) : c.diagonalLoopFromSheets = c.diagonalLoop := by
  rw [Characteristic.diagonalLoopFromSheets, c.endomorphismIrregularityFromSheets_eq]
  rfl

end IrregularStokes
end GaloisForLFunctions
