import GaloisForLFunctions.HTGeometry.AugmentationGradedFormationSpectrum
import GaloisForLFunctions.HTGeometry.PolynomialShiftDifference

/-!
# Completion of the augmentation-graded formation spectrum

This file closes the exact annihilator, polynomial-clock classification, coefficient-`ℓ¹`
boundedness, minimal observer order, and reflected winding laws of ULF-TAFM-24.
-/

open scoped LaurentPolynomial

namespace GaloisForLFunctions.HTGeometry

noncomputable section

open LaurentPolynomial Polynomial

theorem augmentationBoundaryAnnihilator_iff
    (r : ℕ) (clock : ℤ → ℤ) :
    (∀ P : AugmentationFormationAlgebra,
      augmentationObserverPairing (augmentationFormationBoundary r P) clock = 0) ↔
      ∀ k : ℤ, augmentationIteratedForwardDifference r clock k = 0 := by
  constructor
  · intro h k
    have hk := h (LaurentPolynomial.C 1 * T k)
    rw [augmentationObserverPairing_boundary] at hk
    rw [augmentationObserverPairing_C_mul_T] at hk
    simpa using hk
  · intro h P
    rw [augmentationObserverPairing_boundary]
    simp [augmentationObserverPairing, h]

/-- Coefficient `ℓ¹` size of a finite Laurent history. -/
def augmentationCoefficientL1 (P : AugmentationFormationAlgebra) : ℤ :=
  P.coeff.sum fun _ q => |q|

def augmentationClockBoundedAtOrder (r : ℕ) (clock : ℤ → ℤ) : Prop :=
  ∃ C : ℤ, 0 ≤ C ∧
    ∀ k : ℤ, |augmentationIteratedForwardDifference r clock k| ≤ C

def augmentationBoundaryResponseBoundedAtOrder
    (r : ℕ) (clock : ℤ → ℤ) : Prop :=
  ∃ C : ℤ, 0 ≤ C ∧ ∀ P : AugmentationFormationAlgebra,
    |augmentationObserverPairing (augmentationFormationBoundary r P) clock| ≤
      C * augmentationCoefficientL1 P

private theorem abs_pairing_le
    {clock : ℤ → ℤ} {C : ℤ} (_hC : 0 ≤ C)
    (hclock : ∀ k, |clock k| ≤ C) (P : AugmentationFormationAlgebra) :
    |augmentationObserverPairing P clock| ≤ C * augmentationCoefficientL1 P := by
  unfold augmentationObserverPairing augmentationCoefficientL1
  calc
    |P.coeff.sum fun k q => q * clock k| ≤
        P.coeff.sum fun k q => |q * clock k| := by
      change |∑ k ∈ P.coeff.support, P.coeff k * clock k| ≤
        ∑ k ∈ P.coeff.support, |P.coeff k * clock k|
      exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ P.coeff.sum fun _ q => |q| * C := by
      apply Finsupp.sum_le_sum
      intro k hq
      rw [abs_mul]
      exact mul_le_mul_of_nonneg_left (hclock k) (abs_nonneg (P.coeff k))
    _ = C * P.coeff.sum fun _ q => |q| := by
      change (∑ k ∈ P.coeff.support, |P.coeff k| * C) =
        C * ∑ k ∈ P.coeff.support, |P.coeff k|
      rw [Finset.mul_sum]
      simp only [mul_comm]

theorem augmentationBoundaryResponseBoundedAtOrder_iff
    (r : ℕ) (clock : ℤ → ℤ) :
    augmentationBoundaryResponseBoundedAtOrder r clock ↔
      augmentationClockBoundedAtOrder r clock := by
  constructor
  · rintro ⟨C, hC, hbound⟩
    refine ⟨C, hC, fun k => ?_⟩
    have hk := hbound (LaurentPolynomial.C 1 * T k)
    rw [augmentationObserverPairing_boundary] at hk
    rw [augmentationObserverPairing_C_mul_T] at hk
    have hl1 : augmentationCoefficientL1 (T k) = 1 := by
      have hcoeff : (T k : AugmentationFormationAlgebra).coeff =
          Finsupp.single k 1 := by
        ext n
        rw [T_apply]
        simp [Finsupp.single_apply]
      unfold augmentationCoefficientL1
      rw [hcoeff]
      simp
    have hCT : (LaurentPolynomial.C 1 : AugmentationFormationAlgebra) * T k = T k := by
      simp
    rw [hCT, hl1, mul_one] at hk
    simpa using hk
  · rintro ⟨C, hC, hbound⟩
    refine ⟨C, hC, fun P => ?_⟩
    rw [augmentationObserverPairing_boundary]
    exact abs_pairing_le hC hbound P

private theorem augmentationIteratedForwardDifference_succ_apply
    (r : ℕ) (clock : ℤ → ℤ) (k : ℤ) :
    augmentationIteratedForwardDifference (r + 1) clock k =
      augmentationForwardDifference
        (augmentationIteratedForwardDifference r clock) k := by
  induction r generalizing clock with
  | zero => rfl
  | succ r ih =>
      rw [augmentationIteratedForwardDifference, ih]
      rfl

private theorem augmentationClockBoundedAtOrder_succ
    {r : ℕ} {clock : ℤ → ℤ}
    (h : augmentationClockBoundedAtOrder r clock) :
    augmentationClockBoundedAtOrder (r + 1) clock := by
  obtain ⟨C, hC, hbound⟩ := h
  refine ⟨2 * C, mul_nonneg (by omega) hC, fun k => ?_⟩
  rw [augmentationIteratedForwardDifference_succ_apply,
    augmentationForwardDifference]
  calc
    |augmentationIteratedForwardDifference r clock (k + 1) -
        augmentationIteratedForwardDifference r clock k| ≤
        |augmentationIteratedForwardDifference r clock (k + 1)| +
          |augmentationIteratedForwardDifference r clock k| := abs_sub _ _
    _ ≤ C + C := add_le_add (hbound (k + 1)) (hbound k)
    _ = 2 * C := by ring

private theorem augmentationClockBoundedAtOrder_mono
    {r s : ℕ} {clock : ℤ → ℤ} (hrs : r ≤ s)
    (h : augmentationClockBoundedAtOrder r clock) :
    augmentationClockBoundedAtOrder s clock := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hrs
  clear hrs
  induction d with
  | zero => simpa using h
  | succ d ih =>
      simpa [Nat.add_assoc] using augmentationClockBoundedAtOrder_succ ih

/-- If order `r` is bounded and order `r-1` is unbounded, `r` is the least recovery order with a
bounded coefficient-`ℓ¹` observer response. -/
theorem augmentationObserverOrder_isLeast
    {r : ℕ} {clock : ℤ → ℤ}
    (hr : augmentationClockBoundedAtOrder r clock)
    (hprev : ¬ augmentationClockBoundedAtOrder (r - 1) clock) :
    IsLeast {s : ℕ | augmentationBoundaryResponseBoundedAtOrder s clock} r := by
  have hrpos : 0 < r := by
    by_contra hzero
    have hr0 : r = 0 := by omega
    subst r
    exact hprev hr
  constructor
  · exact (augmentationBoundaryResponseBoundedAtOrder_iff r clock).2 hr
  · intro s hs
    by_contra hrs
    have hsr : s < r := Nat.lt_of_not_ge hrs
    have hsclock :=
      (augmentationBoundaryResponseBoundedAtOrder_iff s clock).1 hs
    exact hprev (augmentationClockBoundedAtOrder_mono (by omega) hsclock)

theorem augmentationCycleClosure_reflected_firstGradedResidue (p : ℕ) :
    SameModuloAugmentationBoundary 2
      (invert ((T (p : ℤ) : AugmentationFormationAlgebra) - 1))
      (-(p : AugmentationFormationAlgebra) * (T 1 - 1)) := by
  obtain ⟨D, hD⟩ := augmentationReflection_associatedGraded_parity
    1 (augmentationCycleCarrier p)
  have hfactor := augmentationCycleClosure_factorization p
  have hres := augmentationCycleClosure_firstGradedResidue p
  refine ⟨D - augmentationCycleCurvature p, ?_⟩
  simp only [augmentationFormationBoundary, pow_one] at hD
  rw [← hfactor] at hD
  calc
    invert ((T (p : ℤ) : AugmentationFormationAlgebra) - 1) -
          (-(p : AugmentationFormationAlgebra) * (T 1 - 1)) =
        (invert ((T (p : ℤ) : AugmentationFormationAlgebra) - 1) -
          (-1 : AugmentationFormationAlgebra) *
            ((T (p : ℤ) : AugmentationFormationAlgebra) - 1)) -
          (T 1 - 1) ^ (2 : ℕ) * augmentationCycleCurvature p := by
            rw [hres]
            ring
    _ = augmentationFormationBoundary 2 D -
          augmentationFormationBoundary 2 (augmentationCycleCurvature p) := by
      rw [hD]
      simp [augmentationFormationBoundary]
    _ = augmentationFormationBoundary 2
          (D - augmentationCycleCurvature p) := by
      simp [augmentationFormationBoundary]
      ring

/-- Degree-controlled discrete integration for the unit forward shift. -/
private theorem exists_shiftDiffPoly_eq_degree_lt :
    ∀ (n : ℕ) (p : Polynomial ℂ), p.degree < (n : WithBot ℕ) →
      ∃ q : Polynomial ℂ,
        q.degree < ((n + 1 : ℕ) : WithBot ℕ) ∧ shiftDiffPoly 1 q = p := by
  intro n
  induction n with
  | zero =>
      intro p hp
      have hp0 : p = 0 := by
        rw [← Polynomial.degree_eq_bot]
        exact Nat.WithBot.lt_zero_iff.mp (by exact_mod_cast hp)
      subst p
      exact ⟨0, by simp, by simp [shiftDiffPoly]⟩
  | succ n ih =>
      intro p hp
      set c : ℂ := p.coeff n with hc
      set residual : Polynomial ℂ := p - Polynomial.C c * fallPoly 1 n with hresidual
      have hresidualDegree : residual.degree < (n : WithBot ℕ) := by
        refine (Polynomial.degree_lt_iff_coeff_zero residual n).mpr fun m hm => ?_
        have hnm : n ≤ m := by exact_mod_cast hm
        rw [hresidual, Polynomial.coeff_sub, Polynomial.coeff_C_mul]
        rcases eq_or_lt_of_le hnm with rfl | hlt
        · rw [coeff_fallPoly_self, mul_one, ← hc, sub_self]
        · have hpm : p.coeff m = 0 := by
            refine Polynomial.coeff_eq_zero_of_degree_lt (lt_of_lt_of_le hp ?_)
            exact_mod_cast Nat.succ_le_of_lt hlt
          rw [hpm, coeff_fallPoly_eq_zero 1 hlt, mul_zero, sub_zero]
      obtain ⟨q, hqDegree, hqDiff⟩ := ih residual hresidualDegree
      have hden : ((n : ℂ) + 1) ≠ 0 := by
        exact_mod_cast Nat.succ_ne_zero n
      let top : Polynomial ℂ :=
        Polynomial.C (c / ((n : ℂ) + 1)) * fallPoly 1 (n + 1)
      have htopDiff : shiftDiffPoly 1 top = Polynomial.C c * fallPoly 1 n := by
        dsimp [top]
        rw [Polynomial.mul_comp, Polynomial.C_comp, ← mul_sub, shiftDiff_fallPoly]
        simp only [mul_one]
        rw [← mul_assoc, ← Polynomial.C_mul]
        field_simp
      have htopNatDegree : top.natDegree ≤ n + 1 := by
        dsimp [top]
        calc
          (Polynomial.C (c / ((n : ℂ) + 1)) *
              fallPoly 1 (n + 1)).natDegree ≤
              (Polynomial.C (c / ((n : ℂ) + 1))).natDegree +
                (fallPoly 1 (n + 1)).natDegree := Polynomial.natDegree_mul_le
          _ = n + 1 := by simp [natDegree_fallPoly]
      have htopDegree : top.degree < ((n + 2 : ℕ) : WithBot ℕ) := by
        refine lt_of_le_of_lt Polynomial.degree_le_natDegree ?_
        have hnat : top.natDegree < n + 2 := by omega
        exact WithBot.coe_lt_coe.mpr hnat
      refine ⟨q + top, ?_, ?_⟩
      · refine lt_of_le_of_lt (Polynomial.degree_add_le q top) ?_
        exact max_lt (hqDegree.trans (by exact_mod_cast Nat.lt_succ_self (n + 1))) htopDegree
      · rw [map_add, hqDiff, htopDiff]
        rw [hresidual]
        ring

/-- Complex polynomial clocks of degree strictly below the formation order. -/
def AugmentationPolynomialClockBelowOrder
    (r : ℕ) (clock : ℤ → ℤ) : Prop :=
  ∃ P : Polynomial ℂ, P.degree < (r : WithBot ℕ) ∧
    ∀ k : ℤ, P.eval (k : ℂ) = (clock k : ℂ)

private theorem polynomialClock_of_iteratedForwardDifference_eq_zero :
    ∀ (r : ℕ) (clock : ℤ → ℤ),
      (∀ k, augmentationIteratedForwardDifference r clock k = 0) →
        AugmentationPolynomialClockBelowOrder r clock := by
  intro r
  induction r with
  | zero =>
      intro clock h
      refine ⟨0, by simp, fun k => ?_⟩
      have hk : clock k = 0 := by
        simpa [augmentationIteratedForwardDifference] using h k
      rw [hk]
      simp
  | succ r ih =>
      intro clock h
      have hdiff : ∀ k,
          augmentationIteratedForwardDifference r
            (augmentationForwardDifference clock) k = 0 := h
      obtain ⟨Q, hQDegree, hQ⟩ := ih (augmentationForwardDifference clock) hdiff
      obtain ⟨P₀, hP₀Degree, hP₀Diff⟩ :=
        exists_shiftDiffPoly_eq_degree_lt r Q hQDegree
      let correction : ℂ := (clock 0 : ℂ) - P₀.eval 0
      let P : Polynomial ℂ := P₀ + Polynomial.C correction
      have hPdegree : P.degree < ((r + 1 : ℕ) : WithBot ℕ) := by
        refine lt_of_le_of_lt (Polynomial.degree_add_le _ _) ?_
        apply max_lt hP₀Degree
        refine lt_of_le_of_lt Polynomial.degree_C_le ?_
        exact WithBot.coe_lt_coe.mpr (Nat.succ_pos r)
      have hPdiff : shiftDiffPoly 1 P = Q := by
        change shiftDiffPoly 1 (P₀ + Polynomial.C correction) = Q
        rw [map_add, hP₀Diff]
        simp [shiftDiffPoly]
      have hstep : ∀ k : ℤ,
          P.eval ((k + 1 : ℤ) : ℂ) - P.eval (k : ℂ) =
            ((clock (k + 1) - clock k : ℤ) : ℂ) := by
        intro k
        have heval := congrArg (Polynomial.eval (k : ℂ)) hPdiff
        rw [shiftDiffPoly_apply, Polynomial.eval_sub, Polynomial.eval_comp] at heval
        simp only [Polynomial.eval_add, Polynomial.eval_X, Polynomial.eval_C] at heval
        rw [hQ k] at heval
        simpa [augmentationForwardDifference] using heval
      have hzero : P.eval (0 : ℂ) = (clock 0 : ℂ) := by
        dsimp [P, correction]
        simp
      refine ⟨P, hPdegree, fun k => ?_⟩
      induction k using Int.induction_on with
      | zero => simpa using hzero
      | succ i hi =>
          have hs := hstep (i : ℤ)
          rw [hi] at hs
          have hcast : ((clock ((i : ℤ) + 1) - clock (i : ℤ) : ℤ) : ℂ) =
              (clock ((i : ℤ) + 1) : ℂ) - (clock (i : ℤ) : ℂ) := by
            push_cast
            rfl
          rw [hcast] at hs
          linear_combination hs
      | pred i hi =>
          have hs := hstep (-(i : ℤ) - 1)
          have hindex : -(i : ℤ) - 1 + 1 = -(i : ℤ) := by omega
          rw [hindex, hi] at hs
          have hcast : ((clock (-(i : ℤ)) - clock (-(i : ℤ) - 1) : ℤ) : ℂ) =
              (clock (-(i : ℤ)) : ℂ) - (clock (-(i : ℤ) - 1) : ℂ) := by
            push_cast
            rfl
          rw [hcast] at hs
          linear_combination -hs

private theorem shiftDiffPoly_degree_lt
    {P : Polynomial ℂ} (hP : P ≠ 0) :
    (shiftDiffPoly 1 P).degree < P.degree := by
  by_cases hdeg : P.natDegree = 0
  · obtain ⟨c, hc⟩ := Polynomial.natDegree_eq_zero.mp hdeg
    have hc0 : c ≠ 0 := by
      intro hcz
      apply hP
      rw [← hc, hcz, map_zero]
    rw [← hc]
    simp [shiftDiffPoly, Polynomial.degree_C hc0]
  · have hcompdeg : (P.comp (Polynomial.X + Polynomial.C 1)).natDegree = P.natDegree := by
      rw [Polynomial.natDegree_comp, Polynomial.natDegree_X_add_C, mul_one]
    have hlead : (P.comp (Polynomial.X + Polynomial.C 1)).leadingCoeff =
        P.leadingCoeff := by
      rw [Polynomial.leadingCoeff_comp (by
        rw [Polynomial.natDegree_X_add_C]
        norm_num)]
      rw [Polynomial.leadingCoeff_X_add_C, one_pow, mul_one]
    have hcoeffTop :
        (P.comp (Polynomial.X + Polynomial.C 1) - P).coeff P.natDegree = 0 := by
      rw [Polynomial.coeff_sub]
      have h1 : P.coeff P.natDegree = P.leadingCoeff := rfl
      have h2 : (P.comp (Polynomial.X + Polynomial.C 1)).coeff P.natDegree =
          P.leadingCoeff := by
        rw [← hcompdeg]
        exact hlead
      rw [h1, h2, sub_self]
    have hle : (P.comp (Polynomial.X + Polynomial.C 1) - P).natDegree ≤
        P.natDegree := le_trans (Polynomial.natDegree_sub_le _ _) (by rw [hcompdeg, max_self])
    by_cases hzero : shiftDiffPoly 1 P = 0
    · rw [hzero, Polynomial.degree_zero, Polynomial.degree_eq_natDegree hP]
      exact WithBot.bot_lt_coe _
    · have hlt : (shiftDiffPoly 1 P).natDegree < P.natDegree := by
        change P.comp (Polynomial.X + Polynomial.C 1) - P ≠ 0 at hzero
        rcases lt_or_eq_of_le hle with hlt | heq
        · exact hlt
        · exfalso
          have hlc := Polynomial.leadingCoeff_ne_zero.mpr hzero
          rw [Polynomial.leadingCoeff, heq] at hlc
          exact hlc hcoeffTop
      rw [Polynomial.degree_eq_natDegree hzero, Polynomial.degree_eq_natDegree hP]
      exact WithBot.coe_lt_coe.mpr hlt

private theorem shiftDiffPoly_degree_lt_order
    {r : ℕ} {P : Polynomial ℂ} (hPdegree : P.degree < ((r + 1 : ℕ) : WithBot ℕ)) :
    (shiftDiffPoly 1 P).degree < (r : WithBot ℕ) := by
  by_cases hP : P = 0
  · subst P
    simp [shiftDiffPoly]
  have hdrop := shiftDiffPoly_degree_lt hP
  by_cases hdiff : shiftDiffPoly 1 P = 0
  · rw [hdiff, Polynomial.degree_zero]
    exact WithBot.bot_lt_coe _
  have hPnat : P.natDegree < r + 1 := by
    rw [Polynomial.degree_eq_natDegree hP] at hPdegree
    exact WithBot.coe_lt_coe.mp hPdegree
  have hdiffNat : (shiftDiffPoly 1 P).natDegree < P.natDegree := by
    rw [Polynomial.degree_eq_natDegree hdiff,
      Polynomial.degree_eq_natDegree hP] at hdrop
    exact WithBot.coe_lt_coe.mp hdrop
  rw [Polynomial.degree_eq_natDegree hdiff]
  exact WithBot.coe_lt_coe.mpr (lt_of_lt_of_le hdiffNat (Nat.lt_succ_iff.mp hPnat))

private def iteratedShiftDiffPoly : ℕ → Polynomial ℂ → Polynomial ℂ
  | 0, P => P
  | r + 1, P => iteratedShiftDiffPoly r (shiftDiffPoly 1 P)

private theorem iteratedShiftDiffPoly_eq_zero
    {r : ℕ} {P : Polynomial ℂ} (hP : P.degree < (r : WithBot ℕ)) :
    iteratedShiftDiffPoly r P = 0 := by
  induction r generalizing P with
  | zero =>
      have : P = 0 := by
        rw [← Polynomial.degree_eq_bot]
        exact Nat.WithBot.lt_zero_iff.mp (by exact_mod_cast hP)
      simp [iteratedShiftDiffPoly, this]
  | succ r ih =>
      rw [iteratedShiftDiffPoly]
      exact ih (shiftDiffPoly_degree_lt_order hP)

private def complexForwardDifference (clock : ℤ → ℂ) (k : ℤ) : ℂ :=
  clock (k + 1) - clock k

private def complexIteratedForwardDifference : ℕ → (ℤ → ℂ) → (ℤ → ℂ)
  | 0, clock => clock
  | r + 1, clock =>
      complexIteratedForwardDifference r (complexForwardDifference clock)

private theorem eval_iteratedShiftDiffPoly
    (r : ℕ) (P : Polynomial ℂ) (k : ℤ) :
    (iteratedShiftDiffPoly r P).eval (k : ℂ) =
      complexIteratedForwardDifference r (fun j : ℤ => P.eval (j : ℂ)) k := by
  induction r generalizing P with
  | zero => rfl
  | succ r ih =>
      rw [iteratedShiftDiffPoly, complexIteratedForwardDifference, ih]
      congr 1
      funext j
      simp [complexForwardDifference, shiftDiffPoly,
        Polynomial.eval_comp]

private theorem complexIteratedForwardDifference_intCast
    (r : ℕ) (clock : ℤ → ℤ) (k : ℤ) :
    complexIteratedForwardDifference r (fun j => (clock j : ℂ)) k =
      (augmentationIteratedForwardDifference r clock k : ℂ) := by
  induction r generalizing clock with
  | zero => rfl
  | succ r ih =>
      rw [complexIteratedForwardDifference,
        augmentationIteratedForwardDifference]
      have hfun : complexForwardDifference (fun j => (clock j : ℂ)) =
          fun j => (augmentationForwardDifference clock j : ℂ) := by
        funext j
        simp [complexForwardDifference, augmentationForwardDifference]
      rw [hfun]
      exact ih (augmentationForwardDifference clock)

private theorem iteratedForwardDifference_eq_zero_of_polynomialClock
    {r : ℕ} {clock : ℤ → ℤ}
    (hclock : AugmentationPolynomialClockBelowOrder r clock) :
    ∀ k, augmentationIteratedForwardDifference r clock k = 0 := by
  obtain ⟨P, hPdegree, hP⟩ := hclock
  have hzero := iteratedShiftDiffPoly_eq_zero hPdegree
  intro k
  have heval := congrArg (Polynomial.eval (k : ℂ)) hzero
  rw [eval_iteratedShiftDiffPoly] at heval
  have hfun : (fun j : ℤ => P.eval (j : ℂ)) = fun j => (clock j : ℂ) := by
    funext j
    exact hP j
  rw [hfun, complexIteratedForwardDifference_intCast] at heval
  have hcast : (augmentationIteratedForwardDifference r clock k : ℂ) = 0 := by
    simpa using heval
  exact_mod_cast hcast

/-- The algebraic clock annihilator is exactly the complex-polynomial clock space below order
`r`, restricted to integer-valued clocks on `ℤ`. -/
theorem augmentationIteratedForwardDifference_eq_zero_iff_polynomialClock
    (r : ℕ) (clock : ℤ → ℤ) :
    (∀ k, augmentationIteratedForwardDifference r clock k = 0) ↔
      AugmentationPolynomialClockBelowOrder r clock := by
  exact ⟨polynomialClock_of_iteratedForwardDifference_eq_zero r clock,
    iteratedForwardDifference_eq_zero_of_polynomialClock⟩

/-- Zero-argument certificate for the complete augmentation-graded formation law. -/
theorem augmentationGradedFormationSpectrum_completion_certificate :
    (∀ r : ℕ, Function.Injective (augmentationFormationBoundary r)) ∧
    (∀ (r : ℕ) (P : AugmentationFormationAlgebra) (clock : ℤ → ℤ),
      augmentationObserverPairing (augmentationFormationBoundary r P) clock =
        augmentationObserverPairing P
          (augmentationIteratedForwardDifference r clock)) ∧
    (∀ (r : ℕ) (P : AugmentationFormationAlgebra),
      invert (augmentationFormationBoundary r P) =
        (-1) ^ r * augmentationFormationBoundary r
          (augmentationHistoryReflection r P)) ∧
    (∀ r : ℕ, Function.Involutive (augmentationHistoryReflection r)) ∧
    (∀ (r : ℕ) (P : AugmentationFormationAlgebra),
      SameModuloAugmentationBoundary (r + 1)
        (invert (augmentationFormationBoundary r P))
        ((-1 : AugmentationFormationAlgebra) ^ r *
          augmentationFormationBoundary r P)) ∧
    (∀ r : ℕ, ∀ x y : ℤ,
      (((-1 : ℤ) ^ r * x) ^ (2 : ℕ) = x ^ (2 : ℕ)) ∧
        ((-1 : ℤ) ^ r * x) * ((-1 : ℤ) ^ (r + 1) * y) = -(x * y)) ∧
    (∀ p : ℕ,
      (T (p : ℤ) : AugmentationFormationAlgebra) - 1 =
        (T 1 - 1) * augmentationCycleCarrier p ∧
      augmentationObserver (augmentationCycleCarrier p) = p ∧
      (T (p : ℤ) : AugmentationFormationAlgebra) - 1 =
        (p : AugmentationFormationAlgebra) * (T 1 - 1) +
          (T 1 - 1) ^ (2 : ℕ) * augmentationCycleCurvature p) ∧
    (∀ (r : ℕ) (clock : ℤ → ℤ),
      (∀ P : AugmentationFormationAlgebra,
        augmentationObserverPairing (augmentationFormationBoundary r P) clock = 0) ↔
        AugmentationPolynomialClockBelowOrder r clock) ∧
    (∀ (r : ℕ) (clock : ℤ → ℤ),
      augmentationBoundaryResponseBoundedAtOrder r clock ↔
        augmentationClockBoundedAtOrder r clock) ∧
    (∀ (r : ℕ) (clock : ℤ → ℤ),
      augmentationClockBoundedAtOrder r clock →
      (¬ augmentationClockBoundedAtOrder (r - 1) clock) →
      IsLeast
        {s : ℕ | augmentationBoundaryResponseBoundedAtOrder s clock} r) ∧
    (∀ p : ℕ,
      SameModuloAugmentationBoundary 2
        (invert ((T (p : ℤ) : AugmentationFormationAlgebra) - 1))
        (-(p : AugmentationFormationAlgebra) * (T 1 - 1))) := by
  exact ⟨augmentationFormationBoundary_injective,
    augmentationObserverPairing_boundary,
    invert_augmentationFormationBoundary,
    augmentationHistoryReflection_involutive,
    augmentationReflection_associatedGraded_parity,
    augmentationAdjacentGrade_orientationParity,
    fun p => ⟨augmentationCycleClosure_factorization p,
      augmentationObserver_cycleCarrier p,
      augmentationCycleClosure_firstGradedResidue p⟩,
    fun r clock => (augmentationBoundaryAnnihilator_iff r clock).trans
      (augmentationIteratedForwardDifference_eq_zero_iff_polynomialClock r clock),
    augmentationBoundaryResponseBoundedAtOrder_iff,
    fun _ _ => augmentationObserverOrder_isLeast,
    augmentationCycleClosure_reflected_firstGradedResidue⟩

end

end GaloisForLFunctions.HTGeometry

