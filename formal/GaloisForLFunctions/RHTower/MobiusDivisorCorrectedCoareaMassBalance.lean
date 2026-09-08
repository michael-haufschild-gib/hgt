import GaloisForLFunctions.RHTower.MobiusDivisorFibreCoareaVariance
import GaloisForLFunctions.RHTower.MobiusDivisorCorrectedCoareaAction
import GaloisForLFunctions.RHTower.MobiusDivisorPositiveNormalizationCost

/-!
# The signed-mass component that survives the late-diagonal correction

Removing remaining isolated late singletons leaves absolute mass `U-r`
and signed mass `S+r`. Corrected action is head mass times this retained
conditional energy plus the exact late diagonal. Its unavoidable component
is therefore `a*(S+r)^2/(U-r)`, with an exact nonnegative variance remainder.
In particular consumed late mass `t` forces `t*(S+r)^2 ≤ U*H_corrected`.
-/
noncomputable section
set_option autoImplicit false
open Finset
namespace RHTower

/-- All source labels except the remaining isolated active late singleton labels. -/
def mobiusDivisorRetainedCoareaLabels (M : ℕ) (P : Finset ℕ) : Finset (Finset ℕ) :=
  (mobiusDivisorSelectionPrimes M).powerset \
    (mobiusDivisorActiveLatePrimes M \ P).image (fun p => ({p}:Finset ℕ))

private lemma late_subset (M : ℕ) (P : Finset ℕ) :
    (mobiusDivisorActiveLatePrimes M \ P).image (fun p => ({p}:Finset ℕ)) ⊆
      (mobiusDivisorSelectionPrimes M).powerset := by
  intro R hR
  obtain ⟨p,hp,rfl⟩ := mem_image.mp hR
  have h := mem_mobiusDivisorActiveLatePrimes (mem_sdiff.mp hp).1
  have hpU : p ∈ mobiusDivisorSelectionPrimes M := mem_filter.mpr ⟨mem_range.mpr h.2.1,h.1⟩
  simp [hpU]

private lemma sum_split (M : ℕ) (P : Finset ℕ) (f : Finset ℕ → ℝ) :
    (∑ R ∈ mobiusDivisorRetainedCoareaLabels M P, f R) +
      (∑ p ∈ mobiusDivisorActiveLatePrimes M \ P, f {p}) =
      ∑ R ∈ (mobiusDivisorSelectionPrimes M).powerset, f R := by
  have h := sum_sdiff (f:=f) (late_subset M P)
  rw [sum_image (by intro a _ b _ he; simpa using he)] at h
  exact h

/-- Every retained partition conserves the full original absolute source mass. -/
theorem sum_mobiusDivisorFibreAbsoluteMass (M : ℕ) (P : Finset ℕ) :
    (∑ R ∈ (mobiusDivisorSelectionPrimes M).powerset, mobiusDivisorFibreAbsoluteMass M P R) =
      mobiusDivisorAbsoluteMass M := by
  have hlabels : ∀ d ∈ mobiusDivisorSelectionIndices M,
      d.primeFactors ⊆ mobiusDivisorSelectionPrimes M := by
    intro d hd p hp
    have hdM := mem_Icc.mp (mem_filter.mp hd).1
    have hpd := Nat.le_of_mem_primeFactors hp
    exact mem_filter.mpr ⟨mem_range.mpr (by omega),(Nat.mem_primeFactors.mp hp).1⟩
  change (∑ R ∈ (mobiusDivisorSelectionPrimes M).powerset,
    subsetLabelFibre _ _ _ P R) = _
  rw [subsetLabelFibre_sum _ _ _ _ hlabels]
  calc
    _ = ∑ d ∈ Icc 1 (M-1), |mobiusDivisorDilationChannel M d| := by
      rw [mobiusDivisorSelectionIndices,sum_filter]
      apply sum_congr rfl
      intro d _
      by_cases hs : Squarefree d
      · simp [hs]
      · simp [hs,mobiusDivisorDilationChannel,ArithmeticFunction.moebius_eq_zero_of_not_squarefree hs]
    _ = _ := by
      apply sum_subset
      · intro d hd
        have h := mem_Icc.mp hd
        exact mem_Icc.mpr ⟨h.1,by omega⟩
      · intro d hd hn
        have he : d=M := by simp only [mem_Icc] at hd hn; omega
        subst d
        by_cases hM : M=0
        · simp [hM,mobiusDivisorDilationChannel]
        · simp [mobiusDivisorDilationChannel,Icc_eq_empty_of_lt (by omega : M-1<M)]

/-- Removing negative late cells leaves signed mass equal to the full total plus remaining late mass. -/
theorem sum_mobiusDivisorRetainedCoarea_signed (M : ℕ) (P : Finset ℕ) :
    (∑ R ∈ mobiusDivisorRetainedCoareaLabels M P, mobiusDivisorSelectionFibre M P R) =
      (∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d)+mobiusDivisorRemainingLateMass M P := by
  have h := sum_split M P (mobiusDivisorSelectionFibre M P)
  have hl : (∑ p ∈ mobiusDivisorActiveLatePrimes M \ P, mobiusDivisorSelectionFibre M P {p}) =
      -mobiusDivisorRemainingLateMass M P := by
    unfold mobiusDivisorRemainingLateMass
    rw [← sum_neg_distrib]
    apply sum_congr rfl
    intro p hp
    have hpr := mem_mobiusDivisorActiveLatePrimes (mem_sdiff.mp hp).1
    rw [mobiusDivisorSelectionFibre_late_prime hpr.1 hpr.2.1 hpr.2.2 P {p}
      (mem_sdiff.mp hp).2 (mem_singleton_self p),if_pos rfl,
      abs_of_nonpos (mobiusDivisorDilationChannel_late_prime_nonpos hpr.1 M)]
    ring
  rw [hl,mobiusDivisorSelectionFibre_sum] at h
  linarith only [h]

/-- Removing isolated late cells subtracts precisely their original absolute mass. -/
theorem sum_mobiusDivisorRetainedCoarea_mass (M : ℕ) (P : Finset ℕ) :
    (∑ R ∈ mobiusDivisorRetainedCoareaLabels M P, mobiusDivisorFibreAbsoluteMass M P R) =
      mobiusDivisorAbsoluteMass M-mobiusDivisorRemainingLateMass M P := by
  have h := sum_split M P (mobiusDivisorFibreAbsoluteMass M P)
  have hl : (∑ p ∈ mobiusDivisorActiveLatePrimes M \ P, mobiusDivisorFibreAbsoluteMass M P {p}) =
      mobiusDivisorRemainingLateMass M P := by
    apply sum_congr rfl
    intro p hp
    have hpr := mem_mobiusDivisorActiveLatePrimes (mem_sdiff.mp hp).1
    rw [mobiusDivisorFibreAbsoluteMass_late_prime hpr.1 hpr.2.1 hpr.2.2 P {p}
      (mem_sdiff.mp hp).2 (mem_singleton_self p),if_pos rfl]
  rw [hl,sum_mobiusDivisorFibreAbsoluteMass] at h
  linarith only [h]

/-- Corrected action is exactly head mass times retained coarea plus the original late diagonal. -/
theorem mobiusDivisorCorrectedCoareaAction_eq_retained (M : ℕ) (P : Finset ℕ) :
    mobiusDivisorCorrectedCoareaAction M P = mobiusDivisorFibreAbsoluteMass M P ∅ *
      (∑ R ∈ mobiusDivisorRetainedCoareaLabels M P,
        (mobiusDivisorSelectionFibre M P R)^2 / mobiusDivisorFibreAbsoluteMass M P R) +
      mobiusDivisorRemainingLateEnergy M P := by
  have h := sum_split M P (fun R =>
    (mobiusDivisorSelectionFibre M P R)^2 / mobiusDivisorFibreAbsoluteMass M P R)
  have hl : (∑ p ∈ mobiusDivisorActiveLatePrimes M \ P,
      (mobiusDivisorSelectionFibre M P {p})^2 / mobiusDivisorFibreAbsoluteMass M P {p}) =
      mobiusDivisorRemainingLateMass M P := sum_congr rfl (fun p hp =>
        mobiusDivisorCoarea_activeLate_singleton (mem_sdiff.mp hp).1 P (mem_sdiff.mp hp).2)
  rw [hl] at h
  rw [mobiusDivisorCorrectedCoareaAction_eq_correction,
    mobiusDivisorCoareaHeadAction_eq_mass_mul_coarea,← h]
  ring

/-- The corrected action has an exact forced signed-mass term and nonnegative variance remainder. -/
theorem mobiusDivisorCorrectedCoareaAction_eq_variance (M : ℕ) (P : Finset ℕ) :
    mobiusDivisorCorrectedCoareaAction M P = mobiusDivisorFibreAbsoluteMass M P ∅ *
      (((∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d)+mobiusDivisorRemainingLateMass M P)^2 /
        (mobiusDivisorAbsoluteMass M-mobiusDivisorRemainingLateMass M P) +
       ∑ R ∈ mobiusDivisorRetainedCoareaLabels M P,
        (mobiusDivisorSelectionFibre M P R-
          (((∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d)+mobiusDivisorRemainingLateMass M P) /
            (mobiusDivisorAbsoluteMass M-mobiusDivisorRemainingLateMass M P)) *
              mobiusDivisorFibreAbsoluteMass M P R)^2 / mobiusDivisorFibreAbsoluteMass M P R) +
      mobiusDivisorRemainingLateEnergy M P := by
  rw [mobiusDivisorCorrectedCoareaAction_eq_retained,mobiusDivisorFibre_coarea_variance,
    sum_mobiusDivisorRetainedCoarea_signed,sum_mobiusDivisorRetainedCoarea_mass]

/-- Corrected action is nonnegative at every actual state. -/
theorem mobiusDivisorCorrectedCoareaAction_nonneg (M : ℕ) (P : Finset ℕ) :
    0 ≤ mobiusDivisorCorrectedCoareaAction M P := by
  unfold mobiusDivisorCorrectedCoareaAction
  exact add_nonneg (add_nonneg (sq_nonneg _) (mul_nonneg
    (mobiusDivisorFibreAbsoluteMass_nonneg M P ∅) (mobiusDivisorMixedCoarea_nonneg M P)))
    (sum_nonneg (fun _ _ => sq_nonneg _))

/-- Mass conservation alone forces a lower bound on corrected action, irrespective of mixed cancellation. -/
theorem mobiusDivisorCorrectedCoareaAction_mass_balance (M : ℕ) (P : Finset ℕ) :
    mobiusDivisorConsumedLateMass M P *
      ((∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d)+mobiusDivisorRemainingLateMass M P)^2 ≤
      mobiusDivisorAbsoluteMass M * mobiusDivisorCorrectedCoareaAction M P := by
  let J := ∑ R ∈ mobiusDivisorRetainedCoareaLabels M P,
    (mobiusDivisorSelectionFibre M P R)^2 / mobiusDivisorFibreAbsoluteMass M P R
  have hJ : 0 ≤ J := sum_nonneg (fun R _ => div_nonneg (sq_nonneg _)
    (mobiusDivisorFibreAbsoluteMass_nonneg M P R))
  have hc := mobiusDivisorFibre_coarea_cauchy M P (mobiusDivisorRetainedCoareaLabels M P)
  rw [sum_mobiusDivisorRetainedCoarea_signed,sum_mobiusDivisorRetainedCoarea_mass] at hc
  have ha := mobiusDivisorFibreAbsoluteMass_nonneg M P ∅
  have hU : 0 ≤ mobiusDivisorAbsoluteMass M := sum_nonneg (fun _ _ => abs_nonneg _)
  have hr : 0 ≤ mobiusDivisorRemainingLateMass M P := sum_nonneg (fun _ _ => abs_nonneg _)
  have he : 0 ≤ mobiusDivisorRemainingLateEnergy M P := sum_nonneg (fun _ _ => sq_nonneg _)
  have haction := mobiusDivisorCorrectedCoareaAction_eq_retained M P
  calc
    _ ≤ mobiusDivisorFibreAbsoluteMass M P ∅ *
        ((∑ d ∈ Icc 1 M, mobiusDivisorDilationChannel M d)+mobiusDivisorRemainingLateMass M P)^2 :=
      mul_le_mul_of_nonneg_right (mobiusDivisorConsumedLateMass_le_headMass M P) (sq_nonneg _)
    _ ≤ mobiusDivisorFibreAbsoluteMass M P ∅ *
        ((mobiusDivisorAbsoluteMass M-mobiusDivisorRemainingLateMass M P)*J) :=
      mul_le_mul_of_nonneg_left hc ha
    _ ≤ mobiusDivisorAbsoluteMass M * (mobiusDivisorFibreAbsoluteMass M P ∅*J) := by
      nlinarith only [mul_nonneg hr (mul_nonneg ha hJ)]
    _ ≤ _ := by rw [haction]; nlinarith only [mul_nonneg hU he]

end RHTower
