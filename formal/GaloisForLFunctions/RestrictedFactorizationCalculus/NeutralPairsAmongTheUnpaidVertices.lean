import GaloisForLFunctions.RestrictedFactorizationCalculus.ThePowerExponentOfEveryUnsignedPrefix
import GaloisForLFunctions.RestrictedFactorizationCalculus.TheMertensAbscissaOnOneDensityZeroFixedSet
import GaloisForLFunctions.BezoutValuationIncidence.TheVaughanEmptyLegReadsTheZeroAbscissa
import GaloisForLFunctions.ZeroForcingCalculus.EulerDilationAndRootCoincidenceExclusion

/-!
# Opposite signs surviving at the same cutoff

The smaller sign class of the unpaid set counts exactly how many further
pairs could be removed by unrestricted opposite-sign matching. Even this
neutral population has sharp power exponent one.
-/

noncomputable section

open Finset Filter
open ArithmeticFunction hiding id
open scoped Classical ArithmeticFunction.Moebius
open GaloisForLFunctions.QuantitativeFactorizationMatching GaloisForLFunctions.BezoutValuationIncidence

namespace GaloisForLFunctions.RestrictedFactorizationCalculus

/-- Maximum number of disjoint pairs of opposite signs in the unpaid set
when there is no restriction on their factorization. -/
def neutralUnpaid (F : ℕ → ℕ) (X : ℕ) :=
  min (posParity (prefixUnpaid F X)).card (negParity (prefixUnpaid F X)).card

/-- Exact separation of the net Möbius mass and the neutral population. -/
theorem neutral_unpaid_decomposition (F : ℕ → ℕ) (hF : ∀ n,Squarefree n →
    F (F n)=n ∧ (F n=n ∨ GlobalDyadicOneTwoRel n (F n))) (X : ℕ) :
    ((prefixUnpaid F X).card:ℝ)=2*(neutralUnpaid F X:ℝ)+|coprimeMoebiusSum 1 X| := by
  let S := prefixUnpaid F X
  have hs : squarefreeOf S=S := filter_eq_self.mpr (fun _ hn => (mem_filter.mp (mem_filter.mp hn).1).2)
  have hsize := card_squarefreeOf S
  rw [hs] at hsize
  have hbal := (prefix_switch_balance F hF X).trans (sum_moebius_eq_card_pos_sub_neg S)
  have hcast : (∑ n ∈ Icc 1 X,(μ n:ℝ))=((posParity S).card:ℝ)-((negParity S).card:ℝ) := by exact_mod_cast hbal
  have hm : coprimeMoebiusSum 1 X=∑ n ∈ Icc 1 X,(μ n:ℝ) := by
    simp [coprimeMoebiusSum,coprimeMoebiusIndicator]
  rw [hm,hcast]
  change (S.card:ℝ)=2*(min (posParity S).card (negParity S).card:ℕ)+_
  rw [hsize,Nat.cast_add]
  rcases le_total (posParity S).card (negParity S).card with h | h
  · rw [min_eq_left h,abs_of_nonpos (sub_nonpos.mpr (Nat.cast_le.mpr h))]
    ring
  · rw [min_eq_right h,abs_of_nonneg (sub_nonneg.mpr (Nat.cast_le.mpr h))]
    ring

private theorem full_strip_power {t : ℝ} (ht : 20999/24000<t) : PrefixPower t (coprimeMoebiusSum 1) := by
  obtain ⟨C,hC,h⟩ := exists_moebius_power_bound_of_abscissa_lt
    (ZeroForcingCalculus.zetaZeroAbscissa_le_sub_seven_eighths.trans_lt ht)
  refine ⟨C,hC,fun n => ?_⟩
  by_cases hn : n=0
  · simp [hn,coprimeMoebiusSum,Real.zero_rpow (by linarith only [ht] : t ≠ 0)]
  simpa [coprimeMoebiusSum,coprimeMoebiusIndicator,moebiusReal] using h n (Nat.pos_of_ne_zero hn)

/-- Both signs must be large at the same cutoffs. The unmatched mass left
after subtracting the exact signed discrepancy still has exponent one. -/
theorem neutral_unpaid_power_iff (F : ℕ → ℕ) (hF : ∀ n,Squarefree n →
    F (F n)=n ∧ (F n=n ∨ GlobalDyadicOneTwoRel n (F n))) {θ : ℝ} (hθ : 0<θ) :
    PrefixPower θ (fun X => (neutralUnpaid F X:ℝ)) ↔ 1 ≤ θ := by
  constructor
  · rintro ⟨C,hC,h⟩
    by_contra! hlt
    let s := max θ (7/8)
    have hts : θ ≤ s := le_max_left ..
    have hβs : (7/8:ℝ) ≤ s := le_max_right ..
    have hs : s<1 := max_lt hlt (by norm_num)
    obtain ⟨K,hK,hM⟩ := full_strip_power (by norm_num : (20999:ℝ)/24000<7/8)
    apply hs.not_ge ((unsigned_prefix_power_iff F hF (hθ.trans_le hts)).1 ?_)
    refine ⟨2*C+K,by positivity,fun X => ?_⟩
    change |((prefixUnpaid F X).card:ℝ)| ≤ _
    rw [abs_of_nonneg (Nat.cast_nonneg _),neutral_unpaid_decomposition F hF]
    by_cases hx : X=0
    · simp [hx,neutralUnpaid,prefixUnpaid,squarefreeOf,posParity,negParity,coprimeMoebiusSum,
        Real.zero_rpow (hθ.trans_le hts).ne']
    have hx1 : (1:ℝ) ≤ X := by exact_mod_cast Nat.pos_of_ne_zero hx
    have hu := h X
    change |(neutralUnpaid F X:ℝ)| ≤ _ at hu
    rw [abs_of_nonneg (Nat.cast_nonneg _)] at hu
    have hc' := hu.trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 hts) hC)
    have hk' := (hM X).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hx1 hβs) hK)
    linarith only [hc',hk']
  · intro hθ1
    obtain ⟨K,hK,h⟩ := (unsigned_prefix_power_iff F hF hθ).2 hθ1
    refine ⟨K,hK,fun X => ?_⟩
    rw [abs_of_nonneg (Nat.cast_nonneg _)]
    have hcost : neutralUnpaid F X ≤ (prefixUnpaid F X).card := (min_le_left ..).trans (card_le_card (filter_subset ..))
    exact (Nat.cast_le.mpr hcost).trans ((le_abs_self _).trans (h X))

/-- In a single sublinearly short matching of density one, both signed
components separately attain every power above the corpus zero-free strip.
Their smaller unsigned sign class still has exact power exponent one. -/
theorem separate_signed_savings_on_one_short_involution :
    ∃ F : ℕ → ℕ, (∀ n,F (F n)=n ∧ (F n=n ∨ GlobalDyadicOneTwoRel n (F n))) ∧
      (∀ ε : ℝ,0<ε → ∀ᶠ X : ℕ in Filter.atTop,
        ((prefixUnpaid F X).card:ℝ) ≤ ε*X ∧ |(F X:ℝ)-X| ≤ ε*X) ∧
      (∀ t : ℝ,20999/24000<t → PrefixPower t (fixedSignedPrefix F) ∧ PrefixPower t (crossingSignedPrefix F)) ∧
      ∀ θ : ℝ,0<θ → (PrefixPower θ (fun X => (neutralUnpaid F X:ℝ)) ↔ 1 ≤ θ) := by
  obtain ⟨F,hF,hcount,htransfer⟩ := one_density_zero_fixed_set_detects_the_mertens_abscissa
  have law := fun (n : ℕ) (_ : Squarefree n) => hF n
  refine ⟨F,hF,hcount,?_,fun _ ht => neutral_unpaid_power_iff F law ht⟩
  intro t ht
  let s := ((20999:ℝ)/24000+t)/2
  have hs : (20999:ℝ)/24000<s := by dsimp only [s]; linarith only [ht]
  have hs0 : 0<s := by linarith only [hs]
  have hst : s<t := by dsimp only [s]; linarith only [ht]
  have hfix := (htransfer s hs0).2 (full_strip_power hs) (t-s) (sub_pos.mpr hst)
  rw [show s+(t-s)=t by ring] at hfix
  obtain ⟨A,hA,hfull⟩ := full_strip_power ht
  obtain ⟨B,hB,hb⟩ := hfix
  refine ⟨⟨B,hB,hb⟩,A+B,add_nonneg hA hB,fun X => ?_⟩
  have he := fixed_add_crossing F law X
  have hc : crossingSignedPrefix F X=coprimeMoebiusSum 1 X-fixedSignedPrefix F X := by linarith only [he]
  rw [hc,add_mul]
  exact (abs_sub ..).trans (add_le_add (hfull X) (hb X))

#print axioms neutral_unpaid_decomposition
#print axioms neutral_unpaid_power_iff
#print axioms separate_signed_savings_on_one_short_involution

end GaloisForLFunctions.RestrictedFactorizationCalculus
