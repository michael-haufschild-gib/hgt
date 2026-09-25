import GaloisForLFunctions.RHTower.MobiusDivisorFiniteDepthPrimeCancellation
import GaloisForLFunctions.RHTower.MobiusDivisorLatePrimeBlocks
import GaloisForLFunctions.RHTower.MobiusDivisorLocalizedInteractions

/-!
# Cofinal negative mixed curvature after a two-prime source core

The processed prime-free divisor head changes sign once two old primes are
present. A fresh prime selected in a negative child band has a positive
singleton fibre. A second fresh prime above half the cutoff has a strictly
negative singleton fibre. Its merger changes energy only through the head,
so their mixed second difference is negative at every sufficiently large
cutoff. This is an actual source-side cancellation channel beyond the
pair-inactive upper-third sector; it does not bound its cumulative payment
along an exhaustive history.
-/

noncomputable section
open Finset Filter Topology
namespace RHTower

private theorem late_prime_dilation_strict_neg
    {M q : ℕ} (hq : q.Prime) (hqM : q < M) (hMq : M < 2 * q) :
    mobiusDivisorDilationChannel M q < 0 := by
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq.pos
  have hx : (M : ℝ) / q ∈ Set.Ioo (1 : ℝ) 2 := by
    constructor
    · exact (one_lt_div hq0).mpr (by exact_mod_cast hqM)
    · exact (div_lt_iff₀ hq0).mpr (by exact_mod_cast hMq)
  have hF := divisorContinuousUnitHead_pos_first hx
  have hU := divisorContinuousUnitHead_dilation M q hq.pos
  rw [mobiusDivisorDilationChannel_eq_moebius_unsigned,
      ArithmeticFunction.moebius_apply_prime hq]
  push_cast
  nlinarith [Real.sqrt_pos.mpr hq0]

private theorem mixed_eq_late_head_product
    (M : ℕ) (P : Finset ℕ) {p q : ℕ}
    (hq : q.Prime) (hqM : q < M) (hMq : M < 2 * q)
    (hqP : q ∉ P) (hpq : p ≠ q) :
    mobiusDivisorSelectionEnergy M (insert q (insert p P)) -
      mobiusDivisorSelectionEnergy M (insert p P) -
      mobiusDivisorSelectionEnergy M (insert q P) +
        mobiusDivisorSelectionEnergy M P =
      2 * mobiusDivisorSelectionFibre M P {p} *
        mobiusDivisorDilationChannel M q := by
  have hqPp : q ∉ insert p P := by simp [hqP, hpq.symm]
  have h₁ := mobiusDivisorSelectionEnergy_insert_late_prime
    hq hqM hMq.le (insert p P) hqPp
  have h₀ := mobiusDivisorSelectionEnergy_insert_late_prime
    hq hqM hMq.le P hqP
  have hh : mobiusDivisorSelectionFibre M (insert p P) ∅ =
      mobiusDivisorSelectionFibre M P ∅ +
        mobiusDivisorSelectionFibre M P {p} := by
    rw [mobiusDivisorSelectionFibre_insert]
    simp
  calc
    _ = (mobiusDivisorSelectionEnergy M (insert q (insert p P)) -
          mobiusDivisorSelectionEnergy M (insert p P)) -
        (mobiusDivisorSelectionEnergy M (insert q P) -
          mobiusDivisorSelectionEnergy M P) := by ring
    _ = 2 * mobiusDivisorSelectionFibre M (insert p P) ∅ *
          mobiusDivisorDilationChannel M q -
        2 * mobiusDivisorSelectionFibre M P ∅ *
          mobiusDivisorDilationChannel M q := by rw [h₁, h₀]
    _ = _ := by rw [hh]; ring

private theorem eventually_late_prime (B : ℕ) :
    ∀ᶠ M : ℕ in atTop, ∃ q : ℕ,
      q.Prime ∧ q < M ∧ M < 2 * q ∧ B < q := by
  have hhalf : Tendsto (fun M : ℕ => (M : ℝ) / 2) atTop atTop :=
    tendsto_natCast_atTop_atTop.atTop_div_const (by norm_num)
  have hpr := hhalf.eventually (prime_between (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [hpr, eventually_ge_atTop (2 * (B + 1))] with M hM hB
  obtain ⟨q, hq, hlo, hhi⟩ := hM
  have hMr : (0 : ℝ) < M := by exact_mod_cast (show 0 < M by omega)
  have hqMr : (q : ℝ) < M := by nlinarith only [hhi, hMr]
  have hMqr : (M : ℝ) < 2 * q := by nlinarith only [hlo]
  have hBqr : (B : ℝ) < q := by
    have hBr : (2 * (B + 1) : ℝ) ≤ M := by exact_mod_cast hB
    nlinarith only [hlo, hBr]
  exact ⟨q, hq, by exact_mod_cast hqMr,
    by exact_mod_cast hMqr, by exact_mod_cast hBqr⟩

/-- A two-prime processed core has cofinal fresh pairs with genuinely
negative signed mixed energy curvature. -/
theorem eventually_exists_mobiusDivisorSelectionEnergy_negative_mixed
    (P : Finset ℕ) (hP : 1 < P.card) (hprime : ∀ p ∈ P, p.Prime) :
    ∀ᶠ M : ℕ in atTop, ∃ p q : ℕ,
      p.Prime ∧ q.Prime ∧ p ∉ P ∧ q ∉ P ∧ p ≠ q ∧
      mobiusDivisorSelectionEnergy M (insert q (insert p P)) -
        mobiusDivisorSelectionEnergy M (insert p P) -
        mobiusDivisorSelectionEnergy M (insert q P) +
          mobiusDivisorSelectionEnergy M P < 0 := by
  obtain ⟨c, η, hc, hη, hsource⟩ :=
    eventually_exists_mobiusDivisorFiniteDepth_uniform_prime_collar
      P {1} hP hprime (by simp)
  have hsourceM := hsource (P.sup id)
  have hlateM := eventually_late_prime (P.sup id)
  filter_upwards [hsourceM, hlateM, eventually_ge_atTop 1] with M hsourceNow hlateNow hM
  let a : ({1} : Finset ℕ) → ℝ := fun _ => 1
  have ha : a ≠ 0 := by
    intro he
    have hh := congrFun he (⟨1, by simp⟩ : ({1} : Finset ℕ))
    norm_num [a] at hh
  obtain ⟨p, hp, _, hpP, hcollar⟩ := hsourceNow a ha
  have hstay : (M : ℝ) ≤ (1 + η) * M := by
    have hMr : (0 : ℝ) ≤ M := by positivity
    nlinarith only [hη, hMr]
  have hgain := hcollar M le_rfl hstay
  have hsum : (∑ r : ({1} : Finset ℕ),
      a r * mobiusDivisorInterpolatedFibre M (p * (r : ℕ)) P ∅) =
      mobiusDivisorInterpolatedFibre M p P ∅ := by simp [a]
  rw [hsum] at hgain
  have hanorm : 0 < ‖a‖ := norm_pos_iff.mpr ha
  have hnegative : mobiusDivisorInterpolatedFibre M p P ∅ < 0 := by
    have hcprod := mul_pos hc hanorm
    linarith
  have hpF : 0 < mobiusDivisorSelectionFibre M P {p} := by
    change 0 < mobiusDivisorSelectionFibre M P (insert p ∅)
    rw [mobiusDivisorSelectionFibre_prime_interpolation hp M P ∅ hpP (by simp)]
    have hs : 0 < Real.sqrt (p : ℝ) :=
      Real.sqrt_pos.mpr (by exact_mod_cast hp.pos)
    nlinarith only [mul_neg_of_pos_of_neg hs hnegative]
  obtain ⟨q, hq, hqM, hMq, hqB⟩ := hlateNow
  have hqP : q ∉ P := by
    intro hmem
    exact (not_le_of_gt hqB) (Finset.le_sup (f := id) hmem)
  have hqD := late_prime_dilation_strict_neg hq hqM hMq
  have hpq : p ≠ q := by
    intro he
    subst q
    have hsingle := mobiusDivisorSelectionFibre_late_prime
      hp hqM hMq.le P {p} hpP (by simp)
    simp only [if_true] at hsingle
    rw [hsingle] at hpF
    exact (not_lt_of_ge hpF.le) hqD
  refine ⟨p, q, hp, hq, hpP, hqP, hpq, ?_⟩
  rw [mixed_eq_late_head_product M P hq hqM hMq hqP hpq]
  exact mul_neg_of_pos_of_neg (mul_pos (by norm_num) hpF) hqD

end RHTower
