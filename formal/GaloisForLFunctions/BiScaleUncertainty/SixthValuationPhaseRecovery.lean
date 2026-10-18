import GaloisForLFunctions.BiScaleUncertainty.SieveMomentFourier
import GaloisForLFunctions.BiScaleUncertainty.ValuationTripleResonance
import GaloisForLFunctions.BiScaleUncertainty.CubicSievePhaseRecovery

/-!
# Unconditional sixth-moment recovery within valuation blocks

Explicit Fourier readouts of literal translated sieve moments recover signed
pair products. Real rank-one rigidity then gives one common sign on every fixed
power-of-two order class, with no support or nonvanishing assumptions.
-/

open scoped BigOperators
open Finset ZMod
noncomputable section
namespace GaloisForLFunctions.BiScaleUncertainty.SieveMoments
open GaloisForLFunctions.BiScaleUncertainty.AffineSieve
set_option autoImplicit false
local instance (N : ℕ) : NeZero N.factorial := ⟨Nat.factorial_ne_zero N⟩

/-- One explicit Fourier readout of literal sixth translated sieve observations. -/
def sixthPairReadout (N : ℕ) (c : ℕ → ℝ) (k p q : ℕ) : ℝ :=
  (momentDFT (fun h : Fin 6 → ZMod N.factorial =>
    (translatedMoment N c (fun i => (h i).val) : ℂ)) (valuationSix N k p q)).re

/-- No support assumption is needed: a sixth readout isolates any same-valuation pair. -/
theorem sixthPairReadout_eq {N k p q : ℕ} (c : ℕ → ℝ) (hp : Odd p) (hq : Odd q)
    (hd : 2^k*p ∈ Finset.Icc 1 N) (he : 2^k*q ∈ Finset.Icc 1 N) :
    sixthPairReadout N c k p q = (N.factorial : ℝ)^6 *
      (selbergMultiplesCoord N c (2^k*p) * selbergMultiplesCoord N c (2^k*q))^3 := by
  unfold sixthPairReadout
  simp_rw [translatedMoment_complex_eq,ZMod.natCast_zmod_val]
  rw [momentDFT_sieve,if_pos (valuationSix_sum hp hq hd he),
    valuationSix_order_product hp hq hd he]
  rw [coordinate_ofReal,coordinate_ofReal]
  norm_cast

/-- Equality of this actual observation is precisely equality of the signed pair product. -/
theorem sixthPairReadout_eq_iff {N k p q : ℕ} (c e : ℕ → ℝ) (hp : Odd p) (hq : Odd q)
    (hd : 2^k*p ∈ Finset.Icc 1 N) (he : 2^k*q ∈ Finset.Icc 1 N) :
    sixthPairReadout N c k p q = sixthPairReadout N e k p q ↔
      selbergMultiplesCoord N c (2^k*p) * selbergMultiplesCoord N c (2^k*q) =
        selbergMultiplesCoord N e (2^k*p) * selbergMultiplesCoord N e (2^k*q) := by
  rw [sixthPairReadout_eq c hp hq hd he,sixthPairReadout_eq e hp hq hd he]
  have hP : (N.factorial : ℝ)^6 ≠ 0 := by positivity
  constructor
  · intro hh
    exact (show Odd (3 : ℕ) from ⟨1,rfl⟩).pow_injective (mul_left_cancel₀ hP hh)
  · intro hh
    rw [hh]

/-- Rank-one real products determine a single sign, including zero and empty supports. -/
theorem pair_products_eq_iff_common_sign {ι : Type*} (s : Set ι) (a b : ι → ℝ) :
    (∀ i ∈ s, ∀ j ∈ s, a i*a j = b i*b j) ↔
      (∀ i ∈ s, a i = b i) ∨ (∀ i ∈ s, a i = -b i) := by
  constructor
  · intro h
    by_cases hex : ∃ i ∈ s, a i ≠ 0
    · obtain ⟨i,hi,hai⟩ := hex
      have hii : (a i)^2 = (b i)^2 := by simpa only [pow_two] using h i hi i hi
      rcases sq_eq_sq_iff_eq_or_eq_neg.mp hii with hab | hab
      · have hbi : b i ≠ 0 := by rwa [← hab]
        left
        intro j hj
        apply mul_left_cancel₀ hbi
        simpa only [hab] using h i hi j hj
      · have hbi : b i ≠ 0 := by intro hb; apply hai; simp [hab,hb]
        right
        intro j hj
        have hh := h i hi j hj
        rw [hab] at hh
        have hz : b i*(a j+b j) = 0 := by linear_combination -hh
        have := (mul_eq_zero.mp hz).resolve_left hbi
        linarith
    · left
      intro i hi
      have hai : a i = 0 := by by_contra hn; exact hex ⟨i,hi,hn⟩
      have hh := h i hi i hi
      rw [hai,zero_mul] at hh
      have hbi : b i = 0 := (mul_self_eq_zero.mp hh.symm)
      rw [hai,hbi]
  · rintro (h | h) i hi j hj <;> rw [h i hi,h j hj]
    ring

/-- The explicit finite readouts recover exactly one sign on each fixed valuation block. -/
theorem sixth_readouts_eq_iff_valuation_sign (N k : ℕ) (c e : ℕ → ℝ) :
    (∀ p, Odd p → 2^k*p ∈ Finset.Icc 1 N →
      ∀ q, Odd q → 2^k*q ∈ Finset.Icc 1 N →
        sixthPairReadout N c k p q = sixthPairReadout N e k p q) ↔
      (∀ p, Odd p → 2^k*p ∈ Finset.Icc 1 N →
        selbergMultiplesCoord N c (2^k*p) = selbergMultiplesCoord N e (2^k*p)) ∨
      (∀ p, Odd p → 2^k*p ∈ Finset.Icc 1 N →
        selbergMultiplesCoord N c (2^k*p) = -selbergMultiplesCoord N e (2^k*p)) := by
  have h := pair_products_eq_iff_common_sign
    {p : ℕ | Odd p ∧ 2^k*p ∈ Finset.Icc 1 N}
    (fun p => selbergMultiplesCoord N c (2^k*p))
    (fun p => selbergMultiplesCoord N e (2^k*p))
  simp only [Set.mem_setOf_eq,and_imp] at h
  rw [← h]
  constructor <;> intro heq p hp hd q hq he
  · exact (sixthPairReadout_eq_iff c e hp hq hd he).mp (heq p hp hd q hq he)
  · exact (sixthPairReadout_eq_iff c e hp hq hd he).mpr (heq p hp hd q hq he)

/-- Literal sixth translated data alone recover all relative signs within every valuation block. -/
theorem sixth_moments_recover_valuation_block (N k : ℕ) (c e : ℕ → ℝ)
    (h : ∀ h : Fin 6 → ℕ, translatedMoment N c h = translatedMoment N e h) :
    (∀ p, Odd p → 2^k*p ∈ Finset.Icc 1 N →
      selbergMultiplesCoord N c (2^k*p) = selbergMultiplesCoord N e (2^k*p)) ∨
    (∀ p, Odd p → 2^k*p ∈ Finset.Icc 1 N →
      selbergMultiplesCoord N c (2^k*p) = -selbergMultiplesCoord N e (2^k*p)) := by
  apply (sixth_readouts_eq_iff_valuation_sign N k c e).mp
  intro p _ _ q _ _
  unfold sixthPairReadout
  simp_rw [h]

end GaloisForLFunctions.BiScaleUncertainty.SieveMoments
