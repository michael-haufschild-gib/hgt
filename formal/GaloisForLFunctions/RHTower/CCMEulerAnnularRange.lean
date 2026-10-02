import GaloisForLFunctions.RHTower.CCMEulerAnnularLocalRange
import GaloisForLFunctions.RHTower.CCMEulerEventualCarrier
import GaloisForLFunctions.RHTower.SoninAnnularExtension

/-!
# Exact annular range of the actual finite Euler boundary

Prime insertion composes the original physical Euler factors, retaining every
mixed term. Their exact local boundary sections and the Sonin annular extension
realize the complete finite boundary range.
-/

noncomputable section

open IsDedekindDomain
open scoped BigOperators Classical

namespace RHTower

private def boundaryPrime (v : HeightOneSpectrum ℤ) : ℕ :=
  Rat.HeightOneSpectrum.primesEquiv v

private theorem boundaryPrime_one_lt (v : HeightOneSpectrum ℤ) : 1 < boundaryPrime v :=
  (Rat.HeightOneSpectrum.primesEquiv v).property.one_lt

theorem ccmFiniteEulerCarrierScale_pos (S : Finset (HeightOneSpectrum ℤ)) :
    0 < ccmFiniteEulerCarrierScale S := by
  unfold ccmFiniteEulerCarrierScale
  apply Finset.prod_pos
  intro v _
  have h : (0 : ℕ) < (Rat.HeightOneSpectrum.primesEquiv v : ℕ) :=
    zero_lt_one.trans (Rat.HeightOneSpectrum.primesEquiv v).property.one_lt
  exact_mod_cast h

/-- Every datum in the predicted annulus is attained by the actual finite Euler polynomial
on the actual Sonin carrier. -/
theorem exists_sonin_ccmFiniteEulerDenominator_preimage
    (S : Finset (HeightOneSpectrum ℤ)) (b c : ℝ) (hb : 0 < b) (hc : 0 < c)
    {u : evenSubspace}
    (hulo : evenFourierCutoff (b / ccmFiniteEulerCarrierScale S) u = 0)
    (huhi : evenFourierCutoff c u = u) :
    ∃ f ∈ evenCentralSoninCarrier b,
      evenFourierCutoff c (ccmFiniteEulerDenominator S f) = u := by
  induction S using Finset.induction_on generalizing c u with
  | empty =>
    have hulo' : evenFourierCutoff b u = 0 := by
      simpa only [ccmFiniteEulerCarrierScale, Finset.prod_empty, div_one] using hulo
    by_cases hbc : b ≤ c
    · obtain ⟨f, hf, hfu⟩ := exists_sonin_lift_of_fourier_annulus hb hbc hulo' huhi
      exact ⟨f, hf, by simpa [ccmFiniteEulerDenominator] using hfu⟩
    · have hu0 : u = 0 := by
        have hnest := DFunLike.congr_fun
          (evenFourierCutoff_mul_of_le c b (le_of_not_ge hbc)) u
        change evenFourierCutoff c (evenFourierCutoff b u) = evenFourierCutoff c u at hnest
        rw [hulo', map_zero, huhi] at hnest
        exact hnest.symm
      subst u
      exact ⟨0, (evenCentralSoninCarrier b).zero_mem, by simp⟩
  | @insert v S hv ih =>
    let p : ℝ := boundaryPrime v
    have hp : 1 < p := by
      change (1 : ℝ) < (boundaryPrime v : ℝ)
      exact_mod_cast boundaryPrime_one_lt v
    have hP := ccmFiniteEulerCarrierScale_pos S
    have hprod : ccmFiniteEulerCarrierScale (insert v S) =
        p * ccmFiniteEulerCarrierScale S := by
      unfold ccmFiniteEulerCarrierScale
      rw [Finset.prod_insert hv]
      rfl
    have hscale : p⁻¹ * (b / ccmFiniteEulerCarrierScale S) =
        b / ccmFiniteEulerCarrierScale (insert v S) := by
      rw [hprod]
      field_simp [(zero_lt_one.trans hp).ne', hP.ne']
    have hgap : evenFourierCutoff (p⁻¹ * (b / ccmFiniteEulerCarrierScale S)) u = 0 := by
      rwa [hscale]
    obtain ⟨w, hwlo, hwhi, hwu⟩ := exists_annular_evenPrimeLocalFactor_preimage
      p hp (b / ccmFiniteEulerCarrierScale S) c (div_pos hb hP) hc hgap huhi
    obtain ⟨f, hf, hfw⟩ := ih (p * c) (mul_pos (zero_lt_one.trans hp) hc) hwlo hwhi
    refine ⟨f, hf, ?_⟩
    rw [ccmFiniteEulerDenominator_insert S v hv, _root_.mul_apply_eq_comp]
    change evenFourierCutoff c (evenPrimeLocalFactor p hp (ccmFiniteEulerDenominator S f)) = u
    calc
      evenFourierCutoff c (evenPrimeLocalFactor p hp (ccmFiniteEulerDenominator S f)) =
          evenFourierCutoff c (evenPrimeLocalFactor p hp
            (evenFourierCutoff (p * c) (ccmFiniteEulerDenominator S f))) :=
        (evenPrimeLocalFactor_cutoff_absorb p hp c hc.le _).symm
      _ = u := by rw [hfw]; exact hwu

/-- Exact source range: the Fourier annulus with lower edge divided by the complete prime
product. This also covers the zero range when the two edges cross. -/
theorem ccmFiniteEulerDenominator_range_iff_annulus
    (S : Finset (HeightOneSpectrum ℤ)) (b c : ℝ) (hb : 0 < b) (hc : 0 < c)
    (u : evenSubspace) :
    (∃ f ∈ evenCentralSoninCarrier b,
      evenFourierCutoff c (ccmFiniteEulerDenominator S f) = u) ↔
        evenFourierCutoff (b / ccmFiniteEulerCarrierScale S) u = 0 ∧
          evenFourierCutoff c u = u := by
  constructor
  · rintro ⟨f, hf, rfl⟩
    have hP := ccmFiniteEulerCarrierScale_pos S
    have hfgap := ((mem_evenCentralSoninCarrier_iff_cutoffs_zero b f).mp hf).2
    have hscale : ccmFiniteEulerCarrierScale S * (b / ccmFiniteEulerCarrierScale S) = b := by
      field_simp
    have hgap : evenFourierCutoff (b / ccmFiniteEulerCarrierScale S)
        (ccmFiniteEulerDenominator S f) = 0 :=
      (ccmFiniteEulerDenominator_fourierGap_iff S (div_pos hb hP) hb hfgap).mpr
        (by simpa only [hscale] using hfgap)
    have hcomm : evenFourierCutoff (b / ccmFiniteEulerCarrierScale S) * evenFourierCutoff c =
        evenFourierCutoff c * evenFourierCutoff (b / ccmFiniteEulerCarrierScale S) := by
      rcases le_total (b / ccmFiniteEulerCarrierScale S) c with h | h
      · rw [evenFourierCutoff_mul_of_le _ _ h, evenFourierCutoff_mul_of_le_rev _ _ h]
      · rw [evenFourierCutoff_mul_of_le_rev _ _ h, evenFourierCutoff_mul_of_le _ _ h]
    refine ⟨?_, DFunLike.congr_fun (evenFourierCutoff_mul_of_le c c le_rfl) _⟩
    calc
      evenFourierCutoff (b / ccmFiniteEulerCarrierScale S)
          (evenFourierCutoff c (ccmFiniteEulerDenominator S f)) =
          evenFourierCutoff c (evenFourierCutoff (b / ccmFiniteEulerCarrierScale S)
            (ccmFiniteEulerDenominator S f)) := DFunLike.congr_fun hcomm _
      _ = 0 := by rw [hgap, map_zero]
  · rintro ⟨hulo, huhi⟩
    exact exists_sonin_ccmFiniteEulerDenominator_preimage S b c hb hc hulo huhi

end RHTower
