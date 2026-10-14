import GaloisForLFunctions.RHTower.JointAncestryLevelOneDensityL2
import GaloisForLFunctions.RHTower.JointAncestryLocalizedCriterion
import GaloisForLFunctions.RHTower.WeilLagFunctionHerglotz
import Mathlib.MeasureTheory.Function.ConvergenceInMeasure

/-! # The signed JAS density is real without a critical-line assumption

The existing reflected conjugate zero permutation pairs the full complex
sectors. The resulting conjugation identity survives the L² limit.
-/

namespace RHTower

open MeasureTheory Filter GaloisForLFunctions.HTGeometry
open scoped BigOperators Topology ComplexConjugate

noncomputable section

theorem lagWeight_lagPartner (q : XiZeroCopy) :
    lagWeight (lagPartner q) = conj (lagWeight q) := by
  simp only [lagWeight, lagPartner_coe, map_div₀, map_one, map_mul, map_sub,
    sub_sub_cancel, mul_comm]

theorem conj_jasZeroSumDensity (c : ℝ) (P : Finset Nat.Primes) (w : ↥P → ℂ) :
    conj (jasZeroSumDensity c P w) = jasZeroSumDensity c P w := by
  let F : XiZeroCopy → ℂ := fun q => lagWeight q *
    ∏ i : ↥P, jasHoloLocal (jasHoloA ((q.1 : ℂ) + c) i)
      (jasHoloB ((q.1 : ℂ) - c) i) (w i)
  have hpartner (q : XiZeroCopy) : F (lagPartner q) = conj (F q) := by
    dsimp only [F]
    rw [lagWeight_lagPartner, lagPartner_coe, map_mul, map_prod]
    congr 1
    apply Finset.prod_congr rfl
    intro i _
    rw [jasHoloA_reflect, jasHoloB_reflect, jasHoloLocal_conj_conj]
  change conj (∑' q, F q) = ∑' q, F q
  calc
    _ = ∑' q, conj (F q) := tsum_star
    _ = ∑' q, F (lagPartner q) := tsum_congr fun q => (hpartner q).symm
    _ = _ := lagPartner.tsum_eq F

theorem star_jasLevelOneFiniteDensity (P : Finset Nat.Primes) :
    star (jasLevelOneFiniteDensity P) = jasLevelOneFiniteDensity P := by
  apply Lp.ext
  filter_upwards [Lp.coeFn_star (jasLevelOneFiniteDensity P),
    coeFn_jasLevelOneFiniteDensity P] with x hs hx
  rw [hs]
  change conj (jasLevelOneFiniteDensity P x) = jasLevelOneFiniteDensity P x
  rw [hx, conj_jasZeroSumDensity]

theorem star_jasLevelOneDensity : star jasLevelOneDensity = jasLevelOneDensity := by
  obtain ⟨ns, _hns, hlim⟩ :=
    (tendstoInMeasure_of_tendsto_Lp tendsto_jasLevelOneFiniteDensity).exists_seq_tendsto_ae
  have hreal : ∀ᵐ x ∂torusHaar Nat.Primes, ∀ N,
      conj (jasLevelOneFiniteDensity (jasPrimePrefix N) x) =
        jasLevelOneFiniteDensity (jasPrimePrefix N) x := by
    refine ae_all_iff.mpr fun N => ?_
    filter_upwards [coeFn_jasLevelOneFiniteDensity (jasPrimePrefix N)] with x hx
    rw [hx, conj_jasZeroSumDensity]
  apply Lp.ext
  filter_upwards [Lp.coeFn_star jasLevelOneDensity, hlim, hreal] with x hs hx hr
  rw [hs]
  exact tendsto_nhds_unique hx.star
    (hx.congr' (Eventually.of_forall fun N => (hr (ns N)).symm))

theorem ae_im_jasLevelOneDensity_eq_zero :
    ∀ᵐ x ∂torusHaar Nat.Primes, (jasLevelOneDensity x).im = 0 := by
  filter_upwards [Lp.coeFn_star jasLevelOneDensity] with x hx
  rw [star_jasLevelOneDensity] at hx
  exact Complex.conj_eq_iff_im.mp hx.symm

end

end RHTower
