import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetPatternEndpoints
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerJacquetIdempotents
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraWeightNonneg

/-! The root exchange preserves the Jacquet weight on every polynomial series. -/

noncomputable section
open Polynomial WindowedLandauTheory.MainNotions.ArithmeticCylinders

namespace GlobalTheory.GLq

variable {g n : ℕ} [Fact g.Prime]

/-- The Jacquet and column-vanishing averages have equal weights on each
Harish–Chandra series. -/
theorem wtC_eJ_eq_eJ' (L : LabelDatum g) (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1)
    (k s : ℕ) (hn : n = k + 2 * s + 1) (f : (ZMod g)[X]) :
    wtC L (eJ g n k s ψ) f = wtC L (eJ' g n k ψ) f := by
  let a := eJ g n k s ψ
  let b := eJ' g n k ψ
  have hc : a.coeff 1 = b.coeff 1 :=
    (eJ_mul_self_coeff_one (n := n) ψ k s (by omega)).2.trans
      (eJ'_mul_self_coeff_one (n := n) ψ k (by omega)).2.symm
  change wtC L a f = wtC L b f
  unfold wtC
  rw [hc]
  apply congrArg (fun c : ℂ => c.re / (b.coeff 1).re)
  unfold eSerC
  refine finsum_mem_induction (fun c => (a * c).coeff 1 = (b * c).coeff 1) (by simp) ?_ ?_
  · intro c d hc hd
    rw [mul_add, mul_add, MonoidAlgebra.coeff_add, MonoidAlgebra.coeff_add,
      Finsupp.add_apply, Finsupp.add_apply, hc, hd]
  · intro χ hχ
    obtain ⟨V, _, hV⟩ := (show IsIrr χ from hχ.1)
    have hcl : IsClass χ := fun x y =>
      (hV (y * x * y⁻¹)).symm.trans ((V.char_conj x y).trans (hV x))
    have he : tr a χ = tr b χ := JacquetPattern.tr_eJ_eq_tr_eJ' ψ hψ k s hn χ hcl
    rw [coeff_one_mul_zOf, coeff_one_mul_zOf, he]

end GlobalTheory.GLq
