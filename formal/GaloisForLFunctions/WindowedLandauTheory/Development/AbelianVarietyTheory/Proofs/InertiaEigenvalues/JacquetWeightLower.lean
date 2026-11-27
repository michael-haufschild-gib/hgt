import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetDerivativeTrace
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetPatternEndpoints
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerJacquetIdempotents
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraWeightNonneg

/-! The rank-zero term in the Jacquet trace yields a lower bound for
every Harish–Chandra series after normalization at the identity. -/

noncomputable section
open Polynomial WindowedLandauTheory.MainNotions.ArithmeticCylinders

namespace GlobalTheory.GLq

variable {g n : ℕ} [Fact g.Prime]

/-- The Jacquet series weight is at least `1-g⁻¹` times the Whittaker
series weight. -/
theorem wtC_eJ_lower (L : LabelDatum g) (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1)
    (k s : ℕ) (hn : n = k + 2 * s + 1) (hk : 0 < k) (f : (ZMod g)[X]) :
    (1 - (g : ℝ)⁻¹) * wtC L (eU g n ψ) f ≤ wtC L (eJ g n k s ψ) f := by
  let q : ℝ := g
  let N := n * (n - 1) / 2
  have hq : 0 < q := Nat.cast_pos.mpr (Fact.out : g.Prime).pos
  have hq' : (q : ℂ) = (g : ℂ) := Complex.ofReal_natCast _
  have hU : ((eU g n ψ).coeff 1).re = (q ^ N)⁻¹ := by
    rw [(eU_mul_self_coeff_one ψ (n := n)).2]
    simp only [← hq', ← Complex.ofReal_pow, ← Complex.ofReal_inv, Complex.ofReal_re, N]
  have hJ : ((eJ g n k s ψ).coeff 1).re = q ^ k * (q ^ N)⁻¹ := by
    rw [(eJ_mul_self_coeff_one ψ k s (by omega : s + k < n)).2]
    simp only [← hq', ← Complex.ofReal_pow, ← Complex.ofReal_inv, ← Complex.ofReal_mul,
      Complex.ofReal_re, N]
  have hpos : 0 < (q ^ N)⁻¹ := inv_pos.mpr (pow_pos hq _)
  let r := q ^ k - q ^ (k - 1)
  have hb := wtC_le_of_trace_comparison L (eU g n ψ) (eJ g n k s ψ) f r
    (hU.symm ▸ hpos) (hJ.symm ▸ mul_pos (pow_pos hq _) hpos) (by
      intro χ hχ
      obtain ⟨V, _, hV⟩ := hχ
      have hcl : IsClass χ := fun x y => (hV _).symm.trans ((V.char_conj x y).trans (hV x))
      rw [JacquetPattern.tr_eJ_eq_tr_eJ' ψ hψ k s hn χ hcl]
      change r * (wh ψ χ).re ≤ _
      obtain ⟨b, rfl⟩ := Nat.exists_eq_add_of_le (show k + 1 ≤ n by omega)
      exact tr_eJ'_lower ψ hψ hk χ ⟨V, hV⟩)
  have hr : r * (q ^ N)⁻¹ / (q ^ k * (q ^ N)⁻¹) = 1 - q⁻¹ := by
    rw [mul_div_mul_right _ _ hpos.ne']
    obtain ⟨d, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
    dsimp only [r]
    rw [pow_succ, Nat.succ_sub_one]
    field_simp [hq.ne']
  rwa [hU, hJ, hr] at hb

end GlobalTheory.GLq
