import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JacquetColumnTrace
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicDerivativeAverages
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MirabolicHarishChandra
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GelfandGraevNorm
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WhittakerDerivativeTrace
import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.CharacterTheory.HarishChandraRestrictionClass

/-! The column-vanishing Jacquet trace decomposes into the Whittaker
multiplicities of the derivatives, weighted by Gelfand–Graev norms. -/

noncomputable section
open GaloisForLFunctions
open scoped Classical

namespace GlobalTheory.GLq

variable {g k b : ℕ} [Fact g.Prime]

private theorem gg_isClass (ψ : AddChar (ZMod g) ℂ) (n : ℕ) : IsClass (gg ψ n) := by
  rw [gg_eq_inducedFunction]
  intro x y
  exact inducedFunction_conj (upperUnitriangular g n) _ y x

private theorem wh_hc_gg (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) {i : ℕ}
    (hi : i ≤ k) (α : Gn g i → ℂ) (hα : IsClass α) :
    wh ψ (hc i (k - i) α (gg ψ (k - i)) k) =
      wh ψ α * wh ψ (gg ψ (k - i)) := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hi
  rw [Nat.add_sub_cancel_left i d]
  exact wh_hc_mul_of_isClass ψ hψ hα (gg_isClass ψ d)

/-- The exact coefficient of each derivative is the squared norm of the
Gelfand–Graev character at the complementary rank. -/
theorem tr_eJ'_eq_sum_wh_der (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1)
    (χ : Gn g (k + 1 + b) → ℂ) (hχ : IsClass χ) :
    tr (eJ' g (k + 1 + b) k ψ) χ =
      ∑ i : Fin (k + 1), wh ψ (der ψ i.val χ) * wh ψ (gg ψ (k - i.val)) := by
  let T := tailAverage (a := k + 1) (b := b) ψ lastRowFirstColumn χ
  have hT : IsMirabolicClass T := tailAverage_isMirabolicClass ψ χ hχ
  have he (A : Gn g k) : T (mirabolicBlock A 0) =
      ∑ i : Fin (k + 1), hc i.val (k - i.val) (der ψ i.val χ) (gg ψ (k - i.val)) k A := by
    change T (mirabolicUnit A 0).val = _
    rw [mirabolic_eq_sum_induced_derivatives ψ hψ k T hT]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [show mirabolicDerivative ψ k i T = der ψ i.val χ from
      mirabolicDerivative_tailAverage ψ k b χ i]
    exact mirabolicInductionAt_diag ψ i _ (der_isClass ψ (by omega) χ hχ) A
  rw [tr_eJ'_eq_wh_tailAverage, show
    (fun A : Gn g k => tailAverage (a := k + 1) (b := b) ψ lastRowFirstColumn χ (mirabolicBlock A 0)) =
      _ from funext he]
  have hadd (F : Fin (k + 1) → Gn g k → ℂ) :
      wh ψ (fun A => ∑ i, F i A) = ∑ i, wh ψ (F i) := by
    unfold wh tr
    simp only [Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hadd]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hi : i.val ≤ k := Nat.le_of_lt_succ i.isLt
  exact wh_hc_gg ψ hψ hi _ (der_isClass ψ (hi.trans (by omega)) χ hχ)

/-- The Gelfand–Graev norm is one in rank zero and the difference of
successive powers of the field size in positive rank. -/
theorem wh_gg_eq_real (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (d : ℕ) :
    wh ψ (gg ψ d) = ((if d = 0 then 1 else (g : ℝ) ^ d - (g : ℝ) ^ (d - 1) : ℝ) : ℂ) := by
  by_cases hd : d = 0
  · subst d
    rw [gg_zero, wh_rank_zero]
    simp
  · rw [GGNorm.wh_gg ψ hψ _ (Nat.pos_of_ne_zero hd), if_neg hd]
    simp only [Complex.ofReal_sub, Complex.ofReal_pow, Complex.ofReal_natCast]

/-- In positive retained rank, the rank-zero derivative alone supplies the
Gelfand–Graev norm times the full Whittaker multiplicity. -/
theorem tr_eJ'_lower (ψ : AddChar (ZMod g) ℂ) (hψ : ψ ≠ 1) (hk : 0 < k)
    (χ : Gn g (k + 1 + b) → ℂ) (hχ : IsChar χ) :
    ((g : ℝ) ^ k - (g : ℝ) ^ (k - 1)) * (wh ψ χ).re ≤
      (tr (eJ' g (k + 1 + b) k ψ) χ).re := by
  have hgg : ∀ d : ℕ, 0 ≤ (if d = 0 then 1 else (g : ℝ) ^ d - (g : ℝ) ^ (d - 1)) := by
    intro d
    split_ifs
    · exact zero_le_one
    · exact sub_nonneg.mpr (pow_le_pow_right₀
        (by exact_mod_cast (Fact.out : g.Prime).one_le) (Nat.sub_le _ _))
  let i₀ : Fin (k + 1) := ⟨0, Nat.succ_pos k⟩
  have hzero :
      (wh ψ (der ψ i₀.val χ) * wh ψ (gg ψ (k - i₀.val))).re =
        ((g : ℝ) ^ k - (g : ℝ) ^ (k - 1)) * (wh ψ χ).re := by
    change (wh ψ (der ψ 0 χ) * wh ψ (gg ψ k)).re = _
    rw [wh_der_zero, wh_gg_eq_real ψ hψ, if_neg hk.ne', mul_comm, Complex.re_ofReal_mul]
  have hcl : IsClass χ := by
    obtain ⟨V, hV⟩ := hχ
    intro x y
    exact (hV _).symm.trans ((V.char_conj x y).trans (hV x))
  rw [tr_eJ'_eq_sum_wh_der ψ hψ χ hcl, ← hzero]
  change _ ≤ Complex.reAddGroupHom (∑ i : Fin (k + 1),
    wh ψ (der ψ i.val χ) * wh ψ (gg ψ (k - i.val)))
  rw [map_sum]
  apply Finset.single_le_sum (f := fun i : Fin (k + 1) =>
    (wh ψ (der ψ i.val χ) * wh ψ (gg ψ (k - i.val))).re) _ (Finset.mem_univ i₀)
  intro i _
  obtain ⟨d, hd⟩ := wh_der_eq_nat ψ (a := i.val) (by omega) χ hχ
  rw [hd, wh_gg_eq_real ψ hψ, mul_comm, Complex.re_ofReal_mul, Complex.natCast_re]
  exact mul_nonneg (hgg (k - i.val)) (Nat.cast_nonneg d)

end GlobalTheory.GLq
