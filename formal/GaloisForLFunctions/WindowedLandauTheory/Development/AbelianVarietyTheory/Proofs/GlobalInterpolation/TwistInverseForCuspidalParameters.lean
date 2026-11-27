import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.CuspidalPointParameters

/-! The two unramified rank-one parameters have inverse Frobenius
eigenvalues. Their local character twists cancel, and multiplicity one
identifies the resulting cuspidal parameter with the original one. -/

noncomputable section

open WindowedLandauTheory.BasicNotions

namespace WindowedLandauTheory.NormalizedTypes

variable (D : D7)

private theorem eta_twist_char_trivial (w : PlE D.host) :
    D.naut.lpChar (D.naut.locG D.naut.etaTinv w) (D.naut.locG D.naut.etaT w) =
      D.naut.lpUnr w {1} := by
  let a := D.naut.locG D.naut.etaTinv w
  let b := D.naut.locG D.naut.etaT w
  have hb : D.naut.unr b := D.naut.etaT_unr w
  have ha : D.naut.unr a := (D.naut.etaTinv_def w).1
  have hd : D.naut.lpDim b = 1 := D.naut.locG_dim _ _
  obtain ⟨c, hc⟩ := Multiset.card_eq_one.mp ((D.naut.frobEig_card b hb).trans hd)
  have h₀ : c ≠ 0 := by
    rintro rfl
    exact D.naut.frobEig_ne_zero b hb (by rw [hc]; exact Multiset.mem_singleton_self 0)
  have hac : D.naut.frobEig a = {c⁻¹} := by
    rw [(D.naut.etaTinv_def w).2, hc, Multiset.map_singleton]
  change D.naut.lpChar a b = D.naut.lpUnr w {1}
  rw [D.naut.unr_eq_lpUnr _ (D.naut.unr_char a b hd ha hb),
    D.naut.frobEig_char a b c ha hb hd hc, hac, Multiset.map_singleton, inv_mul_cancel₀ h₀]

/-- Inverse local character twists cancel on a positive-rank global
parameter when its local components determine it. -/
theorem eta_twist_undo
    (hAssoc : ∀ (w : PlE D.host) (a χ ψ : D.naut.LP w),
      D.naut.lpDim χ = 1 → D.naut.lpDim ψ = 1 →
      D.naut.lpChar (D.naut.lpChar a χ) ψ = D.naut.lpChar a (D.naut.lpChar χ ψ))
    (hUnit : ∀ (w : PlE D.host) (a : D.naut.LP w),
      D.naut.lpChar a (D.naut.lpUnr w {1}) = a)
    {n : ℕ} (π : D.naut.CG n)
    (hUnique : ∀ x y : D.naut.CG n, (∀ w, D.naut.locG x w = D.naut.locG y w) → x = y) :
    D.naut.tw (D.naut.tw π D.naut.etaTinv) D.naut.etaT = π := by
  apply hUnique
  intro w
  rw [D.naut.locG_tw, D.naut.locG_tw,
    hAssoc w _ _ _ (D.naut.locG_dim _ _) (D.naut.locG_dim _ _),
    eta_twist_char_trivial, hUnit]

end WindowedLandauTheory.NormalizedTypes
