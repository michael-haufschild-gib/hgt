import GaloisForLFunctions.SquareRootThreshold.NyquistResolutionOfTheWeilForm

/-!
# A prime-side criterion on a three-parameter family of tests

By the explicit formula for `ζ` (`Zeta23.WeilEF.EF_lit_zetaZeroConfig`), the Weil form of the
nontrivial zeros is the prime-side functional

`P(k) = h_k(i/2) + h_k(−i/2) − Σ_n Λ(n)/√n (k(log n) + k(−log n)) + (1/2π) ∫ h_k(r) Γ(r) dr`

at the autocorrelation `k = f ⋆ f̃` (`zeta_W_eq_literatureRHS`). With the unimodular two-bump
criterion this gives (`onLine_iff_primeSide_twoBump_nonneg`): every nontrivial zero of `ζ` lies on
the critical line iff `Re P(f ⋆ f̃) ≥ 0` for every

`f(t) = κ_γ(t + v/2) + τ κ_γ(t − v/2)`,  `γ ∈ ℝ`, `v ≥ 0`, `|τ| = 1`,

with `κ_γ` the fixed bump modulated to height `γ`. This is Weil's criterion with the test space cut
down to three real parameters. The polar-free bump gives the same criterion in the Hodge class
(`onLine_iff_primeSide_polarFree_twoBump_nonneg`), where the pole terms `h_k(±i/2)` vanish.
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

/-- **The explicit formula for the Weil form of `ζ`.** For `f ∈ C_c²`,
`W_ζ(f, f) = P(f ⋆ f̃)` with `P` the prime-side functional. -/
theorem zeta_W_eq_literatureRHS {f : ℝ → ℂ} (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    zetaZeroConfig.W f f = EF.literatureRHS (EF.weilTest f f) := by
  rw [ZeroConfig.W, ← (WeilEF.EF_lit_zetaZeroConfig _ (EF.weilTest_contDiff hf hf.continuous hfc)
    (EF.weilTest_hasCompactSupport hfc hfc)).2]
  refine tsum_congr fun ρ => ?_
  rw [ZeroConfig.Wsummand, EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc, mul_assoc]

/-- **Prime-side two-bump criterion.** Every nontrivial zero of `ζ` lies on the critical line iff the
prime-side functional is nonnegative on the autocorrelations of the unimodular two-bump tests
`κ_γ(t + v/2) + τ κ_γ(t − v/2)`. -/
theorem onLine_iff_primeSide_twoBump_nonneg :
    (∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2) ↔
      ∀ (γ v : ℝ) (τ : ℂ), 0 ≤ v → ‖τ‖ = 1 →
        0 ≤ (EF.literatureRHS (EF.weilTest (twoBump (modScaledBump 1 γ) v τ)
          (twoBump (modScaledBump 1 γ) v τ))).re := by
  refine zeta_onLine_iff_twoBump_nonneg.symm.trans ?_
  refine forall_congr' fun γ => forall_congr' fun v => forall_congr' fun τ => ?_
  rw [zeta_W_eq_literatureRHS (f := twoBump (modScaledBump 1 γ) v τ)
    (contDiff_bumpTest (contDiff_modScaledBump_two 1 γ) v ![1, τ])
    (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
      (modScaledBump_support one_pos γ)) v τ)]

/-- **Prime-side criterion in the Hodge class.** The same with the polar-free bump: every
nontrivial zero of `ζ` lies on the critical line iff the prime-side functional, whose pole terms now
vanish, is nonnegative on the polar-free unimodular two-bump tests. -/
theorem onLine_iff_primeSide_polarFree_twoBump_nonneg :
    (∀ ρ ∈ zetaZeroConfig.carrier, ρ.re = 1 / 2) ↔
      ∀ (γ v : ℝ) (τ : ℂ), 0 ≤ v → ‖τ‖ = 1 →
        0 ≤ (EF.literatureRHS (EF.weilTest (twoBump (scaledBumpPolarFree 1 γ) v τ)
          (twoBump (scaledBumpPolarFree 1 γ) v τ))).re := by
  have hstrip : ∀ ρ ∈ zetaZeroConfig.carrier, (ρ.re = 1 / 2 ∨ ρ = 0 ∨ ρ = 1) ↔ ρ.re = 1 / 2 := by
    intro ρ hρ
    have h : 0 < ρ.re ∧ ρ.re < 1 := hρ.2
    refine ⟨fun h' => ?_, Or.inl⟩
    rcases h' with h' | rfl | rfl
    · exact h'
    · simp at h
    · simp at h
  refine (forall₂_congr fun ρ hρ => hstrip ρ hρ).symm.trans
    ((onLine_or_poles_iff_polarFree_twoBump_nonneg _ temperedConfig_zetaZeroConfig).symm.trans ?_)
  refine forall_congr' fun γ => forall_congr' fun v => forall_congr' fun τ => ?_
  rw [zeta_W_eq_literatureRHS (f := twoBump (scaledBumpPolarFree 1 γ) v τ)
    (contDiff_bumpTest (contDiff_scaledBumpPolarFree 1 γ) v ![1, τ])
    (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
      (scaledBumpPolarFree_support one_pos γ)) v τ)]

end GaloisForLFunctions.SquareRootThreshold
