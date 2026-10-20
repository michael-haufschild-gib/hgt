import GaloisForLFunctions.SquareRootThreshold.PrimeSideTwoBumpCriterion

/-!
# The three-parameter criterion for Dirichlet `L`-functions

Let `χ` be a primitive character modulo `q > 1`. The nontrivial zeros of `L(s, χ)` form a tempered
configuration (`temperedConfig_LZeros`, from the local zero count `ThmE.localCountChi`). By the
explicit formula `ThmE.EF_lit_chi_L`, its Weil form is the twisted prime-side functional

`P_χ(k) = −Σ_n Λ(n)/√n (χ(n) k(log n) + χ̄(n) k(−log n))
  + (1/2π) ∫ h_k(r) (Re ψ(¼ + κ/2 + ir/2) + log(q/π)) dr`

at `k = f ⋆ f̃` (`LZeros_W_eq_literatureRHSchi`), `κ` the parity of `χ`; there are no pole terms.
The configuration theorems therefore apply verbatim:

* **GRH ⟺ Weil positivity** (`grh_iff_weil_nonneg`) on compactly supported `C²` tests.
* **GRH ⟺ positivity on three parameters** (`grh_iff_primeSide_twoBump_nonneg`): every nontrivial
  zero of `L(s, χ)` lies on the critical line iff `Re P_χ(f ⋆ f̃) ≥ 0` for every
  `f = κ_γ(t + v/2) + τκ_γ(t − v/2)`, `γ ∈ ℝ`, `v ≥ 0`, `|τ| = 1`. The same holds with the polar-free
  bump (`grh_iff_primeSide_polarFree_twoBump_nonneg`).
-/

open MeasureTheory Complex Set Filter Topology
open scoped Real ComplexConjugate

noncomputable section

namespace GaloisForLFunctions.SquareRootThreshold

open Zeta23 _root_.RHTower

variable {q : ℕ} [NeZero q] {χ : DirichletCharacter ℂ q}

theorem temperedConfig_LZeros (hq : 1 < q) (hprim : χ.IsPrimitive) :
    TemperedConfig (ThmE.LZeros (ThmE.LSeam_of hq hprim)) := by
  obtain ⟨A₀, hA₀, hloc⟩ := ThmE.localCountChi hq hprim
  refine WeilEF.zero_sum_inv_sq_gen _ hA₀ fun t => ?_
  rw [ThmE.LZeros_N]
  exact hloc t

/-- **The explicit formula for the Weil form of `L(s, χ)`.** For `f ∈ C_c²`,
`W_χ(f, f) = P_χ(f ⋆ f̃)`. -/
theorem LZeros_W_eq_literatureRHSchi (hq : 1 < q) (hprim : χ.IsPrimitive) {f : ℝ → ℂ}
    (hf : ContDiff ℝ 2 f) (hfc : HasCompactSupport f) :
    (ThmE.LZeros (ThmE.LSeam_of hq hprim)).W f f =
      ThmE.literatureRHSchi (ThmE.parity χ) q (ThmE.coeff χ) (EF.weilTest f f) := by
  rw [ZeroConfig.W, ← (ThmE.EF_lit_chi_L hq hprim _ (EF.weilTest_contDiff hf hf.continuous hfc)
    (EF.weilTest_hasCompactSupport hfc hfc)).2]
  refine tsum_congr fun ρ => ?_
  rw [ZeroConfig.Wsummand, EF.paperFT_weilTest hf.continuous hf.continuous hfc hfc, mul_assoc]

/-- **GRH for `L(s, χ)` is Weil positivity** of the zero-side form on compactly supported `C²`
tests. -/
theorem grh_iff_weil_nonneg (hq : 1 < q) (hprim : χ.IsPrimitive) :
    (∀ ρ ∈ (ThmE.LZeros (ThmE.LSeam_of hq hprim)).carrier, ρ.re = 1 / 2) ↔
      ∀ f : ℝ → ℂ, ContDiff ℝ 2 f → HasCompactSupport f →
        0 ≤ ((ThmE.LZeros (ThmE.LSeam_of hq hprim)).W f f).re :=
  (weil_nonneg_iff_onLine _ (temperedConfig_LZeros hq hprim)).symm

/-- **GRH for `L(s, χ)` on three parameters.** Every nontrivial zero of `L(s, χ)` lies on the
critical line iff the twisted prime-side functional is nonnegative on the autocorrelations of the
unimodular two-bump tests `κ_γ(t + v/2) + τ κ_γ(t − v/2)`. -/
theorem grh_iff_primeSide_twoBump_nonneg (hq : 1 < q) (hprim : χ.IsPrimitive) :
    (∀ ρ ∈ (ThmE.LZeros (ThmE.LSeam_of hq hprim)).carrier, ρ.re = 1 / 2) ↔
      ∀ (γ v : ℝ) (τ : ℂ), 0 ≤ v → ‖τ‖ = 1 →
        0 ≤ (ThmE.literatureRHSchi (ThmE.parity χ) q (ThmE.coeff χ)
          (EF.weilTest (twoBump (modScaledBump 1 γ) v τ) (twoBump (modScaledBump 1 γ) v τ))).re := by
  refine (onLine_iff_twoBump_nonneg _ (temperedConfig_LZeros hq hprim)).symm.trans ?_
  refine forall_congr' fun γ => forall_congr' fun v => forall_congr' fun τ => ?_
  rw [LZeros_W_eq_literatureRHSchi hq hprim (f := twoBump (modScaledBump 1 γ) v τ)
    (contDiff_bumpTest (contDiff_modScaledBump_two 1 γ) v ![1, τ])
    (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
      (modScaledBump_support one_pos γ)) v τ)]

/-- **GRH for `L(s, χ)` in the Hodge class.** The same with the polar-free bump. -/
theorem grh_iff_primeSide_polarFree_twoBump_nonneg (hq : 1 < q) (hprim : χ.IsPrimitive) :
    (∀ ρ ∈ (ThmE.LZeros (ThmE.LSeam_of hq hprim)).carrier, ρ.re = 1 / 2) ↔
      ∀ (γ v : ℝ) (τ : ℂ), 0 ≤ v → ‖τ‖ = 1 →
        0 ≤ (ThmE.literatureRHSchi (ThmE.parity χ) q (ThmE.coeff χ)
          (EF.weilTest (twoBump (scaledBumpPolarFree 1 γ) v τ)
            (twoBump (scaledBumpPolarFree 1 γ) v τ))).re := by
  have hstrip : ∀ ρ ∈ (ThmE.LZeros (ThmE.LSeam_of hq hprim)).carrier,
      (ρ.re = 1 / 2 ∨ ρ = 0 ∨ ρ = 1) ↔ ρ.re = 1 / 2 := by
    intro ρ hρ
    have h : 0 < ρ.re ∧ ρ.re < 1 := hρ.2
    refine ⟨fun h' => ?_, Or.inl⟩
    rcases h' with h' | rfl | rfl
    · exact h'
    · simp at h
    · simp at h
  refine (forall₂_congr fun ρ hρ => hstrip ρ hρ).symm.trans
    ((onLine_or_poles_iff_polarFree_twoBump_nonneg _ (temperedConfig_LZeros hq hprim)).symm.trans ?_)
  refine forall_congr' fun γ => forall_congr' fun v => forall_congr' fun τ => ?_
  rw [LZeros_W_eq_literatureRHSchi hq hprim (f := twoBump (scaledBumpPolarFree 1 γ) v τ)
    (contDiff_bumpTest (contDiff_scaledBumpPolarFree 1 γ) v ![1, τ])
    (hasCompactSupport_twoBump (hasCompactSupport_of_support_subset_abs
      (scaledBumpPolarFree_support one_pos γ)) v τ)]

end GaloisForLFunctions.SquareRootThreshold
