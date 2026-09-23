import GaloisForLFunctions.RHTower.PhotonicFixedKGeometricFloquetNoGo
import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.Module.Pi

/-!
# Multimode geometric Floquet rigidity

A geometric Floquet ladder with one spatial-mode profile is incompatible with
a nonzero drive and an injective grade-independent spatial operator. Arbitrary
mode mixing in the three material operators does not remove the obstruction.
This concerns a formal modal recurrence, not a derivation of the full rotating-
cylinder Maxwell boundary operator.
-/

namespace RHTower

set_option autoImplicit false

/-- Three grades force both sides of a fixed vector-valued quadratic Floquet
equation to vanish. -/
theorem ptr_multimode_three_grade_common_null {σ : Type*}
    (ω Δ : ℂ) (hΔ : Δ ≠ 0) (u w : σ → ℂ)
    (h : ∀ n : ℤ, (ω + (n : ℂ) * Δ) ^ 2 • u = w) :
    u = 0 ∧ w = 0 := by
  have hs (s : σ) : u s = 0 ∧ w s = 0 := by
    apply ptr_three_fixedK_geometric_frequencies_common_null
      ω Δ (u s) (w s) hΔ
    · simpa using congrArg (fun f : σ → ℂ => f s) (h 0)
    · simpa using congrArg (fun f : σ → ℂ => f s) (h 1)
    · simpa using congrArg (fun f : σ → ℂ => f s) (h 2)
  exact ⟨funext (fun s => (hs s).1), funext (fun s => (hs s).2)⟩

/-- Three-operator material convolution on a mode-indexed Floquet ladder. -/
def ptrMultiMaterialCoefficient {σ : Type*}
    (M0 Mplus Mminus : Module.End ℂ (σ → ℂ))
    (c : ℤ → σ → ℂ) (n : ℤ) : σ → ℂ :=
  M0 (c n) + Mplus (c (n - 1)) + Mminus (c (n + 1))

/-- A geometric ladder factors the material convolution into its pencil. -/
theorem ptrMultiMaterialCoefficient_geometric {σ : Type*}
    (M0 Mplus Mminus : Module.End ℂ (σ → ℂ))
    (lam : ℂ) (hlam : lam ≠ 0) (v : σ → ℂ) (n : ℤ) :
    ptrMultiMaterialCoefficient M0 Mplus Mminus
      (fun j => lam ^ j • v) n =
      lam ^ n • (M0 v + lam⁻¹ • Mplus v + lam • Mminus v) := by
  rw [ptrMultiMaterialCoefficient]
  rw [zpow_sub₀ hlam, zpow_add₀ hlam]
  simp only [zpow_one, div_eq_mul_inv, map_smul]
  funext s
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- Exact necessary common-nullspace condition for an all-grade separable
geometric solution of the matrix-valued modal recurrence. -/
theorem ptr_multimode_geometric_common_null {σ : Type*}
    (M0 Mplus Mminus H : Module.End ℂ (σ → ℂ))
    (ω Δ lam : ℂ) (hΔ : Δ ≠ 0) (hlam : lam ≠ 0) (v : σ → ℂ)
    (h : ∀ n : ℤ,
      (ω + (n : ℂ) * Δ) ^ 2 •
        ptrMultiMaterialCoefficient M0 Mplus Mminus
          (fun j => lam ^ j • v) n = H (lam ^ n • v)) :
    (M0 v + lam⁻¹ • Mplus v + lam • Mminus v = 0) ∧ H v = 0 := by
  let u := M0 v + lam⁻¹ • Mplus v + lam • Mminus v
  let w := H v
  have hgrade (n : ℤ) : (ω + (n : ℂ) * Δ) ^ 2 • u = w := by
    have hn := h n
    rw [ptrMultiMaterialCoefficient_geometric M0 Mplus Mminus lam hlam v n] at hn
    rw [map_smul] at hn
    funext s
    have hns := congrArg (fun f : σ → ℂ => f s) hn
    simp only [Pi.smul_apply, smul_eq_mul] at hns ⊢
    have hlampow : lam ^ n ≠ 0 := zpow_ne_zero n hlam
    have hh : ((ω + (n : ℂ) * Δ) ^ 2 * u s) * lam ^ n =
        w s * lam ^ n := by
      calc
        ((ω + (n : ℂ) * Δ) ^ 2 * u s) * lam ^ n =
            (ω + (n : ℂ) * Δ) ^ 2 * ((lam ^ n) * u s) := by ring
        _ = (lam ^ n) * w s := hns
        _ = w s * lam ^ n := by ring
    exact mul_right_cancel₀ hlampow hh
  exact ptr_multimode_three_grade_common_null ω Δ hΔ u w hgrade

/-- Sharp classification: separable geometric modal solutions are exactly the
common nullspace of the material pencil and the spatial operator. -/
theorem ptr_multimode_geometric_solution_iff_common_null {σ : Type*}
    (M0 Mplus Mminus H : Module.End ℂ (σ → ℂ))
    (ω Δ lam : ℂ) (hΔ : Δ ≠ 0) (hlam : lam ≠ 0) (v : σ → ℂ) :
    (∀ n : ℤ,
      (ω + (n : ℂ) * Δ) ^ 2 •
        ptrMultiMaterialCoefficient M0 Mplus Mminus
          (fun j => lam ^ j • v) n = H (lam ^ n • v)) ↔
      (M0 v + lam⁻¹ • Mplus v + lam • Mminus v = 0) ∧ H v = 0 := by
  constructor
  · exact ptr_multimode_geometric_common_null M0 Mplus Mminus H ω Δ lam hΔ hlam v
  · rintro ⟨hP, hH⟩ n
    rw [ptrMultiMaterialCoefficient_geometric M0 Mplus Mminus lam hlam v n,
      hP, map_smul, hH]
    simp

/-- Closed no-premise obstruction: injective spatial dynamics excludes any
nonzero separable geometric Floquet state, for arbitrary mode-mixing material
operators. -/
theorem ptr_no_injective_multimode_geometric_solution :
    ¬ ∃ (σ : Type) (M0 Mplus Mminus H : Module.End ℂ (σ → ℂ))
        (ω Δ lam : ℂ) (v : σ → ℂ),
      Δ ≠ 0 ∧ lam ≠ 0 ∧ Function.Injective H ∧ v ≠ 0 ∧
      ∀ n : ℤ,
        (ω + (n : ℂ) * Δ) ^ 2 •
          ptrMultiMaterialCoefficient M0 Mplus Mminus
            (fun j => lam ^ j • v) n = H (lam ^ n • v) := by
  rintro ⟨σ, M0, Mplus, Mminus, H, ω, Δ, lam, v,
    hΔ, hlam, hH, hv, hrec⟩
  have hnull := ptr_multimode_geometric_common_null
    M0 Mplus Mminus H ω Δ lam hΔ hlam v hrec
  exact hv (hH (by simpa using hnull.2))

end RHTower
