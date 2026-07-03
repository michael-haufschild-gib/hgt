/-
# Schwarz / Painlevé reflection engine across a straight line

The classical analytic-continuation principle mathlib does **not** carry: a function continuous on an
open set and holomorphic off a straight line is holomorphic across it (Painlevé's theorem / the engine
behind Schwarz reflection).  The proof is entirely mathlib-native once the right tool is located —
**Morera on a disk** (`Complex.isConservativeOn_and_continuousOn_iff_isDifferentiableOn`).  For a
rectangle straddling the line height `a`, split it at `a` into two closed sub-rectangles whose *open
interiors avoid the line*; each has vanishing boundary integral directly by the closed-rectangle
Cauchy–Goursat theorem (`integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn`, which
needs holomorphy only on the interior), and the two sum to the whole rectangle's boundary integral by
interval additivity.  So `f` is conservative on every disk, and Morera upgrades continuity to
holomorphy — no limiting argument in the line-crossing edge.

Why this file exists: it is the mathlib-absent core of the both-connected q62 smooth-piece rigidity
(`SmoothPieceRigidity`, `HbothconnAssembly`).  A relatively open Julia piece on the modulus-one locus
`{‖wfam k‖ = 1}` of a branch that is analytic across the frontier makes that locus a real-analytic
arc; carrying the arc to a line by its uniformiser and reflecting forces the Böttcher branch to
continue across the frontier — contradicting the natural boundary `hnb_of_mem_mandelbrot_connected`.
`differentiableOn_of_off_horizontal_line` is the reflection step of that chain; the general
straight-line form `differentiableOn_of_off_line` is its affine conjugate (any line, any angle),
the shape the arc-uniformiser reduction lands on.

Axiom-clean (`propext`, `Classical.choice`, `Quot.sound`).
-/
import Mathlib.Analysis.Complex.HasPrimitives
import Mathlib.Analysis.Complex.CauchyIntegral

open Complex MeasureTheory Metric Set Topology intervalIntegral
open scoped Interval

namespace Bottcher

/-- **Reflection across a horizontal line (Painlevé / Schwarz engine).**  If `f` is continuous on an
open set `U` and holomorphic on `U` off the horizontal line `{z | z.im = a}`, then `f` is holomorphic
on all of `U`.  Proof: Morera on disks, the straddling rectangle split at height `a` into two closed
sub-rectangles whose interiors avoid the line. -/
theorem differentiableOn_of_off_horizontal_line
    {f : ℂ → ℂ} {U : Set ℂ} {a : ℝ} (hU : IsOpen U)
    (hcont : ContinuousOn f U)
    (hdiff : DifferentiableOn ℂ f (U ∩ {z : ℂ | z.im ≠ a})) :
    DifferentiableOn ℂ f U := by
  have hnotIoo1 : ∀ t : ℝ, a ∉ Ioo (min t a) (max t a) := by
    intro t
    simp only [Set.mem_Ioo, min_lt_iff, lt_max_iff, lt_self_iff_false, or_false]
    rintro ⟨h1, h2⟩; exact absurd h1 (asymm h2)
  have hnotIoo2 : ∀ t : ℝ, a ∉ Ioo (min a t) (max a t) := by
    intro t
    simp only [Set.mem_Ioo, min_lt_iff, lt_max_iff, lt_self_iff_false, false_or]
    rintro ⟨h1, h2⟩; exact absurd h2 (asymm h1)
  -- Case A: a rectangle whose open imaginary range avoids the line height `a`.
  have claimA : ∀ x₀ x₁ y₀ y₁ : ℝ, ([[x₀, x₁]] ×ℂ [[y₀, y₁]]) ⊆ U →
      a ∉ Ioo (min y₀ y₁) (max y₀ y₁) →
      (((∫ x : ℝ in x₀..x₁, f (↑x + ↑y₀ * I)) - ∫ x : ℝ in x₀..x₁, f (↑x + ↑y₁ * I)) +
        I • ∫ y : ℝ in y₀..y₁, f (↑x₁ + ↑y * I)) -
      I • ∫ y : ℝ in y₀..y₁, f (↑x₀ + ↑y * I) = 0 := by
    intro x₀ x₁ y₀ y₁ hsub ha
    refine integral_boundary_rect_eq_zero_of_continuousOn_of_differentiableOn f
      ⟨x₀, y₀⟩ ⟨x₁, y₁⟩ (hcont.mono hsub) (hdiff.mono ?_)
    intro p hp
    rw [Complex.mem_reProdIm] at hp
    refine ⟨hsub ?_, ?_⟩
    · rw [Complex.mem_reProdIm, Set.uIcc, Set.uIcc]
      exact ⟨Ioo_subset_Icc_self hp.1, Ioo_subset_Icc_self hp.2⟩
    · simp only [mem_setOf_eq]
      intro hpa
      exact ha (hpa ▸ hp.2)
  -- Conservativity of `f` on `U`, then Morera.
  have hcons : IsConservativeOn f U := by
    intro z w hR
    rw [Complex.Rectangle] at hR
    rw [eq_comm, neg_eq_iff_add_eq_zero, add_comm, wedgeIntegral_add_wedgeIntegral_eq]
    by_cases ha : a ∈ Ioo (min z.im w.im) (max z.im w.im)
    · -- straddling rectangle: split at the line height `a`
      have haU : a ∈ [[z.im, w.im]] := by
        rw [Set.uIcc]; exact ⟨le_of_lt ha.1, le_of_lt ha.2⟩
      have hedgeCont : ∀ b : ℝ, b ∈ [[z.re, w.re]] →
          ContinuousOn (fun y : ℝ => f (↑b + ↑y * I)) [[z.im, w.im]] := by
        intro b hb
        apply hcont.comp (by fun_prop : Continuous fun y : ℝ => (↑b + ↑y * I : ℂ)).continuousOn
        intro y hy
        apply hR
        rw [Complex.mem_reProdIm]
        exact ⟨by simpa using hb, by simpa using hy⟩
      have hVw : (∫ y : ℝ in z.im..a, f (↑w.re + ↑y * I)) + (∫ y : ℝ in a..w.im, f (↑w.re + ↑y * I))
          = ∫ y : ℝ in z.im..w.im, f (↑w.re + ↑y * I) := by
        apply integral_add_adjacent_intervals
        · exact ((hedgeCont w.re right_mem_uIcc).mono
            (Set.uIcc_subset_uIcc left_mem_uIcc haU)).intervalIntegrable
        · exact ((hedgeCont w.re right_mem_uIcc).mono
            (Set.uIcc_subset_uIcc haU right_mem_uIcc)).intervalIntegrable
      have hVz : (∫ y : ℝ in z.im..a, f (↑z.re + ↑y * I)) + (∫ y : ℝ in a..w.im, f (↑z.re + ↑y * I))
          = ∫ y : ℝ in z.im..w.im, f (↑z.re + ↑y * I) := by
        apply integral_add_adjacent_intervals
        · exact ((hedgeCont z.re left_mem_uIcc).mono
            (Set.uIcc_subset_uIcc left_mem_uIcc haU)).intervalIntegrable
        · exact ((hedgeCont z.re left_mem_uIcc).mono
            (Set.uIcc_subset_uIcc haU right_mem_uIcc)).intervalIntegrable
      have hsubL : ([[z.re, w.re]] ×ℂ [[z.im, a]]) ⊆ U := by
        intro p hp; rw [Complex.mem_reProdIm] at hp
        apply hR; rw [Complex.mem_reProdIm]
        exact ⟨hp.1, (Set.uIcc_subset_uIcc left_mem_uIcc haU) hp.2⟩
      have hsubU : ([[z.re, w.re]] ×ℂ [[a, w.im]]) ⊆ U := by
        intro p hp; rw [Complex.mem_reProdIm] at hp
        apply hR; rw [Complex.mem_reProdIm]
        exact ⟨hp.1, (Set.uIcc_subset_uIcc haU right_mem_uIcc) hp.2⟩
      have hL := claimA z.re w.re z.im a hsubL (hnotIoo1 z.im)
      have hUp := claimA z.re w.re a w.im hsubU (hnotIoo2 w.im)
      rw [← hVw, ← hVz]
      simp only [smul_eq_mul] at hL hUp ⊢
      linear_combination hL + hUp
    · exact claimA z.re w.re z.im w.im hR ha
  exact (isConservativeOn_and_continuousOn_iff_isDifferentiableOn hU).mp ⟨hcons, hcont⟩

/-- **Reflection across a general straight line** `{z | (c * z + d).im = a}`, `c ≠ 0`.  Affine
conjugate of `differentiableOn_of_off_horizontal_line`: the biholomorphism `A z = c z + d` carries
the line to the horizontal line at height `a`, so `f ∘ A⁻¹` reflects there and pulls back to `f`. -/
theorem differentiableOn_of_off_line
    {f : ℂ → ℂ} {U : Set ℂ} {c d : ℂ} {a : ℝ} (hc : c ≠ 0) (hU : IsOpen U)
    (hcont : ContinuousOn f U)
    (hdiff : DifferentiableOn ℂ f (U ∩ {z : ℂ | (c * z + d).im ≠ a})) :
    DifferentiableOn ℂ f U := by
  set A : ℂ → ℂ := fun z => c * z + d with hA
  set B : ℂ → ℂ := fun w => c⁻¹ * (w - d) with hB
  have hBA : ∀ z, B (A z) = z := by
    intro z; simp only [hA, hB, add_sub_cancel_right]
    rw [← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  have hAB : ∀ w, A (B w) = w := by
    intro w; simp only [hA, hB, ← mul_assoc, mul_inv_cancel₀ hc, one_mul, sub_add_cancel]
  have hAdiff : Differentiable ℂ A := by fun_prop
  have hBdiff : Differentiable ℂ B := by fun_prop
  have hAopen : IsOpenMap A :=
    (Homeomorph.mk ⟨A, B, hBA, hAB⟩ hAdiff.continuous hBdiff.continuous).isOpenMap
  have hAU : IsOpen (A '' U) := hAopen _ hU
  set g : ℂ → ℂ := fun w => f (B w) with hg
  have hgcont : ContinuousOn g (A '' U) := by
    show ContinuousOn (f ∘ B) (A '' U)
    refine hcont.comp hBdiff.continuous.continuousOn ?_
    rintro w ⟨z, hz, rfl⟩; rw [hBA]; exact hz
  have hgdiff : DifferentiableOn ℂ g ((A '' U) ∩ {w : ℂ | w.im ≠ a}) := by
    show DifferentiableOn ℂ (f ∘ B) _
    refine hdiff.comp hBdiff.differentiableOn ?_
    rintro w ⟨⟨z, hz, rfl⟩, hw⟩
    simp only [mem_setOf_eq] at hw
    refine ⟨?_, ?_⟩
    · rw [hBA]; exact hz
    · show (c * B (A z) + d).im ≠ a
      rw [show c * B (A z) + d = A z from hAB (A z)]; exact hw
  have hgU : DifferentiableOn ℂ g (A '' U) := differentiableOn_of_off_horizontal_line hAU hgcont hgdiff
  have hcomp : DifferentiableOn ℂ (g ∘ A) U :=
    hgU.comp hAdiff.differentiableOn (fun z hz => ⟨z, hz, rfl⟩)
  refine hcomp.congr (fun z _ => ?_)
  simp only [hg, Function.comp_apply, hBA]

/-- **Reflection across the preimage of a straight line under a partial biholomorphism.**  If `ψ` is a
biholomorphism of the open set `V` onto the open set `ψ '' V` with holomorphic inverse `ψinv`, and `f`
is continuous on `V` and holomorphic off the arc `{z ∈ V | (c * ψ z + d).im = a}`, then `f` is
holomorphic on all of `V`.  This is the reflection engine in the form the smooth-piece discharge
consumes: `ψ` is the local uniformiser of the modulus-one Julia arc (a local inverse of the branch
`wfam k`), carrying the arc to a straight line where `differentiableOn_of_off_line` reflects. -/
theorem differentiableOn_of_off_biholom_preimage_line
    {f ψ ψinv : ℂ → ℂ} {V : Set ℂ} {c d : ℂ} {a : ℝ} (hc : c ≠ 0)
    (hVimg : IsOpen (ψ '' V))
    (hψ : DifferentiableOn ℂ ψ V) (hψinv : DifferentiableOn ℂ ψinv (ψ '' V))
    (hleft : ∀ z ∈ V, ψinv (ψ z) = z)
    (hcont : ContinuousOn f V)
    (hdiff : DifferentiableOn ℂ f (V ∩ {z : ℂ | (c * ψ z + d).im ≠ a})) :
    DifferentiableOn ℂ f V := by
  have hright : ∀ w ∈ ψ '' V, ψ (ψinv w) = w := by
    rintro w ⟨z, hz, rfl⟩; rw [hleft z hz]
  set g : ℂ → ℂ := fun w => f (ψinv w) with hg
  have hgcont : ContinuousOn g (ψ '' V) := by
    show ContinuousOn (f ∘ ψinv) (ψ '' V)
    refine hcont.comp hψinv.continuousOn ?_
    rintro w ⟨z, hz, rfl⟩; rw [hleft z hz]; exact hz
  have hgdiff : DifferentiableOn ℂ g ((ψ '' V) ∩ {w : ℂ | (c * w + d).im ≠ a}) := by
    show DifferentiableOn ℂ (f ∘ ψinv) _
    refine hdiff.comp (hψinv.mono inter_subset_left) ?_
    rintro w ⟨hwimg, hw⟩
    simp only [mem_setOf_eq] at hw
    obtain ⟨z, hz, rfl⟩ := hwimg
    refine ⟨?_, ?_⟩
    · rw [hleft z hz]; exact hz
    · show (c * ψ (ψinv (ψ z)) + d).im ≠ a
      rw [hleft z hz]; exact hw
  have hgV : DifferentiableOn ℂ g (ψ '' V) :=
    differentiableOn_of_off_line hc hVimg hgcont hgdiff
  have hcomp : DifferentiableOn ℂ (g ∘ ψ) V :=
    hgV.comp hψ (fun z hz => ⟨z, hz, rfl⟩)
  refine hcomp.congr (fun z hz => ?_)
  simp only [hg, Function.comp_apply, hleft z hz]

end Bottcher
