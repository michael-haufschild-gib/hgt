import GaloisForLFunctions.RHTower.ZetaLowHeightZeroFree
import Mathlib.NumberTheory.Harmonic.ZetaAsymp
import Mathlib.Analysis.Complex.RemovableSingularity

/-!
# The entire pole unit `(s-1)·ζ(s)` and the log-derivative split

`ζ(s) - 1/(s-1)` extends analytically across `s = 1` (removable
singularity, limit `γ`), so `Z(s) := (s-1)·ζ(s)` extends to an entire
function with `Z(1) = 1`.  Wherever `ζ(s) ≠ 0`, `s ≠ 1`:

`-ζ′/ζ(s) = 1/(s-1) - Z′/Z(s)`,

isolating the simple pole of the Perron integrand — the regular part
`Z′/Z` is then differentiable on the zero-free rectangle and
Cauchy–Goursat applies to it.
-/

noncomputable section

namespace RHTower

open Filter

/-- `ζ(s) - 1/(s-1)`, patched at `s = 1` with its limit `γ`. -/
def zetaRegularized : ℂ → ℂ :=
  Function.update (fun s : ℂ => riemannZeta s - 1 / (s - 1)) 1
    ((Real.eulerMascheroniConstant : ℝ) : ℂ)

theorem zetaRegularized_of_ne {s : ℂ} (hs : s ≠ 1) :
    zetaRegularized s = riemannZeta s - 1 / (s - 1) :=
  Function.update_of_ne hs _ _

/-- The regularized zeta is entire (removable singularity at `1`). -/
theorem differentiable_zetaRegularized :
    Differentiable ℂ zetaRegularized := by
  have hformula : ∀ {z : ℂ}, z ≠ 1 →
      DifferentiableAt ℂ (fun s : ℂ => riemannZeta s - 1 / (s - 1)) z := by
    intro z hz
    exact (differentiableAt_riemannZeta hz).sub
      ((differentiableAt_const _).div
        ((differentiableAt_id.sub_const 1)) (sub_ne_zero.2 hz))
  intro z
  rcases eq_or_ne z 1 with rfl | hz
  · apply AnalyticAt.differentiableAt
    apply
      Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
    · filter_upwards [self_mem_nhdsWithin] with w hw
      have hw1 : w ≠ 1 := hw
      apply (hformula hw1).congr_of_eventuallyEq
      filter_upwards [isOpen_compl_singleton.mem_nhds hw1] with v hv
      exact zetaRegularized_of_ne hv
    · rw [zetaRegularized, continuousAt_update_same]
      exact tendsto_riemannZeta_sub_one_div
  · apply (hformula hz).congr_of_eventuallyEq
    filter_upwards [isOpen_compl_singleton.mem_nhds hz] with v hv
    exact zetaRegularized_of_ne hv

/-- The entire continuation of `(s-1)·ζ(s)`. -/
def zetaPoleUnit : ℂ → ℂ := fun s => (s - 1) * zetaRegularized s + 1

theorem differentiable_zetaPoleUnit : Differentiable ℂ zetaPoleUnit :=
  ((differentiable_id.sub_const 1).mul
    differentiable_zetaRegularized).add_const 1

theorem zetaPoleUnit_of_ne {s : ℂ} (hs : s ≠ 1) :
    zetaPoleUnit s = (s - 1) * riemannZeta s := by
  have h1 : s - 1 ≠ 0 := sub_ne_zero.2 hs
  unfold zetaPoleUnit
  rw [zetaRegularized_of_ne hs]
  field_simp
  ring

theorem zetaPoleUnit_one : zetaPoleUnit 1 = 1 := by
  unfold zetaPoleUnit
  simp

theorem zetaPoleUnit_ne_zero {s : ℂ} (hs : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) : zetaPoleUnit s ≠ 0 := by
  rw [zetaPoleUnit_of_ne hs]
  exact mul_ne_zero (sub_ne_zero.2 hs) hζ

/-- **The log-derivative pole split**:
`-ζ′/ζ(s) = 1/(s-1) - Z′/Z(s)` off the pole and the zeros. -/
theorem neg_zeta_logDeriv_eq {s : ℂ} (hs : s ≠ 1)
    (hζ : riemannZeta s ≠ 0) :
    - (deriv riemannZeta s / riemannZeta s)
      = 1 / (s - 1) - deriv zetaPoleUnit s / zetaPoleUnit s := by
  have hs1 : s - 1 ≠ 0 := sub_ne_zero.2 hs
  have hZ : zetaPoleUnit s ≠ 0 := zetaPoleUnit_ne_zero hs hζ
  have heq : riemannZeta =ᶠ[nhds s]
      fun w : ℂ => zetaPoleUnit w / (w - 1) := by
    filter_upwards [isOpen_compl_singleton.mem_nhds hs] with v hv
    rw [zetaPoleUnit_of_ne hv, mul_comm, mul_div_assoc,
      div_self (sub_ne_zero.2 hv), mul_one]
  have hqd : HasDerivAt (fun w : ℂ => zetaPoleUnit w / (w - 1))
      ((deriv zetaPoleUnit s * (s - 1) - zetaPoleUnit s * 1)
        / (s - 1) ^ (2 : ℕ)) s :=
    (differentiable_zetaPoleUnit s).hasDerivAt.div
      ((hasDerivAt_id s).sub_const 1) hs1
  have hd : deriv riemannZeta s
      = (deriv zetaPoleUnit s * (s - 1) - zetaPoleUnit s * 1)
        / (s - 1) ^ (2 : ℕ) := by
    rw [heq.deriv_eq]
    exact hqd.deriv
  have hζs : riemannZeta s = zetaPoleUnit s / (s - 1) := by
    rw [zetaPoleUnit_of_ne hs, mul_comm, mul_div_assoc,
      div_self hs1, mul_one]
  rw [hd, hζs]
  field_simp
  ring

end RHTower
