import GaloisForLFunctions.RHTower.MobiusLaplaceMellinPlancherelBridge

/-!
# Plancherel for the causal Laplace transform on the imaginary axis

The corpus already carries the exact Mellin--Plancherel line law.  In logarithmic coordinates the
Mellin trace on `Re s = 0` *is* the Laplace transform on the imaginary axis, so the same law reads

```text
∫_R ‖(L g)(i y)‖² dy = 2 π ∫_R ‖g(u)‖² du
```

for every `g ∈ L¹ ∩ L²(R)`.  Applied to a causal `g` (supported on `[0,∞)`) this is the
Paley--Wiener energy identity used by the centered-boundary and causal-graph laws.
-/

open Complex MeasureTheory Set Filter
open scoped Topology

noncomputable section
namespace RHTower

/-- The Laplace transform of `g` evaluated on the imaginary axis. -/
def laplaceBoundary (g : ℝ → ℂ) (y : ℝ) : ℂ :=
  ∫ u : ℝ, Complex.exp (-((y : ℂ) * Complex.I) * (u : ℂ)) * g u

theorem logMellinLineSource_log_comp (g : ℝ → ℂ) :
    logMellinLineSource (fun x : ℝ => g (-Real.log x)) 0 = g := by
  funext u
  rw [logMellinLineSource, Real.log_exp]
  simp

theorem mellin_log_comp_eq_laplaceBoundary (g : ℝ → ℂ) (y : ℝ) :
    mellin (fun x : ℝ => g (-Real.log x)) (((0 : ℝ) : ℂ) + (y : ℂ) * Complex.I)
      = laplaceBoundary g y := by
  rw [mellin_eq_integral_exp_neg_mul_log, laplaceBoundary]
  refine integral_congr_ae ?_
  filter_upwards [] with u
  rw [Real.log_exp]
  congr 2
  · push_cast
    ring
  · norm_num

/-- **Plancherel for the boundary Laplace transform.** -/
theorem integral_norm_sq_laplaceBoundary
    {g : ℝ → ℂ} (h1 : Integrable g) (h2 : MemLp g 2 volume) :
    (∫ y : ℝ, ‖laplaceBoundary g y‖ ^ (2 : ℕ)) = 2 * Real.pi * ∫ u : ℝ, ‖g u‖ ^ (2 : ℕ) := by
  have hsrc := logMellinLineSource_log_comp g
  have h1' : Integrable (logMellinLineSource (fun x : ℝ => g (-Real.log x)) 0) := by
    rw [hsrc]; exact h1
  have h2' : MemLp (logMellinLineSource (fun x : ℝ => g (-Real.log x)) 0) 2 volume := by
    rw [hsrc]; exact h2
  have hmain := integral_norm_sq_mellin_line_eq_logMellinLineSource h1' h2'
  rw [hsrc] at hmain
  rw [← hmain]
  refine integral_congr_ae ?_
  filter_upwards [] with y
  rw [mellin_log_comp_eq_laplaceBoundary]

/-- **Integrability companion.** -/
theorem integrable_norm_sq_laplaceBoundary
    {g : ℝ → ℂ} (h1 : Integrable g) (h2 : MemLp g 2 volume) :
    Integrable (fun y : ℝ => ‖laplaceBoundary g y‖ ^ (2 : ℕ)) := by
  have hsrc := logMellinLineSource_log_comp g
  have h1' : Integrable (logMellinLineSource (fun x : ℝ => g (-Real.log x)) 0) := by
    rw [hsrc]; exact h1
  have h2' : MemLp (logMellinLineSource (fun x : ℝ => g (-Real.log x)) 0) 2 volume := by
    rw [hsrc]; exact h2
  have hmain := integrable_norm_sq_mellin_line_of_logMellinLineSource h1' h2'
  refine hmain.congr ?_
  filter_upwards [] with y
  rw [mellin_log_comp_eq_laplaceBoundary]

/-- Linearity of the boundary transform on integrable inputs. -/
theorem laplaceBoundary_sub {g h : ℝ → ℂ} (hg : Integrable g) (hh : Integrable h) (y : ℝ) :
    laplaceBoundary (fun u => g u - h u) y = laplaceBoundary g y - laplaceBoundary h y := by
  have hgi : Integrable (fun u : ℝ => Complex.exp (-((y : ℂ) * Complex.I) * (u : ℂ)) * g u) := by
    refine hg.bdd_mul (c := 1) ?_ ?_
    · exact (by fun_prop :
        Measurable fun u : ℝ => Complex.exp (-((y : ℂ) * Complex.I) * (u : ℂ))).aestronglyMeasurable
    · filter_upwards [] with u
      rw [Complex.norm_exp]
      have hre : (-((y : ℂ) * Complex.I) * (u : ℂ)).re = 0 := by
        simp [Complex.mul_re]
      rw [hre]
      norm_num
  have hhi : Integrable (fun u : ℝ => Complex.exp (-((y : ℂ) * Complex.I) * (u : ℂ)) * h u) := by
    refine hh.bdd_mul (c := 1) ?_ ?_
    · exact (by fun_prop :
        Measurable fun u : ℝ => Complex.exp (-((y : ℂ) * Complex.I) * (u : ℂ))).aestronglyMeasurable
    · filter_upwards [] with u
      rw [Complex.norm_exp]
      have hre : (-((y : ℂ) * Complex.I) * (u : ℂ)).re = 0 := by
        simp [Complex.mul_re]
      rw [hre]
      norm_num
  rw [laplaceBoundary, laplaceBoundary, laplaceBoundary, ← integral_sub hgi hhi]
  refine integral_congr_ae ?_
  filter_upwards [] with u
  ring

end RHTower
