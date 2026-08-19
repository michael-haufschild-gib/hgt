import GaloisForLFunctions.HTGeometry.HardyDiskModelDimension

/-!
# Hardy cyclicity is blind to the rational inner gauge

`hardy-cyclicity-maximal-ht-field-blindness`, statement `1` and statement `4` (equations
`(16)`–`(7)`).

The bounded outer carrier of the card is `O = exp σ` with `σ` analytic and `‖σ‖ < 1` on the disk:
then `O` and `O⁻¹ = exp (-σ)` are both bounded analytic, so `O` is a cyclic vector of the shift on
`H²(D)` — i.e. `[O] = H²(D)`.  Multiplying by a finite Blaschke product `B` of degree `k` gives

```text
[B·O] = B · H²(D),      dim (H²(D) ⊖ [B·O]) = k,
```

so one and the same carrier `O` produces every finite cyclicity defect.
-/

open Complex Filter Metric Real Topology

noncomputable section

namespace GaloisForLFunctions.HTGeometry

/-! ## The exponential carrier -/

/-- `exp σ` as a bounded analytic multiplier, for `‖σ‖ < 1` on the disk. -/
def expMultiplier {σ : ℂ → ℂ} (hσ : DifferentiableOn ℂ σ (Metric.ball 0 1))
    (hb : ∀ z ∈ Metric.ball (0:ℂ) 1, ‖σ z‖ < 1) : DiskMultiplier where
  fn := fun z => Complex.exp (σ z)
  diff := Complex.differentiable_exp.comp_differentiableOn hσ
  bd := Real.exp 1
  bd_nonneg := (Real.exp_pos 1).le
  bd_le := fun z hz => by
    rw [Complex.norm_exp]
    refine Real.exp_le_exp.mpr (le_of_lt (lt_of_le_of_lt ?_ (hb z hz)))
    exact Complex.re_le_norm _

theorem expMultiplier_fn {σ : ℂ → ℂ} (hσ : DifferentiableOn ℂ σ (Metric.ball 0 1))
    (hb : ∀ z ∈ Metric.ball (0:ℂ) 1, ‖σ z‖ < 1) (z : ℂ) :
    (expMultiplier hσ hb).fn z = Complex.exp (σ z) := rfl

theorem neg_bounded {σ : ℂ → ℂ} (hb : ∀ z ∈ Metric.ball (0:ℂ) 1, ‖σ z‖ < 1) :
    ∀ z ∈ Metric.ball (0:ℂ) 1, ‖(fun w => -σ w) z‖ < 1 := by
  intro z hz
  show ‖-σ z‖ < 1
  rw [norm_neg]
  exact hb z hz

/-- **Statement 1.**  `O = exp σ` and `O⁻¹ = exp (-σ)` are both bounded analytic on the disk, so
`O` is a cyclic vector for the shift: `[O] = H²(D)`. -/
theorem cyclicSubspace_expCarrier {σ : ℂ → ℂ} (hσ : DifferentiableOn ℂ σ (Metric.ball 0 1))
    (hb : ∀ z ∈ Metric.ball (0:ℂ) 1, ‖σ z‖ < 1) :
    cyclicSubspace (hardyOf (expMultiplier hσ hb)) = ⊤ := by
  refine cyclicSubspace_hardyOf_eq_top (ψ := expMultiplier hσ.neg (neg_bounded hb))
    (fun z _ => ?_)
  show Complex.exp (σ z) * Complex.exp (-σ z) = 1
  rw [← Complex.exp_add, add_neg_cancel, Complex.exp_zero]

/-! ## The full gauge-blindness statement -/

/-- **Statement 4 / equations (16), (7).**  For the bounded invertible carrier `O = exp σ` and any
finite Blaschke product `B` of degree `k`:

* `[O] = H²(D)`;
* `[B·O] = B·H²(D)`;
* `dim (H²(D) ⊖ [B·O]) = k`.

Hence a single carrier realizes every finite Hardy cyclicity defect. -/
theorem hardyCyclicityDefect {σ : ℂ → ℂ} (hσ : DifferentiableOn ℂ σ (Metric.ball 0 1))
    (hb : ∀ z ∈ Metric.ball (0:ℂ) 1, ‖σ z‖ < 1)
    {k : ℕ} (a : Fin k → ℂ) {c : ℝ} (hc0 : 0 ≤ c) (hc1 : c < 1) (hle : ∀ j, ‖a j‖ ≤ c) :
    cyclicSubspace (hardyOf (expMultiplier hσ hb)) = ⊤ ∧
      cyclicSubspace (hardyMul (blaschkeOf a hc0 hc1 hle).toMultiplier
          (hardyOf (expMultiplier hσ hb)))
        = LinearMap.range ((hardyMul (blaschkeOf a hc0 hc1 hle).toMultiplier :
            HardyDisk →L[ℂ] HardyDisk) : HardyDisk →ₗ[ℂ] HardyDisk) ∧
      Module.finrank ℂ ((LinearMap.range ((hardyMul (blaschkeOf a hc0 hc1 hle).toMultiplier :
        HardyDisk →L[ℂ] HardyDisk) : HardyDisk →ₗ[ℂ] HardyDisk))ᗮ : Submodule ℂ HardyDisk) = k := by
  have hcyc := cyclicSubspace_expCarrier hσ hb
  exact ⟨hcyc, cyclicSubspace_blaschke_mul _ hcyc,
    (finrank_orthogonal_range_blaschkeOf k a hc0 hc1 hle).2⟩

end GaloisForLFunctions.HTGeometry
