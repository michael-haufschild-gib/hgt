import GaloisForLFunctions.RHTower.Sieve.HalaszPerronAssembly
import GaloisForLFunctions.HTGeometry.WeightedHolder
/-!
# The vertical integral split at a height

A smoothed Perron kernel has two different bounds: a uniform one, `‖W‖ ≤ (N+H)^σ/σ`, and a quadratic-decay
one, `‖W‖ ≤ C/(1+y²)` whose constant `C ≍ N^σ(N/H)²` is large for a narrow cutoff.  Using the second on the
whole line pays the `(N/H)²` everywhere; splitting the integral at height `T` pays it only in the tail, where
it is multiplied by `π − 2 arctan T`:

`‖∫_ℝ g₁g₂g₃W‖ ≤ M·Wsup·(∫_{|y|≤T}‖g₁‖²)^{1/2}(∫_{|y|≤T}‖g₂‖²)^{1/2} + Mg·C·(π − 2 arctan T)`,

with `Mg` a trivial bound for the product of the three series.  The truncated part is the Cauchy–Schwarz
inequality over `volume.restrict (Icc (−T) T)`, and the tail uses the corpus's
`integral_compl_Icc_inv_one_add_sq_le`.  This is the same split the corpus's Halász assembly performs for the
distance route, carried out here for the mean-square route.
-/

noncomputable section
namespace RHTower.Sieve
open MeasureTheory Set

/-- **The tail of a vertical integral against a decaying kernel.**  Beyond height `T` the integrand is bounded
by its trivial size times the kernel's decay, whose integral is `π − 2 arctan T`. -/
theorem norm_integral_compl_Icc_le {g W : ℝ → ℂ} {T Mg C : ℝ} (hT : 0 ≤ T) (hMg : 0 ≤ Mg)
    (hC : 0 ≤ C) (hg : ∀ y : ℝ, ‖g y‖ ≤ Mg) (hdecay : ∀ y : ℝ, ‖W y‖ ≤ C * (1 + y ^ (2 : ℕ))⁻¹) :
    ‖∫ y in (Set.Icc (-T) T)ᶜ, g y * W y‖ ≤ Mg * C * (Real.pi - 2 * Real.arctan T) := by
  have hbound : ∀ y : ℝ, ‖g y * W y‖ ≤ (Mg * C) * (1 + y ^ (2 : ℕ))⁻¹ := by
    intro y
    rw [norm_mul]
    calc ‖g y‖ * ‖W y‖ ≤ Mg * (C * (1 + y ^ (2 : ℕ))⁻¹) :=
          mul_le_mul (hg y) (hdecay y) (norm_nonneg _) hMg
      _ = (Mg * C) * (1 + y ^ (2 : ℕ))⁻¹ := by ring
  have hint2 : IntegrableOn (fun y : ℝ => (Mg * C) * (1 + y ^ (2 : ℕ))⁻¹) (Set.Icc (-T) T)ᶜ :=
    (integrable_inv_one_add_sq.const_mul (Mg * C)).integrableOn
  refine le_trans (norm_integral_le_integral_norm _) ?_
  have hmono : (∫ y in (Set.Icc (-T) T)ᶜ, ‖g y * W y‖)
      ≤ ∫ y in (Set.Icc (-T) T)ᶜ, (Mg * C) * (1 + y ^ (2 : ℕ))⁻¹ := by
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _) hint2 ?_
    filter_upwards with y using hbound y
  refine hmono.trans ?_
  rw [integral_const_mul]
  exact mul_le_mul_of_nonneg_left (integral_compl_Icc_inv_one_add_sq_le hT) (by positivity)

/-- **The vertical integral split at a height.**  The part beyond `T` is charged to the kernel's decay. -/
theorem norm_integral_le_truncated_add_tail {g W : ℝ → ℂ} {T Mg C : ℝ} (hT : 0 ≤ T) (hMg : 0 ≤ Mg)
    (hC : 0 ≤ C) (hg : ∀ y : ℝ, ‖g y‖ ≤ Mg) (hdecay : ∀ y : ℝ, ‖W y‖ ≤ C * (1 + y ^ (2 : ℕ))⁻¹)
    (hint : Integrable fun y => g y * W y) :
    ‖∫ y : ℝ, g y * W y‖
      ≤ ‖∫ y in Set.Icc (-T) T, g y * W y‖ + Mg * C * (Real.pi - 2 * Real.arctan T) := by
  have hsplit := integral_add_compl (measurableSet_Icc (a := -T) (b := T)) hint
  rw [← hsplit]
  refine le_trans (norm_add_le _ _) ?_
  have htail := norm_integral_compl_Icc_le (g := g) (W := W) hT hMg hC hg hdecay
  linarith [htail]

/-- **The truncated master inequality.**  Cauchy–Schwarz against the *uniform* kernel bound on `[−T, T]`, plus
the kernel's decay beyond it:

`‖∫_ℝ g₁g₂g₃W‖ ≤ M·Wsup·(∫_{|y|≤T}‖g₁‖²)^{1/2}(∫_{|y|≤T}‖g₂‖²)^{1/2} + Mg·C·(π − 2 arctan T)`.

The truncated part sees only `Wsup`, the uniform size of the kernel on a bounded height range, and the
quadratic-decay constant `C` — large for a smoothed cutoff of small width — is confined to the tail, where it
is multiplied by `π − 2 arctan T`. -/
theorem norm_integral_mul_three_le_truncated_add_tail {g₁ g₂ g₃ W : ℝ → ℂ} {M Wsup Mg C T : ℝ}
    (hT : 0 ≤ T) (hM0 : 0 ≤ M) (hWsup0 : 0 ≤ Wsup) (hMg0 : 0 ≤ Mg) (hC0 : 0 ≤ C)
    (hm1 : AEStronglyMeasurable g₁ (volume.restrict (Set.Icc (-T) T)))
    (hm2 : AEStronglyMeasurable g₂ (volume.restrict (Set.Icc (-T) T)))
    (hM : ∀ y : ℝ, ‖g₃ y‖ ≤ M) (hW : ∀ y : ℝ, ‖W y‖ ≤ Wsup)
    (hg : ∀ y : ℝ, ‖g₁ y * g₂ y * g₃ y‖ ≤ Mg)
    (hdecay : ∀ y : ℝ, ‖W y‖ ≤ C * (1 + y ^ (2 : ℕ))⁻¹)
    (hint : Integrable fun y => g₁ y * g₂ y * g₃ y * W y)
    (h1 : IntegrableOn (fun y => ‖g₁ y‖ ^ (2 : ℕ)) (Set.Icc (-T) T))
    (h2 : IntegrableOn (fun y => ‖g₂ y‖ ^ (2 : ℕ)) (Set.Icc (-T) T)) :
    ‖∫ y : ℝ, g₁ y * g₂ y * g₃ y * W y‖
      ≤ M * Wsup * (Real.sqrt (∫ y in Set.Icc (-T) T, ‖g₁ y‖ ^ (2 : ℕ))
            * Real.sqrt (∫ y in Set.Icc (-T) T, ‖g₂ y‖ ^ (2 : ℕ)))
        + Mg * C * (Real.pi - 2 * Real.arctan T) := by
  have hsplit := norm_integral_le_truncated_add_tail (g := fun y => g₁ y * g₂ y * g₃ y) (W := W)
    hT hMg0 hC0 hg hdecay hint
  refine hsplit.trans ?_
  have hmain := GaloisForLFunctions.HTGeometry.norm_integral_mul_three_le_sup_mul_sqrt_measure
    (μ := volume.restrict (Set.Icc (-T) T)) hm1 hm2 hM0 hWsup0
    (Filter.Eventually.of_forall hM) (Filter.Eventually.of_forall hW) h1 h2
  linarith [hmain]

end RHTower.Sieve
end
