import GaloisForLFunctions.RHTower.HalfWeightEisensteinRegularity
import GaloisForLFunctions.HTGeometry.CauchyDominatedIntegralHolomorphy

/-!
# The Rankin–Selberg integral against the weight-½ Eisenstein series

For a continuous `G` on `ℍ` with `G(γz) = \overline{j(γ,z)} G(z)` on `Γ₀(4M)` (the law of
`u(4z) \overline{θ(z)} y^{1/4}` for `Γ₀(M)`-invariant `u`), define the folded integral

`rsFold(w) = ∫_𝒟 Σ_{c ∈ Γ₀(4M)\SL₂(ℤ)} G(out c · z) E*(out c · z, w) dμ`.

* **`differentiableAt_rsFold`**: if every translate `G(out c · z)` decays faster than every power of `y`
  and `1/y` on `𝒟` (integrability against `y^A + y^{-A}`), then `rsFold` is holomorphic on the strip
  `Re w > 1/4` (dominated differentiation under the integral, using `Estar_growth` and
  `continuous_Estar`).
* **`rsFold_eq`**: for `Re w > 1`, `rsFold(w) = 2 ρ(w) ∫_{0 ≤ Re z < 1} G(z) y^w dμ`
  (`unfold_eisHalf`).

Hence `w ↦ ρ(w) ∫_{strip} G y^w dμ`, `ρ(w) = (4w-3)(4w-2)ζ(4w-1)`, continues holomorphically from
`Re w > 1` to `Re w > 1/4`: this is Shimura's continuation of `Σ ρ_u(k²) k^{-s}` once the Mellin
transform of the zeroth Fourier coefficient of `G` is evaluated.
-/

open Real Complex Filter Topology MeasureTheory UpperHalfPlane Metric
open CongruenceSubgroup ModularGroup
open scoped MatrixGroups

namespace GaloisForLFunctions.RHTower.HalfWeight

open GaloisForLFunctions.HTGeometry

noncomputable section

variable (M : ℕ) [NeZero M]

/-- The folded Rankin–Selberg integral `∫_𝒟 Σ_{c ∈ Γ₀(4M)\SL₂(ℤ)} G(out c · z) E*(out c · z, w) dμ`. -/
def rsFold (G : UpperHalfPlane → ℂ) (w : ℂ) : ℂ :=
  ∫ z in fd, ∑ c : Cos0 M, G (Quotient.out c • z) * Estar M (Quotient.out c • z) w

theorem continuous_smul_sl (g : SL(2, ℤ)) : Continuous fun z : UpperHalfPlane => g • z := by
  show Continuous fun z : UpperHalfPlane => (Matrix.SpecialLinearGroup.mapGL ℝ g) • z
  exact continuous_const_smul _

/-- **Holomorphy of the folded Rankin–Selberg integral** on the half-plane `Re w > 1/4`, for a
continuous `G` whose translates decay faster than every power of `y` and `1/y` on `𝒟`. -/
theorem differentiableAt_rsFold {G : UpperHalfPlane → ℂ} (hGc : Continuous G)
    (hdec : ∀ (A : ℝ) (c : Cos0 M), IntegrableOn (fun z : UpperHalfPlane => ‖G (Quotient.out c • z)‖ *
      ((Quotient.out c • z).im ^ A + (Quotient.out c • z).im ^ (-A))) fd)
    {w₀ : ℂ} (h1 : 1 / 4 < w₀.re) :
    DifferentiableAt ℂ (rsFold M G) w₀ := by
  obtain ⟨r, hr0, C, A, hC0, hgrow⟩ := Estar_growth M h1
  set R := min r ((w₀.re - 1 / 4) / 2) with hR
  have hR0 : 0 < R := lt_min hr0 (by linarith)
  have hRr : R ≤ r := min_le_left _ _
  have hR1 : R ≤ (w₀.re - 1 / 4) / 2 := min_le_right _ _
  have hstrip : ∀ w ∈ ball w₀ R, 1 / 4 < w.re := by
    intro w hw
    obtain ⟨h3, h4⟩ := re_ge_of_mem_closedBall (ball_subset_closedBall hw)
    linarith
  set F : ℂ → UpperHalfPlane → ℂ := fun w z =>
    ∑ c : Cos0 M, G (Quotient.out c • z) * Estar M (Quotient.out c • z) w
  set bound : UpperHalfPlane → ℝ := fun z => ∑ c : Cos0 M,
    C * (‖G (Quotient.out c • z)‖ * ((Quotient.out c • z).im ^ A + (Quotient.out c • z).im ^ (-A)))
  have hmeas : ∀ w ∈ ball w₀ R, AEStronglyMeasurable (F w) (volume.restrict fd) := by
    intro w hw
    have h3 := hstrip w hw
    refine Continuous.aestronglyMeasurable ?_
    refine continuous_finsetSum _ fun c _ => ?_
    exact (hGc.comp (continuous_smul_sl _)).mul ((continuous_Estar M h3).comp (continuous_smul_sl _))
  have hdiff : ∀ z : UpperHalfPlane, DifferentiableOn ℂ (fun w => F w z) (ball w₀ R) := by
    intro z w hw
    have h3 := hstrip w hw
    refine DifferentiableAt.differentiableWithinAt ?_
    simp only [F]
    refine DifferentiableAt.fun_sum fun c _ => ?_
    exact (differentiableAt_Estar M _ h3).const_mul _
  have hbound : ∀ z : UpperHalfPlane, ∀ w ∈ ball w₀ R, ‖F w z‖ ≤ bound z := by
    intro z w hw
    have hwr : w ∈ closedBall w₀ r := closedBall_subset_closedBall hRr (ball_subset_closedBall hw)
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [norm_mul]
    have := hgrow w hwr (Quotient.out c • z)
    calc ‖G (Quotient.out c • z)‖ * ‖Estar M (Quotient.out c • z) w‖
        ≤ ‖G (Quotient.out c • z)‖ * (C * ((Quotient.out c • z).im ^ A + (Quotient.out c • z).im ^ (-A))) :=
          mul_le_mul_of_nonneg_left this (norm_nonneg _)
      _ = _ := by ring
  have hboundInt : Integrable bound (volume.restrict fd) :=
    integrable_finsetSum _ fun c _ => (hdec A c).const_mul C
  exact differentiableAt_integral_of_cauchy_dominated hR0 hmeas hdiff hbound hboundInt

/-- **The Rankin–Selberg identity**: for `Re w > 1`,
`∫_𝒟 Σ_c G(out c · z) E*(out c · z, w) dμ = 2 ρ(w) ∫_{0 ≤ Re z < 1} G(z) y^w dμ`. -/
theorem rsFold_eq {G : UpperHalfPlane → ℂ}
    (hG : ∀ γ ∈ Gamma0 (4 * M), ∀ z, G (γ • z) = starRingEnd ℂ (jU γ z) * G z)
    {w : ℂ} (hw : 1 < w.re)
    (hint : IntegrableOn (fun z : UpperHalfPlane => G z * ((z.im : ℝ) : ℂ) ^ w) modularStrip) :
    rsFold M G w = 2 * regF w * ∫ z in modularStrip, G z * ((z.im : ℝ) : ℂ) ^ w := by
  unfold rsFold
  simp_rw [Estar_eq M hw]
  have e : ∀ z : UpperHalfPlane, ∑ c : Cos0 M, G (Quotient.out c • z) *
      (regF w * eisHalf M (1 : DirichletCharacter ℂ (4 * M)) w (Quotient.out c • z)) =
      regF w * ∑ c : Cos0 M, G (Quotient.out c • z) *
        eisHalf M (1 : DirichletCharacter ℂ (4 * M)) w (Quotient.out c • z) := by
    intro z; rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun c _ => by ring
  simp_rw [e]
  rw [integral_const_mul, unfold_eisHalf M hw hG hint]
  ring

end

end GaloisForLFunctions.RHTower.HalfWeight
