import GaloisForLFunctions.RHTower.Sieve.VerticalPoleIntegral
import GaloisForLFunctions.RHTower.Sieve.PerronVerticalPrimeBound

/-!
# The Cesàro Perron kernel on a vertical line

The kernel `x^s/s²` decays like `1/|s|²`, and that second order of decay is *absolutely integrable* on
the line:

`∫_ℝ dt/‖σ+it‖² = ∫_ℝ dt/(σ² + t²) = π/σ`,

so the vertical integral of a Dirichlet series against it is bounded by the series' *pointwise* size
alone — no mean square, no Cauchy–Schwarz, no dyadic split, and no block count.  Against the first-order
kernel `x^s/s`, whose integral `∫ dt/|t|` diverges logarithmically, the whole apparatus of block moments
exists precisely to replace that divergence; at second order it is unnecessary.

The price is paid on the arithmetic side instead: `x^s/s²` has a double pole at `s = 0` and reproduces
the *logarithmically weighted* partial sum `∑_{n ≤ x} c_n log(x/n)`, not the partial sum itself.
-/

noncomputable section
namespace RHTower.Sieve
open Complex MeasureTheory Set

/-- The squared modulus of a point of the line `Re s = σ`. -/
theorem normSq_line (σ t : ℝ) : ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2 = σ ^ 2 + t ^ 2 := by
  rw [Complex.norm_add_mul_I, Real.sq_sqrt (by positivity)]

/-- The reciprocal squared modulus is continuous on the line. -/
theorem continuous_inv_normSq_line {σ : ℝ} (hσ : 0 < σ) :
    Continuous fun t : ℝ => 1 / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2 := by
  have heq : (fun t : ℝ => 1 / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2)
      = fun t : ℝ => 1 / (σ ^ 2 + t ^ 2) := by
    funext t
    rw [normSq_line]
  rw [heq]
  exact continuous_const.div (by continuity) fun t => by positivity

/-- **The line integral of the second-order kernel converges.**  `∫_{-T}^{T} dt/(σ² + t²) ≤ π/σ`,
uniformly in the height. -/
theorem integral_symm_inv_normSq_le {σ : ℝ} (hσ : 0 < σ) (T : ℝ) :
    (∫ t in (-T)..T, 1 / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2) ≤ Real.pi / σ := by
  have hpt : ∀ t : ℝ, 1 / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2 = σ⁻¹ * (σ / (σ ^ 2 + t ^ 2)) := by
    intro t
    rw [normSq_line]
    have hne : (σ ^ 2 + t ^ 2) ≠ 0 := by positivity
    field_simp
  rw [intervalIntegral.integral_congr (g := fun t => σ⁻¹ * (σ / (σ ^ 2 + t ^ 2)))
    (fun t _ => hpt t), intervalIntegral.integral_const_mul,
    integral_re_pole_line (α := σ) (T := T) (ne_of_gt hσ)]
  have harc : Real.arctan (T / σ) < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have hinv : (0 : ℝ) < σ⁻¹ := by positivity
  have hstep : σ⁻¹ * (2 * Real.arctan (T / σ)) ≤ σ⁻¹ * (2 * (Real.pi / 2)) :=
    mul_le_mul_of_nonneg_left (by linarith) hinv.le
  have hval : σ⁻¹ * (2 * (Real.pi / 2)) = Real.pi / σ := by field_simp
  rw [hval] at hstep
  exact hstep

/-- The modulus of the Cesàro Perron integrand. -/
theorem norm_cesaro_integrand {x : ℝ} (hx : 0 < x) (a : ℂ) (σ t : ℝ) :
    ‖a * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)‖
      = ‖a‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2) := by
  have hre : ((σ : ℂ) + (t : ℝ) * I).re = σ := by simp
  rw [norm_mul, norm_div, norm_pow, Complex.norm_cpow_eq_rpow_re_of_pos hx, hre]

/-- **The vertical integral against the Cesàro kernel, from a pointwise bound alone.**  A Dirichlet
series bounded by `V` on the range of integration has

`∫_{|t| ≤ T} ‖L(g,σ+it)·x^s/s²‖ ≤ V·x^σ·π/σ`,

with no dependence on the height whatsoever: the second-order decay is integrable.  This is the whole
analytic side of the Cesàro route, and it is where the extra `1/(σ−1)` of the mean-square route
disappears — there is no mean square to pay it. -/
theorem integral_symm_norm_cesaro_le {g : ℕ → ℂ} {sg : Finset ℕ} (hg0 : 0 ∉ sg)
    (hgsupp : ∀ n : ℕ, g n ≠ 0 → n ∈ sg) {σ x V T : ℝ} (hσ : 0 < σ) (hx : 0 < x) (hV : 0 ≤ V)
    (hT : 0 ≤ T)
    (hgV : ∀ t : ℝ, |t| ≤ T → ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ ≤ V) :
    (∫ t in (-T)..T,
        ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)
            * ((x : ℂ) ^ ((σ : ℂ) + (t : ℝ) * I) / ((σ : ℂ) + (t : ℝ) * I) ^ 2)‖)
      ≤ V * x ^ σ * (Real.pi / σ) := by
  have hxσ : (0 : ℝ) ≤ x ^ σ := Real.rpow_nonneg hx.le σ
  have hTle : -T ≤ T := by linarith
  have hgc : Continuous fun t : ℝ => LSeries g ((σ : ℂ) + (t : ℝ) * I) :=
    continuous_LSeries_line_of_support hg0 hgsupp σ
  have hKinv : Continuous fun t : ℝ => 1 / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2 :=
    continuous_inv_normSq_line hσ
  have hKeq : (fun t : ℝ => x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2)
      = fun t : ℝ => x ^ σ * (1 / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2) := by
    funext t
    rw [mul_one_div]
  have hKc : Continuous fun t : ℝ => x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2 := by
    rw [hKeq]
    exact continuous_const.mul hKinv
  have hKnn : ∀ t : ℝ, (0 : ℝ) ≤ x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2 := fun t =>
    div_nonneg hxσ (by positivity)
  rw [intervalIntegral.integral_congr (g := fun t : ℝ =>
      ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2))
    (fun t _ => norm_cesaro_integrand hx _ σ t)]
  have hmono : ∀ t ∈ Set.Icc (-T) T,
      ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2)
        ≤ V * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2) := fun t ht =>
    mul_le_mul_of_nonneg_right (hgV t (abs_le.2 ⟨ht.1, ht.2⟩)) (hKnn t)
  calc (∫ t in (-T)..T,
        ‖LSeries g ((σ : ℂ) + (t : ℝ) * I)‖ * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2))
      ≤ ∫ t in (-T)..T, V * (x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2) :=
        intervalIntegral.integral_mono_on hTle ((hgc.norm.mul hKc).intervalIntegrable _ _)
          ((continuous_const.mul hKc).intervalIntegrable _ _) hmono
    _ = V * ∫ t in (-T)..T, x ^ σ / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2 :=
        intervalIntegral.integral_const_mul _ _
    _ = V * (x ^ σ * ∫ t in (-T)..T, 1 / ‖(σ : ℂ) + (t : ℝ) * I‖ ^ 2) := by
        rw [hKeq, intervalIntegral.integral_const_mul]
    _ ≤ V * (x ^ σ * (Real.pi / σ)) :=
        mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (integral_symm_inv_normSq_le hσ T) hxσ) hV
    _ = V * x ^ σ * (Real.pi / σ) := by ring

end RHTower.Sieve
end
