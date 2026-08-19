import GaloisForLFunctions.HTGeometry.QuasiAbelianComplementGrowthData

/-!
# The seed bound on an arbitrary compact set

The damped bound holds only on a region small compared with the lattice spacing, because that is
what makes the damping rate positive.  Local normal convergence of the Poincaré series, by contrast,
is a statement at a **fixed** scale on **every** compact set, so it needs no damping at all: the
constant may depend on the compact set and on the scale.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- A compact set has a uniform radius about any centre. -/
theorem exists_centered_radius_of_isCompact {d : ℕ} (center : Fin d → ℂ)
    {K : Set (Fin d → ℂ)} (hK : IsCompact K) :
    ∃ ρ : ℝ, 0 ≤ ρ ∧ ∀ x ∈ K, ∀ i,
      |(x i).re - (center i).re| ≤ ρ ∧ |(x i).im - (center i).im| ≤ ρ := by
  classical
  obtain ⟨R, hR0, hR⟩ := exists_coordinate_bound_of_isCompact hK
  refine ⟨R + ∑ j, (|(center j).re| + |(center j).im|), by positivity, fun x hx i => ?_⟩
  have hxi := hR x hx i
  have hcj : |(center i).re| + |(center i).im|
      ≤ ∑ j, (|(center j).re| + |(center j).im|) :=
    Finset.single_le_sum (f := fun j => |(center j).re| + |(center j).im|)
      (fun j _ => by positivity) (Finset.mem_univ i)
  constructor
  · have h1 : |(x i).re - (center i).re| ≤ |(x i).re| + |(center i).re| := abs_sub _ _
    have := abs_nonneg ((center i).im)
    linarith [hxi.1]
  · have h1 : |(x i).im - (center i).im| ≤ |(x i).im| + |(center i).im| := abs_sub _ _
    have := abs_nonneg ((center i).re)
    linarith [hxi.2]

/-- **The scaled Gaussian on an arbitrary compact set.**  No smallness hypothesis: the constant
absorbs the region. -/
theorem exists_norm_scaledGaussian_realTranslate_le {d : ℕ} (σ : Fin d → ℝ) (hσ : ∀ i, 0 < σ i)
    (center : Fin d → ℂ) {K : Set (Fin d → ℂ)} (hK : IsCompact K) {B : ℝ} (hB : 1 ≤ B) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (v : Fin d → ℝ) (x : Fin d → ℂ), x ∈ K →
      ‖(centeredComplexGaussian (fun i => B * σ i) center).1 (x + fun i => ((v i : ℝ) : ℂ))‖
        ≤ C * Real.exp (-∑ i, σ i / 4 * (v i) ^ 2) := by
  classical
  obtain ⟨ρ, hρ0, hρ⟩ := exists_centered_radius_of_isCompact center hK
  have hB0 : (0 : ℝ) < B := by linarith
  refine ⟨Real.exp (B * ((∑ i, σ i) * (2 * ρ ^ 2))), (Real.exp_pos _).le, fun v x hx => ?_⟩
  rw [norm_centeredComplexGaussian_apply, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hterm : ∀ i : Fin d,
      -((B * σ i) * ((((x + fun j => ((v j : ℝ) : ℂ)) i - center i).re) ^ 2
          - (((x + fun j => ((v j : ℝ) : ℂ)) i - center i).im) ^ 2))
        ≤ B * (σ i * (2 * ρ ^ 2)) - σ i / 4 * (v i) ^ 2 := by
    intro i
    have hre : (((x + fun j => ((v j : ℝ) : ℂ)) i - center i)).re
        = (x i).re + v i - (center i).re := by
      simp [Complex.add_re, Complex.sub_re]
    have him : (((x + fun j => ((v j : ℝ) : ℂ)) i - center i)).im
        = (x i).im - (center i).im := by
      simp [Complex.add_im, Complex.sub_im]
    rw [hre, him]
    obtain ⟨ht, hu⟩ := hρ x hx i
    set t : ℝ := (x i).re - (center i).re with htdef
    set u : ℝ := (x i).im - (center i).im with hudef
    have hsum : (x i).re + v i - (center i).re = v i + t := by rw [htdef]; ring
    rw [hsum]
    have ht2 : t ^ 2 ≤ ρ ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg t) ht 2
      rwa [sq_abs] at h
    have hu2 : u ^ 2 ≤ ρ ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg u) hu 2
      rwa [sq_abs] at h
    have hkey : (v i) ^ 2 / 2 - t ^ 2 ≤ (v i + t) ^ 2 := by
      nlinarith [sq_nonneg (v i + 2 * t)]
    have hσi := (hσ i).le
    have hBσ : (0 : ℝ) ≤ B * σ i := mul_nonneg hB0.le hσi
    have hshrink : σ i / 4 * (v i) ^ 2 ≤ B * σ i * ((v i) ^ 2 / 2) := by
      have hprod : (0 : ℝ) ≤ (B - 1) * σ i * (v i) ^ 2 :=
        mul_nonneg (mul_nonneg (by linarith) hσi) (sq_nonneg _)
      nlinarith [sq_nonneg (v i), hσi, hprod]
    nlinarith [mul_le_mul_of_nonneg_left hkey hBσ,
      mul_le_mul_of_nonneg_left ht2 hBσ, mul_le_mul_of_nonneg_left hu2 hBσ, hshrink]
  have hsum_le : (-∑ i, (B * σ i) * ((((x + fun j => ((v j : ℝ) : ℂ)) i - center i).re) ^ 2
        - (((x + fun j => ((v j : ℝ) : ℂ)) i - center i).im) ^ 2))
      ≤ ∑ i, (B * (σ i * (2 * ρ ^ 2)) - σ i / 4 * (v i) ^ 2) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun i _ => hterm i
  refine le_trans hsum_le ?_
  rw [Finset.sum_sub_distrib]
  have hA : ∑ i, B * (σ i * (2 * ρ ^ 2)) = B * ((∑ i, σ i) * (2 * ρ ^ 2)) := by
    rw [← Finset.mul_sum, ← Finset.sum_mul]
  rw [hA]
  linarith

end

end GaloisForLFunctions.HTGeometry
