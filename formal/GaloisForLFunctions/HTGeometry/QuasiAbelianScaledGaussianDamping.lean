import GaloisForLFunctions.HTGeometry.QuasiAbelianGaussianLatticeDecay

/-!
# Scaling the Gaussian width damps the nonzero lattice translates

Abe's damping family is not a new function but a rescaling: replacing the Gaussian widths `σ` by
`B·σ` leaves the centre value, and hence every finite jet at the centre, untouched, while sharpening
the lattice decay to `exp(-B·Σσᵢkᵢ²/2)`.

The catch is that the constant in the lattice bound comes from `(k+t)² ≥ k²/2 - t²` and from the
imaginary part, so it too is exponential in the scale.  The damping is genuine exactly when the
evaluation region is small compared with the lattice spacing: `(Σσᵢ)·2ρ² < σ₀/4`, a condition on the
region alone, stable under the rescaling.
-/

open Filter Topology

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- A nonzero integer vector contributes at least one full width to the Gaussian exponent. -/
theorem sum_width_sq_ge_of_ne_zero {d : ℕ} (σ : Fin d → ℝ) (hσ : ∀ i, 0 < σ i)
    {σ₀ : ℝ} (hσ₀le : ∀ i, σ₀ ≤ σ i) {k : Fin d → ℤ} (hk : k ≠ 0) :
    σ₀ ≤ ∑ i, σ i * ((k i : ℝ)) ^ 2 := by
  classical
  obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hk (funext hall)
  have hone : (1 : ℝ) ≤ ((k i : ℝ)) ^ 2 := by
    have h1 : (1 : ℤ) ≤ |k i| := Int.one_le_abs (by omega)
    have h2 : (1 : ℝ) ≤ |(k i : ℝ)| := by exact_mod_cast h1
    nlinarith [abs_nonneg ((k i : ℝ)), sq_abs ((k i : ℝ))]
  have hterm : σ₀ ≤ σ i * ((k i : ℝ)) ^ 2 := by
    have := hσ₀le i
    nlinarith [(hσ i).le]
  refine le_trans hterm (Finset.single_le_sum (f := fun j => σ j * ((k j : ℝ)) ^ 2)
    (fun j _ => mul_nonneg (hσ j).le (sq_nonneg _)) (Finset.mem_univ i))

/-- **The scaled Gaussian is exponentially damped in the scale on every nonzero lattice
translate.**  The evaluation region is required to be small compared with the lattice spacing; that
requirement is on the region alone, so it survives the rescaling. -/
theorem norm_scaledGaussian_realTranslate_damped {d : ℕ} (σ : Fin d → ℝ) (hσ : ∀ i, 0 < σ i)
    (center : Fin d → ℂ) {ρ σ₀ : ℝ}
    {K : Set (Fin d → ℂ)}
    (hKb : ∀ x ∈ K, ∀ i, |(x i).re - (center i).re| ≤ ρ ∧ |(x i).im - (center i).im| ≤ ρ)
    {B : ℝ} (hB : 1 ≤ B) {v : Fin d → ℝ} (hv : σ₀ ≤ ∑ i, σ i * (v i) ^ 2)
    {x : Fin d → ℂ} (hx : x ∈ K) :
    ‖(centeredComplexGaussian (fun i => B * σ i) center).1 (x + fun i => ((v i : ℝ) : ℂ))‖
      ≤ Real.exp (-((σ₀ / 4 - (∑ i, σ i) * (2 * ρ ^ 2)) * B))
        * Real.exp (-∑ i, σ i / 4 * (v i) ^ 2) := by
  classical
  have hB0 : (0 : ℝ) < B := by linarith
  rw [norm_centeredComplexGaussian_apply, ← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  -- bound the exponent coordinatewise
  have hterm : ∀ i : Fin d,
      -((B * σ i) * ((((x + fun i => ((v i : ℝ) : ℂ)) i - center i).re) ^ 2
          - (((x + fun i => ((v i : ℝ) : ℂ)) i - center i).im) ^ 2))
        ≤ B * (σ i * (2 * ρ ^ 2)) - B * (σ i * (v i) ^ 2) / 2 := by
    intro i
    have hre : (((x + fun i => ((v i : ℝ) : ℂ)) i - center i)).re
        = (x i).re + v i - (center i).re := by
      simp [Complex.add_re, Complex.sub_re]
    have him : (((x + fun i => ((v i : ℝ) : ℂ)) i - center i)).im
        = (x i).im - (center i).im := by
      simp [Complex.add_im, Complex.sub_im]
    rw [hre, him]
    obtain ⟨ht, hu⟩ := hKb x hx i
    set t : ℝ := (x i).re - (center i).re with htdef
    set u : ℝ := (x i).im - (center i).im with hudef
    have hsum : (x i).re + v i - (center i).re = v i + t := by rw [htdef]; ring
    rw [hsum]
    have habs_t : |t| ≤ ρ := ht
    have habs_u : |u| ≤ ρ := hu
    have ht2 : t ^ 2 ≤ ρ ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg t) habs_t 2
      rwa [sq_abs] at h
    have hu2 : u ^ 2 ≤ ρ ^ 2 := by
      have h := pow_le_pow_left₀ (abs_nonneg u) habs_u 2
      rwa [sq_abs] at h
    have hkey : (v i) ^ 2 / 2 - t ^ 2 ≤ (v i + t) ^ 2 := by
      nlinarith [sq_nonneg (v i + 2 * t)]
    have hσi := (hσ i).le
    have hBσ : (0 : ℝ) ≤ B * σ i := mul_nonneg hB0.le hσi
    nlinarith [mul_le_mul_of_nonneg_left hkey hBσ,
      mul_le_mul_of_nonneg_left ht2 hBσ, mul_le_mul_of_nonneg_left hu2 hBσ]
  have hsum_le : (-∑ i, (B * σ i) * ((((x + fun i => ((v i : ℝ) : ℂ)) i - center i).re) ^ 2
        - (((x + fun i => ((v i : ℝ) : ℂ)) i - center i).im) ^ 2))
      ≤ ∑ i, (B * (σ i * (2 * ρ ^ 2)) - B * (σ i * (v i) ^ 2) / 2) := by
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_le_sum fun i _ => hterm i
  refine le_trans hsum_le ?_
  rw [Finset.sum_sub_distrib]
  have hA : ∑ i, B * (σ i * (2 * ρ ^ 2)) = B * ((∑ i, σ i) * (2 * ρ ^ 2)) := by
    rw [← Finset.mul_sum, ← Finset.sum_mul]
  have hkpos : σ₀ ≤ ∑ i, σ i * (v i) ^ 2 := hv
  have hBsum : ∑ i, B * (σ i * (v i) ^ 2) / 2 = B * (∑ i, σ i * (v i) ^ 2) / 2 := by
    rw [Finset.mul_sum, ← Finset.sum_div]
  have hquarter : ∑ i, σ i / 4 * (v i) ^ 2 = (∑ i, σ i * (v i) ^ 2) / 4 := by
    rw [Finset.sum_div]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [hA, hBsum, hquarter]
  set T : ℝ := ∑ i, σ i * (v i) ^ 2 with hT
  have hT0 : 0 ≤ T := Finset.sum_nonneg fun i _ => mul_nonneg (hσ i).le (sq_nonneg _)
  nlinarith [hB0, hkpos, hT0]

/-- The lattice case: a nonzero integer translate carries at least one full width. -/
theorem norm_scaledGaussian_lattice_damped {d : ℕ} (σ : Fin d → ℝ) (hσ : ∀ i, 0 < σ i)
    (center : Fin d → ℂ) {ρ σ₀ : ℝ} (hσ₀le : ∀ i, σ₀ ≤ σ i)
    {K : Set (Fin d → ℂ)}
    (hKb : ∀ x ∈ K, ∀ i, |(x i).re - (center i).re| ≤ ρ ∧ |(x i).im - (center i).im| ≤ ρ)
    {B : ℝ} (hB : 1 ≤ B) {k : Fin d → ℤ} (hk : k ≠ 0) {x : Fin d → ℂ} (hx : x ∈ K) :
    ‖(centeredComplexGaussian (fun i => B * σ i) center).1 (x + integerCastVector k)‖
      ≤ Real.exp (-((σ₀ / 4 - (∑ i, σ i) * (2 * ρ ^ 2)) * B))
        * Real.exp (-∑ i, σ i / 4 * ((k i : ℝ)) ^ 2) := by
  have hv : σ₀ ≤ ∑ i, σ i * (((k i : ℤ) : ℝ)) ^ 2 := sum_width_sq_ge_of_ne_zero σ hσ hσ₀le hk
  have h := norm_scaledGaussian_realTranslate_damped σ hσ center hKb hB hv hx
  have hvec : (fun i => (((k i : ℤ) : ℝ) : ℂ)) = integerCastVector k := by
    funext i
    rw [integerCastVector]
    push_cast
    ring
  rwa [hvec] at h

end

end GaloisForLFunctions.HTGeometry
