import GaloisForLFunctions.RHTower.ZetaFixedSigmaDensity

/-!
# Near-line comparison of `|ξ|` along horizontal segments

For `0 ≤ v ≤ d` and a height `y`,

`|ξ(½ + v + iy)| ≤ |ξ(½ + d + iy)|`

whenever every zero `ρ` of `ξ` satisfies `2(Re ρ − ½)² ≤ d²` or `(Re ρ − ½)² ≤ (Im ρ − y)²`
(`norm_xi_half_add_le_of_zeros`). Only zeros displaced by more than `d/√2` from the critical line
and closer in height to `y` than their own displacement can obstruct the comparison.

The proof is the Weierstrass pair law for `Ξ(z) = ξ(½ + iz)` (`DeBruijn.norm_sub_shift_le_local`)
at the midpoint `m = (v + d)/2` with shift `λ = (d − v)/2`: a conjugate pair of zeros with
imaginary part `b` obstructs only if `b² > (Re − y)² + m² + λ²`, and `m² + λ² = (v² + d²)/2 ≥ d²/2`.
-/

noncomputable section

open Complex Set

namespace RHTower

namespace DeBruijn

/-- **Height comparison for `Ξ`.** -/
theorem norm_riemannHeat_zero_vertical_le {x v d : ℝ} (hv : 0 ≤ v) (hvd : v ≤ d)
    (hloc : ∀ ζ, riemannHeat 0 ζ = 0 → 2 * ζ.im ^ 2 ≤ d ^ 2 ∨ ζ.im ^ 2 ≤ (ζ.re - x) ^ 2) :
    ‖riemannHeat 0 ((x : ℂ) + I * v)‖ ≤ ‖riemannHeat 0 ((x : ℂ) + I * d)‖ := by
  obtain ⟨C, hC, hbound⟩ := (riemannKernel_superExp.mul_exp_sq le_rfl).exists_envelope
  rcases eq_or_lt_of_le hvd with h | h
  · rw [h]
  by_cases hz1 : riemannHeat 0 ((x : ℂ) + I * v) = 0
  · rw [hz1, norm_zero]; exact norm_nonneg _
  have hd0 : 0 < d := by linarith
  have hz2 : riemannHeat 0 ((x : ℂ) + I * d) ≠ 0 := by
    intro h0
    rcases hloc _ h0 with hc | hc <;> simp at hc <;> nlinarith
  set z : ℂ := (x : ℂ) + I * ((v + d) / 2 : ℝ) with hz
  set lam : ℝ := (d - v) / 2 with hlam
  have hzm : z - lam * I = (x : ℂ) + I * v := by rw [hz, hlam]; push_cast; ring
  have hzp : z + lam * I = (x : ℂ) + I * d := by rw [hz, hlam]; push_cast; ring
  have hzre : z.re = x := by simp [hz]
  have hzim : z.im = (v + d) / 2 := by simp [hz]
  have hres := norm_sub_shift_le_local hC (riemannHeat_analytic le_rfl)
    (riemannHeat_zero_ne le_rfl) (riemannHeat_neg le_rfl) (riemannHeat_conj le_rfl) hbound
    (lam := lam) (z := z) (by rw [hlam]; linarith) (by rw [hzim]; linarith)
    (fun ζ hζ => by
      rw [hzre, hzim, hlam]
      rcases hloc ζ hζ with hc | hc
      · nlinarith [sq_nonneg (ζ.re - x), sq_nonneg v]
      · nlinarith [sq_nonneg ((v + d) / 2), sq_nonneg ((d - v) / 2)])
    (by rw [hzm]; exact hz1) (by rw [hzp]; exact hz2)
  rwa [hzm, hzp] at hres

end DeBruijn

/-- `|ξ(½ − v + iy)| = |ξ(½ + v + iy)|`. -/
theorem norm_xi_half_sub_eq (v y : ℝ) :
    ‖xi ((1 / 2 - v : ℝ) + (y : ℂ) * I)‖ = ‖xi ((1 / 2 + v : ℝ) + (y : ℂ) * I)‖ := by
  have h1 : ((1 / 2 - v : ℝ) : ℂ) + (y : ℂ) * I =
      1 - (starRingEnd ℂ) (((1 / 2 + v : ℝ) : ℂ) + (y : ℂ) * I) := by
    apply Complex.ext
    · simp; ring
    · simp
  rw [h1, xi_one_sub, xi_conj, Complex.norm_conj]

/-- **Near-line comparison for `|ξ|`.** -/
theorem norm_xi_half_add_le_of_zeros {y v d : ℝ} (hv : 0 ≤ v) (hvd : v ≤ d)
    (hzeros : ∀ ρ : ℂ, xi ρ = 0 →
      2 * (ρ.re - 1 / 2) ^ 2 ≤ d ^ 2 ∨ (ρ.re - 1 / 2) ^ 2 ≤ (ρ.im - y) ^ 2) :
    ‖xi ((1 / 2 + v : ℝ) + (y : ℂ) * I)‖ ≤ ‖xi ((1 / 2 + d : ℝ) + (y : ℂ) * I)‖ := by
  have hpt : ∀ w : ℝ, DeBruijn.riemannHeat 0 ((y : ℂ) + I * w) =
      xi ((1 / 2 - w : ℝ) + (y : ℂ) * I) := by
    intro w
    rw [DeBruijn.riemannHeat_zero]
    congr 1
    apply Complex.ext
    · simp; ring
    · simp
  have hloc : ∀ ζ, DeBruijn.riemannHeat 0 ζ = 0 →
      2 * ζ.im ^ 2 ≤ d ^ 2 ∨ ζ.im ^ 2 ≤ (ζ.re - y) ^ 2 := by
    intro ζ hζ
    rw [DeBruijn.riemannHeat_zero] at hζ
    have hre : (1 / 2 + I * ζ).re = 1 / 2 - ζ.im := by simp; ring
    have him : (1 / 2 + I * ζ).im = ζ.re := by simp
    rcases hzeros _ hζ with h | h
    · left
      rw [hre] at h
      nlinarith
    · right
      rw [hre, him] at h
      nlinarith
  have h := DeBruijn.norm_riemannHeat_zero_vertical_le (x := y) hv hvd hloc
  rw [hpt, hpt, norm_xi_half_sub_eq, norm_xi_half_sub_eq] at h
  exact h

end RHTower
