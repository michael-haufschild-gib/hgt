import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.TheCalibratedTowerIsATemperedConfiguration

/-!
# Logarithmic local counts for the calibrated tower

A unit ordinate window meets one level. Each calibrated node contributes
two reflected zeros, and index separation bounds the node count by
`1+k/Γ`. The chosen logarithmic density bound puts the configuration in
class `𝒵(γmin,C)`.
-/

open Complex Filter Set Topology

noncomputable section

namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
open ArithmeticOrientationGeometry ArithmeticCastelnuovoSeveri SquareRootThreshold Zeta23
namespace CalibratedWindowTower.Tower

variable {γmin C Θ : ℝ} {R : ℝ → ℝ} (W : Tower γmin C Θ R)

/-- Every unit ordinate window satisfies the prescribed logarithmic zero-count bound. -/
theorem localCount_config (hC : 0 < C) (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) (t : ℝ) :
    ((W.config hΘ hΘ2).N t (t + 1) : ℝ) ≤ C * Real.log (|t| + 3) := by
  classical
  let Z := W.config hΘ hΘ2
  have hlog0 : 0 ≤ Real.log (|t| + 3) := Real.log_nonneg (by linarith only [abs_nonneg t])
  rcases (Z.window t (t + 1)).eq_empty_or_nonempty with hE | ⟨ρ₀, hρ₀⟩
  · have hN0 : Z.N t (t + 1) = 0 := by simp only [ZeroConfig.N, hE, finsum_mem_empty]
    rw [hN0, Nat.cast_zero]
    exact mul_nonneg hC.le hlog0
  rcases hρ₀ with ⟨⟨p₀, rfl⟩, htlo, hthi⟩
  let j₀ := p₀.1
  let S := Finset.univ.filter (fun i : Fin ((W.block j₀).k + 1) =>
    t < ((W.block j₀).z i).im ∧ ((W.block j₀).z i).im ≤ t + 1)
  let F : Finset ℂ := (S ×ˢ (Finset.univ : Finset Bool)).image (fun p => W.pt ⟨j₀, p⟩)
  have hfin := Z.finite_window t (t + 1)
  have hsub : hfin.toFinset ⊆ F := by
    intro ρ hρ
    rw [Set.Finite.mem_toFinset] at hρ
    rcases hρ with ⟨⟨⟨j, i, b⟩, rfl⟩, hlo, hhi⟩
    have hj : j = j₀ := W.level_eq_of_common_unit_window ⟨j, (i, b)⟩ p₀ hlo hhi htlo hthi
    subst j
    apply Finset.mem_image.mpr
    refine ⟨(i, b), Finset.mem_product.mpr ⟨?_, Finset.mem_univ _⟩, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_univ _, by simpa only [W.pt_im] using And.intro hlo hhi⟩
  have hN : Z.N t (t + 1) ≤ 2 * S.card := by
    calc
      _ = ∑ ρ ∈ hfin.toFinset, Z.mult ρ := finsum_mem_eq_finite_toFinset_sum _ hfin
      _ = hfin.toFinset.card := by simp [Z, config]
      _ ≤ F.card := Finset.card_le_card hsub
      _ ≤ (S ×ˢ (Finset.univ : Finset Bool)).card := Finset.card_image_le
      _ = _ := by rw [Finset.card_product, Finset.card_univ, Fintype.card_bool, Nat.mul_comm]
  have hΓ : 0 < (W.block j₀).Γ := by linarith only [(W.block j₀).four_le]
  have hk : (0 : ℝ) < (W.block j₀).k := by exact_mod_cast (W.block j₀).degree_pos
  have hcount := card_calibrated_ordinate_window_le (div_pos hΓ hk) (W.block j₀).z
    (W.block j₀).separation t
  have hrecip : 1 / ((W.block j₀).Γ / (W.block j₀).k) =
      (W.block j₀).k / (W.block j₀).Γ := by field_simp
  rw [hrecip] at hcount
  have hNr : (Z.N t (t + 1) : ℝ) ≤ 2 * (S.card : ℝ) := by exact_mod_cast hN
  have hΓsq : (W.block j₀).Γ ≤ (|t| + 3) ^ 2 := by
    have him := (W.pt_im_bounds p₀).1
    have ht := le_abs_self t
    nlinarith only [him, hthi, ht, abs_nonneg t, sq_nonneg |t|]
  have hlog : Real.log (W.block j₀).Γ ≤ 2 * Real.log (|t| + 3) := by
    have hh := Real.log_le_log hΓ hΓsq
    simpa only [Real.log_pow, Nat.cast_ofNat] using hh
  have hClog := mul_le_mul_of_nonneg_left hlog hC.le
  have hdensity := (W.block j₀).local_count
  change (S.card : ℝ) ≤ (W.block j₀).k / (W.block j₀).Γ + 1 at hcount
  nlinarith only [hNr, hcount, hdensity, hClog]

/-- The calibrated tower belongs to the prescribed density class. -/
theorem inClassZ_config (hγ : 0 < γmin) (hC : 0 < C) (hΘ : 0 < Θ) (hΘ2 : Θ ≤ 1 / 2) :
    InClassZ γmin C (W.config hΘ hΘ2) := by
  refine ⟨W.temperedConfig_config hΘ hΘ2, ?_, ?_, W.localCount_config hC hΘ hΘ2⟩
  · rintro ρ ⟨p, rfl⟩
    have hh := (W.block p.1).lowest.trans (W.pt_im_bounds p).1
    exact (hγ.trans_le hh).ne'
  · rintro ρ ⟨p, rfl⟩
    have hh := (W.block p.1).lowest.trans (W.pt_im_bounds p).1
    rw [abs_of_pos (hγ.trans_le hh)]
    exact hh

end CalibratedWindowTower.Tower
end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
