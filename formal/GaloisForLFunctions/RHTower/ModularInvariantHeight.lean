import GaloisForLFunctions.RHTower.RepPointPairCuspBound

/-!
# The invariant height on the upper half-plane

`Y(z) = sup_{γ ∈ SL(2,ℤ)} Im(γz)` is attained at the representative of `z` in the modular cell, where it
equals `Im` (`invHeight_eq_of_mem_fd`), and it is `SL(2,ℤ)`-invariant (`invHeight_smul`).  Heights of
near points are comparable: `(Im z − Im w)² ≤ |z − w|² = 4 Im z Im w u(z, w)` gives
`Im z ≤ ρ(u) Im w` with `ρ(u) = 1 + 2u + 2√(u² + u)` (`im_le_rho_mul`), and the same holds for `Y`
(`invHeight_le_rho_mul`).  Since `ρ(u) → 1` as `u → 0`, `Y` is continuous (`continuous_invHeight`).
-/

open UpperHalfPlane ModularGroup Filter Topology
open scoped MatrixGroups

namespace GaloisForLFunctions.RHTower.RepPointPair

open GaloisForLFunctions.HTGeometry

noncomputable section

/-- The invariant height `Y(z) = sup_{γ ∈ SL(2,ℤ)} Im(γz)`. -/
def invHeight (z : ℍ) : ℝ := ⨆ g : SL(2, ℤ), (g • z).im

theorem bddAbove_im_orbit (z : ℍ) : BddAbove (Set.range fun g : SL(2, ℤ) => (g • z).im) := by
  obtain ⟨g₀, hg₀⟩ := exists_smul_mem_fd z
  refine ⟨(g₀ • z).im, ?_⟩
  rintro _ ⟨g, rfl⟩
  have := im_smul_le_of_mem_fd hg₀ (g * g₀⁻¹)
  rwa [mul_smul, inv_smul_smul] at this

theorem im_smul_le_invHeight (g : SL(2, ℤ)) (z : ℍ) : (g • z).im ≤ invHeight z :=
  le_ciSup (bddAbove_im_orbit z) g

theorem im_le_invHeight (z : ℍ) : z.im ≤ invHeight z := by
  simpa using im_smul_le_invHeight 1 z

theorem invHeight_pos (z : ℍ) : 0 < invHeight z := z.im_pos.trans_le (im_le_invHeight z)

theorem invHeight_eq_of_mem_fd {z : ℍ} (hz : z ∈ fd) : invHeight z = z.im :=
  le_antisymm (ciSup_le fun g => im_smul_le_of_mem_fd hz g) (im_le_invHeight z)

/-- **`Y` is `SL(2,ℤ)`-invariant.** -/
theorem invHeight_smul (B : SL(2, ℤ)) (z : ℍ) : invHeight (B • z) = invHeight z := by
  unfold invHeight
  simp_rw [← mul_smul]
  exact (Equiv.mulRight B).iSup_congr fun g => rfl

/-- The comparison factor `ρ(u) = 1 + 2u + 2√(u² + u)`. -/
def heightRatio (u : ℝ) : ℝ := 1 + 2 * u + 2 * Real.sqrt (u ^ 2 + u)

theorem continuous_heightRatio : Continuous heightRatio := by
  unfold heightRatio
  fun_prop

theorem heightRatio_zero : heightRatio 0 = 1 := by simp [heightRatio]

/-- **Heights of near points are comparable**: `Im z ≤ ρ(u(z, w)) Im w`. -/
theorem im_le_rho_mul (z w : ℍ) : z.im ≤ heightRatio (pairU z w) * w.im := by
  set u := pairU z w
  have hu : 0 ≤ u := pairU_nonneg z w
  have hy := z.im_pos
  have hy' := w.im_pos
  have hsq : (z.im - w.im) ^ 2 ≤ 4 * z.im * w.im * u := by
    have h1 : (z.im - w.im) ^ 2 ≤ dist (z : ℂ) w ^ 2 := by
      rw [Complex.dist_eq, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      simp only [Complex.sub_re, Complex.sub_im, UpperHalfPlane.coe_im, UpperHalfPlane.coe_re]
      nlinarith [sq_nonneg (z.re - w.re)]
    have h2 : dist (z : ℂ) w ^ 2 = 4 * z.im * w.im * u := by
      simp only [u, pairU]
      field_simp
    linarith
  set s := Real.sqrt (u ^ 2 + u)
  have hs0 : 0 ≤ s := Real.sqrt_nonneg _
  have hs2 : s ^ 2 = u ^ 2 + u := Real.sq_sqrt (by positivity)
  unfold heightRatio
  by_contra hlt
  push Not at hlt
  have h3 : 2 * s * w.im < z.im - (1 + 2 * u) * w.im := by linarith
  have h4 : (2 * s * w.im) ^ 2 < (z.im - (1 + 2 * u) * w.im) ^ 2 :=
    pow_lt_pow_left₀ h3 (by positivity) two_ne_zero
  have h5 : (2 * s * w.im) ^ 2 = 4 * (u ^ 2 + u) * w.im ^ 2 := by
    rw [mul_pow, mul_pow, hs2]
    ring
  nlinarith [h4, h5, hsq]

/-- **The invariant heights of near points are comparable**: `Y(z) ≤ ρ(u(z, w)) Y(w)`. -/
theorem invHeight_le_rho_mul (z w : ℍ) : invHeight z ≤ heightRatio (pairU z w) * invHeight w := by
  refine ciSup_le fun g => ?_
  have h := im_le_rho_mul (g • z) (g • w)
  rw [pairU_smul_int] at h
  have hρ : 0 ≤ heightRatio (pairU z w) := by
    unfold heightRatio
    have := pairU_nonneg z w
    positivity
  exact h.trans (mul_le_mul_of_nonneg_left (im_smul_le_invHeight g w) hρ)

/-- **`Y` is continuous.** -/
theorem continuous_invHeight : Continuous invHeight := by
  refine continuous_iff_continuousAt.2 fun z => ?_
  have hu : Tendsto (fun w => pairU z w) (𝓝 z) (𝓝 0) := by
    have := (continuous_pairU_right z).tendsto z
    simpa [pairU] using this
  have hu' : Tendsto (fun w => pairU w z) (𝓝 z) (𝓝 0) := by
    simpa [pairU_comm] using hu
  have hρ : Tendsto (fun w => heightRatio (pairU z w)) (𝓝 z) (𝓝 1) := by
    rw [← heightRatio_zero]
    exact (continuous_heightRatio.tendsto 0).comp hu
  have hρ' : Tendsto (fun w => heightRatio (pairU w z)) (𝓝 z) (𝓝 1) := by
    rw [← heightRatio_zero]
    exact (continuous_heightRatio.tendsto 0).comp hu'
  have hlow : Tendsto (fun w => invHeight z / heightRatio (pairU z w)) (𝓝 z) (𝓝 (invHeight z)) := by
    have := (tendsto_const_nhds (x := invHeight z)).div hρ one_ne_zero
    rw [div_one] at this
    exact this
  have hup : Tendsto (fun w => heightRatio (pairU w z) * invHeight z) (𝓝 z)
      (𝓝 (invHeight z)) := by
    simpa using hρ'.mul_const (invHeight z)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le hlow hup (fun w => ?_) (fun w => ?_)
  · have h := invHeight_le_rho_mul z w
    have hρpos : 0 < heightRatio (pairU z w) := by
      unfold heightRatio
      have := pairU_nonneg z w
      positivity
    rw [div_le_iff₀ hρpos, mul_comm]
    exact h
  · exact invHeight_le_rho_mul w z

end

end GaloisForLFunctions.RHTower.RepPointPair
