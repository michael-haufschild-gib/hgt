import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Sqrt

/-!
# The zero-edge response of a source and its regularized capacity

A nonnegative operator `A` with a source `v` represented by `A ζ = ρ • v` and `⟪v, ζ⟫ = 1` has an
exact zero-edge structure.  The representation forces the source to annihilate the kernel, and the
reduced inverse recovers the reciprocal residue,

`⟪v, S v⟫ = 1/ρ`.

Regularizing by `τ` splits the response along the kernel: with `v = p + q`, `p` in the kernel and
`q` orthogonal to it,

`⟪v, (A+τ)⁻¹ v⟫ = ‖p‖²/τ + ⟪q, (A+τ)⁻¹ q⟫`.

Hence a source with nonzero ground component has a response diverging like `‖p‖²/τ`, while a source
orthogonal to the kernel has a finite response.  Moving the source at the natural square-root rate
turns the second case into a Lorentzian profile of width `√τ`: if the ground component vanishes to
first order with velocity `c`, the regularized capacity converges to `ρ/(1 + ρ c s²)`.
-/

open Filter Topology RealInnerProductSpace

noncomputable section

namespace GaloisForLFunctions.HTGeometry

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-! ## The zero-edge reduced response -/

/-- **(HSC.19) The source annihilates the kernel.**  A source represented by a nonzero multiple of
the operator applied to one vector is orthogonal to the whole kernel. -/
theorem inner_ker_eq_zero_of_source (A : H →ₗ[ℝ] H)
    (hsymm : ∀ x y : H, ⟪A x, y⟫ = ⟪x, A y⟫)
    {v ζ k : H} {ρ : ℝ} (hρ : ρ ≠ 0) (hA : A ζ = ρ • v) (hk : A k = 0) :
    ⟪v, k⟫ = 0 := by
  have h1 : ⟪A ζ, k⟫ = ⟪ζ, A k⟫ := hsymm ζ k
  rw [hA, hk, inner_zero_right, real_inner_smul_left] at h1
  rcases mul_eq_zero.1 h1 with h | h
  · exact absurd h hρ
  · exact h

/-- **(HSC.19) The reduced resolvent recovers the reciprocal residue.**  If the source is
represented by `A ζ = ρ • v` with unit pairing and the reduced inverse `S` undoes `A` on the
kernel complement, then `⟪v, S v⟫ = 1/ρ`. -/
theorem inner_reducedInverse_eq_inv (A S : H →ₗ[ℝ] H)
    {v ζ k z : H} {ρ : ℝ} (hρ : ρ ≠ 0)
    (hdec : ζ = k + z) (hk : A k = 0) (hSz : S (A z) = z)
    (hA : A ζ = ρ • v) (hnorm : ⟪v, ζ⟫ = 1) (hperp : ⟪v, k⟫ = 0) :
    ⟪v, S v⟫ = 1 / ρ := by
  have hAz : A z = ρ • v := by
    rw [hdec, map_add, hk, zero_add] at hA
    exact hA
  have hSv : ρ • S v = z := by
    rw [← hSz, hAz, map_smul]
  have h1 : ⟪v, z⟫ = 1 := by
    rw [hdec, inner_add_right, hperp, zero_add] at hnorm
    exact hnorm
  have h2 : ρ * ⟪v, S v⟫ = 1 := by
    rw [← real_inner_smul_right, hSv, h1]
  field_simp
  linarith

/-! ## The regularized response -/

/-- The regularized resolvent applied to a source split along the kernel. -/
theorem resolvent_apply_ground_split (A : H →ₗ[ℝ] H) {τ : ℝ} (hτ : τ ≠ 0)
    {v p q r : H} (hv : v = p + q) (hAp : A p = 0) (hr : A r + τ • r = q) :
    A (τ⁻¹ • p + r) + τ • (τ⁻¹ • p + r) = v := by
  have hsplit : A (τ⁻¹ • p + r) + τ • (τ⁻¹ • p + r) = p + (A r + τ • r) := by
    rw [map_add, map_smul, hAp, smul_zero, zero_add, smul_add, smul_smul,
      mul_inv_cancel₀ hτ, one_smul]
    abel
  rw [hsplit, hr, hv]

/-- **(HSC.25) The exact zero-edge decomposition.**  Against a source split along the kernel the
regularized response is the ground term `‖p‖²/τ` plus the reduced term. -/
theorem inner_resolvent_ground_split {τ : ℝ} (hτ : τ ≠ 0) {v p q r : H}
    (hv : v = p + q) (hpq : ⟪p, q⟫ = 0) (hpr : ⟪p, r⟫ = 0) :
    ⟪v, τ⁻¹ • p + r⟫ = ‖p‖ ^ (2 : ℕ) / τ + ⟪q, r⟫ := by
  have hqp : ⟪q, p⟫ = 0 := by rw [real_inner_comm]; exact hpq
  rw [hv, inner_add_left, inner_add_right, inner_add_right, real_inner_smul_right,
    real_inner_smul_right, real_inner_self_eq_norm_sq, hpr, hqp, add_zero, mul_zero, zero_add]
  field_simp

/-- **(HSC.26)-(HSC.27) The ground velocity is bounded below.**  A kernel vector pairing
nontrivially with the source velocity forces a positive ground component. -/
theorem norm_ge_inner_div_norm {p ξ : H} (hξ : ξ ≠ 0) : |⟪p, ξ⟫| / ‖ξ‖ ≤ ‖p‖ := by
  have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
  rw [div_le_iff₀ hn]
  exact abs_real_inner_le_norm p ξ

/-! ## The square-root profile -/

/-- The squared norm of a vanishing analytic family along a square-root path has the exact
quadratic profile of its velocity. -/
theorem tendsto_normSq_sqrt_path {G : ℝ → H} {G' : H} {κ₀ s : ℝ}
    (hG : HasDerivAt G G' κ₀) (h0 : G κ₀ = 0) :
    Tendsto (fun τ : ℝ => ‖G (κ₀ + s * Real.sqrt τ)‖ ^ (2 : ℕ) / τ) (𝓝[>] 0)
      (𝓝 (s ^ (2 : ℕ) * ‖G'‖ ^ (2 : ℕ))) := by
  rcases eq_or_ne s 0 with hs | hs
  · subst hs
    have hfun : ∀ τ : ℝ, ‖G (κ₀ + 0 * Real.sqrt τ)‖ ^ (2 : ℕ) / τ = 0 := by
      intro τ
      simp [h0]
    simp only [hfun]
    have hz : (0 : ℝ) ^ (2 : ℕ) * ‖G'‖ ^ (2 : ℕ) = 0 := by ring
    rw [hz]
    exact tendsto_const_nhds
  · have hslope : Tendsto (slope G κ₀) (𝓝[≠] κ₀) (𝓝 G') :=
      hasDerivAt_iff_tendsto_slope.1 hG
    have hpath : Tendsto (fun τ : ℝ => κ₀ + s * Real.sqrt τ) (𝓝[>] 0) (𝓝[≠] κ₀) := by
      refine tendsto_nhdsWithin_iff.2 ⟨?_, ?_⟩
      · have hc0 : Tendsto (fun τ : ℝ => Real.sqrt τ) (𝓝 0) (𝓝 (Real.sqrt 0)) :=
          Real.continuous_sqrt.tendsto 0
        rw [Real.sqrt_zero] at hc0
        have h1 : Tendsto (fun τ : ℝ => Real.sqrt τ) (𝓝[>] 0) (𝓝 0) :=
          hc0.mono_left nhdsWithin_le_nhds
        have h2 := (h1.const_mul s).const_add κ₀
        simpa using h2
      · filter_upwards [self_mem_nhdsWithin] with τ hτ
        have hsq : 0 < Real.sqrt τ := Real.sqrt_pos.2 hτ
        have : s * Real.sqrt τ ≠ 0 := mul_ne_zero hs (ne_of_gt hsq)
        simpa using this
    have hcomp : Tendsto (fun τ : ℝ => ‖slope G κ₀ (κ₀ + s * Real.sqrt τ)‖ ^ (2 : ℕ) * s ^ (2 : ℕ))
        (𝓝[>] 0) (𝓝 (s ^ (2 : ℕ) * ‖G'‖ ^ (2 : ℕ))) := by
      have h := (((hslope.comp hpath).norm).pow 2).mul_const (s ^ (2 : ℕ))
      have hval : ‖G'‖ ^ (2 : ℕ) * s ^ (2 : ℕ) = s ^ (2 : ℕ) * ‖G'‖ ^ (2 : ℕ) := by ring
      rw [hval] at h
      exact h
    have hval : ∀ τ : ℝ, 0 < τ →
        ‖slope G κ₀ (κ₀ + s * Real.sqrt τ)‖ ^ (2 : ℕ) * s ^ (2 : ℕ)
          = ‖G (κ₀ + s * Real.sqrt τ)‖ ^ (2 : ℕ) / τ := by
      intro τ hτ
      have hsq : Real.sqrt τ ^ (2 : ℕ) = τ := Real.sq_sqrt hτ.le
      have hne : s * Real.sqrt τ ≠ 0 :=
        mul_ne_zero hs (ne_of_gt (Real.sqrt_pos.2 hτ))
      have hslopeval : slope G κ₀ (κ₀ + s * Real.sqrt τ)
          = (s * Real.sqrt τ)⁻¹ • G (κ₀ + s * Real.sqrt τ) := by
        rw [slope_def_module, h0, sub_zero, add_sub_cancel_left]
      rw [hslopeval, norm_smul, norm_inv, Real.norm_eq_abs]
      rw [mul_pow, inv_pow, ← abs_pow, mul_pow, hsq]
      have hs2 : (0 : ℝ) < s ^ (2 : ℕ) := by positivity
      have habs : |s ^ (2 : ℕ) * τ| = s ^ (2 : ℕ) * τ := abs_of_pos (by positivity)
      rw [habs]
      field_simp
    refine hcomp.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact hval τ hτ

/-- **(HSC.28) The Lorentzian capacity spike.**  A ground component vanishing to first order and a
finite reduced response produce the exact square-root profile `ρ/(1 + ρ c s²)`. -/
theorem tendsto_capacity_spike {c ρ s : ℝ} (hρ : 0 < ρ) (hc : 0 ≤ c)
    {N E C : ℝ → ℝ} (hC : ∀ τ, 0 < τ → C τ = (N τ / τ + E τ)⁻¹)
    (hN : Tendsto (fun τ => N τ / τ) (𝓝[>] 0) (𝓝 (c * s ^ (2 : ℕ))))
    (hE : Tendsto E (𝓝[>] 0) (𝓝 ρ⁻¹)) :
    Tendsto C (𝓝[>] 0) (𝓝 (ρ / (1 + ρ * c * s ^ (2 : ℕ)))) := by
  have hden : (0 : ℝ) < c * s ^ (2 : ℕ) + ρ⁻¹ := by positivity
  have hlim : Tendsto (fun τ => (N τ / τ + E τ)⁻¹) (𝓝[>] 0) (𝓝 (c * s ^ (2 : ℕ) + ρ⁻¹)⁻¹) :=
    (hN.add hE).inv₀ (ne_of_gt hden)
  have hval : (c * s ^ (2 : ℕ) + ρ⁻¹)⁻¹ = ρ / (1 + ρ * c * s ^ (2 : ℕ)) := by
    field_simp
    ring
  rw [← hval]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  exact (hC τ hτ).symm

/-- **(HSC.29) The linear collapse.**  A source with nonzero ground component has regularized
capacity of exact order `τ`. -/
theorem tendsto_capacity_ratio {p2 L : ℝ} (hp2 : 0 < p2)
    {E C : ℝ → ℝ} (hC : ∀ τ, 0 < τ → C τ = (p2 / τ + E τ)⁻¹)
    (hE : Tendsto E (𝓝[>] 0) (𝓝 L)) :
    Tendsto (fun τ => C τ / τ) (𝓝[>] 0) (𝓝 (1 / p2)) := by
  have hτ0 : Tendsto (fun τ : ℝ => τ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hlim : Tendsto (fun τ => (p2 + τ * E τ)⁻¹) (𝓝[>] 0) (𝓝 (p2 + 0 * L)⁻¹) :=
    (tendsto_const_nhds.add (hτ0.mul hE)).inv₀ (by simpa using ne_of_gt hp2)
  have hval : (p2 + 0 * L)⁻¹ = 1 / p2 := by
    rw [zero_mul, add_zero, one_div]
  rw [← hval]
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  have hτ' : (0 : ℝ) < τ := hτ
  have hτne : τ ≠ 0 := ne_of_gt hτ'
  have h1 : p2 / τ + E τ = (p2 + τ * E τ) / τ := by field_simp
  rw [hC τ hτ', h1, inv_div, div_div, mul_comm (p2 + τ * E τ) τ, ← div_div, div_self hτne,
    one_div]

/-- **(HSC.22) The ground pole.**  A source with nonzero ground component has a zero-edge response
diverging to infinity. -/
theorem tendsto_atTop_groundResponse {p2 : ℝ} (hp2 : 0 < p2)
    {E M : ℝ → ℝ} (hM : ∀ τ, 0 < τ → M τ = p2 / τ + E τ) (hE : ∀ τ, 0 < τ → 0 ≤ E τ) :
    Tendsto M (𝓝[>] 0) atTop := by
  have hbase : Tendsto (fun τ : ℝ => p2 / τ) (𝓝[>] 0) atTop := by
    have hinv : Tendsto (fun τ : ℝ => τ⁻¹) (𝓝[>] 0) atTop := tendsto_inv_nhdsGT_zero
    have := hinv.const_mul_atTop hp2
    simpa [div_eq_mul_inv] using this
  refine tendsto_atTop_mono' _ ?_ hbase
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  rw [hM τ hτ]
  linarith [hE τ hτ]

/-- **(HSC.22) A ground source has nonzero ground component.**  A kernel vector with unit pairing
against the source forces a nonzero ground projection of the source. -/
theorem ground_ne_zero_of_unit_pairing {v p q ζ : H} (hv : v = p + q)
    (hζ : ⟪q, ζ⟫ = 0) (hnorm : ⟪v, ζ⟫ = 1) : p ≠ 0 := by
  intro h
  rw [hv, h, zero_add, hζ] at hnorm
  exact absurd hnorm (by norm_num)

/-- **(HSC.28) The capacity spike from a vanishing ground family.**  If the ground component of the
moving source vanishes at `κ₀` with velocity `G'`, and the reduced response converges to `ρ⁻¹`, the
regularized capacity along the square-root path has the Lorentzian profile. -/
theorem tendsto_capacity_spike_of_vanishing_ground {G : ℝ → H} {G' : H} {κ₀ s ρ : ℝ}
    (hG : HasDerivAt G G' κ₀) (h0 : G κ₀ = 0) (hρ : 0 < ρ) {E C : ℝ → ℝ}
    (hC : ∀ τ, 0 < τ → C τ = (‖G (κ₀ + s * Real.sqrt τ)‖ ^ (2 : ℕ) / τ + E τ)⁻¹)
    (hE : Tendsto E (𝓝[>] 0) (𝓝 ρ⁻¹)) :
    Tendsto C (𝓝[>] 0) (𝓝 (ρ / (1 + ρ * ‖G'‖ ^ (2 : ℕ) * s ^ (2 : ℕ)))) := by
  refine tendsto_capacity_spike (c := ‖G'‖ ^ (2 : ℕ)) (N := fun τ => ‖G (κ₀ + s * Real.sqrt τ)‖ ^ (2 : ℕ))
    hρ (by positivity) hC ?_ hE
  have h := tendsto_normSq_sqrt_path (G := G) (G' := G') (κ₀ := κ₀) (s := s) hG h0
  have hval : s ^ (2 : ℕ) * ‖G'‖ ^ (2 : ℕ) = ‖G'‖ ^ (2 : ℕ) * s ^ (2 : ℕ) := by ring
  rw [hval] at h
  exact h

end GaloisForLFunctions.HTGeometry

end
