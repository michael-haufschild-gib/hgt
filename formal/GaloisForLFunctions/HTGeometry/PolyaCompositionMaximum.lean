import GaloisForLFunctions.HTGeometry.BohrCoveringCircle

/-!
# Pólya's composition-growth theorem

**Pólya (1926), Theorem II.**  There is an absolute constant `c > 0` such that for entire `g` and
`h` with `h 0 = 0`,

```text
M(r, g ∘ h) ≥ M(c · M(r/2, h), g).
```

The proof is exactly Pólya's: Bohr's circle-covering theorem applied to `φ(ζ) = h(rζ)/H` makes the
image of `‖z‖ < r` under `h` contain a whole circle `‖u‖ = H t` with `t ≥ C`, and the maximum
modulus of `g` on the disc `‖v‖ ≤ H t` is attained on that circle.

* `exists_sphere_max` — the maximum modulus of an entire function on a closed disc is attained on
  the boundary circle.
* `exists_polya_constant` — the composition-growth inequality in pointwise form.
-/

namespace GaloisForLFunctions.HTGeometry

open Bottcher Complex Metric Set

noncomputable section

/-- **The maximum modulus over a closed disc is attained on its boundary circle.** -/
theorem exists_sphere_max {g : ℂ → ℂ} (hg : Differentiable ℂ g) {R : ℝ} (hR : 0 < R) :
    ∃ u₀ : ℂ, ‖u₀‖ = R ∧ ∀ v : ℂ, ‖v‖ ≤ R → ‖g v‖ ≤ ‖g u₀‖ := by
  have hne : (sphere (0 : ℂ) R).Nonempty := NormedSpace.sphere_nonempty.mpr hR.le
  obtain ⟨u₀, hu₀mem, hu₀max⟩ :=
    (isCompact_sphere (0 : ℂ) R).exists_isMaxOn hne (hg.continuous.norm.continuousOn)
  refine ⟨u₀, by simpa [mem_sphere_iff_norm] using hu₀mem, ?_⟩
  intro v hv
  have hbdd : Bornology.IsBounded (ball (0 : ℂ) R) := isBounded_ball
  have hdc : DiffContOnCl ℂ g (ball (0 : ℂ) R) := hg.diffContOnCl
  have hfr : ∀ z ∈ frontier (ball (0 : ℂ) R), ‖g z‖ ≤ ‖g u₀‖ := by
    intro z hz
    rw [frontier_ball 0 hR.ne'] at hz
    exact hu₀max hz
  have hvcl : v ∈ closure (ball (0 : ℂ) R) := by
    rw [closure_ball 0 hR.ne']
    simpa [mem_closedBall, dist_zero_right] using hv
  exact norm_le_of_forall_mem_frontier_norm_le hbdd hdc hfr hvcl

/-- **Pólya's composition-growth theorem.**  With `c` the constant from Bohr's covering theorem at
`ρ = 1/2`: if the entire `h` with `h 0 = 0` reaches modulus `H` somewhere on `‖z‖ ≤ r/2`, then
`g ∘ h` attains, at some point of `‖z‖ < r`, a modulus at least as large as every value of `g` on
the disc `‖v‖ ≤ c·H`. -/
theorem exists_polya_constant :
    ∃ c : ℝ, 0 < c ∧ ∀ g h : ℂ → ℂ, Differentiable ℂ g → Differentiable ℂ h → h 0 = 0 →
      ∀ r H : ℝ, 0 < r → 0 < H → (∃ z₀ : ℂ, ‖z₀‖ ≤ r / 2 ∧ H ≤ ‖h z₀‖) →
      ∃ z : ℂ, ‖z‖ < r ∧ ∀ v : ℂ, ‖v‖ ≤ c * H → ‖g v‖ ≤ ‖g (h z)‖ := by
  obtain ⟨C, hC0, hBohr⟩ := exists_covered_circle (ρ := 1 / 2) (by norm_num) (by norm_num)
  refine ⟨C, hC0, ?_⟩
  rintro g h hg hh hh0 r H hr hH ⟨z₀, hz₀, hz₀H⟩
  have hrC : (r : ℂ) ≠ 0 := by
    simpa using ne_of_gt hr
  have hHC : (H : ℂ) ≠ 0 := by
    simpa using ne_of_gt hH
  set φ : ℂ → ℂ := fun ζ => h ((r : ℂ) * ζ) / (H : ℂ) with hφdef
  have hφdiffAll : Differentiable ℂ φ := by
    rw [hφdef]
    exact (hh.comp (differentiable_id.const_mul (r : ℂ))).div_const _
  have hφdiff : DifferentiableOn ℂ φ (ball (0 : ℂ) 1) := hφdiffAll.differentiableOn
  have hφ0 : φ 0 = 0 := by
    rw [hφdef]
    simp [hh0]
  have hφ1 : ∃ ζ₁ : ℂ, ‖ζ₁‖ ≤ 1 / 2 ∧ 1 ≤ ‖φ ζ₁‖ := by
    refine ⟨z₀ / (r : ℂ), ?_, ?_⟩
    · rw [norm_div]
      have hrn : ‖(r : ℂ)‖ = r := by simpa using abs_of_pos hr
      rw [hrn, div_le_iff₀ hr]
      linarith
    · have hmul : (r : ℂ) * (z₀ / (r : ℂ)) = z₀ := by field_simp
      rw [hφdef]
      simp only [hmul, norm_div]
      have hHn : ‖(H : ℂ)‖ = H := by simpa using abs_of_pos hH
      rw [hHn, le_div_iff₀ hH]
      linarith
  obtain ⟨t, htC, htcov⟩ := hBohr φ hφdiff hφ0 hφ1
  have htpos : 0 < t := lt_of_lt_of_le hC0 htC
  have hHt : 0 < H * t := by positivity
  obtain ⟨u₀, hu₀n, hu₀max⟩ := exists_sphere_max hg hHt
  have hquot : ‖u₀ / (H : ℂ)‖ = t := by
    rw [norm_div, hu₀n]
    have hHn : ‖(H : ℂ)‖ = H := by simpa using abs_of_pos hH
    rw [hHn]
    field_simp
  obtain ⟨ζ, hζ, hζval⟩ := htcov (u₀ / (H : ℂ)) hquot
  refine ⟨(r : ℂ) * ζ, ?_, ?_⟩
  · rw [norm_mul]
    have hrn : ‖(r : ℂ)‖ = r := by simpa using abs_of_pos hr
    rw [hrn]
    calc r * ‖ζ‖ < r * 1 := by exact mul_lt_mul_of_pos_left hζ hr
      _ = r := mul_one r
  · have hhz : h ((r : ℂ) * ζ) = u₀ := by
      have := hζval
      rw [hφdef] at this
      field_simp at this
      exact this
    rw [hhz]
    intro v hv
    refine hu₀max v ?_
    calc ‖v‖ ≤ C * H := hv
      _ ≤ t * H := by exact mul_le_mul_of_nonneg_right htC hH.le
      _ = H * t := by ring

end

end GaloisForLFunctions.HTGeometry
