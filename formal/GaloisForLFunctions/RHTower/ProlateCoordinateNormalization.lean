import GaloisForLFunctions.RHTower.ProlateGroundProfileIntegral
import GaloisForLFunctions.HTGeometry.ShapeRatioDilation

/-!
# The ground coordinate in the eigenfunction's own normalisation

The profile limit is stated for the rescaled, amplitude-normalised profile

```text
Ψ_c(ξ) = Φ_c(ξ / √c) / Φ_c(0) ,
```

whose shape ratio over the growing window `[-√c, √c]` tends to `2√π`.  The shape ratio is
insensitive to the amplitude and picks up exactly one factor of the dilation, so the same limit read
in the eigenfunction's own variable on its own interval `[-1,1]` is

```text
√c · ( ∫_{-1}^{1} Φ_c )² / ∫_{-1}^{1} Φ_c²  ⟶  2√π .
```

The amplitude `Φ_c(0)` cannot vanish for large bandwidth: if it did, the normalised profile would be
identically zero and its shape ratio would be `0`, contradicting a nonzero limit.  So the transfer
needs no positivity input beyond the limit itself.
-/

noncomputable section

open Filter Topology MeasureTheory

namespace GaloisForLFunctions.RHTower

open _root_.RHTower

/-- **The ground coordinate limit in the eigenfunction's own normalisation.** -/
theorem tendsto_sqrt_mul_prolateGround_coordSq :
    ∃ Psi : ℝ → ℝ → ℝ,
      (∀ c : ℝ, 0 < c → ∃ lam chi : ℝ, lam ≠ 0 ∧
        ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Psi c) ∧ Psi c ≠ 0 ∧ Function.Even (Psi c) ∧
        (∀ x : ℝ, bandTransform c (Psi c) x = lam * Psi c x) ∧
        (∀ x : ℝ, prolateSLAction c (Psi c) x = chi * Psi c x)) ∧
      Tendsto (fun c : ℝ => Real.sqrt c *
          ((∫ u in (-1 : ℝ)..1, Psi c u) ^ (2 : ℕ) / ∫ u in (-1 : ℝ)..1, (Psi c u) ^ (2 : ℕ)))
        atTop (𝓝 (2 * Real.sqrt Real.pi)) := by
  obtain ⟨Psi, hfam, hlim⟩ := tendsto_prolateGround_shapeRatio
  refine ⟨Psi, hfam, ?_⟩
  have hlimne : (2 * Real.sqrt Real.pi) ≠ 0 := by
    have : 0 < Real.sqrt Real.pi := Real.sqrt_pos.2 Real.pi_pos
    positivity
  have hzero : ∀ c : ℝ, Psi c 0 = 0 →
      ((∫ xi in (-Real.sqrt c)..(Real.sqrt c), normalizedProlateProfile c (Psi c) xi) ^ (2 : ℕ)
        / ∫ xi in (-Real.sqrt c)..(Real.sqrt c),
          (normalizedProlateProfile c (Psi c) xi) ^ (2 : ℕ)) = 0 := by
    intro c hc
    have hprof : ∀ xi : ℝ, normalizedProlateProfile c (Psi c) xi = 0 := by
      intro xi
      rw [normalizedProlateProfile, hc, div_zero]
    simp [hprof]
  have hratne : ∀ᶠ c : ℝ in atTop,
      ((∫ xi in (-Real.sqrt c)..(Real.sqrt c), normalizedProlateProfile c (Psi c) xi) ^ (2 : ℕ)
        / ∫ xi in (-Real.sqrt c)..(Real.sqrt c),
          (normalizedProlateProfile c (Psi c) xi) ^ (2 : ℕ)) ≠ 0 :=
    hlim.eventually_ne hlimne
  refine hlim.congr' ?_
  filter_upwards [hratne, eventually_gt_atTop (0 : ℝ)] with c hcne hcpos
  have hsq : 0 < Real.sqrt c := Real.sqrt_pos.2 hcpos
  have hamp : Psi c 0 ≠ 0 := by
    intro h
    exact hcne (hzero c h)
  have hprof : ∀ xi : ℝ,
      normalizedProlateProfile c (Psi c) xi = (Psi c 0)⁻¹ * Psi c (xi / Real.sqrt c) := by
    intro xi
    rw [normalizedProlateProfile, prolateHermiteRescale, div_eq_inv_mul]
  have hdil := HTGeometry.shapeRatio_dilate (Psi c) (α := Real.sqrt c)
    (β := (Psi c 0)⁻¹) (ne_of_gt hsq) (inv_ne_zero hamp) 1
  rw [mul_one] at hdil
  calc ((∫ xi in (-Real.sqrt c)..(Real.sqrt c), normalizedProlateProfile c (Psi c) xi) ^ (2 : ℕ)
        / ∫ xi in (-Real.sqrt c)..(Real.sqrt c),
          (normalizedProlateProfile c (Psi c) xi) ^ (2 : ℕ))
      = ((∫ xi in (-Real.sqrt c)..(Real.sqrt c),
            (Psi c 0)⁻¹ * Psi c (xi / Real.sqrt c)) ^ (2 : ℕ)
          / ∫ xi in (-Real.sqrt c)..(Real.sqrt c),
            ((Psi c 0)⁻¹ * Psi c (xi / Real.sqrt c)) ^ (2 : ℕ)) := by
        simp only [hprof]
    _ = Real.sqrt c * ((∫ u in (-1 : ℝ)..1, Psi c u) ^ (2 : ℕ)
          / ∫ u in (-1 : ℝ)..1, (Psi c u) ^ (2 : ℕ)) := hdil

end GaloisForLFunctions.RHTower

end
