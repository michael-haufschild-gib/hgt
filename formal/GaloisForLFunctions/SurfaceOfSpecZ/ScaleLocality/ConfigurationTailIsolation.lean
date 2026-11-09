import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.PositiveTailIsolation
import GaloisForLFunctions.SurfaceOfSpecZ.ThePrimesSampleEveryTopLayer
import GaloisForLFunctions.SquareRootThreshold.FiniteLagWindowRecordPotentialLaw
import GaloisForLFunctions.ZeroConfigurationGeometry.TheCompactCoordinatesOfTemperedConfigurations

/-!
# Positive tail deletion for tempered configurations

Inverse-square ordinate summability makes positive deletion arbitrarily
cheap. A prescribed exponent survives while all but finitely many spline
modes vanish. Conjugate modes share the same real positive filter.
-/

open Complex Filter Topology
open scoped ComplexConjugate
open GaloisForLFunctions.SquareRootThreshold Zeta23
open GaloisForLFunctions.ZeroConfigurationGeometry.CompactCoordinates
noncomputable section
namespace GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality

/-- Positive tail deletion preserves any specified exponent at arbitrarily small square cost. -/
theorem exists_configuration_tail_deletion (Z : ZeroConfig) (hZ : TemperedConfig Z)
    (hnoreal : ∀ ρ ∈ Z.carrier, ρ.im ≠ 0) (α : ℝ) (w₀ : ℂ) {ε : ℝ} (hε : 0 < ε) :
    ∃ (a h : ℕ → ℝ) (S : Finset ℂ),
      Summable (fun n => h n ^ 2) ∧ (∑' n, h n ^ 2) < ε ∧
      (∏' n, quartetFactor (a n) (h n) w₀) ≠ 0 ∧
      ∀ z ∉ S, evenCoeff Z (boxSpline 1 3) z ≠ 0 →
        (∏' n, quartetFactor (a n) (h n) (z - (α : ℂ))) = 0 := by
  classical
  let p := encoding Z
  let a : ℕ → ℝ := fun n => ((p n).1 : ℝ) - 1 / 2 - α
  let h : ℕ → ℝ := fun n => Real.pi * (p n).2
  let z : ℕ → ℂ := fun n => ⟨((p n).1 : ℝ) - 1 / 2, (p n).2⁻¹⟩
  have hsq : Summable fun n => h n ^ 2 := by
    have hs := (hasSum_encoding_sq Z hZ hnoreal).summable.mul_left (Real.pi ^ 2)
    apply hs.congr
    intro n
    dsimp only [h, p]
    ring
  obtain ⟨N, hcost, hkeep⟩ := exists_small_nonzero_tail_multiplier a h hsq w₀ hε
  let S₀ : Finset ℂ := (Finset.range N).image z
  let S : Finset ℂ := S₀ ∪ S₀.image conj
  let a' : ℕ → ℝ := fun n => a (n + N)
  let h' : ℕ → ℝ := fun n => h (n + N)
  have hsq' : Summable fun n => h' n ^ 2 := (summable_nat_add_iff N).mpr hsq
  have hkill : ∀ ρ ∈ Z.carrier, ρ - 1 / 2 ∉ S₀ →
      (∏' n, quartetFactor (a' n) (h' n) (ρ - 1 / 2 - (α : ℂ))) = 0 := by
    intro ρ hρ hout
    let i : Copy Z := ⟨⟨ρ, hρ⟩, ⟨0, Z.one_le_mult ρ hρ⟩⟩
    let k := label Z i
    have hp : p k = (⟨ρ.re, Z.strip ρ hρ⟩, ρ.im⁻¹) :=
      encoding_label Z hZ hnoreal i
    have hzk : z k = ρ - 1 / 2 := by
      apply Complex.ext <;> simp [z, hp]
    have hNk : N ≤ k := by
      by_contra hNk
      exact hout (Finset.mem_image.mpr ⟨k,
        Finset.mem_range.mpr (lt_of_not_ge hNk), hzk⟩)
    have ha : a' (k - N) = (ρ - 1 / 2 - (α : ℂ)).re := by
      simp only [a', Nat.sub_add_cancel hNk, a, hp, Complex.sub_re, Complex.ofReal_re]
      norm_num
    have hh : h' (k - N) * (ρ - 1 / 2 - (α : ℂ)).im = Real.pi := by
      simp only [h', Nat.sub_add_cancel hNk, h, hp, Complex.sub_im, Complex.ofReal_im]
      norm_num only [Complex.div_ofNat_im, Complex.one_im, zero_div, sub_zero]
      rw [mul_assoc, inv_mul_cancel₀ (hnoreal ρ hρ), mul_one]
    have he : (a' (k - N) : ℂ) + ((ρ - 1 / 2 - (α : ℂ)).im : ℂ) * I =
        ρ - 1 / 2 - (α : ℂ) := by rw [ha, Complex.re_add_im]
    have hk := tprod_quartetFactor_root a' h' hsq' (k - N) hh
    rwa [he] at hk
  refine ⟨a', h', S, hsq', hcost, hkeep, ?_⟩
  intro w hw hcw
  rcases mem_of_evenCoeff_ne_zero hcw with hw₁ | hw₂
  · have hout : (1 / 2 : ℂ) + w - 1 / 2 ∉ S₀ := by
      intro hm
      apply hw
      apply Finset.mem_union_left
      convert hm using 1 <;> ring
    have hh := hkill _ hw₁ hout
    have he : (1 / 2 : ℂ) + w - 1 / 2 - (α : ℂ) = w - (α : ℂ) := by ring
    rwa [he] at hh
  · have hout : (1 / 2 : ℂ) + conj w - 1 / 2 ∉ S₀ := by
      intro hm
      apply hw
      apply Finset.mem_union_right
      apply Finset.mem_image.mpr
      refine ⟨conj w, ?_, Complex.conj_conj w⟩
      convert hm using 1 <;> ring
    have hh := hkill _ hw₂ hout
    have he : (1 / 2 : ℂ) + conj w - 1 / 2 - (α : ℂ) = conj (w - (α : ℂ)) := by
      simp only [map_sub, Complex.conj_ofReal]
      ring
    rw [he, tprod_quartetFactor_conj a' h' hsq'] at hh
    simpa only [Complex.conj_conj, map_zero] using congrArg conj hh

theorem configuration_shifted_exponent_bound {Z : ZeroConfig} (α : ℝ) {z : ℂ}
    (hz : evenCoeff Z (boxSpline 1 3) z ≠ 0) :
    |(z - (α : ℂ)).re| ≤ 1 / 2 + |α| := by
  have htri : |z.re - α| ≤ |z.re| + |α| := by
    simpa only [Real.norm_eq_abs] using norm_sub_le z.re α
  exact htri.trans (add_le_add (abs_re_le_of_evenCoeff_ne_zero hz) le_rfl)

/-- Real shifts preserve the absolutely convergent spline expansion. -/
theorem configuration_shifted_trace_series {Z : ZeroConfig} (hZ : TemperedConfig Z) (α t : ℝ) :
    Real.exp (-α * t) * (2 * (lagStructure Z (boxSpline 1 3) t).re) =
      ∑' z : ℂ, (evenCoeff Z (boxSpline 1 3) z *
        Complex.exp ((z - (α : ℂ)) * t)).re := by
  have he := ofReal_normTrace (b := α) hZ t
  have hs : Summable fun z : ℂ => evenCoeff Z (boxSpline 1 3) z *
      Complex.exp ((z - (α : ℂ)) * t) := by
    apply Summable.of_norm_bounded
      ((summable_norm_evenCoeff_spline hZ).mul_right
        (Real.exp ((1 / 2 + |α|) * |t|)))
    intro z
    by_cases hz : evenCoeff Z (boxSpline 1 3) z = 0
    · simp [hz]
    rw [norm_mul, Complex.norm_exp]
    apply mul_le_mul_of_nonneg_left _ (norm_nonneg _)
    apply Real.exp_le_exp.mpr
    simp only [Complex.mul_re, Complex.sub_re, Complex.ofReal_re,
      Complex.sub_im, Complex.ofReal_im, sub_zero, mul_zero]
    have hw : |z.re - α| ≤ 1 / 2 + |α| := configuration_shifted_exponent_bound α hz
    exact (le_abs_self ((z.re - α) * t)).trans
      (by rw [abs_mul]; exact mul_le_mul_of_nonneg_right hw (abs_nonneg _))
  have hre := congrArg Complex.re he
  rw [show (∑' z : ℂ, evenCoeff Z (boxSpline 1 3) z *
      Complex.exp ((z - (α : ℂ)) * t)).re =
      ∑' z : ℂ, (evenCoeff Z (boxSpline 1 3) z *
        Complex.exp ((z - (α : ℂ)) * t)).re from Complex.reCLM.map_tsum hs] at hre
  simp only [Complex.ofReal_re] at hre
  rw [neg_mul, mul_comm]
  exact hre

#print axioms exists_configuration_tail_deletion
#print axioms configuration_shifted_trace_series

end GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality
