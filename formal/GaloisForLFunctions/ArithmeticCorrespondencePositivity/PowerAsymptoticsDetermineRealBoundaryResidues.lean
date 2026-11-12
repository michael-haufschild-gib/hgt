import GaloisForLFunctions.ArithmeticCorrespondencePositivity.PowerAsymptoticsHaveNoNonrealBoundaryResidues

/-!
# A summatory power asymptotic determines its real boundary residue

The resonant Abelian theorem reads the limit of the logarithmic staircase.
Multiplication by the Mellin variable restores the residue `θL` of the
summatory Mellin pairing at its real power boundary.
-/

noncomputable section

open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.ArithmeticCorrespondencePositivity

open TransHorizonIncidenceMechanics (complexMellinPairing)
open SelbergClass.DegreeOne

/-- A leading summatory coefficient `L` at power `θ` gives real Mellin
residue `θL`. -/
theorem tendsto_mul_complexMellinPairing_at_real_boundary
    {f : ℕ → ℝ} (hf0 : f 0 = 0) {θ L : ℝ} (hθ : 0 ≤ θ)
    (hf : Tendsto (fun N : ℕ => (N : ℝ) ^ (-θ) * f N) atTop (𝓝 L)) :
    Tendsto (fun ε : ℝ => (ε : ℂ) * complexMellinPairing f ((θ + ε : ℝ) : ℂ))
      (𝓝[>] 0) (𝓝 ((θ : ℂ) * (L : ℂ))) := by
  obtain ⟨C, hC, hbound⟩ := exists_power_bound_of_normalized_tendsto hf0 hf
  let r := stepLaplaceIntegrand f (θ : ℂ)
  have hr : AEStronglyMeasurable r (volume.restrict (Ioi 0)) :=
    (measurable_stepLaplaceIntegrand f (θ : ℂ)).aestronglyMeasurable
  have hb : ∀ u, 0 < u → ‖r u‖ ≤ C := by
    intro u _
    rw [norm_stepLaplaceIntegrand, ofReal_re]
    have hn := Real.rpow_le_rpow (Nat.cast_nonneg ⌊Real.exp u⌋₊)
      (Nat.floor_le (Real.exp_pos u).le) hθ
    have hh := mul_le_mul_of_nonneg_left ((hbound _).trans
      (mul_le_mul_of_nonneg_left hn hC)) (Real.exp_pos (-(θ * u))).le
    have he : Real.exp (-(θ * u)) * (C * (Real.exp u) ^ θ) = C := by
      rw [Real.rpow_def_of_pos (Real.exp_pos u), Real.log_exp, mul_left_comm,
        ← Real.exp_add, show -(θ * u) + u * θ = 0 by ring, Real.exp_zero, mul_one]
    exact hh.trans_eq he
  have hlim := tendsto_stepLaplaceIntegrand_of_power_asymptotic hf
  have heps : Tendsto (fun ε : ℝ => ε) (𝓝[>] 0) (𝓝 0) := nhdsWithin_le_nhds
  have hab := tendsto_abelIntegral_resonant hr hb hlim 0
    (show ∀ᶠ ε : ℝ in 𝓝[>] 0, 0 < ε from self_mem_nhdsWithin)
    heps (τ := fun _ : ℝ => 0) (by simpa only [zero_div] using
      (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : ℝ)) (𝓝[>] 0) (𝓝 0)))
  simp only [abelExponent, ofReal_zero, mul_zero, sub_zero, Complex.cpow_one,
    zero_mul, add_zero, Complex.Gamma_one, mul_one] at hab
  have hs : Tendsto (fun ε : ℝ => ((θ + ε : ℝ) : ℂ)) (𝓝[>] 0) (𝓝 (θ : ℂ)) := by
    have hh := Complex.continuous_ofReal.continuousAt.tendsto.comp (heps.const_add θ)
    rw [add_zero] at hh
    exact hh.congr fun _ => rfl
  apply (hs.mul hab).congr'
  filter_upwards [self_mem_nhdsWithin] with ε hε
  have hε0 : 0 < ε := hε
  let s : ℂ := ((θ + ε : ℝ) : ℂ)
  have hsre : s.re = θ + ε := Complex.ofReal_re _
  have hs0 : 0 < s.re := by rw [hsre]; linarith only [hθ, hε0]
  have hsum := summable_mellin_majorant_of_power_bound hf0 hbound
    (show θ < s.re by rw [hsre]; linarith only [hε0])
  have hi : abelIntegral r 0 (ε : ℂ) = complexMellinPairing f s / s := by
    have he : (fun u => r u * abelKernel 0 (ε : ℂ) u) = stepLaplaceIntegrand f s := by
      funext u
      simp only [r, stepLaplaceIntegrand, abelKernel, ofReal_zero, mul_zero, neg_zero,
        Complex.cpow_zero, one_mul]
      rw [mul_right_comm, ← Complex.exp_add]
      congr 2
      dsimp only [s]
      push_cast
      ring
    rw [abelIntegral, he, ← integral_Ici_eq_integral_Ioi]
    calc
      _ = ∫ u, stepLaplaceIntegrand f s u := by
        rw [setIntegral_eq_integral_of_forall_compl_eq_zero]
        intro u hu
        exact stepLaplaceIntegrand_of_neg hf0 s (not_le.mp hu)
      _ = _ := integral_stepLaplaceIntegrand hf0 hs0 hsum
  rw [hi]
  have hsne : s ≠ 0 := fun h => by rw [h, zero_re] at hs0; exact lt_irrefl 0 hs0
  change s * ((ε : ℂ) * (complexMellinPairing f s / s)) =
    (ε : ℂ) * complexMellinPairing f s
  field_simp [hsne]

end GaloisForLFunctions.ArithmeticCorrespondencePositivity
