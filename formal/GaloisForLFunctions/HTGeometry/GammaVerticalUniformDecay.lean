import GaloisForLFunctions.HTGeometry.GammaVerticalModulus
import GaloisForLFunctions.HTGeometry.PolygammaUniformLeadingAsymptotic
import Mathlib.Analysis.SpecialFunctions.Gamma.BohrMollerup

/-!
# Gamma decays faster than every power, uniformly on a vertical tube

The corpus proves `t^N·Γ(σ+it) → 0` on each vertical line through the Fourier transform, a statement
that fixes the line.  For the tube form of the projective boundary law the decay must be uniform in
the abscissa, and two facts the corpus already owns give that directly:

* `norm_Gamma_le_Gamma_re` — the modulus is bounded by the real Gamma of the abscissa;
* `norm_Gamma_add_nat` — the functional equation in modulus form,
  `‖Γ(z+m)‖ = (∏_{i<m}‖z+i‖)·‖Γ(z)‖`.

On a vertical line every factor `‖z+i‖` is at least the ordinate, so shifting `k+2` steps to the right
costs `t^{k+2}`, and the shifted abscissa lies where the real Gamma is monotone.  One constant then
serves every abscissa in the tube.
-/

open Filter Set Topology Function

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

noncomputable section

/-- **Gamma decays faster than every power, uniformly on a vertical tube.**  One constant serves
every abscissa `0 < σ ≤ M`. -/
theorem exists_uniform_bound_norm_Gamma_vertical {M : ℝ} (hM : 0 < M) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ σ t : ℝ, 0 < σ → σ ≤ M → 1 ≤ t →
      ‖Complex.Gamma ((σ : ℂ) + (t : ℂ) * Complex.I)‖ ≤ C / t ^ k := by
  classical
  set m : ℕ := k + 2 with hm
  refine ⟨Real.Gamma (M + m), le_of_lt (Real.Gamma_pos_of_pos (by positivity)), ?_⟩
  intro σ t hσ hσM ht
  have htpos : (0 : ℝ) < t := lt_of_lt_of_le zero_lt_one ht
  set z : ℂ := (σ : ℂ) + (t : ℂ) * Complex.I with hz
  have him : ∀ i : ℕ, (z + (i : ℂ)).im = t := by
    intro i
    rw [hz]
    simp
  have hne : ∀ i : ℕ, i < m → z + (i : ℂ) ≠ 0 := by
    intro i _ h0
    have hi := him i
    rw [h0] at hi
    simp only [Complex.zero_im] at hi
    linarith
  -- the functional equation in modulus form
  have hprod := norm_Gamma_add_nat z m hne
  have hfac : ∀ i ∈ Finset.range m, t ≤ ‖z + (i : ℂ)‖ := by
    intro i _
    calc t = (z + (i : ℂ)).im := (him i).symm
      _ ≤ ‖z + (i : ℂ)‖ := Complex.im_le_norm _
  have hprodge : t ^ m ≤ ∏ i ∈ Finset.range m, ‖z + (i : ℂ)‖ := by
    calc t ^ m = ∏ _i ∈ Finset.range m, t := by
          rw [Finset.prod_const, Finset.card_range]
      _ ≤ ∏ i ∈ Finset.range m, ‖z + (i : ℂ)‖ :=
          Finset.prod_le_prod (fun i _ => le_of_lt htpos) hfac
  -- the shifted modulus is bounded by the real Gamma of the shifted abscissa
  have hre : (z + (m : ℂ)).re = σ + m := by
    rw [hz]
    simp
  have hrepos : (0 : ℝ) < (z + (m : ℂ)).re := by
    rw [hre]
    positivity
  have hshift : ‖Complex.Gamma (z + (m : ℂ))‖ ≤ Real.Gamma (σ + m) := by
    have := norm_Gamma_le_Gamma_re hrepos
    rwa [hre] at this
  have hmono : Real.Gamma (σ + m) ≤ Real.Gamma (M + m) := by
    rcases eq_or_lt_of_le hσM with hEq | hlt
    · rw [hEq]
    · refine le_of_lt (Real.Gamma_strictMonoOn_Ici ?_ ?_ (by linarith))
      · show (2 : ℝ) ≤ σ + m
        rw [hm]
        push_cast
        linarith
      · show (2 : ℝ) ≤ M + m
        rw [hm]
        push_cast
        linarith
  -- solve for the modulus at the original point
  have hval : ‖Complex.Gamma z‖ * t ^ m ≤ Real.Gamma (M + m) := by
    calc ‖Complex.Gamma z‖ * t ^ m
        ≤ ‖Complex.Gamma z‖ * ∏ i ∈ Finset.range m, ‖z + (i : ℂ)‖ :=
          mul_le_mul_of_nonneg_left hprodge (norm_nonneg _)
      _ = ‖Complex.Gamma (z + (m : ℂ))‖ := by rw [hprod]; ring
      _ ≤ Real.Gamma (M + m) := le_trans hshift hmono
  have hpow : t ^ k ≤ t ^ m := pow_le_pow_right₀ ht (by omega)
  rw [le_div_iff₀ (by positivity)]
  calc ‖Complex.Gamma z‖ * t ^ k ≤ ‖Complex.Gamma z‖ * t ^ m :=
        mul_le_mul_of_nonneg_left hpow (norm_nonneg _)
    _ ≤ Real.Gamma (M + m) := hval

end

end GaloisForLFunctions.HTGeometry
