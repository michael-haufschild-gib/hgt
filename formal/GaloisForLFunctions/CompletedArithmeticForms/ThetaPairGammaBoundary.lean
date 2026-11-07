import GaloisForLFunctions.CompletedArithmeticForms.BesselGammaAsymptotic
import GaloisForLFunctions.CompletedArithmeticForms.ThetaPairCenterTailSpectrum
import GaloisForLFunctions.HTGeometry.HarmonicOrdinateDivergence
import GaloisForLFunctions.RHTower.TwoEdgeBoundaryQuartet

/-!+# Fixed pair heads and the absolute Gamma boundary

Every fixed pair amplitude retains its inverse-square-root coefficient
on the natural Gamma scale. The diagonal coefficients form a harmonic
series, excluding a frequency-uniform summable absolute majorant.
Finite heads instead retain the square of their complete phase sum.
-/

open Complex Filter
open scoped Topology
noncomputable section
namespace GaloisForLFunctions.CompletedArithmeticForms

/-- The fixed-pair coefficient surviving natural Gamma normalization. -/
def thetaPairGammaCoefficient (n m : ℕ) : ℝ :=
  4 * (Real.pi * n * m) ^ (-(1 / 2 : ℝ))

theorem thetaPairGammaCoefficient_pos {n m : ℕ} (hn : 0 < n) (hm : 0 < m) :
    0 < thetaPairGammaCoefficient n m := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  unfold thetaPairGammaCoefficient
  positivity

theorem thetaPairGammaCoefficient_factor (n m : ℕ) :
    thetaPairGammaCoefficient n m = 4 * Real.pi ^ (-(1 / 2 : ℝ)) *
      (n : ℝ) ^ (-(1 / 2 : ℝ)) * (m : ℝ) ^ (-(1 / 2 : ℝ)) := by
  unfold thetaPairGammaCoefficient
  rw [Real.mul_rpow (by positivity) (Nat.cast_nonneg m),
    Real.mul_rpow Real.pi_pos.le (Nat.cast_nonneg n)]
  ring

private theorem diagonal_coefficient {n : ℕ} (hn : 0 < n) :
    thetaPairGammaCoefficient n n = 4 * Real.pi ^ (-(1 / 2 : ℝ)) / n := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  rw [thetaPairGammaCoefficient_factor, mul_assoc,
    ← Real.rpow_add hnR, show -(1 / 2 : ℝ) + -(1 / 2 : ℝ) = -1 by ring,
    Real.rpow_neg hnR.le, Real.rpow_one]
  rfl

/-- Each fixed radial pair retains its full coefficient on the Gamma scale. -/
theorem tendsto_thetaPairCenterTailAmplitude_div_gamma {n m : ℕ}
    (hn : 0 < n) (hm : 0 < m) (r : ℝ) :
    Tendsto (fun τ => thetaPairCenterTailAmplitude n m r (2 * τ) /
      besselNaturalGammaWeight τ) atTop (𝓝 (thetaPairGammaCoefficient n m)) := by
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hh := (tendsto_besselFirstAtomTailDensity_div_gamma
    (show 0 < Real.pi * n * m * Real.exp r by positivity)).const_mul
      (thetaPairGammaCoefficient n m)
  simpa only [thetaPairCenterTailAmplitude, thetaPairGammaCoefficient,
    mul_div_cancel_left₀ _ (by norm_num : (2 : ℝ) ≠ 0), mul_one, mul_div_assoc] using hh

/-- Even the diagonal prevents a summable absolute majorant uniform in frequency. -/
theorem not_summable_absolute_pair_gamma_majorant {r : ℝ} (hr : 0 ≤ r) :
    ¬ ∃ C : ℕ × ℕ → ℝ, Summable C ∧ ∀ n m : ℕ, ∀ τ : ℝ, 1 ≤ τ →
      |thetaPairCenterTailSpectrum (n + 1) (m + 1) r (2 * τ)| /
        besselNaturalGammaWeight τ ≤ C (n, m) := by
  rintro ⟨C, hC, hbound⟩
  let A : ℝ := 4 * Real.pi ^ (-(1 / 2 : ℝ))
  have hA : 0 < A := by dsimp only [A]; positivity
  have hdiag (n : ℕ) : A / ((n : ℝ) + 1) ≤ C (n, n) := by
    have hlim := tendsto_thetaPairCenterTailAmplitude_div_gamma
      (Nat.succ_pos n) (Nat.succ_pos n) r
    rw [diagonal_coefficient (Nat.succ_pos n), Nat.cast_add, Nat.cast_one] at hlim
    apply le_of_tendsto hlim
    filter_upwards [eventually_ge_atTop (1 : ℝ)] with τ hτ
    have hb := hbound n n τ hτ
    rw [abs_of_pos (thetaPairCenterTailSpectrum_diagonal_pos (Nat.succ_pos n) hr _),
      thetaPairCenterTailSpectrum_eq (Nat.succ_pos n) (Nat.succ_pos n) hr,
      sub_self, mul_zero, Real.cos_zero, one_mul] at hb
    exact hb
  have hs : Summable (fun n : ℕ => C (n, n) / A) :=
    (hC.comp_injective (fun _ _ h => congrArg Prod.fst h)).div_const A
  have hinv : Summable (fun n : ℕ => ((n : ℝ) + 1)⁻¹) := by
    apply Summable.of_nonneg_of_le (fun n => by positivity) _ hs
    intro n
    apply (le_div_iff₀ hA).mpr
    simpa only [div_eq_mul_inv, mul_comm] using hdiag n
  exact GaloisForLFunctions.HTGeometry.not_summable_inv_of_le_linear
    (c := 1) (by norm_num) (fun n => by positivity)
      (Eventually.of_forall fun n => by simp) hinv

/-- The logarithmic phase vector of a finite initial atom head. -/
def thetaFiniteGammaPhase (M : ℕ) (τ : ℝ) : ℂ :=
  ∑ j : Fin M, (((((j : ℕ) + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ) *
    Complex.exp (((2 * τ * Real.log ((j : ℕ) + 1) : ℝ) : ℂ) * I)

/-- The nonnegative leading term retains all ordered-pair phase correlations. -/
def thetaFiniteGammaLeading (M : ℕ) (τ : ℝ) : ℝ :=
  4 * Real.pi ^ (-(1 / 2 : ℝ)) * ‖thetaFiniteGammaPhase M τ‖ ^ 2

theorem thetaFiniteGammaLeading_nonneg (M : ℕ) (τ : ℝ) :
    0 ≤ thetaFiniteGammaLeading M τ := by
  unfold thetaFiniteGammaLeading
  positivity

/-- The finite cosine head is exactly one positive Gram square. -/
theorem thetaFiniteGammaLeading_eq_cosine_sum (M : ℕ) (τ : ℝ) :
    thetaFiniteGammaLeading M τ = ∑ i : Fin M, ∑ j : Fin M,
      Real.cos (2 * τ * (Real.log ((i : ℕ) + 1) - Real.log ((j : ℕ) + 1))) *
        thetaPairGammaCoefficient ((i : ℕ) + 1) ((j : ℕ) + 1) := by
  let c : Fin M → ℂ := fun j => (((((j : ℕ) + 1 : ℕ) : ℝ) ^ (-(1 / 2 : ℝ)) : ℝ) : ℂ)
  let T : Fin M → ℝ := fun j => Real.log ((j : ℕ) + 1)
  have hh := _root_.RHTower.trigPoly_normSq c T τ
  change ((‖thetaFiniteGammaPhase M τ‖ ^ 2 : ℝ) : ℂ) = _ at hh
  have hre := congrArg Complex.re hh
  simp only [Complex.ofReal_re, Complex.sum_re, c, T, Complex.conj_ofReal,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.exp_re, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero,
    add_zero, mul_one, Real.exp_zero, one_mul] at hre
  unfold thetaFiniteGammaLeading
  rw [hre, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [thetaPairGammaCoefficient_factor]
  push_cast
  ring

private theorem fixed_pair_error_tendsto {n m : ℕ} (hn : 0 < n) (hm : 0 < m)
    {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun τ => thetaPairCenterTailSpectrum n m r (2 * τ) /
      besselNaturalGammaWeight τ -
        Real.cos (2 * τ * (Real.log n - Real.log m)) * thetaPairGammaCoefficient n m)
      atTop (𝓝 0) := by
  have hlim := (tendsto_thetaPairCenterTailAmplitude_div_gamma hn hm r).sub_const
    (thetaPairGammaCoefficient n m)
  simp only [sub_self] at hlim
  have hnorm := hlim.norm
  rw [norm_zero] at hnorm
  apply squeeze_zero_norm' _ hnorm
  filter_upwards with τ
  rw [thetaPairCenterTailSpectrum_eq hn hm hr]
  have he : Real.cos (2 * τ * (Real.log n - Real.log m)) *
      thetaPairCenterTailAmplitude n m r (2 * τ) / besselNaturalGammaWeight τ -
        Real.cos (2 * τ * (Real.log n - Real.log m)) * thetaPairGammaCoefficient n m =
      Real.cos (2 * τ * (Real.log n - Real.log m)) *
        (thetaPairCenterTailAmplitude n m r (2 * τ) / besselNaturalGammaWeight τ -
          thetaPairGammaCoefficient n m) := by ring
  rw [he, norm_mul, Real.norm_eq_abs]
  simpa only [one_mul] using mul_le_mul_of_nonneg_right (Real.abs_cos_le_one _)
    (norm_nonneg (thetaPairCenterTailAmplitude n m r (2 * τ) /
      besselNaturalGammaWeight τ - thetaPairGammaCoefficient n m))

private theorem finite_sum_tendsto_zero {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hf : ∀ i ∈ s, Tendsto (f i) atTop (𝓝 0)) :
    Tendsto (fun τ => ∑ i ∈ s, f i τ) atTop (𝓝 0) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (tendsto_const_nhds (x := (0 : ℝ)))
  | @insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    simpa only [zero_add] using (hf i (Finset.mem_insert_self _ _)).add
      (ih (fun j hj => hf j (Finset.mem_insert_of_mem hj)))

/-- Every fixed finite pair head has the nonnegative phase square as its Gamma leading form. -/
theorem tendsto_thetaFinitePairHead_div_gamma_sub_leading (M : ℕ)
    {r : ℝ} (hr : 0 ≤ r) :
    Tendsto (fun τ =>
      (∑ i : Fin M, ∑ j : Fin M,
        thetaPairCenterTailSpectrum ((i : ℕ) + 1) ((j : ℕ) + 1) r (2 * τ)) /
          besselNaturalGammaWeight τ - thetaFiniteGammaLeading M τ) atTop (𝓝 0) := by
  have hh := finite_sum_tendsto_zero Finset.univ
    (fun i : Fin M => fun τ => ∑ j : Fin M,
      thetaPairCenterTailSpectrum ((i : ℕ) + 1) ((j : ℕ) + 1) r (2 * τ) /
        besselNaturalGammaWeight τ -
          Real.cos (2 * τ * (Real.log ((i : ℕ) + 1) - Real.log ((j : ℕ) + 1))) *
            thetaPairGammaCoefficient ((i : ℕ) + 1) ((j : ℕ) + 1))
    (fun i _ => finite_sum_tendsto_zero Finset.univ _
      (fun j _ => fixed_pair_error_tendsto (Nat.succ_pos _) (Nat.succ_pos _) hr))
  convert hh using 1
  funext τ
  rw [thetaFiniteGammaLeading_eq_cosine_sum]
  simp only [Finset.sum_div, Finset.sum_sub_distrib]

#print axioms not_summable_absolute_pair_gamma_majorant
#print axioms thetaFiniteGammaLeading_eq_cosine_sum
#print axioms tendsto_thetaFinitePairHead_div_gamma_sub_leading

end GaloisForLFunctions.CompletedArithmeticForms
