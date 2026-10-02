import GaloisForLFunctions.RHTower.CCMCoherentGammaModulationRecurrence
import GaloisForLFunctions.RHTower.SuzukiWeilFriedrichsOperator

/-!
# The actual norm shift also controls the remainder without its polar term

Modulation at a recurrent finite-prime phase clock leaves the prime quadratic
unchanged in the limit and sends both polar charges to zero. Thus deleting
the finite-rank polar term cannot enlarge the numerical radius of the
scalar-minus-prime remainder. This argument concerns bounded physical
operators; it makes no claim about the Gamma energy of modulated vectors.
-/

open Complex MeasureTheory Set Filter
open scoped InnerProduct Topology BigOperators
open GaloisForLFunctions.HTGeometry
noncomputable section
namespace RHTower

private theorem phase_clock (d : ℕ) (v : Fin d → ℝ) :
    ∃ κ : ℕ → ℝ, Tendsto κ atTop atTop ∧
      ∀ i, Tendsto (fun j => modulationSymbol (κ j) (v i)) atTop (𝓝 1) := by
  have hc (j : ℕ) :=
    exists_fin_simultaneous_two_pi_phase_approximation_annular_quantitative
      (Nat.succ_pos j) (fun i => 2 * Real.pi * v i)
  choose k hk _ m hm using hc
  let κ : ℕ → ℝ := fun j => (k j : ℝ)
  have hκ : Tendsto κ atTop atTop := by
    apply tendsto_atTop_mono _ tendsto_natCast_atTop_atTop
    intro j
    change (j : ℝ) ≤ (k j : ℝ)
    exact_mod_cast (Nat.le_succ j).trans (hk j)
  refine ⟨κ, hκ, fun i => ?_⟩
  have hb (j : ℕ) :
      ‖modulationSymbol (κ j) (v i) - 1‖ ≤ 2 * Real.pi / ((j + 1 : ℕ) : ℝ) := by
    have h := (norm_exp_I_mul_real_sub_one_le_mod_two_pi
      ((k j : ℝ) * (2 * Real.pi * v i)) (m j i)).trans (hm j i)
    have heq : modulationSymbol (κ j) (v i) =
        Complex.exp (I * (((k j : ℝ) * (2 * Real.pi * v i) : ℝ) : ℂ)) := by
      unfold modulationSymbol
      dsimp only [κ]
      congr 1
      push_cast
      ring
    rwa [heq]
  have hi : Tendsto (fun j : ℕ => ((j + 1 : ℕ) : ℝ)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp
      (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
  have hb0 : Tendsto (fun j : ℕ => 2 * Real.pi / ((j + 1 : ℕ) : ℝ)) atTop (𝓝 0) := by
    simpa only [mul_zero, div_eq_mul_inv] using hi.const_mul (2 * Real.pi)
  rw [tendsto_iff_dist_tendsto_zero]
  simpa only [dist_eq_norm] using squeeze_zero (fun j => norm_nonneg _) hb hb0

private theorem modulation_inner (t : ℝ) (f g : SoninL2) :
    inner ℂ (modulationMul t f) (modulationMul t g) = inner ℂ f g := by
  let U : SoninL2 →ₗᵢ[ℂ] SoninL2 :=
    { (modulationMul t).toLinearMap with
      norm_map' := GaloisForLFunctions.norm_modulationMul_eq t }
  exact U.inner_map_map f g

private theorem translated_modulation_inner (t h : ℝ) (f : SoninL2) :
    inner ℂ (logTranslationCLM h (modulationMul t f)) (modulationMul t f) =
      star (modulationSymbol t h) * inner ℂ (logTranslationCLM h f) f := by
  rw [logTranslationCLM_modulationMul_apply, inner_smul_left, modulation_inner]
  simp only [starRingEnd_apply]

/-- The literal scalar-minus-prime quadratic is bounded by the norm of the
full remainder, although that remainder also contains the polar operator. -/
theorem abs_ccmPolarFreeRemainderQuadratic_le (a : SuzukiPositiveAperture)
    (f : suzukiApertureHilbert a) :
    |(ccmArchimedeanRemainderScalar * inner ℂ f f -
        inner ℂ (ccmFinitePrimeOperator a f) f).re| ≤
      ‖ccmRestrictedWeilBoundedRemainder a‖ * ‖f‖ ^ 2 := by
  let N := Nat.floor (Real.exp (2 * a.1))
  obtain ⟨κ, hκ, hp⟩ := phase_clock (N + 1) (fun i => Real.log (i : ℕ))
  have hp' (n : ℕ) (hn : n ≤ N) :
      Tendsto (fun j => modulationSymbol (κ j) (Real.log n)) atTop (𝓝 1) :=
    hp ⟨n, Nat.lt_succ_of_le hn⟩
  have hm (n : ℕ) (hn : n ≤ N) :
      Tendsto (fun j => modulationSymbol (κ j) (-Real.log n)) atTop (𝓝 1) := by
    have he (t h : ℝ) : modulationSymbol t (-h) = star (modulationSymbol t h) := by
      change modulationSymbol t (-h) = (starRingEnd ℂ) (modulationSymbol t h)
      rw [conj_modulationSymbol]
      unfold modulationSymbol
      congr 1
      push_cast
      ring
    simpa only [he, star_one] using (hp' n hn).star
  let F : ℕ → suzukiApertureHilbert a := fun j => ccmApertureModulation a (κ j) f
  have hprime : Tendsto (fun j => inner ℂ (ccmFinitePrimeOperator a (F j)) (F j))
      atTop (𝓝 (inner ℂ (ccmFinitePrimeOperator a f) f)) := by
    simp_rw [inner_ccmFinitePrimeOperator, inner_ccmPrimeTransportOperator]
    apply tendsto_finsetSum
    intro n hn
    have hn' : n ≤ N := (Finset.mem_Icc.mp hn).2
    change Tendsto (fun j => (ArithmeticFunction.vonMangoldt n : ℂ) *
      (((1 / Real.sqrt n : ℝ) : ℂ) *
        (inner ℂ (logTranslationCLM (Real.log n) (modulationMul (κ j) f.1))
          (modulationMul (κ j) f.1) +
         inner ℂ (logTranslationCLM (-Real.log n) (modulationMul (κ j) f.1))
          (modulationMul (κ j) f.1)))) _ _
    simp_rw [translated_modulation_inner]
    simpa only [star_one, one_mul, mul_assoc] using
      (((hp' n hn').star.mul_const (inner ℂ (logTranslationCLM (Real.log n) f.1) f.1)).add
        ((hm n hn').star.mul_const (inner ℂ (logTranslationCLM (-Real.log n) f.1) f.1))).const_mul
          ((ArithmeticFunction.vonMangoldt n : ℂ) * ((1 / Real.sqrt n : ℝ) : ℂ))
  have hcharge (s : ℝ) :
      Tendsto (fun j => inner ℂ (ccmPolarApertureVector a s) (F j)) atTop (𝓝 0) :=
    (inner_ccmApertureModulation_tendsto_zero a f (ccmPolarApertureVector a s)).comp hκ
  have hpolar : Tendsto (fun j => inner ℂ (ccmPolarOperator a (F j)) (F j))
      atTop (𝓝 0) := by
    simp_rw [inner_ccmPolarOperator, starRingEnd_apply]
    simpa only [star_zero, zero_mul, add_zero] using
      (((hcharge (-1 / 2)).star.mul (hcharge (1 / 2))).add
        ((hcharge (1 / 2)).star.mul (hcharge (-1 / 2))))
  have hfull : Tendsto
      (fun j => inner ℂ (ccmRestrictedWeilBoundedRemainder a (F j)) (F j)) atTop
      (𝓝 (ccmArchimedeanRemainderScalar * inner ℂ f f -
        inner ℂ (ccmFinitePrimeOperator a f) f)) := by
    have hself (j : ℕ) : inner ℂ (F j) (F j) = inner ℂ f f :=
      modulation_inner (κ j) f.1 f.1
    simp_rw [inner_ccmRestrictedWeilBoundedRemainder, hself]
    simpa only [add_zero] using
      (tendsto_const_nhds.add hpolar).sub hprime
  apply le_of_tendsto ((Complex.continuous_re.tendsto _).comp hfull |>.abs)
  apply Eventually.of_forall
  intro j
  calc
    _ ≤ ‖ccmRestrictedWeilBoundedRemainder a (F j)‖ * ‖F j‖ := by
      exact (Complex.abs_re_le_norm _).trans
        (norm_inner_le_norm (ccmRestrictedWeilBoundedRemainder a (F j)) (F j))
    _ ≤ (‖ccmRestrictedWeilBoundedRemainder a‖ * ‖F j‖) * ‖F j‖ :=
      mul_le_mul_of_nonneg_right ((ccmRestrictedWeilBoundedRemainder a).le_opNorm _) (norm_nonneg _)
    _ = _ := by rw [show ‖F j‖ = ‖f‖ from norm_ccmApertureModulation a (κ j) f]; ring

end RHTower
