import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.AttenuatedBlocks.SquareClosure

/-! # A missing line can retain an arbitrary fraction of a finite occupation -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology Set ContinuousLinearMap InnerProductSpace

/-- A unit missing direction whose second component moves to arbitrarily high occupation. -/
def escapingWave (t : Ioc (0:ℝ) 1) (n : ℕ) : Gas :=
  (Real.sqrt (1-t.val):ℂ) • modeWave 1 + (Real.sqrt t.val:ℂ) • modeWave (number (n+1))

theorem escapingWave_norm (t : Ioc (0:ℝ) 1) (n : ℕ) : ‖escapingWave t n‖ = 1 := by
  have hn : (1:ℕ+) ≠ number (n+1) := by
    intro h
    have he := congrArg PNat.val h
    change 1 = n+1+1 at he
    omega
  have ho : inner ℂ (modeWave 1) (modeWave (number (n+1))) = 0 := by
    simp [modeWave,lp.inner_single_left,lp.single_apply,Pi.single_eq_of_ne hn]
  have he := norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero (𝕜 := ℂ)
    ((Real.sqrt (1-t.val):ℂ) • modeWave 1) ((Real.sqrt t.val:ℂ) • modeWave (number (n+1)))
    (by simp only [inner_smul_left,inner_smul_right,ho,mul_zero])
  change ‖escapingWave t n‖ * ‖escapingWave t n‖ = _ at he
  simp only [norm_smul,Complex.norm_real,Real.norm_of_nonneg (Real.sqrt_nonneg _),modeWave_norm,mul_one] at he
  nlinarith only [he,Real.sq_sqrt (sub_nonneg.mpr t.property.2),Real.sq_sqrt t.property.1.le,norm_nonneg (escapingWave t n)]

private theorem attenuation_far (n : ℕ) : Real.sqrt (occupationWeight n) = attenuation (number n) :=
  Real.sqrt_sq (attenuation_pos _).le

private theorem heated_tail_tendsto {r : ℕ} (N : ℕ) (j : Fin r) :
    Tendsto (fun n => criticalOperator (translatedMode N j (modeWave (number (n+1))))) atTop (𝓝 0) := by
  have hs : Tendsto (fun n => occupationWeight (n+1)) atTop (𝓝 0) := occupationWeight_tendsto.comp (tendsto_add_atTop_nat 1)
  have ha : Tendsto (fun n => attenuation (number (n+1))) atTop (𝓝 0) := by
    have ht : Tendsto (fun n => Real.sqrt (occupationWeight (n+1))) atTop (𝓝 (Real.sqrt 0)) :=
      (Real.continuous_sqrt.tendsto 0).comp hs
    simpa only [attenuation_far,Real.sqrt_zero] using ht
  rw [tendsto_zero_iff_norm_tendsto_zero]
  apply squeeze_zero (fun n => norm_nonneg _) _ ha
  intro n
  rw [translatedMode_single,heat_modeWave,norm_smul,modeWave_norm,mul_one,
    Complex.norm_real,Real.norm_of_nonneg (attenuation_pos _).le]
  exact attenuation_antitone ((progression_increases j _).trans (skipLabel_increases 0 N _))

/-- Heat-visible part of the missing direction after its high-energy component escapes. -/
def visibleMode (N : ℕ) {r : ℕ} (j : Fin r) (t : Ioc (0:ℝ) 1) :=
  (Real.sqrt (1-t.val):ℂ) • criticalOperator (modeWave (number (N+j.val)))

private theorem heated_wave_tendsto (N : ℕ) {r : ℕ} (j : Fin r) (t : Ioc (0:ℝ) 1) :
    Tendsto (fun n => criticalOperator (translatedMode N j (escapingWave t n))) atTop (𝓝 (visibleMode N j t)) := by
  have he (n : ℕ) : criticalOperator (translatedMode N j (escapingWave t n)) =
      visibleMode N j t + (Real.sqrt t.val:ℂ) • criticalOperator (translatedMode N j (modeWave (number (n+1)))) := by
    unfold escapingWave translatedMode
    simp only [map_add,map_smul]
    rw [show extendModes (skipLabel 0 N) (extendModes (progression j) (modeWave 1)) = _ from translatedMode_first N j]
    rfl
  simp only [funext he]
  simpa only [smul_zero,add_zero] using (tendsto_const_nhds (x := visibleMode N j t)).add
    ((tendsto_const_nhds (x := (Real.sqrt t.val:ℂ))).smul (heated_tail_tendsto N j))

/-- Ideal squared heat with independently attenuated occupations in a single block. -/
def attenuatedSquare (N : ℕ) {r : ℕ} (t : Fin r → Ioc (0:ℝ) 1) : GasOp :=
  squareHeat.val - ∑ j, rankOne ℂ (visibleMode N j (t j)) (visibleMode N j (t j))

/-- Any prescribed nonzero surviving fractions occur in the norm closure at exactly the same missing rank. -/
theorem attenuatedSquare_mem_closure (N : ℕ) {r : ℕ} (t : Fin r → Ioc (0:ℝ) 1) :
    attenuatedSquare N t ∈ closure (physicalSquares r) := by
  let W (n : ℕ) (j : Fin r) := translatedMode N j (escapingWave (t j) n)
  have hw (n : ℕ) (j : Fin r) : ‖W n j‖ = 1 := (translatedMode_norm _ _ _).trans (escapingWave_norm _ _)
  have hn (n : ℕ) (j : Fin r) : W n j ≠ 0 := norm_ne_zero_iff.mp ((hw n j).trans_ne one_ne_zero)
  have ho (n : ℕ) (i j : Fin r) (h : i ≠ j) : inner ℂ (W n i) (W n j) = 0 := translatedMode_orthogonal N h _ _
  have he (n : ℕ) (j : Fin r) : lineCorrection (W n j) = rankOne ℂ (criticalOperator (W n j)) (criticalOperator (W n j)) := by
    rw [lineCorrection_eq,hw,one_pow,Complex.ofReal_one,inv_one,one_smul]
  have ht (j : Fin r) : Tendsto (fun n => lineCorrection (W n j)) atTop (𝓝 (rankOne ℂ (visibleMode N j (t j)) (visibleMode N j (t j)))) := by
    simp only [he]
    exact (_root_.RHTower.continuous_rankOne_self.tendsto _).comp (heated_wave_tendsto N j (t j))
  have hlim : Tendsto (fun n => projected (omitFamily (W n))^2) atTop (𝓝 (attenuatedSquare N t)) := by
    have e (n : ℕ) := family_square (hn n) (ho n)
    simp only [e,attenuatedSquare]
    exact tendsto_const_nhds.sub (tendsto_finsetSum Finset.univ (fun j _ => ht j))
  exact isClosed_closure.mem_of_tendsto hlim (Eventually.of_forall fun n =>
    translated_square_mem_closure N _ (fun j => norm_ne_zero_iff.mp ((escapingWave_norm (t j) n).trans_ne one_ne_zero)))

#print axioms escapingWave_norm
#print axioms attenuatedSquare_mem_closure

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
