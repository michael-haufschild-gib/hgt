import GaloisForLFunctions.HTGeometry.FinitePhaseLawFromRatios
import GaloisForLFunctions.HTGeometry.GammaFieldLawWitness

/-!
# The law over Gamma-jet data is inhabited

The trivial Gamma-jet datum has shape `1`, so a constant coefficient is presented by it with its own
value as residue.  The exponential line therefore satisfies the hypotheses of the law over Gamma-jet
data on every vertical line, and its frequency rank is finite — the hypothesis class is not empty.
-/

open Filter Topology Complex

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- The trivial Gamma-jet datum has shape `1`. -/
@[simp] theorem gammaJetShape_zero (σ : ℝ) (t : ℝ) : gammaJetShape σ 0 0 0 0 t = 1 := by
  rw [gammaJetShape, polyJetShape]
  simp

/-- **The law over Gamma-jet data is inhabited.**  On every vertical line the exponential line
satisfies its hypotheses with constant coefficients, so its rational Bohr frequency rank is
finite. -/
theorem finite_phase_law_gammaJet_expLine {σ : ℝ} (hσ : 0 < σ) (μ : ℝ) (hμ : μ ≠ 0) :
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies (expLineBC μ σ)) ≤ (K : Cardinal) := by
  classical
  set f : ℝ →ᵇ ℂ := expLineBC μ σ with hfdef
  letI : MeasurableSpace (BohrHull f) := borel _
  haveI : BorelSpace (BohrHull f) := ⟨rfl⟩
  have hR : (0 : ℝ) < 1 := one_pos
  have hΦ : DifferentiableOn ℂ (expLine μ) (verticalStrip σ 1) :=
    (differentiable_expLine μ).differentiableOn
  have hap : IsStripAlmostPeriodic (expLine μ) σ 1 := isStripAlmostPeriodic_expLine μ _ _
  set e : Fin 2 → Fin 2 → ℕ := ![![0, 1], ![1, 0]] with hedef
  set F : Fin 2 → ℂ → ℂ := ![fun _ => 1, fun _ => -(μ : ℂ)] with hFdef
  set c : Fin 2 → ℂ := ![1, -(μ : ℂ)] with hcdef
  have hc : ∀ α : Fin 2, c α ≠ 0 := by
    intro α
    fin_cases α <;> simp [hcdef, hμ]
  have hFlim : ∀ α : Fin 2, Tendsto (fun t : ℝ => F α ((σ : ℂ) + (t : ℂ) * Complex.I)
      / gammaJetShape σ 0 0 0 0 t) atTop (nhds (c α)) := by
    intro α
    refine tendsto_const_nhds.congr (fun t => ?_)
    rw [gammaJetShape_zero, div_one]
    fin_cases α <;> simp [hFdef, hcdef]
  have hrel : ∀ s : ℂ,
      ∑ α, F α s * ∏ i : Fin 2, (iteratedDeriv (i : ℕ) (expLine μ) s) ^ (e α i) = 0 := by
    intro s
    rw [Fin.sum_univ_two]
    simp only [hedef, hFdef, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      iteratedDeriv_expLine, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    ring
  have he : Function.Injective e := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all
  have hline : IsBohrAlmostPeriodic
      (fun t : ℝ => expLine μ ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    isBohrAlmostPeriodic_line hR hap
  have hf : ∀ x : ℝ, f x = expLine μ ((σ : ℂ) + (x : ℂ) * Complex.I) := by
    intro x
    rw [hfdef, expLineBC_apply]
  have hcont : Continuous (fun x : ℝ => f x) := by
    have hfun : (fun x : ℝ => f x)
        = fun t : ℝ => expLine μ ((σ : ℂ) + (t : ℂ) * Complex.I) := funext hf
    rw [hfun]
    exact continuous_line_restriction hR hΦ
  have hapf : IsBohrAlmostPeriodic (fun x : ℝ => f x) := by
    have hfun : (fun x : ℝ => f x)
        = fun t : ℝ => expLine μ ((σ : ℂ) + (t : ℂ) * Complex.I) := funext hf
    rw [hfun]
    exact hline
  obtain ⟨-, -, -, -, -, hrank⟩ := finite_phase_law_of_gammaJet_data (rr := 1/4) (ρ := 1/4)
    hσ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hR hΦ hap e F
    (fun _ => 0) (fun _ => 0) (fun _ => 0) (fun _ => 0) c hc hFlim hrel he hf
    (uniformContinuous_of_isBohrAlmostPeriodic hcont hapf)
    (hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic hcont hapf)
  exact hrank

/-- The log-degree-one Gamma-jet datum has shape the leading logarithm. -/
@[simp] theorem gammaJetShape_log_one (σ : ℝ) (t : ℝ) :
    gammaJetShape σ 0 1 0 0 t = vertLog t := by
  rw [gammaJetShape, polyJetShape]
  simp

/-- **The law over Gamma-jet data is inhabited by a genuinely transcendental coefficient.**  Taking
the digamma function itself as the coefficient — datum `(0, 1, 0, 0)`, residue `1` — the exponential
line again satisfies the hypotheses, so the hypothesis class is not confined to constants. -/
theorem finite_phase_law_gammaJet_expLine_digammaCoeff {σ : ℝ} (hσ : 0 < σ) (μ : ℝ) (hμ : μ ≠ 0) :
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies (expLineBC μ σ)) ≤ (K : Cardinal) := by
  classical
  set f : ℝ →ᵇ ℂ := expLineBC μ σ with hfdef
  letI : MeasurableSpace (BohrHull f) := borel _
  haveI : BorelSpace (BohrHull f) := ⟨rfl⟩
  have hR : (0 : ℝ) < 1 := one_pos
  have hΦ : DifferentiableOn ℂ (expLine μ) (verticalStrip σ 1) :=
    (differentiable_expLine μ).differentiableOn
  have hap : IsStripAlmostPeriodic (expLine μ) σ 1 := isStripAlmostPeriodic_expLine μ _ _
  set e : Fin 2 → Fin 2 → ℕ := ![![0, 1], ![1, 0]] with hedef
  set F : Fin 2 → ℂ → ℂ :=
    ![fun s => Complex.digamma s, fun s => -(μ : ℂ) * Complex.digamma s] with hFdef
  set c : Fin 2 → ℂ := ![1, -(μ : ℂ)] with hcdef
  have hc : ∀ α : Fin 2, c α ≠ 0 := by
    intro α
    fin_cases α <;> simp [hcdef, hμ]
  have hbase : Tendsto (fun t : ℝ =>
      Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) / vertLog t) atTop (nhds 1) :=
    tendsto_digamma_div_vertLog hσ.le
  have hFlim : ∀ α : Fin 2, Tendsto (fun t : ℝ => F α ((σ : ℂ) + (t : ℂ) * Complex.I)
      / gammaJetShape σ 0 1 0 0 t) atTop (nhds (c α)) := by
    intro α
    fin_cases α
    · refine hbase.congr (fun t => ?_)
      rw [gammaJetShape_log_one]
      simp [hFdef]
    · have hmul := hbase.const_mul (-(μ : ℂ))
      rw [mul_one] at hmul
      refine hmul.congr (fun t => ?_)
      rw [gammaJetShape_log_one]
      show -(μ : ℂ) * (Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I) / vertLog t)
        = (-(μ : ℂ) * Complex.digamma ((σ : ℂ) + (t : ℂ) * Complex.I)) / vertLog t
      rw [mul_div_assoc]
  have hrel : ∀ s : ℂ,
      ∑ α, F α s * ∏ i : Fin 2, (iteratedDeriv (i : ℕ) (expLine μ) s) ^ (e α i) = 0 := by
    intro s
    rw [Fin.sum_univ_two]
    simp only [hedef, hFdef, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      iteratedDeriv_expLine, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    ring
  have he : Function.Injective e := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all
  have hline : IsBohrAlmostPeriodic
      (fun t : ℝ => expLine μ ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    isBohrAlmostPeriodic_line hR hap
  have hf : ∀ x : ℝ, f x = expLine μ ((σ : ℂ) + (x : ℂ) * Complex.I) := by
    intro x
    rw [hfdef, expLineBC_apply]
  have hcont : Continuous (fun x : ℝ => f x) := by
    have hfun : (fun x : ℝ => f x)
        = fun t : ℝ => expLine μ ((σ : ℂ) + (t : ℂ) * Complex.I) := funext hf
    rw [hfun]
    exact continuous_line_restriction hR hΦ
  have hapf : IsBohrAlmostPeriodic (fun x : ℝ => f x) := by
    have hfun : (fun x : ℝ => f x)
        = fun t : ℝ => expLine μ ((σ : ℂ) + (t : ℂ) * Complex.I) := funext hf
    rw [hfun]
    exact hline
  obtain ⟨-, -, -, -, -, hrank⟩ := finite_phase_law_of_gammaJet_data (rr := 1/4) (ρ := 1/4)
    hσ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hR hΦ hap e F
    (fun _ => 0) (fun _ => 1) (fun _ => 0) (fun _ => 0) c hc hFlim hrel he hf
    (uniformContinuous_of_isBohrAlmostPeriodic hcont hapf)
    (hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic hcont hapf)
  exact hrank

/-- The argument-degree-one datum has shape the coordinate. -/
@[simp] theorem gammaJetShape_arg_one (σ : ℝ) (t : ℝ) :
    gammaJetShape σ 0 0 1 0 t = (σ : ℂ) + (t : ℂ) * Complex.I := by
  rw [gammaJetShape, polyJetShape]
  simp

/-- The Gamma-degree-one datum has shape `Γ`. -/
@[simp] theorem gammaJetShape_gamma_one (σ : ℝ) (t : ℝ) :
    gammaJetShape σ 1 0 0 0 t = gammaLine σ t := by
  rw [gammaJetShape, polyJetShape]
  simp

/-- **The law applies to the exponential line with any presented coefficient.**  Multiplying the
relation `Φ′ − μΦ = 0` by a coefficient that converges against its Gamma-jet shape keeps every
hypothesis, so the rank is finite. -/
theorem finite_phase_law_gammaJet_expLine_of_data {σ : ℝ} (hσ : 0 < σ) (μ : ℝ) (hμ : μ ≠ 0)
    (u a dP b : ℕ) (G : ℂ → ℂ) {cG : ℂ} (hcG : cG ≠ 0)
    (hG : Tendsto (fun t : ℝ => G ((σ : ℂ) + (t : ℂ) * Complex.I)
      / gammaJetShape σ u a dP b t) atTop (nhds cG)) :
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies (expLineBC μ σ)) ≤ (K : Cardinal) := by
  classical
  set f : ℝ →ᵇ ℂ := expLineBC μ σ with hfdef
  letI : MeasurableSpace (BohrHull f) := borel _
  haveI : BorelSpace (BohrHull f) := ⟨rfl⟩
  have hR : (0 : ℝ) < 1 := one_pos
  have hΦ : DifferentiableOn ℂ (expLine μ) (verticalStrip σ 1) :=
    (differentiable_expLine μ).differentiableOn
  have hap : IsStripAlmostPeriodic (expLine μ) σ 1 := isStripAlmostPeriodic_expLine μ _ _
  set e : Fin 2 → Fin 2 → ℕ := ![![0, 1], ![1, 0]] with hedef
  set F : Fin 2 → ℂ → ℂ := ![G, fun s => -(μ : ℂ) * G s] with hFdef
  set c : Fin 2 → ℂ := ![cG, -(μ : ℂ) * cG] with hcdef
  have hc : ∀ α : Fin 2, c α ≠ 0 := by
    intro α
    fin_cases α
    · simpa [hcdef] using hcG
    · have hμc : (-(μ : ℂ)) ≠ 0 := by simpa using hμ
      simpa [hcdef] using mul_ne_zero hμc hcG
  have hFlim : ∀ α : Fin 2, Tendsto (fun t : ℝ => F α ((σ : ℂ) + (t : ℂ) * Complex.I)
      / gammaJetShape σ u a dP b t) atTop (nhds (c α)) := by
    intro α
    fin_cases α
    · exact hG
    · have hmul := hG.const_mul (-(μ : ℂ))
      refine hmul.congr (fun t => ?_)
      show -(μ : ℂ) * (G ((σ : ℂ) + (t : ℂ) * Complex.I) / gammaJetShape σ u a dP b t)
        = (-(μ : ℂ) * G ((σ : ℂ) + (t : ℂ) * Complex.I)) / gammaJetShape σ u a dP b t
      rw [mul_div_assoc]
  have hrel : ∀ s : ℂ,
      ∑ α, F α s * ∏ i : Fin 2, (iteratedDeriv (i : ℕ) (expLine μ) s) ^ (e α i) = 0 := by
    intro s
    rw [Fin.sum_univ_two]
    simp only [hedef, hFdef, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      iteratedDeriv_expLine, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    ring
  have he : Function.Injective e := by
    intro x y hxy
    fin_cases x <;> fin_cases y <;> simp_all
  have hline : IsBohrAlmostPeriodic
      (fun t : ℝ => expLine μ ((σ : ℂ) + (t : ℂ) * Complex.I)) :=
    isBohrAlmostPeriodic_line hR hap
  have hf : ∀ x : ℝ, f x = expLine μ ((σ : ℂ) + (x : ℂ) * Complex.I) := by
    intro x
    rw [hfdef, expLineBC_apply]
  have hcont : Continuous (fun x : ℝ => f x) := by
    have hfun : (fun x : ℝ => f x)
        = fun t : ℝ => expLine μ ((σ : ℂ) + (t : ℂ) * Complex.I) := funext hf
    rw [hfun]
    exact continuous_line_restriction hR hΦ
  have hapf : IsBohrAlmostPeriodic (fun x : ℝ => f x) := by
    have hfun : (fun x : ℝ => f x)
        = fun t : ℝ => expLine μ ((σ : ℂ) + (t : ℂ) * Complex.I) := funext hf
    rw [hfun]
    exact hline
  obtain ⟨-, -, -, -, -, hrank⟩ := finite_phase_law_of_gammaJet_data (rr := 1/4) (ρ := 1/4)
    hσ (by norm_num) (by norm_num) (by norm_num) (by norm_num) hR hΦ hap e F
    (fun _ => u) (fun _ => a) (fun _ => dP) (fun _ => b) c hc hFlim hrel he hf
    (uniformContinuous_of_isBohrAlmostPeriodic hcont hapf)
    (hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic hcont hapf)
  exact hrank

/-- Inhabited with the coordinate as coefficient — the argument-degree level. -/
theorem finite_phase_law_gammaJet_expLine_coordCoeff {σ : ℝ} (hσ : 0 < σ) (μ : ℝ) (hμ : μ ≠ 0) :
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies (expLineBC μ σ)) ≤ (K : Cardinal) := by
  refine finite_phase_law_gammaJet_expLine_of_data hσ μ hμ 0 0 1 0 (fun s => s)
    (cG := 1) one_ne_zero ?_
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_vertical_ne_zero σ] with t hs
  rw [gammaJetShape_arg_one, div_self hs]

/-- Inhabited with `Γ` as coefficient — the Gamma-exponent level. -/
theorem finite_phase_law_gammaJet_expLine_gammaCoeff {σ : ℝ} (hσ : 0 < σ) (μ : ℝ) (hμ : μ ≠ 0) :
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies (expLineBC μ σ)) ≤ (K : Cardinal) := by
  refine finite_phase_law_gammaJet_expLine_of_data hσ μ hμ 1 0 0 0
    (fun s => Complex.Gamma s) (cG := 1) one_ne_zero ?_
  refine tendsto_const_nhds.congr (fun t => ?_)
  rw [gammaJetShape_gamma_one, gammaLine]
  exact (div_self (by simpa [gammaLine] using gammaLine_ne_zero hσ t)).symm

end GaloisForLFunctions
