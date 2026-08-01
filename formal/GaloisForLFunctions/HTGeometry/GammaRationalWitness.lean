import GaloisForLFunctions.HTGeometry.GammaRationalFinitePhaseRank
import GaloisForLFunctions.HTGeometry.StripAlmostPeriodicExpSum

/-!
# The finite-phase law is not vacuous

The exponential `z ↦ e^{μ z}` with a nonzero real frequency satisfies every hypothesis of the
finite-phase law over the Gamma field: it is entire, almost periodic on every vertical strip, its line
restriction is a bounded continuous function with totally bounded orbit, and it solves the relation
`Φ' − μ Φ = 0`, whose coefficients `1` and `−μ` are Gamma-rational (constants) and whose two monomials
are distinct.

So the hypothesis class of the law is inhabited by nonconstant functions, and the conclusion is a
statement about a nonempty class.
-/

open Filter Topology Metric Set MvPolynomial

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open _root_.HTGeometry

/-- The exponential `z ↦ e^{μ z}` with a real frequency. -/
noncomputable def expLine (μ : ℝ) : ℂ → ℂ := fun z => Complex.exp ((μ : ℂ) * z)

theorem expLine_eq_expSum (μ : ℝ) : expLine μ = expSum (fun _ : Fin 1 => 1) (fun _ : Fin 1 => μ) := by
  funext z
  simp [expLine, expSum]

theorem differentiable_expLine (μ : ℝ) : Differentiable ℂ (expLine μ) := by
  rw [expLine_eq_expSum]
  exact differentiable_expSum _ _

theorem isStripAlmostPeriodic_expLine (μ σ R : ℝ) : IsStripAlmostPeriodic (expLine μ) σ R := by
  rw [expLine_eq_expSum]
  exact isStripAlmostPeriodic_expSum _ _ _ _

theorem deriv_expLine (μ : ℝ) (z : ℂ) : deriv (expLine μ) z = (μ : ℂ) * expLine μ z := by
  have h1 : HasDerivAt (fun w : ℂ => (μ : ℂ) * w) (μ : ℂ) z := by
    simpa using (hasDerivAt_id z).const_mul (μ : ℂ)
  have h2 : HasDerivAt (expLine μ) (Complex.exp ((μ : ℂ) * z) * (μ : ℂ)) z := h1.cexp
  rw [h2.deriv]
  simp only [expLine]
  ring

theorem iteratedDeriv_expLine (μ : ℝ) (k : ℕ) (z : ℂ) :
    iteratedDeriv k (expLine μ) z = (μ : ℂ) ^ k * expLine μ z := by
  induction k generalizing z with
  | zero => simp [iteratedDeriv_zero]
  | succ j ih =>
      rw [iteratedDeriv_succ]
      have hfun : iteratedDeriv j (expLine μ) = fun w => (μ : ℂ) ^ j * expLine μ w := by
        funext w
        exact ih w
      rw [hfun]
      have hd : deriv (fun w : ℂ => (μ : ℂ) ^ j * expLine μ w) z
          = (μ : ℂ) ^ j * deriv (expLine μ) z := by
        exact deriv_const_mul _ ((differentiable_expLine μ) z)
      rw [hd, deriv_expLine]
      ring

theorem norm_expLine_line (μ σ x : ℝ) :
    ‖expLine μ ((σ : ℂ) + (x : ℂ) * Complex.I)‖ = Real.exp (μ * σ) := by
  rw [expLine, Complex.norm_exp]
  congr 1
  simp

theorem continuous_expLine_line (μ σ : ℝ) :
    Continuous fun x : ℝ => expLine μ ((σ : ℂ) + (x : ℂ) * Complex.I) := by
  refine Complex.continuous_exp.comp ?_
  exact continuous_const.mul (continuous_const.add (Complex.continuous_ofReal.mul continuous_const))

/-- The vertical line restriction of `z ↦ e^{μ z}` as a bounded continuous function. -/
noncomputable def expLineBC (μ σ : ℝ) : ℝ →ᵇ ℂ :=
  BoundedContinuousFunction.mkOfBound
    ⟨fun x : ℝ => expLine μ ((σ : ℂ) + (x : ℂ) * Complex.I), continuous_expLine_line μ σ⟩
    (2 * Real.exp (μ * σ)) (by
      intro x y
      have hx := norm_expLine_line μ σ x
      have hy := norm_expLine_line μ σ y
      have h := dist_le_norm_add_norm (expLine μ ((σ : ℂ) + (x : ℂ) * Complex.I))
        (expLine μ ((σ : ℂ) + (y : ℂ) * Complex.I))
      simp only [ContinuousMap.coe_mk]
      rw [hx, hy] at h
      linarith)

@[simp] theorem expLineBC_apply (μ σ x : ℝ) :
    expLineBC μ σ x = expLine μ ((σ : ℂ) + (x : ℂ) * Complex.I) := rfl

/-- **The finite-phase law over the Gamma field is not vacuous.**  The exponential `e^{μ z}` with a
nonzero real frequency satisfies every hypothesis: it is holomorphic and strip almost periodic, its
line restriction is a bounded continuous function with totally bounded orbit, and it solves the
Gamma-rational relation `Φ' − μ (expLine μ) = 0` with distinct monomials. -/
theorem rank_finite_expLine (μ : ℝ) (hμ : μ ≠ 0) :
    ∃ K : ℕ, Module.rank ℤ (bohrHullFrequencies (expLineBC μ 2)) ≤ (K : Cardinal) := by
  classical
  set f : ℝ →ᵇ ℂ := expLineBC μ 2 with hfdef
  letI : MeasurableSpace (BohrHull f) := borel _
  haveI : BorelSpace (BohrHull f) := ⟨rfl⟩
  have hR : (0 : ℝ) < 1 := one_pos
  have hΦdiff : DifferentiableOn ℂ (expLine μ) (verticalStrip 2 1) := (differentiable_expLine μ).differentiableOn
  have hap : IsStripAlmostPeriodic (expLine μ) 2 1 := isStripAlmostPeriodic_expLine μ 2 1
  have hf : ∀ x : ℝ, f x = (expLine μ) ((2 : ℂ) + (x : ℂ) * Complex.I) := by
    intro x
    rw [hfdef, expLineBC_apply]
    norm_num
  have hline : IsBohrAlmostPeriodic (fun t : ℝ => (expLine μ) (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I)) :=
    isBohrAlmostPeriodic_line hR hap
  have hcont : Continuous (fun x : ℝ => f x) := by
    have : (fun x : ℝ => f x)
        = fun t : ℝ => (expLine μ) (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
      funext x
      rw [hf x]
      norm_num
    rw [this]
    exact continuous_line_restriction hR hΦdiff
  have hapf : IsBohrAlmostPeriodic (fun x : ℝ => f x) := by
    have hfun : (fun x : ℝ => f x)
        = fun t : ℝ => (expLine μ) (((2 : ℝ) : ℂ) + (t : ℂ) * Complex.I) := by
      funext x
      rw [hf x]
      norm_num
    rw [hfun]
    exact hline
  have hfu : UniformContinuous (fun x : ℝ => f x) :=
    uniformContinuous_of_isBohrAlmostPeriodic hcont hapf
  have hftb : HasTotallyBoundedOrbit (fun x : ℝ => f x) :=
    hasTotallyBoundedOrbit_of_isBohrAlmostPeriodic hcont hapf
  -- the relation `Φ' - μ (expLine μ) = 0`
  set e : Fin 2 → Fin 2 → ℕ := ![![0, 1], ![1, 0]] with hedef
  set Cf : Fin 2 → ℂ → ℂ := ![fun _ => 1, fun _ => -(μ : ℂ)] with hCfdef
  set pp : Fin 2 → Polynomial ℂ := ![Polynomial.C 1, Polynomial.C (-(μ : ℂ))] with hppdef
  set qq : Fin 2 → Polynomial ℂ := ![Polynomial.C 1, Polynomial.C 1] with hqqdef
  have hq0 : ∀ α, (qq α).eval 0 ≠ 0 := by
    intro α
    fin_cases α <;> simp [hqqdef]
  have hp0 : ∀ α, (pp α).eval 0 ≠ 0 := by
    intro α
    fin_cases α <;> simp [hppdef, hμ]
  have hCf : ∀ (α : Fin 2), ∀ s ∈ verticalStrip (2 : ℝ) 1,
      Cf α s = ((Complex.Gamma s) ^ (0 : ℕ) * (pp α).eval (Complex.Gamma s))
        / ((Complex.Gamma s) ^ (0 : ℕ) * (qq α).eval (Complex.Gamma s)) := by
    intro α s _
    fin_cases α <;> simp [hCfdef, hppdef, hqqdef]
  have hrelC : ∀ s : ℂ,
      ∑ α, Cf α s * ∏ j : Fin 2, (iteratedDeriv (j : ℕ) (expLine μ) s) ^ (e α j) = 0 := by
    intro s
    rw [Fin.sum_univ_two]
    simp only [hedef, hCfdef, Fin.prod_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one,
      iteratedDeriv_expLine, Fin.val_zero, Fin.val_one, pow_zero, pow_one]
    ring
  have he : Function.Injective e := by
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all
  refine rank_finite_of_gamma_rational_relation (r := 1/4) (ρ := 1/4) (by norm_num) (by norm_num)
    (by norm_num) hR (by norm_num) hΦdiff hap e Cf pp qq (fun _ => 0) (fun _ => 0) 0
    hq0 hp0 hCf hrelC (fun α => le_rfl) hf hfu hftb he

/-- The frequency character is Lipschitz for the translation distance of the exponential. -/
theorem norm_expChar_sub_le (μ σ : ℝ) (s t : BohrLine (expLineBC μ σ)) :
    ‖expChar μ s.val - expChar μ t.val‖ ≤ Real.exp (-(μ * σ)) * dist s t := by
  have hval : ∀ x u : ℝ, (expLineBC μ σ) (x + u)
      = Complex.exp ((μ * σ : ℝ)) * expChar μ x * expChar μ u := by
    intro x u
    rw [expLineBC_apply, expLine, expChar, expChar]
    rw [← Complex.exp_add, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hpt : ‖(expLineBC μ σ) (0 + s.val) - (expLineBC μ σ) (0 + t.val)‖
      = Real.exp (μ * σ) * ‖expChar μ s.val - expChar μ t.val‖ := by
    rw [hval 0 s.val, hval 0 t.val]
    have h0 : expChar μ 0 = 1 := by simp [expChar]
    rw [h0, mul_one, ← mul_sub, norm_mul]
    congr 1
    rw [Complex.norm_exp]
    simp
  have hle : ‖(expLineBC μ σ) (0 + s.val) - (expLineBC μ σ) (0 + t.val)‖ ≤ dist s t := by
    rw [BohrLine.dist_eq, ← dist_eq_norm]
    have := BoundedContinuousFunction.dist_coe_le_dist (f := translateBC s.val (expLineBC μ σ))
      (g := translateBC t.val (expLineBC μ σ)) 0
    simpa [translateBC_apply] using this
  rw [hpt] at hle
  have hexp : 0 < Real.exp (μ * σ) := Real.exp_pos _
  rw [Real.exp_neg, inv_mul_eq_div, le_div_iff₀ hexp]
  nlinarith [norm_nonneg (expChar μ s.val - expChar μ t.val), hle]

/-- **The frequency of the exponential is a frequency of its hull.** -/
theorem isBohrHullFrequency_expLineBC (μ σ : ℝ) : IsBohrHullFrequency (expLineBC μ σ) μ := by
  refine (LipschitzWith.of_dist_le_mul (K := ⟨Real.exp (-(μ * σ)), (Real.exp_pos _).le⟩)
    fun s t => ?_).uniformContinuous
  rw [dist_eq_norm]
  exact norm_expChar_sub_le μ σ s t

/-- **The witness has nonzero phase rank.** -/
theorem one_le_rank_expLineBC (μ : ℝ) (hμ : μ ≠ 0) (σ : ℝ) :
    1 ≤ Module.rank ℤ (bohrHullFrequencies (expLineBC μ σ)) := by
  have hmem : μ ∈ bohrHullFrequencies (expLineBC μ σ) := isBohrHullFrequency_expLineBC μ σ
  haveI : Nontrivial (bohrHullFrequencies (expLineBC μ σ)) := by
    refine ⟨⟨0, ⟨μ, hmem⟩, ?_⟩⟩
    intro hcon
    exact hμ (by simpa [eq_comm] using congrArg Subtype.val hcon)
  have hpos : 0 < Module.rank ℤ (bohrHullFrequencies (expLineBC μ σ)) := rank_pos
  exact Cardinal.one_le_iff_pos.mpr hpos

/-- **The finite-phase law is inhabited by an object of nonzero rank.**  For a nonzero real
frequency the exponential satisfies every hypothesis of the law and its rational Bohr frequency rank
lies between `1` and the finite bound the law provides. -/
theorem rank_expLine_pos_and_finite (μ : ℝ) (hμ : μ ≠ 0) :
    ∃ K : ℕ, 1 ≤ Module.rank ℤ (bohrHullFrequencies (expLineBC μ 2)) ∧
      Module.rank ℤ (bohrHullFrequencies (expLineBC μ 2)) ≤ (K : Cardinal) := by
  obtain ⟨K, hK⟩ := rank_finite_expLine μ hμ
  exact ⟨K, one_le_rank_expLineBC μ hμ 2, hK⟩

end GaloisForLFunctions
