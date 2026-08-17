import GaloisForLFunctions.RHTower.HermiteRungRayleighDefect
import GaloisForLFunctions.RHTower.ProlateHighModeCounting
import GaloisForLFunctions.RHTower.ProlateTrialSpaceTransport

/-!
# The rung-family trial space beats its ladder threshold

A single rescaled Hermite function has prolate Rayleigh quotient above the oscillator ladder value
of its own rung.  Counting excited modes needs the same bound for every nonzero *combination* of a
family of rungs, against the ladder value of the **top** rung of the family.

Writing `ψ = ∑ aᵢ φ_{rᵢ}` and rescaling to the Hermite variable `ξ = √c·x`, the excess

```text
∫ (L_c ψ(√c·))·ψ(√c·)  +  (2N+1)c ∫ ψ(√c·)²
```

is exactly

```text
c·∑ᵢ∑ⱼ aᵢaⱼ·2(N − rᵢ)·∫_{-√c}^{√c} φ_{rᵢ}φ_{rⱼ}
  + ∫_{-√c}^{√c} ξ²(ψ′)²  −  [ξ²ψψ′]_{-√c}^{√c} ,
```

divided by `√c`.  Every off-diagonal `∫φ_{rᵢ}φ_{rⱼ}` is the increment of the Hermite Wronskian, a
polynomial times a Gaussian, so it dies faster than `c` grows; the boundary term dies for the same
reason.  What is left is a fixed positive-definite quadratic form: its first part is positive unless
the combination lives on the top rung alone, and its second part — the square `∫ξ²(ψ′)²` — is
positive exactly there.  Compactness of the coefficient sphere turns that into a uniform positive
lower bound, and the two vanishing errors are eventually smaller than it.
-/

open Filter Topology Set MeasureTheory intervalIntegral

noncomputable section

namespace RHTower

variable {n : ℕ}

/-! ## The combination and its derivatives -/

/-- A linear combination of Hermite functions at the rungs `r`. -/
def hermiteCombo (r : Fin (n + 1) → ℕ) (a : Fin (n + 1) → ℝ) (ξ : ℝ) : ℝ :=
  ∑ i, a i * hermiteFun (r i) ξ

theorem hasDerivAt_hermiteCombo (r : Fin (n + 1) → ℕ) (a : Fin (n + 1) → ℝ) (ξ : ℝ) :
    HasDerivAt (hermiteCombo r a) (∑ i, a i * deriv (hermiteFun (r i)) ξ) ξ := by
  have h : HasDerivAt (∑ i : Fin (n + 1), fun y : ℝ => a i * hermiteFun (r i) y)
      (∑ i : Fin (n + 1), a i * deriv (hermiteFun (r i)) ξ) ξ :=
    HasDerivAt.sum fun i _ => HasDerivAt.const_mul (a i) (hasDerivAt_hermiteFun (r i) ξ)
  have hfun : (∑ i : Fin (n + 1), fun y : ℝ => a i * hermiteFun (r i) y) = hermiteCombo r a := by
    funext y
    simp [hermiteCombo, Finset.sum_apply]
  rwa [hfun] at h

theorem deriv_hermiteCombo (r : Fin (n + 1) → ℕ) (a : Fin (n + 1) → ℝ) :
    deriv (hermiteCombo r a) = fun ξ => ∑ i, a i * deriv (hermiteFun (r i)) ξ :=
  funext fun ξ => (hasDerivAt_hermiteCombo r a ξ).deriv

theorem hasDerivAt_deriv_hermiteCombo (r : Fin (n + 1) → ℕ) (a : Fin (n + 1) → ℝ) (ξ : ℝ) :
    HasDerivAt (deriv (hermiteCombo r a))
      (∑ i, a i * deriv (deriv (hermiteFun (r i))) ξ) ξ := by
  have h : HasDerivAt (∑ i : Fin (n + 1), fun y : ℝ => a i * deriv (hermiteFun (r i)) y)
      (∑ i : Fin (n + 1), a i * deriv (deriv (hermiteFun (r i))) ξ) ξ :=
    HasDerivAt.sum fun i _ =>
      HasDerivAt.const_mul (a i) (differentiable_deriv_hermiteFun (r i) ξ).hasDerivAt
  have hfun : (∑ i : Fin (n + 1), fun y : ℝ => a i * deriv (hermiteFun (r i)) y)
      = deriv (hermiteCombo r a) := by
    funext y
    rw [deriv_hermiteCombo]
    simp [Finset.sum_apply]
  rwa [hfun] at h

theorem deriv2_hermiteCombo (r : Fin (n + 1) → ℕ) (a : Fin (n + 1) → ℝ) (ξ : ℝ) :
    deriv (deriv (hermiteCombo r a)) ξ = ∑ i, a i * deriv (deriv (hermiteFun (r i))) ξ :=
  (hasDerivAt_deriv_hermiteCombo r a ξ).deriv

theorem continuous_deriv2_hermiteFun (m : ℕ) : Continuous (deriv (deriv (hermiteFun m))) := by
  have h : deriv (deriv (hermiteFun m)) = fun x : ℝ => (x ^ 2 - 2 * (m : ℝ) - 1) * hermiteFun m x :=
    funext (deriv2_hermiteFun m)
  rw [h]
  exact (((continuous_pow 2).sub continuous_const).sub continuous_const).mul
    (continuous_hermiteFun m)

theorem continuous_hermiteCombo (r : Fin (n + 1) → ℕ) (a : Fin (n + 1) → ℝ) :
    Continuous (hermiteCombo r a) :=
  continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_hermiteFun (r i))

theorem continuous_deriv_hermiteCombo (r : Fin (n + 1) → ℕ) (a : Fin (n + 1) → ℝ) :
    Continuous (deriv (hermiteCombo r a)) := by
  rw [deriv_hermiteCombo]
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_deriv_hermiteFun (r i))

theorem continuous_deriv2_hermiteCombo (r : Fin (n + 1) → ℕ) (a : Fin (n + 1) → ℝ) :
    Continuous (deriv (deriv (hermiteCombo r a))) := by
  have h : deriv (deriv (hermiteCombo r a))
      = fun ξ => ∑ i, a i * deriv (deriv (hermiteFun (r i))) ξ :=
    funext (deriv2_hermiteCombo r a)
  rw [h]
  exact continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_deriv2_hermiteFun (r i))

theorem differentiable_hermiteCombo (r : Fin (n + 1) → ℕ) (a : Fin (n + 1) → ℝ) :
    Differentiable ℝ (hermiteCombo r a) := fun ξ => (hasDerivAt_hermiteCombo r a ξ).differentiableAt

theorem hasDerivAt_hermiteCombo' (r : Fin (n + 1) → ℕ) (a : Fin (n + 1) → ℝ) (ξ : ℝ) :
    HasDerivAt (hermiteCombo r a) (deriv (hermiteCombo r a) ξ) ξ :=
  (differentiable_hermiteCombo r a ξ).hasDerivAt

theorem hasDerivAt_deriv_hermiteCombo' (r : Fin (n + 1) → ℕ) (a : Fin (n + 1) → ℝ) (ξ : ℝ) :
    HasDerivAt (deriv (hermiteCombo r a)) (deriv (deriv (hermiteCombo r a)) ξ) ξ := by
  rw [deriv2_hermiteCombo]
  exact hasDerivAt_deriv_hermiteCombo r a ξ

/-- **The oscillator action of a combination is the rung-weighted combination.** -/
theorem hermiteSLAction_hermiteCombo (r : Fin (n + 1) → ℕ) (a : Fin (n + 1) → ℝ) (ξ : ℝ) :
    hermiteSLAction (hermiteCombo r a) ξ
      = ∑ i, a i * (-(2 * (r i : ℝ) + 1)) * hermiteFun (r i) ξ := by
  rw [hermiteSLAction, deriv2_hermiteCombo, hermiteCombo, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [deriv2_hermiteFun]
  ring

/-! ## The defect of a combination is a square up to a boundary term -/

/-- **One integration by parts for a combination.**  The two correction terms of the scaled prolate
action are the two terms of `(ξ²ψ)′`, so pairing them with `ψ` gives a square. -/
theorem integral_comboDefect (r : Fin (n + 1) → ℕ) (a : Fin (n + 1) → ℝ) (R : ℝ) :
    (∫ ξ in (-R)..R, (-(ξ ^ 2 * deriv (deriv (hermiteCombo r a)) ξ)
        - 2 * ξ * deriv (hermiteCombo r a) ξ) * hermiteCombo r a ξ)
      = (∫ ξ in (-R)..R, ξ ^ 2 * deriv (hermiteCombo r a) ξ ^ 2)
        - (R ^ 2 * hermiteCombo r a R * deriv (hermiteCombo r a) R
            - (-R) ^ 2 * hermiteCombo r a (-R) * deriv (hermiteCombo r a) (-R)) := by
  set ψ : ℝ → ℝ := hermiteCombo r a with hψdef
  set u : ℝ → ℝ := fun ξ => ξ ^ 2 * ψ ξ with hu
  set u' : ℝ → ℝ := fun ξ => 2 * ξ * ψ ξ + ξ ^ 2 * deriv ψ ξ with hu'
  set v : ℝ → ℝ := deriv ψ with hv
  set v' : ℝ → ℝ := fun ξ => deriv (deriv ψ) ξ with hv'
  have hcψ : Continuous ψ := continuous_hermiteCombo r a
  have hcv : Continuous (deriv ψ) := continuous_deriv_hermiteCombo r a
  have hcv2 : Continuous (deriv (deriv ψ)) := continuous_deriv2_hermiteCombo r a
  have hud : ∀ ξ ∈ uIcc (-R) R, HasDerivAt u (u' ξ) ξ := by
    intro ξ _
    have h := (hasDerivAt_pow 2 ξ).mul (hasDerivAt_hermiteCombo' r a ξ)
    refine h.congr_deriv ?_
    simp only [hu']
    push_cast
    ring
  have hvd : ∀ ξ ∈ uIcc (-R) R, HasDerivAt v (v' ξ) ξ := fun ξ _ =>
    hasDerivAt_deriv_hermiteCombo' r a ξ
  have hu'i : IntervalIntegrable u' volume (-R) R := by
    refine Continuous.intervalIntegrable ?_ _ _
    exact ((continuous_const.mul continuous_id).mul hcψ).add ((continuous_pow 2).mul hcv)
  have hv'i : IntervalIntegrable v' volume (-R) R := hcv2.intervalIntegrable _ _
  have hparts := intervalIntegral.integral_mul_deriv_eq_deriv_mul hud hvd hu'i hv'i
  have hA : (∫ ξ in (-R)..R, ξ ^ 2 * deriv (deriv ψ) ξ * ψ ξ)
      = u R * v R - u (-R) * v (-R) - ∫ ξ in (-R)..R, u' ξ * v ξ := by
    rw [← hparts]
    refine intervalIntegral.integral_congr fun ξ _ => ?_
    simp only [hu, hv']
    ring
  have hrhs : (∫ ξ in (-R)..R, u' ξ * v ξ)
      = (∫ ξ in (-R)..R, 2 * ξ * deriv ψ ξ * ψ ξ)
        + ∫ ξ in (-R)..R, ξ ^ 2 * deriv ψ ξ ^ 2 := by
    rw [← intervalIntegral.integral_add]
    · refine intervalIntegral.integral_congr fun ξ _ => ?_
      simp only [hu', hv]
      ring
    · exact (((continuous_const.mul continuous_id).mul hcv).mul hcψ).intervalIntegrable _ _
    · exact ((continuous_pow 2).mul (hcv.pow 2)).intervalIntegrable _ _
  have hdef : (∫ ξ in (-R)..R, (-(ξ ^ 2 * deriv (deriv ψ) ξ) - 2 * ξ * deriv ψ ξ) * ψ ξ)
      = -(∫ ξ in (-R)..R, ξ ^ 2 * deriv (deriv ψ) ξ * ψ ξ)
        - ∫ ξ in (-R)..R, 2 * ξ * deriv ψ ξ * ψ ξ := by
    rw [← intervalIntegral.integral_neg, ← intervalIntegral.integral_sub]
    · refine intervalIntegral.integral_congr fun ξ _ => ?_
      ring
    · exact ((((continuous_pow 2).mul hcv2).mul hcψ).neg).intervalIntegrable _ _
    · exact (((continuous_const.mul continuous_id).mul hcv).mul hcψ).intervalIntegrable _ _
  rw [hdef, hA, hrhs]
  simp only [hu, hv]
  ring


/-! ## The exact Rayleigh excess in Hermite coordinates -/

/-- The excess integrand in the Hermite variable: the rung-gap term plus the defect term. -/
def comboExcessIntegrand (r : Fin (n + 1) → ℕ) (a : Fin (n + 1) → ℝ) (N : ℕ) (c ξ : ℝ) : ℝ :=
  c * ((∑ i, a i * (2 * ((N : ℝ) - (r i : ℝ))) * hermiteFun (r i) ξ) * hermiteCombo r a ξ)
    + (-(ξ ^ 2 * deriv (deriv (hermiteCombo r a)) ξ)
        - 2 * ξ * deriv (hermiteCombo r a) ξ) * hermiteCombo r a ξ

theorem continuous_comboExcessIntegrand (r : Fin (n + 1) → ℕ) (a : Fin (n + 1) → ℝ) (N : ℕ)
    (c : ℝ) : Continuous (comboExcessIntegrand r a N c) := by
  have h1 : Continuous fun ξ : ℝ => ∑ i, a i * (2 * ((N : ℝ) - (r i : ℝ))) * hermiteFun (r i) ξ :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_hermiteFun (r i))
  refine (continuous_const.mul (h1.mul (continuous_hermiteCombo r a))).add ?_
  refine Continuous.mul ?_ (continuous_hermiteCombo r a)
  exact (((continuous_pow 2).mul (continuous_deriv2_hermiteCombo r a)).neg).sub
    ((continuous_const.mul continuous_id).mul (continuous_deriv_hermiteCombo r a))

/-- **Pointwise form of the excess.**  Adding the top-rung ladder value to the scaled prolate
action collapses the rung weights to the gaps `2(N − rᵢ)`. -/
theorem comboExcess_pointwise {c : ℝ} (hc : 0 < c) (r : Fin (n + 1) → ℕ) (a : Fin (n + 1) → ℝ)
    (N : ℕ) (x : ℝ) :
    prolateSLAction c (fun y => hermiteCombo r a (Real.sqrt c * y)) x
        * hermiteCombo r a (Real.sqrt c * x)
      + (2 * (N : ℝ) + 1) * c *
        (hermiteCombo r a (Real.sqrt c * x) * hermiteCombo r a (Real.sqrt c * x))
      = comboExcessIntegrand r a N c (Real.sqrt c * x) := by
  have hs : Real.sqrt c ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hc)
  have hxx : Real.sqrt c * x / Real.sqrt c = x := by field_simp
  have h := prolateSLAction_sqrtScale hc (hermiteCombo r a) (Real.sqrt c * x)
  rw [hxx] at h
  set ξ : ℝ := Real.sqrt c * x with hξ
  have hP : hermiteCombo r a ξ = ∑ i, a i * hermiteFun (r i) ξ := rfl
  have hkey : (∑ i, a i * (-(2 * (r i : ℝ) + 1)) * hermiteFun (r i) ξ)
      + (2 * (N : ℝ) + 1) * hermiteCombo r a ξ
      = ∑ i, a i * (2 * ((N : ℝ) - (r i : ℝ))) * hermiteFun (r i) ξ := by
    rw [hP, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  rw [h, hermiteSLAction_hermiteCombo]
  simp only [comboExcessIntegrand]
  linear_combination (c * hermiteCombo r a ξ) * hkey

/-- The excess integral splits into the rung-gap Gram sum and the square-minus-boundary defect. -/
theorem integral_comboExcessIntegrand (r : Fin (n + 1) → ℕ) (a : Fin (n + 1) → ℝ) (N : ℕ)
    (c R : ℝ) :
    (∫ ξ in (-R)..R, comboExcessIntegrand r a N c ξ)
      = c * (∑ i, ∑ j, a i * a j * (2 * ((N : ℝ) - (r i : ℝ)))
              * ∫ ξ in (-R)..R, hermiteFun (r i) ξ * hermiteFun (r j) ξ)
        + ((∫ ξ in (-R)..R, ξ ^ 2 * deriv (hermiteCombo r a) ξ ^ 2)
            - (R ^ 2 * hermiteCombo r a R * deriv (hermiteCombo r a) R
                - (-R) ^ 2 * hermiteCombo r a (-R) * deriv (hermiteCombo r a) (-R))) := by
  have hgap : Continuous fun ξ : ℝ =>
      ∑ i, a i * (2 * ((N : ℝ) - (r i : ℝ))) * hermiteFun (r i) ξ :=
    continuous_finsetSum _ fun i _ => continuous_const.mul (continuous_hermiteFun (r i))
  have hdefc : Continuous fun ξ : ℝ => (-(ξ ^ 2 * deriv (deriv (hermiteCombo r a)) ξ)
      - 2 * ξ * deriv (hermiteCombo r a) ξ) * hermiteCombo r a ξ := by
    refine Continuous.mul ?_ (continuous_hermiteCombo r a)
    exact (((continuous_pow 2).mul (continuous_deriv2_hermiteCombo r a)).neg).sub
      ((continuous_const.mul continuous_id).mul (continuous_deriv_hermiteCombo r a))
  have hsplit : (∫ ξ in (-R)..R, comboExcessIntegrand r a N c ξ)
      = (∫ ξ in (-R)..R, c * ((∑ i, a i * (2 * ((N : ℝ) - (r i : ℝ))) * hermiteFun (r i) ξ)
            * hermiteCombo r a ξ))
        + ∫ ξ in (-R)..R, (-(ξ ^ 2 * deriv (deriv (hermiteCombo r a)) ξ)
            - 2 * ξ * deriv (hermiteCombo r a) ξ) * hermiteCombo r a ξ := by
    rw [← intervalIntegral.integral_add]
    · rfl
    · exact ((continuous_const.mul (hgap.mul (continuous_hermiteCombo r a)))).intervalIntegrable _ _
    · exact hdefc.intervalIntegrable _ _
  rw [hsplit, integral_comboDefect r a R, intervalIntegral.integral_const_mul]
  congr 1
  congr 1
  have hpt : ∀ ξ : ℝ, (∑ i, a i * (2 * ((N : ℝ) - (r i : ℝ))) * hermiteFun (r i) ξ)
      * hermiteCombo r a ξ
      = ∑ i, ∑ j, a i * a j * (2 * ((N : ℝ) - (r i : ℝ)))
          * (hermiteFun (r i) ξ * hermiteFun (r j) ξ) := by
    intro ξ
    rw [hermiteCombo, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [intervalIntegral.integral_congr (g := fun ξ => ∑ i, ∑ j,
    a i * a j * (2 * ((N : ℝ) - (r i : ℝ))) * (hermiteFun (r i) ξ * hermiteFun (r j) ξ))
    (fun ξ _ => hpt ξ)]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum]
    · refine Finset.sum_congr rfl fun j _ => ?_
      exact intervalIntegral.integral_const_mul _ _
    · exact fun j _ => (continuous_const.mul
        ((continuous_hermiteFun (r i)).mul (continuous_hermiteFun (r j)))).intervalIntegrable _ _
  · intro i _
    refine Continuous.intervalIntegrable ?_ _ _
    exact continuous_finsetSum _ fun j _ => continuous_const.mul
      ((continuous_hermiteFun (r i)).mul (continuous_hermiteFun (r j)))

/-- **The exact excess identity.**  Everything about the trial space is in the right-hand side:
a Gram sum weighted by the rung gaps, a square, and a boundary term. -/
theorem integral_comboExcess {c : ℝ} (hc : 0 < c) (r : Fin (n + 1) → ℕ) (a : Fin (n + 1) → ℝ)
    (N : ℕ) :
    (∫ x in (-1 : ℝ)..1, prolateSLAction c (fun y => hermiteCombo r a (Real.sqrt c * y)) x
        * hermiteCombo r a (Real.sqrt c * x))
      + (2 * (N : ℝ) + 1) * c *
        (∫ x in (-1 : ℝ)..1,
          hermiteCombo r a (Real.sqrt c * x) * hermiteCombo r a (Real.sqrt c * x))
      = (Real.sqrt c)⁻¹ *
        ((∫ ξ in (-Real.sqrt c)..(Real.sqrt c), comboExcessIntegrand r a N c ξ)) := by
  have hs : Real.sqrt c ≠ 0 := ne_of_gt (Real.sqrt_pos.2 hc)
  have hFc : Continuous fun x : ℝ => comboExcessIntegrand r a N c (Real.sqrt c * x) :=
    (continuous_comboExcessIntegrand r a N c).comp (continuous_const.mul continuous_id)
  have hKc : Continuous fun x : ℝ =>
      hermiteCombo r a (Real.sqrt c * x) * hermiteCombo r a (Real.sqrt c * x) :=
    (((continuous_hermiteCombo r a).comp (continuous_const.mul continuous_id)).mul
      ((continuous_hermiteCombo r a).comp (continuous_const.mul continuous_id)))
  have hA : (∫ x in (-1 : ℝ)..1,
        prolateSLAction c (fun y => hermiteCombo r a (Real.sqrt c * y)) x
          * hermiteCombo r a (Real.sqrt c * x))
      = ∫ x in (-1 : ℝ)..1, (comboExcessIntegrand r a N c (Real.sqrt c * x)
          - (2 * (N : ℝ) + 1) * c *
            (hermiteCombo r a (Real.sqrt c * x) * hermiteCombo r a (Real.sqrt c * x))) := by
    refine intervalIntegral.integral_congr fun x _ => ?_
    have h := comboExcess_pointwise hc r a N x
    linarith
  have hKc' : Continuous fun x : ℝ => (2 * (N : ℝ) + 1) * c *
      (hermiteCombo r a (Real.sqrt c * x) * hermiteCombo r a (Real.sqrt c * x)) :=
    continuous_const.mul hKc
  rw [hA, intervalIntegral.integral_sub (hFc.intervalIntegrable _ _)
      (hKc'.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, sub_add_cancel]
  have hsub := intervalIntegral.integral_comp_mul_left (a := (-1 : ℝ)) (b := 1)
    (fun ξ => comboExcessIntegrand r a N c ξ) hs
  rw [hsub, smul_eq_mul]
  norm_num

/-! ## The two vanishing errors -/

/-- The Hermite Wronskian dies faster than a square grows. -/
theorem tendsto_sq_mul_hermiteWronskian_atTop (m k : ℕ) :
    Tendsto (fun R : ℝ => R ^ 2 * hermiteWronskian m k R) atTop (𝓝 0) := by
  have h1 : Tendsto (fun R : ℝ => deriv (hermiteFun m) R * (R ^ 2 * hermiteFun k R))
      atTop (𝓝 0) := by
    simpa using (tendsto_deriv_hermiteFun_atTop m).mul (tendsto_sq_mul_hermiteFun_atTop k)
  have h2 : Tendsto (fun R : ℝ => R ^ 2 * hermiteFun m R * deriv (hermiteFun k) R)
      atTop (𝓝 0) := by
    simpa using (tendsto_sq_mul_hermiteFun_atTop m).mul (tendsto_deriv_hermiteFun_atTop k)
  have h := h1.sub h2
  rw [sub_zero] at h
  refine h.congr fun R => ?_
  rw [hermiteWronskian_eq]
  ring

theorem tendsto_sq_mul_hermiteWronskian_neg (m k : ℕ) :
    Tendsto (fun R : ℝ => R ^ 2 * hermiteWronskian m k (-R)) atTop (𝓝 0) := by
  have hneg : Tendsto (fun R : ℝ => -R) atTop atBot := tendsto_neg_atTop_atBot
  have h1 : Tendsto (fun R : ℝ => deriv (hermiteFun m) (-R) * ((-R) ^ 2 * hermiteFun k (-R)))
      atTop (𝓝 0) := by
    simpa using ((tendsto_deriv_hermiteFun_atBot m).comp hneg).mul
      ((tendsto_sq_mul_hermiteFun_atBot k).comp hneg)
  have h2 : Tendsto (fun R : ℝ => (-R) ^ 2 * hermiteFun m (-R) * deriv (hermiteFun k) (-R))
      atTop (𝓝 0) := by
    simpa using ((tendsto_sq_mul_hermiteFun_atBot m).comp hneg).mul
      ((tendsto_deriv_hermiteFun_atBot k).comp hneg)
  have h := h1.sub h2
  rw [sub_zero] at h
  refine h.congr fun R => ?_
  rw [hermiteWronskian_eq]
  ring

/-- **The bandwidth cannot rescue the off-diagonal overlap.**  Multiplying the truncated
orthogonality defect by the bandwidth still gives zero in the limit. -/
theorem tendsto_mul_integral_hermiteFun_mul {m k : ℕ} (hmk : m ≠ k) :
    Tendsto (fun c : ℝ => c *
        ∫ ξ in (-Real.sqrt c)..(Real.sqrt c), hermiteFun m ξ * hermiteFun k ξ) atTop (𝓝 0) := by
  have hbase : Tendsto (fun R : ℝ =>
      (R ^ 2 * hermiteWronskian m k R - R ^ 2 * hermiteWronskian m k (-R))
        / (2 * ((k : ℝ) - (m : ℝ)))) atTop (𝓝 0) := by
    have h := (tendsto_sq_mul_hermiteWronskian_atTop m k).sub
      (tendsto_sq_mul_hermiteWronskian_neg m k)
    rw [sub_zero] at h
    simpa using h.div_const (2 * ((k : ℝ) - (m : ℝ)))
  have h := hbase.comp Real.tendsto_sqrt_atTop
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop (0 : ℝ)] with c hc
  have hsq : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc
  simp only [Function.comp_apply, hsq]
  rw [integral_hermiteFun_mul_eq hmk]
  ring

/-- Off-diagonal Gram error of the trial family, already multiplied by the bandwidth. -/
def comboTailBound (r : Fin (n + 1) → ℕ) (N : ℕ) (c : ℝ) : ℝ :=
  ∑ i, ∑ j, (if i = j then (0 : ℝ) else
    2 * (N : ℝ) * |c * ∫ ξ in (-Real.sqrt c)..(Real.sqrt c),
        hermiteFun (r i) ξ * hermiteFun (r j) ξ|)

/-- Boundary error of the trial family, already multiplied by the bandwidth. -/
def comboBdryBound (r : Fin (n + 1) → ℕ) (c : ℝ) : ℝ :=
  ∑ i, ∑ j, (|c * (hermiteFun (r i) (Real.sqrt c) * deriv (hermiteFun (r j)) (Real.sqrt c))|
    + |c * (hermiteFun (r i) (-Real.sqrt c) * deriv (hermiteFun (r j)) (-Real.sqrt c))|)

theorem comboTailBound_nonneg (r : Fin (n + 1) → ℕ) (N : ℕ) (c : ℝ) :
    0 ≤ comboTailBound r N c := by
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  split_ifs with h
  · exact le_rfl
  · positivity

theorem comboBdryBound_nonneg (r : Fin (n + 1) → ℕ) (c : ℝ) : 0 ≤ comboBdryBound r c := by
  refine Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => ?_
  positivity

theorem tendsto_comboTailBound (r : Fin (n + 1) → ℕ) (hinj : Function.Injective r) (N : ℕ) :
    Tendsto (comboTailBound r N) atTop (𝓝 0) := by
  have hterm : ∀ i : Fin (n + 1), Tendsto (fun c : ℝ => ∑ j, (if i = j then (0 : ℝ) else
      2 * (N : ℝ) * |c * ∫ ξ in (-Real.sqrt c)..(Real.sqrt c),
        hermiteFun (r i) ξ * hermiteFun (r j) ξ|)) atTop (𝓝 0) := by
    intro i
    have h : ∀ j ∈ (Finset.univ : Finset (Fin (n + 1))),
        Tendsto (fun c : ℝ => (if i = j then (0 : ℝ) else
          2 * (N : ℝ) * |c * ∫ ξ in (-Real.sqrt c)..(Real.sqrt c),
            hermiteFun (r i) ξ * hermiteFun (r j) ξ|)) atTop (𝓝 0) := by
      intro j _
      by_cases hij : i = j
      · simp [hij]
      · have hrij : r i ≠ r j := fun h => hij (hinj h)
        have h0 := (tendsto_mul_integral_hermiteFun_mul hrij).abs
        rw [abs_zero] at h0
        have := h0.const_mul (2 * (N : ℝ))
        rw [mul_zero] at this
        simpa [hij] using this
    have h2 := tendsto_finsetSum (Finset.univ : Finset (Fin (n + 1))) h
    rwa [Finset.sum_const_zero] at h2
  have h3 := tendsto_finsetSum (Finset.univ : Finset (Fin (n + 1))) (fun i _ => hterm i)
  rw [Finset.sum_const_zero] at h3
  exact h3

theorem tendsto_comboBdryBound (r : Fin (n + 1) → ℕ) :
    Tendsto (comboBdryBound r) atTop (𝓝 0) := by
  have hterm : ∀ i j : Fin (n + 1),
      Tendsto (fun c : ℝ =>
        |c * (hermiteFun (r i) (Real.sqrt c) * deriv (hermiteFun (r j)) (Real.sqrt c))|
          + |c * (hermiteFun (r i) (-Real.sqrt c) * deriv (hermiteFun (r j)) (-Real.sqrt c))|)
        atTop (𝓝 0) := by
    intro i j
    have hsqrt : Tendsto (fun c : ℝ => Real.sqrt c) atTop atTop := Real.tendsto_sqrt_atTop
    have hA : Tendsto (fun R : ℝ =>
        R ^ 2 * hermiteFun (r i) R * deriv (hermiteFun (r j)) R) atTop (𝓝 0) := by
      simpa using (tendsto_sq_mul_hermiteFun_atTop (r i)).mul (tendsto_deriv_hermiteFun_atTop (r j))
    have hneg : Tendsto (fun R : ℝ => -R) atTop atBot := tendsto_neg_atTop_atBot
    have hB : Tendsto (fun R : ℝ =>
        (-R) ^ 2 * hermiteFun (r i) (-R) * deriv (hermiteFun (r j)) (-R)) atTop (𝓝 0) := by
      simpa using ((tendsto_sq_mul_hermiteFun_atBot (r i)).comp hneg).mul
        ((tendsto_deriv_hermiteFun_atBot (r j)).comp hneg)
    have hA' := (hA.comp hsqrt).abs
    have hB' := (hB.comp hsqrt).abs
    rw [abs_zero] at hA' hB'
    have hsum := hA'.add hB'
    rw [add_zero] at hsum
    refine hsum.congr' ?_
    filter_upwards [eventually_ge_atTop (0 : ℝ)] with c hc
    have hsq : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc
    have hsq' : (-Real.sqrt c) ^ 2 = c := by rw [neg_pow]; simp [hsq]
    simp only [Function.comp_apply]
    rw [hsq, hsq']
    ring_nf
  have hrow : ∀ i : Fin (n + 1), Tendsto (fun c : ℝ => ∑ j,
      (|c * (hermiteFun (r i) (Real.sqrt c) * deriv (hermiteFun (r j)) (Real.sqrt c))|
        + |c * (hermiteFun (r i) (-Real.sqrt c) * deriv (hermiteFun (r j)) (-Real.sqrt c))|))
      atTop (𝓝 0) := by
    intro i
    have h2 := tendsto_finsetSum (Finset.univ : Finset (Fin (n + 1)))
      (fun j (_ : j ∈ Finset.univ) => hterm i j)
    rwa [Finset.sum_const_zero] at h2
  have h3 := tendsto_finsetSum (Finset.univ : Finset (Fin (n + 1))) (fun i _ => hrow i)
  rw [Finset.sum_const_zero] at h3
  exact h3

/-! ## The fixed positive-definite lower form -/

/-- The bandwidth-free lower form of the trial space: rung gaps against a fixed window mass, plus
the window square of the derivative. -/
def comboLower (r : Fin (n + 1) → ℕ) (N : ℕ) (R₀ : ℝ) (a : Fin (n + 1) → ℝ) : ℝ :=
  (∑ i, a i ^ 2 * (2 * ((N : ℝ) - (r i : ℝ))) * ∫ ξ in (-R₀)..R₀, hermiteFun (r i) ξ ^ 2)
    + ∑ i, ∑ j, a i * a j *
        ∫ ξ in (-R₀)..R₀, ξ ^ 2 * (deriv (hermiteFun (r i)) ξ * deriv (hermiteFun (r j)) ξ)

/-- The second part of the lower form is the window square of the combination's derivative. -/
theorem comboLower_sq (r : Fin (n + 1) → ℕ) (a : Fin (n + 1) → ℝ) (R₀ : ℝ) :
    (∫ ξ in (-R₀)..R₀, ξ ^ 2 * deriv (hermiteCombo r a) ξ ^ 2)
      = ∑ i, ∑ j, a i * a j *
        ∫ ξ in (-R₀)..R₀, ξ ^ 2 * (deriv (hermiteFun (r i)) ξ * deriv (hermiteFun (r j)) ξ) := by
  have hpt : ∀ ξ : ℝ, ξ ^ 2 * deriv (hermiteCombo r a) ξ ^ 2
      = ∑ i, ∑ j, a i * a j *
          (ξ ^ 2 * (deriv (hermiteFun (r i)) ξ * deriv (hermiteFun (r j)) ξ)) := by
    intro ξ
    simp only [deriv_hermiteCombo]
    have hs : (∑ i, a i * deriv (hermiteFun (r i)) ξ) ^ 2
        = ∑ i, ∑ j, (a i * deriv (hermiteFun (r i)) ξ) * (a j * deriv (hermiteFun (r j)) ξ) := by
      rw [sq, Finset.sum_mul_sum]
    rw [hs, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [intervalIntegral.integral_congr (fun ξ _ => hpt ξ), intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [intervalIntegral.integral_finsetSum]
    · exact Finset.sum_congr rfl fun j _ => intervalIntegral.integral_const_mul _ _
    · exact fun j _ => (continuous_const.mul ((continuous_pow 2).mul
        ((continuous_deriv_hermiteFun (r i)).mul
          (continuous_deriv_hermiteFun (r j))))).intervalIntegrable _ _
  · intro i _
    exact (continuous_finsetSum _ fun j _ => continuous_const.mul ((continuous_pow 2).mul
      ((continuous_deriv_hermiteFun (r i)).mul
        (continuous_deriv_hermiteFun (r j))))).intervalIntegrable _ _

theorem comboLower_smul (r : Fin (n + 1) → ℕ) (N : ℕ) (R₀ t : ℝ) (a : Fin (n + 1) → ℝ) :
    comboLower r N R₀ (fun i => t * a i) = t ^ 2 * comboLower r N R₀ a := by
  simp only [comboLower]
  rw [mul_add, Finset.mul_sum, Finset.mul_sum]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by ring
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring

theorem comboLower_zero (r : Fin (n + 1) → ℕ) (N : ℕ) (R₀ : ℝ) :
    comboLower r N R₀ (0 : Fin (n + 1) → ℝ) = 0 := by
  simp [comboLower]

theorem continuous_comboLower (r : Fin (n + 1) → ℕ) (N : ℕ) (R₀ : ℝ) :
    Continuous (comboLower r N R₀) := by
  unfold comboLower
  refine Continuous.add ?_ ?_
  · exact continuous_finsetSum _ fun i _ =>
      (((continuous_apply i).pow 2).mul continuous_const).mul continuous_const
  · exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      ((continuous_apply i).mul (continuous_apply j)).mul continuous_const

theorem comboLower_fst_nonneg (r : Fin (n + 1) → ℕ) (ν : Fin (n + 1)) (hν : ∀ i, r i ≤ r ν)
    {R₀ : ℝ} (hR₀ : 0 < R₀) (a : Fin (n + 1) → ℝ) (i : Fin (n + 1)) :
    0 ≤ a i ^ 2 * (2 * ((r ν : ℝ) - (r i : ℝ))) * ∫ ξ in (-R₀)..R₀, hermiteFun (r i) ξ ^ 2 := by
  have hcast : (r i : ℝ) ≤ (r ν : ℝ) := by exact_mod_cast hν i
  have h2 : 0 ≤ ∫ ξ in (-R₀)..R₀, hermiteFun (r i) ξ ^ 2 :=
    le_of_lt (integral_hermiteFun_sq_pos (r i) (by linarith))
  exact mul_nonneg (mul_nonneg (sq_nonneg _) (by linarith)) h2

theorem comboLower_snd_nonneg (r : Fin (n + 1) → ℕ) (a : Fin (n + 1) → ℝ) {R₀ : ℝ}
    (hR₀ : 0 < R₀) :
    0 ≤ ∑ i, ∑ j, a i * a j *
      ∫ ξ in (-R₀)..R₀, ξ ^ 2 * (deriv (hermiteFun (r i)) ξ * deriv (hermiteFun (r j)) ξ) := by
  rw [← comboLower_sq]
  refine intervalIntegral.integral_nonneg (by linarith) fun u _ => by positivity

/-- **The lower form is positive definite.**  Either the combination puts weight below the top
rung — and then a rung gap contributes — or it sits on the top rung alone, where the derivative
square contributes. -/
theorem comboLower_pos (r : Fin (n + 1) → ℕ) (hinj : Function.Injective r) (ν : Fin (n + 1))
    (hν : ∀ i, r i ≤ r ν) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hsq : 0 < ∫ ξ in (-R₀)..R₀, ξ ^ 2 * deriv (hermiteFun (r ν)) ξ ^ 2)
    {a : Fin (n + 1) → ℝ} (ha : a ≠ 0) : 0 < comboLower r (r ν) R₀ a := by
  have hfst : 0 ≤ ∑ i, a i ^ 2 * (2 * ((r ν : ℝ) - (r i : ℝ)))
      * ∫ ξ in (-R₀)..R₀, hermiteFun (r i) ξ ^ 2 :=
    Finset.sum_nonneg fun i _ => comboLower_fst_nonneg r ν hν hR₀ a i
  have hsnd : 0 ≤ ∑ i, ∑ j, a i * a j *
      ∫ ξ in (-R₀)..R₀, ξ ^ 2 * (deriv (hermiteFun (r i)) ξ * deriv (hermiteFun (r j)) ξ) :=
    comboLower_snd_nonneg r a hR₀
  by_cases hcase : ∀ i, i ≠ ν → a i = 0
  · have haν : a ν ≠ 0 := by
      intro h
      refine ha (funext fun i => ?_)
      by_cases hi : i = ν
      · rw [hi]; exact h
      · exact hcase i hi
    have hderiv : ∀ ξ : ℝ, deriv (hermiteCombo r a) ξ = a ν * deriv (hermiteFun (r ν)) ξ := by
      intro ξ
      simp only [deriv_hermiteCombo]
      refine Finset.sum_eq_single ν (fun i _ hi => ?_) (fun h => absurd (Finset.mem_univ ν) h)
      rw [hcase i hi, zero_mul]
    have hs2 : (∑ i, ∑ j, a i * a j *
        ∫ ξ in (-R₀)..R₀, ξ ^ 2 * (deriv (hermiteFun (r i)) ξ * deriv (hermiteFun (r j)) ξ))
        = a ν ^ 2 * ∫ ξ in (-R₀)..R₀, ξ ^ 2 * deriv (hermiteFun (r ν)) ξ ^ 2 := by
      rw [← comboLower_sq, ← intervalIntegral.integral_const_mul]
      refine intervalIntegral.integral_congr fun ξ _ => ?_
      rw [hderiv ξ]
      ring
    have hpos : 0 < a ν ^ 2 * ∫ ξ in (-R₀)..R₀, ξ ^ 2 * deriv (hermiteFun (r ν)) ξ ^ 2 :=
      mul_pos (by positivity) hsq
    unfold comboLower
    rw [hs2]
    linarith
  · obtain ⟨i₀, hi₀ne, hi₀⟩ : ∃ i, i ≠ ν ∧ a i ≠ 0 := by
      by_contra hcon
      refine hcase fun i hi => ?_
      by_contra hne
      exact hcon ⟨i, hi, hne⟩
    have hlt : (r i₀ : ℝ) < (r ν : ℝ) := by
      have hle : r i₀ ≤ r ν := hν i₀
      have hne : r i₀ ≠ r ν := fun h => hi₀ne (hinj h)
      exact_mod_cast lt_of_le_of_ne hle hne
    have hterm : 0 < a i₀ ^ 2 * (2 * ((r ν : ℝ) - (r i₀ : ℝ)))
        * ∫ ξ in (-R₀)..R₀, hermiteFun (r i₀) ξ ^ 2 :=
      mul_pos (mul_pos (by positivity) (by linarith))
        (integral_hermiteFun_sq_pos (r i₀) (by linarith))
    have hle := Finset.single_le_sum
      (f := fun i => a i ^ 2 * (2 * ((r ν : ℝ) - (r i : ℝ)))
        * ∫ ξ in (-R₀)..R₀, hermiteFun (r i) ξ ^ 2)
      (fun i _ => comboLower_fst_nonneg r ν hν hR₀ a i) (Finset.mem_univ i₀)
    unfold comboLower
    linarith

/-- **The lower form is coercive.**  Compactness of the coefficient sphere turns pointwise
positivity into a uniform quadratic bound. -/
theorem exists_comboLower_bound (r : Fin (n + 1) → ℕ) (hinj : Function.Injective r)
    (ν : Fin (n + 1)) (hν : ∀ i, r i ≤ r ν) {R₀ : ℝ} (hR₀ : 0 < R₀)
    (hsq : 0 < ∫ ξ in (-R₀)..R₀, ξ ^ 2 * deriv (hermiteFun (r ν)) ξ ^ 2) :
    ∃ κ : ℝ, 0 < κ ∧ ∀ a : Fin (n + 1) → ℝ,
      κ * (∑ k, a k ^ 2) ≤ comboLower r (r ν) R₀ a := by
  classical
  set S : Set (Fin (n + 1) → ℝ) := {a | ∑ k, a k ^ 2 = 1} with hS
  have hsumcont : Continuous fun a : Fin (n + 1) → ℝ => ∑ k, a k ^ 2 :=
    continuous_finsetSum _ fun k _ => (continuous_apply k).pow 2
  have hclosed : IsClosed S := isClosed_eq hsumcont continuous_const
  have hbdd : Bornology.IsBounded S := by
    rw [isBounded_iff_forall_norm_le]
    refine ⟨1, fun a ha => ?_⟩
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have h1 : a i ^ 2 ≤ ∑ k, a k ^ 2 :=
      Finset.single_le_sum (fun k _ => sq_nonneg _) (Finset.mem_univ i)
    have h2 : a i ^ 2 ≤ 1 := by
      have : (∑ k, a k ^ 2) = 1 := ha
      linarith
    have : |a i| ≤ 1 := by nlinarith [abs_nonneg (a i), sq_abs (a i)]
    simpa [Real.norm_eq_abs] using this
  have hcomp : IsCompact S := Metric.isCompact_of_isClosed_isBounded hclosed hbdd
  have hne : S.Nonempty := by
    refine ⟨fun i => if i = 0 then (1 : ℝ) else 0, ?_⟩
    show ∑ k, (if k = (0 : Fin (n + 1)) then (1 : ℝ) else 0) ^ 2 = 1
    rw [Finset.sum_eq_single (0 : Fin (n + 1))]
    · simp
    · intro b _ hb; simp [hb]
    · intro h; exact absurd (Finset.mem_univ (0 : Fin (n + 1))) h
  obtain ⟨a₀, ha₀S, ha₀min⟩ := hcomp.exists_isMinOn hne
    (continuous_comboLower r (r ν) R₀).continuousOn
  have ha₀ne : a₀ ≠ 0 := by
    intro h
    have : (∑ k, a₀ k ^ 2) = 1 := ha₀S
    rw [h] at this
    simp at this
  refine ⟨comboLower r (r ν) R₀ a₀, comboLower_pos r hinj ν hν hR₀ hsq ha₀ne, fun a => ?_⟩
  by_cases ha : a = 0
  · rw [ha, comboLower_zero]
    simp
  · have hpos : 0 < ∑ k, a k ^ 2 := by
      rcases lt_or_eq_of_le (Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => sq_nonneg (a k))
        with h | h
      · exact h
      · exfalso
        refine ha (funext fun i => ?_)
        have hzero : ∀ k ∈ (Finset.univ : Finset (Fin (n + 1))), a k ^ 2 = 0 :=
          (Finset.sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg (a k)).1 h.symm
        have := hzero i (Finset.mem_univ i)
        simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.1 this
    set t : ℝ := Real.sqrt (∑ k, a k ^ 2) with ht
    have htpos : 0 < t := Real.sqrt_pos.2 hpos
    have ht2 : t ^ 2 = ∑ k, a k ^ 2 := Real.sq_sqrt (le_of_lt hpos)
    set b : Fin (n + 1) → ℝ := fun i => t⁻¹ * a i with hb
    have hbS : b ∈ S := by
      show ∑ k, (t⁻¹ * a k) ^ 2 = 1
      have : ∑ k, (t⁻¹ * a k) ^ 2 = t⁻¹ ^ 2 * ∑ k, a k ^ 2 := by
        rw [Finset.mul_sum]
        exact Finset.sum_congr rfl fun k _ => by ring
      rw [this, ← ht2]
      field_simp
    have hab : (fun i => t * b i) = a := by
      funext i
      simp only [hb]
      field_simp
    have hkey : comboLower r (r ν) R₀ a = t ^ 2 * comboLower r (r ν) R₀ b := by
      rw [← hab, comboLower_smul]
    rw [hkey, ← ht2]
    have := (isMinOn_iff.1 ha₀min) b hbS
    have ht2pos : (0 : ℝ) < t ^ 2 := by positivity
    calc comboLower r (r ν) R₀ a₀ * t ^ 2 ≤ comboLower r (r ν) R₀ b * t ^ 2 := by nlinarith
      _ = t ^ 2 * comboLower r (r ν) R₀ b := by ring

/-! ## The two error bounds -/

theorem abs_mul_le_sum_sq (a : Fin (n + 1) → ℝ) (i j : Fin (n + 1)) :
    |a i * a j| ≤ ∑ k, a k ^ 2 := by
  have h1 : |a i * a j| ≤ (a i ^ 2 + a j ^ 2) / 2 := by
    rw [abs_mul]
    nlinarith [sq_nonneg (|a i| - |a j|), abs_nonneg (a i), abs_nonneg (a j),
      sq_abs (a i), sq_abs (a j)]
  have h2 : a i ^ 2 ≤ ∑ k, a k ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (a k)) (Finset.mem_univ i)
  have h3 : a j ^ 2 ≤ ∑ k, a k ^ 2 :=
    Finset.single_le_sum (fun k _ => sq_nonneg (a k)) (Finset.mem_univ j)
  linarith

theorem sum_sub_diag (f : Fin (n + 1) → Fin (n + 1) → ℝ) :
    (∑ i, ∑ j, f i j) - (∑ i, f i i) = ∑ i, ∑ j, (if i = j then (0 : ℝ) else f i j) := by
  classical
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h1 : (∑ j, (if i = j then f i j else (0 : ℝ))) = f i i := by
    rw [Finset.sum_ite_eq]
    simp
  have h2 : (∑ j, (if i = j then (0 : ℝ) else f i j))
      + (∑ j, (if i = j then f i j else (0 : ℝ))) = ∑ j, f i j := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by split_ifs <;> ring
  rw [h1] at h2
  linarith

/-- **The off-diagonal Gram mass is inside the tail error.** -/
theorem comboOffDiag_bound (r : Fin (n + 1) → ℕ) (ν : Fin (n + 1)) (hν : ∀ i, r i ≤ r ν)
    (c : ℝ) (a : Fin (n + 1) → ℝ) :
    |c * (∑ i, ∑ j, a i * a j * (2 * ((r ν : ℝ) - (r i : ℝ)))
          * ∫ ξ in (-Real.sqrt c)..(Real.sqrt c), hermiteFun (r i) ξ * hermiteFun (r j) ξ)
        - c * (∑ i, a i * a i * (2 * ((r ν : ℝ) - (r i : ℝ)))
          * ∫ ξ in (-Real.sqrt c)..(Real.sqrt c), hermiteFun (r i) ξ * hermiteFun (r i) ξ)|
      ≤ comboTailBound r (r ν) c * (∑ k, a k ^ 2) := by
  classical
  set f : Fin (n + 1) → Fin (n + 1) → ℝ := fun i j => a i * a j * (2 * ((r ν : ℝ) - (r i : ℝ)))
    * ∫ ξ in (-Real.sqrt c)..(Real.sqrt c), hermiteFun (r i) ξ * hermiteFun (r j) ξ with hf
  have hsplit : c * (∑ i, ∑ j, f i j) - c * (∑ i, f i i)
      = ∑ i, ∑ j, (if i = j then (0 : ℝ) else c * f i j) := by
    rw [← mul_sub, sum_sub_diag f, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by split_ifs <;> ring
  rw [hsplit]
  calc |∑ i, ∑ j, (if i = j then (0 : ℝ) else c * f i j)|
      ≤ ∑ i, |∑ j, (if i = j then (0 : ℝ) else c * f i j)| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, (if i = j then (0 : ℝ) else
          2 * ((r ν : ℕ) : ℝ) * |c * ∫ ξ in (-Real.sqrt c)..(Real.sqrt c),
            hermiteFun (r i) ξ * hermiteFun (r j) ξ|) * (∑ k, a k ^ 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        refine Finset.sum_le_sum fun j _ => ?_
        by_cases hij : i = j
        · simp [hij]
        · have hw1 : (0 : ℝ) ≤ 2 * ((r ν : ℝ) - (r i : ℝ)) := by
            have : (r i : ℝ) ≤ (r ν : ℝ) := by exact_mod_cast hν i
            linarith
          have hw2 : 2 * ((r ν : ℝ) - (r i : ℝ)) ≤ 2 * (r ν : ℝ) := by
            have : (0 : ℝ) ≤ (r i : ℝ) := Nat.cast_nonneg _
            linarith
          have hI : (0 : ℝ) ≤ |c * ∫ ξ in (-Real.sqrt c)..(Real.sqrt c),
              hermiteFun (r i) ξ * hermiteFun (r j) ξ| := abs_nonneg _
          have hS : (0 : ℝ) ≤ ∑ k, a k ^ 2 := Finset.sum_nonneg fun k _ => sq_nonneg (a k)
          have hA := abs_mul_le_sum_sq a i j
          have habs : |c * f i j| = |a i * a j| * (2 * ((r ν : ℝ) - (r i : ℝ)))
              * |c * ∫ ξ in (-Real.sqrt c)..(Real.sqrt c),
                  hermiteFun (r i) ξ * hermiteFun (r j) ξ| := by
            simp only [hf]
            rw [show c * (a i * a j * (2 * ((r ν : ℝ) - (r i : ℝ)))
                * ∫ ξ in (-Real.sqrt c)..(Real.sqrt c), hermiteFun (r i) ξ * hermiteFun (r j) ξ)
                = (a i * a j) * (2 * ((r ν : ℝ) - (r i : ℝ)))
                  * (c * ∫ ξ in (-Real.sqrt c)..(Real.sqrt c),
                      hermiteFun (r i) ξ * hermiteFun (r j) ξ) from by ring]
            rw [abs_mul, abs_mul, abs_of_nonneg hw1]
          have e1 : |a i * a j| * (2 * ((r ν : ℝ) - (r i : ℝ)))
                * |c * ∫ ξ in (-Real.sqrt c)..(Real.sqrt c),
                    hermiteFun (r i) ξ * hermiteFun (r j) ξ|
              ≤ (∑ k, a k ^ 2) * (2 * ((r ν : ℝ) - (r i : ℝ)))
                * |c * ∫ ξ in (-Real.sqrt c)..(Real.sqrt c),
                    hermiteFun (r i) ξ * hermiteFun (r j) ξ| :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hA hw1) hI
          have e2 := mul_nonneg (mul_nonneg hS hI) (sub_nonneg.2 hw2)
          simp only [hij, if_false]
          rw [habs]
          nlinarith [e1, e2]
    _ = comboTailBound r (r ν) c * (∑ k, a k ^ 2) := by
        rw [comboTailBound, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]

/-- **The boundary mass is inside the boundary error.** -/
theorem comboBdry_bound (r : Fin (n + 1) → ℕ) (a : Fin (n + 1) → ℝ) (c : ℝ) :
    |c * (hermiteCombo r a (Real.sqrt c) * deriv (hermiteCombo r a) (Real.sqrt c))
        - c * (hermiteCombo r a (-Real.sqrt c) * deriv (hermiteCombo r a) (-Real.sqrt c))|
      ≤ comboBdryBound r c * (∑ k, a k ^ 2) := by
  have hprod : ∀ x : ℝ, hermiteCombo r a x * deriv (hermiteCombo r a) x
      = ∑ i, ∑ j, a i * a j * (hermiteFun (r i) x * deriv (hermiteFun (r j)) x) := by
    intro x
    simp only [hermiteCombo, deriv_hermiteCombo]
    rw [Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hprod, hprod]
  have hsplit : (c * ∑ i, ∑ j, a i * a j *
        (hermiteFun (r i) (Real.sqrt c) * deriv (hermiteFun (r j)) (Real.sqrt c)))
      - (c * ∑ i, ∑ j, a i * a j *
        (hermiteFun (r i) (-Real.sqrt c) * deriv (hermiteFun (r j)) (-Real.sqrt c)))
      = ∑ i, ∑ j, (a i * a j * (c * (hermiteFun (r i) (Real.sqrt c)
            * deriv (hermiteFun (r j)) (Real.sqrt c)))
          - a i * a j * (c * (hermiteFun (r i) (-Real.sqrt c)
            * deriv (hermiteFun (r j)) (-Real.sqrt c)))) := by
    rw [← mul_sub, ← Finset.sum_sub_distrib, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hsplit]
  calc |∑ i, ∑ j, (a i * a j * (c * (hermiteFun (r i) (Real.sqrt c)
            * deriv (hermiteFun (r j)) (Real.sqrt c)))
          - a i * a j * (c * (hermiteFun (r i) (-Real.sqrt c)
            * deriv (hermiteFun (r j)) (-Real.sqrt c))))|
      ≤ ∑ i, |∑ j, (a i * a j * (c * (hermiteFun (r i) (Real.sqrt c)
            * deriv (hermiteFun (r j)) (Real.sqrt c)))
          - a i * a j * (c * (hermiteFun (r i) (-Real.sqrt c)
            * deriv (hermiteFun (r j)) (-Real.sqrt c))))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i, ∑ j, (|c * (hermiteFun (r i) (Real.sqrt c)
            * deriv (hermiteFun (r j)) (Real.sqrt c))|
          + |c * (hermiteFun (r i) (-Real.sqrt c)
            * deriv (hermiteFun (r j)) (-Real.sqrt c))|) * (∑ k, a k ^ 2) := by
        refine Finset.sum_le_sum fun i _ => ?_
        refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
        refine Finset.sum_le_sum fun j _ => ?_
        have hA := abs_mul_le_sum_sq a i j
        have h1 : (0 : ℝ) ≤ |c * (hermiteFun (r i) (Real.sqrt c)
            * deriv (hermiteFun (r j)) (Real.sqrt c))| := abs_nonneg _
        have h2 : (0 : ℝ) ≤ |c * (hermiteFun (r i) (-Real.sqrt c)
            * deriv (hermiteFun (r j)) (-Real.sqrt c))| := abs_nonneg _
        refine le_trans (abs_sub _ _) ?_
        have hm1 : |a i * a j * (c * (hermiteFun (r i) (Real.sqrt c)
            * deriv (hermiteFun (r j)) (Real.sqrt c)))|
            = |a i * a j| * |c * (hermiteFun (r i) (Real.sqrt c)
                * deriv (hermiteFun (r j)) (Real.sqrt c))| := abs_mul _ _
        have hm2 : |a i * a j * (c * (hermiteFun (r i) (-Real.sqrt c)
            * deriv (hermiteFun (r j)) (-Real.sqrt c)))|
            = |a i * a j| * |c * (hermiteFun (r i) (-Real.sqrt c)
                * deriv (hermiteFun (r j)) (-Real.sqrt c))| := abs_mul _ _
        rw [hm1, hm2]
        have e1 := mul_le_mul_of_nonneg_right hA h1
        have e2 := mul_le_mul_of_nonneg_right hA h2
        nlinarith [e1, e2]
    _ = comboBdryBound r c * (∑ k, a k ^ 2) := by
        rw [comboBdryBound, Finset.sum_mul]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.sum_mul]

/-! ## The trial-space Rayleigh bound -/

theorem sum_sq_pos_of_ne_zero {a : Fin (n + 1) → ℝ} (ha : a ≠ 0) : 0 < ∑ k, a k ^ 2 := by
  rcases lt_or_eq_of_le (Finset.sum_nonneg fun k (_ : k ∈ Finset.univ) => sq_nonneg (a k))
    with h | h
  · exact h
  · exfalso
    refine ha (funext fun i => ?_)
    have hzero : ∀ k ∈ (Finset.univ : Finset (Fin (n + 1))), a k ^ 2 = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg fun k _ => sq_nonneg (a k)).1 h.symm
    have hk := hzero i (Finset.mem_univ i)
    simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.1 hk

/-- **The excess dominates the fixed lower form minus the two errors.** -/
theorem comboExcess_lower_bound (r : Fin (n + 1) → ℕ) (ν : Fin (n + 1)) (hν : ∀ i, r i ≤ r ν)
    {R₀ c : ℝ} (hR₀ : 0 < R₀) (hc1 : 1 ≤ c) (hcR : R₀ ≤ Real.sqrt c) (a : Fin (n + 1) → ℝ) :
    comboLower r (r ν) R₀ a
        - (comboTailBound r (r ν) c + comboBdryBound r c) * (∑ k, a k ^ 2)
      ≤ ∫ ξ in (-Real.sqrt c)..(Real.sqrt c), comboExcessIntegrand r a (r ν) c ξ := by
  have hc0 : (0 : ℝ) ≤ c := by linarith
  have hRsq : Real.sqrt c ^ 2 = c := Real.sq_sqrt hc0
  have hRsq' : (-Real.sqrt c) ^ 2 = c := by rw [neg_pow]; simp [hRsq]
  have hR₀le : -R₀ ≤ R₀ := by linarith
  have hdiag : (∑ i, a i ^ 2 * (2 * ((r ν : ℝ) - (r i : ℝ)))
        * ∫ ξ in (-R₀)..R₀, hermiteFun (r i) ξ ^ 2)
      ≤ c * (∑ i, a i * a i * (2 * ((r ν : ℝ) - (r i : ℝ)))
          * ∫ ξ in (-Real.sqrt c)..(Real.sqrt c),
              hermiteFun (r i) ξ * hermiteFun (r i) ξ) := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    have hW : (0 : ℝ) ≤ 2 * ((r ν : ℝ) - (r i : ℝ)) := by
      have : (r i : ℝ) ≤ (r ν : ℝ) := by exact_mod_cast hν i
      linarith
    have hcongr : (∫ ξ in (-Real.sqrt c)..(Real.sqrt c),
        hermiteFun (r i) ξ * hermiteFun (r i) ξ)
        = ∫ ξ in (-Real.sqrt c)..(Real.sqrt c), hermiteFun (r i) ξ ^ 2 :=
      intervalIntegral.integral_congr fun ξ _ => by ring
    have hmono : (∫ ξ in (-R₀)..R₀, hermiteFun (r i) ξ ^ 2)
        ≤ ∫ ξ in (-Real.sqrt c)..(Real.sqrt c), hermiteFun (r i) ξ ^ 2 := by
      refine intervalIntegral.integral_mono_interval (by linarith) hR₀le hcR ?_ ?_
      · filter_upwards with x
        positivity
      · exact ((continuous_hermiteFun (r i)).pow 2).intervalIntegrable _ _
    have hnn : 0 ≤ ∫ ξ in (-R₀)..R₀, hermiteFun (r i) ξ ^ 2 :=
      le_of_lt (integral_hermiteFun_sq_pos (r i) (by linarith))
    have hF : (0 : ℝ) ≤ a i ^ 2 * (2 * ((r ν : ℝ) - (r i : ℝ))) := mul_nonneg (sq_nonneg _) hW
    have e1 := mul_le_mul_of_nonneg_left hmono hF
    have e2 := mul_nonneg (by linarith : (0 : ℝ) ≤ c - 1)
      (mul_nonneg hF (le_trans hnn hmono))
    rw [hcongr]
    nlinarith [e1, e2]
  have hsqmono : (∑ i, ∑ j, a i * a j *
        ∫ ξ in (-R₀)..R₀, ξ ^ 2 * (deriv (hermiteFun (r i)) ξ * deriv (hermiteFun (r j)) ξ))
      ≤ ∫ ξ in (-Real.sqrt c)..(Real.sqrt c), ξ ^ 2 * deriv (hermiteCombo r a) ξ ^ 2 := by
    rw [← comboLower_sq]
    refine intervalIntegral.integral_mono_interval (by linarith) hR₀le hcR ?_ ?_
    · filter_upwards with x
      positivity
    · exact ((continuous_pow 2).mul
        ((continuous_deriv_hermiteCombo r a).pow 2)).intervalIntegrable _ _
  have hbdryeq : (Real.sqrt c ^ 2 * hermiteCombo r a (Real.sqrt c)
        * deriv (hermiteCombo r a) (Real.sqrt c)
      - (-Real.sqrt c) ^ 2 * hermiteCombo r a (-Real.sqrt c)
        * deriv (hermiteCombo r a) (-Real.sqrt c))
      = c * (hermiteCombo r a (Real.sqrt c) * deriv (hermiteCombo r a) (Real.sqrt c))
        - c * (hermiteCombo r a (-Real.sqrt c)
          * deriv (hermiteCombo r a) (-Real.sqrt c)) := by
    rw [hRsq, hRsq']
    ring
  have hoff := abs_le.1 (comboOffDiag_bound r ν hν c a)
  have hb := abs_le.1 (comboBdry_bound r a c)
  rw [integral_comboExcessIntegrand, hbdryeq]
  unfold comboLower
  linarith [hoff.1, hoff.2, hb.1, hb.2, hdiag, hsqmono]

/-- **The rung-family trial space beats the top-rung ladder value.**  For all large bandwidths,
*every* nonzero combination of the trial functions at the rungs `r` has prolate Rayleigh quotient
strictly above `−(2·r ν + 1)·c`, the oscillator value of the top rung. -/
theorem eventually_hermiteTrial_combination_rayleigh_gt (r : Fin (n + 1) → ℕ)
    (hinj : Function.Injective r) (ν : Fin (n + 1)) (hν : ∀ i, r i ≤ r ν) :
    ∀ᶠ c in atTop, ∀ a : Fin (n + 1) → ℝ, a ≠ 0 →
      -((2 * (r ν : ℝ) + 1) * c) *
          (∫ x in (-1 : ℝ)..1, (∑ i, a i * hermiteTrial c (r i) x)
              * (∑ i, a i * hermiteTrial c (r i) x))
        < ∫ x in (-1 : ℝ)..1,
            prolateSLAction c (fun y => ∑ i, a i * hermiteTrial c (r i) y) x
              * (∑ i, a i * hermiteTrial c (r i) x) := by
  obtain ⟨p, q, hpq, hposwin⟩ := exists_pos_window_integral (r ν)
  set R₀ : ℝ := |p| + |q| + 1 with hR₀def
  have hR₀ : 0 < R₀ := by
    have := abs_nonneg p
    have := abs_nonneg q
    simp only [hR₀def]
    linarith
  have hp : -R₀ ≤ p := by
    have h1 := neg_abs_le p
    have h2 := abs_nonneg q
    simp only [hR₀def]
    linarith
  have hq : q ≤ R₀ := by
    have h1 := le_abs_self q
    have h2 := abs_nonneg p
    simp only [hR₀def]
    linarith
  have hsq : 0 < ∫ ξ in (-R₀)..R₀, ξ ^ 2 * deriv (hermiteFun (r ν)) ξ ^ 2 := by
    refine lt_of_lt_of_le hposwin ?_
    refine intervalIntegral.integral_mono_interval hp hpq.le hq ?_ ?_
    · filter_upwards with x
      positivity
    · exact (continuous_hermiteRungSquare (r ν)).intervalIntegrable _ _
  obtain ⟨κ, hκ, hκle⟩ := exists_comboLower_bound r hinj ν hν hR₀ hsq
  have hsum := (tendsto_comboTailBound r hinj (r ν)).add (tendsto_comboBdryBound r)
  rw [add_zero] at hsum
  have hev := hsum.eventually_lt_const hκ
  filter_upwards [hev, Real.tendsto_sqrt_atTop.eventually_ge_atTop R₀,
    eventually_ge_atTop (1 : ℝ)] with c hcerr hcR hc1
  intro a ha
  have hc : 0 < c := by linarith
  have hfun : ∀ y : ℝ, (∑ i, a i * hermiteTrial c (r i) y)
      = hermiteCombo r a (Real.sqrt c * y) := fun _ => rfl
  simp only [hfun]
  have hkey := integral_comboExcess hc r a (r ν)
  have hlow := comboExcess_lower_bound r ν hν hR₀ hc1 hcR a
  have hS := sum_sq_pos_of_ne_zero ha
  have hcoerc := hκle a
  have hgap : 0 < (κ - (comboTailBound r (r ν) c + comboBdryBound r c)) * (∑ k, a k ^ 2) :=
    mul_pos (by linarith) hS
  have hpos : 0 < ∫ ξ in (-Real.sqrt c)..(Real.sqrt c),
      comboExcessIntegrand r a (r ν) c ξ := by nlinarith [hlow, hcoerc, hgap]
  have hRinv : 0 < (Real.sqrt c)⁻¹ := inv_pos.2 (Real.sqrt_pos.2 hc)
  have hfinal : 0 < (Real.sqrt c)⁻¹ *
      ∫ ξ in (-Real.sqrt c)..(Real.sqrt c), comboExcessIntegrand r a (r ν) c ξ :=
    mul_pos hRinv hpos
  rw [← hkey] at hfinal
  linarith

/-! ## Excited modes above the top-rung ladder value -/

theorem contDiff_hermiteTrial (c : ℝ) (m : ℕ) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (hermiteTrial c m) :=
  (contDiff_hermiteFun m).comp (contDiff_const.mul contDiff_id)

theorem even_hermiteTrial {c : ℝ} {m : ℕ} (hm : Even m) : Function.Even (hermiteTrial c m) := by
  intro x
  show hermiteFun m (Real.sqrt c * -x) = hermiteFun m (Real.sqrt c * x)
  rw [show Real.sqrt c * -x = -(Real.sqrt c * x) from by ring]
  exact even_hermiteFun hm _

/-- **The excited ladder is populated.**  For all large bandwidths there are `n+1` linearly
independent even joint band/prolate modes whose separation constants all exceed the oscillator
value of the top rung of any prescribed family of even rungs. -/
theorem eventually_exists_highModeClasses_hermiteRungs (r : Fin (n + 1) → ℕ)
    (hinj : Function.Injective r) (ν : Fin (n + 1)) (hν : ∀ i, r i ≤ r ν)
    (heven : ∀ i, Even (r i)) :
    ∀ᶠ c in atTop, ∃ w : Fin (n + 1) → GaloisForLFunctions.RHTower.RealIntervalL2 (-1 : ℝ) 1,
      LinearIndependent ℝ w ∧ ∀ i, IsHighModeClass c ((2 * (r ν : ℝ) + 1) * c) (w i) := by
  filter_upwards [eventually_hermiteTrial_combination_rayleigh_gt r hinj ν hν,
    eventually_gt_atTop (0 : ℝ)] with c hray hc
  exact exists_linearIndependent_highModeClasses hc n (fun i => hermiteTrial c (r i))
    (fun i => contDiff_hermiteTrial c (r i)) (fun i => even_hermiteTrial (heven i)) hray

end RHTower

end
