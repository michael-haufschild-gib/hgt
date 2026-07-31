import GaloisForLFunctions.HTGeometry.ExponentialCharacter

/-!
# A continuous character of the line is differentiable

Averaging removes the differentiability hypothesis from the classification of one-parameter
characters.  If `f` is continuous and multiplicative with `f 0 = 1`, then its primitive
`F a = ∫ t in 0..a, f t` has derivative `f` everywhere, and `F` cannot vanish identically because
its derivative at the origin is `1`.  Choosing `a` with `A = F a ≠ 0` and using multiplicativity,

`A · f s = ∫ t in 0..a, f (s + t) = F (s + a) - F s`,

which exhibits `f` as a difference of translates of a differentiable function.  Continuity alone
therefore forces differentiability, and with it the exponential form of the character.
-/

namespace GaloisForLFunctions.HTGeometry

open intervalIntegral MeasureTheory

variable {f : ℝ → ℂ}

/-- The primitive of a continuous function is differentiable with the function as derivative. -/
theorem hasDerivAt_charPrimitive (hf : Continuous f) (b : ℝ) :
    HasDerivAt (fun u : ℝ => ∫ t in (0 : ℝ)..u, f t) (f b) b :=
  (hf.integral_hasStrictDerivAt 0 b).hasDerivAt

/-- The primitive of a continuous character does not vanish identically. -/
theorem exists_charPrimitive_ne_zero (hf : Continuous f) (h0 : f 0 = 1) :
    ∃ a : ℝ, (∫ t in (0 : ℝ)..a, f t) ≠ 0 := by
  by_contra hall
  push Not at hall
  have hconst : (fun u : ℝ => ∫ t in (0 : ℝ)..u, f t) = fun _ : ℝ => (0 : ℂ) := funext hall
  have hzero : HasDerivAt (fun u : ℝ => ∫ t in (0 : ℝ)..u, f t) 0 0 := by
    rw [hconst]
    exact hasDerivAt_const 0 0
  have huniq := hzero.unique (hasDerivAt_charPrimitive hf 0)
  rw [h0] at huniq
  exact one_ne_zero huniq.symm

/-- **Averaging identity.**  Multiplicativity turns the primitive into a translation formula. -/
theorem charPrimitive_smul_eq (hf : Continuous f)
    (hmul : ∀ s t : ℝ, f (s + t) = f s * f t) (a s : ℝ) :
    (∫ t in (0 : ℝ)..a, f t) * f s =
      (∫ t in (0 : ℝ)..(s + a), f t) - ∫ t in (0 : ℝ)..s, f t := by
  have hsplit : (∫ t in (0 : ℝ)..s, f t) + (∫ t in s..(s + a), f t)
      = ∫ t in (0 : ℝ)..(s + a), f t :=
    integral_add_adjacent_intervals (hf.intervalIntegrable _ _) (hf.intervalIntegrable _ _)
  have hshift : (∫ t in (0 : ℝ)..a, f (s + t)) = ∫ t in s..(s + a), f t := by
    simp
  have hfac : (∫ t in (0 : ℝ)..a, f (s + t)) = f s * ∫ t in (0 : ℝ)..a, f t := by
    rw [← intervalIntegral.integral_const_mul]
    exact integral_congr fun t _ => hmul s t
  rw [← hsplit, ← hshift, hfac]
  ring

/-- **A continuous character is differentiable.**  Hence continuity alone suffices in the
classification of one-parameter characters. -/
theorem exists_hasDerivAt_of_continuous_character (hf : Continuous f)
    (hmul : ∀ s t : ℝ, f (s + t) = f s * f t) (h0 : f 0 = 1) :
    ∃ c : ℂ, HasDerivAt f c 0 := by
  obtain ⟨a, ha⟩ := exists_charPrimitive_ne_zero hf h0
  set A : ℂ := ∫ t in (0 : ℝ)..a, f t with hA
  set F : ℝ → ℂ := fun u => ∫ t in (0 : ℝ)..u, f t with hF
  have hFderiv : ∀ b : ℝ, HasDerivAt F (f b) b := hasDerivAt_charPrimitive hf
  have hrepr : ∀ s : ℝ, f s = A⁻¹ * (F (s + a) - F s) := by
    intro s
    have h := charPrimitive_smul_eq hf hmul a s
    field_simp [hA, hF] at h ⊢
    linear_combination h
  have hshiftDeriv : HasDerivAt (fun s : ℝ => F (s + a)) (f (0 + a)) 0 :=
    (hFderiv (0 + a)).comp_add_const 0 a
  have hdiff : HasDerivAt (fun s : ℝ => A⁻¹ * (F (s + a) - F s))
      (A⁻¹ * (f (0 + a) - f 0)) 0 :=
    ((hshiftDeriv.sub (hFderiv 0)).const_mul A⁻¹)
  refine ⟨A⁻¹ * (f (0 + a) - f 0), ?_⟩
  refine hdiff.congr_of_eventuallyEq ?_
  exact Filter.Eventually.of_forall fun s => hrepr s

/-- **Classification of continuous unimodular characters of the line.**  A continuous
multiplicative unimodular function on `ℝ` is `x ↦ exp (i λ x)` for a real `λ`.  mathlib has no
such classification; this is the statement the flow blocks need, and `λ` is the generator
eigenvalue of the block. -/
theorem exists_real_generator_of_continuous_unimodular_character (hf : Continuous f)
    (hmul : ∀ s t : ℝ, f (s + t) = f s * f t) (h0 : f 0 = 1) (hnorm : ∀ x : ℝ, ‖f x‖ = 1) :
    ∃ lam : ℝ, ∀ x : ℝ, f x = Complex.exp (Complex.I * ((lam : ℂ) * (x : ℂ))) := by
  obtain ⟨c, hc⟩ := exists_hasDerivAt_of_continuous_character hf hmul h0
  exact exists_real_generator_of_unimodular_character hmul h0 hc hnorm

end GaloisForLFunctions.HTGeometry
