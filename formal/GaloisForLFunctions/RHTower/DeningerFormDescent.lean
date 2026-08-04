import GaloisForLFunctions.RHTower.DeningerStageOneFormExact

/-!
# Descent of periodic forms along the exponential covering

A form on the covering space that is periodic in every coordinate is the pullback of a form on the
character stage.  The descended form is obtained by evaluating at a logarithm of the point and
composing with the inverse of the derivative of the covering, which is the diagonal of the inverse
coordinates; the periodicity makes the choice of logarithm immaterial.

* `deningerPeriodicDescent` : a coordinatewise periodic map is constant on the fibres, in any
  codomain.
* `deningerDescendForm` : the form on the stage attached to a periodic form upstairs.
* `deningerDescendForm_pullback` : it pulls back to the given form.
-/

namespace RHTower

open Complex

section GeneralDescent

variable {r : ℕ} {M : Type*}

/-- A function periodic in one coordinate is invariant under integer multiples of the period in
that coordinate, in any codomain. -/
theorem deningerPeriodicInt {G : (Fin r → ℂ) → M}
    (hper : ∀ (j : Fin r) (w : Fin r → ℂ),
      G (w + (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) = G w)
    (j : Fin r) (w : Fin r → ℂ) (m : ℤ) :
    G (w + ((m : ℂ) * (2 * Real.pi * Complex.I)) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) = G w := by
  have hfun : Function.Periodic
      (fun t : ℂ => G (w + t • (Pi.single j (1 : ℂ) : Fin r → ℂ)))
      (2 * Real.pi * Complex.I) := by
    intro t
    have h := hper j (w + t • (Pi.single j (1 : ℂ) : Fin r → ℂ))
    rw [add_assoc, ← add_smul] at h
    exact h
  have h := (hfun.int_mul m) 0
  simpa using h

/-- **A coordinatewise periodic map is constant on the fibres of the exponential covering**, in any
codomain. -/
theorem deningerPeriodicDescent {G : (Fin r → ℂ) → M}
    (hper : ∀ (j : Fin r) (w : Fin r → ℂ),
      G (w + (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) = G w)
    {w₁ w₂ : Fin r → ℂ} (h : deningerExpMap r w₁ = deningerExpMap r w₂) : G w₁ = G w₂ := by
  classical
  have hcoord : ∀ j : Fin r, ∃ m : ℤ, w₁ j = w₂ j + (m : ℂ) * (2 * Real.pi * Complex.I) := by
    intro j
    have hj : Complex.exp (w₁ j) = Complex.exp (w₂ j) := congrFun h j
    exact Complex.exp_eq_exp_iff_exists_int.1 hj
  choose m hm using hcoord
  have hstep : ∀ s : Finset (Fin r),
      G (w₂ + fun l => if l ∈ s then (m l : ℂ) * (2 * Real.pi * Complex.I) else 0) = G w₂ := by
    intro s
    induction s using Finset.induction with
    | empty =>
        have hz : (fun l : Fin r =>
            if l ∈ (∅ : Finset (Fin r)) then (m l : ℂ) * (2 * Real.pi * Complex.I) else 0) = 0 := by
          funext l
          simp
        rw [hz, add_zero]
    | @insert a s ha ih =>
        have hsplit : (fun l => if l ∈ insert a s then
              (m l : ℂ) * (2 * Real.pi * Complex.I) else 0) =
            (fun l => if l ∈ s then (m l : ℂ) * (2 * Real.pi * Complex.I) else 0) +
              ((m a : ℂ) * (2 * Real.pi * Complex.I)) •
                (Pi.single a (1 : ℂ) : Fin r → ℂ) := by
          funext l
          by_cases hl : l = a
          · subst hl
            simp [ha]
          · simp [Finset.mem_insert, hl]
        rw [hsplit, ← add_assoc, deningerPeriodicInt hper a, ih]
  have hall : w₁ = w₂ + fun l => if l ∈ (Finset.univ : Finset (Fin r)) then
      (m l : ℂ) * (2 * Real.pi * Complex.I) else 0 := by
    funext l
    simp only [Finset.mem_univ, if_true, Pi.add_apply]
    exact hm l
  rw [hall]
  exact hstep Finset.univ

end GeneralDescent

section DescendForm

variable {r n : ℕ}

/-- **The form on the stage attached to a periodic form on the covering space**: evaluate at a
logarithm of the point and compose with the inverse of the derivative of the covering. -/
noncomputable def deningerDescendForm (η : (Fin r → ℂ) → (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ)
    (z : Fin r → ℂ) : (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ :=
  (η (fun j => Complex.log (z j))).compContinuousLinearMap (deningerLogBranchDeriv z)

/-- The derivative of the covering cancels against the inverse coordinates. -/
theorem deningerLogBranchDeriv_expDeriv (w : Fin r → ℂ) :
    (deningerLogBranchDeriv (deningerExpMap r w)).comp (deningerExpDeriv w) =
      ContinuousLinearMap.id ℂ (Fin r → ℂ) := by
  refine ContinuousLinearMap.ext fun u => ?_
  funext l
  show (deningerExpMap r w l)⁻¹ * (Complex.exp (w l) * u l) = u l
  show (Complex.exp (w l))⁻¹ * (Complex.exp (w l) * u l) = u l
  rw [← mul_assoc, inv_mul_cancel₀ (Complex.exp_ne_zero _), one_mul]

/-- **A periodic form on the covering space descends**: the form it defines on the stage pulls back
to it. -/
theorem deningerDescendForm_pullback {η : (Fin r → ℂ) → (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ}
    (hper : ∀ (j : Fin r) (w : Fin r → ℂ),
      η (w + (2 * Real.pi * Complex.I) • (Pi.single j (1 : ℂ) : Fin r → ℂ)) = η w)
    (w : Fin r → ℂ) :
    deningerPullbackForm (deningerExpMap r) (deningerDescendForm η) w = η w := by
  have hlog : deningerExpMap r (fun j => Complex.log (deningerExpMap r w j)) =
      deningerExpMap r w := by
    funext j
    exact Complex.exp_log (Complex.exp_ne_zero _)
  have hval : η (fun j => Complex.log (deningerExpMap r w j)) = η w :=
    deningerPeriodicDescent hper hlog
  show ((deningerDescendForm η (deningerExpMap r w))).compContinuousLinearMap
    (fderiv ℂ (deningerExpMap r) w) = η w
  rw [(deningerExpMap_hasFDerivAt w).fderiv]
  show ((η (fun j => Complex.log (deningerExpMap r w j))).compContinuousLinearMap
      (deningerLogBranchDeriv (deningerExpMap r w))).compContinuousLinearMap
        (deningerExpDeriv w) = η w
  rw [hval]
  ext v
  show (η w) (fun i => (deningerLogBranchDeriv (deningerExpMap r w))
    (deningerExpDeriv w (v i))) = (η w) v
  have hcancel : ∀ u : Fin r → ℂ,
      (deningerLogBranchDeriv (deningerExpMap r w)) (deningerExpDeriv w u) = u := by
    intro u
    have h := deningerLogBranchDeriv_expDeriv w
    exact congrArg (fun L : (Fin r → ℂ) →L[ℂ] (Fin r → ℂ) => L u) h
  simp only [hcancel]

end DescendForm

end RHTower

namespace RHTower

section PullbackInjective

variable {r n : ℕ}

/-- The derivative of the covering is inverted by the diagonal of the inverse coordinates. -/
theorem deningerExpDeriv_logBranchDeriv (w : Fin r → ℂ) :
    (deningerExpDeriv w).comp (deningerLogBranchDeriv (deningerExpMap r w)) =
      ContinuousLinearMap.id ℂ (Fin r → ℂ) := by
  refine ContinuousLinearMap.ext fun u => ?_
  funext l
  show Complex.exp (w l) * ((deningerExpMap r w l)⁻¹ * u l) = u l
  show Complex.exp (w l) * ((Complex.exp (w l))⁻¹ * u l) = u l
  rw [← mul_assoc, mul_inv_cancel₀ (Complex.exp_ne_zero _), one_mul]

/-- **Composing with a surjective linear map is injective on alternating forms.** -/
theorem deningerCompContinuousLinearMap_cancel {A B : (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ}
    {L L' : (Fin r → ℂ) →L[ℂ] (Fin r → ℂ)} (hLL' : L.comp L' = ContinuousLinearMap.id ℂ _)
    (h : A.compContinuousLinearMap L = B.compContinuousLinearMap L) : A = B := by
  ext v
  have hsurj : ∀ u : Fin r → ℂ, L (L' u) = u := by
    intro u
    exact congrArg (fun M : (Fin r → ℂ) →L[ℂ] (Fin r → ℂ) => M u) hLL'
  have hv := congrArg (fun C : (Fin r → ℂ) [⋀^Fin n]→L[ℂ] ℂ => C (fun i => L' (v i))) h
  show A v = B v
  calc A v = A (fun i => L (L' (v i))) := by simp only [hsurj]
    _ = (A.compContinuousLinearMap L) (fun i => L' (v i)) := rfl
    _ = (B.compContinuousLinearMap L) (fun i => L' (v i)) := hv
    _ = B (fun i => L (L' (v i))) := rfl
    _ = B v := by simp only [hsurj]

/-- **The pullback along the exponential covering is injective on stage forms.** -/
theorem deningerExpPullback_injective {A B : DeningerStageForm r n}
    (h : ∀ w : Fin r → ℂ, deningerPullbackForm (deningerExpMap r) A w =
      deningerPullbackForm (deningerExpMap r) B w)
    {z : Fin r → ℂ} (hz : z ∈ deningerStageTorus r) : A z = B z := by
  set w : Fin r → ℂ := fun j => Complex.log (z j) with hw
  have hexp : deningerExpMap r w = z := by
    funext j
    exact Complex.exp_log (hz j)
  have hpull := h w
  rw [deningerPullbackForm, deningerPullbackForm, (deningerExpMap_hasFDerivAt w).fderiv,
    hexp] at hpull
  exact deningerCompContinuousLinearMap_cancel
    (L' := deningerLogBranchDeriv (deningerExpMap r w))
    (deningerExpDeriv_logBranchDeriv w) hpull

end PullbackInjective

end RHTower
