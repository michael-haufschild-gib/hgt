import GaloisForLFunctions.HTGeometry.BohrApproximation

/-!
# The character group of the hull is the Bohr frequency group

Every continuous character of the Bohr hull restricts along the dense homomorphism `ι` to a
continuous character of the line, hence to an exponential `t ↦ e^{iλt}`; the frequency `λ` is a hull
frequency and the character is the one already attached to it.  Conversely distinct frequencies give
distinct characters.

So the dual of the phase carrier *is* the frequency group of `f`, read inside `ℝ`.  This is the
identification `dual(X) = Γ(f)` on which the finite-rank law rests.
-/

open MeasureTheory TopologicalSpace

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open HTGeometry

noncomputable section

variable {f : ℝ →ᵇ ℂ}

/-- Distinct frequencies give distinct characters of the hull. -/
theorem bohrHullChar_injective {mu nu : ℝ} (hmu : IsBohrHullFrequency f mu)
    (hnu : IsBohrHullFrequency f nu) (h : bohrHullChar f mu = bohrHullChar f nu) : mu = nu := by
  by_contra hne
  have hd : mu - nu ≠ 0 := sub_ne_zero.mpr hne
  set t : ℝ := Real.pi / (mu - nu) with ht
  have h1 : expChar mu t = expChar nu t := by
    have := congrFun h (bohrIota f t)
    rwa [bohrHullChar_bohrIota hmu, bohrHullChar_bohrIota hnu] at this
  have h2 : Complex.exp (((mu - nu) * t : ℝ) * Complex.I) = 1 := by
    have hne0 : Complex.exp ((nu * t : ℝ) * Complex.I) ≠ 0 := Complex.exp_ne_zero _
    have hsum : ((mu - nu) * t : ℝ) * Complex.I + ((nu * t : ℝ) * Complex.I)
        = ((mu * t : ℝ) * Complex.I) := by
      push_cast
      ring
    have := h1
    unfold expChar at this
    calc Complex.exp (((mu - nu) * t : ℝ) * Complex.I)
        = Complex.exp (((mu - nu) * t : ℝ) * Complex.I + ((nu * t : ℝ) * Complex.I))
            / Complex.exp ((nu * t : ℝ) * Complex.I) := by
          rw [Complex.exp_add]
          field_simp
      _ = 1 := by
          rw [hsum, this]
          field_simp
  have h3 : ((mu - nu) * t : ℝ) = Real.pi := by
    rw [ht]
    field_simp
  rw [h3] at h2
  rw [Complex.exp_pi_mul_I] at h2
  exact absurd h2 (by norm_num)

/-- **Every continuous character of the hull comes from a Bohr frequency.** -/
theorem exists_frequency_of_hull_character (hf : UniformContinuous (fun x => f x))
    (htb : HasTotallyBoundedOrbit (fun x => f x)) {χ : BohrHull f → ℂ} (hcont : Continuous χ)
    (hmul : ∀ x y : BohrHull f, χ (x + y) = χ x * χ y) (hnorm : ∀ x : BohrHull f, ‖χ x‖ = 1) :
    ∃ lam : ℝ, IsBohrHullFrequency f lam ∧ χ = bohrHullChar f lam := by
  haveI : CompactSpace (BohrHull f) := compactSpace_bohrHull htb
  -- the restriction to the line is an exponential
  obtain ⟨lam, hlam⟩ := exists_exp_of_continuous_character
    (ψ := fun t : ℝ => χ (bohrIota f t)) (hcont.comp (continuous_bohrIota hf))
    (fun s t => by rw [bohrIota_add, hmul]) (fun t => hnorm _)
  -- hence the frequency is a hull frequency
  have hfreq : IsBohrHullFrequency f lam := by
    have hcoe : UniformContinuous (fun t : BohrLine f => ((t : BohrHull f))) :=
      UniformSpace.Completion.uniformContinuous_coe _
    have hχu : UniformContinuous χ := CompactSpace.uniformContinuous_of_continuous hcont
    have hcomp : UniformContinuous (fun t : BohrLine f => χ ((t : BohrHull f))) :=
      hχu.comp hcoe
    have heq : (fun t : BohrLine f => expChar lam t.val)
        = fun t : BohrLine f => χ ((t : BohrHull f)) := by
      funext t
      show Complex.exp ((lam * t.val : ℝ) * Complex.I) = χ ((t : BohrHull f))
      rw [← hlam t.val]
      rfl
    rw [IsBohrHullFrequency, heq]
    exact hcomp
  refine ⟨lam, hfreq, ?_⟩
  refine Continuous.ext_on (denseRange_bohrIota f) hcont (continuous_bohrHullChar f lam) ?_
  rintro x ⟨t, rfl⟩
  rw [bohrHullChar_bohrIota hfreq, hlam t]
  rfl

end

end GaloisForLFunctions
