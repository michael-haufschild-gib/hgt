import GaloisForLFunctions.HTGeometry.ConformalClockMatrixRecovery
import Mathlib.Topology.UrysohnsLemma

/-!
# Continuous scale recovery through scalar mass collisions

Projective observations of `s(x) M(x)` distinguish real scales exactly where
the mass matrix is nonscalar. Continuous scales are consequently distinguished
on the closure of that locus. Every value outside the closure has a compatible
continuous realization. The same criterion applies to positive conformal scales
`exp (2 sigma)` through their continuous logarithmic scale `sigma`.

This is a uniqueness classification; it does not assert a stable inverse at a
vanishing mass gap. The mass field itself need not be continuous.
-/

namespace GaloisForLFunctions.HTGeometry

universe u

variable {X : Type u} {n : ℕ}

/-- Events with a nonzero projective mass matrix. -/
def clockNonscalarMassSet
    (M : X → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) : Set X :=
  {x | ¬ ∃ c : ℂ, M x = c • 1}

/-- Projective observations of a real scale field against a known mass field. -/
noncomputable def mixedClockScaleObservation
    (M : X → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (scale : X → ℝ) :
    X → ProjectiveDelayIndex n → ℂ :=
  fun x => projectiveDelayPanel ((scale x : ℂ) • M x)

/-- Exact observation equality is agreement on the nonscalar mass locus. -/
theorem mixedClockScaleObservation_eq_iff
    (M : X → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (scale other : X → ℝ) :
    mixedClockScaleObservation M other = mixedClockScaleObservation M scale ↔
      Set.EqOn other scale (clockNonscalarMassSet M) := by
  constructor
  · intro h x hx
    have hpanel : projectiveDelayPanel ((other x : ℂ) • M x + (0 : ℂ) • 1) =
        projectiveDelayPanel ((scale x : ℂ) • M x + (0 : ℂ) • 1) := by
      simpa [mixedClockScaleObservation] using congrFun h x
    have heq := (projectiveDelayPanel_mixedClock_eq_iff (M x) (other x) 0 (scale x) 0).mp hpanel
    exact Complex.ofReal_inj.mp (heq.resolve_right hx)
  · intro h
    funext x
    have hpanel := (projectiveDelayPanel_mixedClock_eq_iff (M x) (other x) 0 (scale x) 0).mpr
      (by
        by_cases hx : ∃ c : ℂ, M x = c • 1
        · exact Or.inr hx
        · exact Or.inl (congrArg (fun t : ℝ => (t : ℂ)) (h hx)))
    simpa [mixedClockScaleObservation] using hpanel

/-- Exponentiating twice the logarithmic scale changes no observation fibers;
strict positivity of the physical scale introduces no extra uniqueness premise. -/
theorem mixedClockScaleObservation_exp_eq_iff
    (M : X → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (scale other : X → ℝ) :
    mixedClockScaleObservation M (fun x => Real.exp (2 * other x)) =
        mixedClockScaleObservation M (fun x => Real.exp (2 * scale x)) ↔
      mixedClockScaleObservation M other = mixedClockScaleObservation M scale := by
  rw [mixedClockScaleObservation_eq_iff, mixedClockScaleObservation_eq_iff]
  constructor
  · intro h x hx
    have heq := Real.exp_injective (h hx)
    linarith
  · intro h x hx
    change Real.exp (2 * other x) = Real.exp (2 * scale x)
    rw [h hx]

variable [TopologicalSpace X]

/-- Continuous scale fields with the same observations agree exactly on the
closure of the nonscalar mass locus. -/
theorem continuousMixedClockScale_eq_iff_eqOn_closure
    (M : X → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (scale other : C(X, ℝ)) :
    mixedClockScaleObservation M other = mixedClockScaleObservation M scale ↔
      Set.EqOn other scale (closure (clockNonscalarMassSet M)) := by
  rw [mixedClockScaleObservation_eq_iff]
  constructor
  · intro h
    exact closure_minimal h (isClosed_eq other.continuous scale.continuous)
  · intro h x hx
    exact h (subset_closure hx)

variable [NormalSpace X] [T1Space X]

/-- At a limit of nonscalar masses, the scale value is fixed; elsewhere every
real scale value is realized by an observation-preserving continuous field. -/
theorem continuousMixedClockScale_value_fiber
    (M : X → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ)
    (scale : C(X, ℝ)) (x : X) (value : ℝ) :
    (∃ other : C(X, ℝ),
      mixedClockScaleObservation M other = mixedClockScaleObservation M scale ∧
      other x = value) ↔
      (x ∈ closure (clockNonscalarMassSet M) → value = scale x) := by
  constructor
  · rintro ⟨other, hother, hvalue⟩ hx
    exact hvalue.symm.trans
      ((continuousMixedClockScale_eq_iff_eqOn_closure M scale other).mp hother hx)
  · intro hvalue
    by_cases hx : x ∈ closure (clockNonscalarMassSet M)
    · exact ⟨scale, rfl, (hvalue hx).symm⟩
    · obtain ⟨f, hf, hfx, _⟩ := exists_continuous_zero_one_of_isClosed
        isClosed_closure isClosed_singleton (Set.disjoint_singleton_right.mpr hx)
      let other : C(X, ℝ) :=
        ⟨fun y => scale y + (value - scale x) * f y,
          scale.continuous.add (continuous_const.mul f.continuous)⟩
      refine ⟨other, (continuousMixedClockScale_eq_iff_eqOn_closure M scale other).mpr ?_, ?_⟩
      · intro y hy
        change scale y + (value - scale x) * f y = scale y
        rw [hf hy]
        simp
      · change scale x + (value - scale x) * f x = value
        rw [hfx (Set.mem_singleton x)]
        simp

/-- The sharp continuous scale determination locus includes scalar-mass points
whenever nonscalar masses accumulate there. -/
theorem continuousMixedClockScale_determined_iff
    (M : X → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (scale : C(X, ℝ)) (x : X) :
    (∀ other : C(X, ℝ),
      mixedClockScaleObservation M other = mixedClockScaleObservation M scale →
      other x = scale x) ↔ x ∈ closure (clockNonscalarMassSet M) := by
  constructor
  · intro h
    by_contra hx
    obtain ⟨other, hother, hvalue⟩ :=
      (continuousMixedClockScale_value_fiber M scale x (scale x + 1)).mpr
        (fun hx' => (hx hx').elim)
    have := h other hother
    linarith
  · intro hx other hother
    exact (continuousMixedClockScale_eq_iff_eqOn_closure M scale other).mp hother hx

/-- Dense nonscalarity is necessary and sufficient for global recovery of a
continuous scale field, even with scalar mass collisions. -/
theorem continuousMixedClockScale_unique_iff_dense
    (M : X → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (scale : C(X, ℝ)) :
    (∀ other : C(X, ℝ),
      mixedClockScaleObservation M other = mixedClockScaleObservation M scale →
      other = scale) ↔ Dense (clockNonscalarMassSet M) := by
  constructor
  · intro h
    apply dense_iff_closure_eq.mpr
    apply Set.eq_univ_of_forall
    intro x
    apply (continuousMixedClockScale_determined_iff M scale x).mp
    intro other hother
    rw [h other hother]
  · intro h other hother
    ext x
    exact (continuousMixedClockScale_eq_iff_eqOn_closure M scale other).mp hother
      (by rw [h.closure_eq]; trivial)

/-- Positive conformal scales have the same sharp recovery boundary, expressed
without any assumed positivity or pointwise mass-gap premise. -/
theorem continuousConformalLogScale_unique_iff_dense
    (M : X → Matrix (Fin (n + 1)) (Fin (n + 1)) ℂ) (sigma : C(X, ℝ)) :
    (∀ other : C(X, ℝ),
      mixedClockScaleObservation M (fun x => Real.exp (2 * other x)) =
        mixedClockScaleObservation M (fun x => Real.exp (2 * sigma x)) →
      other = sigma) ↔ Dense (clockNonscalarMassSet M) := by
  simp only [mixedClockScaleObservation_exp_eq_iff]
  exact continuousMixedClockScale_unique_iff_dense M sigma

end GaloisForLFunctions.HTGeometry
