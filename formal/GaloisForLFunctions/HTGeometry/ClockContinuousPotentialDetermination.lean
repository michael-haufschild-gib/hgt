import GaloisForLFunctions.HTGeometry.ClockProbeSolutionSpace
import Mathlib.Topology.UrysohnsLemma

/-!
# Continuous potential recovery across common zeros

For continuous competing potentials, preserving every original solution is exactly
agreement on the closure of the solution family's nonvanishing locus. On a normal
T1 space, values outside that closure remain completely free, by continuous
separation. Thus dense visibility is the sharp global recovery criterion.

For two independent species the scale is determined on the intersection of the
separate closures. Equal masses give the separate, totalized zero-scale case.
No linearity or regularity of the wave operator is required.
-/

namespace GaloisForLFunctions.HTGeometry

universe u

variable {X : Type u} [TopologicalSpace X]

/-- Continuous potentials preserve all original solutions exactly when they agree
on the closure of the original solution family's visible locus. -/
theorem solutionSet_subset_iff_eqOn_closure
    (wave : (X → ℝ) → (X → ℝ)) (potential other : C(X, ℝ)) :
    solutionSet wave potential ⊆ solutionSet wave other ↔
      Set.EqOn other potential
        (closure (potentialDeterminationSet (solutionSet wave potential))) := by
  constructor
  · intro h
    exact closure_minimal
      (potential_eqOn_potentialDeterminationSet (fun _ hu => h hu) (fun _ hu => hu))
      (isClosed_eq other.continuous potential.continuous)
  · intro h u hu x
    by_cases hux : u x = 0
    · simpa only [hux, mul_zero] using hu x
    · rw [h (subset_closure ⟨u, hu, hux⟩)]
      exact hu x

section Normal

variable [NormalSpace X] [T1Space X]

/-- At a visible limit point the only compatible value is the original value;
outside the closure every real value has a continuous compatible realization. -/
theorem continuousPotential_value_fiber
    (wave : (X → ℝ) → (X → ℝ)) (potential : C(X, ℝ)) (x : X) (value : ℝ) :
    (∃ other : C(X, ℝ), solutionSet wave potential ⊆ solutionSet wave other ∧
        other x = value) ↔
      (x ∈ closure (potentialDeterminationSet (solutionSet wave potential)) →
        value = potential x) := by
  constructor
  · rintro ⟨other, hother, hvalue⟩ hx
    exact hvalue.symm.trans ((solutionSet_subset_iff_eqOn_closure wave potential other).mp
      hother hx)
  · intro hvalue
    by_cases hx : x ∈ closure (potentialDeterminationSet (solutionSet wave potential))
    · exact ⟨potential, fun _ hu => hu, (hvalue hx).symm⟩
    · obtain ⟨f, hf, hfx, _⟩ := exists_continuous_zero_one_of_isClosed
        isClosed_closure isClosed_singleton (Set.disjoint_singleton_right.mpr hx)
      let other : C(X, ℝ) :=
        ⟨fun y => potential y + (value - potential x) * f y,
          potential.continuous.add (continuous_const.mul f.continuous)⟩
      refine ⟨other, (solutionSet_subset_iff_eqOn_closure wave potential other).mpr ?_, ?_⟩
      · intro y hy
        change potential y + (value - potential x) * f y = potential y
        rw [hf hy]
        simp
      · change potential x + (value - potential x) * f x = value
        rw [hfx (Set.mem_singleton x)]
        simp

/-- The exact pointwise determination locus within continuous potentials is the
closure of the solution family's visible locus. -/
theorem continuousPotential_determined_iff_mem_closure
    (wave : (X → ℝ) → (X → ℝ)) (potential : C(X, ℝ)) (x : X) :
    (∀ other : C(X, ℝ), solutionSet wave potential ⊆ solutionSet wave other →
        other x = potential x) ↔
      x ∈ closure (potentialDeterminationSet (solutionSet wave potential)) := by
  constructor
  · intro h
    by_contra hx
    obtain ⟨other, hother, hvalue⟩ :=
      (continuousPotential_value_fiber wave potential x (potential x + 1)).mpr
        (fun hx' => (hx hx').elim)
    have := h other hother
    linarith
  · intro hx other hother
    exact (solutionSet_subset_iff_eqOn_closure wave potential other).mp hother hx

/-- Global continuous potential recovery is equivalent to dense visibility, with
no requirement for a nonvanishing probe at each individual event. -/
theorem continuousPotential_unique_iff_dense
    (wave : (X → ℝ) → (X → ℝ)) (potential : C(X, ℝ)) :
    (∀ other : C(X, ℝ), solutionSet wave potential ⊆ solutionSet wave other →
        other = potential) ↔
      Dense (potentialDeterminationSet (solutionSet wave potential)) := by
  constructor
  · intro h
    apply dense_iff_closure_eq.mpr
    apply Set.eq_univ_of_forall
    intro x
    apply (continuousPotential_determined_iff_mem_closure wave potential x).mp
    intro other hother
    rw [h other hother]
  · intro h other hother
    ext x
    exact (solutionSet_subset_iff_eqOn_closure wave potential other).mp hother
      (by rw [h.closure_eq]; trivial)

/-- Independent continuous species determine their scale exactly on the
intersection of their separate visible closures, unless equal masses make every
totalized scale zero. -/
theorem continuousScale_determined_iff
    (wave₁ wave₂ : (X → ℝ) → (X → ℝ)) (potential₁ potential₂ : C(X, ℝ))
    (massSq₁ massSq₂ : ℝ) (x : X) :
    (∀ other₁ other₂ : C(X, ℝ),
      solutionSet wave₁ potential₁ ⊆ solutionSet wave₁ other₁ →
      solutionSet wave₂ potential₂ ⊆ solutionSet wave₂ other₂ →
      reconstructedScale other₁ other₂ massSq₁ massSq₂ x =
        reconstructedScale potential₁ potential₂ massSq₁ massSq₂ x) ↔
    massSq₁ = massSq₂ ∨
      x ∈ closure (potentialDeterminationSet (solutionSet wave₁ potential₁)) ∩
        closure (potentialDeterminationSet (solutionSet wave₂ potential₂)) := by
  by_cases hmass : massSq₁ = massSq₂
  · simp [hmass, reconstructedScale]
  · have hden : massSq₁ - massSq₂ ≠ 0 := sub_ne_zero.mpr hmass
    constructor
    · intro h
      right
      constructor
      · apply (continuousPotential_determined_iff_mem_closure wave₁ potential₁ x).mp
        intro other hother
        have heq := h other potential₂ hother (fun _ hu => hu)
        simp only [reconstructedScale] at heq
        have hnum := mul_right_cancel₀ hden ((div_eq_div_iff hden hden).mp heq)
        linarith
      · apply (continuousPotential_determined_iff_mem_closure wave₂ potential₂ x).mp
        intro other hother
        have heq := h potential₁ other (fun _ hu => hu) hother
        simp only [reconstructedScale] at heq
        have hnum := mul_right_cancel₀ hden ((div_eq_div_iff hden hden).mp heq)
        linarith
    · rintro (h | ⟨hx₁, hx₂⟩) other₁ other₂ h₁ h₂
      · exact (hmass h).elim
      · have e₁ := (solutionSet_subset_iff_eqOn_closure wave₁ potential₁ other₁).mp h₁ hx₁
        have e₂ := (solutionSet_subset_iff_eqOn_closure wave₂ potential₂ other₂).mp h₂ hx₂
        simp only [reconstructedScale, e₁, e₂]

end Normal

/-- Dense visibility can recover every continuous potential value even when the
full solution family has a common zero. -/
theorem exists_continuousPotential_unique_not_noCommonZero :
    ∃ wave : (ℝ → ℝ) → (ℝ → ℝ),
      ¬ NoCommonZero wave (0 : C(ℝ, ℝ)) ∧
      ∀ other : C(ℝ, ℝ),
        solutionSet wave (0 : C(ℝ, ℝ)) ⊆ solutionSet wave other → other = 0 := by
  let wave : (ℝ → ℝ) → (ℝ → ℝ) := fun u x => if x = 0 then u x else 0
  refine ⟨wave, ?_, (continuousPotential_unique_iff_dense wave 0).mpr ?_⟩
  · intro h
    obtain ⟨u, hu, hzero⟩ := h 0
    have hu0 := hu 0
    simp [wave] at hu0
    exact hzero hu0
  · apply (dense_compl_singleton (0 : ℝ)).mono
    intro x hx
    have hx0 : x ≠ 0 := hx
    let u : ℝ → ℝ := fun y => if y = 0 then 0 else 1
    refine ⟨u, ?_, ?_⟩
    · intro y
      by_cases hy : y = 0 <;> simp [wave, u, hy]
    · simp [u, hx0]

end GaloisForLFunctions.HTGeometry
