import GaloisForLFunctions.HTGeometry.ClockDescentAnomaly

/-!
# Observation-composition cocycle for clock descent anomalies

Physics anomalies are consistency defects: their useful structure is a cocycle law under
composition, not a proposed time evolution.  The same principle applies to the clock-descent
anomaly in `ClockDescentAnomaly`.  If an observation is performed in two stages, its composite
anomaly is exactly the downstream anomaly pulled back through the first observation plus the
upstream anomaly pushed forward through the second.

The payoff is not terminology.  Surjectivity of the first observation or injectivity of the
second makes composite consistency detect the remaining local consistency condition.  These are
hypothesis-discharge rules for multi-stage observable constructions.  The finite Tate-clock
specialization shows that arbitrary post-processing of a finite clock window is covered directly.

No parameter here is temporal.  The objects are source constraints, observable shadows, and maps
between observable structures.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K V O W : Type*}
  [Field K]
  [AddCommGroup V] [Module K V]
  [AddCommGroup O] [Module K O]
  [AddCommGroup W] [Module K W]

/-- **Observation-composition cocycle.**  For a two-stage observation `V → O → W`, the anomaly
of the composite is the sum of the downstream anomaly pulled back to `V` and the upstream anomaly
pushed forward to `W`:

`A(S, g ∘ f, R) = A(T, g, R) ∘ f + g ∘ A(S, f, T)`.

Thus a composite comparison has no independent anomaly term. -/
theorem clockDescentAnomaly_comp_observation
    (source : V →ₗ[K] V)
    (observe₀ : V →ₗ[K] O) (observe₁ : O →ₗ[K] W)
    (shadow₀ : O →ₗ[K] O) (shadow₁ : W →ₗ[K] W) :
    clockDescentAnomaly source (observe₁.comp observe₀) shadow₁ =
      (clockDescentAnomaly shadow₀ observe₁ shadow₁).comp observe₀ +
        observe₁.comp (clockDescentAnomaly source observe₀ shadow₀) := by
  ext v
  simp [clockDescentAnomaly, LinearMap.comp_apply, map_sub]

/-- If the upstream observation intertwines its source and shadow exactly, the composite anomaly
is precisely the pullback of the downstream anomaly. -/
theorem clockDescentAnomaly_comp_of_upstream_eq_zero
    (source : V →ₗ[K] V)
    (observe₀ : V →ₗ[K] O) (observe₁ : O →ₗ[K] W)
    (shadow₀ : O →ₗ[K] O) (shadow₁ : W →ₗ[K] W)
    (hupstream : clockDescentAnomaly source observe₀ shadow₀ = 0) :
    clockDescentAnomaly source (observe₁.comp observe₀) shadow₁ =
      (clockDescentAnomaly shadow₀ observe₁ shadow₁).comp observe₀ := by
  rw [clockDescentAnomaly_comp_observation, hupstream]
  simp

/-- If the downstream observation intertwines its source and shadow exactly, the composite
anomaly is precisely the pushforward of the upstream anomaly. -/
theorem clockDescentAnomaly_comp_of_downstream_eq_zero
    (source : V →ₗ[K] V)
    (observe₀ : V →ₗ[K] O) (observe₁ : O →ₗ[K] W)
    (shadow₀ : O →ₗ[K] O) (shadow₁ : W →ₗ[K] W)
    (hdownstream : clockDescentAnomaly shadow₀ observe₁ shadow₁ = 0) :
    clockDescentAnomaly source (observe₁.comp observe₀) shadow₁ =
      observe₁.comp (clockDescentAnomaly source observe₀ shadow₀) := by
  rw [clockDescentAnomaly_comp_observation, hdownstream]
  simp

/-- **Surjective-stage discharge.**  If the upstream anomaly vanishes and the first observation
is surjective, then composite consistency is equivalent to downstream consistency.  Hence a
composite zero-anomaly hypothesis can discharge the downstream one. -/
theorem clockDescentAnomaly_comp_eq_zero_iff_downstream_of_surjective
    (source : V →ₗ[K] V)
    (observe₀ : V →ₗ[K] O) (observe₁ : O →ₗ[K] W)
    (shadow₀ : O →ₗ[K] O) (shadow₁ : W →ₗ[K] W)
    (hupstream : clockDescentAnomaly source observe₀ shadow₀ = 0)
    (hsurj : Function.Surjective observe₀) :
    clockDescentAnomaly source (observe₁.comp observe₀) shadow₁ = 0 ↔
      clockDescentAnomaly shadow₀ observe₁ shadow₁ = 0 := by
  rw [clockDescentAnomaly_comp_of_upstream_eq_zero
    source observe₀ observe₁ shadow₀ shadow₁ hupstream]
  constructor
  · intro h
    ext o
    obtain ⟨v, rfl⟩ := hsurj o
    exact LinearMap.congr_fun h v
  · intro h
    rw [h]
    simp

/-- **Injective-stage discharge.**  If the downstream anomaly vanishes and the second observation
is injective, then composite consistency is equivalent to upstream consistency.  Hence a
composite zero-anomaly hypothesis can discharge the upstream one. -/
theorem clockDescentAnomaly_comp_eq_zero_iff_upstream_of_injective
    (source : V →ₗ[K] V)
    (observe₀ : V →ₗ[K] O) (observe₁ : O →ₗ[K] W)
    (shadow₀ : O →ₗ[K] O) (shadow₁ : W →ₗ[K] W)
    (hdownstream : clockDescentAnomaly shadow₀ observe₁ shadow₁ = 0)
    (hinj : Function.Injective observe₁) :
    clockDescentAnomaly source (observe₁.comp observe₀) shadow₁ = 0 ↔
      clockDescentAnomaly source observe₀ shadow₀ = 0 := by
  rw [clockDescentAnomaly_comp_of_downstream_eq_zero
    source observe₀ observe₁ shadow₀ shadow₁ hdownstream]
  constructor
  · intro h
    ext v
    apply hinj
    simpa using LinearMap.congr_fun h v
  · intro h
    rw [h]
    simp

/-- Every finite Tate-clock window is an onto observation of the unrestricted clock packet. -/
theorem tateClockFiniteObservation_surjective (s : Finset ℕ) :
    Function.Surjective (tateClockFiniteObservation (K := K) s) := by
  intro y
  let x : ℕ → K := fun n ↦ if h : n ∈ s then y ⟨n, h⟩ else 0
  refine ⟨x, ?_⟩
  ext i
  simp [tateClockFiniteObservation, x, i.2]

/-- **Finite-clock post-processing discharge.**  Once the source comparison is exact on a finite
clock window, exactness after arbitrary linear post-processing is equivalent to exactness of the
post-processing itself.  This is a direct clock-observability consumer of the general cocycle law.
-/
theorem tateClockPostObservationAnomaly_eq_zero_iff
    (s : Finset ℕ)
    (source : (ℕ → K) →ₗ[K] (ℕ → K))
    (shadow : (s → K) →ₗ[K] (s → K))
    (postObserve : (s → K) →ₗ[K] W) (postShadow : W →ₗ[K] W)
    (hfinite : clockDescentAnomaly source (tateClockFiniteObservation s) shadow = 0) :
    clockDescentAnomaly source
        (postObserve.comp (tateClockFiniteObservation s)) postShadow = 0 ↔
      clockDescentAnomaly shadow postObserve postShadow = 0 :=
  clockDescentAnomaly_comp_eq_zero_iff_downstream_of_surjective
    source (tateClockFiniteObservation s) postObserve shadow postShadow
      hfinite (tateClockFiniteObservation_surjective s)

end

end GaloisForLFunctions.HTGeometry
