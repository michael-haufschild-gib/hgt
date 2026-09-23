import GaloisForLFunctions.HTGeometry.TupleHistogramCount
import GaloisForLFunctions.HTGeometry.ComponentReplicaCollisionLaw
import GaloisForLFunctions.HTGeometry.FiniteEntropyPlateauFutureLaw

/-!
# The component product law for completed spectral form factor moments

Replica sums indexed by multiplicity vectors are tuple sums weighted by histogram fibres, so the
completed collision mass of a uniform finite spectrum counts pairs of tuples with equal histograms.
For a product alphabet the histogram-collision event factorizes over components, and the completed
moment of the spectral form factor becomes the product of the component collision coefficients

```text
a_{d,m} = d^{-m} ∑_{|k| = m} multinomial(k)^(2 : ℕ).
```
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-! ## Replica sums as tuple sums -/

variable {X : Type*} [Fintype X] [DecidableEq X]

theorem tupleHistogram_mem_piAntidiag {m : ℕ} (f : Fin m → X) :
    tupleHistogram f ∈ (Finset.univ : Finset X).piAntidiag m :=
  Finset.mem_piAntidiag.mpr ⟨sum_tupleHistogram f, fun i _ => Finset.mem_univ i⟩

/-- **Multiplicity sums are tuple sums.**  A multinomial-weighted sum over multiplicity vectors of
total mass `m` is the plain sum of the same quantity over tuples of length `m`. -/
theorem sum_multinomial_piAntidiag_eq_sum_tuple (m : ℕ) (Φ : (X → ℕ) → ℝ) :
    ∑ p ∈ (Finset.univ : Finset X).piAntidiag m,
        (Nat.multinomial Finset.univ p : ℝ) * Φ p
      = ∑ f : Fin m → X, Φ (tupleHistogram f) := by
  classical
  rw [← Finset.sum_fiberwise_of_maps_to
    (g := fun f : Fin m → X => tupleHistogram f)
    (s := (Finset.univ : Finset (Fin m → X)))
    (t := (Finset.univ : Finset X).piAntidiag m)
    (fun f _ => tupleHistogram_mem_piAntidiag f) (fun f => Φ (tupleHistogram f))]
  refine Finset.sum_congr rfl fun p hp => ?_
  have hval : ∀ f ∈ Finset.univ.filter fun f : Fin m → X => tupleHistogram f = p,
      Φ (tupleHistogram f) = Φ p := by
    intro f hf
    rw [(Finset.mem_filter.mp hf).2]
  rw [Finset.sum_congr rfl hval, Finset.sum_const, nsmul_eq_mul,
    card_tupleHistogram_fiber m p (Finset.mem_piAntidiag.mp hp).1]

theorem sum_pair_multinomial_piAntidiag_eq_sum_tuple (m : ℕ) (Ψ : (X → ℕ) → (X → ℕ) → ℝ) :
    ∑ p ∈ (Finset.univ : Finset X).piAntidiag m,
        ∑ q ∈ (Finset.univ : Finset X).piAntidiag m,
          (Nat.multinomial Finset.univ p : ℝ) * (Nat.multinomial Finset.univ q : ℝ) * Ψ p q
      = ∑ f : Fin m → X, ∑ g : Fin m → X, Ψ (tupleHistogram f) (tupleHistogram g) := by
  classical
  have hinner : ∀ p : X → ℕ,
      ∑ q ∈ (Finset.univ : Finset X).piAntidiag m,
          (Nat.multinomial Finset.univ p : ℝ) * (Nat.multinomial Finset.univ q : ℝ) * Ψ p q
        = (Nat.multinomial Finset.univ p : ℝ) *
            ∑ g : Fin m → X, Ψ p (tupleHistogram g) := by
    intro p
    rw [← sum_multinomial_piAntidiag_eq_sum_tuple m (Ψ p), Finset.mul_sum]
    refine Finset.sum_congr rfl fun q _ => ?_
    ring
  rw [Finset.sum_congr rfl fun p _ => hinner p]
  exact sum_multinomial_piAntidiag_eq_sum_tuple m fun p => ∑ g : Fin m → X, Ψ p (tupleHistogram g)

/-! ## The histogram collision count -/

/-- The number of ordered pairs of length-`m` tuples with equal histograms, which is the sum of
squared multinomial coefficients of `(9)`. -/
def histogramCollisionCount (X : Type*) [Fintype X] [DecidableEq X] (m : ℕ) : ℝ :=
  ∑ k ∈ (Finset.univ : Finset X).piAntidiag m, (Nat.multinomial Finset.univ k : ℝ) ^ (2 : ℕ)

theorem histogramCollisionCount_eq_sum_tuple (m : ℕ) :
    histogramCollisionCount X m
      = ∑ f : Fin m → X, ∑ g : Fin m → X,
          if tupleHistogram f = tupleHistogram g then (1 : ℝ) else 0 := by
  classical
  rw [← sum_pair_multinomial_piAntidiag_eq_sum_tuple m
    (fun p q => if p = q then (1 : ℝ) else 0), histogramCollisionCount]
  refine Finset.sum_congr rfl fun p hp => ?_
  rw [Finset.sum_eq_single p]
  · rw [if_pos rfl]
    ring
  · intro q _ hqp
    rw [if_neg (fun h => hqp h.symm), mul_zero]
  · intro hp'
    exact absurd hp hp'

/-- The normalized component collision coefficient `a_{d,m}` of `(9)`. -/
def replicaFormFactorCoefficient (X : Type*) [Fintype X] [DecidableEq X] (m : ℕ) : ℝ :=
  histogramCollisionCount X m / (Fintype.card X : ℝ) ^ m

/-! ## Component factorization -/

variable {C : Type*} [Fintype C] [DecidableEq C]
variable {J : C → Type*} [∀ c, Fintype (J c)] [∀ c, DecidableEq (J c)]

/-- The product-alphabet coordinate system. -/
abbrev piCoordinate (J : C → Type*) : ∀ c, (∀ c, J c) → J c := fun c x => x c

/-- Splitting a pair of product-alphabet tuples into its component pairs. -/
def componentTuplePairEquiv (m : ℕ) (J : C → Type*) :
    ((Fin m → ∀ c, J c) × (Fin m → ∀ c, J c)) ≃ (∀ c, (Fin m → J c) × (Fin m → J c)) where
  toFun fg c := (fun s => fg.1 s c, fun s => fg.2 s c)
  invFun F := (fun s c => (F c).1 s, fun s c => (F c).2 s)
  left_inv _ := rfl
  right_inv _ := rfl

/-- The number of ordered pairs of product-alphabet tuples whose component histograms agree. -/
def componentHistogramCollisionCount (J : C → Type*) [∀ c, Fintype (J c)]
    [∀ c, DecidableEq (J c)] (m : ℕ) : ℝ :=
  ∑ f : Fin m → ∀ c, J c, ∑ g : Fin m → ∀ c, J c,
    if ∀ c, tupleHistogram (fun s => f s c) = tupleHistogram (fun s => g s c) then (1 : ℝ) else 0

/-- **Component factorization of the collision count.**  Component histogram collisions are
independent across components. -/
theorem componentHistogramCollisionCount_eq_prod (m : ℕ) :
    componentHistogramCollisionCount J m = ∏ c, histogramCollisionCount (J c) m := by
  classical
  set e : (Fin m → ∀ c, J c) ≃ (∀ c, Fin m → J c) := Equiv.piComm _ with he
  have hsplit : componentHistogramCollisionCount J m
      = ∑ F : ∀ c, Fin m → J c, ∑ G : ∀ c, Fin m → J c,
          ∏ c, if tupleHistogram (F c) = tupleHistogram (G c) then (1 : ℝ) else 0 := by
    rw [componentHistogramCollisionCount]
    refine Fintype.sum_equiv e _ _ fun f => ?_
    refine Fintype.sum_equiv e _ _ fun g => ?_
    rw [Finset.prod_boole]
    simp [he, Equiv.piComm]
  rw [hsplit]
  have hinner : ∀ F : ∀ c, Fin m → J c,
      ∑ G : ∀ c, Fin m → J c,
          ∏ c, (if tupleHistogram (F c) = tupleHistogram (G c) then (1 : ℝ) else 0)
        = ∏ c, ∑ g : Fin m → J c,
            (if tupleHistogram (F c) = tupleHistogram g then (1 : ℝ) else 0) := by
    intro F
    rw [Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [Finset.sum_congr rfl fun F _ => hinner F]
  have hRHS : ∏ c, histogramCollisionCount (J c) m
      = ∑ F : ∀ c, Fin m → J c, ∏ c, ∑ g : Fin m → J c,
          (if tupleHistogram (F c) = tupleHistogram g then (1 : ℝ) else 0) := by
    rw [Finset.prod_congr rfl fun c _ => histogramCollisionCount_eq_sum_tuple (X := J c) m,
      Finset.prod_univ_sum, Fintype.piFinset_univ]
  rw [hRHS]

/-! ## The component histogram of a tuple -/

theorem componentReplicaMultiplicityOn_tupleHistogram {m : ℕ} (f : Fin m → ∀ c, J c) (c : C)
    (i : J c) :
    componentReplicaMultiplicityOn (piCoordinate J) (tupleHistogram f) c i
      = tupleHistogram (fun s => f s c) i := by
  classical
  have hfib := Finset.card_eq_sum_card_fiberwise (f := f)
    (s := Finset.univ.filter fun s => f s c = i)
    (t := Finset.univ.filter fun x : ∀ c, J c => x c = i)
    (fun s hs => Finset.mem_filter.mpr ⟨Finset.mem_univ _, (Finset.mem_filter.mp hs).2⟩)
  have hterm : ∀ x ∈ Finset.univ.filter fun x : ∀ c, J c => x c = i,
      ((Finset.univ.filter fun s => f s c = i).filter fun s => f s = x).card
        = tupleHistogram f x := by
    intro x hx
    rw [tupleHistogram]
    congr 1
    ext s
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact (Finset.mem_filter.mp hx).2, h⟩⟩
  rw [componentReplicaMultiplicityOn, ← Finset.sum_filter]
  calc ∑ x ∈ Finset.univ.filter fun x : ∀ c, J c => x c = i, tupleHistogram f x
      = ∑ x ∈ Finset.univ.filter fun x : ∀ c, J c => x c = i,
          ((Finset.univ.filter fun s => f s c = i).filter fun s => f s = x).card :=
        (Finset.sum_congr rfl hterm).symm
    _ = tupleHistogram (fun s => f s c) i := by
        rw [tupleHistogram]
        exact hfib.symm

/-! ## The uniform collision mass -/

theorem prod_microcanonicalWeight_pow {m : ℕ} {p : X → ℕ}
    (hp : p ∈ (Finset.univ : Finset X).piAntidiag m) :
    ∏ x, microcanonicalWeight X x ^ p x = ((Fintype.card X : ℝ)⁻¹) ^ m := by
  simp only [microcanonicalWeight]
  rw [Finset.prod_pow_eq_pow_sum, (Finset.mem_piAntidiag.mp hp).1]

/-- **The uniform component collision mass counts component-histogram collisions.** -/
theorem fidelityReplicaComponentCollisionMassOn_microcanonical (m : ℕ) :
    fidelityReplicaComponentCollisionMassOn (piCoordinate J)
        (microcanonicalWeight (∀ c, J c)) m
      = ((Fintype.card (∀ c, J c) : ℝ)⁻¹) ^ (2 * m) * componentHistogramCollisionCount J m := by
  classical
  set w : ℝ := ((Fintype.card (∀ c, J c) : ℝ)⁻¹) with hw
  have hstep : fidelityReplicaComponentCollisionMassOn (piCoordinate J)
      (microcanonicalWeight (∀ c, J c)) m
      = ∑ p ∈ (Finset.univ : Finset (∀ c, J c)).piAntidiag m,
          ∑ q ∈ (Finset.univ : Finset (∀ c, J c)).piAntidiag m,
            (Nat.multinomial Finset.univ p : ℝ) * (Nat.multinomial Finset.univ q : ℝ) *
              (w ^ (2 * m) *
                if ∀ c i, componentReplicaMultiplicityOn (piCoordinate J) p c i
                    = componentReplicaMultiplicityOn (piCoordinate J) q c i then 1 else 0) := by
    rw [fidelityReplicaComponentCollisionMassOn]
    refine Finset.sum_congr rfl fun p hp => ?_
    refine Finset.sum_congr rfl fun q hq => ?_
    by_cases hcond : ∀ c i, componentReplicaMultiplicityOn (piCoordinate J) p c i
        = componentReplicaMultiplicityOn (piCoordinate J) q c i
    · rw [if_pos hcond, if_pos hcond, fidelityReplicaMultiplicityWeight,
        prod_microcanonicalWeight_pow hp, prod_microcanonicalWeight_pow hq, two_mul, pow_add]
      ring
    · rw [if_neg hcond, if_neg hcond]
      ring
  rw [hstep, sum_pair_multinomial_piAntidiag_eq_sum_tuple, componentHistogramCollisionCount,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  have hiff : (∀ c i, componentReplicaMultiplicityOn (piCoordinate J) (tupleHistogram f) c i
      = componentReplicaMultiplicityOn (piCoordinate J) (tupleHistogram g) c i)
      ↔ ∀ c, tupleHistogram (fun s => f s c) = tupleHistogram (fun s => g s c) := by
    constructor
    · intro h c
      funext i
      have := h c i
      rwa [componentReplicaMultiplicityOn_tupleHistogram,
        componentReplicaMultiplicityOn_tupleHistogram] at this
    · intro h c i
      rw [componentReplicaMultiplicityOn_tupleHistogram,
        componentReplicaMultiplicityOn_tupleHistogram, h c]
  by_cases hcond : ∀ c, tupleHistogram (fun s => f s c) = tupleHistogram (fun s => g s c)
  · rw [if_pos hcond, if_pos (hiff.mpr hcond)]
  · rw [if_neg hcond, if_neg (fun h => hcond (hiff.mp h))]

/-! ## The component product law -/

/-- **Exact component product law for the completed form-factor moment.**  Scaling the completed
uniform survival moment by the Hilbert-space dimension gives exactly the product of the component
collision coefficients, which is `(10)`. -/
theorem card_pow_mul_componentCollisionMass_eq_prod (m : ℕ) :
    (Fintype.card (∀ c, J c) : ℝ) ^ m *
        fidelityReplicaComponentCollisionMassOn (piCoordinate J)
          (microcanonicalWeight (∀ c, J c)) m
      = ∏ c, replicaFormFactorCoefficient (J c) m := by
  classical
  have hcard : ((Fintype.card (∀ c, J c) : ℝ)) ^ m = ∏ c, (Fintype.card (J c) : ℝ) ^ m := by
    rw [Fintype.card_pi, Nat.cast_prod, Finset.prod_pow]
  have hright : ∏ c, replicaFormFactorCoefficient (J c) m
      = componentHistogramCollisionCount J m / (Fintype.card (∀ c, J c) : ℝ) ^ m := by
    simp only [replicaFormFactorCoefficient]
    rw [componentHistogramCollisionCount_eq_prod, hcard]
    exact Finset.prod_div_distrib _ _
  rw [fidelityReplicaComponentCollisionMassOn_microcanonical, hright]
  rcases eq_or_ne ((Fintype.card (∀ c, J c) : ℝ) ^ m) 0 with hzero | hzero
  · rw [hzero, zero_mul, div_zero]
  · rw [two_mul, pow_add, inv_pow]
    field_simp

/-- **Completed spectral form factor moments factorize over components.** -/
theorem tendsto_componentFormFactorMoment (energy : ∀ c, J c → ℝ)
    (hindependent : ComponentProjectivelyIndependent energy) (m : ℕ) :
    Filter.Tendsto
      (fun T => (Fintype.card (∀ c, J c) : ℂ) ^ m *
        finiteSpectralSurvivalFidelityMean (microcanonicalWeight (∀ c, J c))
          (factorizedEnergyOn (piCoordinate J) energy) m T)
      Filter.atTop
      (nhds ((∏ c, replicaFormFactorCoefficient (J c) m : ℝ) : ℂ)) := by
  have h := finiteSpectralSurvivalFidelityMean_factorizedOn_tendsto_componentCollisionMass
    (piCoordinate J) (microcanonicalWeight (∀ c, J c)) energy hindependent m
  have hlimit := h.const_mul ((Fintype.card (∀ c, J c) : ℂ) ^ m)
  have hval : ((Fintype.card (∀ c, J c) : ℂ) ^ m *
      (fidelityReplicaComponentCollisionMassOn (piCoordinate J)
        (microcanonicalWeight (∀ c, J c)) m : ℂ))
      = ((∏ c, replicaFormFactorCoefficient (J c) m : ℝ) : ℂ) := by
    rw [← card_pow_mul_componentCollisionMass_eq_prod m]
    push_cast
    ring
  rwa [hval] at hlimit

end

end GaloisForLFunctions.HTGeometry
