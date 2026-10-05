import GaloisForLFunctions.HTGeometry.FormationEquivariance

/-!
# Positive two-sided formation groups are trivial

**Theorem 9.1.**  Let `V_+` be a pointed cone in an additive group `V` (`v ∈ V_+` and `-v ∈ V_+`
force `v = 0`) and `γ : (ℝ, +) → (V, +)` an additive homomorphism.  If `γ_u ∈ V_+` for every
admitted parameter `u` and admission is closed under `u ↦ -u`, then `γ_u = 0` for every admitted
`u`: `γ_{-u} = -γ_u` and both lie in the cone.  A faithful calibration
`ℓ(γ_u) = c u`, `c ≠ 0`, then admits only `u = 0`.  The positive measures form a pointed
cone in `M(K)` (two positive measures summing to zero vanish, by Riesz–Markov–Kakutani), so this
applies to formation dust; an equivariance `A_*γ_u = γ_{-u}` is compatible with but
not needed for the conclusion.

The three hypotheses are independent: a one-sided positive semigroup `u ↦ u δ_1`, `u ≥ 0`, a signed
group `u ↦ u δ_1`, `u ∈ ℝ`, and a non-additive positive family `u ↦ δ_1` all carry nonzero dust.
-/

open Filter Topology NormedSpace MeasureTheory Set

noncomputable section

namespace GaloisForLFunctions.HTGeometry.FormationDust

/-! ### The abstract selection theorem -/

section Abstract

variable {V : Type*} [AddCommGroup V]

/-- **Theorem 9.1**: a positive two-sided additive formation family vanishes. -/
theorem eq_zero_of_pointedCone (P : Set V) (hP : ∀ v, v ∈ P → -v ∈ P → v = 0) (γ : ℝ →+ V)
    (U : Set ℝ) (hU : ∀ u ∈ U, -u ∈ U) (hγ : ∀ u ∈ U, γ u ∈ P) {u : ℝ} (hu : u ∈ U) :
    γ u = 0 :=
  hP _ (hγ u hu) (by rw [← map_neg]; exact hγ _ (hU u hu))

/-- with a faithful calibration `ℓ(γ_u) = c u`, `c ≠ 0`, only `u = 0` is
admitted. -/
theorem eq_zero_of_calibration (P : Set V) (hP : ∀ v, v ∈ P → -v ∈ P → v = 0) (γ : ℝ →+ V)
    (U : Set ℝ) (hU : ∀ u ∈ U, -u ∈ U) (hγ : ∀ u ∈ U, γ u ∈ P) (ℓ : V →+ ℝ) {c : ℝ} (hc : c ≠ 0)
    (hℓ : ∀ u, ℓ (γ u) = c * u) {u : ℝ} (hu : u ∈ U) : u = 0 := by
  have h := hℓ u
  rw [eq_zero_of_pointedCone P hP γ U hU hγ hu, map_zero] at h
  exact (mul_eq_zero.1 h.symm).resolve_left hc

/-- The salient pointed cones of a real vector space are pointed in the above sense. -/
theorem PointedCone.eq_zero_of_mem_neg_mem {W : Type*} [AddCommGroup W] [Module ℝ W]
    (C : PointedCone ℝ W) (hC : (C : ConvexCone ℝ W).Salient) {v : W} (hv : v ∈ C)
    (hnv : -v ∈ C) : v = 0 := by
  by_contra h
  exact hC v hv h hnv

end Abstract

/-! ### The positive cone of `M(K)` -/

variable {K : Type*} [TopologicalSpace K] [CompactSpace K] [T2Space K] [SecondCountableTopology K]
  [CommMonoid K] [ContinuousMul K] [MeasurableSpace K] [BorelSpace K]

open MeasureAlgebra

/-- The positive measures form a pointed cone. -/
theorem eq_zero_of_isPositive_of_isPositive_neg {Φ : MeasureAlgebra K} (hΦ : IsPositive Φ)
    (hnΦ : IsPositive (-Φ)) : Φ = 0 := by
  obtain ⟨μ, hμ⟩ := hΦ.exists_ofMeasure_eq
  obtain ⟨ν, hν⟩ := hnΦ.exists_ofMeasure_eq
  have hsum : μ + ν = 0 := ofMeasure_injective (by rw [ofMeasure_add, hμ, hν, add_neg_cancel,
    ofMeasure_zero])
  have h1 := congrArg (fun m : FiniteMeasure K => (m : Measure K) univ) hsum
  simp only [FiniteMeasure.toMeasure_add, Measure.add_apply, FiniteMeasure.toMeasure_zero,
    Measure.coe_zero, Pi.zero_apply] at h1
  have hμ0 : μ = 0 := (FiniteMeasure.mass_zero_iff μ).1 (by
    have h2 := FiniteMeasure.ennreal_mass (μ := μ)
    rw [(add_eq_zero.1 h1).1] at h2
    exact_mod_cast h2)
  rw [← hμ, hμ0, ofMeasure_zero]

/-- **Theorem 9.1 for formation dust**: an additive family of dust measures that is positive at
every admitted parameter, with admission closed under negation, vanishes. -/
theorem dust_eq_zero (γ : ℝ →+ MeasureAlgebra K) (U : Set ℝ) (hU : ∀ u ∈ U, -u ∈ U)
    (hγ : ∀ u ∈ U, IsPositive (γ u)) {u : ℝ} (hu : u ∈ U) : γ u = 0 :=
  eq_zero_of_pointedCone {Φ | IsPositive Φ}
    (fun _ h hn => eq_zero_of_isPositive_of_isPositive_neg h hn) γ U hU hγ hu

/-- With an order-preserving functional-equation automorphism exchanging the two legs,
`A_*γ_u = γ_{-u}`, both legs vanish: the action transports them, the group law
forces them to be zero. -/
theorem dust_legs_eq_zero (A : K ≃ₜ* K) (γ : ℝ →+ MeasureAlgebra K) (U : Set ℝ)
    (hU : ∀ u ∈ U, -u ∈ U) (hγ : ∀ u ∈ U, IsPositive (γ u))
    (hA : ∀ u ∈ U, pushAlgHom (A : K →ₜ* K) (γ u) = γ (-u)) {u : ℝ} (hu : u ∈ U) :
    γ u = 0 ∧ pushAlgHom (A : K →ₜ* K) (γ u) = 0 := by
  refine ⟨dust_eq_zero γ U hU hγ hu, ?_⟩
  rw [hA u hu]
  exact dust_eq_zero γ U hU hγ (hU u hu)

/-- for formation dust. -/
theorem dust_calibration (γ : ℝ →+ MeasureAlgebra K) (U : Set ℝ) (hU : ∀ u ∈ U, -u ∈ U)
    (hγ : ∀ u ∈ U, IsPositive (γ u)) (ℓ : MeasureAlgebra K →+ ℝ) {c : ℝ} (hc : c ≠ 0)
    (hℓ : ∀ u, ℓ (γ u) = c * u) {u : ℝ} (hu : u ∈ U) : u = 0 :=
  eq_zero_of_calibration {Φ | IsPositive Φ}
    (fun _ h hn => eq_zero_of_isPositive_of_isPositive_neg h hn) γ U hU hγ ℓ hc hℓ hu

/-! ### Independence of the three hypotheses -/

/-- `u ↦ u δ_1` as an additive family. -/
def linearDust : ℝ →+ MeasureAlgebra K where
  toFun u := (u : ℂ) • (1 : MeasureAlgebra K)
  map_zero' := by simp
  map_add' u v := by push_cast; rw [add_smul]

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
theorem one_ne_zero' : (1 : MeasureAlgebra K) ≠ 0 := by
  intro h
  have := congrArg (fun Φ : MeasureAlgebra K => Φ 1) h
  simp at this

omit [SecondCountableTopology K] in
/-- **One-sided semigroups carry dust**: `u ↦ u δ_1` is additive and positive on `u ≥ 0`, but
nonzero; the admitted set `[0, ∞)` is not symmetric. -/
theorem oneSided_dust_ne_zero :
    (∀ u ∈ Ici (0 : ℝ), IsPositive (linearDust (K := K) u)) ∧ linearDust (K := K) 1 ≠ 0 := by
  refine ⟨fun u hu => ?_, ?_⟩
  · exact IsPositive.smul isPositive_one hu
  · simp [linearDust, one_ne_zero']

omit [SecondCountableTopology K] [MeasurableSpace K] [BorelSpace K] in
/-- **Signed groups carry odd dust**: `u ↦ u δ_1` is additive on all of `ℝ` and nonzero, but not
positive at `u = -1`. -/
theorem signed_dust_not_positive : ¬ IsPositive (linearDust (K := K) (-1)) := by
  intro h
  have := (h 1 fun _ => zero_le_one).2
  norm_num [linearDust, realToComplex] at this

omit [SecondCountableTopology K] in
/-- **Non-additive positive families need not vanish**: `u ↦ δ_1` is positive at every `u` and
admission `ℝ` is symmetric, yet it is nonzero. -/
theorem constant_dust_ne_zero :
    (∀ _u : ℝ, IsPositive (1 : MeasureAlgebra K)) ∧ (1 : MeasureAlgebra K) ≠ 0 :=
  ⟨fun _ => isPositive_one, one_ne_zero'⟩

end GaloisForLFunctions.HTGeometry.FormationDust
