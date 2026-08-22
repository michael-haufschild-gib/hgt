import GaloisForLFunctions.HTGeometry.SpectralOrbitComplexityAssembly
import GaloisForLFunctions.HTGeometry.AnalyticImageFinitenessComplex
import GaloisForLFunctions.HTGeometry.TranscendenceSubfamilyExtraction
import GaloisForLFunctions.HTGeometry.TwoQubitGateParametrisation

/-!
# The times at which the orbit is reachable by a bounded two-qubit circuit are finite

Equation `(2)` of the exact-complexity card.  The orbit's coordinates carry transcendence degree at
least `D − 1` at every nonzero algebraic time, so `D − 1` of them are algebraically independent
there; a word of `s` two-qubit gates has only `16 s` parameters; and one polynomial separates the
independent point from that image, so the exceptional times are the zeros of a single nonzero
complex-valued real-analytic function.

No o-minimality and no semialgebraic geometry.

## Main results

* `analyticOnNhd_orbit_coord` — the orbit's coordinates are real-analytic in time.
* `finite_twoQubit_circuit_times` — **the exceptional-time theorem.**
-/

open Matrix Polynomial
open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

namespace AlgebraicOrbit

set_option linter.unusedSectionVars false

noncomputable section

variable {α : Type*} [Fintype α] [DecidableEq α]

/-- A single spectral phase is real-analytic in time. -/
theorem analyticOnNhd_phase (c : ℂ) :
    AnalyticOnNhd ℝ (fun t : ℝ => Complex.exp (c * (t : ℂ))) Set.univ := by
  have hg : AnalyticOnNhd ℂ (fun z : ℂ => Complex.exp (c * z)) Set.univ := by
    refine DifferentiableOn.analyticOnNhd ?_ isOpen_univ
    exact (Complex.differentiable_exp.comp (differentiable_id.const_mul c)).differentiableOn
  have hgR : AnalyticOnNhd ℝ (fun z : ℂ => Complex.exp (c * z)) Set.univ := hg.restrictScalars
  have hof : AnalyticOnNhd ℝ (fun t : ℝ => (t : ℂ)) Set.univ :=
    fun t _ => Complex.ofRealCLM.analyticAt t
  exact hgR.comp hof (fun t _ => Set.mem_univ _)

/-- **The orbit's coordinates are real-analytic in time.** -/
theorem analyticOnNhd_orbit_coord {H : Matrix α α ℂ} {e : α → α → ℂ} {lam : α → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (hlaminj : Function.Injective lam) (Ω : α → ℂ) (i : α) :
    AnalyticOnNhd ℝ (fun t : ℝ => (unitaryEvolution H t *ᵥ Ω) i) Set.univ := by
  have hrw : (fun t : ℝ => (unitaryEvolution H t *ᵥ Ω) i)
      = fun t : ℝ => ∑ j, lagrangeStateMatrix H lam Ω i j *
          Complex.exp ((-(Complex.I * ((lam j : ℝ) : ℂ))) * (t : ℂ)) := by
    funext t
    rw [unitaryEvolution_mulVec_apply_eq_sum_lagrange heb hlaminj Ω t i]
    refine Finset.sum_congr rfl fun j _ => ?_
    congr 1
    ring
  rw [hrw]
  refine Finset.analyticOnNhd_fun_sum Finset.univ fun j _ => ?_
  exact analyticOnNhd_const.mul (analyticOnNhd_phase _)

/-! ### The exceptional-time theorem -/

variable {n : ℕ}

/-- **Equation (2).**  On any compact set of times, only finitely many times carry an orbit point
reachable from the rational input by `s` two-qubit gates, as soon as `16 s < D − 1`. -/
theorem finite_twoQubit_circuit_times
    {H : Matrix (Fin n → Bool) (Fin n → Bool) ℂ} {e : (Fin n → Bool) → (Fin n → Bool) → ℂ}
    {lam : (Fin n → Bool) → ℝ}
    (heb : IsOrthoEigenBasis H e lam) (hlaminj : Function.Injective lam)
    (hHalg : ∀ i j, IsAlgebraic ℚ (H i j))
    (hlamalg : ∀ i, IsAlgebraic ℚ ((lam i : ℝ) : ℂ))
    {v : (Fin n → Bool) → ℚ}
    (hc : ∀ j, finiteComplexInner (e j) (fun i => algebraMap ℚ ℂ (v i)) ≠ 0)
    (i₀ : Fin n → Bool)
    (hrigid : LinearMap.ker (SpectralExp.relationForm (fun i => ((lam i : ℝ) : ℂ)))
      = PermSubspace.constLine (K := ℚ) (ι := (Fin n → Bool)))
    {s : ℕ} (hs : s * 16 < Fintype.card (Fin n → Bool) - 1)
    {S : Set ℝ} (hS : IsCompact S) :
    {t ∈ S | ∃ (pos : Fin s → Fin n × Fin n)
        (G : Fin s → Matrix (Fin n → Bool) (Fin n → Bool) ℂ),
        (∀ k, TwoQubitCircuit.IsTwoQubitGate (pos k).1 (pos k).2 (G k)) ∧
        (List.ofFn G).prod *ᵥ (fun i => algebraMap ℚ ℂ (v i))
          = unitaryEvolution H t *ᵥ (fun i => algebraMap ℚ ℂ (v i))}.Finite := by
  classical
  set Ω : (Fin n → Bool) → ℂ := fun i => algebraMap ℚ ℂ (v i) with hΩ
  have hΩrat : ∀ i, ∃ a : ℚ, Ω i = algebraMap ℚ ℂ a := fun i => ⟨v i, rfl⟩
  have hone : IsAlgebraic ℚ (((1 : ℝ) : ℝ) : ℂ) := by
    rw [Complex.ofReal_one]
    exact isAlgebraic_one
  have hk := card_sub_one_le_trdeg_orbit heb hlaminj hHalg hlamalg hΩrat hc
    (t := (1 : ℝ)) one_ne_zero hone i₀ hrigid
  obtain ⟨σ₀, hσ₀⟩ := exists_algebraicIndependent_subfamily
    (F := (↥algNum)) (E := ℂ) (I := (Fin n → Bool)) (unitaryEvolution H 1 *ᵥ Ω) hk
  have hσQ : AlgebraicIndependent ℚ (fun l => (unitaryEvolution H 1 *ᵥ Ω) (σ₀ l)) :=
    hσ₀.restrictScalars (algebraMap ℚ (↥algNum)).injective
  set D : ℕ := Fintype.card (Fin n → Bool) with hD
  set eqv : (Fin n → Bool) ≃ Fin D := Fintype.equivFin _ with heqv
  set γ : Fin D → ℝ → ℂ := fun i t => (unitaryEvolution H t *ᵥ Ω) (eqv.symm i) with hγ
  have hγan : ∀ i, AnalyticOnNhd ℝ (γ i) Set.univ := fun i =>
    analyticOnNhd_orbit_coord heb hlaminj Ω (eqv.symm i)
  set σ : Fin (D - 1) → Fin D := fun l => eqv (σ₀ l) with hσ
  have hP : AlgebraicIndependent ℚ (fun l => γ (σ l) 1) := by
    have hfun : (fun l => γ (σ l) 1)
        = fun l => (unitaryEvolution H 1 *ᵥ Ω) (σ₀ l) := by
      funext l
      rw [hγ, hσ]
      simp
    rw [hfun]
    exact hσQ
  -- one finite set for each choice of gate positions
  have hfin : ∀ pos : Fin s → Fin n × Fin n,
      {t ∈ S | ∃ u : Fin (s * 16) → ℂ, ∀ i,
        γ i t = MvPolynomial.aeval u
          (TwoQubitCircuit.twoQubitCircuitCoords s pos v (eqv.symm i))}.Finite := by
    intro pos
    exact finite_meets_image_subfamily_complex hs σ
      (fun i => TwoQubitCircuit.twoQubitCircuitCoords s pos v (eqv.symm i)) γ hγan hP hS
  refine Set.Finite.subset (Set.Finite.biUnion (Set.finite_univ
    (α := Fin s → Fin n × Fin n)) (fun pos _ => hfin pos)) ?_
  rintro t ⟨htS, pos, G, hG, hprep⟩
  refine Set.mem_biUnion (Set.mem_univ pos) ⟨htS, ?_⟩
  obtain ⟨u, hu⟩ := TwoQubitCircuit.aeval_twoQubitCircuitCoords pos v G hG
  refine ⟨u, fun i => ?_⟩
  rw [hu (eqv.symm i), ← hprep]
  rfl

end

end AlgebraicOrbit

end GaloisForLFunctions.HTGeometry
