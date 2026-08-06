import GaloisForLFunctions.HTGeometry.TorusDerivationJets

/-!
# Autonomous relations transfer to the phase observables

An autonomous algebraic differential relation satisfied by a quasiperiodic
function along the real time axis is a polynomial identity among the iterated
torus derivatives of its phase observable, valid on the dense real orbit.  The
orbit is a uniqueness set for the polyannulus, so the identity holds on the
whole polyannulus; conversely, restriction to the orbit recovers the relation.

Minimal autonomous order can therefore be read from the phase functions.
-/

open Complex Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

/-! ### Analyticity of polynomial expressions in analytic functions -/

omit [DecidableEq d] in
theorem analyticOnNhd_mvPolynomialEval {σ : Type*} {s : Set (d → ℂ)}
    {g : σ → (d → ℂ) → ℂ} (hg : ∀ j, AnalyticOnNhd ℂ (g j) s)
    (Q : MvPolynomial σ ℂ) :
    AnalyticOnNhd ℂ (fun z => MvPolynomial.eval (fun j => g j z) Q) s := by
  induction Q using MvPolynomial.induction_on with
  | C a =>
      have hfun : (fun z : d → ℂ =>
          MvPolynomial.eval (fun j => g j z) (MvPolynomial.C a)) = fun _ => a := by
        funext z
        rw [MvPolynomial.eval_C]
      rw [hfun]
      exact analyticOnNhd_const
  | add p q hp hq =>
      have hfun : (fun z => MvPolynomial.eval (fun j => g j z) (p + q)) =
          fun z => MvPolynomial.eval (fun j => g j z) p +
            MvPolynomial.eval (fun j => g j z) q := by
        funext z
        rw [map_add]
      rw [hfun]
      exact hp.add hq
  | mul_X p j hp =>
      have hfun : (fun z => MvPolynomial.eval (fun j' => g j' z)
            (p * MvPolynomial.X j)) =
          fun z => MvPolynomial.eval (fun j' => g j' z) p * g j z := by
        funext z
        rw [map_mul, MvPolynomial.eval_X]
      rw [hfun]
      exact hp.mul (hg j)

omit [DecidableEq d] in
theorem analyticOnNhd_polynomialEval₂ {n : ℕ} {s : Set (d → ℂ)}
    {g : Fin n → (d → ℂ) → ℂ} (hg : ∀ j, AnalyticOnNhd ℂ (g j) s)
    {h : (d → ℂ) → ℂ} (hh : AnalyticOnNhd ℂ h s)
    (P : Polynomial (MvPolynomial (Fin n) ℂ)) :
    AnalyticOnNhd ℂ
      (fun z => Polynomial.eval₂ (MvPolynomial.eval fun j => g j z) (h z) P) s := by
  induction P using Polynomial.induction_on with
  | C a =>
      have hfun : (fun z => Polynomial.eval₂
            (MvPolynomial.eval fun j => g j z) (h z) (Polynomial.C a)) =
          fun z => MvPolynomial.eval (fun j => g j z) a := by
        funext z
        rw [Polynomial.eval₂_C]
      rw [hfun]
      exact analyticOnNhd_mvPolynomialEval hg a
  | add p q hp hq =>
      have hfun : (fun z => Polynomial.eval₂
            (MvPolynomial.eval fun j => g j z) (h z) (p + q)) =
          (fun z => Polynomial.eval₂ (MvPolynomial.eval fun j => g j z) (h z) p) +
            fun z => Polynomial.eval₂ (MvPolynomial.eval fun j => g j z) (h z) q := by
        funext z
        rw [Polynomial.eval₂_add]
        rfl
      rw [hfun]
      exact hp.add hq
  | monomial k a _ =>
      have hfun : (fun z => Polynomial.eval₂
            (MvPolynomial.eval fun j => g j z) (h z)
            (Polynomial.C a * Polynomial.X ^ (k + 1))) =
          fun z => MvPolynomial.eval (fun j => g j z) a * h z ^ (k + 1) := by
        funext z
        rw [Polynomial.eval₂_mul, Polynomial.eval₂_C, Polynomial.eval₂_pow,
          Polynomial.eval₂_X]
      rw [hfun]
      exact (analyticOnNhd_mvPolynomialEval hg a).mul (hh.pow _)

/-! ### Phase jets -/

/-- The `k`-th phase jet of a phase observable. -/
def phaseJet (omega : d → ℝ) (F : (d → ℂ) → ℂ) (k : ℕ) : (d → ℂ) → ℂ :=
  (torusDerivation omega)^[k] F

theorem analyticOnNhd_phaseJet {s : Set (d → ℂ)} (omega : d → ℝ)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F s) (k : ℕ) :
    AnalyticOnNhd ℂ (phaseJet omega F k) s :=
  analyticOnNhd_torusDerivation_iterate omega hF k

theorem phaseJet_torusOrbitPoint {ρ omega : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) (k : ℕ) (t : ℝ) :
    phaseJet omega F k (torusOrbitPoint omega t) =
      iteratedDeriv k (phaseFunction omega F) (t : ℂ) :=
  (iteratedDeriv_phaseFunction_ofReal hρ hF k t).symm

/-- Evaluation of an autonomous relation at the phase jets. -/
def phaseJetEval (omega : d → ℝ) (F : (d → ℂ) → ℂ) {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) ℂ)) (z : d → ℂ) : ℂ :=
  Polynomial.eval₂ (MvPolynomial.eval fun j : Fin n => phaseJet omega F j z)
    (phaseJet omega F n z) P

theorem analyticOnNhd_phaseJetEval {s : Set (d → ℂ)} (omega : d → ℝ)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F s) {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) ℂ)) :
    AnalyticOnNhd ℂ (phaseJetEval omega F P) s :=
  analyticOnNhd_polynomialEval₂
    (fun j => analyticOnNhd_phaseJet omega hF j)
    (analyticOnNhd_phaseJet omega hF n) P

/-! ### Autonomous relations along the real time axis -/

/-- An autonomous algebraic differential relation of order `n` satisfied along
the real time axis. -/
def RealAutonomousAnnihilator (f : ℂ → ℂ) (n : ℕ)
    (P : Polynomial (MvPolynomial (Fin n) ℂ)) : Prop :=
  ∀ t : ℝ, Polynomial.eval₂
    (MvPolynomial.eval fun j : Fin n => iteratedDeriv (j : ℕ) f (t : ℂ))
    (iteratedDeriv n f (t : ℂ)) P = 0

theorem phaseJetEval_torusOrbitPoint {ρ omega : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) ℂ)) (t : ℝ) :
    phaseJetEval omega F P (torusOrbitPoint omega t) =
      Polynomial.eval₂
        (MvPolynomial.eval fun j : Fin n =>
          iteratedDeriv (j : ℕ) (phaseFunction omega F) (t : ℂ))
        (iteratedDeriv n (phaseFunction omega F) (t : ℂ)) P := by
  have hjets : (fun j : Fin n => phaseJet omega F (j : ℕ) (torusOrbitPoint omega t)) =
      fun j : Fin n => iteratedDeriv (j : ℕ) (phaseFunction omega F) (t : ℂ) := by
    funext j
    exact phaseJet_torusOrbitPoint hρ hF (j : ℕ) t
  rw [phaseJetEval, phaseJet_torusOrbitPoint hρ hF n t, hjets]

/-- **Equation `(10)`: an autonomous relation along the real orbit is an
identity of phase observables.** -/
theorem phaseJetEval_eq_zero_of_realAutonomousAnnihilator {ρ omega : d → ℝ}
    (hρ : ∀ j, 0 < ρ j) (hindep : RationallyIndependentFrequency omega)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) {n : ℕ}
    {P : Polynomial (MvPolynomial (Fin n) ℂ)}
    (hP : RealAutonomousAnnihilator (phaseFunction omega F) n P) :
    ∀ z ∈ polyannulus ρ, phaseJetEval omega F P z = 0 := by
  refine eqOn_zero_polyannulus_of_eqOn_zero_orbit hρ hindep
    (analyticOnNhd_phaseJetEval omega hF P) fun t => ?_
  rw [phaseJetEval_torusOrbitPoint hρ hF P t]
  exact hP t

/-- The converse: restriction to the real orbit recovers the relation. -/
theorem realAutonomousAnnihilator_of_phaseJetEval_eq_zero {ρ omega : d → ℝ}
    (hρ : ∀ j, 0 < ρ j) {F : (d → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) {n : ℕ}
    {P : Polynomial (MvPolynomial (Fin n) ℂ)}
    (hP : ∀ z ∈ polyannulus ρ, phaseJetEval omega F P z = 0) :
    RealAutonomousAnnihilator (phaseFunction omega F) n P := by
  intro t
  rw [← phaseJetEval_torusOrbitPoint hρ hF P t]
  exact hP _ (torusOrbitPoint_mem_polyannulus hρ omega t)

/-- **Minimal autonomous order is read from the phase observables.** -/
theorem realAutonomousAnnihilator_iff_phaseJetEval_eq_zero {ρ omega : d → ℝ}
    (hρ : ∀ j, 0 < ρ j) (hindep : RationallyIndependentFrequency omega)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) {n : ℕ}
    (P : Polynomial (MvPolynomial (Fin n) ℂ)) :
    RealAutonomousAnnihilator (phaseFunction omega F) n P ↔
      ∀ z ∈ polyannulus ρ, phaseJetEval omega F P z = 0 :=
  ⟨fun hP => phaseJetEval_eq_zero_of_realAutonomousAnnihilator hρ hindep hF hP,
    fun hP => realAutonomousAnnihilator_of_phaseJetEval_eq_zero hρ hF hP⟩

end

end GaloisForLFunctions.HTGeometry
