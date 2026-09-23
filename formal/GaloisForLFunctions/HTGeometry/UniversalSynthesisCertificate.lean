/-
# The universal state-synthesis certificate

Two-level synthesis produces, for every finite register and every tolerance, a *single* finite gate
alphabet and a *single* reference state whose words of length at most twice the dimension reach
every pure state of the register to within that tolerance.  Since a unitary evolution preserves the
norm, every orbit of every self-adjoint Hamiltonian is such a pure state at every time, so the
alphabet certifies the whole orbit uniformly in the Hamiltonian, the seed and the time.

Main results:
* `transportAct` — the synthesis alphabet read on an arbitrary finite register.
* `exists_universal_synthesis_certificate` — **the uniform synthesis cap `2 · dim`**.
* `exists_orbit_synthesis_certificate` — the same cap along every self-adjoint orbit.
-/
import GaloisForLFunctions.HTGeometry.SynthesisWordApproximation
import GaloisForLFunctions.HTGeometry.FastForwardableStratumCodimension

open Finset

noncomputable section

namespace GaloisForLFunctions.HTGeometry

open _root_.HTGeometry

set_option linter.unusedSectionVars false

section Transport

variable {K : ℕ} {d : Type} [Fintype d] [DecidableEq d]

/-- The word map of the synthesis alphabet at the level of coefficient functions. -/
def synthWordFn (K m : ℕ) (w : List (SynthLetter K m)) : (Fin K → ℂ) → (Fin K → ℂ) :=
  fun v => w.foldr (synthGate K m) v

theorem synthWordFn_nil (K m : ℕ) (v : Fin K → ℂ) : synthWordFn K m [] v = v := rfl

theorem synthWordFn_cons (K m : ℕ) (g : SynthLetter K m) (w : List (SynthLetter K m))
    (v : Fin K → ℂ) :
    synthWordFn K m (g :: w) v = synthGate K m g (synthWordFn K m w v) := rfl

theorem eucVec_ofLp (x : EuclideanSpace ℂ d) : eucVec (WithLp.ofLp x) = x := rfl

theorem wordAct_synthAct_eucVec (K m : ℕ) :
    ∀ (w : List (SynthLetter K m)) (v : Fin K → ℂ),
      wordAct (synthAct K m) w (eucVec v) = eucVec (synthWordFn K m w v)
  | [], v => by rw [wordAct_nil, synthWordFn_nil]
  | g :: w, v => by
      rw [wordAct_cons, wordAct_synthAct_eucVec K m w v, synthWordFn_cons]
      rfl

/-- Read a coefficient function of the model register on an arbitrary register. -/
def pullVec (E : d ≃ Fin K) (v : Fin K → ℂ) : d → ℂ := fun i => v (E i)

/-- Read a coefficient function of an arbitrary register on the model register. -/
def pushVec (E : d ≃ Fin K) (v : d → ℂ) : Fin K → ℂ := fun r => v (E.symm r)

theorem pushVec_pullVec (E : d ≃ Fin K) (v : Fin K → ℂ) : pushVec E (pullVec E v) = v := by
  funext r
  rw [pushVec, pullVec, Equiv.apply_symm_apply]

theorem dist_eucVec_pullVec (E : d ≃ Fin K) (u v : Fin K → ℂ) :
    dist (eucVec (pullVec E u)) (eucVec (pullVec E v)) = dist (eucVec u) (eucVec v) := by
  rw [dist_eucVec, dist_eucVec]
  refine congrArg Real.sqrt ?_
  exact Equiv.sum_comp E (fun r => ‖u r - v r‖ ^ (2 : ℕ))

/-- The synthesis alphabet transported to an arbitrary finite register. -/
def transportAct (E : d ≃ Fin K) (m : ℕ) :
    SynthLetter K m → EuclideanSpace ℂ d → EuclideanSpace ℂ d :=
  fun g x => eucVec (pullVec E (synthGate K m g (pushVec E (WithLp.ofLp x))))

theorem transportAct_eucVec_pullVec (E : d ≃ Fin K) (m : ℕ) (g : SynthLetter K m)
    (v : Fin K → ℂ) :
    transportAct E m g (eucVec (pullVec E v)) = eucVec (pullVec E (synthGate K m g v)) := by
  rw [transportAct]
  congr 2
  rw [show WithLp.ofLp (eucVec (pullVec E v)) = pullVec E v from rfl, pushVec_pullVec]

theorem wordAct_transportAct (E : d ≃ Fin K) (m : ℕ) :
    ∀ (w : List (SynthLetter K m)) (v : Fin K → ℂ),
      wordAct (transportAct E m) w (eucVec (pullVec E v))
        = eucVec (pullVec E (synthWordFn K m w v))
  | [], v => by rw [wordAct_nil, synthWordFn_nil]
  | g :: w, v => by
      rw [wordAct_cons, wordAct_transportAct E m w v, synthWordFn_cons,
        transportAct_eucVec_pullVec]

end Transport


section Certificate

variable {d : Type} [Fintype d] [DecidableEq d]

theorem sum_normSq_ofLp_eq_one {ψ : EuclideanSpace ℂ d} (hψ : ‖ψ‖ = 1) :
    ∑ r, ‖WithLp.ofLp ψ r‖ ^ (2 : ℕ) = 1 := by
  have h : Real.sqrt (∑ r, ‖WithLp.ofLp ψ r‖ ^ (2 : ℕ)) = 1 := by
    rw [← hψ, EuclideanSpace.norm_eq]
  have hnn : (0 : ℝ) ≤ ∑ r, ‖WithLp.ofLp ψ r‖ ^ (2 : ℕ) := by positivity
  nlinarith [Real.sq_sqrt hnn, h]

/-- **The uniform state-synthesis cap.**  Every finite register carries a finite gate alphabet and
a single reference state whose words of length at most twice the dimension reach every pure state
of the register to within a prescribed tolerance. -/
theorem exists_universal_synthesis_certificate (d : Type) [Fintype d] [DecidableEq d]
    [Nonempty d] {eta : ℝ} (heta : 0 < eta) :
    ∃ (Γ : Type) (act : Γ → EuclideanSpace ℂ d → EuclideanSpace ℂ d)
      (chi : EuclideanSpace ℂ d),
      ∀ ψ : EuclideanSpace ℂ d, ‖ψ‖ = 1 →
        ∃ w : List Γ, w.length ≤ 2 * Fintype.card d ∧ dist ψ (wordAct act w chi) ≤ eta := by
  classical
  obtain ⟨E⟩ : Nonempty (d ≃ Fin (Fintype.card d)) := ⟨Fintype.equivFin d⟩
  have hK : 0 < Fintype.card d := Fintype.card_pos
  obtain ⟨m, hm, hsynth⟩ := exists_synthesis_alphabet (Fintype.card d) hK heta
  refine ⟨SynthLetter (Fintype.card d) m, transportAct E m,
    eucVec (pullVec E (unitBasisFirst (Fintype.card d))), fun ψ hψ => ?_⟩
  obtain ⟨w, hwlen, hwdist⟩ := hsynth (pushVec E (WithLp.ofLp ψ))
    (by
      rw [← sum_normSq_ofLp_eq_one hψ]
      exact Equiv.sum_comp E.symm (fun i => ‖WithLp.ofLp ψ i‖ ^ (2 : ℕ)))
  refine ⟨w, hwlen, ?_⟩
  rw [wordAct_transportAct, dist_comm]
  have hpull : eucVec (pullVec E (pushVec E (WithLp.ofLp ψ))) = ψ := by
    rw [← eucVec_ofLp ψ]
    congr 1
    funext i
    rw [pullVec, pushVec, Equiv.symm_apply_apply]
    rfl
  calc dist (eucVec (pullVec E (synthWordFn (Fintype.card d) m w
          (unitBasisFirst (Fintype.card d))))) ψ
      = dist (eucVec (pullVec E (synthWordFn (Fintype.card d) m w
          (unitBasisFirst (Fintype.card d)))))
        (eucVec (pullVec E (pushVec E (WithLp.ofLp ψ)))) := by rw [hpull]
    _ = dist (eucVec (synthWordFn (Fintype.card d) m w (unitBasisFirst (Fintype.card d))))
        (eucVec (pushVec E (WithLp.ofLp ψ))) := dist_eucVec_pullVec E _ _
    _ ≤ eta := by
        rw [← wordAct_synthAct_eucVec]
        exact hwdist

/-- **The synthesis cap along every orbit.**  One alphabet certifies the orbit of every
self-adjoint Hamiltonian from every unit seed at every time. -/
theorem exists_orbit_synthesis_certificate (d : Type) [Fintype d] [DecidableEq d]
    [Nonempty d] {eta : ℝ} (heta : 0 < eta) :
    ∃ (Γ : Type) (act : Γ → EuclideanSpace ℂ d → EuclideanSpace ℂ d)
      (chi : EuclideanSpace ℂ d),
      ∀ (H : Matrix d d ℂ), IsSelfAdjoint H → ∀ ψ : EuclideanSpace ℂ d, ‖ψ‖ = 1 → ∀ s : ℝ,
        ∃ w : List Γ, w.length ≤ 2 * Fintype.card d ∧
          dist (orbitState H ψ s) (wordAct act w chi) ≤ eta := by
  classical
  obtain ⟨Γ, act, chi, hcert⟩ := exists_universal_synthesis_certificate d heta
  refine ⟨Γ, act, chi, fun H hH ψ hψ s => hcert (orbitState H ψ s) ?_⟩
  have hself : finiteComplexInner (WithLp.ofLp (orbitState H ψ s))
      (WithLp.ofLp (orbitState H ψ s)) = 1 := by
    have hstep : WithLp.ofLp (orbitState H ψ s)
        = Matrix.mulVec (unitaryEvolution H s) (WithLp.ofLp ψ) := rfl
    rw [hstep, finiteComplexInner_unitaryEvolution_self hH]
    have hcast : finiteComplexInner (WithLp.ofLp ψ) (WithLp.ofLp ψ)
        = ((∑ r, ‖WithLp.ofLp ψ r‖ ^ (2 : ℕ) : ℝ) : ℂ) := by
      rw [finiteComplexInner, Complex.ofReal_sum]
      refine Finset.sum_congr rfl fun r _ => ?_
      rw [← Complex.normSq_eq_conj_mul_self, Complex.sq_norm]
    rw [hcast, sum_normSq_ofLp_eq_one hψ]
    norm_num
  rw [← eucVec_ofLp (orbitState H ψ s)]
  exact norm_eucVec_eq_one hself

end Certificate

end GaloisForLFunctions.HTGeometry

end
