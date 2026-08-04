import GaloisForLFunctions.HTGeometry.EntireValence
import GaloisForLFunctions.HTGeometry.AnalyticMeroPolynomialEval
import GaloisForLFunctions.HTGeometry.OneVariableMvPolynomial
import GaloisForLFunctions.HTGeometry.PrefixStateIndependence
import Mathlib.LinearAlgebra.Lagrange

/-!
# The states of an entire cascade are algebraically independent

The iterates of a sequence of transcendental entire functions are algebraically independent over the
constants, with no growth, value-distribution or differential hypothesis.

The proof is an induction on the length of the cascade which peels off the *first* edge.  Writing the
states as `z, f₀ z, f₁(f₀ z), …`, every state but the coordinate is a function of `f₀ z`, so on a fibre
of `f₀` a relation collapses to a polynomial in the coordinate alone.  A transcendental entire function
has fibres of unbounded size — and the values with large fibres form an open set — so that polynomial
has more roots than its degree and vanishes identically.  Each of its coefficients is then a relation
among the states of the shifted cascade, valid on an open set of values and hence everywhere, which the
induction hypothesis forbids.
-/

namespace GaloisForLFunctions.HTGeometry

open GaloisForLFunctions

/-- Peeling the first edge: the `(k+1)`-st state of a cascade is the `k`-th state of the shifted
cascade, evaluated at the first constituent. -/
theorem entireCascade_succ_shift (f : ℕ → ℂ → ℂ) (k : ℕ) (z : ℂ) :
    entireCascade f (k + 1) z = entireCascade (fun i => f (i + 1)) k (f 0 z) := by
  induction k with
  | zero => simp
  | succ k ih =>
      have h1 : entireCascade f (k + 1 + 1) z = f (k + 1) (entireCascade f (k + 1) z) := rfl
      have h2 : entireCascade (fun i => f (i + 1)) (k + 1) (f 0 z)
          = f (k + 1) (entireCascade (fun i => f (i + 1)) k (f 0 z)) := rfl
      rw [h1, h2, ih]

/-- **Algebraic independence of the states of an entire cascade.**  No nonzero polynomial vanishes on
the iterates of a sequence of transcendental entire functions. -/
theorem noRelation_entireCascade_of_transcendental :
    ∀ (m : ℕ) (f : ℕ → ℂ → ℂ), (∀ i : ℕ, TranscendentalEntire (f i)) →
      ∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 →
        ¬ (∀ z : ℂ, MvPolynomial.eval (fun j : Fin m => entireCascade f (j : ℕ) z) P = 0) := by
  intro m
  induction m with
  | zero =>
      intro f _ P hP hrel
      have heq : (MvPolynomial.eval (fun j : Fin 0 => entireCascade f (j : ℕ) (0 : ℂ)) :
            MvPolynomial (Fin 0) ℂ →+* ℂ)
          = (MvPolynomial.isEmptyRingEquiv ℂ (Fin 0) : MvPolynomial (Fin 0) ℂ →+* ℂ) :=
        eval_empty_eq _
      have hz : (MvPolynomial.isEmptyRingEquiv ℂ (Fin 0) : MvPolynomial (Fin 0) ℂ →+* ℂ) P = 0 := by
        rw [← heq]
        exact hrel 0
      exact hP ((MvPolynomial.isEmptyRingEquiv ℂ (Fin 0)).injective (by simpa using hz))
  | succ m ih =>
      intro f hall P hP hrel
      set f' : ℕ → ℂ → ℂ := fun i => f (i + 1) with hf'
      have hall' : ∀ i : ℕ, TranscendentalEntire (f' i) := fun i => hall (i + 1)
      have hf'an : ∀ i : ℕ, AnalyticOnNhd ℂ (f' i) (Set.univ : Set ℂ) := by
        intro i
        exact DifferentiableOn.analyticOnNhd
          (fun z _ => ((hall' i).1 z).differentiableWithinAt) isOpen_univ
      set Q : Polynomial (MvPolynomial (Fin m) ℂ) := MvPolynomial.finSuccEquiv ℂ m P with hQdef
      have hQ0 : Q ≠ 0 := by
        intro h
        refine hP ((MvPolynomial.finSuccEquiv ℂ m).injective ?_)
        rw [← hQdef, h, map_zero]
      -- a value of the first constituent with more preimages than the degree
      obtain ⟨U, R, hU, hUne, hmany⟩ := exists_open_many_preimages (hall 0) (Q.natDegree + 1)
      -- on such a fibre the relation is a polynomial in the coordinate with too many roots
      have hcoeff : ∀ u ∈ U, ∀ i : ℕ,
          MvPolynomial.eval (fun j : Fin m => entireCascade f' (j : ℕ) u) (Q.coeff i) = 0 := by
        intro u hu i
        obtain ⟨T, hTcard, _, hTf⟩ := hmany u hu
        set p : Polynomial ℂ :=
          Polynomial.map (MvPolynomial.eval (fun j : Fin m => entireCascade f' (j : ℕ) u)) Q
          with hpdef
        have hroots : ∀ x ∈ T, p.eval x = 0 := by
          intro x hx
          have hfx : f 0 x = u := hTf x hx
          have hxrel := hrel x
          have hcons : (fun j : Fin (m + 1) => entireCascade f (j : ℕ) x)
              = Fin.cons x (fun j : Fin m => entireCascade f' (j : ℕ) u) := by
            funext j
            refine Fin.cases ?_ ?_ j
            · simp
            · intro i'
              rw [Fin.cons_succ]
              have hval : ((i'.succ : Fin (m + 1)) : ℕ) = (i' : ℕ) + 1 := rfl
              rw [hval, entireCascade_succ_shift, hfx]
          rw [hcons, MvPolynomial.eval_eq_eval_mv_eval'] at hxrel
          rw [hpdef, hQdef]
          exact hxrel
        have hdeg : p.degree < (T.card : ℕ) := by
          by_cases hp0 : p = 0
          · rw [hp0, Polynomial.degree_zero]
            exact WithBot.bot_lt_coe _
          · rw [Polynomial.degree_eq_natDegree hp0]
            have h1 : p.natDegree ≤ Q.natDegree := by
              rw [hpdef]
              exact Polynomial.natDegree_map_le
            exact_mod_cast lt_of_le_of_lt h1 (by omega)
        have hp0 : p = 0 := Polynomial.eq_zero_of_degree_lt_of_eval_finset_eq_zero T hdeg hroots
        have hci := congrArg (fun q : Polynomial ℂ => q.coeff i) hp0
        simpa [hpdef, Polynomial.coeff_map] using hci
      -- an analytic identity valid on an open set is valid everywhere
      have hzero : ∀ i : ℕ, ∀ u : ℂ,
          MvPolynomial.eval (fun j : Fin m => entireCascade f' (j : ℕ) u) (Q.coeff i) = 0 := by
        intro i
        obtain ⟨u₀, hu₀⟩ := hUne
        have han : AnalyticOnNhd ℂ
            (fun u => MvPolynomial.eval
              (fun j : Fin m => entireCascade f' (j : ℕ) u) (Q.coeff i))
            (Set.univ : Set ℂ) :=
          analyticOnNhd_eval_mvPolynomial (fun j : Fin m => entireCascade f' (j : ℕ))
            (fun j => analyticOnNhd_entireCascade hf'an _) (Q.coeff i)
        have hev : (fun u => MvPolynomial.eval
            (fun j : Fin m => entireCascade f' (j : ℕ) u) (Q.coeff i)) =ᶠ[nhds u₀] 0 := by
          filter_upwards [hU.mem_nhds hu₀] with u hu
          exact hcoeff u hu i
        have heq := han.eqOn_zero_of_preconnected_of_eventuallyEq_zero
          isPreconnected_univ (Set.mem_univ u₀) hev
        intro u
        exact heq (Set.mem_univ u)
      -- every coefficient is a relation among the states of the shifted cascade
      refine hQ0 (Polynomial.ext ?_)
      intro i
      by_contra hne
      exact ih f' hall' (Q.coeff i) hne (hzero i)

/-- **State independence for a prefix family.**  The corpus's independence predicate, discharged
outright for a cascade of transcendental entire functions. -/
theorem noRelation_prefixFamily_of_transcendental (f : ℕ → ℂ → ℂ)
    (hall : ∀ i : ℕ, TranscendentalEntire (f i)) (m : ℕ) :
    ∀ P : MvPolynomial (Fin m) ℂ, P ≠ 0 →
      ¬ (∀ z : ℂ, MvPolynomial.eval
        (fun j => prefixFamily (entireCascade f) m j z) P = 0) :=
  noRelation_entireCascade_of_transcendental m f hall

end GaloisForLFunctions.HTGeometry
