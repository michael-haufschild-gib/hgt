import GaloisForLFunctions.HTGeometry.Hypertranscendence
import GaloisForLFunctions.HTGeometry.AutonomousSeparant

/-!
# Autonomous equations witness differential algebraicity

An autonomous annihilator — a nonzero univariate polynomial over the lower-jet ring vanishing
along the jets of `f` — embeds into the full jet frame (with its point slot) as a nonzero
differential polynomial annihilating `f`.  The embedding sends the coefficient variables to
the corresponding jet slots and the polynomial variable to the top jet slot; a retraction
(kill the point slot, restore the top jet as the polynomial variable) shows it preserves
nonzeroness, with no injectivity theory needed.

* `differentiallyAlgebraic_of_autonomous` — a nonzero autonomous annihilator of any order
  makes `f` differentially algebraic.
* `Hypertranscendental.autonomousAnnihilator_eq_zero` — contrapositive: a hypertranscendental
  function satisfies **no** nonzero autonomous algebraic differential equation of any order.
-/

open MvPolynomial

namespace GaloisForLFunctions

/-- Jet-slot embedding: the `j`-th lower-jet variable goes to slot `j+1` of the full frame. -/
def jetIncl (n : ℕ) : Fin n → Fin (n + 2) := fun j => j.succ.castSucc

/-- Embedding of an autonomous equation into the full jet frame: coefficients through the
jet-slot renaming, the polynomial variable to the top jet slot. -/
noncomputable def autonomousToJet (n : ℕ) :
    Polynomial (MvPolynomial (Fin n) ℂ) →+* MvPolynomial (Fin (n + 2)) ℂ :=
  Polynomial.eval₂RingHom ((rename (jetIncl n)).toRingHom : MvPolynomial (Fin n) ℂ →+* _)
    (X (Fin.last (n + 1)))

/-- Retraction of the embedding: kill the point slot, send jet slot `j+1` back to the `j`-th
coefficient variable and the top slot back to the polynomial variable. -/
noncomputable def jetToAutonomous (n : ℕ) :
    MvPolynomial (Fin (n + 2)) ℂ →+* Polynomial (MvPolynomial (Fin n) ℂ) :=
  (aeval (Fin.cases 0 (Fin.lastCases Polynomial.X
    (fun j => Polynomial.C (X j)))) : MvPolynomial (Fin (n + 2)) ℂ →ₐ[ℂ] _).toRingHom

theorem jetToAutonomous_comp_autonomousToJet (n : ℕ)
    (P : Polynomial (MvPolynomial (Fin n) ℂ)) :
    jetToAutonomous n (autonomousToJet n P) = P := by
  have hhom : (jetToAutonomous n).comp (autonomousToJet n)
      = RingHom.id (Polynomial (MvPolynomial (Fin n) ℂ)) := by
    apply Polynomial.ringHom_ext
    · intro a
      simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [show autonomousToJet n (Polynomial.C a) = rename (jetIncl n) a from
        Polynomial.eval₂_C _ _]
      induction a using MvPolynomial.induction_on with
      | C c => simp [jetToAutonomous, algebraMap_eq]
      | add p q hp hq => simp [map_add, hp, hq]
      | mul_X p j hp =>
        have hX : jetToAutonomous n (X (jetIncl n j) : MvPolynomial (Fin (n + 2)) ℂ)
            = Polynomial.C (X j) := by
          show aeval _ (X (jetIncl n j)) = _
          rw [aeval_X]
          simp only [jetIncl, ← Fin.succ_castSucc, Fin.cases_succ, Fin.lastCases_castSucc]
        simp only [map_mul, rename_X]
        rw [hX, hp]
    · simp only [RingHom.comp_apply, RingHom.id_apply]
      rw [show autonomousToJet n Polynomial.X = X (Fin.last (n + 1)) from
        Polynomial.eval₂_X _ _]
      show aeval _ (X (Fin.last (n + 1))) = _
      rw [aeval_X]
      simp only [← Fin.succ_last, Fin.cases_succ, Fin.lastCases_last]
  calc jetToAutonomous n (autonomousToJet n P)
      = ((jetToAutonomous n).comp (autonomousToJet n)) P := rfl
    _ = P := by rw [hhom, RingHom.id_apply]

/-- **A nonzero autonomous equation witnesses differential algebraicity.** -/
theorem differentiallyAlgebraic_of_autonomous {f : ℂ → ℂ} {n : ℕ}
    {P : Polynomial (MvPolynomial (Fin n) ℂ)} (hP : P ≠ 0)
    (hA : AutonomousAnnihilator f n P) : DifferentiallyAlgebraic f := by
  refine ⟨n, autonomousToJet n P, ?_, ?_⟩
  · intro h0
    apply hP
    rw [← jetToAutonomous_comp_autonomousToJet n P, h0, map_zero]
  · intro z
    have hcomp : (MvPolynomial.eval
        (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z))).comp
        ((rename (jetIncl n)).toRingHom : MvPolynomial (Fin n) ℂ →+* _)
        = MvPolynomial.eval (fun j : Fin n => iteratedDeriv (j : ℕ) f z) := by
      refine RingHom.ext fun a => ?_
      simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
      rw [eval_rename]
      have hfun : ((Fin.cons z fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z) ∘ jetIncl n)
          = fun j : Fin n => iteratedDeriv (j : ℕ) f z := by
        funext j
        simp only [Function.comp_apply, jetIncl, ← Fin.succ_castSucc, Fin.cons_succ,
          Fin.val_castSucc]
      rw [hfun]
    have hlast : MvPolynomial.eval
        (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z))
        (X (Fin.last (n + 1))) = iteratedDeriv n f z := by
      rw [eval_X]
      simp only [← Fin.succ_last, Fin.cons_succ, Fin.val_last]
    have h := Polynomial.hom_eval₂ P
      ((rename (jetIncl n)).toRingHom : MvPolynomial (Fin n) ℂ →+* _)
      (MvPolynomial.eval
        (Fin.cons z (fun j : Fin (n + 1) => iteratedDeriv (j : ℕ) f z)))
      (X (Fin.last (n + 1)))
    show MvPolynomial.eval _ (autonomousToJet n P) = 0
    rw [show autonomousToJet n P = Polynomial.eval₂
        ((rename (jetIncl n)).toRingHom : MvPolynomial (Fin n) ℂ →+* _)
        (X (Fin.last (n + 1))) P from rfl, h, hcomp, hlast]
    exact hA z

/-- **A hypertranscendental function admits no nonzero autonomous equation of any order.** -/
theorem Hypertranscendental.autonomousAnnihilator_eq_zero {f : ℂ → ℂ}
    (hf : Hypertranscendental f) {n : ℕ} {P : Polynomial (MvPolynomial (Fin n) ℂ)}
    (hA : AutonomousAnnihilator f n P) : P = 0 := by
  by_contra hP
  exact hf (differentiallyAlgebraic_of_autonomous hP hA)

end GaloisForLFunctions
