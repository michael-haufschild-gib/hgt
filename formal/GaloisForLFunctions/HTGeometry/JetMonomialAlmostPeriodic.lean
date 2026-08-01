import GaloisForLFunctions.HTGeometry.VerticalAlmostPeriodicDerivative
import GaloisForLFunctions.HTGeometry.LineJetTransfer

/-!
# Jet monomials of a strip almost periodic function

Powers and finite products of continuous almost periodic functions are almost periodic, the corpus's
product law applying inductively.  The jets of a strip almost periodic holomorphic function restrict
to continuous almost periodic functions on the central line, so every monomial in those jets is
continuous and almost periodic there.

These are exactly the monomials of an algebraic differential relation, so the recurrence collapse
needs no hypothesis about them beyond the strip almost periodicity of the solution itself.
-/

open Filter Topology Finset

namespace GaloisForLFunctions

open _root_.HTGeometry

variable {σ R : ℝ}

/-- Powers of a continuous almost periodic function are almost periodic. -/
theorem isBohrAlmostPeriodic_pow {g : ℝ → ℂ} (hc : Continuous g) (ha : IsBohrAlmostPeriodic g) :
    ∀ k : ℕ, IsBohrAlmostPeriodic fun t => (g t) ^ k := by
  intro k
  induction k with
  | zero =>
      intro ε hε
      refine ⟨1, one_pos, fun a => ⟨a, ⟨le_refl a, by linarith⟩, fun x => ?_⟩⟩
      simp [hε.le]
  | succ j ih =>
      have hcj : Continuous fun t => (g t) ^ j := hc.pow j
      have hfun : (fun t => (g t) ^ (j + 1)) = fun t => (g t) ^ j * g t := by
        funext t
        rw [pow_succ]
      rw [hfun]
      exact isBohrAlmostPeriodic_mul hcj ih hc ha

/-- Finite products of continuous almost periodic functions are almost periodic. -/
theorem isBohrAlmostPeriodic_finsetProd {ι : Type*} (s : Finset ι) (g : ι → ℝ → ℂ)
    (hc : ∀ i, Continuous (g i)) (ha : ∀ i, IsBohrAlmostPeriodic (g i)) :
    IsBohrAlmostPeriodic fun t => ∏ i ∈ s, g i t := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      intro ε hε
      refine ⟨1, one_pos, fun a => ⟨a, ⟨le_refl a, by linarith⟩, fun x => ?_⟩⟩
      simp [hε.le]
  | insert i s hi ih =>
      have hcs : Continuous fun t => ∏ j ∈ s, g j t :=
        continuous_finsetProd _ fun j _ => hc j
      have hfun : (fun t => ∏ j ∈ insert i s, g j t) = fun t => g i t * ∏ j ∈ s, g j t := by
        funext t
        rw [Finset.prod_insert hi]
      rw [hfun]
      exact isBohrAlmostPeriodic_mul (hc i) (ha i) hcs ih

/-- **Jet monomials of a strip almost periodic function are almost periodic on the line.** -/
theorem isBohrAlmostPeriodic_jetMonomial {F : ℂ → ℂ} (hR : 0 < R)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R)) (hap : IsStripAlmostPeriodic F σ R)
    {m : ℕ} (e : Fin m → ℕ) :
    Continuous (fun t : ℝ =>
        ∏ j : Fin m, (iteratedDeriv (j : ℕ) F ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ (e j)) ∧
      IsBohrAlmostPeriodic (fun t : ℝ =>
        ∏ j : Fin m, (iteratedDeriv (j : ℕ) F ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ (e j)) := by
  have hjetc : ∀ j : Fin m, Continuous fun t : ℝ =>
      iteratedDeriv (j : ℕ) F ((σ : ℂ) + (t : ℂ) * Complex.I) := fun j =>
    continuous_line_restriction hR (isStripAlmostPeriodic_iteratedDeriv hF hap (j : ℕ)).1
  have hjeta : ∀ j : Fin m, IsBohrAlmostPeriodic fun t : ℝ =>
      iteratedDeriv (j : ℕ) F ((σ : ℂ) + (t : ℂ) * Complex.I) := fun j =>
    isBohrAlmostPeriodic_line hR (isStripAlmostPeriodic_iteratedDeriv hF hap (j : ℕ)).2
  constructor
  · exact continuous_finsetProd _ fun j _ => (hjetc j).pow (e j)
  · have hfamc : ∀ j : Fin m, Continuous
        (fun t : ℝ => (iteratedDeriv (j : ℕ) F ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ (e j)) :=
      fun j => (hjetc j).pow (e j)
    have hfam : ∀ j : Fin m, IsBohrAlmostPeriodic
        (fun t : ℝ => (iteratedDeriv (j : ℕ) F ((σ : ℂ) + (t : ℂ) * Complex.I)) ^ (e j)) :=
      fun j => isBohrAlmostPeriodic_pow (hjetc j) (hjeta j) (e j)
    exact isBohrAlmostPeriodic_finsetProd (Finset.univ : Finset (Fin m)) _ hfamc hfam

end GaloisForLFunctions
