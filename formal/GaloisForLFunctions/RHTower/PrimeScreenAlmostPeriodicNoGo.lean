import GaloisForLFunctions.HTGeometry.CompactGroupAlmostPeriodic
import GaloisForLFunctions.RHTower.ThetaCuspComplexStrip
import GaloisForLFunctions.RHTower.XiHadamardFactorization

/-!
# Bounded prime-screen observables cannot produce the completed Xi amplitude

The prime torus `∏_p S¹` carries the arithmetic Kronecker flow `t ↦ (p^{it})_p`.  Every continuous
observable of a state on that compact group has a Bohr almost periodic expectation, whereas the
completed Xi amplitude decays exponentially along the critical line and does not vanish at the
central point.  Hence no bounded continuous prime-screen observable reproduces it: an exact
completion observable must carry noncompact archimedean data.
-/

open Filter Topology MeasureTheory
open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- The prime torus: one circle of phases for each prime. -/
def PrimeTorus : Type := Nat.Primes → Circle

noncomputable instance : CommGroup PrimeTorus :=
  inferInstanceAs (CommGroup (Nat.Primes → Circle))

noncomputable instance : TopologicalSpace PrimeTorus :=
  inferInstanceAs (TopologicalSpace (Nat.Primes → Circle))

instance : IsTopologicalGroup PrimeTorus :=
  inferInstanceAs (IsTopologicalGroup (Nat.Primes → Circle))

instance : CompactSpace PrimeTorus :=
  inferInstanceAs (CompactSpace (Nat.Primes → Circle))

instance : SecondCountableTopology PrimeTorus :=
  inferInstanceAs (SecondCountableTopology (Nat.Primes → Circle))

noncomputable instance : MeasurableSpace PrimeTorus := borel PrimeTorus

instance : BorelSpace PrimeTorus := ⟨rfl⟩

/-- The arithmetic Kronecker flow `t ↦ (p^{it})_p` on the prime torus. -/
noncomputable def primeKronecker (t : ℝ) : PrimeTorus :=
  fun p : Nat.Primes => Circle.exp (t * Real.log (p : ℕ))

/-- The Kronecker flow is a one-parameter group. -/
theorem primeKronecker_add (s t : ℝ) :
    primeKronecker (s + t) = primeKronecker s * primeKronecker t := by
  funext p
  show Circle.exp ((s + t) * Real.log (p : ℕ))
    = Circle.exp (s * Real.log (p : ℕ)) * Circle.exp (t * Real.log (p : ℕ))
  rw [add_mul, Circle.exp_add]

/-- The Kronecker flow is continuous. -/
theorem continuous_primeKronecker : Continuous primeKronecker := by
  show Continuous fun t : ℝ => (fun p : Nat.Primes => Circle.exp (t * Real.log (p : ℕ)))
  exact continuous_pi fun p => Circle.exp.continuous.comp (continuous_id.mul continuous_const)

/-- **The completed Xi amplitude decays along the critical line.** -/
theorem tendsto_XiC_ofReal_atTop :
    Tendsto (fun t : ℝ => XiC ((t : ℝ) : ℂ)) atTop (𝓝 0) := by
  have hπ : (3 : ℝ) < Real.pi := Real.pi_gt_three
  obtain ⟨C, -, hbound⟩ :=
    exists_norm_XiC_ofReal_le (δ := 1 / 2) (by norm_num) (by linarith)
  refine squeeze_zero_norm (fun t => hbound t) ?_
  have hcomp : Tendsto (fun t : ℝ => -(1 / 2 * |t|)) atTop atBot := by
    have habs : Tendsto (fun t : ℝ => 1 / 2 * |t|) atTop atTop :=
      (tendsto_abs_atTop_atTop).const_mul_atTop (by norm_num)
    exact tendsto_neg_atTop_atBot.comp habs
  have : Tendsto (fun t : ℝ => Real.exp (-(1 / 2 * |t|))) atTop (𝓝 0) :=
    Real.tendsto_exp_atBot.comp hcomp
  simpa using this.const_mul C

/-- **No bounded continuous symbol on the prime torus produces the completed Xi amplitude.**
Along the Kronecker flow such a symbol is Bohr almost periodic, hence cannot both decay at
vertical infinity and be nonzero at the centre. -/
theorem not_exists_primeScreen_symbol_eq_XiC :
    ¬ ∃ g : PrimeTorus → ℂ, Continuous g ∧
      ∀ t : ℝ, g (primeKronecker t) = XiC ((t : ℝ) : ℂ) := by
  rintro ⟨g, hg, hEq⟩
  have hlim : Tendsto (fun t : ℝ => g (primeKronecker t)) atTop (𝓝 0) := by
    have := tendsto_XiC_ofReal_atTop
    refine this.congr fun t => (hEq t).symm
  have hzero := eq_zero_of_compact_flow_of_tendsto_zero primeKronecker_add hg hlim 0
  rw [hEq 0] at hzero
  exact XiC_zero_ne (by simpa using hzero)

/-- **No bounded prime-screen observable produces the completed Xi amplitude.**  The expectation
of a continuous observable in the Kronecker-translated states is almost periodic in height, while
the completed Xi amplitude decays; only a noncompact archimedean component can supply that decay. -/
theorem not_exists_primeScreen_observable_eq_XiC (μ : Measure PrimeTorus) [IsFiniteMeasure μ] :
    ¬ ∃ f : PrimeTorus → ℂ, Continuous f ∧
      ∀ t : ℝ, (∫ z, f (primeKronecker t * z) ∂μ) = XiC ((t : ℝ) : ℂ) := by
  rintro ⟨f, hf, hEq⟩
  refine not_exists_primeScreen_symbol_eq_XiC ⟨screenAverage μ f, continuous_screenAverage μ hf, ?_⟩
  intro t
  exact hEq t

end RHTower
