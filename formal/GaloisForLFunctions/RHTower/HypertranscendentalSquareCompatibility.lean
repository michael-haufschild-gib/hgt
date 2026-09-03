import GaloisForLFunctions.HTGeometry.AnalyticJetFieldBridge
import GaloisForLFunctions.HTGeometry.ScalarLogCurrentReconstruction
import GaloisForLFunctions.HTGeometry.DifferentialAlgebraicOnClosure
import GaloisForLFunctions.HTGeometry.FamilyPowerGauge
import GaloisForLFunctions.RHTower.RHLadderTheory

/-!
# Hypertranscendence is compatible with analytic squares

The report's differential-Galois step proposes hypertranscendence as a possible veto against a
square-root carrier.  The implication runs in the opposite direction: for an entire function `g`,
`g` is hypertranscendental exactly when its square is hypertranscendental.

The easy direction uses closure of differential algebraicity under multiplication.  The converse
passes to the global meromorphic differential field, where every positive power of a
hypertranscendental element remains hypertranscendental, and then returns through the exact global
analytic-jet bridge. The same equivalence holds on every nonempty connected open domain, hence in
particular on the strict right half-plane relevant to the Xi square-root problem. Thus even a proof
that Xi is hypertranscendental could not exclude an entire or half-plane analytic square-root
mechanism on differential-algebraic grounds.
-/

namespace RHTower

open GaloisForLFunctions
open GaloisForLFunctions.HTGeometry
open Bottcher
open scoped Differential

noncomputable section

/-- The square of an entire hypertranscendental function is hypertranscendental. -/
theorem hypertranscendental_square_of_entire {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (Set.univ : Set ℂ))
    (hHT : Hypertranscendental g) :
    Hypertranscendental (fun z => g z * g z) := by
  letI := Bottcher.isDomain_analyticSubring (Set.univ : Set ℂ) isOpen_univ
    isPreconnected_univ Set.univ_nonempty
  letI : Algebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
    (ratfuncToMero (Set.univ : Set ℂ) isOpen_univ isPreconnected_univ Set.univ_nonempty
      Set.infinite_univ).toAlgebra
  letI : Differential (RatFunc ℂ) := ratFuncCoordinateDifferential
  letI := meroFieldDifferential (U := (Set.univ : Set ℂ)) isOpen_univ isPreconnected_univ
    Set.univ_nonempty
  letI : DifferentialAlgebra (RatFunc ℂ) (meroField (Set.univ : Set ℂ)) :=
    meroFieldRatFuncDifferentialAlgebra isOpen_univ isPreconnected_univ Set.univ_nonempty
      Set.infinite_univ
  letI : CharZero (meroField (Set.univ : Set ℂ)) :=
    charZero_of_injective_algebraMap
      (algebraMap (RatFunc ℂ) (meroField (Set.univ : Set ℂ))).injective
  have hmeroHT : HypertranscendentalOver (RatFunc ℂ) (analyticMeroElement g hg) := by
    intro hDA
    exact hHT
      (differentiallyAlgebraic_of_differentialAlgebraicOver_analyticMeroElement hg hDA)
  have hsqMeroHT :
      HypertranscendentalOver (RatFunc ℂ) ((analyticMeroElement g hg) ^ 2) :=
    hypertranscendentalOver_pow_of_pos (N := 2) hmeroHT (by norm_num)
  intro hsqDA
  apply hsqMeroHT
  rw [pow_two, ← analyticMeroElement_mul hg hg]
  exact differentialAlgebraicOver_analyticMeroElement_of_differentiallyAlgebraic
    (hg.mul hg) hsqDA

/-- For entire functions, hypertranscendence is unchanged by squaring. -/
theorem hypertranscendental_square_iff_of_entire {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g (Set.univ : Set ℂ)) :
    Hypertranscendental (fun z => g z * g z) ↔ Hypertranscendental g := by
  constructor
  · intro hsq hDA
    exact hsq (differentiallyAlgebraic_mul hg hg hDA hDA)
  · exact hypertranscendental_square_of_entire hg

/-- On any nonempty connected open domain, an analytic function satisfies no algebraic
differential equation exactly when its square satisfies none. -/
theorem not_differentiallyAlgebraicOn_square_iff
    {U : Set ℂ} (hUo : IsOpen U) (hUc : IsPreconnected U)
    (hUne : U.Nonempty) (hUinf : U.Infinite) {g : ℂ → ℂ}
    (hg : AnalyticOnNhd ℂ g U) :
    (¬ DifferentiallyAlgebraicOn (fun z => g z * g z) U) ↔
      ¬ DifferentiallyAlgebraicOn g U := by
  constructor
  · intro hsq hDA
    exact hsq (differentiallyAlgebraicOn_mul hUo hUc hUne hUinf hg hg hDA hDA)
  · intro hHT
    have hpow := not_differentiallyAlgebraicOn_pow (N := 2) (by norm_num)
      (fun z hz => (hg z hz).contDiffAt) hHT
    simpa only [pow_two] using hpow

/-- Squaring changes no differential-algebraic phase on `Re s > 1/2`, the exact domain of the
desired Xi half-divisor carrier. -/
theorem not_differentiallyAlgebraicOn_square_rightHalf_iff
    {g : ℂ → ℂ} (hg : AnalyticOnNhd ℂ g rightHalf) :
    (¬ DifferentiallyAlgebraicOn (fun z => g z * g z) rightHalf) ↔
      ¬ DifferentiallyAlgebraicOn g rightHalf := by
  have hnonempty : rightHalf.Nonempty := by
    refine ⟨2, ?_⟩
    change 1 / 2 < ((2 : ℂ).re)
    norm_num
  have hinjective : Function.Injective (fun n : ℕ => (n : ℂ) + 1) := by
    intro m n h
    have hre : (m : ℝ) + 1 = (n : ℝ) + 1 := by
      simpa using congrArg Complex.re h
    exact_mod_cast (add_right_cancel hre)
  have hrange : Set.range (fun n : ℕ => (n : ℂ) + 1) ⊆ rightHalf := by
    rintro _ ⟨n, rfl⟩
    change 1 / 2 < (n : ℝ) + 1
    have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hinfinite : rightHalf.Infinite :=
    (Set.infinite_range_of_injective hinjective).mono hrange
  exact not_differentiallyAlgebraicOn_square_iff isOpen_rightHalf
    convex_rightHalf.isPreconnected hnonempty hinfinite hg

end

end RHTower
