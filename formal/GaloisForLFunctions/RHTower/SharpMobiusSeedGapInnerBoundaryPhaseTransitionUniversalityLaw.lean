import GaloisForLFunctions.RHTower.RouteBSeedGap
import GaloisForLFunctions.RHTower.RouteBTwoField

/-!
# Sharp Möbius seed-gap inner/boundary phase-transition universality law

Sharp Möbius design annihilates every complete inner row of the Route-B two-field window.  The
same row reappears in the singleton-window boundary band with coefficient exactly equal to its
Möbius value.  Prime-packet rigidity then turns that arithmetic value into an observable
all-interval dichotomy: precisely squarefree rows carry positive boundary energy.
-/

namespace RHTower

open Complex

noncomputable section

/-- The real-valued sharp Möbius row weight. -/
def sharpMobiusRowWeight (d : ℕ) : ℝ :=
  ((ArithmeticFunction.moebius d : ℤ) : ℝ)

/-- In the complete inner range, the actual sharp Möbius seed-gap coefficient vanishes. -/
theorem sharpMobiusSeedGapCoeff_eq_zero_of_inner
    {N y d p : ℕ} (hd2 : 2 ≤ d) (hdy : d ≤ y)
    (hp : p.Prime) (hpy : y < p) (hdpN : d * p ≤ N) :
    seedGapCoeff sharpMobiusRowWeight N y (p * d) = 0 := by
  have hinner :=
    inner_row_vanishes_sharp (N := N) (z := y) (u := d) (p := p)
      hd2 hdy hp hpy hdpN
  have hnotRough :
      ¬(∀ q, q.Prime → q ∣ p * d → y < q) :=
    not_rough_of_smooth_divisor hd2 hdy (dvd_mul_left d p)
  simp only [seedGapCoeff, hnotRough, if_false, sub_zero,
    sharpMobiusRowWeight]
  simpa [Nat.mul_comm] using hinner

/-- In the singleton-window boundary range, the same row reappears with its exact Möbius
coefficient. -/
theorem sharpMobiusSeedGapCoeff_eq_rowWeight_of_boundary
    {N y d p : ℕ} (hd2 : 2 ≤ d) (hdy : d ≤ y)
    (hp : p.Prime) (hpy : y < p) (hpN : p ≤ N)
    (hbig : N < p * d.minFac) :
    seedGapCoeff sharpMobiusRowWeight N y (p * d) =
      sharpMobiusRowWeight d :=
  seedGapCoeff_eq_lam_of_singleton_boundary
    sharpMobiusRowWeight hp hpy hd2 hdy hpN hbig

/-- Every nonempty singleton-window boundary packet for a sharp row has positive interval energy
exactly when the row label is squarefree. -/
theorem sharpMobiusSeedGap_boundarySecondMoment_pos_iff_squarefree
    {N y d : ℕ} (hd2 : 2 ≤ d) (hdy : d ≤ y)
    {P : Finset ℕ} (hP : ∀ p ∈ P, p.Prime) (hPne : P.Nonempty)
    (hPy : ∀ p ∈ P, y < p) (hPN : ∀ p ∈ P, p ≤ N)
    (hbig : ∀ p ∈ P, N < p * d.minFac)
    {A B : ℝ} (hAB : A < B) :
    (0 < ∫ x in A..B,
        ‖dpoly (seedGapCoeff sharpMobiusRowWeight N y)
          (P.image (fun p => p * d)) x‖ ^ 2) ↔
      Squarefree d := by
  rw [seedGap_boundary_component_secondMoment_pos_iff
    sharpMobiusRowWeight hd2 hdy hP hPne hPy hPN hbig hAB]
  simp only [sharpMobiusRowWeight, Int.cast_ne_zero]
  exact ArithmeticFunction.moebius_ne_zero_iff_squarefree

/-- **Sharp Möbius seed-gap inner/boundary phase-transition universality law.**  Every smooth row
vanishes throughout its complete inner range, reappears with its Möbius value in the
singleton-window boundary range, and carries positive energy on every nonempty vertical interval
exactly when its row label is squarefree. -/
theorem sharpMobiusSeedGap_innerBoundaryPhaseTransitionUniversality
    {N y d : ℕ} (hd2 : 2 ≤ d) (hdy : d ≤ y) :
    (∀ {p : ℕ}, p.Prime → y < p → d * p ≤ N →
      seedGapCoeff sharpMobiusRowWeight N y (p * d) = 0) ∧
    (∀ {p : ℕ}, p.Prime → y < p → p ≤ N → N < p * d.minFac →
      seedGapCoeff sharpMobiusRowWeight N y (p * d) =
        sharpMobiusRowWeight d) ∧
    ∀ {P : Finset ℕ}, (∀ p ∈ P, p.Prime) → P.Nonempty →
      (∀ p ∈ P, y < p) → (∀ p ∈ P, p ≤ N) →
      (∀ p ∈ P, N < p * d.minFac) →
      ∀ {A B : ℝ}, A < B →
        ((0 < ∫ x in A..B,
            ‖dpoly (seedGapCoeff sharpMobiusRowWeight N y)
              (P.image (fun p => p * d)) x‖ ^ 2) ↔
          Squarefree d) := by
  refine ⟨?_, ?_, ?_⟩
  · intro p hp hpy hdpN
    exact sharpMobiusSeedGapCoeff_eq_zero_of_inner hd2 hdy hp hpy hdpN
  · intro p hp hpy hpN hbig
    exact sharpMobiusSeedGapCoeff_eq_rowWeight_of_boundary
      hd2 hdy hp hpy hpN hbig
  · intro P hP hPne hPy hPN hbig A B hAB
    exact sharpMobiusSeedGap_boundarySecondMoment_pos_iff_squarefree
      hd2 hdy hP hPne hPy hPN hbig hAB

end

end RHTower
