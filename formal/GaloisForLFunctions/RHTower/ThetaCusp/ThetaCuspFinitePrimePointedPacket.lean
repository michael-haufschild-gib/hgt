import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFinitePrimeResolvent
import GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspFinitePrimePositiveScreen
import GaloisForLFunctions.HTGeometry.GammaProjectivePrimeTorusCarrier

/-!
# Pointed finite-prime theta cusp packet

The completed scalar screen does not erase its construction data: packet keeps marked prime set,
actual physical resolvent, unscreened source, cutoff, both one-sided traces, and FE average together.
-/

noncomputable section

namespace RHTower

/-- Literal pointed incidence packet retained behind one completed finite-prime theta screen. -/
structure FinitePrimeThetaCuspPointedPacket where
  markedPrimes : Finset Nat.Primes
  seed : ℝ → ℝ
  resolvent : evenSubspace →L[ℂ] evenSubspace
  unscreenedSource : ℝ → ℝ
  cutoff : ℝ → ℝ
  rightScreen : ℝ → ℝ
  reflectedRightScreen : ℝ → ℝ
  completedScreen : ℝ → ℝ

/-- Actual packet `(P_N,a,R_N(1/2),k_N,η_j,r_j,r_j∘(-·),g_j)` at screen stage `j`. -/
def finitePrimeThetaCuspPointedPacket (j : ℕ) :
    FinitePrimeThetaCuspPointedPacket where
  markedPrimes := GaloisForLFunctions.primesLE
    (finitePrimeThetaCuspPositiveScreenIndex j)
  seed := thetaCuspLogSeed
  resolvent := finitePrimeEvenResolvent
    (finitePrimeThetaCuspPositiveScreenIndex j)
  unscreenedSource := finitePrimeThetaCuspSource
    (finitePrimeThetaCuspPositiveScreenIndex j)
  cutoff := finitePrimeThetaCuspScreenCutoff j
  rightScreen := finitePrimeThetaCuspRightScreen j
  reflectedRightScreen := fun x => finitePrimeThetaCuspRightScreen j (-x)
  completedScreen := finitePrimeThetaCuspEvenScreen j

/-- Packet retains exactly `π(N_j)` individually marked prime coordinates. -/
theorem finitePrimeThetaCuspPointedPacket_markedPrimes_card (j : ℕ) :
    (finitePrimeThetaCuspPointedPacket j).markedPrimes.card =
      Nat.primeCounting (finitePrimeThetaCuspPositiveScreenIndex j) := by
  exact GaloisForLFunctions.primesLE_card _

/-- Completed scalar trace is the FE average of the packet's two one-sided marked traces. -/
theorem finitePrimeThetaCuspPointedPacket_completedScreen_eq (j : ℕ) (x : ℝ) :
    (finitePrimeThetaCuspPointedPacket j).completedScreen x =
      ((finitePrimeThetaCuspPointedPacket j).rightScreen x +
        (finitePrimeThetaCuspPointedPacket j).reflectedRightScreen x) / 2 := by
  rfl

/-- Unscreened packet component is exactly the selected prime resolvent source. -/
theorem finitePrimeThetaCuspPointedPacket_unscreened_eq (j : ℕ) :
    (finitePrimeThetaCuspPointedPacket j).unscreenedSource =
      finitePrimeThetaCuspResolventSeries
        (finitePrimeThetaCuspPositiveScreenIndex j) thetaCuspLogSeed := by
  funext x
  exact finitePrimeThetaCuspResolventSeries_seed_eq_source
    (finitePrimeThetaCuspPositiveScreenIndex j) x |>.symm

end RHTower
