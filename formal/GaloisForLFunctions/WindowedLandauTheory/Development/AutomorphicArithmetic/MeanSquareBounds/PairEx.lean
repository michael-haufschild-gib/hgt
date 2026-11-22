import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PairExOfProgressions
import GaloisForLFunctions.WindowedLandauTheory.Development.AutomorphicArithmetic.MeanSquareBounds.PrimeProgressions.RelativePrimeNumberTheorem

/-! Auxiliary primes whose twists have zero-free boxes and square-root window bounds. -/

theorem QH.pairEx : UpperTheory.Top.PairEx :=
  QH.pairEx_of_progressions QH.PrimeProgressions.pnt_progressions_relative_weak_holds
