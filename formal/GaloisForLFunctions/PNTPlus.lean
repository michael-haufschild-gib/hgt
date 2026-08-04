/-
# PrimeNumberTheoremAnd (PNT+) vendored area umbrella

Vendored unconditional core of the PrimeNumberTheoremAnd project
(Kontorovich–Tao et al.): Selberg sieve, Brun–Titchmarsh, rectangle residue
calculus, Perron formulas, Mellin calculus, Wiener–Ikehara Tauberian theorem,
zeta bounds with an explicit zero-free region, and the prime number theorem
with error term `O(x · exp(-c (log x)^{1/10}))` (`MediumPNT`) plus its
consequences (`chebyshev_asymptotic`, `pi_asymp`, `mu_pnt`, `lambda_pnt`,
`WeakPNT_AP`).

This umbrella imports the complete area inventory, so building or scanning it
omits no leaf module.  Provenance, licensing, and the map of intentional
overlaps with `RHTower` and mathlib: `PNTPlus/PROVENANCE.md`.
-/
import GaloisForLFunctions.PNTPlus.Mathlib.Algebra.Notation.Support
import GaloisForLFunctions.PNTPlus.Mathlib.Analysis.Asymptotics.Asymptotics
import GaloisForLFunctions.PNTPlus.Mathlib.Analysis.Asymptotics.Uniformly
import GaloisForLFunctions.PNTPlus.Mathlib.Analysis.SpecialFunctions.Log.Basic
import GaloisForLFunctions.PNTPlus.Mathlib.NumberTheory.Sieve.AuxResults
import GaloisForLFunctions.PNTPlus.Mathlib.NumberTheory.Sieve.Basic
import GaloisForLFunctions.PNTPlus.Mathlib.NumberTheory.Sieve.Selberg
import GaloisForLFunctions.PNTPlus.Mathlib.NumberTheory.Sieve.SelbergBounds
import GaloisForLFunctions.PNTPlus.Tactic.AdditiveCombination
import GaloisForLFunctions.PNTPlus.Auxiliary
import GaloisForLFunctions.PNTPlus.EulerMaclaurin
import GaloisForLFunctions.PNTPlus.Rectangle
import GaloisForLFunctions.PNTPlus.ResidueCalcOnRectangles
import GaloisForLFunctions.PNTPlus.Sobolev
import GaloisForLFunctions.PNTPlus.Fourier
import GaloisForLFunctions.PNTPlus.SmoothExistence
import GaloisForLFunctions.PNTPlus.Defs
import GaloisForLFunctions.PNTPlus.MellinCalculus
import GaloisForLFunctions.PNTPlus.PerronFormula
import GaloisForLFunctions.PNTPlus.BrunTitchmarsh
import GaloisForLFunctions.PNTPlus.Wiener
import GaloisForLFunctions.PNTPlus.ZetaConj
import GaloisForLFunctions.PNTPlus.ZetaBounds
import GaloisForLFunctions.PNTPlus.MediumPNT
import GaloisForLFunctions.PNTPlus.Consequences
