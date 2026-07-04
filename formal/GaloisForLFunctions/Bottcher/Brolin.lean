/-
# Böttcher tower — Brolin / Riesz-measure interface

Public aggregator for the Brolin/Riesz-measure proof stack.  The implementation
is split into chapter modules under `Bottcher/Brolin/` so agents can work in the
right layer without reopening the whole 12k-line history.
-/
import GaloisForLFunctions.Bottcher.Brolin.Basic
import GaloisForLFunctions.Bottcher.Brolin.FiniteMeasures
import GaloisForLFunctions.Bottcher.Brolin.FiniteLimits
import GaloisForLFunctions.Bottcher.Brolin.TargetShifted
import GaloisForLFunctions.Bottcher.Brolin.GapAMuCore
import GaloisForLFunctions.Bottcher.Brolin.BoundaryTruncation
import GaloisForLFunctions.Bottcher.Brolin.BoundaryAtom
import GaloisForLFunctions.Bottcher.Brolin.SingularTail
import GaloisForLFunctions.Bottcher.Brolin.BoundaryCriteria
import GaloisForLFunctions.Bottcher.Brolin.TargetLimit
import GaloisForLFunctions.Bottcher.Brolin.Cauchy
import GaloisForLFunctions.Bottcher.Brolin.UnitCircle
import GaloisForLFunctions.Bottcher.Brolin.RieszFundamental
import GaloisForLFunctions.Bottcher.Brolin.RieszFlux
import GaloisForLFunctions.Bottcher.Brolin.RieszLogIBP
import GaloisForLFunctions.Bottcher.Brolin.RieszPerLevel
import GaloisForLFunctions.Bottcher.Brolin.RieszLimit
import GaloisForLFunctions.Bottcher.Brolin.RieszSupport
import GaloisForLFunctions.Bottcher.Brolin.WeylLemma
import GaloisForLFunctions.Bottcher.Brolin.WeylLemma
