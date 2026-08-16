# Source/Gamma naturality shared-ghost producer (2026-08-16)

Formalized module:
- formal/GaloisForLFunctions/RHTower/SourceGammaNaturalitySharedGhostProducer.lean
- wired into formal/GaloisForLFunctions/RHTower.lean; umbrella NOT built.

Core source theorem:
- Prime/arch orientation difference is literal Calderón–Witt boundary:
  deningerCalderonWittGlobalOrientedBoundary_primeArchWitness.
- PrimeGammaTwoThreeSourceNaturalReporter t is non-circular: arbitrary linear reporter, prescribed inverse-Gamma coefficients at prime 2 and 3, positive real arch readout, vanishing only on selected 2–∞ and 3–∞ boundaries. It contains no proposed shared scalar.
- primeGammaTwoThreeSharedGhost_of_naturalReporter derives c := Re(F(e∞)) and forces c=2^-t=3^-t, hence shared inverse Ward ghost.
- Nonempty natural reporter iff canonical source-natural inverse ghost iff shared ghost iff t=0.
- Xi pointwise formulation quantified over divisor support iff RH, but corpus does NOT yet prove reporter existence at every Xi divisor.

Exact remaining open producer:
For every Xi divisor rho, construct a coefficient-faithful reporter F on the actual Calderón–Witt top source with F(e2)=2^-t, F(e3)=3^-t, positive real F(e∞), and F(d w2)=F(d w3)=0, t=2 Re(rho)-1. This is RH-strength.

Failed conjectures recorded in card: affine Kummer–Gamma jet, Big-Witt base naturality, adelic product formula, CCM cyclic-homology equality, Fisher quotient identification.
Survivor card:
docs/drafts/pipeline/3-formalized/not_new_scientific_knowledge/source-gamma-naturality-shared-ghost-producer.md

Verification:
- lake env lean source module: PASS
- exact leaf lake build GaloisForLFunctions.RHTower.SourceGammaNaturalitySharedGhostProducer: PASS
- scripts/formal_tools.py lint: PASS
- axioms only propext, Classical.choice, Quot.sound
- no umbrella build.
