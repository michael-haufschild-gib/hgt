# Clock-coframe conservation budget law

- **ID:** `clock-coframe-conservation-budget-law`
- **Stage:** 3-formalized
- **Paper proof:**
  `../2-fully-proven/new_scientific_knowledge/clock-coframe-conservation-budget-law.md`
- **Lean:** `formal/GaloisForLFunctions/HTGeometry/ChronometricCausalSusceptibility.lean`

## Formalized statement

Over an arbitrary ring, let the clock-gradient synthesis map be a linear equivalence

\[
  \Theta:C\overset{\sim}{\longrightarrow}V.
\]

Lean defines the adaptive source

\[
  a_b=\Theta^{-1}(-b)
\]

and proves

\[
  b+\Theta(a_b)=0.
\]

For an arbitrary additional type \(S\), it defines

\[
  \mathcal A(b,s)=(a_b,s)
\]

and proves exact conservation, exact recovery of \(s\), and joint injectivity in \((b,s)\).

## Lean declarations

- `conservationBalancedClockSource`
- `clockCoframe_conservation`
- `conservationBalancedClockSourceWithSignal`
- `clockCoframe_conservation_withSignal`
- `clockCoframe_signal_reconstruction`
- `conservationBalancedClockSourceWithSignal_injective`

## Boundary

The theorem formalizes the algebraic conservation budget. It does not prove scalar clock gradients
form a physical coframe, construct Einstein--scalar solutions, establish nonlinear linearization
stability, or implement conserved sources in apparatus. Those analytic/physical results remain
external and are explicitly prior work in the Kurylev--Lassas--Uhlmann active-measurement program.
