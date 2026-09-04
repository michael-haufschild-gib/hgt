# Squarefree convolution-half Cesàro source criterion

- **ID:** squarefree-convolution-half-cesaro-source-criterion
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `multiplicity-parity-ladder-route.md`
- **Status:** `[FALSE] [ALL COFINAL SCHEDULES CLOSED] [LEAN-PROVED] [NOT RH]`

## Exact surviving edge

Construct an analytic square root of `poleClearedFirstTraceExponentialContinuation` on
`rightHalf`, equivalently discharge `RHLadder 1`. This is the first open edge of the report's
multiplicity ladder; Kramers, Clifford, and differential-Galois reformulations do not discharge it.

## Retired conjecture C-CE1

Let `D_N` be the canonical Dirichlet-polynomial truncation of `squarefreeConvolutionHalf` and let

\[
  C_N(s)=\frac{1}{N+1}\sum_{M=0}^{N}D_M(s).
\]

Synchronize `C_N` with pole-factor degree `N` and divide by the nonvanishing Carleman
half-determinant. The resulting family is locally bounded on `rightHalf`.

Status: `[FALSE] [LEAN-PROVED NO-GO]`. Pole-factor growth would force `N C_N(6/11)` bounded; exact
discrete differentiation recovers raw `D_N(6/11)`, contradicting its certified unboundedness.

## Retired conjecture C-CE2

There exists a cofinal pole-degree schedule `κ(N)` growing slowly enough that the scheduled
pole-cleared Cesàro family is locally bounded on `rightHalf`. Necessary escape regime exposed by
C-CE1 is that `N / 5^(κ(N)-24)` not be eventually bounded. The canonical
`iteratedLogarithmicCayleySchedule` is cofinal and Lean proves it lies in this escape regime.
The stronger power obstruction required every candidate schedule to avoid certified amplification
`5^(κ(N)-24) ≳ N^ρ` for every `ρ>6/11`.

Status: `[FALSE] [LEAN-PROVED NO-GO]`. A schedule-independent discrete Landau interpolation now
proves that `C_N(6/11) → 0` would force the raw partial sums to be `O(N^(1/3))`, contradicting the
polynomial Abel threshold `5/11`. Thus every cofinal schedule fails, including iterated-log.

## Why this class survived earlier locks

- It retains literal convolution-half coefficients.
- It is nonlocal in cutoff and is not a point-Hermite jet subtraction.
- Raw partial-sum unboundedness does not logically imply unboundedness of Cesàro averages.
- It agrees with the canonical Euler half-germ if Euler-chamber compact-open convergence survives
  averaging.

## Formalized bridge

Module:
`formal/GaloisForLFunctions/RHTower/SquarefreeConvolutionHalfCesaroCriterion.lean`.

Lean now proves unconditionally:

- `squarefreeHalfCesaroSum N` is entire;
- Cesàro averages converge locally uniformly to `LSeries squarefreeConvolutionHalf` on `farHalf`;
- pole-cleared Cesàro approximants are analytic on `rightHalf` and retain exact canonical source
  limit on `farHalf`;
- their local boundedness on `rightHalf` implies `RHLadder 1`.

Verification on 2026-09-04: direct check pass; targeted build `12847/12847`; principal theorem
axioms only `propext`, `Classical.choice`, `Quot.sound`; umbrella import wired.

Independent schedules are formalized in
`formal/GaloisForLFunctions/RHTower/SquarefreeConvolutionHalfCesaroScheduleCriterion.lean`.
For every cofinal `κ`, local boundedness of
`poleClearedFirstTraceCesaroScheduledApprox κ` implies `RHLadder 1` while retaining the canonical
Euler-chamber limit.

The exact rate obstruction is formalized in
`formal/GaloisForLFunctions/RHTower/SquarefreeConvolutionHalfCesaroFastScheduleNoGo.lean`.
If `5^(κ(N)-24)` eventually dominates `N` up to a constant, scheduled local boundedness is
impossible. Direct checks and targeted builds pass (`12848/12848` and `13032/13032`); main theorem
axioms only `propext`, `Classical.choice`, `Quot.sound`; umbrella imports wired.

The concrete surviving boundary is formalized in
`formal/GaloisForLFunctions/RHTower/SquarefreeConvolutionHalfCesaroIteratedLogFrontier.lean`.
Lean proves `iteratedLogarithmicCayleySchedule` is not fast and restates its local-boundedness
criterion as a direct implication to `RHLadder 1`. This does not prove local boundedness.
Verification on 2026-09-04: direct check pass; targeted build `13041/13041`; both theorem axiom
audits only `propext`, `Classical.choice`, `Quot.sound`; umbrella import wired.

The schedule-independent arithmetic core is exposed in
`formal/GaloisForLFunctions/RHTower/SquarefreeConvolutionHalfCesaroWeightedIdentity.lean` and
`formal/GaloisForLFunctions/RHTower/SquarefreeConvolutionHalfCesaroVanishingNecessity.lean`:

\[
 C_N(s)=N^{-1}\sum_{n<N}(N-n-1)\,a_n n^{-s},
\]

and local boundedness along any cofinal schedule forces `C_N(6/11) → 0`. Therefore schedule choice
cannot evade the common zero-limit gate. Direct checks pass; targeted builds `12848/12848` and
`13043/13043`; principal axiom audits only `propext`, `Classical.choice`, `Quot.sound`; umbrella
imports wired.

Polynomial Abel continuation in
`formal/GaloisForLFunctions/RHTower/SquarefreeConvolutionHalfCesaroPowerScheduleNoGo.lean` proves
that raw partial sums at real `sigma>1/2` cannot be `O(N^alpha)` for
`alpha<1-sigma`. Combining this with the Cesàro discrete derivative closes every schedule whose
certified amplification dominates `N^rho` for some `6/11<rho≤1`. Verification on 2026-09-04:
direct check pass; targeted build `13049/13049`; principal axiom audits only `propext`,
`Classical.choice`, `Quot.sound`; umbrella import wired.

The terminal schedule-independent obstruction is formalized in
`formal/GaloisForLFunctions/RHTower/SquarefreeConvolutionHalfCesaroAllCofinalNoGo.lean`.
Lean proves
`not_tendsto_squarefreeHalfCesaroSum_boundaryExteriorPoint_zero`: a backward block of length
`k^3`, `k=floor(sqrt(floor(sqrt N)))`, turns hypothetical Cesàro vanishing into the forbidden raw
bound `O(N^(1/3))`. Consequently
`no_poleClearedFirstTraceCesaroScheduledLocallyBounded_of_cofinal` closes every cofinal schedule.
Verification on 2026-09-04: direct check pass; targeted build `13053/13053`; principal axiom audits
only `propext`, `Classical.choice`, `Quot.sound`; umbrella import wired.

## Positive survivor / next attack

1. Cesàro/Riesz order one is terminal. Do not spend further effort engineering cutoff schedules.
2. Any successor smoothing must avoid a first primitive bounded by `O(N)`, or include a singular
   nonlinear/arithmetic correction whose discrete derivative is not the raw half partial sum.
3. Selberg--Delange asymptotics could sharpen the nonvanishing statement but are unnecessary for
   this closure and remain absent from the corpus.

## Falsifier

Achieved: `C_N(6/11)` cannot tend to zero, while every cofinal scheduled local bound would force
that zero limit.

## Log

- 2026-09-04 — corpus search found no canonical convolution-half Abel/Riesz/Cesàro implementation;
  card opened before formal construction
- 2026-09-04 — entire holomorphy, Euler compact-open convergence, pole-cleared convergence, and
  exact Vitali-to-rung bridge formalized and axiom-audited
- 2026-09-04 — diagonal synchronization refuted in Lean via exact Cesàro discrete derivative and
  boundary pole-factor growth; C-CE2 opened for slow independent schedules
- 2026-09-04 — independent-schedule Vitali criterion and general fast-schedule no-go formalized;
  every live schedule must be cofinal yet sublogarithmic in the certified base-five scale
- 2026-09-04 — canonical iterated-log schedule proved outside the fast no-go; its local boundedness
  is the concrete surviving C-CE2 obligation
- 2026-09-04 — exact triangular weight and cofinal vanishing necessity formalized; all schedules
  now share one zero-limit arithmetic gate at `6/11`
- 2026-09-04 — polynomial Abel continuation closes every certified amplification exponent
  `rho>6/11`; iterated-log remains subcritical and open
- 2026-09-04 — discrete fourth-root-block Landau interpolation refutes the common zero-limit gate;
  every cofinal Cesàro schedule is now closed, including iterated-log
