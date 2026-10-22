# Suzuki Cauchy-wall Gamma secant assembly

## Status

Formalized in Lean 4.  Route map remains read-only.  This constructs missing source-faithful
prime--polar--Gamma wall carrier and identifies its lower-Hardy value.  Remaining open core is
quantitative Ward/Gram domination on this carrier.

## Corpus-first frontier audit

Exact `scripts/formal_tools.py research` searches were run before conjecturing for unit-Riesz
Suzuki reporters, complex wall phases, Gamma-density wall counterterms, Hardy evaluation, and
completed-source two-depth secants.  Corpus already knew:

- `unitRieszSuzukiReporter H h = exp((h-H)/2) - exp(h-H)`;
- literal `ccmPublishedArchimedeanDensity` and Suzuki arch/polar corrections;
- outgoing charge = Green + polar correction - archimedean correction;
- completed prime-minus-polar Cauchy wall and its `-I` evaluation.

No theorem represented Suzuki reporter as a complex wall secant, transported the literal Gamma
density into that carrier, or assembled all three channels into a zero-height-recentered wall with
Green lower-Hardy value.

## Theorem

Define the two-depth wall secant

\[
 S_{H,h}(z)=\chi_{h-H}(z)-\chi_{h-H}(2z),\qquad
 \chi_x(z)=e^{ixz/2}.
\]

Then

\[
 S_{H,h}(-i)=e^{(h-H)/2}-e^{h-H}
 =\operatorname{unitRieszSuzukiReporter}(H,h).
\]

Consequently the literal Gamma and polar corrections have canonical wall realizations

\[
 A_H(z)=\int_{1/2}^{H}S_{H,h}(z)\,a_\Gamma(h)\,dh,
\]

\[
 P_H(z)=\int_{1/2}^{H}S_{H,h}(z)\,2\cosh(h/2)\,dh
 -e^{H/2}{iz/2\over1+iz/2},
\]

with `A_H(-i)` and `P_H(-i)` equal to the existing literal Suzuki archimedean and polar
corrections.  If `Phi_N` is completed prime-minus-polar wall, the full Ward wall

\[
 W_N(z)=\Phi_N(z)-P_{\log N}(z)+A_{\log N}(z)
\]

satisfies

\[
 W_N(0)=0,
 \qquad
 W_{n+2}(-i)=\operatorname{unitRieszSuzukiGreen}(\log(n+2)).
\]

## New scientific content

Gamma correction is no longer external scalar appended after wall evaluation.  It is an actual
continuous superposition of the same normalized Suzuki wall phases as prime channel, but in a
forced two-depth secant.  Reporter coefficients are therefore spectral geometry, not ad hoc test
weights.  This supplies a concrete carrier on which remaining reflected-wall Ward inequality can
be stated without dropping or scalarizing Gamma channel first.

## Hostile audit

- No bound, sign, Loewner domination, or RH conclusion is claimed.
- Assembly identity follows from literal source terms; it does not make Green value small.
- Two-depth secant is forced by exact reporter exponents `1/2` and `1`, not chosen to fit endpoint
  after fact.
- No zero data, numerical computation, RH premise, or added axiom is used.

## Lean certificate

- **Module:** `GaloisForLFunctions.RHTower.Suzuki.SuzukiCauchyWallGammaSecantAssembly`
- **Reporter secant:** `suzukiUnitRieszReporterWallSecant_neg_I`
- **Literal Gamma evaluation:** `suzukiUnitRieszArchWallSecant_neg_I`
- **Literal polar evaluation:** `suzukiUnitRieszPolarWallSecant_neg_I`
- **Zero-height completion:** `suzukiUnitRieszGammaCompletedWardWall_zero`
- **Green assembly:** `suzukiUnitRieszGammaCompletedWardWall_add_two_neg_I_eq_green`

## Log

- 2026-08-16 — corpus-first collision audit completed.
- 2026-08-16 — paper theorem and unconditional Lean formalization completed; umbrella wired.
