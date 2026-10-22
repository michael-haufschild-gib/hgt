# PW-B source-square admission of every complex connection shift

- **ID:** PW-B-SHIFTED-SOURCE-2026-09-10
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** PW-B frontier; original-source-square horizontal energy
- **Statement:** The shifted singular PW connection has a nonzero finite-source-energy mode for every complex shift, with exact reflection pairing and energy density.

## Goal and failed conjecture

The RH chain needs source-forced partner balance before Xi specialization. After
the unshifted horizontal mode survived the literal Gamma-source-square norm, test
whether spectral displacement restores selection. It does not: every complex
shift is admitted by this norm. This is a statement about this explicit connection
and candidate domain, not a realization of Xi zeros or identification of the
physical source domain.

## Dependency-closed paper proof [PROVED HERE]

Use the existing exact functions
`phi(t)=sinh(t)-t/2`, `p(t)=cosh(t)-1/2`,
`q(t)=exp(t/2-exp(t))`, `w=q^2`, `a=exp(2*phi)`.
For any `z` in `C`, put `f_z(t)=exp(phi(t)+z*t)`. Differentiation gives
`f_z'=(p+z)*f_z`; the exponential is nowhere zero. Conversely, multiplying any
solution by `exp(-phi-z*t)` gives derivative zero, hence every solution is
`c*f_z`. No spectral restriction occurs in this classification.

The exact weighted norm density is
`w*|c*f_z|^2=|c|^2*exp(-2*cosh(t)+2*Re(z)*t)`.
For every real `b`, this last exponential with `b*t` is integrable. Set
`A=|b|+1>0`. On the nonnegative half-line its exponent is at most
`A*t-exp(t)`; on the negative half-line it is at most
`A*(-t)-exp(-t)`. Thus the sum of the two reflected, integrable Gamma log
profiles `expShift A 0` dominates it everywhere. Its integral is strictly
positive. This proves admission of the function and of its connection image
`z*f_z`, with no numerical computation.

The complex-linear weighted reflection `Tf(t)=a(t)*f(-t)` satisfies
`T f_z=f_(-z)`. Substitution `t -> -t` makes their total energies equal.
Reflection pairing and finite positive source energy therefore admit every
complex displacement. They do not imply individual PW balance.

## No-go closure

- **Exact killing mechanism:** explicit admitted mode at each complex shift.
- **Strongest positive survivor:** complete one-dimensional solution spaces,
  exact weighted densities and reflection pairing, all-shift finite energy.
- **New insight:** the finite-energy exception is not confined to the neutral
  mode. A proposed adjoint/Fredholm argument must derive a different, justified
  source domain or additional arithmetic equation; it cannot infer a selective
  spectrum from this candidate norm.
- **Status:** paper proof and Lean audit closed. No
  claim about closedness, Hilbert adjoints, resolvents, or Fredholm index.

## Literature and method audit

Broad September/June/August arXiv searches for Fredholm, supersymmetry and duality
found [Kapranov, August 2026](https://arxiv.org/html/2608.12846v1).
Theorem 2.3.7 characterizes theta by two infinite-order fixed-point equations.
These are modular-variable equations, not Mellin spectral balance. Theorem 2.3.7
and Proposition 2.3.10 do not assert that the odd generators annihilate theta;
fixedness under a discrete exponential cannot be differentiated into stationarity.
An exact PW/Mellin transmutation remains unproved, so no RH implication is imported.

The corpus adjoint search found the Hedenmalm weighted derivative and shifted
cokernel, whose source weight and closed domain differ from this connection.
Their adjoint kernel theorems cannot be reused without a proved identification.
The current proof uses the existing Gamma log-profile integrability and
integrating-factor method instead.

## Lean verification, 2026-09-11

Module: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingParikhWilczekSingularSourceSquareShiftedModes`.
Capstone: `RHTower.pwLogGammaSource_every_complex_shift_admitted`.
Classification: `RHTower.pwLogShiftedSourceMode_classification`.

- Foreground scratch `lake env lean /tmp/pwb-shifted-modes.lean`: passed.
- Foreground `lake env lean` on the final leaf: passed without warnings.
- Final targeted `lake build` on this exact module: passed. No umbrella build.
- Umbrella import wired in `formal/GaloisForLFunctions/RHTower.lean`.
- All 11 public theorem axiom lists checked through
  `/tmp/pwb-shifted-axioms.lean`: only `propext`, `Classical.choice`, `Quot.sound`.
  No additional axiom or computation oracle occurs.
- `scripts/formal_tools.py lint`: passed; existing large-file warnings remain.

Four deep corpus searches, including stored method results, are preserved in
`../1-in-progress/pw-b-shifted-source-searches.json`. Source and semantic coverage
are partial; these search results are not an exhaustive absence claim.

RH remains unproved. The missing source-to-PW arithmetic transmutation and its
vanishing/orientation law are not supplied by the shifted-mode classification.
