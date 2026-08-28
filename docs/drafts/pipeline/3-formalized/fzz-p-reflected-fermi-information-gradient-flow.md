# FZZ-P reflected Fermi information gradient flow

- **ID:** FZZ-P-HC37
- **Stage:** 3-formalized
- **Type:** THEOREM / nonlinear source dynamics and exact stationary endpoint
- **Source:** `FermiMellinPhaseProperness` + `FZZCigarParityDelaySourceContinuation`
- **Frontier map:** read-only; no edit permitted

## Frozen conjecture

For `0<sigma<1`, let `m(sigma)` and `V(sigma)>0` be literal Fermi--Mellin log mean and variance.
Define reflected information work

`W(sigma)=(2 sigma-1)(m(sigma)-m(1-sigma))`

and nonlinear force

`F(sigma)=2(m(sigma)-m(1-sigma))`

`          +(2 sigma-1)(V(sigma)+V(1-sigma))`.

Conjecture:

1. `W'=F` on open strip;
2. `F<0` left of `1/2`, `F=0` exactly at `1/2`, and `F>0` right of `1/2`;
3. negative-gradient velocity `-F` is strictly inward off center;
4. FZZ parity-Mellin mode is stationary for this literal source force exactly when its real part is
   `1/2`;
5. all open-strip FZZ parity-Mellin modes are stationary iff RH.

Unlike local Riesz stability, this is a genuinely nonlinear, nonlocal source law: mean and variance
are full half-line Fermi observables, and force is gradient of symmetric reflected KL work. It would
construct missing center-oriented dynamics unconditionally. Remaining RH burden after proof would
be physical stationarity/landing of every divisor mode, not orientation mechanics.

## Paper proof

Existing corpus proves `m'=V`, `V>0`, and strict monotonicity of `m`. Product and chain rules give
displayed derivative. If `sigma>1/2`, then `sigma>1-sigma`, hence both terms in `F` are positive.
If `sigma<1/2`, both are negative. At center both vanish. Multiplying velocity `-F` by centered
coordinate gives strict negative radial drift off center. Mode-stationary classification follows
from unique force zero; global equivalence follows from source-first FZZ Mellin completeness
endpoint already proved equivalent to RH.

## Corpus audit

Mandatory searches on 2026-08-28:

- `scripts/formal_tools.py research "salem Fermi Mellin log coordinate Fourier transform reflection Wronskian zero real part"`
- `scripts/formal_tools.py research "Fermi kernel Mellin functional equation coercive identity critical line"`
- `scripts/formal_tools.py research "eta Mellin zero positivity log delay reflection paired integral"`
- `scripts/formal_tools.py research "Fermi Mellin phase derivative Wronskian horizontal zero uniqueness Turan"`

Corpus has phase orthogonality, Fisher lower bound, reflected Jeffreys work, and strict log-mean
monotonicity, but no derivative force, global inward-flow theorem, or FZZ mode-stationarity endpoint.

## Literature boundary

Search located Salem/Fermi RH criterion and generic information-geometric gradient literature, but
no literal Fermi--Mellin reflected force or FZZ critical-center flow. Generic exponential-family
calculus is standard; novelty claim is limited to source-specific force synthesis and route burden
separation.

Primary sources checked on 2026-08-28:

- González--Negrín, *A new equivalence to RH by Salem integral equation*, arXiv:2604.15396;
- Raskutti--Mukherjee, *Information Geometry of Mirror Descent*, arXiv:1310.7780;
- Nagaoka, *Exponential family of Markov chains and its information geometry*, arXiv:1701.06119.

This is a bounded corpus-and-source audit, not a claim that all literature has been exhausted.

## Formal theorem

Module:
`GaloisForLFunctions.RHTower.FZZCigarParityReflectedFermiInformationGradientFlow`

The formalization proves unconditionally:

1. reflected work is exactly the Jeffreys divergence between the two literal Fermi--Mellin laws;
2. its derivative is the displayed nonlinear force;
3. force has strict sign away from center and a unique zero at `1/2`;
4. negative-gradient velocity points strictly inward and dissipates work by a strict negative
   square away from center;
5. a source-first FZZ Mellin mode is stationary exactly when it lies on the critical line;
6. universal open-strip stationarity is equivalent to FZZ Mellin completeness and hence RH.

## New route knowledge and remaining burden

HC37 removes orientation mechanics as the nonlinear FZZ-P gap: literal half-line source data itself
supplies a global strict Lyapunov orientation with no finite-dimensional reporter choice. It also
turns critical-line membership into a source-native equilibrium condition.

It does **not** prove that divisor modes obey this gradient dynamics or must be stationary. The
remaining RH-strength burden is a source/physical Ward law forcing every divisor mode to be an
equilibrium (or a comparably strong landing theorem). Defining stationarity is not evidence for that
Ward law; it is now the isolated open core.

## Verification

- direct check: `lake env lean GaloisForLFunctions/RHTower/FZZCigarParityReflectedFermiInformationGradientFlow.lean`;
- targeted build: `lake build GaloisForLFunctions.RHTower.FZZCigarParityReflectedFermiInformationGradientFlow`
  passed (`8797` jobs);
- `#print axioms` on all 12 public endpoints reported only `propext`, `Classical.choice`, and
  `Quot.sound`;
- formal lint reported no finding for HC37; repository-wide lint still reports unrelated pre-existing
  unreachable modules;
- module is wired into `GaloisForLFunctions.RHTower`; full umbrella build intentionally not run;
- frontier map remained read-only and untouched.

## Status

- [x] corpus-led conjecture frozen
- [x] dependency-closed paper proof
- [x] Lean formalization
- [x] direct check, targeted build, axiom/lint audit, umbrella wiring
- [x] move to `3-formalized`
