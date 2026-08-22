# Erlang wave packets give HT-faithful finite-resolution Wigner--Smith detectors

- **ID:** `erlang-wigner-smith-ht-faithful-coarse-graining`
- **Stage:** 2-fully-proven / not new scientific knowledge
- **Type:** THEOREM / PHYSICAL BRIDGE / FINITE-RESOLUTION DETECTOR
- **Scientific status:** `[PROVED HERE] [ABSTRACT RECOVERY PRINCIPLE IS EXISTING INFRASTRUCTURE]`
- **Scope:** scalar elastic scattering on an above-threshold energy half-line; no RH or special
  function input
- **Statement:** A smooth one-sided Erlang energy packet measures a positive finite-width average
  of the Wigner--Smith delay whose third-order differential image is the unsmoothed delay.  The
  finite-resolution response therefore has exactly the same DA/HT class as the underlying delay
  at every positive width.

## Setup

Let `Q(E)` be the scalar Wigner--Smith delay on an elastic energy half-line and assume the
integrals and differentiations below converge; polynomial growth is more than sufficient.  For
`epsilon>0` define the one-sided exponential averaging operator

```text
(A_epsilon f)(x)
  = integral_(s>=0) epsilon^(-1) exp(-s/epsilon) f(x+s) ds.            (1)
```

Integration by parts gives

```text
(1-epsilon D) A_epsilon f=f,              D=d/dx.                     (2)
```

The third iterate is the Erlang average

```text
R_epsilon(x)=A_epsilon^3 Q(x)
  = integral_(s>=0) rho_epsilon(s) Q(x+s) ds,

rho_epsilon(s)=s^2 exp(-s/epsilon)/(2 epsilon^3).                     (3)
```

The density is nonnegative, has integral one, and has positive width for every `epsilon>0`.

## Exact physical wave packet `[PROVED]`

Put

```text
psi_(epsilon,x)(E)
  = (E-x) exp(-(E-x)/(2 epsilon))
      /(sqrt(2) epsilon^(3/2))       for E>=x,
  = 0                                for E<x.                         (4)
```

Then `|psi_(epsilon,x)(E)|^2=rho_epsilon(E-x)`.  The amplitude vanishes at the lower edge, belongs
to the first Sobolev domain of `-i d/dE`, and is normalized.  The exact scalar
Eisenbud--Wigner--Smith identity therefore gives

```text
<S psi_(epsilon,x),-i d/dE(S psi_(epsilon,x))>
  - <psi_(epsilon,x),-i d/dE psi_(epsilon,x)>
  = R_epsilon(x).                                                    (5)
```

This is a physical positive-probability energy packet, not a signed postprocessing kernel.  Its
support stays above the controllable lower edge `x`, so no subthreshold tail is introduced.

## Finite differential recovery `[PROVED]`

Applying `(2)` three times gives the exact detector equation

```text
(1-epsilon D)^3 R_epsilon=Q.                                        (6)
```

Consequently:

1. if `R_epsilon` is DA over `C(x)`, then `(6)` makes `Q` DA;
2. if `Q` is DA, then `(6)` is a nonzero linear differential equation for `R_epsilon` over the DA
   extension `C(x)<Q>`, so differential-algebraic transitivity makes `R_epsilon` DA.

Thus, for every positive detector width,

```text
R_epsilon is HT over C(x)  <=>  Q is HT over C(x).                   (7)
```

This is stronger than approximate-identity law escape.  The detector does not merely approach an
HT signal as its resolution is refined: every member of the positive-width Erlang family is
already HT.

## All-resolution finite falsifiers `[PROVED FROM EXISTING INFRASTRUCTURE]`

Fix any finite differential-law window `Law(r,d,h)`.  Equation `(7)` makes its evaluation family
on `R_epsilon` linearly independent for every `epsilon>0`.  The already-formalized finite
evaluation-packet theorem therefore selects finitely many lower-edge energies at which the law
matrix is invertible.  Its least singular value supplies a positive deterministic noise margin.

As `epsilon->0`, `R_epsilon->Q` in every fixed `C^r` norm on compact energy intervals.  Hence one
finite energy packet selected for `Q` remains valid, with asymptotically the same margin, for all
sufficiently small positive widths.

## General sufficient principle

Let a coarse-grained response `R` to a source `Q` satisfy

```text
Q=L R                                                               (8)
```

for a nonzero finite differential operator `L` with DA coefficients.  Then

```text
Q HT  =>  R HT.                                                      (9)
```

If `(8)` is itself a differential equation for `R` over `C(x)<Q>`, the DA implication also runs in
the reverse direction.  Such a detector is **differentially recoverable**.  Erlang packets provide
an explicit positive wave-packet family with recovery operator `(1-epsilon D)^3`.

## Anti-theatre and novelty verdict

1. **Abstract source extraction called new.**  It is not.  Equation `(9)` is the contrapositive of
   the existing finite-differential-circuit closure theorem.
2. **Green-function calculus called new.**  It is not.  Equations `(2)`--`(3)` are standard
   resolvent/Erlang convolution identities.
3. **Finite resolution assumed harmless.**  False in general.  Only differentially recoverable
   kernels are covered.  An arbitrary smoothing may change DA/HT class.
4. **A discontinuous exponential packet used outside the time-operator domain.**  Avoided: the
   third-order Erlang amplitude `(4)` vanishes linearly at its lower edge and lies in `H^1`.
5. **Threshold leakage.**  Avoided by the one-sided above-edge support.
6. **A significance result claimed.**  The physical conjunction `(5)`--`(7)` is a strong bridge,
   but each mathematical ingredient is standard or already formalized.  It does not clear the
   novelty gate as new scientific knowledge.

The live new problem generated by this bridge is not to restate differential recovery.  It is to
classify physically positive HT-faithful detector kernels, determine their minimal recovery order,
and relate that order to noise amplification and quantum resource cost.

## Lean boundary

`SourceLogarithmicBoundary.lean`, `FiniteDifferentialCircuitBoundary.lean`, and
`FiniteEvaluationPacket.lean` already formalize the differential-algebraic and finite-detector
skeleton.  A useful Lean contribution must prove the exact analytic Erlang packet identity and
its `H^1`/integral interface as one theorem.  An algebra-only alias of `(9)` would be wrapper bloat.

## Primary parent literature

- S. Richard and R. Tiedra de Aldecoa, *Time Delay Is a Common Feature of Quantum Scattering
  Theory*, <https://arxiv.org/abs/1008.3433>.
- U. Smilansky, *Delay-Time Distribution in the Scattering of Time-Narrow Wave Packets. (I)*,
  <https://arxiv.org/abs/1701.00675>.
- E. Gustafson, Y. Zhu, P. Dreher, N. M. Linke, and Y. Meurice, *Real-Time Quantum Calculations
  of Phase Shifts Using Wave Packet Time Delays*, <https://arxiv.org/abs/2103.06848>.

## Gates

- [x] positive normalized Erlang packet constructed
- [x] packet lies in the first derivative domain
- [x] exact Wigner--Smith response identified
- [x] finite differential recovery equation proved
- [x] all-positive-width DA/HT equivalence proved
- [x] all-resolution finite falsifier consequence proved
- [x] abstract recovery and Green-function ingredients classified as parent theory
- [ ] positive HT-faithful detector-kernel classification
- [ ] minimal recovery order versus noise-amplification theorem
- [ ] unconditional analytic Lean interface
