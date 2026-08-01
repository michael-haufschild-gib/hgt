# Dissipative quantum return information transition

- **ID:** `dissipative-quantum-return-information-transition`
- **Stage:** 3-formalized
- **Type:** UNIVERSAL THEOREM CANDIDATE / OPEN-QUANTUM RECURRENCE /
  RATE--DISTORTION PHASE TRANSITION
- **Scientific status:** `[NEW CORE CANDIDATE] [NOVELTY AUDIT OPEN]`
- **Source:** quantitative extension of the projective recurrence--water law to finite
  Hilbert-contractive dynamics
- **Headline:** Noise fixes how much quantum information can ever return; reverse-water
  information fixes how long the surviving part must wait.

## False broad claim and exact replacement

The statement “every finite open quantum system returns arbitrarily close to its initial state”
is false. Amplitude damping already destroys it. The maximal honest replacement has two parts.

1. Every finite Hilbert-space contraction has a canonical lossless peripheral sector and a
   transient sector. The transient sector decays; the peripheral sector is unitary.
2. For an initial vector, the squared norm of its peripheral projection is the exact long-time
   ceiling of normalized return amplitude. Below that ceiling, the least worst-spectrum return
   deadline is governed by the existing reverse-water functional of the normalized peripheral
   spectral weights. Above it, sufficiently late return is impossible.

Closed unitary dynamics is exactly the ceiling-one boundary, not a separate law.

## Abstract contraction statement

Let `T` be a contraction on a finite-dimensional complex Hilbert space. Its canonical reducing
decomposition is

```text
H = H_perp ⊕ H_tr,
T = U ⊕ S,
```

where `U` is unitary and `S^n -> 0` in operator norm. For a unit vector
`x = x_perp + x_tr`, put

```text
p = ||x_perp||^2.
```

Diagonalize `U` and write

```text
<x_perp,U^n x_perp> = p sum_j w_j exp(i n omega_j),
w_j >= 0,  sum_j w_j = 1                              (1)
```

when `p>0`. Orthogonality gives

```text
<x,T^n x>
 = p sum_j w_j exp(i n omega_j) + <x_tr,S^n x_tr>.      (2)
```

The transient term tends to zero. Simultaneous phase recurrence makes the first term approach
`p` along arbitrarily late clocks. Therefore

```text
limsup_(n->infinity) |<x,T^n x>| = p,                   (3)
limsup_(n->infinity) |<x,T^n x>|^2 = p^2.               (4)
```

Consequences:

```text
a > p  => all sufficiently late clocks have amplitude < a;
0 <= a < p => arbitrarily late clocks have amplitude > a. (5)
```

Thus `p` is an exact return-information ceiling, not an upper estimate.

## Quantitative floor-plus-clock law

Assume a certified burn-in `B` satisfies

```text
|<x_tr,S^n x_tr>| <= (p-a)/2  for every n >= B,          (6)
```

where `0<a<p`. Put

```text
eta = (p-a)/(2p).                                         (7)
```

Let `T_w(eta)` be the least universal projective phase deadline for the persistent probability
vector in `(1)`. The delayed recurrence theorem applied with multiplier `B+1` gives a clock

```text
B < n <= (B+1) T_w(eta)                                  (8)
```

at which

```text
|<x,T^n x>| >= a.                                         (9)
```

The already proved three-way water law then yields

```text
log n <= log(B+1) + H_water(w,eta) + explicit O(r),        (10)
```

and the matching hard peripheral spectra give the same water exponent from below. Dissipation
therefore contributes a burn-in and a ceiling; recurrence complexity is paid only by surviving
spectral information.

If `||S^n|| <= C rho^n` with `0<=rho<1`, condition `(6)` is certified by

```text
C rho^B ||x_tr||^2 <= (p-a)/2.                            (11)
```

No numerical feasibility claim follows without measured or analytically established `C,rho`.

## Direct open-quantum scope

Every finite bistochastic quantum channel is a Hilbert--Schmidt contraction: Kadison--Schwarz and
trace preservation give

```text
||Phi(X)||_HS^2
 <= Tr Phi(X†X)
 =  Tr(X†X).                                               (12)
```

Hence `(1)`--`(11)` apply to the Hilbert--Schmidt autocorrelation of every observable or state
operator under every finite bistochastic channel. This includes unitary channels, dephasing,
depolarizing and Pauli/Weyl-covariant noise, and many stroboscopic open-system semigroups.

For a general nonunital CPTP channel, Hilbert--Schmidt contractivity need not hold. The qualitative
attractor/transient decomposition remains available in finite dimension, but the orthogonal
ceiling formula requires either a faithful invariant-state geometry, detailed balance, or a
different norm. No all-CPTP Hilbert--Schmidt claim is permitted.

## Paper proof

### Peripheral reduction

For a contraction, a unit-modulus eigenvector is also an adjoint eigenvector with conjugate
eigenvalue. Distinct peripheral eigenspaces are therefore orthogonal. Their sum is reducing and
the restriction of `T` is unitary. A nontrivial Jordan step at a unit-modulus eigenvalue would make
`||T^n||` grow, contradicting `||T^n||<=1`; hence all peripheral eigenvalues are semisimple.
The orthogonal complement is invariant under `T` and `T†`, contains no unit-modulus spectral value,
and is finite-dimensional. Its spectral radius is therefore strictly below one, so `S^n->0`.

### Exact ceiling

Equation `(2)` follows from the reducing orthogonal sum. The transient term tends to zero, while
the persistent term has modulus at most `p`. This proves the upper half of `(3)`. For every
accuracy and delay, simultaneous Diophantine recurrence finds a later `n` at which every
`exp(i n omega_j)` is close to one. The persistent term then approaches `p`, proving the reverse
inequality and `(3)`--`(5)`.

### Quantitative deadline

At the delayed persistent return supplied by `T_w(eta)`,

```text
|sum_j w_j exp(i n omega_j)| >= 1-eta.
```

The reverse triangle inequality and `(6)` give

```text
|<x,T^n x>|
 >= p(1-eta) - (p-a)/2
 = a.
```

This proves `(8)`--`(10)`. A hard spectrum in the peripheral sector and a transient block that
vanishes after one step transfers the existing minimax lower law, so the water exponent cannot be
improved uniformly from the stated data.

## Prior-art boundary

Known parent results:

- finite quantum-channel asymptotics identify the attractor subspace with the peripheral
  eigenspaces and describe the transient decay;
- decoherence-free algebra theory characterizes the lossless asymptotic algebra;
- open-system recurrence has been studied for real-spectrum non-Hermitian Hamiltonians;
- quantum Kac lemmas study monitored expected return times for iterated channels;
- closed-system recurrence bounds study unitary dynamics.

Current searches found no source joining:

```text
exact persistent autocorrelation ceiling
  + sharp return/no-return threshold
  + burn-in/peripheral separation
  + reverse-water minimax recurrence information.          (13)
```

Search absence is not a novelty proof. Before promotion, inspect the full papers and citation
graphs around Amato--Facchi--Konderak, Liu--Zheng, quantum-channel Kac lemmas, and quantitative
closed recurrence.

## Formal targets

1. Finite damped spectral packet:
   - transient autocorrelation bound;
   - polynomial--exponential Jordan transients;
   - exact arbitrarily-late ceiling;
   - late impossibility above ceiling;
   - quantitative return below ceiling;
   - hard-spectrum minimax transfer.
2. Finite Hilbert contraction:
   - canonical peripheral reducing subspace;
   - unitary restriction;
   - stable complement and power convergence;
   - autocorrelation specialization to target 1.
3. Bistochastic matrix channel:
   - exact Hilbert--Schmidt contraction from Schwarz plus trace preservation;
   - application of the abstract contraction theorem.

## Gates

- [x] false all-open recurrence claim killed
- [x] dependency-closed packet-level paper proof
- [x] exact open-system scope and nonunital boundary stated
- [x] preliminary exact-phrase novelty search found no collision
- [ ] full primary-source citation-graph collision audit
- [x] finite damped and Jordan-complete polynomial packets formalized
- [x] arbitrary finite-contraction decomposition formalized
- [x] bistochastic-channel bridge formalized
- [ ] hostile review confirms result is stronger than a known attractor reformulation
- [ ] manuscript integration only after all displayed claims are unconditional

## Lean formalization

- Abstract finite-contraction decomposition, transient power decay, exact amplitude/fidelity
  ceilings, threshold dichotomy, burn-in deadline, and reverse-water deadline:
  `formal/GaloisForLFunctions/RHTower/DissipativeQuantumReturnInformationTransition.lean`.
- Exact finite bistochastic matrix-channel bridge:
  `formal/GaloisForLFunctions/RHTower/FiniteBistochasticMatrixChannel.lean`.
- Complete positivity is defined through every finite block amplification. The Lean proof derives
  positivity, adjoint preservation, the two-by-two Kadison--Schwarz inequality, trace/Frobenius
  identity, Hilbert--Schmidt contractivity, bounded operator realization, and all channel-specific
  ceiling/dichotomy/deadline capstones without additional hypotheses.
- Umbrella import: `formal/GaloisForLFunctions/RHTower.lean`.
- Verification: direct `lake env lean`, final module build, formal lint, and axiom audit pass. Audited
  capstones depend only on `propext`, `Classical.choice`, and `Quot.sound`.
