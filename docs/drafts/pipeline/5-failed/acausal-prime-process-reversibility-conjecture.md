# Retired acausal prime-process reversibility conjecture

- **ID:** `acausal-prime-process-reversibility-conjecture`
- **Stage:** 5-failed
- **Type:** `[RETIRED: REFLECTED PHYSICALITY IS THE TARGET]`
- **Scientific status:** `[FAILED RH ROUTE]`; finite localization survives only as a bridge
- **Source:** user scalar-field / pre-Big-Bang ideation, 2026-07-11
- **Statement:** A completed all-prime higher-order quantum process, defined without a global causal
  order, is conjectured to become deterministically reversible exactly at completed-zeta defects.
  Functional-equation reflection supplies the reverse process. Physical reversibility then forces
  every prime transfer mode `p^(1/2-s)` to have unit modulus, localizing every defect to
  `Re(s)=1/2`.

## Terminal no-go

`[PROVED; ROUTE RETIRED]` The process category adds no zeta-specific constraint. Let `P` be finite
and nonempty, put

```text
D_(P,s)=diag(1,(p^(1/2-s))_(p in P)),
Phi_(P,s)(X)=D_(P,s) X D_(P,s)^*,
Psi_(P,s)(X)=D_(P,s)^(-1) X D_(P,s)^(-*) .
```

Both maps are completely positive and are algebraic inverses for every `s`. The map `Phi_(P,s)` is
trace preserving exactly when

```text
D_(P,s)^* D_(P,s)=1
```

and this holds exactly when `|p^(1/2-s)|=1` for every `p`, equivalently `Re(s)=1/2`. The inverse map
is trace preserving under the same condition. Thus even the smallest exact acausal/reversible model
has physicality locus equal to the critical line before `xi` or its zeros enter.

More generally, every eigenvalue of a finite-dimensional quantum channel has modulus at most one.
If a channel at `s` has mode `p^(1/2-s)` and a reflected channel at `tau(s)=1-conj(s)` has the
reciprocal mode

```text
p^(1/2-tau(s))=1/conj(p^(1/2-s)),
```

then simultaneous physicality already forces both moduli to equal one. The inverse relation is not
needed.

Consequently the conditional premise

```text
xi(rho)=0 -> the process at rho and its reflection are physical
```

is RH itself in process language. Indefinite causal order, causal witnesses, and channel
reversibility do not produce the missing source-to-critical-line implication. This route is a recut
of the prime-unitarity/superselection wall and is retired.

## Goal

Interpret "before the Big Bang" literally as absence of a background causal order, not as an
earlier value of time. Singularity, inflation, and reheating are local laboratories inside one
higher-order process. Their ordering is not chosen, evolved, or summed by a Hamiltonian.

The proposed arithmetic laboratories are:

```text
S: impose the global no-background constraint;
A: apply the archimedean completion/reflection operation;
P_p: expose the local event at prime p.
```

A process matrix `W_s` assigns joint probabilities to interventions in these laboratories without
assuming a global order among them. The completed scalar is not a partition function of an
evolution. It is conjectured to be the obstruction to `W_s` having a deterministic physical inverse.

## What is deliberately not used

- no Hamiltonian with zeta zeros as spectrum;
- no heat, RG, cosmological, or vertical evolution parameter;
- no local Higgs or Landau--Ginzburg vacuum germ;
- no ordinary reflection positivity or cohomology support locus;
- no causal-set reconstruction from a zero list;
- no postulated determinant whose entries are chosen from the zero divisor.

The only composition used is the algebraic constraint "process followed by reflected process equals
identity" at a defect. If a later realization needs a semigroup or iteration to generate `W_s`, the
route has smuggled a flow back in and fails.

## Candidate moves and attacks

### Biased quantum-switch amplitude

`[REFUTED]` Put the three laboratories in a coherent superposition of causal orders and weight the
two orientations by `1` and `p^(1/2-s)`.

A quantum switch remains a valid normalized process with unequal branch amplitudes. Causal
nonseparability alone therefore does not force unit modulus or the critical line. Imposing equal
branch probabilities would insert the desired modulus condition by hand.

### Prime-word pregeometry and reheating abelianization

`[REFUTED AS THE LOAD-BEARING MECHANISM]` Before reheating, replace integers by ordered words in
prime events; reheating abelianizes a word to its occupation vector and hence to an integer.

For scalar Euler weights, every permutation of a fixed prime multiset has exactly the same
amplitude. The canonical state already lies in the symmetric word subspace, so the order-erasing
environment records no information and supplies no defect. A noncommuting prime lift would have to
be invented, and no source-canonical lift is presently known. The surrounding free-monoid,
Beurling, bosonic-Fock, and mixed-prime-word structures also already exist in the project.

### Causal-witness vanishing

`[REFUTED]` Declare zeta zeros to be zeros of a causal-nonseparability witness.

Causal witnesses are not faithful coordinates on the process cone: one witness vanishes on large
families of distinct processes. Choosing a witness with determinant `xi` would be target-built and
circular.

### Reflected physical inverse

`[CONJECTURE; SELECTED]` For each finite prime set `P`, construct a process `W_(P,s)` with a local
prime-control channel `Phi_(P,s)` on one fixed finite-dimensional matrix algebra. It has
distinguished nonzero prime modes `E_p` satisfying

```text
Phi_(P,s)(E_p) = p^(1/2-s) E_p.                         (1)
```

Let `tau(s)=1-conj(s)`. At a completed-source defect the reverse-oriented process is conjectured to
be the deterministic physical inverse:

```text
Phi_(P,tau(s)) Phi_(P,s) = id,
Phi_(P,s) Phi_(P,tau(s)) = id,                          (2)
```

with both maps completely positive and trace preserving. The limit over `P` must be compatible with
the archimedean laboratory and must be constructed before the zero divisor is inspected.

## Finite localization theorem

`[PROVED; BRIDGE]` Assume `(1)` and `(2)` for one nonempty finite `P`. Then `Re(s)=1/2`.

### Proof

A finite-dimensional quantum channel with a quantum-channel inverse is reversible, hence is unitary
conjugation. Its action on the complex operator space therefore has spectrum on the unit circle.
Equation `(1)` gives

```text
|p^(1/2-s)| = p^(1/2-Re(s)) = 1
```

for any `p in P`. Since `p>1`, this is equivalent to `Re(s)=1/2`. QED.

This theorem is parent quantum information theory plus elementary prime scaling. It is not new
scientific knowledge.

## Conditional RH theorem

`[PROVED CONDITIONAL BRIDGE]` Suppose there is a compatible all-prime/archimedean process family
`W_s`, constructed from the completed Euler--Gamma source without reading its divisor, such that for
every nontrivial zero `rho` of `xi`:

1. the process at `rho` and the reflected process at `tau(rho)` are deterministic physical
   processes;
2. their local prime-control channels satisfy `(1)`;
3. the two channels are inverse as in `(2)`.

Then RH follows by the finite localization theorem applied to any prime.

The zero is not an eigenvalue of a Hamiltonian. It is a parameter at which an acausal higher-order
process becomes exactly reversible.

## Boundary and degenerate cases

### One-dimensional control

A one-dimensional CPTP map is the identity and cannot carry the prime eigenmode. Every local prime
laboratory must therefore have a nontrivial operator space. Merely writing a scalar multiplier as a
"channel" is invalid.

### Physicality on an open set

If `(1)` and `(2)` held on an open set of `s`, the finite theorem would force that open set into the
critical line, an impossibility. Reversibility must be a defect condition, not a generic property of
the family.

### Reflection without inverse

Equivariance `W_(tau(s))=W_s^dagger` is too weak. Adjoint or time-reversed noisy channels can exist
off the line. The route needs the two-sided deterministic inverse law `(2)`.

### Shifted completed fake

The symmetric shifted product `xi(s+a)xi(s-a)` has off-line zeros and radial local parameters
`p^(+a),p^(-a)`. A process realization with a physical reflected inverse would reject it because
those reciprocal modes cannot both belong to a reversible channel unless `a=0`. This is a necessary
fake-family test, but the shifted-product calculation itself is already known in the project and
literature.

### Hidden-flow test

The route survives only while the process matrix is specified as a static multilinear probability
constraint with no global causal order. If the proof constructs it by time evolution, repeated
channel powers, transfer-matrix propagation, or a Hamiltonian whose spectral reality does the work,
it reduces to a flow/Hilbert--Polya route and is retired.

## Fake proof and exact failure

`[FAKE PROOF]` Take the completed Euler factors, regard multiplication by `p^(1/2-s)` as the local
prime channel, use the functional equation as its inverse, and apply the finite localization theorem.

`[FAILURE 1]` Scalar multiplication by `p^(1/2-s)` is not a trace-preserving quantum channel except
in a trivial one-dimensional misuse of the word channel.

`[FAILURE 2]` The functional equation identifies scalar completed amplitudes; it does not construct
an inverse higher-order process or a CPTP inverse on a prime-control algebra.

`[FAILURE 3]` Nothing presently shows that `xi(s)=0` is a reversibility event. Declaring the
reversibility obstruction to have determinant `xi` would be circular.

These failures localize the genuine mathematical task. The missing object is not another proof that
unit modulus selects the line; it is a source-canonical process whose reversibility obstruction is
the completed scalar for structural reasons.

## Exact open core

`[OPEN CORE 1: PRIME PROCESS CONSTRUCTION]` Construct a finite-prime process matrix with genuine
nontrivial local laboratories, Choi positivity, process normalization, and prime transfer modes
`p^(1/2-s)` on a source-defined operator subspace.

`[OPEN CORE 2: ARCHIMEDEAN ACAUSAL WELD]` Add the theta/Gamma laboratory as a higher-order operation
without choosing a global order and prove the reflected process law before zeros are read.

`[OPEN CORE 3: ZERO--REVERSIBILITY IDENTITY]` Prove that `xi(s)=0` forces the two-sided physical
inverse law. This must follow from a universal property, normalization failure, or Choi-rank collapse
of the source-built process, not from a determinant defined to be `xi`.

`[OPEN CORE 4: NONTRIVIALITY]` Exhibit one finite-prime or finite-mode model in which reversibility is
not automatic, not impossible, and not equivalent by definition to `Re(s)=1/2`.

## Preliminary collision and literature audit

`[SEARCH; NO EXACT SIGN FOUND]` Project-wide searches found no process-matrix, quantum-switch,
causal-nonseparability, or CPTP-inverse RH route. Multiple focused arXiv and general-web searches
likewise found no Riemann-zeta/RH use of indefinite causal order or of zeros as reversibility events
of a process matrix.

Nearby but noncolliding parent work includes:

- the process-matrix framework and causal witnesses for indefinite causal order;
- reversible/unitary quantum-channel structure;
- spectral, field-theoretic, modular-bootstrap, spin-foam, and quantum-chaos models of zeta zeros.

The last group is not the present mechanism: it treats zeros as spectra, partition-function data,
or correlator data, not as exact reversibility points of an acausal prime process.

This is still not a scientific-novelty verdict. Search-engine absence is weak, and the construction
and zero--reversibility theorem do not yet exist. The card remains `[NOVELTY UNVERIFIED]` and makes no
claim beyond the preliminary "no sign found" audit.

## Current verdict

`[LIVE OUTLANDISH CONJECTURE; NOT AN RH PROOF]`

The route has one proved localization lemma and one genuinely unbuilt object. Its value is that the
pre-Big-Bang premise changes the mathematical category: no global causal order is assumed, and a
zeta zero is proposed to be a reversibility singularity rather than an energy level, field vacuum,
or cohomology jump. The next move is to build the smallest two-prime, three-laboratory process and
decide whether a noncircular zero--reversibility obstruction can exist at all.

## Gates

- [x] 0 -> 1 in-progress: exact process object specified; four naive variants attacked; conditional
  RH theorem and first failures explicit; local and preliminary literature collision checks clean.
- [ ] 1 -> 2 fully-proven: no source-built process or zero--reversibility theorem exists.
- [ ] 2 -> 3 formalized: intentionally out of scope for the greenfield pass.
- [ ] 3 -> 4 publication-ready: ineligible before proof, significance, full parent-literature, and
  independent rediscovery audit.

## Parent references

- Oreshkov--Costa--Brukner, *Quantum correlations with no causal order*,
  [arXiv:1105.4464](https://arxiv.org/abs/1105.4464).
- Araújo--Branciard--Costa--Feix--Giarmatzi--Brukner, *Witnessing causal nonseparability*,
  [arXiv:1506.03776](https://arxiv.org/abs/1506.03776).
- Wallman--Granade--Harper--Flammia, *Estimating the coherence of noise*,
  [arXiv:1503.07865](https://arxiv.org/abs/1503.07865).
