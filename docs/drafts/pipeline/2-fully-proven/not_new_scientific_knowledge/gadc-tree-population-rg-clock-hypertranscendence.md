# Generalized-amplitude-damping tree population clock is hypertranscendental

- **ID:** `gadc-tree-population-rg-clock-hypertranscendence`
- **Stage:** 2-fully-proven / not new scientific knowledge
- **Type:** THEOREM (paper) / QUANTUM-CHANNEL POPULATION-SECTOR COROLLARY
- **Scientific status:** `[PROVED] [PARENT-DERIVED] [NOT NEW MATHEMATICS]`
  `[GENUINE CPTP CHANNEL] [COMMUTATIVE DIAGONAL SECTOR ONLY]`
- **Parent theorem:**
  `../needs-audit/asymmetric-binary-tree-channel-rg-clock-hypertranscendence.md`
- **Statement:** The diagonal population sector of an interior generalized amplitude damping
  channel, when used independently on every edge of a homogeneous regular tree and followed by
  exact population-likelihood belief propagation, has a hypertranscendental exact message-depth
  beta and clock in every locally invertible differentially algebraic message coordinate.  The
  transition is at damping `d=1-1/p` and is independent of the bath population.  This is a physical
  realization of the asymmetric binary-channel theorem, not an operator-valued quantum theorem.

## Exact channel input

Use `d in [0,1]` for the damping parameter denoted `gamma` in the source, and let `N in [0,1]` be
the excited-state population of the bath.  Khatri--Sharma--Wilde give the Bloch action of the
generalized amplitude damping channel `A_(d,N)` as

```text
(r_x,r_y,r_z) |->
  (sqrt(1-d) r_x, sqrt(1-d) r_y, (1-d) r_z+d(1-2N)).             (1)
```

In particular, diagonal density matrices remain diagonal.  With `+` denoting the `sigma_z=+1`
basis state, restriction to the invariant population algebra gives the binary transition matrix

```text
alpha := P(+|+) = 1-dN,
gamma := P(+|-) = d(1-N).                                      (2)
```

The two affine signal parameters and their gap are therefore

```text
u=2 alpha-1 = 1-2dN,
v=2 gamma-1 = 2d(1-N)-1,
u-v=2(1-d),             alpha-gamma=1-d.                        (3)
```

For `0<d<1` and `0<N<1`, equation `(2)` is a strictly positive informative binary channel:

```text
0<gamma<alpha<1.                                                (4)
```

The conventional non-inverted positive-temperature branch has `0<N<1/2`; `N=1/2` is the
infinite-temperature bath, and `N>1/2` is the population-inverted branch related by Pauli-`X`
conjugation.  The theorem uses only the interior channel condition `(4)`.

## Branch multiplication and the exact rational map

Represent an incoming diagonal likelihood message by magnetization `y`.  The two one-child
likelihood weights are proportional to `1+uy` and `1+vy`.  For `p>=2` identical conditionally
independent descendants, likelihoods multiply.  The exact homogeneous posterior-population update
is consequently

```text
                    (1+uy)^p-(1+vy)^p
R_(p;d,N)(y)= ----------------------------------,               (5)
                    (1+uy)^p+(1+vy)^p

u=1-2dN,              v=2d(1-N)-1.
```

This is exactly the parent asymmetric binary-tree family.  It has no primitive
numerator-denominator cancellation for `(4)`, and its zero-message multiplier is

```text
R_(p;d,N)'(0)=p(alpha-gamma)=p(1-d).                             (6)
```

The bath population changes the nonlinear asymmetry of `(5)` but cancels from the linear signal
eigenvalue.  At `N=1/2`, one has `u=1-d` and `v=-(1-d)`, so `(5)` reduces exactly to the symmetric
Bethe/BSC family with signal parameter `a=1-d`.

## All-interior-channel theorem

The parent asymmetric-transfer theorem applies for every `0<d<1` and `0<N<1`:

1. if `d>1-1/p`, then `p(1-d)<1`, zero is attracting, and the local Schroeder beta/clock is HT;
2. if `d=1-1/p`, then the zero fixed point is parabolic and every sectorial Abel beta/clock is HT;
3. if `d<1-1/p`, then zero is repelling, the positive interval supplies a non-superattracting
   fixed basin excluding every Ritt-integrable rational class, and the Poincare beta/clock is HT.

Therefore every interior GADC has a hypertranscendental exact homogeneous population-message clock
after regular-tree branch multiplication.  The conclusion survives every locally invertible DA
population-message coordinate, including magnetization, odds, log-likelihood, and cavity-field
charts on their local domains.

The endpoints are different:

- `d=0` is the identity quantum channel.  Equation `(5)` is the noiseless symmetric tree map,
  Moebius-conjugate to `z |-> z^p`, and its exact clock is DA.
- `d=1` is full thermal reset.  The two rows in `(2)` coincide, `u=v`, and `(5)` collapses to zero.
- `N=0` and `N=1` are non-strict bath boundaries.  They are not promoted by the interior parent
  theorem on this card.

## The physical fracture: sequential versus branching dynamics

The GADC by itself does **not** generate an HT time evolution.  Iterating the channel sequentially
on its diagonal sector gives the affine recursion

```text
r_z |-> (1-d)r_z+d(1-2N),                                      (7)
```

whose iterates and continuous interpolation are elementary and DA.  The HT obstruction is born at
the nonlinear operation absent from `(7)`:

```text
independent quantum-channel branches
  + multiplication of their diagonal likelihoods
  + projective normalization
  -> nonexceptional rational iteration
  -> no finite algebraic-differential exact depth generator.   (8)
```

Thus the physical carrier is not dissipation alone.  It is branching conditional independence
followed by Bayesian/tensor contraction.  Damping controls the universal multiplier `(6)`; the bath
population controls the asymmetric higher-order geometry.

## Quantum scope boundary

This is a theorem about a genuine completely positive trace-preserving qubit channel, but only
about its invariant commutative diagonal algebra.  It does not prove any of the following:

- hypertranscendence of the transverse coherence components `r_x,r_y`;
- an operator-valued or noncommutative quantum belief-propagation clock;
- hypertranscendence of channel capacities, entanglement, or a Lindblad semigroup;
- a continuum QFT renormalization theorem.

The next quantum novelty gate is therefore sharp: replace scalar diagonal likelihoods by
noncommuting positive matrices or completely positive message maps, and prove that a physically
defined scalar observable inherits HT without diagonalizing the problem back to a classical
binary channel.

## Anti-theatre and novelty verdict

The GADC Kraus/Bloch formulas, its invariant diagonal population algebra, and binary-tree belief
propagation are parent theory.  Once `(2)` is identified, the HT conclusion is a direct substitution
into the already proved asymmetric-channel theorem.  It is scientifically useful because it is the
first exact realization in this project by a finite-temperature CPTP noise model, but it is not new
mathematics and must not be sold as quantum-coherence hypertranscendence.

Targeted searches for the conjunction of generalized amplitude damping, tree belief propagation,
Schroeder/Abel/Poincare iteration, and hypertranscendence found the component literatures but no
prior statement of this population-clock corollary.  That negative evidence does not pass the
novelty gate: a new physical instantiation of a proved class theorem remains parent-derived.  Recent
work on amplitude damping in quantum-code and tensor-network settings is neighboring literature,
not evidence for the noncommutative theorem still missing here.

## Lean boundary

The affine Bloch population action, the induced transition probabilities `(2)`, the parameter gap
`(3)`, the rational family `(5)`, its symmetric-bath specialization, multiplier `(6)`, and damping
endpoints are unconditional algebra.  They are formalized in
`formal/GaloisForLFunctions/HTGeometry/GADCTreePopulationRG.lean`.

Complete positivity is a physical domain property of the source channel and is not postulated as a
Lean axiom.  The real interval dynamics and the external Becker--Bergweiler HT classification
remain paper-level parent theorems and are not encoded as assumptions.

## Primary sources

- S. Khatri, K. Sharma, and M. M. Wilde, *Information-theoretic aspects of the generalized
  amplitude damping channel*, *Physical Review A* 102, 012401 (2020),
  <https://arxiv.org/abs/1903.07747>.  Equations (70)--(78) give the Kraus and Bloch actions used in
  `(1)`--`(3)`.
- S. B. Hopkins and A. Li, *Adversarially-Robust Inference on Trees via Belief Propagation*,
  <https://proceedings.mlr.press/v247/hopkins24a.html>.
- G. Fernandes, *A survey on the hypertranscendence of the solutions of Schroeder's, Boettcher's
  and Abel's equations*, <https://arxiv.org/abs/2102.12168>.
- W. Bergweiler, *Solution of a problem of Rubel concerning iteration and algebraic differential
  equations*, *Indiana University Mathematics Journal* 44 (1995), 257--267.
- S. K. Zhao et al., *Amplitude Damping and Post-Selection Effects in the Toric Code*,
  <https://arxiv.org/abs/2607.01364>, neighboring quantum-code literature published after the parent
  GADC analysis; it does not supply the theorem on this card.

## Gates

- [x] GADC Bloch action checked against the Kraus-source formulas.
- [x] Invariant diagonal algebra and induced binary transition matrix derived.
- [x] Exact `p`-branch population-likelihood recursion derived.
- [x] Multiplier `p(1-d)` and bath-independence proved.
- [x] Attracting, parabolic, and repelling HT regimes inherited from the parent theorem.
- [x] Identity and reset endpoints separated.
- [x] Sequential affine dynamics separated from branching HT dynamics.
- [x] Classical diagonal-sector and quantum-coherence claims separated.
- [x] Direct-corollary novelty failure stated.
- [x] Unconditional exact algebra formalized in HTGeometry.
- [ ] Operator-valued noncommutative channel-message inheritance theorem proved.
- [ ] Continuum QFT observable inheriting the same obstruction proved.
