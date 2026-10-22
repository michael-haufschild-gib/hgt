# Real spectral factors have zero transverse logarithmic graph

- **ID:** `ccm-real-spectral-loggraph-transverse-vanishing-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper), `[BRIDGE]`
- **Scientific status:** `[PROVED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** Smirnov maximum principle and the Hardy characterization of zero Hankel
  symbols
- **Statement:** The anti-causal logarithmic graph of every even real-rooted Cartwright spectral
  factor is the zero operator. For the completed Xi source the same operator vanishes exactly when
  RH holds. Hence graph-core convergence from finite real-spectrum CCM determinants is itself
  RH-equivalent and cannot serve as a weaker replacement for divisor-preserving determinant
  convergence.

## 1. Real-rooted spectral factors

Let `F` be a nonzero Cartwright entire function whose zeros are all real, and put

```text
q_F(z)=-2F'(z)/F(z).                                     (1)
```

On the upper half-plane, `q_F` is analytic and belongs to the Smirnov class. Define

```text
D_(q_F)={f in H2_+:q_F f in L2(R)},
H_(q_F)f=P_-(q_F f).                                     (2)
```

Then

```text
H_(q_F)=0 on D_(q_F),
bar(H_(q_F))=0.                                         (3)
```

### Proof

The logarithmic derivative of a real-zero Cartwright product is analytic of Smirnov class in the
upper half-plane. If `f in D_(q_F)`, then `q_Ff` is again Smirnov and its boundary value belongs to
`L2`. The Smirnov maximum principle gives

```text
q_Ff in H2_+.                                           (4)
```

Therefore its anti-causal projection is zero, proving `(3)`. Boundary poles at real zeros cause no
exception: membership in `D_(q_F)` is exactly the cancellation condition making `(4)` an `H2`
function.

## 2. Exact Xi equivalence

For

```text
q_Xi(z)=-2Xi'(1/2-iz)/Xi(1/2-iz),                       (5)
```

let `D_Xi` be the closed anti-causal operator already constructed from its maximal multiplication
domain. Then

```text
D_Xi=0  iff  RH.                                        (6)
```

If RH holds, the centered Xi spectral factor has only real zeros, so Section 1 applies. Conversely,
every right-half Xi zero becomes an upper-half-plane pole of `(5)`. The rational-pole Hardy formula

```text
P_-(c f/(.-w))(x)=c f(w)/(x-w)                          (7)
```

gives one nonzero rank-one evaluation coordinate for that pole; distinct pole coordinates cannot
cancel. Hence `D_Xi` is nonzero whenever RH fails.

## 3. Consequence for finite CCM determinants

Under the CCM simple-even hypothesis, remove the nonvanishing aperture phase from the finite
regularized determinant and call the resulting even real-rooted factor `F_(lambda,N)`. Its closed
anti-causal logarithmic operator satisfies

```text
D_(lambda,N)=0.                                         (8)
```

Suppose a proposed finite-stage boundary-strip implementation asks for convergence on a graph core
`C_Xi`:

```text
Q_uD_(lambda_j,N_j)f -> Q_uD_Xi f                       (9)
```

for every `f in C_Xi` and every `u>0`. By `(8)`, the left side is identically zero. Hence `(9)`
forces `Q_uD_Xi=0` for every `u`, then `D_Xi=0`, and finally RH by `(6)`.

Thus the graph-core convergence hypothesis is not an easier analytic substitute for the CCM
determinant limit. On the real-spectrum branch it has already absorbed the entire RH conclusion.
The surviving positive alternatives are exactly the original ones:

```text
locally uniform divisor-preserving determinant convergence,
cofinal Weil spectral-floor convergence,
or a finite-stage carrier with genuine transverse charge.                (10)
```

The theorem is standard Hardy/Smirnov theory and is a bridge rather than new scientific knowledge.

## 4. Periodic-pencil audit

The intrinsic periodic-pencil theorem does not change `(8)`--`(10)`. Its dimension counts analytic
variables in an exact nonpure Stanley--Reisner HT realization. The causal/anti-causal decomposition
in `(2)` is two Hardy polarizations of one analytic variable, not a periodic-pencil realization on
`C^2`. Applying the dimension-two lower bound to CCM would first require an exact proof that the
CCM source--divisor relation complex is nonpure and has the stated Stanley--Reisner annihilator.
No such identification is currently available.

## Gates

- [x] real-rooted logarithmic graph proved transverse-zero
- [x] Xi transverse graph proved zero exactly under RH
- [x] finite CCM graph-core shortcut proved RH-equivalent
- [x] divisor and spectral-floor branches retained as the live alternatives
- [x] periodic-pencil dimension kept separate from Hardy channel count
- [ ] prove the CCM divisor limit or the cofinal Weil floor
- [ ] RH

## Lean status

`[FORMALIZED]` — module `formal/GaloisForLFunctions/RHTower/CCM/CCMRealSpectralLogGraph.lean`
(4 theorems, all unconditional, axioms exactly `[propext, Classical.choice, Quot.sound]`, wired into
`formal/GaloisForLFunctions/RHTower.lean`).

What is proved in Lean:

- `antiCausal_coordinate_ne_zero` — **equation (7), nonvanishing**: the anti-causal rank-one
  coordinate `x ↦ c/(x-w)` attached to an upper half-plane pole is a nonzero function whenever the
  residue is nonzero.  The exact causal/anti-causal split of the Cauchy insertion itself is
  `CCMTwoChannelGraph.cauchy_insertion_split` (card
  `ccm-logderivative-closed-two-channel-graph-law`), reused here.
- `cauchy_coeff_eq_zero_of_vanishing_on_real` — **section 2, independence step**: a finite
  combination of Cauchy kernels with *distinct non-real* poles that vanishes on the whole real line
  has all coefficients zero.  This is the "distinct pole coordinates cannot cancel" step that turns
  one nonzero evaluation coordinate per off-line zero into nonvanishing of the operator.  The proof
  clears denominators into a polynomial identity, uses that a polynomial vanishing on ℝ is zero, and
  evaluates at each pole.
- `eq_zero_of_tendsto_of_forall_eq_zero` — **equations (8)–(9)**: a convergent family of zero
  operators has zero limit, so graph-core convergence from identically-zero finite stages forces the
  limit to vanish.
- `eq_zero_of_forall_compression_zero` — **section 3, compression step**: if every compression
  `Q_u D` vanishes and the compressions converge back, then `D = 0`.  Together with the previous
  item this is exactly the card's deduction `(8)` + `(9)` ⟹ `D_Ξ = 0` ⟹ RH.

Deliberately outside the Lean statement (cited parents, not results of this card):

- the Smirnov maximum principle and the Smirnov-class membership of the logarithmic derivative of a
  real-rooted Cartwright product, i.e. `(4)` and hence `(3)`;
- the Hardy characterization of zero Hankel symbols;
- the analytic construction of the closed anti-causal operator `D_Ξ` from its maximal
  multiplication domain, and the equivalence `(6)` itself;
- the CCM simple-even hypothesis and the removal of the aperture phase in section 3.
