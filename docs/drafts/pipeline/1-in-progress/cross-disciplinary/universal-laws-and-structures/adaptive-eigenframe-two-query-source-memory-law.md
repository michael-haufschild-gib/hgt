# Adaptive eigenframe two-query source-memory law

**Status:** `[ACTIVE] [CORE LEAN-PROVEN] [ASYMPTOTIC LEAN-PROVEN] [NOVELTY AUDITED]`

## Frontier target

Remove bounded-Pauli-weight loss from permanent static-Hamiltonian/Haar separation and apply the
result to fixed-body Majorana/SYK Hamiltonians, whose Jordan--Wigner Pauli strings have extensive
qubit weight.

## Conjecture loop

1. **Choi dictionary score.** Two maximally entangled queries recover squared Pauli-transfer
   coefficients and should give static score `M^-2` against Haar scale `(D^2-1)^-1`.
   **Survives mathematically, but rejected as proof route:** exact adjoint-Haar moment would require
   new fourth-entry-moment infrastructure and ancillas are unnecessary.
2. **Adaptive eigenframe score.** For dictionary words `A_i`, choose `i,j` uniformly, choose a
   uniform product eigenstate of `A_j`, evolve two copies by the same unknown `U`, measure `A_i`
   on both, and multiply outcomes. **Live.** Eigenframe completeness plus Cauchy--Schwarz gives the
   same static lower bound `M^-2`; the existing pure-state Haar theorem gives exact Haar score
   `(D+1)^-1`. No factor exponential in Jordan--Wigner Pauli weight occurs. **Proved in Lean.**

## Proposed universal theorem

Let `A_1,...,A_M` be distinct nonidentity Pauli words on `n >= 1` qubits and let `U` be any unitary.
For each `j`, let `{rho_{j,x}}_{x in {0,1}^n}` be the product eigenframe of `A_j`. Define

```text
E_A(U) = (1 / (M^2 2^n)) sum_{i,j,x}
           Tr(rho_{j,x} U^* A_i U)^2.
```

If `C_{ji}=2^-n Tr(A_j U^* A_i U)` is the dictionary compression of the Pauli-transfer matrix, then

```text
(1/M^2) sum_{i,j} C_{ji}^2 <= E_A(U).
```

Consequently, if `C h=h` for some nonzero coefficient vector, then

```text
E_A(U) >= 1/M^2.
```

For Haar `V`, each `rho_{j,x}` is pure and each `A_i` is a traceless Hermitian involution, hence

```text
E_Haar E_A(V) = 1/(2^n+1).
```

Thus every autonomous Hamiltonian supported on this dictionary is permanently separated from Haar
by the same efficient two-forward-query experiment whenever `M^2 < 2^n+1`.

## Fixed-body Majorana specialization

Use the corpus Jordan--Wigner frame `QuantumAlg.TFIM.frame n`. A `q`-body Majorana word is a
`q`-element subset of its `2n` Majorana generators; its phase-free Pauli label is their XOR.

For two subsets `S,T` of equal cardinality, equality of XOR labels is impossible unless `S=T`:
choose `a in S \ T` and pair both labels with `gamma_a` under the Pauli symplectic form. The left
pairing contains `q-1` ones and the right contains `q` ones, differing by one in `ZMod 2`.
Therefore the fixed-`q` dictionary has exactly `binom(2n,q)` distinct words. For positive even `q`,
every word is nonidentity by the same pairing with one of its members. **All statements in this
paragraph are proved in Lean for every Pauli-Majorana frame, then specialized to the concrete
Jordan--Wigner frame.**

The live separation condition is

```text
binom(2n,q)^2 < 2^n + 1.
```

For each fixed even `q`, polynomial-versus-exponential growth makes this true eventually. In
particular it applies to fixed-`q` SYK (including the standard `q=4` ensemble) without any
minimum-gap, spectral-universality, eigenbasis-moment, or disorder assumption.

## Open obligations

- Formalize a bounded-outcome sampling/amplification theorem for the literal two-copy experiment.
- Compare the resulting quantitative design obstruction line by line with the approximation norm in
  recent SYK pseudorandomness claims.

## Lean status

Implemented and foreground-verified in
`formal/GaloisForLFunctions/HTGeometry/AdaptiveEigenframeTwoQuerySourceMemory.lean`:

- exact eigenframe extraction and Cauchy domination;
- permanent autonomous dictionary lower bound;
- exact Haar score;
- fixed-cardinality Majorana injectivity for every Pauli-Majorana frame;
- exact dictionary cardinality `binom(2n,q)`;
- nonidentity for every positive even `q`;
- permanent Jordan--Wigner/Majorana source-memory lower bound and finite-size strict Haar
  separation;
- cofinite separation for every fixed positive even `q`, every nonzero coefficient vector, and every
  real time;
- Haar high-score probability at most `binom(2n,q)^2/(2^n+1)`, with this bound proved to tend to
  zero;
- a literal coefficient-parametrized fixed-`q` Majorana Hamiltonian, with dictionary support and
  nonzeroness proved rather than assumed.

## External novelty audit

- Cui--Schuster--Mao--Huang--Brandao, *Random unitaries from Hamiltonian dynamics*,
  arXiv:2510.08434, already proves a two-copy product-state distinguisher for constant qubit-local
  Hamiltonians. Its frame is sampled independently of the measured Pauli word and the stated signal
  carries the `3^-q` product-frame penalty. Therefore the generic conservation idea and the broad
  phrase “static Hamiltonians are not Haar” are not novel.
- The present mathematical increment is the word-adapted signed eigenframe identity: it extracts a
  chosen Pauli-transfer coordinate exactly and eliminates the weight penalty. This makes the test
  apply to polynomial dictionaries whose individual Jordan--Wigner strings have extensive qubit
  weight.
- For fixed-`q` Majorana/SYK support this yields an unconditional efficient-scale obstruction:
  dictionary size is `binom(2n,q)`, static score is at least its inverse square for every time, Haar
  mean is exactly `(2^n+1)^-1`, and Haar probability of reaching the static floor vanishes.
- Golmohammadi, *Pseudorandom Dynamics in the SYK Model and Cryptographic Censorship in JT
  Gravity*, arXiv:2605.25178, claims approximate polynomial designs under random-matrix/eigenbasis
  assumptions. The new invariant is directly relevant: any approximation claim strong enough to
  suppress this two-query polynomial signal must explain why the conserved fixed-`q` source
  coordinate is absent. No contradiction is claimed until approximation norms and quantifiers are
  matched formally.
