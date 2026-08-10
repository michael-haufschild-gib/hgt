# Adaptive eigenframe two-query source-memory law

**Status:** `[ACTIVE] [PAPER PROOF IN PROGRESS] [LEAN OPEN] [NOVELTY OPEN]`

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
   `(D+1)^-1`. No factor exponential in Jordan--Wigner Pauli weight occurs.

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
every word is nonidentity by the same pairing with one of its members.

The live separation condition is

```text
binom(2n,q)^2 < 2^n + 1.
```

For each fixed even `q`, polynomial-versus-exponential growth makes this true eventually. In
particular it applies to fixed-`q` SYK (including the standard `q=4` ensemble) without any
minimum-gap, spectral-universality, eigenbasis-moment, or disorder assumption.

## Open obligations

- Prove adaptive eigenframe coefficient extraction and Cauchy domination in Lean.
- Prove exact Haar score in Lean from `haar_sq_trace_pure_state_conjugation`.
- Formalize fixed-cardinality Majorana-word injectivity and nonidentity.
- Formalize eventual separation for fixed even `q`, or provide an unconditional explicit regime.
- Audit external novelty and exact oracle-model consequences for recent SYK pseudorandomness work.

