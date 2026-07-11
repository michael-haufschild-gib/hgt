# Prime-density local-unitary invariants are zero-blind

- **ID:** `prime-density-local-unitary-zero-blindness`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper); route gate
- **Scientific status:** `[BRIDGE; NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** `../../5-failed/prime-aperture-unitary-screen-conjecture.md`; Helson zeta
  prescribed-divisor theorems
- **Statement:** Completely multiplicative unimodular phase twists preserve the full prime density
  matrix up to a tensor product of one-prime unitaries, and therefore preserve every
  local-unitary-invariant quantum statistic of every prime partition, while their continued Euler
  products can have prescribed zero and pole divisors below `Re(s)=1`.

## Setup

Fix `sigma>1/2`. On `l2(N_{>0})`, define the normalized arithmetic state

```text
Psi_(sigma,chi)
  = zeta(2 sigma)^(-1/2) sum_(n>=1) chi(n)n^(-sigma)|n>,
```

where `chi:N_{>0}->S^1` is completely multiplicative. Since `|chi(n)|=1`,

```text
||Psi_(sigma,chi)||^2
  = zeta(2 sigma)^(-1) sum_n n^(-2 sigma)
  = 1.
```

Let

```text
rho_(sigma,chi)=|Psi_(sigma,chi)><Psi_(sigma,chi)|.
```

The untwisted zeta state is the case `chi=1`.

Unique factorization identifies the coefficient Hilbert space with the incomplete prime Fock
tensor product

```text
l2(N_{>0}) ~= tensor_p l2(N_0),
|n> ~= tensor_p |v_p(n)>.
```

For each prime define the local diagonal unitary

```text
U_(p,chi)|k> = chi(p)^k |k>.
```

The global diagonal unitary is

```text
U_chi|n> = chi(n)|n>.
```

On the algebraic finite-occupation core, complete multiplicativity gives the exact tensor identity

```text
U_chi = tensor_p U_(p,chi).
```

It extends unitarily to `l2(N_{>0})` because it preserves every coefficient norm.

## Theorem

For every `sigma>1/2` and every completely multiplicative unimodular `chi`,

```text
Psi_(sigma,chi)=U_chi Psi_(sigma,1),
rho_(sigma,chi)=U_chi rho_(sigma,1) U_chi^*.
```

Consequently the following data are independent of `chi`:

1. the spectrum, rank, purity, Schatten norms, and von Neumann or Renyi entropies of the full
   density operator;
2. the normalizability and trace-class threshold `sigma=1/2`;
3. every quantum Fisher quantity in the `sigma` direction;
4. the spectrum and entropy of every reduced density matrix associated with an arbitrary prime
   bipartition; and
5. every entanglement monotone invariant under tensor products of local prime unitaries.

In fact each `Psi_(sigma,chi)` is the prime-product state

```text
tensor_p
  ((1-p^(-2 sigma))^(1/2)
    sum_(k>=0) chi(p)^k p^(-k sigma)|k>),
```

so its entanglement across every partition of the prime modes is zero. The phase twist changes the
wave interference without changing any particle-side or local-unitary quantum information.

## Proof

For each basis vector `|n>`, complete multiplicativity and unique factorization give

```text
(tensor_p U_(p,chi))|n>
  = product_p chi(p)^(v_p(n)) |n>
  = chi(n)|n>
  = U_chi|n>.
```

Thus the tensor product identity holds on the finite-occupation basis and hence on its dense
linear span. Both sides are isometries, so they extend to the same unitary on the completion.

Applying `U_chi` termwise to the untwisted state proves the vector identity. Taking the rank-one
outer product proves unitary conjugacy of the densities. Spectral, Schatten, entropy, and purity
claims follow from unitary conjugacy. For a prime bipartition `P=A disjoint_union B`, the unitary
factorizes as `U_A tensor U_B`; partial trace therefore conjugates the reduced density by the
corresponding local unitary and preserves its spectrum. The explicit tensor product proves
separability and zero prime-partition entanglement.

The Fisher metric in `sigma` is also unchanged because `U_chi` is independent of `sigma`:

```text
partial_sigma Psi_(sigma,chi)
  = U_chi partial_sigma Psi_(sigma,1).
```

All inner products entering the pure-state quantum Fisher tensor are therefore identical.

## Divisor separation

The local-unitary orbit does not control analytic continuation. A Helson zeta function has

```text
zeta_chi(s)
  = sum_n chi(n)n^(-s)
  = product_p (1-chi(p)p^(-s))^(-1)
```

on `Re(s)>1`. Bochkov--Romanov prove essentially arbitrary zero and pole prescription in
`21/40<Re(s)<1`; Andersson proves a Mittag--Leffler theorem allowing prescribed continued zeros
and poles in `Re(s)<1` for suitable Helson zeta functions.

Hence Euler tensor factorization, the entire prime probability law, the full density spectrum,
all prime-partition entanglement data, the Fisher wall, and every local-unitary invariant can be
held fixed while the continued divisor changes.

## Consequence for RH architectures

`[PROVED ROUTE GATE]` No RH criterion can factor through the local-unitary equivalence class of the
prime density matrix. This excludes, by itself or in any combination:

- particle probabilities and prime occupation statistics;
- density eigenvalues, purity, entropy, and Schatten profiles;
- prime-subsystem entanglement spectra and local-unitary entanglement monotones;
- the normalizability or Fisher signature wall; and
- any purported uncertainty functional invariant under independent one-prime phase rotations.

A viable joint object must contain an external phase reference not transported by `U_chi`. In the
zeta problem the only canonical candidate is the archimedean theta/Gamma completion together with
its functional-equation polarization. The missing invariant is therefore relative: it must measure
the failure of the prime phase gauge to commute with the fixed archimedean completion.

This theorem does not show that such a relative invariant exists, and it does not prove RH.

## Parent-theory and novelty verdict

The unitary-conjugacy proof is elementary Hilbert-space and tensor-product theory. The flexible
divisor input is imported from the Helson zeta literature. Their combination gives a useful and
broad RH route gate, but it is a direct cross-parent consequence rather than new scientific
knowledge.

## Gates

- [x] 0 -> 1: full density, prime tensor factorization, local phase gauge, and divisor comparison
  stated exactly
- [x] 1 -> 2: complete paper proof; Helson divisor flexibility cited; route consequence delimited
- [ ] 2 -> 3: optional Lean formalization after a reusable infinite prime tensor model exists
- [ ] 3 -> 4: not a standalone novelty target

## References

- I. Bochkov and R. Romanov, *On zeroes and poles of Helson zeta functions*, J. Funct. Anal. 282
  (2022), arXiv:2106.15949.
- J. Andersson, *Mittag--Leffler type theorems for Helson zeta-functions*, arXiv:2408.15713.
