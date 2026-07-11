# Infinite-real-support Cauchy-jet controllability

- **ID:** `infinite-real-support-cauchy-jet-controllability`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean) — `[PROVED] [FORMALIZED] [BRIDGE]`
- **Lane:** constrained Herglotz source variation; finite complex jet packets
- **Statement:** Finitely supported real masses on any infinite injective real support realize
  every finite complex Cauchy-jet packet at distinct upper-half-plane nodes.

## The theorem

Let `T` be an infinite set, let `t:T→R` be injective, let `(x_i)` be a finite injective family in
the upper half-plane, and assign a jet multiplicity `n_i` to every node.  Define

```text
A(a)_(i,j)=sum_(s in T) a_s (t_s-x_i)^(-(j+1)),
0<=j<n_i,                                                   (1)
```

for finitely supported real masses `a:T→R`.  Then

```text
A: R^(T,finite) → product_i C^(n_i)
```

is surjective as a real-linear map.

## Proof

First allow complex masses.  Suppose a complex linear functional annihilates every column of (1).
Its coefficients `c_(i,j)` satisfy

```text
sum_(i,j) c_(i,j)(t_s-x_i)^(-(j+1))=0                       (2)
```

for every `s`.  Multiply by

```text
D(X)=product_i (X-x_i)^(n_i).
```

The result is a polynomial `Q` which vanishes at every distinct `t_s`.  Since the support is
infinite, `Q=0`.  Uniqueness of the partial-fraction decomposition with pairwise coprime linear
denominators `(X-x_i)^(n_i)` forces every `c_(i,j)=0`.  Thus the complex column span is the full
complex jet space.

For real masses, let a real-linear functional annihilate all columns.  Write its restriction to
each complex coordinate as

```text
z ↦ Re(c_(i,j) z).
```

Equation (2) is replaced by the vanishing of its real part on the real support.  Adjoin the
Schwarz-conjugate node packet and coefficients `conj(c_(i,j))`.  Because every `t_s` is real, the
doubled complex Cauchy form is the original form plus its conjugate, hence zero.  The complex
result applies to the injective packet consisting of the upper nodes and their lower-half-plane
conjugates.  It forces every coefficient to vanish, so the real dual kernel is zero.  Finite
dimensional duality proves real surjectivity. `QED`

## Prime-log specialization

Taking `T` to be the primes and `t_p=log p` gives the exact finite-dimensional source
controllability needed by the facet-sewn Herglotz construction.  The support is injective and
infinite, while every evaluation node lies in the upper half-plane.

The theorem concerns arbitrary signed infinitesimal mass directions.  At a positive base mass,
every finitely supported direction remains inside the positive cone after multiplication by a
sufficiently small real scalar.  Thus it supplies the local submersion input; it does not by itself
perform the subsequent nonlinear rank-defect avoidance or Baire intersection.

## Lean certificate

`GaloisForLFunctions.HTGeometry.CauchyJetControllability` proves:

- `eval_clearedCauchyJetPolynomial_eq_mul_sum`;
- `cauchyJet_coeff_eq_zero_of_infinite`;
- `cauchyJetLinearCombination_surjective`;
- `cauchyJetRealLinearCombination_surjective`.

`GaloisForLFunctions.HTGeometry.PrimeLogCauchyJetControllability` proves the actual source theorem
`primeLogCauchyJetRealLinearCombination_surjective`.

The axiom audit contains only `propext`, `Classical.choice`, and `Quot.sound`.

## Classification

The proof is a confluent Cauchy/partial-fraction uniqueness argument plus finite-dimensional
duality.  It is a decisive formal bridge for the HT realization route, but its mechanism belongs
to classical interpolation theory and is not claimed as new scientific knowledge.

## Gates

- [x] 0 → 1: exact constrained source-control statement isolated
- [x] 1 → 2: complete unconditional paper proof
- [x] 2 → 3: unconditional Lean theorem, source specialization, and axiom audit
- [ ] 3 → 4: no standalone publication planned; classified as a bridge
