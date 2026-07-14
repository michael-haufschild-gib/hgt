# Xi prime seams are finite rational-Hurwitz fibre defects

- **ID:** `xi-hurwitz-rational-fiber-seam`
- **Stage:** 3-formalized
- **Type:** THEOREM / source-value bridge
- **Scientific status:** `[PROVED] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** A normalized finite rational fibre of absolutely convergent Hurwitz-zeta values
  recovers `n^s` exactly.  Therefore every FE--Schwarz scale seam is exactly the difference of the
  inverse responses at `conj rho` and `1-rho`; no Hurwitz continuation at a zero, divisor
  enumeration, or limiting coefficient extraction is required.

## Theorem

For `n > 0` and `Re(s) > 0`, define

```text
R_n(s)
 = [sum_(0 <= k < n) zeta(s+1,(1+k)/n)]
   / [n zeta(s+1)].
```

Every value in this expression is represented by its absolutely convergent Dirichlet series.  The
Hurwitz distribution relation gives

```text
R_n(s)=n^s.                                             (1)
```

For an open-strip point `rho`, define the finite-fibre reflection seam

```text
S_n(rho)
 = log(n) [R_n(conj rho)^(-1)-R_n(1-rho)^(-1)].        (2)
```

Then

```text
S_n(rho)
 = log(n) [n^(-conj rho)-n^(-(1-rho))]
 = orbitwiseNatPrimeSeamCharge n rho.                  (3)
```

At `n=2`, equality of the two responses is exactly vanishing of the common first-prime charge and
therefore implies RH by the existing charge collapse.  No all-prime coherence premise is needed for
this finite-value formulation.  The new content is `(1)--(3)`: it moves the producer interface
entirely into two finite value packets in `Re > 1`, rather than asserting critical-line
localization.

## Proof

Apply the already-formalized `hzeta_distribution` at exponent `s+1` and base point `a=1`.  Since
`Re(s+1)>1`, `hzeta_one_eq_riemannZeta` identifies the base value and the Euler product makes its
zeta denominator nonzero.  Dividing the distribution relation by `n zeta(s+1)` and using the
complex-power addition law gives `(1)`.

The inverse-power identity `(n^s)^(-1)=n^(-s)` then turns `(2)` into `(3)`.  At any modulus `n>1`,
equality of the two responses implies equality of their norms.  These norms are

```text
n^(Re rho),   n^(1-Re rho),
```

so strict monotonicity of real powers forces `Re rho=1/2`; the converse is immediate from
`conj rho=1-rho`.  At `n=2`, the existing scale-two identification makes this response equality
equivalent to vanishing of `orbitwiseFirstPrimeSeamCharge`.  The global theorem then passes through
the already-proved first-prime/coherent-prime collapse to RH.

## Anti-circularity gate

Equation `(1)` is unconditional for every positive-real-part exponent and does not use a zeta
zero.  Equation `(3)` is an exact source representation of the existing seam, not a proof that it
vanishes.  The remaining source obligation is explicit: prove equality of the two normalized
two-point packets at exponents `conj rho + 1` and `2-rho` by an independent source relation.  Lean
also proves that this equality is RH-equivalent, so the multiplication formula alone cannot supply
it.

## Literature placement

The parent identity is the classical Hurwitz multiplication/distribution formula; [DLMF
25.11.15](https://dlmf.nist.gov/25.11.E15) derives it by Euclidean reindexing of the defining series
and points to Apostol.  The finite-fibre
normalization `(1)` is an immediate shifted specialization.  No novelty is claimed.  Its role is
to expose the RH seam inside a finite packet of absolutely convergent Hurwitz values.

## Lean certificate

The module

```text
formal/GaloisForLFunctions/RHTower/XiHurwitzRationalFiberSeam.lean
```

proves and wires:

```text
rationalHurwitzFiberResponse_eq_cpow
rationalHurwitzFiberResponse_two
rationalHurwitzFiberReflectionSeam_eq_primeSeamCharge
rationalHurwitzFiberResponse_reflection_fixed_iff
rationalHurwitzFiberTwoReflectionSeam_eq_firstPrimeSeamCharge
rationalHurwitzFiberTwo_reflection_fixed_iff_firstPrimeSeamCharge_eq_zero
xiRationalHurwitzFiberTwoReflectionFixed_iff_firstPrimeSeamChargesVanish
riemannHypothesis_of_xiRationalHurwitzFiberTwoReflectionFixed
xiRationalHurwitzFiberTwoReflectionFixed_iff_riemannHypothesis
```

The theorem is imported by the `RHTower` umbrella.  The leaf build and axiom audit pass; the final
theorems use only Lean's standard `propext`, `Classical.choice`, and `Quot.sound` axioms.

## Gates

- [x] prior Lean and pipeline search
- [x] failed heat-echo descent checked and excluded
- [x] classical parent identified
- [x] Lean theorem proved
- [x] RHTower umbrella wired
- [x] generated indexes wired
- [x] targeted build and axiom audit pass
- [x] `RHTower` umbrella build passes
- [x] formal lint pass

## Paper-level dyadic refinement square

The paper theorem
`../../2-fully-proven/not_new_scientific_knowledge/xi-rational-hurwitz-dyadic-refinement-square-law.md`
normalizes the modulus-`n` reflection seam by

```text
H_n(rho) = n*||rationalHurwitzFiberReflectionSeam n rho||^2
             /(4*log(n)^2).
```

For every `n>1` it proves

```text
H_n(rho) = sinh((re(rho)-1/2)*log(n))^2,
H_(n^2)(rho) - 4*H_n(rho) = 4*H_n(rho)^2.
```

Thus the nonlinear part of the exact finite-fibre refinement `n -> n^2` is a positive square whose
zero locus is the critical line.  At `n=2`, a source proof of the linear refinement
`H_4=4*H_2` on every Xi fibre would force the already formalized common first-prime charge to
vanish and hence imply RH.  This composition is proved on paper but not yet formalized.
