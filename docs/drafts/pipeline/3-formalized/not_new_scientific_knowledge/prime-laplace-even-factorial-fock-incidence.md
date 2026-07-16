# Gamma damping makes the complete prime incidence Hilbert--Schmidt in the even-factorial jet metric

- **ID:** `prime-laplace-even-factorial-fock-incidence`
- **Stage:** 3-formalized/not_new_scientific_knowledge
- **Type:** THEOREM / SOURCE INCIDENCE / RH BRIDGE INFRASTRUCTURE
- **Scientific status:** `[PROVED HERE] [LEAN-VERIFIED] [NOT NEW SCIENTIFIC KNOWLEDGE]
  [NOT AN RH PROOF]`
- **Parent:** `prime-laplace-gamma-jet-incidence-phase-transition.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/PrimeLaplaceEvenFactorialFockIncidence.lean`

## Statement

For a prime `p`, a source point `x`, and a raw-jet index `j`, set

```text
E_x(p,j)=phi_Gamma(2 log p) p^(-2x) (log p)^(2j)/(2j)!,
phi_Gamma(t)=cosh(t)^(-1/2).
```

Then

```text
sum_(j>=0) E_x(p,j)
 =phi_Gamma(2 log p) p^(-2x) cosh(log p)
 <=sqrt(2) p^(-2x).
```

Consequently, for every `x>1/2`,

```text
sum_p sum_(j>=0) E_x(p,j)<infinity.
```

Thus the complete Gamma-damped prime-to-raw-jet matrix is Hilbert--Schmidt after normalizing the
`j`-th coordinate by `sqrt((2j)!)`.

## Proof

The even Taylor series gives the exact identity

```text
sum_(j>=0) (log p)^(2j)/(2j)!=cosh(log p).
```

For every prime `p`,

```text
cosh(log p)=(p+p^(-1))/2<=p,
phi_Gamma(2 log p)<=sqrt(2) exp(-log p)=sqrt(2)/p.
```

Their product is at most `sqrt(2)`.  The remaining majorant is the convergent prime power series
`sum_p p^(-2x)` for `x>1/2`.  Tonelli's theorem for nonnegative series yields the double
summability.

## RH meaning

This removes the naive factorial-Fock divergence from complete source incidence.  It supplies a
canonical all-prime Hilbert--Schmidt carrier on the source half-plane and can feed every normalized
raw jet simultaneously.

It does **not** yet prove RH.  Three logically separate gates remain:

1. prove that the even-factorial completion supports the required critical transport, or replace
   it by a transported relative completion;
2. identify its completed source Gram form with the canonical Xi/Weil form rather than merely with
   prime--Gamma reconstruction data;
3. derive the missing critical orientation/coercivity from that source identity.

The present theorem is deliberately not promoted to positivity: square-summable source incidence
does not imply Hankel positivity, spectral reality, or Weil positivity.

## Gates

- [x] find a canonical normalization that avoids `exp((log p)^2)` column growth
- [x] prove the exact one-prime even-factorial energy identity
- [x] prove the Gamma cancellation bound
- [x] prove all-prime double summability for `x>1/2`
- [x] formalize the result unconditionally in Lean
- [ ] prove critical transport in the new completion
- [ ] identify the transported Gram form with the Xi/Weil form
- [ ] force critical orientation from the source
