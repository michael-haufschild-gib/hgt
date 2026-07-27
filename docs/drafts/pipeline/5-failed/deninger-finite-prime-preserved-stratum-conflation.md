# Finite-prime preserved-stratum conflation

- **ID:** `deninger-finite-prime-preserved-stratum-conflation`
- **Stage:** 5-failed
- **Type:** STRUCTURAL NO-GO WITH POSITIVE SURVIVOR
- **Label:** `DAC_FINITE_PRIME_PRESERVED_STRATUM_CONFLATION_NO_GO`
- **Parent:** `deninger-archimedean-conormal-dual-conormal-trace-domain`
- **Failed route:** Treat finite-prime pro-log residue packets as the
  preserved-leaf support \(M^0\) of a conormal/dual-conormal dynamical
  trace complex.

## The no-go

`[PAPER-PROVED] [DAC_FINITE_PRIME_PRESERVED_STRATUM_CONFLATION_NO_GO]`

Finite-prime packets cannot be identified with preserved/fixed
components in Deninger's dynamical Lefschetz dictionary.

### Source proof

1. Deninger's arithmetic dictionary assigns a finite prime \(p\) to a
   periodic orbit of primitive period \(\log p\).
2. His 2018 rational-Witt dynamical system assigns every closed point a
   compact packet of such periodic orbits and states that the flow has
   no fixed points.
3. His conjectural arithmetic compactification assigns infinite primes,
   not finite primes, to stationary points. For a real infinite prime the
   transverse exponent is \(-2\); for a complex infinite prime it is
   \(-1\).

These assignments are mutually exclusive.

### Trace-support proof

For one finite prime, the positive-time orbit distribution has the form
\[
 T_p=(\log p)\sum_{m\ge1}\delta_{m\log p}.                      \tag{1}
\]
It is supported on the discrete set
\(\{m\log p:m\ge1\}\).

For a preserved leaf \(L\) with nonzero Euler coefficient and transverse
exponent \(\kappa\ne0\), the Álvarez
López--Kordyukov--Leichtnam supported/dual-supported character restricts
on \(\mathbb R^\times\) to
\[
 W_L(t)=\frac{\chi(L)}{|e^{\kappa t}-1|}.                      \tag{2}
\]
Choose a nonempty interval \(U\Subset(0,\infty)\) disjoint from
\(\{m\log p:m\ge1\}\), and choose
\(0\le f\in C_c^\infty(U)\), \(f\ne0\). Then
\[
 \langle T_p,f\rangle=0,\qquad
 \langle W_L,f\rangle\ne0.                                    \tag{3}
\]
If \(\chi(L)=0\), `(2)` vanishes and still cannot equal the nonzero
distribution `(1)`. Hence no preserved-leaf contribution equals a
finite-prime orbit contribution.

## Root cause

Two different localizations were conflated:

1. **Arithmetic sheaf localization:** generic coefficient to finite
   prime residue strata.
2. **Dynamical trace localization:** finite-prime periodic orbits versus
   archimedean stationary components.

The residue comparison must connect these structures without identifying
their geometric supports.

## Positive survivor

`[PAPER-PROVED]` The source construction must satisfy a
**two-localization separation principle**:

- finite-prime pro-log collars construct arithmetic residues and local
  Hodge compatibility;
- the same primes appear dynamically as periodic-orbit packets in the
  open flow;
- conormal/dual-conormal support is reserved for an archimedean
  compactification;
- comparison is established by the global Lefschetz character, not by
  declaring residue strata to be fixed leaves.

This survivor is the scope law used by
`DAC_ARCHIMEDEAN_CONORMAL_DUAL_CONORMAL_TRACE_DOMAIN`.

## Lean status

Not yet formalized. The elementary trace-support separation is
dependency-closed, but no Lean build is justified until it is batched
with the arithmetic trace-support layer.

## References

- Christopher Deninger, *A note on arithmetic topology and dynamical
  systems*, arXiv:math/0204274.
- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  arXiv:1807.06400.
- Jesús A. Álvarez López, Yuri A. Kordyukov, and Eric Leichtnam,
  *A trace formula for foliated flows*, arXiv:2402.06671.

## Log

- 2026-07-27 — Retired finite-prime preserved-leaf interpretation after
  primary-source and trace-support audits; extracted two-localization
  separation principle.
