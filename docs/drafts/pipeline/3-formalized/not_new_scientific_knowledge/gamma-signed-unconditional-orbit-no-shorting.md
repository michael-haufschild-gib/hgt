# Gamma signed unconditional-orbit no-shorting

- **ID:** `gamma-signed-unconditional-orbit-no-shorting`
- **Stage:** 3-formalized
- **Type:** CLASS-COMPLETE UNORDERED-SCALAR NO-GO
- **Scientific status:** `[LEAN-PROVED] [NOT RH] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Parent:** `../new_scientific_knowledge/route-r-gamma-signed-summable-orbit-no-shorting.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/GammaSignedUnconditionalOrbitNoShorting.lean`
- **RH used:** no
- **Computation used:** no
- **Statement:** A canonical cross-prime/depth Gamma orbit which has an unordered scalar sum at one
  positive real displacement cannot supply a genuinely beyond-\(\ell^1\) universal cancellation.
  Unordered scalar summation already forces absolute physical-amplitude summability, so the existing
  Bohr coefficient theorem makes every coefficient zero.

## Exact theorem

Let \(E_n\) be pairwise distinct canonical cross-prime/depth edges.  Write

\[
 \lambda_n=\log\!\bigl(p_n^{e_n+1}q_n^{f_n+1}\bigr)>0,
 \qquad A_n>0,
 \qquad \mathcal O_n(z)=A_n\sinh(\lambda_n z).
\]

For complex coefficients \(c_n\), assume:

1. the unordered scalar family \(\sum_n c_n\mathcal O_n(1)\) is summable; and
2. for every real \(y\), the unordered scalar orbit satisfies
   \[
     \sum_n c_n\mathcal O_n(iy)=0.
   \]

Then

\[
 \boxed{\forall n,\ c_n=0.}
\]

The first hypothesis means convergence over the directed net of all finite subsets, not convergence
in one selected enumeration.  It is therefore exactly the divisor/order-independent scalar notion
used by Lean's `Summable` and `HasSum`.

## Proof

Put \(d_n=c_nA_n\).  Every canonical cross-prime/depth product is at least six, hence

\[
 \lambda_n\geq\log 6,
 \qquad
 \sinh(\lambda_n)\geq\sinh(\log 6)=\frac{35}{12}>1.
\]

The scalar space \(\mathbb C\) is finite-dimensional over \(\mathbb R\).  Unconditional summability
therefore implies absolute summability.  Applying this at \(z=1\) gives

\[
 \sum_n |d_n|\sinh(\lambda_n)<\infty.
\]

The uniform lower bound above implies \(\sum_n|d_n|<\infty\).  The existing Bohr--Cesaro
coefficient-extraction theorem now applies to

\[
 \sum_n d_n\sinh(i\lambda_n y)=0.
\]

Distinctness of the edges gives distinct positive frequencies, so every \(d_n=0\).  Since
\(A_n>0\), every \(c_n=0\).  `QED`

## Hostile audit

1. **A conditionally convergent enumeration is not covered.**  It chooses an order and therefore
   is not an unordered, divisor-independent source totalization.
2. **Infinite-dimensional unconditional series need not be norm-absolutely summable.**  This
   theorem scalarizes only at the actual orbit evaluation \(z=1\).  A genuine preclosure-valued
   boundary can escape only if that scalar evaluation is unavailable or discontinuous before
   completion.
3. **Divisor-dependent coefficients are not covered.**  Coupling coefficients to a divisor before
   frequency separation destroys the universal fixed-coefficient orbit hypothesis.  That is the
   surviving RH-bearing class, not a defect in the theorem.
4. **Nonseparability alone does nothing.**  Once the candidate admits the unordered scalar orbit at
   one positive real point, finite-dimensional unconditional convergence forces it back into the
   already-closed \(\ell^1\) class.
5. **No cancellation law is constructed.**  The theorem proves that the requested beyond-\(\ell^1\)
   cancellation cannot live in an ordinary scalar `tsum`.  The positive survivor must remain
   relative/distribution-valued before frequency separation or be divisor-coupled there.

## Consequence for the three-core program

The exact dependency chain is now:

```text
local essential first-trace edge                         [Lean-proved]
  -> strict preclosure Wold--Gamma/BV extension landing [open]
  -> nonscalar/divisor-coupled anomaly annihilation      [open]
  -> atomic non-erasure and covariant descent            [Lean-proved]
  -> source-forced triviality of modular cocycle         [equivalent to RH]
```

The new no-go removes “nonseparable scalar unordered sum beyond \(\ell^1\)” from the second arrow.
It does not remove genuinely distribution-valued preclosure totalization, conditional source-ordered
renormalization with an independently proved order law, or divisor coupling before Bohr separation.

## Literature boundary

The finite-dimensional equivalence of unconditional and absolute convergence is classical; no
novelty is claimed for it.  The Orlicz--Pettis literature concerns vector-valued subseries and weak
convergence.  Burnol's co-Poisson/Sonine work supplies distributional and Hilbert-space source
objects, Meyer's construction supplies a nuclear Frechet spectral quotient, and Connes--Consani
study Weil positivity through trace-formula/Sonin compressions.  None of these sources proves the
specific strict Wold--Gamma/BV extension landing or a source-first annihilation of the horizontal
modular character.

Primary references:

- Jean-Francois Burnol, *Entrelacement de co-Poisson*, arXiv:math/0407443;
- Jean-Francois Burnol, *Two complete and minimal systems associated with the zeros of the Riemann
  zeta function*, arXiv:math/0203120;
- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann zeta function*,
  arXiv:math/0412277;
- Alain Connes and Caterina Consani, *Weil positivity and Trace formula, the archimedean place*,
  arXiv:2006.13771;
- Charles W. McArthur, *On a theorem of Orlicz and Pettis*, Pacific J. Math. 22 (1967), 297--302.

## Gates

- [x] exact source family identified
- [x] dependency-closed paper proof
- [x] hostile no-theatre audit
- [x] primary-literature boundary audited
- [x] unconditional Lean formalization
- [x] umbrella wiring and direct Lean verification
- [x] axiom audit: only `propext`, `Classical.choice`, and `Quot.sound`
- [x] formal lint and targeted final build
- [ ] strict preclosure extension landing
- [ ] nonscalar/divisor-coupled arithmetic annihilation
- [ ] source-forced modular-cocycle triviality
- [ ] RH

## Log

- 2026-08-03 -- Froze and proved the unordered-scalar no-go.  Corrected “beyond-\(\ell^1\)
  nonseparable cancellation” to the surviving nonscalar preclosure/divisor-coupled class.
- 2026-08-03 -- Formalized the actual canonical orbit theorem in Lean and wired it into the
  `RHTower` umbrella.  Direct Lean verification passed; scratch axiom audit reports only standard
  mathlib axioms.
- 2026-08-03 -- `scripts/formal_tools.py lint` and
  `LAKE_JOBS=1 lake build GaloisForLFunctions.RHTower.GammaSignedUnconditionalOrbitNoShorting`
  passed.  Exact imported capstone axiom audit again reports only `propext`, `Classical.choice`,
  and `Quot.sound`.
