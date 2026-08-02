# Deninger--Meyer secondary complex and radial parity correction

- **ID:** `deninger-meyer-secondary-complex-parity-correction`
- **Stage:** 3-formalized
- **Type:** SOURCE-DERIVED COMPLEX, EXACT SPURIOUS-COHOMOLOGY NO-GO, AND POSITIVE REPAIR
- **Label:** `DAC_DENINGER_MEYER_SECONDARY_COMPLEX_PARITY_CORRECTION`
- **Parent:** Route L in `rh-current-frontier-map.md`
- **Claim:** Literal Meyer--Poisson boundary and secondary first-suspension regulator form a
  nontrivial three-term complex on the separated radial sector. Its maximal algebraic Bessel
  middle term is not the arithmetic relevant middle source: the entire vector space of functions
  supported on negative radii injects linearly into its `H¹`. Intersecting with evenness on both
  collars is the source-forced correction; it preserves the literal complex and exact prime-cycle
  law and removes that whole defect sector.

## 1. Source-derived three-term complex

Fix a packet field \(a=(a_p)_p\). Put
\[
 A^0=H_\cap,\qquad
 A^1_{\max}={\cal D}_a,\qquad
 A^2=\bigoplus_p^{\ell^2}
 L^2(B_p\times\mathbb R/\log p\,\mathbb Z),
\]
where \({\cal D}_a\) is the maximal domain on which
\[
 d^1(h)_p
 =p^{-1/2}\bigl(h_+(p)-p^{-1}h_-(p^{-1})\bigr)T_p(a_p)
\]
is square-summable. Define
\[
 d^0f=(Zf,Z\widehat f).
\]
The preceding secondary-regulator theorem proves \(d^0f\in{\cal D}_a\) and
\(d^1d^0f=0\), so
\[
 H_\cap\xrightarrow{d^0}{\cal D}_a\xrightarrow{d^1}A^2
\]
is an actual complex, not merely two unrelated maps.

Exact degree-one cycle law:
\[
 h\in\ker d^1
 \iff
 \forall p,\quad
 h_+(p)=p^{-1}h_-(p^{-1})
 \ \text{or}\ a_p=0.
\]
The explicit Hermite Meyer probe has \(d^0b\ne0\), witnessed by its physical value at prime \(2\).
Thus the first differential is genuinely nonzero.

This is a separated radial complex. It is not identified with Deninger's missing sheafified
relevant coefficient complex.

## 2. Maximal-domain parity no-go

Let
\[
 N_-=\{k:\mathbb R\to\mathbb C:\ k(x)=0\text{ for }x\ge0\}.
\]
For \(k\in N_-\), define \(\iota(k)=(k,0)\). Every prime is positive, so
\[
 \iota(k)_+(p)=0=p^{-1}\iota(k)_-(p^{-1}).
\]
Consequently \(d^1\iota(k)=0\), and \(\iota(k)\in{\cal D}_a\) with zero Bessel family.

Every \(f\in H_\cap\) is even. Termwise,
\[
 Zf(-x)
 =\sum_{n\ge1}f(-nx)
 =\sum_{n\ge1}f(nx)
 =Zf(x).
\]
Hence the physical collar of every boundary \(d^0f\) is even.

Suppose \(\iota(k)=d^0f\). For \(x<0\), \(-x>0\), and therefore
\[
 k(x)=Zf(x)=Zf(-x)=k(-x)=0.
\]
Definition of \(N_-\) gives \(k(x)=0\) for \(x\ge0\), so \(k=0\). Thus
\[
 \iota(N_-)\cap\operatorname{range}d^0=\{0\}.
\]
Induced map
\[
 N_-\longrightarrow H^1(A^\bullet_{\max})
\]
is complex-linear and injective.

This proves a structural no-go:
\[
 \boxed{\ {\cal D}_a\text{ cannot be the literal arithmetic middle source.}\ }
\]
Defect is infinite-dimensional and exists independently of packet nonvanishing, Xi zeros, or RH.
Point mass at \(-1\) supplies an explicit nonzero class, but the injective theorem is the strong
result.

## 3. Strongest positive survivor: parity-corrected domain

Define
\[
 {\cal E}
 =\{(h_+,h_-):h_\pm(-x)=h_\pm(x)\},
\qquad
 {\cal D}^{\mathrm{even}}_a={\cal D}_a\cap{\cal E}.
\]
Both \(f\) and \(\widehat f\) are even for \(f\in H_\cap\), hence both \(Zf\) and
\(Z\widehat f\) are even. Therefore
\[
 d^0(H_\cap)\subseteq{\cal D}^{\mathrm{even}}_a.
\]
Restricting \(d^1\) gives another three-term complex
\[
 H_\cap\xrightarrow{d^0}
 {\cal D}^{\mathrm{even}}_a
 \xrightarrow{d^1}A^2,
\]
with the same exact prime-cycle classification.

Moreover,
\[
 \iota(k)\in{\cal E}\iff k=0
\qquad(k\in N_-).
\]
Thus correction removes the complete negative-radius defect sector, not only one witness.
This is the no-go's strongest positive survivor and a necessary source constraint for every
subsequent topology, sheaf, Hodge, and cup construction.

## 4. Admission--separation audit

Publication manuscript's conservation law separates source admission from separation. Maximal
Bessel domain passes boundary admission but fails source fidelity: it admits arbitrary
negative-radius directions invisible to every positive-prime restriction. Treating its resulting
`H¹` as arithmetic cohomology would be source-provenance theatre.

Parity correction is forced by literal source, not chosen to kill counterexample: Meyer's source
space is even by definition, Fourier transform preserves parity, and Poisson boundary inherits it
on both collars.

## 5. Hostile audit

- **Not a renamed fact that even functions are even.** Classical parity is one input. New result
  is linear injection of entire negative-support function space into `H¹` of newly constructed
  secondary complex and exact corrected-complex survivor.
- **Not one pathological point.** The theorem is \(N_-\hookrightarrow H^1\); point mass only
  witnesses nontriviality.
- **Not target-selected pruning.** Evenness is already part of \(H_\cap\) and is preserved by
  Fourier transform and Meyer summation.
- **Not a proof that corrected `H¹` is arithmetic.** Even algebraic function domain remains larger
  than any established nuclear/sheaf source. Topology, closed range, all-place compatibility,
  cup/Hodge transport, and Xi inclusion remain open.
- **Not an RH implication.** No Xi divisor, zeta zero, positivity premise, or spectral
  identification occurs.

## 6. Novelty audit

Repository search found no prior negative-radius cohomology injection, parity-corrected secondary
complex, or exact defect-sector elimination. Existing modules supplied Meyer even source, Poisson
reflection, first-suspension regulator, and abstract three-term cohomology separately.

Primary-source searches found Meyer's even nuclear spectral quotient, Deninger's rational-Witt
and dynamical programs, Paugam's odd spectral symmetry, and Deninger's later rational-Witt sheaf
work. No located source states this separated three-term complex, injection
\(N_-\hookrightarrow H^1\), or parity-corrected maximal secondary domain. Priority remains
provisional pending specialist review.

## 7. Lean status

Formalized unconditionally in:

- `GaloisForLFunctions/RHTower/DeningerMeyerSecondaryThreeTermComplex.lean`;
- `GaloisForLFunctions/RHTower/DeningerMeyerRadialParityCorrection.lean`.

Capstones:

1. `deningerMeyerSecondaryThreeTermComplex`;
2. `deningerMeyerSecondaryThreeTerm_cycles1_iff`;
3. `deningerMeyerPrimeBoundaryProbe_d0_ne_zero`;
4. `deningerMeyerNegativeRadialH1LM_injective`;
5. `deningerMeyerNegativePointMass_H1_ne_zero`;
6. `deningerMeyerEvenSecondaryThreeTermComplex`;
7. `deningerMeyerEvenSecondaryThreeTerm_cycles1_iff`;
8. `deningerMeyerNegativeRadialPair_mem_even_iff`.

No `sorry`, `admit`, `axiom`, `opaque`, `unsafe`, numerical computation, Xi divisor, zeta zero,
or RH-equivalent hypothesis is used.

## 8. Exact remaining boundary

Parity is necessary but not sufficient. Corrected middle term still consists of arbitrary even
algebraic radial functions satisfying a Bessel condition only at prime samples. Full Route L
requires a source-defined mixed nuclear topology and an actual relevant-coefficient sheaf whose
closed middle boundaries are exactly the kernel of global secondary restriction. Only after that
identification can reciprocal Paugam cup/Hodge form descend honestly and spectral comparison be
attempted.

## References

- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann zeta function*,
  https://arxiv.org/abs/math/0412277.
- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  https://arxiv.org/abs/1807.06400.
- Frédéric Paugam, *Spectral symmetries of zeta functions*,
  https://arxiv.org/abs/0803.0199.
- Christopher Deninger, *Rational Witt vectors and associated sheaves*,
  https://arxiv.org/abs/2508.05329.

## Log

- 2026-08-02 — Literal boundary and maximal secondary restriction assembled into nontrivial
  three-term complex with exact cycle law.
- 2026-08-02 — Entire negative-support radial function space proved to inject linearly into
  uncorrected middle cohomology.
- 2026-08-02 — Source-forced even-collar intersection constructed; literal differential and cycle
  classification preserved; complete negative-radius defect sector eliminated.
