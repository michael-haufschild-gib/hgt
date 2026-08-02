# Deninger--Meyer pointwise-Xi comparison sharpness

- **ID:** `deninger-meyer-pointwise-xi-comparison-sharpness`
- **Stage:** 3-formalized
- **Type:** POSITIVE SURVIVOR / SOURCE-FIDELITY CLASSIFICATION / SHARP REGULARITY BOUNDARY
- **Label:** `DAC_DENINGER_MEYER_POINTWISE_XI_COMPARISON_SHARPNESS`
- **Parent:** Route L in `rh-current-frontier-map.md`
- **Claim:** Pointwise Xi nonerasure is compatible with one fixed uniformly first-order regular
  complete-source-to-Meyer comparison.  Such a comparison can nevertheless be rank one,
  label-blind, and reflection-erasing.  For the constructed comparison every normalized actual
  Xi trace is nonzero, but those values converge to zero cofinally.

## 1. Fixed source avoiding every actual Xi point

Choose one nonnegative smooth compactly supported function \(b\) with
\[
 \int_{\mathbb R} b(t)\,dt=1.
\]
Its bilateral Laplace/Mellin transform
\[
 F(s)=\int_{\mathbb R}e^{st}b(t)\,dt
\]
is entire and \(F(0)=1\), so its zero set
\[
 Z=\{s\in\mathbb C:F(s)=0\}
\]
is closed discrete and hence countable.

For \(a\in\mathbb C\), set
\[
 b_a(t)=e^{at}b(t).
\]
Compact support puts every \(b_a\) in the literal all-weight Meyer source, and
\[
 {\cal M}b_a(s)=F(s+a).
\]
Actual Xi divisor support is countable.  Therefore the bad modulation set
\[
 B=\bigcup_{\rho\in\operatorname{supp}\operatorname{div}\Xi}
      \{a:\rho+a\in Z\}
\]
is countable.  Since \(\mathbb C\) is uncountable, choose \(a\notin B\).  The single fixed
source
\[
 g=b_a
\]
then satisfies
\[
 \boxed{\quad {\cal M}g(\rho)\ne0
   \quad\text{for every actual Xi divisor point }\rho.\quad}
 \tag{1}
\]

This is simultaneous countable avoidance, not one interpolant selected separately for each
divisor point.

## 2. Fixed rank-one comparison

Let
\[
 D:\ell^1(\mathbb N,\mathbb C)\longrightarrow\mathbb C,
 \qquad
 D(x)=\sum_jx_j
\]
be the norm-one source codiagonal, and define one fixed complex-linear comparison
\[
 T(x)=D(x)g.
 \tag{2}
\]
Every actual complete-resolution source has codiagonal one:
\[
 D(E_K(\rho))=1.
\]
Equations (1)--(2) therefore give
\[
 {\cal M}(T E_K(\rho))(\rho)
 =
 {\cal M}g(\rho)\ne0
\]
for every exponent \(K\) and every actual Xi divisor point \(\rho\).

The comparison is uniformly first-order regular.  Exact Sobolev homogeneity gives
\[
 C_{1,\sigma}(T x)
 =
 |D(x)|\,C_{1,\sigma}(g).
\]
The norm-one codiagonal bound and the standard closed-strip Meyer majorant imply
\[
 C_{1,\sigma}(T x)
 \le
 \left(
   \int_{\mathbb R}e^{|t|}
     (|g(t)|+|g'(t)|)\,dt
 \right)\|x\|_{\ell^1},
 \qquad 0\le\sigma\le1.
 \tag{3}
\]

## 3. Exact failure of source fidelity

The same comparison destroys the arithmetic geometry needed by Route L:

1. for all labels \(i,j\),
   \[
   T(e_i)=g=T(e_j);
   \]
2. every canonical source reflection displacement lies in \(\ker D\), hence
   \[
   T(E_K(s)-E_K(1-\bar s))=0;
   \]
3. \(T\) has rank one and sees only total source mass.

Thus pointwise nonerasure at every actual Xi fibre does not imply label retention, reflection
fidelity, injectivity, or arithmetic provenance.

On unit-normalized actual source vectors, every escaping-stage trace remains nonzero:
\[
 {\cal M}\!\left(
   T\frac{E_K(\rho_n)}{\|E_K(\rho_n)\|_1}
 \right)(\rho_n)\ne0.
\]
But equation (3) places \(T\) inside the already-proved uniform regularity class, so
\[
 \boxed{\quad
 {\cal M}\!\left(
   T\frac{E_K(\rho_n)}{\|E_K(\rho_n)\|_1}
 \right)(\rho_n)\longrightarrow0.
 \quad}
 \tag{4}
\]
This proves sharpness of the cofinal attenuation theorem: it cannot be strengthened to eventual
or pointwise vanishing.

## 4. New scientific consequence

“Retains every Xi fibre pointwise” is not a sufficient last-mile comparison condition.  It is
already met by a source-geometry-erasing regular rank-one map.  Route L must require at least:

1. pointwise Xi nonerasure;
2. transverse source-label retention;
3. nonannihilation of off-critical reflection displacement, or the exact Hodge-equivariant
   replacement of that condition;
4. arithmetic construction from the relevant coefficient complex;
5. cup/trace/flow compatibility.

Only after those source-fidelity requirements are imposed does the earlier singularity theorem
become an RH-relevant obstruction: uniform first-order regularity then still rules out a uniform
Xi-trace floor, but ordinary pointwise nonzero values are no evidence of successful comparison.

This moves the frontier by replacing an underspecified “pointwise nonerasing comparison” gate
with a falsifiable source-fidelity package.

## 5. Hostile audit

- **Not divisor-selected interpolation.** One modulation \(a\) and one source \(g\) work for all
  actual Xi points simultaneously.
- **Not a hidden use of RH.** Only countability and discreteness of actual Xi divisor support are
  used; no location, simplicity, or symmetry classification of zeros is assumed.
- **Not a claimed arithmetic comparison.** Equation (2) is deliberately label-blind.  Its purpose
  is to prove that pointwise nonerasure alone cannot certify arithmetic provenance.
- **Not a contradiction with vertical decay.** Nonzero values may converge to zero.  Equation
  (4) proves that this is exactly what happens along the canonical escaping sequence.
- **Not positivity or Hodge theory.** No polarization, relevant complex, or spectral real-part
  theorem is constructed.
- **No numerical computation.** The avoiding modulation is obtained by uncountability, not by
  locating zeros or evaluating a transform.

## 6. Novelty audit

The ingredients “zeros of a nonzero entire function are discrete” and “a countable union of
countable sets is countable” are classical and are not claimed as new.  Meyer's vertical
Schwartz decay and existing zeta-zero interpolation results remain prior art.

The restricted novelty claim is the exact two-source sharpness classification:

- one fixed compact literal-Meyer source is simultaneously nonzero on actual Xi support;
- codiagonal composition yields a uniformly regular pointwise-Xi-nonerasing comparison on the
  predeclared complete source;
- the same comparison is proved label-blind and reflection-erasing;
- normalized traces are pointwise nonzero yet cofinally tend to zero.

No located primary source or repository theorem states this package for the canonical complete
high-exponent source and literal Meyer source.  Specialist priority review remains necessary.

## 7. Lean status

Formalized unconditionally in:

- `GaloisForLFunctions/RHTower/DeningerMeyerPointwiseXiComparisonSharpness.lean`.

Capstones:

1. `exists_deningerMeyerXiModulatedSource_nonzero_on_support`;
2. `deningerMeyerPointwiseXiComparison_nonzero_on_support`;
3. `deningerMeyerPointwiseXiComparison_firstOrderRegular`;
4. `deningerMeyerPointwiseXiComparison_unitLabels_eq`;
5. `deningerMeyerPointwiseXiComparison_erases_reflection`;
6. `deningerMeyerPointwiseXiComparison_normalizedEscape_nonzero`;
7. `deningerMeyerPointwiseXiComparison_normalizedEscape_tendsto_zero`.

Direct `lake env lean` and targeted module build pass.  Axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`.  No `sorry`, `admit`, project `axiom`,
`opaque`, `unsafe`, RH premise, numerical computation, or target-selected family is used.

## 8. Exact survivor

The unresolved comparison must be built from the arithmetic relevant complex and retain
transverse source geometry.  Merely requiring one nonzero scalar Mellin value at every Xi fibre
does not constrain the comparison enough to touch the Hodge/RH gate.

## References

- Ralf Meyer, *On a representation of the idele class group related to primes and zeros of
  \(L\)-functions*, arXiv:math/0412277.
- Frédéric Paugam, *Spectral symmetries of zeta functions*, arXiv:0803.0199.
- Andriy Bondarenko, Danylo Radchenko, Kristian Seip, *Fourier interpolation with zeros of zeta
  and \(L\)-functions*, arXiv:2005.02996.
