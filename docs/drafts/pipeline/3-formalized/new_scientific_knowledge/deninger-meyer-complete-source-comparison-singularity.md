# Deninger--Meyer complete-source comparison singularity

- **ID:** `deninger-meyer-complete-source-comparison-singularity`
- **Stage:** 3-formalized
- **Type:** SOURCE-TO-SOURCE COMPARISON / COFINAL TRACE ATTENUATION / REGULARITY NO-GO
- **Label:** `DAC_DENINGER_MEYER_COMPLETE_SOURCE_COMPARISON_SINGULARITY`
- **Parent:** Route L in `rh-current-frontier-map.md`
- **Claim:** One fixed complex-linear comparison from the actual complete-resolution
  \(\ell^1\) source into literal all-weight Meyer source space cannot be both uniformly bounded
  for the canonical first vertical Sobolev cost and uniformly faithful on the Xi trace. On
  unit-normalized actual source vectors its Mellin trace tends to zero along an actual cofinal
  sequence of Xi divisor points.

## 1. Two predeclared source spaces

For every \(s\) in the open right half-plane, complete high-exponent resolution supplies the
actual vector
\[
 E_K(s)=\bigl(M_{K,j}(s)\bigr)_{j\ge0}\in\ell^1(\mathbb N,\mathbb C),
 \qquad
 \sum_jM_{K,j}(s)=1.
\]
It is nonzero before any consumer is chosen. Define its unit source normalization
\[
 \widehat E_K(s)=\frac{E_K(s)}{\|E_K(s)\|_{\ell^1}}.
\]

Literal Meyer source consists of smooth logarithmic profiles \(g\) having all exponential
moments in every derivative. For
\[
 {\cal M}g(s)=\int_{\mathbb R}e^{st}g(t)\,dt,
\]
its natural first vertical cost is
\[
 C_{1,\sigma}(g)
 =
 \int_{\mathbb R}
   \left|\frac d{dt}\bigl(e^{\sigma t}g(t)\bigr)\right|\,dt.
\]

No comparison between these spaces is declared by the construction.

## 2. Regular comparison class

Let one fixed complex-linear map
\[
 T:\ell^1(\mathbb N,\mathbb C)\longrightarrow{\cal S}_{\rm Meyer}
\]
be given. Call it uniformly first-order regular on the critical strip when there is
\(C\ge0\) such that
\[
 C_{1,\sigma}(Tx)\le C\|x\|_{\ell^1}
 \qquad
 (0\le\sigma\le1,\ x\in\ell^1).
 \tag{1}
\]

This is not an assumed arithmetic comparison theorem. It isolates the strongest ordinary
source-norm continuity class that a proposed comparison might satisfy.

Choose actual Xi divisor points \(\rho_n\) with
\[
 |\Im\rho_n|>n+1.
\]
Since \(0<\Re\rho_n<1\), equation (1) applies to
\(T\widehat E_K(\rho_n)\). Fourier integration by parts gives
\[
 |\Im\rho_n|\,
 \left|
 {\cal M}\bigl(T\widehat E_K(\rho_n)\bigr)(\rho_n)
 \right|
 \le
 C_{1,\Re\rho_n}\bigl(T\widehat E_K(\rho_n)\bigr)
 \le C.
\]
Therefore
\[
 \boxed{\quad
 {\cal M}\bigl(T\widehat E_K(\rho_n)\bigr)(\rho_n)
 \longrightarrow0.
 \quad}
 \tag{2}
\]

In particular there is no \(\varepsilon>0\) for which
\[
 \varepsilon\le
 \left|
 {\cal M}\bigl(T\widehat E_K(\rho_n)\bigr)(\rho_n)
 \right|
 \qquad\text{for every }n.
 \tag{3}
\]

Thus a source comparison that retains a uniform amount of actual Xi trace must fail (1). Its
singularity is forced relative to canonical norms on both predeclared source spaces.

## 3. Scientific consequence for Route L

Finite Xi interpolation cannot create the missing arithmetic comparison. Even after literal
Meyer finite packet surjectivity is closed, a single source-defined comparison is constrained by
equation (2):

- a uniformly regular comparison cofinally attenuates normalized Xi trace;
- a uniformly Xi-trace-faithful comparison is necessarily source-singular;
- raw product packet surjectivity is unavailable and cannot be used to normalize the trace;
- ordinary bounded source descent is therefore too small for a uniformly faithful last mile.

Combined with complete-source label-blind rigidity, the admissible comparison class is now
sharply typed: it must retain transverse source labels, and uniform Xi faithfulness additionally
forces singularity in the literal Meyer vertical topology.

This does not construct the relevant arithmetic complex, positive Hodge metric, or a singular
comparison. It removes the regular uniformly faithful comparison class from the open core.

## 4. Hostile audit

- **Not a target-selected interpolant.** \(T\) is fixed on the entire complete source space;
  it does not depend on \(\rho_n\).
- **Not a divisor-indexed source.** Inputs are the canonical complete-resolution vectors already
  defined for every point of the open half-plane.
- **Not normalization theatre.** Normalization occurs only in the predeclared \(\ell^1\) source
  norm. It tests uniform source faithfulness rather than forcing target values.
- **Not Meyer's vertical Schwartz theorem renamed.** Meyer supplies vertical decay for one fixed
  source. Here the source varies with \(\rho_n\) through one fixed source-comparison map; uniform
  operator control converts that varying family into cofinal trace attenuation.
- **Not a proof of pointwise erasure.** Equation (2) permits every finite-stage value to remain
  nonzero while tending to zero. Pointwise nonerasure, which is enough for the source-character
  RH reduction once norm-conservative equivariance exists, is not excluded.
- **Not positive Hodge.** No norm-conservative Meyer quotient flow is constructed.
- **Not RH progress by renaming a hypothesis.** Remaining source comparison and Hodge gates are
  stated explicitly.

## 5. Novelty audit

Primary-source audit located:

- Meyer's nuclear Fréchet spectral realization and Fourier--Laplace image, including vertical
  Schwartz decay and divisor multiplicities;
- Bondarenko--Radchenko--Seip's Fourier interpolation bases indexed by zeta zeros and jets;
- Paugam's symplectic pairing on the Connes--Meyer spectral realization.

No located primary source states equation (2) for the canonical complete high-exponent
\(\ell^1\) Riemann source under one fixed uniformly Meyer-regular comparison, or the resulting
regularity-versus-uniform-Xi-faithfulness dichotomy. Repository search found no prior theorem.

Priority claim is restricted to this exact two-source comparison law. Specialist priority review
remains necessary.

## 6. Lean status

Formalized unconditionally in:

- `GaloisForLFunctions/RHTower/Deninger/DeningerMeyerCompleteSourceComparisonSingularity.lean`.

Capstones:

1. `norm_completeResolutionXiEscapeUnitSource`;
2. `deningerMeyerCompleteSourceXiEscapeTrace_tendsto_zero`;
3. `no_uniformlyXiTraceFaithful_firstOrderRegular_completeSourceComparison`.

No `sorry`, `admit`, project `axiom`, `opaque`, `unsafe`, numerical computation, RH, zero
simplicity, positive-Hodge premise, inverse Mellin theorem, or constructed arithmetic comparison
is used.

## 7. Exact survivor

Route L's source comparison can still exist with pointwise nonzero but cofinally vanishing Xi
trace. To close the RH-bearing gate it must be constructed from the arithmetic relevant complex
and must satisfy:

1. transverse source-label retention;
2. pointwise nonerasure on every Xi divisor fibre;
3. flow/cup/trace compatibility;
4. positive norm-conservative Hodge descent on the comparison image;
5. either canonical source singularity or a topology weaker than uniform first-order Meyer
   regularity, while still supporting closed middle-boundary descent.

The hard survivor is narrower, not solved.

## References

- Ralf Meyer, *On a representation of the idele class group related to primes and zeros of
  \(L\)-functions*, arXiv:math/0412277.
- Frédéric Paugam, *Spectral symmetries of zeta functions*, arXiv:0803.0199.
- Andriy Bondarenko, Danylo Radchenko, Kristian Seip, *Fourier interpolation with zeros of zeta
  and \(L\)-functions*, arXiv:2005.02996.
