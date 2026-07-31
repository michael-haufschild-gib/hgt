# Prime first-trace essential normal Bockstein

- **ID:** `prime-first-trace-essential-normal-bockstein`
- **Stage:** 3-formalized
- **Type:** VECTOR-VALUED ESSENTIAL NORMAL LIMIT / SOURCE-SPECIFIC BOCKSTEIN MODEL
- **Scientific status:** `[LEAN-PROVED] [NOVELTY UNVERIFIED] [NOT RH]`
- **Parents:**
  - `prime-first-trace-exponential-flat-graph-fracture.md`;
  - `../prime-valuation-reflection-type-conservation-law.md`;
  - `../../2-fully-proven/not_new_scientific_knowledge/source-linear-essential-superselection-no-sewing.md`.

## Discovery

The existing theorem retains only the scalar essential rate
\[
 \|X_p\|\bigl(-\log\|Y_p\|\bigr)\longrightarrow1.
\]
It does not identify a vector-valued response boundary.  The raw blow-up \(pY_p\) is not
canonical: its first response coordinate depends on the auxiliary prime
\(p^2<r_p\leq2p^2\).  Removing that already visible first coordinate before blow-up makes the
limit canonical.

Let
\[
\begin{aligned}
 X_p&=\operatorname{primeHardyKernelMap}(w_p),\\
 Y_p&=\operatorname{primeFirstTraceClock}(w_p)-e_1,\\
 \Pi_1^\perp y&=y-y(1)e_1,
\end{aligned}
\]
where \(w_p=\operatorname{primeFirstTraceWitness}(p,r_p)\) and
\(r_p=\operatorname{farPrime}(p)\).  Then
\[
 \boxed{\qquad p\,\Pi_1^\perp Y_p\longrightarrow e_2.\qquad}
\tag{1}
\]

Together with the formalized source limit
\[
 (\log p)X_p\longrightarrow e_1,
\tag{2}
\]
and the zero-prepending Hardy shift \(S\), for which \(Se_1=e_2\), equation `(1)` gives the joint
limit
\[
 \boxed{\qquad
 \bigl((\log p)X_p,\;p\Pi_1^\perp Y_p\bigr)
 \longrightarrow
 (e_1,Se_1).
 \qquad}
\tag{2a}
\]
This is the first literal vector-valued model of the essential associated graph: the logarithmic
source normal \(e_1\) has a reciprocal-prime response normal equal to its next Hardy jet after
the ordinary first response face is removed.

## Exact identity

Put \(P=p\), \(R=r_p\), \(L=\log P\), \(M=\log R\), and let
\[
 {\rm rem}_q=q^{-1}{\rm tail}_q-e_1.
\]
The first-trace witness formula gives
\[
 Y_p
 =
 {\rm rem}_{1/P}
 -
 {PM\over L}{\rm tail}_{1/R}.
\tag{3}
\]
Since \(Y_p(1)=-PM/(RL)\) and
\[
 {\rm tail}_{1/R}-{1\over R}e_1={1\over R}{\rm rem}_{1/R},
\]
one obtains
\[
 \Pi_1^\perp Y_p
 =
 {\rm rem}_{1/P}
 -
 {PM\over RL}{\rm rem}_{1/R}.
\tag{4}
\]
The first remainder has the exact shifted identity
\[
 P\,{\rm rem}_{1/P}-e_2
 =
 S{\rm rem}_{1/P},
\tag{5}
\]
where \(S\) is zero-prepending, hence an isometry.  Therefore
\[
 \left\|P\,{\rm rem}_{1/P}-e_2\right\|
 =
 \|{\rm rem}_{1/P}\|
 \leq {2\over P}.
\tag{6}
\]
The second term in \(P\Pi_1^\perp Y_p\) satisfies
\[
\begin{aligned}
 \left\|
 {P^2M\over RL}{\rm rem}_{1/R}
 \right\|
 &\leq
 {P^2M\over RL}{2\over R}\\
 &\leq {6P^2\over R^2}
 \leq {6\over P^2},
\end{aligned}
\tag{7}
\]
using \(M\leq3L\) and \(R\geq P^2\).  Hence
\[
 \boxed{\quad
 \left\|P\,\Pi_1^\perp Y_p-e_2\right\|
 \leq {2\over P}+{6\over P^2}.
 \quad}
\tag{8}
\]
Equation `(1)` follows along consecutive primes.

## Meaning

This sharpens “essential singularity is required.”

```text
ordinary graph closure:
  forgets all source-response coupling;

finite Rees associated grades:
  kill the response as all-orders flat;

raw reciprocal-prime blow-up:
  retains an auxiliary-prime-dependent first face;

relative blow-up after removing that face:
  converges canonically to the next Hardy jet e₂.
```

Thus the essential object is not arbitrary operator growth.  It is an iterated boundary
operation: remove the already attained face, rescale at the next exponential action, and retain
the next jet.  In this first-trace model, the anisotropically rescaled graph converges literally
to one edge of the Hardy shift \(e_1\mapsto e_2\).  This is the concrete local algebra that a full
Euler--Gamma/co-Poisson source-normal Bockstein must globalize.

## Sharpened RH-facing conjecture

The full source has the squarefree action set
\[
 {\cal A}_{\rm sf}=\{\log n:\mu(n)\ne0,\ n\ge2\}.
\]
The theorem above realizes one local associated-graded edge.  The required infinity is therefore
not an undifferentiated infinite-rank space.  The Toeplitz ladder itself is parent structure
already isolated elsewhere in the corpus; declaring another infinite shift completion would not
move the frontier.  New content must identify this concrete essential edge with the
Euler--Gamma/BV boundary of the source determinant extension and then carry that same class,
before divisor specialization, to the relative Contou--Carrère/Meyer extension and the literal
co-Poisson/Sonin boundary.

`[BOLD CONJECTURE] [XI_ESSENTIAL_EDGE_SOURCE_EXTENSION_LANDING]`

> The ordinary-prime Euler--Gamma/co-Poisson producer admits a strict preclosure totalization
> \({\cal T}_{\rm sf}\) such that:
>
> 1. every squarefree action has a relative normal edge of the form `(2a)`;
> 2. diagonal action condensation of these edges is the reciprocal-Xi germ and
>    \(-u\Xi'(u)/\Xi(u)\);
> 3. the differentiated source determinant-extension comparison sends `(2a)` to the
>    BV/renormalized first-trace residue class, while its group-level comparison sends prime
>    dilation and the distinguished determinant section to \(p^{s-1/2}\) and \(\Xi(s)\);
> 4. this comparison extends in the restricted all-action topology before localization, not as a
>    product of zero-indexed symbols;
> 5. its boundary functor is the literal pair of Gamma/co-Poisson/Sonin contractions, with source
>    reversal and Hilbert adjunction acting on the same preclosure class; and
> 6. the boundary image of their difference lies nondivisively in the co-Poisson ideal, while
>    principal-conormal localization remains conservative.

Clause 6 is exactly the source producer missing from the already-proved Burnol mate-curvature
identity.  At a Xi zero the ideal vanishes, so the radial curvature
\[
 \left(|r^{\rho-1/2}|^2-|r^{\rho-1/2}|^{-2}\right)\|y_{\rho,j}\|^2
\]
must vanish; nonzero quotient evaluation then gives \(\Re\rho=\tfrac12\).

This conjecture is narrower than “find an essential singular completion.”  Arbitrary essential
completions are nonselective, and every closed source-linear boundary relation splits off line.
The only live site is the source-extension comparison on the action-indexed preclosure
totalization together with its literal Gamma/co-Poisson boundary landing.

## Corpus collision and corrected open core

The Wold--Toeplitz carrier, determinant central extensions, the local
Contou--Carrère/tame symbol, and the infinitesimal Meyer Green cocycle are parent mathematics
already present in the corpus.  In particular, the local identity
\[
 {1\over2\pi i}\int_{\gamma_\rho}
 (s-\tfrac12)\log p\,d\log\Xi(s)
 =
 m_\rho(\rho-\tfrac12)\log p
\]
already computes the divisor character.  Repackaging it as an index or an essential shift would
be theatre.

The new theorem `(2a)` supplies something those parent identifications did not: an actual
source-defined vector-valued essential edge on the prime first-trace graph.  The corrected open
core is the compatibility square
\[
\begin{array}{ccc}
 (e_1\longmapsto Se_1)_{\rm first\ trace}
 &\longrightarrow&
 \operatorname{Lie}\widehat{\mathcal G}_{\rm Wold/Gamma/BV}^{\rm src}\\[2mm]
 \big\downarrow{\rm action\ condensation}
 &&
 \big\downarrow d\Phi_{\rm CC}\\[2mm]
 -u\,\Xi'(u)/\Xi(u)
 &\longrightarrow&
 \operatorname{Res}\!\left((s-\tfrac12)\log p\,d\log\Xi\right),
\end{array}
\tag{9}
\]
together with the further boundary map from the lower-right class to the literal
Gamma/co-Poisson/Sonin mate-curvature class.  The horizontal and vertical arrows in `(9)` must be
constructed from the ordinary-prime source before a zero is selected.  The right vertical arrow
is the differentiated form of the still-open restricted extension comparison
\[
 \widehat{\mathcal G}_{\rm Wold/Gamma/BV}^{\rm src}
 \longrightarrow
 \widehat{\mathcal G}_{\rm CC}^{\rm rel}.
\tag{10}
\]

This makes the essential-singularity statement categorical rather than merely quantitative.
Finite-Rees morphisms preserve the all-orders-flat radical; arbitrary essential operators are
nonselective; closed source-linear essential operators cannot cross disjoint reflected sectors.
The remaining possible carrier is therefore the secondary class measuring failure of source
completion, reporter completion, and reflection to commute.  In the language of the corpus it is
the source completion-curvature/Bockstein class; `(2a)` is its first computed local chart.

## Hostile audit

1. **Not RH.**  No Xi zero or Sonin boundary occurs in `(1)`.
2. **Not a sewing operator.**  The two scale factors \(\log p\) and \(p\) differ; `(1)` is a
   relative associated-graded graph, not a closed operator on the ordinary Hilbert completion.
3. **First-coordinate subtraction is source-fixed.**  It is the fixed projection
   \(\Pi_1^\perp\), independent of a zero and of the choice of \(r_p\).
4. **Auxiliary-prime dependence is genuinely removed.**  The remaining \(r_p\)-term is
   \(O(P^{-2})\); no limit for \(r_p/P^2\) is assumed.
5. **Finite-dimensionality is irrelevant.**  The result identifies one nonzero essential
   normal class.  It does not contradict invariance of the all-orders-flat radical under
   finite-Rees operator families.
6. **No automatic Gamma/co-Poisson landing.**  The load-bearing next theorem is that the full
   all-action Euler source carries these iterated essential jets to the literal Sonin boundary,
   with reflection and adjunction acting on the same preclosure class.

## Novelty boundary

Zero-prepending shifts, geometric Hardy tails, and vector-valued boundary-layer rescaling are
parent mathematics.  Targeted exact web and corpus searches found no statement of `(1)` or `(8)`
for the actual-prime first-trace graph.  Any novelty claim is restricted to this source-specific
essential normal class and remains provisional pending broader specialist audit.

## Lean certificate

- Module:
  `formal/GaloisForLFunctions/RHTower/PrimeFirstTraceEssentialNormalBoundary.lean`
- Exact identities:
  - `prime_smul_remainder_sub_basisTwo_eq_prependZero`
  - `primeFirstTraceEssentialResponse_eq`
- Uniform bound:
  - `norm_primeFirstTraceEssentialResponse_blowup_sub_basisTwo_le`
- Vector-valued essential boundary:
  - `tendsto_primeFirstTraceEssentialResponse_blowup_basisTwo`
- Joint essential graph:
  - `hardyPrependZero_basisOne_eq_basisTwo`
  - `tendsto_primeFirstTrace_anisotropicEssentialGraph`
- Verification:
  - `lake env lean GaloisForLFunctions/RHTower/PrimeFirstTraceEssentialNormalBoundary.lean`
  - `lake build GaloisForLFunctions.RHTower.PrimeFirstTraceEssentialNormalBoundary`
  - `#print axioms`: only `propext`, `Classical.choice`, and `Quot.sound`
- Formal lint:
  new module is reachable from `GaloisForLFunctions.RHTower`; lint still exits nonzero on
  unrelated pre-existing unreachable modules.

## Gates

- [x] exact vector identity
- [x] explicit norm bound
- [x] auxiliary-prime independence
- [x] first hostile audit
- [x] Lean formalization
- [ ] broader literature audit
- [ ] attach full prime-log action spectrum
- [ ] identify Gamma/co-Poisson/Sonin boundary image
- [ ] RH
