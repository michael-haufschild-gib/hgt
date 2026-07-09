# Sonin place-transition cutoff dichotomy

- **ID:** sonin-place-transition-cutoff-dichotomy
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) + THEOREM (Lean, structural core)
- **Grade:** BRIDGE (substrate, shortcut-closing); not C5
- **Source:** Connes--Consani--Moscovici, *Zeta zeros and prolate wave operators*,
  arXiv:2310.18423v2, Theorem 4.6 and Proposition 4.8;
  `../../1-in-progress/sonin-cutoff-transversality-realization.md`;
  `../../3-formalized/new/cutoff-cross-boundary-seam-nonmember.md`
- **Statement:** The semilocal Sonin construction supplies no determinant-transverse prime cutoff defect
  in either of its two immediate readings: natural place transitions intertwine transported cutoffs and
  have zero cross-boundary, while the raw support-cutoff corner of the explicit prime factor is noncompact
  and therefore does not define the finite polynomial Fitting class used by the current torsion-seam model.
  This closes those shortcuts but leaves the paper's actual formal semilocal prolate operator as the
  source-defined successor.

## Theorem

Fix `lambda > 0`. For a finite set of places `S` containing infinity, write

`H_S := S_lambda(X_S, alpha)`

for the semilocal Sonin space. Let `B_lambda` be the common Hilbertian entire-function carrier in
Proposition 4.8.

### A. The canonical place transition is cutoff-flat

`[PROVED HERE, using the cited Sonin isomorphisms]` Let

`v_S : H_S -> B_lambda`

be the isomorphism induced by the dual Hardy--Titchmarsh transform, and for `S subset T` define the
canonical transition

`J_{T,S} := v_T^{-1} v_S : H_S -> H_T`.

For every idempotent `q` on `B_lambda`, transport it to

`q_S := v_S^{-1} q v_S`, `q_T := v_T^{-1} q v_T`.

Then

`J_{T,S} q_S = q_T J_{T,S}`

and hence

`(1 - q_T) J_{T,S} q_S = 0`.

The four abstract linear-algebra declarations are formalized in
`formal/GaloisForLFunctions/RHTower/CutoffCochain.lean`:

- `transitionBoundary_eq_zero_of_intertwines`;
- `operatorNaturalityDefect`;
- `transitionBoundary_operatorNaturalityDefect`;
- `canonicalTransition_intertwines_transportedCutoff`;
- `transportedCutoff_idempotent`;
- `canonicalTransition_boundary_eq_zero`.

### B. The explicit prime factor has a noncompact raw corner

`[PROVED HERE]` In the one-prime case, the paper computes the place-addition map on
`H = L^2(R_+^*, d^*u)` as

`T_p = 1 - p^(-1/2) D_p`, where `(D_p f)(u) = f(u/p)`.

Its Mellin multiplier is `1 - p^(-1/2-is)`, so `T_p` is bounded and boundedly invertible because

`|1 - p^(-1/2-is)| >= 1 - p^(-1/2) > 0`.

Let `P_lambda` be multiplication by the indicator of `(0, lambda]`. Then

`(1-P_lambda) T_p P_lambda = -p^(-1/2) (1-P_lambda) D_p P_lambda`.

The last operator restricts to a unitary map

`L^2((lambda/p, lambda], d^*u) -> L^2((lambda, p lambda], d^*u)`.

Both shell spaces are infinite-dimensional. Therefore this corner has singular value `p^(-1/2)` with
infinite multiplicity; it is not compact, Hilbert--Schmidt, or trace class. In particular it is not a
finite-rank polynomial matrix entry and has no adjugate trace in the existing
`MPlusTorsionSeam`/`FittingSeamBoundary` interface.

This assertion is orientation-specific: it uses the inside support projection `P_lambda` and
`D_p f(u)=f(u/p)`. Complementing the projection or reversing the dilation moves the shell crossing to
the opposite corner or can make the displayed corner vanish. Moreover, `P_lambda` is an ambient
`L^2` diagnostic and need not preserve the full physical-and-Fourier Sonin intersection. Thus B rules
out this raw shortcut; it does not assert a two-sided noncompactness theorem for every Sonin cutoff.

### C. The source vector was mis-typed, but a formal prolate operator exists

`[PROVED BY SOURCE CHECK]` The paper's `sigma_p = epsilon_0 - p^(-1) epsilon_1` is a self-Fourier
**vector** spanning the radial local Sonin space, not a prime endomorphism `U_p` of a fixed semilocal
Sonin carrier. Tensoring by the vectors `sigma_p` constructs the place-change isomorphism. The paper
does not construct the `U_p` or finite torsion presentation `A_lambda` assumed by the old candidate card.

It does, however, define in Section 4.3 the first **formal** semilocal prolate candidate

`W_{lambda,S} = (H + 1/2)^2 + lambda^2 N_S`,

where `N_S` is the grading of the cyclic pair `(S, xi_S)`. What is deferred is the computation of the
general-`S` Jacobi coefficients and, in Section 5, a second metaplectic candidate. The source therefore
supplies a prime-sensitive operator shape, but not the analytic or determinant-line structure required
by the present seam category.

### D. The surviving source defect is prolate non-naturality

`[SOURCE-LEVEL FORMAL IDENTITY]` Let `eta_S` be the full-space amplification used to build the cyclic
pair. It commutes with the scaling term, while Remark 4.2(i) states

`N_S eta_S != eta_S N_infinity` unless `S = {infinity}`.

On the common cyclic core this gives

`Omega_{S,lambda}
   := W_{lambda,S} eta_S - eta_S W_{lambda,infinity}
    = lambda^2 (N_S eta_S - eta_S N_infinity)`.

Thus `Omega_{S,lambda}` is nonzero for `lambda != 0` and nontrivial `S`. This is an immediate
consequence of the source, hence SEARCH/BRIDGE rather than new knowledge. It is also an exact
naturality coboundary `delta W`, not curvature. A potentially native class can occur only if taking the
Sonin cutoff corner and a determinant boundary fails to erase or split this exact defect.

For a cutoff-compatible nested-place transition `J_{T,S}`, define

`Omega_{T,S} := W_{lambda,T} J_{T,S} - J_{T,S} W_{lambda,S}`.

The newly formalized structural theorem gives

`(1-q_T) Omega_{T,S} q_S
   = crossBoundary(q_T,W_{lambda,T}) J_{T,S}
     - J_{T,S} crossBoundary(q_S,W_{lambda,S})`.

After conjugation to a common carrier this is `(1-q)(W_hat_T-W_hat_S)q=b_T-b_S`. It telescopes along
place inclusions. Therefore an arbitrary vertexwise gauge kills it; a nonfake class requires a pinned
presentation and a proof that the relevant `b_S` are not admissible gauge changes.

## Proof of A

Theorem 4.6 identifies every `H_S` with the archimedean Sonin space. Proposition 4.8 identifies every
`H_S` with the same `B_lambda`, and its commutative diagram gives `v_S theta_S = v_infinity`. Thus
place enlargement, conjugated to `B_lambda`, is the identity. Directly,

`J_{T,S} q_S = v_T^{-1} v_S v_S^{-1} q v_S = v_T^{-1} q v_S`

and

`q_T J_{T,S} = v_T^{-1} q v_T v_T^{-1} v_S = v_T^{-1} q v_S`.

Idempotence of `q_T` then gives

`(1-q_T)J_{T,S}q_S = (1-q_T)q_TJ_{T,S} = 0`.

## Attack and boundary cases

- `[PROVED]` At `lambda = 0`, the support cutoff is zero and both corners vanish trivially.
- `[PROVED]` For every finite prime `p` and `lambda > 0`, the raw support corner is noncompact. Its norm
  tends to zero as `p -> infinity`, but compactness does not improve at any finite `p`.
- `[PROVED]` Finite-dimensional compression can manufacture a polynomial lower-left entry, but the entry
  depends on the chosen channels. It is a finite probe, not the source-built Sonin transition.
- `[PROVED IN COMPANION CARD]` The bounded positive Euler norm-change operator also fails: its corner
  across the actual archimedean Sonin projection is noncompact for every prime and `lambda>0`; see
  `sonin-euler-metric-corner-noncompact.md`. This closes the metric fallback, not the formal prolate
  naturality defect.
- `[PROVED FROM SOURCE]` At `lambda = 0` or `S = {infinity}`, `Omega_{S,lambda}=0`. For one added prime
  and `lambda != 0`, its nonvanishing is already contained in Remark 4.2(i), so nonvanishing alone is
  not a new result.
- `[OPEN CORE]` Close `W_{lambda,S}` analytically, construct domain-compatible idempotents onto the Sonin
  sectors, and decide whether
  `(1-Q_{lambda,S}) Omega_{S,lambda} Q_{lambda,infinity}` lies in a Schatten ideal. If it does, construct
  a presentation-invariant determinant boundary and compute its two-place cross-effect.
- `[OPEN CORE]` If the raw corner is not Schatten, test the relative resolvent
  `R_T(z)J-JR_S(z)=-R_T(z)Omega_{T,S}R_S(z)` as the canonical smoothing and determine whether it is
  trace class.

The fake proof of determinant transversality fails four times. It treats the source vector `sigma_p` as
an endomorphism `U_p`; replaces an infinite-dimensional noncompact shell operator by one scalar entry of
a `2 x 2` polynomial matrix; infers a nonzero Sonin corner from the nonzero operator
`Omega_{S,lambda}`; and infers a nonzero determinant boundary from a corner without constructing a
presentation-invariant reduction. The abstract sheared witness proves that the target category permits a
nonfake corner; it does not prove that the Sonin source lands in that category.

## Novelty and significance gates

- **NOVEL:** The abstract intertwiner lemma and the shell noncompactness are standard separately. Their
  combination with the repository's Fitting-seam acceptance test is not a literature restatement: it
  decides the two shortcut readings of the outstanding Sonin realization card. The formula for
  `Omega_{S,lambda}` itself is source extraction and is not counted as novel.
- **SIGNIFICANT:** The outstanding Sonin realization no longer asks for an invented `U_p`. It targets the
  source's formal `W_{lambda,S}` and the exact place-naturality defect of its cyclic grading. This removes
  the false `2 x 2` shortcut and localizes the missing analytic and categorical structure exactly.

## Next move

Promote the source data to a **trace-ideal Sonin seam datum** with all four properties:

1. the formal `W_{lambda,S}` has a controlled closed realization on a place-compatible domain;
2. the Sonin idempotents are domain-compatible and the corner of `Omega_{S,lambda}` is compact of a
   stated Schatten class;
3. its determinant-line boundary is invariant under changing the finite-mode presentation and under
   the derived admissible gauge group, which must not contain arbitrary vertexwise subtraction;
4. after canonical transport, its two-place cross-effect is computed and is either nonzero or proved to
   split into one-prime terms.

Only after these are proved is the low-coefficient/Fitting transversality question well-typed.

`[CONJECTURE]` The two-place cross-effect of the resulting determinant boundary is nonzero. If every
boundary decomposes into the sum of its singleton-prime terms, the construction remains BRIDGE and this
native-seam route is retired.

## Gates

- [x] 0 -> 1: the two canonical source readings and the finite-presentation gap are explicit.
- [x] 1 -> 2: natural-transition vanishing and raw-corner noncompactness are proved.
- [ ] 2 -> 3: the structural naturality theorem is formalized; the analytic `L^2` noncompactness proof
      remains paper-only.
- [ ] 3 -> 4: requires the trace-ideal prolate defect or a publication-level route-closure note.
