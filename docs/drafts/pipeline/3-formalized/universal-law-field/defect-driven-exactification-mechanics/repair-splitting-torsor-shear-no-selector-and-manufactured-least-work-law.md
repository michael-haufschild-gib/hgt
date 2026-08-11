# Repair splitting torsor, shear no-selector, and manufactured least-work law

- **ID:** ULF-DDE-1
- **Stage:** 3-formalized
- **Type:** ROUTE-INDEPENDENT SELECTOR NO-GO WITH POSITIVE CLASSIFICATION
- **Statement:** Exact repair data determine an affine torsor of repairs, not a preferred repair;
  shear symmetries act transitively, and every repair can be made uniquely least-work by a suitable
  positive quadratic cost.
- **Status:** [LEAN-PROVED] [DEPENDENCY-CLOSED] [BRIDGE] [SELECTOR NO-GO]
  [POSITIVE TORSOR CLASSIFICATION] [UMBRELLA-WIRED] [NOT RH]

## 1. Failed conjecture

`[FALSIFIED]` **Intrinsic least-work exactification.** Given an exact defect and the set of its
primitives, choose the primitive of least norm. This was proposed as the missing constitutive law
linking obstruction, promotion cost, and singular admission.

The claim is ill-founded until the cost geometry is produced independently. Exactness alone has a
large symmetry group, and every candidate can be declared least-work after changing that geometry.

## 2. Exact algebraic repair law

Let `F` be a field, let `K,W` be `F`-vector spaces, put `V=K direct-sum W`, and let

\[
 q:V\longrightarrow W,\qquad q(k,w)=w.
 \tag{1}
\]

A **repair selector** is a linear splitting `s:W->V` with `q s=id_W`. For every linear
`h:W->K` define

\[
 s_h(w)=(h(w),w).
 \tag{2}
\]

For every linear `a:W->K` define the vertical shear

\[
 S_a(k,w)=(k+a(w),w).
 \tag{3}
\]

### Theorem 2.1 -- splitting torsor and transitive shear action

1. Every repair selector is `s_h` for a unique `h in Hom_F(W,K)`.
2. Every `S_a` is an automorphism of `V`, with inverse `S_(-a)`, and `q S_a=q`.
3. The shear action is
   \[
   S_a s_h=s_{h+a}.
   \tag{4}
   \]
   Hence the shears act simply transitively on repair selectors.
4. If `Hom_F(W,K)` is nonzero, no repair selector is invariant under every automorphism of the
   exact repair problem `(V,q)`.

### Proof

If `s` splits `q`, its second coordinate is `w`; its first coordinate defines a unique linear map
`h`, proving `s=s_h`. Formulas `(3)` give `S_(-a)S_a=id=S_aS_(-a)` and `qS_a=q`. Direct
substitution gives `(4)`. For any `h,h'`, the unique shear sending `s_h` to `s_(h')` is
`S_(h'-h)`, proving simple transitivity. If `a` is nonzero, `(4)` shows no `s_h` is fixed by
`S_a`. QED.

Thus exactification supplies an affine torsor. It does not supply its origin.

## 3. Every repair can be made least-work

Assume now that `K,W` are finite-dimensional real inner-product spaces. For an arbitrary repair
parameter `h:W->K`, define

\[
 \langle(k,w),(k',w')\rangle_h
 =\langle k-hw,k'-hw'\rangle_K+\langle w,w'\rangle_W.
 \tag{5}
\]

This is an inner product because `(k,w) mapsto (k-hw,w)` is a linear isomorphism. Its squared
cost is

\[
 E_h(k,w)=\lVert k-hw\rVert_K^2+\lVert w\rVert_W^2.
 \tag{6}
\]

### Theorem 3.1 -- manufactured least-work selector

For every target `w`, `s_h(w)` is the unique minimum-cost element of the fibre `q^(-1)(w)`. More
precisely, every lift has the unique form `(h(w)+z,w)` and

\[
 E_h(h(w)+z,w)=E_h(s_h(w))+\lVert z\rVert_K^2.
 \tag{7}
\]

### Proof

Substitute `(h(w)+z,w)` in `(6)`. The first term becomes `||z||^2`, while
`E_h(s_h(w))=||w||^2`. Nonnegativity proves minimality; equality holds exactly when `z=0`.
QED.

No special property of `h` was used. Every algebraic repair can therefore be presented as the
canonical least-work repair for a suitably manufactured positive geometry.

## 4. Strongest positive survivor

The invariant content is not a minimizer but the following mechanism boundary:

1. **Exactness produces a repair torsor.** Differences of repairs lie in `Hom(W,K)`.
2. **Vertical symmetries erase origins.** A selector can be intrinsic only after some source datum
   reduces the shear group.
3. **A metric is selection data.** Least-work becomes predictive only when the metric or cost is
   derived before the selected repair and is independently testable under interventions.
4. **Rank/admission walls remain meaningful only after that derivation.** Moore--Penrose blow-up is
   a real singularity of a fixed Hilbert realization, but cannot justify that realization.

This converts the failed optimizer proposal into a precise acceptance gate: a universal repair law
must produce a shear-breaking datum, not merely optimize a cost supplied after the fact.

## 5. Corpus and literature boundary

- `[CORPUS]` `matrix_rightInverse_iff_kernelPerturbation` in
  `HTGeometry.AlgebraicIndependentLinearForms` already formalizes the affine right-inverse law for
  matrices. The current theorem extracts its selector consequence and adds the manufactured-cost
  no-go.
- `[LOCAL-RESEARCH]` reporter-constrained promotion already proves that a conserved reporter can
  forbid a quotient. It does not choose among remaining repairs.
- `[LITERATURE]` Moore--Penrose inversion is analytic only on suitable fixed-rank/closed-range
  strata; Chiumiento--Massey study precisely this stratified geometry:
  <https://arxiv.org/abs/2312.02693>.
- Affine spaces of splittings and orthogonal least-norm lifts are classical linear algebra. No
  novelty claim is made for the isolated theorem.

## 6. Sharp scope

1. If `Hom(W,K)=0`, the splitting torsor is a point and the no-selector conclusion is vacuous.
2. A source-fixed inner product, involution, order, integral lattice, or reporter may break the
   shear symmetry. The theorem demands its provenance; it does not forbid it.
3. Infinite-dimensional Hilbert spaces require boundedness and closed-range hypotheses for the
   Moore--Penrose formulation. The algebraic torsor theorem itself does not.
4. The result does not select a replacement mechanism, prove an RH implication, or identify all
   legal source structures.

## 7. No-go closure

- **Exact killing mechanism:** transitive vertical shear symmetry plus cost manufacture `(5)`.
- **Strongest positive survivor:** repair choices form an affine torsor, and lawful selection is
  exactly a source-derived symmetry reduction problem.
- **New insight:** optimization cannot be primitive; source-revealed response must determine whether
  a scalar work law exists before minimization is meaningful.
- **Status:** paper proof and exact Lean formalization closed; isolated theorem remains a classical
  bridge, while source-revealed repair genesis is open.

## 8. Lean certificate

Module `GaloisForLFunctions.HTGeometry.ConstitutiveRepairTorsorSelectorNoGo` certifies:

- classification of every splitting by a unique vertical map;
- target-preserving shear automorphisms and simple transitivity;
- absence of fixed repair sections under every nonzero shear;
- exact squared-norm decomposition around an arbitrary selector;
- minimality and uniqueness in every target fibre;
- closed capstone quantifying over every selector, target, and competing lift.

Direct elaboration and the 11,415-job
`GaloisForLFunctions.HTGeometry.UniversalLawField` build pass. Axiom audit reports only
`propext`, `Classical.choice`, and `Quot.sound`. Forbidden-token scan is clean.

## Log

- 2026-08-09 -- intrinsic least-work conjecture killed; torsor classification and manufactured-cost
  survivor proved on paper.
- 2026-08-09 -- exact theorem formalized, axiom-audited, and wired into universal-law umbrella.
- 2026-08-11 -- Lean surface audited complete against the card; promoted to stage 3.
