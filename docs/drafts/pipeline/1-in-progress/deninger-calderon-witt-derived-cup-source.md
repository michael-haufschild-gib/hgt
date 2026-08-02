# Calderón--Witt derived cup source

- **ID:** `deninger-calderon-witt-derived-cup-source`
- **Stage:** 1-in-progress
- **Type:** SOURCE-OBJECT CONSTRUCTION
- **Label:** `DAC_CALDERON_WRAT_DERIVED_CUP_SOURCE`
- **Parent:** Route L in `rh-current-frontier-map.md`
- **Statement:** the source-varying Calderón/rational-Witt cross-effect is
  the degree-one multiplication of a two-step arithmetic coefficient
  object before completion or cohomology; it is not a linear differential
  on the square-zero direct sum.

## Exact missing object

Fix a rational prime \(p\).  Let
\[
 Q_p=\mathbb C^2/\Gamma_p
\]
be the Meyer--Poisson Calderón defect line,
\[
 P_p=L^2(B_p^{\mathrm{aff}})
\]
the actual affine-gauge rational-Witt packet, and
\[
 S_p=L^2(B_p^{\mathrm{aff}}\times
           \mathbb R/\log p\,\mathbb Z)
\]
the first-suspension packet.  The already-proved source cross-effect is
\[
 \chi_p:Q_p\otimes P_p\longrightarrow S_p,\qquad
 \chi_p(q\otimes a)
 =
 \bar\delta_p(q)\,p^{-1/2}T_p(a).                 \tag{1}
\]

The missing local coefficient has degree-one term
\[
 A_p^1=Q_p\oplus P_p
\]
and degree-two term \(A_p^2=S_p\).  Its degree-one product is forced by
graded commutativity:
\[
 (q,a)\smile(q',a')
 =
 \chi_p(q\otimes a')-\chi_p(q'\otimes a).          \tag{2}
\]
Products involving two \(Q_p\)-inputs or two \(P_p\)-inputs vanish.
Equation `(2)` is alternating, skew, bilinear, and source-defined.

## Construction theorem

`[CONJECTURE] [DAC_CALDERON_WRAT_DERIVED_CUP_SOURCE]`

The following statements hold.

1. **Local two-step coefficient.**  Formula `(2)` defines a
   dependency-closed two-step graded coefficient.  Its vector-valued
   radical is zero:
   \[
   \bigl(\forall y\in A_p^1,\ x\smile y=0\bigr)
   \Longrightarrow x=0.                                  \tag{3}
   \]
   Thus neither Calderón defect nor packet direction is erased before
   scalar trace.
2. **Finite rational-Witt source.**  Every finite affine packet stage is
   a graded subobject.  Gauge-corrected refinement maps preserve `(2)`
   literally, not only up to isomorphism.
3. **All-prime algebraic source.**  The finite-support direct sums
   \[
   A_{\mathrm{arith}}^1=\bigoplus_p A_p^1,\qquad
   A_{\mathrm{arith}}^2=\bigoplus_p A_p^2
   \]
   carry the componentwise cup.  It is again alternating and has zero
   vector-valued radical.  This object is formed before any Hilbert,
   product-topology, or nuclear closure.
4. **Arithmetic descent.**  Cup commutes with rational-Witt gauge
   refinement, Frobenius, residue/corestriction, and the two-column
   arithmetic differential.  Its trace transgression agrees with the
   Meyer \(Z/\mathcal F\) correction on the separated Poisson sector.
5. **Positive completion interface.**  Reciprocal doubling and the
   real orientation twist turn `(2)` into the chain-level alternating
   form whose Hodge rotation is the full packet norm.  Completion is
   taken only after the source cup and boundary subspace are fixed.

## Why this is the frontier

The square-zero amplitude retains \(Q_p\oplus P_p\) only as an additive
group.  The proved no-go shows that no linear map on that direct sum can
recover `(1)`.  Downstream Bessel estimates, Green pullbacks, and Hodge
purity theorems therefore cannot manufacture the missing arithmetic map.

Formula `(2)` puts the nonzero cross-effect into source multiplication.
It is the minimal two-step derived attachment exposed by
\(I/\mathfrak mI\cong\Lambda^2V\): the discarded quadratic distinction
returns in degree two.  This is a source object, not a chosen target
restriction.

## Falsifiers

- If `(2)` has nonzero vector-valued radical, it does not retain source
  distinctions and cannot supply Route L cup data.
- If gauge refinement changes `(2)`, finite rational-Witt witnesses do
  not define one cofinal source object.
- If all-prime assembly is performed in the canonical ungraded product
  topology before cup formation, the complete source-horizon theorem
  makes the relation maximally vertical.
- A positive norm applied to \(\chi_p\) after externally fixing the
  packet does not construct this object.
- No zeta zero, divisor-indexed sector, RH premise, or Paugam
  RH-conditional positivity may define `(1)` or `(2)`.

## Proof program

1. Construct the local two-step coefficient and prove `(3)`.
2. Prove exact finite-stage and affine-gauge refinement naturality.
3. Construct finite-support all-prime cup and prove its radical theorem.
4. Insert the cup into the arithmetic three-term/two-column source
   complex and prove the Leibniz and residue identities.
5. Construct reciprocal real-oriented Hodge rotation and identify its
   diagonal with full packet energy.
6. Only then pass to the strict nuclear source topology and compare with
   Paugam/Meyer.

## Current status

- Local cross-effect `(1)`: paper- and Lean-proved.
- Affine gauge limit and refinement invariance on pure tensors:
  paper- and Lean-proved.
- Local/all-prime two-step cup object: open.
- Differential, residue, Green, and Paugam compatibility: open.

## Gates

- [x] isolate source object rather than downstream consumer
- [ ] local two-step coefficient and zero radical
- [ ] cofinal finite-stage descent
- [ ] all-prime algebraic source
- [ ] arithmetic differential/cup compatibility
- [ ] positive reciprocal Hodge interface
- [ ] strict nuclear closure and Meyer comparison
- [ ] RH

