# Affine-gauge first-suspension descent

## Status

Paper proof complete. Formalised unconditionally in Lean.

## Route-L dependency

The rational-Witt source transition is covariant. Its finite packet evaluation is
contravariant for the forced affine maps

\[
\kappa_{s,t}(q)=[a_{s,t}]\,\rho_{s,t}(q).
\]

The already-formalised affine limit

\[
A_p=\varprojlim_{\kappa} Q_s
\]

is a torsor under the literal Deninger packet. What was not yet proved is that
finite rational-Witt packet coefficients define one cofinal first-suspension
class on \(A_p\), rather than unrelated classes after arbitrary stage choices.

The updated source-horizon theorem also rules out the previous proposed next
step. A closed relation retaining the complete ungraded prime-normal reader in
the canonical product topology is

\[
\mathcal R=\operatorname{dom}\mathcal R\times\mathbb C^{\mathbb N}.
\]

It is information-free. The present theorem therefore stops at the canonical
primewise affine packet and records that the following all-prime attachment
must be graded or topology-changing before closure.

## Conjecture audit

### C1 — standard packet pullback is cofinal

False in general. It holds exactly on functions invariant under the forced
primitive-root gauge translation. This is already formalised in
`DeningerRationalWittPacketGaugeDescent`.

### C2 — affine-limit pullback is strictly cofinal

True. For \(F:Q_s\to\mathbb C\), set

\[
\widetilde F_s(a)=F(a_s),\qquad a\in A_p.
\]

If \(s\le t\) and \(F_t=F\circ\kappa_{s,t}\), then

\[
\widetilde F_t(a)
=F(\kappa_{s,t}(a_t))
=F(a_s)
=\widetilde F_s(a).
\]

This is equality of continuous functions, hence equality in transported Haar
\(L^2\), equality of first-suspension modes, and equality after the tensorized
Calderón cross-effect.

### C3 — the descended tensor class can be attached through one ordinary
closed relation on the complete prime-normal product

False. `completeResolution_closedLinearRelation_countablePrime_affine_eq_domain_prod`
proves that every such relation is maximally vertical and imposes no output
constraint.

### C4 — a grade-preserving all-prime attachment can survive

Open. Grade must be retained before closure. Candidate grades are rational-Witt
stage, suspension degree, and prime graph-energy disk. Any viable construction
must prove its closed radical equals the genuine middle boundary without
forgetting these grades.

## Theorem

Fix a prime \(p\).

1. Every coordinate projection \(\pi_s:A_p\to Q_s\) is continuous and
   surjective.
2. Pullback
   \[
   F\longmapsto F\circ\pi_s
   \]
   is injective into continuous functions and into complex Haar \(L^2(A_p)\).
3. Tensoring with the first Fourier character on
   \(\mathbb R/\log(p)\mathbb Z\) gives an isometric injective
   first-suspension map.
4. For \(s\le t\),
   \[
   \widetilde{(F\circ\kappa_{s,t})}_t=\widetilde F_s
   \]
   as continuous functions, Haar \(L^2\) vectors, and first-suspension vectors.
5. The Calderón quotient cross-effect therefore descends strictly across every
   rational-Witt refinement. On the unit defect it is nonzero for every
   nonzero finite packet coefficient.
6. Every finite coefficient has one arithmetic-Frobenius-fixed rational-Witt
   witness whose entire cofinal family maps to this single nonzero descended
   tensor class.

## Proof

Continuity of \(\pi_s\) is inherited from the product topology defining the
inverse limit. For surjectivity, let \(a_0\in A_p\) be the fixed coherent
basepoint and \(q\in Q_s\). The standard packet projection is surjective, so
choose \(x\) whose \(s\)-coordinate is \(a_{0,s}^{-1}q\). The torsor action
gives \(a_0x\in A_p\), and its \(s\)-coordinate is \(q\).

The pullback of a nonzero \(F\) is nonzero by surjectivity. Transported Haar
measure has full support, so the continuous-to-\(L^2\) map is injective.

The first-suspension map is separated product with the norm-one first circle
character. The separated-product norm formula proves isometry and injectivity.

Strict refinement invariance is the defining coherence equation of \(A_p\):
\(\kappa_{s,t}(a_t)=a_s\). All later equalities follow by congruence through
continuous-to-\(L^2\), first suspension, tensoring, and the Calderón regulator.
Nonvanishing follows from the nonzero half-density scalar, injectivity of first
suspension, and nonvanishing of the pulled-back packet.

The rational-Witt witness is supplied by coherent finite cyclotomic descent.
Its evaluation at every larger stage is the forced affine pullback, so the
previous equality identifies all stages with one global tensor class.

## Novelty and theatre audit

Inverse-limit coordinate pullback, Haar \(L^2\), and Fourier suspension are
standard separately. Claimed source-specific contribution is their exact
assembly for independently gauged rational-Witt embeddings:

- the primitive-root gauge is not discarded;
- no externally frozen packet is selected;
- refinement equality is literal, not merely unitary equivalence;
- nonzero output comes from an arithmetic-Frobenius-fixed Wrat witness; and
- the theorem explicitly refuses the now-impossible ungraded relation step.

This advances Route L by closing the finite-to-cofinal tensor descent gate. It
does not prove the RH-bearing Hodge positivity, closed-middle-boundary
classification, or Xi spectral inclusion.

## Next open theorem

Construct a grade-preserving all-prime secondary attachment on the affine
packet first-suspension classes, with a non-product source topology, and prove
that its closed radical is exactly the arithmetic middle boundary. Only then
can Paugam cup/trace and positive Hodge transport be meaningfully attempted.

## Lean certificate

Module:
`GaloisForLFunctions.RHTower.DeningerRationalWittGaugeFirstSuspensionDescent`.

Capstone:
`deningerPrimeComplexifiedRationalWitt_exists_cofinalGaugeTensorClass`.

Direct file checking and the targeted module build pass. The capstone's axiom
audit reports only `propext`, `Classical.choice`, and `Quot.sound`.
