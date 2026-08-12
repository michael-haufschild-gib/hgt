# Positive-cone midpoint recovery and amplified properness programme

- **ID:** ULF-RFTM-3
- **Stage:** 1-in-progress
- **Type:** CONJECTURE / THEOREM PROGRAMME
- **Source:** ULF-RFTM-1 and ULF-RFTM-2
- **Statement:** Global midpoint--relative reconstruction is Lean-proved in ULF-RFTM-3A; the live
  open claim is that bounded amplified packets force the formation coordinate to be neutral.

## Goal

Replace routewise scalar obstructions by one global formation mechanism. A direct/reflected packet
must retain two independent coordinates:

1. its positive midpoint, which is the formation state;
2. its oriented displacement from that midpoint, which is the internal law state.

The target theorem must prove joint reconstruction and a global properness/selection law before any
arithmetic landing is considered.

## Exact conjecture

Let \(\mathcal P_n\) be the cone of real symmetric or complex Hermitian positive-definite
\(n\times n\) matrices. For \(R,Q\in\mathcal P_n\), define

\[
  \Phi(R,Q)=(X,Y):=(RQR,RQ^{-1}R).
  \tag{PMR.1}
\]

Write \(X\#Y\) for the metric geometric mean: the unique positive solution \(S\) of

\[
  SX^{-1}S=Y.
  \tag{PMR.2}
\]

Theorem package, with current status:

1. **Midpoint recovery** `[LEAN-PROVED: ULF-RFTM-3A]`
   \[
     X\#Y=R^2.
     \tag{PMR.3}
   \]
2. **Global inverse chart**. `[SET-THEORETIC PART LEAN-PROVED: ULF-RFTM-3A; ANALYTICITY OPEN]`
   Given arbitrary \(X,Y\in\mathcal P_n\), put
   \[
     S=X\#Y,\qquad R=S^{1/2},\qquad Q=R^{-1}XR^{-1}.
     \tag{PMR.4}
   \]
   Then \(Y=RQ^{-1}R\). Hence \(\Phi:\mathcal P_n^2\to\mathcal P_n^2\) is a
   real-analytic diffeomorphism.
3. **Reflection law** `[LEAN-PROVED: ULF-RFTM-3A]`. Swapping \((X,Y)\) fixes \(R\) and sends
   \(Q\mapsto Q^{-1}\).
4. **Metric conservation**. For the affine-invariant distance
   \[
     \delta(A,B)=\|\log(A^{-1/2}BA^{-1/2})\|_{\mathrm{HS}},
   \]
   \[
     \delta(X,Y)=2\|\log Q\|_{\mathrm{HS}},\qquad
     \delta(X,R^2)=\delta(R^2,Y)=\|\log Q\|_{\mathrm{HS}}.
     \tag{PMR.5}
   \]
5. **Amplified properness/selection**. Set
   \[
     X_k=R^kQR^k,\qquad Y_k=R^kQ^{-1}R^k \quad(k\ge0).
     \tag{PMR.6}
   \]
   Then
   \[
     X_k\#Y_k=R^{2k},\qquad
     \delta(I,X_k\#Y_k)=2k\|\log R\|_{\mathrm{HS}}.
     \tag{PMR.7}
   \]
   Consequently the midpoint orbit is bounded iff \(R=I\). Equivalently, there exist
   \(0<m\le M<\infty\) with
   \[
     mI\preceq X_k,Y_k\preceq MI\quad\text{for every }k
     \tag{PMR.8}
   \]
   iff \(R=I\).

## Why this is a higher pivot

The two packet legs are not redundant estimators and their sum is not the fundamental object.
They are endpoints of a reversible formation chart. Formation lives in the midpoint; internal law
lives in oriented relative displacement. ULF-RFTM-2's double-commutator term is then the local
failure of scalar radial coordinates to retain this global two-coordinate chart. Tracial no-gos are
quotient shadows of discarding the relative tangent.

This mechanism simultaneously explains:

- why reciprocal direct/reflected formation is information-neutral before observation;
- why scalar trace/determinant observers can be blind while the full packet is faithful;
- why bounded amplified formation can select a neutral coordinate without a route-specific
  vanishing theorem;
- why infinite/cofinal completion is a separate gate: finite positive-cone properness does not
  automatically survive weak or non-Hausdorff completion.

## Proof plan

1. Verify algebraically that \(S=R^2\) satisfies \(SX^{-1}S=Y\); uniqueness of the positive
   Riccati solution proves (PMR.3).
2. Use (PMR.2) to verify the inverse formulas (PMR.4); positivity is preserved by congruence.
3. Use congruence invariance of the affine-invariant metric and functional calculus for commuting
   \(Q,Q^{-1}\) to prove (PMR.5).
4. Apply (PMR.3) to \(R^k\), then spectral calculus to obtain (PMR.7).
5. For (PMR.8), positive geometric-mean monotonicity puts \(R^{2k}\) in the same spectral annulus.
   Every eigenvalue \(\lambda>0\) with \(m\le\lambda^{2k}\le M\) for all \(k\) equals one.

## Hostile gates and falsifiers

- [x] Prove the positive Riccati solution is unique; do not insert midpoint as extra marked data.
- [ ] Prove the inverse chart is analytic; its global set-theoretic inverse is Lean-proved.
- [ ] Prove exact distance identities with the stated metric convention.
- [ ] Check one-sided \(k\ge0\) spectral annulus really excludes eigenvalues both below and above
  one.
- [x] Formalize the complete reconstruction/reflection subtheorem in Lean.
- [ ] Do not infer an RH conclusion without a pre-zero constitutive map identifying physical
  displacement with \(R\) and proving packet boundedness.

Sharp limitations:

1. An unordered packet loses the coorientation \(Q\leftrightarrow Q^{-1}\).
2. A single distance retains only \(\|\log Q\|\), not the full relative law.
3. Determinant sum/difference retain only \(\det R\) and \(\det Q\).
4. Indefinite/Krein cones need not have a unique positive midpoint.
5. Infinite-dimensional bounded sets need not be compact; cofinal properness requires its own
   source-controlled topology or ideal.

## External parent audit

Matrix geometric means as unique positive Riccati solutions, affine-invariant geodesic midpoints,
and symmetric-cone quadratic representations are established mathematics. The proposed field
content is their use as one source-formation chart together with reciprocal packet generation,
history erasure, and amplified selection. No external priority claim is made.

## Gates

- [x] 0 → 1: well-posed, exact source-independent mechanism, proof plan, hostile falsifiers
- [ ] 1 → 2: dependency-closed paper proof of all promoted clauses
- [ ] 2 → 3: Lean theorem package, foreground build, axiom/lint audit, umbrella import
- [ ] 3 → 4: standalone synthesis with source comparison and cofinal extension

## Log

- 2026-08-12 — created after noncommutative fusion/history theorem exposed midpoint-relative split.
- 2026-08-12 — corpus search found no existing ULF positive-cone midpoint formation chart.
- 2026-08-12 — external audit identified geometric-mean/Riccati and symmetric-cone parent theories;
  theorem is pursued as formation-mechanics synthesis, not framework novelty.
- 2026-08-12 — promoted exact reconstruction/reflection subtheorem to ULF-RFTM-3A and formalized it
  in `ConstitutivePositiveConeMidpointRecovery` and `ConstitutivePositiveFormationReflection`.
  Remaining open core is amplified metric/properness, not packet recoverability.
