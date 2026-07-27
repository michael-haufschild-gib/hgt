# Multiple elliptic gamma strict face-depth rigidity

- **ID:** MEG-STRICT-FACE-DEPTH-RIGIDITY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** Positive survivor of `MEG-FACE-DEPTH-RIGIDITY`
- **Statement:** Along every proper deletion chain whose deeper face retains at least two periods, external-lattice translates of the two genuine face coordinates are unequal.

## Goal

Give an unconditional, all-orders rigidity law for the actual logarithmic-derivative face hierarchy.
The law excludes every collision that respects the deletion partial order; it is stronger than
same-face injectivity and does not assume the still-open all-face Stanley--Reisner gluing theorem.

## Exact theorem

Let \(I\) be finite, \(\tau_i\in\mathbb H\), and assume

\[
 m+\sum_{i\in I}n_i\tau_i=0,\quad m,n_i\in\mathbb Z
 \Longrightarrow m=0,\ n_i=0\ (i\in I).
\]

For deletion faces \(J\subsetneq L\subseteq I\), assume \(L\) leaves at least two parameters.  If
\(\lambda\in\sum_{j\in J}\mathbb Z\tau_j\) and
\(\mu\in\sum_{\ell\in L}\mathbb Z\tau_\ell\), then

\[
 \Psi_J(z+\lambda)\ne\Psi_L(z+\mu)
\]

as global meromorphic functions, where \(\Psi_J\) is the actual logarithmic derivative of the
multiple elliptic gamma function on face \(J\).

## Proof certificate

- **Lean theorem:** `multipleEllipticGammaFace_translate_ne_of_ssubset`
- **Module:** `GaloisForLFunctions.HTGeometry.FaceDepthRigidity`
- **Development check:** `lake env lean GaloisForLFunctions/HTGeometry/FaceDepthRigidity.lean`
- **Axioms:** pending final isolated `#print axioms` audit
- **Final module build:** pending publication audit

## Proof architecture `[PROVED HERE]`

1. Encode simultaneous finite differences as an alternating Boolean cube
   `faceDifferenceCube`.
2. Prove cube recursion and the intrinsic descent identity from
   `multipleEllipticGammaLogDerivFaceMero_addTranslation_sub`.
3. Extend the deeper face to any bottom face with two survivors.
4. The shallower translate descends to one bottom-packet coordinate.  The deeper translate descends
   to a nontrivial alternating cube inside the same bottom packet.
5. Integral period independence makes subset-sum labels injective.
6. Bottom-packet differential independence implies ordinary linear independence, so one coordinate
   cannot equal the nontrivial cube.

No computation, choice of special numerical periods, unproved analytic lemma, or external
differential-algebraicity theorem enters the Lean proof.

## Gates

- [x] 0 → 1 in-progress: exact source-pure statement and attack
- [x] 1 → 2 fully-proven: dependency-closed paper proof
- [x] 2 → 3 formalized: theorem accepted by `lake env lean`
- [ ] 3 → 4 publication-ready: final module build, lint, axioms, manuscript integration

## Antagonist audit

- **Could Boolean-cube terms cancel internally?** No.  Integral period independence injects all
  subset sums.
- **Could the target translate be one cube term?** At most one.  A nonempty cube has at least two
  distinct terms; the proof selects an uncancelled term.
- **Could differential independence be used circularly?** No.  Bottom-packet independence is proved
  upstream from the two-period divisor obstruction and does not use face-depth rigidity.
- **Could the deeper face have too few survivors?** Excluded explicitly and reflected in the Lean
  hypothesis `2 ≤ (Lᶜ).card`.
- **Does the theorem separate incomparable faces?** No claim is made.  Publication wording must say
  "proper deletion chain" or "comparable faces", never "all distinct faces".

## Log

- 2026-07-27 — extracted as strongest Lean-closed survivor while full cross-depth separation remains
  at Stage 2.
- 2026-07-27 — formalized in `FaceDepthRigidity.lean`; foreground `lake env lean` check passed.
