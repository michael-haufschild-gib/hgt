# Poset Hilbert innovation and incomparability Gram localization

- **ID:** poset-hilbert-incomparability-gram-localization
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Novelty:** `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** Hilbert-space metric research prompted by the 2026-07-19 universal-law goal
- **Statement:** Canonical predecessor residualization preserves the full Gram volume of every finite Hilbert frame while forcing every comparable pair to be orthogonal, so the normalized residual determinant localizes exactly all remaining coherence onto the incomparability graph and is invariant under the full incidence-gauge group.

## Goal

Let \(P\) be a finite poset, let \(H\) be a real or complex Hilbert space, and let
\(x=(x_p)_{p\in P}\) be linearly independent.  Put
\[
  V_p(x)=\operatorname{span}\{x_q:q<p\},\qquad
  r_p(x)=x_p-\operatorname{proj}_{V_p(x)}x_p,
\]
and write \(\nu_p(x)=\lVert r_p(x)\rVert\),
\(u_p(x)=r_p(x)/\nu_p(x)\).

Prove the following exact universal law.

1. **Ideal-span conservation.** For every order ideal \(I\subseteq P\),
   \[
     \operatorname{span}\{r_p(x):p\in I\}
       =\operatorname{span}\{x_p:p\in I\}.
   \]
2. **Comparability annihilation.** If \(q<p\), then
   \(\langle r_q(x),r_p(x)\rangle=0\).
3. **Gram-volume conservation and incomparability localization.** If
   \(G(x)=(\langle x_p,x_q\rangle)\) and
   \(C_P(x)=(\langle u_p(x),u_q(x)\rangle)\), then
   \[
     \det G(x)
       =\det G(r(x))
       =\left(\prod_{p\in P}\nu_p(x)^2\right)\det C_P(x).
   \]
   The diagonal of \(C_P(x)\) is one and every comparable off-diagonal entry is
   zero.  Hence all nontrivial determinant interaction is supported on the
   incomparability graph.
4. **Sharp metric phase law.** The scalar
   \[
     \kappa_P(x)=\det C_P(x)
       =\frac{\det G(x)}{\prod_p\nu_p(x)^2}
   \]
   satisfies \(0<\kappa_P(x)\le 1\).  Equality \(\kappa_P(x)=1\) holds exactly
   when the incomparable residual pairs are also orthogonal.
5. **Incidence-gauge invariance.** If
   \[
     y_p=a_p x_p+v_p,\qquad a_p\ne0,\quad v_p\in V_p(x),
   \]
   then \(V_p(y)=V_p(x)\),
   \(r_p(y)=a_p r_p(x)\), and \(\kappa_P(y)=\kappa_P(x)\).
   Conversely, equality of the predecessor spaces together with
   \(r_p(y)=a_p r_p(x)\) reconstructs exactly such an invertible incidence-gauge
   transformation.

The theorem is about Hilbert metric geometry.  Its relationship to the wider
research is motivational only: finite noncommuting word packets carry a natural
subword poset, so the law would separate predecessor-explained directions from
genuine incomparable metric coherence without making an HTGeometry or RHTower
claim.

## Gates

- [x] 0 → 1  in-progress: exact finite-poset statement, unconditional Hilbert hypotheses, attack and falsifiers recorded
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: exact Lean master theorem, targeted `lake env lean`, final module `lake build` green
- [ ] 3 → 4  publication-ready: independent specialist priority audit and standalone exposition

## Parent theory and novelty boundary

### Established parents

- Ordinary Gram–Schmidt orthogonalization and the Gram-determinant product law for a
  total order are classical.
- Invertible upper-triangular matrices are the stabilizer of a complete flag.
- Incidence algebras and incidence groups of finite posets are classical.
- Bolognini–Sentinelli, *P-flag spaces and incidence stratifications*
  (arXiv:1907.09047), identify \(GL(n)/I^*(P)\) as a \(P\)-flag homogeneous space.
- Hadamard's determinant inequality and its equality case are classical.

### Candidate-new content

The novelty claim is restricted to the fused Hilbert-metric theorem: canonical
projection against the complete strict predecessor span simultaneously preserves
every ideal span and the full Gram determinant, annihilates exactly the comparable
support, and produces an incidence-gauge-invariant normalized determinant whose
entire nontrivial support is the incomparability graph.  No located source states an
equivalent predecessor-residual determinant localization or the sharp invariant and
equality classifier.

This is not yet a priority claim.  Promotion requires a second specialist search over
poset orthogonalization, sparse Cholesky/graphical models, incidence-group invariant
theory, covariance residualization, and generalized flag metrics.

## Approach

1. Use finite-dimensionality of each predecessor span to define its actual
   orthogonal projection in an arbitrary Hilbert space.
2. Prove ideal-span conservation by well-founded induction on the finite poset.
3. Comparability annihilation follows because \(r_p\perp V_p(x)\) and
   \(r_q\in\operatorname{span}\{x_t:t\le q\}\subseteq V_p(x)\) for \(q<p\).
4. In a linear extension of \(P\), the change \(x\mapsto r(x)\) is unit
   triangular; its determinant is one, so the two Gram determinants agree.
5. Normalize the residual columns and apply multiplicativity of determinants.
   Positive definiteness gives \(\kappa_P>0\); Hadamard gives
   \(\kappa_P\le1\) and its equality classifier.
6. For an incidence gauge, induct over \(P\) to identify predecessor spans.  Linearity
   of orthogonal projection then gives \(r_p(y)=a_p r_p(x)\); diagonal phase
   conjugation of \(C_P\) proves determinant invariance.
7. Formalize the construction and the exact master law in a new general Hilbert
   module, reusing the existing Gram determinant infrastructure but no source-specific
   theorem.

## Hostile checks and falsifiers

- **Dependence:** linear independence is essential for normalization and strict
  positivity.  The unnormalized span, orthogonality, and determinant identities should
  be stated separately so that no division-by-zero is hidden.
- **Non-ideal subsets:** ideal-span conservation is false for arbitrary subsets; the
  down-set hypothesis is sharp.
- **Immediate predecessors only:** projecting only onto covers generally fails because
  their vectors need not span all strict predecessors.
- **Non-orthogonal projection:** replacing the Hilbert projection by an arbitrary
  algebraic complement preserves triangular determinant but destroys the canonical
  metric factor and Hadamard phase law.
- **Infinite posets:** the finite theorem does not silently extend to infinite products
  or determinants.  Any infinite version is a separate conjecture.
- **Novelty falsifier:** an existing theorem giving the same canonical predecessor
  residuals, comparable-pair zero pattern, determinant factorization, and incidence
  gauge invariant makes this `[REDISCOVERED]` or `[BRIDGE]`.

## No-go closure (mandatory when falsified)

- **Exact killing theorem/mechanism:** pending
- **Strongest positive survivor:** pending
- **New insight:** pending
- **Status:** active Stage-1 candidate

## Literature audit log

- Projective differential geometry and ordinary Wronskian gauge covariance kill the
  earlier variable-phase one-parameter jet-volume proposal as a novelty target.
- QR/Cholesky and flag stabilizers kill the bare triangular innovation-covariance
  proposal as a novelty target.
- Incidence groups and \(P\)-flag spaces kill the bare claim that poset-compatible
  shears form a new group.
- Searches for `poset Gram-Schmidt`, `incidence algebra Gram determinant`,
  `predecessor span orthogonalization`, and `incomparability graph Gram determinant`
  located adjacent parent theories but no exact equivalent of the surviving metric law.

## Log

- 2026-07-19 — created directly in `1-in-progress` after internal corpus search,
  three retired precursor chains, and a first external parent/novelty audit.
