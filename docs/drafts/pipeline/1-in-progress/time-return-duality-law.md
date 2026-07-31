# Time–return duality law

- **ID:** time-return-duality-law
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** recurrence corpus synthesis
- **Statement:** A recurrence Weyl law makes observer-visible temporal dimension the small-defect return-volume exponent, its temporal metric the prefactor, and exact relation rank the complementary projective capacity.

## Goal

Replace novelty-by-assembly with one operational law whose shadows are the
existing constraint-conversion, observer-quotient, water-entropy,
interaction, countable-depth and peripheral-carrier results.

For a finite probability-weighted quantum spectrum, let \(K\) be the exact
projective orbit hull, let \(\nu_K\) be Haar measure on \(K\), and let
\[
  V(\eta)=\nu_K\!\left\{z:
    \left|\sum_j w_jz_j\right|\ge 1-\eta\right\}.
\]
Write \(\tau\) for rational rank of visible energy gaps, \(C\) for
projective phase capacity and \(\rho\) for exact balanced-relation rank.
Conjecture:
\[
  \tau
  =2\lim_{\eta\downarrow0}
      \frac{-\log V(\eta)}{\log(1/\eta)}
  =C-\rho.
\]
More sharply, after a primitive \(\tau\)-torus parametrization of the orbit
hull,
\[
  V(\eta)\sim
  \frac{\operatorname{vol}(B_\tau)}
       {(2\pi)^\tau\sqrt{\det G_{\mathcal O}}}
  (2\eta)^{\tau/2},
\]
where \(G_{\mathcal O}\) is the positive temporal metric obtained by
restricting the observer-weighted gap quadratic form to the hull tangent
space. The precise factor \(2\eta\) is for survival amplitude threshold
\(1-\eta\); an observer displacement threshold uses its own quadratic
defect directly.
The metric statement must remain valid after an arbitrary finite observer
quotient. Interaction then obeys
\[
  \Delta\tau=-\Delta\rho
  =2\,\Delta(\text{return-scarcity exponent}).
\]
For summable countable pure-point packets, the finite exponent is replaced
by a running profile whose exact slope is the visible spectral count. For a
finite contraction, the law acts on its peripheral carrier after transient
decay.

## Gates

- [x] 0 → 1 in-progress: well-posed, corpus shadows identified, primary
  novelty kill test started
- [ ] 1 → 2 fully-proven: complete relation-aware small-target proof,
  observer pullback proof, countable and peripheral corollaries
- [ ] 2 → 3 formalized: unconditional Lean theorem(s), foreground
  `lake env lean` verification and standard-axiom audit
- [ ] 3 → 4 publication-ready: master paper rewritten around this identity,
  source-complete priority audit and hostile Nature review

## Approach

1. Kill-test against quantitative recurrence/local-dimension literature.
   Existing mixing theorems do not cover nonmixing quasiperiodic quantum
   phase flows or the exact constraint-conversion identity.
2. Represent the finite orbit hull as the image of a full-rank integer map
   from a \(\tau\)-torus after choosing a rational gap basis and clearing
   denominators.
3. Pull the fidelity defect back to that torus. Positive spectral weights
   make its Hessian positive definite modulo the finite kernel. Prove
   two-sided quadratic comparison on a small fundamental neighborhood.
4. Convert quadratic comparison to two-sided Haar-volume bounds
   \(c\eta^{\tau/2}\le V(\eta)\le C\eta^{\tau/2}\).
5. Join with projective rank–nullity, observer action, weak interaction and
   fixed-hopping realization.
6. Recover the existing water entropy as the relation-free finite-resolution
   form and spectral-depth entropy as its countable running form.

## Kill tests

- If zero weights are allowed, invisible coordinates must first be removed;
  otherwise the Hessian is degenerate and the stated exponent is false.
- Finite cyclic orbit hulls have \(\tau=0\) and nonvanishing target mass;
  exponent \(0\), as required.
- Individual first-return exponents of Liouville rotations need not equal
  dimension. The law concerns exact orbit-Haar return scarcity and minimax
  clock entropy, not every fixed spectrum's first-hit asymptotic.
- Atomless spectra do not have a finite torus exponent; existing zero-density
  law is the dispersive branch, not evidence for a finite equality.
- Rank–nullity alone is not novelty. Operational return-volume identity and
  physical interaction conversion are required.

## Log

- 2026-07-31 — created in 1-in-progress after rejecting novelty by conjunction.
