# Time–return duality law

- **ID:** time-return-duality-law
- **Stage:** 1-in-progress
- **Type:** MASTER CONJECTURE / UNIVERSAL STATIONARY RECURRENCE QUOTIENT
- **Source:** recurrence corpus synthesis
- **Statement:** Every stationary quantum return experiment factors through one maximal
  unoriented system--clock quotient.  Uniform long-time sampling then retains exactly the
  recurrent atomic hull.  In finite rank, the dimension of that hull is twice the
  small-defect return-volume exponent and the complement of exact relation rank.

## Goal

Replace novelty-by-assembly with one operational law whose shadows are the
existing constraint-conversion, observer-quotient, water-entropy,
interaction, countable-depth and peripheral-carrier results.

The candidate primitive is no longer the finite-dimensional Weyl exponent.
For an arbitrary probability energy law \(\mu\) and probability clock law
\(\rho\), put
\[
  \nu_\mu=\mu*\widetilde\mu,\qquad
  \sigma_\rho=\frac{\rho+\widetilde\rho}{2},
\]
and define the complete sampled recurrence law
\[
  \mathfrak R(\mu,\rho)
  =
  \bigl(\widehat{\nu_\mu}\bigr)_*\sigma_\rho.
  \tag{URQ}
\]
Here \(\widehat{\nu_\mu}(t)=|\widehat\mu(t)|^2\in[0,1]\).
The corpus already proves that the two quotient maps in `(URQ)` are maximal
under universal cross-testing: systems are indistinguishable to every clock
exactly when their difference laws agree, and clocks are indistinguishable
to every system exactly when their orientation quotients agree.

The missing stationary-completion theorem is the single weak limit
\[
  \mathfrak R(\mu,\rho_T)
  \Longrightarrow
  \left(
    \left|\sum_jw_jz_j\right|^2
  \right)_*m_{K_\mu},
  \qquad
  \rho_T=\operatorname{Unif}[-T,T],
  \tag{SC}
\]
where \((w_j,E_j)\) are the atoms of \(\mu\), \(K_\mu\) is their compact
relation hull and \(m_{K_\mu}\) its invariant probability law.  Thus the
continuous spectral part disappears from the complete long-time return
distribution without disappearing from the underlying unitary evolution.
The finite Weyl law below is a local geometric corollary of `(SC)`, not the
master law.

The intended physical sentence is:

> **Quantum recurrence reveals the geometry of stationary time, but its
> maximal observable is intrinsically unoriented.**

This wording has two exact obligations.  “Geometry” means the recurrent
atomic relation hull, its observer quotient, target volumes and finite-rank
metric.  “Unoriented” means the proved maximal clock quotient
\(\rho\mapsto\sigma_\rho\), not a claim that all causal observables or all
experiments are time-reversal blind.

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

## RH-corpus stress test: the same quotient boundary

The RH corpus was audited as a hostile test of the interpretation, not as a
source of an RH claim for this paper.

The repeated exact pattern is:

1. reflection-invariant positive, quadratic or intensity readers can be
   complete for their even quotient;
2. the source-facing orientation lives in an odd phase/character lift;
3. passing to the quotient preserves collision location or magnitude while
   erasing the first oriented jet;
4. adding more equivalent positive criteria does not recreate the erased
   coordinate.

The clearest formal instances are:

- `Oriented reflection quotient law`: channel exchange sends the odd Cayley
  coordinate \(J\) to \(-J\); invariant entire readers descend through
  \(J^2\) and every differentiable even reader has zero first jet at the
  collision.
- `HedenmalmOrientationUpperSingularityCeilingRH`: the exact RH-facing
  criterion is analyticity of a canonical *oriented* multiplier, not merely
  positivity of a symmetric scalar.
- `SuzukiVolterraCartesianPhaseDefect`: keeping the symmetric Cartesian
  response fixed leaves a nonzero phase half-difference.
- `HorizonBogoliubovGammaObservability`: the reflected intensity core is
  differentially algebraic while the orientation-sensitive phase quotient
  and Wigner--Smith logarithmic delay are hypertranscendental and cannot be
  recovered by a finite differential circuit from intensity.
- `riemann-source-modular-superselection/main.tex`: source clock, collision
  geometry, global magnitude, diagonal positivity, odd orientation and
  global common-test positivity form a strict observable hierarchy.  Its
  central warning is that “complete” must name the quotient for which it is
  complete.

The recurrence corpus has the same architecture in an exact, non-analogical
form:
\[
  \rho\longmapsto\sigma_\rho
  \quad\text{erases clock orientation},\qquad
  \mu\longmapsto\nu_\mu
  \quad\text{erases energy origin and phase-retrieval representatives}.
\]
All return laws factor through these maps, and each map is maximal against
the opposite universal probe family.  Therefore the paper must never call
return data complete for the Hamiltonian, state, clock orientation or causal
arrow.  The allowed statement is stronger and more precise: return data are
complete for the maximal stationary recurrence quotient.

No connection to RH is authorized for the public manuscript unless a new
formal theorem explicitly connects an RH carrier to `(URQ)`.  The present
audit supplies the missing conceptual distinction, not an RH consequence.

## Log

- 2026-07-31 — created in 1-in-progress after rejecting novelty by conjunction.
- 2026-07-31 — proved and formalized local temporal-metric brick in
  `ObserverReturnTemporalMetricLaw.lean`: exact phase defect is bounded above
  by observer Gram energy and, on the principal chart, bounds it below up to
  `π²/4`; positive visible weights make the metric nondegenerate exactly
  when gaps separate temporal coordinates. Foreground compile passed; axiom
  audit uses only `propext`, `Classical.choice`, `Quot.sound`.
- 2026-07-31 — proved and formalized
  `ObserverReturnLocalVolumeLaw.lean`: under positive coercivity constants,
  the local high-fidelity target is trapped between Euclidean balls with
  radii proportional to `√ε`, and its measure is trapped between their
  exact volumes. This proves the local `ε^(τ/2)` Weyl scale without a
  Gaussian or randomness premise.
- 2026-07-31 — removed the remaining local hypotheses in
  `ObserverReturnTemporalCoercivityLaw.lean`: every finite separating
  positively weighted gap family has a positive-definite Gram matrix,
  automatic two-sided quadratic bounds, and an automatic positive principal
  phase radius. `ObserverReturnLocalVolumeLaw.lean` now contains an
  assumption-free local ball sandwich for every such family.
- 2026-07-31 — proved the compact global localization step in
  `ObserverReturnGlobalLocalizationLaw.lean`: on any compact orbit carrier,
  the complete sufficiently small return sublevel lies in any prescribed
  neighborhood of the exact-return set. Foreground compiles passed; axiom
  audit of the new coercivity and automatic local-volume theorems uses only
  `propext`, `Classical.choice`, and `Quot.sound`.
- 2026-07-31 — RH-wide corpus audit and
  `riemann-source-modular-superselection/main.tex` forced a stronger master:
  recurrence is a maximal unoriented quotient followed by stationary atomic
  completion.  The finite recurrence Weyl law is now a corollary.  The audit
  also forbids calling recurrence complete for the source, Hamiltonian or
  arrow of time.
