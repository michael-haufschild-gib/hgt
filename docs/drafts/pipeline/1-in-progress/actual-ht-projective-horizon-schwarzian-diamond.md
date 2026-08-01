# Actual HT projective-horizon Schwarzian diamond

- **Stage:** 1 — theorem proved; paper integration and final audit in progress
- **Type:** universal theorem; exact transport to every hypertranscendental scalar
- **Claim label:** `[LEAN-PROVEN; FINAL AXIOM/LINT AUDIT PENDING]`
- **Source:** free-jet horizon join/meet laws plus canonical evaluation at an HT jet family
- **Paper target:** `4-publication-ready/riemann-source-modular-superselection`

## Question

For a hypertranscendental scalar (x) over a differential field (C), put

\[
J_n(x)=C\bigl(\delta^k x:k\ge n\bigr),\qquad
\mathcal S(x)=C\bigl(\delta^k\{x,t\}:k\ge0\bigr),
\]

where \(\{x,t\}=x'''/x'-\tfrac32(x''/x')^2\) is the Schwarzian.  The prior
corpus proved the exact join, nontrivial Schwarzian inclusion at depth one,
and scalar collapse as soon as either side reaches depth two.  The new theorem
identifies the actual depth-one meet exactly.

## Candidate theorem — sharp actual-carrier diamond

Assume (x) is hypertranscendental over (C).  Then

\[
\boxed{
\begin{aligned}
J_1(x)\vee J_1(x^{-1}) &= J_0(x),\\
J_1(x)\wedge J_1(x^{-1}) &= \mathcal S(x),\\
J_m(x)\wedge J_n(x^{-1}) &= C
  &&(m,n\ge1,\ \max\{m,n\}\ge2).
\end{aligned}}
\tag{D}
\]

The transition is sharp: one derivative erases the projective frame but
retains exactly projective curvature; deleting one further derivative erases
every common nonconstant rational differential observable.

## Paper proof

Let

\[
e_x:C(X_0,X_1,\ldots)\longrightarrow J_0(x),\qquad
e_x(X_k)=\delta^k x.
\]

Hypertranscendence makes the jet family algebraically independent, hence
(e_x) is a field isomorphism.  If the coefficient field is constant, the
universal derivation (D X_k=X_{k+1}) and ambient derivation commute with
evaluation on the full free rational field.  That stronger statement follows
first on polynomials and then by the quotient rule.  An arbitrary differential
coefficient field need not be constant, so full commutation is false there.

The needed Schwarzian statement survives without that restriction.  Every
formal jet (D^r\{X_0,t\}) is defined over the prime field.  Coefficient
extension of free scalar-jet fields is injective, commutes with the jet shift,
preserves these prime-field Schwarzian jets, and commutes with actual
evaluation.  Hypertranscendence over (C) restricts to the prime field, where
every coefficient is killed by the derivation.  Consequently

\[
e_x(D^rF)=\delta^r e_x(F)\quad(r\ge0).
\tag{1}
\]

The already-proved generator identities give

\[
e_x\bigl(C(X_k:k\ge n)\bigr)=J_n(x),\qquad
e_x\bigl(C(D^k(X_0^{-1}):k\ge n)\bigr)=J_n(x^{-1}).
\tag{2}
\]

The free theorem identifies the depth-one intersection with

\[
C\bigl(D^k\{X_0,t\}:k\ge0\bigr).
\]

Because evaluation preserves rational operations and, by (1), the complete
prime-field Schwarzian tower, its image is exactly \(\mathcal S(x)\).
Transporting the free
meet equality through the field isomorphism proves the middle line of (D).
The first and third lines are the existing intrinsic join and depth-two
collapse theorems.

## Formal implementation

1. Proved a constant-base universal-evaluation lemma for
   `projectiveHorizonJetParametrization`: evaluation commutes with
   `freeJetShift`.  Compare two derivations on the polynomial ring and extend
   through the fraction field, or use `IntermediateField.adjoin_induction`.
2. Proved injective coefficient base change for the free scalar-jet field,
   commutation with total jet shift, prime-field definition of every
   Schwarzian jet, and naturality of actual evaluation.  This removes the
   constant-base hypothesis from the final theorem.
3. Identified the map of `schwarzianDifferentialField` with the actual field
   `IntermediateField.adjoin C (Set.range fun k => differentialJet k
   (schwarzian x))`.
4. Pulled an element of the actual meet back with the existing two preimage
   lemmas, apply `jetTail_inf_eq_schwarzianDifferentialField`, and push it
   forward.  Prove the reverse inclusion from generator membership.
5. Packaged (D) as one capstone theorem and instantiated it literally on the
   centered zeta--Gamma HT carrier over its natural `RatFunc ℂ` base.

Tree modules:

- `HTGeometry/ProjectiveHorizonActualSchwarzianDiamond.lean`
- `RHTower/ZetaGammaProjectiveHorizonSchwarzianDiamond.lean`

## Internal collision audit

- `ProjectiveHorizonSchwarzianHorizonMeet` proves the exact meet only in the
  literal free rational jet field.
- `ProjectiveHorizonJetTailTransition` proves the exact actual join, a strict
  nonconstant Schwarzian lower bound on the actual first meet, and the exact
  scalar collapse at depth two; it does not prove the reverse inclusion at
  actual depth one.
- `ZetaGammaPhaseIntensityObservability` applies only the current three-part
  profile (distinctness, join, Schwarzian membership), so it also lacks the
  exact meet.
- No corpus theorem found in the pre-proof 7,060-module snapshot stated the
  actual first-depth equality.

## Antagonist attacks before formalization

1. **Decorative free model.**  Defeated only if the theorem is transported to
   every actual HT scalar and to the paper's zeta--Gamma carrier.
2. **Classical invariant theory.**  The assertion that the Schwarzian is the
   basic projective differential invariant is classical.  Novelty cannot rest
   on that slogan; it must rest on the exact two-horizon field lattice and its
   sharp depth-one/depth-two phase transition.
3. **No RH sign.**  (D) gives no zero exclusion.  Paper must present it as the
   universal information law explaining why one-sided scalarizations lose
   orientation, not as progress that locates zeros.
4. **Coefficient-field ambiguity.**  State all joins and meets inside
   (J_0(x)), and identify bottom with the image of (C); do not silently
   assume the ambient field is generated by (x).
5. **Differential-base failure.**  Full evaluation commutes with derivation
   only over constants.  Defeated without weakening the theorem: the
   Schwarzian tower descends to the prime field, and coefficient-base-change
   naturality transports precisely that tower over every compatible
   differential base.

## Gates

- [x] Exact conjecture isolated from already-proved neighboring claims
- [x] Dependency-closed paper proof
- [x] Internal collision search against current corpus snapshot
- [ ] External differential-invariant literature collision audit
- [x] Lean scratch proof, foreground `lake env lean <file>`
- [ ] Tree module proof and axiom audit
- [x] Tree modules pass foreground `lake env lean <file>`
- [x] Zeta--Gamma specialization over natural `ℂ(z)` base
- [ ] Paper integration and antagonistic review

## External collision audit — 2026-08-01

The middle equality cannot be advertised as discovery of the Schwarzian's
invariant-generating property.  Classical projective differential-invariant
theory already says that every rational projective differential invariant of
a parametrized projective line is generated by the Schwarzian and its total
derivatives; Marí Beffa--Sanders make this explicit in their
`sl_2`/transvection treatment, and moving-frame/Lie--Tresse theory supplies the
general invariant-generation setting.  Scanlon's generalized Schwarzian
likewise realizes the quotient by constant group points in differential
algebraic terms.

Targeted searches found no source stating the exact lattice identity

\[
C(x',x'',\ldots)\cap C((x^{-1})',(x^{-1})'',\ldots)
  = C\langle\{x,t\}\rangle
\]

together with the all-depth join and the sharp collapse of that meet to the
coefficient field when either cutoff advances from one to two.  Novelty must
therefore be claimed, if at all, for this **two-observer field-lattice phase
law**, not for Schwarzian invariance or generation alone.  Final manuscript
must cite classical invariant generation as antecedent and phrase priority
cautiously (`we are not aware of this exact horizon-lattice formulation`).

Key collision sources checked:

- G. Marí Beffa and J. A. Sanders, *Transvection and differential invariants
  of parametrized curves*, Journal of Lie Theory **18** (2008), 93--123.
- T. Scanlon, *Algebraic differential equations from covering maps*, Advances
  in Mathematics **330** (2018), 1071--1100.
- P. J. Olver, moving-frame and projective differential-invariant
  classification work, including *Projective invariants of images* (2022).

- [x] External differential-invariant literature collision audit
