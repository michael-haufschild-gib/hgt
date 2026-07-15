# Hypertranscendence of every finite Gamma iterate

- **ID:** finite-gamma-iteration-hypertranscendence
- **Stage:** 3-formalized
- **Type:** THEOREM · ITERATION HYPERTRANSCENDENCE
- **Status:** `[PROVEN] [LEAN FORMALIZED] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** Let `F₀(z)=z` and `Fₖ₊₁(z)=Γ(Fₖ(z))`.  For every `k ≥ 1`, the germ of
  `Fₖ` at the Gamma fixed point `1` admits no nonzero polynomial-coefficient differential relation.
  Consequently every finite Gamma iterate is hypertranscendental.

## Source-pure mechanism

The point `1` is fixed by Gamma, and every finite iterate is analytic on some neighborhood of `1`.
At the factorial poles of the innermost Gamma,

\[
  \Gamma\!\left(-n+\frac{(-1)^{n+1}}{n!}x\right)\longrightarrow -\frac1x.
\]

Thus a hypothetical local differential relation for `Fₖ₊₁ = Fₖ ∘ Γ`, propagated to all late
microscopes, has a nonzero initial form annihilating `x ↦ Fₖ(-1/x)`.  Möbius jet pullback turns it
into a nonzero local relation for `Fₖ` near `1`, contradicting the induction hypothesis.  The
argument uses only a small microscope neighborhood of `x=-1`; unlike the first global composition
principle, it must not assume that `Fₖ` is analytic on the whole right half-plane.

## Local reflection core `[PROVEN]`

Localize the factorial initial-form theorem and the outer-composition jet-convergence theorem to an
arbitrary open microscope patch `U` containing `-1`, under analyticity of the outer germ on a
neighborhood of `-1/U`.  Prove that the existing triangular Möbius pullback remains injective and
that the resulting relation holds eventually near `1`.  Then package the fixed-point induction.

This is an analytic localization of the concrete Gamma microscope, not a new carrier or abstract
constraint-reflector class.

The localization is realized using the intrinsic domain

\[
  U_\Omega=\{x\ne0:-1/x\in\Omega\},
\]

where `Ω` is the outer germ's open regular set.  Compact-open Gamma convergence keeps every late
microscope inside `Ω`; Cauchy jet convergence produces the initial relation; the local Möbius
pullback contradicts rigidity at `1`.

For the induction, the depth-`k` regular set is defined recursively by requiring the innermost
Gamma input to avoid its poles and its value to lie in the depth-`k-1` regular set.  Every Gamma
fiber is countable, so every finite-depth singular complement is countable and the regular set is
path connected.  A relation on any regular patch therefore propagates to the microscope domain.

## Stronger route kept separate

Differential algebraic independence of `(F₁,…,Fₖ)` would be substantially stronger.  One microscope
lowers every depth by one, but the first component degenerates to the rational germ `-1/x`; a
nonzero multivariate initial polynomial may therefore enter the differential ideal of that rational
germ.  Defeating this kernel requires a source-specific higher residue or deformation invariant and
is not implied by the single-function induction above.

## Novelty and significance gate

- Classical iteration theory studies the dynamics and singularities of meromorphic iterates, not
  their algebraic differential equations.
- Existing Gamma hypertranscendence and shift-independence results do not, in the sources checked so
  far, state hypertranscendence of all finite self-iterates.
- The depth-two theorem `Γ ∘ Γ` is already formalized.  The candidate new content here is the
  source-specific induction through every finite depth.
- A prior theorem for all finite Gamma iterates, or a general local composition theorem covering
  this meromorphic-inner setting, retires the novelty claim.

## Gates

- [x] 0 → 1 in-progress: fixed-point induction and exact missing local theorem isolated
- [x] 1 → 2 fully-proven: localized microscope reflection, recursive regular-domain theorem, and
  fixed-point induction proved
- [x] 2 → 3 formalized: local reflector and all-depth theorem formalized with targeted checks
- [ ] 3 → 4 publication-ready: exact iteration/differential-algebra priority audit independently
  replicated

## Formal realization

`formal/GaloisForLFunctions/HTGeometry/GammaIterationHypertranscendence.lean` contains:

- `gammaFiber_countable` and `gammaIterateRegularSet_compl_countable`;
- `no_eventual_differential_relation_outer_comp_Gamma_local`;
- `locallyPolynomialJetRigidAt_gammaIterate`;
- `hypertranscendental_gammaIterate`;
- `no_local_differential_relation_gammaIterate`.

The module compiles directly and through its individual Lake target.  The six audited declarations
depend only on `propext`, `Classical.choice`, and `Quot.sound`.  Formal lint passes.  No full build
was run.

## Log

- 2026-07-15 — opened after `Γ ∘ Γ` was formalized.  The full-right-half-plane hypothesis in the
  existing reflector was identified as unnecessary for the all-depth route and as the precise
  obstacle to reusing the theorem verbatim.
- 2026-07-15 — recursive regular sets, localized factorial reflection, all-depth rigidity,
  hypertranscendence, and regular-patch relation-freeness formalized; promoted to stage 3 after
  targeted compilation and axiom audit.
