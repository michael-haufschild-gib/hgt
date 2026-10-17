# RH proof constraints

Read this at the start of an RH research session. It records broad constraints
established by the Lean corpus: what an RH proof must ultimately establish, what
information an argument must preserve, and what specific classes of evidence cannot
establish the missing step. It is a checklist for a *new* idea, not a history of routes.
Route state belongs in the [frontier map], scoped failures in [killed routes], and
individual theorems in their Lean files and [pipeline cards].

**Logical status.** RH remains unproved here. An equivalence with RH identifies a
sufficient target, not a proof of its premise. Every negative statement below has a
stated class of hypotheses; none bans an unrelated method.

## What any proof must ultimately do

1. **Exclude every off-line zero of the actual zeta function.** The target is
   `Re ρ = 1/2` for every nontrivial zero, at every height and every nonzero horizontal
   displacement. Finite-height verification, a density-one result, and large-height
   approach to the line all leave possible exceptions. Multiplicity is part of divisor
   accounting; RH alone does not assert simple zeros. If a proof selects an extremal
   off-line zero, it must establish attainment or treat nonattainment.
   [Zeros-approach-line and attainment][zal-attainment].

2. **Close both large-height and residual-exception gaps, in some form.** The corpus
   proves `RH ↔ ZerosApproachLine ∧ AsymptoticAbscissaLaw`. The first property says that
   for every fixed distance from the line, only finitely many zeros can remain that
   deep; the second says that a *finite* set strictly right of any line `Re s = 1/2 + h`
   (`h ≥ 0`) must be empty. Under approach-to-line, an off-line zero would attain a
   maximal real part; the abscissa law removes that last possibility. This split is a
   diagnostic, not a required proof format: a proposed large-height theorem must still
   remove residual zeros, and a local exclusion theorem must still cover all heights.
   [Exact split][zal-aal]; [attainment][zal-attainment].

3. **Prove the decisive premise from independent arithmetic input.** An implication
   `P ⇒ RH` or equivalence `P ↔ RH` does not establish `P`. Positivity, a moment
   measure, a spectral identification, boundedness, or an asymptotic law can be the
   whole open problem in new notation. For example, one positive measure representing
   *every* canonical normalized prime–archimedean moment is equivalent to RH; matching a
   few moments is not that measure. State exactly which side is proved and where the
   independent source estimate or construction enters.
   [All-order moment criterion][moment-measure];
   [finite exact moment match][finite-sixth].

4. **Tie the argument to ζ with the exact data its identity needs.** A model, operator,
   transform, source, or replacement Dirichlet series must be proved to recover the
   relevant ζ/Ξ function or divisor, with correct analytic domain, multiplicities,
   coefficients, Gamma factor, pole terms, and normalization. In the *fixed ζ* full Weil
   cone, positivity for every compact-test autocorrelation forces `λ(n) = Λ(n)` for
   every `n ≥ 2`, and the cone is nonempty exactly under RH. Even an `o(Λ)` perturbation
   cannot give another full-positive point. This is rigidity of the fixed problem, not a
   ban on auxiliary forms. [Unconditional cone rigidity][weil-unique];
   [small-deviation rigidity][weil-small].

5. **Reach a criterion's exact strength and quantifiers.** For
   `ψ(x) = Σ_{p^k ≤ x} log p`, the corpus proves `RH ↔ ψ(x) − x = O(√x log² x)`. An
   estimate on only a sequence of `x`, with constants depending on a growing order, or
   below the required range does not meet this statement without a transfer theorem.
   Conversely, the unconditional `ψ(x) − x = Ω±(√x log log log x)` forbids an `O(√x)`
   target or either eventual fixed sign. Check the exact receiver before seeking a
   stronger but false bound. [Von Koch scale][von-koch];
   [Littlewood oscillation][littlewood].

6. **Preserve the information used to reject an off-line zero.** Show that the
   observation distinguishes the configurations it is meant to separate. Track zeros
   added or lost by division, continuation, projection, and normalization; retain zero
   orders when a divisor is claimed. A vanishing scalar reading need not mean a
   vanishing vector. Reflection-even data can detect *magnitude* of displacement, but
   cannot by themselves recover a reflection-odd sign; if a sign matters, identify its
   source. A transformed criterion with an exact inverse is useful only after its new
   inequality is proved independently.

7. **Pay for every global passage and signed term.** Specify domains and the topology
   needed to exchange sums, integrals, derivatives, contour shifts, traces, and limits.
   Control height, cutoff, aperture, test order, and their joint growth when they vary.
   Keep means, cross terms, tails, residues, endpoint charges, and normalization costs.
   In the exact ζ Weil form, nonnegative jump energies coexist with a signed creation
   potential and an indefinite pole plane. RH is equivalent to a bound on the *complete*
   negative sinh direction at every level; jump positivity alone does not provide it. In
   the literal prime-depth source, the exact von Mangoldt channel is an off-diagonal
   indefinite pairing; replacing either leg with a positive Gram square changes that
   source. [Weil decomposition and capacity criterion][weil-capacity];
   [literal source pairing][krein-source].

## Boundaries proved for common kinds of evidence

- **Symmetry and generic positivity do not locate ζ zeros.** The functional equation
  pairs off-line zeros but does not place them on its fixed line. An entire order-one
  completion with nonnegative generalized von Mangoldt data can have off-line zeros.
  That counterexample has a different pole order from ζ, so it refutes this *weaker
  package*, not the full ζ data. [Functional-equation countermodel][fe-countermodel].

- **Changing the archimedean or polar datum changes the positivity problem.** Pole-free
  Dirichlet and modular Weil cones with nonnegative archimedean density contain zero
  arithmetic weights in the stated conductor/weight ranges. Adding a sufficiently large
  positive archimedean boost to the ζ datum admits the constant weights `λ(n)=1` for
  `n≥2`. Positivity for an altered form therefore cannot be read as positivity of the
  fixed ζ form; prove the comparison and retain its cost.
  [Pole-free cones][cone-anatomy]; [boosted ζ example][boosted-cone].

- **Critical-line twins are rigid under their full arithmetic hypotheses.** For a
  real-coefficient degree-`d` Dirichlet twin with `a(1)=1`, an absolutely convergent
  half-plane series, and the specified entire finite-order reflection-even completion,
  having *all* completed zeros on the critical line forces RH and equality with `ζ^d` on
  the common convergence half-plane. This is a conditional uniqueness theorem, not a way
  to establish critical-line zeros for a proposed twin. [Twin rigidity][twin-rigidity].

- **Finite source data do not supply an all-order condition.** One positive finite
  carrier matches the actual source's quadratic, quartic, and sixth traces exactly
  without locating Ξ zeros. Every fixed finite Hankel block has infinitely many
  unrestricted moment-sequence continuations. In the pole-constrained Weil form,
  finitely many prescribed strict-interior physical source values leave the ground
  infimum unchanged. These are precise finite-data obstructions; they do not preclude a
  proved finite reduction or a uniform theorem covering all orders.
  [Exact finite match][finite-sixth]; [Hankel extensions][finite-moments];
  [source sampling][finite-samples].

- **Shape conditions alone do not replace literal theta arithmetic.** Compact
  theta-source perturbations can remain positive, even, strongly log-concave, match any
  prescribed finite moment list and the critical half-density charge, and stay positive
  on the right after every finite prime deletion, yet acquire an off-real Mellin zero.
  They do *not* preserve the exact theta Euler coefficients. A shape-based argument
  needs a constraint that excludes these perturbations; the countermodels do not assert
  an off-line zero for ζ. [Theta countermodels][theta-shape].

- **Literal theta Euler completion carries a singular boundary charge.** At the critical
  Mellin weight, each finite-prime theta source has integral `0`, while the completed
  source has integral `1/2`; finite-prime sources therefore cannot converge in the
  corresponding weighted `L¹` norm. Their two reflected ports also differ: a stage with
  `|P|` admitted primes has a zero at `+1/2` and a pole of order `|P|` at `−1/2`,
  whereas the completed source has finite charge at both. Any use of this source must
  retain the boundary observation and justify the two-port limit. This is a constraint
  on that completion, not on every RH proof. [Critical charge][theta-charge];
  [two-port divisor price][theta-ports].

- **Local source convergence need not preserve the complex divisor.** Every *finite*
  literal prime deletion of the completed theta source preserves interior Ξ zero orders:
  its Mellin transform is `Ξ` times zero-free Euler factors there. Along an exhaustion
  of the primes, those sources converge locally to the Gaussian seed, whose transform
  has no such interior zeros. Thus source convergence, even with each finite-stage
  divisor known, needs a stronger global transform/divisor theorem. The positive
  survivor is exact finite-deletion divisor fidelity, not a limit identification.
  [Prime deletion and spectral escape][theta-deletion].

- **A detector must have enough divisor capacity.** No nonzero continuous compactly
  supported test has Fourier–Laplace transform divisible by `Ξ` or `Ξ²`: its exponential
  type allows `O(T)` zeros, against `≫T log T` already supplied by distinct critical Ξ
  ordinates. In a separate rigged prime-source model, a fixed bounded scalar reading is
  a weighted Dirichlet readout with only `O(T)` real zeros unless it vanishes on the
  source coordinates; a nontrivial limiting divisor reader in that model forces reader
  norms to diverge. These statements constrain *single fixed readings* in the named
  classes, not compact test families or all spectral constructions.
  [Compact-test obstruction][divisor-density];
  [bounded reading obstruction][bounded-reader].

- **Averaging can erase the location being tested.** Full translation averages of entire
  one-level tests with the stated stripwise quadratic decay are independent of a zero's
  horizontal displacement. Such an average cannot detect off-line zeros. This says
  nothing about every density statistic: before using an average, compute which
  transverse information survives it. [Translation-average blindness][averaging].

- **Pointwise or strong convergence need not pay a global norm cost.** In the specified
  prime co-shift parameter class, finite kernel projections converge strongly to the
  full ground projection while remaining norm distance one from it. A finite-stage sign,
  compact-open source limit, or strong operator limit therefore needs the particular
  uniform bound required by the final receiver. The theta boundary charge and
  prime-deletion examples above show two distinct ways a spectral or boundary
  contribution can escape. [Cofinal completion gap][completion-gap].

- **Self-adjointness alone is not a ζ spectral theorem.** An arbitrary real diagonal
  energy has a densely defined self-adjoint multiplication operator on its maximal `ℓ²`
  domain. Encoding selected real ordinates as eigenvalues is therefore cheap. A spectral
  proof must identify *every* relevant ζ zero with the actual operator, including its
  domain and converse; formal modes, resonances, and Hilbert eigenvectors need separate
  justification. [Maximal diagonal realization][spectral-realization].

## Checklist for a new topic

- [ ] State exact proposed theorem, its status, and a proved implication to RH.
- [ ] Identify independent arithmetic premise still to prove; do not count an RH equivalence as its proof.
- [ ] Test both large-height approach and residual finite exceptions, or explain how proposal excludes every off-line zero directly.
- [ ] Locate exact ζ/Ξ coefficients, Gamma and pole terms, domain, normalization, and divisor multiplicities in construction.
- [ ] Check sign, exponent, test class, and *all* quantifiers required by intended receiver.
- [ ] Name information lost under each transform, symmetry, average, projection, and limit; supply recovery theorem if it matters.
- [ ] Account for signed pieces, means, tails, boundary charges, and uniform parameter dependence in topology used.
- [ ] Apply a no-go only when every hypothesis holds for proposal; record any sharp positive survivor.

An unanswered box is a proof obligation, not an automatic rejection. No corpus result
requires every RH proof to be singular, noncompact, nonlinear, or built from any
particular route. Add to this document only when a proved result changes a broadly
applicable constraint; keep route logs, conjectures, build reports, and theorem
inventories elsewhere.

[frontier map]: rh-current-frontier-map.md
[killed routes]: rh-killed-routes.md
[pipeline cards]: ../drafts/pipeline/
[zal-attainment]: ../../formal/GaloisForLFunctions/RHTower/ZerosApproachLineAttainment.lean
[zal-aal]: ../../formal/GaloisForLFunctions/RHTower/ZetaWeakRecurrenceLadderCollapse.lean
[moment-measure]: ../../formal/GaloisForLFunctions/RHTower/PrimeArchMomentMeasureRH.lean
[finite-sixth]: ../../formal/GaloisForLFunctions/RHTower/XiPrimeMarkedFiniteSixthExactCarrier.lean
[weil-unique]: ../../formal/GaloisForLFunctions/RHTower/WeilConeUniquenessUnconditional.lean
[weil-small]: ../../formal/GaloisForLFunctions/RHTower/WeilLittleOVonMangoldtRigidity.lean
[von-koch]: ../../formal/GaloisForLFunctions/RHTower/VonKochChebyshevBound.lean
[littlewood]: ../../formal/GaloisForLFunctions/RHTower/LittlewoodOmega.lean
[weil-capacity]: ../../formal/GaloisForLFunctions/RHTower/WeilMarkovPoleCapacity.lean
[krein-source]: ../../formal/GaloisForLFunctions/RHTower/EulerPrimitiveJointDepthKreinXiLanding.lean
[fe-countermodel]: ../../formal/GaloisForLFunctions/RHTower/EntireFunctionalEquationOffLine.lean
[cone-anatomy]: ../../formal/GaloisForLFunctions/RHTower/WeilConePoleDualityAnatomy.lean
[boosted-cone]: ../../formal/GaloisForLFunctions/RHTower/TrivialWeightBoostedWeilCone.lean
[twin-rigidity]: ../../formal/GaloisForLFunctions/RHTower/TwinRigidityZetaPower.lean
[finite-moments]: ../../formal/GaloisForLFunctions/HTGeometry/FiniteHankelBoundaryExtensionClass.lean
[finite-samples]: ../../formal/GaloisForLFunctions/RHTower/CCMFiniteSamplingGroundRigidity.lean
[theta-shape]: ../../formal/GaloisForLFunctions/RHTower/ThetaCompactStripZeroEngineering.lean
[theta-charge]: ../../formal/GaloisForLFunctions/RHTower/ThetaCriticalBoundaryMellinCharge.lean
[theta-ports]: ../../formal/GaloisForLFunctions/RHTower/ThetaEulerTwoPortJetPole.lean
[theta-deletion]: ../../formal/GaloisForLFunctions/RHTower/ThetaPrimeDeletionSpectralEscape.lean
[divisor-density]: ../../formal/GaloisForLFunctions/RHTower/CompactTestXiDivisibilityObstruction.lean
[bounded-reader]: ../../formal/GaloisForLFunctions/RHTower/PhysicalOrdinateZeroDensityRigidity.lean
[averaging]: ../../formal/GaloisForLFunctions/RHTower/TranslationAveragedDensityDepthBlindness.lean
[completion-gap]: ../../formal/GaloisForLFunctions/RHTower/PaperPrimeCoShiftCofinalGap.lean
[spectral-realization]: ../../formal/GaloisForLFunctions/HTGeometry/MaximalRealDiagonalSelfAdjoint.lean
