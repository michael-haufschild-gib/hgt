# RH proof constraints

Route-independent facts and checks for every new RH research topic. The target is
the actual Riemann zeta function: every nontrivial zero `ρ` has `Re ρ = 1/2`.
Read this before choosing a mechanism. Detailed route state belongs in the
[frontier map](rh-current-frontier-map.md); individual results belong in their
proofs and [pipeline cards](../drafts/pipeline/).

**Scope matters.** Universal obligations appear first. Obstructions below apply
only under their stated hypotheses. A counterexample to one construction does
not classify all possible RH proofs.

## What a proof must establish

1. **Exclude every off-line zero.** Finite-height verification, density-one
   results, and zeros approaching the line leave possible exceptions. Cover all
   heights and arbitrarily small nonzero horizontal displacements. Handle
   multiplicities; simplicity requires its own proof. If an argument chooses a
   rightmost zero, prove that the supremum is attained or handle nonattainment.
   [Attainment and the remaining exceptions][attainment].

2. **Prove the decisive premise independently.** An implication `P ⇒ RH`, or
   equivalence `P ⇔ RH`, is a criterion, not a proof of `P`. Positivity, boundedness,
   recurrence, compactness, nonvanishing, and exact descent can each hide the
   whole problem. Identify the unproved premise and derive it without assuming
   RH or another unproved equivalent. Arguments about zeros are legitimate;
   fitting an object to desired zero locations does not establish those locations.

3. **Stay connected to the actual arithmetic object.** Prove any replacement
   source, transform, operator, or model has the required relation to ζ. Keep the
   exact coefficients, Gamma factor, pole terms, and normalizations whenever the
   chosen identity uses them. A modified source needs a proved transfer back.
   In the fixed ζ Weil problem, positivity on all compact test autocorrelations
   forces the weights to equal `Λ(n)` for `n ≥ 2`; the cone is `{Λ}` under RH and
   empty otherwise. Changing the archimedean or polar datum changes that problem.
   [Exact-weight rigidity][weights].

4. **Reach the actual threshold.** State the exponent, sign, test class, and
   quantifiers that imply RH. For example, with
   `ψ(x) = Σ_{p^k ≤ x} log p`, RH is equivalent to
   `ψ(x) − x = O(√x log²x)`. An estimate short of its receiver's threshold remains
   short, however elegant its formulation. Stronger targets also need checking:
   `ψ(x) − x = Ω±(√x log log log x)` rules out `O(√x)` and either eventual fixed
   sign. [RH scale][von-koch]; [unavoidable oscillation][littlewood].

5. **Retain enough information for zero exclusion.** Prove that the decisive
   observation detects the off-line configurations it is meant to exclude.
   Track zeros introduced or removed by division, normalization, projection,
   and continuation; track multiplicity when the criterion uses it. A vanishing
   scalar reading need not mean a vanishing vector. Erased information needs a
   recovery theorem or an independent reason it is irrelevant.

6. **Justify the global passage in the topology actually needed.** Give the
   domains, convergence, and parameter dependence required for summation,
   differentiation, integration, traces, and limits. Control moving height,
   cutoff, aperture, and order when they occur together. A bound for each fixed
   order does not automatically allow order to grow with height. Identify any
   mass, residue, or spectral contribution that can escape the limiting observation.

7. **Close the complete signed comparison.** Keep cross terms, means, tails,
   endpoint contributions, and normalization costs. Positive pieces do not
   establish the sign of their difference; a lower bound is not an upper bound.
   In the actual Weil form, nonnegative jump energies coexist with a signed
   creation term and an indefinite pole contribution. Their full balance is
   the requirement. [Exact decomposition and capacity criterion][weil-balance].

## What cannot supply the missing step by itself

1. **Functional-equation symmetry and generic source positivity.** Reflection
   pairs off-line zeros; it does not put them at fixed points. Entire order-one
   completions with nonnegative generalized von Mangoldt data can still have
   off-line zeros. The cited example changes the pole order and is not ordinary
   ζ: it refutes only the weaker package of assumptions.
   [Scoped counterexample][fe-countermodel].

2. **Positive shape without the arithmetic restriction.** Positivity, evenness,
   strong log-concavity, any prescribed finite moment list, and the exact critical
   half-density charge do not force real Fourier zeros. Compact perturbations of
   the theta source preserve these properties while forcing an off-real zero.
   They do not preserve the exact theta source. A shape-based proof needs an
   additional restriction that excludes such perturbations.
   [Theta-source countermodels][theta-shape].

3. **A fixed finite collection of checks.** A finite Hankel block admits
   infinitely many unrestricted sequence extensions. For the pole-constrained
   Weil form, prescribing finitely many strict-interior physical source values
   leaves its ground infimum unchanged. Neither result forbids a theorem
   controlling all orders or a valid finite reduction; the reduction itself
   must be proved. [Moment indeterminacy][finite-moments]; [sampling obstruction][finite-samples].

4. **An observation that has removed the distinction being tested.** Full
   translation averages of entire one-level tests with quadratic decay on every
   horizontal strip are independent of a zero's horizontal displacement.
   They cannot detect off-line zeros. This is a statement about that averaging
   operation, not every density statistic. Likewise, an invariant reading cannot
   recover a sign reversed by its symmetry. An even quantity such as
   `(Re ρ − 1/2)²` can still detect displacement; proving it vanishes is the task.
   [Translation-average blindness][averaging].

5. **A new encoding of an old obstruction.** Invertible transforms, exact
   reconstruction, equivalent criteria, and several coordinates of the same
   defect provide no additional restriction merely by agreeing. Integer-valued
   charge does not vanish because it is integral: it needs a zero law, sign
   argument, or bound below the first allowed nonzero value. Optimization needs
   an independently justified objective and admissible class.

6. **Finite-stage or weak convergence without the required limit theorem.**
   Strong operator convergence does not imply norm convergence: actual finite
   prime co-shift projections converge strongly while staying norm distance one
   from the limit. Local convergence of sources likewise does not by itself
   justify convergence of their global transforms or divisors.
   [Explicit completion gap][completion-gap].

7. **Self-adjointness or a positive Hilbert model without zero identification.**
   Arbitrary real spectral data have self-adjoint realizations. Listing zero
   ordinates in a real spectrum says nothing about their real parts. A spectral
   proof must link every relevant zero to the actual operator and domain;
   resonances, formal eigenfunctions, and Hilbert-space eigenvectors are different
   notions. [Generic realization][spectral-realization].

8. **A carrier too small for the required divisor.** Growth and zero-count laws
   must match. For example, no nonzero continuous compactly supported test has a
   Fourier–Laplace transform vanishing at every real zero of `Ξ`: its exponential
   type allows only `O(T)` zeros, while the critical zeros already supply
   `≫ T log T`. Thus such a transform cannot be divisible by `Ξ` or `Ξ²`.
   This does not rule out compactly supported test families in positivity criteria.
   [Divisibility obstruction][divisor-density].

## Checklist for a new topic

- [ ] What exact new statement is being sought, and what proved implication connects it to RH?
- [ ] Which premise remains unproved? Is it merely an RH-equivalent condition in new notation?
- [ ] Where does the argument use the actual ζ data rather than properties shared by countermodels?
- [ ] Does it exclude a single off-line zero, including arbitrarily high, near-line, or multiple zeros?
- [ ] Which information survives every transform, and where are all signed and boundary terms accounted for?
- [ ] Are domains, limit exchanges, parameter dependence, and any attainment assumption justified?
- [ ] Does each cited obstruction satisfy the proposal's hypotheses together, in the same model?

An unanswered item is an explicit proof obligation, not automatically a reason
to reject a research topic. No result here requires every RH proof to be
nonlinear, singular, noncompact, based on two directed legs, or outside standard
mathematics. Quantitative estimates and positive forms remain possible methods;
their decisive arithmetic properties must be proved.

## Keep this document useful

Keep this a short session brief (target: at most 1,500 words). Add an entry only
when a proved result changes a route-independent requirement or a broadly useful
obstruction. State its scope and link exact evidence; distinguish a proved
conditional implication from a proved premise, and paper evidence from formal
evidence. Merge overlapping constraints instead of appending another theorem.

Route progress, dates, loop numbers, build reports, conjectures, proposed next
steps, and theorem inventories belong in the frontier map or pipeline cards.
Details of retired mechanisms belong in [scoped no-gos](rh-killed-routes.md).
Do not promote a failed construction into a universal ban, or an open replacement
hypothesis into something every proof must use.

[attainment]: ../../formal/GaloisForLFunctions/RHTower/ZerosApproachLineAttainment.lean
[weights]: ../../formal/GaloisForLFunctions/RHTower/WeilConeUniquenessUnconditional.lean
[von-koch]: ../../formal/GaloisForLFunctions/RHTower/VonKochChebyshevBound.lean
[littlewood]: ../../formal/GaloisForLFunctions/RHTower/LittlewoodOmega.lean
[weil-balance]: ../../formal/GaloisForLFunctions/RHTower/WeilMarkovPoleCapacity.lean
[fe-countermodel]: ../../formal/GaloisForLFunctions/RHTower/EntireFunctionalEquationOffLine.lean
[theta-shape]: ../../formal/GaloisForLFunctions/RHTower/ThetaCompactStripZeroEngineering.lean
[finite-moments]: ../../formal/GaloisForLFunctions/HTGeometry/FiniteHankelBoundaryExtensionClass.lean
[finite-samples]: ../../formal/GaloisForLFunctions/RHTower/CCMFiniteSamplingGroundRigidity.lean
[averaging]: ../../formal/GaloisForLFunctions/RHTower/TranslationAveragedDensityDepthBlindness.lean
[completion-gap]: ../../formal/GaloisForLFunctions/RHTower/PaperPrimeCoShiftCofinalGap.lean
[spectral-realization]: ../../formal/GaloisForLFunctions/RHTower/CountableSpectralHamiltonianRealization.lean
[divisor-density]: ../../formal/GaloisForLFunctions/RHTower/CompactTestXiDivisibilityObstruction.lean
