# Arithmetic coherence: physics attack on bounded returns

- ID: ULF-MHBR-001-PHYS
- Stage: 1-in-progress; physics interpretation and proof-strategy audit, not a proved new field.
- Parent claim remains ULF-MHBR-001: C_N(r)<=0 for all N, r>=1 [CONJECTURE].
- Weaker required endpoint: bounded upper returns for r>1 arbitrarily close to 1 [OPEN CORE].
- No new unconditional RH estimate obtained. No numerical evidence promoted to proof.

## What the existing physics research actually says

[LOCAL-RESEARCH] Read `4-publication-ready/universal-quantum-recurrence-anatomy/main.tex`,
the complete `body.tex`, proof audit, claim trace, hostile review and singular-completion blueprint.
The current manuscript is **Persistent phase geometry of quantum recurrence** (24 August 2026).
Older blueprints are not the current manuscript. Its factorization is persistent carrier ->
relation hull -> weighted metric -> observer quotient, with a separate finite-inference boundary.

[CORPUS] Six load-bearing declarations were re-audited with `lake env lean` in
`/tmp/hgt_physics_recurrence_audit.lean`; all passed, axioms only
`propext`, `Classical.choice`, `Quot.sound`:

- `RHTower.exists_phase_fisher_blind_with_prescribed_zero`:
  unimodular Euler twists retain every Born probability and energy-observable Born variance
  while admitting prescribed Helson zeros. This is not blindness of every interferometric QFI.
- `RHTower.exists_infiniteJetQuantumRecurrenceSeparation`:
  an indeterminate normalized Hamburger class admits recurrent and dispersive completions
  with identical complete local-time jets. Compact moment determinacy is not contradicted.
- `RHTower.quantumRecurrenceGlobalCompletionWitness`:
  positive-energy all-depth Jacobi data and, separately, all-order perturbative data on a
  compact positive spectrum need not select persistent recurrence.
- `RHTower.finite_quantum_observer_coherence_law`:
  observed return is an exact weighted edge-phase energy; capacity is vertices minus components.
- `GaloisForLFunctions.HTGeometry.exists_quditPath_everyChart_sameDraw_recurrenceCollisionLaw`:
  generic static nearest-neighbour qudit paths have maximal rank, sharp clock exponents and
  all-order collision floors. Local support does not force small recurrence rank.
- `GaloisForLFunctions.HTGeometry.pureGeneratorQuantumFisher_collective_eq_four_mul_sum`:
  collective pure-state QFI is four times the full covariance sum, not just its diagonal.

[LOCAL-RESEARCH] `DiscreteTimeCrystalSpinChain.lean` records exact ideal spin flips,
period doubling and collective-QFI algebra. Its header explicitly does not formalize a numerical
phase diagram, robustness under imperfect driving, or a thermodynamic time-crystal phase.

## Primary physics sources and transferable mechanisms

- [2609.03539](https://arxiv.org/pdf/2609.03539), equations (17)--(23): a perturbative plasma
  reduction yields two counter-propagating KP equations and a Hirota bilinear representation.
  Useful question: does a nonlinear coupled evolution create an exact conservation law?
  No arithmetic evolution or Möbius-energy bound is provided by this paper.
- [2609.04037](https://arxiv.org/html/2609.04037v1): finite-chain numerical DTC study;
  ideal flip algebra and empirical persistence under pulse errors are different claims.
- [2508.15448v2](https://arxiv.org/html/2508.15448v2), published
  [September 2026](https://www.nature.com/articles/s41534-026-01331-x): global metrological
  information includes system and monitoring history. Enhanced rate is controlled by slow
  Liouvillian response; gap closing and non-normality must not be replaced by an equal-time QFI.
- [2103.02619](https://arxiv.org/html/2103.02619): a quantum comb retains interventions and
  memory, not just endpoint states. Its finite-dimensional optimization does not supply a
  uniform infinite-arithmetic resource bound.
- [1309.6620v4](https://arxiv.org/abs/1309.6620v4): postselected precision must include success
  probability and failed trials in its resource accounting. A normalized rare branch is not free.
- [2404.11503v2](https://arxiv.org/html/2404.11503): hypocoercivity transfers an undamped
  component into damped directions through Hamiltonian motion. Its microscopic/macroscopic
  coercivity, compatibility and boundedness hypotheses must be derived, not declared.
  Related space-time formulation: [2406.09115](https://arxiv.org/abs/2406.09115).

## Exact metrological reframing [BRIDGE; specialization not Lean-formalized]

For r>0 work in C|0> direct-sum L2((0,infinity),dx). Set

    f_n(x)=x^((r-1)/2) exp(-nx),
    X_n=mu(n)(|f_n><0|+|0><f_n|),
    G_N=sum_(n<=N) X_n.

The vacuum is unit and orthogonal to every f_n. Each X_n is bounded self-adjoint and
has zero vacuum mean. The Gamma integral gives

    <f_m,f_n>=Gamma(r)/(m+n)^r,
    F_Q(|0>,G_N)=4 E_N(mu;r),
    sum_(n<=N) F_Q(|0>,X_n)=4 D_N(r),
    F_Q(|0>,G_N)-sum_(n<=N)F_Q(|0>,X_n)=4 C_N(r).

Derivation: G_N|0>=sum mu(n)f_n; pure-state unitary QFI is four times generator variance.
Replacing all f_n by mutually orthogonally labelled copies removes exactly the cross terms.
This compares two coupling geometries; it is NOT a free CPTP erasure operation on one fixed
experiment, and the diagonal sum is NOT automatically a bound on total preparation cost.

Thus the frozen conjecture says the arithmetic coupling pattern is never collectively
super-enhancing relative to its distinguishable-mode baseline. Bounded returns require only
cofinally bounded excess enhancement. This is an exact physical interpretation of the old claim,
not a second proof or a new conjecture manufactured by renaming it.

## Hostile loop and representation lessons

1. **Fixed-system quantum recurrence supplies cutoff returns.** Invalid application:
   time t->infinity at fixed N is not N->infinity. The manuscript explicitly orders completed
   time before growing size. Positive survivor: it identifies the precise joint-limit obligation;
   its recurrence and observer laws remain usable only after a same-process identification.
2. **Bound QFI using diagonal information or finite local geometry.** Rejected as a universal
   argument by the audited blindness/separation laws. Coherent phase-sensitive interventions
   survive this objection, but their complete covariance is an extra quantity to control.
3. **Use the QFI interpretation itself as an upper bound.** Rejected: replacing mu(n) by 1
   gives E_N>=Gamma(r)N^2/(2N)^r, which diverges for 0<r<2, whereas D_N stays bounded for r>1.
   Finite diagonal resource alone therefore cannot imply the required collective bound.
   Survivor is the exact distinction between collective and label-resolved coupling, not selection.
4. **A KP name or a time-crystal phase is the missing law.** No producer identified:
   neither literature result constructs the unchanged arithmetic signal or controls its cutoff.
   A valid nonlinear embedding must impose extra source-specific identities, not merely encode
   the already known exponential sum in more variables.

## Mechanism to investigate, not yet a well-typed new conjecture

**Dynamical removal of dark directions, with the complete arithmetic history retained.**
The relevant physics is hypocoercivity, not static positivity. The corpus has an exact dark
direction: same-sign Gibbs dissipation vanishes when currents at x and px are opposite.
Such a direction may remain undamped at one step while a different physical evolution moves it
into a damped direction. This is what a genuine interaction law would have to demonstrate.

Arithmetic hard-cutoff formation must be used. If

    J_(S,N)(x)=sum_(T subset S, product(T)<=N) (-1)^|T| exp(-x product(T)),

then for a new prime p the coefficient identity is

    J_(S+p,N)(x)=J_(S,N)(x)-J_(S,floor(N/p))(px).

The second term changes BOTH scale and cutoff. It is not the untruncated same-aperture Euler
multiplier. Product(T)<=N keeps the actual integer prefix; independent aperture formation can
retain a large tail of products exceeding N. This identity is elementary and not counted as new.

First discriminating question: do these actual boundary transfers move antiscale null directions
into dissipative ones with a quantitative estimate that survives cofinal cutoffs?
Adding arbitrary noise, averaging unrelated Euler phases, or assuming a Lindblad gap does not
answer it: each changes the source or inserts the missing estimate.

[OPEN CORE] No source-derived evolution, hypocoercive estimate or preparation-work identity is
yet constructed. The physics analogy does not authorize calling one proved or asserting a new
universal law. Its first valid quantitative estimate must bound the SAME unnormalized E_N along
arbitrarily large cutoffs; subtracting the already bounded diagonal then supplies C_N's returns,
and the existing Mellin--Plancherel implication closes RH. If it only bounds a normalized state,
a different phase average, or fixed-N long-time response, it has not reached that implication.

## Exact cutoff-transfer attack: ULF-HCTI-001 [LEAN-PROVED bridge]

`GibbsHardCutoffTransport.lean` tests the proposed extra cutoff motion. The literal operators
`T_p F(N,x)=F(N div p,px)` satisfy `T_p T_q=T_(pq)=T_q T_p`. Thus `D_p=I+T_p`
commutes with every constant-coefficient signed insertion `I-T_q`; the floor has not supplied
an independent noncommuting transport. This falsifies that specific proposed realization,
not hypocoercivity with additional operators or variable Gibbs hazards.

Positive survivor: integer birth has exact incidence
`Delta T_p F(N,x)=1_(p divides N+1) T_p Delta F(N,x)`. Same-sign seam data with zero
initial boundary are injective and reconstruct the history by a finite alternating sum.
This algebraic injectivity is insufficient quantitatively: for every p>=2,
`F_p(N,x)=(-1)^floor(log_p N)(floor(log_p N)+1)` at N>0, zero at N=0, has
`|D_p F_p|<=1` everywhere but `|F_p(p^K,x)|=K+1`. One fixed history works at every depth.

This is not a Möbius counterexample and says nothing by itself about its Gamma--Hankel norm.
It prevents the specific inference from bounded seams/absence of exact dark modes to a
cutoff-uniform bound. Paper proof and certificate:
`3-formalized/universal-law-field/hard-cutoff-transport-incidence.md`.
No upper bound for C_N(r) obtained. STATUS F650--651/CANNOT-292 record the exact scope.
The next candidate must retain actual integer births and establish a quantitative estimate
for their arithmetic history; generic subdivision already fails by CANNOT-291. Merely
renaming birth incidence as a Hamiltonian is not a replacement conjecture.
