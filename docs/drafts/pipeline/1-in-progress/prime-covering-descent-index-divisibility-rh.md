# Prime Covering-Descent Index Divisibility

- **ID:** prime-covering-descent-index-divisibility-rh
- **Stage:** 1-in-progress
- **Type:** CONJECTURE (mechanism) + two support THEOREM targets (paper-provable now)
- **Lane:** Fable (`logs/rhproof-fable.md`), parity/divisibility collision cluster
- **Source:** siblings `height-adaptive-cancelled-source-socle-weyl-rh.md`,
  `multiplicity-parity-ladder-route.md`, `height-adaptive-adjacent-divisor-census-collision.md`;
  formal inputs `WeldWeylMultiplicity.lean`, `XiHeightAdaptiveAdjacentCensusCollision.lean`,
  Jensen envelope (`XiHeightAdaptiveAdjacentCensusCollision` capstone), Gohberg--Krein winding
  reading of window counts.

## Exact claim

**[CONJECTURE — covering-descent divisibility]** For each prime `p` and depth `k >= 1` there is a
source-defined Fredholm operator `D_(p,k)` attached to a `p`-adapted stack of right-half windows
(stack = `2^k` vertical translates by `theta_(p,k) = 2*pi/(2^k*log p)`, boundaries zero-free),
with **operator-valued symbol** whose fibre is the all-prime (non-`p`) source channel, such that:

1. `ind D_(p,k) = -N(stack)`, the total Xi-multiplicity in the window stack (argument-principle
   normalization);
2. `D_(p,k)` descends along the degree-`2^k` covering `w -> w^(2^k)` of the `p`-annulus
   (`w = p^(-s)`; the deck group is vertical translation by `theta_(p,k)`), i.e. `D_(p,k)` is the
   pullback of a Fredholm operator built from fractional-frequency source data (frequencies in
   `(log p / 2^k) * Z`);
3. no divisor-selected datum enters the construction (windows are chosen by height-adaptation to
   the unconditional Jensen envelope only).

Covering-index divisibility (Atiyah Gamma-index for the free `Z/2^k` deck action; elementary in
this abelian-deck case) then gives `2^k | N(stack)`. Height-adaptation puts `N(stack)` under
`2^k`, forcing `N(stack) = 0`; exhaustion gives RH.

## Why this mechanism class (route selection record)

- The Lee--Yang no-margin theorem (formalized 2026-07-16, `LeeYangForcingThreshold.lean`) +
  Rodgers--Tao `t0 = Lambda >= 0`: one-parameter monotone inequality routes are structurally
  silent at the physical point. Integer/divisibility collisions are the mechanism class immune to
  margin degeneration.
- Formal reader no-go (verified-height lane): off-line pair vs on-line double are quadratically
  indistinguishable to every bounded scalar boundary reader. The present mechanism never compares
  with on-line configurations: it lives strictly in the right half, where RH-true makes every
  count 0 and the theorem has content only against RH-false configurations — the correct logical
  geometry for a contradiction chain.
- Literature audit (2026-07-18, Fable session 1): individual off-line multiplicity parity, sqrt-Xi
  monodromy representations, and 2-divisibility descent on L-function zero multiplicities are all
  ABSENT from the literature; Ivic math/0501434 (repulsion bounds) is the only off-line
  multiplicity paper. Covering-index/K-theory realizations of window zero counts: no hits.

## Support theorem 1 — fixed-window Weyl rigidity `[TO PROVE ON PAPER — elementary]`

Let `Omega` be a bounded domain, `A` holomorphic on a neighborhood of `closure(Omega)` with
finite zero divisor `{(rho_i, m_i)}` in `Omega`, none on the boundary, and let
`Q = O(Omega)/(A) ~= directSum_i C[x]/(x^(m_i))`. Let `u = class of p^(-s)` and `M_u` its
multiplication operator. Then for a primitive `2^k`-th root of unity `zeta` (`k >= 1`):

> An invertible map `W : Q -> Q` with `W M_u W^(-1) = zeta * M_u` exists in ANY of the three
> categories — (a) `C`-linear, (b) conjugate-linear, (c) semilinear over an algebra automorphism
> of `Q` — **iff** the window divisor is invariant (in case (b), after conjugation-reflection)
> under the vertical translation `s -> s + 2*pi*i*j/(2^k*log p)` mod `(2*pi*i/log p)*Z` for the
> corresponding `j`.

Proof skeleton (case a): `charpoly(zeta*M_u)(X) = zeta^(dim Q) * charpoly(M_u)(X/zeta)`;
similarity preserves charpoly; roots multiset `{p^(-rho_i)}` (with multiplicity `m_i`, since
`u' = -log(p)*p^(-s)` never vanishes, so each local block is a single Jordan block) must be
`zeta`-rotation invariant; `p^(-rho') = zeta*p^(-rho)` unwinds to the stated shift. Case (b):
conjugate-linear conjugation conjugates the charpoly coefficients. Case (c): algebra
automorphisms of a product of truncated local rings = (local automorphism group) semidirect
permutations of equal-multiplicity points; the condition `sigma(u) = zeta*u` in `Q` forces the
point permutation to realize the same rotation on values `p^(-rho_i)` and the local parts to fix
the exponential jet.

**Consequence:** the socle--Weyl open core ("cutoff or derived reduction" carrying the Weyl pair)
cannot be discharged by ANY operator pair on the fixed window quotient in which one member is
similar into the commutative image of `O(Omega)`. This strengthens that card's kill-condition 4
and forces the reduction to change the underlying space (boundary-completed, derived, or adelic).

## Support theorem 2 — abelian descent collapse `[TO PROVE ON PAPER — elementary]`

At the scalar-symbol level the covering-descent mechanism collapses back into the rigidity no-go:

> If `xi = P * R` on a neighborhood of the closed window stack with `P` exactly
> `theta_(p,k)`-periodic and `R` zero-free-or-small-winding on the stack, then
> `N(stack) ≡ winding(R)` mod `2^k`; and if `R` is zero-free on the stack then the entire stack
> divisor is `theta_(p,k)`-periodic — the vertical-AP symmetry of Support Theorem 1.

Hence the descent operator of the main conjecture **must** have a genuinely operator-valued
(infinite-dimensional fibre) symbol: for scalar or matrix symbols the index abelianizes to a
determinant winding and the AP-rigidity re-enters. The fibre must be the all-prime/adelic channel
— exactly the socle card's requirement "integral boundary-completed or genuinely
all-prime/nonlocal" (its kill-condition 8 excludes cofinal finite-prime idealizers).

## Analytic shadow / calibration

Landau's explicit formula: `sum_(0<gamma<T) x^rho = -(T/(2*pi))*Lambda(x) + O(log T)` with
`Lambda(p^(1/2^k)) = 0` for `k >= 1` (fractional prime powers are not prime powers). The
`zeta_(2^k)`-twisted vertical window-count sums at step `theta_(p,k)` are the finite-window
reading of exactly this vanishing frequency. The conjecture asserts the operator frame upgrades
this `O(log T)`-margin statement to EXACT integer congruences — margins removed by index
integrality, not by sharper estimates. This is the precise sense in which the mechanism is not an
estimate in disguise.

## Kill conditions (hostile tests this card must survive)

1. **AP smuggling:** any construction whose fibre lift secretly periodizes the Xi divisor (e.g. a
   fibre unitary implementing the `p`-shift only on a divisor-selected subspace) is dead by
   Support Theorem 1.
2. **Abelianization:** any symbol with finite-dimensional fibre is dead by Support Theorem 2
   (matrix determinant winding).
3. **One-prime Toeplitz commutator failure:** the failed lane records `[Pi_a, G_p]` noncompact
   killing a one-prime Toeplitz index route (verified-height card). The descent construction must
   not require `[window projection, p-shift]` compact. Re-read that failed card before any
   operator choice. `[DONE 2026-07-18: see log; the PV/crossed-product frame does not need the
   compact commutator, but every concrete Fredholm module candidate must be checked against this
   exact failure]`
4. **Holonomy vacuity (socle KC7):** moving-fiber holonomy alone has no determinant consequence
   on one fixed space. The covering-descent argument must produce an index identity on ONE
   Fredholm operator, not a holonomy narrative along the orbit.
5. **Divisor selection:** windows adapted to anything but the unconditional Jensen envelope are
   inadmissible.
6. **Hidden restatement test:** if the first open sub-theorem (descent existence) is shown to
   already imply RH through a shorter existing corpus branch, this card is a restatement and must
   be retired (lesson: ccm-pointed-incidence-rayleigh failure).

## Open cores (ordered)

- `[OPEN CORE 1]` Paper-prove Support Theorems 1 and 2 exactly as stated (elementary; no RH
  content; they are the search-space theorems).
- `[OPEN CORE 2 — DISCHARGED 2026-07-18]` One-prime periodic model: contained in Support
  Theorem 2(i) of the sibling card
  (`fixed-window-weyl-rigidity-abelian-descent-collapse.md`): any `theta_(p,k)`-periodic scalar
  symbol zero-free on the stack boundary has `winding_{∂S} = 2^k * winding_{∂Omega_0} ≡ 0
  (mod 2^k)`. The rotation-equivariant Toeplitz dressing adds nothing at the abelian level
  (Theorem 2(iii)); no separate calibration theorem is needed.
- `[OPEN CORE 3]` Construct the operator-valued-symbol candidate: fibre = completed non-`p`
  source channel; base = `p`-annulus with `Z/2^k` rotation; total operator Fredholm with index
  `-N(stack)`; identify the exact descent obstruction as a concrete cocycle/class and measure it
  against source identities (corpus decimation laws: BV square-index decimation
  `p_j(N) = p_(j-2)(r^2*N)`, dyadic sharp-window tomography). THIS is the RH-bearing step; expect
  it to fail informatively — the failure class is the next theorem.

## OPEN CORE 3 working notes (2026-07-18, session 1)

The covariance structure exists and is canonical; the descent defect is a concrete monodromy.

1. **Exact covariance.** Vertical translation by `theta = theta_(p,k)` acts on Dirichlet/adelic
   data as twisting by the idele-class character `n ↦ n^{-i*theta}`: each Euler factor obeys
   `(1 - q^{-s-i*theta})^{-1} = (1 - chi(q) q^{-s})^{-1}` with `chi(q) = q^{-i*theta}`. So for a
   symbol `A(s)` built from the full source channel there is a FIBRE UNITARY
   `U_theta = mult by n^{-i*theta}` with `A(s + i*theta) = U_theta A(s) U_theta^*` — exact
   translation-covariance with unitary twist, no periodicity assumption. This evades Support
   Theorem 2's collapse: nothing scalar is periodic, and no determinant exists on the
   infinite-dimensional fibre.
2. **The descent defect is a residual monodromy.** The deck step closes after `2^k` steps ONLY on
   the `p`-modes: `R := U_theta^{2^k} = mult by n^{-2*pi*i/log p}` is the identity exactly on
   powers of `p` (`p^{-2*pi*i*m/log p} = 1`) and nontrivial on every other mode
   (`q^{-2*pi*i/log p} ≠ 1` for `q ≠ p`). Descent is therefore to a MAPPING TORUS with monodromy
   `R`, not to a product; covering-index divisibility acquires a correction term = an index /
   spectral-flow invariant of `R` on the non-`p` fibre.
3. **Where the arithmetic enters.** The spectrum of `R` is `{exp(-2*pi*i*log n/log p)}`:
   the correction invariant is governed by the distribution of `log q / log p mod 1` — prime-log
   rational independence, which THIS corpus has already formalized
   (`StieltjesLogWeldTierOne.lean`: affine independence of `{1} ∪ {log p}` via in-tree
   `exp_int_irrational`; `linearIndependent_log_primes`). The divisibility defect is thus not an
   analytic estimate but an arithmetic-rigidity invariant with existing Lean substrate.
4. **Next exact sub-questions (in order).**
   (a) Fix the fibre: weighted `ell^2` over non-`p` integers (or the corpus's completed
   prime--Gamma channel) and a symbol class where window-Toeplitz compressions of `A` are
   Fredholm with `ind = -N(window)` — the operator-valued Gohberg--Krein step. Check against the
   failed one-prime Toeplitz commutator card (`[Pi_a, G_p]` noncompact) — the mapping-torus frame
   must not need that commutator compact.
   (b) Compute the mapping-torus index-divisibility correction as a function of `R` in the
   simplest nontrivial model (two primes `p, q`; fibre = `ell^2` of `q`-powers; `R = mult by
   q^{-2*pi*i*m_j/log p}` diagonal). Exact toy theorem wanted: index mod `2^k` = explicit
   functional of the `R`-spectral flow, reducing to 0 when the flow is trivial.
   (c) Only then: does any source identity (decimation laws, square-index BV decimation) make the
   correction vanish or become computable for the actual Xi symbol? If the correction is
   generically nonzero and uncontrollable, record the exact failure mechanism — that failure
   class is itself the next theorem (relentless-interrogation step).

## Gates

- [x] 0 -> 1 in-progress: well-posed, source-pure, attack plan, no-go compliance recorded
- [ ] 1 -> 2 fully-proven (support theorems may move independently as a split card)
- [ ] 2 -> 3 formalized
- [ ] 3 -> 4 publication-ready

## Log

- 2026-07-18 (Fable session 1): card created. Derivation chain: socle-Weyl open core ->
  fixed-window Weyl rigidity (new no-go) -> annulus/rotation reading of the Weyl phase ->
  covering-index divisibility as the non-margin producer -> abelian collapse -> operator-valued
  fibre forced. Literature audit: mechanism class absent from the literature (see
  `logs/rhproof-fable.md` session-1 audit records).

## 2026-07-18 session 1 (cont.) — T3: covariant-symbol blindness; mechanism reclassified

**[T3 — TO PROVE ON PAPER, proof sketch complete]** Let `A(s)` be an operator-valued Fredholm
symbol on the window stack, invertible on every window boundary, EXACTLY covariant:
`A(s + i*theta) = U A(s) U*` for a fixed fibre unitary `U`. Then for every `j`, the window
Toeplitz compression satisfies `T_{A|window_j} = (conj by U^j) T_{A|window_0}` up to the
contour reparametrization `s -> s + i*j*theta`, hence ALL window indices are equal and
`ind(stack) = 2^k * ind(window_0)` — divisibility for free, BUT the window index is constant
across the stack. Since actual Xi window counts `N(window_j)` are not constant, no exactly
covariant symbol can satisfy `ind T_{A|window_j} = -N(window_j)`. Exact covariance is as
divisor-blind as periodicity: the index rigidity that produces the divisibility simultaneously
destroys the divisor identification.

**Classification consequence (relentless interrogation of T1+T2+T3).** The three theorems close
the entire symmetry-transport family for the Weyl/covering mechanism:
- T1: fixed-window operator conjugation — requires divisor AP symmetry (dead);
- T2: periodic/descended scalar or finite-fibre symbols — winding abelianization, requires the
  same AP symmetry (dead);
- T3: exactly covariant infinite-fibre symbols — index constancy contradicts divisor
  sensitivity (dead).
A Weyl pair exists iff `2^k | dim` (socle KC1, tautology); T1-T3 prove every natural symmetry
implementation of that tautology on the zeta divisor is blocked. **The surviving producer class
for integer divisibility is non-symmetric: exact source RECURSIONS/census identities** — e.g. a
completed-source finite-ring census value per height (the DISC-census open core) or exact
decimation relations `N(scale r^2 X) vs N(scale X)` where divisibility emerges from a recursion
rather than a group action. This is a rigorous narrowing of the whole parity cluster's search
space: the census-scalar construction is not one option among many; it is the unique survivor
of the mechanism family.

**Next concrete target.** (i) Write T3's proof rigorously (Toeplitz-compression bookkeeping;
elementary). (ii) Re-read `height-adaptive-adjacent-divisor-census-collision.md` +
`XiHeightAdaptiveAdjacentCensusCollision.lean` to state the census scalar's exact required
identity, now with the T1-T3 classification as design guardrails (no symmetry ansatz can work;
the scalar must come from a finite-ring/recursion identity of the source). (iii) Candidate
starting identity: the corpus's formalized BV square-index decimation
`p_j(N) = p_{j-2}(r^2 N)` — an exact termwise recursion already carrying a square-index (depth-2)
structure; question: does its Laurent-character form on zero fibres
(`R_j/R_{j-2} = r^{2 rho - 1}`) admit a finite-ring reduction whose obstruction to consistency
at depth `2^k` is the census scalar?
