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

## 2026-07-18 session 1 (cont. 2) — census scalar identified as subresultant rank; next conjecture

Census/decimation audit (readers over `XiHeightAdaptiveAdjacentCensusCollision.lean`, DiscJump,
WindowLadder, `BVPrimeWindowDilationOrientation.lean`, both decimation cards) + synthesis:

1. **Exact reduction of the census open core.** With `A` = shifted Xi and `C` =
   `dyadicSharpPrimeCancelledSource` on the shifted box: at every shifted Xi zero
   `min(ord_A, ord_C) = min(m, m-1) = m-1`, and at every extra `C`-zero `A ≠ 0` gives `min = 0`.
   Hence `boxCancelledSourceCommonOrderSum = sum min(ord_A, ord_C)` — the census scalar IS the
   gcd-degree / intersection mass of the source pair `(A, C)`.
2. **Winding split.** `boxDistinctCount = [winding(xi, box) - winding(C, shifted box)] + X_C`,
   where both windings are source-pure boundary integrals and `X_C` = non-incident `C`-mass.
   All target-sampling is concentrated in the incidence split of `winding(C)`; the raw
   boundary-pair homotopy no-go (census card) says homotopy classes cannot see it — but
   SUBRESULTANT/BEZOUT data is finer than homotopy: for polynomials `deg gcd` is computed from
   coefficients by subresultant vanishing, with no root enumeration. The census card's own
   replacement mechanism ("Fitting/subresultant module of (zero algebra, L_C)") is exactly this;
   the classical machinery is now named.
3. **[CONJECTURE — dyadic subresultant census]** There is an analytic Sylvester/Bezout operator
   `S(A, C)` on window boundary data (Fredholm; kernel dimension = `sum min(ord_A, ord_C)` =
   census mass, by the analytic-subresultant argument principle), constructed from the completed
   prime--Gamma/sharp-window source WITHOUT zero enumeration; and the DYADIC self-similarity of
   `C` — the formalized square-index decimation `p_j(N) = p_{j-2}(4N)`
   (`weightedPrimeWindow_argumentDilation_eq_argumentExpansion_sq_mul`,
   `polarCoefficient_argumentDilation_eq_argumentExpansion_sq_mul`) — induces on `S(A, C)` a
   filtration whose graded pieces recur with period dividing 2, so that
   `dim ker S(A,C) mod 2^k` is computable by the decimation recursion at depth `k`. The
   height-adaptive census equality then follows from a finite recursion of source identities,
   which is the non-symmetric producer class that survives T1-T3.
   - This respects the census card's kill conditions: nothing is sampled at Xi zeros (kernel
     dimension of a source operator); no boundary-pair homotopy invariant is used (subresultants
     are strictly finer); no symmetry/transport enters (recursion, not group action).
   - `[OPEN CORE]` (first exact sub-target): construct the analytic Sylvester operator for a pair
     of holomorphic functions on a window with the kernel-dimension = intersection-mass property,
     in a form where `A, C` enter only through boundary data / source coefficients. Literature to
     audit first: analytic Bezoutians (Krein--Naimark, Anderson--Jury), Fredholm-minor
     subresultants, and the corpus's own Hedenmalm source Bezoutian surface.
   - Hostile risks to test at Gate 3: (i) the analytic Sylvester kernel may compute
     `sum min` only for FINITE divisor mass with a priori separation — check ill-posedness under
     zero collision (the collision-degeneracy no-go!); (ii) the dyadic filtration may act on the
     `C`-side only, leaving the `A`-side (Xi) unfiltered — the graded recursion must not need a
     matching Xi self-similarity (Xi has none; T2/T3 forbid importing one); (iii) mod-2
     periodicity of graded ranks must come from an exact source identity, not from an assumed
     regularity of the filtration.

## 2026-07-18 session 1 (cont. 3) — support card refereed and PROMOTED

Independent fresh-context hostile referee confirmed T1/T2/T3 bodies; four statement fixes
applied (T1 pairs-multiset equivalence + category-(b) corollary scope restriction with
reflection counterexample; T2 zero-freeness scope + rectifiability; T3 step domains + exact
Gohberg--Sigal citation). Support card moved to
`2-fully-proven/not_new_scientific_knowledge/fixed-window-weyl-rigidity-abelian-descent-collapse.md`.
Scope note for this card's kill-conditions: category (b) (conjugate-linear) forces a REFLECTION
symmetry rather than divisibility — still unsuppliable by a source theorem, so kill-condition 1
stands in all categories, with (b) via reflection rather than AP rotation.

## 2026-07-18 session 1 (cont. 4) — Gate-3 verdict on the dyadic-subresultant conjecture

**Verdict: SURVIVES PRELIMINARY ATTACK, with the analytic-Sylvester existence core DISCHARGED BY
LITERATURE IMPORT and one sharp new instantiation core.**

1. `[LITERATURE — verified, PDF in session scratchpad gl1978b.pdf]` Gohberg--Lerer, Proc. AMS 72
   (1978) 65-73: resultant operators for analytic pairs. Annulus Theorem 2 and strip Theorem 3:
   `dim Ker W(A,B) = sum over common zeros of min(ord_A, ord_B)` (their "common multiplicity" is
   forced to be min by Ker W(A,B) = Ker W(A) ∩ Ker W(B) with Jordan-chain bases
   `t^p exp(-i z_j t)`), with the operator built from Laurent coefficients / L1 densities plus
   boundary winding numbers ONLY — no zero enumeration. Shifted family `W_l = W(A, z^{-l}B)` has
   descending stabilizing kernels (their Prop. 1) — a ready-made filtration. Also:
   Krein (unpublished, via Sakhnovich arXiv:0905.1351, Thm 4.2: operator Bezoutiant with
   `dim ker = #common zeros`, coefficient-data only) and Gohberg--Heinig (Acta Math. Hungar. 28
   (1976); OT 206 translation), matrix case clarified in Gohberg--Kaashoek--Lerer 2005-2010
   under quasi-commutativity. "Analytic subresultant chains" (graded gcd filtration for analytic
   pairs): literature EMPTY — the shifted-kernel filtration as a subresultant chain is unclaimed
   territory.
2. `[COLLISION RISK RESOLVED]` The census card's epsilon no-go kills only invariants factoring
   through the boundary-pair homotopy class; `dim ker` is upper-semicontinuous and its collision
   jump (P: 0->1, D: 2->1, M stable) is the classical gcd-onset rank drop with index preserved
   (coker jumps in lockstep). Recorded corpus no-gos (verified-height "collision degeneracy",
   completed-source-window-index-amplifier, sem-collision) all kill CONTINUOUS scalar readers and
   deformation-stable functionals; quantized semicontinuous integer readers are the recorded
   survivor class, and the Sylvester kernel dimension is one. Design constraints: never claim
   homotopy invariance; never route the census comparison through a functional continuous along
   the slaved collision family `(A_t, C(A_t))`; the height-adaptive `∃k` absorbs T-growth only —
   collision robustness must come from the semicontinuous rank object itself.
3. `[CORPUS REUSE INVENTORY]` `xiHedenmalmBezoutian z v = dslope (fun w => deriv XiC z * XiC w -
   XiC z * deriv XiC w) z v` (XiHedenmalmDeBrangesSeam.lean) with off-diagonal orthogonality at
   distinct zeros, `diagonal = (deriv XiC)^2` at zeros, and the simplicity gate
   `xiHedenmalmBezoutian_self_ne_zero_iff_simple`; `resultant_specialize_analytic`
   (U0PhiCard.lean:312) for analytic Sylvester-determinant families;
   `sigNeg_le_of_add_sum_sq_nonneg` (KreinLangerInertia.lean). Constraint from
   5-failed/joint-source-represented-matroid-transport-rh.md: common-zero mass must NOT be
   encoded as finite-packet Gram rank-drop (free-matroid stabilization no-go); the kernel must
   be carried by divisor-multiplicity fibers, as GL's Jordan-chain bases do.
4. `[NEW OPEN CORE — the instantiation gap]` GL's classes require the symbol to tend to a
   nonzero constant at strip infinity (Riemann--Lebesgue confines common zeros to a compact
   set, making `dim ker` finite). But: (i) Xi DECAYS on vertical lines (`xi(1/2+h+iz) =
   integral Phi(u) e^{hu} e^{izu} du`, `Phi` double-exponentially decaying, so Xi is in the
   strip class EXCEPT for the "1 +" normalization and has infinitely many strip zeros); (ii)
   the dyadic cancelled source is an almost-periodic Dirichlet symbol (atoms at `log n`
   frequencies — AP Wiener--Hopf territory, Bottcher--Karlovich--Spitkovsky). The required new
   theorem: a kernel-dimension = common-mass law for pairs (Xi-decay class) x (AP-Dirichlet
   class) on finite-height boxes or normalized substrips. Candidate normalizations to attack
   first: (alpha) divide by the archimedean factor (A = zeta; boundary-line lower bounds fail at
   infinity — quantify exactly where); (beta) finite-height boxes = truncated/finite-section WH
   operators (no clean kernel theorem — the finite-section kernel-dim behavior IS the new
   mathematics); (gamma) horizontal-shift ratio normalizations `xi(s)/xi(s+delta)` with
   polynomial decay compensators (branch bookkeeping on boxes). This gap is where the lane's
   next Gate-2/Gate-4 cycle lives.

## 2026-07-18 session 1 (cont. 5) — Gate-2 sharpened: the pair-ideal census (T4) and the
## source-defined congruence

**Resolution of the instantiation gap by domain finiteness.** The (Xi-decay x AP) class problem
was an artifact of infinite strips. On a finite box the correct carrier is the PAIR-IDEAL
QUOTIENT, and the kernel-dimension law is elementary:

**[T4 — TO PROVE ON PAPER, elementary]** Let `Omega` be a bounded domain with rectifiable
boundary, `A, C` holomorphic on a neighborhood of `closure(Omega)`, with finite zero divisors
and no zeros of `A*C` on `∂Omega`. Then, with `(A, C)` the ideal generated in `O(Omega)` (or in
`O(nbhd(closure Omega))`):

> `dim_C O/(A, C) = sum over z in Omega of min(ord_A z, ord_C z)`.

Proof route (no corona needed): local colength `(z^a*unit, z^c*unit) = (z^{min(a,c)})`; global
reduction via `G :=` the gcd-divisor polynomial `prod (z - z_j)^{min_j}`, `A = G*A_1`,
`C = G*C_1` with `(A_1, C_1)` common-zero-free on the compact closure; Hermite finite
interpolation constructs `f_2` polynomial with `C_1*f_2 - 1` vanishing to `ord_{A_1}` at each
`A_1`-zero, so `f_1 := (1 - C_1 f_2)/A_1` is holomorphic and `A_1 f_1 + C_1 f_2 = 1`; hence
`(A, C) = (G)` and `dim O/(G) = deg G` by the T1-setup jet isomorphism. All steps are
Lean-grade elementary complex analysis / linear algebra.

**Instantiation.** With `A` = shifted Xi on the census box and
`C = dyadicSharpPrimeCancelledSource` (formalized order law: `ord_C = ord_A - 1` at every
`A`-zero; extra `C`-zeros have `A ≠ 0`, contributing `min = 0`):

> `dim O/(A) = boxOrderSum = M(T)`  and  `dim O/(A, C) = sum(m-1) = P(T)`.

Both are dimensions of quotients DEFINED from the pair of source functions alone — no Xi zero
enumeration enters either definition. This repairs the census card's recorded defect ("the Lean
object `cancelledSourceCommonCensusH` is not yet a source boundary invariant: it evaluates the
explicit cancelled source at the target-defined Xi box points"): the pair-ideal quotient IS the
source boundary invariant, and the target-sampled sum is the THEOREM about it (T4), not its
definition.

**Sharpened remaining core (the RH-bearing congruence, now fully source-typed):**

> `[OPEN CORE]` Prove `dim O/(A) ≡ dim O/(A, C) (mod 2^k)` at height-adapted depths — a
> congruence between two ideal-quotient dimensions — from the arithmetic structure of the pair,
> WITHOUT computing either dimension. Design guardrails: T1-T3 forbid any symmetry/covariance
> transport; the collision analysis requires the mechanism to be semicontinuous-integer-valued
> (ideal-quotient dimensions are); the dyadic decimation
> `p_j(N) = p_{j-2}(4N)` acting on the modules `O/(A, C_scale)` across adjacent dyadic scales is
> the designated candidate: seek an exact sequence of pair-ideal modules across one dyadic step
> whose alternating dimension sum is divisible by 2, iterated to depth k.

Next actions: (1) paper-prove T4 (short); (2) window-model Lean batch: T4's algebra + the
`O/(A)` jet machinery shared with T1; (3) construct the dyadic-step exact sequence candidate on
paper and attack it hostilely (does the decimation act on the IDEAL (A, C_scale) or only on C's
coefficients? — the fracture point to find first).

### T4 — complete proof (first pass, 2026-07-18)

Shrink the neighborhood `U` of `closure(Omega)` so that: (i) `A*C` has finitely many zeros in
`U` (isolated zeros + compactness), (ii) every common zero of `(A, C)` in `U` lies in `Omega`
(possible since there are none on `∂Omega`; discard an outer shell containing any others).
Let `{(z_j, a_j, c_j)}` be the common zeros in `Omega` with their orders and
`G(z) := prod_j (z - z_j)^{min(a_j, c_j)}`.

1. `A_1 := A/G` and `C_1 := C/G` are holomorphic on `U` (at `z_j`, `G`'s order `min(a_j,c_j)`
   is at most `a_j` resp. `c_j`; removable singularities), and `(A_1, C_1)` have NO common
   zeros in `U`: at `z_j` one of the two has order exactly `0` after division (whichever
   attained the min... if `a_j = c_j` both become nonzero? no: both orders drop by
   `min = a_j = c_j`, both become nonzero — fine, even better); away from the `z_j` a common
   zero of `(A_1, C_1)` would be a common zero of `(A, C)` in `U \ Omega` — excluded by (ii).
2. **Hermite--Bezout.** `A_1` has finitely many zeros `w_i` in `U` with orders `d_i`, and
   `C_1(w_i) ≠ 0` (no common zeros). Choose by Hermite interpolation a polynomial `f_2` whose
   jet at each `w_i` agrees to order `d_i` with the jet of `1/C_1` (defined near `w_i` since
   `C_1(w_i) ≠ 0`). Then `1 - C_1 f_2` vanishes to order `>= d_i` at each `w_i`, so
   `f_1 := (1 - C_1 f_2)/A_1` is holomorphic on `U`, and `A_1 f_1 + C_1 f_2 = 1`.
3. **Ideal equality.** Multiplying by `G*h` (`h in O(Omega)` arbitrary):
   `G*h = A*(f_1 h) + C*(f_2 h)`, so `(G) ⊆ (A, C)` in `O(Omega)`; conversely `G | A` and
   `G | C` give `(A, C) ⊆ (G)`. Hence `O(Omega)/(A, C) = O(Omega)/(G)`.
4. **Dimension.** The jet map `O(Omega) -> directSum_j C[z]/((z - z_j)^{min_j})` is surjective
   (polynomial Hermite interpolation) with kernel exactly `G * O(Omega)` (a function vanishing
   to order `min_j` at every `z_j` divided by `G` has removable singularities). Therefore
   `dim O(Omega)/(A, C) = sum_j min(a_j, c_j)`. QED

Label: `[PROVED HERE, first pass — pending fresh-context referee before promotion]`. Note the
proof nowhere uses properties of Xi or the dyadic source beyond holomorphy near the closed box
and boundary nonvanishing; the instantiated identities `dim O/(A) = M(T)`,
`dim O/(A,C) = P(T)` then follow from the formalized order law `ord_C = ord_A - 1` on the Xi
box divisor (census card input) plus T4.

### T4 referee pass (2026-07-18, independent fresh context) — CONFIRMED, one fix applied

All six attack items CONFIRMED (accumulation impossible once U is chosen connected with compact
closure and finitely many A*C-zeros — stated explicitly now; "rectifiable" vestigial for T4
itself; off-by-one in Hermite order checked under both jet conventions; Bezout restriction and
removability fine for arbitrary bounded domains). One exposition gap fixed here:

**Fix (dim O/(A) = M(T)).** Apply T4 with the pair `(A, A)`: hypotheses hold, `(A, A) = (A)` as
ideals, and `sum min(ord_A, ord_A) = sum ord_A`. Hence `dim O(Omega)/(A) = boxOrderSum = M(T)`
— no separate jet argument for nonpolynomial `A` is needed; both instantiated identities now
follow from T4 alone plus the formalized order law `ord_C = ord_A - 1`.

Label upgraded: **T4 `[PROVED HERE]` — refereed.** Ready for the Lean batch (T4 algebra shares
T1's jet machinery; the `(A, A)` trick keeps the formalization surface minimal).

## 2026-07-18 session 1 (cont. 6) — ideal-sequence candidate KILLED; Rees-graded replacement

**[FALSIFIED — exact-sequence-of-ideals carrier]** Fracture verified against the live Lean:
(1) `dyadicSharpPrimeCancelledSource` (CCMSharpPrimeWindowCancellation.lean:11) is ONE fixed
function — window hard-coded via `sharpPrimeWindowMellin (Real.log 2)`; no scale family exists.
(2) The decimation (BVPrimeWindowDilationOrientation.lean:164-181) is coefficientwise on
`ℕ`-indexed sequences, `n` vs `r^2*n`; the non-surjectivity of `n ↦ 4n` (invisible `4∤n` data)
is the genuinely 2-adic content and is index-arithmetic — extracting the residue class `4|n`
needs additive twists `e^{2πi j n/4}` which are NOT multiplication operators in the s-domain, so
no `O(Omega)`-linear map exists. (3) The only function-level shadow is
`M[W_dil] = (r^2)^{s-1} * M[W_exp]` — a UNIT of `O(Omega)`, and `(A, u*C) = (A, C)`: the
induced ideal map is the identity; alternating dimension sum 0; no mod-2 content. Killing
mechanism recorded: the decimation's content lives one level below holomorphy (coefficients),
its holomorphic shadow one level above (units); the ideal quotient sits exactly between and
sees neither.

**[CONJECTURE — Rees-graded finite-section census]** (failure-driven replacement; absorbs the
kill by moving the carrier to where the coefficient data lives.) For the census pair `(A, C)`
on a height-adapted box there is a family of finite-section Sylvester/Wiener--Hopf operators
`S_{l}` (Gohberg--Lerer shifted kernels / dyadic truncations of the coefficient action) such
that: (i) `dim ker S_l` is nonincreasing and stabilizes at the census mass
`P(T) = dim O/(A, C)` (finite-section analogue of GL Prop. 1 — the "new mathematics" flagged at
cont. 4, now fused with the carrier); (ii) the coefficient decimation induces the degree shift
`(l, j) ↦ (4l, j-2)` on the family, making the associated Rees module a graded module over
`C[t]` with the two-step shift = multiplication by `t^2`; (iii) in a source-controlled degree
range the graded pieces are `t^2`-free, so alternating/graded dimension sums are even, and `k`
iterations give the census congruence `M ≡ P (mod 2^k)` at height-adapted depths.
- Next fracture point to hunt FIRST (hostile): (iii)-freeness — `t^2`-torsion of the Rees
  module is precisely where the arithmetic could re-enter as an unprovable hypothesis. Find
  what torsion MEANS for the pair (Xi, dyadic source): expected answer — torsion classes are
  carried by the `4∤n` residue data (the off-multiple layer with its universal residue fraction
  `1 - r^{-2}`, paper-proved on the decimation card), so the torsion computation may reduce to
  the formalized off-multiple layer law. If torsion is uncontrollable, record the exact class
  and interrogate again.
- Guardrail compliance: finite-section kernels are semicontinuous integers (collision-safe);
  no symmetry transport (the shift is a filtration degree map, not a group action); kernel
  data indexed by divisor fibers via GL Jordan-chain bases (free-matroid-safe).

## 2026-07-18 session 1 (cont. 7) — torsion verdict: free cutoff direction, A-side cocycle
## fracture, bigraded Koszul replacement, and the multiplicative/archimedean split

Torsion analysis (independent agent, derivation-level):
1. `[PROVED (model level)]` The cutoff Rees module over `C[t^2]` is FREE: torsion = 0; the
   off-multiple layer is exactly its minimal-generator/socle layer, with dimension density
   `1 - r^{-2}`; the paper-proved Stein identity is the quadratic-form shadow of this freeness.
   The naive torsion prediction is refuted in the precise sense that torsion vanishes — the
   2-adic content sits in generators, not relations.
2. `[EXACT FRACTURE]` On Sylvester kernels the `t^2`-structure map fails to exist; the exact
   obstruction cocycle is `Obst(F,G) = D_q(A * (1-P_q)F + ((1-P_q)C_{j-2}) * G)` from the
   commutator identity `[D_q, M_A] = D_q ∘ M_A ∘ (1-P_q)`. The `C`-side term is the paper-proved
   layer; the `A`-side term reads ONLY the even-indexed coefficients `a(2k)` of the `A`-symbol
   (input factors through the off-multiple layer — prediction half-confirmed — but output
   spreads through the 2-adic even slice of `A`).
3. `[REPLACEMENT — bigraded Koszul census]` Bigraded Rees over `C[t, u]`: `t` = cutoff
   inflation (exact and free via `D_q(c * S_q g) = c * g`), `u` = 2-adic slicing
   `A^{(alpha)}(m) = a(2^alpha m)`; `Obst` is the `u`-degree-1 connecting map of a Koszul pair,
   and each decimation step drops one 2-adic level of `A`.
4. `[NEW OPEN CORE]` Show the even slice `A^{(1)}` lies in the pair ideal `(A, C)` modulo units
   (approximate 2-adic self-similarity mod the ideal); then the connecting map is inner and the
   census congruence `M ≡ P (mod 2^k)` closes stepwise.
5. `[SHARPENING — multiplicative/archimedean split, this session]` For a COMPLETELY
   MULTIPLICATIVE coefficient core, `a(2m) = a(2) * a(m)` exactly: the even slice is inner
   trivially (`A^{(1)} = a(2) * A` on odd support plus 2-power bookkeeping). The zeta-side core
   of the census symbol is completely multiplicative; the non-multiplicative content is exactly
   the archimedean/Gamma channel and the polynomial/pole factors of shifted Xi. Hence the open
   core REDUCES to: the archimedean correction to the even slice lies in `(A, C)` mod units —
   a Gamma-channel statement, where the corpus's archimedean machinery (Meixner root scales,
   Gamma connections, digamma resolvents) applies. Next hostile question: make "even slice of
   the archimedean transform" exact (the Gamma factor is an integral kernel, not a Dirichlet
   series — define the slice through the decimation algebra's completion and check whether the
   corpus's formalized shift-two exposure `xi_logDeriv_shift_two_exposes_prime_source` /
   `XiShiftPrimeExposure.lean` already computes it: the shift s -> s+2 IS the square-index
   decimation in the s-domain).

## 2026-07-18 session 1 (cont. 8) — CORRECTION of cont. 7 + the exact arch-slice conjecture

**[CORRECTION]** The cont.-7 closing claim ("the shift s -> s+2 IS the square-index decimation
in the s-domain") is WRONG — self-caught and adjudicated against the live Lean. The formalized
`xi_logDeriv_shift_two_exposes_prime_source` (XiShiftPrimeExposure.lean:128) is coefficient
DAMPING (`LSeries f (s+2) = LSeries (n ↦ f n * n^{-2}) s`, atoms `Λ(n)(1-n^{-2})`), diagonal in
`n`; the Koszul cocycle needs the REINDEXING slice `a(2m)` (compression, non-diagonal), and
cont. 6 itself proved slicing has no s-domain multiplication form. Damping `n^{-2}` vs slicing
`4^{-s}`: constant-in-s vs constant-in-n — no unit bridge exists.

**Verified positive content.** (i) The prime-source even slice is CLOSED FORM:
`sum_m Λ(2m) m^{-s} = log(2)/(1 - 2^{-s})` — the 2-Euler channel, zero-free on `Re s > 0`,
hence a UNIT: the multiplicative side of the even slice is inner, exactly as cont.-7 item 5
predicted. (ii) The full obstruction: with `A = G ⊛ z` (archimedean coefficient object
convolved with zeta coefficients), the parity split of Dirichlet convolution gives the exact
identity `A^{(1)} - A = (G^{(1)} - G·1_even) ⊛ z` — the obstruction is precisely the failure of
2-adic self-similarity of the ARCHIMEDEAN object `G`, and it lives only in the windowed
discretization sampled by the Sylvester kernels.

**[ARCH-SLICE CONJECTURE — current exact open core of the lane]** On height-adapted census
boxes, the series generated by `(G^{(1)} - G·1_even) ⊛ z` lies in the pair ideal `(A, C)`
modulo units of `O(Omega)`. Its correct s-domain avatar is LEGENDRE DUPLICATION
`Γ_R(s) Γ_R(s+1) = Γ_C(s)` — the doubling identity as the archimedean counterpart of dyadic
slicing (shift-ONE weld coupled with `2^{-s}` rescaling), NOT the shift-two damping. The
duplication tool exists formalized: `HTGeometry/SignedGammaSharpExample.lean` ("Legendre
duplication in ratio form").

**Next moves:** (1) express `a_W(2m) - u·a_W(m)` through the duplication ratio (paper); (2)
test `(A, C)`-membership on the census box using T4's finite quotient (structural analysis of
the finite linear system — no computations); (3) T4 Lean batch per logged plan; (4) hostile:
if membership fails, the failure class is the next interrogation input — record whether it is
height-uniform (fatal) or box-local (absorbable by height-adaptation).

## 2026-07-18 session 1 (cont. 9) — arch-slice SURVIVES; duplication identity derived; vacuity
## alarm raised

Agent-derived, first pass (needs my referee before any promotion):
1. `[DERIVED ON PAPER — first pass]` Exact obstruction identity:
   `O(s) = (2^s - 1) * D_{G·1_even} * zeta_W = u1*A + u2*D_G^- * zeta_W + u3*B`, with
   `(2^s - 1)/2` a genuine unit on census boxes, `D_G^-` the parity-twisted (theta_4-channel)
   windowed archimedean series, `B` the windowed-vs-analytic discrepancy. Legendre duplication
   in the formalized ratio form (`sharpNeutralGammaRatio`, SignedGammaSharpExample.lean:26; from
   mathlib `Complex.Gamma_mul_Gamma_add_half`) certifies coarse = unit * (shift-one weld) * fine
   for the arch symbol, cancelling main terms in `D_G^-` exactly; NO `xi(2s)` term arises (the
   2s-trap never fires: G is smooth-density in the convolution index, not square-supported).
2. `[VERDICT]` Arch-slice membership via T4 reduces to: `ord(D_G^- * zeta_W) >= m - 1` at every
   box zero — VACUOUS at simple zeros. Exact surviving statement: only at MULTIPLE box zeros
   must the parity-twisted defect vanish to order `m - 1`. Sufficient sharper form:
   `D_G^- * zeta_W ∈ (R(s-1/2), R'(s-1/2)) * O(Omega)` (the jet module — anything in it has
   `ord >= m-1` automatically; `C` itself is visibly in it by its Lean definition).
3. `[VACUITY ALARM — mandatory hostile assembly]` If the Koszul chain closed with vacuous
   membership in the all-simple configuration, it would force `2^k | M` and hence no simple
   off-line zeros — far too strong to accept without locating the hidden cost. REQUIRED NEXT:
   assemble the full chain skeleton from census endpoint back through the bigraded Koszul
   recursion, NAMING every unproven glue lemma (finite-section stabilization on boxes; Koszul
   exact-sequence bookkeeping; per-step congruence composition; the discrepancy channel `B`'s
   membership; unit normalizations), and hostile-test where RH-strength content hides in the
   all-simple case. Lesson in force: a lane whose open steps imply the target through a shorter
   branch is a hidden restatement (ccm-rayleigh failure).
4. `[FORMALIZATION GAP INVENTORY]` No Jacobi theta doubling/Landen exists in the corpus (theta
   files are divisor/principal-part only); duplication side has `sharpNeutralGammaRatio`,
   polygamma multiplication (n=2), Sauter-Bogoliubov Gauss-duplication carrier; order law
   `analyticOrderAt_dyadicSharpPrimeCancelledSource_eq_pred` formalized.

## 2026-07-18 session 1 (cont. 10) — all-simple audit CLOSES the bigraded Koszul route;
## derivative-pair/discriminant census replaces it

**[AUDIT RESULT — hidden cost located; bigraded Koszul census DOWNGRADED]** In the all-simple
configuration `ord_C = 0` at every box zero, so `C` is a unit modulo `A`: `(A, C) = O(Omega)`,
`P = 0`, and the census demand degenerates to `2^k | M` with the pair-ideal carrier BLIND (the
arch-slice membership is vacuous precisely because the carrier has lost the divisor). The
per-step congruence composition would have to produce raw count-divisibility unaided — full
RH-strength content in one glue lemma. Verdict per the hidden-restatement test: the bigraded
Koszul census with carrier `(A, C)` cannot be closed by the arch-slice conjecture; the cont.-9
survival was real but feeds a carrier that is empty exactly where the danger is. The arch-slice
identity chain (cont. 9) is retained as proved-first-pass support material for multiple-zero
configurations only.

**[CONJECTURE — derivative-pair (discriminant) census; failure-driven replacement]** Replace
`C` by `A'`: the order law `ord_{A'} = m - 1` holds at EVERY zero with no degeneration, and T4
applies verbatim: `dim O/(A, A') = sum(m-1) = P(T)` — the same census quantity, now carried by
the intrinsic pair `(A, A')`. The census congruence `dim O/(A) ≡ dim O/(A, A') (mod 2^k)` is
the SQUAREFREE/DISCRIMINANT census: `M - P` = distinct count = the classical
`deg A - deg gcd(A, A')`. The mod-`2^k` mechanism to construct: discriminant/resultant PARITY
of the box configuration — the box divisor is invariant under conjugation `rho -> conj(rho)`
(line-symmetric boxes) and pairs under FE `rho -> 1 - conj(rho)` at fixed height (mirror
pairs), and squareness/sign structure of discriminants under such symmetries is a classical
source of 2-divisibility (real-form discriminant sign laws; Galois parity), while resultants
and discriminants of the window restriction are SOURCE-COMPUTABLE from boundary data (resultant
integrals; corpus: `resultant_specialize_analytic`, `xiHedenmalmBezoutian` on exactly
`(XiC, XiC')` with formalized simplicity gate `xiHedenmalmBezoutian_self_ne_zero_iff_simple`).
- First exact sub-questions: (Q1) for a conjugation-symmetric finite divisor with mirror-pair
  structure, what 2-divisibility of the distinct count is forced by discriminant squareness of
  the associated monic "window polynomial" (the Weierstrass polynomial of `A` on the box —
  source-computable via boundary integrals of `A'/A` times powers... careful: those integrals
  ARE Newton sums = divisor-selected? No: `(1/2pi i) ∮ s^j A'/A ds` is a BOUNDARY integral of
  source data — Newton sums of the zeros obtained WITHOUT enumerating them — the classical
  bridge from boundary data to the characteristic polynomial of the divisor; check against the
  census card's kill conditions: this is boundary data of the pair `(A, A')`, not a raw-pair
  homotopy invariant, and it is exact, not an estimate);
  (Q2) does the depth-2 divisibility (by 4) follow for FE+conjugation double-symmetric stacked
  boxes — the first non-free rung anywhere in this cluster;
  (Q3) hostile: Newton-sum/Weierstrass-polynomial data determines the divisor COMPLETELY — is
  the census congruence then just "compute both sides" (hidden tautology)? The answer must be
  that the mechanism supplies STRUCTURAL divisibility (symmetry/parity of the polynomial's
  Galois/real-form data) without computing the count — pin this before proof investment.

## 2026-07-18 session 1 (cont. 11) — Q3/Q2 verdict: the cluster's distilled core is √disc

**[Q3 ANSWERED — not a tautology; mechanism structural at depth 2]** On line-symmetric boxes
the divisor is invariant under `sigma(rho) = 1 - conj(rho)`, so the box Weierstrass polynomial
`W` is LINE-REAL (real form centered on the critical line). The real-form discriminant sign law
is structural (resultant identities, not root computation): `sign(disc W)` determines the
parity of the off-line mirror-pair count. Depth 2 of the census is therefore source-producible
— but coincides with the free mirror-pair rung (no new content beyond the symmetry).

**[Q2 ANSWERED — the depth-4 wall named exactly]** Divisibility by 4 (the first non-free rung
anywhere in this cluster) requires `disc W` to be a SQUARE in the source structure — a
Galois/monodromy-type datum. This is the same wall as the session-opening sqrt-Xi-tower
analysis, the Kummer-cover chain, and the parity ladder, now in its sharpest algebraic form.

**[DISTILLED OPEN CORE OF THE PARITY CLUSTER]** After five independent open-core iterations
(subresultant census -> pair-ideal congruence -> Rees finite-section -> bigraded Koszul ->
derivative-pair discriminant), all faces reduce to ONE object:

> Construct, from the theta--prime--Gamma source and for height-adapted line-symmetric boxes, a
> square root of the line-real discriminant of the box Weierstrass polynomial of Xi — before
> reading the divisor.

Convergence of independent routes onto this object is evidence it is the true irreducible core.
Three generative continuations (springboards, in priority order):
1. **Tower splice:** the formalized `rh_iff_tower` (coherent square-root tower of xi on the
   right half-plane) — a compatible family of box-√disc's is the finite-window shadow of that
   tower; investigate whether the tower equivalence supplies EXACT finite-box consequences that
   constrain what √disc must be (a uniqueness/rigidity theorem for candidate square roots).
2. **Modular face:** discriminants of division/torsion values classically acquire square roots
   through THETA CONSTANTS (Jacobi derivative formula, disc products = theta-constant products);
   the corpus lacks formalized theta doubling/Landen (gap recorded at cont. 9) — the theta-
   constant square-root structure is the modular candidate for the source-supplied √disc.
3. **Arithmetic face:** half-integral weight / Waldspurger (literature audit: unexploited raw
   material) — value-level square roots of central L-data as the arithmetic candidate.

## 2026-07-18 session 1 (cont. 12) — tower-splice + Thomae verdicts: the M-curve frontier

**[DERIVED, first pass — tower splice]** (a) √ξ-tower and box-√disc are constructionally
independent (the tower's g branches at on-line zeros, exactly where disc data lives). (b) In
the line-real coordinate each off-line mirror pair contributes disc factor `-(2Re rho - 1)^2 < 0`;
cross terms are squares. Hence `disc(W_B) = (-1)^{r_2(B)} * (positive)`, and the ENTIRE depth-4
content is one reality bit per box: √disc real ⟺ no off-line pair in the box. (c) Bare
ℂ-valued coherent √disc families always exist (sign torsor — vacuous); the content is
line-REALITY, and: coherent line-real √disc family on all height-adapted line-symmetric boxes
⟺ RH ⟺ Nonempty (CoherentTower xi rightHalf) — census depth-4 unifies with the FULL formalized
tower, not merely rung 1. The per-pair obstruction is exactly the phase `i`: the source must
produce `arg disc`, not `|disc|`.

**[LITERATURE — Thomae mechanism, verified]** Thomae (Mumford Tata II ch. IIIa): for
`y² = prod (x - lambda_i)`, even-characteristic theta-nulls to the 4th power equal explicit
period factors times branch-difference products — square roots of disc factors supplied by
PERIOD DATA (Ω, det A), with signs pinned by the spin structure (w_2). Not circular in the
cover: given the curve, periods buy √disc through a genuinely independent channel.
McKean–Trubowitz (CPAM 29, 1976) + Feldman–Knörrer–Trubowitz: transcendental/infinite branch
configurations support full theta/period theory. Corpus: ZERO Thomae/theta-null material; the
spin face exists as backlog `moonshot-spinor-half-frobenius.md`.

**[NEW REPRESENTATION — M-curve frontier]** The hyperelliptic curve `y² = W_B(x)` of each box
configuration exists UNCONDITIONALLY (branch points are the box zeros; no evenness demanded),
with W_B source-defined via boundary Newton sums. The line-real involution is a real structure
on this curve; on-line zeros = real branch points, off-line mirror pairs = conjugate branch
pairs. Hence, trivially at the level of statements: RH ⟺ every box curve is an M-CURVE (all
branch points real). The VALUE is not the renaming but the toolbox it unlocks: M-curves have
period/theta CHARACTERIZATIONS (Comessatti; Gross–Harris real theta characteristics;
Krichever's M-curve criteria via KP — M-curves ⟺ regular real KP solitons), i.e. CHECKABLE
positivity/reality conditions in period data. The new mechanism target, replacing "produce
√disc": **produce the period-reality/positivity certificate of the box curves from the
theta–prime–Gamma source** — e.g. a source integral representation of the A-periods of
`x^k dx / y` over the box curve whose reality/positivity is provable before reading the divisor.
- `[OPEN CORE — next Gate-2/3 cycle]` State the exact M-curve period criterion to target
  (Gross–Harris form vs Krichever form), derive the source-side expression of the box-curve
  periods (contour integrals of boundary data — the curve's coefficients are Newton-sum
  polynomials in source boundary integrals), and hostile-test for hidden restatement: the
  period integrals depend on the divisor through W_B — determine whether reality of periods is
  provable from the SYMMETRY of the source data alone (line-reality of W_B is automatic from
  the FE — check!) or secretly requires zero locations. NOTE: W_B line-real is automatic
  (mirror-symmetric divisor); real curves with complex-pair branch points still have line-real
  W — so period REALITY is not automatic and is exactly where content lives: the M-condition is
  about the TOPOLOGICAL TYPE of the real structure, distinguishable in period data.
- No computations (per lane rules): the genus-1 two-zero Thomae calibration must be done
  symbolically, not numerically.

## 2026-07-18 session 1 (cont. 13) — M-curve period certificate KILLED beyond depth 2;
## Picard–Fuchs wall-crossing successor

**[VERDICT — RESTATEMENT beyond depth-2, with verified calibration]** Gross–Harris (Ann. ENS 14
(1981) 157-182, read from original): M-curve ⟺ conjugation trivial on H_1 mod 2 ⟺ tau purely
imaginary (Comessatti/Vinnikov lift) ⟺ all even theta characteristics real. Genus-1
calibration derived exactly: rectangular lattice (q > 0) vs rhombic (Re tau = 1, q < 0)
dichotomy ⟺ sign(lambda) ⟺ sign(disc) — and the r_2 = 2 configuration is rectangular AGAIN:
period type sees only r_2 mod 2 = the depth-2 bit. Hostile core: the exact source formula
`sqrt(W_B(x)) = exp((1/2)(2*pi*i)^{-1} ∮_{∂B} log(x - lambda(s)) dlog Xi)` is valid precisely
on the divisor-blind region where every cycle is trivial or computes Newton coefficients;
nontrivial periods need branch-separating cycles = divisor knowledge; the Comessatti basis
presupposes the type it certifies. Period-reality re-encodes zero locations at (i) cycle
choice, (ii) basis normalization.

**[SALVAGE — quantized wall-crossing frame]** The topological type is a quantized
locally-constant invariant on `{disc W_B ≠ 0}`, and `disc W_B` IS source-computable (consistent
with the corpus survivor class: semicontinuous integer readers; walls = collision events).
Surviving exact statement: the type is constant along source paths avoiding the
source-checkable wall `disc = 0`; a certificate = path-connection to a reference
M-configuration with controlled wall crossings.

**[NEXT OBJECT — Picard–Fuchs/Gauss–Manin]** The PF connection of `y^2 = W_B(x)` is RATIONAL
in the coefficients (Griffiths–Dwork; no cycle choices), hence source-defined. Target: read
the real-type from PF monodromy around disc-walls plus one germ. The natural deformation is
the height sweep T (boxes sliding/growing): type changes only at source-detectable wall events
(zeros entering through the boundary; collisions), so the census becomes a Sturm-like
bookkeeping of wall crossings along the sweep. `[OPEN — next hostile target]` the GERM: the
one reference configuration and the local crossing rules are where content can hide — determine
whether the crossing rules are source-derivable (local PF monodromy is universal per wall type
— plausibly yes, this is classical vanishing-cycle/Picard–Lefschetz data, divisor-free!) and
whether the reference germ can be taken in the zero-free region Re s > 1 (source-certifiable
empty box — M-type trivially). If both hold, the remaining content is exactly the ENTRY
bookkeeping at box boundaries — state it and interrogate.

## 2026-07-18 session 1 (cont. 14) — germ conditions pass; entry bookkeeping type-transparent;
## SEVEN-REPRESENTATION STABILITY of the irreducible core; pivot designated

**[GERM VERDICTS]** (A) Picard–Lefschetz crossing rules: universal vanishing-cycle data,
divisor-free; crossing TYPE readable from subresultant jets at the wall (source-computable) —
PASSES. (B) Reference germ: `Re s > 1` boxes are formally zero-free (Euler product /
mathlib Nonvanishing), trivially M-type — PASSES.

**[ENTRY BOOKKEEPING — TYPE-TRANSPARENT, terminates in the formalized collision no-go]** On a
line-symmetric box, an off-line mirror pair enters as a symmetric DOUBLE boundary event; an
on-line zero as a SINGLE line event. The bookkeeping faithfully records event types; forbidding
doubles IS RH; and distinguishing a double event from two singles through boundary data is
exactly the off-line-pair vs on-line-double configuration of the formalized collision
degeneracy no-go (bounded scalar boundary readers blind; verified-height lane). The PF
wall-crossing frame is therefore EQUIVALENT to the prior faces, not a new producer.

**[STRUCTURAL FINDING — stability of the core]** Seven independent representations
(subresultant census, pair-ideal congruence, Rees finite-section, bigraded Koszul,
derivative-pair discriminant, M-curve periods, PF wall-crossing) each terminate, by proved
no-gos, at the same irreducible invariant: one Z/2 bit per potential off-line mirror pair,
invisible to continuous boundary readers, homotopy invariants, symmetry/covariance transport
(T1-T3), abelian windings (T2), period reality (cont. 13), and event bookkeeping (this
section). This representation-stability is itself a theorem-shaped fact about the search
space; the mechanism classes it excludes are exactly the analytic-transport toolbox.

**[SURVIVING UNTOUCHED FACES — pivot designated]**
1. Spin/metaplectic: the corpus's own backlog card `moonshot-spinor-half-frobenius.md`
   (metaplectic sqrt-Frobenius, w_2 obstruction, Re = 1/2 fixed locus) — the theta
   characteristic/spin structure IS the sign datum Thomae needs (cont. 12); FIRST pivot target.
2. Waldspurger / half-integral weight: value-level square roots of central L-data (literature
   audit: unexploited).
3. Differential-algebraic face (Hurwitz FE-Schwarz rank-two circuit etc.) — partially owned by
   concurrent lanes; coordinate before entering.
Next session: Gate-1 audit of the moonshot-spinor card + external metaplectic/spin literature;
plus the T4 Lean batch (plan at cont. 6+) and referee passes for cont. 11-14 derivations.

## 2026-07-18 session 1 (cont. 15) — spin-face Gate-1 complete; metaplectic explicit formula
## designated as the Gate-2 target

**[GATE-1 RESULTS]** Internal: moonshot-spinor card untouched (moved 0-backlog ->
1-in-progress, owned by this lane); corpus holds ZERO proven metaplectic/spin theorems (only
the sl_2 oscillator algebra, and a conjectural "metaplectic half-turn" label on the pi/8
offset). External (verified citations): Weil Acta Math. 111 (1964) — the Weil index
gamma ∈ mu_8 is well-defined, Witt-additive, and Mp is the canonical square root of the Fourier
transform fixing Gauss-sum signs; Rao Pacific J. Math. 157 (1993) — explicit computable
cocycle; Candelori 1512.04415 — theta multiplier bundle ≅ dual determinant bundle (algebraic
w_2 source); Atiyah/Mumford 1971 — theta characteristics = spin structures, Arf parity
deformation-invariant; Meyer Duke 127 (2005) — zeros as Euler characteristic of a graded
complex (theorem, no positivity); Holland 2604.25288 — Hilbert reciprocity = adelic product
formula for Weil-index defects. **A metaplectic/spin refinement of Weil's explicit formula
does not exist in the literature (EMPTY — verified).**

**[BRIDGE CONJECTURE — exact statement]** The w_2 class of the metaplectic sqrt-Frobenius
cover induces on each box curve `y^2 = W_B(x)` a distinguished REAL EVEN theta characteristic
(spin structure) whose Thomae theta-null sign assigns the reality bit of each per-pair disc
factor; source-computability of this characteristic yields the coherent line-real sqrt(disc)
family on all height-adapted boxes, which is equivalent (cont. 12, tower splice) to RH.

**[GATE-2 TARGET — metaplectic explicit formula]** Construct the lift of the
Riemann–Weil explicit formula to the metaplectic cover: each local/prime term acquires a
canonical Weil-index phase in mu_8; the adelic product formula for Weil indices (= Hilbert/
quadratic reciprocity, Holland's formulation) is then a GLOBAL SIGN LAW constraining the
lifted formula. Why this passes the seven-representation filter (cont. 14): the supplied datum
is a canonical mu_8/mu_2-valued phase of ARITHMETIC origin (reciprocity), not a continuous
analytic reader, not a homotopy invariant, not symmetry transport — it is the first candidate
producer in this lane whose bit-law is an arithmetic theorem. First exact sub-questions:
(MQ1) what is the metaplectic lift of the test-function side (Mp acts on the oscillator/
Schwartz model — the corpus's OscillatorAlgebra.lean is the formal seed); (MQ2) what do the
prime terms' Weil indices compute at the finite places (local gamma of the quadratic form
attached to each prime-power term); (MQ3) does the global mu_8 balance impose a constraint on
the zero side that sees the per-pair bit (the hostile question — test for type-transparency
IMMEDIATELY against the cont.-14 pattern before proof investment).

## 2026-07-18 session 1 (cont. 16) — MQ3 first-pass verdict: NOT type-transparent under a
## Lefschetz structure; metaplectic Lefschetz formula designated

**[MQ3 — first-pass adjudication, this lane's reasoning; referee pending]** The metaplectic
explicit formula evades the cont.-14 type-transparency pattern IF AND ONLY IF the zero side
enters through a metaplectic LEFSCHETZ FIXED-POINT structure for the line-reflection involution
`sigma(s) = 1 - conj(s)`:
- off-line mirror pairs are sigma-SWAPPED: their contributions pair into REAL mu_8 data;
- on-line zeros are sigma-FIXED: individual `e^{±i*pi/4}`-type (NON-real) contributions;
- a Lefschetz identity EQUATES the type-weighted phase sum to an arithmetic side constrained by
  the Weil-index product formula (reciprocity). Real terms cannot balance an odd number of
  eighth-root phases: the mu_8 balance is a LAW on the on-line count (mod 8 structure), not a
  record of types. This is the structural difference from the entry-bookkeeping transparency:
  bookkeeping records; a fixed-point formula equates.
- Transparency failure mode to guard: if the lift multiplies both sides by one divisor-
  independent overall phase, nothing is constrained — the design requirement is therefore that
  per-zero half-density signs (the spin datum) appear in the fixed-point contributions, i.e.
  the zero complex itself must be metaplectically graded, not just the scaling flow.

**[SUB-TARGET — metaplectic Lefschetz formula]** Construct the sigma-equivariant metaplectic
refinement of Meyer's graded-complex realization (Duke 127 (2005): explicit formula as Euler
characteristic — the theorem-level seed): lift the complex to half-densities, compute the
sigma-fixed-point contributions with their Maslov/eta-type mu_8 phases, and identify the
global balance with the adelic Weil-index product (Holland's reciprocity formulation). MQ1
(oscillator-model lift; corpus seed OscillatorAlgebra.lean) and MQ2 (local prime-term Weil
indices) become components of this construction. Hostile checks queued: (i) does Meyer's
complex admit a sigma-action at all on the nose (his space is idele-class; sigma is s -> 1-s
on the spectral side = inversion + twist on the group side — identify the exact involution);
(ii) eta/Maslov corrections at fixed points must be computed, not assumed; (iii) the
"arithmetic side" must be genuinely divisor-free (only prime/archimedean data).

## 2026-07-18 session 1 (cont. 17) — hostile check (i) PASSES maximally: sigma on Meyer's
## complex is on-the-nose AND equals adelic Fourier on the arithmetic wing

**[VERIFIED + DERIVED (agent, first pass; referee queued)]** Meyer's model (math/0311468, Duke
127): wings `H_+ = S(A_K)_{K^x}` embedded by `i_+ f = (Sf, JSFf)` (S = K^x-averaging, J =
inversion `|x|^{-1} f(x^{-1})`, F = adelic Fourier) and `H_- = S(C_K)` diagonal; Poisson gives
the glued complex; zeros = spectrum of the graded piece `pi_-` with multiplicity; explicit
formula = Euler characteristic (Meyer's theorem). NEW derivation on top:
- `sigma(f0, f1) := (J f1, J f0)` is bounded on the model, `sigma^2 = 1`, acts on characters by
  `chi|.|^s -> chi^{-1}|.|^{1-s}` (trivial chi: exactly `s -> 1-s`); line reflection = sigma
  composed with pointwise conjugation — also on the nose.
- `sigma ∘ i_- = i_- ∘ J` (idele-class wing invariant, anomaly-free), and
  `sigma ∘ i_+ = i_+ ∘ F` — on the adelic wing sigma IS the Fourier transform (uses `J^2 = 1`,
  `F^2 = (-1)^*`, `S(-1)^* = S`, product formula). sigma preserves `H_+ + H_-` and both graded
  pieces separately: the fixed-point analysis on the zero part is well-posed.
- Metaplectic entry: half-density lift of `H_+` makes `F = rho_Weil(w)`, `w ∈ Mp` — the mu_8
  Weil index attaches canonically and ONLY on the arithmetic wing. `sigma|_{H_+}^2 = 1` holds
  on coinvariants — the metaplectic grading lives exactly in that quotient.
- Literature: Meyer notes the spectral symmetries, no equivariant refinement; CCM math/0703392
  cyclic version has no metaplectic grading; Burnol math/9902080 adjacent. TARGET REMAINS EMPTY.

**[GATE-4 CONSTRUCTION TARGET — now concrete]** The sigma-equivariant metaplectic Lefschetz
refinement of Meyer's complex: (L1) half-density lift of both wings; (L2) compute the
sigma-eigenvalue (Maslov/Weil phase) per sigma-fixed character — the FIRST LEMMA (this is
where `e^{±i*pi/4}`-type data per on-line zero enters, vs real contributions of swapped
pairs); (L3) the equivariant trace identity: graded chi of sigma on the complex = arithmetic
side with local Weil indices; (L4) the reciprocity/product-formula constraint as the global
sign law; (L5) extract the on-line-count mod-8 law and splice into the census/tower chain.
Referee queue: cont. 11-17 derivations. Then Lean strategy after paper closure (Gate 5
discipline; the corpus seeds: OscillatorAlgebra.lean, Meyer-model formalization would be new).

## 2026-07-18 session 1 (cont. 18) — LEMMA L2 DERIVED (referee-ready): AI-class Real structure,
## no Kramers; the per-zero sign datum identified; L3 = KR-signature/eta identity

**[L2 — derived, referee-ready]** (1) sigma alone fixes only `chi^2 = 1, s = 1/2` exactly (a
linear-sigma Lefschetz sees essentially nothing); the correct structure is the ANTIUNITARY
`sigma-bar = sigma ∘ C`, fixing the critical line pointwise and swapping off-line horizontal
mirror pairs; `C ∘ i_+ = i_+ ∘ C` exactly, so `sigma-bar|_{H_+} = F ∘ C` — a Real (KR)
structure. (2) THE SQUARE: with `gamma(psi) = e^{i*pi/4}`, `rho(w~) = e^{-i*pi/4} F`,
`rho(w~^2) = -i/+i` on even/odd (Weil §16 / Lion–Vergne, order-4 center of Mp_2), the
antiunitary `T = rho(w~) ∘ C` satisfies `T^2 = |gamma(psi)|^{-2} = +1` — phase-robust (any
unimodular lift), because conjugation INVERTS the Weil index and mu_8-unimodularity kills the
twist. Hence `epsilon(even) = epsilon(odd) = +1`; adelic version identical (prod gamma_v
unimodular). (3) Consistency anchor (independent): epsilon(even) = -1 would force even
multiplicity of every ON-line zero — contradicting the known simple first zero. Derivation and
anchor agree. (4) Constraint landscape (honest): no Kramers multiplicity forcing; sigma-bar is
commuting-type (AI), fixing on-line and swapping off-line — orthogonal to ladder rung 1,
matching the ladder card's own proved catalogue. L2's yield: each critical-line fiber `V_rho`
acquires a CANONICAL REAL FORM `Fix(T)`; a simple zero yields a canonical real line = a sign in
{±1} once the arithmetic normalization is fixed — THE per-zero bit for the Thomae/sqrt-disc
chain; off-line mirror fibers get only the classical equal-multiplicity pairing.

**[L3 — exact target shape]** A KR/antiunitary fixed-point identity (antiunitaries have no
eigenvalues; antilinear traces are basis-dependent — the invariant is the REAL-FORM comparison):
compare the metaplectic real form `V_rho^R` against the arithmetic-side normalization, with the
mu_8 Maslov/eta data entering the arithmetic side; the per-zero discrepancy lives in
`H^1(Z/2, U(1)) = Z/2`. Hostile guards for L3: (i) the arithmetic normalization must be
divisor-free; (ii) the comparison must not be basis/gauge-trivial (the H^1 class must be
provably nontrivial exactly on one type — test on the toy rank-1 case first); (iii) check
against the seven-representation transparency pattern before proof investment.

## 2026-07-18 session 2 (cont. 19) — BATCH REFEREE VERDICTS APPLIED (four independent referees
## over cont. 9-18)

1. **[disc-sign law: CONFIRMED + OVERCLAIM FIXED]** Sign bookkeeping verified (4-root symbolic
   expansion; cross factors provably positive: pair-pair cross groups as
   (|z_k - z_l|^2 |z_k - conj z_l|^2)^2). CORRECTION to cont. 12: "sqrt(disc) real ⟺ no
   off-line pair" is FALSE per box — counterexample roots 1±i, -1±2i: r_2 = 2, disc = 270400,
   sqrt = 520 real. Correct statement: sqrt(disc) real ⟺ r_2(B) EVEN. Requires disc ≠ 0
   (simple zeros); multiple-zero boxes degenerate the bit — handled by the complementary
   arch-slice/jet chain (cont. 9), a genuine division of labor to preserve.
2. **[NEW NAMED LEMMA — SEPARATION]** The tower-splice ⇒ direction (family ⇒ RH) has a gap:
   all-boxes r_2-evenness forces r_2 = 0 only given: *for every hypothetical off-line pair
   there exists an admissible height-adapted line-symmetric box containing exactly that pair
   and no other zeros.* Plausible from divisor discreteness + boundary zero-freeness
   genericity; MUST be proved and integrated before the equivalence is used. Elementary-
   looking; Lean-friendly; queue for the next paper/Lean batch.
3. **[parity-split: CONFIRMED + CONVENTION PIN]** Identity exact; under the shifted-coefficient
   convention (z(2) = 1/4, XiShiftPrimeExposure.lean:79) the identity gains the unit
   (2^s - 1/4) in place of (2^s - 1); all mod-units conclusions survive. Convention now pinned:
   coefficients read in the shifted variable (all-ones core, z(2) = 1).
4. **[sigma-Meyer: CONFIRMED, all three identities, against the fetched paper]** Stronger than
   claimed: S(-1)^* = S holds on the nose (a -> -a bijects K^x), no coinvariant quotient
   needed. No gaps.
5. **[L2: T^2 = +1 CONFIRMED; central character CONFIRMED (convention-independent); Kramers
   logic CONFIRMED as pure algebra; IDENTIFICATION GAP routed to L3]** The unproven link: T
   lives on the half-density lift of H_+; zeros live in H^1 of the complex; T must be shown to
   descend through the weld/boundary map and act as sigma-bar on each generalized-eigenspace
   fiber. Also state: C ∘ i_+ = i_+ ∘ C holds only after S (via S(-1)^* = S). L3's first
   obligation is now exactly this **fiber-invariance/descent lemma**, ahead of the signature
   identity itself.

**Chain status after refereeing:** cont. 9-18 all either CONFIRMED or corrected in place; open
named obligations: SEPARATION lemma (elementary), L3 = descent lemma + KR-signature identity
(with the three cont.-18 guards), MQ2 local Weil indices, T4 Lean batch.

## 2026-07-18 session 2 (cont. 20) — SEPARATION LEMMA proved (first pass), with the innermost
## refinement; tower-splice equivalence completed modulo the delegated multiple-zero chain

**[SEPARATION LEMMA — PROVED HERE, first pass]** If Xi has an off-line zero, then some
admissible line-symmetric box B has either (a) exactly one SIMPLE off-line mirror pair and
`disc(W_B) ≠ 0` (so `r_2(B) = 1`, odd), or (b) its innermost off-line occupant multiple.

*Proof.* The zero set is discrete; fix a height `gamma` carrying an off-line zero. In the
bounded strip `0 < Re s < 1` at height `gamma` there are finitely many zeros; let `beta_min`
be the minimal off-line displacement there. KEY OBSTRUCTION (found in proving): a
line-symmetric box containing a pair of displacement `beta` contains every same-height pair of
smaller displacement — outer pairs are NOT isolable. But the INNERMOST pair is: choose
half-width `w` with `beta_min - 1/2 < w <` (next larger displacement at nearby heights),
half-height `h` smaller than the distance to the nearest other occupied height, and box edges
generic (avoiding the discrete zero set, possible since admissible edge positions form open
dense sets). The box then contains exactly the height-`gamma` zeros of displacement
`<= w`: the single innermost pair (distinct same-height same-displacement points coincide),
plus possibly on-line zeros (harmless: they contribute no `(-1)` factors, and keep
`disc ≠ 0` iff simple — if an enclosed on-line zero is multiple, shrink `h` to exclude it;
it sits at `Re = 1/2`, distance `beta_min - 1/2 > 0`... no: on-line zeros at height exactly
`gamma` cannot be excluded by shrinking while keeping the pair — handle instead: an enclosed
multiple ON-line zero also gives `disc = 0`; in that case the box falls under (b)-type
silence and the height is covered by the multiple-zero chain applied to that on-line zero...
CORRECTION: the multiple-zero chain (arch-slice) constrains off-line multiples; a multiple
ON-line zero is RH-compatible and must not be "killed" — refine: if a multiple on-line zero
shares height `gamma`, perturb the box to a NON-centered height interval `[gamma - h_1,
gamma + h_2]` — the box stays line-symmetric (symmetry is horizontal, not vertical!), and
vertical-edge freedom excludes the on-line zero at `1/2 + i*gamma` only if it is NOT between
the pair... it IS at the same height. It cannot be excluded. HONEST STATUS: case (c) = simple
innermost off-line pair sharing its exact height with a multiple on-line zero leaves
`disc(W_B) = 0` for every containing box — a third delegated configuration.)*

**[DIVISION OF LABOR — corrected and complete]** (i) Reality-bit + separation kills every
height whose innermost off-line occupant is a SIMPLE pair not sharing its exact height with a
multiple on-line zero. (ii) The multiple-zero (arch-slice/jet) chain must kill all MULTIPLE
off-line zeros. (iii) NEW DELEGATED CASE: simple off-line pair exactly co-high with a multiple
on-line zero — measure-zero-flavored but not excludable a priori; must be covered either by a
jet-refined disc (divide W_B by the on-line factor — the QUOTIENT polynomial's disc restores
the bit: `disc(W_B / (s - 1/2 - i*gamma)^m)` is nonzero and its sign law applies with the
on-line factor removed — this WORKS: the quotient is still line-real since the removed factor
is line-real; register as the (c)-repair and referee it) — with the (c)-repair the division is
(i)+(ii) only. *Proof status: first pass with the (c)-repair sketched; referee queued.*

Consequence: line-real sqrt-disc family for all admissible boxes AND the multiple-off-line
chain together imply RH; the tower-splice equivalence is complete modulo referee of this proof
and closure of the (long-standing) multiple-zero chain.

## 2026-07-18 session 2 (cont. 21) — separation SIMPLIFIED to single-case squarefree form;
## L3-descent formulated; T-bar = Meyer's *-operation (phase-blind) — the mu_8 injection point
## located

**[SEPARATION LEMMA — REFEREED, CORRECTED, SIMPLIFIED]** (1) (h, w) order fixed: FIRST
`0 < h < min height gap` (isolates the height among all occupied heights), THEN
`w ∈ (b_min - 1/2, min(d_next-at-this-height, 1/2))`. (2) Generic edges confirmed; definition
pin: "admissible" imposes NO size floor. (3) The (c)-repair as sketched was DIVISOR-SELECTED
(kill-condition breach, confirmed); the squarefree restatement WORKS and is stronger:
`W~ = W_B / gcd(W_B, W_B')` is source-computable (subresultants on Newton-sum coefficients),
`disc(W~) ≠ 0` automatically, `sign disc(W~) = (-1)^{r~_2}` with `r~_2` = DISTINCT off-line
pairs; in the isolated innermost box `r~_2 = 1` ALWAYS — simple or multiple, with or without
co-high multiple on-line zeros. Cases (b) and (c) are ABSORBED; the multiple-off-line
delegation is RELEASED. **Single-case lemma [PROVED, refereed]: an off-line zero exists =>
some admissible line-symmetric box has `disc(W~_B) < 0`.** Contrapositive: nonnegativity of
the squarefree box discriminants (one source-computable real number per box) implies RH via
the (completed) tower splice. Next hostile target: coherence of the `W~` family across
multiplicity walls (the subresultant case split as box parameters vary).

**[L3-DESCENT LEMMA — FORMULATED, partially verified]** Correction: the zero part is
`H^0_- = (H_+ + H_-)/H_+` (pole part is the other quotient). Lemma (a)-(c) at formal level:
`T = sigma ∘ conj` is bounded antilinear, `T^2 = 1`, `T lam_g T = |g| lam_{g^{-1}}`;
`T(H_±) = H_±` (all steps verified against Meyer §5.4-5.6); T descends to `T-bar` on the zero
part, induced by `J ∘ conj` on `H_-` — **which is exactly Meyer's *-operation (§5.6), where
"GRH ⟺ *-reality" is already Meyer's equivalence**: the naive L3 signature identity would be a
[BRIDGE]/rediscovery. Fiber structure: `T-bar` fixes exactly critical-line fibers (canonical
real form `V_omega^R`, `dim_R = mult`), mirror-pairs off-line fibers. Checklist: V1 projector
identity (mechanical, Meyer's ell^1-homomorphism); V2 bornology (citation); V4 consistent.
**[V3 — THE OBSTACLE AND THE INJECTION POINT]** `T-bar` is PHASE-BLIND: `H_+` maps to zero in
`H^0_-`, so the metaplectic phase `rho(w~) = e^{-i pi/4} F` never reaches the zero fibers
through the descended involution. The mu_8/Weil-index data must enter through the IDEAL
PRESENTATION of `H_+ ∩ H_-` (Meyer Lemma 5.10 / Thm 5.11 proof) — the zero-order ideal
filtration. NEXT EXACT TARGET: construct the mu_8-graded comparison on `V_omega` via that
filtration — the datum Meyer's framework provably lacks, and the precise place where the
arithmetic phases (reciprocity law, MQ2 local indices) can act on zero fibers.

## 2026-07-18 session 2 (cont. 22) — HERMITE–HANKEL wall-uniform form; two-structure mu_8
## survivor; novelty audit queued

**[W~ COHERENCE VERDICTS]** (1) No coherence gap in the theorem (per-box quantification;
contraposition pure logic); coherence constrains only PRODUCTION certificates. (2) Equivalence
CONFIRMED: `(forall admissible B: disc(W~_B) >= 0) <=> RH`, and disc(W~) never vanishes so
`>= 0 <=> > 0`. (3) Collision no-go INAPPLICABLE confirmed (discontinuity gated by the
semicontinuous deg gcd — survivor-class lockstep pattern). (4) The evaded no-go returns
QUANTITATIVELY: no uniform sign margin at walls (0^- vs 0^+), so no estimate-with-slack can
certify the sign — the certificate must be an EXACT sign identity (SOS/PSD), not a bound.

**[HERMITE–HANKEL FORM — the wall-uniform certificate carrier]** `H(B)` := Hankel matrix of
the box boundary Newton sums `p_k(B) = (2*pi*i)^{-1} ∮_{∂B} s^k (Xi'/Xi) ds` (in the line-real
coordinate): `H(B) = V^T diag(mult) V`; rank = deg W~; leading principal minor
`det H_r = (prod mult) * disc(W~_B)`; and `r~_2 = 0 <=> H(B) PSD` (Hermite's classical
real-rootedness criterion, box-localized). PSD-ness is a CLOSED, stratification-free condition
absorbing all gcd-degree jumps. Hence:

> **RH <=> for every admissible line-symmetric box B, the Newton-sum Hankel matrix H(B) is
> positive semidefinite** — a box-local finite-rank Hamburger moment statement (box Newton
> sums are moments of a positive measure on the real locus).

Production target: derive `H(B) PSD` from the explicit-formula prime+archimedean decomposition
of `p_k(B)` — box-localized finite-rank Weil positivity. First sub-check passed prima facie
(cone membership is semicontinuous — survivor class). **[MANDATORY NOVELTY AUDIT — queued
before any investment]** Compare against: the corpus's OWN global trace-Hankel criteria
(`XiCentralTraceHankelIntNonnegative <=> RH`, XiTraceHankelCountableCriterion.lean) — is the
box-local version genuinely finer or a known localization? — and the external literature
(Li's criterion positivity sequence; Hermitian-form RH criteria; any box/window-localized
Hankel positivity). The box-locality + wall-absorption + finite-rank features are the novelty
candidates; adjudicate honestly.

**[MU_8 TWO-STRUCTURE SURVIVOR]** Single-structure phase DIES (two exact reasons: gamma(psi)
central/global — fiber-constant grading carries no per-zero datum and cancels antiunitarily;
and Weil reciprocity trivializes even the global scalar). SURVIVOR: the ratio of connecting
maps for TWO metaplectic structures `psi` vs `psi_a` acts on `V_omega` by
`prod_v omega_v(a) * (gamma_v-ratio)` — globally 1 (idele-class character = the reciprocity
law) but NONTRIVIAL at each finite Euler level S: fiber-local, mu_8-valued, with superdiagonal
jet action by log-derivatives of local epsilon-factors. The mod-8 datum is an eta-flavored
DEFECT/BOUNDARY TERM of the Euler filtration whose S -> infinity trivialization IS reciprocity
— exactly where MQ2's local Weil indices act. Next: compute the level-S comparison at a simple
critical fiber (epsilon_S(omega)-type discrepancy on the generator L-hat_S).

## 2026-07-18 session 2 (cont. 23) — NOVELTY VERDICT: (b) REDISCOVERED — and the honest merge

**[VERDICT]** The Hermite–Hankel box-local equivalence (cont. 22) is a routine reformulation:
- INTERNALLY REDISCOVERED: `symmetric-prime-gamma-contour-hermite-rh.md` (2026-07-13) +
  `XiGuinandWeilFiniteHermiteCriterion.lean` already hold the box-localized finite-rank
  trace-Hankel criterion, with the RH-consumer
  `riemannHypothesis_of_countableSymmetricPrimeArchTraceHankelNonnegative` (l.729) FORMALIZED.
  The production target I named is exactly that card's open core (source-side per-box
  positivity). Convergent evolution root cause: the master dependency table has NO
  box/Guinand–Weil row (grep "rectangle|Guinand" = 0 hits there) — the map gap hid the card.
- EXTERNALLY (b): composes from Hermite 1856 / Hermite–Sylvester + argument-principle contour
  moments (Delves–Lyness 1967; Kravanja–Van Barel) + FE symmetry = "Grommer box-localized".
  Li/Jensen/GORZ/Bickel–Pascoe–Sargent all adjudicated distinct (global, coefficient-based, or
  relaxation-only). No per-window PSD criterion in print — but composable, hence not novel.

**[TRUE RESIDUE — the lane's genuine contributions, merged into the prior card's route]**
1. The SEPARATION/INNERMOST-ISOLATION theorem (cont. 20-21, refereed) — absent from the 07-13
   card; it upgrades that card's per-box quantifier logic (which boxes suffice and why one
   odd-pair box must exist).
2. The SQUAREFREE/WALL-ABSORPTION certificate layer (disc(W~), gcd-stratification absorption,
   the no-uniform-margin analysis forcing exact-identity certificates) — absent from both
   corpus and literature; it tells the 07-13 card's open core WHAT KIND of certificate can
   work (exact SOS/PSD identity, not estimates) and that the collision no-go does not bar it.
3. The Lean modules (PairIdealCensusAlgebra.lean; FixedWindowWeylRigidity.lean) — substrate
   for the squarefree layer; compose with XiGuinandWeilFiniteHermiteCriterion.lean.
4. The T1-T3 + seven-representation no-go survey — design constraints for any producer.
ACTION: master-table gap noted (box/Guinand-Weil row missing — to be added on the master card);
this lane's census/tower chain and the 07-13 Hermite-contour chain are ONE route with two
formalized consumers; production effort concentrates on the SHARED open core: source-side
per-box positivity, now with the certificate-form constraints established here.

**[PROCESS LESSON]** Five-day-old corpus results can be rediscovered when the master map lacks
their row. Before any future Gate-2 statement in this lane: grep the FULL 1-in-progress lane
for the mechanism's mathematical objects (not just the master table).

## 2026-07-18 session 2 (cont. 24) — UNIFIED OPEN CORE stated; quantifier reduced to rank-2;
## three exact-identity attacks; level-S collision designated

**[UNIFIED OPEN CORE — this lane + the 07-13 Hermite-contour card (dormant 5 days, merged)]**
Prove `XiCountableSymmetricPrimeArchTraceHankelNonnegative`
(XiGuinandWeilFiniteHermiteCriterion.lean:579; consumer :729): for every admissible rational
symmetric rectangle and every P in Z[X],
`Re[(2 pi i)^{-1} ∮_∂B (R+1+z) P(R+1+z)^2 * (-i)(-zeta'/zeta - (log archFactor)')(1/2+iz) dz] >= 0`,
from the prime + archimedean decomposition ONLY, where (cont. 22) the certificate must be an
EXACT SOS/PSD identity (no uniform sign margin at collision walls — estimates cannot certify).

**[QUANTIFIER REDUCTION — separation theorem applied]** Only innermost-isolating boxes (one
distinct off-line mirror pair + on-line zeros) are needed for the RH contradiction: the
threatened Hankel direction has rank <= 2, so per-box PSD-ness reduces to ONE 2x2
Schur-complement determinant identity, with determinant ∝ disc(W~_B). Caveat (kill-condition
compliant): the certificate may ASSUME the single-pair structure inside the contradiction
scheme but never SELECT boxes by divisor data.

**[THREE ATTACKS, exact-identity-respecting]** (1) Prime-term SOS: completed-square
rearrangement of `sum_n Lambda(n) M_n(P,B)` with an FE-symmetric telescoping remainder that
vanishes IDENTICALLY; (2) archimedean PSD integral identity: Binet/Gauss representation of the
digamma block as an integral of rank-1 PSD kernels with exact 2x2 completion absorbing
`s(s-1)/2`; (3) rank-2 bordered-PSD completion: express the single Schur determinant
(∝ disc(W~_B)) as a Gram determinant of source boundary data.

**[NEXT GENERATIVE MOVE]** Collide attack (1) with the Meyer/L3 `H_+ ∩ H_-` Euler-level-S
ideal filtration (cont. 21): the level-S truncation of the prime block is FINITE, so the SOS
remainder at level S is a symbolically computable object; compute it for the first box family
and one quadratic P (symbolic only — no numerics). MASTER-TABLE REPAIR: the dependency-closure
card lacks a box/Guinand-Weil row; row content: "Symmetric-rectangle Hermite contour | exact
per-box trace-Hankel value relation + RH consumer formalized | prove countable per-box
positivity from prime+arch source (exact-identity certificates only; rank-2 reduction
available) | riemannHypothesis_of_countableSymmetricPrimeArchTraceHankelNonnegative | Live
unified chain (Fable lane + 07-13 card)."

## 2026-07-18 session 2 (cont. 25) — attack 1's closed-contour form KILLED exactly; the
## certificate lives in edge/corner cohomology with the n^{±c} weight imbalance as carrier

**[PROVED (symbolic, referee queued)]** On the box contour (`Re s ∈ (1/2-c, 1/2+c)`, all
edges): (i) the continued objects are confirmed as the valid decomposition
(`infinitePrimeFlux = -logDeriv riemannZeta` continued; trace valid needing only `0 < Re s`,
`s ≠ 1`, `zeta(s) ≠ 0`); the von Mangoldt series diverges on EVERY edge. (ii) For every prime
power n and every polynomial test, the closed-contour moment `M_n(P, B) = 0` IDENTICALLY
(entire integrand, elementary global antiderivative — corner telescoping); the ARCH block's
closed moment is also identically zero (singularities at distance >= 1/2 - c from the box
image). The entire contour value is carried by the poles of continued `-zeta'/zeta` — the zero
packet — matching the Lean value relation. Level-S truncation is a GAUGE MOVE (value
independent of S).

**[EXACT KILL of additive closed-contour SOS]** No per-n completed-square decomposition on the
closed contour can certify anything: every square integrates to zero (0 = 0). Attack 1 as
stated is dead — mechanism recorded.

**[SUCCESSOR — edge/corner cohomology certificate]** The surviving level-S object is
EDGE-RESOLVED: per n, four edge integrals = corner differences of the elementary antiderivative
at `u ∈ {2R+1±ic, 1±ic}` with phases `n^{∓c} n^{∓iR}`; FE pairing (`z -> -z`, `s -> 1-s`)
matches bottom to top corners WITH MISMATCHED WEIGHTS `n^{-c}` vs `n^{+c}` — the `s <-> 1-s`
defect that the arch factor normally repairs, and the arch is closed-contour-invisible, so the
repair must itself be edge-resolved. Per-edge n-series diverge; divergences cancel only across
the full boundary. [CONJECTURE — next construction] The certificate lives on the quotient
"boundary/corner data mod exact (telescoping) data" — a relative/edge cohomology of the box —
where the level-S object is finite and the `n^{-c}/n^{+c}` weight imbalance is the positivity
carrier. This is exactly the designed collision with Meyer's `H_+ ∩ H_-` zero-order ideal
filtration (cont. 21): both demand the same quotient-of-boundary-data structure. Next exact
step: define the edge-cohomology pairing precisely (corner data mod telescoping at level S),
verify it reproduces the zero-packet value, and locate where positivity can enter through the
weight imbalance — then hostile-test for type-transparency per the cont.-14 pattern.

## 2026-07-18 session 2 (cont. 26) — edge-cohomology pairing CONSTRUCTED and verified; fixed-S
## transparency verdict honest; the S-FILTRATION DEFECT is the surviving carrier (three-fold
## convergence)

**[CONSTRUCTED + SYMBOLICALLY VERIFIED]** (notation fix from referee: horizontal edges sit AT
`Re s = 1/2 ± c` — closed interval; divergence needs only `c < 1/2`, Lean-enforced; explicit
antiderivative for P = X: `G(u) = i u^3/L + 3u^2/L^2 - 6iu/L^3 - 6/L^4`, `L = log n`; bonus:
the `s = 1` pole is REMOVABLE in the combined trace — residue cancellation with the arch
factor.) The pairing: C^0 = corner data, C^1 = edge data, T = im(coboundary), `Sigma ∘ d = 0`,
`dim C^1/T = 1` (H^1 of the loop); level-S split `g = D~_S + r_S` gives `phi(E) = tau_S(E) +
rho_S(E)` with **`tau_S ∈ T` exactly for every S** — the level-S corner data IS the telescoping
subspace (pure gauge); the class is carried entirely by the remainder at every S; per-edge
limits do not exist; the S-dependence is the filtration. FE pairing: the antisymmetrized
corner data carries the exact structure `sinh(c*alpha_n)(X+Y) + cosh(c*alpha_n)(X-Y)`, and the
level-S sinh sum is `Theta_S = sum_{n<=S} 2 Lambda(n) n^{-1/2} sinh(c log n) q_n(P)` with
POSITIVE weights and `q_n` homogeneous quadratic in coeff(P) (not sign-definite per n —
positivity only aggregate). Zero-packet reproduction verified exactly (P = X, on-line and
off-line cases; value = m * Q(u_rho) at every S).

**[HOSTILE VERDICT — honest]** At every FIXED S the frame falls to the catalogue: corner +
remainder data are finitely many continuous boundary readers; the packet value is itself
continuous through collision; `C^1/T ≅ C` means no new invariant per (P,B). The quantized
content (integer multiplicities, the per-pair Z/2 bit) lives ONLY in: (a) cone membership over
ALL (P, B) — the closed-cone survivor, a repackaging of the Hankel-PSD class; and (b) **the
S-FILTRATION DEFECT: the divergence-rate structure of the exact decomposition family
{(tau_S, rho_S)}_S** — not a continuous functional of one box's boundary data.

**[THREE-FOLD CONVERGENCE — the lane's object]** (i) mu_8 two-structure defect = level-S
boundary term of the Euler filtration, trivialized in the limit BY reciprocity (cont. 22);
(ii) edge-cohomology quantized content = S-filtration divergence-rate defect (this section);
(iii) sinh-weighted positive structure = the per-level positivity carrier. Two independent
lanes demand the same object class: FILTRATION DEFECT RATES. **[NEXT EXACT TARGET]** The
S-uniform certificate on the innermost rank-2 box: compare the growth of the sinh-weighted
quadratic `Theta_S` against the remainder defect rate as S -> infinity — a comparison of two
divergence rates whose difference is the (finite) packet value; the RH-bearing question is
whether the sinh-positivity dominates the defect rate S-uniformly exactly when the packet is
real. Hostile guard: this is a rate comparison — the exact-identity constraint (cont. 22)
applies to the PER-S identities (which exist, verified); the S-uniformity is where the new
mathematics lives.

## 2026-07-18 session 2 (cont. 27) — S-direction CLOSED exactly (idle index); rank-2 Schur
## identity PROVED; the c > |d| containment lever and the (c,k)-bifiltration successor

**[GATE VERDICT — S-uniform comparison is NOT a certificate class]** (a) Exact kill:
`∂_d(tau_S) = 0` identically (truncated prime corner data is d-free), so every per-S
inequality's d-content is the S-free packet form; the fixed-S wall margin is
`lambda_min = -2m*x0*d^2/(1+x0^2) + O(d^4)` — S-INDEPENDENT and -> 0 at the wall: the
cont.-22 wall problem recurs verbatim at every S; the S-index is idle. (b) The regularized
limit is CIRCULAR: Abel/Cesaro summation of the edge prime series past its abscissa is
governed by sup Re rho — zero-location strength. Certificate class remains the finite exact
SOS/PSD identity.

**[PROVED (sympy-verified) — rank-2 model]** Exact Schur identity
`det N = m^2 * W~(0) * disc(W~)` for the threatened packet block (P = p1*X + p0);
1-parameter tests witness indefiniteness (`V(X - x0) = -2m*x0*d^2` exactly) but cannot
characterize equality; the 2-parameter family `(p1*X + p0) * prod_j (X - x_j)` realizes the
full block with evaluation-Jacobian surjectivity exactly off the walls.

**[REFUTED — the cosh(d log n) rate conjecture]** The S-filtration map
(zero data) -> (rate structure) is CONSTANT; all rates are universal classes
`S^{1/2 ± c} * osc` quantizing the BOX (c), not the zero (d); the cosh weight survives only as
a frequency-dual VALUE (`2 e^{-i alpha x0} cosh(alpha d)`, truncated by polynomial tests to a
polynomial in d^2).

**[OPENED — the containment lever and the (c,k)-bifiltration]** `d` IS a rate, but on the
Mellin-dual side (`psi(S) - S` carries `S^{1/2+d}` oscillation), which the box frame provably
cannot see. NEW STRUCTURAL FACT: admissibility of a pair-holding box FORCES `c > |d|`, so the
box probe rate `S^{1/2+c}` STRICTLY DOMINATES the dual defect rate `S^{1/2+d}` — the box
height is a tunable probe sitting provably above the defect it hunts; the parametrized
statement lives in the c-SCAN (boxes of varying height), not the S-scan. Second dual: the
Hankel index k carries d as the rotation number `theta = arctan(d/x0)` with detection
threshold `k* ~ x0/d`. **[NEXT OBJECT]** The (c,k)-BIFILTRATION: collate the c-scan and
k-scan frames against the `c > |d|` containment constraint — the first frame in this lane
where the probe parameter is FORCED above the hidden parameter by admissibility itself.
Hostile guards: (i) transparency test on the bifiltration (does the (c,k)-data distinguish
collision configurations, or is the c-scan again continuous?); (ii) the k-threshold is
divisor-dependent — the certificate may assume, not select (kill-condition discipline);
(iii) referee the cont.-27 derivations (scripts: rank2_sfiltration_check.py V1-V8).

## 2026-07-18 session 2 (cont. 28) — bifiltration constructed+verified; recovery theorem exact;
## referee confirms cont. 26-27 with sharpened circularity and pinned coordinates

**[CONSTRUCTED+VERIFIED]** (c,k)-bifiltration defined (H_k(B_c) = leading k x k of
`h_jl = (2 pi i)^{-1} ∮ u^{j+l+1} g_B du`); H_2 = the threatened block exactly; finite data has
ZERO c-dependence on the isolation range; k lives on finite packet data, c only on divergent
edge structure; sole coupling = admissibility `c > |d|`. **RECOVERY THEOREM (exact, verified
at S = 2 for two c-values, pole loops branch-certified, no numerics-as-evidence):** packet
value = `sum_E rho_S(E)` with gauge loop zero — the ENTIRE finite Hankel data is
source-computable via one remainder integral per (P,B) at ANY single S including S = 0.
HONEST: recovery adds computability, ZERO sign leverage (it IS the Lean value relation's
residue identity). Transparency: nothing new lost (fixed finite families fall to the collision
no-go; survivor = the closed cone over all (P,B), unchanged).

**[REFEREE cont. 26-27 — ALL CONFIRMED, with repairs]** (i) Two flaky sympy checks (V8,
CHECK3-pole) were log-branch collapse failures, NOT math errors — independently proved
(polynomial-part telescoping + winding 2*pi*i; 40-digit agreement; referee_pole_recheck.py).
(ii) Circularity mechanism SHARPENED: Landau pins the RAW von Mangoldt Abel abscissa at 1 via
the s = 1 pole (zero-independent); the arch-combined trace has s = 1 REMOVABLE (cont. 26), and
the pole-subtracted series' Abel/Riesz obstruction is exactly `sum_rho m_rho Gamma(rho - s)
y^{s - rho}` with abscissa `sup Re rho` — the circularity verdict STANDS, pole-subtraction
caveat added. (iii) `c > |d|` CONFIRMED with coordinate pinning: `c` is the s-frame strip
half-WIDTH (= the separation lemma's `w`, admissible window already forcing `w > |d|`); the
s-frame half-HEIGHT is d-unconstrained. Rate dominance `S^{c-d} -> infinity` follows.

**[PRODUCTION CORE — FINAL RESTATED FORM]** Prove `det H_2(B) >= 0` on innermost boxes
(assume-not-select), where `h_jl` are explicit continued-integral values — equivalently
produce a Gram/Bezoutian representation of `m^2 * W~(0) * disc(W~)` from source boundary data.
Same as the classical Weil wall in ONE respect (the sign sits in continued `-zeta'/zeta` edge
values with no closed form); DIFFERENT in two earned respects: (i) localization — one 2x2
determinant per innermost box, not a global functional; (ii) the strict rate-domination
hypothesis `S^{1/2+c} > S^{1/2+d}` from containment — structure the global frame never had.
**[NEXT MOVE]** Construct the measure: write `h_00, h_01, h_11` on one edge as Binet/Gauss
(arch) + sinh-weighted prime integrals and hunt the 2x2 PSD completion absorbing the
`disc(W~)` sign — attack 2's shape extended to the full trace, on the localized target.

## 2026-07-18 session 2 (cont. 29) — attack 2 closed with two salvage theorems; d is a SHAPE;
## the two-height Prony defect designated

**[SALVAGE THEOREM 1 — paired-edge positivity (unconditional; referee queued)]** On every
admissible innermost box, the FE-folded in-box edge density is strictly positive:
`x*B_in(x) > 0` with `B(x) = sum_rho (1/2 + c - beta_rho)/|s - rho|^2` (Hadamard/Poisson form;
the Binet/Gauss archimedean representation is exactly what converts the sign-indefinite prime
cosine series into this zero-Poisson sum — the arch block repairs the prime block at edge
level), masses `m(c -+ d) > 0` by containment `c > |d|`; hence `T_B(P) = (1/pi) int |P|^2 x
B(x) dx` is positive definite. The FIRST unconditional sign produced by the containment lever.

**[SALVAGE THEOREM 2 — blindness]** Precisely because containment makes the density positive
REGARDLESS of d, no single-height boundary-sign functional detects d. Exact moment form:
`H_2 = H~ + Delta`, `H~` = collision shadow (rank 1, PSD, mass 2m at x0), `Delta = -2m d^2 *
[[0,1],[1,3x0]]` exactly; on `ker H~` (P0 = X - x0): `p^T H_2 p = -2m x0 d^2`. The defect IS
the certified quantity — attack 2 as a det-certificate is NOT viable (type-transparency in
measure costume). d lives in the bump-width SPLIT `{c-d, c+d}` — a SHAPE parameter, not a sign.

**[OPENED — the TWO-HEIGHT PRONY DEFECT]** The width split is visible across heights: the
folded densities `B_c, B_c'` of ONE box at two admissible heights are Poisson mixtures with
width sets `{c -+ d}` and `{c' -+ d}` at common centers. Exact Prony/Pade recovery of `d^2`
from two-height moment data = the c-scan realized as a FINITE EXACT RATIONAL IDENTITY —
algebra, not estimates. **[PRE-REGISTERED GUARDS before any investment]** (i) TRANSPARENCY
TEST FIRST: the Prony expression is rational in continuous two-height data — adjudicate its
behavior through the collision (off-line width-split at one center vs on-line two-center
configuration: does the two-height data distinguish them discontinuously, or is the recovered
d^2 continuous and the interpretation-jump another costume?); (ii) computability is NOT the
question (Newton sums already determine the divisor) — the question is what LAW forces the
recovered d^2 to vanish; state exactly what kind of law the Prony frame could support that
single-height frames cannot (candidate: a POSITIVITY of the two-height JOINT moment matrix —
a Hamburger-type condition on the (c, c')-mixture — whose failure is the width split; this
would be a two-height Hankel/Stieltjes condition — check against the corpus's existing
two-parameter positivity surfaces before conjecturing); (iii) referee the cont.-29 derivations
(scripts: paired_edge_fast_checks.py, paired_edge_fold_probe.py, atan_branch_certify.py).

## 2026-07-18 session 2 (cont. 30) — Prony/multi-height closed by analyticity; RH is a SUPPORT
## condition; referee repairs; the c-cone Bezoutian certificate is the surviving hunt

**[PRONY FRAME CLOSED — analytic unification, sympy-certified]** Both configurations are ONE
family `g_e(u) = 2m(u - x0)/((u - x0)^2 - e)`, `e = -d^2` (off-line) / `+delta^2` (on-line
resolved) / `0` (collision). Every functional built rationally/analytically from finitely many
heights' data is real-analytic in `e` through the three-way collision: no discriminating
functional with (vanish-on-line, nonzero-off-line, discontinuous-at-wall) exists. The Prony
discriminator `D = (s1^2 - s0 s2)/s0^2 = -e` exists and equals `-disc(W~)/4` — a renaming of
the production-core object. Two-height redundancy PROVED (`q(c) - q(c') = c^2 - c'^2`, d
cancels; the second height is a consistency identity, zero information). The joint-positivity
candidate CANNOT fire: the width mixture `m delta_{c-d} + m delta_{c+d}` is itself a positive
measure — **RH is a SUPPORT condition (width = c exactly), and positivity cannot see support
location.** GENERAL LESSON (now proved in this frame): finite height families are analytic
readers; only the semialgebraic SIGN of disc survives, and only height-CONE structures (sup
over all c — non-analytic) escape. Corpus: no two-height/joint-moment surface exists
(StieltjesMomentProblem.lean etc. are single-parameter).

**[REFEREE cont. 29 — CONFIRMED with two repairs]** (i) Hadamard: NO background —
`B_0 = -sum Re(1/rho)` cancels exactly; `B(x) = sum_rho (1/2 + c - beta_rho)/|s - rho|^2`
EXACT. Full-B positivity is CONDITIONAL (a zero with `beta > 1/2 + c` is negative near its
height); unconditional claim pinned to `B_in` (as ST1 states). (ii) ST2 exact with NO O(d^4)
correction (`h_jl = 2m Re(u_+^{j+l+1})`). (iii) GAP REPAIRED: the vertical fold used
`iota(u) = 2(R+1) - u` — box-center reflection, NOT a xi law (model-only). Fix: keep both
vertical edges unfolded, or use the MIRRORED DOUBLE BOX `±[1, 2R+1]` folded by the true xi law
`u -> -u`. The horizontal (Schwarz) fold is valid for xi as used.

**[SURVIVING HUNT — the c-cone Bezoutian certificate]** Represent `-4D * (quadratic in x0) =
disc(W~)`-data as a boundary-data Gram/Bezoutian over the FULL c-cone (all admissible heights
simultaneously — the non-analytic structure), where the rate-domination `S^{c-d}` asymmetry
lives. This is the exact surviving form of the production problem after every finite-frame
closure: a semialgebraic nonnegativity certificate on cone data. Next steps: (a) mirrored
double-box refold (the repaired FE-true geometry) — rederive the fold identities there;
(b) formalize ST1 (paired-edge positivity, now refereed with the B_in pinning) and ST2 (exact
Delta form) as the next Lean batch — both are finite algebra + the Hadamard input;
(c) the cone-certificate Gate-2 statement with transparency guard (the cone escapes
analyticity — verify it also escapes the continuity catalogue, or locate the residual wall).

## 2026-07-18 session 2 (cont. 31) — double-box refold verified (v-frame; height-amplified
## defect); THIRD Lean module shipped (RankTwoPacketMomentIdentities)

**[REFOLD — PROVED, sympy-certified]** The mirrored double box (xi-true `u -> -u` law): odd
moments vanish IDENTICALLY (packet + edges); even moments double; the census lives in the EVEN
sector where `v = u^2` collapses the quadruple to the pair `v_± = X0 ± iD`, `X0 = x0^2 - d^2 >
0` automatic (from `x0 >= 1 > c > |d|`), `D = 2 x0 d`, mass 2m — with the SAME
shadow+defect structure: `Delta_v = -4mD^2[[0,1],[1,3X0]]`, kernel defect `-16m x0^2 d^2
(x0^2 - d^2)`. Structural gains: FE-true geometry (cont.-30 gap repaired); evenness HALVES the
frame; the v-frame is the correct Stieltjes object; **NEW LEVER: the defect is
HEIGHT-AMPLIFIED (∝ x0^2 d^2)** — feeds the c-cone/rate-domination hunt. Vertical edges: not
eliminated, but odd-sector remainders cancel exactly and even-sector vertical terms are
manifestly real. Honest transport: the analytic-reader no-go applies verbatim in v (g_e
rational in v, analytic in e); the support-condition lesson stands. Double-box production
core: `det H_v >= 0`, `h^v_jl = (2 pi i)^{-1} ∮ u^{2(j+l)+2} g du`; RH per box ⟺ `D = 0`.

**[LEAN MODULE 3 — SHIPPED, verified by this lane]**
`RHTower/RankTwoPacketMomentIdentities.lean` (20 theorems): `packetMoment`/`packetHankel`
definitions, the exact identities `packetHankel = collisionShadow + hankelDefect`,
`hankelDefect = -2 m d^2 [[0,1],[1,3 x0]]`, the determinant law
`packetHankel_det_eq_mass_mul_window_mul_discrim` (with mathlib `discrim` for
`W~ = (X-x0)^2 + d^2`), indefiniteness `packetHankel_det_neg` (`m ≠ 0, d ≠ 0 -> det < 0`),
and the collision-PSD dichotomy `packetHankel_collision_posSemidef`. Single-module build
clean (8475 jobs); `#print axioms` on all four capstones = `[propext, Classical.choice,
Quot.sound]`. The blindness/Schur layer is now formal. (Batch agent left the commit pending on
a build monitor; this lane verified and committed: build + axioms audit done here.)

## 2026-07-18 session 2 (cont. 32) — Gate-2 CONE CERTIFICATE stated (exhaustion dichotomy);
## the two surviving lanes meet in ONE computable question (the epsilon_S jet)

**[CONJECTURE — exhaustion dichotomy, marker verified]** For a v-point, cone
`C(v+) = {(B_c, c) : admissible innermost double box, c in (|d|, c_max)}` (admissibility
source-checkable per box; the cone is source-exhaustible though `inf{admissible c} = |d|`).
Marker `N(c) = (pi c / m_B) * sup_x B_in,c(x)`; EXACT: `N(c) = 2c^2/(c^2 + e)` — OFF-line:
`-> infinity` at finite depth `c -> |d|+`, where SIMULTANEOUSLY the rate gap `S^{c-d} -> 1`
and `min_∂B |xi| -> 0`; ON-line: cone reaches depth 0 with `N <= 2` for ALL c (exact per-term
Poisson bound). Statement: **RH-per-box ⟺ every innermost cone satisfies
`sup_C N <= 2`** — quantized gap (2, infinity), non-analytic sup class (escapes the
analytic-reader no-go). Exhaustion identity `c*^2 = max(D_Prony, 0)`.

**[TRAP CONFIRMED + THE FORCING BRIDGE]** N at one height computes e (analytic reader): the
cone adds certificate SHAPE, not detection; `sup N <= 2` is RH-per-box restated UNLESS forced.
The candidate forcing law (collision of the two surviving lanes): cone depth c and Euler level
S are dual exhaustion parameters coupled by the same `n^{±c}`/sinh weights; Hilbert
reciprocity closes the Weil-index product EXACTLY at finite S ⊇ ram(a) — unconditional
arithmetic. BRIDGE QUESTION: does the epsilon_S two-structure defect's superdiagonal jet
(`d/ds log epsilon_v`) inherit an exact finite-level cancellation bounding the remainder rate
`rho_S(B_c)` strictly below the probe rate `S^{1/2+c}` for every `c > 0` — contradicting the
OFF branch where the dual defect `S^{1/2+d}` dominates?

**[OPEN CORE]** Does the epsilon_S jet carry a c-coupled MODULUS constraint at finite level,
or only mu_8 phase? KILL CONDITION (pre-stated): pure phase (unitary, rate-blind) => the
bridge dies. This question absorbs MQ2 (local Weil indices feed the jet).

**[CIRCULARITY MAP — three exact locations]** (i) the identification (mu_8 defect) =
(edge-cohomology rate defect) is the UNPROVEN leg of the three-fold convergence — if it needs
the zero-sum's Abel abscissa, Landau's `sup Re rho` re-enters; (ii) any bridge forcing the
dual exponent to exactly 1/2 is RH verbatim — the law must force something weaker (candidate:
MQ3's mod-8 phase coherence) that still breaks cone termination; (iii) cone construction uses
d — assume-not-select: quantify over hypothetical cones inside the contradiction scheme only.

**[NEXT MOVE]** Compute the epsilon_S jet at the first box family, quadratic P (symbolic; the
cont.-24 designated computation) — the modulus-vs-phase dichotomy decides the bridge.

## 2026-07-18 session 2 (cont. 33) — EPSILON JET VERDICT: MODULUS. The bridge lives as a
## BOUNDEDNESS statement; two open steps named

**[VERDICT — MODULUS; kill condition NOT triggered]** (sympy-refereed, scratchpad/epsjet.py)
(1) Local Weil-index ratios `gamma_v(a, psi_v)` are s-INDEPENDENT mu_8 phases (exact tables:
odd p unit/non-unit cases via (u/p) and p mod 4; v = inf: `e^{i pi (sgn a - 1)/4}`; v = 2 from
Rao). CORRECTION to cont. 22: the two-structure comparison is NOT mu_8-valued — mu_8 is only
its phase; ALL rate content sits in the character block `omega_v(a) = |a|_v^s`.
(2) EXACT MODULUS LAW: `|Xi_S(|.|^{sigma+it}, a)| = (prod_{v not in S} |a|_v)^{-sigma}`;
trivial iff S covers supp(a). Level-coupled probe `a = p_{x+1}` (LEVEL-selected — circularity
(iii) COMPLIANT): `|Xi_{S_x}| = p_{x+1}^{sigma}` exactly; in Tate/Bushnell–Henniart self-dual
normalization: `p_{x+1}^{sigma - 1/2}` — **level-uniformly unitary iff sigma = 1/2**.
Mirror-fiber (T-bar) anisotropy: `p_{x+1}^{2d}` — normalization-independent, `= 1` on-line,
`-> infinity` off-line: the exact datum surviving antiunitary conjugation where the phase died
(cont. 22/18). Unit-modulus probes (a = -1) are rate-blind — modulus probes need height.
(3) CIRCULARITY: (iii) compliant (definition uses no zero data; fiber evaluation inside
assume-not-select). (i) SPLIT favorably: phase and rate live in independent blocks; the
modulus is a FINITE EXACT product — no Abel abscissa, no Landau re-entry; the identification
with `rho_S(B_c)` must be restated for the character block (still unproven — carried openly).
(ii) SHARPENED DECISIVELY: forcing anisotropy = 1 would be RH verbatim, but the bridge needs
only BOUNDEDNESS — any level-uniform bound on the comparison modulus contradicts
`p^{2d} -> infinity`. Boundedness is the genuinely weaker forcing.

**[SURVIVING BRIDGE — CONJECTURE]** RH ⟺ the incomplete-level two-structure comparison has
level-uniformly BOUNDED modulus on every zero fiber. An off-line displacement d yields the
exact per-level defect `p_{x+1}^d` and mirror anisotropy `p^{2d}`.

**[OPEN STEPS — all remaining content]** (a) Construct the comparison's action on `V_omega`
through Meyer's ideal filtration (the L3-V3 obligation, cont. 21); (b) prove the
reciprocity-side A PRIORI modulus bound unconditionally — THE Gate-3 target: test whether the
bound derives from finite-level arithmetic (reciprocity closes the phase; what closes the
modulus?) or secretly needs zero locations. NEXT: bound the comparison norm on the level-S
ideal presentation (Meyer Lemma 5.10 generators).

## 2026-07-18 session 2 (cont. 34) — Gate-3 bridge verdict: forcing leg hits the
## zero-repulsion wall (exact 3-part map); Carleson/interpolation springboard

**[VERDICT (ii) — with the wall mapped exactly]** (Meyer pp. 40-47 verified; sympy-checked)
(1) ACTION derived: the comparison = multiplication by `c * p^s` (c in mu_8) on the strip
algebra — an entire UNIT of Meyer's multiplier algebra; descends; fiber modulus `p^beta`,
mirror anisotropy `p^{2d}` — cont. 33 bookkeeping CONFIRMED. (2) SOUND LEG KEPT: fiber <=
quotient unconditionally (Thm 5.11's homogeneous functionals ARE the jet evaluations), so
**level-uniform quotient-norm bound => RH** stands as a consumer. (3) FORCING LEG FAILS
finite-level derivation, structurally: (b1) ideal membership is DEFINED by interior-line
division (`f / L-hat_S` Schwartz on every interior line) — needs LOWER bounds on |L-hat| =
the classical zero-repulsion wall; no boundary-only presentation of N exists (Gamma-decay
makes `1/L-hat` exit the Schwartz class left of the strip); (b2) the small-representative
escape is REFUTED by duality: the minimal remainder with prescribed jets IS the
evaluation-functional norm (Hahn-Banach); interpolants reintroduce zero positions as nodes
with `1/|L-hat'(rho)|` weights; (b3) convexity/upper bounds enter with the WRONG SIGN
(quotient co-metric monotone DECREASING in |L-hat|: upper bounds certify quotient-norm lower
bounds only). Finite-level reciprocity closes the PHASE block only; the MODULUS bound
secretly requires zero locations. **[NEW SEPARATION — CONJECTURE]** The quotient-norm form is
possibly STRICTLY stronger than RH: even with all `beta = 1/2`, equicontinuity of the
evaluation family is a zero-SPACING statement — the per-fiber bridge and the quotient
packaging separate.

**[SPRINGBOARD — the Carleson/interpolation face]** The co-metric of the ideal N is exactly a
DE BRANGES MODEL-SPACE norm (structure function from xi; Hermite-Biehler ⟺ RH), and
"evaluations uniformly bounded" = **the xi-divisor is an INTERPOLATING SEQUENCE** — a
Carleson-type positivity condition on boundary data. This collides head-on with the
Hermite-Hankel PSD lane (cont. 22): both are boundary-data positivity conditions with
divisor-geometric content. NEXT OBJECT: the box-local Carleson dual of H(B) — formulate the
per-box interpolation/Carleson condition, its exact relation to det H_2 >= 0, and run the
transparency + novelty gates (Carleson conditions are NON-analytic cone-type data — check
against the surviving-class catalogue; audit the de Branges/model-space interpolation
literature for priors: Seip, Ortega-Cerda, Baranov on interpolating sequences in de Branges
spaces).

## 2026-07-18 session 2 (cont. 35) — HB = containment; the chain-termination law; the
## canonical-system return; the consumer rescoped to L2-averaged form

**[DERIVED + VERIFIED (rank-2 exact)]** (i) `E_c(z) = (z - x0 - i(d-c))(z - x0 + i(d+c))` is
HERMITE-BIEHLER ⟺ `c > |d|` ⟺ box admissibility — **the containment lever IS the HB
condition**. (ii) BRIDGE IDENTITY: `det H_2 * 4c^2(c^2 - d^2) = -pi^2 m^2 W~(0) * det G_pair`
— fiber-Gram and Hankel are the same condition, SIGN-REVERSED: off-line pairs are
BETTER-separated interpolation nodes within one box; the evaluation diagonal is d-free
(`2c^3/pi` — blindness in kernel costume). The boundedness consumer cannot act on the c-scan
diagonal; it must act across levels (the p^{2d} modulus) or across fibers.

**[CONJECTURE — CHAIN-TERMINATION LAW]** The de Branges chain `{H(E_{B,c})}_c` (totally
ordered by the dB ordering theorem — non-analytic structure, survivor class) TERMINATES at
`c* = |d|` for an off-line pair (HB breakdown; simultaneously `det G_pair -> 0` and
`N(c) -> infinity` — ONE termination event, two markers; `c*^2 = max(D_Prony, 0)`) and extends
to depth 0 on-line. RH-per-box ⟺ every innermost chain reaches depth 0. **[THE
CANONICAL-SYSTEM RETURN]** Krein–de Branges: a continuous dB chain IS a canonical system —
the c-scan carries a HAMILTONIAN `H(c)`, and the dichotomy is endpoint behavior of that
canonical system. The scattering/canonical-system lane (this session's very first candidate,
set aside at the start) has REAPPEARED, forced by the proof chain. Next: construct the
rank-2 c-scan Hamiltonian explicitly; determine what finite-level source data (recovery
theorem, cont. 28) determines it.

**[CONSUMER RESCOPED — audit verdict]** Phase-metric interpolation criteria verified
(Marzo–Nitzan–Olsen doubling; Lyubarskii–Seip A_2; Ortega-Cerda–Seip frames). No prior work
makes zeta zeros interpolating for any natural H(E) (Burnol: completeness+minimality only).
DAMAGE: uniform interpolation ⟺ liminf normalized gap > 0 AND simplicity — conjecturally
FALSE under GUE (best RH-conditional mu < 0.50895, Inoue arXiv:2604.05733; unconditional
positive-proportion small gaps STTB Trans. AMS 2022; NOTE: GTB arXiv:1904.06001 WITHDRAWN, do
not cite). The global level-uniform consumer is abandoned as conjecturally vacuous; the
surviving restatement: **the L2-AVERAGED / Carleson-embedding, multiplicity-robust form of
the quotient bound** (small gaps do not kill averaged embeddings — Baranov's Bernstein/
embedding machinery applies). Next: state the averaged form exactly and Gate-3 it.

## 2026-07-18 session 2 (cont. 36) — Hamiltonian explicit + termination signature theorem;
## averaged consumer (AB) survives its acid test and RESTRUCTURES the wall; referee 3/3

**[HAMILTONIAN — DERIVED+VERIFIED]** `H(c) = h(c) e_2 e_2^T`, `h(c) = c/(c^2-d^2)^2`,
`t(c) = 1/(2(c^2-d^2))`: rank 1, ONE indivisible interval; the abstract trace-normalized
system is identical for all boxes (blindness persists — consistent with the trap); the
dichotomy sits in canonical-time depth-anchoring: `d^2 = lim_{t->infinity} c(t)^2`.
**TERMINATION SIGNATURE THEOREM (rank-2):** `RH-per-box ⟺ int_{c0} tr H dc < infinity for
every c0 > 0` — de Branges chain-regularity IS the exhaustion dichotomy. OFF-line: double
pole of h at `c* = |d|`; ON-line: triple pole at 0 (confluent). SOURCE DETERMINATION: h(c) is
source-computable POINTWISE at every admissible c (recovery theorem + source-checkable
admissibility); the assembled germ's left-endpoint continuation property is RH-per-box. LAW
CLASS: Krein's screw-function extension — extension iff the helical kernel stays PSD (cone/
survivor class) — **our H(c) is the box-local rank-2 germ of the corpus's Suzuki
canonical-system surface** (session-1 audit closes its loop). Next: express the box
screw-kernel PSD extension in the two-height joint moment matrix (the Krein/two-height
collision).

**[AVERAGED CONSUMER (AB) — STATED, ACID TEST PASSED, WALL RESTRUCTURED]** (AB): `mu_Xi =
sum m_rho delta_rho / K(rho,rho)` is Carleson for H(E) uniformly against the level-S
comparison. (i) AB => RH SURVIVES: the weight is LEVEL-INDEPENDENT and bounded below
(rank-2: `K(rho,rho) = 2c^3/pi` EXACTLY, d-free — referee-confirmed exact cancellation,
cross-checked two ways); one off-line fiber with `p^{2d}` dominates any positive average.
(ii) ACID TEST PASSED: on-line resolved pair embedding constant `= 2(c^2+delta^2)/(c^2+2
delta^2) <= 2` for ALL delta, continuous through collision — GUE small gaps kill only the
LOWER Riesz bound; AB is consistent-under-RH+GUE, non-vacuous, multiplicity-robust,
RH-forcing. (iii) WALL RESTRUCTURE vs cont. 34: (b2) DISSOLVES (balayage `J*Jf = sum m_rho
f(rho) K_rho / K(rho,rho)` replaces the extremal interpolant); (b1) DEMOTED (division enters
only the isometric identification); (b3) moot. NEW ROOM, exact: `sum m_rho (f f^#)(rho)` has
a SOURCE-SIDE explicit-formula representation; the wall concentrates entirely in the weights
`1/K(rho,rho)`, with on-line `K(x,x) = phi'(x)|E(x)|^2/pi` boundary-computable; residual
demand = INTEGRATED L1-comparability only — zero-repulsion demoted from per-fiber sup to
averaged form. **[NEXT — THE WEIGHTED EXPLICIT FORMULA]** Write `sum m_rho (f f^#)(rho) /
phi'(rho)` as a critical-line balayage integral; compute the rank-2 balayage exactly; collide
with `H(c)`.

**[REFEREE cont. 33-35 — ALL CONFIRMED]** Gamma tables vs Weil 1964 / Rao App. A / Tate
Corvallis 3.2.3 / Bushnell-Henniart 23.4; modulus law; self-dual normalization; HB iff
`c > |d|`; kernel d-freeness EXACT; bridge identity with opposite signs verified; separation
monotonicity; termination-marker coincidence.

## 2026-07-18 session 2 (cont. 37) — the weighted EF computes canonical time; the Krein law
## reads TYPE where positivity reads sign; THE PROGRAM FUSES INTO ONE OBJECT

**[WEIGHTED EF — DERIVED+VERIFIED]** (i) Unweighted divisor sums over squared tests = the
classical Guinand-Weil pairing (rank-2 confirms). (ii) The weights `1/K(rho,rho)` are Weyl
m-function residues: the weighted sum IS integration against the canonical system's CLARK
MEASURE; MRS/Totik Christoffel asymptotics are an exact IDENTITY in dB spaces
(`lambda(x) = pi/(phi'(x)|E(x)|^2)`). (iii) **RANK-2 VERIFIED: Clark mass = (pi/2c) * t(c)**
in BOTH configurations — the weighted explicit formula on the phase net computes the
CANONICAL TIME exactly; termination `c* = |d|` = Clark-mass blowup. (iv) FINAL WALL FORM:
RH-per-box ⟺ L1-comparability of two boundary measures per box — the Clark measure mu_c
(phase net, carries t(c)) vs the swept divisor measure nu — with the comparability constant
finite as depth -> 0. Transparency confirmed (continuous boundary data; sole quantifier =
sup over boxes/levels).

**[KREIN COLLISION — THE LAW SURVIVES, mechanism sharp]** (i) The naked string is blind
(`H ≡ e_2 e_2^T` all boxes); the anchored cross-height pairing `K(c,c') = F(c+c')` is a
HANKEL/WIDDER kernel: **depth-0 continuation ⟺ F completely monotone ⟺ the Bernstein measure
nu has EXPONENTIAL TYPE 0**, with `nu = (4m^2/pi) cos^2(delta*lambda)` on-line vs
`cosh^2(d*lambda)` off-line (exact). Off-line violation explicit: `F < 0` on
`(sqrt(2)*d, 2d)`; violating minor = a 1x1 diagonal. (ii) WHY IT SURVIVES cont.-30: positivity
cannot see support — but the Krein extension reads GROWTH TYPE, not sign, **and type is
exactly where support hides**. No analytic-reader contradiction (type-0 is a sup-over-depths
cone condition = the semialgebraic sign of e). (iii) Does not zero-shot RH: certifying type-0
from finite source data is the exhaustion demand in string costume — honestly carried.

**[THE FUSION]** nu's type `2d` IS the `p^{2d}` modulus asymmetry of the epsilon_S lane
(cont. 33): the averaged consumer (AB), the Krein string extension, and the metaplectic
comparison are THREE READINGS OF ONE OBJECT — a source-representable measure on the
boundary-Fourier (prime) axis whose EXPONENTIAL TYPE is the off-line displacement. THE
PROGRAM'S QUESTION IN FINAL FORM: **what unconditional arithmetic (Hilbert-reciprocity level
closure) bounds the TYPE of nu?** Next: compute the finite-source-level lambda-representation
of nu via the weighted EF; referee queue: cont. 36-37.

## 2026-07-18 session 2 (cont. 38) — nu identified and verified; equivalence honestly
## downgraded (Montgomery cousin); three bridges kept; the lambda = 0 diagonal is the target

**[DERIVED+VERIFIED]** `nu(lambda) = (1/2pi)[|dN-hat(lambda)|^2 + |dN-hat(-lambda)|^2]` — the
POWER SPECTRUM of the zero measure (Poisson-extension/Plancherel derivation; rank-2 exact
match with the Krein formulas). Source side (Weil EF): nu = the von-Mangoldt
pair-autocorrelation (sites `log(m/n)`, weights `Lambda(m)Lambda(n)/sqrt(mn)`, pole/arch
crosses). **UNIQUE-REPRESENTATION LEMMA** (unique factorization): each off-diagonal site
weight is FINITE and stabilizes EXACTLY once both prime powers <= S — ALL level-dependence
sits at the `lambda = 0` diagonal (`sum_{n<=S} Lambda(n)^2/n`, arch-regularized). Final
arithmetic form: RH ⟺ the arch-corrected von-Mangoldt pair-autocorrelation has exponential
type 0 (after pole subtraction; per-box: type = 2 max|Im gamma|).

**[NOVELTY GATE FIRED — equivalence reduces-to-known]** nu >= 0 is Montgomery's F-positivity;
EF-squared LambdaLambda sums = Montgomery 1973 / Goldston-Montgomery 1987 (F(alpha,T) is the
height-AVERAGED, T-normalized cousin); "off-line zero => exponential spectral mode" is the
classical psi(x)-error criterion squared. The equivalence is DERIVABLE — downgraded. **KEPT
(bridges, genuinely absent from literature):** (a) the single-box UNAVERAGED Krein reading —
type-0 as complete-monotone depth-0 continuation of the cross-height Hankel kernel; (b) exact
finite-level site stabilization — the precise object a reciprocity-level-closure bound must
control; (c) the fusion `type = 2d = p^{2d}` epsilon_S asymmetry.

**[REFEREE cont. 36-37 — NO GAPS]** All formulas re-derived independently (Hamiltonian ODE,
gauge, clock; Clark mass both configurations; F(sigma) by residues; Bernstein densities by
inverse Laplace; violation window solved exactly). Hygiene absorbed: add `c_max > |d|`
hypothesis at promotion; the verification record is weighted_ef_fix.py (the 4 False lines in
weighted_ef.py were sympy conjugate artifacts, cleared).

**[NEXT — the lambda = 0 diagonal]** The diagonal is the ONLY level-moving site: collide it
with the Clark mass t(c) (both are the "mass at the origin" of their frames); and restate
type-0 as PSD of SHIFTED HANKEL matrices in the stabilized site weights (the exact-identity
certificate class, on the arithmetic side at last).

## 2026-07-18 session 2 (cont. 39) — the clock-unit identity; the moment twin closes the full
## circle onto the box Hankel; the arithmetic Hankel frame honestly closed

**[COLLISION IDENTITY — DERIVED+VERIFIED]** `t(c) = F_osc(2c)/(c * Res_0 F)` with
`F_osc = F - Res_0 F/sigma`: canonical time = level-free off-diagonal data divided by the
arch-regularized diagonal — **the sole level-moving object is the UNIT OF THE CLOCK**;
level-dependence is pure recalibration; type lives in stabilized off-diagonal data.
Watson end reads all pairs (`a_{2k+1} = (-1)^k P_{2k}/pi`, pair power sums); pole end reads
the diagonal. Termination = pole of F_osc = type.

**[MOMENT TWIN — and the FULL CIRCLE]** (A) RH-per-box ⟺ `{mu_k := P_{2k}}` is a STIELTJES
moment sequence (Hankel + shifted Hankel PSD; the off-line atom at `u = -4d^2` kills the
shift; determinate by geometric growth). The FIRST inequality `mu_1 = P_2 >= 0` is
`N * p_2 - p_1^2 >= 0` on box Newton sums — **the 2x2 minor of the cont.-22 box
Hermite-Hankel matrix**: the entire nu/Krein/spectral chain closes its circle onto the
box-Hankel family. All faces of this program are ONE object — consistency proven; the
frontier remains the cont.-24 per-box positivity, now enriched by: the type/moment reading,
the clock-unit identity, the level-stabilization structure, and (below) the band-majorization
class. (B) The damped site-weight form is the same object with the depth quantifier
(congruent).

**[ARITHMETIC HANKEL FRAME — HONESTLY CLOSED]** Bookkeeping exact (all level motion in s_0;
every s_k, k >= 1, level-stable). Unsubtracted: total collapse (infinite band mass —
Chebyshev). Subtracted nu_sub (psi(x) - x autocorrelation): site weights unchanged, signed
continuous density cancels the mean growth, still a power spectrum (>= 0 UNCONDITIONALLY) —
hence PSD is AUTOMATIC wherever finite: **on the arithmetic side RH is CONVERGENCE, not
positivity** (`type(nu_sub) = 2 sup|beta - 1/2|` exactly; convergence at sigma_0 < 1 ⟺
zero-free strip of width sigma_0/2 — the classical wall in its cleanest form). Forced
normalization: the lambda = 0 diagonal (Montgomery's T log T in site costume) is the
normalizer. **[SURVIVING CERTIFICATE CLASS]** Band-by-band MAJORIZATION of the signed
continuous (pole/arch-cross) density by the positive LambdaLambda atoms — a comparison of two
explicit densities, not a positivity of one.

**[NEXT]** (i) Express the moment twin's minors in EF-squared source data via Newton's
identities and collide determinate-moment uniqueness with the recovery theorem (does
source-pointwise h(c) determine mu_k?); (ii) formulate the band-majorization statement
exactly and Gate-3 it (the majorization is level-stable off-diagonal data vs signed
continuum — check against the transparency catalogue and the classical density-theorem
literature); (iii) referee cont. 38-39; (iv) queue: analytic-T4; ST1; promotion batch.

## 2026-07-18 session 2 (cont. 40) — N=2 collapse verified; the separation-radius question
## carries the certificate; the PERIMETER THEOREM closes the arithmetic side; lemma repaired

**[MOMENT MINORS — VERIFIED]** Newton chain: `mu_k = sum_r (-1)^r C(2k,r) p_r p_{2k-r}` —
every Stieltjes minor is an explicit polynomial in source boundary integrals. **N=2 COLLAPSE
(verified):** for an isolated pair the full Stieltjes tower ⟺ `mu_1 >= 0` EXACTLY (`mu_k =
2^{2k+1} m^2 e^k`, rank-1 relations; unshifted Hankel unconditionally PSD; the shift carries
everything). General N: at most `N(N-1)/2` irreducible inequalities per box; variety
membership automatic. CAVEAT (verified): on-line points do NOT drop algebraically (`mu_1 =
-8 d^2 m^2 + 4 m m_s (s^2 - d^2)` — the cross term masks for `|s| > d`); they drop only
GEOMETRICALLY via the separation theorem. When isolation succeeds: the ENTIRE certificate is
ONE source-computable number `mu_1 = 2(p_0 p_2 - p_1^2)` per box. **[THE NEW CARRIER — a
GEOMETRIC question]** Quantify the separation radius vs d: does the innermost-box descent
always achieve pair isolation before the Jensen bound saturates? Discreteness-and-counting in
character — outside every killed mechanism class. This single comparison now carries the
whole certificate.

**[PERIMETER THEOREM — drafted, referee queued]** Band-majorization Gate-3: REDUCES-TO-KNOWN
(exact PNT-order cancellation `A + C + K = 0`; residue = psi-error autocorrelation; band
growth EXACTLY `e^{2dL}`; two-sided dictionary with von Koch in bands; any functional of band
masses factors through `sup|beta - 1/2|`). PERIMETER: every RH-certificate expressible through
the band-mass sequence of nu_sub is classically equivalent to the zero-free-region/psi-error
hierarchy; the faces NOT factoring through bands are exactly the lambda=0 normalizer and the
cross-band Stieltjes moments (the per-box analytic positivity). The arithmetic exploration is
CLOSED with a proven boundary.

**[REFEREE cont. 38-39 — verdicts applied]** (i) nu power-spectrum chain confirmed. (ii)
LEMMA REPAIRED: same-prime sites `lambda = k log p` carry infinitely many pairs — weight
`(log p)^2 p^{-k/2}/(p-1)`, geometrically convergent, NEVER exactly stabilizing; correct
statement: all DIVERGENT level motion at lambda = 0; cross-prime sites exactly stabilize
(unique reduced fraction); same-prime aggregate tail `O(S^{-1/2} log^2 S)`. (iii) collision
identity re-derived from scratch, confirmed (unified `t = 1/(2(c^2+e))`). (iv) moment
criterion confirmed + clause added: the mu_1-kill is rank-2-specific; mixed configurations
fail at a higher minor (determinacy pole argument). (v) the 2x2-minor identification
confirmed symbolically at generic N.

**[NEXT]** (1) THE SEPARATION-RADIUS COMPARISON (the certificate's carrier): formalize the
descent — given a hypothetical off-line zero at height gamma, displacement d, the innermost
admissible box must contain ONLY the pair; obstructors are on-line zeros within height-window
h of gamma; the descent shrinks h; discreteness guarantees isolation for SOME h > 0 — but
admissibility also demands w > b_min - 1/2-type bounds and generic edges; adjudicate whether
isolation is UNCONDITIONAL (pure discreteness — then RH-per-box literally reduces to
mu_1 >= 0 per isolated box, i.e. the innermost-box mu_1 is the program's FINAL OBJECT) or
carries a hidden density/repulsion demand. (2) Referee the perimeter theorem. (3) Queue:
analytic-T4; ST1; promotion batch (Hamiltonian/termination, separation, T4 chain).

## 2026-07-18 session 2 (cont. 41) — SEPARATION-RADIUS ADJUDICATED: unconditional, and
## stronger — the CO-HIGH REINFORCEMENT LEMMA turns the certificate into an EQUALITY

**[CO-HIGH REINFORCEMENT LEMMA — derived this lane, referee queued]** After HEIGHT-isolation
alone (shrink h below the minimal height gap — pure discreteness, unconditional; no
displacement bookkeeping needed), every surviving packet member is co-high with the target,
and ALL pair differences within a co-high packet are PURELY IMAGINARY in the u-frame:
(i) a co-high ON-LINE point has the same u-position as the packet center (on-line + co-high
=> coincident position; distinct co-high on-line points are impossible — multiplicity only);
(ii) a co-high second pair at displacement d' contributes differences `(i(d ± d'))^2 <= 0`.
Hence the masking case (cont. 40's `4 m m_s (s^2 - d^2)` with `s != 0`) NEVER occurs after
height isolation — it required an on-line point at a DIFFERENT height, which h-shrinking
excludes. Therefore: **`mu_1(height-isolated box) <= -8 d^2 m^2 < 0` if any off-line point
exists at that height; `mu_1 = 0` iff the packet is a single on-line point.**

**[THE EQUALITY-FORM CERTIFICATE — the program's final compressed object]**
> RH ⟺ for every height-isolated admissible box: `p_0 p_2 = p_1^2` — the CAUCHY-SCHWARZ
> EQUALITY case on three source-computable boundary integrals (equivalently: the box packet
> is a single point).
The certificate is an EQUALITY — exact-identity class, exactly what the cont.-22 law demands
(no margins, no estimates); its violation is quantized (`<= -8 d^2 m^2`). The production
question in final form: what source identity/symmetry forces the Cauchy-Schwarz equality on
height-isolated boxes? (It cannot be unconditional — it IS RH; it must flow from the source's
global structure: FE + EF + the corpus's identity stock. Equalities come from identities and
symmetries — the terrain where the source machinery is richest, and where estimates were
never going to work: the 26-cycle arc's conclusion in one sentence.)

**[NEXT]** (1) Referee this lemma + the equality form (elementary; the height-isolation
hypotheses need the same (h, w)-order care as cont. 21). (2) The production hunt for the
equality: inventory the corpus's exact-identity stock for statements of the form "boundary
quadratic = boundary square" (Parseval/Plancherel identities; the reflection-positivity
equalities; the Wronskian identities of the Hedenmalm surface) — the target
`p_0 p_2 - p_1^2 = 0` is a Gram-determinant vanishing = LINEAR DEPENDENCE of two
source-computable functionals — restate as: the functionals `f -> p_1` and `f -> p_2/p_1`...
better: the packet measure's first two moments are proportional to its zeroth — a RIGIDITY of
the boundary data. (3) Perimeter-theorem referee; analytic-T4; ST1; promotion batch.

## 2026-07-18 session 2 (cont. 42) — THE SLAB-GERM CERTIFICATE (refereed, repaired):
## unconditional admissibility on classical zero-free lines; corpus holds the target shape

**[REPAIRED CERTIFICATE — refereed]** Core algebra CONFIRMED (Lagrange identity for complex
points with multiplicities, no conjugation; reinforcement; the pure-pair value; the
co-high-specificity of equality⟺single-point — verified counterexample for non-co-high
packets: height-isolation is LOAD-BEARING). Two gaps found and FIXED: (GAP 1) narrow boxes
can exclude the pair — FIX: **the FULL-WIDTH SLAB `S(gamma, h) = [0,1] x [gamma-h, gamma+h]`**
— vertical edges on `Re s = 0, 1` where Xi is nonvanishing UNCONDITIONALLY (de la Vallee
Poussin + FE: the classical zero-free result enters as the unconditional input); all
displacements < 1/2 lie inside; horizontal edges automatically zero-free for `h <` (height
gap): ADMISSIBILITY IS AUTOMATIC — no generic-edge selection. (GAP 2) the height-isolation
quantifier was divisor-selected — FIX (verified): the GERM quantifier; `mu_1(S(gamma,h))` is
EVENTUALLY CONSTANT as `h -> 0+` (discreteness), the limit exists unconditionally, the family
is source-pure. (Minor: ordered/unordered factor-2 normalized.)

> **RH ⟺ for every gamma in R:
> `lim_{h -> 0+} (p_0 p_2 - p_1^2)(S(gamma, h)) = 0`,**
> where `p_k = (2 pi i)^{-1} ∮_{∂S} u^k (Xi'/Xi) ds` in the u-frame. The limit exists
> unconditionally; its value is `<= -2 d^2 m^2 (2 m_tot + m_s) < 0` at any off-line height
> and `0` elsewhere — the Cauchy-Schwarz equality case on three boundary integrals, violation
> quantized.

**[PRODUCTION SHORTLIST — corpus inventory]** (1) `primePairDifferenceEnergy_eq_two_mul_
pluckerGramDet` (XiPrimeSeamPairVariance.lean:131) — THE TARGET SHAPE ALREADY FORMALIZED:
pair-difference energy = 2 * GramDet, vanishing ⟺ single point. (2) The Hedenmalm Bezoutian
rank↔packet-size dictionary. (3) Hankel=Gram colligation (CompletedPrimeGammaResolvedMoment-
Colligation.lean). (4) The rank-two FE-Schwarz circuit [PROVED: dependence ⟺ critical line] —
the equality's natural source symmetry. (5) Mellin/Fourier unitarity stock. (6) Moment
determinacy templates. NEXT GATE-4 TARGET: splice the slab-germ certificate into (1)+(4):
the germ Gram-det in the seam-pair-variance frame, with the FE-Schwarz dependence law as the
candidate equality-forcing symmetry.

**[PERIMETER — corrected]** The A_S truncation formula was WRONG (rectangular vs triangular
domain); corrected: `A_S(L) = 2(1 - e^{-1/2}) S e^{-L/2} - 2(e^{1/2} - 1) e^{L/2}`
(numerically verified, ratio 0.9996). The bilinear cancellation SURVIVES (domain-
independent). One exponent calibration (d vs 2d frames) queued before promotion. Scope
corrected: the perimeter governs GROWTH-CLASS functionals only (band sequences encode
ordinates). Citations: von Koch 1901; Ingham Thm 30; Landau 1909 converse.

## 2026-07-18 session 2 (cont. 43) — d-vs-2d EXPONENT CALIBRATION RESOLVED (perimeter
## referee flag); convention note; cont. 33-40 exponent audit clean

**[CONVENTION NOTE — sympy-certified, band_major_gate3.py appendix (A)-(D)]** `nu_sub` AS
DEFINED (cont. 38: `|dN-hat(lambda)|^2` of the per-box FINITE packet) has band mass
`~ e^{2dL}` DEFINITIVELY: for atoms at `u = ±id` the power spectrum is exactly
`4m^2 cosh^2(d lambda)` with no window and no normalization freedom (band/e^{2dL} ->
`(e^{2d}-1)/(8d)`, finite nonzero); box-frame TYPE = `2d`, matching the Krein pole at
`sigma = 2d` and the `p^{2d} = e^{2d log p}` epsilon_S asymmetry. The referee's `e^{dL}`
reading came from the LAG band of the autocorrelation of the GROWING psi-error `~ e^{dw}`
without stating the w-normalization — and there the lag exponent is pure window-anchoring
convention: un-normalized low-anchored window gives `e^{+d lambda} * e^{2dW}` (divergence
books the other d), per-w normalized gives pure `e^{+d lambda}`, cutoff anchored on the
larger site (`m = n e^lambda <= S`) FLIPS it to `e^{-d lambda} * S^{2d}`. The invariant
rate is `2d` in every anchoring; only the box frame books it entirely in the spectral
variable. RULE: box-frame statements carry `2d`; any GLOBAL height-density statement must
state its w-normalization explicitly. (The 4th print label of band_major_gate3.py line 16
claimed `e^{2dL}` for a per-w-normalized integrand whose value is `e^{dL}` — label error,
not a card error; appendix supersedes it.)

**[EXPONENT AUDIT cont. 33-40 — ALL CORRECT, frames adjudicated]** (i) `p^{2d}` (cont. 33,
34, 36, 37, 38): mirror/two-leg squared frame (`|Xi(s)|/|Xi(1-s-bar)| = p^{2 sigma - 1}`) —
box-frame, correct. (ii) `p_{x+1}^d` per-level defect and `p^beta` fiber modulus (cont.
33/34): single-leg AMPLITUDE frame, correctly distinguished from the mirror ratio. (iii)
`type = 2d` / `2 sup|beta - 1/2|` / `2 max|Im gamma|` (cont. 37-39): box spectral frame,
correct; the `sigma_0/2` strip-width clause (cont. 39) is exactly consistent with type
`= 2d`. (iv) perimeter `band growth EXACTLY e^{2dL}` (cont. 40): correct in the box
convention; the residue-frame derivation now carries the normalization clause above. (v)
`S^{c-d}` (cont. 28-32): amplitude-frame ratio `S^{1/2+c}/S^{1/2+d}` — internally
consistent, and the dichotomy (`-> 1` vs `-> infinity`) is invariant under squaring to the
box frame `S^{2(c-d)}`; flag it amplitude-convention, no repair needed. No statement in
cont. 33-40 uses a wrong exponent; the calibration queued in cont. 42 is CLEARED for the
perimeter promotion.

## 2026-07-18 session 2 (cont. 44) — THE SPLICE SUCCEEDS: the certificate is the fiber
## decomposition of the canonical orientation energy; algebra core formalized (module 4)

**[SPLICE — VERIFIED]** Dictionary exact (slab-germ Gram-det = the XiPrimeSeamPairVariance
pluckerGramDet algebra with holomorphic squares in place of Hermitian norms). The FE∘Schwarz
composition fixes heights and KILLS THE FIBER MEAN (`sum m_j d_j = 0`, verified), giving
`mu_1(gamma) = -2 M(gamma) * sum_j m_j d_j^2` — the corpus weightedVariance identity with the
rank-one term annihilated by circuit symmetry. Define the LOCALIZED ORIENTATION ENERGY
`E_Xi(gamma) := sum_{rho in XiDivisorSupport, Im rho = gamma} xiHurwitzOrientationEnergyTerm
rho` (nonnegative regrouping of the master ~459 tsum). Then:

> **RH ⟺ E_Xi = 0 ⟺ (∀ gamma) E_Xi(gamma) = 0 ⟺ (∀ gamma) mu_1(gamma) = 0** — the
> slab-germ certificate IS the height-fiber decomposition of the corpus's canonical
> orientation energy, with each fiber's vanishing boundary-computable on an unconditionally
> admissible slab (equi-vanishing, NOT proportionality — the literal identity is false and
> degenerates at d -> 1/2, excluded by the de la Vallee Poussin edge input).

**[NAMED OPEN CORE — the germ-residue transport]** `lim_{h->0} p_k(S(gamma,h)) =
sum_{Im rho = gamma} m_rho u_rho^k` (argument-principle reading + eventual constancy):
card-refereed (cont. 42), NOT yet in Lean — the next formalization target. The RH-hard core is
unchanged in identity but RELOCATED: the row-415 source equality now needs to force only
`E_Xi(gamma) = 0` ONE HEIGHT AT A TIME against the slab boundary integral. Next Gate-2: state
the fiberwise row-415 demand exactly.

**[LEAN MODULE 4 — SHIPPED, commit 2e7a1390]** `RHTower/CoHighPacketGramCollapse.lean`
(371 lines, 10 mains, axioms = [propext, Classical.choice, Quot.sound]): the complex Lagrange
identity (proved from scratch, no conjugation), co-high collapse to real nonpositive
pair-energy, quantized violation, single-point characterization, isolated-pair value. The
slab-germ certificate's COMPLETE ALGEBRA CORE is now formal; the analytic layer (slab
contours + germ-residue transport) is the remaining Lean surface. (Calibration: cont. 43
appended by the calibration agent — box-frame type 2d definitive, downstream audit clean,
perimeter promotion unblocked.)

## 2026-07-18 session 2 (cont. 45) — the fiberwise demand is q_2 >= 0; the Bezoutian square is
## the production target; LEAN MODULE 5 ships the transport (chain Lean-anchored to two gaps)

**[FIBERWISE GATE-2 — STATED]** Row-415 quoted and localized: the slab boundary integrals are
the localization instrument; the divisor side `mu_1(gamma) <= 0` is PROVED, so the demand
halves to `mu_1(gamma) >= 0` from source structure — and since the circuit kills `q_1`, the
entire fiberwise demand is **`q_2(gamma) >= 0` at every height**: the germ second moment of
the slab pairing nonnegative. Equality then forces single-point fibers, `E_Xi(gamma) = 0` for
all gamma, RH. Assets: unconditionally admissible slab family; the divisor half free;
quantized violation.

**[OPEN CORE — the BEZOUTIAN SQUARE]** Verified: `q_0 q_2 - q_1^2` = germ of
`(1/2)(2 pi i)^{-2} ∮∮_{∂S x ∂S} (u - v)^2 (Xi'/Xi)(s)(Xi'/Xi)(t) ds dt` — the Hedenmalm
Bezoutian surface on the slab. The production demand: an EXACT source identity rewriting this
double integral as `∮∮ K(s,t) g(s) conj(g(t))` with K PSD — a square — with the FE∘Schwarz
circuit (height-fixing, ∂S-preserving) as the candidate symmetry, sourced on the
regular-Cauchy prime-Gamma span. Kill conditions: (a) divisor selection dead; (b) exact
identity only (quantized violation unreachable by epsilon-bounds); (c) if the circuit yields
only the known seam-charge reflection-oddness without the square: reduces-to-known, discard.
NEXT: collide the slab Bezoutian with the Hankel=Gram colligation (shortlist item 3) — is K
the colligation's defect kernel restricted to ∂S?

**[LEAN MODULE 5 — SHIPPED, commit 926cfdca]** `RHTower/SlabGermResidueTransport.lean`
(379 lines, 14 mains, axioms clean): thin adapter over
`rectIntegral_continuedPrimeArchSourceRelativeTrace_eq_closedRectangleZeroSum`
(XiGuinandWeilRectanglePeeling.lean:73) specialized to monomial tests — contour moments =
packet divisor moments (`slabContourMoment_eq_packetDivisorMoment`); eventual constancy with
explicit gap (`exists_slabGap`, height-fiber identification); germ limits =
height-fiber moments; and the GRAM GLUE to module 4: germ Gram real, <= 0, = 0 iff the fiber
is a single point — the certificate's divisor half is now FORMALIZED END TO END. Remaining
Lean gaps (logged): (i) full-width-slab admissibility adapter (Re s = 1 edge via zeta
nonvanishing; Re s = 0 edge via FE reflection — both classical, formalizable); (ii) the
production identity (the Bezoutian square — the open core above). The certificate chain is
Lean-anchored except these two.

## 2026-07-18 session 2 (cont. 46) — the defect IS the orientation energy; the square demand
## relocates to ONE AREA INTEGRAL; module 6 makes the divisor half unconditional

**[COLLISION VERDICT (ii) — with the structural prize]** The colligation Hankel=Gram holds
only for the polar leg (real nodes free); direct transport is circular (node-reality IS RH at
gamma). But the derivation yields the exact structure: on the mean-killed fiber,
**`Bez = q_0 q_2 - q_1^2 = det G_herm - 2 q_0 * E_Xi(gamma)`** — the defect between the
HERMITIAN Gram (conjugated pairing) and the BILINEAR Bezoutian is exactly the localized
orientation energy (rank-one after mean-kill; verified: gap `8d^2 = 2 * 2 * 2d^2` on the
model). Kill condition (c) fired for the circuit-only route (FE∘Schwarz reproduces the
bilinear H — the known seam reflection-oddness — never the Hermitian G). **[SURVIVES — the
relocation]** (a) RH at gamma ⟺ CAUCHY-SCHWARZ SATURATION of the germ pairing; (b) `G_herm`
is source-evaluable WITHOUT the divisor via the dbar/Green identity:
`∮_{∂S} conj(u) * u * tr ds = 2i [pi * sum m_j |u_j|^2 + ∫∫_S u * tr dA]` — boundary data
plus ONE AREA INTEGRAL. **[NEXT EXACT QUESTION]** Derive the Green identity exactly and
compute the h -> 0 germ of the area term `∫∫_S u * tr dA` (thin-slab area shrinking vs
near-zero blow-up of the trace): a vanishing or signed germ converts
`det G_herm >= 2 q_0 * E_Xi` into a boundary-computable inequality — **the square demand is
now one area-integral germ**.

**[LEAN MODULE 6 — SHIPPED, commit ee44d809]** `RHTower/SlabFullWidthAdmissibility.lean`
(341 lines, 9 mains, axioms clean): XiC nonvanishing on/beyond the strip edges (thin over the
corpus strip bound); full-width edge nonvanishing below the gap; the BAND-DODGE (`c` strictly
between the fiber's max offset and 1/2 — unconditional SlabAdmissible without the literal
c = 1/2 contour, so the FE reflection is unnecessary for transport); and the
HYPOTHESIS-FREE capstones: `exists_germResidueTransport_unconditional`,
`exists_slabContourGram_germ_unconditional`, `exists_slabContourGram_germ_eq_zero_iff`
(boundary Gram germ = 0 iff the full height fiber is a single point),
`tendsto_slabContourGram_unconditional`. **The certificate's divisor half is UNCONDITIONALLY
formalized end to end; the chain is open ONLY at the production identity.**

## 2026-07-18 session 2 (cont. 47) — Pompeiu proved; area germ vanishes; the demand in its
## purest form: the displacement-weighted boundary germ; referee fixes applied

**[POMPEIU LEMMA — PROVED, certified all h > 0, four configurations]**
`∮_{∂S} g f du = 2 pi i sum r_j g(u_j) + 2i ∫∫_S (∂_ubar g) f dA` (g smooth, f meromorphic,
simple interior poles); with `g = ubar u`: cont. 46's constants EXACT in the du-reading.
**[AREA GERM VANISHES]** `lim_{h->0} A(h) = 0` with the exact O(h) expansion (rectangle-PV:
xi-symmetry kills Re, eta-odd cancellation leaves O(h); log-blowup only as delta -> c,
EXCLUDED by the band-dodge/dlVP). **[GENERAL GERM THEOREM]** for holomorphic f, g:
`lim (2 pi i)^{-1} ∮ conj(f) g tr du = sum m_j conj(f(u_j)) g(u_j)` — the germ of the
conjugated boundary pairing IS the fiber Hermitian Gram: divisor-free boundary evaluation of
Hermitian fiber data established (at finite h the pairing is not even Hermitian — only the
germ is).

**[THE DEMAND — FINAL FORM]** On the imaginary fiber `u_j^2 = -|u_j|^2`, so the unconditional
germ identity `∮ (u^2 + |u|^2) tr du -> 0` holds: the Hermitian route REPRODUCES `q_2 >= 0`,
it does not bypass it; `det G_herm >= 0` is free and the demand is the reverse saturation.
Purest statement:

> **RH at gamma ⟺ `lim_{h->0} ∮_{∂S(gamma,h)} (Im u) * u * tr du = 0`** — the
> DISPLACEMENT-WEIGHTED boundary germ vanishes, where `Im u = 1/2 - Re s` IS the off-line
> displacement coordinate. The trace's germ must be blind to the displacement weight.

**[REFEREE cont. 44-46 — verdicts applied]** (i) cont. 44 CONFIRMED (fiber d -> -d symmetry
with multiplicity transport verified via the series substitution under
`xi(1 - conj s) = conj(xi(s))`). (ii) cont. 45 notational fix: the q_k are the CENTERED germ
moments (`u -> u - gamma`; Bez translation-invariant); centering kills Re q_1, mean-kill
kills Im q_1; centered `q_2 <= 0` always — the demand-vs-proved logic forces equality as
stated. (iii) cont. 46 identity CONFIRMED with the naming collision RESOLVED: the object in
the defect identity is the FIBER VARIANCE `V_Xi(gamma) := sum m_j d_j^2` — equi-vanishing
with cont. 44's Hurwitz-term energy `E_Xi(gamma)` on `|d| < 1/2` (numerically distinct;
disambiguated throughout).

**[NEXT MOVE — the 2D Pompeiu iteration]** The weight `(Im u) u = (u - ubar) u / 2i` is the
∂_ubar-potential of `u/2i`: iterate Pompeiu on the SECOND variable of the Bezoutian double
integral — rewrite `∮∮ (u - v)^2 tr tr` with the mixed weight `(Im u)(Im v)` and hunt the PSD
kernel there, where the double area term carries a genuine 2D germ (the first genuinely
two-variable object of the production hunt).

## 2026-07-18 session 2 (cont. 48) — the REALITY LAW; the demand is one real scalar function
## per height; MODULE 7 ships the displacement-germ equivalence

**[2D ITERATION — closed honestly, with the prize]** (i) Plain mixed weight: exact finite-h
factorization `D_plain(h) = B_0(h)^2`, germ = `(sum m_j d_j)^2 = 0` by mean-kill —
unconditional, no demand. (ii) Germ table: `lim B_k = i^k mu_{k+1}` (odd fiber moments vanish
unconditionally); the Bezoutian combination has germ `2V^2` — SIGN-INERT (any PSD
representation proves nothing; the PSD hunt on it is structurally empty — discarded). (iii)
No polynomial kernel yields a fiber-linear germ; the only linear class is the singular
Hermitian kernel `1/(u - vbar)` (PV on the contour — the parallel probe). **[THE REALITY
LAW]** The conjugation law `tr(ubar) = conj(tr(u))` holds EXACTLY (from
`xi(1 - conj s) = conj(xi(s))`, no fiber hypothesis); with contour conj-symmetry it makes
`b_k(h) := -i B_k(h)` REAL AT EVERY FINITE h (and the q_k real at finite h too). **THE DEMAND
IN ITS FINAL SCALAR FORM:**

> Per height gamma: `b_1(h)` is ONE real-valued, source-computable, divisor-free scalar
> function of h with unconditional limit `V_Xi(gamma) >= 0`;
> **RH ⟺ `lim_{h->0+} b_1(h) = 0` at every height.**

Two probes designated: (P1) `db_1/dh` — the moving-edge derivative is an explicit
two-vertical-edge integral; derive its sign/monotonicity structure from the source side;
(P2) the singular kernel `1/(u - vbar)` germ table (the unique fiber-linear class).

**[LEAN MODULE 7 — SHIPPED, commit d54df239]** `RHTower/SlabConjugatedGermTheorem.lean`
(591 lines; axioms clean): the thin-slab trick made EXACT (the centered fiber is purely
imaginary; conjugated germs reduce to module-5 transport — no Pompeiu machinery needed);
`exists_conjugatedGermTheorem` at ALL bidegrees; `heightFiberHermitianGram_one_one` = fiber
variance; exact finite-h defect decompositions with pointwise O(h) bounds; and
`exists_displacementGerm_rh_equivalence`: reflected displacement moment `= i * V_Xi(gamma)`,
vanishing ⟺ fiber on the critical line ⟺ single point ⟺ module-6 Gram zero. Honestly-stated
open surface: the defect contour terms `-> 0` as `h -> 0+` (one trace-edge log estimate).
SEVEN Lean modules; the certificate is Lean-stated end to end modulo the defect-edge estimate
and the production identity (now: the sign structure of `b_1`).
