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
