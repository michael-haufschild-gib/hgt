# Ordered Wold lower-Hardy ray injectivity

- **ID:** T2-WOLD-RAY
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `rh-current-frontier-map.md` · T2 ordered-prime shell defect
- **Statement:** The canonical scalar Wold residual lower-Hardy kernel, restricted to one cofinal negative-imaginary ray, is coefficient-faithful: eventual vanishing is equivalent to vanishing of every centered ordered Wold residual coefficient and to vanishing of the full unit-Lipschitz log-mesh transport current.

## Goal

Close T2's source-faithful scalar landing problem without asserting forbidden compact-open bubble
continuity or upper-half continuation.  Convert the physical residual edge kernel into a generalized
Dirichlet series on actual prime-log frequencies and recover its source coefficients from one
interior Laplace ray.

## Gates

- [x] 0 → 1  in-progress: source-pure conjecture derived from corpus transport current, residual damping, and generalized Dirichlet injectivity
- [x] 1 → 2  fully-proven: complete paper proof below, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean theorem package in `XiHeatCassiniWoldLowerHardyRayInjectivity`, target build green, axiom audit standard
- [ ] 3 → 4  publication-ready: standalone theorem note plus external expert novelty review

## Frozen claim

Write `h_N = log p_N` and let `R_N` be the centered ordered Wold residual.  Define the node boundary

`a_0 = R_0`,  `a_(N+1) = R_(N+1) - R_N`

and the generalized Dirichlet series

`D(s) = sum_N a_N exp(-h_N s)`.

Prove unconditionally:

1. `sum_N |R_N| / p_N < infinity` and `sum_N |a_N| / p_N < infinity`.
2. For every real `x >= 1`, the canonical lower-Hardy edge kernel satisfies
   `K(-i x) = D(x)`.
3. If `K(-i x)=0` eventually as `x -> +infinity`, then every `a_N=0`, hence every `R_N=0`.
4. Conversely, coefficientwise vanishing makes `K` identically zero.
5. Therefore eventual scalar-ray vanishing, coefficientwise Wold-source vanishing, and annihilation
   of every unit-Lipschitz prime-log observable by the transport current are equivalent.

No claim of actual vanishing, RH, critical-gap energy, critical-wall absolute variation, or
upper-half continuation is included.

## Approach

Use the corpus square-root-log estimate for `R_N`.  The Burnol subordinate-prime summability theorem,
with damping parameter halved, turns it into the `ell^1(p^-1)` statement.  The discrete node boundary
inherits the same weighted summability by the triangle inequality and monotonicity of prime-log
heights.

At `z=-ix`, every negative prime character is `exp(-h_N x)`.  Absolute convergence permits the
edge-to-node summation-by-parts identity.  The node series has strictly increasing positive
frequencies `h_N`.  Apply the corpus generalized Dirichlet uniqueness theorem at abscissa one:
eventual zero on a far-right real ray forces every node coefficient to vanish.  The recurrence
`a_(N+1)=R_(N+1)-R_N`, beginning with `a_0=R_0`, then forces every `R_N=0`.

## Proof

**[PROVED HERE]** Corpus theorem
`exists_xiHeatCassiniOrderedWoldResidualLogDiscrepancy_exp_rate` gives positive `c`, nonnegative `B`,
and eventually

`|R_N| <= B exp(-c sqrt(log p_N))`.

`burnolSummable_poissonWeight_logPow` at parameter `c/2` and log order zero proves

`sum_p B exp(-c sqrt(log p))/p < infinity`.

Finite initial terms do not affect summability, so `sum_N |R_N|/p_N` converges.  Since
`p_(N+1) >= p_N`,

`|a_(N+1)|/p_(N+1) <= |R_(N+1)|/p_(N+1) + |R_N|/p_N`;

hence `sum_N |a_N|/p_N` converges as well.  Because `exp(-h_N)=1/p_N`, this is absolute convergence
of `D` at real abscissa one and therefore at every `x>=1`.

Let `A_N(x)=R_N exp(-h_N x)` and `B_N(x)=R_N exp(-h_(N+1) x)`.  Both series are absolutely
summable for `x>=1`.  The node recurrence gives

`a_0 exp(-h_0 x)=A_0(x)`,

`a_(N+1) exp(-h_(N+1) x)=A_(N+1)(x)-B_N(x)`.

Separating the first term and reindexing the absolutely convergent tails yields

`D(x)=sum_N A_N(x)-sum_N B_N(x)
     =sum_N R_N (exp(-h_N x)-exp(-h_(N+1) x))
     =K(-ix)`.

The frequencies `h_N` are strictly increasing and `h_0>0`.  If `K(-ix)` is eventually zero, so is
`D(x)`.  Generalized Dirichlet coefficient recovery gives `a_N=0` for every `N`.  Induction from
`a_0=R_0` and `a_(N+1)=R_(N+1)-R_N` gives `R_N=0` for every `N`.  The converse is termwise.
Combining this classification with the already formalized exact unit-Lipschitz edge probes proves
that the scalar lower-Hardy ray and the nonscalar transport current have precisely the same source
kernel.  No premise remains.

## Hostile audit

- **Circularity:** none.  No Xi zero, divisor, RH, critical-energy, or continuation premise occurs.
- **Compact-open no-go:** no conflict.  The theorem uses a fixed interior lower-half-plane ray and
  generalized Dirichlet asymptotics.  It does not define a sequentially continuous scalar charge
  on multiplicity-matched escaping bubble families.
- **Upper-half no-go:** no conflict.  All evaluation points have negative imaginary part and move
  deeper into the unconditional Hardy domain.
- **Degeneracy:** excluded.  Eventual zero on only one scalar ray already recovers every source
  coefficient, and the final theorem identifies its kernel with the complete unit-Lipschitz current.
- **What remains:** theorem closes T2 scalar `LAND`/source-faithfulness.  It does not supply the
  actual inverse-log shell defect, critical prime-gap energy, or signed subhalf continuation
  (`ORD + COF`).
- **Literature audit (2026-08-28):** coefficient uniqueness for general Dirichlet series is classical;
  modern background explicitly treats strictly increasing frequencies and coefficient recovery,
  e.g. [Schoolmann, *On Bohr's theorem for general Dirichlet series*](https://doi.org/10.1002/mana.201800542).
  Searches for Wold residual, ordered prime-log edge current, and lower-Hardy ray combinations found
  no matching construction or this exact coefficient/source-kernel theorem.  Novelty claim is the
  arithmetic Wold application and exact transport-current identification, not generalized
  Dirichlet uniqueness itself; external expert audit remains required for publication.

## No-go closure

- **Exact killing theorem/mechanism:** ordinary compact-open scalar reporters erase
  multiplicity-matched escaping Wold bubbles; critical absolute graph variation is incompatible
  with critical mesh energy.
- **Strongest positive survivor:** one fixed lower-Hardy interior ray is a coefficient-faithful
  scalar reporter under the source's unconditional Laplace summability.
- **New insight:** compact-open scalar blindness is topological, not algebraic.  Scalarization retains
  the complete ordered Wold source when tested in the proper noncompact interior-ray topology.
- **Status:** dependency-closed paper proof and Lean formalization complete.  Main declarations:
  `xiHeatCassiniWoldResidualLowerHardyKernel_neg_mul_I_eq_nodeDirichletSeries`,
  `eventually_lowerImaginaryRay_woldResidualLowerHardyKernel_eq_zero_iff`, and
  `eventually_lowerImaginaryRay_woldResidualLowerHardyKernel_eq_zero_iff_current_zero`.

## Lean audit

- Source: `formal/GaloisForLFunctions/RHTower/XiHeatCassiniWoldLowerHardyRayInjectivity.lean`
- Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
- Direct check: `lake env lean GaloisForLFunctions/RHTower/XiHeatCassiniWoldLowerHardyRayInjectivity.lean`
- Target build: `lake build GaloisForLFunctions.RHTower.XiHeatCassiniWoldLowerHardyRayInjectivity`
- Axioms: `[propext, Classical.choice, Quot.sound]`

## Log

- 2026-08-28 — corpus-first conjecture from Wold transport exactness, source damping, and generalized Dirichlet injectivity.
- 2026-08-28 — `[PROVED HERE]`; formal source check, target-only build, umbrella wiring, and standard-axiom audit complete.
