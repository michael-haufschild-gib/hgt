# Finite polynomial certificates for the completed Xi root budget

- **ID:** PAPR-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** Explicit zero-constant polynomials recover root mass from positive energy moments, giving finite source certificates for every proposed nuclear-root ceiling.

## Proof chain and scope

Literal completed prime--Gamma moments → positive source realization → complete Hankel positivity → RH. The current corpus excludes summable positive roots and proves cofinal root-budget escape by compactness. This task seeks explicit finite linear moment certificates for that cost. It does not claim a source positivity theorem or completion of RH. Route C1 is the direct application; other moment/trace routes can use the generic result only after proving their own coefficient-faithful identification.

## Plan

- [x] Read frontier live cores/candidate interfaces and universal constraints; search full declaration index for root budgets, polynomial approximation, Schatten moments, and spectral dust.
- [x] Audit existing `OrderedRootBudgetMomentCompactness`, `PrimeArchMomentRootBudgetEscape`, `GammaSewnPluckerGlobalMeanMomentNoGo`, and ordered Xi Schatten threshold.
- [x] Prove scalar polynomial recursion, zero constant, trace domination, monotonicity, and root convergence in scratch.
- [x] Prove exact finite moment evaluation and error budget; recover summable root mass or prove divergence for nonsummable roots.
- [x] Apply to completed moments, preserving all multiplicities, without assuming RH in the exported arithmetic alternative.
- [x] Direct Lean checks, named leaf builds only, axiom audit, umbrella wiring; update current-state frontier and route-independent constraints.
- [x] Final formal lint and whitespace check.

## Conjecture loop and paper proof

1. **Rejected:** uniform approximation of square root permits summing its error over an infinite spectrum. Uniform error alone has no summable majorant; multiplying it by infinite rank is invalid. Positive survivor: approximants must vanish at zero with a stage-dependent linear majorant in the energy variable.
2. **Proved survivor:** `P₀=0`, `Pₙ₊₁=Pₙ+(X−Pₙ²)/2`. For `0≤x≤1`, induction gives `0≤Pₙ(x)≤Pₙ₊₁(x)≤√x` and `Pₙ(x)≤nx/2`. The error factorization is `√x−Pₙ₊₁(x)=(√x−Pₙ(x))(1−(√x+Pₙ(x))/2)`, so pointwise convergence follows geometrically when `x>0`, and is exact at zero. Every stage trace is finite for a square-summable root sequence. Finite prefix limits recover all root mass; hence bounded stage traces imply root summability, and nonsummable roots force divergence.
3. **Arithmetic test:** under the internally derived complete Hankel criterion, completed moments equal all ordered Xi energy moments. Their root sequence is square-summable, is not summable, and lies below one. Therefore the polynomial source certificates diverge. If the cone fails, its definition gives a finite negative Hankel witness. This is an unconditional alternative, not a choice of the RH branch.

4. **Quantitative extension, proved:** write `eₙ=a−Pₙ(a²)` for `0≤a≤1`. Then `eₙ₊₁≤eₙ−eₙ²/2`. Induction against `2/(n+2)` gives a uniform scalar error. Apply this only to the first `K` roots; apply the energy majorant to the infinite remainder. With `Cₙ=ΣₖPₙ(aₖ²)` and `S_K=Σ_{k<K}aₖ`,

   `S_K−2K/(n+2) ≤ Cₙ ≤ S_K+(n/2)Σ_{k≥K}aₖ²`.

   Since `Pₙ=XQₙ`, the certificate is the finite sum `Σ_r coeff(Qₙ,r) M_r`. The triangle inequality gives error at most `Σ_r |coeff(Qₙ,r)| |ΔM_r|`. No infinite series is rearranged without summability.

## Exact formal surface

- `formal/GaloisForLFunctions/HTGeometry/PolynomialRootBudget.lean`: scalar recursion, trace/moment identity, root-summability classification, divergence, finite coefficient-error inequality, and the two prefix/tail inequalities; 18 theorems.
- `formal/GaloisForLFunctions/RHTower/PrimeArchPolynomialRootBudget.lean`: `primeArch_negative_hankel_or_rootBudget_escape`, `exists_primeArch_finite_rootBudget_certificate`, and `primeArchRootMomentCertificate_le_cost_add_error`.
- The main arithmetic alternative has no hypotheses. Generic analytic estimates retain their stated positivity, contractivity, summability, and ordering conditions; none assumes RH or an unproved arithmetic landing. The existing ordered Xi enumeration retains every multiplicity and both reflection copies.

## Route and novelty audit

C1 receives a concrete finite certificate family and a perturbation budget. The generic statements are available to any other trace/moment route after its own source identification. No STC/CSB comparison, U degree-uniform positivity, K-RVM source construction, or other branch's arithmetic order gate is closed here. The recursion has rapidly growing degree; neither an efficient evaluation scheme nor a numerical first obstructing index is claimed. The arithmetic alternative does not determine which branch holds. RH remains unproved and undisproved.

## Attribution and novelty boundary

The approximation recursion is classical (Rudin, *Principles of Mathematical Analysis*, Chapter 7, Exercise 23); the independently written derivation in [Matt Rosenzweig's note](https://matthewhr.wordpress.com/2013/06/21/proving-stone-weierstrass-without-weierstrass/) records the same recursion and error factorization. No novelty is claimed for polynomial approximation or monotone convergence. Intended new corpus contribution: a concrete certificate functional, its perturbation budget, and its multiplicity-faithful completed-Xi application. Search misses do not establish research priority.

## Verification

- Scratch direct checks passed for both proofs; production arithmetic direct check passed.
- `lake --old build GaloisForLFunctions.HTGeometry.PolynomialRootBudget`: exit 0, new leaf built.
- `lake --old build GaloisForLFunctions.RHTower.PrimeArchPolynomialRootBudget`: exit 0, new leaf and required root-budget dependency built. Existing dependency warnings/informational messages were replayed; the new leaves emit no warnings.
- `lake env lean /tmp/hgt-polynomial-root.3tYEoN/Audit.lean`: exit 0; all 21 new theorem closures use only `propext`, `Classical.choice`, and `Quot.sound`.
- Both leaves are imported by their area umbrellas; no umbrella or full build ran. Generated declaration indexes refreshed.
- `python3 scripts/formal_tools.py lint`: final exit 0, existing file-size warnings only. Initial lint exposed a tracked, unchanged RH module absent from its umbrella: `EulerDeletionBalancedPeriodCurvatureNoGo`. Its direct check and named leaf build passed; its missing import was restored. No theorem bodies in that module were changed.
- `git diff --check`: exit 0. No numerical experiments or computational proof certificates are used. Existing unrelated worktree changes and other agents' Lean processes are outside this task's ownership.
