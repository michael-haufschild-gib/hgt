# RH source-intervention experiments

**Status:** numerical source obstructions and two algebraic modules with eighteen proved theorems; no RH solution, no route retired. The central Hankel proof attack is paused. Numerical counterfactuals below change the source and do not disprove RH.

The route survey exposed recurring gaps in signed arithmetic cancellation, propagation across scales, and preservation of orientation. We tested mechanisms at three different source interfaces, then let failures determine the next experiments. The frozen statements and adaptive protocols are in [EXPERIMENTS.md](EXPERIMENTS.md). This is exploratory evidence, not a finite certificate for an infinite inequality.

## Main discoveries

### 1. Theta compensation can lose and regain its sign as a tiny contaminant is added

The first mass-matched scan retained the sign in all **4,704** one- and two-atom replacements. Polarizing the infinitesimal response then exposed **9 negative mixed entries among 2,100 tested triples**. Diagonal responses differed by many orders of magnitude. This directed the search to mixture weights below the initial grid's minimum .01.

That intervention found a narrow negative region between positive regions. It is visible in [theta-contamination.png](theta-contamination.png). A concrete, independently verified witness is:

- Left source point `x₀=log(6/π)/2`, displacement `t=.003`, center `u=x₀+t`, homotopy parameter `λ=0`.
- Preserve the actual higher-tail Laplace mass `τ=0.0000003045995948944022109514203828567839…` at `x₀`.
- Replace its normalized tilted spectral distribution by weights `1−ε, ε` at nodes `3,255`, with **exact decimal `ε=.0000026`**.
- The complete third compensation is **`−1.82305179046807098037849942023922… × 10⁻²¹`**.

The counterfactual log likelihood is explicitly

`log(1+τ[(1−ε) exp(−3(A(x)−6))+ε exp(−255(A(x)−6))])`, where `A(x)=π exp(2x)`.

Independent differentiation of this log likelihood and of the original compensation agrees with the analytic jet formula at 80 and 120 decimal digits. See `regime-diagnostics.json`. Pure atoms and coarse mixtures missed the intermediate failure: componentwise positivity does not explain the mixture.

The failure persists after preserving **mass, mean, and second moment** of the actual tilted tail. At `t=.0001`, use nodes

`3, 3.44016541191573104366880362820334…, 255`

with normalized weights

`.899029572600972908871258515280332…, .100970424399027091128741484719668…, .000000003`.

The result is **`−5.39469231966272532956021325032690… × 10⁻³³`**. These nodes and weights come from the moment equations, not a tolerance-based optimizer. The equations and independent differentiation were checked at 80/120 digits, and the theta cutoff was doubled from 40 to 80; displayed digits were unchanged. See `moment-witness-validation.json`.

**Interpretation:** low-order mass statistics can conceal a direction that changes orientation. The actual theta source satisfies additional differential shape laws. Every negative compensation in that initial moment-dissection batch had negative lower-transport curvature `H''`; the literal source has a Lean proof of `H''>0`. The counterfactuals therefore identify information erased by the intervention, not a failure of the source theorem. Preserving three normalized moments yielded no negative value among 112 admissible probes; this does not establish sufficiency.

### 2. The surviving balance uses different combinations of terms in different regions

Write `M'''=−W'''H−3W''H'−3W'H''`. The candidate bridge “the first two terms have nonnegative sum and `W'≤0`” survived the moment dissection but failed in **477 of 5,472** adversarial multi-atom evaluations. These failures retained positive action, the basic positive source jets, `H<0`, `H'>0`, and `H''>0`.

The complete compensation stayed positive in those cases: the negative two-term sum was extremely small relative to the positive third term. Its largest observed adverse ratio was **`2.162 × 10⁻¹¹`**. All observed negative two-term sums had action at least **27.988**; positive sums also occurred at larger action, so action is not a complete classifier. That bounded batch found no case with `H''>0` and `M'''<0`. The [escaping-atom attack](boundary-followup/ESCAPE-REPORT.md) now supplies such a counterfactual even at left scale six with actual mass and first moment preserved; B1 is rejected numerically.

An exact algebraic residue makes the missing boundary explicit. In the nondegenerate physical domain, set

`A=−dq`, `B=−H`, `v=t a`, `b=(exp(q)+1)/(exp(q)−1)`,
`r=−dv/(v A)`, `s=H'/(B A)`, `h=H''/(B A²)`.

Then

`M'''/(v B A³) = (b²−1)[12(r−b/2)(s−b/2)−1] + 3h[(6+4b)r−2(b²−1)]`.

The first two channels have a **hyperbolic sign boundary**. If `L=(6+4b)r−2(b²−1)>0`, the exact curvature threshold is

`hcrit=(b²−1)[1−12(r−b/2)(s−b/2)]/(3L)`.

See [MATHEMATICAL-RESIDUE.md](MATHEMATICAL-RESIDUE.md) for the derivation and formalization scope. The source-facing problem is now explicit: prove the actual source has `h≥hcrit`, including where `hcrit>0`. Positivity of `h` alone does not supply that comparison. This bridge preserves the signed contributions that the rejected simpler cones discard.

### 3. Larger prime groups help, but the tested arithmetic classes are not stable

We compressed literal outer-prime symmetric translations onto Legendre spaces satisfying both pole constraints. For matrices `Tₚ`, compare the full saving `Σ‖Tₚ‖−‖ΣTₚ‖` with the saving retained by a partition into groups.

At aperture `a=2.2`, basis 96, the 18-prime packet gives:

| Largest group | Fraction of full saving captured |
|---|---:|
| 2, computed optimal matching | .27162 |
| 3, computed optimal partition | .43214 |
| 4, feasible partition / solver upper bound | .54351 / .57023 |
| 9, contiguous-log split | .78223 |
| 9, modulo-6 split | .75038 |

Grouping exposes collective interaction that pairs miss. It does **not** yet expose intrinsic prime types. Against 512 fixed-seed random balanced splits, the modulo-6 split falls from the **85th percentile at basis 64 to the 26th at basis 96**. After moving the same weighted atoms to evenly spaced shifts, it reaches the **99.8th percentile** at basis 96. The arithmetic label alone therefore does not explain the effect. See [prime-grouping-controls.png](prime-grouping-controls.png).

The smaller four-prime packet at `a=1.4` also shows why basis refinement matters: the literal pair/full ratio is `.3902` at basis 40, `.5315` at 64, and `.5380` at 96. A downward extrapolation from the first two basis sizes was misleading. Doubled overlap quadrature reproduces the reported grouping comparisons.

**Consequence for the user's grouping idea:** classify contributions by a stable interaction mechanism, retain cross-group terms, and distinguish a useful finite partition from an exhaustive classification of zeros. This experiment provides no assignment of a zeta zero to a prime class. Frequency modulation and finite-phase recurrence are corpus-derived explanations to investigate for the changing dominant modes; operator-level norm invariance under finite constraints is not claimed proved here.

### 4. Möbius cancellation is not a blockwise monotonic process

For `Cᵣ(N)=Γ(r) Σ_(m≤N<n≤2N) μ(m)μ(n)/(m+n)ʳ`, the frozen nonpositivity claim fails at `N=256`:

`C₁.₀₁(256)=.011753821964101240959321493565… > 0`.

Independent integer convolution and Laplace quadrature agree to about `2×10⁻¹⁸`; `r=1.5` is also positive. Across the literal dyadic sample `2⁸…2¹⁷` and five exponents, 5/50 cross values are positive. Sign-shuffled controls preserving squarefree support and dyadic charge can exhibit similar behavior, so the pattern is not specific enough to provide a Möbius producer.

The interaction map reveals delayed reinforcement and compensation. For block `(256,512]`, interaction with the next three blocks reinforces rather than repays its energy; interaction with all later sampled blocks through `2¹⁸` compensates it. For `(512,1024]`, the aggregate later sampled interaction still reinforces it. Thus neither monotone addition nor the tested fixed repayment horizon explains the bounded-return mechanism. These finite observations do not decide an eventual or cofinal return law. See [mobius-interaction-map.png](mobius-interaction-map.png).

## Evidence, reproducibility, and limits

All numerical work ran on the authorized Runpod in `/root/rh-route-surprise-20260906`, with up to eight Python processes and one BLAS/OMP thread per worker. Each numerical batch had a 120-second external limit; the longest reported completed numerical batch took **12.83 seconds**. No hour-long search was run. Local work consisted of source inspection, editing, and Lean verification.

Environment: Python 3.8.10, NumPy 1.24.4, SciPy 1.10.1, mpmath 1.3.0; matplotlib 3.7.5 installed into the run folder's private `plotlib` directory for figures. The two reused helpers are unchanged copies from `weil-polar-ground-energy/weil_polar_galerkin.py` and `clg-ttf-c5-homotopy-numerical-test/clg_compensation.py`.

Run the scripts in this folder remotely, in order: `mobius_blocks.py`, `prime_coalitions.py`, `tail_interventions.py`, then their adaptive scripts. `prime_coalitions.py --basis 64 96 --apertures 1.4 2.2 --output prime-refinement.json` reproduces the refinement. `regime_diagnostics.py` consumes `tail-channel-attack.json`; `make_figures.py` consumes the saved results. For plotting use `PYTHONPATH=/root/rh-route-surprise-20260906/plotlib`. JSON files preserve parameters, seeds, witnesses, timing, optimizer gaps, and validation results.

Finite Galerkin norms, optimizer output, and high-precision values are numerical evidence. No numerical result is used in Lean. Four-atom partition optimizations at basis 96 reached their time limits; both feasible values and upper bounds are retained. No positivity census is presented as an all-degree or all-scale proof.

Formal audit: `ThetaCuspC5BoseHyperbolicReserve.lean` passes scratch and source `lake env lean` checks and its named-module final build. Its eight algebraic theorems have only the standard `propext`, `Classical.choice`, and `Quot.sound` dependencies. The module is wired into `RHTower.lean`; no umbrella build was run. Only missing prerequisite oleans were supplied, in separate foreground checks. The final follow-up build compiled the needed `SuzukiCriticalRootedBianchiCofinalNoGo` dependency and then the reserve leaf. This verifies the algebraic bridge, not the experimental inequalities.

Repository-wide `scripts/formal_tools.py lint` passes after index regeneration, with existing large-file warnings. The follow-up moment-transport module also passes its ten theorem axiom audits and named-module build; see [the scoped audit](boundary-followup/ESCAPE-REPORT.md).

Corpus starting points: `MobiusLaplaceGammaHankelWall`, `MobiusIntegerCuspConfinement`, `CCMRestrictedWeilPrimeInterference`, `ThetaCuspLikelihoodSpectralMeasure`, `ThetaCuspFixedActionC5LikelihoodHomotopyCurvatureReduction`, `ThetaCuspLikelihoodHomotopyLowerTransport`, `ThetaCuspLikelihoodHomotopySeamRatioOrientation`, and `ThetaCuspLikelihoodHomotopyCurvatureEnergy`. Global corpus searches also explored interference, source births, cubic polarization, modulation, and transport ratios in `HTGeometry`, including `NilpotentContractionInterference` and `ConstraintMotiveRelativity/PrimePhasePortRecurrence`. The scientific-method guide and both RH ledgers determined the experimental scope. No literature or pretrained assertion is used as a claimed discovery.

The numerical source failures are not universal no-go theorems. The exact moment family does prove that fixed positive mass and first moment alone cannot bound a second moment; its scope is recorded with the escaping-atom result.

## Current mathematical next steps

1. The actual threshold `h>=hcrit` remains open. Generic positive mass and first-moment constraints, even with positive lower-transport curvature, are insufficient in the enlarged source class ([validated witness and formal residue](boundary-followup/ESCAPE-REPORT.md)). This positivity investigation is paused; the active experiment inspects exact signed arithmetic remainders without a PSD or energy producer.
2. Test prime classifications by stability under basis refinement and source interventions, then identify what cross-group estimate a proof would require. Current residue-class evidence is insufficient.
3. Find a source-specific recurrence mechanism for signed Möbius block interactions; squarefree support and preserved block charges do not distinguish the observed cancellation adequately.

Even a completed structural-tail compensation proof would still need the remaining compact/core and global packet/completion steps in the CLG chain. RH remains unresolved in this workspace.
