# Finite physical sampling preserves the restricted Weil ground energy

- **ID:** RW-SAMPLE-GROUND
- **Stage:** 3-formalized
- **Type:** THEOREM; named leaves and standard-axiom audit passed
- **Source:** Route RW in `docs/reports/rh-current-frontier-map.md`.
- **Statement:** At every positive aperture, any arbitrary finite prescription of strict-interior physical source values leaves the exact pole-constrained Weil Rayleigh infimum unchanged.

## Mathematical statement

Fix an aperture `a>0`. Let `D_a` be the actual complete archimedean form domain, `J_a` its injective physical L² embedding, and `Q_a` the complete arithmetic Weil source quadratic, with all Gamma, prime and polar terms retained. Let `V_a` be the closed sector with both exponential pole coordinates zero, and let `mu(a)` be its ground-energy infimum. For a finite set `S` contained strictly in `(-a,a)` and arbitrary values `v:S→C`, let

`R(a,S,v) = {Q_a(g)/||J_a g||² : g∈C_c^∞(-a,a), g∈V_a, J_a g≠0, g(x)=v(x) for x∈S}`.

Then `R(a,S,v)` is nonempty and bounded below, and

`inf R(a,S,v) = mu(a)`.

More strongly, every such sampling fibre is dense in `V_a` in its actual form norm. These are unconditional statements about the literal source, with structural aperture and interior-set parameters only.

## Dependency-closed paper proof

1. **Zero-capacity isolators [CORPUS].** For any finite distinct interior points and any one selected point, there exists an exact-pole compact smooth source taking value one at that point, zero at all other points, and having arbitrarily small form norm. `CCMConstrainedPointCapacity` supplies localized isolators; `CCMFinitePointGramObstruction` already proves the finite Kronecker version.
2. **Arbitrary finite interpolation [PROVED HERE].** Induct on the finite sample set. Assume a constrained source `f` matches old samples with norm below `epsilon/2`. Add `c h`, where `c=v(x)-f(x)` and `h` is the exact constrained Kronecker isolator at the new point with norm below `epsilon/(2(||c||+1))`. Old samples remain exact, the new sample is exact, and `||f+c h||<epsilon`. The empty case is the zero source. The two pole constraints survive addition and scalar multiplication exactly.
3. **Full source energy [PROVED HERE].** `Q_a` is continuous in form norm and `Q_a(0)=0`. Choose the interpolation norm radius small enough to ensure both `||g||<epsilon` and `|Q_a(g)|<epsilon`. No positivity of `Q_a` is used.
4. **Dense sampling fibre [PROVED HERE].** Given `u∈V_a`, choose a constrained compact smooth approximant `f` within `epsilon/2` in form norm, using the corpus smooth-core theorem. Interpolate the residual values `v-f` with a constrained source of norm below `epsilon/2` and add it. The result lies in the prescribed sample fibre and within `epsilon` of `u`.
5. **Ground rigidity [PROVED HERE].** Choose a smooth constrained near-minimizer with nonzero physical mass and Rayleigh value below `mu(a)+epsilon/2`. Physical mass and `Q_a` are continuous; hence its Rayleigh quotient is continuous in a neighbourhood where physical mass remains nonzero. Step 4 gives a prescribed-sample source in that neighbourhood, with Rayleigh value below `mu(a)+epsilon`. Every such value is at least `mu(a)` by the actual completed Rayleigh floor. The sampled set is nonempty and bounded below; its infimum therefore equals `mu(a)`.

No off-line zero, RH assumption, numerical experiment, new axiom, or independent source bound is consumed.

## Exact prime-curvature consequence

At the corpus aperture `a=log(21/10)`, the actual prime jump stencil at `x=log 2` sees exactly the multiplicative positions `{1/2,2/3,1,4/3,3/2,2}`. The existing polynomial observable `w` has exact iterated prime energy

`c = (125/3)(log 2)² − (13805/216)(log 2)(log 3) + (1696/81)(log 3)² < 0`.

The sign is the existing kernel-checked analytic theorem, not a new numerical finding. Write `p(x)=e^(x/2)+e^(-x/2)>0`. Step 2 prescribes physical complex source values `g(x)=p(x) k w(x)` at all six points, while Step 3 makes both its actual form norm and complete Weil energy arbitrarily small. The real normalized physical observable `Re(g(x))/p(x)` consequently has prime curvature exactly `k² c` at `log 2`: all literal rates and aperture indicators are unchanged. Choosing `k` sufficiently large gives curvature below any specified negative threshold in any positive form-norm ball, with arbitrarily small full quadratic.

Scope is precise: `g` is a literal complex smooth exact-pole source; the prime Bochner reader acts on its real normalized observable. No sign of the complete Weil form is inferred, and no real-valuedness of the constructed complex source is asserted.

## No-go closure

- **Retired mechanism:** finite physical point-value repair of RW's constrained ground energy; bounded form-norm compensation for the negative pointwise prime-curvature stencil.
- **Strongest positive survivor:** exact unchanged Rayleigh infimum for every finite sample prescription, and density of each sampling fibre in the completed constrained source sector.
- **New insight:** finite physical point data and the completed source energy topology are independent. Imposing exact point conditions cannot improve the ground floor, even when the original constrained state is recovered arbitrarily closely. A viable source law must control nonlocal or stronger source information and retain full arithmetic compensation.
- **Limits:** does not exclude integrated jump-curvature identities, Fourier observations, infinitely many constraints, or a different stronger topology. RH remains open.

## Novelty audit

Corpus searches run before formalization:
- `restricted Weil ground energy pole vanishing frontier`
- `theta radical pole correction negative index no dimension loss`
- `full test pole constrained finite aperture Hodge transfer`
- `prime pole negative curvature constrained smooth compact form domain`
- `finite prescribed point constrained interpolation zero capacity`
- `sampled polar Rayleigh infimum finite sampling constraints dense`

The relevant predecessor files are explicitly read. They prove individual finite isolators, Gram-domination failure and an unconstrained smooth prime-curvature witness. The new claims connect them to exact finite-sample ground-energy rigidity and unbounded prime curvature on the exact compact source core. The interpolation/density argument uses standard functional analysis; no claim of new generic capacity theory is made.

Search reports include `partial=false`, but semantic coverage is unavailable and most compiler snapshots are source-only or stale. Candidate applicability is checked in Lean, not inferred from search metadata. Exhaustive source-text searches supplement ranked retrieval for the exact prime-Bochner mechanism.

Primary literature checked:
- [Connes–Consani, Weil positivity and Trace formula: the archimedean place](https://alainconnes.org/wp-content/uploads/Selecta.pdf), Appendix C: finite **Mellin-transform** vanishings preserve the **all-aperture RH criterion**. This is distinct from arbitrary **physical values** preserving the **fixed-aperture ground infimum**.
- [Zhu, Weil positivity in compact windows](https://arxiv.org/html/2608.24827v2): finite-window certified operator positivity. No matching point-curvature or physical-sampling theorem found in the inspected text.

Targeted web searches for the exact combinations of Weil ground energy, physical sampling, point capacity, prime carré du champ, and Bochner curvature found no matching theorem. This is limited novelty evidence: absence from every public source or inaccessible training data is not certified. A literature match would retire the novelty claim and trigger the next conjecture.

## Formal audit

Leaves: `CCMFiniteSamplingGroundRigidity.lean` and `CCMConstrainedPrimeCurvatureInstability.lean`, imported by `RHTower.lean`.

- Named foreground `lake --old --log-level=error build +GaloisForLFunctions.RHTower.CCMConstrainedPrimeCurvatureInstability`: exit 0.
- Final direct `lake env lean GaloisForLFunctions/RHTower/CCMFiniteSamplingGroundRigidity.lean`: exit 0.
- Final direct `lake env lean GaloisForLFunctions/RHTower/CCMConstrainedPrimeCurvatureInstability.lean`: exit 0.
- `/tmp/hgt-rw-axiom-audit.lean`: all eight public theorems depend only on `propext`, `Classical.choice`, `Quot.sound`; exit 0. No new axiom, `sorry`, `admit`, `opaque`, `unsafe`, or heartbeat override.
- Formal index refreshed. Global `scripts/formal_tools.py lint` reached the wiring gate and failed on twelve other unwired modules; neither new leaf was reported. Those shared-workspace modules are outside this change. Global lint is therefore **not green**. No full or umbrella build was run.

Capstones: `RHTower.ccmSampledPolarRayleigh_inf_eq` and `RHTower.PrimeCurvatureCounterexample.constrained_curvature_unbounded_below`.
