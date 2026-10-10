# Exponential price of exact coefficient isolation

- **ID:** finite-weil-coordinate-isolation-cost
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** local Lean geometric cluster envelope, singleton quadratic cost certificates, coefficient pairing/scaling, and uniform exact realization.
- **Statement:** At every sufficiently large cutoff, some coefficient has a quadratic-cost unit response but requires exponential cost when all other cutoff coefficients must vanish. Exact isolation remains attainable.

## Exact unconditional target

There exist c>0, A>0 and integer K>=2 such that for every N>=2K there exists i in Finset.range N with:

1. Some actual Gram test w has coefficient i exactly 1 and native unit cost <= A N^2, with the other coefficients unrestricted.
2. Some actual Gram test realizes the entire target Pi.single i 1.
3. Every actual Gram test realizing that target has native unit cost >= c 2^(N/K).

All tests are the corpus's actual FiniteWeilGramTest, with its existing cost. The lower bound is independent of node count, node positions, and outer scale. This is a worst-coordinate assertion, not a claim about every coordinate. Constants are uniform over cutoffs; the selected index may vary with N.

## Local audit / attack

Only Lean sources and proof algebra. No external searches, papers, numerical experiments, or external novelty claims. Queries `target exponential cost` and `coefficient isolation cost` in WeilLogShift returned no hits; source search for isolation/expensive/spike found only FirstProbeInterpolation's scalar first-probe signed-spike construction. The existing exponential theorem controls the SUM of costs of a certificate family. The target here controls EVERY single test realizing a particular coordinate spike, without a dimension loss from summing a basis family.

Read local `exists_pairedLogKernel_geometric_cluster_envelope`, the cutoff-budget argument, `allOrder_gram_sensitivity`, the injective extension/potential identity, `exists_singletonWeil_quadratic_cost_certificate`, coefficient scaling, and normalization-cost scaling. The uniform realization theorem now compiles, preventing an empty-fiber interpretation of the obstruction.

Verdict: **BRIDGE**. The sharp new interpretation is the price of zeroing other coordinates: producing the chosen coefficient alone has polynomial cost, while exact isolation has exponential cost. Do not claim the elementary finite duality argument itself is novel.

## Dependency-closed paper proof [PROVED HERE]

1. The geometric cluster envelope gives fixed B>0 and L>=1. For r,k with 4L(r+1)<=k+2, there exists c:Fin(r+2)->Real of supremum norm 1 such that, for every real shift z,

       |sum_j c_j pairedLogKernel(z,k+2+j)|
         <= B exp(2|z|) / ((k+2)^2 2^r).

   The finite nonempty index set has an index j with |c_j|=1, since the supremum norm is its largest absolute coordinate.

2. Suppose all k+j belong to a finite support s. Embed the cluster by e(j)=k+j and extend c by zero to d:s->Real. Injectivity and finite sum reindexing give the exact displayed kernel sum as finiteWeilPotential s d. For any actual test w, the double-sum triangle inequality in the native form/cost definitions gives

       |finiteWeilGramForm s w d| ((k+2)^2 2^r)
         <= finiteWeilGramTailCost B w.

   This is precisely the mechanism already proved in the source-private allOrder_gram_sensitivity; no new analytic estimate is assumed.

3. Choose i=e(j) at a largest coefficient. If the full coefficient vector is Pi.single i 1, the existing coefficient pairing identity gives finiteWeilGramForm s w d=d_i=c_j. Its absolute value is 1. Consequently EVERY exact isolating test costs at least (k+2)^2 2^r / B in unit normalization, using cost_B=B cost_1. Its fibre is nonempty by the new unconditional fixed-node realization theorem.

4. For cutoffs use the corpus's exact arithmetic budget: choose integer K>4L+1, with K>=2. Given N>=2K, put q=N/K, r=q-2 and k=N-q. Then q>=2, r+2=q, k+q=N and Kq<=N. The existing argument proves 4L(r+1)<=k+2 and embeds the whole cluster into range N. Since k+2>=2,

       (k+2)^2 2^r >= 4*2^r = 2^q.

   Thus c=1/B is a uniform exponential lower-bound prefactor for the selected coordinate. This avoids the factor N that would be lost by using a whole coordinate-certificate family.

5. Cheap single-coordinate response: the singleton theorem supplies fixed B_s>0, C_s>0 and, at every index k, a two-test normalized certificate of total B_s-cost <= C_s(k+2)^2. Apply its certificate property to the constant coefficient -1 on the singleton. One member w then has coefficient k strictly greater than 1. Its nonnegative cost is bounded by the total. The coordinate's value is independent of which finite support contains k, by the actual coefficient formula.

6. Let v>1 be that coordinate value and scale w's outer factor by 1/v. Coefficient scaling makes the coordinate exactly 1; the native cost scales by 1/v and cannot increase. The latter identity follows immediately by multiplying the existing outer NNReal factor in the cost definition. Converting B_s-cost to unit cost gives <=(C_s/B_s)(k+2)^2. For k<N and N>=1, k+2<=N+1<=2N. Therefore A=4C_s/B_s>0 gives the asserted bound A N^2. Apply this to the expensive coordinate selected in step 4. Exact isolation is therefore strictly stronger than merely producing its unit response.

No open mathematical core remains. All helper bounds and existence premises have actual corpus producers. Formalization is pending.

## Working plan

- [x] Local source audit, exact conjecture, attack and paper proof.
- [x] Formalize the cluster-to-coordinate obstruction, preserving the all-node/all-test quantifier.
- [x] Carry the cutoff budget into a unit-coordinate exponential lower bound.
- [x] Produce cheap exact unit responses from singleton certificates by positive outer scaling.
- [x] Combine with the unconditional exact-realization witness.
- [x] Audit all public declarations.
- [x] Native leaf builds, umbrella wiring, index, lint run (six unrelated umbrella omissions; no owned diagnostics); no full builds or heartbeat changes.
- 2026-10-10: Card recorded before Lean edits. No code for this card has been written. Uniform-realization-cost final audit is complete: 26 public declarations and 92 API terms passed, with all seven native artifacts fresh. Its card is now `../3-formalized/finite-weil-uniform-realization-cost.md`. This coordinate-isolation card is the next active research step.
- 2026-10-10: WeilLogShiftGramCoordinateObstruction native build passed: public sensitivity transfer, cluster spike obstruction, and unconditional cutoff exponential obstruction. No division by support size was introduced. The coordinate's fibre lower bound covers arbitrary test nodes, count, amplitudes and outer scale. Added unit-response and final separation leaves; their builds/audits are pending. Existing ancestor sources were not changed.
- 2026-10-10: WeilLogShiftGramUnitResponse native build clean. Its root gives one universal quadratic unit-cost bound for every coordinate of every finite support, with exact response equal to one. The native outer-scaling identity is public. Final separation leaf now building; scratch final audit prepared for all six public declarations and 110 API terms. No heartbeat changes or full builds.
- 2026-10-10: WeilLogShiftGramIsolationSeparation native build passed cleanly on first attempt. The root includes the cheap exact unit response, existence of an exact spike, and the exponential lower bound for every realizing test, all in native unit normalization. Final axiom/API audit and index refresh running. All three new leaves are wired once in the umbrella; no existing ancestor Lean sources were modified.
- 2026-10-10: Final audit passed for all six public declarations, with only `propext`, `Classical.choice`, `Quot.sound`; all 110 API terms passed. All three native builds clean, oleans fresh, imports exactly once, API index contains all six declarations, exact root search returns one hit at line 15, and whitespace checks pass. All owned processes terminal.

## Exact Lean delivery

- `WeilLogShiftGramCoordinateObstruction.lean`: public native sensitivity transfer; cluster coordinate obstruction; unconditional exponential coordinate-spike cost obstruction over every actual test.
- `WeilLogShiftGramUnitResponse.lean`: exact outer-scale cost identity and universal quadratic-cost exact unit responses at any coordinate of any finite support.
- `WeilLogShiftGramIsolationSeparation.lean:15`: `exists_finiteWeilGram_coordinate_isolation_cost_separation`, combining the two cost bounds with a genuine exact-isolation witness.

Native logs: `/tmp/hgt-coordinate-obstruction-build.log`, `/tmp/hgt-gram-unit-response-build.log`, `/tmp/hgt-gram-isolation-separation-build.log`. Audit: `/tmp/hgt-isolation-final-audit.lean` and `.log`. Index/lint/search: `/tmp/hgt-isolation-index.log`, `/tmp/hgt-isolation-lint.log`, `/tmp/hgt-isolation-receiver-search.json`.

Global lint reports six unrelated missing umbrella imports: `RHTower.PhotonicLosslessProductPortThinSlab`, `RHTower.XiHorizontalSlicePolyaFrequencyCriterion`, `HTGeometry.PaperGammaHankelPolarization`, `HTGeometry.PaperMoebiusPrimeEnergy`, `HTGeometry.PaperPrimeTransportEnergyDomain`, `HTGeometry.QKrawtchoukCompanionTriangular`. Those shared-worktree files were not changed.

## Research assessment and positive survivor

The obstruction is nonvacuous: exact isolation exists, and the same coordinate admits a polynomial-cost exact unit response. Thus the added cost comes from constraining other coefficients. This sharpens the certificate-family lower bound without paying a support-size factor. This is an internal quantitative bridge; no external priority claim.

The proof exposes a stronger positive survivor: retain its dual vector to bound unavoidable off-coordinate leakage at any given native cost. The complete paper proof is recorded in [cost-leakage tradeoff](../3-formalized/finite-weil-cost-leakage-tradeoff.md). That is the next active card; no Lean code for it has been written.
