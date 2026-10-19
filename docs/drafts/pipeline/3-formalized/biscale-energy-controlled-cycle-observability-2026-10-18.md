# Energy-controlled closed-cycle observability and signed-grid tails

- **ID:** biscale-energy-controlled-cycle-observability-2026-10-18
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parent:** [100-contribution programme](../1-in-progress/biscale-100-contribution-programme-2026-10-18.md)
- **Status:** obstruction and positive survivors proved on paper and in Lean; four direct source checks and standard-axiom audits passed. Counted as one package. Repository lint has one unrelated BVI umbrella error; no full lint pass claimed.

## Mathematical target

Use actual normalized autocorrelations `H_f` and the singular archimedean energy. Couple finite closed-cycle observations on a bounded interval to the actual signed logarithmic trace in the tail. Obtain an unconditional error bound whose right side consists of observable defects and explicit functions of actual source energy, with no derivative-energy replacement and no zero-grid restriction.

For an energy ceiling K, derive an explicit positive collar radius rho from the existing logarithmic increment estimate. At nodes x in a finite mesh choose n with |x|/n <= rho. Two literal cycles measure H_f(x/n)^2 and H_f(x) H_f(x/n)^n. Their errors control signed H_f(x)-H_g(x), including negative outer correlations. The energy modulus controls interpolation between mesh nodes. Beyond a chosen radius, the logarithmic ceiling-node sampling estimate controls the difference by the actual signed trace discrepancy plus an explicit O(sqrt(K/radius)) term. The grid-blind case is a specialization, not the theorem's domain.

This extends the positive mechanism in [the earlier finite-cycle card](../2-fully-proven/biscale-finite-cycle-recovery-1810.md); that supporting formalization is not separately counted.

## Exact-order obstruction: paper construction

Bounded normalized energy and the full logarithmic zero grid may still fail to impose a uniform **exact** closed-cycle detection order. The old identical-copy example cannot establish this: narrowing its base source increases energy. Instead try two different source shapes:

1. Fix a nonzero smooth base source u of diameter less than log 2.
2. Put a nonzero smooth corrector v in a fixed small interval. Impose finitely many linear cross-correlation equations so the separated cross packets vanish at every logarithmic node meeting their compact support.
3. Use more disjoint smooth bumps than linear constraints to obtain a nonzero v. Prove its cross-correlation with u is not identically zero; this is an obligation, not an assumption.
4. Compare u + a T_T v and u - a T_T v at large separation T. Their central packets agree and their distant cross packets have opposite signs. Closed cycles shorter than T divided by the packet radius have zero net packet charge, hence agree exactly.
5. Choose a nonzero amplitude a after v is constructed to keep both normalized energies under one fixed ceiling. All logarithmic-grid constraints remain exact because the cross equations are homogeneous.

The following construction closes the mathematical nonzero-response obligation without assuming a general convolution injectivity theorem. The actual-source construction is formalized below.

Fix a nonzero real smooth source u supported in [-r,r], with r=log(2)/8. Write h=autocorr(u), R=h(0)>0 and E=J(u). Put D=4r=log(2)/2. For a prescribed order m choose T>(m+2)D+1. All constants R,E,D are independent of m.

Let A be the finite set of integers n>=2 with log(n) in [T-D,T+D], and let q=|A|. Choose q+1 distinct shifts s_j in [0,r]. Define

`v_c(t) = sum_j c_j u(t-s_j)`,

`C_c(z) = integral u(t) v_c(t+z) dt = sum_j c_j h(z-s_j)`.

The map c -> (C_c(log(n)-T))_(n in A) is a real linear map from dimension q+1 to dimension q, so it has a nonzero kernel vector. For this vector C_c is not identically zero: h is a nonzero compact continuous L² function, and its distinct translates are linearly independent. The corpus already proves the stronger arbitrary-L² theorem `HTGeometry.linearIndependent_L2_translates`; real coefficients embed into the complex theorem. Thus v_c is also nonzero. This uses the actual cross-correlation, not a formal coefficient surrogate. An equivalent implementation may constrain every n < N for a fixed natural N > exp(T+D), using N+1 translates. This includes all relevant grid samples and yields the identical existence theorem; no dimension-optimality claim is made.

The source v_c is supported in [-r,2r]. Hence h_u, h_v and both cross-correlation orientations are supported inside [-D,D]. The finite set A contains every positive logarithmic node that can meet the positive cross packet, while the negative cross packet cannot meet any positive logarithmic node. The central packet is supported below log(2). These support statements show that both

`F_plus(t)=u(t)+a v_c(t-T)` and `F_minus(t)=u(t)-a v_c(t-T)`

satisfy **all** logarithmic-grid zeros whenever a is real, independently of its size. Choose `a=1/(1+J(v_c))>0`. The Lévy quadratic-form parallelogram and nonnegativity give

`J(F_plus), J(F_minus) <= 2(E+a²J(v_c)) <= 2(E+1)`.

Disjoint source supports give equal masses `R+a²||v_c||² >= R`; both normalized energies are at most the fixed `K=2(E+1)/R`. Every source is smooth and compact; no energy bound is assumed of the kernel vector.

The two autocorrelations have the same central packet and opposite remote packets centered at +/-T. In a nonzero closed product with at most m factors, label each lag by its unique packet center kT, k in {-1,0,1}. Each packet error has magnitude at most D. Since the lags sum to zero, `|sum k|T <= mD < T`, hence `sum k=0`. The number of remote factors is even. Therefore all such closed products agree, including products with zero factors and the empty product. Equal source masses make the same statement true after normalization. Some remote correlation differs because C_c is not identically zero and a>0.

**Paper conclusion:** there exists one finite K such that, for every m, two actual smooth full-grid sources below K have identical complete closed-product data through order m but distinct signed normalized correlations. This is stronger than eventual blindness at each fixed grid node. It is also outside the existing identical-copy-train obstruction, since the corrector shape varies with the finite interpolation constraints. The positive survivor is finite-accuracy recovery with an explicit order/noise bound; the obstruction and both positive survivors have now passed the formal audits recorded below.

## Search and classical comparison

- All 91 lexical `cycle` hits in the field were inspected across offsets 0,20,40,60,80; eight modules. The full-hierarchy theorem and sharp identical-copy threshold are existing work, not new claims.
- `/tmp/bsu-100-signed-observation-deep.json` returns the exact signed-grid compactness equivalence, `DistantCopySharpness`, and integer-train peak classifications. It is partial (decomposition unfinished), semantic coverage unmeasured. `exists_smooth_pointwise_grid_blind_noncompact` was inspected in full: its approximating sources have eventual pointwise blindness, not simultaneous full-grid blindness.
- `/tmp/bsu-100-cross-kernel-search.json` is partial (semantic retrieval/reranking unfinished); all candidate/source inventories and proposed ingredient sets were inspected. It supplies convolution support/continuity, not the required injectivity. Direct source discovery located the stronger L² translate-independence theorem; a focused corpus query is recorded separately.
- `/tmp/bsu-100-finite-kernel-search.json` returns `LinearMap.ker_ne_bot_of_finrank_lt` and rank–nullity. All candidate/source statements were inspected. This supplies precisely the finite constraint argument; its actual toolchain probe and use in the final proof passed. `/tmp/bsu-100-real-translates-search.json` supplies compact-support L² embeddings but no simpler real-translate independence theorem. Both searches finished their requested stages; semantic coverage remains unmeasured and index refresh remains in progress.
- [Jaming–Kolountzakis, 2003](https://nyjm.albany.edu/j/2003/9-12p.pdf), especially the Fourier product formula in section 2.1, is a close classical mechanism. Closed products of H=Fourier(P) correspond to transformed higher correlations of P. Thus closed-product reconstruction by itself is not a new principle. Any novelty claim must rest on the simultaneous full logarithmic-grid constraint, fixed singular-energy ceiling, actual-source construction and quantitative surviving recovery.
- [Ransford's Titchmarsh note](https://arxiv.org/abs/2011.05420) supplies a classical alternative for nonzero compact convolution. The finite-translate construction above instead reuses the local corpus's stronger L² independence result. Neither classical ingredient is counted as a contribution.
- A further primary-source check of [Jaming–Kolountzakis, section 2.3](https://nyjm.albany.edu/j/2003/9-12.pdf) confirms smooth finite-order ambiguity (Theorem 2.4), all-order recovery (Lemma 2.6), and the gap/order mechanism (Lemma 2.1). These mechanisms are classical. Candidate novelty must be the simultaneous integer-log zeros at one fixed singular-energy ceiling for actual compact sources, with the native quantitative survivor; not a renamed phase-retrieval construction.

Paper transfer check (2π Fourier convention): for smooth compact f, put P=|Fourier(f)|²/R_f(0). Plancherel gives integral P=1; autocorrelation gives Fourier(P)=H_f. Fubini gives Fourier(N_k(P))(ξ₁,…,ξₖ₋₁)=∏H_f(ξ_j)·H_f(−Σξ_j); rapid decay justifies the interchanges. Thus the classical model applies to these spectral densities. It does not supply the additional fixed-energy logarithmic-zero constraint.

## Explicit finite recovery protocol

Write c = exp(-1/2), K₊ = max(K,0), and ε > 0. Every normalized source in `LevyEnergySource K` has modulus radius δ(K,η) = exp(-(1 + 8K₊/(cη²))) and positive collar ρ = δ(K,1/2), on which H > 1/2. These statements are derived from the existing singular-energy inequality, not added as premises.

Set R = 1 + 32K₊/(cε²), δ = δ(K,ε/2), n = ceil(R/ρ). Use mesh xᵢ = -R + δi for 0 ≤ i ≤ floor(2R/δ). At each mesh point observe the pair [yᵢ,-yᵢ] and spoke [-xᵢ,yᵢ,...,yᵢ], where yᵢ = xᵢ/(n+1) occurs n+1 times. Both are literal closed lag lists; maximum order is n+2. Let Δ be the maximum absolute discrepancy over these 2(floor(2R/δ)+1) observations. Put A = 2^(n+1)(n+2), and let τ be the supremum of the actual signed logarithmic trace discrepancy over all integer nodes.

The collar factorization gives |H_f(xᵢ)-H_g(xᵢ)| ≤ AΔ. Every point in [-R,R] is within δ of a mesh point, so the source modulus yields error < AΔ+ε there. Beyond R, the existing logarithmic sampling inequality yields error < τ+ε. Thus the global error is < max(AΔ,τ)+ε. No unsigned trace, truncated-grid replacement, assumed positive collar, or assumed tightness is used. Equal signed-grid trace and equal finite observations imply global error < ε. This is the positive survivor accompanying the exact-order obstruction; it is not counted separately as a new contribution.

Implementation: `EnergyControlledClosedCycleRecovery.lean` proves this protocol with the existing actual-source energy API. `global_recovery`, `fixed_integer_grid_recovery`, and `value_eq_normalized` passed direct source/axiom checks. The formalized energy-derived κ=1/2 case closes the corresponding part of the earlier paper card, without claiming its arbitrary-κ or other open cases.

### Positive survivor: decay of exact order ambiguity

This quantitative statement has a paper proof and a passing direct Lean check with a standard-axiom audit. It belongs to the same package. If all normalized closed products through order n+2 agree and the full signed logarithmic traces agree, then for every x,

    exp(-1/2) * n * ρ(K) * |H_f(x)-H_g(x)|² ≤ 32 max(K,0).

Paper derivation: for |x| ≤ nρ, subdivision into n+1 pieces lies strictly inside the positive collar, so the matching two-edge and spoke products give exact equality at x. For |x| > nρ, use the shared signed sample at log(ceil(exp(|x|))). Each sample residual satisfies c|x|a² ≤ 8K. The elementary inequality (a-b)² ≤ 2a²+2b² yields c|x||H_f-H_g|² ≤ 32K, hence the displayed result. The case n=0 is immediate from nonnegativity. Thus fixed-energy ambiguity diameter is O(n^(-1/2)) even though the proposed obstruction keeps it nonzero at every finite order. No optimal-rate assertion is made. This is part of the same obstruction/survivor package, not an additional contribution count.

`/tmp/bsu-100-order-decay-search.json` was inspected across all candidate/source statements; it returns existing sharp copy-order and Gram-detection theorems, but no matching energy/order rate. Requested stages completed; semantic coverage is unmeasured. `/tmp/bsu-100-generic-charge-search.json` likewise returns the existing source-specific packet-charge proofs, whose bodies were inspected before preparing the two-shape extension. No general absence claim is made.

## Proof and verification gates

All four direct named-source checks exited 0 with no warnings. Each used `lake --old env lean -j 1 -o .lake/build/lib/lean/GaloisForLFunctions/BiScaleUncertainty/<module>.olean GaloisForLFunctions/BiScaleUncertainty/<module>.lean` in `formal/`; no umbrella or full build ran.

| Module | Passing log |
| --- | --- |
| `EnergyControlledClosedCycleRecovery` | `/tmp/bsu-100-energy-cycle-leaf-r2.log` |
| `FiniteGridNullCorrector` | `/tmp/bsu-100-corrector-leaf-r3.log` |
| `FullGridEnergyCycleAmbiguity` | `/tmp/bsu-100-full-grid-leaf-r1.log` |
| `ClosedCycleAmbiguityDecay` | `/tmp/bsu-100-decay-leaf-r1.log` |

Imported final audit: `lake --old env lean -j 1 /tmp/bsu_100_final_axioms.lean` exited 0. `GridCycleAmbiguity.exists_full_grid_bounded_energy_cycle_aliases`, `EnergyCycle.order_ambiguity_square_bound`, `global_recovery`, and `fixed_integer_grid_recovery` depend only on `propext`, `Classical.choice`, and `Quot.sound`; log `/tmp/bsu-100-final-axioms.log`. The corrector and exact two-source correlation/energy identities also passed scratch standard-axiom audits. All four leaves are imported by the field umbrella.

`scripts/formal_tools.py index` completed, including generated documentation and the source index. `scripts/formal_tools.py lint --check-generated` exited 1 with a single error outside this package: unreachable `BezoutValuationIncidence.RamanujanGapChainConditionalTailCoercivity`; log `/tmp/bsu-100-final-lint.log`. Existing large-file warnings remain. No new-package lint error, active placeholder, or added axiom was reported. Scoped `git diff --check` passed. This is recorded lint evidence, not a repository-wide pass.

Final corpus audit: the global deep query returned mostly unrelated energy results and was rejected as novelty evidence. The focused deep query `research '"cycle" "grid" "energy"' --any --module BiScaleUncertainty --per-module 0 --mode deep --budget-seconds 300 --json` completed its stages; all 20 candidate and 20 source-argument inventories were checked. Newly indexed leaves were distinguished from antecedents. Existing uniform-tail, signed compactness, collar-energy and Sobolev-grid results do not state the two-shape obstruction. Semantic coverage remains unmeasured, with an older-generation coverage warning and a background refresh, so this is not an exhaustive semantic absence claim.

Additional lexical audit: all 31 results for `"ambiguity" "homometric" "k-deck" "crossNull" --any` in the field were paginated at offsets 0 and 20; all nine `"cross" "null"` results were inspected. The former includes the existing separated-copy/polar and arithmetic sign-ambiguity packages; the latter consists of the new corrector package. These complement the complete 91-hit cycle inventory, not replace source-level comparison. Evidence: `/tmp/bsu-100-native-final-audit.json`, `/tmp/bsu-100-ambiguity-lexical*.json`, `/tmp/bsu-100-cross-null-lexical.json`.

- [x] Inspect returned corpus inventories and relevant statements, recording coverage limits.
- [x] Compare primary literature and the actual Fourier transfer; avoid a universal priority claim.
- [x] Prove explicit signed sampling, finite mesh and cycle-noise recovery on actual sources.
- [x] Prove the two-shape full-grid obstruction at one fixed energy ceiling.
- [x] Formalize the finite-accuracy and order-decay positive survivors.
- [x] Run direct source checks, imported axiom audit, umbrella wiring, index and lint; record unrelated lint failure.

The contribution is the precise coexistence of simultaneous full logarithmic-grid zeros, a uniform singular-energy ceiling and unbounded exact detection order, together with its quantitative recovery boundary. Classical phase ambiguity, the finite-dimensional corrector, individual helper lemmas and completion of prior paper work are not separately counted. No optimal order-decay rate or universal literature priority is asserted.

The failed uniform-exact-order route and its surviving theorems are recorded in [the closure card](../5-failed/biscale-uniform-exact-cycle-order-2026-10-18.md).

Read-only baseline: field README SHA-256 `95c0fc8e6bc87af3b980d39f00a17f294b2bd16ae248f9361eff557e303ad275` remains unchanged. Four new Lean leaves and their umbrella imports were added; no existing Lean proof was modified.
