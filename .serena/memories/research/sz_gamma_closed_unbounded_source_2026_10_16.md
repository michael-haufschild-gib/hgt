# SZ: exact Gamma boundary domain and closed deattenuation

Four directly audited Lean modules in formal/GaloisForLFunctions/RHTower:
- SuzukiCausalDepthGammaBoundaryCancellation
- SuzukiCausalDepthGammaClosedSource
- SuzukiCausalDepthGammaUnboundedSource
- SuzukiCausalDepthGammaFiniteRowBoundary

Actual two-leg columns are p times the original causal-depth Gamma feature-operator columns, with all prime depths retained. For surviving degrees d(0)=1, d(k+1)=k+3 and c_k=JacobiNormalization(d(k)), adjacent rows c_(k+1)b_k-c_k b_(k+1) are Hilbert rows: the literal factor p(1-tanh(log(p^(e+1))/2)) is bounded. The homogeneous output recurrence is z*c_k; c_k is not square-summable. Hence closure of the finite basis/column graph is single-valued, closed, densely defined, and preserves every finite packet and Gram pairing.

Actual first Gamma row at depth zero has divergent squared prime sum. No bounded extension exists. Fixed premise-free capstone: RHTower.suzukiGammaCanonicalTwoLegSource_closed_dense_unbounded (h=a=1).

Sharp finite-row theorem: RHTower.suzukiGammaFiniteRow_hilbert_iff_boundary_zero. A finite complex row sum alpha_k*b_k has a Hilbert source representative iff sum alpha_k*c_k=0. Explicit correction W_k=c_0*b_k-c_k*b_0 proves both directions. RHTower.suzukiGammaTwoLeg_finite_packet_pairing retains exact p*q*GammaSchurKernel, including mixed terms.

All four modules passed direct lake --old env lean -j 1 audits; main capstone, classification and polarized pairing print only propext, Classical.choice, Quot.sound. No full build, numerical experiment, external novelty search or heartbeat increase. Umbrella imports added.

Scope: old square-summable amplitude-admission predicate remains false. New result is an unconditional non-diagonal closed realization of unchanged columns, with exact finite-row boundary classification. Does NOT prove completed signed Robin/Ward comparison, moving-source Wronskian law, or RH. Minimal graph need not be claimed equal to every maximal extension.

Paper proof and failed-conjecture log: docs/drafts/pipeline/3-formalized/sz-gamma-closed-unbounded-source.md.
