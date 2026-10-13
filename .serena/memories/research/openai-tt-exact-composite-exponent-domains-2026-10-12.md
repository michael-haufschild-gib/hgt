# Exact literal composite exponent domains
Verified native application of proven OpenAI/math compact-ideal mechanisms to TT, using docs/reports/rh-current-frontier-map.md. No mathematical novelty claim.

New leaves in formal/GaloisForLFunctions/RHTower/: PaperWoldCompositeFamily.lean, PaperWoldCompositeGrowth.lean, PaperWoldCompositeDomain.lean. 28 new theorems +5 definitions. Existing private rectangle estimate in PaperWoldPrimeNormGrowth was promoted to paperWold_finite_rectangle_norm_lower with unchanged proof; only dependent leaf PaperWoldBoundedDomain needed rebuilding.

For every real exponent, the literal even-composite matrix admits a bounded l2 operator iff t<=1/2, compact iff t<1/2, Hilbert-Schmidt iff t<1/2, bounded noncompact iff t=1/2. Complete family paperWoldCompositeOperator has norm<=5 throughout closed-half domain; ideal cost zero belowhalf, infinite at endpoint. Every finite cutoff compact/zero cost at every exponent; endpoint cutoffs equal earlier paperWoldCriticalCompositeCutoff exactly.

For t>1/2 and N>=1, paperWoldCompositeFiniteCutoff t (range(3*N)) has norm >= N^(2*t-1)/48, tending to infinity. Proof retains rows Ico N (2N) and columns Ico (2N) (3N), original composite cell bounds >=1/(6N), >=1/(8N), row power >=N^(2t). No prime distribution input. Excludes every full compressed bounded realization. Original FULL arithmetic bounded domain remains t<half.

All5affected leaf final plain lake --old env lean checks passed with empty logs; all42 public declarations checked with only propext/Classical.choice/Quot.sound. Exact34newlypublic module/name pairs registered;3new leaves wired once;objects current. Global formal lint PASSED.25priorTTsourcehashes unchanged;edited parent separately audited. Audit tmp/hgt-openai-math/tt-composite-domain-audits.json; totals file824leaves/8810public/6629theorems, carried earlier821notallreaudited.

No goal completion or commits/pushes; broad39route/candidate scope active. Next selected question in tt-composite-parameter-next.json: actual A_t row damping D_t A_half, strong convergence from below, persistent norm gap>=1/24 and ideal-cost jump. Not yet searched or proved. No spectral-disk or sharp-norm assertion.

Lean APIs: global tendsto_rpow_atTop (not Real.tendsto_rpow_atTop); Nat.card_Ico (not Finset.card_Ico). HasLpMatrix.ext in GaloisForLFunctions.HTGeometry; lpBasisVec must unfold in basis comparisons. Source exact casts hnhi n<2N to (n:R)+1<=2N handled by exact_mod_cast. Final axiom log can wrap over multiple lines; parse bracket blocks with DOTALL.

Owned build/final helpers and API probe removed; /tmp/paper-tt-composite-domain-axioms.lean and audit/log/search evidence retained. All owned sessions terminal. Shared unrelated dirty work preserved.