# Hilbert geometry of graded observation defects

**Status:** completion, physical flow extension, normalized Hilbert basis, basis-independent analytic heat trace, Mellin zero orders, and half-flow metric rigidity are formalized. Ten Hilbert leaves, 102 declarations, final-built and axiom-audited; four gap/quotient prerequisites add 36 declarations. Standard Hilbert and spectral principles, not a novelty claim.

For weight k+1, the actual homogeneous defect Q_k is H_(k+1)/(A∩H_(k+1)). Its missing coefficient λ_k and positive attained physical recovery gap δ_k give the quotient norm δ_k|λ_k|. The real inner product is forced by this norm: ⟨x,y⟩=δ_k²λ_k(x)λ_k(y). Each Q_k is a complete real line. The projection preserves the original observation addition and scalar action.

Define H as the Hilbert sum of these actual lines: sequences x_k∈Q_k for which Σδ_k²|λ_k(x_k)|² converges. Its norm squared is that sum; its inner product is Σδ_k²λ_k(x_k)λ_k(y_k). Finite truncations converge, and single-grade embeddings are isometries for the physical quotient norm. Thus this topology retains the exact physical recovery cost in every grade while enforcing orthogonality between distinct flow weights.

The algebraic normalization quotient has the already proved finite-support basis [u^k c]. Send a class to its graded coefficient classes. Lean proves the map injective, recovers every original missing coefficient, and places every single-grade vector in its image. The grade-sum convergence proves density. Pulling back the Hilbert norm gives the existing algebraic quotient a norm and inner product. The embedding is an isometry, and CubicDefectCompletion packages H as an actual AbstractCompletion of this normed quotient. In particular ‖[u^k c]‖=δ_k. This norm is not the uniform quotient seminorm, which vanishes on c by unrestricted polynomial recovery.

Physical contraction q∈[0,1] acts on Q_k by q^(k+1). It therefore extends to a contraction on H, preserving each grade. In fact its operator norm is exactly q: each multiplier is between zero and q, giving the upper bound in the Hilbert norm, while the nonzero weight-one line attains it. The operators multiply as T_qT_r=T_(qr), and their real diagonal makes them symmetric. Equality with the original algebraic operator is checked on the already proved basis [u^k c]; density makes the continuous extension unique. For q=exp(−τ), τ>0, its diagonal on the physically normalized grade vectors is exp(−(k+1)τ). The diagonal sum agrees with the previously proved cusp heat. The extension and analytic trace identification are formalized. The trace is the corpus's ContinuousLinearMap.opTrace, with its hypotheses proved by Hilbert–Schmidt factorization.

## Analytic trace — formalized

Normalize each actual graded line by its physical norm, writing b_k=[u^k c]/δ_k. These vectors are orthonormal; every single-grade vector lies in their span, so grade-sum convergence supplies a Hilbert basis. Its coefficient for an original algebraic class is δ_k times the original missing coefficient.

For 0≤q<1, Σ‖T_q b_k‖²=Σq^(2(k+1)) is finite. Hence T_q is Hilbert–Schmidt. Factor T_q=T_(√q)T_(√q); both factors are Hilbert–Schmidt. The corpus's `ContinuousLinearMap.opTrace_comp_eq_tsum_basis` in `HTGeometry/HilbertSchmidtTrace.lean` proves convergence and basis independence of the ordinary operator trace for such products, over real as well as complex Hilbert spaces. Consequently tr(T_q)=Σq^(k+1)=q/(1−q). At q=exp(−τ), this is 1/(exp τ−1), precisely the already formalized cusp heat. CubicHilbertTrace proves this factorization, trace formula, and convergence to the same trace in every Hilbert basis. CubicHilbertMellin defines the response using that analytic operator trace and the actual continuous reference integral; its Mellin transform is −Γ(s)ζ(s), with exactly the strip zeta zeros and multiplicities.

## Rigidity from the single half-retraction

The single half-retraction forces the required orthogonality. On the original algebraic defect, write e_k=[u^k c] and consider real bilinear forms B satisfying only B(e_k,e_k)=δ_k² and B(T_(1/2)x,y)=B(x,T_(1/2)y). For i≠j the second identity gives (2^(-(i+1))−2^(-(j+1))) B(e_i,e_j)=0. The factor is nonzero, so the cross term vanishes. The fixed diagonal and bilinearity then determine B on every finite linear combination. The already constructed graded inner product is one such form; therefore it is the unique one. Positivity and definiteness follow, without being assumed in this characterization. CubicHilbertRigidity proves that this set of bilinear forms is exactly the singleton containing the constructed graded inner form, and proves its positive definiteness. The distinct-eigenvalue argument is classical.

## Formal coverage and remaining targets

| Leaf | Declarations | Result |
|---|---:|---|
| CubicGradedLine | 11 | Actual quotient operations; physical infimum norm; complete one-dimensional inner product space |
| CubicDefectHilbert | 10 | Complete Hilbert sum; weighted norm and inner product; isometric grade inclusions; convergent grade sum |
| CubicDefectEmbedding | 14 | Actual B/A embedding; exact coefficient recovery; injectivity; density |
| CubicDefectCompletion | 8 | Graded norm and inner product on B/A; isometry; AbstractCompletion; original basis norms δ_k |
| CubicHilbertFlow | 14 | Bounded positive symmetric physical flow; exact norm q; endpoints and semigroup |
| CubicHilbertExtension | 7 | Agreement with original algebraic flow; unique continuous extension |
| CubicHilbertBasis | 13 | Actual physically normalized Hilbert basis; exact coefficient representation |
| CubicHilbertTrace | 12 | Hilbert–Schmidt factorization; analytic trace q/(1−q) in every Hilbert basis |
| CubicHilbertMellin | 7 | Operator-trace response; absolute Mellin convergence; strip zeta zeros and orders |
| CubicHilbertRigidity | 6 | Costs and one symmetric half-flow uniquely force the algebraic inner form |

Next: [multiplication by u](chronological-recovery-shift.md) retains the successive recovery-cost ratios that cancel from the normalized heat trace. The physical bound δ_(k+1)≤δ_k/4 and the resulting bounded weighted shift are paper-only. Its self-commutator, log-convexity, and moment-measure questions provide concrete further targets. No explicit higher-weight δ_k formula or optimizer uniqueness is used in the completed trace construction.

All 102 Hilbert declarations and the 36 prerequisites use only Lean/mathlib's standard logical axioms. Final aggregate audit: `/tmp/chronological-hilbert-trace-audit-summary.txt`. No numerical certificate was used.
