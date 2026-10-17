# Multi-chain Gram research ledger

This is a working mathematical state ledger, not a chronological log. Update or replace entries when evidence changes. Scope: Bi-Scale Uncertainty and coupling across odd dyadic cosets. No literature-wide novelty claims; mathematical frontier evidence comes from the local corpus.

## Established facts

### Full Gram energy replaces independent coset penalties

For real translation autocorrelation `h`, let `R=h(0)`, `v_t=U_t g`, `P=Σ_i w_i v_(t_i)`, `Q=||P||²`, `B=Σ_i w_i h(t_i)`, and `W>0`. Then

`W(R-h(y))+Σ_i w_i(R-h(t_i-y))`

`= RΣ_i w_i - B - Q/(2W) + ||W(v_y-g)-P||²/(2W)`.

- **Status:** Paper proof and Lean proof complete. Certified by `autocorr_gram_leverage_remainder`, `autocorr_gram_leverage_bound`, and `autocorr_odd_coset_gram_leverage` in `MultiChainToeplitzGramCoupling.lean`.
- **Consequence:** Rational leverage holds for arbitrary actual autocorrelations and arbitrary real weights; no sign or definiteness premise is needed. Exact zeros remove `B`.
- **Evidence:** [Proof card](../../drafts/pipeline/1-in-progress/bi-scale-multichain-gram-coupling-2026-10-17.md).
- **Use:** Retain `Q`, including its off-diagonal terms, instead of replacing it by independent chain envelopes.

### Exact cost of forgetting cross-coset correlations

For finite packets `P_m`,

`D=(Σ_m ||P_m||)²-||Σ_m P_m||²`

` =Σ_(m,m') (||P_m|| ||P_m'||-<P_m,P_m'>) ≥ 0`.

For orthogonal within-coset families, write `||P_m||²=R a_m²`. The best independently allocated rational penalty is `R(Σ_m a_m)²/(2W)`. Retaining the full Gram form improves the lower bound by **exactly** `D/(2W)`.

- **Status:** Paper and Lean proofs complete: `packetPartitionLoss_eq_sum`, `packetPartitionLoss_nonneg`, `packet_coupling_gain`, and `packetPartitionLoss_eq_zero_iff`.
- **Equality:** `D=0` exactly when every pair of nonzero packets is positively collinear (vacuously true if every packet is zero). Strictness requires misalignment, not a negative cross-correlation.
- **Use:** The correct target is a quantitative lower bound for `D`, rather than estimating each cross entry by an unrelated absolute value.

### Arithmetic cross blocks have more zeros than a coset partition records

`G_((m,k),(m',l))=h(log(m/m')+(k-l)log 2)` is Toeplitz in dyadic exponents. If `m'=q m` for an odd integer `q>1`, integer-ratio grid zeros annihilate every cross entry with `l≥k` (provided the actual grid cutoff contains the participating nodes). Reversing block orientation reverses the triangle.

- **Status:** Paper consequence of the established divisibility-pair orthogonality theorem; specialized block theorem not formalized.
- **Evidence:** `autocorr_log_divisibility_pair_orth` in `MultiplicativeChainBesselAndOriginLeverage.lean`.
- **Use:** Investigate strictly triangular cross-block contractions and synchronized weights. This can force a uniform improvement that qualitative nonalignment alone does not provide.

### Current corpus benchmark: shared-origin block relaxation

`SharedOriginMultiCosetLeverage.lean` now supplies `shared_origin_leverage_bound`,
`shared_origin_leverage_rational_bound`, and `shared_origin_support_attained`.
The denominator penalty uses `(Σ_m √Σ_k w_(m,k)²)²`; this is sharp when only separate
chain sphere constraints are retained. Its source explicitly imposes no compatibility
between different blocks on the attaining witness.

- **Status:** Source inspected; this ledger does not claim to have independently audited that module.
- **Consequence:** Our contribution is the additional full-Gram compatibility correction `D/(2W)`, not discovery of the shared-origin block formula.
- **Use:** Compare future uniform improvements against this sharp relaxation, not an unoptimized allocation.

## Failed assumptions and scope boundaries

- **Invalid shortcut:** Distinct odd cosets are mutually orthogonal. Only within-coset differences are automatically integer logarithms; cross correlations usually survive. Explicit counterexample under grid constraints alone: choose `log(5/3)<L<log 2` and a continuous nonnegative function supported on `[0,L]`, positive on `(0,L)` (e.g. `u(L-u)` inside that interval and zero outside). Every `h(log n)` for `n≥2` vanishes by disjoint support, but `h(log(5/3))>0` by positive overlap. Thus cosets based at `3` and `5` have a strictly positive cross correlation despite the full zero grid. This counterexample asserts no polar neutrality.
- **Invalid shortcut:** Every cross correlation must be negative to improve leverage. Improvement compares `Q` with the optimized partition envelope `R(Σ a_m)²`, not with the smaller diagonal-only value `RΣ a_m²`.
- **Unjustified inference:** Strict inequality for each compactly supported test gives a uniform positive gain over all tests. Qualitative strictness does not supply a uniform gap.
- **Attainment boundary:** The square-root Gram estimate is a sharp support bound over Hilbert vectors of the prescribed norm. A translation orbit need not contain its maximizing vector.
- **Zero-block boundary:** Optimal allocation `W_m=W a_m/Σ a_m` gives zero budget to zero packets. Omit zero packets or use an infimum; do not claim an attained optimum over strictly positive budgets for all blocks.
- **Novelty boundary:** The packet defect and positive-ray classification derive from classical Hilbert geometry. Existing corpus already has scalar complex triangle-equality machinery (`HTGeometry.CalibrationSpectrumMechanics.weighted_triangle_eq_iff`). Count the Bi-Scale coupling result once, not each algebraic helper.

## Open questions that determine next actions

1. Prove a quantitative arithmetic lower bound for `D`, uniform over admissible correlations, using triangular cross blocks from multiplicatively related odd cosets.
2. Construct the coefficient-space contraction of synchronized dyadic packets and prove arithmetic nilpotence, then apply the existing numerical-radius theorem without an extra analytic premise.
3. Establish the exact equality/nonattainment classification for actual compactly supported translates, beyond abstract Hilbert packet geometry.
4. Compare the coupled exact square-root bound against optimized partitioning in Lean, not only on paper.

## Contribution accounting

- Target: 100 significant contributions.
- Verified contribution 1: Gram-resolved origin leverage with exact partition-loss correction.
- Verified count: **1 / 100**. Candidate contribution 2 remains uncounted until its arithmetic bridge is formalized and audited.
- All supporting algebraic lemmas belong to contribution 1; they do not increase the count.

## Concrete next test: two levels in cosets `m` and `3m`

Nodes `{m,2m,3m,6m}` have exactly one potentially nonzero off-diagonal correlation under the integer-log zero grid: the pair `{2m,3m}`. Every other ratio, in its larger-to-smaller orientation, is an integer. For equal unit weights,

`Q=4R+2h(log(3/2)) ≤ 6R`.

The two independent dyadic chains have optimized penalty numerator `R(√2+√2)²=8R`. Thus `D≥2R`, giving a **uniform** improvement of at least `R/W` in the rational leverage bound. Include the origin anchor only when all selected nodes are grid zeros (e.g. odd `m≥3`, cutoff `N≥6m`); choosing `m=1` introduces the origin itself and must be treated separately.

- **Status:** Paper candidate, not counted or Lean-certified. This follows directly from the inspected divisibility theorem and Cauchy–Schwarz envelope; its formal bridge and exact comparison remain to be written.
- **Next action:** Audit this minimal arithmetic example before attempting general nilpotent-contraction bounds. It separates an actual uniform arithmetic gain from the generic measured-gain identity.

## Reusable nilpotent-contraction machinery already in the corpus

The numerical-radius theorem itself is **not** an open problem here.

- `HTGeometry.nilpotent_contraction_real_inner_gap` in `HTGeometry/NilpotentContractionInterference.lean` proves the elementary deficit `Re<x,Cx> ≤ (1-1/(2N²))||x||²` for a contraction with `C^N=0` (in denominator-free form).
- `RHTower.norm_inner_nilpotent_contraction_le_sine` in `RHTower/CCMNilpotentContractionSine.lean` proves the sharper `|<Tx,x>| ≤ cos(π/(N+1))||x||²`. Its statement and proof are general Hilbert-space mathematics despite its storage location. The proof uses finite defect-chain telescoping and the existing sharp chain inequality.
- **Evidence status:** Both actual sources inspected; imports/API and axiom audits for use in this topic remain pending.
- **Next action:** Construct the cross-coset coefficient-space contraction and derive its nilpotence from arithmetic zeros. Do not spend a contribution reproving the existing numerical-radius theorem. Do not assume contractivity or nilpotence as new input interfaces.

## Candidate contribution 2: synchronized cosets have a uniform sine gap

**Exact proposed theorem.** Let `m≥3` and `q≥3` be odd integers, `L≥1`, and `N≥qm 2^(L-1)`. Assume the actual real autocorrelation is zero on the integer-log grid through `N`. In the two cosets based at `m` and `qm`, use the same real coefficient vector `(c_0,...,c_(L-1))`. Put `S=Σ_k c_k²`, `R=h(0)`, and `ρ_L=cos(π/(L+1))`. Then

`Q=||P_m+P_(qm)||² ≤ 2R(1+ρ_L) S`,

`D≥2R(1-ρ_L)S`.

Thus the rational leverage bound improves uniformly over the sharp independent-block relaxation by at least `R(1-ρ_L)S/W`. Its lower bound becomes

`E ≥ R(2Σ_k c_k - (1+ρ_L)S/W)`.

**Paper proof.** If `R=0`, every translate is zero. Otherwise divide both orthogonal chains by `√R`, producing two isometries `A,B: ℂ^L→H` by finite synthesis. The coefficient-space map `T=A*B` is a contraction because both synthesis maps are isometries. Its `(i,j)` entry is `h(log q+(j-i)log 2)/R`, which vanishes for `j≥i`: the ratio `q2^(j-i)` is an integer in the pinned grid. Hence `T` is strictly lower triangular and `T^L=0`. The existing sharp numerical-radius theorem gives `Re<c,Tc>≤ρ_L||c||²`. Expand `||√R Ac+√R Bc||²` to obtain the claimed `Q` bound. Substitute into the proved Gram-resolved leverage formula and the definition of `D`.

- **Status:** Dependency-closed paper argument using the inspected nilpotent numerical-radius theorem; actual coefficient-space construction, arithmetic triangularity, and the application are not yet formalized. Not counted.
- **Important boundary:** The shared coefficient vector is essential to this proof. Arbitrary unrelated vectors give a bilinear pairing, not a numerical-radius expression; nilpotence does not improve the operator norm below one.
- **Sharpness boundary:** No claim that the constant is optimal among actual translation autocorrelations. Sharpness for abstract nilpotent contractions alone does not prove realizability by a logarithmic translation orbit.
- **Next action:** Formalize the arithmetic synthesis construction without accepting contractivity, orthogonality, or nilpotence as external interfaces. The four-node `L=2` instance is the minimal validation case.


## Verification evidence for contribution 1

- Module: `formal/GaloisForLFunctions/BiScaleUncertainty/MultiChainToeplitzGramCoupling.lean`.
- Source SHA-256: `5fae9738e06f22f6da8e9f54a3b407c7b0c96dbacc48e4debcf4fae8692fecba`.
- `lake build --old +GaloisForLFunctions.BiScaleUncertainty.MultiChainToeplitzGramCoupling`: PASS.
- Final `lake env lean GaloisForLFunctions/BiScaleUncertainty/MultiChainToeplitzGramCoupling.lean`: PASS, no output or warnings.
- `#print axioms` for **all 14 theorems**, via a scratch module checked with `lake env lean`: each uses only `[propext, Classical.choice, Quot.sound]`; no added axiom, `sorryAx`, or `Lean.ofReduceBool`.
- Umbrella import and generated API entries present; `scripts/formal_tools.py index` completed.
- Final `scripts/formal_tools.py lint --check-generated`: PASS, with existing unrelated large-file warnings.
- Formal scope: unconditional in displayed data; arbitrary real weights; compactly supported continuous actual tests; arbitrary real Hilbert packets. No claim that square-root refinements or the synchronized-coset sine gap are already formalized here.


## Robust form of the synchronized-chain sine gap (active proof)

For arbitrary test `f`, define the within-chain matrix `Γ_ij=h((j-i)log 2)` and cross matrix `C_ij=h((j-i)log 2-log q)`. All matrix norms below are **Euclidean operator norms**, not coefficient supremum norms. Let

`δ=||Γ-RI||`, `ε=||C-strictUpper(C)||`, `ρ=cos(π/(L+1))`.

The stronger, premise-free target is

`||P_m+P_(qm)||² ≤ 2(1+ρ)(R+δ+ε) Σ_k c_k²`.

Complete paper argument: the strictly upper part `T` of `C` is nilpotent with exponent `L`; normalize it by its actual norm and apply the existing sharp numerical-radius theorem. Since `||T||≤||C||+ε`, one obtains `|<Cx,x>|≤[ρ||C||+(1+ρ)ε]||x||²`. Actual synthesis gives `C=B†A` and `A†A=B†B=Γ`; hence `||C||≤||A||||B||≤R+δ`. Expand the norm of the packet sum and bound both diagonal energies by `(R+δ)||c||²`. No unproved contractivity/nilpotence input occurs. When actual grid zeros hold, `δ=ε=0`, giving candidate contribution 2 exactly.

This formula keeps grid errors explicit; it is not a replacement of the uniform sine-gap target by a weaker theorem. Its error-free specialization is the full arbitrary-length target. Formal construction and audit remain in progress; verified contribution count stays 1.
