# Explicit component averaging and physical best approximation

Status: dependency-closed paper proof, written before Lean implementation;
formalized and audited as connected contribution16/100.

## Canonical finite components

Fix d∈ℕ,D⊆ℕ and A(k) iff some e∈insert d D has e+2 dividing k+1.
Use the certified start function s(0)=0 and
s(k+1)=s(k) when A(k), otherwise s(k+1)=k+1.
For each cell k, let H(k) mean that some edge k+n is missing. If H(k), let
r(k) be the least such n and e(k)=k+r(k); otherwise put e(k)=k as a harmless
total-function convention. Mean subtraction will be zero in this latter case.

Induction gives s(k+n)=s(k) when all edges k,…,k+n−1 are active. Hence, if
H(k), the interval [s(k),e(k)+1) is the finite component containing k.
For every missing edge j, the fibre {k:e(k)=j} is exactly
I_j=[s(j),j+1). Indeed, a first missing edge at j has an active path from k
to j, giving s(j)=s(k)≤k≤j. Conversely, if s(j)≤k≤j, a missing edge before j
would contradict internal activity of I_j. Thus e(k)=j. An active endpoint j
can receive only cells with H(k) false, where the correction will vanish.
Each I_j has positive integer length L_j=j+1−s(j), so every finite component
is counted exactly once by its final missing edge.

## Explicit coefficient producer

For actual w∈ℓ² define

    μ_w(k) = (Σ_(i∈[s(k),e(k)+1))w_i)/(e(k)+1−s(k))  if H(k),
             0                                           otherwise,
    c_w(k) = w_k−μ_w(k).

These formulas define actual square-summable data without an admission premise.
To prove this, use the certified closed space
C_A={v∈ℓ²:Σ_(i<k+1)v_i=0 whenever ¬A(k)} and its Hilbert projection P.
The residual g=w−Pw lies in C_A⊥, so it is constant on each finite component
and zero on any infinite active tail. On a finite component I, Σ_I Pw=0;
therefore its residual constant is (Σ_I w)/|I|. Consequently g_k=μ_w(k)
for every k, and c_w=Pw. This proves square summability, admission to C_A,
linearity, contraction and exact equality with the explicit formula.

Define the endpoint charge

    Γ_j(w) = (Σ_(i∈I_j)w_i)²/L_j  if ¬A(j),
              0                   otherwise.

The series Σ_jΓ_j(w) converges, with exact sum ‖w−Pw‖². Proof: the squares
of g are summable because g is an actual ℓ² vector. Group that convergent
series by e. Missing-edge fibres are I_j, where g has constant value μ;
therefore their sums are L_j μ²=(Σ_Ij w)²/L_j. Active-endpoint fibres have
zero residual values. Regrouping the actual absolutely convergent series
proves both summability and the formula; neither is hypothesized.

## Physical producer and exact error

Let S be certified unit-cell synthesis and define B=S*, the actual bounded
cell-analysis map. Its coordinates are

    b_k=(Bq)_k=∫_(k,k+1]q=F(k+1)−F(k),   F(t)=∫₀ᵗq.

Adjoint identities give BS=id and ⟨Sv,q−SBq⟩=0 for every actual v∈ℓ².
Thus Qq=SBq is the cellular projection, with
‖q‖²=‖Bq‖²+‖q−Qq‖². Prefix telescoping gives
Σ_(i<n)b_i=F(n), and hence Σ_(i∈I_j)b_i=F(j+1)−F(s(j)).

The requested producer is

    P_A q = S(c_(Bq)).

It belongs to the certified physical completion for every q∈L²(ℝ), d,D.
Its cell-k coefficient is explicitly b_k−μ_b(k), and its integer/logarithmic
traces are the finite cumulative sums of those coefficients. No ℓ² condition
on those cumulative traces, finite-family condition or run bound is assumed.
The exact approximation error is

    ‖q−P_A q‖² = ‖q−Qq‖²
                + Σ_(j:¬A(j)) (F(j+1)−F(s(j)))²/(j+1−s(j)).

Indeed q−P_Aq=(q−Qq)+S(b−Pb), with orthogonal summands. Isometry of S and
the coefficient charge identity give the formula. The corresponding energy
identity adds ‖P_Aq‖² to the right-hand side to recover ‖q‖², giving an
unconditional energy contraction.

For every completed datum v∈C_A, orthogonality gives the sharper identity

    ‖q−Sv‖² = ‖q−P_Aq‖² + ‖c_b−v‖².

To check the orthogonality directly, pair S(v) with q−P_Aq. The cellular
residual q−Qq pairs to zero; the remaining pairing is ⟨v,b−Pb⟩=0.
This proves unique best approximation. The operator is bounded linear,
idempotent, and has range exactly S(C_A)=closure(range E_A).

## First cell, negative half-line and full-family specialization

Edge0 is always missing. Its component is [0,1), with mean b_0. Thus the
producer's first cell coefficient is exactly zero, and F_(P_Aq)(1)=0.

Construct q⁻=1_(-∞,0]q as an actual L² class using measurable truncation.
Every positive unit-cell integral of q⁻ is zero, so Bq⁻=0 and P_Aq⁻=0.
Pointwise truncation gives ⟨q⁻,q−q⁻⟩=0; the adjoint formula gives
⟨q⁻,Sb⟩=0. Hence the noncellular residual has the exact split

    ‖q−Qq‖²=‖q⁻‖²+‖q−q⁻−Qq‖²,
    ‖q⁻‖²=∫_(-∞,0]q².

Substitution into the main error formula accounts for the entire negative
half-line, positive noncellular variation and arithmetic component means.
Nothing is silently projected away without charging its error.

For D=ℕ, all edges k≥1 are active. The only finite component is [0,1);
all later cells lie on an infinite active tail. Thus the unconditional
specialization is

    P_Aq = S(b−δ_0 b_0)=Qq−b_0 unitCell0,
    ‖q−P_Aq‖²=‖q−Qq‖²+b_0².

This gives a completely instantiated projection in the nonclosed old-range
regime. General component means give the corresponding explicit formula for
all other divisor families, including bounded-run cases.

## Provenance and scope

Classical Hilbert projection and best approximation are parent tools, not an
external novelty claim: [MIT18.102, Proposition183 and orthogonal decomposition](https://ocw.mit.edu/courses/18-102-introduction-to-functional-analysis-spring-2021/8fb8d5c170f1613151aca71de21027bc_MIT18_102s21_full_lec.pdf),
[official mathlib projection theory](https://leanprover-community.github.io/mathlib4_docs/Mathlib/Analysis/InnerProductSpace/Projection/Basic.html).
The field contribution is the explicit arithmetic component formula, the
proved convergent charge series and the full physical best-approximation
producer, including unbounded-run families and negative physical coordinates.
No RH, full SourceGraph, full affine-unitary or unweighted logarithmic H1
identification is asserted. The field README is read-only.

Prior query: `orthogonal cell component mean subtraction projection physical
velocity residual`, BiScaleUncertainty filter, --any,60-second budget. All20
candidate statements and20 source arguments inspected. Existing cell synthesis,
projection residual, completed-space and component-constancy results supply
building blocks; no explicit arbitrary-component averaging formula appeared.
Search partial=true, interrupted text/source retrieval; inventory snapshot
1446427 vs current1446428, enrichment counts pending, refresh incomplete due
to background indexer. Compiler coverage is mixed, mostly pending/source-only;
all candidate applicability must be checked in this toolchain. No absence or
external novelty conclusion follows from the search.

## Formal certificate

Five serial direct `lake --old env lean -o <normal-output> <leaf>` checks pass
without diagnostics: DivisorCellEndpoints, DivisorComponentAverages,
DivisorComponentCharge, PhysicalCellAveraging, DivisorPhysicalProjection.
The last module exports the explicit coefficient formula, exact range,
unique best approximation, convergent physical charge, full error split,
contraction and full-family specialization. All87 public declarations pass
the `/tmp/divisor_averaging_axioms.lean` audit with only propext,
Classical.choice and Quot.sound;17 principal signatures and50 API probes
checked. Five umbrella imports and87 exact catalog entries verified.

Global lint reports eight unrelated unreachable modules and concurrent
LEAN_API/LEAN_OVERVIEW drift; exact errors are retained in
`/tmp/divisor-averaging-lint-errors.json`. No own or proof-debt error.
The indexes are refreshed separately. No full/umbrella build, numerical
experiment, heartbeat increase or README edit. Trap10 is addressed within
continuum shear by instantiated producer coefficients and unconditional exact
error, without an assumed Chebyshev estimate or pre-floor counterterm.
