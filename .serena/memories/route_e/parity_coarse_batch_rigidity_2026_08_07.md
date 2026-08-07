# Route E parity-coarse batch rigidity (2026-08-07)

## Exact new theorem

For any finite positive weighted batch split into classes I+ and I-, with class masses W±, unsigned numerators K±, and leaf values f, the checkerboard-signed residual splits exactly:

R = V+ + V- + C,

where V± are within-class weighted residuals and

C = (W+ W-)/(W+ + W-) * (K+/W+ + K-/W-)^2.

Therefore R ≤ η forces V+ ≤ η, V- ≤ η, C ≤ η. Zero residual iff f is constant inside each class and the two class constants are negatives.

For Gibbs powerset leaves, I± are even/odd subset cardinality, w_T = Z_S(m_T x), f_T = ψ_S(m_T x). This yields exact source identity

J_{S∪P}(x)^2/Z_{S∪P}(x) + V_even + V_odd + C
= Σ_{T⊆P} w_T ψ_S(m_T x)^2.

## Four-current determinant sharpening

Put W=W++W-, A=K++K-, B=W+-W-, J=K+-K-. Then

D_anti = W A - B J = 2(W- K+ + W+ K-),
D_np   = W J - B A = 2(W- K+ - W+ K-),

and

C = D_anti^2 / (W (W^2-B^2)).

D_np detects unequal unsigned class response / departure from parity-block product behavior. D_anti detects failure of antiscale opposition. Only D_anti enters coarse dissipation. Thus a theorem proving merely that moving-boundary weights are nonproduct is insufficient: nonproduct response can lie entirely in antiscale escape. Required source theorem must be antiscale-transverse (physical-power D_anti) or force physical-power within-parity variation.

## Current Route E frontier

Sharper open premise: GIBBS-PARITY-CLASS-RIGIDITY-BREAKING. At a cofinal moving batch, prove a physical-power lower bound for at least one of V_even, V_odd, or C relative to leaf energy, retaining literal Gibbs weights and parity balance. Terminal shell can collapse one parity mass; proof must prevent collapse or extract same-parity variance first.

Fresh Halász–GHS/Lorentzian prime-supported mean-square infrastructure may help frequency-averaged same-parity variation, but current Halász strength is x^(1-o(1)), not square-root scale. It is not Route E closure without a new moving-boundary physical-power conversion.

OPEN-SOURCE-001 and RH remain open.

## Artifacts

- Lean: formal/GaloisForLFunctions/RHTower/GibbsBatchParityCoarseGraining.lean
- Stage 3 card: docs/drafts/pipeline/3-formalized/new_scientific_knowledge/route-e-parity-coarse-grained-batch-rigidity.md
- Active card and frontier map updated.
- Module wired into formal/GaloisForLFunctions/RHTower.lean.
- Direct lean pass; targeted build 9712/9712; #print axioms only propext, Classical.choice, Quot.sound.
- Repository-wide `python3 scripts/formal_tools.py lint` passed.
- No full build run.