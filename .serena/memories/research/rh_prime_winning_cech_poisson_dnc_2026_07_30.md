# RH prime-winning Čech / Poisson DNC mechanism (2026-07-30)

## Exact Lean progress

Module: `formal/GaloisForLFunctions/RHTower/PrimeDilationTropicalBoundaryTomography.lean`.

Unconditional Lean theorems now include:
- `primeDifference_winningFaceIndicator_of_nonempty_not_mem`: Δ_p b_{F,m} = -b_{F∪{p},m}` for nonempty F, p∉F.
- `iteratedPrimeDifference_tropicalShellIndicator`: for distinct prime list ps, iterated Δ on shell a_m equals `(-1)^(|ps|-1)(b_{F,m-1}-b_{F,m})`.
- `winningFaceIndicator_mul`: b_F b_G = b_{F∪G}.
- `tropicalShellIndicator_eq_alternating_winningFace_sum`: finite winner-simplex Čech augmentation recovers shell indicator.
Direct Lean and focused module build pass. Axiom audit uses only standard `propext`, `Classical.choice`, `Quot.sound`. No stale Lean processes.

Formalized card: `docs/drafts/pipeline/3-formalized/prime-dilation-higher-winning-face-generation.md`.

## Paper theorem 1: prime-winning Čech divisor resolution

Card: `docs/drafts/pipeline/2-fully-proven/prime-winning-cech-divisor-resolution.md`.

For nonempty finite F and m≥1, winning-face Dirichlet series
`B_{F,m}(s)=Σ_{M(n)=m,F⊆W(n)} n^-s` has exact formula

`B_{F,m}(s)=ζ(s) U_{F,m}(s)`, where

`U_{F,m}(s)=1/ζ((m+1)s) ∏_{p∈F} [p^(-ms)(1-p^-s)/(1-p^(-(m+1)s))]`.

U is holomorphic and zero-free on Re s>1/2. Thus every nonempty positive face is a unit presentation of the zeta divisor for every m≥1. Principal conormal transitions are exact local factors `R_{p,m}`. Face inclusion-exclusion resolves each radial shell; the infinite Euler augmentation recovers `H_m=1/ζ((m+1)s)-1/ζ(ms)`.

Interpretation: actual prime covariance failures generate complete Čech nerve. Finite fibres are canonically contractible by coning to least winner, so ordinary lim^1 cannot create RH class. Missing invariant is controlled fate of this exact contraction under completion/Gamma reflection/Xi base change.

## Paper theorem 2: Poisson strictness created at infinite exponent depth

Card: `docs/drafts/pipeline/2-fully-proven/bounded-exponent-poisson-strictness-emergence.md`.

For bounded exponent depth M, positive dilation operator on (M+1)-free integers has multiplier

`A_M(s)=ζ(s)/ζ((M+1)s)`.

It has a forced pole at `s_M=-2/(M+1)`. Explicit fixed Meyer test
`f(x)=x^2(x^2-3/(2π))e^{-πx²}` lies in H_cap and has
`Mf(s)=(s-1)/4 π^{-(s+4)/2} Γ((s+2)/2)`, nonzero at every s_M. Hence every finite truncation fails to land in Meyer H_-, while full infinite-depth sum is Meyer's strict Poisson operator. Horizontal winning-face Čech augmentation + vertical shell-depth telescope is a source-generated double resolution; finite rectangle leaves terminal pole, complete totalization creates regularity.

Boundary flux:
`lim (M+1) Res_{s=-2/(M+1)} A_M(s)=2π²/ζ(3)` and residue/distance → `π²/ζ(3)`.

## Deformation-to-normal-cone jump

Let ε_M=1/(M+1), s=ε_M u. Exact blow-up:

`A_M(ε_M u)=ζ(ε_Mu)/ζ(u) → ζ(0)/ζ(u)=-1/(2ζ(u))`.

Thus every zeta zero and multiplicity becomes a pole of exceptional boundary fibre. Bulk fixed-s limit is ζ(s); exceptional normal-coordinate limit is reciprocal ζ. The third completion candidate is the DNC gluing these two charts, not initially an unknown Hilbert space.

Gamma completion:
`X_0(ε,u)=Xi(εu)/Xi(u)` and `X_1(ε,u)=Xi(1-εu)/Xi(u)` are exactly equal by functional equation for every ε,u. Common exceptional fibre is `1/(2Xi(u))`, retaining all nontrivial zeros/multiplicity jets before choosing any zero.

Hypertranscendence reinterpretation: scaled Gamma/reciprocal-zeta HT proves exceptional transition cannot be flattened into finite differential-algebraic state chart; HT is boundary-gluing complexity, not direct zero locator.

## Determinant emergence from depth succession

Define `X_M(s)=Xi(s)/Xi((M+1)s)`. At s=ε_M u:

`X_{M+1}/X_M = Xi(u)/Xi((1+ε_M)u)`,
so
`ε_M^-1 log(X_{M+1}/X_M) → -u Xi'(u)/Xi(u)`.

Balancing endpoint 0 and 1 yields reflection-invariant connection
`G_bal(u)=-(u-1/2) Xi'(u)/Xi(u)`.
At zero ρ order d, `Res_ρ G_bal=-d(ρ-1/2)`. Horizontal displacement is radial residue of source-generated depth successor law.

## Corrected open core after hostile residue audit

The scalar `G_bal(u)=-(u-1/2) Xi'(u)/Xi(u)` is the Euler contraction of the DNC logarithmic connection, not a possible Herglotz coefficient. In centered coordinate it is `-z Phi'/Phi`; paired real Xi zeros at `±a` give residues `-ma,+ma`, so the scalar is neither Herglotz nor anti-Herglotz even under RH.

`[SOURCE_DEPTH_LOG_CONNECTION_FORM_REALIZATION]`: construct a divisor-free matrix-valued Green/Weyl realization of the uncontracted DNC form `-d log Xi_C`, compatible with prime-winning Čech incidence, Meyer Poisson strictness, Gamma reflection, and strict Xi conormal base change. This survives the residue attack but remains only the already formalized Xi Herglotz criterion until the source producer is proved.

Exact failure card: `docs/drafts/pipeline/5-failed/source-depth-euler-contraction-herglotz-no-go.md`. Need common source class and matrix positivity before specialization.

Active synthesis card: `docs/drafts/pipeline/1-in-progress/riemann-autogenic-obstruction-operation-purity-law.md`.