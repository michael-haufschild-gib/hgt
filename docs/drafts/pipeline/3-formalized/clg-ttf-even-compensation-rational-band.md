# CLG/TTF complete-source even compensation coefficient

- **Stage:** 3-formalized
- **Closed result:** The literal even four-by-four determinant is negative at the self-dual center. Its canonical integral-preserving compensation coefficient satisfies `10^12<C_*<3·10^12`. Every coefficient in the closed rational band repairs that center and gives strict positivity on common regions near zero and in the tail, including the exact weighted source.
- **Open:** Strict positivity on the intervening compact interval, the actual mixed rank-seven sign and the complete hierarchy. RH remains unproved.
- **Full chain:** Literal theta source → every signed center-mixed Hankel section nonnegative → global Fourier-current sign → Xi Bezoutian orientation → RH.

## Complete modular seam

Let `M=thetaCuspSelfDualThetaMass>0` and `X=thetaCuspSelfDualModularScale²`. The existing literal modular source bounds give `191/10<X<96/5`. Normalize the four modular state coordinates at zero to `(H,Z,R,P)=(1,0,√X,0)`. Their proved differential equations are

`H′=−H(P+RZ)/6`, `Z′=−R(1−Z²)`,

`R′=−2R(P+RZ)/3`, `P′=3−P²/3+R²(3+Z²)/12`.

Apply the exact Leibniz convolution to these equations through order fourteen. The normalized source derivatives are

`f_k(X)=(H^(2k+2)(0)−H^(2k)(0)/4)/2`, for `0≤k≤6`.

They are explicit rational polynomials of degrees one through seven. In particular `f₀=(X−6)/16`. Each recurrence step is a separately proved polynomial identity. The existing exact modular incidence, together with parity of the full theta source, gives

`Φ^(2k)(0)=M f_k(X)` and `Φ^(2k+1)(0)=0`.

These are derivatives of the complete infinite source. No retained-atom approximation is used. The seven coefficient tables and the recurrence proof are in `HTGeometry/PolynomialODEEvenSeamJets`.

## Exact signed determinant normalization

For the literal reflection jets `j_n(x)=D_t^n[Φ(x+t)Φ(x−t)]|_(t=0)`, put `m_k=(-1)^k j_(2k)` and

`q_k(X)=(-1)^k Σ_(i=0)^k binom(2k,2i) f_i(X) f_(k−i)(X)`.

The finite Leibniz identity gives `m_k(0)=M²q_k(X)` through index six. In particular `Φ(0)²=M²q₀(X)` and `q₀=(X−6)²/256>0`.

Define `D₃(X)=det[q_(i+j)(X)]_(i,j<3)` and `D₄(X)=det[q_(i+j)(X)]_(i,j<4)`. Their exact expanded degrees are twelve and twenty. The generic four-by-four determinant identity and the seven signed moments prove

`det A(0)=M⁶D₃(X)`, `det E₀(0)=M⁸D₄(X)`.

Here `A=[m_(i+j)]_(i,j<3)` is the already proved strictly positive literal head, `b=(m₃,m₄,m₅)`, and `S=m₆−bᵀA⁻¹b`. Its invertibility and the exact Schur determinant formula give

`S(0)/Φ(0)²=D₄(X)/(D₃(X)q₀(X))`, with `D₃(X)q₀(X)>0`.

All mass factors cancel. The determinant tables are in `HTGeometry/PolynomialODEEvenSeamDeterminant`; complete-source transport is in `RHTower/ThetaCusp/ThetaCuspEvenSeamDeterminant`.

## Rational coefficient reserves

Write `z=10X−191`. For `X≥191/10`, symbolic expansion gives

`−D₄−10^12 D₃q₀ = α₀+Σ_(n=1)^20 α_n z^n`,

with every `α_n>0`. For `191/10≤X≤96/5`, one has `0≤z≤1`, and a second exact expansion gives

`(3·10^12−1)D₃q₀+D₄ = β₀+Σ_(n=1)^20 β_n(1−z^n)`,

with every `β_n>0`. Thus both reserves are strictly positive. The full rational coefficient lists and symbolic equality proofs are in `HTGeometry/PolynomialODEEvenSeamReserves`; positivity uses only rational arithmetic and nonnegative powers. No sampled sign or computational oracle is a premise.

The first reserve proves `D₄<0`, hence `det E₀(0)<0` and `S(0)<0`. Consequently the canonical source coefficient satisfies

`C_*=(|S(0)|+Φ(0)²)/Φ(0)²=1−D₄/(D₃q₀)`.

Dividing the two strict reserves by the positive denominator proves `10^12<C_*<3·10^12` unconditionally.

## Positive survivor and common endpoint regions

Let `G=3Φ²+2xΦΦ′` and `E_C=[m_(i+j)]_(i,j<4)+CG e₃e₃ᵀ`. The proved strict-head Schur equivalence is

`E_C(x) strictly positive ↔ S(x)+C G(x)>0`, for `x≥0`.

At zero, `G(0)=3Φ(0)²` and `S(0)=(1−C_*)Φ(0)²`. Hence every `C≥10^12` gives a strictly positive seam scalar, using the strict upper bound on `C_*`. This is the positive replacement for the negative native even determinant.

Set `L=10^12`, `U=3·10^12`. At any fixed center, positivity for `E_L` and `E_U` implies positivity for every `L≤C≤U`: use the lower endpoint when `G≥0` and the upper endpoint when `G≤0`. Continuity supplies a common positive seam interval for the two endpoints. The already proved complete-source tail supplies a cofinal ray for each endpoint; their intersection is again a cofinal ray. Therefore there are `0<δ≤R` such that

`E_C(x)` is strictly positive whenever `L≤C≤U`, `x≥0`, and `x<δ` or `R≤x`.

For `w_a(r)=r sinh(ar)` and `F_a(r)=r²sinh(ar)Φ(r/2)²`, the previously proved exact correction has zero half-line integral and satisfies `F_a′(r)≥w_a(r)G(r/2)`. Thus the weighted corrected matrix is strictly positive on common endpoint regions for every coefficient in the rational band and every positive aperture. Its integrated entries remain exactly the actual signed mixed derivatives through order twelve, for `0≤a<1/2`.

The unique positive zero `τ` of `G` selects explicit lower comparisons for the canonical scalar: `S+LG≤S+C_*G` on `0≤x≤τ`, and `S+UG≤S+C_*G` on `x≥τ`. Neither inequality supplies positivity in the remaining interior. The [explicit complete-source outer margin](clg-ttf-even-four-explicit-tail.md) gives `R=6/5` uniformly on this coefficient band. The inner threshold `δ>0` remains existential. [Complete full-source error bounds through twelve](clg-ttf-even-four-complete-error.md), including the correction and a finite lower quadratic comparison, are proved. A positive margin and quantitative small-center control remain to be established, or the exact successor integral must be controlled directly.

## Lean verification

Eight new modules are checked: `HTGeometry/HankelFourDeterminant`, `PolynomialODEEvenSeamJets`, `PolynomialODEEvenSeamDeterminant`, `PolynomialODEEvenSeamReserves`; `RHTower/ThetaCusp/ThetaCuspEvenSeamJets`, `ThetaCuspEvenSeamDeterminant`, `ThetaCuspEvenCompensationCoefficient`, `ThetaCuspEvenCompensationRationalFamily`.

Each was checked in scratch with one foreground `lake env lean` process at a time, emitting only its needed olean. Checked bytes were copied into the corpus and wired into the relevant umbrellas without building the umbrellas. Seven new capstones were audited once; their only axioms are `propext`, `Classical.choice` and `Quot.sound`. The formal lint gate passed.
