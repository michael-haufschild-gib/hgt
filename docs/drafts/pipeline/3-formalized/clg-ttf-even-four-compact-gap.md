# CLG/TTF even rank-four compensation outside a compact gap

- **Stage:** 3-formalized
- **Closed result:** One fixed coefficient defined from the literal theta source gives a strictly positive corrected even four-by-four block near the self-dual center and on a cofinal ray. The exact weighted correction preserves every integrated entry, including the twelfth mixed derivative.
- **Open:** The intervening compact source comparison, the actual mixed rank-seven sign and the all-order hierarchy. RH remains unproved.
- **Explicit outer endpoint:** The [complete-source reserve theorem](clg-ttf-even-four-explicit-tail.md) gives `x≥6/5` uniformly for `0≤C≤3·10^12`, and weighted positivity for every `a>0` on `r≥12/5`. Only the inner endpoint remains existential for the canonical coefficient.
- **Coefficient calibration:** The [complete modular seam theorem](clg-ttf-even-compensation-rational-band.md) proves the negative native seam determinant, `10^12<C_*<3·10^12`, and common endpoint regions for every coefficient in that rational band.
- **Full chain:** Literal theta source → every signed center-mixed Hankel section nonnegative → global Fourier-current sign → Xi Bezoutian orientation → RH.

## Exact twelfth source limit

Write `q=π exp(2x)`, `φ=thetaCuspSourceTerm x 1`, and
`j_n(x)=D_t^n[Φ(x+t)Φ(x−t)]|_(t=0)` for the complete theta source.

After extracting `exp(x/2−q)`, the first-atom derivative polynomials satisfy

`P₀(q)=4q²−6q`,

`P_(n+1)(q)=(1/2−2q)P_n(q)+2qP_n′(q)`.

Symbolic recurrence and the exact finite Leibniz identity give the first-atom reflected twelfth derivative as `exp(x/2−q)² B₁₂(q)`, where

`B₁₂(q)=−491520q³+1408303104q⁴−75547148288q⁵+603009318912q⁶−1280916848640q⁷+886529064960q⁸−239798845440q⁹+43599790080q¹⁰`.

Dividing by `φ²q⁶` gives a rational function of `1/q`, with limit `43599790080/16=2724986880`. The already proved complete-source error at every fixed derivative order tends to zero after this normalization. Therefore the actual infinite source satisfies

`j₁₂(x)/(φ²q⁶) → 2724986880`.

No finite truncation or sampled inequality enters this theorem. Together with the existing lower limits, the signed normalized even moments through index six converge to

`(1,8,192,7680,430080,30965760,2724986880)`.

## Strict complete-source tail

The limiting even four-by-four Hankel matrix has the exact quadratic form

`(v₀+8v₁+192v₂+7680v₃)² + 128(v₁+48v₂+2880v₃)² + 98304(v₂+120v₃)² + 188743680v₃²`.

The triangular forms vanish simultaneously only at the zero vector. Thus the limit is strictly positive. The corpus theorem on entrywise convergence of Hermitian matrices transfers this strictness to the complete source.

Set `m_k(x)=(-1)^k j_(2k)(x)` and `G(x)=3Φ(x)²+2xΦ(x)Φ′(x)`. Let

`E_C(x)=[m_(i+j)(x)]_(0≤i,j<4)+C G(x)e₃e₃ᵀ`.

For every fixed real `C`, the correction normalized by `φ²q⁶` tends to zero. The diagonal congruence with entries `φ q^i` identifies the normalized matrix with `E_C`. Hence, for each fixed `C`, there is `R>0` such that `E_C(x)` is strictly positive whenever `x≥R`. This is a complete-source theorem; its threshold is existential, not an explicit numerical bound or a bound uniform in `C` or matrix order.

## Literal seam correction

The actual even head `A(x)=[m_(i+j)(x)]_(0≤i,j<3)` is strictly positive for all `x≥0`. For positive centers this follows by principal restriction and sign congruence from the native five-point theorem. At zero, continuity gives a positive semidefinite limit and the proved strictly positive eighth-order seam determinant upgrades it to strict positivity.

Consequently its inverse is available without an added premise. With `b=(m₃,m₄,m₅)`, define

`S(x)=m₆(x)−b(x)ᵀA(x)⁻¹b(x)`.

The exact determinant factorization and Schur test prove

`E_C(x) strictly positive ↔ S(x)+C G(x)>0` for `x≥0`.

Choose the fixed literal coefficient

`C_*=(|S(0)|+Φ(0)²)/Φ(0)²>0`.

Since `G(0)=3Φ(0)²`, its corrected seam scalar is

`S(0)+3|S(0)|+3Φ(0)²>0`.

Continuity gives `δ>0` on which `E_(C_*)` is strictly positive. Combining this with the complete-source tail gives `0<δ≤R` and strict positivity for every `x≥0` with `x<δ` or `x≥R`. The coefficient is the same on both regions. No sign of the uncorrected even determinant at zero is assumed or asserted here.

## Exact weighted incidence

Let `w_a(r)=r sinh(ar)` and `F_a(r)=r² sinh(ar)Φ(r/2)²`. The existing source theorem proves absolute integrability and zero half-line integral of `F_a′`, and proves

`F_a′(r)≥w_a(r)G(r/2)` for `a,r≥0`.

The corrected matrix is

`W_(a,C)(r)=w_a(r)[m_(i+j)(r/2)]+C F_a′(r)e₃e₃ᵀ`.

All entries are integrable for `0≤a<1/2`. Their exact integrals are

`∫_(r>0) W_(a,C)(r)_ij dr = (-1)^(i+j) f_a⁽²⁽ⁱ⁺ʲ⁾⁾(0)`.

For `C≥0` and `a,r>0`, the difference `W_(a,C)(r)−w_a(r)E_C(r/2)` is a nonnegative diagonal matrix. Thus native corrected strictness implies strictness of the exact weighted matrix. For `C_*`, the weighted matrix is therefore strictly positive near zero and on a cofinal ray, with the same center bounds for every positive aperture.

The remaining sufficient comparison for this correction is `S(x)+C_*G(x)>0` on the intervening compact interval. Endpoint positivity alone does not determine the integrated block. No global rank-seven positivity or propagation to all orders follows from the current result.

## Lean implementation and verification

Six new modules and one extension:

- `HTGeometry/HankelSuccessorSchurStrict`: exact determinant factorization and strict Schur equivalence for every strict finite head.
- `RHTower/ThetaCusp/ThetaCuspFirstAtomReflectionJets`: extended through order twelve by symbolic polynomial identities.
- `RHTower/ThetaCusp/ThetaCuspNativeTwelfthJetLimit`: first-atom limit, complete-source transport and lower-order compensation.
- `RHTower/ThetaCusp/ThetaCuspNativeEvenFourTail`: explicit Gaussian square decomposition and complete corrected matrix tail.
- `RHTower/ThetaCusp/ThetaCuspNativeEvenHead`: strict actual head, including zero.
- `RHTower/ThetaCusp/ThetaCuspEvenFourCompensation`: exact scalar comparison, fixed source coefficient and compact-gap theorem.
- `RHTower/ThetaCusp/ThetaCuspEvenFourCenterIntegration`: entry integrability, exact moment preservation and weighted compact-gap theorem.

Each module was checked in scratch with one foreground `lake env lean` process at a time. Only needed oleans were emitted. New imports are wired into both relevant umbrellas without umbrella or full builds. The formal lint gate passed. Seven new capstones were audited once; their only axioms are `propext`, `Classical.choice` and `Quot.sound`.
