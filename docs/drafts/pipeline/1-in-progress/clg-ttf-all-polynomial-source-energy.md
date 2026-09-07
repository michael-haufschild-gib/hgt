# CLG/TTF: direct all-polynomial source-sign attempt

**Status:** sign open. The identities below are paper derivations from the existing source
calculus, not new Lean theorems or a proof of RH. No numerical experiment is required for them.

**Full chain:** literal theta source → every signed center-mixed Hankel form nonnegative →
Fourier-current sign → Xi Bezoutian orientation → RH.

The target is every polynomial at every critical aperture, not another fixed-rank determinant.
The finite coefficient queue and single-flux numerical probe do not discharge this target.

## Exact normalization and cancellation

Write `Φ = thetaCuspFullSource`, `ψ_a(x) = exp(ax) Φ(x)`, `M = -i d/dx`, and
`p(z) = Σ_i v_i z^i` with real coefficients. Put `r(z)=p(2z)` and
`f_a=r(M)ψ_a`. Throughout, `0<a<1/2` and inner products mean
`⟨f,g⟩=∫ conjugate(f) g` on the full real line.

The existing `ThetaCuspTiltedSchwartz` supplies these finite differential filters in Schwartz
space. `HedenmalmAutocorrelationPath` identifies the actual mixed density with the aperture
derivative of the tilted autocorrelation. With the plus-tilt convention used here, evenness gives

```
C_a(t) = ∫ exp(2ax) Φ(x+t) Φ(x-t) dx,
∂_a C_a(t) = ∫_(r>0) r sinh(ar) Φ(r/2+t) Φ(r/2-t) dr.
```

The factor two in `r(z)=p(2z)` retains the exact scale in
`ThetaCuspCenterMixedSignedJetCompleteness`: `m_n=2π·2^(-n)·s_n`.
Consequently, for the actual signed Hankel quadratic form `Q_a(v)`, Plancherel gives

```
Q_a(v) = d/da ||f_a||² = 2 ∫ x |f_a(x)|² dx.                 (1)
```

The second equality needs a cancellation, not a discarded term:
`∂_a f_a = x f_a - i r'(M)ψ_a`, and
`⟨r(M)ψ_a,r'(M)ψ_a⟩` is real because both Fourier multipliers are real.
Its contribution to the real energy derivative is therefore zero. This argument uses real
polynomial coefficients; it must not be asserted for arbitrary complex filters without adjustment.

Differentiation under the integral uses a compact aperture neighborhood inside `|a|<1` and the
finite derivative bounds in `ThetaCuspTiltedSchwartz`; no all-degree uniform domination is claimed.

## Attempt to produce the sign from the full source

Choose any fixed `c>0` and retain the exact Gaussian residual

```
h_c = -Φ' - c x Φ,
g_a = r(M)(exp(ax) h_c).
```

All terms are Schwartz: `exp(ax)h_c=(a-cx)ψ_a-ψ_a'`. Applying the filter to this identity yields

```
∂_x f_a = (a-cx)f_a + i c r'(M)ψ_a - g_a.
```

Integration by parts gives `Re⟨f_a,∂_x f_a⟩=0`; the same real-multiplier cancellation removes the
`i c` term. Thus the exact all-degree identity is

```
(c/2) Q_a(v) = a ||f_a||² - Re⟨f_a,g_a⟩.                    (2)
```

For a Gaussian source the residual vanishes and this supplies the sign at every degree.
For the literal theta source the remaining obligation is precisely

```
Re⟨r(M)ψ_a, r(M)(exp(ax)(-Φ'-cxΦ))⟩ ≤ a ||r(M)ψ_a||²       (3)
```

for every real polynomial and every critical aperture. Equation (3) is an unresolved
source-specific comparison, not an extra premise that may be inserted into a final RH theorem.
Changing `c` only rearranges the exact identity; it does not prove the comparison.

## Where the attempted estimate fails

The ordinary Cauchy–Schwarz bound loses the required cancellation already at zero aperture.
Here `Φ` is even, `h_c` is odd, and `Re⟨r(M)Φ,r(M)h_c⟩=0`. For the constant filter,
however, `||Φ|| ||h_c||` is strictly positive: `h_c=0` would make Φ Gaussian, inconsistent
with its positive value and proved `C exp(9x/2-π exp(2x))` upper tail envelope. By continuity this
absolute-norm estimate cannot be bounded by `a||ψ_a||²` for all sufficiently small positive `a`.
This rejects that estimate, not the exact signed comparison (3).

The modular drift and energy bounds in `ThetaCuspModularEnergyBounds` control the source orbit.
They do not currently bound (3). In a logarithmic-derivative approach, putting
`W=-Φ'/Φ-cx` introduces `[r(M),[r(M),W]]`; its differential expansion contains derivatives
of W through order `2 deg(r)`. Bounds at a fixed derivative order cannot silently discharge
the universal polynomial quantifier. No sign-preserving all-order estimate for this term has
been derived from the modular system.

## Parity refinement: exact curvature, still no sign producer

Put `E_r(a)=||r(M)ψ_a||²`. Differentiating (1) once more, retaining the commutator and
integrating its real part by parts, gives the paper identity

```
E_r''(a) = 4 ||x r(M)ψ_a||² - 2 ||r'(M)ψ_a||²
           + 2 Re⟨r(M)ψ_a,r''(M)ψ_a⟩.                       (4)
```

The negative derivative norm and the signed last pairing must both be retained. At zero
aperture, the unnormalized Fourier transform is the real function `Xi`, so the same identity is

```
E_r''(0) = (1/π) ∫ r(b)² (Xi'(b)² - Xi(b) Xi''(b)) db.      (5)
```

Thus differentiating the parity cancellation exposes the first Laguerre margin; it does not
turn the pairing into a norm square. `XiLaguerrePolya.xi_laguerre_inequality_of_rh` requires RH
(the declaration namespace is `RHTower`) and cannot be used to close this step. The exact
completed-flux identity in `CompletedFluxLaguerreReader` also retains its sign as an obligation.
Even a proof of (5)'s sign would still require an argument at positive apertures to prove (3).

The existing `HTGeometry.LaguerreKernelCounterexample` excludes a proof from generic positivity,
evenness and log-concavity. It does not exclude a proof from the literal theta modular identities.
Likewise `ThetaCuspWignerProductFiberNormalForm` already retains full shell summation and parity
pairing; its `thetaCuspCofinalCoupledConeKernel_negative_witness` excludes pointwise positivity,
while leaving the integrated source-mass comparison open. Neither result should be restated as
an impossibility theorem for every theta-source proof.

## Direct deformation attempt: retain the complete source

A finite shell prefix cannot serve as a smooth even starting source. The existing theorem
`deriv_thetaCuspFiniteShellPrefix_zero_pos` gives `P_N'(0)>0` for every nonempty prefix.
Thus `P_N(|x|)` has a cusp. The full source cancels every odd seam derivative by
`tsum_thetaCuspShellOddSeamJet_eq_zero`; this cancellation uses the complete sum. Likewise the
half-line interpolation `P_N + λ(Φ-P_N)` has derivative `(1-λ)P_N'(0)` at zero and retains its
cusp for `λ<1`. This rejects that smooth starting family, not arbitrary corrected approximants.
The negative Fourier tail of a prefix in `ThetaFiniteShellFourierBoundary` is not itself a
negative-current or negative-Hankel witness.

Instead take the smooth even family `Φ_τ(x)=exp(τx²)Φ(x)` and write

```
F_τ(z) = ∫ Φ_τ(x) exp(-izx) dx,
H(τ,a,b) = |F_τ(b+ia)|²,       J = ∂_a H.
```

For each bounded set of `τ,a,b`, the literal theta tail absorbs the quadratic and linear
exponentials and every fixed derivative required here. Differentiating the full integral gives
`∂_τ F_τ = -∂_z² F_τ`. Holomorphic differentiation then gives the exact paper identities

```
∂_τ H = (∂_a² H - ∂_b² H)/2,
∂_τ J = (∂_a² J - ∂_b² J)/2.                              (6)
```

Indeed `H_bb=2|F'|²+2 Re(conj(F)F'')` and
`H_aa=2|F'|²-2 Re(conj(F)F'')`. No positivity term was discarded. For a real polynomial `q`,
let `L_q=(1/(2π))∫q(b)J(τ,a,b)db`. Integration by parts twice yields

```
∂_τ L_q = (∂_a² L_q - L_(q''))/2.                         (7)
```

At `τ=0`, `L_(r²)` is the desired filtered energy derivative. Equation (7) is exact at every
finite degree, but it does not produce positivity: reversing heat time reverses the aperture
diffusion sign, and `q''=2(r')²+2rr''` retains its signed cross term. A maximum-principle
argument cannot treat (6) as an ordinary positive heat equation.

### Test the proposed backward sign propagation exactly

The existing `HTGeometry.LaguerreKernelCounterexample` supplies a direct test of this claim,
without numerical experimentation. Put `B=6/5`, `ω=laguerreOmega`, so `ω²=2π/5`, and deform
its source on `0≤τ≤π/2`:

```
K_τ(x) = exp(-(π-τ)x²) (cosh(ωx)+B).
u=π-τ,   A=exp(ω²/(4u)),   κ=ω/(2u).
```

Every member is positive, even, smooth and strongly log-concave. In fact, for `y=cosh(ωx)≥1`,

```
(log K_τ)'' = -2u + ω² (1+By)/(y+B)² ≤ -2u+ω² ≤ -3π/5.
```

The middle inequality follows from `(y+B)²-(1+By)=y²+By+B²-1≥0`.
The ordinary Gaussian integral, with the same unnormalized Fourier convention as above, gives

```
G_τ(z) = sqrt(π/u) exp(-z²/(4u)) (B+A cos(κz)).
S = B² + 2AB cos(κb)cosh(κa) + A²(cos²(κb)+sinh²(κa)),
∂_a |G_τ(b+ia)|²
  = (π/u) exp((a²-b²)/(2u))
      [ (a/u)S + 2Aκ sinh(κa)(B cos(κb)+A cosh(κa)) ].     (8)
```

At `τ=π/2`, `A=exp(1/5)>6/5=B`. Consequently every term in the bracket is nonnegative
for every `a>0` and real `b`: `S` is a modulus square and
`B cos(κb)+A cosh(κa)≥A-B>0`. The terminal current therefore has the desired sign at
every aperture and frequency, hence against every polynomial square.

At `τ=0`, `A=exp(1/10)` satisfies `1<A<B`, already proved by
`one_lt_laguerreAmp` and `laguerreAmp_lt`. Fix `b₀=π/κ`, with κ evaluated at zero time.
The current vanishes at `a=0`, but its derivative there is

```
∂_a² |G_0(b₀+ia)|² at a=0
  = exp(-b₀²/(2π)) (B-A) (6/(5π)) (1-A) < 0.             (9)
```

Thus the initial current is negative at `b₀` for all sufficiently small positive apertures.
Equations (8)–(9) refute backward sign propagation from a positive heat time using smoothness,
evenness, positivity and strong log-concavity alone. This extends the existing counterexample
on paper; the parameterized deformation and (6)–(9) have not been formalized here. It does not
exclude a propagation theorem using additional identities of the literal theta source.

The needed theta-specific comparison between the two second derivatives in (6), or another
argument controlling the full signed evolution down to `τ=0`, remains unproved. The generic
count declarations in `FinitenessTransition` assume their monotonicity/collision inputs and do
not supply it. `PolyaFrequencyIsTheHypothesis` also transports only an assumed equivalence;
it supplies no Pólya-frequency theorem for the source. Their documentation now states this scope.

## Direct arithmetic integral-of-squares attempt

The modular Lie recurrence in `PolynomialODEJetRankThreeGeneralClosure` produces every source
derivative, and `ThetaCuspModularSeamSourceJets` identifies its evaluation with the literal
source. This is an exact recurrence, not a positivity-preserving recurrence for the integrated
forms in (1). The available modular energy inequalities do not bound the signed pairing (3).
No all-degree estimate was obtained by applying that recurrence to the filtered energy.

A different attempt was to adapt an actual integral-of-squares identity to the source, rather
than assume its sign. [Gasper, equations (2.6)–(2.11)](https://arxiv.org/abs/0801.2996) obtains
nonnegative transverse derivatives for the Bessel carriers `K_(iz)(c)` from integrals of
real Bessel squares; the paper also treats Pólya's approximate Xi kernel. Applying those
formulas to the literal theta source requires an exact compatible expansion and control of
every cross term. The following calculation tests that requirement before any Lean build.

Write `φ_n(x)=thetaCuspSourceTerm x n`, for `n≥1`, and `q=πn²`. The literal definition is

```
φ_n(x) = (4q² exp(9x/2)-6q exp(5x/2)) exp(-q exp(2x)).
```

The smooth symmetrization `S_n(x)=(φ_n(x)+φ_n(-x))/2` has the pointwise absolutely convergent
expansion, obtained by expanding `exp(q exp(-2x))` and its reflection,

```
S_n(x) = exp(-2q cosh(2x))
         Σ_(k≥0) (q^k/k!) (4q²-6k) cosh((9/2-2k)x).       (10)
```

These are Bessel-type source factors, but their coefficients are negative whenever
`k>2q²/3`. The expansion therefore does not express the current as a sum of the nonnegative
diagonal terms from Gasper's formula. Squares of the transformed sum retain mixed terms.
This sign issue concerns this particular expansion, not every possible Bessel representation.

There is also an exact obstruction to integrating the raw shells before completing them.
`PrimeArchThetaAtomLikelihoodRatio.thetaCuspSourceTerm_shift_one` gives

```
φ_n(x) = n^(-1/2) φ_1(x+log n).
```

For `|a|<1/2`, let `C_a=∫ exp(ax)|φ_1(x)| dx`. This is finite and strictly positive:
the first shell has a double-exponential positive tail, an `O(exp(5x/2))` negative tail,
and is not identically zero. Translation gives the exact norm scaling

```
∫ exp(ax)|φ_n(x)| dx = n^(-a-1/2) C_a.                    (11)
```

Consequently the sum of these norms diverges at every critical aperture. Multiplying by
`exp(-ibx)` changes none of these norms. Pointwise absolute convergence of the theta series
does not authorize full-line shellwise Fourier integration.

The failure already has a sign at zero frequency. For `s=1/2+a∈(0,1)`, the substitution
`t=n exp(x)` and the existing first-atom Mellin identity give

```
∫ exp(ax)φ_n(x) dx = n^(-s) A(s),
A(s) = s(s-1) π^(-s/2) Γ(s/2)/2 < 0.                     (12)
```

Here `A` is the corpus `archFactor`, by
`EulerHedenmalmGammaStokesTransgression.mellin_thetaCuspSeed_eq_archFactor`.
The partial sums of (12) tend to negative infinity, whereas integrating the complete positive
source gives `∫exp(ax)Φ(x)dx>0`. Thus even ordinary summation of the raw full-line shell
integrals cannot be the intended representation. At `a=0`,
`A(1/2)=-Γ(1/4)/(8π^(1/4))`. This conclusion does not depend on RH or numerical evidence.

The available repair is already exact in the corpus: restrict each shell to the positive
half-line and include both Fourier phases there. `ThetaCuspShellHedenmalmCurrent` proves
absolute assembly of the resulting values, first derivatives, and complete shell-pair current.
`ThetaCuspWignerProductFiberNormalForm` further groups the complete divisor packets and both
orientations before the final integral. This repair retains a signed cross pairing; neither
(10) nor the diagonal Bessel-square identity proves its sign. The new scaling deductions
(10)–(12) are paper arguments here, not newly formalized declarations.

The unresolved work remains a phase-sensitive estimate for (3), retaining its cancellation at
`a=0` and controlling every polynomial degree. Ordinary source norm positivity, a finite
collection of coefficient identities, backward heat propagation, and raw shellwise
integral-of-squares assembly do not supply it. No new equivalent criterion is being promoted.

## Retain the seed's zero mean inside each arithmetic cell

The full-line obstruction (11) can be repaired before taking a Fourier transform. This tests
whether retaining the exact arithmetic cancellation also supplies the sign. Let
`g=thetaCuspSeed` and extend the shell parameter continuously by
`φ_t(x)=exp(x/2)g(t exp(x))`, including `φ_0=0`. The already formalized identity
`ThetaCuspSeedZeroMean.integral_thetaCuspSeed_Ioi_eq_zero` gives
`∫_(t>0) φ_t(x)dt=0` for each fixed `x`. Define

```
R_n(x) = φ_n(x) - ∫_n^(n+1) φ_t(x)dt,       n≥0.
Σ_(n≥0) R_n(x) = Φ(x).                                      (13)
```

The second identity follows by taking the limit of the finite sum: the discrete part tends
to `Φ`, and the continuum part tends to zero. The seed has the exact primitive
`g(t)=-2π(d/dt)(t³ exp(-πt²))`. In particular,

```
R_0(x) = 2π exp(5x/2) exp(-π exp(2x)),
R_n(x) = φ_n(x) + 2π exp(5x/2)
           [(n+1)³ exp(-π(n+1)² exp(2x))
             - n³ exp(-πn² exp(2x))].                       (14)
```

Here is the convergence gain, with the derivative control required by the actual target.
Fix `|a|<1/2`, put `σ=a+1/2>0`, and let `K_a(y)=exp(ay)φ_1(y)`. Dilation gives

```
exp(ax)φ_t(x) = t^(-σ) K_a(x+log t),
∂_t(exp(ax)φ_t(x))
  = t^(-σ-1)(K_a'-σ K_a)(x+log t).
```

Both profiles are Schwartz: their left tails decay exponentially and their right tails
decay double exponentially. Write `φ_n-φ_t=-∫_n^t ∂_v φ_v dv` inside each cell.
Translation, Minkowski's inequality, and `|x|^k≤C_k(|x+log v|^k+|log v|^k)` then give,
for either `p=1` or `p=2` and every fixed pair of nonnegative integers `j,k`,

```
||x^k D^j(exp(ax)R_n)||_p
  ≤ C_(a,j,k,p) n^(-σ-1)(1+log(n+1))^k,       n≥1.           (15)
```

The zero cell is handled directly by (14). Thus the repaired series converges absolutely
in every weighted derivative norm needed by a fixed polynomial filter. In particular,
with `f_n=r(M)(exp(ax)R_n)`, the complete signed form is the legitimate double pairing

```
Q_a(r) = 2 Re Σ_(n,m≥0) ∫ x conjugate(f_n(x)) f_m(x) dx.     (16)
```

Absolute convergence follows from
`Σ_(n,m) |∫x conjugate(f_n)f_m| ≤ (Σ_n ||x f_n||_2)(Σ_m ||f_m||_2)`.
This proves an admissible representation, not positivity of its right-hand side.

The Fourier transform reveals exactly what has been gained. For `s=σ-ib`, (12) and (14) give

```
F_(R_0)(b+ia) = A(s)/(s-1),
F_(R_n)(b+ia) = A(s)[n^(-s)-∫_n^(n+1)t^(-s)dt],   n≥1,
F_Φ(b+ia) = A(s)[1/(s-1)
                   + Σ_(n≥1)(n^(-s)-∫_n^(n+1)t^(-s)dt)].   (17)
```

The bracket is the continuum-subtracted continuation of `ζ(s)`: its summands are
`O_s(n^(-Re(s)-1))`, locally uniformly for `Re(s)>0`; for `Re(s)>1` the continuum
integral cancels `1/(s-1)`, leaving the usual series. Analytic continuation identifies the
bracket throughout `Re(s)>0`, away from the pole. Formula (17) therefore repairs the invalid
interchange without providing an additional arithmetic inequality.

Nor are the repaired shells individually positive for the required current. Taylor's formula
in the cell parameter, in weighted Schwartz seminorms, gives

```
n^(3/2)R_n(y-log n) = B(y)+O(1/n),
B = φ_1/4-φ_1'/2.
```

To check the error, apply second-order Taylor expansion to
`(1+v/n)^(-1/2)φ_1(y+log(1+v/n))`, integrate `0≤v≤1`, and use bounded profile
derivatives for `0≤v/n≤1`. After tilt and filtering,
`n^(σ+1) f_n(y-log n)=r(M)(exp(ay)B(y))+O(1/n)` in both `L²` and `y`-weighted `L²`.
For a nonzero real polynomial `r`, the limiting function is nonzero: `B` is nonzero, and
a nonzero polynomial Fourier multiplier cannot annihilate a nonzero Schwartz function.
Consequently

```
2∫x|f_n(x)|²dx / ||f_n||² = -2log n+O(1).                  (18)
```

The diagonal current is eventually negative for every fixed nonzero filter. This statement
does not determine the sign of the complete sum (16); its cross terms are essential.

An explicit test of those cross terms is available even before filtering. For `u,v>0`, put
`β=a+5/2`, `P=u²+v²`, and `h=u²v²/P²`. A Gaussian substitution gives the exact pair integral

```
I_a(u,v) := ∫exp(2ax)φ_u(x)φ_v(x)dx
  = 2π²u²v²(πP)^(-β)Γ(β)[9-6β+4β(β+1)h].                (19)
```

Indeed, expand the product into its `exp(4x)`, `exp(6x)`, and `exp(8x)` terms and use
`Γ(β+1)=βΓ(β)` twice. At `a=0`, the bracket is `-6+35h`: it is positive on the diagonal
and negative, for example, at `u=1,v=3`. Cell subtraction applies in both parameters;
the constant-filter current uses `∂_a I_a`. Positivity of the Gram kernel `I_a` as a
quadratic form does not imply positivity of this aperture derivative. No bound on the full
subtracted cross sum, for general polynomial filters, has been established here.

Equations (13)–(19) are paper calculations, not new Lean declarations. They retain the
cancellation and expose the unresolved pairing; they do not close or retire CLG/TTF.

## Test one correction profile for the whole hierarchy

The proved finite-rank center compensation does not extend to a nonzero fixed displacement
profile `C(t)` multiplying the aperture-independent correction `G(x)`. If `C(0)=0` and
`Φ(x+t)Φ(x-t)+G(x)C(t)` satisfies every positive-definite two-point bound, logarithmic
concavity forces `|G(x)/Φ(x)²| |C(t)|≤2`. The normalized coefficient tends to negative
infinity, so `C=0`. The sharper allowed interval and the rigidity theorem are proved in
`ThetaCuspFixedCenterCorrectionRigidity`. See the
[exact proof, positive survivor and scope](../5-failed/clg-ttf-fixed-center-profile-compensation.md).

This excludes that proposed all-order certificate. It does not exclude center-dependent
correction profiles, formal moment sequences without a kernel realization, or corrections
using the different aperture-dependent flux coefficient. The original finite-rank theorems
remain valid. Any proposed global correction must be tested against its full kernel bounds,
not only its first few derivatives.

## Damped exact flux and the remaining full signed comparison

A center-dependent multiplier must enter the full flux derivative. For
`F_a(r)=r² sinh(ar)Φ(r/2)²`, differentiating `exp(-λr)F_a(r)C(t)` gives the exact
normalized correction

```
p_x(t)+h_(a,λ)(x)C(t),
p_x(t)=Φ(x+t)Φ(x-t)/Φ(x)²,
h_(a,λ)(x)=exp(-2λx)[2+2ax coth(2ax)+2xℓ'(x)-2λx],
h_(a,λ)(0)=3.                                             (20)
```

The term `-2λx` cannot be omitted: it is the derivative of the damping multiplier.
For `λ>1`, this normalized correction decays at the far center tail, so the preceding
divergent-coefficient argument alone does not apply. Its full Fourier compatibility was tested
in one preregistered, 4.7-second Runpod experiment. At aperture `1/4`, each tested damping
`7/4,2,3,5` has two centers whose native Fourier values are both negative while their
correction coefficients have opposite signs. One correction transform value would have to
be both positive and negative. Independent 60- and 90-digit checks agree. These literal-source
signs are numerical guidance, not Lean premises or an exclusion of untested parameters.

There are also analytic restrictions on the parameter, independent of these numerical values.
Slow damping `λ≤3/2` forces a nonpositive correction transform at every fixed frequency
by the complete-source tail asymptotic. It therefore cannot repair the native negative Fourier
value at center zero, where `h=3`; this also holds when the local diagonal may change.
Sufficiently fast damping forces a zero of `h` inside the already formalized open chamber
where the native odd rank-three determinant is negative. That chamber cannot be repaired
when the entire correction vanishes. The [derivations, numerical evidence and exact limits](../2-fully-proven/computations/2026-09-07-clg-ttf-damped-flux-fourier/REPORT.md)
leave a bounded scalar parameter range undecided. These two deductions have paper proofs,
not new Lean proofs. No complete retirement of the scalar family is claimed.

A correction that depends jointly on center and frequency can avoid the sampled conflict.
However, with `W(x,b)=∫p_x(t)cos(2bt)dt` and
`q_a(x,b)=4x sinh(2ax)Φ(x)²W(x,b)`, a nonnegative corrected density of the form
`q_a+∂_xH_a`, with both boundary values of `H_a` zero, still requires

```
∫ max(-q_a(x,b),0)dx ≤ ∫ max(q_a(x,b),0)dx   for every b.   (21)
```

This is the complete signed Fourier-current comparison already required by the route.
An antiderivative definition of `H_a` makes its terminal boundary exactly this unsolved
balance; it supplies no independent positive reserve. Neither the existing source inequalities
nor this experiment prove (21). Additional scalar scans and finite-rank corrections do not
address that remaining comparison.

## Complete modular logarithmic curvature: a positive input with a different target

Let `H=Bottcher.completedThetaProfile`, `g=log H`, and `K=g''`. The literal normalization is
`H(x)=exp(x/2) θ(exp(2x))`, where `θ(t)=Σ_(n∈ℤ)exp(-πn²t)`. The existing modular source
calculus identifies `g'=thetaCuspModularMassDrift/6` and `Φ=(H''−H/4)/2`.

There is an unconditional all-order positive kernel here. With the Fourier convention
`Khat(b)=∫K(x)exp(-ibx)dx` and `τ=b/2`,

```
Khat(b) = τ² [5−4 cos(τ log 2)] |ζ(1+iτ)|² / cosh(πτ/2),  b≠0,
Khat(0) = 1.                                             (22)
```

This is known mathematics: [Lagarias–Rains, Theorem 7.4 and (7.16)](https://arxiv.org/pdf/math/0104176)
give the corresponding positive canonical measure and the infinite divisibility of
`H(0)/H(x)`. Formula (22) expresses that measure in this corpus's variables. It is not a
new theorem or a Lean-checked source incidence in this card.

A direct normalization check uses the Jacobi product. If
`I(s)=∫_0^∞ t^(s−1)log θ(t)dt`, its logarithmic product expansion gives

```
I(s)=Γ(s)π^(-s)ζ(s)ζ(s+1)[2−5·2^(-s)+2·2^(-2s)].         (23)
```

Termwise Mellin integration is absolute for `Re s>1`. The complete logarithm behaves as
`−(log t)/2` at zero, so its integral extends to `Re s>0`; the apparent pole at `s=1`
on the right cancels. Two integrations by parts give
`∫exp(2sx)K(x)dx=2s²I(s)` in this half-plane. Modular reflection makes `K` even and
rapidly decreasing at both ends, permitting the boundary limit `s→iτ`.
The zeta functional equation rewrites the right side as

```
s²[4 cosh(s log 2)−5] ζ(1−s)ζ(1+s) / cos(πs/2).
```

This yields (22). At zero, the zeta pole cancels `τ²`; independently,
`∫K=g'(+∞)−g'(−∞)=1`. Thus no numerical value enters the sign. The resulting spectral
density is integrable with every polynomial weight. For any real polynomial `p`,

```
Σ_(i,j) p_i p_j (-i)^(i+j) K^(i+j)(0)
  = (1/(2π)) ∫ p(b)² Khat(b)db ≥ 0,                       (24)
```

where odd derivatives vanish and the surviving even coefficient is `(-1)^((i+j)/2)`.
This is an all-order statement for `K`, distinct from the signed forms of `D_a`.

The exact source reconstruction retains the missing difficulty:

```
Φ(x) = H(x) [K(x)+g'(x)²−1/4]/2.                         (25)
```

The bracket is positive from the literal source theorem, but (24) does not supply the
Fourier-current sign after this nonlinear expression and multiplication by `H`.
The positive-definite family is `(H(0)/H)^u` for `u>0`. Its reciprocal has the explicit
two-point Gram determinant `1−(H(x)/H(0))²<0` for `x≠0`, since the actual mass increases
strictly away from zero. Consequently Schur multiplication cannot transfer its positive
kernel law through (25). This rejects that transfer argument, not other uses of the
logarithmic-curvature measure. No estimate for the filtered signed pairing (3) follows here.

The [normalized theta-power test](../5-failed/clg-ttf-theta-power-curvature-transfer.md)
gives a stronger obstruction to that generic transfer. Lean proves that
`H_v(x)=H(x/v)^v` has a positive cusp source for every `0<v<=4`, with `v=1` exactly
the literal source. Positive mass log curvature and infinite divisibility of inverse mass
persist throughout this family. At `v=4`, the four-square Mellin factorization gives
off-line zeros inside the same normalized critical strip, so the all-aperture current
sign fails. This last transform argument is paper-only. The positive survivor is the
new global modular energy floor `A+4u^2/3>12` and its actual theta-power source theorem
in `ThetaCuspModularEnergyFloor`; it supplies no sign for (3).

The [complete divisor/Eisenstein norm test](theta-wigner-eisenstein-orientation-current.md#exact-geodesic-period-and-cancellation-of-its-cusp-correction)
also leaves (3) open. The regularized geodesic period equals
`R(a,b)=|Lambda(1/2+a+ib)|^2`; its rational cusp correction cancels the Green boundary
term exactly, returning `partial_a[P_b(a)R(a,b)]/(8a)` for the Bezoutian diagonal.
The classical Maass–Selberg norm at a nontrivial zero `rho` instead equals the strictly
positive `|Lambda(2-rho)|^2 T^(1-Re(rho))/(1-Re(rho))` for `T>=1`, throughout
`0<Re(rho)<1`. Norm positivity supplies no critical-line restriction there. These are
paper identities; no new sign-preserving comparison or Lean receiver was obtained.

**Current assessment:** the required all-order sign for `D_a` remains open. The fixed-profile
obstruction and its quantitative survivor, and the normalized theta-power positive survivor,
have Lean proofs; (1)–(25), the damping restrictions, and the theta-power transform obstruction
are paper analysis or cited mathematics. The existing bounded computation rejects four
candidate certificates numerically. The curvature and theta-power analyses required no
numerical computation. The frontier map remains read only.
