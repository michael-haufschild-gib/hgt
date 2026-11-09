# Euler–FE transport theory

## Motivation and target

The Euler product controls positive prime data in a half-plane of absolute convergence.
The Riemann functional equation reflects the continued function across the critical line.
This programme seeks the missing interaction that forces an exceptional zero to recur at
unbounded heights. Its target is AAL, `Θ = Θ∞`, or a counterexample in the specified
Euler–FE class that settles the falsification branch.

For ζ, `Θ` is the supremum of zero real parts and `Θ∞` is the supremum remaining after
arbitrary bounded-height deletions. Failure of AAL leaves a finite top layer above the
tail. The corresponding prime error contains a finite oscillation `x^Θ T(log x)` with
a smaller remainder exponent. The question is why the exact arithmetic and reflection
cannot support that isolated oscillation.

## Objects and language

- **Reflection:** `s ↦ 1−s̄`, with the completed functional equation and pole terms retained.
- **Transport:** a rule producing zeros above every height from a given exceptional zero.
- **Depth:** `Re ρ−½`. **Replication at the same depth** retains this number exactly.
- **Rigid oscillation:** the finite exponential sum forced by an isolated top layer of ζ.
- **Two-scale coupling:** an identity linking the reflected oscillation and the positive
  Euler data at different scales, with both infinite tails retained.
- **Resonant tower:** the evaluations at powers of a base such as `exp(π/γ)`, detecting
  the mode of ordinate `γ`; the desired law couples `γ` to `(2k+1)γ`.
- **FE defect:** the uncompleted critical-line discrepancy `g` in the Hamburger strip
  identity. Its two costs are `D₁=∫⁻‖g‖ₑ` and `D₂=∫⁻‖g‖ₑ²`.
  Gamma-weighted integrability is a different condition.
- **Canonical boundary:** the strong `L²` limit `Bg` of the actual Hamburger Laplace
  defect on vertical lines approaching the imaginary axis; `‖Bg‖²=π⁻¹‖g‖²`.
- **Layer cost:** the infimum of either defect cost over nonclassical countable Beurling
  systems in the stated analytic class carrying a finite nonempty off-line layer.
  Both infima are infinite.

## Foundations and the missing mechanism

The corpus already proves AAL equivalent to zero transport with every positive real-part
loss, and identifies the rigid finite-layer world when AAL fails. Bohr recurrence supplies
transport where uniform holomorphic recurrence is actually available. It does not extend
itself through the critical strip.

The proposed mechanism has four parts:

1. Express the finite top oscillation through the actual prime error and theta transform.
2. Track its reflection from exponent `Θ` to `1−Θ`, including the pole and archimedean terms.
3. Use Euler positivity between atoms to force coherent reproduction of this reflected
   oscillation by the infinite zero tail at every scale.
4. Convert that reproduction into zeros of depth `Θ−½` at unbounded heights.

Parts 2–4 require new arithmetic theorems. Reflection alone preserves absolute height.
An implication assuming the required reproduction or recurrence is not a construction
of the transport operator.

## Milestones

| Milestone | Required mathematical outcome |
|---|---|
| M1 | Proved in the explicit Hamburger strip class for `g∈L¹` or `g∈L²`: exactly the rational primes (B122). |
| M2 | Proved in that class: every nonclassical system has `D₁=D₂=∞`, hence infinite layer cost (B84). |
| M3 | Prove replication for one exceptional quartet of ζ at the same depth. |
| M4 | Prove `LinAt C` for an actual finite `C`, coupling the global and asymptotic depths. |
| M5 | Prove AAL, with the corpus's ZAL implication then giving RH. |

M1 and M2 classify other Euler systems. Complete rigidity does not exclude a finite
layer of ζ. Perturbations with integrable or square-integrable defects provide no nonclassical
models; transport must use exact identities of ζ. M3 is an endpoint target:
AAL permits arbitrarily small positive loss and does not by itself give same-depth copies.

## Tools to develop and open questions

| Tool | Question |
|---|---|
| FE-to-transport operator, B112 | Which exact combination of reflection and Euler factorization changes height? |
| Quantitative recurrence of the rigid oscillation | Which returns survive coupling to the complete prime and zero tails? |
| Resonant-tower identities | How do the modes at `γ` and `(2k+1)γ` constrain each other without a growing frozen head? |
| Conditional prime-discrepancy defect calculus | Nonclassical systems have infinite defect in the stated class, regardless of conditional convergence; what exact identity supplies transport instead? |
| Same-depth replication theorem | Why must one exceptional top force infinitely many tops at its exact real part? |

The critical-zero coupling must be derived from the actual continued Euler product.
Counting zeros, mean-square bounds, or phase recurrence alone do not identify the needed
joint arithmetic information.

## Defect transport and arithmetic rigidity

The classification uses a countable positive Beurling system with
`Σ_x ‖x‖^(-3/2)<∞`. Its Hamburger strip data consist of a function `E` continuous
on `½≤Re s≤3/2`, holomorphic inside, with `‖E(s)‖≤C/(1+Im(s)²)`, and identities

    Γℝ(s) ζ_B(s) = E(s) + β Γℝ(s−1),                     Re s = 3/2,
    E(s)−E(1−s) = −β[Γℝ(s−1)−Γℝ(−s)] + Γℝ(s)g(Im s/2), Re s = 1/2.

The uncompleted defect `g` is measurable and polynomially bounded. If `g∈L¹` or
`g∈L²`, then `β=½`, the generalized-integer counting measure is the ordinary one,
each positive integer has exactly one generalized-integer factorization, `ζ_B=ζ`
on `Re s>1`, and the prime labels are in norm-preserving bijection with rational
primes. No lattice, nonempty-label, recurrence, residue-bound or defect-size premise
is added. Every nonclassical system in this strip class has both `D₁=∞` and `D₂=∞`.
In either finite-cost class, the original strip defect vanishes pointwise. The
finite-energy theta formulation also gives almost-everywhere vanishing directly.

The terminal classification and infinite-cost theorems are in
`IntegrableFunctionalEquationsDetermineThePrimes.lean` and
`FiniteEnergyFunctionalEquationsDetermineThePrimes.lean`.
`FiniteEnergyRigidityAnnihilatesTheDefect.lean` proves vanishing of the defect itself.
Their direct Lean checks and transitive axiom audits use only `propext`,
`Classical.choice`, and `Quot.sound`.

### The exact analytic operator

Euler reflection writes the defect kernel as
`z^(-½+2it)/sin(π/4+πit)`. On the two imaginary rays its squared Mellin weights are
`4/(1+exp(4πt))` and `4/(1+exp(-4πt))`; their sum is `4`. Mellin–Plancherel gives

    ∫ℝ |J_g(iy)|²dy = π⁻¹∫ℝ |g(t)|²dt,       g∈L¹∩L².

Density defines the unique continuous extension `B:L²(ℝ)→L²(ℝ)` with the same
norm law. It represents the actual transform: put `s(t)=½+2it` and
`A(t)=2^s(t)Γ(s(t)/2)/(√πΓ((1-s(t))/2))`. Then
`|A(t)|=√(2/π)` and `A(t)Γ(1-s(t))=1/sin(πs(t)/2)`. The half-line Mellin unitary
`M` determines a bijective source map by

    (Mψ_g)(ξ)=½g(-πξ)A(-πξ),       ‖ψ_g‖²=(2π²)⁻¹‖g‖²,
    J_g(z)=∫₀∞ψ_g(u)e^(-zu)du,    Re z>0.

These transforms exhaust the right-half-plane Hardy class. Their vertical traces
converge strongly in `L²` to `Bg`; every `L²` test pairing passes to the boundary.
The range of `B` is exactly the Fourier image of positive-half-line data, and
`√πB` is unitary onto that space. Thus the analytic transform alone permits every
Hardy boundary value; the restriction comes from the actual positive atomic theta law.

The constructions are in `TheBoundaryPreservesDefectEnergy.lean`,
`FiniteEnergyDefectsHaveCanonicalBoundaries.lean`,
`TheDefectHasAUnitaryMellinSource.lean`,
`FiniteEnergyDefectsAreLaplaceTransforms.lean`, and
`FiniteEnergyDefectsConvergeToTheirBoundary.lean`.

### How arithmetic removes the defect's freedom

For a physical tent `T_(h,a)(y)=max(1-|y-a|/h,0)`, the actual theta identity gives

    ½∫ T_(h,a)(u)dν_B(u)
      = hβ + hΣ_x sinc²(πh‖x‖)cos(2π‖x‖a) + E_g(h,a),
    E_g(h,a)=∫ T_(h,a)(y)Re(Bg(y))dy,       0<h≤1, a>h.

Cauchy–Schwarz gives `|E_g(h,a)|≤√(2h)‖Bg‖₂`, uniformly in the centre.
At fixed width, the moving window's `L²` tail gives `E_g(h,a)→0` as `a→∞`.
The absolutely convergent cosine sums have common distant almost periods.
The unit atomic mass floor therefore forces the exact two-width law
`P_h(a)<¼ ⇒ P_(h/2)(a)=0`. In the atom-free interval `(0,1)`, sufficiently small
tent errors vanish. Lebesgue differentiation gives `Re Bg=0` almost everywhere
there. Reflection of the actual interior identity makes this real boundary even.
Consequently its origin tent pairing is zero.

Strong boundary convergence now removes the origin Fejér defect, leaving

    Σ_x sinc²(π‖x‖)=0.

Positivity forces every norm to be a natural number. Independently, the source
representation gives the height-uniform radial estimate

    |εJ_g(ε+iy)|≤‖ψ_g‖₂√(2ε)/2 → 0.

Thus defects change no atomic Abel residue, and the pole is real. Integer
periodicity identifies Abel means at zero and one, fixing `β=½`. Positivity fixes
every atomic multiplicity at one. A missing positive integer would have zero
atomic residue but the same positive Abel density as zero, a contradiction.
Finite norm fibres recover the generalized integers and prime generators.
An empty prime-label system would force both `2β=1` and `β=0`.

The exact tent, recurrence, unit-gap, integer-support and residue theorems are in
`FiniteEnergyDefectsObeyTheTentIdentity.lean` through
`FiniteEnergyDefectsPreserveAtomicResidues.lean`; their proof cards are
`docs/drafts/pipeline/3-formalized/euler-fe-finite-energy-tent-transport.md` and
`docs/drafts/pipeline/3-formalized/euler-fe-finite-energy-integer-support.md`.
The integrable boundary argument belongs jointly to `ExactEventTheory`.
These results settle the stated classification branches; M3–M5 still require
height transport for ζ itself.

Finally, the bijective Mellin source and injectivity of the half-line Laplace
transform make `g↦J_g` injective on `L²`. The classified integer measure obeys
Jacobi's exact theta law; subtracting its Laplace identity from the original law
gives `J_g=0`, hence `g=0` almost everywhere. In the strip formulation, the actual
boundary identity makes `Γℝ(½+2it)g(t)` continuous. Its almost-everywhere vanishing
and the nonzero Gamma factor give pointwise vanishing without an extra continuity
assumption on `g`.

### Local identification at arbitrary defect cost

Theta data retain the entire polynomially bounded defect even when both unweighted
costs are infinite. Put `H_g(t)=Γℝ(½+2it)g(t)`. Gamma decay absorbs polynomial
growth, giving `|H_g(t)|≤K exp(-|t|/2)`. In logarithmic scale the actual kernel is

    K_g(exp u) = (2π)⁻¹ exp(-u/4) ∫ H_g(t) exp(-iut)dt.

The Fourier integral extends holomorphically to `|Im u|<½`. Consequently equality
of `K_g` and `K_h` on any interval `(a,b)`, `0<a<b`, determines `g=h` almost
everywhere. The identity theorem propagates equality to all logarithmic scales;
Fourier injectivity and the nonvanishing Gamma factor recover the original
defects. This is an exact uniqueness theorem, without a stability estimate or
an arithmetic recurrence premise.

`LocalThetaDataDetermineTheDefect.lean` constructs this local identification.
It also closes the integrable classification's defect endpoint: Jacobi's exact
theta law makes the classified kernel zero, so the uncompleted defect vanishes
almost everywhere. The original strip identity upgrades this to pointwise
vanishing, as formalized in `IntegrableRigidityAnnihilatesTheDefect.lean`.
Thus in either finite-cost class the defect itself is zero; classification does
not merely identify its underlying Euler system.

### Local Gaussian defects identify complete causal tails

The literal Gaussian imposes a separate rigidity on source deformations. Put
`ψ(x)=exp(x/2−π exp(2x))`, `a(x)=π exp(2x)` and
`L=∂x−(1/2−2a(x))`. An outward causal density acts by

    T_K ψ(x) = ∫₀∞ K(t)ψ(x+t)dt.

Its admissibility condition is integrability of the explicit rate density

    q_K(u)=½ exp(−¾ log(1+u)−u) K(½log(1+u)),       u>0.

This includes every measurable complex kernel of exponential order, with
arbitrary signs and infinite support. The rate change `u=exp(2t)−1` gives,
for `a(x)>1`,

    T_K ψ(x)=ψ(x) ∫₀∞ q_K(u) exp(−(a(x)−1)u)du,
    L(T_K ψ)(x)=−2a(x)ψ(x) ∫₀∞ u q_K(u) exp(−(a(x)−1)u)du.

For any open interval `(A,B)` with `π exp(2A)>1`, the local defects of
`cψ+T_Kψ` and `dψ+T_Hψ` agree exactly when `K=H` almost everywhere on
the entire positive ray; `c,d` remain arbitrary. The first rate moment is
holomorphic in the right half-plane. Local equality propagates, and Laplace
uniqueness applied to `u(q_K−q_H)exp(−u)` identifies the rate densities.
The strictly positive change-of-variables Jacobian then recovers the original
causal kernels. No undamped moment assumption is needed.
An admissible infinite causal correction therefore restores the literal Gaussian
equation only by cancelling the entire non-scalar kernel.

`TheGaussianDefectDeterminesTheCausalTail.lean` constructs local rate-moment
recovery. `TheCausalGaussianDefect.lean` proves the actual integral identity,
exponential-order admission and `causalGaussian_defect_local_iff`, the exact
scalar ambiguity. This extends the
Gaussian source constraint beyond finite rational zero surgery. It identifies
causal deformations from their defect; it does not produce height replication
for the undeformed ζ.

### Infinite atomic corrections and the causal measure algebra

The source constraint also detects atoms and singular continuous measures.
For a positive causal measure `μ`, put

    r(t)=exp(2t)−1,   w(t)=exp(t/2−r(t)),   Q_μ=r_*(w μ).

The admission condition is `∫w dμ<∞`; total mass may be infinite. Every causal
measure with any convergent Laplace transform satisfies it, so logarithmic
Euler measures in a Dirichlet half-plane are included. The exact identities are

    T_μψ(x)=ψ(x)∫exp(−(a(x)−1)u)dQ_μ(u),
    L(T_μψ)(x)=−2a(x)ψ(x)∫u exp(−(a(x)−1)u)dQ_μ(u).

Equality of defects on one open interval with `a(x)>1` determines
`μ|(0,∞)`. Exponential tilting turns the locally observed moment into a finite
Laplace measure. Analytic uniqueness determines that measure; cancelling the
positive tilt and the injective rate chart recovers the original source off
zero. For countably supported `A,B` and absolutely continuous `K,H`, equal
defects of `T_(A+K)ψ` and `T_(B+H)ψ` therefore force `A|(0,∞)=B|(0,∞)` and
`K=H`. Signed atomic and continuous corrections cannot cancel each other.

Composition retains the complete infinite sources:
`w(t+u)≤w(t)w(u)` makes weighted admission closed under causal convolution,
and Fubini proves `T_(μ*ν)ψ=T_μ(T_νψ)`. In particular, if `A` is a positive
countably supported causal measure with `A{0}=1`, then

    L T_(A+A*K)ψ = L T_(δ₀+A*H)ψ locally
      ⇒ A=δ₀ and K=H.

Here `K,H` are positive absolutely continuous causal measures; their difference
is the signed continuous surgery. Thus even an infinite normalized positive
Euler correction cannot repair a nonzero continuous Gaussian surgery. The
positive survivor is local reconstruction of the whole causal source, together
with its convolution algebra.

The exclusion also holds for normalized real signed atomic operators. Write the
operator as `A−B`, with `A{0}=B{0}+1`, and put

    μ=A+A*K+B*H,   ν=B+A*H+B*K.

Equal local defects of `T_μψ` and `T_νψ` force `A=B+δ₀` and `K=H`.
Source separation first fixes the atomic operator. After convolution distributes,
both continuous sides contain `B*K+B*H`. Gaussian weighting makes this common
measure finite, so cancellation is valid even when its undamped mass is infinite.
Removing the strictly positive weight then identifies the original continuous
measures. This remains a source calibration, not a height-replication theorem for ζ.

The formalizations are `TheGaussianRateMeasureIsLocallyVisible.lean`,
`TheGaussianDefectDeterminesCausalMeasures.lean`, and
`AtomicEulerCorrectionCannotRepairGaussianSurgery.lean`, and
`SignedEulerCorrectionCannotRepairGaussianSurgery.lean`.

### Gaussian prime currents and their continued finite part

The Gaussian transform of the full prime discrepancy has an unscaled finite
part throughout `0<σ≤1`. Put

    Gσ(y)=Σₙ Λ(n)n^(−σ)e^(−yn²)−∫₁∞u^(−σ)e^(−yu²)du,
    Bσ(y)=Σρ ½Γ((ρ−σ)/2)y^(−(ρ−σ)/2),
    A(s)=1/s+Γℝ′/Γℝ(s).

The zero sum is multiplicity-exact. Without any zero-free assumption,

    Gσ(y)+Bσ(y) → A(σ)−ξ′/ξ(σ),       y→0⁺.

The Gamma-subtracted germ of each zero tends to
`(ρ−½)⁻¹+(σ−ρ)⁻¹`. A summable inverse-square majorant justifies the limit
through the entire zero series; the trivial-zero and archimedean terms tend
to `A(σ)`. Thus this law retains the continued background that disappears
when only the leading oscillation is normalized.

If a finite set `F` contains every zero with `Re ρ≥σ`, the same limit holds
with `Bσ` replaced by its finite sum over `F`. Every complementary mode tends
to zero, dominated by the absolutely summable Gamma amplitudes. No uniform
gap below `σ` is required. In the rigid `¬AAL` world, the actual finite top
layer therefore suffices at every observation point between top and tail.

For `0<σ<1`, the exact functional equation gives the reflected law

    [Gσ(y)+Bσ(y)]+[G_(1−σ)(y)+B_(1−σ)(y)] → A(σ)+A(1−σ).

The infinite fields on both sides are essential to this statement. Removing
the finite top on one side does not justify truncating the reflected field.
This reflects the Mellin weight `σ`; identifying the literal theta action on
the prime oscillation remains open. The identity supplies no new zero height.
`TheFinitePartOfTheGaussianPrimeCurrent.lean` contains the full-series,
finite-layer and reflected laws.

### Resonance and comparison of damping scales

At an actual zero `ρ`, the Gamma mode at that point must be replaced by a
logarithmic term. Let `mρ` be its divisor multiplicity and retain every
nonresonant zero copy in

    Bρ(y)=Σ_{q:ρq≠ρ} ½Γ((ρq−ρ)/2)y^(−(ρq−ρ)/2),
    Cq=(½−ρ)/[(ρq−½)(ρq−ρ)].

For every `y>0`, this entire Gamma field converges absolutely. At every actual
zero, without an extremal-abscissa or simplicity assumption,

    Gρ(y)+Bρ(y)−(mρ/2)log y
      → A(ρ)−mρ/(ρ−½)−Σoff Cq+mργE/2,

where `γE` is Euler's constant. Translated reciprocal families are square
summable. Cauchy–Schwarz therefore controls the complete paired finite part
and the error after two incomplete-Mellin recursions. The resonant fibre
contributes `mρE(y,0)`, whose exponential-integral asymptotic supplies the
logarithm and Euler constant.

Comparing any two positive damping scales cancels the finite-part constant:

    Gρ(y)−Gρ(cy)+Bρ(y)−Bρ(cy) → −mρ log(c)/2,       c>0.

`GaussianRenormalizationAtZeros.lean` proves these laws with the full infinite
prime and zero sums. The counterterms depend on the divisor; this identity
does not provide an independent prime-only multiplicity test or a new zero
height. Same-depth replication remains a separate obligation.

### Prime-only resonance at a rightmost zero

Rightmostness removes the counterterms from the limiting observable. If `ρ`
is any actual rightmost zero, then

    Gρ(e^(−u))/u → −mρ/2,       u→∞.

This retains the full prime current and continuum. There is no assumption
of a finite top, a uniform gap below it, or simplicity. Every nonresonant
Gamma mode has magnitude at most its magnitude at damping `1`; the sum of
these amplitudes is finite. Thus the entire nonresonant field is bounded
and vanishes after division by `u`. The logarithmic finite-part identity
leaves exactly the multiplicity term.

Under `¬AAL`, the actual finite-top theorem supplies such a zero with
`Re ρ>½`. `ThePrimeCurrentReadsTopMultiplicity.lean` proves this specialization
and the general rightmost-zero limit. This reads an existing top through a
prime-only observable. It neither contradicts that top nor produces a new
height; the arithmetic replication mechanism is still missing.

### Uniform archimedean damping and its unique normalization

Let `A_y,c(s)` be the actual Gaussian Mellin–Barnes transform of
`A(s)=1/s+Γℝ′/Γℝ(s)`, with `y,c>0`. Throughout `Re s>0`,

    |A_y,c(s)−e^(−y)A(s)| ≤ ye^(−y)/Re s.

The error therefore tends to zero uniformly on every whole half-plane
`Re s≥σ₀>0`. Height can escape arbitrarily as damping vanishes. The
unrenormalized estimate contains `y|s−2|` and cannot give this conclusion.

One incomplete-Mellin recursion in the full trivial-zero expansion gives

    A_y,c(s)−e^(−y)A(s)=Σₙ 2y E(y,−s−2n)/(s+2n+2).

The endpoint bound `|E(y,a)|≤e^(−y)/(−Re a)` for `Re a<0` gives a telescoping
majorant whose sum is `ye^(−y)/Re s`. For fixed `y,c,σ>0`, the error
`A_y,c(σ+it)−zA(σ+it)` is bounded for all real `t` exactly when `z=e^(−y)`:
every other scalar retains a nonzero multiple of the logarithmically growing
archimedean current.

`TheArchimedeanDampingErrorIsUniform.lean` proves the exact series, uniform
bound, uniform convergence and scalar classification. These laws remove
height dependence from the archimedean error.

### The complete finite part at escaping heights

The full Gamma-subtracted current admits joint control of damping and height.
For complex `s`, retain every zero with multiplicity in

    B_s(y)=Σρ ½Γ((ρ−s)/2)y^(−(ρ−s)/2),
    R_s(y)=G_s(y)+B_s(y)−e^(−y)(A(s)−ξ′/ξ(s)).

Fix `σ₀,δ>0`. Throughout `σ₀≤Re s≤1`, `Im s≥4`, at distance at least `δ`
from every actual zero, there is a constant depending only on `σ₀,δ` such that

    |R_s(y)| ≤ C y(1+y)(1+log Im s),       y>0.

The complete Gamma field is absolutely admitted. Two Mellin recursions bound
each renormalized germ by `6y(1+y)|ρ−s|⁻²`. Local zero counts control the
nearby copies; the infinite far-field second moment bounds the remainder.
Together they give `Σρ|ρ−s|⁻²=O_δ(1+log Im s)`. The archimedean estimate
then closes the exact prime-current bound.

Consequently `R_s(y)/(1+log Im s)→0` uniformly on that whole domain.
Absolute error tends to zero along every admitted path with `y→0⁺` and
`y(1+log Im s)→0`, even when height escapes. Under `¬AAL`, the actual finite
exceptional layer supplies a whole high strip `σ≤Re s≤1`, `Im s≥H`, with
`1/2<σ<1`, on which both the estimate and uniform limit hold; an actual zero
still lies strictly right of `σ`. No separate zero-free or recurrence input
is assumed in this specialization.

`TheFullGaussianCurrentAtEscapingHeights.lean` proves these statements with
the complete prime and zero fields. The Gamma counterterm remains in the
observable. Its removal and same-depth replication require further arithmetic
control.

### Conductor-normalized height reflection

The reflected high profile carries a conductor power. With
`χ(s)=Γℝ(1−s)/Γℝ(s)` and `R(s)=1−conj(s)`, put

    N_t(s)=exp((s−½)log(t/(2π)))/χ(½+it),
    F_t(s)=N_t(s)ζ(s+it),   J_t(s)=conj(ζ(R(s)+it)).

The exact functional equation gives
`F_t−J_t=(N_t χ(s+it)−1)J_t`. The normalized Gamma ratio differs from one
by `O_D(t⁻¹)` on `0<Re s<1`, `|s−½|≤D`, for every radius `D≥0`.
Convexity bounds the entire reflected ζ-profile there by `O(t^(3/4))`, so

    sup_{0<Re s<1, |s−½|≤D} |F_t(s)−J_t(s)| ≤ C_D t^(−1/4) → 0.

`TheNormalizedHeightReflection.lean` proves this uniform law for actual ζ,
without a return or boundedness premise. No separation from the strip's
vertical edges is required. The normalization retains the archimedean drift;
the law still relates profiles at the same height and does not produce
same-depth copies at a new height.

There is also an unconditional restriction on ordinary translates. For any
`τ_j→+∞`, let `U` be a connected open set in the upper half-plane meeting
`Re s>1`. If `ζ(s+iτ_j)` is locally bounded on `U`, then `U⊆{Re s>½}`.
No phase alignment or prescribed limit is assumed. A crossing of the critical
line would contain a reflected disc; boundedness on its left half and Gamma
decay force convergence to zero on its right half. Vitali and analytic
uniqueness propagate the zero limit through `U`, contradicting the uniform
positive Euler lower bound on any fixed line `Re s>1`.

`TheWholeQuadrantCannotSupportReturns.lean` proves this restriction and excludes
whole-quadrant local boundedness for every escaping sequence. It strengthens the
corpus's corresponding phase-return restriction by removing phase alignment.
The whole-quadrant receiver in `ArithmeticAuxiliaryDynamics` therefore has an
impossible premise. Recurrence on smaller domains strictly right of the line
remains a separate arithmetic question.

## Calibration and traps

Every proposed law must use the Euler product and FE jointly at two scales. It must
distinguish ζ from the heat family, `cosh` models, positive Beurling one-offs and Wolff
towers, and recover the established local-squares purity law at finite rank.

An exact zero cannot be replaced by a near-zero event. A return of finitely many prime
phases does not control a continued Euler tail. A positive pairing does not locate zeros
unless the arithmetic input preventing fake configurations is proved. Removing a finite
layer must preserve and verify all Euler, reflection and analytic conditions used.

The source calibration is stronger than positivity alone. The existing
`RHTower/ThetaSeedTransferQuartet.lean` construction can relocate a hypothetical
off-line quartet while preserving positive source and seed, exact outward Euler
resolvent covariance, smooth reflection, mass, leading theta tail and the complete
real-zero divisor. `ThetaTwoEndedTailLaw.lean` and `ThetaTailGermExpansion.lean`
identify the resulting rational deformation from its full tail expansion.
Consequently these properties, even together, do not select the literal theta
source. The exact Gaussian seed equation is an additional constraint:
`ThetaGaussianBaseCommutator.lean` proves that one nonzero Green division violates
it. `ThetaZeroDivisionRateTomography.lean` and
`ThetaZeroDivisionRateDerivativeWitness.lean` detect finite rational surgeries
through the loss of complete monotonicity after sufficiently deep prime deletion.
These are tests of deformed sources. They do not imply that an exceptional zero
of the original source violates its own Gaussian identity.

## Position and contribution criteria

`ExactEventTheory` supplies exact-tail and defect-boundary mechanisms.
`ZeroConfigurationGeometry` supplies AAL, the strict linear dial and the rigid top layer.
`ArithmeticPositiveDuality` supplies Hamburger rigidity, positive measures and one-off
calibrations. `TailArithmeticOfThePrimeOrbit` supplies head–tail identities and returns.
`InfiniteRankWeilTheory`, `ArithmeticCastelnuovoSeveri` and `SurfaceOfSpecZ` supply the
tower and geometric receivers against which transport must be tested.

This programme owns new Euler–FE coupling and replication results in this directory;
its umbrella is `../EulerFETransportTheory.lean`. Shared results retain their original
home. A contribution must remove an actual infinite-problem obstruction or construct
a required operator, identity, classification or counterexample. Finite computations,
renamed equivalences and wrappers around unproved arithmetic inputs do not qualify.

Completion requires the stated tools and questions to be resolved with dependency-closed
Lean proofs, including the replication/AAL branch. A retired route must yield and audit
its strongest positive survivor. The foundational description alone does not develop
the missing mathematics.
