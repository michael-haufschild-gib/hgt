# Finite irregular remainder: intrinsic rigidity theorem

Status: paper argument and final rigidity formalization complete. All twelve source leaves passed direct Lean audits. All thirty-four declarations in this cycle's three leaves passed the scratch axiom/name audit; only `propext`, `Classical.choice` and `Quot.sound`. Not a solution of WP04. Scientific novelty remains provisional.

## Exact statement

Let `hW : WeilPositiveFull lam` and let μ be its canonical boundary measure. Define the integer atomic submeasure

\[
  \kappa=\sum_{r:\,\mu\{r\}\ge1}\lfloor\mu\{r\}\rfloor\,\delta_r,
  \qquad \nu=\mu-\kappa.
\]

Singleton masses are finite. On each compact interval, only finitely many summands in κ are nonzero, since each consumes at least one unit of μ. Thus κ is a locally finite integer counting measure, κ≤μ, and ν is a positive measure. Both are even because μ is even.

**Theorem F:** for every `hW`, either `lam(n)=Λ(n)` for every `n≥2` and RH holds, or `ν(ℝ)=∞`.

Equivalently: an arbitrary finite positive remainder, after removing the integer parts of the actual canonical atoms, forces λ=Λ and RH. The remainder may have singular-continuous mass or accumulating fractional atoms. No ordinate gap or boundary-continuity premise is supplied. `quantization_rigidity_or_infinite_residual` expresses the intrinsic dichotomy with `hW` as its sole substantive input.

This does not establish that ν is finite for arbitrary `hW`. That source obligation remains open. The original half-integer counting goal remains unchanged.

## Exact difference from the inspected frontier

`WeilFractionalMassSummableRigidity` treats summable real atomic masses whose ordinates tend to infinity. `WeilMixedSpectrumRigidity` allows a diffuse part but requires its Herglotz function to be continuous on the closed critical half-plane. `WeilFractionalTwoSidedRigidity` handles near-integer atoms with subpower total variation, again with ordinates escaping to infinity. These results cannot be applied directly to an arbitrary finite singular remainder.

Booker's distributional L-data assume discrete spectral support and finitely many noninteger masses (Definition 1.3(A3)). His degree-one proof uses the reflected contour identity (3.2) before periodicity forces integer conductor. The proposed proof below instead retains a bounded-variation boundary phase and proves its radial contribution vanishes. No claim that all of Booker's other hypotheses follow from `hW` is made.

Verdict: **SURVIVES PRELIMINARY ATTACK**. No identical result was located in the searches recorded in EVIDENCE.md. This is not an exhaustive novelty certification.

## Paper argument, with normalizations

Write `z=s−1/2`. Let Φ be the actual Weil continuation, and let G be its nonvanishing holomorphic exponential primitive on `Re s>1/2`, normalized by

\[
 G(2)=\operatorname{bigG}_\lambda(2)>0,\qquad G'=\Phi G.
\]

Existence follows from a holomorphic primitive on the convex half-plane. The source identity on `Re s>1` gives

\[
 G(s)=s(s-1)\Gamma_{\mathbb R}(s)F(s),\quad
 F(s)=\exp\!\left(\sum_{n\ge2}\frac{\lambda(n)}{\log n}n^{-s}\right)
     =\sum_{n\ge1}a(n)n^{-s},\quad a(1)=1.
\]

All these Dirichlet series converge absolutely for `Re s>1` by the existing full-cone convergence theorem and Dirichlet-exponential construction. Real coefficients give conjugation symmetry. In particular G is positive on the real interval `(1/2,∞)`: it is real, nonzero and positive at 2. Set `β=G(1)/2>0`.

### 1. Radial trace without boundary continuity

Since `Re Φ≥0`, `|G(σ+it)|` increases with σ. It therefore has a finite limit as `σ↓1/2`, bounded by `|G(3/2+it)|`. Its phase, anchored by positivity of `G(σ)`, is

\[
 \theta_\eta(t)=\int_0^t\Re\Phi(1/2+\eta+iu)\,du.
\]

The canonical Poisson formula expresses this as an integral of an arctangent difference against μ. The weighted domination already proved in `WeilWorkQuantizationKernel` applies; at an endpoint the kernel limit is π/2 rather than π. Thus the phase has a finite limit for every fixed t. For `t>0`,

\[
 \theta_0(t)=\pi\mu((0,t))+\tfrac\pi2\mu\{0\}+\tfrac\pi2\mu\{t\}.
\]

The corresponding formula for negative t is obtained by reversing the interval. Multiplying the limiting modulus and limiting unit phase gives a radial trace `G₀(t)` at every t, including points where the modulus tends to zero. As a pointwise limit of continuous functions it is measurable. No assertion of continuity of `G₀` is used.

Away from the countable set of atoms, symmetry and the interval-phase identity give, for y>0,

\[
 G_0(y)=\exp\bigl(i\pi\mu\{0\}+2\pi i\mu((0,y))\bigr)G_0(-y).
\]

This equality remains valid when either side is zero; division by a boundary value is unnecessary.

Uniform vertical Gamma-ratio estimates and horizontal monotonicity give

\[
 |F(x+iy)|\le C(1+|y|)^{1/2},
 \quad 1/2<x\le3/2,\quad |y|\ge2.
\]

Indeed `|G(x+iy)|≤|G(3/2+iy)|`, the right-edge F is bounded by absolute Dirichlet convergence, and `|Γ_R(3/2+iy)/Γ_R(x+iy)|≤C(1+|y|)^{1/2}`. The polynomial factors `s(s−1)` have bounded ratios here. Near the critical line and bounded y their denominators stay away from zero. These estimates dominate the radial traces and every fixed-parameter boundary passage below.

### 2. Two boundary Mellin identities

For `s_t=1/2+2it`, put

\[
 f_0(t)=\frac{G_0(2t)}{s_t(s_t-1)\Gamma_R(s_t)},\qquad
 f_*(t)=\frac{G_0(-2t)}{s_t(s_t-1)\Gamma_R(s_t)}.
\]

For `Re τ>0`, use the principal logarithm and define

\[
 k_\tau(s)=\frac{\tau^{s-1}}{\sin(\pi s/2)},\qquad
 J_h(\tau)=\frac1{2\pi}\int_{\mathbb R}h(t)k_\tau(s_t)\,dt.
\]

This is exactly the corpus `pairKernel`/`defectLaplace` normalization: simplify `offKernel` using `arg(τ²)=2arg τ`, valid on the right half-plane. For fixed τ these integrals converge absolutely, with exponential decay in both directions.

The required identities are

\[
 J_{f_0}(\tau)=\sum_{n\ge1}\frac{a(n)\tau}{\pi(n^2+\tau^2)}-\beta,
 \qquad
 J_{f_*}(\tau)=S(\tau)-\frac\beta{\pi\tau},\qquad
 S(\tau)=\sum_{n\ge1}a(n)e^{-2\pi n\tau}.
\]

For the first identity, pass from the radial boundary to a line `Re s=1/2+δ`, then move to `Re s=3/2`. The only pole crossed is s=1, with residue `2β`; the prefactor is `1/(4πi)`, giving `−β` on the left line. Termwise Mellin inversion on the right line is

\[
 \frac1{4\pi i}\int_{(c)}n^{-s}\frac{\tau^{s-1}}{\sin(\pi s/2)}ds
   =\frac{\tau}{\pi(n^2+\tau^2)},\quad 0<c<2.
\]

For the second identity, reflect the critical-line parameter and use the Gamma reflection and duplication identities in the form

\[
 \frac{\Gamma_R(z)}{\Gamma_R(1-z)\cos(\pi z/2)}
    =\frac{2\Gamma(z)}{(2\pi)^z}.
\]

The resulting integral is `1/(2πi) ∫ F(z)Γ(z)(2πτ)^(−z) dz`. Moving it to `Re z=3/2` crosses the pole with residue `β/(πτ)`; termwise inverse Mellin transformation gives S. Work on interior lines first, then use dominated convergence for the radial boundary. For fixed τ the exponential kernel decay absorbs the uniform polynomial bounds. This argument does not require continuous boundary values or an analytic continuation of G to the left half-plane.

The Mellin identities may first be established for positive real τ, with their extension to `Re τ>0` justified by holomorphy and locally uniform integral domination.

### 3. Arithmetic radial residues

At `τ=ε+im`, fixed integer `m≥1`, absolute convergence of `Σ|a(n)|/n²` isolates the n=m term in the rational sum, giving

\[
 \varepsilon J_{f_0}(\varepsilon+im)\longrightarrow\frac{a(m)}{2\pi}.
\]

For `n>2m`, the remaining denominators have a uniform multiple-of-`n²` lower bound near ε=0; the finitely many other nonresonant terms vanish after multiplication by ε.

For τ=ε>0 the kernel is bounded by `C ε^(−1/2)e^(−π|t|)`. Hence `ε J_{f_*}(ε)→0` and `ε S(ε)→β/π`. Integer periodicity `S(ε+im)=S(ε)` then gives

\[
 \varepsilon J_{f_*}(\varepsilon+im)\longrightarrow\frac\beta\pi.
\]

The upper half-line contribution to either radial integral tends to zero: there the kernel retains uniform exponential decay as ε tends to zero. Thus both displayed limits are carried by the lower half-line.

### 4. Uniform truncated cancellation, retaining the moving tail

For every fixed m≥1 there is `B_m` such that

\[
 \left|\varepsilon\int_a^0 f_0(t)k_{\varepsilon+im}(s_t)dt\right|\le B_m
 \quad(a\le0,\ 0<\varepsilon\le1).
\]

Use a rectangle with vertical sides `1/2+δ` and `3/2`, imaginary heights `2a` and `−2`, initially a≤−1. It crosses no pole. On the right side F is bounded. On the strip below height −2, the kernel is bounded by `C_m exp(−c_m ε|y|)` and F by `C sqrt(1+|y|)`. The right vertical integral, after multiplication by ε, is bounded by a constant. Each horizontal edge contributes at most `C_m ε sqrt(1+|y|) exp(−c_m ε|y|)`, uniformly bounded in y and ε. Pass δ↓0 using the local radial trace and domination; the estimates are independent of δ. The remaining interval `[−1,0]` is uniformly bounded. For each fixed a the same truncated expression tends to zero, since the integrand on `[a,0]` is uniformly bounded near ε=0.

These are the estimates of `HamburgerTruncatedRadialIntegral`, with an interior-line limit replacing the currently required continuous critical edge. The original theorem cannot be applied unchanged.

### 5. Finite remainder pays the phase defect

Assume ν is finite. Put `M=ν((0,∞))`. For t<0 set `h(t)=ν([−2t,∞))`; then h is nonnegative, bounded by M, nondecreasing, and tends to zero as t→−∞. Integer counts in κ disappear after exponentiation. At all non-atomic endpoints, hence almost everywhere,

\[
 f_*(t)=c\,e^{-2\pi i h(t)}f_0(t),\qquad
 c=e^{i\pi\mu\{0\}+2\pi i M}\ne0.
\]

Write `e^(−2πih(t))−1=∫₀ᴹ (−2πi)e^(−2πix) 1[x≤h(t)]dx`. For every x>0 the superlevel set on the negative half-line agrees almost everywhere with a finite interval ending at 0. Fubini is valid for each ε by exponential kernel decay. The uniform truncated bound in step 4 is an integrable constant majorant over `[0,M]`, and the fixed-interval limit is zero. Dominated convergence therefore yields

\[
 \varepsilon J_{(e^{-2\pi ih}-1)f_0,\ t<0}(\varepsilon+im)\longrightarrow0.
\]

Combining the two arithmetic residues gives `β/π=c a(m)/(2π)` for every m≥1. Since a(1)=1, all a(m)=1. Thus F=ζ on `Re s>1`; logarithmic differentiation and Dirichlet coefficient uniqueness give λ(n)=Λ(n) for n≥2. The existing full-cone Weil criterion then gives RH and the canonical integer zero measure. This proves the stated dichotomy if all analytic passages above survive the formal audit.

## Remaining validation work

1. Audit the radial-boundary contour argument, including the principal-power identity, residue signs and factors of two. Do not assume existing closed-boundary theorems apply unchanged.
2. Verify exact source symbols and mathlib names in this toolchain before Lean use. Reuse generic kernels and residue lemmas where their full hypotheses match.
3. Formalize only in `WeilWorkQuantization*.lean`, with no boundary-continuity or finite-remainder premise in the final intrinsic dichotomy beyond its explicit alternative. No added axioms, sorry, heartbeat increases, full builds or umbrella builds.
4. Run direct foreground leaf audits and scratch axiom audit; wire finished leaves. The full WP04 goal still needs a source argument excluding the infinite-remainder alternative.

## Formalization dependency map

The endpoint phase leaf is now compiled. Its canonical theorem retains both endpoint atoms and has no null-endpoint premise. The radial-trace construction is compiled in `WeilWorkQuantizationRadialBoundary.lean`: it uses a primitive normalized at 2, its real-axis phase, monotonicity of its exponential modulus, and the endpoint limit. It proves measurability by a sequence of interior vertical lines and proves conjugation symmetry. Direct leaf and scratch axiom/name audits passed; only the three standard axioms appear.

Status of dependencies, in order:

1. **COMPILED:** normalize the exponential primitive by `bigG lam 2` and identify it with the actual right-half-plane arithmetic completion in `WeilWorkQuantizationRadialGrowth`.
2. **COMPILED:** uniform interior growth, measurable locally bounded quotient trace, local integrability, and compact contour convergence. The horizontal comparison comes directly from the primitive's monotonicity.
3. **COMPILED:** `WeilWorkQuantizationRadialContour` extends the signed truncated estimate to the actual radial trace. Its final source theorem has no boundary-continuity or atomicity premise. The bound is uniform in the truncation height and radial parameter; its intermediate rectangle bound is also uniform in the left edge. Fixed-window rescaled integrals tend to zero.
4. **COMPILED:** `WeilWorkQuantizationRadialMellin` identifies the normalized completion and almost-everywhere trace with the now-compiled `WeilWorkSettledPhaseMellinTrace`, reuses its weighted shift, and proves the actual coefficient-theta identity. `WeilWorkQuantizationRadialTheta` proves the reflected theta relation and both Hamburger/Laplace identities. No closed-edge continuity or functional equation is supplied.
5. **COMPILED:** `WeilWorkQuantizationRadialLayerCake` proves the canonical trace's rescaled monotone-twist integral vanishes. Its superlevel intervals need no density, atom enumeration, or ordinate gap.
6. **COMPILED:** `WeilWorkQuantizationIntegerFloor` constructs the canonical integer atomic submeasure and pays local subtraction. `WeilWorkQuantizationResidualPhase` derives the actual almost-everywhere phase, monotonicity, finite bound and tail limit, then applies signed layer cake without dividing by boundary values.
7. **COMPILED:** `WeilWorkQuantizationFiniteRemainderRigidity` proves the reflection error has zero radial residues at every nonnegative integer height. Both source Hamburger identities, arithmetic periodicity and the existing coefficient receiver yield λ=Λ and RH. Its final intrinsic dichotomy supplies no finite-remainder premise.

Neither the primitive's radial trace nor its measurability supplies an analytic continuation across the line. The full WP04 target still requires exclusion of infinite irregular remainder.

### Next source lemma: radial inverse Mellin, with its boundary passage paid

Use the actual coefficients `a = dirichletExp (lamLog lam)`, the checked normalized G, `β=G(1)/2`, and `E=PhaseLockRigidity.bigEG G`. For `s_y=1/2+iy` define

`E₀(y)=G₀(y)/(s_y(s_y−1))−β Γℝ(s_y−1)`.

The exact next identity is, for every x>0,

`θ_a(x)−β x^(−1/2)e^(−πx) = (1/(2π)) ∫ x^(−(1/4+it)) E₀(2t) dt`.

Dependency-closed analytic argument for this passage:

1. `LSeries_dirichletExp` supplies absolute convergence on every line Re>1 and identifies its sum with `zetaOf lam`. The checked normalization identifies G there. The existing removable quotient `bigEG` is holomorphic throughout Re>1/2, including s=1, and gives the required right-line Mellin identity.
2. Horizontal monotonicity bounds `|G(σ+iy)|` by `|G(2+iy)|` for `1/2<σ≤2`. The existing right-line Gamma bound gives `C (|y|+4)^N exp(−π|y|/4)`. For |y|≥4, the existing polynomial-times-exponential and shifted-Gamma estimates give `|E(s)|≤C'/(1+y²)`, uniformly in `1/2<Re s≤3/2`.
3. Supply the bounded-height part without edge continuity. On `3/4≤Re s≤3/2`, |Im s|≤4, E is continuous on a compact subset of its open domain. On `1/2≤Re s≤3/4`, |Im s|≤4, the polynomial denominator `s(s−1)` is nonzero. The continuous majorant
   `( |G(2+i Im s)| + |β| |mFactor(s)| ) / |s(s−1)|`
   dominates E on the open part of that rectangle. This gives one uniform quadratic-decay constant on the whole open strip.
4. Apply the already proved `HTGeometry.inverse_mellin_shift` at `σ=1/4+η/2`, with `0<η≤1/4`. Its closed strip lies strictly inside the domain; all its continuity and differentiability premises are now paid. The right-line data is unchanged.
5. At each fixed t, E(1/2+η+2it) tends to E₀(2t). This follows from the checked everywhere radial trace of G and the nonzero critical-line polynomial denominator. Continuity of `mFactor` on Re>0 also verifies the shifted-Gamma term at these points without assuming regularity of G on the edge.
6. For η in (0,1/4), the Mellin weight has modulus `x^(−1/4−η/2)`, bounded by `max(x^(−1/4),x^(−1/2))`. The uniform decay gives an integrable constant multiple of `(1+4t²)⁻¹`. Dominated convergence passes the whole-line integral to E₀. This proves the identity above.

This passage is now compiled in `WeilWorkQuantizationRadialMellin.lean`, reusing the checked source weighted shift after identification of both completions and traces. It uses no reflection, finite-remainder hypothesis, or continuous critical-edge extension. The subsequent even theta relation is compiled in `WeilWorkQuantizationRadialTheta.lean` by algebra on these radial integrals.

### Algebra after radial Mellin inversion

For formal integration, first establish the untwisted source identity

`θ_a(x)=β x^(−1/2)+defectKernel(f₀)(x)`.

Combine the radial inverse-Mellin identity with the already available inverse Mellin transform of `x^(−1/2)(exp(−πx)−1)`. Pointwise,

`E₀(2t)+β Γℝ(s_t−1)=Γℝ(s_t) f₀(t)`.

Both summands are integrable after the real positive Mellin weight: the remainder trace has global L1 control; the shifted Gamma term has the existing vertical-line estimate. Thus splitting the integral is justified, including the polar constant β.

The reflected identity can then be obtained directly from this untwisted formula, without repeating the closed-edge even-theta theorem. Define f* as in step 2. Since `(1−s)(−s)=s(s−1)`,

`Γℝ(s_t) f*(t)=Γℝ(s_(−t)) f₀(−t)`.

Changing t to −t and combining the positive-real Mellin powers gives

`x^(−1/2) defectKernel(f₀)(x⁻¹)=defectKernel(f*)(x)`.

Subtract the two theta formulas. The result is

`θ_a(x)−x^(−1/2)θ_a(x⁻¹)=β(x^(−1/2)−1)+defectKernel(f₀−f*)(x)`.

All trace normalizations remain the actual source normalizations. Conjugation symmetry gives `|f*(t)|=|f₀(t)|`; the checked strip growth and compact trace bound therefore give a common polynomial bound. The existing defect-kernel Laplace theorem then applies to both source identities. This supplies the two arithmetic transforms in step 2 without a functional-equation assumption.

### Radial layer cake with a measurable canonical trace

The monotone-twist passage also needs no continuous extension. Let h be nonnegative, monotone, bounded by H, and tend to zero at minus infinity. Write

`exp(−2πi h(t))−1 = ∫_(0,H] 1_(x≤h(t)) (−2πi exp(−2πix)) dx`.

For each x>0, the superlevel set on t<0 agrees up to one endpoint with a finite interval [a,0). Multiply by the actual radial integrand f₀(t)k(2t,ε+im). Its global polynomial bound gives absolute integrability for every ε>0. The product integrand is measurable; its norm is bounded by `2π |f₀(t)k(2t,ε+im)|` on the finite x-interval, so Fubini applies. The canonical signed truncation bound gives the uniform layer bound 2πB. Each fixed layer tends to zero by the checked fixed-window theorem after y=2t. Dominated convergence in x proves vanishing of the rescaled twisted integral for every m≥1. This replaces exactly the old proof's closed-edge continuity input by verified source measurability, growth, and signed contour estimates.

The h assumptions in this analytic helper are not an accepted source premise. The finite-remainder argument must construct h from the actual positive residual measure, prove all four properties, and only then apply this helper.

Use the global definition `h(t)=ν.real(Ici(−2t))` on all real t, with the global bound `H=ν.real(univ)`. The sharper M bound above holds only on t<0 and remains the phase constant `M=ν.real(Ioi 0)`. The proved helper quantifies its monotonicity and bounds over all t, so H is the correct instantiation; layers above M contribute zero on the negative half-line.

For the next measure step, the toolchain's `Measure.sub_add_cancel_of_le` requires a finite subtrahend. The integer atomic floor need not have finite total mass. First restrict both measures to a bounded measurable interval, use `restrict_sub_eq_restrict_sub_restrict`, and apply finite cancellation there. These local identities give exactly the interval-phase decomposition needed above; exhaustion can then identify the whole measures. Do not assume a nonexistent sigma-finite subtraction API.

### Exact construction of the integer floor

Define w(r)=floor(μ.real{r}) and κ=Σ_r w(r)δ_r, with natural-valued w. For a measurable set A, each term w(r)δ_r(A) is at most (μ restricted to A){r}. Finite sums of the latter equal the mass of a finite subset under μ restricted to A, hence are at most μ(A). Taking the supremum over finite index sets proves κ≤μ, without assuming that μ is atomic.

If μ(A)<∞, then Σ_r 1_A(r)w(r)<∞. Every nonzero summand is at least one, so only finitely many are nonzero. The sum is therefore a natural number. This proves integer counting for κ on all finite-mass measurable sets, in particular every bounded interval.

Let ν=μ−κ. On any measurable A with μ(A)<∞, both restrictions are finite and κ restricted to A≤μ restricted to A. Restriction commutes with measure subtraction, so finite cancellation yields ν(A)+κ(A)=μ(A). In real masses this gives μ.real(A)=ν.real(A)+κ.real(A). At A={r}, κ{r}=w(r) and ν.real{r}=μ.real{r}−floor(μ.real{r}), hence 0≤ν.real{r}<1. This is a source-derived decomposition, not an assumed counting or atomicity property of μ. The interval identity is sufficient for the subsequent phase argument.

### Zero-safe residual phase identification

At y>0 with μ{y}=0, endpoint inversion gives `Im P(1/2+η+iy) → πμ((0,y))+πμ{0}/2`. For every complex z,

`exp(z)=exp(2i Im z) conjugate(exp(z))`.

Pass to the already-constructed radial trace in this identity, then use conjugation symmetry and the real normalization at 2. This proves the phase relation for G₀ without dividing by G₀, so boundary zeros cause no exception. Under finite ν, the disjoint partition `(0,∞)=(0,y) ∪ [y,∞)` gives `ν((0,y))=M−ν([y,∞))`. Local subtraction gives `μ((0,y))=ν((0,y))+n` for a natural n. The factor exp(2πin) is one. Hence the lower-half-line quotient satisfies the phase relation in step 5.

The exceptional y form a countable set because μ is s-finite. Pulling this set back by t↦−2t preserves countability, so the lower-half-line identity is Lebesgue-almost-everywhere. For finite ν, continuity from above applied to the increasing family t↦[−2t,∞) as t→−∞ gives h(t)→0, since its intersection is empty. Monotonicity, nonnegativity and the global bound by ν(ℝ) follow directly from measure monotonicity. Thus every input to the checked layer-cake helper is derived from finite ν.

### Final assembly through the existing periodic-residue receiver

Put e=f*−c f₀. This is measurable and polynomially bounded, since |c|=1. For positive integer m, its lower-half-line radial residue vanishes by the paid phase identity and layer cake. Its upper-half-line residue vanishes by the generic one-sided exponential kernel estimate. The single point at zero has zero Lebesgue mass; alternatively the existing compact-window Abel estimate pays that middle term. At m=0, the generic polynomial-bound estimate gives εJ_e(ε)→0 directly. Hence εJ_e(ε+im)→0 for every natural m.

The two checked Hamburger identities and linearity of J give

`H(τ)=c⁻¹S(τ)−c⁻¹β/(πτ)+β+K(τ)`, where `K(τ)=−c⁻¹J_e(τ)`.

Every term in S is i-periodic because its frequency n is an integer. Subtraction at τ+i and τ therefore gives

`H(τ+i)−H(τ)=d/(τ+i)−d/τ+K(τ+i)−K(τ)`, with `d=−c⁻¹β/π`.

The radial residue of K at each nonnegative integer height is zero by the preceding paragraph. Taking differences gives the same property for K(τ+i)−K(τ). The corpus periodic-residue receiver upgrades these radial limits for this exact identity and concludes `a(n+1)=−2πd=2c⁻¹β` for every n. Its required weighted coefficient summability follows from absolute Dirichlet convergence at exponent two. At n=0, a(1)=1 fixes the common value to one. The existing coefficient-one receiver needs only the already-proved source continuation, derivative equation and normalization, so it yields λ=Λ and RH without any closed-edge premise. Finally split on ν(ℝ)=∞ to express F with hW as its sole substantive input.
