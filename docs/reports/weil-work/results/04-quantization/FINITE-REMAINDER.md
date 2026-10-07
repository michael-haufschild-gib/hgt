# Finite irregular remainder: proposed intrinsic rigidity theorem

Status: paper argument assembled; independent proof audit and Lean formalization pending. Not a solution of WP04. No theorem below is claimed Lean-verified. Scientific novelty remains provisional.

## Exact statement

Let `hW : WeilPositiveFull lam` and let μ be its canonical boundary measure. Define the integer atomic submeasure

\[
  \kappa=\sum_{r:\,\mu\{r\}\ge1}\lfloor\mu\{r\}\rfloor\,\delta_r,
  \qquad \nu=\mu-\kappa.
\]

Singleton masses are finite. On each compact interval, only finitely many summands in κ are nonzero, since each consumes at least one unit of μ. Thus κ is a locally finite integer counting measure, κ≤μ, and ν is a positive measure. Both are even because μ is even.

**Proposed theorem F:** for every `hW`, either `lam(n)=Λ(n)` for every `n≥2`, or `ν(ℝ)=∞`.

Equivalently: an arbitrary finite positive remainder, after removing the integer parts of the actual canonical atoms, forces λ=Λ and RH. The remainder may have singular-continuous mass or accumulating fractional atoms. No ordinate gap or boundary-continuity premise is supplied. The eventual main declaration should express the intrinsic dichotomy with `hW` as its sole substantive input.

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

Next obligations, in order:

1. Normalize the exponential primitive by `bigG lam 2`; use `PhaseLockRigidity.G_eq_bigG` on the right half-plane. This theorem does not require closed-edge continuity.
2. Prove uniform interior growth and inherited trace bounds. `TruncatedRadial.exists_norm_prodF_le` currently assumes closed-edge continuity; its interior horizontal comparison must be supplied directly from the primitive's monotonicity.
3. Extend the signed truncated rectangle estimate to measurable radial traces by moving the left edge strictly inside, then taking its radial limit. Preserve bounds uniform in the left edge, truncation height, and radial parameter.
4. Extend the inverse-Mellin identity to radial traces. `HTGeometry.critical_line_inverse_mellin` and `critical_line_even_theta_relation_defect` currently assume continuity on the closed strip. The generic vertical contour-shift lemmas can still be used on strictly interior strips. The existing Gaussian-theta/Laplace algebra may then be reused instead of reproving sine-kernel inversion from scratch.
5. Use finite positive remainder only in the signed layer-cake argument. Its superlevel intervals need no density, atom enumeration, or ordinate gap. Build the canonical integer atomic submeasure and conclude the intrinsic dichotomy.

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

This passage is still awaiting Lean formalization. It uses no reflection, finite-remainder hypothesis, or continuous critical-edge extension. The subsequent even theta relation is algebra on these radial integrals; it must also be instantiated with this trace rather than the existing closed-edge receiver unchanged.
