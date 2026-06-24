# Formulas

Every formula appearing in the `docs/consolidated/revision01` documents, collected here, with
notation **aligned to a single canonical symbol per object** and with relationships that the
documents stated only in prose **rendered as explicit formulas** (marked `[from prose]`).
Each distinct formula is listed once; below each is a bullet list defining its variables/parameters.

---

## Canonical notation

**Core variables**
- `s` — complex variable, `s = σ + it`
- `σ` — real part of `s`
- `t` — imaginary part of `s`
- `ζ` — Riemann zeta function
- `ξ` — completed (Riemann xi) function, `ξ(s) = ½·s(s−1)·π^{−s/2}·Γ(s/2)·ζ(s)`
- `Λ` — completed zeta, `Λ = Γ∞·ζ`
- `Γ` — Euler gamma function; `ψ = Γ'/Γ` — digamma function
- `Γ_ℝ(s) = π^{−s/2}Γ(s/2)` — real gamma factor; `Γ∞` — archimedean factor (`= Γ_ℝ`)
- `ρ` — nontrivial zero; `β = Re ρ`; `γ = Im ρ` (ordinate); `m_ρ` — multiplicity of `ρ`
- `p` — a prime; `n` — a positive integer
- `a = |½ − β|` — distance of an off-line zero from the seam; `τ = t − γ` — height offset
- `κ₋` — faithful (Krein–Langer / Sylvester) negative index = number of off-line zero-pairs

**Aligned compound symbols** (the more informative / proof-standard form was chosen)
- `∂_s log Γ∞` — archimedean term (the documents' placeholder `A`; **expanded**, per "Δ becomes Γ∞")
- `ζ'/ζ` — prime term (the documents' placeholder `P`; **expanded**)
- `H = ∂_s log Λ = ∂_s log Γ∞ + ζ'/ζ` — the weld
- `ω = d log ξ` — transport one-form
- `Δ` — phase-carrier defect
- `ι : s ↦ 1−s` — functional-equation involution
- `σ_p` — prime shift operator on lane `p`; `M_p` — translation-by-`log p`; `∂_s` — dilation generator
- `e_m` — boundary mode (`m` a multi-index `(m_p)_p`); `ℓ = (log p)_p`; `θ_p` — number operator on lane `p`
- `Π(S)` — affine passport
- `Ξ(w) := ξ(½ + w)` (canonical single definition); `M_Ξ := −Ξ'/Ξ` — completed carrier
- `Φ_k(t) := Σ_ρ (½ + it − ρ)^{−k}` — higher log-derivative family (`k = 2` is the curvature; replaces the documents' `P^{(k)}` and "susceptibility = curvature" `χ`)
- `C_a(τ) := 2(a² − τ²)/(a² + τ²)²` — off-line curvature window / detector kernel
- `S_k = Σ_ρ (ρ−½)^{−2k}`; `M_k = Σ_ρ (ρ−½)^k`; `P_k = Σ_ρ ρ^{−k}`; `D2 = Σ_ρ (β−½)²`
- `y_ρ = −(ρ−½)^{−2}`; `T_k = Σ_ρ m_ρ y_ρ^k`; `λ_n` — Li coefficients
- `Q_W` — Weil explicit-formula quadratic form; `H_d` — Hankel matrix; `J_{d,n}` — Jensen polynomials; `a_n` — Taylor/Jensen coefficients of `ξ`
- `χ(s) = Γ_ℝ(1−s)/Γ_ℝ(s)` — functional-equation factor; `χ_n` — frequency susceptibility (subscripted, kept distinct)
- `κ_n` — free cumulants; `β(·)` — Dirichlet beta function (`β(2) = G`, Catalan's constant)

**Collisions resolved by renaming the non-standard user** (canonical kept on the left)
- `γ` = zero ordinate ⟹ contour renamed `C`; Baker–Wüstholz constants renamed `c_B`, `κ_B`; Euler's constant kept as `γ_E`
- `m_ρ` = multiplicity ⟹ multi-index stays `m`; Li blind-spot index renamed `n₀`; FID summation index renamed `n`
- `a` = off-line distance ⟹ Source-A shift multiplier renamed `a_Γ`; cocycle/Jensen coefficients stay subscripted (`a_p`, `a_n`)
- `M_Ξ` = carrier ⟹ difference modules stay subscripted (`M_ζ`, `M_∞`); Mahler measure renamed `M(L)`
- `g_F` = Fisher metric; `g(n)` = Turán ratio; `h(s)` = pole-model holomorphic remainder; `g`, `g_p` = gauge / group elements (kept distinct by subscript/argument)
- generic polynomials in the Bezoutian / Schur–Cohn use `f, g, P` (the placeholders `A, P` were freed by the expansions above)

**Flagged judgment calls** (where two notations might *not* denote the same thing)
- The defect `Δ` is written with the archimedean *log-derivative* `∂_s log Γ∞` to match the weld `H = ∂_s log Γ∞ + ζ'/ζ`; the experimental write-up (`06`) used the factor `Γ∞` itself, which is **not** literally `∂_s log Γ∞`. Canonicalized to `∂_s log Γ∞`; the source variant is noted.
- `Ξ` was written both as a function of `t` (`Ξ(t)=ξ(½+it)`) and of `w` (`Ξ(w)=ξ(½+w)`); merged to `Ξ(w):=ξ(½+w)`, and line-derivative formulas are written directly in `ξ(½+it)`.

---

## Formulas

**Formula 1**
ω = d log ξ(s)
- ω = transport one-form (completed logarithmic connection)
- d = exterior derivative
- ξ = completed zeta (xi) function
- s = complex variable

**Formula 2**
H(s) = ∂_s log Λ(s) = ∂_s log Γ∞(s) + ζ'/ζ(s)
- H = the weld
- ∂_s = derivative with respect to s
- Λ = completed zeta, Λ = Γ∞·ζ
- Γ∞ = archimedean Gamma factor
- ζ'/ζ = logarithmic derivative of ζ (prime term)
- s = complex variable

**Formula 3**
Δ(σ,t) = max( log|∂_s log Γ∞|, log|ζ'/ζ| ) − log|∂_s log Γ∞ + ζ'/ζ|
- Δ = phase-carrier defect (large when the archimedean and prime terms are antiphase)
- σ = real part of s
- t = imaginary part of s
- ∂_s log Γ∞ = archimedean term
- ζ'/ζ = prime term
- log = natural logarithm; |·| = modulus

**Formula 4**
σ_wall = max( ½, 1/k₀ )
- σ_wall = abscissa of the convergence/positivity wall
- k₀ = first nonzero prime-state moment

**Formula 5**
C_a(τ) = 2(a² − τ²)/(a² + τ²)²,   C_a(τ) > 0 ⟺ |τ| < a
- C_a = off-line curvature window / detector kernel
- a = off-line distance, a = |½ − β|
- τ = height offset, τ = t − γ

**Formula 6** `[from prose]` (zero-area of the detector kernel)
∫_{−∞}^{∞} C_a(τ) dτ = 0
- C_a = off-line curvature kernel
- τ = height offset

**Formula 7**
ι : s ↦ 1 − s
- ι = functional-equation involution
- s = complex variable

**Formula 8**
ι² = id,   Fix(ι) = { 1/2 }
- ι = involution s↦1−s
- id = identity map
- Fix(ι) = fixed locus of ι

**Formula 9**
s ↦ 1 − s̄,   with fixed locus the line Re s = ½
- s̄ = complex conjugate of s

**Formula 10**
Λ(s) = Λ(1 − s)
- Λ = completed zeta
- s = complex variable

**Formula 11** `[from prose]` (functional equation of ξ)
ξ(s) = ξ(1 − s)
- ξ = completed zeta (xi) function
- s = complex variable

**Formula 12** `[from prose]` (log-derivative form of the functional equation — the Berry equalization)
ξ'/ξ(s) = − ξ'/ξ(1 − s),   so |ξ'/ξ(½+δ+it)| = |ξ'/ξ(½−δ+it)|
- ξ = completed zeta (xi) function; ξ' = derivative of ξ
- s = complex variable
- δ = lane offset from the seam
- t = imaginary part of s

**Formula 13** `[from prose]` (Ξ recentred; even; divisor)
Ξ(w) := ξ(½ + w),   Ξ(w) = Ξ(−w),   𝒟 = { ρ − ½ }
- Ξ = recentred completed zeta
- w = shifted complex variable
- ξ = completed zeta (xi) function
- 𝒟 = the divisor (zero set of Ξ)
- ρ = a nontrivial zero

**Formula 14**
a_Γ(s) = s/2π
- a_Γ = Source-A shift multiplier
- s = complex variable; π = pi

**Formula 15**
a_Γ(z) = z,   div(z) = [0] − [∞],   deg_ℤ(z) = +1 ≠ 0
- a_Γ = Source-A multiplier as a function
- z = variable
- div = divisor; [0], [∞] = points at 0 and infinity
- deg_ℤ = σ-orbit degree on the orbit ℤ

**Formula 16**
σ_p : x_p ↦ p^{−1} x_p
- σ_p = prime shift operator on lane p
- x_p = coordinate of lane p
- p = a prime

**Formula 17**
C5 = the weld = { the one non-CC place } × { the CC places }
- non-CC place = the σ-orbit-unbalanced (archimedean) place
- CC place = a constant-up-to-coboundary (prime) place

**Formula 18**
ω = H(s) ds,   r(s) = 1 − s,   r*(H ds) = H ds,   H(s) = − H(1 − s)
- ω = the one-form; H = the weld
- s = complex variable; ds = differential of s
- r = reflection s↦1−s; r* = pullback by r

**Formula 19**
𝔾_a ⋊ 𝔾_m
- 𝔾_a = additive group (translation by log p)
- 𝔾_m = multiplicative group (scaling, ∂_s)
- ⋊ = semidirect product

**Formula 20**
[ ∂_s, M_p ] = − log p
- [·,·] = commutator
- ∂_s = dilation generator
- M_p = translation-by-log p operator
- p = a prime

**Formula 21**
σ_p · e_m = p^{−m_p} · e_m
- σ_p = prime shift operator on lane p
- e_m = boundary mode indexed by multi-index m
- p = a prime; m_p = the p-component of m

**Formula 22**
∂_s · e_m = −(m·ℓ) e_m = −( Σ_p m_p log p ) e_m = −(log n) e_m
- ∂_s = dilation generator; e_m = boundary mode
- m = multi-index (m_p)_p; ℓ = (log p)_p; m·ℓ = Σ_p m_p log p
- p = a prime; n = integer with prime exponents m_p (n = ∏ p^{m_p})

**Formula 23**
∂_s = − Σ_p (log p) θ_p
- ∂_s = dilation generator; p = a prime; θ_p = number operator on lane p

**Formula 24**
Π(S) = ( |S|, Σ_{m∈S} m ),   shift − |S| log p
- Π(S) = affine passport of a mode-block S
- S = a set of modes; |S| = number of modes; m = a mode index in S
- p = a prime

**Formula 25**
corank( Λ_{M_ζ} ) over ℚ = ∞
- corank = corank of the difference-Galois relation lattice
- Λ_{M_ζ} = relation lattice of the ζ-module; ℚ = rationals

**Formula 26**
corank( Λ_ff ) over F_q = 1
- Λ_ff = relation lattice (function-field case)
- F_q = finite field with q elements; q = prime power

**Formula 27**
gap = ∞ − 1
- gap = the archimedean seam (difference of coranks)

**Formula 28**
corank < ∞ ⟺ M holonomic
- corank = corank of the relation lattice; M = a difference module

**Formula 29**
trdeg( T_{s_0} ) ≤ corank
- trdeg = transcendence degree; T_{s_0} = continuation data at base point s_0

**Formula 30**
dim W = corank
- dim W = dimension of the weight / Tate-torus space W

**Formula 31**
corank = ∞ ⟺ { log p } ℚ-linearly independent
- { log p } = the set of prime logarithms; ℚ = rationals

**Formula 32**
trdeg = ∞ ⟺ { log p } ℚ-algebraically independent
- trdeg = transcendence degree

**Formula 33**
ξ'/ξ(s) ~ m_ρ /(s − ρ)   near a zero ρ
- ξ = completed zeta; ξ' = derivative of ξ
- s = complex variable; m_ρ = multiplicity of the zero; ρ = a nontrivial zero

**Formula 34**
(1/2πi) ∮_C d log ξ = #{ zeros of ξ inside C }
- π = pi; i = imaginary unit
- ∮_C = contour integral around closed curve C; C = a closed contour

**Formula 35**
μ_ξ = (1/2π) Δ log|ξ|
- μ_ξ = source measure of ξ; π = pi; Δ = Laplacian; log|ξ| = log modulus of ξ

**Formula 36**
(d/dt)² log ξ(½ + it) = Σ_ρ (½ + it − ρ)^{−2} = Φ_2(t)
- t = real height variable; ρ = a nontrivial zero; i = imaginary unit
- ξ = completed zeta; Φ_2 = curvature (k=2 member of Φ_k)

**Formula 37**
Φ_k(t) = Σ_ρ (½ + it − ρ)^{−k},   k ≥ 2
- Φ_k = k-th higher log-derivative along the line
- t = real height variable; ρ = a nontrivial zero; k = order (integer ≥ 2); i = imaginary unit

**Formula 38**
under RH (ρ = ½ + iγ):   Φ_2(t) = − Σ_γ (t − γ)^{−2} < 0
- ρ = a nontrivial zero; γ = ordinate of a zero; t = real height variable; i = imaginary unit

**Formula 39** `[from prose]` (concavity of log|ξ| on the line under RH)
(d/dt)² log|ξ(½ + it)| < 0   (RH)
- ξ = completed zeta; t = real height variable; i = imaginary unit

**Formula 40**
off-line FE-quartet { β±iγ, 1−β±iγ } contributes  C_a(τ) = 2(a²−τ²)/(a²+τ²)² > 0  for |t−γ| < a
- β = real part of an off-line zero; γ = ordinate; a = |½−β|; τ = t−γ; i = imaginary unit

**Formula 41**
det H_d ≥ 0  ∀ d, t  ⟺  RH
- det = determinant; H_d = the d-th Hankel matrix; d = matrix order; t = real height variable
- RH = Riemann Hypothesis

**Formula 42**
𝓛(σ) = − Σ_p log( 1 − X_p p^{−σ} )   converges a.s. ⟺ σ > ½
- 𝓛 = random Euler observable; σ = real part of s; p = a prime; X_p = random phase on lane p

**Formula 43**
Var( Re 𝓛 ) = ½ V(σ) ~ ½ log log X
- Var = variance; Re 𝓛 = real part of 𝓛; V(σ) = variance profile in σ
- σ = real part of s; X = cutoff bound

**Formula 44** `[from prose]` (Selberg central limit theorem)
log|ζ(½ + it)| / √( ½ log log t )  ⇒  𝒩(0, 1)
- ζ = Riemann zeta; t = height; 𝒩(0,1) = standard normal distribution; ⇒ = converges in distribution

**Formula 45** `[from prose]` (prime-sum abscissa, Mertens)
Σ_p p^{−2σ} < ∞  ⟺  σ > ½
- p = a prime; σ = real part of s

**Formula 46**
additive Euler cocycle is a bounded L²-coboundary ⟺ σ ≥ ½
- σ = real part of s; L² = square-integrable function space

**Formula 47**
‖ ψ_s ‖² = ζ(2σ)
- ψ_s = the state vector at s; ‖·‖² = squared norm; ζ = Riemann zeta; σ = real part of s

**Formula 48**
g_F = (log ζ)''(2σ) = Var_p(log n) ~ 1/(2σ − 1)²
- g_F = the Fisher metric; ζ = Riemann zeta; (·)'' = second derivative
- σ = real part of s; Var_p = variance over primes; n = integer

**Formula 49**
χ_n(ρ) / χ_n(1−ρ) = ( n^{1−2β} / |χ_FE| )^{1/m_ρ}  is n-independent ⟺ β = ½
- χ_n = susceptibility at frequency n; ρ = a zero; n = frequency (integer)
- β = real part of ρ; χ_FE = functional-equation factor; m_ρ = multiplicity of ρ

**Formula 50**
χ_n ≡ Φ_k(t) = Σ_ρ (½ + it − ρ)^{−k}   (susceptibility = curvature)
- χ_n = susceptibility; Φ_k = higher log-derivative; t = height; ρ = a zero; k = order; i = imaginary unit

**Formula 51**
Λ(s) = Λ(1−s)  ⟺  θ(1/t) = √t · θ(t)  ⟺  Poisson summation (Ш̂ = Ш)
- Λ = completed zeta; s = complex variable; θ = Jacobi theta function; t = positive real variable
- Ш = the lattice comb; Ш̂ = its Fourier transform

**Formula 52**
g_p = g_p^{−1} ⟹ g_p = ±1
- g_p = group element / multiplier on lane p; p = a prime

**Formula 53**
RH ⟺ Q_W ⪰ 0 ⟺ κ₋ = 0
- RH = Riemann Hypothesis; Q_W = Weil quadratic form; ⪰ 0 = positive semidefinite
- κ₋ = faithful negative index

**Formula 54**
κ₋ = #{ off-line zero-pairs }
- κ₋ = faithful negative index

**Formula 55**
polarization-present ⟺ single Frobenius ⟺ corank = 1 ⟺ F_q
- corank = corank of the relation lattice; F_q = finite field with q elements

**Formula 56**
τ_p = σ_p − 1
- τ_p = additive (translation) part of lane p; σ_p = prime shift operator on lane p

**Formula 57**
additive 1-cocycle:  τ_p a_q = τ_q a_p
- τ_p, τ_q = additive parts of lanes p, q; a_p, a_q = multipliers on lanes p, q; p, q = primes

**Formula 58**
d1 ∘ d0 = 0
- d0, d1 = Koszul coboundary maps (degrees 0, 1); ∘ = composition

**Formula 59**
a = c · σ(g) / g   (constant-up-to-coboundary multiplier gauges to a constant)
- a = a multiplier; c = a constant; σ = the shift; g = a gauge element

**Formula 60**
ω = 0 ∈ H²(G_L)
- ω = residual holonomy class; H²(G_L) = second cohomology of the difference-Galois group G_L

**Formula 61**
ρ_∞(s) · ρ_ζ(s) = 1
- ρ_∞ = archimedean cocycle factor; ρ_ζ = prime (ζ) cocycle factor; s = complex variable

**Formula 62**
χ(s) = Γ_ℝ(1−s)/Γ_ℝ(s) = π^{s−1/2} · Γ((1−s)/2) / Γ(s/2)
- χ(s) = functional-equation defect factor; Γ_ℝ = real Gamma factor; Γ = Gamma function
- s = complex variable; π = pi

**Formula 63**
ι_ζ : θ_p ↦ − θ_p   (prime inversion, zero defect)
- ι_ζ = prime-side involution; θ_p = lane-p phase coordinate; p = a prime

**Formula 64**
∂_s log χ = log π − ½ ψ((1−s)/2) − ½ ψ(s/2) ≠ 0
- ∂_s = derivative in s; χ = functional-equation defect factor; π = pi; ψ = digamma; s = complex variable

**Formula 65**
[ ∂_s, σ_p ] = 0
- [·,·] = commutator; ∂_s = dilation generator; σ_p = prime shift operator on lane p

**Formula 66**
−(φ'/φ)(½ + ir) = 2[ (ξ'/ξ)(1 + 2ir) − (ξ'/ξ)(2ir) ]   ("structurally Ω − Π")
- φ = scattering / Maass–Selberg factor; φ' = its derivative; r = real spectral parameter; i = imaginary unit
- ξ = completed zeta; Ω = archimedean part; Π = prime part

**Formula 67**
κ₋ = APS index:  bulk = Euler / finite places,  boundary η = archimedean;  RH ⟺ Index = 0
- κ₋ = faithful negative index; APS = Atiyah–Patodi–Singer; η = boundary eta-invariant; RH = Riemann Hypothesis

**Formula 68**
κ₋ = 2 · #{ off-line zeros }
- κ₋ = faithful negative index

**Formula 69**
M_Ξ := − Ξ'/Ξ   (the completed carrier)
- M_Ξ = carrier operator; Ξ = recentred completed zeta; Ξ' = derivative of Ξ

**Formula 70**
RH ⟺ supp μ_ξ ⊂ { Re s = ½ }
- RH = Riemann Hypothesis; supp = support; μ_ξ = source measure of ξ; Re s = real part of s

**Formula 71**
(1/2πi) ∮_{∂R} (ξ'/ξ)(s) ds = 0   for every rectangle R off the critical line
- π = pi; i = imaginary unit; ∮_{∂R} = contour integral over rectangle boundary ∂R; R = a rectangle off the line
- ξ = completed zeta; ξ' = derivative of ξ; s = complex variable

**Formula 72**
ρ = β + iγ,   β ≠ ½
- ρ = a nontrivial zero; β = real part of ρ; γ = ordinate of ρ; i = imaginary unit

**Formula 73**
ξ'/ξ(s) ~ m_ρ /(s − ρ) + h(s)   (local pole model)
- ξ = completed zeta; ξ' = derivative of ξ; s = complex variable
- m_ρ = multiplicity of the zero; ρ = a nontrivial zero; h(s) = regular (holomorphic) remainder

**Formula 74**
Δ_{ζ'/ζ} → log 2 (true),   Δ_{(ζ'/ζ)_N} → 0 (finite)
- Δ_{ζ'/ζ} = phase-weld defect for the true prime term
- Δ_{(ζ'/ζ)_N} = phase-weld defect for the finite-Euler truncation
- (ζ'/ζ)_N = finite Euler product to N primes; log 2 = natural log of 2

**Formula 75**
d_transport( ζ'/ζ, (ζ'/ζ)_N ) ≥ c > 0
- d_transport = transport metric; ζ'/ζ = true prime term; (ζ'/ζ)_N = finite-Euler truncation; c = positive constant

**Formula 76**
co-failure excess ≥ c > 0
- c = a positive constant

**Formula 77**
λ₁(G_true) ≥ λ₁(G_finite) + c
- λ₁ = top eigenvalue; G_true, G_finite = association graphs of the true and finite-Euler fields; c = positive constant

**Formula 78**
Cov( O, δV ) > 0 (true) / < 0 (controls)
- Cov = covariance; O = observed-volume / amplitude coordinate; δV = volume perturbation

**Formula 79**
∫ O dθ > c > 0
- ∫ = integral; O = amplitude coordinate; θ = phase momentum (θ = arg(ζ'/ζ)); c = positive constant

**Formula 80** `[from prose]` (phase-space momentum coordinate)
θ(t) = arg( ζ'/ζ(½ + it) ),   O(t) = log( 1 + |ζ'/ζ(½ + it)| )
- θ = phase-space momentum; O = amplitude coordinate; arg = argument (phase angle)
- ζ'/ζ = log-derivative of ζ; t = real height variable; i = imaginary unit

**Formula 81**
| 1/(s − ρ) | = 1 / √( (σ − β)² + τ² )  ⟹  occupation centre at σ = β;   all centres = ½ ⟺ RH
- s = complex variable; ρ = a nontrivial zero; σ = real part of s; β = real part of ρ; τ = t − γ

**Formula 82**
σ > 1  ⟹  (ζ'/ζ)_N → ζ'/ζ   (right-strip collapse)
- σ = real part of s; (ζ'/ζ)_N = finite-Euler truncation; ζ'/ζ = true prime term

**Formula 83**
K_q(σ, σ') = Corr( 𝟙_{Δ(σ+it) > q}, 𝟙_{Δ(σ'+it) > q} )
- K_q = continuum association kernel at threshold q; σ, σ' = two real-part lanes; Corr = correlation
- 𝟙 = indicator function; Δ = phase-carrier defect; t = real height variable; q = threshold level

**Formula 84**
Q_W = 𝔇,   signature (1 | ∞),   V_arch = Re ψ
- Q_W = Weil quadratic form; 𝔇 = explicit-formula distribution; (1|∞) = signature (one positive, ∞ negative)
- V_arch = the single archimedean direction; ψ = relevant test function; Re = real part

**Formula 85**
m_ξ ∈ ℕ₀
- m_ξ = Krein–Langer / Herglotz index of ξ; ℕ₀ = nonnegative integers

**Formula 86**
H = [ m_{i+j} ] ⪰ 0  ∧  H' = [ m_{i+j+1} ] ⪰ 0
- H, H' = Hankel and shifted-Hankel matrices of moments; m_k = the k-th moment; i, j = matrix indices; ⪰ 0 = positive semidefinite

**Formula 87**
#neg(Q_W) = 0 ⟺ ‖ P̃ ‖ ≤ 1 ⟺ Ω ≽ Π,   P̃ = Ω^{−1/2} Π Ω^{−1/2}
- #neg(Q_W) = number of negative eigenvalues of Q_W; ‖·‖ = operator norm; P̃ = normalized prime operator
- Ω = archimedean operator; Π = prime operator; ≽ = operator dominance (Ω − Π ⪰ 0)

**Formula 88**
ω = 0  ⇏  RH
- ω = realization / holonomy class; RH = Riemann Hypothesis; ⇏ = does not imply

**Formula 89**
corank^{(T)} = ∞  for  T ≥ 2
- corank^{(T)} = graded corank at degree T; T = degree bound

**Formula 90**
κ₋ = 0  =  (Q_W ⪰ 0)  =  (FE-polarization ⪰ 0)  =  (m_ξ ∈ ℕ₀)  =  (det H_d ≥ 0 ∀ d,t)  =  (Ω ≽ Π)  =  (G5 unitary)
- κ₋ = faithful negative index; Q_W = Weil form; m_ξ = Krein–Langer index of ξ; det H_d = Hankel determinant of order d
- d = matrix order; t = real height variable; Ω = archimedean operator; Π = prime operator; G5 = unitary-holonomy gatekeeper (ι unitary)

**Formula 91**
C_a(0) = 2 / a²   (center curvature)
- C_a = off-line curvature kernel; a = off-line distance, a = |½ − β|

**Formula 92**
ζ ∉ K_B = ℂ( s, { p^{−s} } )
- ζ = Riemann zeta; K_B = prime flow field; ℂ = complex numbers; s = complex variable; p = a prime

**Formula 93**
⟨ 1, r ⟩ = 𝔾_a ⋊ 𝔾_m,   transverse seam [ 𝔾_a, 𝔾_m ]
- ⟨1, r⟩ = span of the constant and reflection modes; r = reflection s↦1−s
- 𝔾_a = additive group; 𝔾_m = multiplicative group; [·,·] = commutator (the transverse seam)

**Formula 94**
∂_s e_m = −(log n) e_m   (relation on M_ζ);   ∂_s|_{M_∞} = − ½ log π + ½ ψ(s/2)   (generator on M_∞)
- ∂_s = derivative in s; e_m = boundary mode; n = integer (n = ∏ p^{m_p})
- M_ζ = the ζ difference module; M_∞ = the archimedean module; π = pi; ψ = digamma; s = complex variable

**Formula 95**
digamma residue = ½ ψ(s/2)
- ψ = digamma function; s = complex variable

**Formula 96**
Γ_ℝ(s + 2) = (s/2π) Γ_ℝ(s)
- Γ_ℝ = real Gamma factor; s = complex variable; π = pi

**Formula 97**
| p^{−s} | = p^{−1/2}  ⟺  Re(s) = ½
- p = a prime; s = complex variable; |·| = modulus; Re(s) = real part of s

**Formula 98**
φ'(T) = θ'(T) + π · S'(T)
- φ' = total phase derivative (Clark phase); θ' = archimedean/FE channel derivative; S' = derivative of the argument function S
- T = height variable; π = pi

**Formula 99**
θ'(T) = ½ log( T / 2π )
- θ' = archimedean/FE channel derivative; T = height variable; π = pi

**Formula 100**
ω = dO ∧ dφ,   O = log( 1 + |ζ'/ζ| ),   φ = arg( Γ∞ + ζ'/ζ )
- ω = the (scalar) oriented 2-form; d = exterior derivative; ∧ = wedge product
- O = amplitude coordinate; φ = phase coordinate; ζ'/ζ = log-derivative of ζ; Γ∞ = archimedean factor; arg = argument

**Formula 101**
inertia (1, 0, 10),   κ₋ = 1   (Davenport–Heilbronn Weil–Gram)
- inertia = (negative, zero, positive) eigenvalue counts; κ₋ = faithful negative index

**Formula 102**
e^{ q((s−½)²) } · ξ
- e = exponential base; q = quadratic polynomial (Hadamard genus factor); s = complex variable; ξ = completed zeta

**Formula 103** `[from prose]` (the surrogate's log-derivative leaves the prime part intact)
( e^{q((s−½)²)} ξ )'/( e^{q((s−½)²)} ξ ) = ξ'/ξ + q'(s)
- q = quadratic Hadamard factor; q' = its derivative; ξ = completed zeta; ξ' = derivative of ξ; s = complex variable

**Formula 104**
HT ± (D-algebraic) = HT
- HT = hypertranscendental; D-algebraic = differentially-algebraic; ± = sum or difference

**Formula 105** `[from prose]` (Hölder 1887 — the founding negative theorem)
∄ nonzero polynomial F :  F( s, Γ, Γ', …, Γ^{(n)} ) ≡ 0   (and likewise for ζ)
- F = a polynomial in the function and its derivatives; s = complex variable; Γ = Euler gamma; ζ = Riemann zeta; n = order

**Formula 106** `[from prose]` (Wheeler–DeWitt constraint analogy)
Ĥ Ψ = 0
- Ĥ = the constraint (Hamiltonian) operator; Ψ = the state; (constraint, no iℏ∂_t flow term)

**Formula 107**
F^{(T)}(1) = (−1)^T Σ C_a ∏_p (log p)^{a_p}
- F^{(T)} = the T-th derivative object at the s=1 edge; T = order of differentiation
- C_a = combinatorial coefficient indexed by a; a = multi-exponent (a_p)_p; p = a prime

**Formula 108**
(½ − β + iτ)^{−2} + (β − ½ + iτ)^{−2} = 2(a² − τ²)/(a² + τ²)²,   positive ⟺ |τ| < a
- β = real part of an off-line zero; τ = height offset (t − γ); a = |½ − β|; i = imaginary unit

**Formula 109**
n₀ = π γ / (4 δ)
- n₀ = first-negative Li-coefficient index (blind-spot location); π = pi; γ = height scale; δ = offset parameter

**Formula 110**
c = n₀ · δ / γ ≈ 0.79 ≈ π/4
- c = the #88 constant; n₀ = first-negative index; δ = offset parameter; γ = height scale; π = pi

**Formula 111**
| μ | = √q   (exactly)
- μ = a non-trivial Frobenius eigenvalue; q = prime power

**Formula 112**
normalized margin = 1 − q^{−½}
- q = prime power

**Formula 113**
κ_n = ζ(2n + 1)   (free cumulants)
- κ_n = the n-th free cumulant; ζ = Riemann zeta; n = index

**Formula 114**
free-cumulant sign pattern:  κ_2 > 0,  κ_4 < 0,  κ_6 > 0,  κ_8 < 0
- κ_n = the n-th free cumulant

**Formula 115**
c_n = Λ(n) ≥ 0   (ζ log-derivative coefficients)
- c_n = n-th log-derivative Dirichlet coefficient; Λ(n) = von Mangoldt function; n = integer

**Formula 116**
⟨ r ⟩ = 0.611   (GUE order parameter)
- ⟨r⟩ = mean consecutive-spacing ratio (0.611 = the GUE value)

**Formula 117**
M(L) = 1.176280818   (Lehmer polynomial Mahler measure)
- M(L) = Mahler measure of the Lehmer polynomial L

**Formula 118**
corr( log margin, gap ) = − 0.25
- corr = correlation coefficient; log margin = log of the positivity margin; gap = local zero gap

**Formula 119**
T / (N + T)   (domain-corank internal fraction)
- T = number of internal degrees / truncation depth; N = number of base nodes

**Formula 120**
a is CC ⟺ deg_O(a) = 0 on every σ-orbit O
- a = a multiplier; CC = constant-up-to-coboundary; deg_O = σ-orbit degree on orbit O; O = a σ-orbit

**Formula 121**
g = ( p^{−1} )_p,   with infinite-dimensional Zariski closure when Λ = 0
- g = tuple of prime multipliers; p = a prime; Λ = the relation lattice (here all-zero)

**Formula 122**
s ↦ 1 − s  ⟹  p^{−s} ↦ p^{−1}( p^{−s} )^{−1}
- s = complex variable; p = a prime

**Formula 123**
dρ / dε = − n^{−ρ} / ζ'(ρ)
- ρ = a zero; ε = perturbation parameter; n = integer (frequency); ζ' = derivative of ζ

**Formula 124**
trdeg_ℚ{ Stieltjes(ζ_S) } = corank_ℚ{ log p : p ∈ S }
- trdeg_ℚ = transcendence degree over ℚ; Stieltjes(ζ_S) = Stieltjes constants of the S-restricted zeta
- corank_ℚ = corank over ℚ; S = a set of primes; p = a prime

**Formula 125**
γ_n^{(q)} = ( B_n^+ / n! ) ( log q )^n   (corank-1 collapse)
- γ_n^{(q)} = n-th Stieltjes constant in the corank-1 (function-field) case; B_n^+ = a Bernoulli-type number
- n! = factorial; q = prime power

**Formula 126**
F₁ exists ⟺ ( D = 0 ) ∧ ( corank finite );   over ℚ:  ( D = +1, corank = ∞ )
- F₁ = the single "Frobenius" / field with one element; D = the orbit-imbalance degree; corank = corank of the relation lattice; ℚ = rationals

**Formula 127**
{ corank = 1 } ⊊ { trdeg = 1 },   witness { π, π² }:  trdeg = 1,  corank = 2
- corank = corank of the relation lattice; trdeg = transcendence degree; π = pi; ⊊ = proper subset

**Formula 128**
trdeg(periods) = dim G;   dim W = corank = 1;   reflected constraint unitary on the critical locus ⟺ RH-over-F_q
- trdeg = transcendence degree; dim G = dimension of the difference-Galois group; dim W = dimension of the weight space
- corank = corank of the relation lattice; F_q = finite field with q elements

**Formula 129**
c_1 = Σ β_p log p   (Tier-1 Stieltjes weld)
- c_1 = first Stieltjes-related coefficient; β_p = integer/rational coefficient for prime p; p = a prime

**Formula 130**
RH ⟺ archimedean-completed Koszul acyclic ⟺ ω = 0
- RH = Riemann Hypothesis; Koszul acyclic = the completed Koszul complex is acyclic; ω = realization/obstruction class

**Formula 131**
− ξ'/ξ(s) = Σ_{k≥1} P_k s^{k−1},   P_k = Σ_ρ ρ^{−k}
- ξ = completed zeta; ξ' = derivative of ξ; s = complex variable
- P_k = k-th secular power sum; k = index (≥ 1); ρ = a nontrivial zero

**Formula 132**
λ_n = − Σ_j C(n, j) (−1)^j P_j
- λ_n = the n-th Li coefficient; C(n, j) = binomial coefficient "n choose j"; P_j = j-th secular power sum; n, j = indices

**Formula 133**
ℚ( { P_k } ) ⊇ { ζ(odd) }
- ℚ({P_k}) = field generated over ℚ by the secular power sums; P_k = k-th power sum; ζ(odd) = zeta at odd integers

**Formula 134**
{ m : Σ_p m_p log p = 0 } = { 0 }
- m = multi-index (m_p)_p; p = a prime; m_p = p-component of m

**Formula 135**
ι(s) = 1 − s   (order 2);   ῑ fixes exactly Re(s) = ½
- ι = the involution; ῑ = the anti-holomorphic involution; s = complex variable; Re(s) = real part of s

**Formula 136**
ψ(s/2 + 1) = ψ(s/2) + 2/s
- ψ = digamma function; s = complex variable

**Formula 137**
rank = Cardinal.mk( Nat.Primes )   (corank stays ∞ after adjoining ∂_s)
- rank = rank of the prime-log span with the archimedean generator adjoined; Cardinal.mk(Nat.Primes) = cardinality of the set of primes

**Formula 138**
f = g · e^{ z λ }   solves the shift ODE
- f = the solution; g = a gauge element; e = exponential base; z = variable; λ = eigenvalue / rate

**Formula 139**
e_k(S) = q^k e_k(S^{−1});   ∏(1 − ω T) FE-invariant,   |ω| = √q
- e_k = k-th elementary symmetric polynomial; S = multiset of Frobenius eigenvalues; S^{−1} = inverse eigenvalues
- q = prime power; ω = a Frobenius eigenvalue; T = formal variable; |·| = modulus

**Formula 140**
κ₋(H) = #{ off-line conjugate pairs }   (Sylvester)
- κ₋(H) = faithful negative index of carrier H

**Formula 141**
one off-line zero ⟹ κ₋ = 2   (FE-doubling)
- κ₋ = faithful negative index

**Formula 142**
superzeta generating function = Σ_i ( 1 − r_i X )^{−1};   k-th coeff = Σ_ρ ρ^{−k} = P_k
- r_i = the i-th reciprocal root; X = formal variable; k = index; ρ = a nontrivial zero; P_k = k-th power sum

**Formula 143**
f(s) g(t) − f(t) g(s) = (s − t) Σ_j r_j f_j(s) f_j(t)   (Bezoutian)
- f, g = the two polynomials; s, t = variables; r_j = j-th Gram/residue weight; f_j = j-th basis polynomial; j = index

**Formula 144**
sigNeg( scForm[f] ) = winding(f) = #inside(f)
- sigNeg = number of negative eigenvalues (Schur–Cohn inertia); scForm[f] = Schur–Cohn form of polynomial f
- winding(f) = winding number of f; #inside(f) = number of roots inside the unit circle; f = a polynomial

**Formula 145**
| m · ℓ | ≥ c_B · H(m)^{−κ_B}   (Baker–Wüstholz lower bound)
- m = integer vector; ℓ = (log p)_p; m·ℓ = linear form Σ m_p log p; c_B = effective positive constant; H(m) = height of m; κ_B = effective exponent

**Formula 146**
‖ ∂_t arg( Γ∞ + ζ'/ζ ) ‖   (phase-Sobolev H^{1/2} seminorm)
- ∂_t = derivative in t; arg = argument (phase angle); Γ∞ = archimedean factor; ζ'/ζ = prime term; ‖·‖ = an H^{1/2} seminorm

**Formula 147**
C_a(τ) = 2(a² − τ²)/(a² + τ²)²,   matched width ≈ a/2,   8a → 0.016 of peak
- C_a = scale-matched off-line curvature detector; a = off-line distance, a = |½ − β|; τ = height offset (t − γ)

**Formula 148**
∮ d arg = 2πi ( #zeros − #poles )   (winding number)
- ∮ = contour integral; d arg = differential of the argument; π = pi; i = imaginary unit; #zeros, #poles = enclosed counts

**Formula 149**
σ* ∈ (½, 1),   possibly σ* = 3/4,   or the region where Σ_p p^{−2σ} ~ log log
- σ* = the crossover scale; p = a prime; σ = real part of s

**Formula 150**
y_ρ := − (ρ − ½)^{−2}   (reciprocal seam-squared coordinate)
- y_ρ = the chart value at zero ρ; ρ = a nontrivial zero

**Formula 151**
Σ_ρ (ρ − ½)^k diverges   (forward seam power sum)
- ρ = a nontrivial zero; k = power index

**Formula 152**
RH ⟺ every y_ρ real-positive ⟺ {T_k}_{k≥1}, T_k := Σ_ρ m_ρ y_ρ^k, is a Stieltjes moment sequence ⟺ the shifted Hankel towers [T_{i+j+1}]_{i,j≥0}, [T_{i+j+2}]_{i,j≥0} are positive definite to all orders
- RH = Riemann Hypothesis; y_ρ = reciprocal seam-squared chart value at ρ; T_k = the k-th seam moment
- m_ρ = multiplicity of ρ; ρ = a nontrivial zero; k = index (≥ 1); i, j = Hankel indices (≥ 0); [T_{i+j+1}] = Hamburger tower; [T_{i+j+2}] = Stieltjes tower
- T_0 = Σ_ρ 1 = ∞ is excluded (the measure has infinite total mass, finite k≥1 moments); strict positive-definiteness is the target (a singular block ⟹ finite-atomic measure, incompatible with the infinite divisor)

**Formula 153**
κ₋ = 0 ⟺ Q_W ⪰ 0 (signature (1|∞)) ⟺ m_ξ ∈ ℕ₀ ⟺ det H_d ≥ 0 ∀ d,t ⟺ uniform Jensen / Laguerre–Pólya
- κ₋ = faithful negative index; Q_W = Weil form; m_ξ = Krein–Langer index of ξ; det H_d = Hankel determinant of order d
- d = matrix order; t = real height variable; ℕ₀ = nonnegative integers

**Formula 154**
M_k = p_k;   S_k = − k [ w^{2k} ] log Ξ;   λ_n = Σ_j C(n, j) (−1)^{j+1} σ_j
- M_k = k-th contour moment (= Newton power sum p_k); p_k = k-th Newton power sum; S_k = k-th seam Taylor coefficient
- k = index; [w^{2k}] = coefficient extraction of w^{2k}; w = shifted variable; Ξ = recentred completed zeta
- λ_n = n-th Li coefficient; C(n, j) = binomial coefficient; σ_j = j-th elementary symmetric function; n, j = indices

**Formula 155**
Ξ'/Ξ = ∂_s log Γ∞ + ζ'/ζ;   S_k = S_k^A + S_k^P
- Ξ = recentred completed zeta; Ξ' = derivative of Ξ; ∂_s log Γ∞ = archimedean part; ζ'/ζ = prime part
- S_k = k-th seam power sum; S_k^A, S_k^P = its archimedean and prime halves

**Formula 156**
halves ≍ 2^{2k};   residue S_k ≍ γ_1^{−2k};   cancel to 2·(4γ_1²)^{−k} ≈ 2·800^{−k};   Δ_k ∼ k;   ≳ 2.9k guard digits
- 2^{2k} = growth of each half (nearest singularity at distance ½); S_k = k-th seam power sum
- γ_1 ≈ 14.13 = ordinate of the first zero; k = index; Δ_k = phase-defect at order k

**Formula 157**
Σ_ρ (ρ − ½)^{−2k} = 2^{2k} − ¼(2^{2k} − 1) ζ(2k) − 2^{2k−2} β(2k) − ( 2(2k−1)! )^{−1} (ζ'/ζ)^{(2k−1)}(½)
- ρ = a nontrivial zero; k = index; ζ = Riemann zeta; β = Dirichlet beta function (β(2) = G, Catalan's constant)
- (ζ'/ζ)^{(2k−1)} = (2k−1)-th derivative of ζ'/ζ; (·)! = factorial

**Formula 158**
ζ(2k + 1) = ∫ y^k dν,   ν = Σ_n (1/n) δ_{1/n²} ≥ 0
- ζ = Riemann zeta; k = index; y = integration variable; ν = the integer-divisor measure
- n = positive integer; δ_{1/n²} = Dirac mass at 1/n²

**Formula 159**
corank^{(T)} = ∞ ∀ T ≥ 2 ⟺ { log p } ℚ-algebraically independent ⟺ trdeg = ∞ ⟺ DSS
- corank^{(T)} = graded corank at degree T; T = degree bound; { log p } = set of prime logs; ℚ = rationals
- trdeg = transcendence degree; DSS = the value-arithmetic apex statement

**Formula 160**
γ_E ∉ ℚ   (open since 1734)
- γ_E = Euler–Mascheroni constant; ℚ = rationals

**Formula 161**
arithmetic-progression divisor γ_n = n:  S_k = (−1)^k ζ(2k) ∈ ℚ·π^{2k};   π² + 6 S_1 = 0;   5 S_2 = 2 S_1²
- γ_n = ordinate of the n-th zero (here equal to n); n = index; S_k = k-th seam power sum; ζ = Riemann zeta; π = pi
- k = index; S_1, S_2 = first and second seam power sums

**Formula 162**
Σ_ρ h(γ_ρ) = arch − Σ_p (log p) …   (explicit formula)
- ρ = a nontrivial zero; h = a test function; γ_ρ = ordinate of zero ρ; arch = archimedean term; p = a prime

**Formula 163** `[from prose]` (FE forces the odd reciprocal-seam power sums to vanish)
μ_{2k+1} = Σ_ρ (ρ − ½)^{−(2k+1)} = 0,   RH ⟺ D2 = Σ_ρ (β − ½)² = 0
- μ_{2k+1} = the (2k+1)-th (odd) seam power sum; ρ = a nontrivial zero; k = index
- D2 = squared-offset discriminator; β = real part of a zero; RH = Riemann Hypothesis

**Formula 164**
source-built faithful index, signature (1, ρ − 1)   (Hodge index)
- (1, ρ−1) = one positive, ρ−1 negative directions; ρ = the relevant rank (number of classes)

**Formula 165**
A_arch − Σ_{p∈S} P_p ≥ 0 as S → all primes ⟺ RH   (ROUTE-C)
- A_arch = archimedean term; P_p = prime-p contribution; S = a finite set of primes; p = a prime; RH = Riemann Hypothesis

**Formula 166**
RH ⟺ F_ζ elliptic with period point interior to D_∞ = Sp_∞(ℝ)/U(∞)
- RH = Riemann Hypothesis; F_ζ = the period object of ζ; D_∞ = the infinite period domain
- Sp_∞(ℝ) = infinite symplectic group; U(∞) = infinite unitary group

**Formula 167**
K_MS(s, w) ~ ( 1 − Θ(s) Θ(w)‾ ) / ( s + w‾ − 1 ) ∈ ℕ₀  ⟺  RH
- K_MS = the Maass–Selberg two-variable kernel; s, w = complex variables; Θ = inner/characteristic function
- Θ(w)‾, w‾ = complex conjugates; ℕ₀ = the Nevanlinna class N₀; RH = Riemann Hypothesis

**Formula 168**
DSS ⟺ { γ_n } algebraically independent over the period field   (modulo Grothendieck period conjecture)
- DSS = the realization/transcendence apex; γ_n = ordinate of the n-th zero

**Formula 169**
#{ non-real Jensen roots } → 2 κ₋;   = 0 ∀ (d, n) ⟺ LP ⟺ RH
- #{non-real Jensen roots} = count of non-real roots of the Jensen polynomials; κ₋ = faithful negative index
- d = degree; n = shift index; LP = Laguerre–Pólya class; RH = Riemann Hypothesis

**Formula 170**
ξ'/ξ(s) = b + Σ_ρ [ 1/(s − ρ) + 1/ρ ]   (Hadamard, ξ of order 1)
- ξ = completed zeta; ξ' = derivative of ξ; b = the Hadamard constant; s = complex variable; ρ = a nontrivial zero

**Formula 171** `[from prose]` (Hadamard product of ξ implied by order 1)
ξ(s) = ξ(0) · e^{ b s } · ∏_ρ ( 1 − s/ρ ) e^{ s/ρ }
- ξ = completed zeta; s = complex variable; b = the Hadamard constant; ρ = a nontrivial zero

**Formula 172**
RH ⟺ κ₋ = 0 ⟺ det H_d ≥ 0 ∀ d, t   (positivity apex)
- RH = Riemann Hypothesis; κ₋ = faithful negative index; det H_d = Hankel determinant of order d; d = matrix order; t = real height variable

**Formula 173**
corank^{(2)} = ∞   (degree-2 prime-log monomials ℚ-linearly independent; open for { log 2, log 3 })
- corank^{(2)} = graded corank at degree 2; ℚ = rationals

**Formula 174**
M_k(R) = Σ_ρ (ρ − ½)^k   (source-width contour moment)
- M_k(R) = k-th contour moment over radius R; R = contour radius; ρ = a nontrivial zero; k = index

**Formula 175**
D2 = Σ_ρ (β − ½)²,   RH ⟺ D2 = 0
- D2 = squared-offset discriminator; β = real part of a zero; ρ = a nontrivial zero; RH = Riemann Hypothesis

**Formula 176**
g(n) = a_n² / ( a_{n−1} a_{n+1} ) → 1 as ~ c/n   (normalized Turán margin)
- g(n) = normalized Turán ratio at index n; a_n = the n-th Taylor/Jensen coefficient of ξ; n = index; c = a constant

**Formula 177**
det H_d ≥ 0 ∀ d, t;   report anisotropic radius ρ_min(d, n)
- det H_d = Hankel determinant of order d; d = degree; t = real height variable; ρ_min(d, n) = direction-wise (anisotropic) Jensen radius; n = shift index

**Formula 178**
H_FID = [ ζ( 2(i + j) + 3 ) ] ⪰ 0   (FID Hankel matrix, positive semidefinite unconditionally)
- H_FID = the FID Hankel matrix; ζ = Riemann zeta; i, j = matrix indices; ⪰ 0 = positive semidefinite

**Formula 179**
H = B + V C V*,   inertia(H) = inertia(B) + inertia(−C^{−1} − V* B^{−1} V) − inertia(−C^{−1});   C<0 ⟹ κ₋(H) = κ₋(−C^{−1} − V* B^{−1} V);   rank-one threshold α_c = −1/⟨v, B^{−1} v⟩
- H = candidate completed carrier; B = positive Euler/explicit-formula bulk (B>0); V = finite boundary channels; C = Hermitian boundary matrix (Γ/pole/archimedean extension); V* = conjugate transpose
- inertia = (negative, zero, positive) eigenvalue counts; κ₋ = faithful negative index
- α_c = rank-one Krein threshold; v = a boundary vector; ⟨·,·⟩ = inner product

**Formula 180**
folded conjugate pair y=u+iv (weight μ), T_k=μ(y^k+ȳ^k):   det[[T_1,T_2],[T_2,T_3]] = −4μ²|y|²(Im y)²,   det[[T_2,T_3],[T_3,T_4]] = −4μ²|y|⁴(Im y)²   (both < 0 ⟺ Im y ≠ 0; = 0 ⟺ Im y = 0, i.e. y real)
- y = u+iv reciprocal seam-squared coordinate of a folded conjugate pair; μ = atom weight; T_k = k-th reciprocal moment of the pair; |y| = modulus; Im y = imaginary part — the local obstruction coordinate
- the two determinants are the degree-one shifted Hankel minors H_1^(0), H_1^(1); both fail iff Im y ≠ 0, so the shifted reciprocal test is faithful and the obstruction is exactly Im y (a high/near-line defect is tiny but keeps fixed negative sign)
- special case — off-line FE quartet {±a±iγ}, w=ρ−½, y=−1/w², μ=2: gives det H_1^(0)=−64 a²γ²/(a²+γ²)^6, det H_1^(1)=−64 a²γ²/(a²+γ²)^8 (a=|½−β|, γ=ordinate; =0 ⟺ a=0 on-line)

**Formula 181**
T_k = −2k(−1)^k [z^k] log Φ(z),   Φ(z) := Ξ(√z) = ξ(½+√z)   (even FE-orbit quotient generating function)
- z = w² = (ρ−½)² the FE-orbit coordinate (the orbit [w]={w,−w} folds to one z-atom); Φ(z)=Ξ(√z) carries quotient multiplicity m per orbit; [z^k] = Taylor coefficient at z=0; T_k = k-th FE-folded reciprocal seam moment (trace weight 2m per orbit)
- the factor 2 converts the quotient multiplicity m to the bridge trace weight 2m; consistent with S_k = −k[w^{2k}]logΞ and T_k = Σ_ρ m_ρ y_ρ^k = Σ_{[w]} 2m_w y_{[w]}^k (y = −(ρ−½)^{−2})

**Formula 182**
arch/prime Hankel split: T^A_k = (−1)^k S_k^A, T^P_k = (−1)^k S_k^P;   S_k = −[w^{2k−1}](A+P), A = Ξ'/Ξ archimedean part, P = ζ'/ζ;   sig[T^A_{i+j+1}]_{0..d} = (d, 1),   sig[T_{i+j+1}] = (d+1, 0)
- T^A_k, T^P_k = archimedean / prime reciprocal moments; A = 1/(½+w)+1/(w−½)−½logπ+½ψ((½+w)/2); P = ζ'/ζ(½+w)
- sig = inertia (n_pos, n_neg); the arch Hankel has exactly one negative direction (the s=0,1 pole, S_k^A=2^{2k} ⟹ rank-1 negative −4·uu*, u_i=(−4)^i); the prime Hankel is indefinite; the sum is the PD Q_0 Hankel
- the single negative direction is the finite-d shadow of the Weil/Hodge signature (1,∞) / (1,ρ−1)

**Formula 183**
closed-form archimedean seam power-sum:   S_k^A = 2^{2k+1} − ψ^{(2k−1)}(¼) / (2^{2k}·(2k−1)!)   (→ 2^{2k} as k→∞, matching the seam-cancellation half-scale);   pole-direction residue   Q_0[u] = ∫ 2y²/(1+4y)² dν_0,   u_i = (−4)^i
- ψ^{(n)} = polygamma (n-th derivative of digamma); ν_0 = 2Σ y_n δ_{y_n} the reciprocal zero-divisor measure (y_n = γ_n^{−2}); verified against the −[w^{2k−1}] Taylor coefficient of the weld A to 1e-121
- S_k^A is the −[w^{2k−1}] coefficient of the archimedean weld A, in closed form — no Taylor of ζ'/ζ needed; the prime part is then free: S_k^P = (−1)^k T_k − S_k^A, i.e. the prime Hankel H^P = H^0 − H^A
- u_i=(−4)^i is evaluation at the s=1 pole image y=−4; Σ_i(−4)^i y^i = 1/(1+4y) on the support (4y_n<0.02), so Q_0[u] is a convergent positive constant (≈0.04564, independent of d) — the entireness residue of the rank-1 pole cancellation, not a near-failure

**Formula 184** `[PROVED, all d — archimedean rank-one theorem]`
form-level archimedean weld (trivial-zero + pole decomposition):   Q_arch[p] = −4 p(−4)² + Σ_{j≥1} (2j+½)^{−2} p(−(2j+½)^{−2})²;   equivalently S_k^A = 2^{2k} − Σ_{j≥1}(2j+½)^{−2k};   matrix form H_d^A = R_d^A − 4 u uᵀ, R_d^A = Σ_{j≥1}(2j+½)^{−2} v_j v_jᵀ ≻ 0 ⟹ inertia (d,1)
- derived from A(w)=1/(½+w)+1/(w−½)−½logπ+½ψ((½+w)/2) by residues: a simple pole r/(w−w_a) gives r·y_a^k in T^A_k (y_a=−w_a^{−2}); s=0 pole at w=−½ cancels the digamma (net +1 at y=−4), each Γ-factor/trivial-zero pole w=−(2j+½) has residue −1
- exhibits the sig(d,1) explicitly: positive squares over the trivial-zero divisor (y_j=−(2j+½)^{−2}, tight cluster in (−0.16,0)) minus one rank-1 square at the pole image y=−4 (coefficient −4 = y·mass), negative direction p↦p(−4)=⟨c,u⟩
- names the arch budget: RH on u^⊥ ⟺ ∀p with p(−4)=0, Q_prime[p] + Σ_{j≥1}(2j+½)^{−2}p(−(2j+½)^{−2})² ≥ 0 — the prime form absorbed by the trivial-zero square-sum
- PROVED all d: R_d^A ≻ 0 (a nonzero deg-d poly cannot vanish at the infinitely many distinct y_j) ⟹ at most one negative eigenvalue; uᵀH_d^A u = uᵀR_d^A u − 4(uᵀu)² < 1−4 < 0 ⟹ at least one; so inertia (d,1), single neg dir = u. Identity cross-checked Hankel-vs-decomposition to 1e-62 (computations/2026-06-21-connes-arch-trivialzero-decomp.py). Orbit normalization (−½ folded) halves to H_d^A=½Σa_n v_nv_nᵀ−2uuᵀ, a_n=4/(4n+1)²

**Formula 185**
fused four-way split of the zero-side seam power sum:   S_k = POLE_k + ZETA_k + BETA_k + PRIME_k,   POLE_k = 2^{2k+1},   ZETA_k = −½(2^{2k}−1)ζ(2k),   BETA_k = −2^{2k−1}β(2k),   PRIME_k = (−1)^k T_k − (POLE+ZETA+BETA)_k = −(2k−1)!^{−1}(ζ'/ζ)^{(2k−1)}(½)   (all-ρ; orbit normalization halves each)
- POLE+ZETA+BETA = S_k^A (archimedean), cross-checked to the polygamma form (Formula 183/184) at 1e-121; PRIME = S_k^P (prime / log-derivative of ζ at the seam)
- β = Dirichlet beta, β(2k) = 4^{−2k}(ζ(2k,¼)−ζ(2k,¾)) (Hurwitz); ζ(2k) even zeta value; T_k from the zero divisor
- evaluated on the genuine residual direction (λ_min of [T_{i+j+1}]|_{u^⊥}, p(−4)=0 ⟹ Q_pole→0), d=4..8: even-ζ is the sole positive protector, β/Catalan is ~equal-and-opposite, prime is sub-dominant (matches only the arch-even net) — a two-stage ζ-vs-β cancellation closed by the prime, surviving positivity = λ_min. On the pole direction p_d≈0.97u the four are in ratio −4:1:1:2 (the pole cancellation). Script: computations/2026-06-21-connes-fused-split-pd.py

**Formula 186**
character (mod 4) decomposition of the arch budget:   S_k^A = 2^{2k+1} − 2^{−2k}ζ(2k,¼);   ζ(2k,¼)±ζ(2k,¾) = 4^{2k}(1−2^{−2k})ζ(2k) [principal, all odd] resp. 4^{2k}β(2k) [χ₄];   so ZETA_k = −2^{2k−1}Σ_{m odd}m^{−2k} (principal), BETA_k = −2^{2k−1}β(2k) (χ₄)
- ζ(s,a) = Hurwitz zeta; the trivial-zero tower sits at the 1-mod-4 reciprocal points (|w|=(4j+1)/2); β(2k)=L(2k,χ₄), χ₄ the odd character mod 4; identities verified to machine precision
- the residue-class (1 mod 4) budget R_d^A is PD (positive measure), but the character split is NOT termwise positive: inertia(H^ζ)=(d+1,0) PD (all-odd-integer budget) while inertia(H^β)=indefinite (≈(d−1,⌈d/2⌉), stable min eig ≈ −0.226). So decomposing by character breaks manifest positivity — positivity lives in the residue-class measure cone, not the character basis. Script: computations/2026-06-21-connes-character-sectors.py
