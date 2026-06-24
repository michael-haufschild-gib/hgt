# 09 — The Core Formulas and What They Say

> **Scope.** The irreducible formulas of the programme — each distinct formula stated once, in a single
> canonical notation, with the one claim, conjecture, or meaning it carries. Formulas that say the same
> thing in different dress are stated together as the single thing they mean; what remains is the minimal
> set from which the rest follow. Register tags (`[PROVED]` / `[BRIDGE]` / `[OBSERVED]` / `[CONJECTURE]`
> / `[OPEN CORE]`) as the content assigns them. No proof of RH.

---

## The constraint and its seam

**The constraint.** `[PROVED]`
```
   ι : s ↦ 1−s,   ι² = id,   Fix(ι) = { 1/2 },   Fix(ι∘conj) = { Re s = ½ }.
```
The completed object is governed by a single order-2 reflection — a constraint generating ℤ/2, not a
one-parameter flow. The holomorphic reflection fixes only the point `s=½`; the seam `Re s = ½` is the
fixed line of the anti-holomorphic reflection `s ↦ 1−s̄`. The map, its order, and both fixed loci are one
constraint package; the critical-line locus uses the conjugated reflection.

**The functional equation, four faces.** `[PROVED]`
```
   ξ(s) = ξ(1−s)  ⟺  Λ(s) = Λ(1−s)  ⟺  θ(1/t) = √t · θ(t)  ⟺  Poisson summation (Ш̂ = Ш).
```
One statement in four dresses. The ξ- and Λ-forms are exactly equivalent (the extra `½s(s−1)` factor is
itself reflection-invariant). It is the constraint that fixes the object, and it is RH-blind: a function
can satisfy it and still have off-line zeros.

**The reflection on the prime side.** `[PROVED]`
```
   s ↦ 1−s   ⟹   p^{−s} ↦ p^{−1}(p^{−s})^{−1},   i.e.   θ_p ↦ −θ_p   (zero defect).
```
On each prime lane the constraint acts by inversion (equivalently, negation of the lane phase), with no
obstruction. The reflection has no such defect-free realization on the archimedean side — so the
functional-equation obstruction is purely archimedean.

**The seam seen on a prime lane.** `[PROVED]`
```
   | p^{−s} | = p^{−½}   ⟺   Re(s) = ½.
```
Every prime lane sits at its self-dual modulus exactly on the seam.

---

## The weld and the operator geometry

**The weld.** `[PROVED — BRIDGE]`
```
   ω = d log ξ = H ds,   H(s) = ∂_s log Λ(s) = ∂_s log Γ∞(s) + ζ'/ζ(s),   carrier  M_Ξ = −Ξ'/Ξ.
```
The object is a logarithmic transport connection: the weld is the archimedean term `∂_s log Γ∞` plus the
prime term `ζ'/ζ` — the two native generators made literal. As a one-form it is reflection-odd
(`H(s) = −H(1−s)`) and divisor-sensitive. The recentred carrier `−Ξ'/Ξ` is the same weld up to the
reflection-symmetric rational `1/s + 1/(s−1)`. Everything downstream is built on this one split.

**The prime difference base.** `[PROVED]`
```
   σ_p : x_p ↦ p^{−1} x_p,   τ_p = σ_p − 1.
```
Rank-1 shifts with constant multipliers: per-lane holonomic, decoupling, every lane a coboundary.

**The affine group and its curvature.** `[STRUCTURAL / PROVED]`
```
   ⟨1, r⟩ = 𝔾_a ⋊ 𝔾_m   (𝔾_m = ∂_s dilation, 𝔾_a = M_p translation-by-log p),
   [∂_s, M_p] = − log p,    [∂_s, σ_p] = 0.
```
The weld lives on the affine `ax+b` group. The curvature `−log p` is object-independent — the same for
every object on this geometry — so the hypertranscendence and any RH content live in the holonomy, not
the curvature. The order-preserving affine orbit is the flat, RH-blind part; the content is the
transverse seam `[𝔾_a, 𝔾_m]`.

**The generators on the boundary modes.** `[PROVED]`
```
   σ_p · e_m = p^{−m_p} e_m,
   ∂_s = − Σ_p (log p) θ_p,   so  ∂_s · e_m = −(log n) e_m   on the ζ-module,
   ∂_s|_{M_∞} = − ½ log π + ½ ψ(s/2)   on the archimedean module.
```
Both generators are Fourier-diagonal and carry no combination modes. The dilation is a mere relation on
the ζ-module but a genuinely new generator on the archimedean module; the seam is carried entirely by the
digamma term `½ ψ(s/2)`.

**The passport.** `[PROVED]`
```
   Π(S) = ( |S|, Σ_{m∈S} m ),   universal shift  −|S| log p.
```
Every affine tangent-volume observable factors through the passport; blocks with the same passport have
the same trace. So any determinant-volume or summed-Lyapunov observable is RH-blind until the passport is
subtracted — the content is the shape beyond it.

**The shift equation and the coboundary gauge.** `[PROVED]`
```
   f = g · e^{zλ}  solves the shift equation;    a constant-up-to-coboundary multiplier  a = c · σ(g)/g.
```
The rank-1 shift equation is elementarily solvable; this is why each prime lane gauges to a constant.

---

## The two places and the cohomology

**The seam decomposition.** `[PROVED — BRIDGE]`
```
   C5 = weld = { the one non-CC place } × { the CC places }.
```
The weld is the product of the single archimedean place (constant-up-to-coboundary fails there) and the
prime places (each a pure coboundary), glued by the functional equation. No single side can pose this
joint statement.

**Why the archimedean place is the non-CC one.** `[PROVED]`
```
   a_Γ(s) = Γ_ℝ(s+2)/Γ_ℝ(s) = s/2π,   div(a_Γ) = [0] − [∞],   σ-orbit degree = +1 ≠ 0.
   a is CC  ⟺  a = c · σ(g)/g  ⟺  orbit-degree(a) = 0 on every orbit.
```
The archimedean shift multiplier is exactly the gamma-recurrence ratio, and that ratio carries a zero and
a pole — orbit-degree `+1`, not `0`. So it is the unique place where constant-up-to-coboundary fails;
every prime lane is orbit-balanced.

**The cocycle layer.** `[PROVED]`
```
   ρ_∞(s) · ρ_ζ(s) = 1,    additive 1-cocycles:  τ_p a_q = τ_q a_p,    d1 ∘ d0 = 0,    g_p = g_p^{−1} ⟹ g_p = ±1.
```
The functional equation is a cocycle product relation whose entire defect is archimedean; the Koszul
complex composes to zero; and an involutive prime multiplier can only be `±1` — so the prime structure
carries no polarization.

**The realization class, and why it is not RH.** `[PROVED]`
```
   RH  ⟺  archimedean-completed Koszul acyclic  ⟺  ω = 0 ∈ H²(G_L),     but     ω = 0  ⇏  RH.
```
The completed acyclicity is equivalent to RH; the bare vanishing of the realization class is not — the
plain multiplicative complex is acyclic for free. This is the load-bearing caveat that keeps the two
apexes (positivity and transcendence, below) distinct: they are joined only at the seam.

**The field with one element.** `[PROVED]`
```
   F₁ exists  ⟺  (orbit-imbalance D = 0)  ∧  (corank finite);    over ℚ:  D = +1, corank = ∞.
```
Both conditions fail over ℚ, so the single Frobenius is missing.

---

## The corank — the seam as one number

**The corank and its three faces.** `[PROVED — BRIDGE]`
```
   corank < ∞  ⟺  holonomic;     trdeg(T_{s_0}) ≤ corank;     dim W = corank.
   corank over ℚ = ∞,    corank over F_q = 1,    gap = ∞ − 1.
```
One number with three faces — holonomicity, continuation-transcendence, weight-space dimension. Over the
rationals it is infinite (the primes give infinitely many independent Frobenii); over a function field it
is `1` (one Frobenius). The gap `∞ − 1` is the missing single Frobenius — the archimedean seam.

**Linear floor below the algebraic apex.** `[PROVED — BRIDGE / floor]`
```
   corank = ∞  ⟺  { log p } ℚ-linearly independent  ⟺  { m : Σ_p m_p log p = 0 } = { 0 }.
   trdeg ≤ corank  is strict in general   (e.g. { π, π² } : trdeg 1 < corank 2).
   | m · ℓ | ≥ c_B · H(m)^{−κ_B}.
```
The corank is an inherently linear invariant — equivalent to linear independence of the prime logs, with
an effective lower bound on linear forms in them. Linear independence does not force algebraic
independence; the inequality `trdeg ≤ corank` is only an upper bound, and it is strict. So the corank
floor sits one level below the value apex.

**Robustness.** `[PROVED]`
```
   g = (p^{−1})_p  has infinite-dimensional Zariski closure when the relation lattice is 0;
   adjoining ∂_s leaves the rank = the cardinality of the primes.
```
The infinite corank is robust: the archimedean generator does not supply the missing Frobenius.

---

## The faithful index and the positivity wall

**The faithful index.** `[PROVED — BRIDGE]`
```
   κ₋ = #{ off-line zero-pairs } = 2 · #{ off-line zeros },    one off-line zero ⟹ κ₋ = 2.
```
The RH-bearing quantity is a faithful signed integer — the negative index of the completed carrier,
counting off-line zeros with reflection multiplicity. A measured density or variance is blind to
density-zero off-line dust; only the integer index can decide RH. **The scalar Weyl gap `s_d` is the
*rank-one shadow* of `κ₋`, not a substitute for it `[VERIFIED — comp81/72]`:** a fake (reversed prime sign)
can have `κ₋=2` while `s_d>0` (the single Γ-atom repairs only one negative square; `H^0` is not PSD, the
scalar misses it). So even the moment-level `s_d=0` gate is a height-/rank-limited shadow of the integer
`κ₋` — confirming that the faithful object is the index, not any scalar.

**The one wall, its many names.** `[OPEN CORE]`
```
   RH  ⟺  κ₋ = 0
       ⟺  Q_W ⪰ 0   (the explicit-formula quadratic form, signature (1|∞), one archimedean direction)
       ⟺  m_ξ ∈ ℕ₀
       ⟺  det H_d ≥ 0  for all d, t   (uniform Hankel / Laguerre–Pólya / Jensen positivity)
       ⟺  Ω ≽ Π   (the archimedean part dominates the prime part)
       ⟺  ι acts unitarily
       ⟺  supp μ_ξ ⊂ { Re s = ½ },   μ_ξ = (1/2π) Δ log|ξ|
       ⟺  D₂ = Σ_ρ (β − ½)² = 0.
```
A single positivity wall, written many ways; the names are coordinate charts of one divisor. The `d = 2`
leader (`log|ξ(½+it)|` concave) is classical; the uniformity in `d` — equivalently the all-order
positivity below — is the open core, numerically a sparse, sub-grid, collective resonance, not a
pointwise gap.

**The cleanest coordinate (the last bridge).** `[OPEN CORE]`
```
   y_ρ = −(ρ − ½)^{−2},    T_k = Σ_ρ m_ρ y_ρ^k   (absolutely convergent for k ≥ 1; T_0 = ∞ excluded).
   RH  ⟺  every y_ρ > 0  ⟺  {T_k}_{k≥1} a Stieltjes moment sequence
       ⟺  the shifted Hankel towers [T_{i+j+1}], [T_{i+j+2}] are positive-definite to all orders.
```
A zero is on the line exactly when `y_ρ` is a positive real, so all zeros are on the line exactly when the
moment sequence `{T_k}` lies on the positive axis — a moment problem. The forward sum `Σ(ρ−½)^k`
diverges; this reciprocal chart is the one that converges from the first order. The open content is to
force the positivity from the completion and the explicit formula without assuming where the zeros are.

**The explicit-formula form of the wall.** `[BRIDGE]`
```
   Q_W = the explicit-formula distribution,   signature (1|∞),   the one positive direction  V_arch = Re ψ.
   sigNeg of the Bezoutian / Schur–Cohn form = winding = #roots inside;   κ₋ is this index for the carrier.
   Ω ≽ Π :   A_arch − Σ_{p∈S} P_p ≥ 0  as  S → all primes  ⟺  RH.
```
The wall written as the positivity of one quadratic form built from the explicit formula. Its signature
has exactly one positive (archimedean) direction; an off-line zero is a quantized negative direction,
counted by the same inertia that counts roots inside a contour.

**A witness, and a non-witness.** `[OBSERVED]`
```
   off-line zeros  ⟹  inertia (1, 0, 10),  κ₋ = 1     (a function with off-line zeros);
   ζ(2k+1) = ∫ y^k dν,  ν = Σ_m (1/m) δ_{1/m²} ≥ 0   ⟹  its Hankel tower is positive unconditionally.
```
A function with off-line zeros is caught by the faithful index, while a genuine Euler product stays
positive. The integer divisor gives an unconditionally positive tower — so positivity *there* is empty
of RH content; the content is the map from integers to zeros (the explicit formula), not the positivity
of the odd zeta values.

---

## The local geometry of zeros

**Zeros as source charges.** `[PROVED]`
```
   ξ'/ξ(s) ~ m_ρ/(s − ρ) + h(s);    (1/2πi) ∮ d log ξ = #zeros;    ∮ d arg = 2πi(#zeros − #poles).
   (1/2πi) ∮_{∂R} (ξ'/ξ) ds = 0  for every rectangle R strictly off the line  ⟺  RH.
```
A zero is a simple pole of the carrier; the connection counts source charge by winding. RH is exactly the
vanishing of the off-line contour charge.

**The Hadamard product.** `[PROVED]`
```
   ξ(s) = ξ(0) · e^{bs} · ∏_ρ (1 − s/ρ) e^{s/ρ},    ξ'/ξ(s) = b + Σ_ρ [ 1/(s−ρ) + 1/ρ ].
```
ξ has order 1. Quotienting the divisor out of the connection leaves a constant — so removing the zeros
removes exactly the hypertranscendence; the content of ξ is its divisor.

**The line curvature.** `[PROVED]`
```
   Φ_k(t) = Σ_ρ (½ + it − ρ)^{−k},  k ≥ 2;    Φ_2(t) = (d/dt)² log ξ(½ + it).
   RH ⟹ Φ_2 < 0  everywhere  ⟺  log|ξ(½+it)| concave.
   An off-line pair {½−β±iγ, β−½±iγ}:   (½−β+iτ)^{−2} + (β−½+iτ)^{−2} = 2(a²−τ²)/(a²+τ²)²,  a = |½−β|.
```
The transverse seam content is the higher-log-derivative family. Under RH the line curvature is
everywhere negative; an off-line pair forces a local convex window of half-width `a`. Concavity is the
necessary `d=2` leader of the positivity wall, not sufficient.

**The off-line detector.** `[PROVED]`
```
   C_a(τ) = 2(a² − τ²)/(a² + τ²)²,   C_a > 0 ⟺ |τ| < a,   ∫ C_a dτ = 0,   C_a(0) = 2/a²,   width ≈ a/2.
```
The off-line window is zero-area with a positive core and negative wings. A faithful detector must be
sign-changing and scale-matched at width `≈ a/2`; a broad average cancels it.

**A per-zero on-line test, and zero motion.** `[PROVED]`
```
   Φ_k(ρ)/Φ_k(1−ρ) = (n^{1−2β}/|χ|)^{1/m}   frequency-independent  ⟺  β = ½;    dρ/dε = −n^{−ρ}/ζ'(ρ).
```
The mirror-pair susceptibility ratio is independent of frequency exactly when the zero is on the line;
the residue `ζ'(ρ)` controls how a zero moves under a frequency perturbation.

---

## The value structure

**The power sums over the zeros.** `[PROVED]`
```
   P_k = Σ_ρ ρ^{−k}   (the coefficients of  −ξ'/ξ(s) = Σ_{k≥1} P_k s^{k−1}),
   M_k = Σ_ρ (ρ − ½)^k   (the forward seam sum — divergent),
   S_k = Σ_ρ (ρ − ½)^{−2k} = −k [w^{2k}] log Ξ   (the convergent seam chart),
   λ_n = − Σ_j C(n,j) (−1)^j P_j   (Li coefficients),   first negative at  n₀ = πγ/(4δ),  n₀δ/γ ≈ π/4.
```
The power sums over the zero divisor are one object in several charts, related by the Newton identities;
the Li coefficients are a triangular integer change of basis. The forward sum diverges — the reciprocal
chart is the convergent one. The Li chart turns negative first at a definite location.

**The seam values, split into constant-families.** `[PROVED]`
```
   Σ_ρ (ρ−½)^{−2k} = 2^{2k} − ¼(2^{2k}−1) ζ(2k) − 2^{2k−2} β(2k) − (2(2k−1)!)^{−1} (ζ'/ζ)^{(2k−1)}(½),
   μ_{2k+1} = Σ_ρ (ρ−½)^{−(2k+1)} = 0.
```
The even seam power sums have a closed form splitting into three arithmetically distinct families — the
`π`-periods `ζ(2k)`, the Catalan family `β(2k)` (not a `π`-period), and the prime-side log-derivatives —
a concrete value-relation. The functional equation kills all the odd seam sums.

**The transcendence apex.** `[OPEN CORE]`
```
   corank^{(T)} = ∞  for all T ≥ 2   ⟺   { log p } ℚ-algebraically independent   ⟺   trdeg = ∞.
   trdeg_ℚ{ Stieltjes(ζ_S) } = corank_ℚ{ log p : p ∈ S };    c_1 = Σ β_p log p;    ℚ({P_k}) ⊇ { ζ(odd) }.
```
The value axis: algebraic independence of the prime logs. The transcendence of the Stieltjes constants
equals the corank of the prime logs; at the linear level the zeros and prime logs are jointly
inseparable. The first open rung is degree two, open even for `{log 2, log 3}`. This is a separate apex
from the positivity wall — the realization class can vanish without RH — joined only at the seam. Even
the irrationality of `γ_E` is open.

**The external relation that singles out ζ.** `[PROVED]`
```
   Σ_ρ h(γ_ρ) = arch − Σ_p (log p) …    (the explicit formula).
```
A same-density random divisor shares ζ's seam-value rigidity; the one structure that distinguishes ζ is
its relation to the external set `{log p}`. This relation is the source of the explicit-formula quadratic
form, and the only thing that makes the integer-divisor positivity above RH-relevant.

**The function-field model.** `[PROVED — BRIDGE]`
```
   |ω| = √q  exactly,    ∏(1 − ωT) reflection-invariant,    e_k(S) = q^k e_k(S^{−1});
   normalized margin = 1 − q^{−½};
   polarization present ⟺ single Frobenius ⟺ corank 1 ⟺ F_q;
   over F_q:  trdeg(periods) = dim G,   dim W = corank = 1,   reflected constraint unitary on the critical locus ⟺ RH over F_q.
   arithmetic-progression divisor γ_n = n:  S_k = (−1)^k ζ(2k) ∈ ℚ·π^{2k},  π² + 6S_1 = 0,  5S_2 = 2S_1².
```
The solved model the number-field case is contrasted against: corank `1`, a single Frobenius, an exact
margin, and — at this one locus — the positivity apex and the transcendence apex coincide. A toy divisor
of integers collapses the seam values to exact algebraic relations the true ζ does not satisfy, locating
ζ's value-complexity in the Catalan and prime-side terms.

---

## The seam localized many ways (each RH-blind on its own)

**Convergence, variance, signature.** `[PROVED — BRIDGE]`
```
   𝓛(σ) = −Σ_p log(1 − X_p p^{−σ})  converges a.s.  ⟺  Σ_p p^{−2σ} < ∞  ⟺  σ > ½;
   Var(Re 𝓛) ~ ½ log log,    log|ζ(½+it)| / √(½ log log t) ⇒ 𝒩(0,1);
   additive Euler cocycle a bounded L²-coboundary  ⟺  σ ≥ ½;
   ‖ψ_s‖² = ζ(2σ)  changes signature at  σ = ½,    Fisher metric  g_F = (log ζ)''(2σ) ~ 1/(2σ−1)².
   the abscissa wall is  max(½, 1/k₀);    a crossover scale  σ* ∈ (½, 1).
```
Several independent facts pin the seam `½` — the abscissa of almost-sure convergence, the variance and
its Gaussian, the coboundary threshold, the norm-signature wall and its Fisher blow-up. Each is built
from the primes or from the gamma factor and says nothing on its own about where the zeros sit.

**The empirical carrier.** `[OBSERVED]`
```
   Δ(σ,t) = max(log|∂_s log Γ∞|, log|ζ'/ζ|) − log|∂_s log Γ∞ + ζ'/ζ|.
```
The one discriminating observable — how much phase the prime term must supply for the weld to close. The
true continuation produces a structured positive defect in the critical strip that finite Euler
truncations and random-phase surrogates do not, and that collapses for `σ > 1`. *(The experimental
battery measured this with the gamma factor `Γ∞` in place of the weld term `∂_s log Γ∞`; the canonical
weld defect uses `∂_s log Γ∞`, and the two are not literally equal.)*

**The true field is bounded away from every truncation.** `[CONJECTURE / OBSERVED]`
```
   Δ_{ζ'/ζ} → log 2  (true),  Δ_{(ζ'/ζ)_N} → 0  (finite);    d_transport ≥ c > 0;
   coupled co-failure excess ≥ c > 0;    λ₁(G_true) ≥ λ₁(G_finite) + c;    σ > 1 ⟹ (ζ'/ζ)_N → ζ'/ζ.
```
One phenomenon in four observables — the true weld is separated from every finite-Euler truncation in the
strip, by the phase defect, a transport metric, a coupled-reserve co-failure excess, and an
association-graph spectral gap — and all of it must vanish for `σ > 1`.

**The phase-space lift and the oriented structure.** `[OBSERVED; scalar form falsified]`
```
   θ = arg(ζ'/ζ),   O = log(1 + |ζ'/ζ|);    Cov(O, δV) > 0  (true) / < 0  (controls);    ∫ O dθ > c > 0;
   ω = dO ∧ dφ,   φ = arg(Γ∞ + ζ'/ζ);    ‖∂_t arg(Γ∞ + ζ'/ζ)‖  (an H^{1/2} phase seminorm).
```
In the correct phase-space coordinates the true lift has positive signed area while finite-prime is
anti-symplectic. The three oriented signatures are projections of one signed object; the naive scalar
realization is falsified (identical scalars can give opposite areas), so the oriented structure must be
the non-scalar holonomy form, plausibly summarized by a single phase-regularity seminorm.

**The coupled lanes.** `[CONJECTURE / OBSERVED]`
```
   K_q(σ, σ') = Corr( 𝟙_{Δ(σ+it) > q},  𝟙_{Δ(σ'+it) > q} ).
```
The σ-lanes are coupled by a non-product joint measure, to be captured by a continuum association kernel
with a spectral gap for the true field and none for productized or random controls.

---

## The scattering, period, and constraint readings

**The scattering form.** `[PROVED]`
```
   −(φ'/φ)(½ + ir) = 2[ (ξ'/ξ)(1 + 2ir) − (ξ'/ξ)(2ir) ]   — structurally  Ω − Π;
   κ₋ as an index:  bulk = finite places,  boundary = archimedean,   RH ⟺ Index = 0.
```
The weld read as archimedean minus prime — the scattering/index face of the positivity wall.

**Two more coordinates of the wall.** `[CONJECTURE]`
```
   K_MS(s,w) ~ (1 − Θ(s) Θ̄(w)) / (s + w̄ − 1) ∈ ℕ₀   ⟺   RH;
   RH  ⟺  F_ζ elliptic with period point interior to  D_∞ = Sp_∞(ℝ)/U(∞).
```
The same wall as a two-variable kernel in the Nevanlinna class, and as a period point interior to a
symmetric domain (an off-line zero becomes a boundary direction).

**The constraint metaphor.** `[analogy]`
```
   Ĥ Ψ = 0     (a constraint, no  iℏ ∂_t  flow term).
```
The object is fixed by a constraint with no clock, as in superspace and in holography (bulk fixed by
boundary): fixed by a constraint, not propagated by a flow.

**The founding negative theorem.** `[PROVED]`
```
   ∄ nonzero polynomial F :  F(s, Γ, Γ', …, Γ^{(n)}) ≡ 0   (and likewise for ζ);    HT ± (D-algebraic) = HT;
   ζ ∉ ℂ(s, { p^{−s} }).
```
Γ and ζ satisfy no algebraic differential equation: hypertranscendence is the absence of a generative
rule, so there is no founding flow to find. ζ is even differentially transcendental over the prime-flow
field — a generative founding principle is self-defeating. Adding any differentially-algebraic function
preserves hypertranscendence.

**A height datum.** `[OBSERVED]`
```
   M(L) = 1.176280818     (smallest known Mahler measure exceeding 1).
```
A height / transcendence-quantitative marker; the number-field analogue of the function-field margin
`1 − q^{−½}` is conjectural.

---

## Further identities, separators, and signatures

**The recentred completed object.** `[PROVED]`
```
   Ξ(w) = ξ(½ + w),   Ξ(w) = Ξ(−w),   divisor  𝒟 = { ρ − ½ }.
```
Recentring at the seam turns the functional equation into evenness; the divisor `𝒟` is the whole content.

**The digamma recurrence.** `[PROVED]`
```
   ψ(s/2 + 1) = ψ(s/2) + 2/s.
```
The companion of the gamma recurrence; it supplies the seam term `½ ψ(s/2)`.

**The two phase channels.** `[support]`
```
   φ'(T) = θ'(T) + π S'(T),    θ'(T) = ½ log(T/2π).
```
The total phase splits into the gamma / functional-equation channel `θ'` and the prime channel `π S'` —
the two channels are the two sources.

**The Euler-product log-coefficients are nonnegative.** `[OBSERVED]`
```
   c_n = Λ(n) ≥ 0     (the Dirichlet coefficients of  ζ'/ζ).
```
The log-derivative of an Euler product has all-nonnegative coefficients; a function without an Euler
product has many negative ones. The all-positive log-coefficient signature is the Euler product.

**The free cumulants are the odd zeta values.** `[OBSERVED]`
```
   κ_n = ζ(2n+1),    signs  κ_2 > 0, κ_4 < 0, κ_6 > 0, κ_8 < 0.
```
A value-side positivity instance, carrying no RH content of its own.

**The edge-derivative lower bound is transcendence-deep.** `[structural]`
```
   F^{(T)}(1) = (−1)^T Σ C_a ∏_p (log p)^{a_p}.
```
The values at the `s=1` edge are polynomials in the prime logs of every degree. The affine orbit yields
only the upper bound on their independence, so the lower bound is the algebraic-independence question
itself — the value apex, not reachable from the geometry.

**The spacing is GUE; the positivity margin is not local.** `[OBSERVED]`
```
   ⟨r⟩ = 0.611;     corr(log margin, gap) = −0.25.
```
The zero spacings follow the unitary ensemble, forced by the explicit formula rather than by
transcendence; the positivity margin of the wall is not controlled by the local zero gap — it is
collective.

**A necessary inequality for the wall.** `[OBSERVED]`
```
   g(n) = a_n² / (a_{n−1} a_{n+1}) → 1,    a_n = the Taylor coefficients of ξ.
```
The Turán ratio tends to one — a necessary condition for the Laguerre–Pólya positivity, not sufficient.
