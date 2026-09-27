# Exterior spectral reader forced by the flat Gamma gap

- **ID:** stc-flat-gap-exterior-spectral-reader
- **Stage:** 3-formalized
- **Type:** exact source polarization and nonclosability theorem
- **Routes:** STC, RHist, Gamma-six/Sonin source lift
- **Status:** [PROVED ON PAPER] [FORMALIZED IN LEAN] [NOT AN RH PROOF]

## The source-selected spectral band

Fix a nonzero horizontal grade g, put a=|g|, and let x_p=log p. The [unique all-prime flat gap correction](stc-hyperbolic-gap-flat-completion.md) and its [exact packet inertia](stc-hyperbolic-gap-krein-signature.md) are

    K_g(x,y)=sinh(a(x-y)/2)/(a(x-y)/2)
            =(1/a)∫_[-a/2,a/2] exp(u(x-y)) du.

Take the real Hilbert space H_a=L²([-a/2,a/2],du/a), its reflection Jf(u)=f(-u), and the entire exponential feature f_x(u)=exp(ux). Then

    K_g(x,y)=⟨f_x,Jf_y⟩,
    H_g(x,y)=⟨f_x,f_y⟩=K_g(x,-y)
            =sinh(a(x+y)/2)/(a(x+y)/2).                   (1)

Thus the indefinite gap kernel is an exact reflected Hilbert pairing, while H_g is positive semidefinite. Splitting H_a into even and odd functions gives its canonical Krein polarization:

    K_g(x,y)=(2/a)∫_[0,a/2]
      [cosh(ux)cosh(uy)-sinh(ux)sinh(uy)] du.            (2)

This is a structural reflection, not an asserted Osterwalder--Schrader positivity law for the full arithmetic source. The positive kernel in (1) changes x-y to x+y; no congruence makes the original K_g positive.

## Theorem: canonical seam is an exterior, nonclosable reader

At a Xi-zero fibre ρ=1/2+g+iτ, the corpus's literal canonical prime seam obeys

    u_p(ρ)=-2 p^(-1/2+iτ) x_p sinh(g x_p).             (3)

Put v_p=p^(-1/2+iτ)f_(x_p) in the complexification of H_a. For every p, v_p≠0 and

    ‖v_p‖²=p^(-1) sinh(a x_p)/(a x_p),
    |u_p(ρ)|/‖v_p‖
      =2 x_p sinh(a x_p)/sqrt[sinh(a x_p)/(a x_p)].     (4)

For a x_p≥log 2, sinh(a x_p)≥exp(a x_p)/4 and sinh(a x_p)≤exp(a x_p)/2, so

    |u_p(ρ)|/‖v_p‖
      ≥sqrt(a/2) (log p)^(3/2) p^(a/2) →∞.              (5)

Consequently any linear functional on a subspace containing every v_p and assigning v_p↦u_p(ρ) is **not closable** in the H_a norm. Indeed choose primes p→∞ and set z_p=v_p/u_p(ρ). Equation (5) gives z_p→0 in H_a, but every such functional has value 1 on z_p. Equivalently no bounded or closed Hilbert-space functional, and no restriction of a closable one, can supply the canonical seam. For a finite packet containing p, every bounded functional matching the seam has norm at least the right side of (5); this lower bound diverges cofinally.

The mechanism is exact, not merely an asymptotic mismatch. The source feature has spectral parameter u only in [-a/2,a/2], whereas

    x sinh(gx)=sign(g)[f'_x(a)-f'_x(-a)]/2,
    f'_x(u)=x exp(ux).                                  (6)

The seam is a first-derivative evaluation at **twice the source band edge**. Formula (6) is valid on the analytic exponential family, but those outside-band evaluations are not continuous or closable in its L² band norm. The critical half-density and vertical phase in (3) multiply both feature and target equally and cancel from (4), so neither repairs the obstruction. At g=0, the seam and reader vanish; the theorem is deliberately restricted to g≠0.

### Stronger all-prime theorem: widening any compact band still fails

The preceding single-prime norm argument uses the particular source band [-a/2,a/2]. One might widen it until the points ±a enter the band. **That does not yield a bounded reader on all prime labels.** More generally, for any finite complex Borel measure ν with compact real support, the equalities

    ∫ exp(u log p) dν(u) = -2(log p)sinh(g log p)        (7)

cannot hold for every prime p when g≠0. Consequently no bounded functional on L²(μ), for any finite positive compactly supported real spectral measure μ, can map every exponential prime feature to its canonical grade charge. The same holds after multiplying both sides by the common nonzero critical half-density and vertical phase.

Here is a dependency-closed proof. If (7) held, set

    F(z)=∫ exp(uz)dν(u)+2z sinh(gz).

Compact support makes F entire with a global finite-exponential-type bound: if supp ν⊆[-b,b], then |F(z)|≤‖ν‖exp(b|z|)+2|z|exp(a|z|)≤C exp((max(a,b)+1)|z|). It vanishes at every prime logarithm. The corpus already proves the exact uniqueness theorem eq_zero_of_exponentialType_of_primeLog_zeros in PrimeLogExponentialTypeUniqueness.lean, using Jensen zero counting and Chebyshev's prime lower bound; hence F is identically zero. On z=it, however, the integral has modulus at most ‖ν‖ while |2it sinh(igt)|=2|t sin(gt)| is unbounded: take t=(π/2+2πn)/a, adjusting sign when g<0. Contradiction. For the Hilbert corollary, Riesz representation sends a bounded functional to a vector w∈L²(μ); the finite complex measure dν=conj(w)dμ has the required compact support and finite total variation.

This stronger theorem changes the interpretation of (6). The original half-band gives an explicit exponential norm blow-up, but **no finite band enlargement can turn the all-prime derivative evaluation into a bounded Hilbert observable**. A functional defined on the span of all prime features would be unbounded there, since a bounded functional on that span extends to the whole Hilbert space; every unbounded scalar functional on a normed domain is nonclosable by rescaling vectors with unbounded value-to-norm ratio. Prime-log sampling is so dense that it uniquely determines the entire transform, forcing the distributional derivative-of-point-mass target even when its points lie inside the band. A viable repair must change the topology or the source-to-target operation, not merely widen a compact L² spectral interval.

### Finite-order and Gaussian carrier extension

Compact support is unnecessary for the uniqueness argument. Let ν be any finite complex measure on the real spectral line whose bilateral Laplace transform Lν(z)=∫exp(uz)dν(u) exists as an entire function of **finite order**. If Lν(log p)=x_p sinh(gx_p) for every prime, then Lν(z)-z sinh(gz) is entire of finite order and vanishes on all prime logs. The corpus's stronger eq_zero_of_exponentialPower_of_primeLog_zeros theorem forces equality everywhere. On the imaginary axis Lν(it) is bounded by the total variation of ν, whereas |it sinh(igt)|=|t sin(gt)| is unbounded. Thus no such finite measure represents the seam.

This includes a natural **noncompact Gaussian spectral Hilbert space**. Let μ_σ be centered Gaussian probability measure of variance σ²>0, and H_σ=L²(μ_σ). Every w∈H_σ gives the entire readout

    F_w(z)=∫w(u)exp(uz)dμ_σ(u),
    |F_w(z)|≤‖w‖₂ exp(σ² (Re z)²)≤‖w‖₂ exp(σ²|z|²),
    |F_w(it)|≤‖w‖₂.                              (8)

The first bound is Cauchy--Schwarz and the exact Gaussian moment E[exp(2 Re(z) U)]=exp(2σ²(Re z)²). Local versions of the same bound justify differentiation under the integral, so F_w is entire. The target z sinh(gz) also has finite order, hence the preceding contradiction applies. Therefore no bounded functional on H_σ agrees with the grade current on all prime exponential features; by Hilbert extension, any matching functional on their span is nonclosable. This is stronger than the source-band one-feature estimate: even when Gaussian feature norms grow faster than the target at each individual large prime, their **joint all-prime interpolation** still cannot be bounded.

The exact boundary is a topology/analytic-order boundary, not a spectral-width boundary. A finite-order entire finite-measure transform, including every Gaussian carrier in (8), cannot implement the transport tangent. This does not rule out an infinite-order entire, meromorphic, nonlinear or distributional source operation, and it does not show that one of those operations satisfies an RH-producing bound.

### Transport-current interpretation

The flat one-prime potential itself is the finite atomic Laplace transform of m_g=(δ_g+δ_(-g))/2:

    cosh(gx)=∫ exp(ux) dm_g(u).

Its horizontal derivative is the **transport tangent** of those moving atoms. For every smooth test φ,

    (d/dg)∫φ dm_g=[φ'(g)-φ'(-g)]/2,

and with φ(u)=exp(ux) this is x sinh(gx). This is a first-order distribution, not a finite measure. Equation (7) proves that no different compactly supported finite measure can secretly reproduce the same tangent on all prime tests. Thus the algebraic source flattening makes a state, but the physically required seam is its grade **current**. Merely assigning a finite positive transport kinetic energy to the two moving atoms would not select the critical line: their velocities have unit magnitude at every nonzero g. Any successful conservation or positivity law must also use the arithmetic phase and the Xi-zero fibre.

## Consequence for the proof architecture

The source-selected correction cannot be interpreted as a positive Hilbert Gram kernel, and its canonical charge cannot be recovered even by a closable functional after the reflection-positive change of kernel. A viable source-to-Sonin lift must supply a **stronger analytic test-space topology**, a genuinely singular distributional evaluation, or a different source-derived operation outside the finite-order measure-transform class. Its operator cost in the original flat band grows at least as (5) on every single large-prime feature; any claimed bounded transfer must exhibit an independent cancellation or renormalization that pays that cost while retaining the phase and Xi-divisor dependence.

This identifies the type and quantitative scale of the missing law. It does not prove the law, bound the Sonin Calkin class, or exclude off-line Xi zeros. The corpus already has a different nonclosable Euler *prime-boundary* reader in [stc-prime-boundary-height-fibers.md](stc-prime-boundary-height-fibers.md); (3)--(6) instead concern the **horizontal grade spectral band** forced by the flat Gamma gap. Their interaction has not been established.

## Audit

- Literal gap correction, prime-only uniqueness and seam formula: linked flat-completion card. Source pair and seam definitions are in DeningerGammaAllPrimeStokesPairBridge.lean and XiPrimeSeamCoherenceCollapse.lean.
- The integral and norm formulas follow by integrating real exponentials. The ratio bound uses only the displayed elementary hyperbolic inequalities and unboundedness of primes. No numerical computation or RH input is used.
- The all-prime finite-order uniqueness input is already formalized in PrimeLogFiniteOrderUniqueness.lean. The new leaf [STCFlatGapPrimeLogReaderNoGo.lean](../../../../formal/GaloisForLFunctions/RHTower/STCFlatGapPrimeLogReaderNoGo.lean) Lean-proves that a finite-order entire candidate agreeing with the grade current at every prime log cannot have bounded imaginary-axis trace. The compact/Gaussian Laplace growth and bounded-trace specializations, the Riesz Hilbert corollary, the band Hilbert space with its reflection and Krein polarization, the seam norm ratio (4)--(5), nonclosability and the transport current are formalized in STCFlatGapMeasureReaderNoGo.lean and STCFlatGapSpectralBand.lean; see the certificate. Deep corpus searches for the combined mechanism and related source/quotient lemmas were partial; no exact combined theorem was found. No external priority claim is made.

## Log

- 2026-09-27: band Hilbert space `L²([-a/2,a/2],du/a)` with reflection, positive Gram, reflected pairing and Krein polarization (1)--(2); seam formula (3), norm ratio (4), lower bound (5), norm cost, no bounded reader and nonclosability; band-edge derivative (6); compact-band measure no-go (7) and its Riesz Hilbert corollary; finite-order and Gaussian carrier no-go (8); transport current formalized unconditionally (`STCFlatGapSpectralBand.lean`, `STCFlatGapMeasureReaderNoGo.lean`, with `STCFlatGapPrimeLogReaderNoGo.lean`); certificate `stc-flat-gap-exterior-spectral-reader-formalized.md`; moved to stage 3.
