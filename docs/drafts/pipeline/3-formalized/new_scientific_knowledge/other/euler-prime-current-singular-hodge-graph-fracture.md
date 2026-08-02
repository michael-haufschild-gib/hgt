# Euler prime-current singular Hodge graph fracture

- **ID:** `euler-prime-current-singular-hodge-graph-fracture`
- **Status:** formalized unconditionally in Lean 4
- **Route:** L (Calderón--Witt/Hodge)
- **Date:** 2026-08-02
- **Parents:** `EulerPrimeCurrentClockLaw`,
  `EulerPrimitiveCommonTestBoundaryScore`,
  `EulerPrimitivePolarizedHodgeBetaTransgression`,
  `EulerPrimitiveCommonTestPolarizedReflectionRigidity`
- **New statement:** the literal positive von--Mangoldt prime-power current already carries the
  singular Hodge graph-domain fracture at every finite pole scale.  After the source-forced Hodge
  size bias, the reflected endpoint current is summable exactly at zero modular displacement.

## 1. Literal source object

Fix a real pole scale \(\sigma>1\), and put

\[
 \varepsilon=\sigma-1>0,
 \qquad
 x_\sigma(n)=\varepsilon\log n.
\]

Let

\[
 A(\sigma)=\sum_{n\ge1}\Lambda(n)n^{-\sigma}>0,
 \qquad
 \mu_\sigma(n)=\frac{\Lambda(n)n^{-\sigma}}{A(\sigma)}.
\tag{1}
\]

The already constructed Euler clock theorem says that \(\mu_\sigma\) is a probability law and
that the pushforward by \(x_\sigma\) converges weakly to the unit exponential law as
\(\sigma\downarrow1\).

The moving endpoint character at real spectral direction \(a\) is

\[
 M_{\sigma,a}(n)=e^{-a x_\sigma(n)}.
\tag{2}
\]

Hence its unsquared reflection-odd source coordinate is

\[
 D_{\sigma,a}(n)
 =M_{\sigma,-a}(n)-M_{\sigma,a}(n)
 =e^{a x_\sigma(n)}-e^{-a x_\sigma(n)}.
\tag{3}
\]

The source-forced Hodge scale at clock value \(x\) is

\[
 q_H(x)^2=e^x-1.
\tag{4}
\]

Define the positive prime-power Hodge graph-energy coordinate

\[
 G_{\sigma,a}(n)
 =\mu_\sigma(n)q_H(x_\sigma(n))^2
       \lvert D_{\sigma,a}(n)\rvert^2.
\tag{5}
\]

Every ingredient in (5) is source-side and exists before selection of a Xi divisor: the literal
von--Mangoldt current, its pole-scaled clock, the two reflected endpoint characters, and the
odd-Hodge likelihood ratio.  No analytic continuation or divisor coordinate enters the
definition.

## 2. Exact discrete-to-continuous comparison

Under the Euler-clock limit, the reference density is the compact head
\(h(x)=e^{-x}\).  Multiplication by (4) changes it pointwise to the Hardy tail:

\[
 q_H(x)^2h(x)=(e^x-1)e^{-x}=1-e^{-x}=\tau(x).
\tag{6}
\]

Consequently (5) is the finite-pole-scale source precursor of the already constructed continuous
Gamma/Hardy graph density

\[
 \tau(x)\lvert e^{ax}-e^{-ax}\rvert^2.
\tag{7}
\]

Equation (6), not scalar analytic continuation, is the comparison mechanism.  It also identifies
the singularity: \(q_H\) is unbounded at the source horizon.  Weak convergence of the unweighted
Euler clock cannot pass through this multiplier without a graph-domain theorem.

## 3. Finite-scale source-domain theorem

### Theorem 3.1 (prime-current singular Hodge graph fracture)

For every real \(\sigma>1\) and every real \(a\),

\[
 \boxed{
 \sum_{n\ge1}G_{\sigma,a}(n)<\infty
 \quad\Longleftrightarrow\quad
 a=0.}
\tag{8}
\]

Thus the singular Hodge transform of the reflected endpoint current leaves the positive
prime-power source Hilbert leg at every nonzero displacement already at each finite pole scale.
The fracture is not created by the cofinal limit.

### Proof

If \(a=0\), (3) vanishes identically, so every term in (5) is zero.

Assume \(a\ne0\), and put \(b=|a|>0\).  Squaring makes (5) even in \(a\), so it suffices to work
with \(b\).  Restrict the sum to the prime slice.  For a prime \(p\),
\(\Lambda(p)=\log p\), and with \(x_p=\varepsilon\log p\), direct factorization gives

\[
\begin{aligned}
 G_{\sigma,b}(p)
 &=\frac{\log p}{A(\sigma)}p^{-\sigma}
      (e^{x_p}-1)(e^{b x_p}-e^{-b x_p})^2\\
 &=\frac{\log p}{A(\sigma)p}
      e^{2b x_p}(1-e^{-x_p})(1-e^{-2b x_p})^2.
\end{aligned}
\tag{9}
\]

Every prime satisfies \(p\ge2\), hence \(x_p\ge\varepsilon\log2>0\).  Define

\[
 c_1=1-e^{-\varepsilon\log2}>0,
 \qquad
 c_2=1-e^{-2b\varepsilon\log2}>0.
\tag{10}
\]

Monotonicity of the exponential, \(\log p\ge\log2\), and
\(e^{2b x_p}\ge1\) yield

\[
 G_{\sigma,b}(p)
 \ge
 \frac{\log2}{A(\sigma)}c_1c_2^2\frac1p
 =:C_{\sigma,b}\frac1p,
 \qquad C_{\sigma,b}>0.
\tag{11}
\]

If the full series in (8) were summable, its nonnegative prime slice would be summable.  By
(11), \(\sum_p C_{\sigma,b}/p\) would then converge.  Division by the nonzero constant
\(C_{\sigma,b}\) would imply convergence of \(\sum_p1/p\), contradicting Euler's prime-harmonic
divergence.  Therefore the graph energy is nonsummable for every \(a\ne0\).  This proves (8).
\(\square\)

## 4. Abscissa interpretation

Expanding the dominant orientation of (5) on the prime slice cancels the safe source damping:

\[
 p^{-\sigma}e^{x_p}e^{2|a|x_p}
 =p^{-1+2|a|\varepsilon}.
\tag{12}
\]

Thus the Hodge size bias moves one positive prime-flux component strictly across the exponent-one
abscissa whenever \(a\ne0\).  The unweighted endpoint Green trace remains in its safe Euler
half-plane, but the positive graph norm does not.  Meromorphic continuation of the signed scalar
trace cannot alter (11), because (5) is label-retaining and nonnegative.

## 5. Route-L consequence

This theorem constructs the missing literal source-side singular transport and proves its exact
domain on every reflected endpoint character.  It changes the Route-L frontier in two ways.

1. The continuous condition
   \(\tau(t)|e^{at}-e^{-at}|^2\in L^1(0,\infty)\) is not merely an imposed boundary model.  It is
   the Hodge-size-biased graph condition of the actual positive prime-power current.
2. Safe endpoint reconstruction of the completed Xi trace cannot imply graph landing by analytic
   continuation alone.  The singular multiplier crosses the positive prime-flux abscissa at every
   finite \(\sigma>1\) when \(a\ne0\).

The theorem does **not** prove that every Xi divisor has \(a=0\).  The remaining producer theorem
is now sharper: it must force the divisor fibre's unsquared reflected source coordinate to vanish
before Hodge size bias, or supply a genuinely relation-valued cancellation that survives the
positive labelled graph norm.  Repackaging the continued scalar Xi trace cannot do this.

## 6. Novelty audit

### Internal corpus

Targeted searches covered:

- `EulerPrimeCurrentClockLaw` (positive prime-power probability and exponential weak limit),
- `EulerPrimitiveCommonTestBoundaryScore` (finite-scale endpoint characters),
- `EulerPrimitivePolarizedHodgeBetaTransgression` (continuous Hodge scale),
- `EulerPrimitiveCommonTestPolarizedReflectionRigidity` (continuous tail-energy fracture),
- CCM fixed-shift exponential-type rigidity,
- von--Mangoldt/Gamma summability thresholds and Sonin prime-flux divergence.

No declaration or paper was found that applies the singular Hodge likelihood ratio to the literal
finite-\(\sigma\) Euler prime-current probability and proves the iff (8).  Existing modules contain
the ingredients on opposite sides of the source/boundary comparison, not their graph-domain weld.

### External literature

Searches covered co-Poisson/Sonine spaces, Mellin size bias, convergence under biasing, prime-flux
Dirichlet abscissae, and weighted \(L^2\) RH criteria.  Burnol's co-Poisson/Sonine work supplies the
source-space context; general Mellin-bias literature explains why weak convergence needs uniform
integrability under unbounded biasing.  No exact result matching the prime-power Hodge energy
(5), the factorization (9), or the finite-scale iff (8) was located.

The individual ingredients are classical or already formalized.  Claimed novelty is the exact
source-faithful conjunction (5)--(12) and its Route-L consequence, not Euler's divergence, Mellin
size bias, or the continuous exponential integral separately.

## 7. Lean formalization

Formalized module:

```text
GaloisForLFunctions.RHTower.EulerPrimeCurrentSingularHodgeGraphFracture
```

Verified unconditional declarations:

- discrete Hodge scale and reflected endpoint difference;
- exact comparison with `eulerPrimitiveBoundaryHodgeScale` and
  `eulerPrimitiveBoundaryEndpointFeature`;
- nonnegativity of every source energy term;
- prime-slice lower bound by a positive constant times `1 / p`;
- summability iff zero displacement;
- Xi-fracture specialization, without assuming RH.

Direct `lake env lean` elaboration and targeted module build pass.  `#print axioms` reports only
`propext`, `Classical.choice`, and `Quot.sound`; there is no project-specific axiom or RH assumption.
