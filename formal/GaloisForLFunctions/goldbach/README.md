# Goldbach in the objects of the RH research

Goldbach can be read through the same damped divisor source used by the RH
receiver. Its additive reflection also has exactly the mass–defect and even–odd
decompositions used throughout the positivity programmes. These are precise
translations of the problem; the source, kernel and quantifiers remain explicit.

The Lean declarations are in [RiemannHypothesisBridge.lean](RiemannHypothesisBridge.lean).

## One arithmetic source, two kernels

Use the existing source

\[
\tau_\varepsilon(k)=\sum_{d\mid k}\mu(d)d^{-\varepsilon}
 =\prod_{p\mid k}(1-p^{-\varepsilon})\quad(k>0),
\qquad \tau_\varepsilon(0)=0.
\]

It has \(\tau_0(k)=\mathbf1_{k=1}\) and
\(\partial_\varepsilon\tau_\varepsilon(k)|_0=\Lambda(k)\).
The latter is proved in
[DampedChebyshevTangentFormOfTheReceiver.lean](../BezoutValuationIncidence/DampedChebyshevTangentFormOfTheReceiver.lean).

**Goldbach reads a projected second coefficient.** Put

\[
q(k)=\mathbf1_{\operatorname{Squarefree}(k),\ k\ne1},\qquad
a_\varepsilon(k)=q(k)\tau_\varepsilon(k),\qquad
F_N(\varepsilon)=\sum_{k+\ell=N}a_\varepsilon(k)a_\varepsilon(\ell).
\]

Squarefree restriction removes proper prime powers from the tangent; deleting
the unit makes the source vanish at zero. Hence, for every fixed target,

\[
\boxed{\lim_{\varepsilon\to0,\ \varepsilon\ne0}
       \frac{F_N(\varepsilon)}{\varepsilon^2}
       =G(N):=\sum_{\substack{p+q=N\\p,q\text{ prime}}}\log p\log q.}
\]

The source defining \(F_N\) contains divisor incidence, damping and squarefree
projection; it contains no primality predicate. Binary Goldbach is exactly
strict positivity of this limit at every \(N=2(n+2)\).
This is a finite-target limit, with no exchange of damping and horizon limits.

In the normal-layer language, a squarefree integer with \(r\) prime factors
first appears at order \(\varepsilon^r\), since
\(1-p^{-\varepsilon}=\varepsilon\log p+O(\varepsilon^2)\).
Thus Goldbach asks whether every even additive fibre meets the first normal
layer in both coordinates. The order-two contribution survives exactly when
that fibre contains a prime pair. This interpretation follows from the finite
Euler product; it does not assume a distribution law for prime pairs.

Positive overlap at a fixed positive damping is weaker: composite squarefree
pairs also contribute there. Goldbach selects the **quadratic order** of the
overlap, so the normalization by \(\varepsilon^2\) is essential.

**RH reads centered prefix energy.** For the same unprojected source, set

\[
c_\varepsilon=\operatorname{Re}\frac1{\zeta(1+\varepsilon)},\quad
A_\varepsilon(m)=\sum_{k=1}^{m}\tau_\varepsilon(k)-mc_\varepsilon,
\quad
E_T(\varepsilon)=\sum_{m=1}^{T}\frac{A_\varepsilon(m)^2}{m(m+1)}.
\]

The existing
[`riemannHypothesis_iff_cofinallyAdmits`](../ArithmeticContinuationAndCriticalEnergy/TheDampedMobiusCriticalEnergy.lean)
identifies RH with admission at arbitrarily small positive dampings:
for every \(\delta>0\), some \(0<\varepsilon<\delta\) has
\(\sup_T E_T(\varepsilon)<\infty\).

To see the kernels directly, write \(b_\varepsilon(k)=\tau_\varepsilon(k)-c_\varepsilon\)
for \(k\ge1\). Finite expansion and telescoping give

\[
E_T(\varepsilon)=\sum_{j,k=1}^{T}b_\varepsilon(j)b_\varepsilon(k)
 \left(\frac1{\max(j,k)}-\frac1{T+1}\right).
\]

Thus RH tests the centered source through a cumulative kernel and a bound
uniform in the horizon. Goldbach tests its squarefree tangent through the
anchored kernel \(\mathbf1_{j+k=N}\), separately at each even target. This is
an exact common-source relationship. An implication between the two conjectures
would require a further theorem transporting these readings.

## Damping reversal and a finite two-scale test

Symmetrize the same projected source:

\[
b_\varepsilon(k)=e^{\varepsilon\log k/2}a_\varepsilon(k),\qquad
o_\varepsilon(k)=\frac{b_\varepsilon(k)-b_{-\varepsilon}(k)}2.
\]

The finite Euler product gives the exact identity

\[
\boxed{b_{-\varepsilon}(k)=\mu(k)b_\varepsilon(k).}
\]

Thus reflection of the damping parameter is arithmetic factor-count parity.
The odd sector keeps exactly the negative-Möbius part. On the retained
squarefree support,

\[
b_\varepsilon(k)=\prod_{p\mid k}2\sinh(\varepsilon\log p/2),\qquad
o_{2\varepsilon}(k)=D_\varepsilon(k)o_\varepsilon(k),\quad
D_\varepsilon(k)=\prod_{p\mid k}2\cosh(\varepsilon\log p/2)
 \ge 2^{\omega(k)}.
\]

This gives a finite two-scale formulation. Put
\(O_N(\varepsilon)=\sum_{k+\ell=N}o_\varepsilon(k)o_\varepsilon(\ell)\). Then

\[
\boxed{N\text{ has a prime pair}\quad\Longleftrightarrow\quad
 \exists\varepsilon>0:\ O_N(2\varepsilon)<16O_N(\varepsilon).}
\]

Every nonzero endpoint has an odd number of distinct prime factors. A
composite endpoint has at least three, so a supported pair containing a
composite amplifies by at least \(2^{3+1}=16\). Prime pairs instead supply
the quadratic tangent, with limiting amplification four. More precisely,

\[
\frac{16O_N(\varepsilon)-O_N(2\varepsilon)}{\varepsilon^2}
 \longrightarrow 12G(N).
\]

Goldbach therefore becomes an existence assertion for a strict two-scale
inequality in the odd part of the actual RH source. This connects damping
continuation, hyperbolic multipliers, arithmetic parity and the anchored
incidence reading. Proving that inequality at every even target remains
the arithmetic task; it is not an assumption in the equivalence.

## Reflection defect and the signed ledger

On \(0,\ldots,N\), let \(u_N(k)=\mathbf1_{k\text{ prime}}\log k\),
\(J_Nu(k)=u(N-k)\), and \(u_N^\pm=(u_N\pm J_Nu_N)/2\). Then

\[
\boxed{G(N)=\langle u_N,J_Nu_N\rangle
 =\|u_N^+\|^2-\|u_N^-\|^2
 =\|u_N\|^2-\tfrac12\|u_N-J_Nu_N\|^2.}
\]

All norms here are finite counting-measure norms. The normalization counts
ordered prime pairs, including \(p=q\) once. Goldbach has two equivalent forms:

* reflection-even energy strictly exceeds reflection-odd energy;
* reflection defect is strictly smaller than source mass.

Nonnegativity already follows from the source: each prime-pair term is
nonnegative. The arithmetic assertion excludes exact saturation of the
mass–defect inequality. A failed target would have disjoint support from its
reflection, equal even and odd energies, and defect equal to mass.

The coupling \(c_N(i,j)=\mathbf1_{i+j=N}\) is literally an instance of
[SAEI's `incidenceEnergy`](../SignedArithmeticEnergyIncidence/SignedIncidenceForms.lean).
Its energy on the specified prime profile is \(G(N)\). The coupling is
indefinite on arbitrary signed profiles: for \(N>0\), values \(1,-1\) at
the two endpoints give energy \(-2\). Thus the correct quantifier specifies
the arithmetic profile; universal positivity of this matrix is false.

Compensation gives another exact coordinate. With
\(m_N=\vartheta(N)/(N+1)\) and \(r_N=u_N-m_N\mathbf1\),
\(\sum r_N=0\), so

\[
G(N)=(N+1)m_N^2+\langle r_N,J_Nr_N\rangle.
\]

Goldbach asks whether the signed reflected remainder stays strictly above
\(-(N+1)m_N^2\). For a general chosen baseline \(c\), the mixed term must stay:

\[
G(N)=(N+1)c^2+2c\bigl(\vartheta(N)-(N+1)c\bigr)
       +\sum_{k+\ell=N}(u_N(k)-c)(u_N(\ell)-c).
\]

The existing Lean identity `primePairWeight_eq_theta_and_reflection` is
exactly the case \(c=1\).

## Divisor incidence on the additive fold

For positive divisors \(d,e\), define

\[
K_N(d,e)=\#\{1\le k\le N-1:d\mid k,\ e\mid N-k\}.
\]

The congruences are \(k\equiv0\pmod d\) and \(k\equiv N\pmod e\).
Their compatibility is \(\gcd(d,e)\mid N\); when compatible they form one
residue class modulo \(\operatorname{lcm}(d,e)\). Therefore

\[
K_N(d,e)=\mathbf1_{\gcd(d,e)\mid N}
\left(\frac{N-1}{\operatorname{lcm}(d,e)}+\Delta_N(d,e)\right),
\qquad |\Delta_N(d,e)|\le1.
\]

Compatibility alone does not guarantee a representative in the finite interval.
For the projected source retain the squarefree mask in the matrix:

\[
K_N^{\rm sf}(d,e)=\sum_{k=1}^{N-1}
 q(k)q(N-k)\mathbf1_{d\mid k}\mathbf1_{e\mid N-k}.
\]

For \(N\ge2\), finite rearrangement gives the exact formula

\[
F_N(\varepsilon)=\sum_{d,e\le N}
 \mu(d)\mu(e)d^{-\varepsilon}e^{-\varepsilon}K_N^{\rm sf}(d,e),
\]

where the divisor sums run over positive integers. The raw CRT density is not
a replacement for this masked matrix. This is the Bézout–valuation object:
the Möbius row paired with its reflection through an actual finite incidence
matrix. Its target \(N\), boundary and squarefree restrictions remain visible.

## Dictionary for the twelve programmes

The separate [projective return module](ProjectiveIntegralReturns.lean)
checks an arithmetic constraint on transporting the signed bilinear source
\(\mu(T-mn)\). A non-affine integer fractional linear map with nonzero
determinant \(\Delta\) has at most \(2\tau(|\Delta|)\) integer returns;
inversion attains the bound. The induced second coordinate has determinant
\(T^2\Delta\). The checked joint and family bounds retain these costs,
so rational projective symmetry is not silently treated as symmetry of
the fixed integer rectangle. They supply no signed cancellation estimate.

| Programme | Goldbach restatement in its objects | What the translation retains |
|---|---|---|
| [Arithmetic Positivity Theory](../arithmetic-positivity-theory/README.md) | \(G=M-D\), matching the algebra of its zero mass minus reflection defect. | Its zero reflection \(\rho\mapsto1-\bar\rho\) and the integer reflection \(k\mapsto N-k\) act on different spaces. The common identity does not identify their forms. |
| [BiScale Uncertainty](../BiScaleUncertainty/README.md) | The symmetric source is a product of hyperbolic sine multipliers. Goldbach is the strict two-scale test \(O_N(2\varepsilon)<16O_N(\varepsilon)\) at some positive damping. The polynomial reading is \([z^N]P_N(z)^2\), where \(P_N(z)=\sum u_N(k)z^k\). | Keep the odd arithmetic sector and additive anchor. Magnitudes and total energy omit the phase needed for a specified sum coefficient. |
| [Trans-Horizon Incidence Mechanics](../TransHorizonIncidenceMechanics/README.md) | Use the damped Möbius row in \(K_N^{\rm sf}\), with its finite boundary. The receiver uses that same row's centered cumulative response. | A complete-period covariance and a target window are distinct readings. Keep the finite endpoint defect before considering a limit in \(N\). |
| [Bézout–Valuation Incidence](../BezoutValuationIncidence/README.md) | Replace successor incidence by \(d\mid k,e\mid N-k\), giving \(\gcd(d,e)\mid N\). Squarefree projection turns its existing damping tangent into the prime source. | The exact congruence fibre, unit removal, and the squarefree mask. These specify the new matrix rather than merely naming a correlation. |
| [Arithmetic Criticality Theory](../ArithmeticCriticalityTheory/README.md) | Fold at \(N/2\): the reflected sum and difference squares produce \(E_+-E_-\). Goldbach is absence of saturation on the actual prime profile. | This concerns one arithmetic state per target. It is not positivity of a ground-energy form on all profiles. |
| [Square-Root Threshold](../SquareRootThreshold/README.md) | Keep the reading's resolution explicit: a specified additive coefficient versus the boxed mass \(\vartheta(x)^2\). The existing bridge makes RH the square-root error law for that boxed mass. | Average control and targetwise strict positivity have different quantifiers. No square-root threshold for the new reflection problem is claimed without a theorem. |
| [Arithmetic Incidence Positivity](../ArithmeticIncidencePositivity/README.md) | Its micro-fold decomposition becomes the exact ledger \(G=E_+-E_-\); both sectors must stay in the calculation. | Its logarithmic antidiagonals encode products: \(\log a+\log b=\log(ab)\). Goldbach uses sums. The parity algebra transfers, while the incidence kernel changes. |
| [Arithmetic Continuation and Critical Energy](../ArithmeticContinuationAndCriticalEnergy/README.md) | RH is cofinal bounded pronic energy of \(\tau_\varepsilon-c_\varepsilon\); Goldbach is positive quadratic coefficient of the squarefree reflected source. | Same damping parameter and actual divisor family; different projection, kernel and order of limits. |
| [Scale-Signed Incidence Criticality](../ScaleSignedIncidenceCriticality/README.md) | The observation is \(u\mapsto G_u(N)\) with \(N\) retained. Translating a source by \(h\) moves its sum coefficient by \(2h\). | Anchor loss is concrete: \(z^2\) and \(z^3\) have identical magnitudes on the unit circle, but their squared polynomials have different coefficients at degree six. This is a finite-profile witness, not a claim about altered actual primes. |
| [Arithmetic Compensation Theory](../ArithmeticCompensationTheory/README.md) | \(G=(N+1)m_N^2+\langle r_N,J_Nr_N\rangle\), or the full baseline formula with its mixed term. | Coherent contribution and signed remainder are paired before estimating. The exact identity supplies a research coordinate, not a remainder bound. |
| [Arithmetic Castelnuovo–Severi](../ArithmeticCastelnuovoSeveri/README.md) | \(G\) is the weighted incidence of the prime support with its reflected support; equivalently the weighted intersection of prime pairs with the sum fibre. | This is a concrete finite incidence interpretation. Realizing it in the existing scaling-surface intersection pairing would need a separate construction; that identification is not asserted. |
| [Signed Arithmetic Energy Incidence](../SignedArithmeticEnergyIncidence/README.md) | Literally `incidenceEnergy c_N u_N`, with symmetric antidiagonal coupling. | The distinction between a specified state's positive overlap and positivity or local payability of a whole form. The Lean specialization uses the programme's actual definition. |

## Formal statements

The following declarations express the new translations without an added
analytic premise:

* `hasDerivAt_squarefreeDampedSource_zero`
* `tendsto_dampedReflectionOverlap_div_sq`
* `goldbach_iff_positive_dampedReflection_limit`
* `additivePairWeight_eq_even_sub_odd`
* `additivePairWeight_eq_mass_sub_defect`
* `goldbach_iff_reflection_even_dominates`
* `goldbach_iff_reflection_defect_lt_mass`
* `incidenceEnergy_goldbachReflectionCoupling`
* `goldbach_iff_positive_reflection_incidenceEnergy`
* `squarefreeDampedSource_neg`
* `symmetricDampedSource_neg`
* `symmetricDampedSource_eq_prod_sinh`
* `oddDampedSource_eq_negativeMoebius`
* `oddDampedSource_two_mul`
* `primeFactorPower_le_dampingDoublingMultiplier`
* `tendsto_oddDampedDyadicDefect_div_sq`
* `primePair_iff_positive_oddDampedDyadicDefect`
* `goldbach_iff_positive_oddDampedDyadicDefect`

The finite CRT expansion, general compensation formula and polynomial reading
above are paper-level dictionary entries; they are not additional Lean claims.
The result is a bridge within the research corpus. No new analytic estimate,
proof of either conjecture, or external novelty claim is attached to it.

The leaf passes `lake --old env lean`. The four new Goldbach equivalences and
the existing boxed RH equivalence depend only on `propext`, `Classical.choice`
and `Quot.sound`; their closures were checked with `#print axioms`.
The subsequent damping-parity and two-scale extension also passes the leaf
check without warnings. Six further closures, including the finite target
criterion and its all-even formulation, have the same foundational axioms.
