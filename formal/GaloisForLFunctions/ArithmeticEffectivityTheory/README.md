# Arithmetic Effectivity Theory (AET)

Namespace `GaloisForLFunctions.ArithmeticEffectivityTheory`; umbrella `ArithmeticEffectivityTheory.lean`.

**Question.** Over $\mathbb F_q$ Weil's sign is the nonnegativity of a dimension: Riemann–Roch on $C\times C$, dropping $h^1\ge0$,
gives $h^0(D)+h^0(K-D)\ge\tfrac12D\cdot(D-K)+\chi(\mathcal O)$, and sections cannot exist in negative degree. Over $\mathbb Z$ the integers that
could play $h^0$ are log-orders of finite groups and log-volumes of lattices. Which real-valued cohomology on $\operatorname{Spec}\mathbb Z$ and its
correspondence surface has a Riemann–Roch proved without the sign, which effectivity laws does it obey, and which signs can
integers produce?

**Guiding sentence.** RH is the Hodge index theorem of an arithmetic surface whose points are the primes with residue size
$\log p$, whose cohomology is measured by volume, whose Frobenius is the Hecke ring, and whose boundary is the archimedean place.
**Principle.** A sign from integers is a comparison of two computations of one Euler characteristic, positivity entering only
through the existence of a section or the order of a finite group.

---

## 1. Place in the research

Effective *cones* are tautological (universal floor law, ACS; a Boolean section count with RR and Bézout is the sign, ACP).
AET moves the question from cones to **functions**: effectivity is a *growth law* of a real function, to be proved from its
definition. APol studies positivity from symmetry/charge; AET from counting.

| Programme | Takes / adds |
|---|---|
| ArithmeticCastelnuovoSeveri | Polar and scaling surfaces, curve data, golden datum, universal floor law / real-valued effectivity calculus |
| ArithmeticOrientationGeometry | Theta $h^0$ of $\operatorname{Spec}\mathbb Z$ / theta surface with characteristics; non-extension of the base $h^0$ |
| ArithmeticOrientationTheory | Rank counts, Boolean $h^0$ / log-volume counts |
| BiarithmeticGeometry | $E(\log(N+1))=N-\log Q_N$ / log-torsion dictionary of the explicit formula; product formula as Bézout |
| ArithmeticCorrespondencePositivity | Correspondence ring, layers L1–L6 / naive-height form of L5 (Tate limits); Stepanov as Siegel abundance + integrality floor |
| ArithmeticCorrelationGeometry, ArithmeticPolarization | Gauge charge; local types / counting mechanism of a polarization |
| ArithmeticPositiveDuality | $\kappa=1$ rigidity, Beurling rigidity / base axioms against Beurling models |
| `RHTower` | Explicit formula, von Koch, Stepanov and Weil bounds over $\mathbb F_q$, hyperelliptic descent |

---

## 2. Why

**Weil's sign is a growth law.** A class $D$ with $D^2>0$, $D\cdot A=0$ would have $h^0(nD)+h^0(K-nD)\ge\tfrac12n^2D^2-O(n)$ while degree-zero
classes carry boundedly many sections: quadratic growth vs not. Ingredients: $h\ge0$, a **quadratic** Euler characteristic,
a growth bound in degree zero. None is a cone axiom.

**Over $\mathbb Z$ the integers are log-torsions.** $\psi(N)=\log|\mathbb Z/\operatorname{lcm}(1..N)\mathbb Z|$; each prime power adds the log-order $\Lambda(N+1)$ of a
cyclic kernel; box Euler characteristic $E(\log(N+1))=N-\log Q_N$ is not a difference of dimensions. The explicit formula is a
second computation: *log-torsion = zero oscillation + archimedean density*. Cohomology must be real-valued (van der
Geer–Schoof $h^0=\log\theta$); effectivity is the size of a log-volume.

**One intrinsic integrality inequality**: $|n|\ge1$, i.e. the product formula read as Bézout. Every sign from integers over $\mathbb Z$
(Liouville, Chebyshev, Nair, Thue–Siegel, determinant methods, Northcott, Néron–Tate positivity) is this inequality applied to
a Siegel's-lemma auxiliary.

**Positivity of a quadratic form from counting** is a theorem for Néron–Tate heights: theorem of the square up to bounded error
+ nonnegative naive heights. ACP shows the first is free on the correspondence ring; the missing input is a **naive height** on
the integral correspondence ring, nonnegative for an arithmetic reason, at bounded distance from the Rosati form.

**One variable is a base.** The theta $h^0$ of $\operatorname{Spec}\mathbb Z$ has exact (linear) Riemann–Roch whose Mellin transform is $\Lambda(s)$. A surface
needs quadratic $\chi$, hence Hilbert–Samuel growth; the base $h^0$ never extends. On the box class $\sqrt N\cdot A$, $\chi=N$: a surface
$h^0$ has the size of a dimension of Dirichlet polynomials of length $N$, not of the degree $\log N$.

---

## 3. Objects and language

| Over $\mathbb F_q$ | AET object | Lean |
|---|---|---|
| $C\times C$ | polar surface, ample class $A=H+V$ | `PolarSurface`, `scalingSurface` |
| $\chi(D)=\tfrac12D\cdot(D-K)+\chi(\mathcal O)$ | Euler characteristic, Serre symmetric | `eulerChar` |
| $h^0+h^2\ge\chi$ | Riemann inequality $\chi(x)\le h(x)+h(\kappa-x)$ | `RiemannInequality` |
| $h^0$ bounded in degree zero | `DegreeBounded`, `DegreeZeroSubquadratic` | — |
| $D^2>0$, $D\cdot A=0$ | abundant class; abundance rate $\max(0,\tfrac12x^2)$ | `Abundant`, `optimalEffectivity` |
| Hilbert–Samuel | along the ample ray; box class $\sqrt N A$ | `boxClass` |
| theta $h^0$ of the base | $h^0(d)=\log\sum e^{-\pi n^2e^{-2d}}$ | `thetaEffectivity`, `arithH0` |
| Néron–Tate height | naive height; Tate limit; integral Rosati form | `tateLimit`, `intRosatiForm` |
| $\#C(\mathbb F_{q^m})$ | log-torsion of the horizon | `logTorsion` |
| degree of principal divisors $=0$ | product formula $\log n=\sum v_p(n)\log p$ | `log_eq_logTorsion` |
| theta divisor, characteristics | theta surface $h^0(a,d)$, dual, characteristic $\vartheta(J,t)$ | `thetaH0`, `thetaChar` |
| Frobenius graphs ∩ diagonal | torsion orbits $O_n$; $I(m,n)=\log|\operatorname{Res}(\Phi_m,\Phi_n)|$; Abel energy | `orbitIntersection`, `torsionEnergy` |
| Stepanov auxiliary | auxiliary integer polynomial; integrality floor vs analytic ceiling | `nairPoly` |
| $\mathbb P^1\times\mathbb P^1$ | hyperbolic plane, $h^0=(a+1)^+(b+1)^+$ | `hyperbolicPlane`, `p1SquareH0` |

**Words.** *Effectivity function*; *linear/quadratic Riemann inequality*; *Hilbert–Samuel*; *subquadratic in degree zero*;
*abundant class*, *abundance rate*; *naive height*, *Tate limit*, *Northcott*; *log-torsion*; *soft* (holds on every datum of a
family, hence carries none of its arithmetic); *integrality floor*, *ceiling*; *renormalized energy*.

---

## 4. Mechanisms

1. **Weil's argument as a growth law**: quadratic Riemann inequality + subquadratic degree-zero growth ⇒ Hodge index on every
   polar surface; conversely under Hodge $\max(0,\chi)$ works. Abundant ⇔ $x^2>0$; least rate $\max(0,\tfrac12x^2)$; on primitive classes
   the negative part of Weil's form is twice the least abundance rate.
2. **The base does not extend**: Riemann inequality forces Hilbert–Samuel; affine growth in the degree has no Riemann
   inequality; the theta $h^0$ obeys every linear law on every surface and the quadratic one on none.
3. **Tate's limit**: approximate doubling → unique homogeneous limit at distance $C/3$; approximate parallelogram → exact;
   bounded below → positive; Northcott → definite. Rosati positivity at a cycle is decided on integral correspondences
   (rounding) and equals existence of a naive height there.
4. **Naive heights are traces**: on curve data a naive height on $\mathbb Z[F]$ exists iff unitary; kernel counts never supply one
   (complex fake); the theta count's Tate limit is $\pi J^2/t$.
5. **Horizon torsion and box class**: $\log|\mathbb Z/\operatorname{lcm}(1..N)|=\psi(N)$; $\chi(\sqrt NA)=N$.
6. **Theta surface**: Poisson exchanges translation and modulation, $h^0(a,d)-h^{0\vee}(a,-d)=d$; completing the square gives a nonnegative
   naive height for $\pi J^2/t$, identical on every translate — the polarization is **soft**; the fibre at characteristic 0 is $\Lambda(s)$.
7. **Torsion characteristics**: $|\tau(\chi,\psi)|^2=|F|$ by orthogonality; unit root numbers: square-root cancellation is a count at every level.
8. **Stepanov over $\mathbb Z$**: integrality $\operatorname{lcm}(1..n+1)\int_0^1P\in\mathbb Z$ gives $\log(1/\int P)\le\psi(n+1)$ and Nair's $\psi(2m+1)\ge m\log4$: effectivity of
   the base only. Over $\mathbb F_q$ the method reaches the sign through Frobenius-flat coefficients ($x^q=x$, Hasse derivatives); over
   $\mathbb Z$ no coefficients are flat.
9. **Calibrations**: $\mathbb P^1\times\mathbb P^1$ returns Hodge index; odd-degree hyperelliptic curves of every genus over every finite field of
   odd characteristic are unitary *by counting* (Stepanov + Gauss-sum modulus + descent) and carry effectivity functions and
   naive heights; genus one = Hasse.
10. **The prime side is an intersection**: $\Lambda(n)=\sum_{\zeta\in O_n}\log|1-\zeta|$; orbit energies $J(a,b)=\gcd(a,b)\log\operatorname{lcm}(a,b)$; an orbit meets
    its Hecke translate of degree $t$ in $\Lambda(t)$ per point; Weil's prime kernel is a renormalized positive gcd-twisted torsion
    energy — the sign is lost in the renormalization ($\log1/(1-r)$ self-energy).
11. **Counting reaches short sums**: Pólya–Vinogradov by completion; Burgess's bound by counting on curves $y^2=\prod(x+b_i)$ of
    growing genus; least quadratic nonresidue $\le p^{1/(4\sqrt e)+\varepsilon}$.

---

## 5. Pillar theorems

1. **Effectivity calculus = Hodge index** (`hodgeIndex_tfae`, `abundant_iff`, `eventually_optimalEffectivity_le`).
2. **The base does not extend** (`thetaEffectivity_not_riemannInequality`, `exists_degree_effectivity_iff_hodgeIndex`).
3. **Tate's limit law; naive heights are traces** (`tateLimit_parallelogram`, `orbitHodgeIndex_iff_exists_naiveHeight`,
   `exists_naiveHeight_iff_unitary`, `complexFake_kernelCounts_nonneg_no_naiveHeight`).
4. **The integer of the sign**: RH ⇔ $\log|\mathbb Z/\operatorname{lcm}(1..N)|=\chi(\sqrt NA)+O(\sqrt N\log^2N)$ (`riemannHypothesis_iff_logTorsion_sub_eulerChar`).
5. **Theta surface: RR with characteristic, soft polarization** (`thetaH0_riemannRoch`, `tateLimit_log_thetaChar`, `hasSum_shifted_thetaChar`).
6. **Stepanov reaches the base** (`log_inv_integral_le_psi`, `nair_psi_ge`).
7. **Calibration** (`hyperbolicPlane_hodgeIndex`, `riemannHypothesis_oddHyperelliptic`, `goldenDatum_multiplicative_axioms_not_effective`).
8. **One statement in five currencies**: effectivity function ⇔ no abundant class ⇔ naive heights ⇔ fixed tensor loss ⇔ log-torsion
   law ⇔ RH (`riemannHypothesis_effectivity_tfae`).
9. **Prime side as intersection** (`orbitIntersection_hecke`, `weilPrimeKernel_renormalized_torsion_energy`).
10. **Counting reaches short sums** (`abs_burgessS_le`, `eventually_exists_nonresidue_le`).

---

## 6. Traps

| Trap | Truth |
|---|---|
| An effective cone with RR is an effectivity | Its RR is the defect floor; a Boolean count with RR + Bézout is the sign |
| The theta $h^0$ is half of Weil's argument | Linear RR on every surface, quadratic inequality on none |
| A surface $h^0$ is a log-volume of the degree | Must grow like $\chi$: dimension of the box's sections |
| Integrality of point counts constrains the sign | Golden datum: integral counts, zeta, FE, abundant class |
| A positive polarization on a surface over $\mathbb Z$ is Weil's | Theta surface has one at every characteristic: soft |
| The integrality floor reaches the sign | Reaches Chebyshev; deviation of log-torsion from degree is invisible |
| Stepanov = integrality + degree bound | Over $\mathbb F_q$ it needs Frobenius-flat coefficients |
| Square-root cancellation needs analysis | At each finite level it is a count; the open part is uniformity at the arithmetic point |
| Orders of finite kernels give a naive height | Determinants; complex fake |
| Integral positivity is weaker than real | Equivalent by rounding |
| A positive energy with Weil's prime kernel off-diagonal gives positivity | Divergent self-energy on the diagonal; atomic tests are blind to zeros |
| The prime matrix separates gauge twins | $\lambda(m)\lambda(mt)=\lambda(t)$; selectivity lives in archimedean/polar parts |

---

## 7. Open problems

1. **A section count on the scaling surface** with quadratic $\chi$, defined from arithmetic, of box-class size $N$, growth laws
   proved from the definition (partial forms: degree-zero growth bounds, each bounding the negative part of Weil's form).
2. **A naive height on $\mathbb Z[G]$** of trace type, nonnegative for an arithmetic reason, not soft.
3. **Selective sections at torsion characteristics**: positivity separating characteristic 0 from its neighbours.
4. **Limit of Stepanov over $\mathbb Z$** (integer Chebyshev problem): show the integrality floor cannot reach PNT, or find a family of
   coefficients invisible to vanishing conditions.
5. **Uniform square-root cancellation from counting**: finite groups, one per level, computing $\psi(N)-N$ at the arithmetic point.
6. **Emptiness tests**: is every section count with the Riemann inequality on box classes bounded by a large-sieve count in degree zero?
7. **Archimedean place of the torsion picture**: a positive structure whose renormalized limit is Weil's archimedean term; a
   regularization finer than uniform self-energy.

## 8. Tools to build

A section count on the scaling surface defined without the sign; an arithmetic naive height on $\mathbb Z[G]$; the limit of the
Stepanov method; charged sections at torsion characteristics.

## 9. Contribution standard

State the Euler characteristic (linear or quadratic) and which effectivity law is proved (Riemann inequality, Hilbert–Samuel,
degree-zero growth, naive height, Northcott) and from what; report on golden datum, complex fake, curves and the battery; name
the integer or log-volume carrying any sign; calibrate on $\mathbb P^1\times\mathbb P^1$, Hasse, curve unitarity, theta RR of the base. Effectivity is
a growth law; integers over $\mathbb Z$ are log-torsions; the product formula is the Bézout of the base; linear RR is free; a
polarization from counting needs quadratic $\chi$ and must not be soft.
