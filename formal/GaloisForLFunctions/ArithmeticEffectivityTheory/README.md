# Arithmetic Effectivity Theory (AET)

**One question.** Over `𝔽_q` Weil's sign is the nonnegativity of a dimension: Riemann–Roch on
`C × C` reads `h⁰(D) − h¹(D) + h²(D) = ½ D·(D − K) + χ(𝒪)`, dropping `h¹ ≥ 0` leaves
`h⁰(D) + h⁰(K − D) ≥ ½ D·(D − K) + χ(𝒪)`, and sections cannot exist in negative degree. Over `ℤ`
the integers that could play `h⁰` are not dimensions: they are log-orders of finite groups and
log-volumes of lattices. Which real-valued cohomology on `Spec ℤ` and its correspondence surface
has a Riemann–Roch proved without the sign, which effectivity laws does it obey, and which signs can
integers produce?

AET is the theory of **real-valued effectivity**. Its basic object is an *effectivity function*: a
real function `h` on the classes of a polar surface, playing `h⁰`. Its basic invariants are the
**Euler characteristic** `χ` that `h` satisfies Riemann–Roch against, and the **growth** of `h` along
the ample ray and along classes of degree zero. Its guiding sentence:

> *RH is the Hodge index theorem of an arithmetic surface whose points are the primes with residue
> size `log p`, whose cohomology is measured by volume, whose Frobenius is the Hecke correspondence
> ring, and whose boundary is the archimedean place.*

Its basic principle:

> *A sign from integers is a comparison of two computations of one Euler characteristic, in which
> positivity enters only through the existence of a section or the order of a finite group.*

Namespace `GaloisForLFunctions.ArithmeticEffectivityTheory`; umbrella
`ArithmeticEffectivityTheory.lean`. Everything is unconditional; RH and its partial forms appear only
inside equivalences.

---

## 1. Place in the research

The frontier has a complete map of the mechanisms that can be built from the positivity of `Λ`, the
functional equation, the simple pole and strip holomorphy on the line, and each has a sharp limit.
It also knows which layer of Weil's argument is missing over `ℤ`: identities, the theorem of the
square and the budget are free, Rosati positivity is RH (ACP). Every attempt to supply the missing
layer through an *effective cone* is tautological: an ample cone of nonnegative degree has
Riemann–Roch iff it contains the open positive cone and the defect is nonnegative (the universal
floor law, ACS), and a Boolean section count with Riemann–Roch and Bézout exists iff the sign holds
(ACP P29). AET moves the question from cones to functions: effectivity is a *growth law* of a real
function, and the growth must be proved from the definition of the function.

| Programme | What AET takes | What AET adds |
|---|---|---|
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | polar surfaces, the scaling surface and `scalingSurface_hodgeIndex_iff`, curve data, the golden datum, effectivity axioms, the universal floor law, prime-node section counts | the real-valued effectivity calculus: Riemann inequality, Hilbert–Samuel growth, degree-zero growth |
| [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | the theta `h⁰` of `Spec ℤ` with its Riemann–Roch (`arithH0_riemannRoch`), orbit Rosati positivity | the theta surface: characteristics, the free polarization, the failure of the base `h⁰` to extend |
| [ArithmeticOrientationTheory](../ArithmeticOrientationTheory/README.md) | Nyquist rank bounds, `E(s) = h⁰`-supply `− h¹`-obstruction, Boolean `h⁰`, section cones | log-volume counts in place of rank counts |
| [BiarithmeticGeometry](../BiarithmeticGeometry/README.md) | `E(log(N+1)) = N − log Q_N` (`boxDefect_eq_degree_sub_log_torsion`), prime-power transition groups | the log-torsion dictionary of the whole explicit formula; the product formula as Bézout |
| [ArithmeticCorrespondencePositivity](../ArithmeticCorrespondencePositivity/README.md) | correspondence ring, normalized graphs and the free theorem of the square, the layer map L1–L6, P29 (a section count is the sign), P30 (the Stepanov count is the sign) | the naive-height form of L5 (Tate limits); the Stepanov method as Siegel abundance + integrality floor |
| [ArithmeticCorrelationGeometry](../ArithmeticCorrelationGeometry/README.md) | the gauge torus, gauge charge, the boundary of a dilation = the archimedean degree | the additive characteristic of the theta surface as the gauge-charged direction |
| [ArithmeticPolarization](../ArithmeticPolarization/README.md) | the polarization law, local types at reflection pairs, twists, the diagonal collapse of lattice counts on the square | the *counting* mechanism of a polarization, with its Riemann–Roch and its growth laws |
| [ArithmeticPositiveDuality](../ArithmeticPositiveDuality/README.md) | `κ = 1` rigidity, the quantum budget, Beurling rigidity | the base axioms against Beurling models |
| [SquareRootThreshold](../SquareRootThreshold/README.md), [BiScaleUncertainty](../BiScaleUncertainty/README.md), [TransThresholdPairCorrelation](../TransThresholdPairCorrelation/README.md) | the square-root threshold, large sieve, Nyquist diagonal | the emptiness test "sections over `ℤ` are large-sieve sections" |
| RHTower | explicit formula, zero detection, zero density, von Koch | the Stepanov reading of zero detection and local counts |

APol and AET split the polarization problem along its two conceivable sources over `ℤ`: APol studies
positivity coming from a non-hyperbolic localizing symmetry or from charge; AET studies positivity
coming from counting.

---

## 2. Why

**Weil's sign is a dimension.** In Weil's proof three identities (Lefschetz, adjunction, the
theorem of the square) hold for fake data as well as for curves; the sign enters once, through
Riemann–Roch on `C × C`: a class `D` with `D² > 0` and `D·A = 0` would have
`h⁰(nD) + h⁰(K − nD) ≥ ½ n² D² − O(n)`, while classes of degree zero carry boundedly many
sections. A growth that is quadratic in the class against a growth that is not: that is the whole
mechanism. Its ingredients are a function `h ≥ 0`, an Euler characteristic that is *quadratic*, and
a growth bound on degree zero. None is a cone axiom.

**Over `ℤ` the integers are log-torsions.** The prime side of the explicit formula is a sum of
`Λ(n)`, and `Λ(n)` is the logarithm of the order of the kernel of `ℤ/lcm(1..n) → ℤ/lcm(1..n−1)`;
`ψ(N) = log |ℤ/lcm(1..N)ℤ|`. The box Euler characteristic is integer degree minus logarithmic
torsion, `E(log(N+1)) = N − log Q_N`, and it is not a difference of dimensions (BAG). The explicit
formula is the second computation of the same quantity:
*logarithmic torsion = oscillation of the zeros + archimedean density*. A cohomology adapted to this
must be real-valued — log-volumes, as in van der Geer–Schoof, where `h⁰ = log θ` — and effectivity
must be the size of a log-volume, not membership in a cone.

**Over `ℤ` there is one intrinsic integrality inequality.** A nonzero integer has `|n| ≥ 1`;
equivalently the archimedean degree `log |n|` equals the finite log-torsion `Σ v_p(n) log p ≥ 0`. It
is the product formula read as Bézout: an effective principal divisor has nonpositive archimedean
part. Every sign from integers proved over `ℤ` — Liouville, Chebyshev's bounds, Nair's `lcm` bound,
Thue–Siegel, determinant methods, Northcott, the positivity of Néron–Tate heights — is this
inequality applied to an auxiliary object built by Siegel's lemma. Siegel's lemma is the abundance
statement of the base: small sections exist when the lattice is large. AET asks what this mechanism
can and cannot reach for `ζ`.

**Positivity of a quadratic form from counting is a theorem elsewhere.** On an abelian variety over a
number field the Néron–Tate height is a positive semidefinite quadratic form, and the proof uses only
(i) the theorem of the square up to a bounded error and (ii) the nonnegativity of naive heights,
which is the product formula; Northcott makes it definite. Tate's limit is the arithmetic form of
Weil's polarization. ACP shows that (i) is free on the correspondence ring of `ℤ`. AET makes the
missing input explicit: a *naive height* on the integral correspondence ring, nonnegative for an
arithmetic reason and at bounded distance from the Rosati trace form.

**One variable is a base.** The theta `h⁰` of `Spec ℤ` has an exact Riemann–Roch, and its Mellin
transform is `Λ(s)`; it gives the functional equation and holds for every datum with one. Its
Euler characteristic is linear in the degree. A surface needs an Euler characteristic quadratic in
the class, hence growth quadratic along the ample ray (Hilbert–Samuel). AET proves that no function
of the degree with subquadratic growth satisfies a quadratic Riemann inequality on any polar surface:
the base `h⁰` is never the restriction of a surface `h⁰`.

---

## 3. Objects and language

| Over `𝔽_q` | AET object | Over `ℤ` | Owner |
|---|---|---|---|
| `C × C`, intersection form | polar surface `(E, ·, H, V)`, ample class `A = H + V` | scaling surface: pole plane `⟨H, V⟩` ⊕ tests, pairing = explicit formula | ACS |
| `h⁰(D) = dim H⁰` | effectivity function `h : E → ℝ` | theta `h⁰`, log-volumes of node lattices, log-volume counts | AET |
| `χ(D) = ½ D·(D − K) + χ(𝒪)` | Euler characteristic `χ_κ,χ₀(x) = ½ x·(x − κ) + χ₀` | canonical class `κ` in the pole plane | AET |
| Riemann–Roch, `h¹ ≥ 0` dropped | Riemann inequality `h(x) + h(κ − x) ≥ χ(x)` | — | AET |
| `h⁰(nA) ~ n² A²/2` | Hilbert–Samuel growth along the ample ray | — | AET |
| `h⁰` bounded in degree zero | degree-zero growth `h(nx) + h(κ − nx) = o(n²)` on `x·A = 0` | — | AET |
| Néron–Tate height | naive height: `h ≥ −C`, `|h(x+y) + h(x−y) − 2h(x) − 2h(y)| ≤ B`; Tate limit `q = lim 4^{−n} h(2^n x)` | on the integral correspondence ring `ℤ[ℚ_{>0}]` | AET |
| `#ker(m − nF)` | degree of a correspondence as the order of a finite group | log-torsion `Λ(n) = log |ker(ℤ/lcm(1..n) → ℤ/lcm(1..n−1))|` | BAG, AET |
| principal divisors have degree 0 | Arakelov divisors of `Spec ℤ`; Bézout = product formula, `|n| ≥ 1` | — | AET |
| theta divisor on the Jacobian | theta surface: `Θ(a, u) = Σ_n e^{−π(n + a)² u}`, characteristic `a ∈ ℝ/ℤ`, degree `d = −½ log u` | Mathlib `HurwitzZeta.evenKernel`, `cosKernel` | AET |
| auxiliary polynomial (Stepanov) | Stepanov section: Siegel abundance + forced vanishing + integrality floor + analytic ceiling | `lcm(1..n+1) ∫₀¹ P ∈ ℤ`, zero detectors, Jensen counts | AET, RHTower |
| — | base datum: axioms of a base over which `ζ`'s zeros are local data | pole plane | AET, ACP |
| fake curves | battery: golden datum, complex fake, shifted pair, Beurling systems, Liouville twin, `CompletedPositiveSystem 2 1` | — | ACS, ACP |

**Words.**

- *Effectivity function*: a real function `h` on classes. *Linear* or *quadratic Riemann
  inequality*: according to whether its Euler characteristic is affine or quadratic.
- *Hilbert–Samuel*: `h(nA)` grows like `n²`. *Degree-zero subquadratic*: `h(nx) + h(κ − nx) = o(n²)`
  for every `x` with `x·A = 0`.
- *Abundant class*: a degree-zero class along which every function with the Riemann inequality grows
  quadratically. *Abundance cone*: the abundant classes.
- *Naive height*, *Tate limit*, *Northcott*: as for heights on abelian varieties.
- *Log-torsion*: the logarithm of the order of a finite group. *Log-volume*: the logarithm of a
  covolume or of a theta series. *Degree*: pairing with the ample class, or Arakelov degree.
- *Characteristic*: the translation parameter `a` of a theta series. *Charged section*: a section
  that depends on the characteristic.
- *Stepanov section*: an auxiliary object whose nonvanishing is forced by integrality and whose
  size is bounded analytically. *Integrality floor*: `|nonzero integer| ≥ 1`. *Ceiling*: the
  analytic bound.
- *Base datum*, *Beurling model*: as in §4.7.

Parameters: the class `x`, its degree `x·A`, the scaling `n`, the characteristic `a`, the degree
`d` of an Arakelov divisor, the horizon `N`. Every theorem states which are fixed and which grow.

---

## 4. Mechanisms

1. **The effectivity calculus.** On every polar surface: a function satisfying the quadratic
   Riemann inequality and degree-zero subquadratic growth forces the Hodge index; values bounded on
   each degree level suffice. Conversely, under the Hodge index and with `κ` in the pole plane,
   `h = max(0, χ)` satisfies both. A degree-zero class with `x² > 0` is abundant at rate `½ x²`. On
   the scaling surface the existence of such a function is RH; over curve data it is unitarity; the
   golden datum has none.
2. **Linear Riemann–Roch is free; the base does not extend.** On every polar surface `x ↦ h⁰(x·A)`
   (theta `h⁰` of the degree) is positive, increasing, tends to `0` in negative degree and satisfies
   the linear Riemann–Roch `h(x) − h(−x) = x·A` — on fake data as on curves. A function of the degree
   with `o(t²)` growth violates the quadratic Riemann inequality on every polar surface, because the
   Euler characteristic of `nA` is `n² − O(n)`.
3. **Tate's limit.** An approximately quadratic function has a unique quadratic function at bounded
   distance; if it is bounded below that quadratic function is positive semidefinite; with Northcott
   it vanishes only on torsion. On the integral correspondence ring the Rosati trace form is positive
   iff it has a naive height. Calibration: genus one, where the degree `deg(m − nF)` is a kernel
   order, and the golden datum, where `deg(2 − F) = −1` is not.
4. **Log-torsion and the Bézout of `Spec ℤ`.** Node lattices, their indices and log-indices; the
   Lefschetz numbers of `ℤ` as log-orders; Arakelov divisors with the product formula; the
   integrality floor as the only Bézout inequality of the base.
5. **The theta surface.** Theta series with characteristic satisfy Riemann–Roch with the
   characteristic exchanged for a modulation (Poisson). Completing the square gives the free
   polarization `π J² / u`, quadratic in the characteristic, positive at every characteristic. The
   Mellin transform in the degree is the completed even Hurwitz zeta function; `ζ` is the fibre at
   characteristic `0`.
6. **The Stepanov method over `ℤ`.** Siegel's lemma supplies auxiliary sections; vanishing is forced
   by integrality; the integrality floor and an analytic ceiling bound a count. Instances: the
   integrality `lcm(1..n+1) ∫₀¹ P ∈ ℤ` and Chebyshev's lower bound for log-torsion; the coefficient
   `a₁ = 1` of zero detectors; the Jensen count of zeros in a unit window; Bombieri's one-sided
   principle (ACP P30). Each reaches the base's effectivity or the local density, not the sign.
7. **The base.** Axioms for a base datum over which `ζ`'s zeros would be local data with a fixed
   loss, and the test of whether multiplicatively definable axioms admit Beurling models.

---

## 5. Pillar theorems

| Pillar | Statement | Status |
|---|---|---|
| **E1 The effectivity calculus** | quadratic Riemann inequality + degree-zero subquadratic growth ⇔ Hodge index, on every polar surface; abundance at rate `½ x²`; RH ⇔ existence on the scaling surface | planned |
| **E2 The base does not extend** | linear Riemann–Roch is free on every datum; no function of the degree with subquadratic growth has the quadratic Riemann inequality | planned |
| **E3 Tate's limit law** | approximately quadratic + bounded below ⇒ positive semidefinite quadratic part; Northcott ⇒ definite; Rosati positivity ⇔ a naive height on the integral correspondence ring | planned |
| **E4 Log-torsion and Bézout** | node lattices and log-indices; the product formula as Bézout of `Spec ℤ` | planned |
| **E5 The theta surface** | Riemann–Roch with characteristic; the free polarization; the Hurwitz fibres; `ζ` at characteristic `0` | planned |
| **E6 The Stepanov method** | integrality of `lcm · ∫ P`; Chebyshev's lower bound from the integrality floor; the method reaches base effectivity | planned |
| **E7 The base axioms** | base data and Beurling models | planned |

---

## 6. The questions

The five questions of the walls, read in AET's language, with the form an answer must take.

1. **Which integer, attached to the integers themselves and not to the zeros, bounds the
   oscillation of the zero sum?** The candidate is the horizon period `lcm(1..N)`: its log-order is
   `ψ(N)`, and RH says it equals the degree `N` up to `O(√N log² N)`, one-sidedly (ACP P30). Answer
   form: the positive structure — a section count with Riemann–Roch, or a naive height — whose
   effectivity bounds `log lcm(1..N) − N`.
2. **What is a section on `Spec ℤ × Spec ℤ`, and when do sections exist in quadratic abundance?**
   Answer form: the effectivity calculus (E1) fixes what `h⁰` must do; E2 rules out the base; each
   candidate construction is classified by its Euler characteristic and its growth.
3. **What couples `+` and `×` strongly enough to separate the arithmetic point from its gauge
   twins?** Answer form: the characteristic of the theta surface, the additive variable that
   multiplicative data cannot see; its fibres are the Hurwitz functions.
4. **How does a positivity proved on average over heights localize at one height below the zero
   spacing?** Answer form: a growth law that is pointwise in the class, as Hilbert–Samuel is; a
   positivity on average is a statement about a family of classes, not about one.
5. **What is the base?** Answer form: the axioms of a base datum and the test against Beurling
   models (E7).

---

## 7. Traps

| Trap | Truth |
|---|---|
| An effective cone with Riemann–Roch is an effectivity | Its Riemann–Roch is the defect floor (universal floor law); a Boolean count with RR and Bézout is the sign (ACP P29) |
| The theta `h⁰` of `Spec ℤ` is half of Weil's argument | Its Riemann–Roch is linear in the degree; it gives the functional equation and holds on every datum |
| Integrality of point counts constrains the sign | The golden datum has integral counts; integrality must enter as the order of a group attached to every element of the correspondence ring |
| A positive polarization on a surface over `ℤ` is Weil's | The theta surface carries one at every characteristic, including fibres with zeros off the line |
| Siegel's lemma supplies a surface `h⁰` | It is abundance on the base: log-volume linear in the degree |
| The Stepanov method over `ℤ` is a new route | Its instances reach Chebyshev's bounds and local densities; the obstruction is the absence of a ring endomorphism |
| A naive height exists because the theorem of the square is free | Freeness of the quadratic part says nothing about a nonnegative function at bounded distance |

---

## 8. Tools

**From sibling programmes:** polar surfaces, the scaling surface and its Hodge index, curve data and
fakes, the theta `h⁰` of `Spec ℤ`, the box Euler characteristic and transition groups, the
correspondence ring with Rosati and normalized graphs, gauge charge, zero detection and density,
the von Koch and Bombieri one-sided theorems; from Mathlib: Gaussian Poisson summation, the even
Hurwitz kernels and their functional equation, Chebyshev's functions and `lcmUpto`, heights with the
product formula, Northcott, Siegel's lemma.

**Built here:** see §5.

---

## 9. Open research topics

1. **A section count on the scaling surface with a quadratic Euler characteristic**, defined from
   arithmetic, with growth laws proved from its definition.
2. **A naive height on the integral correspondence ring**, nonnegative for an arithmetic reason, at
   bounded distance from the Rosati trace form.
3. **Charged sections**: theta sections at rational characteristics, their Dirichlet decomposition,
   and whether a positivity on them separates the characteristic `0` from its neighbours.
4. **The limit of the Stepanov method over `ℤ`**: the integer Chebyshev problem bounds what
   auxiliary integer polynomials give for log-torsion.
5. **The base axioms** and the minimal additive input a base must contain.
6. **Emptiness tests**: whether every section count with Riemann–Roch on `S` is bounded by the
   large-sieve count; whether the collision charge admits a finite source bound.

---

## 10. Success criteria and contribution standard

AET succeeds when it produces a real-valued effectivity whose Riemann inequality and growth laws are
proved from its definition and which is selective for `ζ`, or a theorem naming why a stated class of
constructions cannot be one, with its positive survivor.

| Criterion | Test |
|---|---|
| Calibration | reproduces Weil for curves (budget `2g`), Hasse in genus one by kernel orders, the theta Riemann–Roch of the base |
| Fakes | fails on the golden datum and the complex fake, for a reason the construction names |
| Selectivity | separates `ζ` from the shifted pair, Beurling systems, the Liouville twin and pole-order-two models |
| Quadratic Euler characteristic | its Riemann–Roch is quadratic in the class; linear Riemann–Roch is free |
| Counting origin | its positivity is a cardinality, a log-order of a finite group or a log-volume |
| Growth | Hilbert–Samuel along the ample class and a pointwise bound in degree zero, each proved |
| Non-circularity | defined before its sign; no interface field carries the conclusion |

A contribution must:

1. be an unconditional Lean theorem about an object of §3;
2. state its Euler characteristic and whether it is linear or quadratic;
3. state which effectivity law it proves (Riemann inequality, Hilbert–Samuel, degree-zero growth,
   Bézout, Northcott) and from what;
4. say what it gives on the golden datum, the complex fake, curves and the battery;
5. keep identities apart from signs and name the integer or log-volume that carries any sign;
6. record the positive survivor of every no-go.

Principles: effectivity is a growth law; integers over `ℤ` are log-torsions; the product formula is
the Bézout of the base; Riemann–Roch on the base is linear and free; a polarization from counting
needs a quadratic Euler characteristic; identities first, sign last; a reformulation is not a
reduction.
