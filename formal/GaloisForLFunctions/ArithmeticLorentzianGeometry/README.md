# Arithmetic Lorentzian Geometry (ALG)

**One question.** The Hodge index theorem was proved for matroids with no variety: start from
objects that are trivially Lorentzian, apply only operations that provably preserve the Lorentzian
signature, and arrive at the form whose signature is wanted. Weil's form of `ζ` has exactly that
signature problem: RH is the statement that the intersection form of the scaling surface of `ℤ`
has one positive square (`riemannHypothesis_iff_one_positive_square`). **Which part of that
signature can be produced by closure — by products, nonnegative substitutions, derivatives and a
local-to-global principle — from elementary positive objects attached to the primes, the scale and
the successor; what does each closure operation cost; and where exactly does closure stop?**

ALG is the combinatorial Hodge theory of the **affine monoid of the integers** `ℕ ⋊ ℕ^×`
(successor `S`, dilations `M_p`, `M_p S = S^p M_p`). Basic object: a **Lorentzian form**, a real
symmetric form with at most one positive square. Basic hypothesis: **a sign**, the nonnegativity of
the coefficients in a fixed gauge. Basic operation: a **closure step** that maps Lorentzian objects
to Lorentzian objects. Everything is unconditional; RH appears only inside equivalences.

Namespace `GaloisForLFunctions.ArithmeticLorentzianGeometry`; umbrella `ArithmeticLorentzianGeometry.lean`.

## Foundational contract

The arithmetic target is a signature theorem for the **specified Weil intersection form**,
including its archimedean term, pole plane and limiting test space. A Lorentzian form constructed
from prime data is useful only together with an exact identification, a valid pullback, or a
proved domination of that target. Positivity of coefficients, a scale substitution and a
Frobenius-shaped symmetry do not supply this bridge by themselves.

Three logically separate problems govern the programme: construct elementary forms and closure
operations; identify the arithmetic form they produce; preserve the resulting inequality in the
critical limit. A theorem solving the first problem must not be advertised as solving the other
two. In particular, lifting a quadratic form to higher degree helps only when the lift's local
signature is established independently of the desired global signature.

Gauge selection is likewise distinct from positivity. A fixed successor or archimedean kernel
can select a common nonnegative gauge, but uniqueness of that gauge does not establish a Hodge
index. Periodic Dirichlet characters with zeros at nonunits are not unit-valued points of the
full prime torus; any character comparison must specify its domain and local factors. The
relation between height-averaged pair correlation and a uniform inequality for all tests is a
research question, not an identification assumed by the programme.

---

## 1. Place in the research

The corpus has three walls (`docs/reports/review-2710/fable2.md`, §1.7): **W1** the critical
arithmetic sign (no positivity input distinguishes `ζ` from its sign twins), **W3** transfer (no
principle carries a sign from one local tower to another), **W14** realization (no variety, no
Frobenius over `ℤ`). Read as missing tools they ask for a Hodge index without a variety (W14), a
positivity theory whose hypothesis is a sign and not a symmetry (W1), and a local-to-global
principle that preserves positivity (W3). In the theory of Lorentzian polynomials, real-stable
polynomials and combinatorial Hodge theory all three are theorems. ALG is the arithmetic form of
that theory: it does not change any theorem of the corpus; it reorganizes the corpus around the
direction *elementary positive objects → closure → Weil's form*, instead of *Weil's form → search
for a symmetry*.

| Programme | Interface |
|---|---|
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md) | The target: the scaling-surface intersection form, its signature law, Hodge index = RH, the `𝔽_q` calibration and fake curves |
| [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | Weil planes, orbit correlations, Rosati positivity: the degree-2 face of the same signature problem |
| [ArithmeticIntersectionTheory](../ArithmeticIntersectionTheory/README.md) | Prime kernel = sum of transverse ladders; the base and the successor; the Hecke cocycle of renormalization |
| [RenormalizedArithmeticPotentialTheory](../RenormalizedArithmeticPotentialTheory/README.md) | Counterterm rank and survival; the regulator class read here as Loewner domination |
| [ArithmeticElectrostatics](../ArithmeticElectrostatics/README.md) | Atomic tests, the stability law, the coupled form `M + 2C² − 2S²`: the base cases of closure |
| [SpacingScaleHarmonicAnalysis](../SpacingScaleHarmonicAnalysis/README.md) | Owns the spacing scale `w ≍ 1/N` (question Q5 below); ALG supplies the signature language |
| [BiarithmeticGaugeGeometry](../BiarithmeticGaugeGeometry/README.md), [ArithmeticCorrelationGeometry](../ArithmeticCorrelationGeometry/README.md) | Gauge torus, real-sign unitary equivalence, successor connection, finite gauge subgroups |
| [RenormalizedBiarithmeticGeometry](../RenormalizedBiarithmeticGeometry/README.md), [ArithmeticPositiveDuality](../ArithmeticPositiveDuality/README.md) | Baumslag–Solitar relation on cells; the Bost–Connes successor forces the Hecke exponent |
| `RHTower` | Explicit formula, Weil criterion, pole term `2C² − 2S²`, Turán slices of `ξ`, Kloosterman–Weil bound |
| `HTGeometry/HermitianInertia` | Positive/negative index of Hermitian matrices, congruence invariance |

---

## 2. Why

**Positivity by closure.** Weil read the Hodge index off a variety. The corpus has shown that no
variety and no symmetry is available: every symmetry of Weil's form acts on an off-line fibre as a
boost, and a form invariant under a boost cannot be definite on the plane the boost preserves. The
alternative is the one that worked for matroids [Adiprasito–Huh–Katz; Brändén–Huh]: build the form
from trivially Lorentzian pieces by operations that preserve the signature. Three features of that
theory match the three walls.

* **The hypothesis is a sign.** A Lorentzian polynomial has nonnegative coefficients. A gauge twist
  of the primes destroys nonnegativity visibly, so a closure argument consumes the gauge charge at
  its input instead of hoping to find it at its output.
* **Local-to-global is a theorem.** The trickle-down theorem (Oppenheim; Anari–Liu–Oveis Gharan–
  Vinzant) derives the global signature of a weighted complex from the signatures of its links and
  the connectivity of the complex.
* **No variety is needed.** For matroids the links are again matroids and the base case is
  elementary; the Hodge index is a combinatorial consequence.

**The decomposition matters.** Sums of Lorentzian forms are not Lorentzian (`x² + y²`); products,
nonnegative substitutions and derivatives preserve the class. The explicit formula decomposes
Weil's form as a *sum* over primes and is therefore the wrong decomposition for closure; the Euler
product is a *product* in disjoint variables (the prime ladders are transverse,
`ladderKernel_mul_ladderKernel_eq_zero`). The archimedean place enters as the scale map
`n = ∏ p^{a_p} ↦ Σ a_p log p`, a nonnegative substitution of the ladder variables into one scale
variable. The pole plane `⟨H, V⟩` (`H² = V² = 0`, `H·V = 1`) is the single positive direction.

---

## 3. Objects and language

| Lorentzian theory | Arithmetic | Lean |
|---|---|---|
| symmetric form `Q`, quadratic `Q[x] = xᵀQx` | intersection form of the scaling surface on a finite family | `qf`, `bil` |
| at most one positive square | Hodge index; RH | `IsHyperbolic` |
| Lorentzian quadratic: `Q ≥ 0` entrywise and hyperbolic | intersection form in a nonnegative gauge | `IsLorentzian` |
| reverse Cauchy–Schwarz `Q[x]Q[y] ≤ (xᵀQy)²` for `Q[x] > 0` | Hodge index inequality `D²E² ≤ (D·E)²` (Khovanskii–Teissier at degree 2) | `IsHyperbolic` (definition) |
| negative semidefinite on a hyperplane | Weil positivity on degree-zero cycles | `isHyperbolic_of_nonpos_on_ker` |
| Loewner domination `Q ≼ Q'` | renormalization: a counterterm dominates | `IsHyperbolic.of_loewner` |
| conditionally negative definite (CND) kernel | Lévy–Khintchine/Markov forms; ladder metrics | `IsCND` |
| link `Q_i` of a vertex, contraction `Q = Σ_i Q_i` | local form at an atom/prime; global form | `TrickleDownDatum` |
| gauge (diagonal unitary conjugation) | prime gauge torus `Ω = ∏_p S¹` | — |
| ultra-log-concave coefficient sequence | Turán inequalities of `ξ` | — |

**Words.** *Hyperbolic*: at most one positive square. *Lorentzian*: hyperbolic with nonnegative
entries in the given coordinates. *Gauge*: a choice of unimodular phases on the atoms; the
signature is gauge-invariant, entrywise nonnegativity is not. *Nonnegative gauge*: a gauge in which
every kernel of the form is entrywise nonnegative. *Link*: the restriction of a symmetric 3-tensor
to one vertex. *Counterterm*: a positive semidefinite correction that dominates the form.
*Closure class*: the forms reachable from given elementary objects by the closure operations.

---

## 4. Principles

* **P1. Positivity by closure, never by symmetry.** A statement of the field produces a signature
  from operations that preserve it; an invariance of Weil's form is never an input.
* **P2. The sign is a gauge-fixing.** Entrywise nonnegativity is not gauge-invariant. Every twin of
  the prime kernel by a completely multiplicative unimodular `ε` is diagonally unitarily equivalent
  to the Euler kernel, so the prime kernel alone carries no sign. The sign becomes a hypothesis only
  when two kernels must be nonnegative *in one gauge*: the prime kernel and a kernel the torus does
  not act on (the archimedean kernel, the pole row, the successor).
* **P3. Local-to-global is multiplicative or it is a trickle-down.** The explicit formula's prime
  sum is a bookkeeping identity. Positivity transfers through products in disjoint variables, or
  through links and connectivity.
* **P4. The archimedean place is a substitution and a gauge-fixer**, not a kernel to be matched
  term by term.
* **P5. The pole is the positive direction.** The regulator freedom is Loewner domination: a form
  dominated by a hyperbolic form is hyperbolic.
* **P6. Truncation stability.** Statements must survive `N → ∞` with widths at the local spacing,
  where the tests see the zeros and every present theorem stops.

---

## 5. Mechanisms

1. **Degree two.** For a real symmetric form the following are equivalent: at most one positive
   square; reverse Cauchy–Schwarz at every vector of positive square; no positive definite plane;
   negative semidefinite on some hyperplane. With nonnegative entries this is the Lorentzian
   property at degree two. At degree two Lorentzian = Hodge index: there is no gain over ACS; the
   gain is in closure and in the higher-degree lifts.
2. **Counterterms dominate.** If `Q' − Q` is positive semidefinite and `Q'` is hyperbolic, so is
   `Q`. Adding a negative semidefinite form preserves hyperbolicity; adding a positive semidefinite
   rank-one form raises the positive index by at most one.
3. **Closure at degree two.** Pullback along any linear map preserves hyperbolicity; along a
   nonnegative map it preserves the Lorentzian property. The product of two nonnegative linear forms
   is Lorentzian. Sums fail. CND forms with nonnegative entries are Lorentzian, and CND is closed
   under sums and nonnegative scaling: the one class in which local-to-global *by sum* works.
4. **Trickle-down.** If a symmetric 3-tensor with nonnegative entries has hyperbolic links, its
   contraction `Q` satisfies `Q[v] ≤ (Qv)ᵀ D⁻¹ (Qv)` with `D = diag(Q·1)`; every positive square of
   `Q` then has normalized eigenvalue exactly one, and connectivity of the support of `Q` makes `Q`
   hyperbolic. Global signature from local signature and connectivity, with no variety.
5. **The gauge charge sits on the non-multiplicative kernels.** In canonical atomic coordinates the
   twisted prime kernel `ε(n/m)Λ(n/m)(n/m)^{−1/2}` is conjugate to the Euler kernel by the gauge
   `diag(ε(n))`. A kernel positive on every pair of atoms (the archimedean kernel) admits only the
   constant gauge. Hence a twin has a nonnegative gauge for both kernels iff `ε(p) = 1` on the primes
   of the horizon: the Lorentzian hypothesis selects the Euler point exactly through the place the
   torus does not act on.
6. **The univariate face.** A bivariate homogeneous polynomial with nonnegative coefficients is
   Lorentzian iff its normalized coefficients are log-concave with no internal zeros (Turán). For
   Jensen polynomials of `ξ` this is the Turán layer of Pólya's criterion; real-rootedness (RH) is
   strictly stronger. Lorentzian is the degree-two shadow of real stability.

---

## 6. Traps

| Trap | Truth |
|---|---|
| Nonnegative coefficients are a property of the form | They are a property of a basis: any finite family on a surface with a hyperbolic plane becomes entrywise nonnegative after the nef shift `f ↦ f + t(H + V)` |
| Lorentzian at degree two is new information | It is the Hodge index itself |
| Nonnegative coefficients single out the Euler point | Every unimodular twin of the prime kernel is gauge-equivalent to the Euler kernel; only a second, gauge-rigid kernel makes the sign a hypothesis |
| Nonnegative Euler products are positive | Beurling systems have nonnegative coefficients and an Euler product and can violate RH; any closure from nonnegative multiplicative local data alone is blind to that |
| Local Lorentzian pieces sum to a Lorentzian form | Sums do not preserve the class; only CND forms or a trickle-down datum transfer |
| The canonical intersection form is a Hessian of a nonnegative polynomial | Its diagonal is negative (atoms have negative self-intersection); only domination by a hyperbolic form is available |
| The positivity locus of the gauge torus is the successor-periodic locus | The archimedean characters `n^{iτ}` are torus points, not periodic, with prime form unitarily equivalent to Euler's; the correct locus is stated modulo them (Hecke characters `χ(n)n^{iτ}`), with asymptotic successor flatness |
| Lorentzian polynomials give real-rootedness | Lorentzian = log-concavity layer; real stability is strictly stronger (Turán vs Jensen hyperbolicity) |
| Trickle-down works without connectivity | Each connected component of the support contributes one positive square |

---

## 7. Questions

1. **Hodge index without a surface.** Which quadratic forms on the atoms `log n` are contractions
   of nonnegative 3-tensors with hyperbolic links, or Hessians of Lorentzian objects built from
   local factors at the primes and the scale map?
2. **The sign as a hypothesis.** In which gauges is the intersection form nonnegative, and which
   twins of the torus admit such a gauge? What is the positivity locus of the torus, modulo the
   archimedean characters?
3. **Transfer.** Which operations preserve the Lorentzian property on the affine monoid; is the
   Euler product one of them; is the successor?
4. **Realization.** What replaces Frobenius: a nonnegative operator `T` with `TᵀQT = λQ` on the
   Lorentzian structure, rather than an endomorphism of the ring `ℤ`?
5. **The critical regime.** What does the spacing scale `α = 1` look like in signature language?
   (Owned analytically by SSHA.)

---

## 8. Tools

To build, in order: the degree-two theory (hyperbolic and Lorentzian forms, the four
characterizations, domination, closure, CND); the bridge to the scaling surface (RH ⇔ reverse
Cauchy–Schwarz for cycles; the nef shift); the trickle-down theorem; the gauge-fixing theorem for
twins; Lorentzian polynomials of degree `d` in coefficient form (M-convex support, quadratic
derivatives), the bivariate = ultra-log-concave theorem and disjoint products; the successor defect
of the atomic prime form; the `𝔽_q` calibration of the trickle-down datum on the Frobenius ladder.

---

## 9. Research topics

1. Degree-two foundations and the scaling-surface bridge.
2. Gauges: nonnegative gauges for the prime, archimedean and pole kernels; the twin classification.
3. Trickle-down data on atoms: links at an atom, at a prime ladder, at a scale; connectivity.
4. The `𝔽_q` calibration: is the Frobenius span form a trickle-down contraction with elementary
   links (the Lorentzian lift of `frobeniusTower`)? A bounded-degree no would say the base is a weight.
5. Product versus sum: Lorentzian polynomials from the ladders in disjoint variables, the scale
   substitution, and the blindness of the multiplicative closure (Beurling data).
6. The successor as a closure operation: the successor defect `P_N(Sx) − P_N(x)` as a shifted-divisor
   correlation and its sign on the nonnegative cone.
7. The positivity locus of the torus modulo archimedean characters; asymptotic successor flatness.
8. The univariate face: Turán/Jensen as bivariate Lorentzian statements about `ξ`.
9. Frobenius substitutes: conformal Lorentzian maps `TᵀQT = λQ` among Hecke operators.
10. The dynamical layer: reflection positivity of the functional equation on the affine algebra.

---

## 10. Pillar theorems

Targets of the programme; each is stated unconditionally.

1. **Degree-two equivalences** and **domination** (counterterm principle).
2. **Scaling-surface Hodge index as reverse Cauchy–Schwarz**: RH ⇔ `D²E² ≤ (D·E)²` for all finite
   families of cycles with `D² > 0`.
3. **Nef shift**: entrywise nonnegativity in some nef basis is automatic.
4. **Trickle-down**: hyperbolic links + connectivity ⇒ one positive square.
5. **Gauge-fixing**: a twin admits a gauge making the prime kernel and a pairwise-positive kernel
   simultaneously nonnegative iff it is the Euler point on the primes of the horizon.
6. **Bivariate Lorentzian = ultra-log-concave.**

---

## 11. Success criteria and contributions

Success:

* **C1.** Reproduce Weil's theorem for curves from the Frobenius ladder by closure (no surface), or
  prove that no bounded-degree closure from the ladder exists.
* **C2.** Fail visibly at the Liouville point: the hypothesis is lost and the pole on the line is
  the consequence.
* **C3.** Separate Hecke characters from the rest of the torus by the successor.
* **C4.** Recover every unconditional positivity of the corpus as an easy closure statement and
  locate the single missing closure operation at the spacing scale.
* **C5.** No hidden hypotheses: everything unconditional and formalized.
* **C6.** Theorems short of RH on the way.

A contribution is unconditional; is stated in signatures, gauges, closure operations or links;
says what it gives over `𝔽_q`, at a sign twin and on a Beurling or fake datum; names the closure
operation it uses or rules out; and records the positive survivor of every no-go.
