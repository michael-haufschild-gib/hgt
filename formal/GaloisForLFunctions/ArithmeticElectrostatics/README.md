# Arithmetic Electrostatics of the Zero Divisor (AES)

**One question.** The nontrivial zeros of `ζ` are the charges of one logarithmic potential,
`U = log |ξ|`. Arithmetic already computes four quantities of that potential: its Laplacian (the
collided form `D`), its regularized gradient at the charges (the field `E`, read off `Λ ⋆ Λ`), its
renormalized self-interaction at the diagonal (torsion log-discriminants, the double pole of
`(ζ′/ζ)²`), and its reflection pairing (Weil's form `W`). RH says that the configuration is in
**transverse equilibrium**: no zero feels a field across the critical line. Equilibrium is
computed; its stability is the sign. Which inequality between the computed quantities makes the
equilibrium stable, which renormalization of the diagonal joins positivity and equivariance, and
which of these inequalities are provably out of reach of the inputs the corpus has?

AES is the potential theory of two charge carriers and of the dictionary between them:

- the **conjugate diagonal**: the zero divisor `Z = Σ_ρ m_ρ δ_ρ` in the critical strip, with the
  reflection `ρ ↦ 1 − ρ` (computed by the explicit formula) and the conjugation `ρ ↦ ρ̄` (computed by
  potential theory of `log |ξ|`);
- the **characteristic circle** `ℝ/ℤ`: torsion orbits `O_n` (primitive `n`-th roots of unity) as
  charges, `−log |1 − z w̄|` as Green function, power maps `z ↦ z^t` as Hecke correspondences, the
  arithmetic point `z = 1` as distinguished fibre.

Its organizing sentence:

> *RH is the coincidence on the zero divisor of reflection and conjugation; in electrostatic terms,
> the statement that every zero is in transverse equilibrium. The explicit formula is the
> equilibrium equation; what it does not supply is stability.*

Namespace `GaloisForLFunctions.ArithmeticElectrostatics`; umbrella `ArithmeticElectrostatics.lean`.
Everything is unconditional; RH and its partial forms appear only inside equivalences.

---

## 1. Place in the research

The frontier ([obstacles summary](../../../docs/reports/review-2710/obstacles-summary.md), §4) maps
every forcing mechanism found so far and its sharp limit. What is missing has a precise shape: an
inequality that turns the computed positive form, or the computed field, into a bound; or a
renormalization that keeps a positive equivariant family positive at the diagonal. Over `𝔽_q` both
come from a polarization of `C × C`: Riemann–Roch gives the positive trace, the Frobenius is a
similitude, the self-intersection of the diagonal is the finite number `2 − 2g`. Over `ℤ` the
pieces exist in separate programmes, each with one property and not the other. AES is the
language in which they are one object — energy, field, self-energy and pairing of one potential —
and the place where the joining inequality (the *adjunction*) is stated, tested and, where
possible, proved.

| Programme | What AES takes | What AES adds |
|---|---|---|
| [ArithmeticPolarization](../ArithmeticPolarization/README.md) | `W`, `D`, `Δ`, `Re W = D − Δ`, Hecke law of `D`, log-Sobolev equivalence, local Weyl law, `σ_γ` and the forcing half | `D` as the energy of the Riesz measure of `log |ξ|`; `W` as its reflection pairing; the defect as the failure of reflection = conjugation |
| [ConjugateDiagonalGeometry](../ConjugateDiagonalGeometry/README.md) | the `ξ` current, theta-prefix metrics, depth distributions, local zero detection | the field and the transverse energy as further computed quantities of the same current |
| [ArithmeticCorrespondencePositivity](../ArithmeticCorrespondencePositivity/README.md) | quadratic terminals, outward rays, the transverse field `xiTransverseField`, the field of a finite configuration `fieldAt` and its appearance in `(ζ′/ζ)²` | the virial laws, the renormalized square, the field as residue of `ξ″/ξ` |
| [ArithmeticEffectivityTheory](../ArithmeticEffectivityTheory/README.md) | torsion orbits, `I(m, n)`, the Hecke law `I(m, mt) = φ(m)Λ(t)`, Abel energies `T_r`, the renormalized torsion limit, the Farey potential | self-intersections of torsion orbits, adjunction along Hecke orbits, conjugation on torsion cycles, counterterm rates |
| `RHTower` (transverse chain) | the transverse force and its marginality identity, the zero network, the maximum principle, the attainment dichotomy, angular energy quantization, the Calogero virial | the energy of the whole divisor, its finiteness law, the work–energy identity |
| [BiarithmeticGaugeGeometry](../BiarithmeticGaugeGeometry/README.md), [ArithmeticCorrelationGeometry](../ArithmeticCorrelationGeometry/README.md) | the gauge torus, successor holonomy, Diophantine repulsion, quantization of surplus residues | gauge charge of electrostatic quantities |
| [ArithmeticCastelnuovoSeveri](../ArithmeticCastelnuovoSeveri/README.md), [ArithmeticOrientationGeometry](../ArithmeticOrientationGeometry/README.md) | the scaling surface, Hodge index, Pontryagin law, `𝔽_q` calibration, curve data and fakes | the electrostatic reading of Weil's adjunction `Γ² = q(2 − 2g)` |

AES does not re-prove what these programmes own; it imports them and builds the laws that relate
them.

---

## 2. Why

**Two involutions.** The zero divisor of `ξ` is invariant under reflection `s ↦ 1 − s` and under
conjugation `s ↦ s̄`. The explicit formula computes sums `Σ_ρ m_ρ h(ρ)` with `h` holomorphic: it
sees the reflection, and its natural pairing is Weil's form `W(f) = Σ m f̂(ρ) conj f̂(1 − ρ̄)`.
Potential theory of `log |ξ|` sees the conjugation: the Riesz measure `(1/2π) Δ log |ξ|` is the
zero divisor, and its natural pairing is the collided form `D(f) = Σ m |f̂(ρ)|²`. The two pairings
agree exactly when `ρ̄ = 1 − ρ` at every zero, i.e. on the critical line. `W` is equivariant and its
positivity is RH; `D` is positive and its equivariance is RH (APol).

**Stieltjes.** The zeros of classical orthogonal polynomials are equilibrium positions of unit
charges in an external field: at each zero, the field of the other zeros balances the external
field, and the equilibrium equation is the differential equation of the polynomial evaluated at
its zeros. For `ξ` the equilibrium equation is the explicit formula and the external field is the
Γ-factor with the pole; but `ξ` satisfies no linear differential equation (it is differentially
transcendental), so equilibrium cannot be derived variationally. What can be derived, on every
finite configuration and on the actual divisor, are the **virial laws**: the work of the field
against a displacement equals an energy. The transverse virial law turns the field into a
nonnegative quadratic energy of the displacements `δ_ρ = Re ρ − ½`, positive definite on
reflection-odd displacements. Equilibrium is the vanishing of the field; stability is positivity
of that energy; RH is equilibrium.

**Quantization.** A zero off the line and its reflection partner `1 − ρ̄` have the same ordinate.
The segment joining them is horizontal, and their contribution to the transverse energy is exactly
`m_ρ m_{ρ*}`, independent of the depth. The transverse energy of a reflection-closed
configuration is therefore either `0` or at least `1`. RH has a gap form: any upper bound for the
transverse energy strictly below one is RH. Detection (a positive field at a zero) becomes a
quantized lower bound; the missing input is an upper bound, an arithmetic inequality for the field.

**One diagonal, three appearances.** Weil's self-intersection `Δ·Δ = 2 − 2g`, the torsion
self-energy `log(1/(1 − r))` of a root of unity, and the double pole `m²/(s − ρ)²` of `(ζ′/ζ)²` are
self-terms of one potential. Removing each leaves the content: the Lefschetz trace, the prime
kernel, the field. In both arithmetic instances the self-term is renormalized by the **degree**:

- on the zero side, `(ζ′/ζ)² + (ζ′/ζ)′ = ζ″/ζ`; the counterterm `(ζ′/ζ)′` has Dirichlet coefficients
  `Λ(n) log n` (the von Mangoldt weight times the degree `log n` of the Hecke correspondence `T_n`),
  and the renormalized source is Selberg's `Λ₂ = Λ log + Λ ⋆ Λ = μ ⋆ log²`, a nonnegative arithmetic
  function. At a zero of order `m` the self-term drops from `m²` to `m(m − 1)` and vanishes at simple
  zeros; the residue is twice the field;
- on the circle, the self-intersection per point of the torsion orbit of order `n` (the
  log-discriminant of `Φ_n` divided by `φ(n)`) is `log n − Σ_{p∣n} log p/(p − 1)`: the degree `log n`
  minus local terms at the primes dividing `n`. Along a Hecke orbit it grows by exactly `log p` per
  step once `p ∣ n` — an adjunction formula.

This is the arithmetic form of Weil's adjunction `Γ_m² = q^m Δ²`, and the question of the
programme is whether the same degree renormalization, paid by the archimedean place, keeps a
positive equivariant family positive.

**Why a field.** The corpus has every forcing mechanism with a sharp limit. Invariant positivity is
isotropic; elliptic localization stops at the conductor; collided positivity is free, computed and
blind; zero-side reserves detect; budgets and counts are the sign. Each of these is a statement
about one quantity of the potential. The joining statement — a Hodge index theorem with
adjunction — is about all four at once.

---

## 3. Objects and language

| Electrostatics | Zero divisor of `ξ` | Characteristic circle | Over `𝔽_q` | Lean |
|---|---|---|---|---|
| charges | zeros `ρ`, multiplicities `m_ρ` | torsion orbits `O_n`, charge `x_n` per point | Frobenius eigenvalues on lines `Re s = ½` | `XiZeroCopy`, `XiDivisorSupport`, `primitiveRoots` |
| potential | `log |ξ(s)|` | `Σ x_n Σ_{ζ∈O_n} log |z − ζ|` | `log |Z_C(q^{−s})|` | — |
| Riesz measure (Laplacian) | `Σ m δ_ρ`; energy `D(f) = Σ m |f̂(ρ)|²` | torsion measure `ν = Σ x_n μ_{O_n}` | — | `collidedForm` |
| field at a charge | `E(ρ) = Σ_{q≠ρ} m_q/(ρ − q)` (symmetric sum); simple coefficient of `(ζ′/ζ)²` is `2mE` | `Σ_η 1/(ζ − η)` | — | `fieldAt`, `xiTransverseField`, `transverseForce` |
| transverse field | `Re E(ρ) = Σ m_q (Re ρ − Re q)/|ρ − q|²` | — | `0` (unitarity) | `xiTransverseField` |
| conductance | `1/|ρ − q|²` | — | — | `zeroConductance` |
| transverse energy | `½ Σ_{ρ≠q} m m (Re ρ − Re q)²/|ρ − q|²` | — | `0` | planned |
| self-energy (diagonal) | double pole `m²` of `(ζ′/ζ)²`; renormalized: `m(m − 1)` in `ζ″/ζ` | `log(1/(1 − r))` per point; renormalized: `log disc Φ_n / φ(n)` | `Δ² = 2 − 2g` | `torsionEnergy`, `orbitIntersection` |
| interaction | Weil's form `W` (reflection pairing) | `I(m, n) = log |Res(Φ_m, Φ_n)|` | `Γ_m · Δ` | `Z.W`, `orbitIntersection` |
| external field | Γ-factor and the pole | Mahler measure, the uniform measure | — | — |
| distinguished fibre | the critical line | the arithmetic point `z = 1` | the fibre over `𝔽_q` | — |
| symmetry | reflection, conjugation, Hecke translations | conjugation `z ↦ z̄ = z^{−1}`, power maps `z ↦ z^t` | Frobenius, Rosati | `supportPartner` |

**Words.**

- *Equilibrium* (at a charge): vanishing transverse field. *Transverse equilibrium* (of a
  configuration): equilibrium at every charge. *Stability*: positivity of the energy whose
  gradient is the field.
- *Work*: `Σ m_ρ δ_ρ Re E(ρ)` with displacement `δ_ρ = Re ρ − ½`. *Virial law*: work = energy.
- *Quantum*: the transverse energy `m_ρ m_{ρ*}` of a reflection pair; *gap*: no reflection-closed
  configuration has transverse energy in `(0, 1)` (integer multiplicities).
- *Self-term*: the coefficient of the diagonal singularity (double pole, `log(1/(1 − r))`, `Δ²`).
  *Regularized*: the singularity is cut off (`r < 1`, `ε > 0`); *renormalized*: a counterterm is
  subtracted and the limit taken. *Counterterm*: what is subtracted; *Hecke compatible*: commuting
  with power maps or Hecke translations; *positivity preserving*: the regularized forms minus the
  counterterm stay positive.
- *Adjunction*: an identity expressing a self-term through the degree of a correspondence.
- *Computed*: produced by an identity from arithmetic (explicit formula, `ξ` current, resultants,
  Laurent coefficients of Dirichlet series). *Bounded*: controlled by an arithmetic inequality.
  *Posited*: assumed. *Detected* / *excluded*: shown visible / shown absent.
- *Collided* (conjugate) and *Rosati* (reflection) pairing; *hyperbolic*, *elliptic*, *unipotent*
  local type; *even*/*odd* sector; *below*/*beyond* the conductor; *gauge invariant*/*charged*;
  *aligned*/*generic* heights — as in APol, ACG and ACP.

Parameters: the configuration (finite, or the actual divisor), multiplicities, depth `a`, ordinate
`γ`, regularization `r` or `ε`, the set of orders `S` or the bound `N`. Every theorem states which
are fixed and which grow.

---

## 4. Mechanisms

1. **Virial laws** (finite configurations). For distinct charges `z_j` with multiplicities `m_j`
   and field `E_j = Σ_{k≠j} m_k/(z_j − z_k)`:
   `Σ_j m_j E_j = 0` (Newton's third law); `Σ_j m_j z_j E_j = ½((Σm)² − Σm²)` (Stieltjes' virial, a
   pure count); `Σ_j m_j (Re z_j − c) Re E_j = ½ Σ_{j≠k} m_j m_k (Re z_j − Re z_k)²/|z_j − z_k|²` (the
   transverse virial: the work of the field is a Dirichlet energy on the complete graph of charges
   with conductances `m_j m_k/|z_j − z_k|²`). The transverse and vertical energies add up to the
   count `½((Σm)² − Σm²)`: a configuration is critical exactly when all its energy is vertical.
2. **Equilibrium is the critical line** (reflection-closed configurations). Transverse equilibrium
   ⇔ zero work ⇔ nonpositive work ⇔ every charge on `Re s = ½`. The transverse energy is at least
   `Σ_{off-line pairs} m_ρ m_{ρ*}`; with integer multiplicities it is `0` or `≥ 1`. The deepest
   charge feels an outward field, the shallowest an inward one (maximum principle).
3. **The divisor.** The transverse energy of the zero divisor of `ξ` is a well-defined element of
   `[0, ∞]`. It vanishes iff RH, it is `< 1` iff RH, it is finite iff the off-line set is finite,
   and then it equals the work of the off-line zeros against the transverse force. The marginality
   identity `transverseForce ρ = 0` (RHTower) is the equilibrium equation; its attained case is RH
   (maximum principle); the non-attained case is escape of depth to infinite height.
4. **The field is computed.** At a zero of order `m` of an analytic function `F`, the regular part
   `R(ρ)` of `F′/F` is the simple Laurent coefficient of `(F′/F)²` divided by `2m`, and the residue of
   `F″/F` divided by `2m`; the double-pole coefficients are `m²` and `m(m − 1)`. For `ξ` the regular
   part is the field of the other zeros (corpus: `XiTerminalRegularField`).
5. **Adjunction on the zero side.** `ζ″/ζ = (ζ′/ζ)² + (ζ′/ζ)′` has Dirichlet coefficients
   `Λ₂ = Λ ⋆ Λ + Λ log = μ ⋆ log² ≥ 0` (Selberg): the degree counterterm `Λ log` removes the
   self-term at every simple zero and keeps the source nonnegative.
6. **Adjunction on the circle.** `I(n, n) = log |disc Φ_n| = φ(n) log n − (φ ⋆ Λ)(n)`; the
   self-intersection per point is `ℓ_n = log n − Σ_{p∣n} log p/(p − 1)`; along the Hecke orbit of `p`
   it grows by `log p` per step once `p ∣ n`. Conjugation is the power map `z ↦ z^{−1}`, fixes every
   torsion orbit, and makes the Hermitian kernel `−log |1 − r ζη̄|` and the bilinear kernel
   `−log |1 − r ζη|` agree on torsion cycles: on the circle the collided and the Rosati pairing
   coincide, and positivity (Abel energies, `r < 1`) and the Hecke law (`r = 1`) are properties of
   one form, separated only by the self-energy.
7. **Counterterm rate.** The least multiple of the self-energy that makes the renormalized torsion
   pairing on orders `≤ N` nonnegative is `Θ(log N)`: at least the self-intersection of the largest
   prime orbit, at most a constant times `log N` (Schur test with weights `n^{−1/2}` and Mertens).
   The renormalization is logarithmic in the order, like the archimedean self-energy `log(1/ε)` of an
   atom of width `ε`; the two match at the scale `ε ≍ 1/N` of the atoms `log n`, `n ≤ N`.
8. **The arithmetic point.** `z = 1` is the only point of the circle fixed by every power map.
   `Λ(n) = Σ_{ζ∈O_n} log |1 − ζ|` is the potential of the orbit `O_n` at the arithmetic point (its circle
   mean is `0`), `ψ(N)` the potential there of the Farey torsion, and RH a bound on that potential
   (corpus: `vonMangoldt_eq_sum_log_norm_one_sub`, `psi_eq_fareySum`, `riemannHypothesis_iff_fareySum`).

---

## 5. Pillar theorems

| Pillar | Statement |
|---|---|
| **ES1 Virial laws** | Newton's third law, Stieltjes' virial and the transverse virial on every finite configuration; transverse + vertical energy = `½((Σm)² − Σm²)` |
| **ES2 Equilibrium is the critical line** | on reflection-closed configurations with positive multiplicities: transverse equilibrium ⇔ nonpositive work ⇔ critical; quantum `m_ρ m_{ρ*}` per off-line pair; gap below `1`; maximum and minimum principle |
| **ES3 The energy of the divisor** | transverse energy of the `ξ` divisor: `= 0` ⇔ RH ⇔ `< 1`; finite ⇔ finitely many off-line zeros; work = energy in the finite case |
| **ES4 The renormalized square** | `F″/F` at a zero of order `m`: double pole `m(m − 1)`, residue `2m R(ρ)`; Dirichlet coefficients of `ζ″/ζ` are `Λ₂ = μ ⋆ log² ≥ 0` |
| **ES5 Torsion adjunction** | `ℓ_n = log n − Σ_{p∣n} log p/(p − 1)`; adjunction along Hecke orbits; conjugation fixes torsion cycles and identifies the Hermitian and bilinear torsion pairings |
| **ES6 Logarithmic counterterm** | minimal renormalization on orders `≤ N` is `Θ(log N)` |
| **ES7 The arithmetic point** | the unique common fixed point of the power maps; `Λ` as its potential; RH as a potential bound |

Inherited pillars, used throughout: `Re W = D − Δ`, `D` faithful, coercive and log-Sobolev (APol);
the transverse force and its marginality identity, the maximum principle, the attainment dichotomy
and angular energy quantization (RHTower); critical configurations in transverse equilibrium, the
deepest off-line zero with positive field, quadratic terminals with a logarithmic reserve (ACP); the
Hecke law of torsion orbits and the renormalized torsion limit of the prime kernel (AET).

---

## 6. Questions the programme must answer

1. **What is the Frobenius at infinity as a correspondence?** On the circle: conjugation is the
   power map of degree `−1`; it fixes every torsion cycle. On the divisor: which correspondence acts
   as `ρ ↦ ρ̄` on the zeros while being computed by arithmetic?
2. **What is the self-intersection of the diagonal?** Which renormalization of the torsion
   self-energy and of the double pole of `Λ ⋆ Λ` is Hecke compatible and positivity preserving?
3. **What bounds the field?** Which arithmetic inequality caps the transverse field, or `ζ′/ζ` on
   outward rays, below the reserve?
4. **What bounds the equivariance defect of the computed positive form?**
5. **What is the arithmetic point, and what is its period?**
6. **How does `σ_γ` localize beyond the conductor; are zero ordinates aligned with small primes?**
7. **What is the non-archimedean gauge charge of the electrostatic quantities?**
8. **Is the coupled class bounded at the centre?**
9. **What selects the fibre?**
10. **What are the escape states of `ζ` at infinite height** (equivalently: is the supremum of the
    depth attained)?
11. **How does an average or a proportion become a point?**
12. **What is the base?**

Each answer is a theorem, an equivalence with a named open statement, or a sharp no-go with its
positive survivor.

---

## 7. Traps

| Trap | Truth |
|---|---|
| Equilibrium can be derived variationally, as for Stieltjes | Stieltjes needs a linear ODE; `ξ` satisfies none |
| The marginality identity is an inequality waiting for a proof | It is RH-equivalent; its attained case is RH by the maximum principle, its non-attained case is escape |
| A positive field at the deepest zero excludes it | It detects; exclusion needs an upper bound for the field |
| The transverse energy decays as zeros approach the line | It is quantized: each off-line pair carries a full unit, at every depth |
| Removing the diagonal from a positive energy keeps it positive | Discrete charges without self-energy have no sign; the counterterm is the content |
| `Λ ⋆ Λ ≥ 0` is positivity beyond isotropy | It is nonnegativity of coefficients; the field enters only through Laurent coefficients |
| The torsion pairing lacks Hecke equivariance | It has the Hecke law exactly; it lacks positivity only at the diagonal |
| Conjugation is the missing correspondence over `ℤ` | On the circle it is a power map; on the divisor it is the collided form, which is not computed by the explicit formula |
| Energy controls the potential at a point | Logarithmic energy does not bound pointwise potentials (Franel–Landau is a potential at one point) |

---

## 8. Tools

**From sibling programmes:** the two forms and the defect, coercivity and the log-Sobolev norm;
the `ξ` current and theta metrics; terminals, outward rays, the transverse field and the
Rankin–Selberg Laurent structure; torsion orbits, resultants, Ramanujan sums, Abel energies and the
gcd twist; the transverse force, the zero network, the maximum principle and angular energy; Mertens'
estimates and Chebyshev bounds; Selberg's identity `Λ log + Λ ⋆ Λ = μ ⋆ log²`
(`vonMangoldt_pmul_log_add_mul_self`).

**To build here:** the virial calculus of finite configurations; the transverse energy of the
divisor; renormalized squares and their Laurent self-terms; self-intersections and adjunction of
torsion orbits; counterterm rates; the arithmetic point; stability laws.

**Not yet built anywhere** (the report's list): arithmetic adjunction preserving positivity; field
and defect inequalities beyond density estimates; Diophantine control of zero ordinates; gauge
margin laws; Hermitian structures on correspondence spaces with computed similitudes.

---

## 9. Open research topics

1. **A field law**: an arithmetic upper bound for the transverse field at the zeros, or for the
   transverse energy of a window, strictly below the quantum.
2. **A stability law (Hodge index with adjunction)**: on degree-zero torsion cycles, the
   renormalized pairing plus the archimedean self-energy is positive, with the renormalization that
   turns the double pole of `Λ ⋆ Λ` into the field.
3. **Matched renormalization**: compare the torsion counterterm on orders `≤ N` with the archimedean
   self-energy of atoms at width `1/N`, constants included.
4. **Electrostatics of the twins**: the field and the energy of the Liouville and sign twins; which
   electrostatic quantity carries gauge charge.
5. **Attainment**: escape of depth to infinite height for the actual divisor.
6. **Alignment**: moments of short prime polynomials at zero ordinates, the electrostatic reading of
   the outward reserve.

---

## 10. Success criteria and what a contribution must be

AES succeeds when it proves a stability law of a type the corpus does not contain — an inequality
between computed quantities of the potential that turns detection into exclusion on a stated class
— or a sharp no-go naming the missing input, with its positive survivor; and when every question of
§6 has an answer of that kind.

A contribution must:

1. be an unconditional Lean theorem about an object of §3;
2. name which of the four quantities (energy, field, self-energy, pairing) it concerns and on which
   carrier (divisor or circle);
3. keep identities (equilibrium, virial, adjunction) apart from signs (stability);
4. state whether it is computed, bounded or posited, and whether it detects or excludes;
5. state its behaviour on reflection-closed finite configurations, on curves over `𝔽_q`, and on the
   battery (golden datum, complex fake, twins, multi-pair configurations);
6. record the positive survivor of every no-go.

Calibration: transverse equilibrium of critical configurations; the quantum of a reflection pair;
`W = D − Δ`; the Hecke law of torsion orbits; Selberg's identity; the Farey potential of `ψ`; Weil
for curves.

Principles: equilibrium is computed, stability is the sign; renormalize by the degree; a detection
is not an exclusion; identities first, sign last; a reformulation is not a reduction.
