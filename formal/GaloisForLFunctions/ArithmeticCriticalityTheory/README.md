# Arithmetic Criticality Theory

Positive solutions, ground-state representations and criticality of the arithmetic jump operator
whose nonnegativity on odd tests is the Riemann Hypothesis.

Lean namespace `GaloisForLFunctions.ArithmeticCriticalityTheory`, umbrella
`GaloisForLFunctions/ArithmeticCriticalityTheory.lean`. This file is the introduction to the theory:
why it exists, what its objects are, how its mechanisms work, where its traps lie, and what it leaves
open. Progress and status live on the pipeline card, not here. To locate a statement, search the
corpus (`scripts/formal_tools.py research "<words>"`); a few central Lean names are given in
parentheses as entry points.

---

## 1. Why: the sign problem and the criticality viewpoint

### 1.1 RH as the positivity of a jump form

Riemann's kernel

    Θ(u) = Σ_{n≥1} e^{u/2} (4π²n⁴e^{4u} − 6πn²e^{2u}) e^{−πn²e^{2u}}

is even, positive, strictly decreasing on `[0, ∞)`, super-exponentially decaying, and its Fourier
transform is Riemann's `Ξ`; `∫ Θ(u) cosh(u/2) du = 1/2`, `∫ Θ(u) sinh(u/2) du = 0`. The corpus proves
an RH criterion of Hardy type: for the odd sector,

    RH  ⟺  for every odd v ∈ C²_c(ℝ):   ∫ Θ(x) cosh(x/2) v(x)² dx  ≤  E_arch(v) + E_prime(v),

    E_arch(v)  = ∫_{t>0} ω(t) ∫_ℝ Θ(x)Θ(x+t) (v(x) − v(x+t))² dx dt,    ω(t) = e^{−t/2}/(1 − e^{−2t}),
    E_prime(v) = Σ_{n≥2} Λ(n) n^{−1/2} ∫_ℝ Θ(x)Θ(x+log n) (v(x) − v(x+log n))² dx

(`riemannHypothesis_iff_forall_odd_phiDoob_markovEnergy_nonneg`; the Markov energy of the test `Θv`
is `E_arch + E_prime − ∫ Θ cosh(x/2) v²`). The right side is the energy of a jump process: jumps of
length `t` at the archimedean rate `ω(t) dt`, jumps of length `log n` at the prime rate
`Λ(n) n^{−1/2}`, both weighted by `Θ(x)Θ(x+t)`. The left side is a potential term whose weight
`Θ cosh(x/2)` is produced by the pole of `ζ`. So RH says: the Schrödinger-type form

    Q(v) = (jump energy of v) − (potential of v)

is nonnegative on odd tests. On even tests it is not: `Q(1) = −1/2`.

### 1.2 Why bounding fails and what replaces it

Estimating the two sides of the inequality separately produces identities, finite classifications
and positivity on restricted families, never a sign on the whole odd sector: any estimate loses a
constant factor, and the inequality has none to spare. In the theory of Dirichlet forms the sign
question has a different shape. A form `E − ρ` is nonnegative if and only if there is a **positive
supersolution** `ω`, that is `Lω ≥ ρω` with `L` the generator of `E` (Allegretto–Piepenbrink), and the
proof is an exact identity, the **ground-state representation**:

    E(ωu) − ∫ ρ (ωu)² = (a nonnegative remainder, quadratic in the differences of u) + ∫ u² ω (Lω − ρω).

If `Lω ≥ ρω`, every test factoring as `v = ωu` has nonnegative form. Arithmetic Criticality Theory
develops this mechanism for the arithmetic jump operator. A bounding problem becomes an existence
problem for a single positive function, and when no such function exists, the same identity shows
exactly which quantity must carry the positivity instead.

Criticality theory exists for local Schrödinger operators and for translation-invariant jump
kernels. It did not exist for a kernel whose jump lengths are logarithms of prime powers, whose
rates are `Λ(n) n^{−1/2}`, and whose potential is the pole of the zeta function. The language of
Pinchover applies verbatim: a form is **supercritical** if it takes a negative value, **critical** if
it is nonnegative but admits no nonzero Hardy weight `W ≥ 0` with `Q ≥ ∫ W v²`, and **subcritical** if
such a weight exists. RH is the statement that the odd arithmetic form is not supercritical.

---

## 2. What: objects and language

### 2.1 Coordinates and gauges

Every statement is made in one of two coordinate systems, and mixing them is the first trap.

- **Test coordinates.** The object is the test `F = Θ v` (or the profile `v`) that enters the Markov
  energy.
- **Doob coordinates.** The object is the quotient `u = v/ω` relative to a chosen function `ω`, the
  **gauge**. Potentials, generators, sources and supersolutions live here. The **test coordinate** of
  a gauge is `M = Θ ω`; a gauge is named by either.

A test factoring through the gauge `ω` is `v = ω u`, i.e. `Θ v = M u`; `u` is the **profile**. The
gauges in use:

| Gauge | Test coordinate `M` | Source `𝓛_D ω − Θ cosh(x/2) ω` |
|---|---|---|
| constant `1 = τ_0` | `Θ` | `−Θ(x) cosh(x/2)` |
| translate ground state `τ_b = Θ(· − b)/Θ` | `Θ(· − b)` | `−Θ(x) cosh((x − b)/2)` |
| shifted ground state `ω_a = τ_a − τ_{−a}` | `m_a(y) = Θ(y − a) − Θ(y + a)` (odd, `> 0` on `(0, ∞)`) | `2 sinh(a/2) sinh(x/2) Θ(x)` |
| finite span `Σ_j c_j ω_{a_j}` | `Σ_j c_j m_{a_j}` | `2σ sinh(x/2) Θ`, `σ = Σ c_j sinh(a_j/2)` |
| translate combination `Σ_j α_j τ_{b_j}` | `Σ_j α_j Θ(· − b_j)` | `−Θ(A cosh(x/2) − B sinh(x/2))`, `A = Σ α_j cosh(b_j/2)`, `B = Σ α_j sinh(b_j/2)` |
| theta convolution `ω_φ = (Θ ∗ φ)/Θ`, `φ ∈ C²_c` | `Θ ∗ φ` | `−Θ(A_φ cosh(x/2) − B_φ sinh(x/2))`, `A_φ = ∫ φ cosh(b/2)`, `B_φ = ∫ φ sinh(b/2)` |
| smeared ground state `ω_ν = ∫ ν(c) ω_c dc`, `ν ≥ 0` on `(0, ∞)` | `∫ ν(c) m_c dc` (odd, `> 0` on `(0, ∞)`) | `σ sinh(x/2) Θ`, `σ = 2∫ ν(c) sinh(c/2) dc` |
| profile gauge `M/Θ`, any decaying `M` | `M` | `−Θ · 𝒲M` |
| plateau gauge, `0 ≤ M ≤ 1`, `M = 1` on `[−r, r]`, `M = 0` off `(−R, R)` | `M` | `−Θ · 𝒲M`, purely archimedean on the window when `2R < log 2` |

A gauge is **harmonic** when its source vanishes (`A = B = 0`, resp. `A_φ = B_φ = 0`, resp.
`σ = 0`); harmonic gauges form the **harmonic theta span**, infinite-dimensional in every family
above, and none of them is positive on the half line. The **shift quotient** of an odd test `F`
vanishing near the origin is `F/m_a`, an even `C²_c` profile.

### 2.2 The jump structure and the pole-free Weil operator

| Object | Definition | Lean |
|---|---|---|
| Jump measure | `dm(t) = ω(t) dt + Σ_{n≥2} Λ(n) n^{−1/2} δ_{log n}` on `t > 0` | `archLevyDensity`, `vonMangoldtAtom` |
| Potential | `ρ(x) = Θ(x) cosh(x/2)` | `phiDoobCoshMass` |
| Doob jump energy | `E(v) = E_arch(v) + E_prime(v) = ∫ dm(t) ∫_ℝ Θ(x)Θ(x+t)(v(x) − v(x+t))² dx` | `phiDoobArchJump`, `phiDoobPrimeJump` |
| Single-length jump energy | `J_ℓ(v) = ∫ Θ(x)Θ(x+ℓ)(v(x) − v(x+ℓ))² dx` | `shiftJumpEnergy` |
| Markov energy | `Q(Θv) = E(v) − ∫ ρ v²` | `markovEnergy (phiDoobTest v)` |
| Pole-free Weil operator | `𝒲M(x) = Σ_n Λ(n)n^{−1/2}(M(x+log n) + M(x−log n)) − ∫_0^∞ [2ν(u)M(x) − ω(u)(M(x+u) + M(x−u))] du + (γ + log π)M(x)`, `ν(u) = e^{−2u}/(1 − e^{−2u})` | `poleFreeWeilOperator` |

The archimedean density has a `1/(2t)` singularity at `0` and decays like `e^{−t/2}`; the prime
atoms have total mass `Σ Λ(n) n^{−1/2} = ∞`. Consequently a "total jump rate"
`∫ dm(t) (Θ(x+t) + Θ(x−t))` does not exist; only differences `ω(x) − ω(x ± t)` are integrable.
Every generator below is defined through differences. The **harmonic identity** of Riemann's kernel
is the statement `𝒲Θ = cosh(x/2)` (`poleFreeWeilOperator_riemannKernelReal`).

### 2.3 Generators in Doob coordinates

For `ω` odd and `x > 0`, two generators arise, differing in how the jump that crosses the origin is
read:

    (𝓛_D ω)(x) = ∫ dm(t) Θ(x)[Θ(x+t)(ω(x) − ω(x+t)) + Θ(x−t)(ω(x) − ω(x−t))]        two-sided (Dirichlet),
    (𝓛_N ω)(x) = ∫ dm(t) Θ(x)[Θ(x+t)(ω(x) − ω(x+t)) + Θ(x−t)(ω(x) − ω(|x−t|))]      folded (Neumann).

The folded generator is the two-sided generator applied to the even reflection `ω(|·|)`
(`foldedGenerator_eq_twoSidedGenerator_abs`): it reads the reflected point `x − t < 0` through
`ω(t − x) > 0` instead of `ω(x − t) < 0`. Their difference is the reflected mass

    (𝓛_D ω)(x) − (𝓛_N ω)(x) = 2 Θ(x) ∫_{t>x} dm(t) Θ(t−x) ω(t−x)     (ω odd, ω > 0 on (0,∞)).

(`twoSidedGenerator`, `foldedGenerator`.) The two-sided generator is defined for every `C²_c` Doob
test, is linear and symmetric, obeys the Leibniz rule `𝓛_D(ωu) = u 𝓛_D ω + Θ · Comm(M, u)` with the
**plateau commutator** `Comm(M,u)(x) = ∫ dm(t)[M(x+t)(u(x) − u(x+t)) + M(x−t)(u(x) − u(x−t))]`, and
its **source** on any gauge is exact: `𝓛_D(M/Θ) − ρ (M/Θ) = −Θ · 𝒲M` whenever the prime sum and the
archimedean integral of `M` converge (`twoSidedGenerator_profileGauge_sub_potential`). The **folded
source** is `−Θ · 𝒲(M(|·|))`, every reflected point read with a plus sign. An `𝓛_N`-supersolution is
the object that would prove positivity; an `𝓛_D`-supersolution proves nothing by itself (3.3).

### 2.4 The energies of a factorised test

For `v = ωu` on `(0, ∞)`, the remainder of the ground-state representation splits by shift `t` into
three pieces, each an integral over the half line of a product of the two kernel values, the two
`ω` values and a square:

| Energy | Integrand | Range | Lean |
|---|---|---|---|
| Same-side `S(ω,u)` | `Θ(x)Θ(x+t) ω(x)ω(x+t) (u(x) − u(x+t))²` | `x > 0` | `sameSideEnergy` |
| Reflected sum `P(ω,u)` | `Θ(x)Θ(t−x) ω(x)ω(t−x) (u(x) + u(t−x))²` | `0 < x < t` | `reflectedSumEnergy` |
| Reflected difference `D(ω,u)` | `Θ(x)Θ(t−x) ω(x)ω(t−x) (u(x) − u(t−x))²` | `0 < x < t` | `reflectedDifferenceEnergy` |

all integrated against `dm(t)`. The **collar** `0 < x < t` is the set of jumps that cross the origin.
The **ground remainder** is `R_N(ω,u) = 2S + P ≥ 0`. For `ω = ω_a` the products of kernel and `ω`
values are `m_a(x) m_a(x+t)` and `m_a(x) m_a(t−x)`: in test coordinates the energies are quadratic
forms in `u` with nonnegative kernels. Each splits into an archimedean and a prime part,
`S = S_arch + S_prime`, `D = D_arch + D_prime`.

On the whole line and for any gauge the relevant object is the **signed jump energy**

    J_M(u) = ∫ dm(t) ∫_ℝ M(x) M(x+t) (u(x) − u(x+t))² dx          (`signedJumpEnergy`),

with **conductances** `M(x)M(x+t)`, negative exactly on the jumps that cross a node of `M`; for
`M = m_a` on the half line it is `2S − D`. The **variance energy** of a measure `μ` is
`V_μ(u) = ∫∫ (u(x) − u(y))² μ(x) μ(y) dx dy` (`varianceEnergy`), and the **cross energy** is
`X(ω_a,u) = ∫ dm(t) ∫_0^t m_a(x) m_a(t−x) u(x) u(t−x) dx` (`crossEnergy`).

### 2.5 Moments, collars and the shifted ground states

| Object | Definition | Lean |
|---|---|---|
| Pole moments of a test | `A(F) = 2∫ F cosh(x/2)` (even pole), `B(F) = 2∫ F sinh(x/2)` (odd pole); `σ = B/2` is the **pole coefficient** of an odd gauge | `evenPoleMoment`, `oddPoleMoment`, `spanSourceCoefficient` |
| Exponential moments | `E_±(F) = ∫ F e^{±x/2}`; `2E_+E_− = (A² − B²)/2` | — |
| Half-line cosh and sinh moments | `∫_0^∞ M cosh(r/2)`, `∫_0^∞ M sinh(r/2)`; the **other-pole moment** `∫_0^∞ e^{−r/2} M` | `coshMoment` |
| Jump-measure moment | `∫ M dm = ∫_0^∞ ω(t) M(t) dt + Σ_n Λ(n) n^{−1/2} M(log n)` | `jumpMeasureMoment` |
| Reflected prime mass | `P_M(x) = Σ_{log n > x} Λ(n) n^{−1/2} M(log n − x)` | `reflectedPrimeMass` |
| Direct prime mass | `Σ_{log n ≤ x} Λ(n) n^{−1/2} M(x − log n)` | `directPrimeMass` |
| Reflected collar mass | `C_a(x) = ∫ dm(t) m_a(t − x)⁺`, and `C_φ`, `C_M` for other gauges | `shiftedCollarMass` |
| Collar ratio | `R(a) = lim_{x→∞} C_a(x)/(sinh(a/2) sinh(x/2)) = 2 + 2∫_0^∞ e^{−r/2} m_a / sinh(a/2)` | `collarRatio` |
| Half-line measure | `μ_a = m_a(x) sinh(x/2) dx` on `(0, ∞)`, total mass `sinh(a/2)/2`; in general `μ = M sinh(x/2)` | — |
| Profile mean and variance | `ū = 2∫ u dμ_a / sinh(a/2)`, `V_a(u) = 4 sinh(a/2) ∫ (u − ū)² dμ_a` | `profileMoment`, `profileVariance` |
| Fold-excess weight | `W_a(x) = ∫_{t>2x} dm(t) (m_a(t−x) − m_a(x+t))⁺` | `foldExcessWeight` |
| Autocorrelation | `G = Θ ∗ Θ`, even, `0 ≤ G(z) ≤ Θ(|z|/2)`, `∫ G cosh(s/2) = 1/4` | `riemannAutocorr` |
| Averaged kernel | `K(x,y) = ∫_0^∞ m_a(x) m_a(y) da = G(x−y) − G(x+y)` | `averagedKernel` |
| Smooth plateau | `u_L(x) = τ(L+1−x) τ(L+1+x)`, `τ` the smooth transition | `smoothPlateau` |
| Capacity | `S(g) = ∫ 2 sinh(u/2) g`, Markov form `M_N(g)` of the Weil–Markov–pole split; **capacity ratio** `S(g)²/(2M_N(g))` | `capacityRatio` |

### 2.6 The forms and the criticality vocabulary

| Form | Definition | Where RH lives |
|---|---|---|
| Markov energy `Q(F)` | `E − ∫ ρ v²` on `F = Θv` | RH ⟺ `Q ≥ 0` on odd `C²_c` tests |
| Zero form `Z(F)` | `Q(F) − 2(∫ F sinh(x/2))²` | RH ⟺ `Z ≥ 0` on odd tests; `Z` annihilates the odd theta span |
| Full zero form `Ẑ(F)` | `Q(F) − 2(∫ F sinh)² + 2(∫ F cosh)² = Q(F) + 2 E_+(F) E_−(F)` | RH ⟺ `Ẑ ≥ 0` on all real `C²_c` tests; `Ẑ` annihilates the whole theta span; `Ẑ = W`, the Weil form |
| Lorentz form | `(B² − A²)/2` on the theta span | the explicit formula with every zero erased |
| Pole-free variation form | `2S_a(u) − D_a(u) + V_a(u) = Z(m_a u)` | gauge invariant |
| Pure jump form | `J_M(u) + V_μ(u) = Z(Θ(ωu))` in any odd gauge with source `σ sinh(x/2) Θ` | RH ⟺ `≥ 0` on even profiles, in every smeared gauge |
| Cone form | `Ẑ(Θv) = E_arch(v) + E_prime(v) + 2(∫ Θv e^{x/2})(∫ Θv e^{−x/2}) − ∫ Θ cosh(x/2) v²` | RH ⟺ the potential is paid on nonnegative profiles |
| Primitive hyperplane | `H = {F : ∫ F cosh(x/2) = 0}`, the `Q`-orthogonal complement of `Θ` | RH ⟺ `Q ≥ 0` on `H` |

A **Hardy weight** for a nonnegative form `Q` on a class of tests is a locally integrable `W ≥ 0`,
positive on a set of positive measure, with `Q(F) ≥ ∫ W F²`; the form is **subcritical** if one
exists, **critical** if nonnegative and none exists, **supercritical** if it takes a negative value.
A form is **rate-critical** when no jump rate can be lowered at any length by any amount without a
negative value, and **variance-critical** in a gauge when `J_M + (1 − ε)V_μ` is negative somewhere
for every `ε > 0`. A **null direction** is a family of tests on which the form tends to zero while
the tests stay away from zero. The **theta span** is the span of the translates `Θ(· − b)`; its
**odd part** is the span of the `m_a`; its **pole-free** or **harmonic** part has `A = B = 0`.

### 2.7 Glossary

| Object | Lean name |
|---|---|
| kernel, shift difference, shifted and translate ground states | `riemannKernelReal`, `shiftDifference`, `shiftedGroundState`, `translateGroundState` |
| span of shifted ground states, source coefficient, shift quotient | `spanGroundState`, `spanShiftDifference`, `spanSourceCoefficient`, `shiftQuotient` |
| theta convolution, convolution gauge, smeared profile | `thetaConv`, `convGauge`, `thetaConv_smearedProfile` |
| two-sided and folded generators, plateau commutator | `twoSidedGenerator`, `foldedGenerator`, `plateauCommutator` |
| pole-free Weil operator, profile arch term, profile prime sum | `poleFreeWeilOperator`, `profileArchTerm`, `profilePrimeSum` |
| Markov energy, zero form, full zero form | `markovEnergy`, `zeroForm`, `fullZeroForm` |
| same-side, reflected sum and difference energies; archimedean and prime parts | `sameSideEnergy`, `reflectedSumEnergy`, `reflectedDifferenceEnergy`, `archSameSideEnergy`, `archReflectedDifferenceEnergy` |
| signed jump energy, variance energy, cross energy, single-length jump energy | `signedJumpEnergy`, `varianceEnergy`, `crossEnergy`, `shiftJumpEnergy` |
| collar mass, collar ratio, reflected and direct prime masses | `shiftedCollarMass`, `collarRatio`, `reflectedPrimeMass`, `directPrimeMass` |
| cosh moment, jump-measure moment, pole moments | `coshMoment`, `jumpMeasureMoment`, `evenPoleMoment`, `oddPoleMoment` |
| profile moment and variance, fold-excess weight | `profileMoment`, `profileVariance`, `foldExcessWeight` |
| autocorrelation, averaged kernel, smooth plateau | `riemannAutocorr`, `averagedKernel`, `smoothPlateau` |
| folded admissibility, finite model | `FoldedAdmissible`, `FiniteJumpFormAllegrettoPiepenbrink` |
| Doob jump energies, cosh mass, capacity ratio | `phiDoobArchJump`, `phiDoobPrimeJump`, `phiDoobCoshMass`, `capacityRatio` |
| RH criteria (entry points) | `riemannHypothesis_iff_forall_odd_zeroForm_nonneg`, `riemannHypothesis_iff_forall_fullZeroForm_nonneg`, `riemannHypothesis_iff_forall_smearedGauge_jumpForm_nonneg`, `riemannHypothesis_iff_forall_nonneg_cone`, `riemannHypothesis_iff_nonneg_and_no_hardyWeight`, `riemannHypothesis_iff_isLeast_primeRate` |

---

## 3. How: the mechanisms

### 3.1 The algebraic ground-state identities

For reals `ω_x, ω_y, u_x, u_y`:

    (ω_x u_x − ω_y u_y)² = ω_x ω_y (u_x − u_y)² + (ω_x − ω_y)(ω_x u_x² − ω_y u_y²)        (difference)
    (ω_x u_x + ω_y u_y)² = ω_x ω_y (u_x + u_y)² + (ω_x − ω_y)(ω_x u_x² − ω_y u_y²)        (sum, Neumann)
    (ω_x u_x + ω_y u_y)² = −ω_x ω_y (u_x − u_y)² + (ω_x + ω_y)(ω_x u_x² + ω_y u_y²)      (sum, Dirichlet)

The last factor on the right is antisymmetric under `x ↔ y`, so after summation against a symmetric
kernel it becomes `2 Σ u² ω (Lω)`: the potential produced by the generator applied to `ω`. No
derivatives are involved; the identities hold for any kernel and any functions.

### 3.2 The folded ground-state representation and the sufficiency theorem

Let `v` be odd, continuous, compactly supported, and `v = ωu` on `(0, ∞)` with `ω` odd, `u` even. The
full-line jump at shift `t` folds onto the half line as twice the same-side jump plus the collar jump
`∫_{0<x<t} Θ(x)Θ(t−x)(v(x) + v(t−x))²` (the two points `x` and `t − x` are on opposite sides of the
origin, and `v` is odd). The difference identity on the same-side part and the Neumann sum identity on
the collar give, for each shift,

    J_v(t) = 2∫_{x>0} same-side + ∫_{0<x<t} reflected sum + 2∫_{x>0} u(x)² ω(x) · (folded shift generator of ω at t, x) dx,

and integrating against `dm` and subtracting the potential, under the integrability conditions that
define admissibility (`FoldedAdmissible`),

    Q(ωu) = R_N(ω,u) + 2 ∫_{x>0} u(x)² ω(x) [ (𝓛_N ω)(x) − Θ(x) cosh(x/2) ω(x) ] dx,     R_N ≥ 0.

**Sufficiency** (`riemannHypothesis_of_foldedSupersolution`). If `ω` is odd, positive on `(0, ∞)` and
`𝓛_N ω ≥ Θ cosh(x/2) ω` there, then `Q ≥ 0` on every odd test factoring through `ω`, hence RH. The
odd sector's Dirichlet condition `v(0) = 0` is encoded by the kink of `|ω|` at the origin.

### 3.3 Why only the folded generator can be used

The Dirichlet sum identity gives a second exact representation with `𝓛_D` in the potential, but its
remainder contains `−Θ(x)Θ(t−x) ω(x)ω(t−x) (u(x) − u(t−x))²` and is indefinite. Only the Neumann
representation has a nonnegative remainder. A positive function with positive `𝓛_D`-defect is
therefore not a certificate of anything; its `𝓛_N`-defect is smaller by the reflected mass of 2.3,
and that mass is what decides.

### 3.4 The equation of motion of `Θ`, the source of every gauge, and the collar ratio

The corpus's harmonic identity of Riemann's kernel (`theta_harmonic_identity`),

    Σ_n Λ(n) n^{−1/2} (Θ(y + log n) + Θ(y − log n)) = cosh(y/2) − 2c Θ(y) + ∫_0^∞ symArchTerm(y,s) ds,

`c = (γ + log π)/2`, with the archimedean remainder bounded uniformly in `y`, is the statement
`𝒲Θ = cosh(x/2)`: in Doob coordinates `𝓛_D 1 = 0` while the potential is positive, so the constant
`1` is a strict **subsolution** on the even sector, whose negative direction is the pole
(`Q(1) = −1/2`). Because the identity absorbs the potential exactly, **the Doob source of every gauge
is the pole-free Weil operator of its test coordinate**, `𝓛_D(M/Θ) − ρ(M/Θ) = −Θ·𝒲M`. Evaluated on
the families of 2.1 this gives the exact source equations of the table: for the translates,
`−Θ(x) cosh((x − b)/2)` (the identity at `x` and `x − b`, the diagonal archimedean densities cancel);
for the shifted ground state `ω_a`, by antisymmetrisation,

    (𝓛_D ω_a)(x) − Θ(x) cosh(x/2) ω_a(x) = 2 sinh(a/2) sinh(x/2) Θ(x),

exact for all `x`; for theta convolutions, by superposition of the translate equation, uniformly in
the translation parameter. Every `ω_a`, `a > 0`, is a strict `𝓛_D`-supersolution on the half line. By
2.3 its folded defect is

    (𝓛_N ω_a)(x) − Θ(x) cosh(x/2) ω_a(x) = 2 Θ(x) [ sinh(a/2) sinh(x/2) − C_a(x) ],

so `ω_a` is a folded supersolution at `x` exactly when the reflected collar mass does not exceed the
source, `C_a(x) ≤ sinh(a/2) sinh(x/2)`. The defect is linear on the span of the shifted ground
states, with source `2σ sinh(x/2) Θ` and combined collar `C_M` (positive parts add on the cone).

**The collar returns more than twice the source.** Since `m_a(log n − x) = Θ(x + a − log n) − Θ(x − a − log n)`,
the signed prime shift sum is `P(x+a) − P(x−a)` with `P(y) = Σ Λ(n) n^{−1/2} Θ(y − log n)`, and the
harmonic identity evaluates `P(y)` as `cosh(y/2)` plus bounded terms. The cosh difference is exactly
`2 sinh(a/2) sinh(x/2)`, and the collar keeps the positive parts of the same terms, so
`C_a(x) ≥ 2 sinh(a/2) sinh(x/2) − K` for `x ≥ a` with an explicit `K` and no prime number theorem;
the same two-sided evaluation holds on the span and on the odd convolution class, where the prime
sum is a superposition of harmonic identities. The exact ratio needs the prime number theorem. For
any decaying `M ∈ C¹` with `M(0) = 0`, Abel summation against Chebyshev's `ψ` and the substitution
`t = e^{x+r}` give `e^{−x/2} P_M(x) = −∫_0^∞ (e^{−r/2}M)'(r) e^{−x} ψ(e^{x+r}) dr`, hence

    e^{−x/2} P_M(x) → ∫_0^∞ e^{r/2} M(r) dr,      e^{−x/2} · (direct mass)(x) → ∫_0^∞ e^{−r/2} M(r) dr,

and since `e^{r/2} = 2 sinh(r/2) + e^{−r/2}`,

    C_a(x) / (sinh(a/2) sinh(x/2)) → R(a) = 2 + 2 ∫_0^∞ e^{−r/2} m_a(r) dr / sinh(a/2) > 2,

with `R(a) → 2` as `a → ∞` and `R(a) → 1 + 8Θ(0) + 4σ`, `σ = ∫_0^∞ Θ sinh(u/2)`, as `a → 0⁺`. The
collar reads a profile through `e^{r/2}`: its sinh moment is twice the source, and the excess is the
moment at the other pole `s = 0`. The folded defect of `ω_a` is asymptotic to `1 − R(a) < −1` times
the source.

### 3.5 No folded supersolution exists: the two-moment law

The hypothesis of the sufficiency theorem is never met, and the obstruction is two linear
functionals of the profile. For every `M ∈ C¹` with `M(0) = 0` and `|M|, |M'| = O(e^{−8|y|})`, with no
sign condition, the folded source of the gauge `M/Θ` is governed at the two ends of the half line by

    (𝓛_N ω − ρω)(x) / Θ(x)         →  −2 ∫ M dm                      (x → 0⁺),
    (𝓛_N ω − ρω)(x) / (Θ(x) e^{x/2})  →  −2 ∫_0^∞ M(r) cosh(r/2) dr      (x → ∞),

and for odd `M` the two-sided source obeys `(𝓛_D ω − ρω)/(Θ e^{x/2}) → 2 ∫_0^∞ M sinh(r/2)`
(`tendsto_foldedSource_div_nhdsGT_zero`, `tendsto_foldedSource_div`, `tendsto_twoSidedSource_div`).
At the origin every jump from `0` lands at distance `t` on one side or the other and the fold reads
both landing points as `M(t)`: the limit is the value of `𝒲(M(|·|))` at `0⁺`. At infinity the
archimedean term of `𝒲` is bounded and the forward prime terms decay, so only the prime terms reading
back into the profile survive: the reflected mass gives `∫ e^{r/2} M`, the direct mass `∫ e^{−r/2} M`,
and the two-sided generator reads the reflected points with the sign of `M` on the negative half
line while the folded one reads them with a plus sign, so the moments combine into `sinh` and
`cosh`. Consequently a folded supersolution near the origin has `∫ M dm ≤ 0`, one near infinity has
`∫_0^∞ M cosh(r/2) ≤ 0`, and for a nonnegative profile, nonzero on `(0, ∞)`, both moments are positive:
**every positive profile of exponential decay is a strict folded subsolution near the origin and on a
half line**, with no domination by a translate of `Θ` and no condition at `log 2`
(`exists_origin_and_infinity_windows_foldedGenerator_lt_potential`). The failure at infinity is
PNT-free prime by prime: a single reflected prime atom `Λ(p) p^{−1/2} M(y₀)`, of size `e^{−x/2}` at
`x = log p + y₀`, beats every local archimedean term, which is `O(e^{−8x})`
(`profileGauge_foldedGenerator_lt_potential_at_prime_shift`). On the finite span and on the
convolution class the quantitative forms are: folded defect `≤ −2Θ(x)[σ sinh(x/2) − K Σ|c_j|]`, resp.
`≤ −Θ(x)[B_φ sinh(x/2) − 2K ∫|φ|]`, both PNT-free, the decisive coefficient being the pole moment
`σ = 2∫_{x>0} M sinh(x/2) > 0` on the nonzero cone; and the folded failure of every odd convolution
is exactly its half-line cosh moment, `−2 ∫_0^∞ M cosh(r/2) < 0`
(`tendsto_foldedDefect_convGauge_div`). Positive even profiles are strict two-sided subsolutions on
a half line.

The sign-changing side is the mirror image: a profile with negative half-line cosh moment is a strict
folded **super**solution on a half line (`exists_infinity_window_potential_lt_foldedGenerator_of_coshMoment_neg`).
The obstruction to folded supersolutions is therefore positivity together with the cosh moment, not
decay or regularity, and no positive gauge can satisfy the sufficiency theorem.

This is the exact sense in which the odd arithmetic form is **not of Z-type**: the reflected jumps
enter the odd-sector operator with a plus sign, and the hard direction of Allegretto–Piepenbrink,
which for a finite Z-matrix follows from Perron–Frobenius (3.12), fails. Positivity, if RH holds, is
carried by the remainder, never by the generator: any proof along these lines is a
subsolution-plus-remainder proof.

### 3.6 The generator calculus and the ground-state representation in an arbitrary gauge

The Markov energy is the weak form of the two-sided generator: for every Doob test `z ∈ C²_c`,

    Q(Θz) = ∫ z(x) [ (𝓛_D z)(x) − Θ(x) cosh(x/2) z(x) ] dx        (`markovEnergy_phiDoob_eq_integral_mul_twoSidedGenerator_sub_potential`).

Shift by shift this is summation by parts; the archimedean shifts are exchanged with the
`x`-integral through `|𝓛_D^t z| ≤ 2Θ(0)² Lip(z) t` against `∫ ω(t) t dt < ∞`, the prime shifts through
`Θ(x ± log n) ≤ Θ(0)/Θ(R) · Θ(log n − R)` on the support. The weak form is symmetric,
`∫ v 𝓛_D z = ∫ z 𝓛_D v`, hence the **polarisation**
`Q(Θ(a + b)) = Q(Θa) + Q(Θb) + 2∫ b(𝓛_D a − ρa)` (`markovEnergy_phiDoob_add`), and the **pairing law**:
for a gauge with source `Θg` and a fixed test `v`, `|∫ v(𝓛_D(ωu_L) − ρωu_L) − ∫ vΘg| ≤ Ke^{−8L}`, the
commutator being localised beyond the plateau. Summation by parts of the commutator,
`∫ u M Comm(M,u) = J_M(u)`, gives the **ground-state representation in an arbitrary gauge**
(`markovEnergy_phiDoob_mul_eq_signedJump_add_source`): for a gauge with `|M| ≤ Ce^{−24|x|}`,
convergent generator and source `Θg`, and every profile `u ∈ C²_c` of any parity,

    Q(Θ(ωu)) = J_M(u) + ∫ u(x)² M(x) g(x) dx,       g = −𝒲M.

For a harmonic gauge there is no potential at all, `Q(Θ(ωu)) = J_M(u)`: on the tests it factors, the
Markov form is a pure signed Dirichlet form, and every sign question is a question about the negative
conductances across the nodes of `M`. The representation contains the two-sided representation of
3.7 (`M = m_a`, `g = 2 sinh(a/2) sinh(x/2)`, the only node at the origin) and the definition of `Q`
(`M = Θ`, `g = −cosh(x/2)`).

**Plateau laws.** With `u = u_L` the main term `∫ u_L² M g` converges and the commutator contributes
`O(e^{−8L})`, so on the finite span of shifted ground states

    | Q(Θ(ω u_L)) − 2σ² | ≤ K e^{−8L}       (`exists_abs_markovEnergy_spanPlateauProfile_sub_le`):

in the limit the odd Markov form restricted to the span is the square of one linear functional, the
pole moment; `ω_a` and `ω_b` are correlated by exactly `2 sinh(a/2) sinh(b/2)` and every `σ = 0`
superposition is a null direction. On the translate combinations the limit is the **Lorentz form**
`(B² − A²)/2` (`exists_abs_markovEnergy_translatePlateau_sub_le`): one negative direction (the even
pole), one positive direction (the odd pole), an infinite-dimensional null space; in particular
`Q(Θu_L) → −1/2`, the calibration `Q(1) = −1/2` as a theorem on compactly supported tests. The same
law holds on the continuous span, `Q(Θ(ω_φ u_L)) → (B_φ² − A_φ²)/2`: the plateau-limit energy of the
whole convolution family factors through the two pole coefficients. This is the explicit formula
restricted to the theta span with every zero erased: the Mellin transform of `Θ` is `ξ`, which
vanishes at the zeros, and what remains is the pole form of signature `(1,1)`.

**The harmonic theta span is the radical.** For a harmonic gauge and every test `v`,
`|Q(Θ(v + ωu_L)) − Q(Θv)| ≤ Ke^{−8L}` for `L ≥ R_v` (`abs_markovEnergy_add_harmonicPlateau_sub_le`):
the Markov form, on every test, descends to the quotient by the harmonic theta span, an
infinite-dimensional space of exact sign-changing solutions of the two-sided arithmetic Schrödinger
equation. This is the structural reason for the criticality of 3.9.

### 3.7 The two-sided representation and the variation inequality; the archimedean place is Z-type

For `ω = ω_a` the ground-state representation holds with no side condition: `(ω_a, u)` is admissible
for every `a > 0` and `u ∈ C¹_c` (3.14). Adding the reflected sum and difference jumps,
`P + D = 4 ∫_{x>0} u² m_a C_a` (collar Fubini), and the folded representation `R_N = 2S + P` becomes
the **two-sided representation**: for `a > 0` and even `u ∈ C²_c`
(`markovEnergy_phiDoob_shiftedGroundState_eq_twoSided`)

    Q(m_a u) = 2 S(ω_a,u) − D(ω_a,u) + 4 sinh(a/2) ∫_{x>0} u(x)² m_a(x) sinh(x/2) dx.

Its source is the two-sided source of `ω_a`, and its only indefinite term is `−D`. Positivity of `Q`
on the tests `m_a u` is the **variation inequality**

    D(ω_a,u) ≤ 2 S(ω_a,u) + 4 sinh(a/2) ∫ u² dμ_a :

the variation of `u` **across** the fold point `t/2`, weighted by the collar kernel
`m_a(x) m_a(t−x)`, is dominated by twice the variation **along** the half line at distance `t` plus
the source. In the corpus's `oddProfile` coordinates (`m_a = 2 sinh(a/2) · oddProfile a`) the source
is THIM's `oddSinhPotential` with coefficient exactly `1`. Expanding the reflected square gives the
**cross-term form** `Q(m_a u) = 2S + 2X − 2 ∫_{x>0} u² m_a (C_a − 2 sinh(a/2) sinh(x/2))`, in which
the collar excess beyond twice the source is the only negative term and the cross term `X` carries
the sign information of the primes through products `u(x) u(t−x)` across the fold.

**The archimedean place satisfies the variation inequality with no source.** In the pair
coordinates `(x, y)` of one jump the same-side jumps sit on the lines `y − x = t` and the reflected
jumps on the anti-diagonals `x + y = t`. Folding the reflected collar at its midpoint and moving every
jump to the same pair of points gives

    D_arch(ω_a,u) = 2 ∫_{x>0} ∫_{s>0} ω(s + 2x) J_s(x) ds dx,     S_arch(ω_a,u) = ∫_{x>0} ∫_{s>0} ω(s) J_s(x) ds dx,

with `J_s(x) = Θ(x)Θ(x+s) ω_a(x) ω_a(x+s) (u(x) − u(x+s))² ≥ 0`; since the Lévy density decreases,
`D_arch ≤ 2 S_arch` for every shift and profile (`archReflectedDifferenceEnergy_le_two_mul_archSameSideEnergy`).
Hence RH ⟺ `D_prime ≤ (2S_arch − D_arch) + 2S_prime + V_a` with a nonnegative archimedean surplus:
every violation of the pole-free variation inequality, hence every failure of RH, is carried by the
prime anti-diagonal atoms `x + y = log n`, at which `Λ(n) n^{−1/2}` is not dominated by the same-side
atoms at `|x − y| = log m`. The odd arithmetic operator is non-Z-type exactly because the prime jump
measure is not monotone.

### 3.8 The pole term, the zero forms, and where the zeros are

The half-line sinh moment of the shift difference is exact: `∫_{x>0} m_a sinh(x/2) = sinh(a/2)/2`.
Hence the source splits as

    4 sinh(a/2) ∫ u² dμ_a = 8 (∫ u dμ_a)² + V_a(u),      V_a(u) = 4 sinh(a/2) ∫ (u − ū)² dμ_a ≥ 0.

The first term is `2 (∫ m_a u e^{−x/2})²`, the **pole term** of the explicit formula for the odd test
`m_a u`; the second is the **profile variance**. The Mellin transform of `m_a` itself is
`−2 sinh(a(s − 1/2)) ξ(s)`, which vanishes at every zero of `ξ`: the shifted ground state is the
zero-free direction of the odd sector, and `Q(m_a) = 2 sinh²(a/2)` is pure pole term.

**Free positivity.** For every `a > 0` there is `L₀` such that every even `u ∈ C²_c` with `0 ≤ u ≤ 1`
and `u = 1` on `[−L, L]`, `L ≥ L₀`, has `Q(m_a u) ≥ sinh²(a/2)` (plateau positivity). For an even
`g ∈ C²_c` supported in `[−1/4, 1/4]` the odd test `g(x − a) − g(−x − a)` has cross term equal to the
autocorrelation of `g` at `t − 2a` with prime part a smoothed log-window prime sum,
`X = 2μ² cosh a + O(1)` with `μ = ∫ g e^{u/2}`, so `Q ≥ μ² e^{a} − K > 0` for all large `a` if
`μ ≠ 0` (far-apart bumps). Both are regions where the pole term dominates.

**The zero form is gauge invariant.** Put `Z(F) = Q(F) − 2(∫ F sinh(x/2))²`. For every shift and even
profile, `2S_a(u) − D_a(u) + V_a(u) = Z(m_a u)` (`poleFreeForm_eq_zeroForm`): the pole-free variation
form depends on the test, not on the gauge, and `PF_a(F/m_a) = PF_b(F/m_b)`. The plateau truncation of
any finite odd superposition, of any pole coefficient, changes `Z` by `O(e^{−8L})`, so `Z` annihilates
the whole odd theta span, and RH ⟺ `Z ≥ 0` on odd `C²_c` tests (the pole moment of a test is cancelled
by a multiple of `m_1 u_L`, invisible to `Z`). Subtracting from a profile its mean times a wide
plateau realises this as the unconditional limit `Q(m_a(u − ū u_L)) → 2S − D + V_a` at rate `e^{−4L}`.

**Single-shift completeness.** Every odd `C²_c` test vanishing near the origin is `m_a u` with an even
`C²_c` profile, and without RH such a test with negative energy exists, the same for every shift.
Hence for every single `a > 0`: RH ⟺ `Q(m_a u) ≥ 0` for all even `u` ⟺ the same for profiles vanishing
near `0` ⟺ the variation inequality ⟺ the pole-free variation inequality ⟺ remainder dominates defect
(`riemannHypothesis_iff_forall_poleFreeVariationInequality`). The shift is a gauge; the origin, where
every folded supersolution fails, carries no zero information; averaging over shifts can reweight but
never enlarge the test class.

**The zero form is a jump form in every odd gauge.** For a gauge with source `σ sinh(x/2) Θ` and
`μ = M sinh(x/2)`, the source term minus the pole term is a variance,
`σ ∫ u² μ − 2(∫ u μ)² = V_μ(u)`, so

    Z(Θ(ωu)) = J_M(u) + V_μ(u)        (`zeroForm_phiDoob_mul_eq_signedJump_add_varianceEnergy`),

with conductances `M(x)M(y)` times the gauge-free kernel `dm(|x − y|) + sinh(x/2) sinh(y/2)`. For an
odd gauge positive on `(0, ∞)` the variance conductances are positive for every pair, including pairs
across the origin, where the jump conductances are negative. The smeared shifted ground states are
positive on `(0, ∞)` and **complete**: RH ⟺ `J_M(u) + V_μ(u) ≥ 0` for every even `u ∈ C²_c`, in every
smeared gauge, exactly and with no plateau limit (`riemannHypothesis_iff_forall_smearedGauge_jumpForm_nonneg`).
The only negative conductances are the crossing pairs where `dm(|x| + y) > sinh(|x|/2) sinh(y/2)`:
near the axes for the Gamma density, and on every prime anti-diagonal `|x| + y = log n`.

**The full zero form and the cone.** On real tests of both parities put
`Ẑ(F) = Q(F) − 2(∫ F sinh)² + 2(∫ F cosh)² = Q(F) + 2 E_+(F) E_−(F)`, which subtracts exactly the
Lorentz form. The whole theta span is its radical (`tendsto_fullZeroForm_add_translatePlateau`), and
RH ⟺ `Ẑ ≥ 0` on every real `C²_c` test (`riemannHypothesis_iff_forall_fullZeroForm_nonneg`): the even
cosh moment is cancelled by a multiple of the truncated kernel, invisible to `Ẑ`, and the result is
handled by the primitive-hyperplane criterion. `Ẑ` coincides with the Weil form on compact tests, so
the explicit formula's pole part is, inside the theory, the Lorentz form of the theta span, and RH is
positivity of the Markov form on the quotient of all tests by the theta span. In Doob coordinates
every term of `Ẑ(Θv)` is a nonnegative functional of a nonnegative profile, and lifting any test into
the cone by `max|v| · u_L` costs nothing in the limit, so

    RH ⟺ ∀ v ∈ C²_c, v ≥ 0:   ∫ Θ cosh(x/2) v²  ≤  E_arch(v) + E_prime(v) + 2(∫ Θv e^{x/2})(∫ Θv e^{−x/2})

(`riemannHypothesis_iff_forall_nonneg_cone`), a criterion with no signed term. It is sharp at the
constant profile: along `u_L → 1` the jump energy tends to `0` and the potential and the pole product
both tend to `1/2`, and for every `ε > 0` the inequality with `(1 + ε)` in front of the potential fails
on the cone. The cone is RH-complete because the radical contains the strictly positive element `Θ`.

**The capacity normalisation.** The Markov part of the finite-aperture Weil–Markov–pole splitting at
any prime aperture beyond the autocorrelation support is the Markov energy, and on odd tests RH is
the capacity inequality `S(g)² ≤ 2M(g)`, the zero form again. Plateau truncations of every
superposition of shifted ground states with `σ ≠ 0` have `S → 2σ`, `M → 2σ²`, so the capacity ratio
`S²/(2M)` tends to one: at every large aperture some odd test has ratio above `1 − ε`, and the
inequality has no uniform margin (`tendsto_capacityRatio_spanPlateau`). The extremal directions are
the plateau truncations of positive odd gauges, whose capacity defect is the zero form `J_M + V_μ → 0`.

**Reading.** The positivity that comes for free is the pole term; the zeros are seen only through
profiles of `μ_a`-mean zero, where the pole term vanishes and the sign of the zero form, a pure jump
form with explicit conductances, is the whole question.

### 3.9 Criticality: no slack anywhere

Pinchover's trichotomy collapses for the arithmetic form.

- **No Hardy weight on the odd sector.** For every locally integrable `W ≥ 0` positive on a set of
  positive measure there is an odd `v ∈ C²_c` with `Q(Θv) < ∫ W (Θv)²`
  (`exists_odd_markovEnergy_lt_integral_weight_mul_sq`). The null sequences are the plateau
  truncations of the pole-free pairs `M_n = sinh(n/2) m_1 − sinh(1/2) m_n`, which separate points.
  Hence RH ⟺ the odd form is nonnegative and critical (`riemannHypothesis_iff_nonneg_and_no_hardyWeight`).
- **No Hardy weight on the primitive hyperplane.** The same with real `F ∈ C²_c` of both parities
  with `∫ F cosh(x/2) = 0`; the null sequences are the even harmonic pairs
  `τ_b + τ_{−b} − 2cosh(b/2) τ_0`, corrected onto the hyperplane by a vanishing multiple of `Θu_0`,
  which separate every point including the origin. Wherever RH makes the form nonnegative it is
  critical.
- **Rate-criticality.** For every jump length `ℓ > 0` and `ε > 0` some odd `v` has `Q(Θv) < ε J_ℓ(v)`
  (`exists_odd_markovEnergy_lt_shiftJumpEnergy`); the archimedean density cannot be lowered on any
  interval either. Every prime-power rate `Λ(n) n^{−1/2}` is needed in full, and RH ⟺ it is the least
  admissible rate at `log n` (`riemannHypothesis_iff_isLeast_primeRate`). The witnesses are plateau
  truncations of a pole-free pair with `ω(ℓ/2) ≠ 0`, whose `ℓ`-jump energy across `−ℓ/2 ↦ ℓ/2` is a
  fixed positive constant while the Markov energy is `O(e^{−8L})`.
- **Variance-criticality.** In every smeared gauge and for every `ε > 0` some even `u` has
  `Z(Θ(ω_ν u)) < ε V_μ(u)` (`exists_zeroForm_lt_mul_varianceEnergy`), so the signed jump energy `J_M`
  alone is negative somewhere, unconditionally: no positive odd gauge makes the conductance form
  positive, and the all-pairs variance is exactly critical. The witness is a pole-free pair divided
  by the gauge, smooth through the origin by Hadamard division because both vanish there and the
  gauge has positive slope.

The arithmetic form has no slack in its potential, its rates or its variance. The critical form has
an infinite-dimensional family of approximate ground states (the pole-free theta span, both parities),
unlike a Schrödinger form whose critical ground state is unique and positive: a new, arithmetic type
of criticality, with sign-changing null directions.

### 3.10 Averaging over the shift

The variation inequality is quadratic in `m_a`, and the shift integrals are explicit:

    ∫_0^∞ m_a(x) m_a(y) da = G(x−y) − G(x+y) = K(x,y),      ∫_0^∞ 4 sinh(a/2) m_a(x) sinh(x/2) da = 2 sinh²(x/2),

the first because each product of translated kernels integrates to a value of the autocorrelation,
the second from the moments of `Θ`. All integrands being nonnegative, the exchanges of the
`a`-integral with the `x`-integrals, the archimedean integral and the prime sum need only the exact
`a`-integrals and the decay `Θ(s) ≤ C e^{−8|s|}` (prime sums `Σ Λ(n) n^{−1/2} (1 + log n) Θ((log n − c)/2)`
converge), and

    ∫_0^∞ Q(m_a u) da = 2 S̄(u) − D̄(u) + 2 ∫_{x>0} u(x)² sinh²(x/2) dx,

where `S̄`, `D̄` are the energies with `m_a(x) m_a(y)` replaced by `K(x,y)`
(`integral_Ioi_markovEnergy_phiDoob_shiftedGroundState`). Nonnegativity of the shift-averaged energy
is the **shift-averaged variation inequality** `D̄ ≤ 2S̄ + 2∫ u² sinh²(x/2)`, with explicit kernels
`G(2x−t) − G(t)` across the fold and `G(t) − G(2x+t)` along the line.

**What averaging destroys (heuristic).** By Plancherel in `a`,
`∫_0^∞ Q(m_a u) da = (1/4π) ∫ Ξ(ξ)² Q(sin(ξ·) u) dξ`. The weight `Ξ(ξ)²` vanishes exactly at the
ordinates of the zeros on the line, and for an off-line zero `ρ = 1/2 + δ + iγ` the `Ξ²`-weighted
contribution of the pair `ρ, 1 − ρ̄` is, to leading order, `(π/2) Ξ(γ)² ∫ u²` for every `δ`, hence
nonnegative. The shift-averaged inequality is therefore expected to hold unconditionally and to carry
no information about off-line zeros; by single-shift completeness the single-shift inequality is RH
at every shift, so the average can only reweight. The zeros are visible in the single-shift
inequality and in averages over windows of shifts narrower than the zero gap.

### 3.11 Fold domination on monotone profiles and the weight criterion

If `u` is even, nonnegative and nonincreasing on `[0, ∞)`, then on `0 < x < t/2` the three points
satisfy `x ≤ t−x ≤ x+t`, so `0 ≤ u(x) − u(t−x) ≤ u(x) − u(x+t) ≤ u(x)`, and the collar symmetry gives
for each shift `D(t) ≤ 2 S(t) + 2 E_a(t)`, with `E_a(t) = ∫_0^{t/2} m_a(x) (m_a(t−x) − m_a(x+t))⁺ u(x)² dx`
the **fold excess**. Integrating against `dm`,

    Q(m_a u) ≥ 4 sinh(a/2) ∫ u² dμ_a − 2 ∫_{x>0} u(x)² m_a(x) W_a(x) dx,

so the **weight criterion** `W_a(x) ≤ 2 sinh(a/2) sinh(x/2)` for all `x > 0` would give positivity on
the whole monotone cone. It is false for every large shift: the fold excess of `ω_a` at `x` is a shift
difference read at `a`, `m_a(t−x) − m_a(t+x) = m_x(t−a) − m_x(t+a)`, so `W_a(x)` is bounded below by
the reflected prime mass of the profile `m_x` at `a`, which is `e^{a/2}(κ_x + o(1))` with
`κ_x = sinh(x/2) + ∫_0^∞ e^{−r/2} m_x`, while the criterion is `e^{a/2}(sinh(x/2) + o(1))`; for every
`x` with `2x < log 2` it fails for all large `a` (`exists_foldExcessWeight_gt_criterion`), by exactly
the other-pole moment, the same excess as in `R(a)`. Whatever replaces the criterion must absorb that
moment through the same-side terms away from the origin that fold domination drops.

### 3.12 The finite model

For a finite symmetric nonnegative kernel `K` and any potential `ρ`, the form `E_K − Σ ρ v²` is
nonnegative if and only if a nonnegative nonzero `ω` with `L_K ω ≥ ρ ω` exists; under connectivity
`ω > 0` (`FiniteJumpFormAllegrettoPiepenbrink`). The hard direction minimises the Rayleigh quotient on
the unit sphere and uses that replacing `v` by `|v|` does not increase the form, which is the Z-type
property. This is the template against which the arithmetic odd sector is measured, and the reason
3.5 is the central no-go: the arithmetic odd-sector operator is not Z-type, and by 3.7 the failure is
located entirely in the prime anti-diagonals.

### 3.13 Positivity below the first prime from a plateau gauge

Below the first prime the obstruction of 3.7 is absent. Take a gauge `M` with `0 ≤ M ≤ 1`, `M = 1` on
`[−r, r]`, `M = 0` outside `(−R, R)`, `2R < log 2`. A test `F` supported in `[−r, r]` satisfies
`F = M · F`, the ground-state representation in the gauge `M` reads `Q(F) = J_M(F) − ∫ F² 𝒲M` with
all conductances `M(x)M(x+t)` nonnegative, and on the window the pole-free Weil operator is purely
archimedean, since no prime shift of a point of `[−r, r]` lands in `(−R, R)`. At `x` with `M(x) = 1`,
with `a = R − x`, `b = R + x` and `N(a) = ∫_a^∞ ν = −½ log(1 − e^{−2a})`, the pointwise inequality
`ω − ν ≤ 3/4` gives `−𝒲M(x) ≥ N(a) + N(b) − (3/4)(a + b) − (γ + log π)`, and `N(a) + N(b) ≥ −log(2R)`:
the gauge feels the window edge only through the killing `N`, logarithmically large on short
windows. With `R = e^{−2}/2` the potential is at least `2 − (3/4)e^{−2} − (γ + log π) > 0.0817`, and
every real `F ∈ C²_c` supported in `[−r, r]`, `r < e^{−2}/2`, satisfies

    Ẑ(F) ≥ (3/40) ∫ F²        (`fullZeroForm_ge_of_support_le`),

the odd pole moment costing at most `4R³ ∫ F²`. Below the first prime positivity of the full zero form
reduces to one explicit archimedean potential; the first prime, where conductances across `log 2`
turn negative, is where the mechanism of 3.7 takes over.

### 3.14 Admissibility: how the analysis is discharged

The ground-state representation requires the remainder and the potential density to be integrable
in `t` against `dm` and in `x`. In test coordinates the potential density of `ω_a` is `u(x)² K_a(t,x)`
with `K_a(t,x) = m_a(x)[ω_a(x)(Θ(x+t) + Θ(|x−t|)) − m_a(x+t) − m_a(|x−t|)]`, and for `u` supported in
`[−R, R]` one has `|K_a(t,x)| ≤ K₁ t` (Lipschitz constants of `Θ` and `m_a`) and
`|K_a(t,x)| ≤ K₂ Θ(t − R − a)`. The one-shift remainder satisfies the same two bounds, because the
collar `0 < x < t` meets the support of `u` in two intervals of length at most `R`. Linear bounds
near `t = 0` tame the `1/t` singularity of the archimedean density (`∫ ω(t) t dt < ∞`); decay bounds
in `t` make the prime sums converge (`Σ Λ(n) n^{−1/2} Θ(log n − c) < ∞`). For general gauges the
decay `|M| ≤ Ce^{−24|x|}` and the localisation of the plateau commutator beyond `L`
(`|u_L M Comm| ≤ C e^{−8L} e^{−8|x|}`) play the same role; for the profile laws at infinity the
inputs are `|Θ'(u)| ≤ Ce^{−2|u|}`, the decay of `m_a` and `m_a'`, Abel summation against `ψ`, the
bound `ψ(y) ≤ Ky` and the prime number theorem in the form `ψ(y)/y → 1`. Two recurring general facts:
a nonnegative series of integrable functions with summable integrals is integrable
(`integrable_tsum_of_nonneg`), and product integrability in `(a, x)` for nonnegative integrands with
explicit `a`-integrals needs no majorant.

---

## 4. Traps and sharp boundaries

| Trap | Why it fails; the correct statement |
|---|---|
| An even positive supersolution on all of `ℝ` | Impossible: it would give `Q ≥ 0` on even tests, but `Q(1) = −1/2`; positive even profiles are strict two-sided subsolutions on a half line. The identity is applied only to odd tests. |
| Using `𝓛_D` as the supersolution operator | Its representation has an indefinite remainder. Only `𝓛_N` has a nonnegative remainder. |
| Reading `ω_a > 0` with positive `𝓛_D`-source as a proof | It is a `𝓛_D`-supersolution, not a `𝓛_N`-supersolution; the collar `C_a` exceeds the source near `0` and for all large `x`, by the factor `R(a) > 2`. |
| Looking for any folded supersolution | None exists among positive profiles: positivity forces positive jump-measure and cosh moments, which force failure at both ends. The live objects are the zero forms, not the sign of a generator defect. |
| Expecting a sign-changing gauge to help | Gauges with negative cosh moment are folded supersolutions at infinity, but the sufficiency theorem needs positivity on the half line; the two requirements exclude each other. |
| Estimating a one-sided prime sum by a window prime number theorem first | Evaluate the signed sum through the harmonic identity of `Θ` and use positivity of the discarded part; the exact identity gives the uniform constant `2` where asymptotics give `R(a)`. Use the prime number theorem only for the exact ratio. |
| Defining the generator through a total jump rate | It diverges (`1/t` singularity, `Σ Λ(n) n^{−1/2} = ∞`). Only differences converge; never split a generator into rate minus average. |
| Mixing test and Doob coordinates | `m_a` is a test, `ω_a = m_a/Θ` its Doob coordinate. Generators and supersolutions live in Doob coordinates; kernels and bounds are simplest in test coordinates. |
| Requiring `v/ω` to be `C²` | The identities need no derivatives. The RH criterion needs `v ∈ C²_c`; the quotient only needs to be continuous and bounded on `(0, R]`, and the shift quotient `F/m_a` of a test vanishing near `0` is `C²_c`. |
| Applying Perron–Frobenius to the odd sector | The reflected prime jumps give positive off-diagonal entries. The archimedean place alone is Z-type; the failure is the non-monotone prime jump measure. |
| Treating the source as the pole term | The source is pole term plus variance. Only the pole term is free positivity; the variance is where profiles differ, and the zeros live on mean-zero profiles. |
| Treating the shift as information | Every frontier inequality at one shift is RH; the shift is a gauge, and the zero form is the same for all shifts. |
| Averaging over all shifts to gain a weaker target | The average over all shifts is `Ξ²`-weighted in frequency and blind to off-line zeros. Use single shifts or narrow shift windows. |
| Expecting a Hardy weight, a lower jump rate or a smaller variance to leave room | The odd form is critical in all three senses; every prime enters at exactly critical strength. |
| Expecting positivity of the conductance form in a positive gauge | `J_M` alone is negative somewhere in every smeared gauge; the variance `V_μ` is indispensable. |
| Proving a statement about `Q` on the theta span as new | On the span the Markov form is the pole form (Lorentz, rank one on the odd part) and the Weil form of `Θ`-translates is pole-only; the harmonic span is the radical. |
| Confusing `Ẑ` with a new form | On compact tests `Ẑ` is the Weil form; what is native is its generator-calculus proof, the exact source of every gauge and the cone criterion. |
| Expecting a uniform margin in the capacity inequality | The capacity ratio tends to one along plateau truncations of positive odd gauges at every large aperture. |
| The weight criterion of fold domination | It fails for every large shift by the other-pole moment; monotone-cone positivity needs the dropped same-side terms. |
| Aperture conditions of THIM's gauge (`a < (log 2)/2`) | Supersolution statements here are pointwise in `x` and carry no aperture window; THIM's absorption ratio grows like `exp(πe^{2R})` and is a different object. The plateau-gauge window `R < e^{−2}/2` is a window on the test, not on the shift. |

Conventions in the Lean development that are easy to get wrong: `integral_add` and `integral_sub`
need lambda-typed integrability facts, not `Pi.add` forms; rewriting `mem_Iic` inside an `if` fails
on the motive (use `simp only [Set.indicator_apply, mem_Iic]`); in long proofs with integral-laden
contexts, linear arithmetic must be called with an explicit hypothesis list (`linarith only [...]`);
Hadamard division of two functions vanishing at the origin goes through the corpus
`smoothCoordinateQuotient`; no statement in this theory carries an unproven arithmetic hypothesis:
consequences of positivity are stated as equivalences or as limits of unconditional identities, and
the prime number theorem enters only through proved corpus forms.

---

## 5. The frontier

1. **The pure jump form.** In every smeared gauge RH is `J_M(u) + V_μ(u) ≥ 0` for even profiles,
   with explicit conductances `M(x)M(y)(dm(|x − y|) + sinh(x/2) sinh(y/2))`. The archimedean
   crossing conductances are dominated by the same-side ones; the obstruction is confined to the
   prime anti-diagonals `|x| + y = log n`, where `Λ(n) n^{−1/2}` must be paid by same-side atoms at
   `|x − y| = log m` and by the variance. A prime-side inequality between anti-diagonal and same-side
   atoms, or a classification of the profiles on which the anti-diagonal mass is not paid, is the
   problem; every term of the form is critical, so the inequality has no slack to lose.
2. **Criticality on the quotient.** The form is critical on the odd sector and on the primitive
   hyperplane, with sign-changing null families inside the theta span. Whether the zero form admits a
   Hardy weight on the quotient by the theta span, that is a positivity margin invisible to the
   radical, is open; so is any quantitative form of the approach to zero along the null sequences.
3. **The monotone cone.** The weight criterion fails by the other-pole moment; a replacement that
   retains the same-side terms away from the origin, or a proof that no inequality in `Θ` alone
   decides the monotone cone, is open.
4. **Beyond the first prime.** The plateau-gauge mechanism gives `Ẑ ≥ (3/40)∫F²` below `e^{−2}/2`
   with nonnegative conductances; past `log 2 / 2` the conductances across the first prime turn
   negative. Extending a gauge argument through the first prime window, with the prime atom paid by
   the potential, is the smallest instance of problem 1.
5. **Selectivity.** The identities of 3.1–3.3 and 3.6 hold for any even positive kernel; the
   arithmetic enters only through the equation of motion of `Θ` (3.4). Rate-criticality shows every
   prime enters at exactly critical strength. What each statement says for `ζ(s−a)ζ(s+a)`, whose
   potential changes, and for a Beurling system, measures which parts of the theory see the primes.
6. **Exact constants.** The collar ratio `R(a)`, the cosh-moment law and the plateau-gauge potential
   are explicit; the dependence of the capacity ratio's approach to one on the aperture, and the
   sharp window radius of problem 4, are not.

---

## 6. Working in the theory

- State in which coordinates a claim lives before writing it; convert with `M = Θ ω`. State which
  gauge, and whether the statement is at a single shift, on the span, on the convolution class, or on
  all profiles.
- Before any new estimate, search the corpus, and search the Weil-form lanes in particular: a
  statement that only evaluates `Q` on theta-span tests is a pole-term fact, and `Ẑ` is the Weil
  form. The same objects exist in the `oddProfile` coordinates of CHMD and THIM
  (`oddProfile a = m_a/(2 sinh(a/2))`, `oddSinhPotential`, collar-versus-direct bounds on the
  low-prime window), the Markov form of the Weil–Markov–pole split lives in the arithmetic
  positivity theory, and the Weil-cone modules own the window prime number theorems.
- Prefer exact identities to asymptotics: the harmonic identity, the exact source of every gauge,
  the collar Fubini identity, the sinh moments, the shift integrals, the Lorentz law. Use positivity
  of discarded terms before using analysis, and the prime number theorem only for exact limits.
- Every theorem is unconditional. A statement that would follow from positivity of the odd form is
  recorded as an equivalence with that positivity, or as a limit of unconditional identities.
