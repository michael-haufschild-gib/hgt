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

### 2.1 Coordinates

Every statement is made in one of two coordinate systems, and mixing them is the first trap.

- **Test coordinates.** The object is the test `f = Θ v` (or `v`) that enters the Markov energy.
- **Doob coordinates.** The object is the quotient `u = v/ω` relative to a chosen positive function
  `ω`. Potentials, generators and supersolutions live here.

The primary example: the **shift difference** `m_a(y) = Θ(y − a) − Θ(y + a)` is a test (odd, positive
on `(0, ∞)` for `a > 0`, vanishing linearly at `0`). Its Doob coordinate is the **shifted ground state**
`ω_a = m_a/Θ`. A test factoring through `ω_a` is `v = ω_a u` with `u` even, i.e. `Θ v = m_a u`.

### 2.2 The jump structure

| Object | Definition | Lean |
|---|---|---|
| Jump measure | `dm(t) = ω(t) dt + Σ_{n≥2} Λ(n) n^{−1/2} δ_{log n}` on `t > 0` | `archLevyDensity`, `vonMangoldtAtom` |
| Potential | `ρ(x) = Θ(x) cosh(x/2)` | `phiDoobCoshMass` |
| Markov energy | `Q(v) = ∫ dm(t) ∫_ℝ Θ(x)Θ(x+t)(v(x) − v(x+t))² dx − ∫ ρ v²` | `markovEnergy (phiDoobTest v)` |

The archimedean density has a `1/(2t)` singularity at `0` and decays like `e^{−t/2}`; the prime
atoms have total mass `Σ Λ(n) n^{−1/2} = ∞`. Consequently a "total jump rate"
`∫ dm(t) (Θ(x+t) + Θ(x−t))` does not exist; only differences `ω(x) − ω(x ± t)` are integrable.
Every generator below is defined through differences.

### 2.3 Generators in Doob coordinates

For `ω` odd and `x > 0`, two generators arise, differing in how the jump that crosses the origin is
read:

    (𝓛_D ω)(x) = ∫ dm(t) Θ(x)[Θ(x+t)(ω(x) − ω(x+t)) + Θ(x−t)(ω(x) − ω(x−t))]        two-sided (Dirichlet),
    (𝓛_N ω)(x) = ∫ dm(t) Θ(x)[Θ(x+t)(ω(x) − ω(x+t)) + Θ(x−t)(ω(x) − ω(|x−t|))]      folded (Neumann).

The folded generator is the two-sided generator applied to the even reflection `|ω|`; it reads the
reflected point `x − t < 0` through `ω(t − x) > 0` instead of `ω(x − t) < 0`. Their difference is the
reflected mass

    (𝓛_D ω)(x) − (𝓛_N ω)(x) = 2 Θ(x) ∫_{t>x} dm(t) Θ(t−x) ω(t−x)     (ω odd, ω > 0 on (0,∞)).

(`twoSidedGenerator`, `foldedGenerator`.) An `𝓛_N`-supersolution is the object that proves
positivity; an `𝓛_D`-supersolution proves nothing by itself (Section 3.3).

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
forms in `u` with nonnegative kernels.

### 2.5 Objects attached to the shifted ground states

| Object | Definition | Lean |
|---|---|---|
| Reflected collar mass | `C_a(x) = ∫ dm(t) m_a(t − x)⁺` | `shiftedCollarMass` |
| Half-line measure | `μ_a = m_a(x) sinh(x/2) dx` on `(0, ∞)`, total mass `sinh(a/2)/2` | — |
| Profile mean and variance | `ū = 2∫ u dμ_a / sinh(a/2)`, `V_a(u) = 4 sinh(a/2) ∫ (u − ū)² dμ_a` | `profileMoment`, `profileVariance` |
| Cross energy | `X(ω_a,u) = ∫ dm(t) ∫_0^t m_a(x) m_a(t−x) u(x) u(t−x) dx` | `crossEnergy` |
| Fold-excess weight | `W_a(x) = ∫_{t>2x} dm(t) (m_a(t−x) − m_a(x+t))⁺` | `foldExcessWeight` |
| Autocorrelation | `G = Θ ∗ Θ`, even, `0 ≤ G(z) ≤ Θ(|z|/2)`, `∫ G cosh(s/2) = 1/4` | `riemannAutocorr` |
| Averaged kernel | `K(x,y) = ∫_0^∞ m_a(x) m_a(y) da = G(x−y) − G(x+y)` | `averagedKernel` |
| Smooth plateau | `u_L(x) = τ(L+1−x) τ(L+1+x)`, `τ` the smooth transition | `smoothPlateau` |

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

### 3.4 The equation of motion of `Θ` and the shifted ground states

The corpus's harmonic identity of Riemann's kernel (`theta_harmonic_identity`),

    Σ_n Λ(n) n^{−1/2} (Θ(y + log n) + Θ(y − log n)) = cosh(y/2) − 2c Θ(y) + ∫_0^∞ symArchTerm(y,s) ds,

`c = (γ + log π)/2`, with the archimedean remainder bounded uniformly in `y`, says in Doob coordinates
that `𝓛_D 1 = 0` while the potential is positive: the constant `1` is a strict **subsolution** on the
even sector, whose negative direction is the pole (`Q(1) = −1/2`). Subtracting the identity at `x − a`
and `x + a` gives the **source equation** of the shifted ground state, exact for all `x`:

    (𝓛_D ω_a)(x) − Θ(x) cosh(x/2) ω_a(x) = 2 sinh(a/2) sinh(x/2) Θ(x).

Every `ω_a`, `a > 0`, is a strict `𝓛_D`-supersolution on the half line. By 2.3 its folded defect is

    (𝓛_N ω_a)(x) − Θ(x) cosh(x/2) ω_a(x) = 2 Θ(x) [ sinh(a/2) sinh(x/2) − C_a(x) ],

so `ω_a` is a folded supersolution at `x` exactly when the reflected collar mass does not exceed the
source, `C_a(x) ≤ sinh(a/2) sinh(x/2)`. The defect is linear on the span of the shifted ground states.

**The collar returns twice the source.** Since `m_a(log n − x) = Θ(x + a − log n) − Θ(x − a − log n)`,
the signed prime shift sum is `P(x+a) − P(x−a)` with `P(y) = Σ Λ(n) n^{−1/2} Θ(y − log n)`, and the
harmonic identity evaluates `P(y)` as `cosh(y/2)` plus bounded terms. The cosh difference is exactly
`2 sinh(a/2) sinh(x/2)`, and the collar keeps the positive parts of the same terms, so for all
`x ≥ a`

    C_a(x) ≥ 2 sinh(a/2) sinh(x/2) − K

with an explicit constant `K`, with no prime number theorem. The folded defect of `ω_a` is therefore
negative on a half line `[X, ∞)`: the prime mass below `e^x` that the folding returns is twice the
mass that the two-sided source equation accounts for. (Heuristic sharpening: by the prime number
theorem the ratio of collar to source tends to `2` from above as `a → ∞` and to `1 + 8Θ(0) + 4σ`,
`σ = ∫_0^∞ Θ sinh(u/2)`, as `a → 0`. This is the corpus's "factor two between `μ = 1/2` and `μ = 1`".)

### 3.5 No folded supersolution exists

The hypothesis of the sufficiency theorem is never met, and the obstruction is concrete.

- **At the origin.** For every `ω` odd, continuous, nonnegative on `[0, ∞)`, positive at `log 2`,
  Lipschitz near `0`, and dominated by a translate of `Θ` (`Θω ≤ C Θ(· − b)` on the half line), the
  folded defect is strictly negative on a right neighbourhood of `0`
  (`exists_origin_window_foldedGenerator_lt_potential_of_profile`). The prime `2` alone forces it:
  its reflected term tends to `−2 Λ(2) 2^{−1/2} Θ(0) Θ(log 2) ω(log 2) < 0`, while the archimedean
  contribution is `O(√x)` (Lipschitz control of short shifts against the `1/t` singularity), the other
  primes contribute `O(Θ(x) ω(x))`, and the potential is nonnegative. Shifted ground states and their
  nonnegative signed combinations satisfy the hypotheses.
- **At infinity.** For `ω_a`, the collar lower bound of 3.4. For a general odd profile with finite
  folded generator the reflected prime mass is asymptotic to `e^{x/2} ∫_0^∞ e^{r/2} g(r) dr`, while
  the potential sees `g` only at `x` (heuristic for general profiles).

This is the exact sense in which the odd arithmetic form is **not of Z-type**: the reflected jumps
enter the odd-sector operator with a plus sign, and the hard direction of Allegretto–Piepenbrink,
which for a finite Z-matrix follows from Perron–Frobenius (3.9), fails. Positivity, if RH holds, is
carried by the remainder `R_N`, never by the generator: any proof along these lines is a
subsolution-plus-remainder proof.

### 3.6 The two-sided representation and the variation inequality

For `ω = ω_a` the ground-state representation holds with no side condition: `(ω_a, u)` is admissible
for every `a > 0` and `u ∈ C¹_c` (3.10). Adding the reflected sum and difference jumps,
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
is THIM's `oddSinhPotential` with coefficient exactly `1`.

Expanding the reflected square gives the **cross-term form**

    Q(m_a u) = 2S + 2X − 2 ∫_{x>0} u² m_a (C_a − 2 sinh(a/2) sinh(x/2)),

in which the collar excess beyond twice the source is the only negative term, and the cross term
`X` carries the sign information of the primes through products `u(x) u(t−x)` across the fold.

### 3.7 The pole term, the variance, and where the zeros are

The half-line sinh moment of the shift difference is exact: `∫_{x>0} m_a sinh(x/2) = sinh(a/2)/2`.
Hence the source splits as

    4 sinh(a/2) ∫ u² dμ_a = 8 (∫ u dμ_a)² + V_a(u),      V_a(u) = 4 sinh(a/2) ∫ (u − ū)² dμ_a ≥ 0.

The first term is `2 (∫ m_a u e^{−x/2})²`, the **pole term** of the explicit formula for the odd test
`m_a u`; the second is the **profile variance**. The Mellin transform of `m_a` itself is
`−2 sinh(a(s − 1/2)) ξ(s)`, which vanishes at every zero of `ξ`: the shifted ground state is the
zero-free direction of the odd sector, and `Q(m_a) = 2 sinh²(a/2)` is pure pole term.

**Plateau positivity** (`exists_plateau_markovEnergy_phiDoob_shiftedGroundState_ge`). For every
`a > 0` there is `L₀` such that every even `u ∈ C²_c` with `0 ≤ u ≤ 1` and `u = 1` on `[−L, L]`,
`L ≥ L₀`, has `Q(m_a u) ≥ sinh²(a/2)`. The reflected energy of such a profile lives where one of the
two collar points lies beyond `L`, and the far factor of `m_a` is super-exponentially small there
(`Θ(x) ≤ C e^{−16|x|}`); the source is within `e^{−8L}` of the pole term; `S ≥ 0`.

**Far-apart bumps** (`exists_shift_markovEnergy_twoBumpProfile_pos`). For an even `g ∈ C²_c`
supported in `[−1/4, 1/4]`, the profile `u = g(·−a)/m_a + g(−·−a)/m_a(−·)` makes `m_a u` the odd test
`g(x − a) − g(−x − a)`; its cross term is the autocorrelation of `g` at `t − 2a`, and the prime part
of `X` is a smoothed log-window prime sum. By the prime number theorem in such windows,
`X = 2μ² cosh a + O(1)` with `μ = ∫ g e^{u/2}`, while the collar excess on the window is bounded by a
universal constant. If `μ ≠ 0`, `Q(g(x−a) − g(−x−a)) ≥ μ² e^{a} − K > 0` for all large `a`.

**The pole-free form.** Subtracting from `u` its mean `ū` times a wide smooth plateau kills the
pole term without changing the differences of `u` on the support of `u`. The source of
`u − ū u_L` is exactly `V_a(u) + 4 sinh(a/2) ū² (∫ u_L² dμ_a − sinh(a/2)/2)`, within `e^{−8L}` of
`V_a(u)`; its energies `S` and `D` are compared with those of `u` through the **transfer principle**,
a pointwise inequality `(w(x) − w(y))² ≤ α (u(x) − u(y))² + β (v(x) − v(y))²` between profiles passes
to `S(w) ≤ αS(u) + βS(v)` and `D(w) ≤ αD(u) + βD(v)` because all energy kernels are nonnegative,
applied with Young's inequality and with the plateau energies, which are `O(e^{−8L})`. The result is
the unconditional limit identity (`tendsto_markovEnergy_meanCorrectedProfile`)

    Q(m_a (u − ū u_L))  →  2 S(ω_a,u) − D(ω_a,u) + V_a(u)      (L → ∞),

with an explicit rate `e^{−4L}`. The **pole-free variation inequality**

    D(ω_a,u) ≤ 2 S(ω_a,u) + V_a(u)

is therefore equivalent to the asymptotic nonnegativity of these Markov energies
(`reflectedDifferenceEnergy_le_poleFree_iff`); positivity of the odd form on compactly supported
tests implies it. It is sharper than the variation inequality by exactly the pole term, and it is
invariant under `u ↦ u + const`, as `S`, `D`, `V_a` only see differences of `u`.

**Reading.** The positivity of the ground-state family that comes for free is the pole term: wide
plateaus (every shift) and far narrow bumps with nonzero exponential moment are positive directions.
The zeros of `ζ` are seen only through profiles of `μ_a`-mean zero, where the pole term vanishes and
the sign of `2S − D + V_a` is the whole question.

### 3.8 Averaging over the shift

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
no information about off-line zeros. The zeros are visible in the single-shift inequality and in
averages over windows of shifts narrower than the zero gap, not in the average over all shifts.

### 3.9 Fold domination on monotone profiles

If `u` is even, nonnegative and nonincreasing on `[0, ∞)`, then on `0 < x < t/2` the three points
satisfy `x ≤ t−x ≤ x+t`, so `0 ≤ u(x) − u(t−x) ≤ u(x) − u(x+t) ≤ u(x)`, and the collar symmetry gives
for each shift `D(t) ≤ 2 S(t) + 2 E_a(t)`, with `E_a(t) = ∫_0^{t/2} m_a(x) (m_a(t−x) − m_a(x+t))⁺ u(x)² dx`
the **fold excess**. Integrating against `dm`,

    Q(m_a u) ≥ 4 sinh(a/2) ∫ u² dμ_a − 2 ∫_{x>0} u(x)² m_a(x) W_a(x) dx,

so the **weight criterion** `W_a(x) ≤ 2 sinh(a/2) sinh(x/2)` for all `x > 0` would give positivity on
the whole monotone cone. The weight depends on `Θ` alone and vanishes for `x + t ≤ a` because `m_a`
increases on `[0, a]`. (Heuristic: at the origin both sides vanish to first order; the slope
comparison `∫_{t>t_a} dm(t) |m_a'(t)| ≤ sinh(a/2)/2` fails for large `a`, so the dropped same-side
terms away from the origin must compensate, and the criterion as stated is not the final word.)

### 3.10 The finite model

For a finite symmetric nonnegative kernel `K` and any potential `ρ`, the form `E_K − Σ ρ v²` is
nonnegative if and only if a nonnegative nonzero `ω` with `L_K ω ≥ ρ ω` exists; under connectivity
`ω > 0` (`FiniteJumpFormAllegrettoPiepenbrink`). The hard direction minimises the Rayleigh quotient on
the unit sphere and uses that replacing `v` by `|v|` does not increase the form, which is the Z-type
property. This is the template against which the arithmetic odd sector is measured, and the reason
3.5 is the central no-go: the arithmetic odd-sector operator is not Z-type.

### 3.11 Admissibility: how the analysis is discharged

The ground-state representation requires the remainder and the potential density to be integrable
in `t` against `dm` and in `x`. In test coordinates the potential density of `ω_a` is `u(x)² K_a(t,x)`
with `K_a(t,x) = m_a(x)[ω_a(x)(Θ(x+t) + Θ(|x−t|)) − m_a(x+t) − m_a(|x−t|)]`, and for `u` supported in
`[−R, R]` one has `|K_a(t,x)| ≤ K₁ t` (Lipschitz constants of `Θ` and `m_a`) and
`|K_a(t,x)| ≤ K₂ Θ(t − R − a)`. The one-shift remainder satisfies the same two bounds, because the
collar `0 < x < t` meets the support of `u` in two intervals of length at most `R`. Linear bounds
near `t = 0` tame the `1/t` singularity of the archimedean density (`∫ ω(t) t dt < ∞`); decay bounds
in `t` make the prime sums converge (`Σ Λ(n) n^{−1/2} Θ(log n − c) < ∞`). Two recurring general
facts: a nonnegative series of integrable functions with summable integrals is integrable
(`integrable_tsum_of_nonneg`), and product integrability in `(a, x)` for nonnegative integrands with
explicit `a`-integrals needs no majorant.

---

## 4. Traps and sharp boundaries

| Trap | Why it fails; the correct statement |
|---|---|
| An even positive supersolution on all of `ℝ` | Impossible: it would give `Q ≥ 0` on even tests, but `Q(1) = −1/2`. The supersolution must vanish at `0`; the identity is applied only to odd tests. |
| Using `𝓛_D` as the supersolution operator | Its representation has an indefinite remainder. Only `𝓛_N` has a nonnegative remainder. |
| Reading `ω_a > 0` with positive `𝓛_D`-source as a proof | It is a `𝓛_D`-supersolution, not a `𝓛_N`-supersolution; the collar `C_a` exceeds the source near `0` and for all large `x`. |
| Looking for any folded supersolution | None exists (3.5). The live objects are the variation inequalities, not the sign of a generator defect. |
| Estimating a one-sided prime sum by a window prime number theorem first | Evaluate the signed sum through the harmonic identity of `Θ` and use positivity of the discarded part; the exact identity gives the uniform constant `2` where asymptotics give `R(a)`. |
| Defining the generator through a total jump rate | It diverges (`1/t` singularity, `Σ Λ(n) n^{−1/2} = ∞`). Only differences converge; never split a generator into rate minus average. |
| Mixing test and Doob coordinates | `m_a` is a test, `ω_a = m_a/Θ` its Doob coordinate. Generators and supersolutions live in Doob coordinates; kernels and bounds are simplest in test coordinates. |
| Requiring `v/ω` to be `C²` | The identities need no derivatives. The RH criterion needs `v ∈ C²_c`; the quotient only needs to be continuous and bounded on `(0, R]`. |
| Applying Perron–Frobenius to the odd sector | The reflected jumps give positive off-diagonal entries. Z-type arguments apply to the even sector (supercritical) and to `𝓛_N` on `|ω|`, not to the odd form. |
| Treating the source as the pole term | The source is pole term plus variance (3.7). Only the pole term is free positivity; the variance is where profiles differ, and the zeros live on mean-zero profiles. |
| Averaging over all shifts to gain a weaker target | The average over all shifts is `Ξ²`-weighted in frequency and blind to off-line zeros (3.8). Use single shifts or narrow shift windows. |
| Aperture conditions of THIM's gauge (`a < (log 2)/2`) | Supersolution statements here are pointwise in `x` and carry no aperture window; THIM's absorption ratio grows like `exp(πe^{2R})` and is a different object. |

Conventions in the Lean development that are easy to get wrong: `integral_add` and `integral_sub`
need lambda-typed integrability facts, not `Pi.add` forms; rewriting `mem_Iic` inside an `if` fails
on the motive (use `simp only [Set.indicator_apply, mem_Iic]`); in long proofs with integral-laden
contexts, linear arithmetic must be called with an explicit hypothesis list (`linarith only [...]`);
no statement in this theory carries an unproven arithmetic hypothesis: consequences of positivity are
stated as equivalences or as limits of unconditional identities.

---

## 5. The frontier

1. **The pole-free variation inequality** `D ≤ 2S + V_a(u)` for `μ_a`-mean-zero profiles. This is
   the sharp form of the problem on the ground-state family: translation-invariant in the profile,
   free of the pole term, equivalent to the asymptotic nonnegativity of explicit Markov energies.
   The known positive regions, wide plateaus and far bumps with nonzero exponential moment, are
   exactly the regions where the pole term dominates. For `u` nonnegative and nonincreasing the weight
   criterion of 3.9 is a sufficient condition in terms of `Θ` alone; whether it holds, or what replaces
   it, is a question about Riemann's kernel.
2. **The remainder-dominates-defect inequality** `4∫ u² ω_a Θ (C_a − sinh(a/2) sinh(x/2)) ≤ R_N(ω_a,u)`,
   the same question in folded form: THIM's absorption problem in closed form, with both sides
   explicit.
3. **Signed superpositions at infinity.** Combinations `Σ c_j ω_{a_j}` with mixed signs that stay
   positive on `(0, ∞)` fail at the origin; at infinity the folded defect is linear and the sign of
   `Σ c_j (sinh(a_j/2) sinh(x/2) − C_{a_j}(x))` for large `x` is not decided by the collar lower
   bounds alone.
4. **Profiles outside the span.** The forced asymptotics at infinity of a general odd profile with
   finite folded generator (3.5, heuristic), and its exact statement.
5. **Critical Hardy weights.** If the odd form is nonnegative, is it critical or subcritical? The
   natural candidates come from the remainder `R_N` and from the variance `V_a`.
6. **Selectivity.** The identities of 3.1–3.3 hold for any even positive kernel; the arithmetic enters
   only through the equation of motion of `Θ` (3.4). What each statement says for `ζ(s−a)ζ(s+a)`,
   whose potential changes, and for a Beurling system, measures which parts of the theory see the
   primes.

---

## 6. Working in the theory

- State in which coordinates a claim lives before writing it; convert with `m_a = Θ ω_a`.
- Before any new estimate, search the corpus; the same objects exist in the `oddProfile` coordinates
  of CHMD and THIM (`oddProfile a = m_a/(2 sinh(a/2))`, `oddSinhPotential`, collar-versus-direct
  bounds on the low-prime window), and the Weil-cone modules own the window prime number theorems.
- Prefer exact identities to asymptotics: the harmonic identity of `Θ`, the collar Fubini identity,
  the sinh moments, the shift integrals. Use positivity of discarded terms before using analysis.
- Every theorem is unconditional. A statement that would follow from positivity of the odd form is
  recorded as an equivalence with that positivity, or as a limit of unconditional identities.
