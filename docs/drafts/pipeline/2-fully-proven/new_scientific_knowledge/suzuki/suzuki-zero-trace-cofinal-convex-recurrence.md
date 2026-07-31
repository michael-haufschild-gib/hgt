# Cofinal convex recurrence of the Suzuki--Xi zero-trace hierarchy

- **ID:** `suzuki-zero-trace-cofinal-convex-recurrence`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / PUBLICATION LANE
- **Scientific status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Source:** `suzuki-screw-cesaro-curvature-recurrence.md`; Suzuki's Xi screw function and zero expansion
- **Formal modules (in progress):**
  `formal/GaloisForLFunctions/HTGeometry/CofinalConvexRecurrence.lean`;
  `formal/GaloisForLFunctions/HTGeometry/WaveTraceSpectrum.lean`;
  `formal/GaloisForLFunctions/HTGeometry/WaveTraceConvexRecurrence.lean`;
  `formal/GaloisForLFunctions/HTGeometry/WaveTraceLaplace.lean`;
  `formal/GaloisForLFunctions/HTGeometry/WaveTracePoleTransform.lean`
- **Statement:** Every finite vector of odd inverse-power Xi-zero traces has the origin in the
  interior of the closed convex hull of each cofinal tail; equivalently, finitely many arbitrarily
  late apertures support a positive quadrature annihilating the whole vector exactly.

## Goal

Upgrade the scalar Suzuki screw--Cesaro crossing into a universal finite-dimensional recurrence
law with an exact positive-quadrature consequence.  The theorem must be unconditional, use no RH,
zero simplicity, or rational independence, and apply to a general symmetric Cartwright divisor
whose rightmost Laplace pole frontier contains no real pole.  The `K=1` specialization must recover
the source crossing used in the Suzuki RH lane; higher `K` must add genuinely new simultaneous
spectral information.

## Gates

- [x] 0 -> 1 in-progress: exact source-pure conjecture and Landau/separation attack identified
- [x] 1 -> 2 fully-proven: convergence, active-pole, scalar half-space escape, convex separation,
      and finite positive quadrature proofs dependency-closed
- [ ] 2 -> 3 formalized: exact universal theorem and Xi specialization proved in Lean; targeted
      module build, axiom audit, and lint pass
- [ ] 3 -> 4 publication-ready: standalone theoretical paper, primary-source novelty audit, and
      reproducible Lean certificate

## Exact conjecture

Let `Gamma` be the multiplicity-exact zero-frequency multiset for
`XiC(z)=xi(1/2+iz)`.  For `j>=1`, define

```text
H_j(t)=sum_(gamma in Gamma) sin(gamma t)/gamma^(2j+1).
```

For every `K>=1` and `T>0`, put

```text
V_K(t)=(H_1(t),...,H_K(t)) in R^K.
```

`[PAPER-PROVED]` The origin lies in the interior of

```text
closure(convexHull {V_K(t):t>T}).
```

Consequently there are `1<=m<=K+1`, distinct `t_r>T`, and positive weights `a_r`
with `sum_r a_r=1` such that

```text
sum_r a_r H_j(t_r)=0       for every 1<=j<=K.
```

The proposed universal form replaces the Xi divisor by any infinite discrete multiset invariant
under `gamma |-> -gamma` and conjugation, with reciprocal-square summability, finite horizontal
width, infinitely many distinct `gamma^2`, and no purely imaginary frequency on the active
rightmost pole frontier of any nonzero polynomial spectral weight.

## Approach

For nonzero `c in R^K`, let

```text
P_c(x)=sum_(j=1)^K c_j x^(j-1),
c dot V_K(t)=sum_gamma sin(gamma t) P_c(gamma^(-2))/gamma^3.
```

Its Laplace transform is the meromorphic active-pole sum

```text
M_c(s)=sum_gamma P_c(gamma^(-2)) /
                 (gamma^2 (s^2+gamma^2)).
```

A nonzero polynomial kills only finitely many distinct inverse-square frequencies.  The remaining
poles determine a finite convergence abscissa `delta_c`.  If `c dot V_K` were eventually one-signed,
Landau's nonnegative-Laplace boundary theorem would force a singularity at the real point
`s=delta_c`; Xi has no real nontrivial zero, so `M_c` is regular there.  Thus every nonzero linear
functional assumes both signs on every tail.  Finite-dimensional separation then places zero in
the interior of every closed tail convex hull.  Relative-interior stability under closure and
Caratheodory yield the exact positive quadrature with at most `K+1` nodes.

## Universal theorem `[PAPER-PROVED]`

Let `Gamma` be an infinite locally finite multiset in `C \ {0}` with multiplicity, invariant under
`gamma |-> -gamma` and complex conjugation.  Assume

```text
sum_gamma |gamma|^(-2)<infinity,
sup_gamma |Im gamma|<infinity,
{gamma^2:gamma in Gamma} is infinite.                  (U1)
```

For a real polynomial `P`, define

```text
H_P(t)=sum_gamma sin(gamma t) P(gamma^(-2))/gamma^3.    (U2)
```

Let `Gamma_P` be the active multiset on which `P(gamma^(-2))!=0`, and put

```text
delta_P=sup_(gamma in Gamma_P)|Im gamma|.               (U3)
```

Then:

1. `H_P` is a real continuous function of exponential order `delta_P`.
2. If nonzero `H_P` is eventually nonnegative or eventually nonpositive, the active frontier
   contains a purely imaginary frequency: there is `gamma in Gamma_P` with
   `gamma=+i delta_P` or `gamma=-i delta_P`.
3. Consequently, if `Gamma` contains no purely imaginary frequency, every nonzero `H_P` assumes
   both strict signs after every time `T`.

The real-edge conclusion in 2 is necessary.  For `Gamma={+i delta,-i delta}` and `P=1`, `(U2)` is
a nonzero constant multiple of `sinh(delta t)` and is one-signed on the positive half-line.

## Dependency-closed proof

### 1. Normal convergence and reality

Local finiteness away from zero gives a positive lower bound for `|gamma|`.  From `(U1)`,
`sum |gamma|^(-3)<infinity`.  A fixed polynomial `P(gamma^(-2))` is bounded on `Gamma`; hence, on
`0<=t<=A`,

```text
|sin(gamma t) P(gamma^(-2))/gamma^3|
 <=C_P exp(delta_P A)|gamma|^(-3).
```

The Weierstrass test gives normal convergence of `(U2)` on compact `t`-intervals and the global
bound `|H_P(t)|<=C exp(delta_P t)`.  Conjugation invariance and real coefficients pair each term
with its complex conjugate, so `H_P(t)` is real.  A nonzero polynomial has finitely many roots,
whereas `{gamma^2}` is infinite; therefore `Gamma_P` is infinite and `H_P` has an active pole below.

### 2. Meromorphic active-pole transform

For `Re s>delta_P`, absolute convergence permits termwise Laplace transformation:

```text
M_P(s):=integral_0^infinity H_P(t)exp(-st)dt
 =sum_gamma P(gamma^(-2)) /
      [gamma^2(s^2+gamma^2)].                           (U4)
```

The series on the right converges normally on every compact set avoiding `s=+-i gamma`: for large
`|gamma|` its summands are `O_P(|gamma|^(-4))`.  It therefore defines a meromorphic function on
`C`.  Every active pole is genuine.  The `gamma` and `-gamma` summands are identical, so their
residues reinforce; no other frequency has the same square.

### 3. Landau forces a real-edge pole

Assume `H_P` is eventually nonnegative, choose `T` beyond its last negative value, and set
`h_T(u)=H_P(T+u)`.  Its transform is

```text
M_(P,T)(s)=exp(sT)
  [M_P(s)-integral_0^T H_P(u)exp(-su)du].               (U5)
```

The subtracted compact integral is entire, so `(U5)` has exactly the active poles of `(U4)`.
The exponential bound gives a convergence abscissa `sigma_c<=delta_P`.  If
`sigma_c<delta_P`, the definition of the supremum supplies an active `gamma` for which one of
`+-i gamma` lies in `Re s>sigma_c`.  The nonnegative Laplace integral is holomorphic there,
contradicting the genuine pole in `(U5)`.  Thus `sigma_c=delta_P`.  The tail cannot be identically
zero, since `(U5)` has a genuine pole.

Landau's boundary theorem for a nonzero nonnegative Laplace carrier forces a singularity at the
real convergence-boundary point `s=delta_P`.  Normal convergence and local finiteness show that
`M_P` is holomorphic near that point unless an active pole satisfies `+-i gamma=delta_P`, namely
unless `gamma=+-i delta_P`.  The entire correction in `(U5)` cannot change this.  Therefore eventual
nonnegativity forces a purely imaginary active edge frequency.  Applying the same argument to
`-H_P` proves the eventual-nonpositivity case.  This proves the universal theorem.

### 4. Polynomial half-space escape

For `K>=1`, set

```text
H_j(t)=sum_gamma sin(gamma t)/gamma^(2j+1),
V_K(t)=(H_1(t),...,H_K(t)).                             (U6)
```

For every nonzero `c in R^K`,

```text
c dot V_K(t)=H_(P_c)(t),
P_c(x)=sum_(j=1)^K c_j x^(j-1).                         (U7)
```

If `Gamma` has no purely imaginary frequency, the universal theorem says that `(U7)` assumes both
strict signs after every `T`.

### 5. Convex recurrence and exact quadrature

Fix `T` and let

```text
C_T=closure(convexHull {V_K(t):t>T}) subset R^K.        (U8)
```

If `0` were not an interior point of `C_T`, finite-dimensional separation would give a nonzero
`c` such that `c dot x>=0` for every `x in C_T` after possibly reversing `c`.  This contradicts
the two strict signs of `(U7)` on the tail.  Hence `0 in interior(C_T)`.

For a convex subset of a finite-dimensional real vector space, taking closure does not change its
relative interior.  Since `(U8)` has nonempty full interior, `0` already belongs to the ordinary
convex hull of the tail.  Caratheodory's theorem therefore gives at most `K+1` tail points whose
convex combination is zero.  Delete zero weights and merge repeated points.  The remaining nodes
are distinct, their weights are strictly positive and sum to one, and every coordinate in `(U6)`
vanishes under that weighted sum.  This proves the positive cofinal quadrature.

## Xi--Suzuki specialization `[PAPER-PROVED]`

Take `Gamma` to be the zeros of `XiC(z)=xi(1/2+iz)`, counted with analytic multiplicity.  Standard
properties of completed zeta give all hypotheses `(U1)`: `XiC` is even and real entire of order
one; its divisor is locally finite and infinite; reciprocal squares are absolutely summable; and
the critical strip gives `|Im gamma|<1/2`.  A purely imaginary `gamma` would give a real
nontrivial zero of `xi` in `(0,1)`, but zeta has no real zero there.  The universal convex
recurrence and positive quadrature therefore hold unconditionally for every `K` and `T`.

Suzuki's multiplicity-exact screw expansion and centered Hadamard identity give

```text
g(t)-c_Xi=sum_gamma cos(gamma t)/gamma^2,
H_1(t)=integral_0^t(g(u)-c_Xi)du.                       (U9)
```

Thus `K=1` recovers the cofinal screw--Cesaro crossing.  Higher coordinates form the canonical
regularized primitive hierarchy

```text
H_(j+1)''=-H_j,
H_j(0)=0,
H_j'(0)=sum_gamma gamma^(-2j).                          (U10)
```

The new result is simultaneous: for every finite order and every lower aperture bound, at most
`K+1` later apertures carry a positive probability law annihilating all first `K` regularized
Suzuki--Xi wave traces exactly.

## Hostile audit

- `[REDISCOVERY RISK]` Scalar half-space escape is a direct Landau consequence.  Paper significance
  must rest on the all-polynomial Xi zero-trace family, cofinal convex recurrence, and exact positive
  quadrature, not on renaming Landau's theorem.
- `[POLE-CANCELLATION TEST]` Frequencies `gamma` and `-gamma` reinforce rather than cancel, but the
  polynomial weight may kill finitely many orbits.  Proof must recompute the active frontier after
  deletion and show a genuine pole remains cofinal there.
- `[REAL-EDGE TEST]` Universal theorem is false without excluding a purely imaginary active edge
  frequency: its hyperbolic-sine mode may be eventually one-signed.  The strongest universal form
  should state a recurrence-versus-real-edge-divisor dichotomy.
- `[CONVEXITY TEST]` Sign change of each coordinate separately is insufficient.  Proof must establish
  sign change for every nonzero linear combination before invoking separation.
- `[CLOSURE TEST]` Interior of a closed convex hull does not by itself give a displayed finite
  combination without a finite-dimensional relative-interior argument; this step must be explicit.
- `[NOVELTY UNVERIFIED]` Searches found Suzuki's scalar screw theory, Voros superzeta theory, and
  classical Landau boundary results, but no all-order cofinal convex recurrence or positive
  annihilating quadrature for the Xi zero wave trace.  Priority remains unverified.

## Paper target

Provisional title: *Cofinal convex recurrence of the Riemann zero wave trace and Suzuki's screw
function*.  Target audience: analytic number theory, spectral theory, and operator-theoretic RH.
Core result must be the universal recurrence/real-edge dichotomy; Xi/Suzuki is the principal
application, not the definition of the abstraction.

## Log

- 2026-07-22 -- Opened after rejecting the rank-two cutoff transport identity as a useful but
  routine quasicommutator bridge.  Scalar `H_1` recurrence already exists in the corpus; new claim
  is simultaneous all-order convex recurrence and positive cofinal quadrature.
- 2026-07-22 -- Hostile audit exposed the sharp purely imaginary edge obstruction.  Replaced the
  naive universal claim by the recurrence-versus-real-edge-divisor dichotomy; completed the
  normal-convergence, genuine-pole, Landau, separation, relative-interior, and Caratheodory proof.

## Lean formalization — Sections 4 and 5 COMPLETE

Unconditional, no `sorry`/`admit`/`axiom`/`opaque`/`unsafe`; axiom audit of every listed
theorem returns exactly `[propext, Classical.choice, Quot.sound]`.

### Universal convex recurrence `(U8)` and exact quadrature — `HTGeometry/CofinalConvexRecurrence.lean`

`CofinalHalfSpaceEscape V` says every nonzero continuous linear observable of the path `V`
becomes strictly negative after every time.

- `zero_mem_interior_convexHull_image_Ioi` : under that hypothesis the origin lies in the
  interior of the convex hull of every cofinal tail `V '' Ioi T`.  The proof compactifies the
  dual sphere: finitely many tail points already make every unit observable strictly
  negative, so a uniform margin `δ` exists, and strict separation of a vector of norm `< δ`
  from the hull of those finitely many points contradicts the margin.  This is the
  `[CLOSURE TEST]` of the hostile audit discharged directly, with no closure/relative-interior
  step needed: interiority is proved for the honest convex hull, not its closure.
- `exists_cofinal_positive_quadrature` : Carathéodory (`eq_pos_convex_span_of_mem_convexHull`)
  then produces `nodes : Finset ℝ` with `nodes.card ≤ finrank + 1`, all nodes later than `T`,
  strictly positive weights summing to one, and `∑ w t • V t = 0`.  Node distinctness is
  automatic: the Carathéodory points are affinely independent, hence distinct, and their
  chosen time preimages are therefore distinct.

### Wave traces `(U2)` — `HTGeometry/WaveTraceSpectrum.lean`

`WaveSpectrum G` bundles a conjugation-stable frequency family: an index involution realizing
`gamma -> conj gamma`, a uniform lower modulus bound (local finiteness away from zero), a
uniform horizontal width, and summable inverse squares `(U1)`.

- `summable_traceTerm`, `norm_traceTerm_le`, `norm_waveTrace_le` : the series `(U2)` converges
  absolutely for every real polynomial weight, with the exponential bound
  `C_P * exp (width * |t|)` of Section 1.
- `conj_waveTrace`, `waveTrace_im`, `realWaveTrace`, `ofReal_realWaveTrace` : conjugation
  symmetry of the spectrum makes the trace real, by reindexing the sum along the involution.
- `waveTrace_add`, `waveTrace_smul`, `realWaveTrace_sum` : linearity in the polynomial weight.

### Polynomial half-space escape `(U6)`, `(U7)` — `HTGeometry/WaveTraceConvexRecurrence.lean`

- `tracePath` : the vector `V_K(t) = (H_1(t), ..., H_K(t))` realized by monomial weights.
- `observablePolynomial`, `coeff_observablePolynomial`, `observablePolynomial_ne_zero`,
  `apply_tracePath` : every linear observable of the path is the wave trace of the polynomial
  carrying its coordinates, and a nonzero observable yields a nonzero polynomial.  This is the
  `[CONVEXITY TEST]` of the hostile audit: sign change is established for every nonzero linear
  combination, not coordinatewise.
- `cofinalHalfSpaceEscape_tracePath` and
  `exists_cofinal_positive_quadrature_waveTrace` : from `CofinalWaveSignEscape` (sign escape
  of every nonzero polynomial weight) the full conclusion follows — at most `K + 1` distinct
  later times with positive probability weights annihilating `H_1, ..., H_K` exactly.

### Laplace transform `(U4)` — `HTGeometry/WaveTraceLaplace.lean`

- `sin_mul_exp_eq`, `integrableOn_sin_mul_exp_Ioi` : the damped sine of a complex frequency
  splits into two decaying exponentials and is integrable on `(T, ∞)` whenever
  `|Im gamma| < Re s`.
- `sq_add_sq_ne_zero` : on that half-plane the resolvent denominator `s ^ 2 + gamma ^ 2` does
  not vanish, because `s = ± i gamma` would force `Re s = ∓ Im gamma`.
- `integral_sin_mul_exp_Ioi` : the exact shifted kernel
  `∫_T^∞ sin (gamma t) e^{-s t} dt
     = e^{-sT} (s sin (gamma T) + gamma cos (gamma T)) / (s ^ 2 + gamma ^ 2)`.
  Starting at `T` instead of `0` keeps the resolvent denominator and replaces the numerator
  `gamma` by a phase factor that again equals `gamma` at `s = ± i gamma`.  This is what makes
  the eventual-positivity hypothesis of Section 3 usable without an entire correction term:
  the shifted transform has exactly the same pole divisor as the unshifted one.
- `integral_dampedTerm`, `integral_norm_dampedTerm_le`,
  `summable_integral_norm_dampedTerm`, `hasSum_integral_dampedTerm` : termwise integration
  against the polynomial weight, giving `(U4)` in shifted form —
  `∫_T^∞ H_P(t) e^{-st} dt = ∑_gamma traceCoeff * poleNumer / (s ^ 2 + gamma ^ 2)`.

### Holomorphy of the active-pole transform — `HTGeometry/WaveTracePoleTransform.lean`

- `norm_ccos_le_exp_abs_im`, `norm_traceCoeff_le`, `norm_poleNumer_le`, `norm_poleTerm_le` :
  on any region of norm at most `M` whose distance to the pole divisor is at least `d > 0`,
  the resolvent terms are dominated by `C (M ‖gamma‖⁻³ + ‖gamma‖⁻²)/d`, which is summable by
  `(U1)`.
- `differentiableOn_poleTransform` : consequently the transform is holomorphic on every such
  region (Weierstrass, via `differentiableOn_tsum_of_summable_norm`).
- `poleTransform_eq_integral` : to the right of the horizontal width the transform is the
  Laplace transform itself.

Note the majorant needs no local finiteness of the divisor: a positive uniform distance to the
pole divisor suffices.  Local finiteness is needed only to produce such a distance and to
isolate a single pole.

### Remaining formal work

Two steps remain in the Landau half of Section 3:

1. the genuine-pole argument — at an active `gamma_0` the terms with `gamma ^ 2 = gamma_0 ^ 2`
   all carry the same coefficient (it depends on `gamma` only through `gamma ^ 2`), so their
   residues reinforce and cannot cancel; the rest of the series is holomorphic there;
2. the Landau transfer itself, through the corpus's continuous engine
   `RHTower/LandauIntegralTransfer.lean` (`landau_complexMGF_integrable_transfer`), pushing the
   convergence abscissa left past every real point and contradicting the pole.

Together these give `CofinalWaveSignEscape` for any spectrum without a purely imaginary
frequency, which is the last hypothesis of
`exists_cofinal_positive_quadrature_waveTrace`.
