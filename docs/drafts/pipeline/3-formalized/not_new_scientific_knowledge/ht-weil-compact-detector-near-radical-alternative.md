# HT Weil compact-detector near-radical alternative

- **ID:** `ht-weil-compact-detector-near-radical-alternative`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) — `[PROVED HERE] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lane:** general hypertranscendence; Weil positivity; remote-divisor detection
- **Statement:** In one exact order-one differential-translation field, a compact normalized family
  of strict Weil square tests cannot detect off-critical quartets escaping vertically.  Any
  detector sequence must either escape compactness or approach the radical of the all-line Weil
  form.

## Goal

Strengthen the finite-packet corollary of
`ht-remote-quartet-compact-open-field-invisibility.md`.  A finite packet is automatically compact,
but the genuine Weil route uses infinitely many tests.  The right question is therefore which
infinite test families remain uniformly blind to a remote quartet.

The answer is a compactness/near-radical alternative.  This does not refute the full Weil
criterion.  It identifies the noncompact resource that any complete implementation must use.

## Test space and Mellin coordinates

Fix `A>0`.  Let `D_A` be the real Frechet space of smooth functions `g` on `(0,infinity)` supported
in `[exp(-A),exp(A)]`.  Write

```text
G_g(s) = integral_0^infinity g(u) u^(s-1) du,
phi_g(x) = exp(x/2) g(exp x).
```

Then `phi_g` is smooth and supported in `[-A,A]`, and

```text
G_g(1/2+i z) = integral_R phi_g(x) exp(i z x) dx.            (1)
```

The topology on `D_A` is the transported `C_c^infinity([-A,A])` topology.

## The all-line HT carrier

Fix `alpha>0` with `2 alpha-1 notin Z`, and put

```text
C_alpha(s)
  = 1/(Gamma(alpha+i(s-1/2)) Gamma(alpha-i(s-1/2))).          (2)
```

The carrier theorem in `finite-order-symmetry-ht-rational-gauge-blindness.md` proves that
`C_alpha` is entire of exact order one, hypertranscendental over `C(s)`, and satisfies the scalar
functional equation and Schwarz symmetry.  Its zeros are the simple critical-line points

```text
1/2 +/- i(alpha+n),  n=0,1,2,... .                            (3)
```

For `g in D_A`, define its zero-side Weil square form

```text
W_0(g) = sum_(C_alpha(rho)=0) G_g(rho) G_g(1-rho)
        = 2 sum_(n>=0) |G_g(1/2+i(alpha+n))|^2.               (4)
```

The series is absolutely convergent and nonnegative.

## Continuity of the all-line form `[PROVED HERE]`

Integration by parts in (1) gives, for nonzero real `t`,

```text
|G_g(1/2+i t)| <= ||phi_g'||_1 / |t|.                         (5)
```

The finitely many small ordinates are continuous evaluation functionals, while
`sum_(n>=0)(alpha+n)^(-2)<infinity`.  Hence (5) makes the map

```text
g |-> (G_g(1/2+i(alpha+n)))_(n>=0)
```

continuous from `D_A` to `ell^2`, and (4) shows that `W_0` is a continuous nonnegative quadratic
form on `D_A`.

## Remote symmetric quartet in the same HT field

Fix `0<|delta|<1/2`, put `w=s-1/2`, and for `T>0` define

```text
R_T(s)
  = ((w^2-(delta+iT)^2)(w^2-(delta-iT)^2))/(delta^2+T^2)^2,
F_T(s) = R_T(s) C_alpha(s).                                   (6)
```

The polynomial `R_T` is real-even about `1/2`, is normalized by `R_T(1/2)=1`, and has exactly the
off-critical quartet

```text
Q_(delta,T)
  = {1/2+delta+iT, 1/2-delta-iT,
     1/2+delta-iT, 1/2-delta+iT}.                             (7)
```

Moreover `R_T -> 1` with every derivative uniformly on compact subsets.  Every `F_T` is therefore
entire of exact order one, FE/Schwarz-symmetric, and hypertranscendental.  Since `R_T` and all its
translates are nonzero elements of `C(s)`, generator-by-generator multiplication gives the exact
field equality

```text
C(s)(D^n T_h F_T : h in C, n>=0)
  = C(s)(D^n T_h C_alpha : h in C, n>=0).                    (8)
```

Thus the quartet is inserted without changing the complete differential-translation field.

Define the zero-side form of `F_T` by summing over its divisor.  Equations (3) and (7) give

```text
W_T(g) = W_0(g) + Delta_T(g),                                 (9)

Delta_T(g)
  = 4 Re(
      G_g(1/2+delta+iT)
      G_g(1/2-delta-iT)).                                    (10)
```

## Uniform remote-quartet invisibility on compact test families `[PROVED HERE]`

Let `K` be a compact subset of `D_A`.  Multiplication by `exp(delta x)` and by
`exp(-delta x)` sends `{phi_g:g in K}` to compact subsets of `L^1([-A,A])`.  The Fourier transform
maps `L^1(R)` continuously into `C_0(R)`.  Compactness upgrades pointwise Riemann--Lebesgue decay to
uniform decay: cover either compact image by finitely many `L^1` balls and apply the ordinary
Riemann--Lebesgue lemma to their centers.  Therefore

```text
sup_(g in K) |G_g(1/2+delta+iT)| -> 0,
sup_(g in K) |G_g(1/2-delta-iT)| -> 0.                        (11)
```

Combining (10) and (11),

```text
sup_(g in K) |Delta_T(g)| -> 0.                               (12)
```

This is stronger than pointwise or finite-packet invisibility.

## Compact strict-positivity no-go `[PROVED HERE]`

Assume `K subset D_A` is compact and

```text
W_0(g)>0 for every g in K.                                   (13)
```

Continuity of `W_0` and compactness give

```text
m_K := min_(g in K) W_0(g) > 0.                              (14)
```

By (12), `sup_K |Delta_T|<m_K` for all sufficiently large `T`.  Equations (9) and (14) then give

```text
W_T(g)>0 for every g in K                                    (15)
```

although `F_T` has an off-critical quartet.  Consequently no compact family of strict normalized
Weil square tests is a sufficient critical-line selector, even after exact order one, FE/Schwarz
symmetry, hypertranscendence, and the complete differential-translation field are fixed.

## Detector escape law `[PROVED HERE]`

Let `T_j -> infinity`, and suppose `g_j` belongs to one compact set `K subset D_A` and detects the
inserted quartet in the sense

```text
W_(T_j)(g_j) <= 0.                                           (16)
```

Because `W_0>=0`, equations (9), (12), and (16) imply

```text
0 <= W_0(g_j) <= |Delta_(T_j)(g_j)| -> 0.                    (17)
```

Thus every compact detector sequence is forced into the near-radical of the all-line form.
Equivalently, a detector family for all remote quartets has only two possibilities:

1. **test escape:** it leaves every compact subset of every fixed-aperture space `D_A`; or
2. **near-radical escape:** along the detecting sequence, `W_0(g_j)->0`.

For smooth tests with a common support interval, boundedness of every derivative seminorm implies
relative compactness by the diagonal Arzela--Ascoli argument.  Hence test escape means concretely
that either the logarithmic support aperture tends to infinity or some derivative seminorm becomes
unbounded.  High-frequency modulation is an example of the second behavior.

## Exact consequence for Weil and semilocal routes

The theorem excludes implementations which attempt to derive RH from a compact normalized battery
of strict Weil inequalities, even when the battery is supplemented by all DA-gauge-invariant HT
data.  It also excludes replacing the full test cone by a precompact family separated by a positive
margin from the all-line radical.

It does **not** exclude the full Weil criterion.  The full route can escape precisely through the
two alternatives above:

- supports may become cofinal in the multiplicative group;
- fixed-support tests may acquire unbounded oscillation;
- or prolate/Sonin vectors may approach the radical while their smallest Weil eigenvalues tend to
  zero.

This last option is not an artificial loophole.  The Connes--Consani spectral-triple program
explicitly constructs near-radical vectors of truncated Weil forms and makes their limiting control
part of the open RH mechanism.  The present theorem proves that some such loss of compact strict
margin is necessary for any remote-divisor-complete implementation.

## Parent-theory and novelty audit

`[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`.

The mathematical engine is the standard continuous map

```text
Fourier : L^1(R) -> C_0(R),
```

whose image of a compact set has uniform tails, followed by compactness of a strictly positive
continuous function.  The remote rational gauge and same-field HT realization are already proved
in the parent cards.  Connes--Consani already identify near-radical Weil vectors as the relevant
finite-aperture phenomenon.  The exact HT same-field compact-detector packaging is useful, but it
is a direct assembly of established mechanisms and fails the parent-theory and anti-theatre novelty
gates.

Primary route comparisons:

- A. Connes and C. Consani, *Spectral triples and zeta-cycles*, Enseign. Math. 69 (2023), 93--148,
  DOI `10.4171/LEM/1049`.
- A. Connes and C. Consani, *The Scaling Hamiltonian*, arXiv:1910.14368, especially the semilocal
  compact-support Weil problem.
- J.-F. Burnol, *Sur les Formules Explicites I: analyse invariante*, arXiv:math/0101068, for the
  unconditional small-support positivity class.

## Lean status

The formal tree contains Schwartz/Fourier infrastructure, the `L^1` Riemann--Lebesgue theorem in
the pinned mathlib toolchain, finite Fourier compactness components, and the exponential-type
zero-density theorem.  It does not contain the compact-set uniform-tail theorem in the required
test-space topology, the reflected-gamma HT carrier, the divisor-summed Weil form, or the exact
same-field analytic family as one unconditional Lean statement.  Formalizing a compactness lemma
alone would not justify stage 3.

## Gates

- [x] 0 -> 1: compact-family strengthening and exact route boundary isolated
- [x] 1 -> 2: complete unconditional paper proof
- [x] parent-theory and literature audit; classified as a bridge
- [x] 2 -> 3: complete unconditional theorem formalized in Lean
- [ ] 3 -> 4: closed by failed novelty gate

## Log

- 2026-07-11 -- Proved uniform remote-quartet invisibility on compact fixed-aperture test families.
- 2026-07-11 -- Extracted the detector alternative: every complete sequence must escape test
  compactness or approach the all-line Weil radical.
- 2026-07-11 -- Compared with the Connes--Consani near-radical mechanism and classified the result
  as a rigorous route bridge rather than new scientific knowledge.

## Lean status update — 2026-08-24

`HTGeometry/CompactDetectorNearRadicalAlternative.lean` now formalizes the complete abstract
compactness engine used in the paper proof: compact-uniform vanishing of pointwise decaying
Lipschitz channels; uniform vanishing of the fourfold real quartet defect; existence of the strict
compact margin; eventual positivity away from the radical; convergence of every compact detecting
sequence to the radical; and the exact compact-escape/near-radical disjunction.

`HTGeometry/L1FourierCompactUniformDecay.lean` and
`HTGeometry/L1MellinBoundedTilt.lean` discharge the concrete harmonic-analysis layer: Fourier
evaluation is proved `1`-Lipschitz on `L¹(ℝ)`; Riemann--Lebesgue decay is uniform on every compact
`L¹` family; arbitrary continuous-linear preprocessing preserves this conclusion; the cut
exponential operators agree almost everywhere with `exp(±δx)` on aperture-supported profiles; and
their exact fourfold real product defect vanishes uniformly on compact profile families.

`HTGeometry/SchwartzLogApertureCompactDecay.lean` realizes the card's fixed-support test topology
as the subtype of Schwartz functions supported in `[-A,A]`, proves continuity of its canonical map
to `L¹`, proves that support survives almost everywhere, and pulls compact-uniform quartet decay
back to every compact family in that Schwartz topology.

At this intermediate checkpoint, the remaining card-specific instantiation was analytic: identify
the shifted Mellin evaluations with normalized Fourier coordinates, define the divisor-summed Weil
forms of the reflected-Gamma carrier, and prove their difference is the quartet defect of
`liRemoteQuartetGaugedCarrier`. The later certificate below closes all three items.

## Lean status update — normalized Mellin channel

`HTGeometry/SchwartzLogMellinFourierEvaluation.lean` now proves the exact convention-sensitive
identity

```text
Fourier(exp(delta x) phi(x))(-T/(2 pi))
  = integral exp(delta x) phi(x) exp(i T x) dx,
```

including the `2 pi` rescaling and Fourier sign. It also proves cocompact invariance under this
rescaling and height reflection, compact-uniform vanishing of every shifted Mellin evaluation, and
compact-uniform vanishing of the correctly oriented product with channels `(delta,T)` and
`(-delta,-T)`. This closed the first remaining analytic item; the final certificate below closes
the divisor-summed forms, continuity, and exact difference law.

## Lean certificate — 2026-08-24

Stage-3 closure is complete.

`HTGeometry/SchwartzArithmeticProgressionWeilForm.lean` constructs the continuous linear map from
Schwartz logarithmic profiles to the `ℓ²` sequence of Mellin values at `alpha+n`. It proves the
reciprocal-linear sample bound, square summability, the exact `tsum` identity

```text
W_0(f) = 2 * sum_(n>=0) |G_f(1/2+i(alpha+n))|^2,
```

continuity of `W_0`, and unconditional nonnegativity.

`RHTower/HTWeilCompactDetectorNearRadicalAlternative.lean` defines the literal four-term divisor
sum over `1/2 ± delta ± iT`, proves conjugate-height symmetry for real tests, and identifies that
sum exactly with `4 Re(G(delta,T)G(-delta,-T))`. It then proves:

- exact difference of the gauged-carrier divisor form and `W_0`;
- compact-uniform decay of that actual complex Weil-form difference;
- eventual strict positivity on every nonempty compact real family separated from the radical;
- convergence to the `W_0` radical for every compact detector sequence;
- the global compact-escape/near-radical disjunction for actual gauged-carrier detectors; and
- closed universal capstones `liRemoteQuartetGaugedCarrier_structuralWeilPackage` and
  `htWeilCompactDetectorNearRadicalAlternative`.

The structural capstone links the form to the already-formalized exact zero divisor, exact entire
order one, FE/Schwarz symmetry, hypertranscendence, and unchanged all-translate/all-derivative
differential field of `liRemoteQuartetGaugedCarrier`.

Targeted source checks and exact leaf builds passed for all new modules. Axiom audits of every new
public theorem report only `propext`, `Classical.choice`, and `Quot.sound`. Modules are wired into
their umbrellas; no umbrella or full build was run. No numerical computation was used.
