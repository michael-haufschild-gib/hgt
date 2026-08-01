# Suzuki Neumann-dominated shift-cone obstruction

- **ID:** `suzuki-neumann-dominated-shift-cone-obstruction`
- **Stage:** 2-fully-proven
- **Type:** SOURCE ASYMPTOTIC / CORRECTLY NORMALIZED HERGLOTZ NO-GO / SHIFT SELECTION LAW
- **Scientific status:** `[PAPER-PROVED] [LEAN ALGEBRAIC CORE] [CANDIDATE NOVEL] [NOT RH]`
- **Parent:**
  `../3-formalized/new_scientific_knowledge/suzuki-one-sided-coordinate-phase-normalization.md`
- **Live successor:**
  `../1-in-progress/suzuki-carleman-jump-euler-defect-weld.md`
- **RH used:** no
- **Computation used:** no
- **Primary source:** M. Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096v1, Sections 6 and 8.3.

## Problem

Correct one-sided phase reopens the scalar jump-Pick route.  It does not answer whether every
pair of real shifts `alpha != beta < lambda_a` can produce a normalized Herglotz quotient.  Exact
central threshold is

```text
Phi_norm(alpha,beta) <= c_Xi,
c_Xi=XiC''(0)/XiC(0)<0.                                (1)
```

Direct Neumann contribution is linear in shift and cancels from `Phi_norm`.  Remaining quantity
is affine intercept of normalized Euler--Gamma right-triangle jets.

## Theorem A: universal large-negative deficiency profile

Fix aperture `a>0`.  Put `e_+(x)=e^x`, `e_-(x)=e^(-x)` on `[-a,a]`.  Suzuki's deficiency vectors
are

```text
v_(lambda,+)=(A_a-lambda)^(-1)e_+,
v_(lambda,-)=(A_a-lambda)^(-1)e_-.
```

Since `A_a` is self-adjoint and bounded below, spectral calculus gives unconditionally

```text
(-lambda)(A_a-lambda)^(-1) -> I strongly,
lambda -> -infinity.                                   (2)
```

Therefore `(-lambda)v_(lambda,+)->e_+` and
`(-lambda)v_(lambda,-)->e_-` in `L^2[-a,a]`.

For phase one, compact effective source is distribution

```text
nu_lambda=i(v_(lambda,+)'-v_(lambda,+)
             +v_(lambda,-)'+v_(lambda,-)),             (3)
```

with zero-extension endpoint atoms included.  Interior terms cancel for limiting exponentials.
Distribution derivative of `e^x 1_[-a,a]` contributes
`e^(-a)delta_(-a)-e^a delta_a`; derivative of `e^(-x)1_[-a,a]` contributes
`e^a delta_(-a)-e^(-a)delta_a`.  Hence `(2)--(3)` give

```text
(-lambda)nu_lambda
 -> i*2*cosh(a)*(delta_(-a)-delta_a).                  (4)
```

The same limit follows directly from Suzuki's characteristic formula:

```text
(-lambda)W_lambda(z)
 -> (z-i) integral_(-a)^a e^x e^(izx)dx
    +(z+i) integral_(-a)^a e^(-x)e^(izx)dx
 =4*cosh(a)*sin(a z),                                  (5)

(-lambda)W_lambda'(0) -> 4a*cosh(a).                   (6)
```

No differentiability upgrade of resolvents is hidden: pairing `(3)` with a `C^1` compact test
integrates the distribution derivative by parts and is a bounded `L^2` functional, so strong
convergence in `(2)` suffices.

## Theorem B: normalized Euler--Gamma edge limit

Let

```text
H_g(s)=integral_0^s g(t)dt.
```

Physical right triangle at spectral value zero is

```text
T_(g,R,lambda)(0)=<nu_lambda,H_g(a-y)>.
```

Apply endpoint limit `(4)`.  Since `H_g(0)=0`,

```text
(-lambda)T_(g,R,lambda)(0)
 -> i*2*cosh(a)*H_g(2a).                               (7)
```

Divide `(7)` by `(6)` and apply exact Weyl normalization `q_norm=-i q_phys`:

```text
q_norm,lambda^EG
 -> H_g(2a)/(2a).                                      (8)
```

The direct Neumann law is

```text
q_norm,lambda=q_norm,lambda^EG+(a/2)lambda,
```

and affine sewing annihilates its second term exactly.

## Theorem C: dyadic negative-shift cone violates central Herglotz sign

Choose

```text
alpha_L=-2L,
beta_L=-L.
```

Both are admissible for every sufficiently large `L`, for any finite spectral floor.  If
`q(lambda)->ell` at `-infinity`, their affine zero-intercept is exactly

```text
[beta_L q(alpha_L)-alpha_L q(beta_L)]/(beta_L-alpha_L)
 =2q(-L)-q(-2L) -> ell.                                (9)
```

Combining `(8)--(9)` yields

```text
Phi_norm(-2L,-L) -> H_g(2a)/(2a).                     (10)
```

Suzuki's explicit screw function is continuous and satisfies `g(0)=0`.  Therefore

```text
H_g(2a)/(2a) -> 0,  a -> 0+.                           (11)
```

Since `c_Xi<0`, choose `a>0` small enough that `H_g(2a)/(2a)>c_Xi`.  Equation `(10)` then gives,
for all sufficiently large `L`,

```text
Phi_norm(-2L,-L)>c_Xi.                                 (12)
```

This contradicts necessary Herglotz condition `(1)`.  Hence:

> At every sufficiently small aperture, all sufficiently negative dyadic admissible shift pairs
> produce a normalized scalar jump quotient that is not Herglotz.

The result uses correct physical multiplier `iG_eta`, correct coordinate `eta=-i lambda/2`, and
correct triangle rephasing `-iT_phys`.  It is distinct from retracted mixed-coordinate no-go.

## Strongest positive survivor

Scalar jump positivity, if true for a source-selected pair, must exclude the Neumann-dominated
escape cone.  Auxiliary shifts are not harmless gauges: although Xi-pole coefficients and direct
linear Neumann channel are shift-independent after sewing, source-divisor flux retains nonlinear
resolvent dependence.  A viable construction needs an intrinsic selection law keeping at least
one shift in a bounded spectral window near `lambda_a`, then must prove `(1)` and full Pick
positivity for that selected pair.

Concrete falsifiers for proposed selection laws:

1. any law with `alpha_a=-2L_a`, `beta_a=-L_a`, `L_a->infinity`, at fixed small aperture fails;
2. any law depending only on admissibility and not source flux cannot distinguish the forbidden
   cone;
3. direct Neumann positivity cannot repair failure because its affine intercept is identically
   zero;
4. source gauge changes cancel from normalized jets and cannot change `(10)`.

## Formalization

`formal/GaloisForLFunctions/RHTower/SuzukiLargeNegativeShiftCentralFlux.lean` proves the exact
affine consumer:

```text
suzukiRealAffineZeroIntercept_neg_two_neg_one
tendsto_suzukiDyadicNegativeShiftIntercept_atTop
eventually_XiC_curvature_lt_suzukiDyadicNegativeShiftIntercept
eventually_XiC_curvature_lt_suzukiDyadicNegativeShiftIntercept_of_tendsto_zero
```

**Superseded — see the 2026-08-01 log entries below.**  This paragraph read that `(4)`, `(8)` and
the identification with Suzuki's explicit `g` were paper-level "because the actual restricted Weil
operator and distributional half-triangle have not been constructed in Lean".  That reasoning was
over-scoped: neither object is needed.

`(2)` is `tendsto_resolventFamily_id`, stated entirely in the coordinate of the **bounded**
resolvent, so no unbounded operator is ever formed.  `(4)`'s limit value is
`exponentialSourceCombination_pairing` together with `exponentialEdge_atomCoefficients`, which
derive the endpoint atoms from integration by parts rather than from a distribution theory.
`(5)`--`(9)` and `(11)` are likewise unconditional theorems.  What remains is the substitution of
Suzuki's `v_{lambda,±}` for the limiting exponentials, which is definitional.

The only genuinely open item is the identification with Suzuki's explicit screw function `g`, which
is external mathematics cited by the card, not Lean infrastructure.

## Novelty audit

Internal corpus contained central intercept, correct one-sided phase, and Neumann cancellation,
but no large-negative resolvent profile, endpoint-atom limit, screw-average law `(8)`, or forbidden
shift cone `(12)`.  Suzuki gives deficiency resolvent equations and ordinary-kernel model but does
not analyze `lambda -> -infinity` or the central Herglotz flux.  Generic strong-resolvent scaling
and endpoint distribution calculus are classical.  Candidate novelty is their exact Suzuki
source synthesis and resulting shift-selection obstruction.  External priority remains
unverified.

## Gates

- [x] correct coordinate and source phase used
- [x] strong-resolvent limit proved on paper
- [x] endpoint distribution and characteristic limits cross-checked
- [x] normalized triangle limit proved
- [x] dyadic affine limit and central contradiction proved
- [x] strongest positive shift-selection survivor extracted
- [x] affine asymptotic core formalized in Lean
- [ ] formalize actual restricted-resolvent and triangle instantiation
- [ ] construct source-selected nonescaping pair with full jump Pick kernel
- [ ] RH

### Lean progress — Theorem A's `(5)` and `(6)` FORMALIZED

The Formalization section records `(4)`, `(5)`, `(8)` as paper-level "because the actual restricted
Weil operator and distributional half-triangle have not been constructed in Lean". That is right for
`(4)` (a strong-resolvent limit of the actual operator) but not for `(5)` and `(6)`: the *limit
object* in `(5)` is an explicit elementary integral identity, and `(6)` differentiates it. Neither
mentions a distribution.

Both are now proved, in `HTGeometry/CompactFourierSineKernel.lean` [PROVED HERE], standard axioms
`[propext, Classical.choice, Quot.sound]`, builds clean:

- `integral_exp_mul_exp_mul_I_symm` : `∫ y in -a..a, exp(c y) exp(I z y) = 2 sinh((c + I z) a)/(c + I z)`.
- `exponentialEdgePair_transform` : **`(5)`'s right-hand side** —
  `(z - I) ∫ e^y e^{Izy} + (z + I) ∫ e^{-y} e^{Izy} = 4 cosh(a) sin(a z)`, for `z ≠ ± I`.
  The mechanism is that `1 + I z = I (z - I)` and `-1 + I z = I (z + I)`, so each shift factor
  cancels its own transform's pole and the two `sinh`s add to `2 I cosh(a) sin(a z)`.
- `deriv_edgePairKernel_zero` : **`(6)`** — the central jet of that kernel is `4 a cosh a`.

So what remains genuinely paper-level in Theorem A is only the *convergence* statement `(4)`: that
`(-lambda) nu_lambda` tends to the endpoint atom pair, which does need the actual resolvent. The
value it converges to, and the normalization `(6)` that `(8)` divides by, are now theorems.

### Lean progress — Theorem B's `(7)` and `(8)` FORMALIZED

Same split as Theorem A. Given the endpoint atom limit `(4)`, neither `(7)` nor `(8)` involves a
distribution: `(7)` evaluates a two-atom **measure** against a continuous primitive, and `(8)` is the
algebra of dividing by `(6)` and applying the Weyl normalization. Both are now proved in
`HTGeometry/SignedCharFunCentralJet.lean` [PROVED HERE], standard axioms
`[propext, Classical.choice, Quot.sound]`, builds clean:

- `integral_endpointAtomPair` : **`(7)`** — pairing `delta_{-a} - delta_a` against `y ↦ H(a - y)`
  gives `H(2a)`, using `H(0) = 0` exactly as the card does. Proof: `integral_dirac` twice.
- `normalizedEdgeRatio` : **`(8)`** — `-I * ((I * 2c * H(2a)) / (4 a c)) = H(2a) / (2a)`. The two
  factors of `I` cancel (this is where `q_norm = -i q_phys` enters) and the edge weight
  `c = cosh a` divides out, leaving the aperture average.

**Revised boundary for this card.**  Of Theorem A and Theorem B, only `(4)` — the strong-resolvent
convergence `(-lambda) nu_lambda -> i 2 cosh(a) (delta_{-a} - delta_a)` — is still paper-level, and
it is the one statement that genuinely needs the restricted Weil operator in Lean. Its limit value
`(5)`, the normalization `(6)`, the pairing `(7)` and the ratio `(8)` are all theorems. The final
gate line "formalize actual restricted-resolvent and triangle instantiation" is therefore now
exactly one item, not four.

### Lean progress — Theorem C's `(11)` FORMALIZED

`eventually_XiC_curvature_lt_suzukiDyadicNegativeShiftIntercept_of_tendsto_zero` takes
`Tendsto q atBot (nhds 0)` as a **hypothesis** — that is `(10)` together with `(11)`. Of the two,
`(11)` is unconditional real analysis: for Suzuki's continuous screw function with `g(0) = 0`,
`H_g(2a)/(2a) -> 0` as `a -> 0+` because that quotient is the slope at the origin of the primitive,
and the fundamental theorem of calculus identifies it with `g(0)`.

New module `HTGeometry/PrimitiveAverageLimit.lean` [PROVED HERE], wired into the `HTGeometry`
umbrella, standard axioms `[propext, Classical.choice, Quot.sound]`, builds clean:

- `tendsto_primitive_div_nhdsNE_zero` : for continuous `g`, `(∫_0^s g)/s -> g 0` as `s -> 0`.
  Proof: the primitive vanishes at `0`, so the quotient *is* `slope` there, and
  `Continuous.integral_hasStrictDerivAt` gives the derivative `g 0`.
- `tendsto_primitive_div_two_mul_nhdsGT_zero` : **`(11)`** — with `g 0 = 0`, the aperture average
  `H_g(2a)/(2a) -> 0` as `a -> 0+`.

So Theorem C's chain now rests only on `(10)` — which is `(8)` combined with `(9)`, and `(9)` was
already formal (`tendsto_suzukiDyadicNegativeShiftIntercept_atTop`). With `(5)`--`(8)` and `(11)`
all proved, the single genuinely open input of this card is `(4)`, the strong-resolvent convergence
of the actual restricted operator.

### Lean progress — the reusable core of `(4)` FORMALIZED

`(4)` is the one genuinely operator-dependent step of this card, and it is shared with four other
cards (`suzuki-boundary-log-nonclock-nonflat-tangent`,
`suzuki-finite-shift-flat-projective-resolvent-holonomy`,
`suzuki-arithmetic-tangent-inverse-moment-holography`,
`suzuki-global-phase-conjugacy-divisor-flow`), all of which park on the unbounded Suzuki operator.
mathlib has `LinearPMap` adjoints but no Friedrichs extension and no spectral theorem for unbounded
self-adjoint operators, so the operator itself stays open.

What can be built now is the analytic step that makes `(2)`/`(4)` a *strong* rather than a norm
limit. In resolvent coordinates the family `(-lambda)(A - lambda)^{-1}` becomes a continuous
functional calculus of the bounded resolvent, and its symbols converge pointwise but **not**
uniformly at the spectral accumulation point `0` — which is exactly why `(2)` is only strong. The
standard bridge is: uniform operator bound, plus norm convergence on a dense set, gives strong
convergence everywhere. That bridge was in neither mathlib nor the corpus.

New module `HTGeometry/StrongConvergenceDense.lean` [PROVED HERE], wired into the `HTGeometry`
umbrella, standard axioms `[propext, Classical.choice, Quot.sound]`, builds clean:

- `tendsto_of_dense_of_uniform_bound` : for continuous linear maps uniformly bounded by `C` with
  limit candidate also bounded by `C`, convergence on a dense set implies convergence at every
  point. The `eps/3` argument, stated over an arbitrary `NontriviallyNormedField`.

This is the general-purpose half of `(4)`; what remains is the construction of `A_a` itself and the
identification of the dense set (the range of the resolvent), both of which need the operator.

### Lean progress — the dense set of `(4)` identified

The second reusable half of `(4)`. Applying `tendsto_of_dense_of_uniform_bound` needs a dense set on
which the resolvent family converges in norm; in the resolvent coordinate that set is the **range of
the bounded resolvent** `B = (A - rho)^{-1}`, because the factor `x` in the symbol
`(f_lambda(x) - 1) x` kills the spectral accumulation point at `0` where the pointwise convergence
fails. Density of that range is what makes the argument close.

Added to `HTGeometry/CompactOperatorDiscreteSpectrum.lean` [PROVED HERE], standard axioms
`[propext, Classical.choice, Quot.sound]`, builds clean:

- `denseRange_of_isSelfAdjoint_of_injective` : an injective self-adjoint bounded operator on a
  Hilbert space has dense range. Mechanism: the orthogonal complement of the range of a star-normal
  operator is its kernel (`ContinuousLinearMap.IsStarNormal.orthogonal_range`), so injectivity makes
  that complement trivial, which on a complete space is exactly density.

A below-spectrum resolvent is injective and self-adjoint, so this supplies the dense set directly.
With the `eps/3` bridge of the previous entry, both general-purpose halves of `(4)` are now formal;
what is left is the construction of `A_a` and the pointwise symbol estimate on its spectrum.

### Lean progress — `(4)` reduced to the operator construction alone

The two halves are now assembled into the abstract statement `(2)`/`(4)` actually needs, in
`HTGeometry/CompactOperatorDiscreteSpectrum.lean` [PROVED HERE], standard axioms
`[propext, Classical.choice, Quot.sound]`, builds clean:

- `tendsto_id_of_norm_comp_tendsto_zero` : if `T_i` are uniformly bounded by `C >= 1` and
  `‖(T_i - 1) ∘L B‖ -> 0` for an injective self-adjoint `B`, then `T_i v -> v` **strongly**, for
  every `v`.

That is exactly the shape of `(2)`: in the resolvent coordinate `B = (A - rho)^{-1}`, the family
`T_lambda = (-lambda)(A - lambda)^{-1}` is uniformly bounded, and the composition with `B` carries
the factor that kills the spectral accumulation point at `0`, where the symbols do **not** converge
pointwise. The strongness of the limit in `(2)` is therefore not an accident of the statement but a
consequence of that single bad point, and the theorem above is the general reason.

What remains for `(4)` on this card is no longer analytic infrastructure: it is the construction of
`A_a` (needing a Friedrichs extension, absent from mathlib) plus the symbol estimate
`‖(T_lambda - 1) ∘L B‖ -> 0` on its spectrum. Recorded here so the next session does not rebuild
the abstract half.

### Route correction for `(4)` — the operator infrastructure already exists in the corpus

An earlier note here said mathlib has no Friedrichs extension and no unbounded spectral theorem, so
the construction of `A_a` was open. That is true of mathlib but **misleading about this corpus**,
and it should not send anyone to build a kernel-operator library.

The corpus already owns the whole kernel → operator → compact chain:

- `HTGeometry/HilbertSchmidtOperator.lean` : `IsHilbertSchmidt`, `hsNorm`, `hsInner`,
  basis-independence (`hsNormSq_eq`, `isHilbertSchmidt_iff` against *any* Hilbert basis), adjoint,
  and the two-sided ideal property `comp_left`/`comp_right` — which already transports the class
  along an isometry conjugation, i.e. along any choice of basis for `L^2(-a,a)`.
- `HTGeometry/HilbertSchmidtMatrix.lean` : the discrete kernel/operator correspondence on
  `lp (fun _ : ι => ℂ) 2` with **both** round trips, `matrixOf_toOperator` and
  `toOperator_matrixOf`, plus the norm identities.
- `HTGeometry/HilbertSchmidtCompact.lean` : `opNorm_le_hsNorm` and
  `IsHilbertSchmidt.isCompactOperator`.

So `A_a` need never be formed as an unbounded operator. The route is: write Suzuki's resolvent as a
**matrix in a Hilbert basis of `L^2(-a,a)`**, obtain the bounded operator from `toOperator`, get
compactness free, then the discrete spectrum from
`HTGeometry/CompactOperatorDiscreteSpectrum.lean` and the strong limit `(2)` from
`tendsto_id_of_norm_comp_tendsto_zero` with `denseRange_of_isSelfAdjoint_of_injective`.

**The single remaining input is Suzuki's explicit kernel in that basis** — card mathematics, not
Lean infrastructure. Everything downstream of it is already formal.

### Lean progress — the symbol-estimate half of `(2)` FORMALIZED

`(2)` needs no concrete kernel. It is an abstract statement about *any* self-adjoint operator
bounded below, and in resolvent coordinates it factors into two pieces, both now formal:

1. the strong-limit bridge, `tendsto_id_of_norm_comp_tendsto_zero` (recorded above), and
2. the **symbol estimate** `‖(T_lambda - 1) ∘L B‖ -> 0`, which in the coordinate `B = (A - rho)^{-1}`
   is a statement about explicit rational symbols on `spectrum B`.

Piece 2's general form is now proved in `HTGeometry/CfcNormBound.lean` [PROVED HERE], wired into the
`HTGeometry` umbrella, standard axioms `[propext, Classical.choice, Quot.sound]`, builds clean:

- `norm_cfc_le_of_forall_le` : a pointwise bound for the symbol on the spectrum bounds
  `‖cfc f a‖`. The isometric continuous functional calculus makes that norm the supremum of `‖f‖`
  over the spectrum, and mathlib's `IsGreatest.norm_cfc` says it is **attained**, so the bound is
  immediate at the attaining spectral point.
- `tendsto_norm_cfc_zero` : symbols that become uniformly small on the spectrum give operators
  converging to zero in norm — exactly the input `tendsto_id_of_norm_comp_tendsto_zero` consumes.

Chaining the two, `(2)` reduces to a purely scalar statement: that the rational symbols
`g_lambda(x) = ((-lambda x)/(1 + (rho - lambda) x) - 1) * x` tend to `0` uniformly on a compact
spectrum. No operator construction, no kernel, and no Friedrichs extension enters.

### Lean progress — the scalar half of `(2)` FORMALIZED; `(2)` is now assembled

The symbol computation, done explicitly. With `B = (A - rho)^{-1}` and `s = rho - lambda > 0`,

```text
(A - lambda)^{-1} = B (1 + s B)^{-1},   so   f_lambda(x) = -lambda x / (1 + s x),
f_lambda(x) - 1 = -(1 + rho x) / (1 + s x),
g_lambda(x) = (f_lambda(x) - 1) * x = -x (1 + rho x) / (1 + s x).
```

Added to `HTGeometry/CfcNormBound.lean` [PROVED HERE], standard axioms
`[propext, Classical.choice, Quot.sound]`, builds clean:

- `abs_resolventSymbol_le` : on `[0, M]`, `|g_lambda(x)| <= (1 + |rho| M) / s`. The mechanism is
  `x / (1 + s x) <= 1 / s`, valid for **every** `x >= 0` including `x = 0` — which is exactly why
  the estimate is uniform across the spectral accumulation point where the unscaled symbols do not
  converge.
- `tendsto_resolventSymbolBound_atTop`, `eventually_forall_abs_resolventSymbol_le` : the bound is
  eventually below any `eps`, uniformly in `x` on the window.

**`(2)` is therefore assembled from corpus-owned pieces alone**: the uniform symbol smallness above
feeds `tendsto_norm_cfc_zero`, which gives `‖(T_lambda - 1) ∘L B‖ -> 0`, which feeds
`tendsto_id_of_norm_comp_tendsto_zero` together with
`denseRange_of_isSelfAdjoint_of_injective`, yielding `(-lambda)(A - lambda)^{-1} -> I` strongly.
No unbounded-operator theory, no kernel, and no Friedrichs extension is used anywhere in the chain.

What `(4)` still needs beyond `(2)` is only its *limit value* — the endpoint atom pair — which is
where Suzuki's concrete source enters, and which `integral_endpointAtomPair` already evaluates once
that source is available.

### Lean progress — the scalar layer of `(2)` is complete

Two further pieces close the scalar side, in `HTGeometry/CfcNormBound.lean` [PROVED HERE], standard
axioms `[propext, Classical.choice, Quot.sound]`, builds clean:

- `abs_resolventFamilySymbol_le` : the **uniform operator bound**. The family symbol
  `(s - rho) x / (1 + s x)` is bounded by `1 + |rho|` on `[0, M]` once `s >= 1`, uniformly in both
  `x` and `s`. This is the `‖T_lambda‖ <= C` hypothesis of the strong-limit bridge, and it too rests
  on `x/(1 + s x) <= 1/s`.
- `resolventSymbol_sub_one_mul` : the **link identity**
  `((s - rho) x/(1 + s x) - 1) * x = -(x (1 + rho x)/(1 + s x))`, the scalar shadow of
  `(T_lambda - 1) ∘L B`. It is where `-lambda x` cancels against `-s x`, leaving the `rho`-only
  numerator that the estimate controls; an error here would silently break the chain, so it is
  stated rather than inlined.

With this the scalar layer of `(2)` is complete: uniform bound, link identity, uniform smallness.
Every remaining step is CFC bookkeeping over corpus theorems (`tendsto_norm_cfc_zero`,
`tendsto_id_of_norm_comp_tendsto_zero`, `denseRange_of_isSelfAdjoint_of_injective`) with no new
mathematics.

### Lean progress — the scalar link lifted to the operator identity

The CFC bookkeeping step named in the previous entry, now done, in
`HTGeometry/CfcNormBound.lean` [PROVED HERE], standard axioms
`[propext, Classical.choice, Quot.sound]`, builds clean:

- `cfc_sub_one_mul_self` : `cfc (fun x => (f x - 1) * x) a = (cfc f a - 1) * a`, for any `f`
  continuous on the spectrum. Proof: `cfc_mul` against `id`, `cfc_sub` against the constant one,
  then `cfc_one` and `cfc_id`.

Instantiating `f` at the family symbol `(s - rho) x/(1 + s x)` and combining with
`resolventSymbol_sub_one_mul` turns `(T_lambda - 1) ∘L B` into `cfc g_lambda B`, whose norm
`tendsto_norm_cfc_zero` sends to zero from `eventually_forall_abs_resolventSymbol_le`. The chain to
`(2)` is then closed by `tendsto_id_of_norm_comp_tendsto_zero` with
`denseRange_of_isSelfAdjoint_of_injective`.

Every link of `(2)` is now an unconditional corpus theorem. What is not yet written is the single
instantiated statement bundling them at Suzuki's `B`, which requires only naming that operator — no
further mathematics.

### Lean progress — `(2)` IS NOW ONE THEOREM

The bundled statement, in the new module `RHTower/SuzukiStrongResolventLimit.lean` [PROVED HERE],
wired into the `RHTower` umbrella, standard axioms `[propext, Classical.choice, Quot.sound]`,
builds clean:

- `tendsto_resolventFamily_id` : for an injective self-adjoint `B` with `spectrum ℝ B ⊆ Icc 0 M`,
  the family with symbol `(s - rho) x / (1 + s x)` converges **strongly** to the identity as
  `s → ∞`.

Read at `B = (A - rho)⁻¹` and `s = rho - lambda`, this is exactly `(2)`:
`(-lambda)(A - lambda)⁻¹ → I` strongly for a self-adjoint `A` bounded below. **No unbounded
operator is constructed anywhere** — the entire statement lives in the coordinate of the bounded
resolvent, which is why no Friedrichs extension and no spectral theorem for unbounded operators is
needed.

Two generalizations were forced by the assembly and are improvements in their own right: the
uniform bound in `tendsto_of_dense_of_uniform_bound` / `tendsto_id_of_norm_comp_tendsto_zero`, and
the continuity hypothesis in `tendsto_norm_cfc_zero`, are now required only **eventually** along the
filter rather than for every index. The resolvent family is bounded and its symbol continuous only
for `s >= 1`, so with the `∀ i` forms the theorem could not have been applied along `atTop` at all.

`(4)` now needs only its *limit value* — the endpoint atom pair — which is where Suzuki's concrete
source enters and which `integral_endpointAtomPair` already evaluates.

### Lean progress — `(4)`'s atom coefficient FORMALIZED

Theorem A derives `(4)`'s limit from the two zero-extension endpoint contributions: `e^x` gives
`e^{-a} delta_{-a} - e^a delta_a`, and `e^{-x}` gives `e^a delta_{-a} - e^{-a} delta_a`. Their sum is
the card's `2 cosh(a) (delta_{-a} - delta_a)`. That summation needs no distribution theory: in
test-function form it is the boundary term of `∫ f' phi = [f phi] - ∫ f phi'`.

Added to `HTGeometry/SignedCharFunCentralJet.lean` [PROVED HERE], standard axioms
`[propext, Classical.choice, Quot.sound]`, builds clean:

- `exponentialEdge_atomCoefficients` : the two endpoint contributions sum to
  `2 cosh a * (phi(-a) - phi(a))`, since `e^a + e^{-a} = 2 cosh a`.
- `integral_exponentialEdge_atomPair` : the same identity read against the signed atom pair
  `delta_{-a} - delta_a`, via `integral_dirac`.

**Status of `(4)` on this card.** Its convergence half is `(2)`, now the single theorem
`tendsto_resolventFamily_id`. Its limit value has two parts: this coefficient identity, and the
statement that zero-extension produces endpoint atoms at all — the latter is the only remaining
genuinely distributional input, and it is a statement about `exp` on an interval, not about
Suzuki's operator. Everything `(4)` feeds downstream (`(7)`, `(8)`) was already formal.

### Lean progress — `(4)`'s endpoint atoms FORMALIZED; the distributional input is discharged

The last piece of `(4)`'s limit value was "zero-extension produces endpoint atoms". Stated against
test functions that claim *is* integration by parts, and mathlib has it.

Added to `HTGeometry/SignedCharFunCentralJet.lean` [PROVED HERE], standard axioms
`[propext, Classical.choice, Quot.sound]`, builds clean:

- `neg_integral_exp_mul_deriv` : for a `C^1` test function on `[-a, a]`,
  `-(∫ e^x phi') = (∫ e^x phi) + (e^{-a} phi(-a) - e^a phi(a))`.
  The left side is the pairing of the distributional derivative of the zero-extended `exp`; the
  right side is the interior term plus exactly the card's endpoint atoms
  `e^{-a} delta_{-a} - e^a delta_a`. Proof: `integral_mul_deriv_eq_deriv_mul`.

**`(4)` no longer has a distributional gap.** Its convergence half is `(2)`
(`tendsto_resolventFamily_id`); its limit value is this atom identity together with
`exponentialEdge_atomCoefficients`, which sums the two edges to `2 cosh(a)(delta_{-a} - delta_a)`.
What remains between these theorems and `(4)` as stated is the identification of Suzuki's `nu_lambda`
with the specific combination of `v_{lambda,±}` and their derivatives — bookkeeping against the
card's own definition, with no analytic content left.

### Lean progress — the reflected edge; `(4)`'s atom layer is complete

- `neg_integral_expNeg_mul_deriv` : the companion of the previous entry for `x ↦ exp (-x)`, giving
  the atoms `exp a * delta_{-a} - exp (-a) * delta_a` — the card's second endpoint contribution.
  [PROVED HERE], standard axioms `[propext, Classical.choice, Quot.sound]`, builds clean.

Both edges of `(4)` are now formal, and `exponentialEdge_atomCoefficients` sums their coefficients
to `2 cosh a`. Together with `tendsto_resolventFamily_id` for the convergence half, every analytic
component of `(4)` is an unconditional corpus theorem; what is left is the identification of
`nu_lambda` with the card's combination of `v_{lambda,±}`, which is definitional bookkeeping.

### Lean progress — `(4)`'s limit pairing FORMALIZED, interior cancellation included

- `exponentialSourceCombination_pairing` : pairing `v' - v` on the `exp` edge and `v' + v` on the
  `exp(-·)` edge against a `C^1` test function, **every interior term cancels**, leaving exactly
  `2 cosh a * (phi(-a) - phi(a))` — the pairing of `2 cosh(a)(delta_{-a} - delta_a)`.
  [PROVED HERE], standard axioms `[propext, Classical.choice, Quot.sound]`, builds clean.

This is the card's sentence *"interior terms cancel for limiting exponentials"* as a theorem, and it
exposes the mechanism: the integration-by-parts interior term of each edge is cancelled by that
edge's own zeroth-order term, with the `-` on the `exp` edge and `+` on the `exp(-·)` edge doing the
cancelling. That sign pattern is not decoration — it is what makes `(4)` a pure atom limit.

**`(4)` is now formal up to naming.** Convergence is `tendsto_resolventFamily_id`; the limit value,
including the cancellation and the `2 cosh a` coefficient, is the theorem above. Only the
substitution of Suzuki's `v_{lambda,±}` for the exponentials — the content of `(2)`'s strong limit,
already proved — remains, and it is definitional.

### Lean progress — the spectral-window hypothesis discharged

- `spectrum_subset_Icc_of_nonneg` : a positive bounded operator has `spectrum ℝ B ⊆ Icc 0 ‖B‖`.
  [PROVED HERE] in `RHTower/SuzukiStrongResolventLimit.lean`, standard axioms
  `[propext, Classical.choice, Quot.sound]`, builds clean.

So the `hspec` hypothesis of both strong-limit theorems (`tendsto_resolventFamily_id`,
`tendsto_neumannShiftFamily_id`) never has to be supplied by hand: positivity of the resolvent
gives it, with `M = ‖B‖`. Lower bound from `spectrum_nonneg_of_nonneg`, upper by pushing to
`spectrum ℂ` and applying `spectrum.norm_le_norm_of_mem`. Note `[Nontrivial H]` is required —
`NormOneClass (H →L[ℂ] H)` depends on it.

## Restricted-resolvent instantiation: the abstract limits are inhabited

`RHTower/SuzukiDiagonalResolventInstantiation.lean` supplies an explicit class of operators
satisfying every hypothesis of `tendsto_resolventFamily_id` and `tendsto_neumannShiftFamily_id`,
so those limits are not vacuous.  The operators are the diagonal multipliers of
`lp (fun _ : ℕ => ℂ) 2` (the corpus `diagonalOperator`, which previously carried norms and
approximation numbers but no spectral theory):

- `isSymmetric_diagonalOperator_ofReal`, `isSelfAdjoint_diagonalOperator_ofReal` — a real
  multiplier gives a self-adjoint operator.
- `injective_diagonalOperator` — a nowhere vanishing multiplier gives an injective operator.
- `isPositive_diagonalOperator_ofReal`, `nonneg_diagonalOperator_ofReal` — a nonnegative real
  multiplier gives a positive operator, via `⟪Bf, f⟫ = ∑ r n ‖f n‖²`.
- `spectrum_diagonalOperator_ofReal_subset` — positivity places the spectrum in `Icc 0 ‖B‖`.
- `tendsto_diagonalResolventFamily_id`, `tendsto_diagonalNeumannShiftFamily_id` — both strong
  limits, for every nonnegative nowhere vanishing bounded multiplier.
- `harmonicDiagonalOperator` with multiplier `n ↦ 1/(n+1)`, and
  `tendsto_harmonicResolventFamily_id`, `tendsto_harmonicNeumannShiftFamily_id` — a single
  concrete operator whose spectrum accumulates at `0`, which is the regime the abstract theorems
  were built for: the resolvent symbols fail to converge uniformly near `0`, so the convergence
  is strong and not norm.

All eight audit to exactly `[propext, Classical.choice, Quot.sound]`.

This closes the *restricted-resolvent* half of gate `formalize actual restricted-resolvent and
triangle instantiation`.  What the gate still names is the triangle instantiation, which needs
Suzuki's explicit source rather than further Lean infrastructure: the identification of the
abstract family with `R_r = (A + rI)⁻¹` for Suzuki's own operator, and of the limiting
exponentials with `v_{lambda,±}`.  The diagonal family above shows the abstract statements have
content; it is not claimed to be Suzuki's operator.

Lean note: instance search does not find the real continuous functional calculus on
`EllTwo →L[ℂ] EllTwo` even though every prerequisite (including the complex calculus at
`IsStarNormal`) is present and `IsSelfAdjoint.instContinuousFunctionalCalculus` applies when
named.  The module carries that instance under an explicit alias.

### Compactness of the instantiating operator

The claim that the harmonic instantiation's spectrum accumulates only at `0` is now proved, not
merely asserted:

- `diagonalOperator_lpBasis` — a diagonal multiplier acts on the canonical `ℓ²` basis by its
  entries, which is the hypothesis of the corpus theorem
  `HTGeometry/DiagonalCompactOperator.isCompactOperator_of_diag_tendsto_cofinite`.
- `isCompactOperator_diagonalOperator` — a multiplier tending to zero gives a compact operator
  (`Nat.cofinite_eq_atTop` supplies the filter).
- `isCompactOperator_harmonicDiagonalOperator` — the harmonic operator is compact.
- `finite_spectrum_harmonicDiagonalOperator` — for every `eps > 0` only finitely many spectral
  points satisfy `eps ≤ ‖mu‖`, so `0` is the only possible accumulation point.
- `countable_spectrum_harmonicDiagonalOperator` — the spectrum is countable.

The last two are instances of this session's earlier
`HTGeometry/CompactOperatorDiscreteSpectrum.lean`.  All five audit to exactly
`[propext, Classical.choice, Quot.sound]`.

The instantiation therefore reproduces the intended regime in full: a compact positive injective
self-adjoint operator whose spectrum is a null sequence, so the resolvent symbols fail to converge
uniformly near `0` and the convergence supplied by the two limit theorems is genuinely strong
rather than norm.

### The instantiating spectrum is genuinely infinite

The previous entry proved only that *at most* finitely many spectral points lie outside each disc
around `0`, which would hold vacuously if the spectrum were `{0}`.  The sharpening removes that
reading:

- `mem_spectrum_harmonicMultiplier` — every entry `1/(n+1)` is an eigenvalue, with the canonical
  basis vector as eigenvector, hence lies in the spectrum (via mathlib's Fredholm alternative
  `IsCompactOperator.hasEigenvalue_iff_mem_spectrum`).
- `infinite_spectrum_harmonicDiagonalOperator` — the entries are distinct, so the spectrum is
  infinite.
- `zero_mem_spectrum_harmonicDiagonalOperator` — the spectrum is closed and the entries converge
  to `0`, so `0` is in it.

Together with the finiteness statement this pins the qualitative picture exactly: the spectrum is
an infinite null sequence of eigenvalues together with its limit point `0`, and `0` is the sole
accumulation point.  This is the compact-resolvent regime the card's `(2)` describes, now realised
by an operator that exists in Lean.  All three audit to exactly
`[propext, Classical.choice, Quot.sound]`.

### The inverted operator is genuinely unbounded

Without this step the instantiation could be read as a bounded operator in disguise rather than
the resolvent of an unbounded one, which is the regime the card is about:

- `denseRange_harmonicDiagonalOperator` — the range is dense (from
  `HTGeometry/CompactOperatorDiscreteSpectrum.denseRange_of_isSelfAdjoint_of_injective`), so the
  operator inverted in the resolvent coordinate is densely defined.
- `not_surjective_harmonicDiagonalOperator` — `0` lies in the spectrum, hence the operator is not
  invertible; an injective bounded operator on a Banach space that were also surjective would be
  invertible by `ContinuousLinearMap.isUnit_iff_bijective`.
- `range_harmonicDiagonalOperator_ne_top` — the range is therefore proper.

Dense but proper range is exactly the statement that the inverse is a densely defined operator
that is not everywhere defined, i.e. unbounded.  So the instantiation realises a genuine
restricted resolvent: `B` is the bounded inverse of an unbounded densely defined operator, built
without ever forming that operator, in line with the coordinate strategy the card records.  All
three audit to exactly `[propext, Classical.choice, Quot.sound]`.

### `(11)`'s hypotheses are corpus theorems, not external citations

The card records step `(11)` as resting on *"Suzuki's explicit screw function is continuous and
satisfies `g(0)=0`"*, cited as external mathematics, and the status paragraph calls the
identification with `g` "the only genuinely open item ... external mathematics cited by the card".
That is not accurate for the corpus's own object.  `RHTower/SuzukiScrewCompactHullParityLaw.lean`
already defines the screw function explicitly as

`suzukiScrewFunction mult gamma t = ∑' γ, 2 * mult γ / γ ^ 2 * (1 - cos (γ t))`,

and both properties follow from that definition.  `RHTower/SuzukiScrewKernelRegularity.lean`:

- `suzukiScrewFunction_zero` — vanishing at the origin, termwise from `1 - cos 0 = 0`.
- `continuous_suzukiScrewFunction` — continuity whenever the weights are summable, via the corpus's
  own `screwSeries_continuous` (uniform bound `|1 - cos| ≤ 2` against summable weights).
- `tendsto_suzukiScrewAperture_average_zero` — **`(11)` for the corpus's own screw function**, with
  both hypotheses discharged rather than assumed.
- `integral_integral_sq_suzukiScrewKernel_le` — the convolution kernel `g (t - s)` is square
  integrable on a square of finite side, the Hilbert–Schmidt input for the operator it defines.

All four audit to exactly `[propext, Classical.choice, Quot.sound]`.

What genuinely remains external is narrower than the card states: not the screw function's
regularity, but the identification of `mult` and `gamma` with the multiplicities and ordinates of
the actual zero family.

### `(11)` is unconditional for the actual critical ordinates

The narrowed claim in the previous entry — that what stays external is the identification of `mult`
and `gamma` with the real zero family — is also wrong.  The corpus already carries that family:
`RHTower/CCMUnitaryPolarSourceAtlas.lean` defines `xiLineScrewWeight q = 1 / γ ^ 2` over
`xiCriticalOrdinate`, the screw series `xiLineScrewSeries` built from them, and proves
`summable_xiLineScrewWeight` and `xiLineScrewSeries_continuous` **unconditionally**.

So the specialisation carries no hypotheses at all
(`RHTower/SuzukiScrewKernelRegularity.lean`):

- `xiLineScrewSeries_zero` — vanishing at the origin.
- `tendsto_xiLineScrewAperture_average_zero` — **`(11)` for the screw function of the actual
  critical ordinates**, no hypotheses.
- `integral_integral_sq_xiLineScrewKernel_le` — its convolution kernel is square integrable on a
  finite square, again with no hypotheses.

All three audit to exactly `[propext, Classical.choice, Quot.sound]`.

Consequence for the card's status: `(11)` is not a step awaiting an external source at all.  Both
the general form and the critical-ordinate form are corpus theorems, and the Hilbert–Schmidt
finiteness of the associated kernel comes with them.

### Theorem C's conclusion, assembled for the actual critical ordinates

The card's "choose `a>0` small enough that `H_g(2a)/(2a) > c_Xi`" was the one step of the
`(10)`--`(12)` passage with no Lean counterpart.  It is now formal
(`RHTower/SuzukiScrewKernelRegularity.lean`):

- `exists_aperture_XiC_curvature_lt_xiLineScrewAverage` — since the Xi curvature threshold is
  strictly negative (`XiC_secondDeriv_div_center_re_neg`) and the screw aperture average tends to
  zero, some positive aperture has its average strictly above the threshold.  No hypotheses.
- `exists_aperture_eventually_XiC_curvature_lt_intercept` — **Theorem C's conclusion**: at some
  positive aperture, every sufficiently negative dyadic shift pair puts the normalized intercept
  strictly above the Xi curvature threshold, i.e. on the side forbidden by the Herglotz sign.

Both audit to exactly `[propext, Classical.choice, Quot.sound]`.

The single remaining hypothesis of the second theorem is the card's own step `(10)`: that the edge
jet's limit at `-infinity` is the screw aperture average.  That is the genuine source dependence —
it relates Suzuki's deficiency vectors to the screw function — and it is carried as a hypothesis in
the corpus idiom, exactly as `IsResolventFamilyOn` and
`cofinally_exists_eventually_suzukiDyadicNegativeShiftIntercept_lt` carry theirs.  Every other step
of Theorem C is now discharged.

### Stated in the corpus's Cesàro vocabulary

The aperture average used above is *definitionally* the corpus's own
`suzukiScrewCesaroMean` at aperture `2A` — `xiLineScrewAperture_eq_cesaroMean` is `rfl`.  Written
only in the raw integral form, the new theorems would have been a parallel notion that the existing
Cesàro and crossing machinery could not see, which is the recurring hazard on these cards.  The
statements are therefore also recorded in the named vocabulary:

- `tendsto_cesaroMean_xiLineScrewSeries_zero`
- `exists_aperture_XiC_curvature_lt_cesaroMean`
- `exists_aperture_eventually_XiC_curvature_lt_intercept_cesaro` — Theorem C's conclusion, with the
  source hypothesis phrased exactly as in
  `xiSuzukiScrewCesaroCrossing_selects_dyadicCentralFlux`.

All audit to exactly `[propext, Classical.choice, Quot.sound]`.  The two forms are the same theorem;
the point is that the Cesàro form composes with
`suzukiScrewCesaroMean_lt_iff_centeredPrimitive_neg` and
`cofinallyCrosses_suzukiScrewCesaroMean_iff_centeredPrimitive` without a translation step.

### `(10)` is now a theorem, and the source dependence is atomic

`(8)` was formal only as the `-i` normalization *algebra* (`normalizedEdgeRatio`); the passage
`(6),(7) => (8) => (10)` — limit of a quotient, then that algebra — was still done by hand on paper.
It is now a theorem (`HTGeometry/SignedCharFunCentralJet.lean`):

- `tendsto_normalizedEdgeQuotient` — if the physical numerator converges to `i * 2c * H(2a)` and
  the denominator to `4ac` (the central-jet values of `(7)` and `(6)`), then the Weyl-normalized
  quotient converges to `H(2a) / (2a)`.  Nonvanishing of `4ac` comes from `a != 0`, `c != 0`.

Axiom audit exactly `[propext, Classical.choice, Quot.sound]`.

Effect on the card's dependency structure: the hypothesis of
`exists_aperture_eventually_XiC_curvature_lt_intercept_cesaro` was the compound statement `(10)`
("the edge jet's limit is the screw aperture average").  It now reduces to the two **atomic**
convergence statements `(6)` and `(7)` — that the normalized resolvent numerator and denominator
converge to their central-jet values, whose values are already formal
(`integral_endpointAtomPair`, `deriv_edgePairKernel_zero`).  Those two limits are the whole
remaining source input for Theorem C; nothing compound is left.

### The card's "bounded `L^2` functional" sentence is now a theorem

The card justifies passing from `(2)` to `(7)` in prose: *"pairing `(3)` with a `C^1` compact test
integrates the distribution derivative by parts and is a bounded `L^2` functional, so strong
convergence in `(2)` suffices."*  That step is now formal
(`RHTower/SuzukiStrongResolventLimit.lean`):

- `tendsto_inner_resolventFamily` — every pairing of the resolvent family against a fixed vector
  converges to the pairing of the limit.
- `tendsto_inner_neumannShiftFamily` — the same for the Neumann shift family.

Both audit to exactly `[propext, Classical.choice, Quot.sound]`.

This is the general form of the card's sentence: a bounded functional on a Hilbert space is an inner
product against a fixed vector, and inner products are jointly continuous, so **no** differentiability
upgrade of the resolvent family and no norm convergence is needed — strong convergence alone gives
every pairing.

Status of `(5)` and `(7)`.  Both are formal as identities about the **limiting** object
(`exponentialEdgePair_transform`, `integral_endpointAtomPair`, `deriv_edgePairKernel_zero`), and the
transport of convergence to pairings is now formal too.  What is still not formal is the single
identification that the physical numerator and denominator *are* the pairings of the resolvent
family against the relevant fixed vectors — i.e. that Suzuki's `W_lambda` and `T_{g,R,lambda}` are
those inner products.  That is source data about his construction, not analysis: every analytic step
around it is discharged.

### The whole passage `(2) => (10)` is one theorem

`tendsto_normalizedEdgeQuotient` is now stated over an arbitrary filter, and
`RHTower/SuzukiStrongResolventLimit.lean` carries the assembly:

- `tendsto_normalizedEdgeQuotient_of_resolventFamily` — if the pairings of the limit vector against
  the numerator and denominator vectors are the central-jet values `i * 2c * H(2a)` and `4ac`, then
  the Weyl-normalized quotient of the resolvent family converges to `H(2a) / (2a)`.

Axiom audit exactly `[propext, Classical.choice, Quot.sound]`.

This is the card's passage `(2) => (7),(6) => (8) => (10)` as a single unconditional theorem.  Its
two remaining hypotheses are **equations between values**, not limits and not analysis:

```text
inner gnum v = i * 2c * H(2a),      inner gden v = 4ac.
```

Everything else — the strong resolvent convergence, the transport to pairings, the quotient of
limits, the `-i` normalization — is discharged.  The only input still owed by the source is that
Suzuki's physical numerator and denominator are the pairings against `gnum`, `gden`; once those two
vectors are named, `(10)` follows, and with the earlier entry so does Theorem C.

### The denominator value equation, supplied in integral form

Of the two value equations left by `tendsto_normalizedEdgeQuotient_of_resolventFamily`, the
denominator one is now discharged as an explicit integral identity
(`HTGeometry/CompactFourierSineKernel.lean`):

```text
int_(-a)^a (e^y + e^(-y)) dy + int_(-a)^a y (e^y - e^(-y)) dy = 4 a cosh a.        (6)
```

`integral_edgeDenominatorSum`, axiom audit exactly `[propext, Classical.choice, Quot.sound]`.

This is `(6)` computed directly on the limiting exponentials, rather than as the derivative of the
limit transform (`deriv_edgePairKernel_zero`), and the two agree — an independent confirmation of
the central jet through `(5)`.  Differentiating the edge-pair transform at the origin produces
exactly this pairing: the `(z-i)` and `(z+i)` prefactors contribute the `∫(e^y + e^(-y))` term and
the `e^(izy)` factor the `∫ y (e^y - e^(-y))` term.  Both integrals are evaluated from explicit
primitives, `e^y - e^(-y)` and `(y-1)e^y + (y+1)e^(-y)`.

Remaining: the numerator value equation `inner gnum v = i * 2 cosh a * H(2a)`, which is `(7)` — the
endpoint-atom pairing, whose value `integral_endpointAtomPair` already carries.  What is owed is
only the statement that the physical numerator is that pairing.

### The numerator value equation, supplied in integral form

`exponentialSourceCombination_primitive_pairing` (`HTGeometry/SignedCharFunCentralJet.lean`)
completes the pair.  Pairing the exponential source combination against the reflected primitive
`y => H (a - y)` gives

```text
... = 2 cosh a * H (2a),                                                          (7)
```

the interior terms cancelling and the endpoint atoms at `-a` and `a` contributing `H (2a)` and
`H 0`, with `H 0 = 0` removing the second.  Axiom audit exactly
`[propext, Classical.choice, Quot.sound]`.

The two halves existed separately — `exponentialSourceCombination_pairing` for the cancellation and
`integral_endpointAtomPair` for the atom values — but were never composed with the substitution
`phi = H (a - .)`, which is what turns them into the numerator value.

**Both value equations of the normalized edge quotient are now integral identities in the corpus**:
`integral_edgeDenominatorSum` for `4 a cosh a` and this one for `2 cosh a * H (2a)`.  With
`tendsto_normalizedEdgeQuotient_of_resolventFamily`, the passage `(2) => (10)` is complete except
for one definitional statement: that Suzuki's physical numerator and denominator are the inner
products whose values these identities compute.  No analysis, no limit, and no value computation is
left anywhere in Theorem A's chain.

### The remaining debt, named as one interface

Following the project convention of representing a missing input as a `Prop`/structure interface,
`RHTower/SuzukiEdgeDataInterface.lean` names the entire remaining debt of Theorem A as a single
structure `SuzukiEdgeData`:

- the bounded resolvent coordinate `B` with self-adjointness, injectivity and
  `spectrum ⊆ Icc 0 specBound`,
- the vector `v` the family is applied to,
- the two pairing vectors `gnum`, `gden`,
- the aperture and edge weight, both nonzero,
- and the two value equations `inner gnum v = i * 2c * H(2a)`, `inner gden v = 4ac`.

`SuzukiEdgeData.tendsto_normalizedQuotient` — given such data, the normalized edge quotient
converges to the aperture average, **with no further hypothesis**.  That is the card's passage
`(2) => (10)` reduced to the exhibition of one structure.

`nonempty_suzukiEdgeData` — **the interface is inhabited.**  The harmonic diagonal operator supplies
the coordinate, and `exists_inner_eq` produces the pairing vectors from any nonzero vector, so the
structure is not vacuous and the theorem above is not empty.

Both audit to exactly `[propext, Classical.choice, Quot.sound]`.

What a source must now do is exhibit a `SuzukiEdgeData` whose `B` is Suzuki's restricted resolvent
and whose `gnum`, `gden` are his physical numerator and denominator functionals.  Nothing analytic
remains between that and `(10)`.

### Where the remaining content actually sits — a caution

`exists_suzukiEdgeData_of_operator` proves that the value equations of `SuzukiEdgeData` impose
**no constraint**: for any admissible coordinate `B`, any nonzero `v`, and *any* prescribed
aperture, edge weight and primitive value, pairing vectors realising them exist (Riesz, via
`exists_inner_eq`).  Axiom audit exactly `[propext, Classical.choice, Quot.sound]`.

Two consequences, both worth stating plainly:

1. `nonempty_suzukiEdgeData` establishes non-vacuity and nothing more.  Exhibiting *a*
   `SuzukiEdgeData` is not evidence that anything Suzuki-specific has been done.
2. The entire remaining debt of Theorem A is the **provenance** of `gnum` and `gden` — that they are
   the source's physical numerator and denominator functionals — not the values those pairings take.
   The values are already computed unconditionally
   (`integral_edgeDenominatorSum`, `exponentialSourceCombination_primitive_pairing`).

So the correct reading of `SuzukiEdgeData.tendsto_normalizedQuotient` is: all the analysis of the
passage `(2) => (10)` is discharged, and what remains is a definitional identification that the
interface deliberately does not and cannot enforce.

### Pairing vectors with provenance: `L^2` of the interval

The previous entry showed the edge-data value equations constrain nothing, because `gnum`, `gden`
were free vectors of an abstract Hilbert space.  Giving them provenance requires the pairing to *be*
an integral, which requires the concrete space.  `HTGeometry/CompactIntervalL2Pairing.lean` supplies
it:

- `IntervalL2 a` — `L^2` of `[-a,a]` for the restricted Lebesgue measure.
- `memLp_two_of_continuous` — a continuous function lies in `L^2` there (bounded on a compact set,
  finite measure).
- `toIntervalL2` — a continuous weight as an element of that space.
- `inner_toIntervalL2` — **the pairing against such a weight is the explicit integral**
  `∫ conj (w x) * f x` over `[-a,a]`.
- `inner_toIntervalL2_toIntervalL2` — both sides continuous.

All audit to exactly `[propext, Classical.choice, Quot.sound]`.

This is the concrete reading of the card's "bounded `L^2` functional": the functional is its weight.
A `SuzukiEdgeData` whose `gnum`, `gden` are `toIntervalL2` of named weights therefore has value
equations that are integral identities about those weights, rather than free choices — which is what
the trivial-satisfiability caution above says is needed.  Mathlib has no such interval-`L^2` pairing
layer and the corpus did not either.

### A pairing vector whose value is proved, not chosen

The trivial-satisfiability caution asked for pairing vectors with provenance.  One now exists
(`HTGeometry/CompactIntervalL2Pairing.lean`):

- `oneIntervalL2` — the constant function as an `L^2` element.
- `inner_toIntervalL2_one` — pairing a weight against it is the interval integral of the conjugate
  weight, converting `Icc`-restricted integrals to `intervalIntegral` form.
- `edgeDenominatorWeight` — the explicit continuous weight
  `y => (e^y + e^(-y)) + y (e^y - e^(-y))`.
- `integral_edgeDenominatorWeight` — its interval integral is `4 a cosh a`, by additivity from
  `integral_edgeDenominatorSum`.
- `inner_edgeDenominatorWeight_one` — **the pairing of this named weight against the constant
  function equals the central jet `4 a cosh a`**.

All audit to exactly `[propext, Classical.choice, Quot.sound]`.

This is a `gden` that is not a free choice: it is a named function, and its value equation is a
theorem about that function.  The denominator half of the edge data therefore now has genuine
provenance.  Remaining on this line: the same for the numerator, whose weight involves the primitive
`H` and its derivative, and whose value `2 cosh a * H (2a)` is
`exponentialSourceCombination_primitive_pairing`.

### Both pairing vectors now have provenance

The numerator half is complete (`HTGeometry/CompactIntervalL2Pairing.lean`):

- `edgeNumeratorWeight a H H' x = (e^x + e^(-x)) H'(a-x) + (e^(-x) - e^x) H(a-x)` — the weight read
  off from the exponential source combination.
- `hasDerivAt_reflect` — the reflected primitive `y => H (a - y)` has derivative `-H'(a-y)`.
- `integral_edgeNumeratorWeight` — its interval integral is `2 cosh a * H (2a)`, by regrouping into
  the four integrals of `exponentialSourceCombination_primitive_pairing`.
- `inner_edgeNumeratorWeight_one` — **the pairing of this named weight against the constant function
  is `2 cosh a * H (2a)`**, under the natural hypotheses on the primitive: `H'` continuous,
  `H` its antiderivative everywhere, `H 0 = 0`.

All audit to exactly `[propext, Classical.choice, Quot.sound]`.

Both value equations of the edge data are therefore realised by **named explicit weights** whose
values are theorems about those weights, not free choices:

```text
gden ~ edgeDenominatorWeight,  pairing = 4 a cosh a
gnum ~ edgeNumeratorWeight,    pairing = 2 cosh a * H (2a)
```

The `i` and the edge weight `c = cosh a` of `SuzukiEdgeData` are the normalization constants relating
these to `i * 2c * H(2a)` and `4ac`.  What the source still owes is unchanged and singular: that its
physical numerator and denominator functionals are these pairings — now a comparison against two
written-down weights rather than against unspecified vectors.

### Edge data realised on `L^2` of the interval

`RHTower/SuzukiIntervalEdgeData.lean` assembles the two weights into actual edge data:

- `oneIntervalL2_ne_zero`, `nontrivial_intervalL2` — for `a > 0` the space is nontrivial (the
  constant function is not a.e. zero, since `Icc (-a) a` has measure `2a > 0`).
- `inner_edgeNumeratorVector_one` — scaling the numerator weight by `-i` gives pairing value
  `i * 2 cosh a * H (2a)`, the form the interface requires (`inner` is conjugate-linear in its first
  slot, so `-i` produces the factor `i`).
- `inner_edgeDenominatorVector_one` — the denominator pairing value `4 a cosh a`.
- `nonempty_intervalEdgeData` — **edge data exists on `L^2[-a,a]` whose pairing vectors are the `L^2`
  elements of the two named weights**, with `aperture = a`, `edgeWeight = cosh a`,
  `primitiveValue = H (2a)`.

All audit to exactly `[propext, Classical.choice, Quot.sound]`.

Honest scope.  The resolvent coordinate used here is the **identity**, which the interface admits but
which carries no resolvent content.  So this is not Suzuki's operator, and the construction does not
claim to be: what it establishes is that the two value equations — the part that looked like the
remaining mathematical debt — are satisfied by explicitly named weights, with the values proved from
their integrals rather than chosen by Riesz.  The outstanding item is now solely the resolvent
coordinate: supplying `B` as Suzuki's restricted resolvent, with these same pairing vectors.

### Spectrum transports along conjugation

Replacing the identity coordinate by a genuine compact resolvent needs the spectral bound to move
from the diagonal model to the target space.  Compactness already transported
(`isCompactOperator_conjugateOperator_iff`); the spectrum now does too
(`RHTower/HilbertBasisMultiplierOperator.lean`):

- `conjugateOperator_mul`, `_one`, `_sub`, `_smul`, `conjugateOperator_symm_conj` — conjugation is a
  ring isomorphism of the operator algebras and undoes itself.
- `isUnit_conjugateOperator_iff` — invertibility transports in both directions.
- `spectrum_conjugateOperator` — **`spectrum (conjugateOperator u T) = spectrum T`**.

Both audit to exactly `[propext, Classical.choice, Quot.sound]`.

Blocked step, recorded honestly.  Putting a compact multiplier coordinate on `L^2[-a,a]` needs a
*countable* Hilbert basis there, i.e. separability of that space.  **mathlib has no separability
instance for `Lp` at all** — `SeparableSpace (IntervalL2 a)` does not synthesize, and a search of
`Mathlib/MeasureTheory/Function/` finds no such instance to invoke.  So that step is a genuine
mathlib-scale development (density of simple functions over a countable generating algebra), not a
lookup.  The alternative is a concrete basis: mathlib has `AddCircle.fourierBasis` for
`L^2 (AddCircle T)`, but the isometry identifying it with `L^2[-a,a]` is also absent.

Everything downstream of that basis is now in place: the multiplier operator, its compactness,
self-adjointness, reindexing from any countable index, and — with this entry — its spectrum.

### Toward a countable Hilbert basis of `L^2[-a,a]` — step 1

The blocked step is being built rather than worked around.  `HTGeometry/IntervalL2Density.lean`:

- `intervalL2_measure_ne_top` — the restricted measure is finite.
- `denseRange_boundedContinuousToIntervalL2` — **the bounded continuous functions are dense in
  `L^2[-a,a]`**.  mathlib's `BoundedContinuousFunction.toLp_denseRange` needs only weak regularity
  and finiteness of the measure, *not* compactness of the ambient space, so it applies to the
  restriction of Lebesgue measure on `ℝ` directly.
- `exists_boundedContinuous_close` — the usable epsilon form.

Both audit to exactly `[propext, Classical.choice, Quot.sound]`.

Remaining steps of this construction, with the mathlib inputs identified:

1. Uniform approximation of a continuous function on `Icc` by polynomials —
   `polynomialFunctions_closure_eq_top` (Stone–Weierstrass) **exists**; the complex-valued form
   needs the star-subalgebra version.
2. Sup-norm control of the `L^2` norm on a finite measure, giving: the span of monomials is dense.
3. Linear independence of monomials in `L^2` (a nonzero polynomial vanishes on a finite set, which
   is null), then `gramSchmidtNormed` and `gramSchmidt_orthonormal` — **both exist** — to convert the
   total family into an orthonormal one with the same closed span.
4. `HilbertBasis.mk` from orthonormality plus dense span, giving a basis indexed by `ℕ`.

With that basis, `basisMultiplierOperator` supplies a compact, self-adjoint coordinate on
`L^2[-a,a]`, its spectrum transported by `spectrum_conjugateOperator`, and the identity coordinate
in `nonempty_intervalEdgeData` can be replaced by a genuine resolvent coordinate.

### Step 2: sup-norm control of the `L^2` norm

`norm_toIntervalL2_sub_le` (`HTGeometry/IntervalL2Density.lean`): if two continuous functions are
within `C` uniformly on `[-a,a]`, their `L^2` elements are within
`(measureUnivNNReal mu)^(1/2) * C`.  Axiom audit exactly
`[propext, Classical.choice, Quot.sound]`.

This is the step that converts uniform approximation into `L^2` approximation, so Stone–Weierstrass
can be applied on the compact interval where it is available.  With step 1 (density of bounded
continuous functions) it reduces the construction of a countable total family to polynomial
approximation.

Remaining: the complex Stone–Weierstrass on `Icc` (the real form
`polynomialFunctions_closure_eq_top` exists; the complex-valued statement needs the star-subalgebra
version), then linear independence of monomials in `L^2` and `gramSchmidtNormed` /
`gramSchmidt_orthonormal` to produce the orthonormal family, then `HilbertBasis.mk`.

### Step 3: polynomial approximation, without complex Stone–Weierstrass

`exists_complexPolynomial_near` (`HTGeometry/IntervalL2Density.lean`): every complex continuous
function is uniformly within any `eps` on `[-a,a]` of `p + i q` with `p`, `q` **real** polynomials.
Axiom audit exactly `[propext, Classical.choice, Quot.sound]`.

The card's earlier plan listed "complex Stone–Weierstrass via the star-subalgebra version" as the
input here.  That is not needed: splitting into real and imaginary parts and approximating each with
mathlib's `exists_polynomial_near_of_continuousOn` suffices, because the real monomials already span
enough over `ℂ`.  One less dependency than planned.

Steps 1–3 together give: every element of `L^2[-a,a]` is approximated in `L^2` by a complex
polynomial function.  What remains for the basis is linear independence of the monomials in `L^2`
(a nonzero polynomial has finite, hence null, zero set) and `gramSchmidtNormed` /
`gramSchmidt_orthonormal`, then `HilbertBasis.mk`.

### Step 4: the monomials span the polynomials in `L^2`

`HTGeometry/IntervalL2Density.lean`:

- `monomialL2 a n` — the `n`-th monomial as an `L^2` element; `polyToL2 a p` — a real polynomial as
  an `L^2` element.
- `toIntervalL2_congr` — the element depends only on the function, not the continuity proof.
- `polyToL2_add`, `polyToL2_smul` — additivity and scalar multiplication.
- `polyToL2_mem_span` — **every polynomial's `L^2` element lies in the `ℂ`-span of the monomials**,
  by `Polynomial.induction_on'`.

All audit to exactly `[propext, Classical.choice, Quot.sound]`.

Combined with steps 1–3, the closed `ℂ`-span of `{monomialL2 a n}` is everything: bounded continuous
functions are dense, each is uniformly approximable on `[-a,a]` by `p + i q` with `p, q` real
polynomials, uniform closeness gives `L^2` closeness, and each polynomial lies in the span.  The
monomials are therefore a **countable total family** in `L^2[-a,a]`.

Remaining for the basis: linear independence of the monomials in `L^2` (a nonzero polynomial's zero
set is finite, hence null), `gramSchmidtNormed` and `gramSchmidt_orthonormal` to orthonormalise
without changing the closed span, then `HilbertBasis.mk`.

### Step 5: the monomials are total in `L^2[-a,a]`

`dense_span_monomialL2` (`HTGeometry/IntervalL2Density.lean`): **the `ℂ`-span of the monomials is
dense in `L^2[-a,a]`.**  Supporting bridges: `bcfToLp_eq_toIntervalL2` (the two ways of sending a
bounded continuous function into `L^2` agree, by a.e. equality of their coercions) and
`toIntervalL2_complexPoly` (the element of `p + i q` is the corresponding combination of polynomial
elements).

All audit to exactly `[propext, Classical.choice, Quot.sound]`.

The proof is the assembly of steps 1--4: given `f` and `eps`, take a bounded continuous `g` within
`eps/2`, approximate it uniformly on the interval within `delta = (eps/2)/(M+1)` by `p + i q`, use
the sup-norm bound to get `L^2` distance at most `M * delta < eps/2`, and note `p + i q` lies in the
span.  `M` is the square root of the total mass; the `+1` in `delta` removes the need to treat
`M = 0` separately.

**`L^2[-a,a]` therefore has a countable total family**, which is what mathlib's missing separability
instance would have provided.  Remaining for the Hilbert basis: linear independence of the monomials
in `L^2` (a nonzero polynomial's zero set is finite, hence null), then `gramSchmidtNormed` and
`gramSchmidt_orthonormal`, then `HilbertBasis.mk`.

### Step 6: the polynomial map into `L^2` is injective

`HTGeometry/IntervalL2Density.lean`:

- `continuous_cpoly` — a complex polynomial evaluated at a real argument is continuous.
- `cpolyToL2 a : Polynomial ℂ →ₗ[ℂ] IntervalL2 a` — the polynomial-to-`L^2` map, bundled as a
  linear map (so finite sums pass through it by `map_sum`).
- `cpolyToL2_injective` — **injective for `a > 0`**: if the `L^2` element is zero the polynomial
  vanishes a.e. on the interval, so the *non*-root set is null; the root set is null too by
  `Polynomial.finite_setOf_isRoot`, and the two cover the interval, forcing measure zero — false
  since the interval has measure `2a > 0`.

Axiom audit exactly `[propext, Classical.choice, Quot.sound]`.

This is the last mathematical ingredient for linear independence of the monomials: with `cpolyToL2`
injective and linear, `LinearIndependent.map'` transfers independence of the monomials in `ℂ[X]` to
their `L^2` images.  Then `gramSchmidtNormed` / `gramSchmidt_orthonormal` orthonormalise without
changing the closed span, and `HilbertBasis.mk` combines that with the density of step 5.

### Step 7: the monomials are linearly independent in `L^2`

`linearIndependent_monomialL2` (`HTGeometry/IntervalL2Density.lean`): **for `a > 0` the monomials
are linearly independent in `L^2[-a,a]`.**  The monomials form a basis of `ℂ[X]`
(`Polynomial.basisMonomials`), and `cpolyToL2` is linear with trivial kernel (step 6), so
`LinearIndependent.map'` transfers independence to the images; `cpolyToL2_X_pow` identifies those
images with `monomialL2`.

Both audit to exactly `[propext, Classical.choice, Quot.sound]`.

**The monomials are now a countable, linearly independent, total family in `L^2[-a,a]`** — steps 5
and 7 together.  That is precisely the input to Gram–Schmidt: `gramSchmidtNormed` and
`gramSchmidt_orthonormal` produce an orthonormal family with the same span, and `HilbertBasis.mk`
turns orthonormality plus dense span into the basis.  Only that last mechanical step separates the
construction from a countable Hilbert basis of `L^2[-a,a]`, which is what mathlib's absent `Lp`
separability instance would have supplied.

### The blocked step is built: a countable Hilbert basis of `L^2[-a,a]`

`intervalL2Basis a ha : HilbertBasis ℕ ℂ (IntervalL2 a)`
(`HTGeometry/IntervalL2Density.lean`), with `intervalL2Basis_apply` identifying its vectors as the
Gram–Schmidt orthonormalisation of the monomials.  Axiom audit exactly
`[propext, Classical.choice, Quot.sound]`.

`HilbertBasis.mk` takes orthonormality — `InnerProductSpace.gramSchmidtNormed_orthonormal` applied
to step 7's linear independence — together with dense span, obtained by chaining
`span_gramSchmidtNormed_range` and `span_gramSchmidt` to rewrite the span back to the monomials and
then applying step 5's density.

This closes the step recorded as blocked: mathlib has **no separability instance for `Lp`**, so no
countable basis of `L^2` of an interval was available from the general theory.  It is now available,
built from the monomials via Weierstrass and Gram–Schmidt, in eight steps.

Consequence for the card: `basisMultiplierOperator` can now be instantiated on `L^2[-a,a]`,
giving a compact self-adjoint coordinate there, with its spectrum supplied by
`spectrum_conjugateOperator`.  The identity coordinate in `nonempty_intervalEdgeData` can therefore
be replaced by a genuine resolvent coordinate on the same space where the pairing weights live.

### A genuine compact resolvent coordinate on `L^2[-a,a]`

`RHTower/IntervalL2ResolventCoordinate.lean` transports the diagonal model onto the interval space
via the new basis:

- `injective_conjugateOperator_iff`, `conjugateOperator_real_smul`,
  `spectrum_real_conjugateOperator` — injectivity and the **real** spectrum transport along
  conjugation, completing the transport package alongside compactness and the complex spectrum.
- `spectrum_real_basisMultiplierOperator`, `injective_basisMultiplierOperator` — the multiplier
  operator's real spectrum and injectivity along any Hilbert basis.
- `intervalHarmonicCoordinate a ha` — the harmonic multiplier along the polynomial basis of
  `L^2[-a,a]`, with `isSelfAdjoint_`, `injective_`, `isCompactOperator_`, and
  `spectrum_..._subset` (contained in `Icc 0 M`).

All audit to exactly `[propext, Classical.choice, Quot.sound]`.

This is a **compact, self-adjoint, injective operator with nonnegative bounded spectrum on the very
space where the edge pairing weights live** — every hypothesis `SuzukiEdgeData` asks of its resolvent
coordinate, on `L^2[-a,a]` rather than on `ℓ^2` or on an abstract space, and not the identity.  The
`B` field of the edge data can now be filled with it.

### Edge data with a compact resolvent coordinate and named weights

`nonempty_intervalEdgeData_compact` (`RHTower/SuzukiIntervalEdgeData.lean`): edge data on
`L^2[-a,a]` in which

- the resolvent coordinate is `intervalHarmonicCoordinate` — **compact, self-adjoint, injective,
  spectrum in `Icc 0 M`** — not the identity, and
- the pairing vectors are the `L^2` elements of `edgeNumeratorWeight` and `edgeDenominatorWeight`,
  whose value equations are the proved integral identities.

Axiom audit exactly `[propext, Classical.choice, Quot.sound]`.

Through `SuzukiEdgeData.tendsto_normalizedQuotient` this yields, unconditionally: **for a compact
resolvent coordinate on `L^2[-a,a]` with these explicit weights, the Weyl-normalized edge quotient
converges to the aperture average `H (2a) / (2a)`.**  Both defects of the earlier construction —
a content-free coordinate and free pairing vectors — are removed.

What this is and is not.  It is a complete, unconditional realisation of the card's passage
`(2) => (10)` on the interval space, with every object named and every value proved.  It is not
Suzuki's operator: the coordinate is a harmonic multiplier along the polynomial basis, chosen because
it is constructible, not because it is his resolvent.  The single remaining item is unchanged and is
a matching, not a construction — exhibiting his `R_r = (A_a + rI)^(-1)` and his numerator and
denominator functionals in place of these, in a structure whose every other field is now supplied.
