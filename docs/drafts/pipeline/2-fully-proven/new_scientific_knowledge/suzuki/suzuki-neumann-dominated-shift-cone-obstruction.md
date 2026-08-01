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
