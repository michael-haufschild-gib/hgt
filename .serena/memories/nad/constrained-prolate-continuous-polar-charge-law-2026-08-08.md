# Card `constrained-prolate-continuous-polar-charge-law` — IN PROGRESS (2026-08-08)

Card: `docs/drafts/pipeline/2-fully-proven/nad/constrained-prolate-continuous-polar-charge-law.md`.
Large analytic card; **most "formalize …" gates are already `[x]`**.  Open Lean gates:
* formalize the concrete radial-PSWF primitive theorem and its polar consequence;
* formalize the concrete radial-PSWF/Bessel realization and `(51)` unconditionally.
Other open gates are audits or open research (`true cofinal Weil floor`, `(18)`/`(32)` promotion).

## Already in the tree (do not rebuild)

* `HTGeometry/FiniteMonotonicityVariation.lean` — namespace is **`HTGeometry`**, not
  `GaloisForLFunctions.HTGeometry`.  `sturmFlux`, one-sign cell critical-point subsingletons,
  `AntitoneOn.eVariationOn_le`, **`eVariationOn_le_of_piecewise_monotone`** (variation ≤ `2nB` from
  a *monotonicity* partition), `boundedVariationOn_of_piecewise_monotone`.
* `RHTower/ProlateOneTurningVariation.lean` — exact prolate flux equation + sign-cell
  critical-point specializations.

## Built 2026-08-08 — `HTGeometry/DerivSignMonotone.lean` (namespace `HTGeometry`)

The missing link between the two files above: *no critical point ⟹ monotone*.
* **`sign_const_of_continuousOn_ne_zero`** — a continuous nonvanishing function on `Icc a b` has
  constant sign (IVT on the subinterval from the endpoint to the offending point;
  `intermediate_value_Icc` / `intermediate_value_Icc'` for the two sign orders).
* **`monotoneOn_or_antitoneOn_of_deriv_ne_zero`** — cell free of critical points is a monotonicity
  cell.  mathlib names are lowercase: `strictMonoOn_of_deriv_pos`, `strictAntiOn_of_deriv_neg`.
* **`eVariationOn_le_of_no_critical_points`** — the variation law with the hypothesis the Sturm side
  actually supplies.

## Second instalment — open-cell form + partition assembly (same file)

**Correction to the first instalment**: requiring `deriv f ≠ 0` on the *closed* cell is unusable —
a partition cut at the critical points has vanishing derivative exactly at its endpoints.  The right
hypothesis is the **open** cell, which is all `strictMonoOn_of_deriv_pos` ever tests.

* **`sign_const_of_continuousOn_ne_zero_Ioo`** — IVT on `uIcc c x` from a fixed interior base point
  (`Set.ordConnected_Ioo |>.uIcc_subset`, `intermediate_value_uIcc`).
* **`monotoneOn_or_antitoneOn_of_deriv_ne_zero_Ioo`**,
  **`eVariationOn_le_of_no_interior_critical_points`**.
* **`exists_partition_of_finite_critical`** — sorting the critical points with the endpoints via
  `Finset.orderIsoOfFin` on `insert a (insert b S)` gives the monotone `I`, `I 0 = a`,
  `I (card−1) = b`, no critical point in any open cell.
  **Lean trap**: `set I : ℕ → ℝ := fun i => …` does *not* let `rw` fire on `I i`; derive
  `hImem : ∀ i (h : i < m), I i = …` by `simp only [hI]; rw [dif_pos h]`, and phrase every
  comparison through **natural-number indices** (`hIcmp`) so the endgame is plain `omega` — Fin
  coercions defeat `omega`.

## Third instalment — item 7's abstract half CLOSED (same file)

* `exists_partition_of_finite_critical` also returns `n ≤ |S| + 1` (`Finset.card_insert_le` twice).
* **`eVariationOn_le_of_finite_critical`** — bounded + finitely many critical points in the open
  interval ⟹ variation ≤ `2(|S|+1)B`.  The caller supplies only the critical set, not a partition.
* **`boundedVariationOn_of_finite_critical`** — the finiteness corollary in the shape the BV
  lattice-envelope modules take as hypothesis.

```
one-sign Sturm cell → ≤ 1 critical point per cell      ProlateOneTurningVariation
finite critical set → ordered monotonicity partition   exists_partition_of_finite_critical
partition + bound   → variation ≤ 2nB                  FiniteMonotonicityVariation
finite crit + bound → BV                               boundedVariationOn_of_finite_critical
```

## Fourth instalment — nodal count reduced to a **sign-change count** (same file)

* **`finite_criticalSet_of_cells`** — `[a,b]` decomposed by a monotone `J` into `N` cells each with
  ≤ 1 critical point ⟹ the whole critical set is finite (induction, `Icc_union_Icc_eq_Icc`,
  `Set.Subsingleton.finite`).
* **`boundedVariationOn_of_finite_criticalSet`** — BV stated for a critical *set* (via
  `Set.Finite.toFinset`), the form the previous item produces.

**Key reduction**: the classical input is no longer a nodal count in the analytic sense — the chain
only needs that `q·f` changes sign finitely often, since
`criticalSet_subsingleton_of_sturm_rhs_pos`/`_neg` already turn each one-sign cell into a
subsingleton:
```
q f has N sign changes → N one-sign cells → ≤1 critical point each → finite critical set
                       → ordered monotonicity partition → variation ≤ 2(N+1)B → BV
```

## Fifth instalment — item 7's abstract theorem, ONE STATEMENT (same file)

* **`finite_criticalSet_of_finite_rhs_zeros`** — `q·f` has finitely many zeros in `(a,b)` ⟹ the
  solution's critical set is finite.  Zero set partitions ⟹ constant sign per open cell ⟹ one-sign
  Sturm law ⟹ `finite_criticalSet_of_cells`.
  **`exists_partition_of_finite_critical` is reused unchanged** — it was stated for an arbitrary
  finite subset, so it partitions by a *zero* set just as well as by a critical set.
* **`boundedVariationOn_of_finite_rhs_zeros`** — the whole one-turning-point argument in one
  statement: a bounded Sturm solution whose RHS has finitely many zeros is BV on the aperture.

For the classical prolate equation `((1−x²)f')' + (χ − c²x²)f = 0` the RHS is a *quadratic* times
the solution, so the hypothesis reduces to: **the solution has finitely many zeros on the aperture
interval**.

## Sixth instalment — zero finiteness (same file)

* **`finite_zeros_of_deriv_ne_zero`** — differentiable, derivative nonzero at each zero ⟹ finitely
  many zeros on a compact interval.  Isolated zeros via `HasDerivAt.tendsto_nhdsNE`; zero set is
  compact (`ContinuousOn.preimage_isClosed_of_isClosed` + `isCompact_Icc.of_isClosed_subset`);
  discrete + compact ⟹ finite (`IsCompact.finite` takes **`IsDiscrete`**, use
  `isDiscrete_iff_nhdsNE` + `Filter.inf_principal_eq_bot`).
* **`finite_zeros_mul`** — zero set of a product is the union.

**mathlib caveat**: `HasDerivAt.eventually_ne` (`Analysis/Calculus/Deriv/Inverse.lean`) is stated
with an **unconstrained** section variable `c` (`variable {c : F}`), reading as `f z ≠ c` for
arbitrary `c`.  Route through `HasDerivAt.tendsto_nhdsNE` instead.
Also: `Deriv/Inverse` and `Topology/DiscreteSubset` are **not** in the import closure of
`FiniteMonotonicityVariation` — import them explicitly.

## Seventh instalment — universal variation lemma COMPLETE; obstruction named

* `deriv_sturmFlux_eq_of_hasDerivAt`, `ode_of_hasDerivAt_on`, **`boundedVariationOn_of_secondOrder`**
  — the whole one-turning-point law in the form a concrete instance must meet.

### The representative `g_λ` is ALREADY BUILT — do not rebuild
`RHTower/ConstrainedProlatePointwiseRepresentative.lean` (1000+ lines) has
`timeBandEigenPointwiseSource`, compact support, integrability, evenness, a.e. equality with the
L² vector, both interior derivatives, half-endpoint equations, and
`timeBandTwoModeConstrainedSource` with zero mean.  `ConstrainedProlatePoissonMuntz.lean` closes
the rest of (35).

### THE CONCRETE OBSTRUCTION (sharp statement)
`timeBandEigenPointwiseSource_unitScale_eigen` is in **integral (finite-Fourier) form**, not the
second-order form the variation law consumes.  The missing step is the classical
**commuting-operator identity**: the prolate operator `((1−x²)f')' + (χ − c²x²)f` commutes with the
finite Fourier transform, so an eigenfunction of the *integral* operator satisfies the *differential*
equation.  No abstract strengthening of the variation law removes this need.

## Eighth instalment — `HTGeometry/SturmSelfAdjoint.lean` (namespace `HTGeometry`)

The analytic heart of the commuting-operator step.  **Not in mathlib, not in the corpus.**
* `integral_mul_sturm_eq_neg` — one IBP against a weight vanishing at both endpoints:
  `∫ u (w v')' = −∫ u' w v'` (`intervalIntegral.integral_mul_deriv_eq_deriv_mul`).
* **`integral_mul_sturm_symm`** — Lagrange's identity, degenerate case: `w` vanishing at both ends
  ⟹ `∫ u (w v')' = ∫ (w u')' v`.  Both sides reduce to `−∫ w u' v'`.

The prolate weight `1 − t²` vanishes exactly at the band ends, so no boundary term survives.

## Ninth instalment — `HTGeometry/ProlateKernelSymmetry.lean` (namespace `HTGeometry`)

* `prolateKernel c x t = exp(i c x t)`,
  `prolateSymbol c x t = −2icxt − c²x² − c²t² + c²x²t²`; **`prolateSymbol_symm`**,
  `prolateKernel_symm`.
* **`hasDerivAt_prolateFlux`** — `d/dt[(1−t²) d/dt K] = (prolateSymbol + c²t²)K`, so subtracting the
  operator's own `c²t²K` leaves `prolateSymbol · K` (`prolateOperator_kernel`).
* **`prolateOperator_kernel_symm`** — hence `L_t K = L_x K`.

**Both halves of the commuting-operator step now exist**: this kernel identity +
`integral_mul_sturm_symm` (8th instalment).

## Tenth instalment — CORRECTION + the missing logical step

**Correction to the 9th instalment**: kernel identity + Sturm symmetry give **commutation only**
(`L f` is again an `F`-eigenfunction with the *same* eigenvalue).  They do **not** give the ODE.
Concluding `L f = μ f` additionally needs the eigenvalue to be **simple**.

`HTGeometry/CommutingEigenvector.lean` (namespace `HTGeometry`), axiom-clean:
* **`eigen_of_commute`** — commuting operators preserve eigenspaces (axioms `[propext, Quot.sound]`).
* **`exists_smul_of_commute_of_eigenspace_le_span`** — + eigenspace spanned by `f` ⟹ `L f = μ • f`.
* `isEigenvector_of_commute_of_simple`.

## Route to (19e): three ingredients, two built

1. ✅ kernel identity `L_t K = L_x K` (`ProlateKernelSymmetry`, 9th)
2. ✅ Sturm symmetry with vanishing weight (`SturmSelfAdjoint`, 8th)
3. ✅ simple-eigenvalue reduction (`CommutingEigenvector`, 10th)

**Still outstanding**: (a) *differentiation under the integral sign*; (b) **simplicity of the
eigenvalue** in the actual constrained spectrum — the same `h₀,h₄` identification the card already
lists as an open gate, so (19e) is blocked on that pre-existing item, not on new abstract work.

## Eleventh instalment — kernel estimates for (a); the assembly did NOT land

Added to `ProlateKernelSymmetry.lean` (all axiom-clean):
* **`norm_prolateKernel`** = 1 (purely imaginary exponent).
* **`hasDerivAt_prolateKernel_fst`** — derivative in the *first* variable, obtained from the
  second-variable one via `prolateKernel_symm`; no separate computation needed.
* **`norm_prolateKernel_deriv_le`** — `‖i c t K‖ ≤ |c|` for `|t| ≤ 1`: the dominating estimate.

## Twelfth instalment — differentiation under the integral PROVED

`HTGeometry/ProlateTransformDeriv.lean` (wired, axiom-clean):
`continuous_prolateKernel_snd`, **`hasDerivAt_prolateTransform`** — for integrable `f` on the band,
`y ↦ ∫₋₁¹ K(c,y,t) f(t) dt` has derivative `∫ i c t K(c,y,t) f(t) dt`.

**All four ingredients of the commuting-operator route are now theorems**: kernel identity
(`ProlateKernelSymmetry`), Sturm symmetry (`SturmSelfAdjoint`), differentiation under the integral
(`ProlateTransformDeriv`), simple-eigenvalue reduction (`CommutingEigenvector`).

## Thirteenth instalment — operator pushed inside the transform (same file)

* `intervalIntegrable_mul_kernelFactor`, `intervalIntegrable_kernel_mul`,
  `prolateTransform_factor` — absorb the parameter factor into the integrand.
  **Trap**: `IntervalIntegrable.congr_fun` does not exist; transport along a pointwise-equal
  function with `have hfun : … = … := by funext t; ring` then `rwa [hfun] at h`.
* **`hasDerivAt_prolateTransform_deriv`** — second derivative, by applying the differentiation
  theorem to `i c t f(t)` rather than redoing the analysis (pass `(c := c)` explicitly — it cannot
  be inferred from the integrability hypothesis).
* **`hasDerivAt_prolateTransformFlux`** — `d/dx[(1−x²) d/dx (Ff)(x)] = ∫ (symbol + c²x²) K f`, so
  the operator becomes the symbol *inside* the integral, same shape as `prolateOperator_kernel`.

With `prolateSymbol_symm` this gives `L_x F f = ∫ (L_t K) f`, one `integral_mul_sturm_symm` away
from `F(L f)`.

## Fourteenth instalment — COMMUTING-OPERATOR IDENTITY ASSEMBLED

* `SturmSelfAdjoint.lean` generalised `ℝ → ℝ` ⟹ `ℝ → A` for
  `[NormedCommRing A] [NormedAlgebra ℝ A] [CompleteSpace A]` (mathlib's interval IBP already lives
  there).  Proof unchanged.  **Commutative** is required — the Lagrange step uses it.
* **`prolateSymbol_integral_eq`** — `∫ f (L_t K) = ∫ (L f) K`.  With
  `hasDerivAt_prolateTransformFlux` (which puts `L_x(Ff)` in that left form) and
  `prolateSymbol_symm`, this *is* the commutation.

**All analytic ingredients of the route are theorems.**

⚠ **Trap**: the transfer uses the kernel's derivative in its **second** variable, factor `i c x`
(`hasDerivAt_prolateKernel`); the differentiation-under-the-integral step uses the **first**-variable
one, factor `i c t` (`hasDerivAt_prolateKernel_fst`).  Not interchangeable.

## Fifteenth instalment — `HTGeometry/SturmWronskian.lean` (simplicity engine)

* **`hasDerivAt_sturmWronskian`** — two solutions of the *same* `(p u')' = q u` ⟹ the weighted
  Wronskian `W = u(p v') − v(p u')` has zero derivative (`W' = u q v − v q u = 0`).
* **`sturmWronskian_eq_of_hasDerivAt`** — `W` is constant.
  **Trap**: `constant_of_has_deriv_right_zero` wants the derivative hypotheses on **`Ico a b`**,
  not `Ioo a b`.

No duplication: `SmallTranslationDerivInvariance.lean` mentions a Wronskian only to say its argument
does *not* need one.

## Sixteenth instalment — simplicity COMPLETED (same file)

* **`div_eq_of_sturmWronskian_eq_zero`** — vanishing Wronskian + `u ≠ 0` + `p ≠ 0` ⟹ `(v/u)' = 0`
  ⟹ `v/u` constant.  The quotient rule turns `p(u v' − v u') = 0` into the numerator of `(v/u)'`.
* **`eq_const_mul_of_sturmWronskian_eq_zero`** — hence `v = (v a / u a) · u`: proportionality.
  End with `calc v y = v y / u y * u y := (div_mul_cancel₀ _ hy0).symm` — `field_simp; linarith`
  fails here.

## Remaining for (19e)

**Every generic Sturm–Liouville ingredient is built** — commutation chain, variation law, BV,
Wronskian, simplicity.  The only outstanding input is the card's own `h₀,h₄` gate: *which* classical
modes sit in the actual constrained spectrum — a question about that specific operator, not about
the general theory.  Then `CommutingEigenvector.exists_smul_of_commute_of_eigenspace_le_span`
converts commutation into the ODE and `boundedVariationOn_of_secondOrder` finishes.

### The exact frictions (all mechanical; solved above)
1. `IntervalIntegrable.1` measurability lands on `Ioc` — rewrite `Set.uIoc_of_le` first.
2. `h_bound`/`h_diff` want `∀ᵐ t, t ∈ uIoc … → …`, **not** a restricted-measure `ae`.
3. Pass `F'` and `bound` explicitly or unification blows the heartbeat limit.
4. The leading argument is a **neighbourhood** `Metric.ball x 1 ∈ 𝓝 x`, not a radius.
5. The name is **overloaded** — must qualify `intervalIntegral.` or the `MeasureTheory` version
   (wanting `Integrable … restrict`) is picked.

### (superseded) earlier attempt
**Attempted and removed**: `ProlateTransformDeriv.lean` assembling
`intervalIntegral.hasDerivAt_integral_of_dominated_loc_of_deriv_le`.  Three frictions, all ordinary
Lean, none mathematical:
1. `IntervalIntegrable.1` gives measurability on `Ioc (-1) 1`; the theorem wants **`uIoc`** — needs
   `uIoc_of_le` rewriting.
2. The dominating-bound step needs the norm split with a different associativity than
   `mul_le_mul_of_nonneg_right` produces (`‖I c t‖ * ‖K * f‖` vs `‖I c t * K‖ * ‖f‖`).
3. The final application **exceeds the heartbeat limit** even at 1.6M — supply the implicit
   `F`/`F'`/`bound` and each hypothesis as separate `have`s with explicit types rather than inline.
The file was deleted rather than left non-compiling in the tree.
