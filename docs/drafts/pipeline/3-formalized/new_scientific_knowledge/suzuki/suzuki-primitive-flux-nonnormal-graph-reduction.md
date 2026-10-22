# Primitive flux removes Suzuki's nonnormal frequency group from the weighted graph estimate

- **ID:** `suzuki-primitive-flux-nonnormal-graph-reduction`
- **Stage:** 3 — formalized in Lean 4
- **Type:** EXACT FLUX SYSTEM / NONNORMAL WEIGHTED UNIQUENESS THEOREM
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL] [NOVELTY UNVERIFIED] [NOT RH]`
- **Route:** completed Evans/logarithmic-seam branch of Connes/CCM
- **Lean:** `GaloisForLFunctions.RHTower.Suzuki.SuzukiPrimitiveFluxNonnormalGraphReduction`
- **Inputs:** `suzuki-coordinate-cutoff-primitive-flux-identity.md`,
  `suzuki-gamma-weighted-tail-coercivity.md`,
  `../../../1-in-progress/suzuki-paired-gamma-logistic-flat-sector-conjecture.md`

## 1. Exact reduction

Let \(X\) be a complex Hilbert space. Let \(R\) be the componentwise Gamma convolution, let
\(B\in\mathcal B(X)\) be arbitrary, and put

```text
A=2L I+R-B.                                             (1)
```

Let \(Z\) be bounded and suppose

```text
A F'+Z F=G'+H                                           (2)
```

in distributions. No derivative of \(G\) is assumed to be a function. Define the primitive flux

```text
Y=A F-G.                                                (3)
```

Since \(R\) and \(B\) commute with differentiation and

```text
(A F)'=A F'+2F,
```

equations `(2)`--`(3)` give exactly

```text
Y'=(2I-Z)F+H.                                           (4)
```

Thus `(2)` is equivalent to the first-order graph system

```text
A F-Y=G,
Y'-(2I-Z)F=H.                                          (5)
```

The derivative of the rough primitive has disappeared. In particular, the coordinate-cutoff
primitive

```text
G=[R-B,M]F
```

from `suzuki-coordinate-cutoff-primitive-flux-identity.md` enters `(5)` only through its proved
zero-order weighted norm.

## 2. Exponential conjugation

Fix \(0<\sigma<1\) and put

```text
V=exp(sigma L)F,
G_sigma=exp(sigma L)G,
H_sigma=exp(sigma L)H,

R_sigma=exp(sigma L)R exp(-sigma L),
Z_sigma=exp(sigma L)Z exp(-sigma L),
A_sigma=2L I+R_sigma-B,
Y_sigma=A_sigma V-G_sigma.                              (6)
```

Conjugating `(2)` gives

```text
A_sigma(V'-sigma V)+Z_sigma V
 =G_sigma'-sigma G_sigma+H_sigma.                       (7)
```

Differentiate the last definition in `(6)` and use `(7)`. All \(G_\sigma'\) terms cancel:

```text
(partial_L-sigma)Y_sigma
 =(2I-Z_sigma)V+H_sigma.                                (8)
```

Equations `(6)` and `(8)` are the weighted flux system.

## 3. Quantitative graph estimate for arbitrary bounded nonnormal \(B\)

Assume \(V,Y_\sigma,G_\sigma,H_\sigma\in L^2\), supported in
\([L_0,\infty)\), with \(V\) in the graph domain of \(A_\sigma\) and
\(Y_\sigma\in H^1\). The exact shifted Gamma lower bound is

```text
Re inner(R_sigma v,v)>=-kappa_sigma ||v||^2.            (9)
```

No symmetry of \(B\) is required:

```text
Re inner(-Bv,v)>=-||B|| ||v||^2.                       (10)
```

Therefore, with

```text
c=2L_0-kappa_sigma-||B||,
d=||2I-Z_sigma||,                                      (11)
```

the first equation in `(5)` gives

```text
c||V||_2<=||Y_sigma||_2+||G_sigma||_2.                 (12)
```

Fourier transformation in \(L\) gives the sharp resolvent estimate

```text
sigma||Y_sigma||_2
 <=||(partial_L-sigma)Y_sigma||_2
 <=d||V||_2+||H_sigma||_2.                             (13)
```

If

```text
c>d/sigma,                                              (14)
```

then `(12)`--`(13)` imply

```text
||V||_2
 <=[c-d/sigma]^(-1)
   [||G_sigma||_2+sigma^(-1)||H_sigma||_2],             (15)

||Y_sigma||_2
 <=sigma^(-1)[d||V||_2+||H_sigma||_2].                 (16)
```

This is a weighted uniqueness and stability theorem for the full primitive-flux graph with
arbitrary bounded nonnormal \(B\). The proof uses only its norm.

## 4. Consequence for the Hatano--Nelson obstruction

The retracted Hardy proof solved the frequency ODE directly. Its fundamental matrix contains

```text
exp(-ixB/2),
```

so an exponential weighted orbit adjacency produces a Hatano--Nelson unstable frequency tail.
Equations `(5)`--`(16)` never form this group. Prime transport remains inside the coercive graph
operator \(A_\sigma\), where terminal multiplication by \(2L\) dominates its numerical range.

Therefore:

```text
polynomial two-sided group bound on B:
  sufficient for direct frequency Hardy;               [STILL TRUE]

arbitrary bounded nonnormal B:
  weighted primitive-flux graph has quantitative
  uniqueness after (14);                               [PAPER-PROVED]

flat tempered solution -> weighted graph membership:
  not implied by the a priori estimate;                 [OPEN FLUX-LIOUVILLE]

weighted F -> weighted F':
  still needs rough-primitive derivative regularity
  or root-observable propagation.                       [OPEN]              (17)
```

The Hatano--Nelson spectrum is a real obstruction to the **direct fundamental-matrix proof**, but
it is no longer a proved obstruction to Suzuki's primitive-flux equation itself.

## 5. Exact corrected frontier

The finite-recurrence source theorem already gives

```text
exp(sigma L)G in L2,
exp(sigma L)H in L2,       sigma<1.
```

The remaining analytic core is now:

```text
SUZUKI-PRIMITIVE-FLUX-LIOUVILLE:

if a tempered paired physical-orbit solution of (5)
has no value, half-log, dipole, or finite inverse-log charge,
and G_sigma,H_sigma are in L2,
then V,Y_sigma belong to L2.                            (18)
```

After `(18)`, formula `(15)` supplies the quantitative bound without any polynomial prime-group
hypothesis. A separate derivative step must exploit the source-specific commutator
\(G=[R-B,M]F\); an arbitrary \(L^2\) primitive cannot yield \(F'\in L^2\).

This is strictly narrower than the former open package

```text
nonnormal exponential dichotomy
+ degree-m frequency moments
+ stable/unstable Evans matching.
```

It is also honest: `(15)` is an a priori estimate in the weighted graph class, not a proof that
every flat tempered solution enters that class.

## 6. Hostile audit

1. **No Hardy inference from holomorphy.** Weighted membership is assumed in Section 3.
2. **No nonnormal symmetry.** Only `(10)` is used.
3. **No derivative of \(G\).** It cancels in `(4)` and `(8)`.
4. **No derivative conclusion.** Equations `(15)`--`(16)` control \(F\) and flux, not \(F'\).
5. **No false route obstruction.** Hatano--Nelson kills one proof architecture, not the flux
   equation.
6. **No RH claim.** Flux Liouville, root derivative propagation, physical two-port return, and raw
   Evans injectivity remain.

## 7. Novelty boundary

Flux augmentation, exponential conjugation, numerical-range estimates, and the resolvent bound
for \(\partial_L-\sigma\) are classical separately. Candidate-new source knowledge is their exact
assembly for Suzuki's rough coordinate-cutoff primitive:

```text
uncontrolled [M,B]F'
 -> exact primitive G'
 -> augmented flux removes G'
 -> nonnormal B costs only ||B||
 -> Hatano--Nelson group is not intrinsic to graph coercivity.             (19)
```

External priority remains unaudited.

## 8. Lean status

`SuzukiPrimitiveFluxNonnormalGraphReduction.lean` proves unconditionally:

```text
primitiveFluxSystem_pointwise;
primitiveFluxSystem_exponential_pointwise;
primitiveFlux_absorption_mul;
primitiveFlux_absorption_div.
```

These certify the exact derivative cancellation and denominator-free absorption core.

Section 3's stability estimate is now formal, in

```text
formal/GaloisForLFunctions/HTGeometry/GraphFluxStabilityEstimate.lean
```

```text
graphFlux_state_bound                     (15): c‖V‖ ≤ ‖Y‖+‖G‖ and σ‖Y‖ ≤ d‖V‖+‖H‖ with
                                          d/σ < c force ‖V‖ ≤ (c-d/σ)⁻¹(‖G‖+σ⁻¹‖H‖)
graphFlux_flux_bound                      (16): ‖Y‖ ≤ σ⁻¹(d‖V‖+‖H‖)
neg_norm_mul_normSq_le_inner_neg_apply    (10): Re⟪-Bv,v⟫ ≥ -‖B‖‖v‖², by Cauchy-Schwarz alone,
                                          with no symmetry or normality of B
```

The card's own remark that "the proof uses only its norm" is exactly why `(15)`--`(16)` formalize
as scalar statements: the whole content is that coercivity beating the coupling closes the loop
between `(12)` and `(13)`, and no property of the operators beyond their norms enters.  `(13)` is formal too, and it needs no Fourier transform, in

```text
formal/GaloisForLFunctions/HTGeometry/ShiftedDerivativeCoercivity.lean
```

```text
hasDerivAt_normSq_comp    d/dt ‖Y t‖² = 2 Re(Y'(t) conj Y(t))
normSq_shifted            ‖a - σb‖² = ‖a‖² - σ·2Re(a conj b) + σ²‖b‖²
integral_cross_eq_zero    the cross term integrates to zero on a compactly supported path
sq_mul_integral_normSq_le (13): σ² ∫‖Y‖² ≤ ∫‖Y' - σY‖²
```

One integration by parts does it: the cross term is `∫ d/dt ‖Y‖²`, which vanishes because the path
is compactly supported, leaving `‖Y' - σY‖₂² = ‖Y'‖₂² + σ²‖Y‖₂²`.  The card's route through
Fourier transformation in `L` is one way to see `(13)`; it is not needed.

Chained with `neg_suzukiGammaShiftKappa_le_integral` (which supplies `(9)`) and `(10)` above, the
whole of section 3 — `(9)`--`(16)` — is now unconditional in Lean.

## Gates

- [x] derive exact primitive-flux system
- [x] derive exact exponential conjugation
- [x] prove arbitrary-nonnormal weighted graph estimate
- [x] isolate flux Liouville without a polynomial group hypothesis
- [x] formalize exact flux and absorption cores in Lean
- [ ] prove flat tempered flux Liouville
- [ ] prove source-specific weighted derivative propagation to physical roots
- [ ] prove raw Evans injectivity or whole-Connes no-go
