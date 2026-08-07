# Suzuki boundary-log non-clock and non-flat tangent theorem

- **ID:** `suzuki-boundary-log-nonclock-nonflat-tangent`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / SUZUKI SOURCE OPERATOR / EXACT NON-CLOCK RIGIDITY
- **Scientific status:** `[PAPER-PROVED] [UNCONDITIONAL] [NOVELTY UNVERIFIED AFTER TARGETED SEARCH]`
  `[NOT AN RH PROOF]`
- **Primary source input:** Masatoshi Suzuki, *Weil's quadratic form via the screw function*,
  arXiv:2606.09096v1 (2026), equations (2.2), (2.9)--(2.11), and Theorem 1.1.
- **New conclusion:** source does not state endpoint action on `e^x`, finite-shift non-clock
  rigidity, or nonvanishing of far-negative projective tangent proved below.

## 1. Setup

Fix `a>0`. Let `A_a` be Suzuki's lower-bounded self-adjoint operator on `L^2(-a,a)`, and let

```text
e_a(x)=e^x,                         -a<x<a,
k=-g''
```

with functions extended by zero outside the interval when convolved. Suzuki's distributional
kernel decomposition is

```text
k(t)=-(1/2) Pf(1/|t|) -(2A+1) delta_0
     -sum_(n>=2) Lambda(n)/sqrt(n) [delta_(log n)+delta_(-log n)] -r''(t).   (1)
```

Only finitely many prime-power shifts occur after restriction to `(-a,a)`.

For `r>0` with `-r<lambda_a`, put

```text
u_r=(A_a+rI)^(-1)e_a,
U_r(z)=integral_(-a)^a u_r(x)e^(izx) dx,
Theta_r(z)=(z-i)U_r(z)/((z+i)U_r(-z)).                    (2)
```

The far-negative free source is

```text
F_a(z)=integral_(-a)^a e^x e^(izx) dx,
Theta_a^free(z)=(z-i)F_a(z)/((z+i)F_a(-z)).               (3)
```

## 2. Theorem A: exact endpoint action and source non-eigenvector

The vector `e_a` belongs to `Dom(A_a)`. There is a function `R_a` with finite one-sided limits at
both endpoints such that, almost everywhere on `(-a,a)`,

```text
(A_a e_a)(x)=-(1/2)e^x log(a^2-x^2)+R_a(x).              (4)
```

Consequently

```text
(A_a e_a)(x) -> +infinity as x -> a-,                    (5)
```

and similarly at `-a+`. In particular,

```text
A_a e_a is not a scalar multiple of e_a.                 (6)
```

Equation (4), rather than only the negative statement (6), is the positive survivor: endpoint
logarithmic coefficient `-e^x/2` is an exact source invariant. Finite prime shifts and the smooth
archimedean remainder cannot alter it.

### Proof

For a smooth `v` on the closed interval, the finite-part term has the exact pointwise form

```text
Pf integral_(-a)^a v(y)/|x-y| dy
 = integral_(-a)^a (v(y)-v(x))/|x-y| dy
   +v(x)log(a^2-x^2).                                    (7)
```

Apply (7) to `v=e_a`. The divided-difference integral

```text
J_a(x)=integral_(-a)^a (e^y-e^x)/|x-y| dy                (8)
```

has finite one-sided endpoint limits by dominated convergence: the mean-value theorem bounds its
integrand uniformly on the compact square. Every shift in (1) is bounded and has a finite one-sided
endpoint limit because the sum is finite. Since `r''` is continuous, its convolution with `e_a` is
continuous. Substitution into (1) gives (4). Its logarithmic term is in `L^2(-a,a)`, hence the whole
right side is in `L^2`.

For completeness, domain membership does not assume a pointwise formula for a general form-domain
element. The Fourier transform of `e_a` is

```text
F_a(z)=2 sinh(a(1+iz))/(1+iz).                            (9)
```

At every zero `gamma` of `xi(1/2-iz)`, `|Im gamma|<1/2`, so (9) is `O_a((1+|gamma|)^(-1))`.
The Riemann--von Mangoldt zero-counting bound makes Suzuki's defining zero sum for the form
absolutely convergent on `e_a`; thus `e_a` is in the closed form domain. Pairing (1) with the form
core gives the `L^2` vector in (4). The representation theorem for closed lower-bounded forms then
places `e_a` in `Dom(A_a)` and identifies its image with (4). Finally, the logarithm tends to
`-infinity`, while `R_a` has a finite limit, proving (5)--(6).

No RH is used: the only zero-location input is the classical critical-strip bound.

## 3. Theorem B: far-negative source tangent is genuinely nonzero

Set `epsilon=1/r`. Projective cancellation of the scalar `epsilon` reduces (2) to the source

```text
v_epsilon=(I+epsilon A_a)^(-1)e_a.                        (10)
```

Because Theorem A proves `e_a in Dom(A_a)`, the correct strong resolvent expansion is

```text
v_epsilon=e_a-epsilon A_a e_a+o(epsilon) in L^2,          (11)
```

as `epsilon -> 0+`. This is a vector expansion; no false operator-norm expansion of the unbounded
operator is used. Boundedness of the Fourier functionals uniformly on compact `z`-sets gives

```text
U_epsilon(z)=F_a(z)-epsilon H_a(z)+o(epsilon),
H_a(z)=integral_(-a)^a (A_a e_a)(x)e^(izx) dx             (12)
```

locally uniformly. Define the entire cross-tangent numerator

```text
N_a(z)=H_a(z)F_a(-z)-F_a(z)H_a(-z).                       (13)
```

Then

```text
N_a is not identically zero.                              (14)
```

Equivalently, away from zeros of `F_a(z)F_a(-z)`, the meromorphic field

```text
Delta_a(z)=H_a(-z)/F_a(-z)-H_a(z)/F_a(z)                 (15)
```

is nonzero and

```text
d/d epsilon Theta_epsilon(z)|_(0+)=Theta_a^free(z)Delta_a(z).  (16)
```

### Proof

Identity (11) follows exactly from

```text
[(I+epsilon A_a)^(-1)e_a-e_a]/epsilon
 =-(I+epsilon A_a)^(-1)A_a e_a -> -A_a e_a.              (17)
```

Suppose (13) vanished identically. For every nonzero integer `n`, set

```text
z_n=pi n/a+i.                                             (18)
```

Equation (9) gives `F_a(z_n)=0` and `F_a(-z_n) != 0`; hence (13) gives `H_a(z_n)=0`. But

```text
H_a(z_n)=integral_(-a)^a [(A_a e_a)(x)e^(-x)] e^(i pi n x/a) dx.  (19)
```

Thus every nonzero Fourier coefficient of `(A_a e_a)e^(-x)` vanishes. Completeness of the
two-sided Fourier basis forces `(A_a e_a)e^(-x)` to be constant almost everywhere, contradicting
(6). This proves (14); quotient differentiation gives (16).

## 4. Theorem C: no finite admissible shift is the free clock

For every finite admissible `r`,

```text
Theta_r != Theta_a^free                                    (20)
```

as meromorphic functions, hence also as Schur functions on the upper half-plane.

### Proof

Assume equality. The points (18) lie in the upper half-plane and are non-anchor zeros of the free
carrier. The Hermite--Biehler denominator of `Theta_r` is nonzero there, so equality forces
`U_r(z_n)=0` for every `n!=0`. Therefore every nonzero Fourier coefficient of `u_r e^(-x)` vanishes,
and Fourier completeness yields

```text
u_r=c e_a.                                                 (21)
```

The resolvent is injective and `e_a` is nonzero, so `c!=0`. Applying `A_a+rI` to (21) gives

```text
A_a e_a=(c^(-1)-r)e_a,                                    (22)
```

contradicting Theorem A.

## 5. Scientific consequence and remaining frontier

This closes two fixed-aperture gaps left open in prior Suzuki work:

```text
finite admissible shift cannot be exactly universal clock;
far-negative source path has a provably nonzero first projective tangent.  (23)
```

The arithmetic deformation is therefore not an artifact that appears only after a cofinal limit.
Every finite shift already leaves the clock boundary, and departure has an exact first-order
source producer `N_a`.

This does **not** prove a cofinal lower bound for `N_a`, select an RH-bearing schedule, or identify a
limit divisor with Xi. The remaining frontier is now narrower: propagate this proven nonzero
finite-aperture tangent through a cofinal intermediate-shift regime without its scale collapsing.

## 6. Formalization map

Lean module:

```text
formal/GaloisForLFunctions/RHTower/SuzukiFiniteShiftNonClock.lean
```

Formalized, unconditionally:

1. exact free-clock sample zeros `z_n=pi n/a+i`;
2. endpoint logarithmic blow-up modulo every residual with a finite endpoint limit;
3. Hilbert-basis completeness: zero nonconstant modes imply a pure zero mode;
4. vanishing reflected cross-tangent implies source proportionality;
5. nonzero-mode source forces a nonzero cross-tangent somewhere;
6. equality with Suzuki's explicit free carrier at all clock samples forces pure zero mode.

**Theorem A's kernel mechanism `(7)`--`(8)` is now formal**, in

```text
formal/GaloisForLFunctions/HTGeometry/HadamardFinitePart.lean
```

```text
integral_left_inv_sub          ∫_{-a}^{x-ε} dy/(x-y) = log (x+a) - log ε
integral_right_inv_sub         ∫_{x+ε}^{a} dy/(y-x) = log (a-x) - log ε
integral_punctured_inv_dist    their sum is log (a² - x²) - 2 log ε
cutoffFinitePart               the cutoff finite part of the Cauchy kernel against a weight
cutoffDividedDifference        the cutoff divided-difference integral
cutoffFinitePart_eq            (7): finite part = divided difference + v(x) log (a² - x²)
```

`cutoffFinitePart_eq` holds **for every cutoff separately**, with no limit taken, so the
logarithmic coefficient `v(x)` is exhibited as an exact cutoff-independent invariant of the kernel
rather than as the value of a limit.  That is precisely the claim that the endpoint logarithmic
coefficient `-e^x/2` of `(4)` cannot be altered by the finitely many prime shifts or by the smooth
archimedean remainder: each of those contributes a bounded term with finite one-sided endpoint
limits and none of them carries a `log ε`.

**The form itself is now a Lean definition**, in
`formal/GaloisForLFunctions/RHTower/SuzukiRestrictedWeilForm.lean`.  Kernel `(1)` is assembled
block by block — finite part, scalar Dirac, prime translation pairs, smooth remainder — so what
this card writes as `A_a u = w` is `IsRestrictedWeilRepresentative`, a statement about an explicit
integral pairing.  No Friedrichs extension and no spectral theorem is involved:

```text
cauchyFinitePart, weilFinitePartBlock, weilScalarBlock, weilPrimeBlock, weilSmoothBlock
restrictedWeilForm, IsRestrictedWeilRepresentative
restrictedWeilRepresentative, restrictedWeilRepresentative_eq
weilPrimeBlock_eq_jumpForms, weilPrimeBlock_jumpPart_nonneg
```

`restrictedWeilRepresentative_eq` is `(4)`'s split: the representative is
`-(1/2) u(x) log(a²-x²)` plus a remainder made of the divided difference and the three other
blocks.  Suzuki's `r''` is carried as a continuous kernel parameter, because `r` is source data the
corpus does not own; every other block is fully explicit.

**`(5)` and `(6)` are theorems**, in
`formal/GaloisForLFunctions/RHTower/SuzukiBoundaryLogEndpointBlowUp.lean`:

```text
cauchyDividedDifference
cauchyFinitePart_eq_dividedDifference_add
abs_cauchyDividedDifference_le                 |divided difference| ≤ 2 a L for L-Lipschitz u
tendsto_neg_half_cauchyFinitePart_atTop        (5): -(1/2) FP → +∞ at the right endpoint
not_bounded_of_tendsto_neg_half_cauchyFinitePart  (6): hence no bounded representative
```

The mechanism is exactly the card's: the divided difference is *uniformly* bounded by the Lipschitz
constant times the aperture length, so the whole endpoint behaviour sits in `log(a²-x²)`, whose
coefficient `u(x)` tends to `u(a) > 0`.

Concrete construction of Suzuki's unbounded `A_a` as an operator, its form domain, and the
identification of the parameter `r''` with Suzuki's own remainder remain outside the current Lean
source layer; the analytic content of Theorem A is formalized without axioms.

## 7. Hostile audit

1. **Unbounded-operator error removed.** No operator-norm Neumann expansion is asserted. Only the
   strong vector derivative (17), valid because Theorem A proves source-domain membership, is used.
2. **No assumed nonzero tangent.** Nonvanishing follows from Fourier completeness plus exact
   endpoint singularity.
3. **No RH.** Critical-strip location and standard zero counting are unconditional.
4. **No finite-dimensional surrogate.** All integer Fourier modes are used.
5. **No cofinal overclaim.** Fixed-`a` nonvanishing may still decay after `a` varies; that remains
   open.

### Cross-reference — endpoint separation added to this card's module

`RHTower/SuzukiFiniteShiftNonClock.lean` now also carries the endpoint *separation* layer, proved
for the Nonvanishing step of `suzuki-full-frequency-neumann-holonomy-survivor.md`:
`tendsto_sub_mul_suzukiBoundaryLog`, `tendsto_sub_mul_suzukiBoundaryPole`, and
`suzukiBoundaryPole_ne_log_add_bounded` — a logarithmic endpoint singularity cannot absorb a simple
pole, with a variable log coefficient allowed. It sits next to this card's `suzukiBoundaryLogTerm`
layer because it is the same endpoint analysis; look here before rebuilding it elsewhere.

### Cross-reference — the operator blocker now has a resolvent-coordinate route

This card parks on "concrete construction of Suzuki's unbounded `A_a`, form domain, and distribution
kernel".  That blocker is shared with four sibling cards, and on
`suzuki-neumann-dominated-shift-cone-obstruction.md` it has now been dissolved rather than solved:
the statements it was thought to require were restated in the coordinate of the **bounded** resolvent
`B = (A - rho)^{-1}`, where no unbounded operator is ever formed.

Machinery available for reuse here, all unconditional and axiom-clean:

- `RHTower/SuzukiStrongResolventLimit.lean` : `tendsto_resolventFamily_id` — the strong resolvent
  limit `(-lambda)(A - lambda)^{-1} -> I` as a single theorem about a bounded `B`.
- `HTGeometry/CfcNormBound.lean` : CFC norm bounds and the resolvent symbol estimates that drive it.
- `HTGeometry/StrongConvergenceDense.lean`, `HTGeometry/CompactOperatorDiscreteSpectrum.lean` :
  the `eps/3` strong-convergence bridge, dense range of an injective self-adjoint operator, and the
  discrete nonzero spectrum of a compact symmetric operator.
- `HTGeometry/SignedCharFunCentralJet.lean` : endpoint atoms from integration by parts
  (`neg_integral_exp_mul_deriv`, `neg_integral_expNeg_mul_deriv`), their coefficient sum
  `2 cosh a`, and the interior cancellation `exponentialSourceCombination_pairing`.

The endpoint-atom layer is directly relevant to this card's `(P11)`-style boundary analysis, and
sits in the same module as this card's own log-versus-pole separation.  Before treating the operator
as a prerequisite here, check whether the statement can be phrased in the resolvent coordinate.

### `(P1)` in the resolvent coordinate — what it actually needs

Restating `(P1)` as the cross-reference above recommends, with `A = rho + B^{-1}` for the bounded
resolvent `B`:

```text
I + eps A = B^{-1} (eps I + (1 + eps rho) B),
(I + eps A)^{-1} = (eps I + (1 + eps rho) B)^{-1} B,
```

whose symbol at a spectral point `x` of `B` is `x / (eps + (1 + eps rho) x)`.  As `eps -> 0` this
tends to `1` for every `x > 0` but **not** at `x = 0` — the same pointwise-not-uniform structure as
`(2)`, so `(I + eps A)^{-1} -> I` is again a *strong* limit and is reachable by
`tendsto_id_of_norm_comp_tendsto_zero` with the estimates in `HTGeometry/CfcNormBound.lean`.

Two consequences worth recording before anyone builds machinery for this:

- The **bounded-operator skeleton of `(P1)` is already in mathlib**: `NormedRing.inverse_add`,
  `NormedRing.inverse_add_norm_diff_nth_order` in `Mathlib/Analysis/Normed/Ring/Units.lean` give the
  first-order expansion of `inverse (x + t)` with its remainder bound.  Nothing needs to be written
  for that half.
- The genuinely card-specific input is `A_a e^x`, i.e. `B^{-1} e^x`, which presupposes
  `e^x ∈ range B` — the statement that the exponential lies in the operator's domain.  That is a
  hypothesis about Suzuki's operator, not an analytic gap, and it is the only part of `(P1)` that
  the resolvent coordinate does not remove.

### Lean progress — `(P1)`'s symbol estimate FORMALIZED

The estimate the resolvent-coordinate route needs for `(P1)`, in
`HTGeometry/CfcNormBound.lean` [PROVED HERE], standard axioms
`[propext, Classical.choice, Quot.sound]`, builds clean:

- `abs_neumannSymbol_le` : for `A = rho + B⁻¹`, the family `(I + eps A)⁻¹` has symbol
  `x / (eps + (1 + eps rho) x)` in the coordinate of `B`, and its estimate symbol
  `-eps x (1 + rho x) / (eps + (1 + eps rho) x)` is bounded by `2 eps (1 + |rho| M)` on `[0, M]`,
  whenever `1 + eps rho >= 1/2`.

The uniformity has the same source as in `(2)`: `x / (eps + (1 + eps rho) x) <= 1 / (1 + eps rho)`
holds for **every** `x >= 0`, the accumulation point included, because cross-multiplying leaves only
`0 <= eps`. So `(I + eps A)⁻¹ -> I` strongly follows from `tendsto_id_of_norm_comp_tendsto_zero` by
the same chain that closed `(2)`, with this estimate in place of `abs_resolventSymbol_le`.

`(P1)`'s remaining content is then its **first-order term** `A_a e^x = B⁻¹ e^x`, which needs
`e^x ∈ range B`; the bounded-operator expansion itself is mathlib's `NormedRing.inverse_add`.

### Lean progress — `(P1)`'s scalar layer is complete

- `eventually_forall_abs_neumannSymbol_le` : as `eps -> 0+`, the Neumann-shift estimate symbols are
  uniformly small on `[0, M]` — the direct input of `tendsto_norm_cfc_zero`.
  [PROVED HERE], standard axioms `[propext, Classical.choice, Quot.sound]`, builds clean.

With `abs_neumannSymbol_le` this completes the scalar layer for `(I + eps A)^{-1} -> I` strongly,
exactly mirroring what closed `(2)` on the sibling card: uniform bound, estimate symbol, uniform
smallness, then `tendsto_norm_cfc_zero` and `tendsto_id_of_norm_comp_tendsto_zero`. The bundling
into one theorem is the same CFC bookkeeping already carried out in
`RHTower/SuzukiStrongResolventLimit.lean`, and would go in an RHTower module for the same
instance reason recorded there.

`(P1)`'s first-order term `A_a e^x = B^{-1} e^x` remains, needing `e^x ∈ range B`.

### Lean progress — `(P1)`'s link identity; the scalar layer is closed

- `neumannSymbol_sub_one_mul` : `(x/(eps + (1+eps rho)x) - 1) * x
  = -(eps (x(1+rho x))/(eps + (1+eps rho)x))` — the `x` terms cancel, leaving an `eps`-only
  numerator. [PROVED HERE], standard axioms `[propext, Classical.choice, Quot.sound]`, builds clean.

All three scalar inputs for `(I + eps A)^{-1} -> I` strongly now exist — uniform bound
(`abs_neumannSymbol_le`), link identity, and uniform smallness
(`eventually_forall_abs_neumannSymbol_le`) — matching one-for-one the inputs that closed `(2)`.
Bundling is the CFC bookkeeping of `RHTower/SuzukiStrongResolventLimit.lean`.

Note for whoever writes that bundle: `field_simp` does **not** close this identity — it normalises
the denominator to a different associativity than the hypothesis and leaves an inverse-form goal
`ring` cannot finish. The working route is `div_sub_one`, then `div_mul_eq_mul_div`, then rewriting
the numerator by hand.

### Lean progress — `(P1)`'s strong limit IS NOW ONE THEOREM

- `abs_neumannFamilySymbol_le` : the shift symbol is bounded by `2` on `[0, M]` when
  `1 + eps rho >= 1/2`, uniformly in `x` and `eps`.
- `tendsto_neumannShiftFamily_id`, in `RHTower/SuzukiStrongResolventLimit.lean` :
  **`(I + eps A)^{-1} -> I` strongly as `eps -> 0+`**, for `A = rho + B^{-1}` with `B` bounded,
  injective and self-adjoint with spectrum in `[0, M]`.

Both [PROVED HERE], standard axioms `[propext, Classical.choice, Quot.sound]`, build clean.

`(P1)`'s convergence half is therefore closed, by the same chain that closed `(2)` on
`suzuki-neumann-dominated-shift-cone-obstruction.md` and with no unbounded operator formed. The
assembly compiled on the first attempt: only the scalar estimates differ between the two families,
so the bridge is genuinely reusable rather than a one-off.

What remains of `(P1)` is its **first-order term** `A_a e^x = B^{-1} e^x`, which needs
`e^x ∈ range B` — a domain hypothesis about Suzuki's operator, not analysis. The bounded-operator
expansion behind it is mathlib's `NormedRing.inverse_add`.
