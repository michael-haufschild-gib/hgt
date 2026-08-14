# Theta Wiener--Hopf transgression and the Hedenmalm bulk--boundary polarity

- **ID:** `prime-tail-hedenmalm-wiener-hopf-transgression`
- **Stage:** 3-formalized
- **Type:** THEOREM / OPEN-CORE REDUCTION
- **Scientific status:** `[PROVED HERE] [NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Parents:**
  - `hedenmalm-reflection-folded-dirac-source-defect.md`;
  - `critical-half-density-prime-tail-resolvent-law.md`;
  - `prime-tail-reflection-folded-second-order-resolvent.md`.

## Question

Is the map from the prime-tail half-line chart to Hedenmalm's theta eigenfunctions itself
missing, or is the obstruction more specifically the Hilbert boundary on which that map must
land?

## Setup

Use logarithmic theta coordinates

```text
k(x)=2 VarTheta_00(i exp(2x)),
D_x=-i partial_x,
XiC(alpha)=integral_R exp(i alpha x) k(x) dx.
```

The function `k` is real, even, Schwartz, and in `L^1(R)`.  For
`f in L^2(R_+)`, extend `f` by zero to the negative half-line and define

```text
(T_- f)(x)=integral_0^infinity k(x-L) f(L) dL,
(T_+ f)(x)=integral_0^infinity k(x+L) f(L) dL,           (1)

C f=(T_- f+T_+ f)/2,
S f=(T_- f-T_+ f)/2.                                    (2)
```

These operators are defined from the theta source before any zero is chosen.

## Theorem 1: bounded source transgression

The maps

```text
T_-,T_+,C,S : L^2(R_+) -> L^2(R)
```

are bounded, with

```text
||T_-||,||T_+|| <= ||k||_1,
T_+ f(x)=T_- f(-x).                                     (3)
```

Consequently `Cf` is even and `Sf` is odd.

### Proof

After zero extension, `T_- f=k*f`.  Young's convolution inequality gives the first bound.
Evenness of `k` gives

```text
T_- f(-x)=integral_0^infinity k(-x-L)f(L)dL
         =integral_0^infinity k(x+L)f(L)dL=T_+f(x).
```

The remaining assertions follow from `(2)`. QED.

## Theorem 2: exact boundary defect

For smooth decaying `f` on the half-line,

```text
partial_x C f=S(f'),
partial_x S f=k f(0)+C(f').                             (4)
```

Equivalently,

```text
D_x C f=-i S(f'),
D_x S f=-i k f(0)-i C(f').                              (5)
```

Thus the rank-one theta defect in the folded Hedenmalm system is exactly the endpoint trace of
an ordinary half-line derivative.  It is not an ad hoc forcing term.

### Proof

Integration by parts in `L` gives

```text
partial_x T_-f = k f(0)+T_-(f'),
partial_x T_+f =-k f(0)-T_+(f').                        (6)
```

Adding and subtracting `(6)` proves `(4)`, and multiplication by `-i` proves `(5)`. QED.

## Theorem 3: zero specialization is exactly Hedenmalm's fold

Let `rho` be a nontrivial Xi zero and set

```text
lambda=rho-1/2,
alpha=-i lambda,
```

so `lambda=i alpha` and `XiC(alpha)=0`.  First assume `Re lambda>0`, and put

```text
f_lambda(L)=exp(-lambda L).                              (7)
```

Then `f_lambda in L^2(R_+)`, and

```text
T_- f_lambda(x)
 =exp(-lambda x) integral_-infinity^x exp(lambda y)k(y)dy
 =u_alpha(x).                                           (8)
```

Since `k` and `XiC` are even and `XiC(-alpha)=0`,

```text
T_+ f_lambda=-u_(-alpha).                               (9)
```

Therefore

```text
C f_lambda=E_alpha,
S f_lambda=O_alpha,                                     (10)
```

where

```text
E_alpha=(u_alpha-u_(-alpha))/2,
O_alpha=(u_alpha+u_(-alpha))/2
```

are the even and odd Hedenmalm reflection folds.  Substitution of
`f_lambda'=-lambda f_lambda` into `(5)` gives exactly

```text
D_x E_alpha=-alpha O_alpha,
D_x O_alpha=-alpha E_alpha-i k,                         (11)

(D_x^2-alpha^2)E_alpha= i alpha k,
(D_x^2-alpha^2)O_alpha=-i D_x k.                        (12)
```

### Proof

Changing variables `y=x-L` in `(1)` proves `(8)`.  Changing variables `y=x+L` gives

```text
T_+f_lambda(x)
 =exp(lambda x) integral_x^infinity exp(-lambda y)k(y)dy.
```

The vanishing of the full integral

```text
integral_R exp(-lambda y)k(y)dy=XiC(-alpha)=0
```

turns the last expression into `-u_(-alpha)(x)`, proving `(9)` and `(10)`.
Equations `(11)` and `(12)` follow from `(5)` and `lambda=i alpha`. QED.

## Theorem 4: exact `L^2`/boundary wall

For the canonical input `(7)`,

```text
||f_lambda||_2^2=1/(2 Re lambda)                        (13)
```

when `Re lambda>0`.  More completely,

```text
Re rho>1/2  iff f_lambda is in L^2(R_+),
Re rho=1/2  iff f_lambda is bounded oscillatory and tempered but not in L^2,
Re rho<1/2  implies f_lambda has exponential growth and is not tempered.  (14)
```

The first alternative is intrinsic.  There is no `g in L^2(R_+)` with
`T_-g=u_alpha` when `alpha` is real and `XiC(alpha)=0`.

### Proof

Equation `(13)` is the elementary integral of `exp(-2 Re(lambda)L)`, and `(14)` follows
immediately.

For the last assertion, take Fourier transforms in `(8)`.  The zero extension of the
oscillation `exp(-i alpha L)` has boundary transform with a nonzero principal part proportional
to `(z-alpha)^{-1}`.  If `T_-g=u_alpha`, then away from the discrete real zero set of `XiC`,

```text
hat g(z)=1/(boundary constant times (z-alpha)).
```

This is not locally square-integrable at `z=alpha`, contradicting Plancherel.  Equivalently,
`T_-` is injective on `L^2(R_+)`: its full-line Fourier multiplier is `XiC`, which is nonzero
almost everywhere because it is a nonzero entire function.  The cancelled boundary pole cannot
be replaced by an `L^2` preimage. QED.

## Corollary: the positive self-adjoint consumer is elementary

Let

```text
A_N=-partial_L^2,  Dom(A_N)={f in H^2(R_+):f'(0)=0},
A_D=-partial_L^2,  Dom(A_D)={f in H^2(R_+):f(0)=0}.      (15)
```

Both are nonnegative self-adjoint operators.  The source-normalized functions

```text
c_lambda(L)=cosh(lambda L),
s_lambda(L)=sinh(lambda L)/lambda                       (16)
```

with `s_0(L)=L` satisfy

```text
A_N c_lambda=-lambda^2 c_lambda,   c_lambda(0)=1, c_lambda'(0)=0,
A_D s_lambda=-lambda^2 s_lambda,   s_lambda(0)=0, s_lambda'(0)=1. (17)
```

These are exactly the Neumann and Dirichlet shapes of the prime-tail reflected monodromy
theorem.  They are tempered generalized eigenfunctions of the fixed positive self-adjoint
operator `A_N direct_sum A_D` exactly when `Re lambda=0`; for `Re lambda != 0`, both have an
exponentially growing component.

Thus no new formal differential operator is required.  What Hedenmalm's proposal lacks is a
source theorem placing every Xi conormal nontrivially in the tempered spectral boundary of this
fixed operator.

## What the calculation means

The regular theta transgression `(1)` exists and exactly recovers Hedenmalm's reflected modes.
It has the wrong Hilbert polarity:

```text
hypothetical right off-line zero -> honest L^2 bulk input,
critical-line zero               -> non-L^2 threshold boundary input,
hypothetical left off-line zero  -> reflected exponentially growing input. (18)
```

Ordinary `L^2` completion therefore cannot prove RH.  It regularizes the wrong side of the
divisor and excludes the critical carrier.  This explains, in one calculation, why:

1. ordinary theta-translate quotients collapse by Wiener cyclicity;
2. finite-Rees maps cannot recover the all-orders-flat theta conormal;
3. infinite rank without a singular trace does not help;
4. Hedenmalm's forced resolvent equation survives while a genuine eigenvector does not;
5. the prime-tail chart sees homogeneous monodromy, while the theta chart sees a flat forced
   response.

They are bulk and boundary presentations of one endpoint-trace exact sequence.

## Revised open core

`[OPEN CORE: THETA_TRANSGRESSION_BOUNDARY_COHOMOLOGY_INJECTIVITY]`

Construct, from the ordinary-integer Euler--Poisson--Gamma source before choosing any zero, a
Hausdorff boundary cohomology `H_boundary` and a closed comparison map

```text
prime-tail monodromy
    -> tempered spectral dual of A_N direct_sum A_D
    -> H_boundary
    -> Hedenmalm theta fold,                              (19)
```

such that:

1. regular `L^2` bulk primitives are exact and vanish in `H_boundary`;
2. every Xi multiplicity conormal maps to a nonzero class;
3. source reflection becomes Hilbert adjunction;
4. the comparison commutes with the nonreal resolvents of `(15)`;
5. no divisor point or zero-dependent normalization occurs in the construction.

If `(19)` exists, each nontrivial Xi zero supplies a nonzero tempered generalized eigenmode of
`A_N direct_sum A_D`.  By `(17)`, its parameter must satisfy

```text
-lambda^2 in [0,infinity),
```

and the open critical strip excludes nonzero real `lambda`.  Hence `lambda` is purely imaginary
and `Re rho=1/2`.

This implication is short, but condition 2 is the RH-bearing theorem.  Calling it
“self-adjointness,” “purity,” “same-fibre dagger,” or “positive realization” does not prove it.
The gain here is narrower and concrete: the regular transgression and positive consumer are now
explicit, leaving only the singular boundary-cohomology lift and its source-side injectivity.

## Hostile audit

1. This does **not** construct `(19)` and does not prove RH.
2. Boundedness of `(1)` does not transport Hedenmalm modes to eigenvectors of `(15)`.  For
   `Re rho>1/2`, it transports a resolvent/bulk vector, which is precisely the wrong conclusion.
3. The Neumann/Dirichlet Laplacians are classical.  Novelty, if any, lies only in the exact
   source-chart comparison and the resulting reversal of the previously stated open core.
4. The Fourier division in Theorem 4 proves that the threshold input cannot secretly be replaced
   by an `L^2` input; it does not prove that the threshold class survives a new completion.
5. A completion defined by declaring the Xi conormals nonzero is target-fed.  Nonannihilation
   must follow from ordinary-prime incidence, Poisson summation, and the Gamma endpoint.
6. A space containing exponentially growing functions would destroy the tempered spectral
   argument.  Mere distributional solvability is insufficient.

## Literature audit

Targeted searches against Hedenmalm's paper, Wiener--Hopf/Volterra terminology, theta
convolution, and half-line self-adjoint realizations found no statement of Theorems 1--4 as the
prime-tail/Hedenmalm chart comparison.  Hedenmalm constructs the theta boundary pencil and asks
for a positive self-adjoint form; he does not make the half-line transgression `(1)` or identify
the `L^2` polarity `(18)`.

Classical credit remains classical:

- Young's convolution inequality;
- Wiener multiplier injectivity;
- half-line Neumann/Dirichlet self-adjoint Laplacians;
- limiting-absorption generalized eigenfunctions.

No external novelty is claimed until a broader operator-theory and analytic-number-theory audit
is complete.

## Lean status

The zero-specialized folded equations `(11)`--`(12)`, parity, and first-conormal
nonannihilation are already formalized in
`formal/GaloisForLFunctions/RHTower/XiHedenmalmReflectionFoldedDirac.lean`.

The new half-line convolution, trace-intertwining, and `L^2` wall are paper-level.  They should
be formalized only as the literal Bochner/Lebesgue integral theorem above; an abstract
“transgression” structure would erase the endpoint trace and would be theatre.

## 2026-08-01 essential-boundary refinement

`hedenmalm-theta-flat-borel-holonomy-law.md` now constructs the literal essential chart of the
flat theta tail.  After `y=x+log(1+t)/2`, every Hedenmalm tail factors through the universal
multiplier

```text
M_alpha(t)=(1+t)^(i alpha/2)=exp(i alpha Q),
Q=log(1+t)/2.
```

`Q` is a fixed positive self-adjoint multiplication generator.  Functional reflection sends
`M_alpha` to its inverse, while Hilbert adjunction sends it to `M_(-conjugate alpha)`.  These agree
exactly for real `alpha`.  Hence positive boundary generator and regular transgression are both
explicit; remaining theorem is common-domain nonannihilation of every source conormal for both
reflected multipliers.  Declaring that domain membership would still be RH, so it remains open.

## 2026-08-09 — the convolution norm inequality Theorem 1 needs

Theorem 1 asserts `‖T_-‖, ‖T_+‖ ≤ ‖k‖₁` as operators `L²(ℝ₊) → L²(ℝ)`, which after zero extension
is Young's convolution inequality `L¹ ⋆ L² → L²`.  An exact search shows **no convolution norm
inequality exists in mathlib** (`Mathlib/Analysis/Convolution.lean` and
`Mathlib/Analysis/LConvolution.lean` carry no `eLpNorm_convolution_le` and no Young statement) and
none in this tree; Minkowski's integral inequality is likewise absent.

`formal/GaloisForLFunctions/HTGeometry/YoungConvolutionL2.lean` supplies it by the route that
avoids Minkowski entirely:

- `lintegral_weighted_sq_le` — Cauchy--Schwarz against the weight `K dy` in `ℝ≥0∞`:
  `(∫ K·G)² ≤ (∫K)·(∫ K·G²)`;
- **`lintegral_convolution_sq_le`** — Tonelli on `∫∫ K(y)·F(x−y)²` plus translation invariance of
  Lebesgue measure, giving `∫ (∫ K(y)F(x−y) dy)² dx ≤ (∫K)²·∫F²`.

Everything is stated in `ℝ≥0∞`, so no integrability hypothesis appears anywhere; the `L²` operator
bound of Theorem 1 is the specialization to `K = ‖k‖₊`, `F = ‖f‖₊`.

## 2026-08-14 — Theorems 1, 2 and the `L²` norm of (13) are formalized

`formal/GaloisForLFunctions/RHTower/ThetaWienerHopfTransgression.lean`, unconditional and
axiom-clean, wired into the `RHTower` umbrella:

**Theorem 1.**  `halfLineConvMinus`, `halfLineConvPlus`, `halfLineConvEven`, `halfLineConvOdd` are
the literal Bochner integrals `T₋`, `T₊`, `C`, `S` of `(1)`–`(2)`.
`halfLineConvPlus_eq_halfLineConvMinus_neg` is `(3)` for an even kernel, whence
`halfLineConvEven_neg` (`C f` even) and `halfLineConvOdd_neg` (`S f` odd).
`lintegral_enorm_sq_halfLineConvMinus_le` and `lintegral_enorm_sq_halfLineConvPlus_le` are the
`L¹ ⋆ L² → L²` bound `‖T∓ f‖₂ ≤ ‖k‖₁‖f‖₂`, obtained from the zero extension
(`zeroExtend`, `halfLineConvMinus_eq_lineConv`) and the corpus's own Young inequality
`HTGeometry.lintegral_enorm_sq_le_of_convolution_bound`.

**Theorem 2.**  `halfLineConvMinus_deriv` and `halfLineConvPlus_deriv` are half-line integration by
parts: `T₋(f') = -k(x)f(0) + T₋^{k'}(f)` and `T₊(f') = -k(x)f(0) - T₊^{k'}(f)`.  Differentiating the
kernel is therefore the same operator with kernel `k'`, and the two endpoint traces cancel in the
even half and add in the odd half:

- `halfLineConvEven_kernelDeriv` — equation `(4)` first identity, `∂_x C f = S(f')`;
- `halfLineConvOdd_kernelDeriv` — equation `(4)` second identity, `∂_x S f = k·f(0) + C(f')`.

This is the card's assertion that the rank-one theta defect is exactly an endpoint trace of an
ordinary half-line derivative, now literal.

**Theorem 4, equation (13).**  `canonicalHalfLineInput lam L = exp (-λL)` of `(7)`, with
`norm_canonicalHalfLineInput` and `integral_norm_sq_canonicalHalfLineInput`:
`∫_0^∞ |f_λ|² = 1/(2 re λ)` whenever `re λ > 0` — the exact `L²` wall of `(14)`, whose finiteness
is precisely the half `re ρ > 1/2`.

(Superseded by the 2026-08-14 entry below: Theorem 3 and the Corollary are now formalized too.)

## 2026-08-14 — Theorem 3, equations `(11)`–`(14)`, and the Corollary are formalized

All in `formal/GaloisForLFunctions/RHTower/ThetaWienerHopfTransgression.lean`, unconditional and
axiom-clean.

**Theorem 3.**  `foldPrimitive lam k x = exp(−λx)·∫_{−∞}^{x} exp(λy)k(y)dy` is the physical fold
primitive `u_α`.

- `halfLineConvMinus_canonicalHalfLineInput` — equation `(8)`: `T₋f_λ = u_α`.  Proved by the
  translation invariance of Lebesgue measure, with **no** integrability hypothesis: the change of
  variables `y = x − L` and the indicator rewriting are unconditional.
- `halfLineConvPlus_canonicalHalfLineInput_eq` — `T₊f_λ(x) = exp(λx)·∫_x^∞ exp(−λy)k(y)dy`, again
  unconditional;
- `halfLineConvPlus_canonicalHalfLineInput` — equation `(9)`: once the reflected theta transform
  `∫_ℝ exp(−λy)k(y)dy` vanishes, `T₊f_λ = −u_{−α}`;
- `halfLineConvEven_canonicalHalfLineInput`, `halfLineConvOdd_canonicalHalfLineInput` — equation
  `(10)`: `C f_λ = (u_α − u_{−α})/2 = E_α` and `S f_λ = (u_α + u_{−α})/2 = O_α`.

**Equations `(11)` and `(12)`.**  `hasDerivAt_canonicalHalfLineInput` (`f_λ' = −λ f_λ`) plus the
Theorem-2 identities give the first-order system
`C^{k'}f_λ = −λ·S^k f_λ` and `S^{k'}f_λ = k − λ·C^k f_λ`
(`halfLineConvEven_kernelDeriv_canonical`, `halfLineConvOdd_kernelDeriv_canonical`), and iterating
once gives the forced second-order system `(12)`:
`C^{k''}f_λ = λ²·C^k f_λ − λ·k` and `S^{k''}f_λ = λ²·S^k f_λ + k'`
(`halfLineConvEven_kernelSecondDeriv`, `halfLineConvOdd_kernelSecondDeriv`).  The admissibility
hypotheses are packaged as `KernelPairAdmissible`.

**Equation `(14)`, the trichotomy.**  `integrableOn_norm_sq_canonicalHalfLineInput` (`Re λ > 0` ⟹
`f_λ ∈ L²`), `not_integrableOn_norm_sq_canonicalHalfLineInput` (`Re λ ≤ 0` ⟹ not in `L²`, because
`|f_λ| ≥ 1` on a half-line of infinite measure), `norm_canonicalHalfLineInput_eq_one` (`Re λ = 0` ⟹
bounded oscillatory) and `tendsto_norm_canonicalHalfLineInput_atTop` (`Re λ < 0` ⟹ exponential
growth).  This is the exact `L²` wall of the card.

**The Corollary.**  `neumannShape lam L = cosh(λL)` and `dirichletShape lam L = sinh(λL)/λ` (with
`s₀(L) = L`) are formalized with their derivatives: `hasDerivAt_neumannShape`,
`hasDerivAt_neumannShapeDeriv` (second derivative `= λ²·c_λ`), `hasDerivAt_dirichletShape`
(`s_λ' = c_λ`), `dirichletShape_secondDeriv`, and the boundary data `c_λ(0)=1`, `c_λ'(0)=0`,
`s_λ(0)=0`, `s_λ'(0)=1` — this is equation `(17)`.  The temperedness dichotomy is
`norm_neumannShape_le_one` (`Re λ = 0` ⟹ `|c_λ| ≤ 1`, via `cosh(ibL) = cos(bL)`) and
`tendsto_norm_neumannShape_atTop` (`Re λ > 0` ⟹ `|c_λ| → ∞`).

**Remaining.**  Two items, both requiring analytic layers absent from mathlib:

1. the last assertion of Theorem 4 — no `g ∈ L²(ℝ₊)` has `T₋g = u_α` for real `α` with
   `XiC(α)=0`.  The proof is the `L¹ ⋆ L² → L²` Fourier multiplier identity `𝓕(k⋆g) = 𝓕k·𝓕g`
   (mathlib has the `L¹ ⋆ L¹` case and the `L²` Plancherel isometry, but not the mixed case) plus
   "the real zero set of a nonzero entire function is null";
2. the self-adjointness of `A_N ⊕ A_D` in `(15)`, which needs half-line Sobolev spaces.

Neither is used by the card's conclusions: `(18)` and the `Revised open core` depend only on the
formalized `(13)`, `(14)` and `(17)`.

### First half of the remaining Fourier input

`formal/GaloisForLFunctions/HTGeometry/EntireZeroSetNull.lean`, unconditional and axiom-clean:

- `HTGeometry.discreteTopology_setOf_eq_zero` — the zero set of an entire function that is not
  identically zero carries the discrete topology (isolated zeros plus the identity theorem);
- `HTGeometry.countable_setOf_eq_zero_of_analyticOnNhd` — hence it is countable, since every subset
  of a second-countable space is Lindelöf and a discrete Lindelöf set is countable;
- `HTGeometry.volume_real_setOf_eq_zero_eq_zero` — hence the **real** zero set of a nonzero entire
  function is Lebesgue-null.

Applied to `XiC` this is exactly the "nonzero almost everywhere" step of the Theorem 4 injectivity
argument.  What still has to be built is the mixed Fourier multiplier identity `𝓕(k⋆g) = 𝓕k·𝓕g`
for `k ∈ L¹`, `g ∈ L²`: mathlib has the `L¹ ⋆ L¹` case (`Real.fourier_mul_convolution_eq`) and the
`L²` Plancherel isometry (`fourierTransformₗᵢ`), and the mixed case follows from Schwartz density
plus the Young bound already proved here — but that transfer is not yet written.

### The multiplier injectivity of `T₋` is formalized

Two new modules, unconditional and axiom-clean, umbrella-wired:

`formal/GaloisForLFunctions/HTGeometry/FourierUniquenessL1.lean` —
**`HTGeometry.ae_eq_zero_of_fourierIntegral_eq_zero`**: an integrable function whose Fourier
transform vanishes identically is almost everywhere zero.  mathlib has inversion only at continuity
points, so the proof mollifies: convolving with a normalized `ContDiffBump` gives a continuous
integrable function whose transform is the product of the two transforms — hence zero — so inversion
makes the convolution itself vanish, and the bump family converges to the identity almost everywhere
on locally integrable functions.  `ae_eq_of_fourierIntegral_eq` is the two-function form.

`formal/GaloisForLFunctions/RHTower/ThetaWienerHopfInjectivity.lean` —

- `halfLineConvMinus_eq_convolution`: on a datum vanishing left of the origin the retarded
  transgression *is* the ordinary convolution `k ⋆ g`;
- **`eq_zero_of_halfLineConvMinus_eq_zero`**: if `𝓕k ≠ 0` almost everywhere then `T₋` kills no
  nonzero integrable half-line datum — the full-line Fourier multiplier argument of the card;
- **`eq_zero_of_halfLineConvMinus_eq_zero_of_entire`**: the form the card actually uses — it is
  enough that the kernel symbol be the restriction to the real axis of an entire function that is
  not identically zero, which is exactly the situation of `XiC`.  The null-set input is
  `HTGeometry.volume_real_setOf_eq_zero_eq_zero`.

What remains of Theorem 4 is only the passage from integrable half-line data to `L²(ℝ₊)`, i.e. the
`L¹ ⋆ L² → L²` multiplier identity; mathlib supplies the `L²` Plancherel isometry
(`fourierTransformₗᵢ`) and the `L¹ ⋆ L¹` product rule, and the transfer is by truncation.

### The `L²` wall is closed, and the card moves to stage 3

`formal/GaloisForLFunctions/RHTower/ThetaWienerHopfL2Injectivity.lean`, unconditional and
axiom-clean.  The passage from integrable to square-integrable data does **not** need the `L²`
Fourier transform at all: an exponential weight moves the whole problem back into `L¹`.

- `expWeight`, `halfLineConvMinus_weighted` — weighting the kernel by `e^{-εt}` and the datum by
  `e^{-εL}` multiplies the transgression by the nonvanishing scalar `e^{-εx}`, so the equation is
  preserved;
- `integrable_expWeight_of_memLp_two` — Hölder makes `g·e^{-εL}` integrable for every
  `g ∈ L²(ℝ₊)`; `integrable_expWeight_of_bounded` does the same for a bounded datum;
- `eq_zero_of_halfLineConvMinus_eq_zero_memLp_two` and its entire-symbol form — **injectivity of
  `T₋` on `L²(ℝ₊)`**, for any kernel with a one-sided exponential margin, which the theta kernel
  has;
- `eq_of_halfLineConvMinus_eq`, `eq_of_halfLineConvMinus_eq_weighted` — the transgression separates
  half-line data outright;
- **`not_exists_memLp_two_of_halfLineConvMinus_eq_canonical`** — the card's assertion verbatim: on
  the critical line (`Re λ = 0`) no square-integrable half-line datum has the same transgression as
  the canonical input, because the canonical input is the *unique* datum with that transgression
  and `(14)` says it is not square-integrable.

`integral_neg_secondDeriv_mul_conj` is Green's identity on the half line: for a compactly supported
`C²` datum obeying either boundary condition of `(15)`, the quadratic form of `−∂_L²` equals the
Dirichlet energy — the nonnegativity and symmetry asserted there.  Essential self-adjointness on
`H²(ℝ₊)` is the one clause still quoted rather than proved; it is textbook operator theory and needs
half-line Sobolev spaces, which mathlib does not have, and nothing in the card's conclusions uses
more than the form nonnegativity proved here.

Theorems 1–4 and the Corollary are therefore formalized; the card moves to stage 3.  The
`Revised open core` is RH-equivalent and remains open, as stated there.
