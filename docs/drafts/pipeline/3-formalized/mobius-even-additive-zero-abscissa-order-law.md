# Möbius even-additive zero-abscissa order law

- **ID:** `mobius-even-additive-zero-abscissa-order-law`
- **Stage:** 3-formalized / needs-priority-review
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [LEAN-FORMALIZED UNCONDITIONALLY: (E3),(E4),(E5a),(E8),(E10),(E16)]` `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT AN RH PROOF]`
- **Source:** Möbius--Laplace continuation wall / Mertens additive-convolution hierarchy
- **Statement:** Every even additive-convolution order of the Mertens function has a one-sided
  growth exponent equal to an affine function of the rightmost zeta-zero abscissa.

## Goal

Replace a list of isolated quadratic and quartic RH criteria by one exact nonlinear spectral law.
The theorem identifies the full rightmost-zero frontier, not only the RH value, using finite
additive arithmetic and only the positive excursions of an even Mertens convolution.

Let

```text
M(0)=0,
M(N)=sum_(1<=n<=N) mu(n),
Theta=sup{Re(rho): zeta(rho)=0, 0<Re(rho)<1}.
```

For every integer `k>=1`, define the `2k`-fold additive Mertens convolution

```text
C_k(N)=sum_(n_1+...+n_(2k)=N) product_(j=1)^(2k) M(n_j).       (E1)
```

Put `C_k(N)^+=max(C_k(N),0)` and define its one-sided order

```text
Lambda_k = limsup_(N->infinity)
  log(1+C_k(N)^+) / log(N+1).                                  (E2)
```

Then

```text
Lambda_k = 2k(1+Theta)-1.                                      (E3)
```

In particular, for every fixed `k>=1`,

```text
RH  <->  Lambda_k=3k-1.                                        (E4)
```

Equivalently, RH holds iff, for one (hence every) `k>=1` and every `epsilon>0`,

```text
C_k(N) <= C_(k,epsilon) (N+1)^(3k-1+epsilon)                   (E5)
```

for all `N`.  No lower bound and no absolute-value bound occurs in `(E5)`.

Unconditionally, `Theta>=1/2`, so `(E3)` also gives the positive-side omega law

```text
C_k(N)=Omega_+(N^(3k-1-epsilon))                              (E5a)
```

for every `epsilon>0`: infinitely many `N` satisfy
`C_k(N)>=N^(3k-1-epsilon)`.  At `k=1`, the second-Cesaro reflected Mertens
self-convolution has unconditional near-quadratic positive excursions.  This is stronger than an
absolute-value omega statement and does not assume RH.

## Exact Abel law

For `0<z<1`, write

```text
A(z)=sum_(n>=1) mu(n)z^n,
B(z)=sum_(N>=0) M(N)z^N=A(z)/(1-z).
```

The coefficient of `z^N` in `B(z)^(2k)` is exactly `C_k(N)`.  Absolute convergence inside the
unit disc gives

```text
A(z)^(2k)=(1-z)^(2k) sum_(N>=0) C_k(N)z^N.                     (E6)
```

For real `z`, the left side is nonnegative.  Consequently

```text
|A(z)|^(2k)
 <= (1-z)^(2k) sum_(N>=0) C_k(N)^+ z^N.                       (E7)
```

This positive-part reduction is the key point: arbitrarily large negative convolution values do
not enter the spectral order.

## Proof of the upper inequality

The classical Littlewood zero-abscissa theorem gives, for every `eta>0`,

```text
|M(N)| <= A_eta (N+1)^(Theta+eta).                             (E8)
```

There are at most `(N+1)^(2k-1)` weak compositions of `N` into `2k` coordinates.  Every coordinate
is at most `N`; hence `(E1)` and `(E8)` give

```text
|C_k(N)|
 <= A_eta^(2k) (N+1)^(2k(Theta+eta)+2k-1).                    (E9)
```

Letting `eta` tend to zero proves

```text
Lambda_k <= 2k(1+Theta)-1.                                    (E10)
```

## Proof of the lower inequality

Assume, to the contrary, that

```text
Lambda_k < lambda < 2k(1+Theta)-1.                            (E11)
```

The limsup definition and absorption of finitely many initial terms give a constant `C_lambda`
such that

```text
C_k(N)^+ <= C_lambda (N+1)^lambda                              (E12)
```

for every `N`.  Choose `lambda>0`, which is harmless because the right endpoint in `(E11)` is at
least `3k-1`.  Put `z=exp(-x)`, `0<x<=1`.  The elementary exponential-moment bound

```text
sum_(N>=0)(N+1)^lambda exp(-Nx) <= K_lambda x^(-lambda-1)      (E13)
```

and `1-exp(-x)<=x` turn `(E7)` into

```text
|Phi(x)| <= D_lambda x^(-b),
b=(lambda+1-2k)/(2k),
Phi(x)=sum_(n>=1)mu(n)exp(-nx).                                (E14)
```

By `(E11)`, `b<Theta`.  Choose a nontrivial zeta zero `rho` with `Re(rho)>b`; this is possible by
the definition of `Theta`.  The Mellin integral of `(E14)` is holomorphic on `Re(s)>b`, while on
`Re(s)>1` the exact identity is

```text
integral_0^infinity Phi(x)x^(s-1)dx = Gamma(s)/zeta(s).         (E15)
```

The identity theorem continues `Gamma/zeta` holomorphically to `Re(s)>b`.  At `rho`, however,
`Gamma(rho)` is finite and nonzero and `zeta(rho)=0`, so `Gamma/zeta` has a pole.  Contradiction.
Therefore

```text
Lambda_k >= 2k(1+Theta)-1.                                    (E16)
```

Equations `(E10)` and `(E16)` prove `(E3)`.  Since functional-equation symmetry gives
`Theta>=1/2`, RH is equivalent to `Theta=1/2`, yielding `(E4)` and `(E5)`.

## Universal form

The proof uses only four inputs:

1. a real reciprocal coefficient sequence;
2. the ordinary-generating-function identity between coefficients and partial sums;
3. a Mellin transform whose singularity frontier is the zero frontier of the parent Dirichlet
   series;
4. equality between partial-sum order and that singularity frontier.

Thus the same affine law holds for any real self-dual reciprocal Dirichlet series satisfying these
standard hypotheses.  For complex coefficients, replace `(E1)` by the mixed convolution of `k`
partial-sum factors and `k` conjugate factors; `(E6)` then has left side `|A(z)|^(2k)`.  This
general extension is a theorem schema; publication claims should state explicit analytic
hypotheses rather than invoke an undefined class of `L`-functions.

## Hostile audit

1. **Not RH.** `(E3)` determines `Theta` from a new arithmetic order but does not prove that its
   value is `1/2`.
2. **Not a renamed Littlewood statement.** The upper inequality uses Littlewood.  The reverse
   inequality is genuinely one-sided and nonlinear: positive excursions of every even additive
   convolution recover the entire zero abscissa, while all negative excursions are discarded.
3. **No positivity sleight of hand.** Individual `C_k(N)` need not be nonnegative.  Positivity is
   used only after Abel synthesis, where the exact generating function is an even power.
4. **No estimate promoted as a law.** Headline is exact order identity `(E3)` for all nonlinear
   orders.  Bounds `(E8)`--`(E14)` are proof mechanisms.
5. **No source closure.** Proving the RH value `Lambda_k=3k-1` remains exactly RH-strength.  Higher
   convolution order does not make the source automatic.
6. **Quadratic/quartic collision.** Existing corpus has `k=1` and `k=2` sufficient criteria and
   conditional RH equivalences.  It does not state the exact `Theta` law, the limsup positive-part
   invariant, or the all-order affine rigidity.
7. **Unconditional positive excursions.** `(E5a)` is forced by the known zero symmetry and the
   positive-part exponent; no unproved zero location or negative excursion is used.

## Literature boundary

Targeted searches for Mertens self-convolution, additive-convolution zero abscissae, and nonlinear
Mertens RH criteria found no statement matching `(E3)`.  The closest located items were:

- Littlewood's classical equivalence and zero-abscissa control of `M`;
- Liflandsky's 2026 direct Möbius--Laplace criterion and explicit formula;
- Banks--Shparlinski's 2025 multiple-Möbius work, which explicitly leaves binary analogues out of
  reach;
- a 2014 MathOverflow question on coefficients of `zeta(s)^(-k)`, which concerns Dirichlet powers,
  not additive powers of Mertens partial sums.

The Abel/Cauchy-product mechanism is classical, and a negative search is not proof of priority.
Classification remains `NOVELTY UNVERIFIED` pending expert review.

A follow-up search for positive `Omega_+` results for `sum_a M(a)M(N-a)` found no match; search
hits concern the ordinary Mertens function, unrelated shifted-convolution papers whose author is
named Mertens, or number-field Mertens functions.

## Significance verdict

`(E3)` is a plausible paper-level universal law: it turns the rightmost zeta-zero coordinate into
an exact nonlinear additive arithmetic spectrum and proves that spectrum is rigid across every
even order.  It is stronger and broader than an isolated equivalent criterion.  It does **not**
solve a major open problem, so it must not be marketed as an RH proof or as satisfying the final
project goal by itself.

The unconditional one-sided omega theorem `(E5a)` is a concrete positive result extracted from
the law.  It proves near-critical positive excursions of every even convolution order, but its
priority and field-level significance still need specialist review.

## Gates

- [x] source and corpus audit
- [x] exact conjecture stated
- [x] hostile proof audit
- [x] dependency-closed paper proof, conditional only on named classical Littlewood theorem
- [x] initial literature search
- [ ] specialist priority review
- [x] formalize generic even-power Abel law
- [x] formalize fixed-`k` positive-part source-to-zero-free theorem
- [x] connect `k=1,2` to existing quadratic and quartic modules
- [ ] prove `Theta=1/2` unconditionally
- [ ] RH

## No-go closure

- **Killed mechanism:** raising to higher even additive order does not weaken RH to an automatic
  positivity statement; exact exponent `(E3)` shows every order retains the same `Theta`.
- **Strongest positive survivor:** universal affine order law `(E3)` and all-order rigidity.
- **New insight:** every off-critical zero forces positive, not merely absolute or signed,
  convolution excursions at every even nonlinear order.
- **Status:** paper-proved; novelty and formalisation pending; no unconditional RH claim.

## Log

- 2026-07-22 -- derived exact affine exponent, completed positive-part Abel proof, hostile audit,
  and initial corpus/literature boundary.

## Lean milestone -- all even orders

Formal module:

```text
formal/GaloisForLFunctions/RHTower/MobiusMertensEvenConvolutionOrderLaw.lean
```

Lean now proves:

- generic recursive additive Cauchy-convolution powers and their absolutely convergent evaluation;
- the sharp universal order transfer
  `a(N)=O(N^alpha) -> a^(*k)(N)=O(N^(k(alpha+1)-1))`;
- the exact all-even Abel identity
  `Phi(x)^(2k)=(1-exp(-x))^(2k) sum_N C_k(N)exp(-Nx)`;
- for every `k>0`, the one-sided `3k-1+o(1)` source implies every strict half-power
  Möbius--Laplace bound and RH;
- the classical all-strict-half-power Mertens family supplies the source at every order;
- the conditional iff after an explicit Littlewood input;
- exact `k=1` and `k=2` connectors to the prior quadratic and quartic modules.

Verification:

```text
lake env lean GaloisForLFunctions/RHTower/MobiusMertensEvenConvolutionOrderLaw.lean  PASS
lake build GaloisForLFunctions.RHTower.MobiusMertensEvenConvolutionOrderLaw         PASS
```

The targeted build reused the dependency cache: 8772 jobs were replayed and only the eight missing
modules on the target chain were compiled.  Endpoint axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.  Formal lint reaches the new module from `RHTower.lean`; its
nonzero result lists unrelated pre-existing unreachable modules and does not list this module.

The exact `Lambda_k=2k(1+Theta)-1` limsup statement remains paper-level because the project does
not yet formalize `Theta` or the classical full zero-abscissa version of Littlewood's theorem.

- 2026-07-22 -- formalized all-order Abel hierarchy, critical source-to-RH bridge, conditional
  converse, and quadratic/quartic connectors; targeted cached build and axiom audit pass.

## Lean milestone -- the zero abscissa and the one-sided lower edge

- 2026-08-08 -- **`Theta` is now formalized, and the lower half of `(E3)` is unconditional.**
  All new declarations report only `propext`, `Classical.choice`, `Quot.sound`.

New modules:

```text
formal/GaloisForLFunctions/RHTower/ZetaZeroAbscissa.lean
formal/GaloisForLFunctions/RHTower/MobiusMertensEvenConvolutionOrderLowerEdge.lean
```

`ZetaZeroAbscissa.lean` defines

```text
zetaZeroAbscissa = sSup { Re rho : zeta rho = 0 }
```

and proves it is well defined and pinned:

- `bddAbove_zetaZeroReSet`, `zetaZeroReSet_nonempty` -- nonemptiness is the corpus's unconditional
  zero-existence theorem `exists_riemannZeta_zero_mem_openStrip`;
- `re_le_zetaZeroAbscissa`, `riemannZeta_ne_zero_of_zetaZeroAbscissa_lt`,
  `exists_zetaZero_lt_re`, `exists_zetaZero_mem_openStrip_lt_re`;
- `riemannZeta_one_sub_eq_zero_of_mem_openStrip` -- the functional equation reflects a nontrivial
  zero across the critical line;
- `half_le_zetaZeroAbscissa : 1/2 <= Theta`, `zetaZeroAbscissa_le_one`, `zetaZeroAbscissa_pos`.

`MobiusMertensEvenConvolutionOrderLowerEdge.lean` proves the genuinely one-sided half of the law:

- `norm_pow_even_mobiusDiscreteLaplaceTransform_le_of_subpower` -- `(E7)` plus the exponential
  moment bound: a global positive-part bound `Re C_k(N) <= C (N+1)^lambda` gives
  `|Phi(x)|^(2k) <= C K_lambda x^(2k-lambda-1)` on `0 < x <= 1`;
- **`le_of_mertensEvenConvolution_subpower`** -- the lower edge in subpower form: any such global
  bound forces `lambda >= 2k(1+Theta)-1`.  Mechanism: the radial bound gives
  `Phi = O(x^(-b))` with `b = (lambda+1-2k)/(2k) < Theta`, and
  `not_isBigO_moebiusProfile_rpow` (the half-plane identity theorem for `G . zetaEntire = s-1`,
  evaluated at a zeta zero with `Re rho > b`) forbids it;
- `mertensEvenConvolutionOrder` -- the limsup `Lambda_k` of `(E2)`, with boundedness
  (`isBoundedUnder_mertensEvenConvolutionOrderSeq`, from the crude cubic bound on the second-Cesaro
  sequence and the corpus order transfer) and nonnegativity;
- **`le_mertensEvenConvolutionOrder`** -- `(E16)`: `2k(1+Theta)-1 <= Lambda_k`;
- **`frequently_rpow_le_mertensEvenConvolution`** -- `(E5a)`, unconditional: for every `k >= 1` and
  every `eps > 0`,
  `C_k(N) >= (N+1)^(3k-1-eps)` at infinitely many `N`.
  This uses only `Theta >= 1/2`, which is now a theorem, not an assumption.

Reusable infrastructure added:
`HTGeometry/LogOrderLimsupBound.exists_global_subpower_of_eventually`,
`exists_global_subpower_of_eventually_le`, `log_one_add_max_div_log_nonneg`.

Remaining for the exact law `(E3)`: the upper inequality `(E10)`, which needs the classical
Littlewood bound `M(N) = O(N^(Theta+eps))` at the true abscissa.  The corpus already owns the
`Theta = 1/2` instance (`riemannHypothesis_implies_mobiusMertensAllStrictHalfPowerBound`) and the
universal transfer `partialSumSeq_subpower_of_smoothPerron`, which is already stated for a general
`Theta`; what is missing is the `Theta`-parameterized version of the reciprocal-zeta shift data
(`exists_invZeta_shift_data_of_rh` and the three-circles lower bound feeding it), whose only use of
RH is `zeta s != 0` for `Re s > 1/2`.  For `Theta = zetaZeroAbscissa` that hypothesis is the
unconditional `riemannZeta_ne_zero_of_zetaZeroAbscissa_lt`.

## Stage-3 Lean certificate

- 2026-08-08 -- **the exact law `(E3)` is closed unconditionally**, together with its Riemann
  form `(E4)` and the classical Littlewood input at the true abscissa.  Every declaration below
  reports only `propext`, `Classical.choice`, `Quot.sound`, and every module is reachable from
  `GaloisForLFunctions.RHTower`.

| Card statement | Lean declaration | Module |
|---|---|---|
| `Theta` | `zetaZeroAbscissa` | `RHTower/ZetaZeroAbscissa` |
| `Theta >= 1/2`, `Theta <= 1` | `half_le_zetaZeroAbscissa`, `zetaZeroAbscissa_le_one` | `RHTower/ZetaZeroAbscissa` |
| `Lambda_k` | `mertensEvenConvolutionOrder` | `RHTower/MobiusMertensEvenConvolutionOrderLowerEdge` |
| `(E6)`--`(E7)` Abel law | `mobiusDiscreteLaplaceTransform_pow_even_eq_one_sub_exp_pow_even_mul_tsum`, `norm_pow_even_mobiusDiscreteLaplaceTransform_le_of_subpower` | `RHTower/MobiusMertensEvenConvolutionOrderLaw`, `.../OrderLowerEdge` |
| `(E8)` Littlewood at `Theta` | `mobiusMertens_subpower_zetaZeroAbscissa` | `RHTower/MobiusMertensAbscissaLittlewood` |
| `(E9)`--`(E10)` upper edge | `norm_mobiusMertensEvenConvolution_le_of_subpower`, `mertensEvenConvolutionOrder_le` | `RHTower/MobiusMertensEvenConvolutionExactOrder` |
| `(E11)`--`(E16)` lower edge | `le_of_mertensEvenConvolution_subpower`, `le_mertensEvenConvolutionOrder` | `RHTower/MobiusMertensEvenConvolutionOrderLowerEdge` |
| **`(E3)`** exact affine law | **`mertensEvenConvolutionOrder_eq`** | `RHTower/MobiusMertensEvenConvolutionExactOrder` |
| **`(E4)`** RH form | **`riemannHypothesis_iff_mertensEvenConvolutionOrder_eq`** | `RHTower/MobiusMertensEvenConvolutionExactOrder` |
| **`(E5a)`** unconditional omega-plus | **`frequently_rpow_le_mertensEvenConvolution`** | `RHTower/MobiusMertensEvenConvolutionOrderLowerEdge` |

The missing classical input named in the earlier log -- the full zero-abscissa version of
Littlewood's theorem -- is now a theorem of the tree.  The RH-specific reciprocal-zeta chain was
generalised to an arbitrary zero-free frontier in

```text
formal/GaloisForLFunctions/RHTower/InvZetaAbscissaSubpolynomial.lean
```

(`exists_three_circles_zeta_lower_bound_of_zeroFree`,
`exists_zeta_lower_bound_subpolynomial_of_zeroFree`, `exists_invZeta_shift_data_of_zeroFree`,
`zetaResidueUnit_ne_zero_of_zeroFree`).  Only two things change from the RH version: the three
circles are centred at `4 + i t` instead of `3 + i t`, so that the outer radius still overshoots
`Re s = Theta + delta/4` for every `Theta <= 1`; and the zero-free input is the hypothesis
`zeta z != 0` for `Re z > Theta`, which at `Theta = zetaZeroAbscissa` is the unconditional
`riemannZeta_ne_zero_of_zetaZeroAbscissa_lt`.  Feeding that datum to the corpus's universal
`partialSumSeq_subpower_of_smoothPerron` gives `M(N) = O(N^(Theta+eps))` with no unproved premise.

## Gates

- [x] source and corpus audit
- [x] exact conjecture stated
- [x] hostile proof audit
- [x] dependency-closed paper proof, conditional only on named classical Littlewood theorem
- [x] initial literature search
- [ ] specialist priority review
- [x] formalize generic even-power Abel law
- [x] formalize fixed-`k` positive-part source-to-zero-free theorem
- [x] connect `k=1,2` to existing quadratic and quartic modules
- [x] formalize `Theta` and the classical Littlewood theorem at the true abscissa
- [x] formalize the exact law `(E3)`, the RH form `(E4)`, and the unconditional omega-plus law `(E5a)`
- [ ] prove `Theta=1/2` unconditionally
- [ ] RH
