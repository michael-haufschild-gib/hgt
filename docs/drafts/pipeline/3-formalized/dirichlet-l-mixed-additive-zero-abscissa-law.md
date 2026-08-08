# Dirichlet-L mixed additive zero-abscissa law

- **ID:** `dirichlet-l-mixed-additive-zero-abscissa-law`
- **Stage:** 3-formalized / needs-priority-review
- **Type:** THEOREM (paper)
- **Scientific status:** `[PROVED HERE] [LEAN-FORMALIZED UNCONDITIONALLY: (D3),(D4),(D4a),(D5),(D6),(D7)]` `[CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT GRH]`
- **Source:** Möbius even-additive zero-abscissa order law / primitive Dirichlet twists
- **Statement:** Positive excursions of every mixed even additive convolution of a twisted
  Mertens function have an exact order determined by the rightmost zero of its Dirichlet
  `L`-function.

## Goal

Promote the zeta-specific order law to a universal arithmetic spectral law for every primitive
Dirichlet character, including complex characters.  The theorem recovers the full rightmost-zero
coordinate of each `L(s,chi)` from a finite additive statistic and discards every negative
convolution excursion.

Let `chi` be a primitive Dirichlet character.  The primitive character of conductor one is
understood as the zeta case.  For conductor greater than one, put

```text
M_chi(0)=0,
M_chi(N)=sum_(1<=n<=N) mu(n) chi(n),
Theta_chi=sup{Re(rho): L(rho,chi)=0, 0<Re(rho)<1}.
```

For every integer `k>=1`, define the real mixed `2k`-fold additive convolution

```text
C_(chi,k)(N)
 = sum_(a_1+...+a_k+b_1+...+b_k=N)
     product_(j=1)^k M_chi(a_j)
     product_(j=1)^k conjugate(M_chi(b_j)).                    (D1)
```

All coordinates are nonnegative integers; terms containing a zero coordinate vanish.  Complex
conjugation and exchange of the two `k`-tuples show that `C_(chi,k)(N)` is real.  Define

```text
Lambda_(chi,k) = limsup_(N->infinity)
  log(1+max(C_(chi,k)(N),0)) / log(N+1).                       (D2)
```

Then the exact law is

```text
Lambda_(chi,k)=2k(1+Theta_chi)-1.                             (D3)
```

Consequently, for every fixed primitive `chi` and every fixed `k>=1`,

```text
GRH for L(s,chi)  <->  Lambda_(chi,k)=3k-1.                   (D4)
```

The Dirichlet GRH is therefore equivalent to `(D4)` holding for all primitive characters at any
one fixed order `k`.

There is also an unconditional one-sided consequence.  Functional-equation symmetry gives
`Theta_chi>=1/2`; hence, for every `epsilon>0`,

```text
C_(chi,k)(N) = Omega_+(N^(3k-1-epsilon)).                    (D4a)
```

Explicitly, infinitely many `N` satisfy
`C_(chi,k)(N) >= N^(3k-1-epsilon)`.  This is positive-side growth, not an absolute-value
omega result.  For `k=1`, the reflected twisted-Mertens convolution has unconditional
near-quadratic positive excursions.

## Exact mixed Abel law

For `0<z<1`, set

```text
A_chi(z)=sum_(n>=1) mu(n)chi(n)z^n,
B_chi(z)=sum_(N>=0) M_chi(N)z^N=A_chi(z)/(1-z).
```

Because `z` is real,

```text
B_conjugate(chi)(z)=conjugate(B_chi(z)).
```

The coefficient of `z^N` in
`B_chi(z)^k B_conjugate(chi)(z)^k` is `(D1)`.  Absolute convergence inside the unit
disc gives

```text
|A_chi(z)|^(2k)
 = (1-z)^(2k) sum_(N>=0) C_(chi,k)(N)z^N.                     (D5)
```

The left side is nonnegative.  Hence

```text
|A_chi(z)|^(2k)
 <= (1-z)^(2k)
      sum_(N>=0) max(C_(chi,k)(N),0)z^N.                      (D6)
```

This is the complex-character replacement for the real even-power argument.  It uses no
self-duality assumption.

## Classical zero-abscissa lemma

For every fixed primitive `chi` and every `eta>0`,

```text
M_chi(N)=O_(chi,eta)((N+1)^(Theta_chi+eta)).                  (D7)
```

This is the fixed-character Littlewood theorem.  Its proof is the standard proof for zeta with
`1/zeta` replaced by `1/L(s,chi)`:

1. for `Re(s)>1`, Euler products give
   `1/L(s,chi)=sum mu(n)chi(n)n^(-s)`;
2. `L(s,chi)` has no zero in `Re(s)>Theta_chi`;
3. the functional equation, finite order, and the logarithmic-derivative expansion over zeros
   give the Littlewood bound for `1/L(s,chi)` in every closed half-plane
   `Re(s)>=Theta_chi+delta`;
4. Perron inversion with the usual truncation then gives `(D7)`.

Equivalently, the abscissa of convergence of the reciprocal Dirichlet series is
`Theta_chi`.  The reverse inequality is immediate from Abel summation: a smaller partial-sum
exponent would continue `1/L(s,chi)` holomorphically across a zero with larger real part.

This lemma is classical input, not a new claim of this card.  Constants may depend on the fixed
character; no uniform conductor estimate is asserted.

## Proof of the upper inequality

Fix `eta>0`.  There are at most `(N+1)^(2k-1)` weak compositions of `N` into `2k`
coordinates.  Bound every twisted Mertens factor in `(D1)` by `(D7)`.  Then

```text
|C_(chi,k)(N)|
 <= A_(chi,eta)^(2k)
    (N+1)^(2k(Theta_chi+eta)+2k-1).                           (D8)
```

The positive part is no larger than the absolute value.  Letting `eta` tend to zero gives

```text
Lambda_(chi,k) <= 2k(1+Theta_chi)-1.                          (D9)
```

## Proof of the lower inequality

Suppose instead that

```text
Lambda_(chi,k) < lambda < 2k(1+Theta_chi)-1.                 (D10)
```

Choose `lambda>0`, possible because functional-equation symmetry gives
`Theta_chi>=1/2`.  The limsup definition absorbs finitely many initial terms into a constant and
gives

```text
max(C_(chi,k)(N),0) <= C_lambda(N+1)^lambda.                  (D11)
```

Put `z=exp(-x)`, where `0<x<=1`.  The standard exponential-moment bound and `(D6)` give

```text
sum_(N>=0)(N+1)^lambda exp(-Nx)=O_lambda(x^(-lambda-1)),
|Phi_chi(x)|=O(x^(-b)),
b=(lambda+1)/(2k)-1,
Phi_chi(x)=sum_(n>=1)mu(n)chi(n)exp(-nx).                     (D12)
```

By `(D10)`, `b<Theta_chi`.  Choose a nontrivial zero `rho` of `L(s,chi)` with
`Re(rho)>b`.  The bound `(D12)` and exponential decay at infinity make

```text
H(s)=1/Gamma(s) integral_0^infinity Phi_chi(x)x^(s-1) dx      (D13)
```

holomorphic on `Re(s)>b`.  Termwise Mellin integration in `Re(s)>1` gives

```text
H(s)=1/L(s,chi).                                              (D14)
```

Thus `H(s)L(s,chi)=1` on `Re(s)>1`, and the identity theorem gives the same identity throughout
`Re(s)>b`.  Evaluation at `rho` is impossible: its left side is zero and its right side is one.
This contradiction proves

```text
Lambda_(chi,k) >= 2k(1+Theta_chi)-1.                          (D15)
```

Together, `(D9)` and `(D15)` prove `(D3)`.

## Functional-equation audit

For a complex character, the functional equation initially exchanges `chi` and
`conjugate(chi)`.  This does not weaken `(D4)`.  If `rho` is a nontrivial zero of
`L(s,chi)`, the functional equation gives a zero `1-rho` of `L(s,conjugate(chi))`, and
coefficient conjugation turns this into a zero `1-conjugate(rho)` of `L(s,chi)`.  Hence the
nontrivial zeros of the same `L(s,chi)` are symmetric about `Re(s)=1/2`.  Therefore
`Theta_chi>=1/2`, and `Theta_chi=1/2` is equivalent to GRH for this character.

A real exceptional zero causes no defect: it merely raises `Theta_chi`, and `(D3)` records that
increase exactly.

## Abstract universal form

The same proof applies to any reciprocal Dirichlet series

```text
1/F(s)=sum_(n>=1) a(n)n^(-s)
```

with the following explicit properties:

1. `a(n)` has at most polynomial growth;
2. the partial sums `S(N)=sum_(n<=N)a(n)` satisfy the zero-abscissa law
   `S(N)=O_eta(N^(Theta_F+eta))`;
3. `F` is holomorphic at its nontrivial zeros and at least one zero occurs arbitrarily close to
   the rightmost-zero abscissa `Theta_F`;
4. termwise Mellin integration gives
   `integral Phi_F(x)x^(s-1)dx=Gamma(s)/F(s)` in an initial right half-plane.

With `k` copies of `S` and `k` copies of `conjugate(S)`, the positive-part order is always

```text
2k(1+Theta_F)-1.                                              (D16)
```

Primitive Dirichlet `L`-functions supply an unconditional, explicit family satisfying these
hypotheses.  Extensions to automorphic or Selberg-class `L`-functions require their own
zero-abscissa lemma and are not claimed without checking those hypotheses.

## Hostile audit

1. **Not GRH.** The theorem measures `Theta_chi`; it does not prove that the measured value is
   `1/2`.
2. **Not a renamed twisted Littlewood criterion.** Littlewood controls the linear partial sum
   with an absolute value.  `(D3)` recovers the exact zero frontier from only positive excursions
   of every nonlinear mixed additive order.
3. **No false positivity for complex characters.** `C_(chi,k)(N)` is real but may be negative.
   Positivity occurs only after exact Abel synthesis into `|A_chi(z)|^(2k)`.
4. **No hidden self-duality.** Pairing `chi` with its conjugate handles arbitrary primitive
   complex characters.
5. **No uniformity over conductor.** Every character is fixed.  The statement does not imply a
   hybrid or conductor-uniform GRH estimate.
6. **No automatic source at higher order.** `(D3)` proves that every `k` retains exactly the same
   rightmost-zero obstruction.
7. **Principal-character corner.** A primitive principal character has conductor one, which is
   precisely the zeta theorem already proved.  Imprimitive principal characters are excluded.
8. **The omega corollary is genuinely one-sided.** `(D4a)` follows from the positive-part limsup;
   no assertion about negative excursions is used or implied.

## Literature boundary

Targeted searches through 2026-07-22 found no matching statement involving the positive part of
mixed additive convolutions of `M_chi` or the exact affine exponent `(D3)`.  Closest results:

- Littlewood's classical twisted-Mertens/GRH equivalence supplies only the linear source bound;
- Corey Everlove's 2018 thesis studies meromorphic continuation of Dirichlet series attached to
  additive convolutions when one ordinary generating function is meromorphic near `z=1`, and
  separately studies `sum M(n)n^(-s)` and partial sums of `chi`; it does not cover twisted
  Mertens self-convolutions, positive parts, or exact zero-abscissa orders;
- Misra--Saha--Sharma (arXiv:2502.08305, revised 2026) treats divisor additive convolutions and
  functions with absolutely convergent Ramanujan expansions, not `mu(n)chi(n)` partial sums;
- Saha's multiple Dirichlet series associated to additive and Dirichlet characters concerns
  analytic continuation of different multiple series, not `(D1)`--`(D3)`.

Negative search is not proof of priority.  Status remains `NOVELTY UNVERIFIED` pending specialist
review and a MathSciNet/Zentralblatt citation search.

A second targeted search for an `Omega_+` theorem for `sum_a M(a)M(N-a)`, twisted Mertens
self-convolutions, and positive additive-convolution excursions found no matching result.  Located
omega results concern the ordinary Mertens function or number-field analogues, not `(D4a)`.

## Significance verdict

`(D3)` is a universal exact law across every primitive Dirichlet `L`-function and every nonlinear
even order.  It turns the rightmost zero into a one-sided finite-additive arithmetic spectrum,
including for complex characters and possible exceptional real zeros.  This is broader and more
structural than another isolated GRH equivalence.

The unconditional corollary `(D4a)` is a concrete new theorem rather than another criterion: it
forces near-critical excursions on the positive side for every primitive character and every
mixed even order.  Whether specialists regard that resolved one-sided omega problem as major
remains part of the novelty/significance audit.

It still does **not** solve a major open problem: the value `Lambda_(chi,k)=3k-1` remains exactly
GRH-strength.  Publication must present this as a new spectral characterization, not as progress
on the truth of GRH unless an unconditional source bound is later proved.

## Gates

- [x] source and corpus audit
- [x] exact theorem stated for real and complex primitive characters
- [x] dependency-closed paper proof using named classical fixed-character Littlewood input
- [x] functional-equation and exceptional-zero audit
- [x] initial external collision search
- [ ] specialist priority review
- [x] formalize generic mixed complex Abel law
- [x] connect the zeta specialization to the existing all-even-order Lean module
  (`mixedAdditiveConvolutionPower_eq_additiveConvolutionPower_two_mul_of_real`)
- [ ] prove the GRH-value source unconditionally
- [ ] Dirichlet GRH
- [ ] RH

## No-go closure

- **Killed mechanism:** passing to twists, conjugate pairing, or higher even order does not make
  the critical source automatic; the exact exponent continues to encode the rightmost zero.
- **Strongest positive survivor:** mixed one-sided affine order law `(D3)` for every primitive
  character and every `k`.
- **New insight:** complex non-self-dual `L`-functions admit the same positive-excursion spectral
  recovery once the additive convolution is paired with its conjugate.
- **Status:** dependency-closed paper proof; generic Hermitian Abel core formalized; novelty and
  full zero-abscissa formalization pending; no GRH claim.

## Lean milestone -- Hermitian mixed Abel core

Formal module:

```text
formal/GaloisForLFunctions/RHTower/DirichletLMixedAdditiveZeroAbscissaLaw.lean
```

Lean proves, for every complex sequence `a` and every order `k`:

- the mixed coefficient obtained by convolving `a^(*k)` with its coefficientwise conjugate;
- exact conjugation invariance and zero imaginary part of every mixed coefficient;
- absolute summability of the mixed Abel series from absolute summability of the original series;
- the exact Hermitian Abel identity
  `(sum a(N)q^N)^k * conjugate((sum a(N)q^N)^k) = sum C_k(N)q^N`
  whenever `conjugate(q)=q`;
- its norm-squared real-part form;
- the generic one-sided comparison turning only coefficient upper bounds into a norm-square Abel
  bound, with all negative coefficients discarded;
- the explicit first-order quadratic specialization.

Verification:

```text
lake env lean GaloisForLFunctions/RHTower/DirichletLMixedAdditiveZeroAbscissaLaw.lean  PASS
```

Endpoint axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`.  The formal
research index finds all new declarations.  Formal lint reaches the module through `RHTower.lean`;
its nonzero exit lists unrelated pre-existing unreachable modules and does not list this module.

The character definitions, `Theta_chi`, classical twisted Littlewood theorem, and exact limsup
identity `(D3)` remain paper-level.

## Log

- 2026-07-22 -- derived mixed-conjugate Abel law, proved exact primitive-character order formula,
  cleared the closest Everlove and Misra--Saha--Sharma collisions, and completed hostile audit.
- 2026-07-22 -- formalized generic complex Hermitian mixed-convolution coefficients, realness,
  summability, and exact Abel evaluation; direct Lean check and axiom audit pass.

- 2026-07-24 — **Zeta-specialization connector formalized** (gate `connect the zeta specialization to
  the existing all-even-order Lean module`), in
  `RHTower/DirichletLMixedAdditiveZeroAbscissaLaw.lean` (unconditional, axioms
  `[propext, Classical.choice, Quot.sound]`):
  * `additiveConvolutionPower_eq_coeff_pow` — the `k`-fold additive convolution power is the `N`-th
    coefficient of `(∑ a(n) Xⁿ)^k` (generating-power-series identification).
  * `additiveConvolutionPower_add` — the convolution **semigroup law**
    `conv_{m+n}(N) = ∑_{ab} conv_m(ab.1)·conv_n(ab.2)`, immediate from `pow_add` and the power-series
    coefficient product (reusable infrastructure for the whole even-order framework).
  * `mixedAdditiveConvolutionPower_eq_additiveConvolutionPower_two_mul_of_real` — for a **real**
    reciprocal-coefficient sequence (the conductor-one/zeta case, `(a N).im = 0`), the Hermitian
    mixed `2k`-convolution equals the plain `2k`-fold even additive convolution
    `additiveConvolutionPower a (2*k)`.  This is the exact zeta specialization: the complex Dirichlet
    mixed law of this module coincides with the real all-even-order law of
    `MobiusMertensEvenConvolutionOrderLaw` on real sequences (via
    `additiveConvolutionPower_im_eq_zero` and the semigroup law).
  Remaining gates are non-formalizable or GRH-level (`prove the GRH-value source unconditionally`,
  `Dirichlet GRH`, `RH`) plus the non-Lean specialist priority review.

## Stage-3 Lean certificate

- 2026-08-08 -- **the exact law `(D3)`, the GRH form `(D4)` and the unconditional omega-plus law
  `(D4a)` are all closed in Lean, with no premises.**  Every declaration below reports only
  `propext`, `Classical.choice`, `Quot.sound`, and every module is reachable from
  `GaloisForLFunctions.RHTower`.

The earlier log entry ("The character definitions, `Theta_chi`, classical twisted Littlewood
theorem, and exact limsup identity `(D3)` remain paper-level") was stale: `Theta_chi`, the twisted
Littlewood theorem and `(D3)` had all been built in the meantime.  What this cycle adds is `(D4)`
and `(D4a)`.

| Card statement | Lean declaration | Module |
|---|---|---|
| `M_chi` | `partialSumSeq (↗χ * ↗μ)` | `RHTower/TwistedMertensOrderLowerBound` |
| `C_(chi,k)` of `(D1)` | `mixedAdditiveConvolutionPower (partialSumSeq (↗χ * ↗μ)) k` | `RHTower/DirichletLMixedAdditiveZeroAbscissaLaw` |
| `Theta_chi` | `zeroAbscissa χ` | `RHTower/DirichletZeroAbscissa` |
| `Theta_chi >= 1/2` | `half_le_zeroAbscissa` | `RHTower/DirichletZeroAbscissa` |
| `(D5)`--`(D6)` mixed Abel law | `pow_mul_star_pow_eq_tsum_mixedAdditiveConvolutionPower_mul_pow`, `norm_sq_pow_le_tsum_of_mixedAdditiveConvolutionPower_upper` | `RHTower/DirichletLMixedAdditiveZeroAbscissaLaw` |
| `(D7)` twisted Littlewood at `Theta_chi` | `twistedMertensSubpowerBound_zeroAbscissa` | `RHTower/TwistedMertensLittlewood` |
| lower half of `(D3)` | `two_mul_one_add_zeroAbscissa_sub_one_le_limsup_mertens` | `RHTower/TwistedOrderLawTheta` |
| upper half of `(D3)` | `limsup_mertens_le_of_subpowerBound` | `RHTower/TwistedOrderLawTheta` |
| **`(D3)`** exact law | **`limsup_mertens_eq_zeroAbscissa`** | `RHTower/TwistedMertensLittlewood` |
| **`(D4a)`** unconditional omega-plus | **`frequently_rpow_le_twistedMertensEvenConvolution`** | `RHTower/TwistedOrderLawExact` |
| GRH predicate | `DirichletGRH` | `RHTower/TwistedOrderLawExact` |
| `GRH_chi <-> Theta_chi = 1/2` | `zeroAbscissa_eq_half_iff_dirichletGRH` | `RHTower/TwistedOrderLawExact` |
| **`(D4)`** GRH form | **`dirichletGRH_iff_limsup_mertens_eq`** | `RHTower/TwistedOrderLawExact` |

The new module also supplies the two structural lemmas the GRH form needs:
`gammaFactor_ne_zero_of_re_pos` and `completedLFunction_eq_zero_of_LFunction_eq_zero` (an
`L`-zero in the right half-plane is a completed zero), and
`LFunction_eq_zero_conj_one_sub` -- the reflection sending a zero of `L(.,chi)` at `rho` in the open
strip to a zero at `conj (1 - rho)`, obtained by composing the completed functional equation
(which lands on `chi` inverse) with the conjugation symmetry `conj_completedLFunction` (which brings
it back to `chi`).  This is what makes `Theta_chi = 1/2` equivalent to GRH rather than merely
implied by it.

## Gates

- [x] source and corpus audit
- [x] exact theorem stated for real and complex primitive characters
- [x] dependency-closed paper proof using named classical fixed-character Littlewood input
- [x] functional-equation and exceptional-zero audit
- [x] initial external collision search
- [ ] specialist priority review
- [x] formalize generic mixed complex Abel law
- [x] connect the zeta specialization to the existing all-even-order Lean module
  (`mixedAdditiveConvolutionPower_eq_additiveConvolutionPower_two_mul_of_real`)
- [x] formalize `Theta_chi` and the twisted Littlewood theorem at the true abscissa
- [x] formalize the exact law `(D3)`, the GRH form `(D4)`, and the omega-plus law `(D4a)`
- [ ] prove the GRH-value source unconditionally
- [ ] Dirichlet GRH
- [ ] RH
