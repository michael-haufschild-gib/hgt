# Suzuki affine resolvent Krein defect and sharp weld debt

- **ID:** `suzuki-affine-resolvent-krein-defect`
- **Stage:** 3 — formalized in Lean 4
- **Formalized companion:** `./suzuki-affine-resolvent-krein-defect-formalized.md`
- **Type:** exact obstruction + positive survivor + revised RH frontier
- **Status:** `[PROVED] [UNCONDITIONAL] [SOURCE-CONNECTED]`
- **Lean:** `formal/GaloisForLFunctions/RHTower/SuzukiAffineResolventKreinDefect.lean`
- **Parent:** `../../1-in-progress/suzuki-jump-kernel-loewner-growth.md`

## 1. Frontier isolated by corpus audit

Suzuki's exact two-shift sewing gives

```text
K_jump = -K_0 + [β H_α - α H_β]/(β-α),   α<β<0.       (1)
```

The full source quotient is Euler--Gamma plus the non-cancelling Neumann projective holonomy
proved in `suzuki-full-frequency-neumann-holonomy-survivor.md`.  The old claim that the second
resolvent identity alone turns `(1)` into `B*B` is false.  What the resolvent identity actually
produces is determined below.

The corpus still cannot prove the following RH-bearing assertion:

> the explicit prime--Gamma exterior term plus Neumann projective holonomy cancels every negative
> coordinate of the local Krein form while preserving the global Xi divisor.

That is the precise global-to-local weld problem.  It is stronger than a central residue identity,
not implied by Donoghue positivity of either negative shift, and not supplied by bare resolvent
algebra.

## 2. Exact scalar theorem

Put

```text
R_λ(t)=1/(t-λ),
E_(α,β)(t)=[βR_α(t)-αR_β(t)]/(β-α).
```

Assume only that all displayed denominators are nonzero.  Then

```text
D_(α,β)(t):=R_0(t)-E_(α,β)(t)
           = αβ/[t(t-α)(t-β)].                         (2)
```

### Proof `[PROVED]`

Use the common denominator `t(t-α)(t-β)(β-α)`.  The numerator of `R_0-E` is

```text
(β-α)(t-α)(t-β)
-t[β(t-β)-α(t-α)]
=αβ(β-α).
```

Cancel `β-α`.  This gives `(2)`.

Now impose the source-relevant order

```text
α<β<0,   β<t,   t≠0.                                  (3)
```

Then `αβ>0`, `t-α>0`, and `t-β>0`; hence

```text
sign D_(α,β)(t)=sign t.                                (4)
```

Equivalently, with

```text
ω_(α,β)(t)=αβ/[|t|(t-α)(t-β)] > 0,
```

one has the exact Krein factorization

```text
D_(α,β)(t)=sgn(t) ω_(α,β)(t).                          (5)
```

## 3. Orientation theorem

For the ordinary resolvent response `q_λ=R_λ`, its affine source gap is

```text
[βq_α-αq_β]/(β-α)-q_0 = -D_(α,β).                     (6)
```

For the negative-Stieltjes/anti-resolvent response `q_λ=-R_λ`, it is

```text
[βq_α-αq_β]/(β-α)-q_0 = D_(α,β).                      (7)
```

Thus only anti-resolvent orientation agrees with the required positive sign on positive spectral
coordinates.  But it is strictly negative on every negative coordinate.  Resolvent algebra gives
a Pontryagin/Krein square, not a Hilbert square.

For a finite diagonal spectral model with nonzero nodes `t_j>β`, coefficients `c_j`, and positive
spectral weights absorbed into `c_j`, `(5)` gives

```text
Q_(α,β)(c)
= Σ_j |c_j|² D_(α,β)(t_j)
= Σ_(t_j>0) |c_j|² ω_(α,β)(t_j)
  - Σ_(t_j<0) |c_j|² ω_(α,β)(t_j).                    (8)
```

Therefore, in a minimal diagonal realization, negative index of sewn local form equals number of
negative spectral nodes counted with multiplicity.  This is exact algebraic bridge between
Suzuki jump-kernel positivity and the restricted-Weil/CCM Morse index.

## 4. Sharp global-to-local compensation law

Let `g(t)` denote arbitrary global target value.  Define local-to-global correction

```text
C_g(t)=-R_0(t)-g(t).
```

For anti-resolvent sewing, exact gap against global target is

```text
G_g(t)
=[β(-R_α(t))-α(-R_β(t))]/(β-α)-g(t)
=D_(α,β)(t)+C_g(t).                                   (9)
```

Consequently

```text
G_g(t)≥0  <=>  C_g(t)≥-D_(α,β)(t).                    (10)
```

If `t<0`, right side is a **strictly positive debt**:

```text
-D_(α,β)(t)=ω_(α,β)(t)>0.                             (11)
```

Equations `(9)`--`(11)` are sharp.  They identify exactly what global Xi multiplier plus full
prime--Gamma/Neumann completion must contribute.  Replacing actual `K_0` by local `R_0` erases
this debt and silently assumes the missing RH-bearing weld.

## 5. Decisive no-go

`[PROVED]` No universal positive `B*B` factorization of two-shift anti-resolvent difference can
follow from second resolvent identity alone on a spectral space admitting a negative node.

Indeed, evaluate proposed nonnegative form on basis vector of any `t_j<0`.  Equation `(8)` gives
`Q(e_j)=-ω(t_j)<0`, contradiction.

This retires `SUZUKI-RESOLVENT-BIANCHI-SQUARE` as an abstract resolvent claim.  It does **not**
retire Suzuki route: exact positive survivor is signed factorization plus explicit completion debt.

## 6. New source-specific conjecture

### `SUZUKI-GLOBAL-LOCAL-KREIN-WELD` `[CONJECTURE]`

For curvature-selected negative shifts and sufficiently large aperture, put actual Suzuki source
data in one characteristic gauge and retain both:

1. reflected prime--Gamma exterior triangle;
2. full-frequency Neumann projective holonomy
   `αβ sin(az)[d_α/W_α-d_β/W_β]/(2z(β-α))`.

There is a source-constructed minimal Pontryagin realization in which jump quadratic form splits

```text
Q_jump(c)=Q_+(c)-Q_-(c)+Q_completion(c),               (12)
```

where `Q_±` are positive/negative spectral pieces forced by `(8)`, and explicit coupled
prime--Gamma/holonomy completion satisfies

```text
Q_completion(c)=Q_-(c)+||B_a c||².                    (13)
```

No divisor data may be inserted into `B_a`; it must be obtained from source triangles and the
centered projective characteristic tangent.  Functional-equation--Schwarz fake orbit insertion
must break `(13)` at source level.

Then `(12)`--`(13)` give `Q_jump=Q_++||B_a c||²≥0`; existing jump-kernel pole tomography yields
RH.

This is falsifiable: one finite node set with
`Q_completion(c)<Q_-(c)` kills conjecture.  It is not presented as proved.

## 7. Why this advances frontier

- replaces incorrect positive-square heuristic by exact signed factorization;
- identifies orientation needed by source response;
- proves negative index is not nuisance but exact restricted-Weil spectral count;
- quantifies, coordinate by coordinate, missing completion contribution;
- narrows RH proof to explicit identity `(13)`, with Neumann holonomy compulsory.

## 8. Novelty and source audit

Suzuki's 2026 paper supplies finite-aperture self-adjoint extensions and characteristic functions,
not affine two-shift positivity.  Generalized Nevanlinna realization theory explains abstractly
that negative squares correspond to Pontryagin index, but corpus and focused current-literature
search found no source deriving `(2)`--`(11)` for Suzuki sewing or identifying the exact
prime--Gamma/Neumann compensation debt.  Novelty claim is this source-specific bridge and sharp
frontier correction, not elementary fraction simplification in isolation.

## 9. Formal status

Lean module proves unconditionally:

- exact identity `(2)`;
- ordinary/anti-resolvent orientation `(6)`--`(7)`;
- positive and negative sign equivalences `(4)`;
- exact decomposition `(9)` and threshold `(10)`;
- positive debt and impossibility of bare nonnegative square at a negative node.

Section 5's no-go is now formal **as a statement about factorizations**, not only about one value:

- `no_squaredNorm_presentation_of_negativeNode`: no assignment of vectors to spectral nodes presents
  the bare anti-resolvent gap as a squared norm, since at a negative node the value would be a
  negative square.
- `no_innerSelf_presentation_of_negativeNode`: the same in the `B*B` form the retired claim proposed.
- `negativeNode_range_nonempty`: the hypotheses are satisfiable, so the no-go is not vacuous.

The pre-existing `suzukiNegativeSpectralNode_bareAntiResolventGap_not_nonneg` is the *scalar* fact
that the gap is negative at such a node; it does not by itself exclude a factorization, which is what
retiring `SUZUKI-RESOLVENT-BIANCHI-SQUARE` requires.

Equation `(8)` and its negative-index consequence are formal too — they were not in the list above,
and the index claim sits behind a "Therefore":

- `suzukiDiagonalKreinForm`: the sewn form of a finite diagonal spectral model.
- `suzukiDiagonalKreinForm_split`: **`(8)`** — the form is its positive-node part plus its
  negative-node part.
- `suzukiDiagonalKreinForm_posPart_nonneg`, `suzukiDiagonalKreinForm_negPart_nonpos`: each part has
  the sign of its nodes, term by term.
- `suzukiDiagonalKreinForm_nonpos_of_allNegative`: an all-negative model has a nonpositive form, so
  the negative index is full.

That the sign is decided term by term is the exact sense in which "the negative index equals the
number of negative nodes": no cancellation between coordinates is possible, so the count is not an
estimate.

`(5)` and `(11)` are formal as *factorizations*, not only as signs:

- `suzukiKreinMagnitude`, `suzukiKreinMagnitude_pos`: the positive magnitude `omega` the sign
  multiplies — the module previously had the sign equivalences `(4)` but no definition of the size.
- `suzukiAffineResolventKreinDefect_eq_sign_mul_magnitude`: **`(5)`**, `D = sgn(t) omega`.
- `neg_kreinDefect_eq_magnitude_of_neg`: **`(11)`**, at a negative node the deficit *is* the
  magnitude, hence strictly positive.

The distinction matters because `(11)`'s debt is measured in `omega`: a sign equivalence says the
debt is positive, but the compensation law `(10)` needs its size.

With the magnitude available, `(8)` is formal exactly as displayed:

- `kreinDefect_eq_magnitude_of_pos`: at a positive node the defect *is* the magnitude.
- `suzukiDiagonalKreinForm_posPart_eq`, `suzukiDiagonalKreinForm_negPart_eq`: each part rewritten in
  magnitudes, the negative one as **minus** the weighted magnitude sum.
- `suzukiDiagonalKreinForm_eq_magnitude_difference`: **`(8)`** — the sewn form is the magnitude sum
  over positive nodes minus the magnitude sum over negative ones.

`suzukiDiagonalKreinForm_negPart_eq` is the coordinate-by-coordinate quantification of the missing
completion contribution that section 7 claims: the debt is not merely positive, it is that specific
weighted sum of magnitudes.

Section 5's surviving claim — "exact positive survivor is signed factorization plus explicit
completion debt" — is formal as well:

- `suzukiDiagonalKreinForm_add_debt_eq_posPart`: adding the debt cancels the negative-node sum
  exactly, leaving the positive part.
- `suzukiDiagonalKreinForm_add_debt_nonneg`: **the positive survivor** — with the debt supplied the
  form is nonnegative.

So the no-go and the survivor are two halves of one computation: the bare form fails precisely by the
debt, and supplying that debt is precisely what restores nonnegativity.

It does not assert `(13)` or RH.

## Log

- 2026-08-01 — section 5's no-go formalized at the level it is stated.  The module already proved the
  scalar fact that the bare anti-resolvent gap is negative at a negative node, but the no-go claims
  more: that **no `B*B` factorization can exist**.  Those differ — a negative value at one point does
  not by itself exclude a factorization until one says the factorization would have to take that
  value.  `no_squaredNorm_presentation_of_negativeNode` and `no_innerSelf_presentation_of_negativeNode`
  state it as the impossibility of a presentation, and `negativeNode_range_nonempty` checks the
  hypothesis class is inhabited so the no-go is not vacuous.  Three new declarations, targeted build
  green, axioms `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — `(8)` and its negative-index consequence formalized.  The card's section 3 derives the
  diagonal form's split and then concludes, behind a "Therefore", that the negative index equals the
  number of negative nodes — the bridge section 7 lists as an advance.  Neither was among the
  module's declarations.  `suzukiDiagonalKreinForm_split` states `(8)`, and the two sign lemmas show
  each part carries the sign of its nodes **term by term**, which is the exact content of the index
  claim: no cancellation between coordinates is possible, so the count is structural rather than
  estimated.  `suzukiDiagonalKreinForm_nonpos_of_allNegative` records the extreme case.  Four new
  declarations, targeted build green, axioms `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — `(5)` and `(11)` formalized as factorizations.  The module carried the sign
  equivalences `(4)` but never defined the magnitude `omega = alpha beta/(|t|(t-alpha)(t-beta))` that
  `(5)` factors the defect through, so `(11)`'s "strictly positive debt" had a sign but no size.
  `suzukiKreinMagnitude` supplies it, `suzukiAffineResolventKreinDefect_eq_sign_mul_magnitude` is
  `(5)`, and `neg_kreinDefect_eq_magnitude_of_neg` is `(11)`.  This matters downstream: the
  compensation law `(10)` bounds the global correction *by* the debt, so it needs the magnitude and
  not merely its positivity.  Three new declarations, targeted build green, axioms
  `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — `(8)` formalized as displayed, in magnitude terms.  With `omega` defined, each node's
  contribution rewrites through the factorization, giving
  `suzukiDiagonalKreinForm_eq_magnitude_difference`: the sewn form is the magnitude sum over positive
  nodes minus the magnitude sum over negative ones.  `suzukiDiagonalKreinForm_negPart_eq` is the
  coordinate-by-coordinate quantification section 7 claims — the completion debt is not merely
  positive but that specific weighted sum, which is what a candidate completion has to match.  Four
  new declarations, targeted build green, axioms `[propext, Classical.choice, Quot.sound]`.
- 2026-08-01 — section 5's surviving claim formalized.  `suzukiDiagonalKreinForm_add_debt_eq_posPart`
  and `suzukiDiagonalKreinForm_add_debt_nonneg` show that adding the quantified debt cancels the
  negative-node sum exactly and leaves a nonnegative form.  The no-go and the survivor are therefore
  two halves of one computation — the bare form fails *precisely* by the debt, and supplying that
  debt is *precisely* what restores nonnegativity — which is the sense in which retiring
  `SUZUKI-RESOLVENT-BIANCHI-SQUARE` does not retire the Suzuki route.  Two new declarations, targeted
  build green, axioms `[propext, Classical.choice, Quot.sound]`.
