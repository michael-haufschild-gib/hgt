# Suzuki affine resolvent Krein defect and sharp weld debt

- **ID:** `suzuki-affine-resolvent-krein-defect`
- **Stage:** 2 — fully proved on paper
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

It does not assert `(13)` or RH.
