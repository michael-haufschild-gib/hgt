# Prime-depth aliasing modular block law

- **ID:** ULF-PDAMB-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parents:** ULF-SFMH-001, ULF-PBFOF-001, TwoPrimeKummerClockSeparation
- **Status:** [FULLY PROVEN] [LEAN-PROVED] [NOT RH]

## Statement

Let `L2=log 2`, `L3=log 3`. For every `epsilon>0` there are positive integers `m,n` such that

~~~text
0 < |m L2-n L3| < epsilon.                              (PDAMB.1)
~~~

Thus fixed distinct prime labels admit arbitrarily close positive prime-depth Burnol clocks.

Let `K` be a field, let

~~~text
C = [[d,g],[g,e]] tensor I,
U = diag(P,Q),
V = diag(Pi,Qi),
Delta = d e-g^2,
~~~

where `P Pi=I`, `Q Qi=I`, and `Delta!=0`. Then the retained source-site block of
`C^(-1) U C V` is

~~~text
(d e I-g^2 Q Pi)/Delta
 = I + (g^2/Delta)(I-Q Pi).                             (PDAMB.2)
~~~

When `V=U^(-1)`, this is the retained block of source-frame modular holonomy. Therefore its
singular coefficient is the normalized Gram capacity `g^2/(d e-g^2)`, multiplying frame mismatch
`I-QP^(-1)`. This is a multiplicative source/completion law, not a quadratic-form selector.

For zero-clock cubic-Cauchy Burnol columns of rates `x,y>0`, amplitude factors cancel and

~~~text
g^2/(d e-g^2)
 = 64 x^3 y^3 / ((x+y)^6-64x^3y^3),                   (PDAMB.3)

(x+y)^6-64x^3y^3
 = (x-y)^2 ((x+y)^4+4xy(x+y)^2+16x^2y^2).            (PDAMB.4)
~~~

Hence the capacity diverges when positive rates coalesce. For the pairs in (PDAMB.1), the theta
blocks remain the fixed distinct blocks `U_2(a),U_3(a)` for every `a!=0`; their mismatch does not
coalesce with prime-power scale.

Precisely, for every `a!=0` and `M>=0`, there are positive depths `m,n` and a theta-channel entry
`(r,s)` for which

~~~text
M < | capacity_(m,n) (I-U_3(a)U_2(a)^(-1))_(r,s) |.   (PDAMB.5)
~~~

Define source-frame admissibility without Xi data by uniform boundedness of these corrections over
all positive depths and both theta channels. Then

~~~text
PrimeDepthThetaModularAdmissible(a) iff a=0.            (PDAMB.6)
~~~

Indeed, (PDAMB.5) contradicts any bound when `a!=0`; at `a=0`, both theta blocks are identity and
every correction is zero.

## Proof

TwoPrimeKummerClockSeparation proves arbitrarily small nonzero values of
`r log 2+s log 3` for nonzero `(r,s) in Z^2`. Choose the value below both `epsilon` and `log 2`.
Coordinates cannot have the same sign: otherwise positivity of both logarithms and nonvanishing
of the pair give absolute value at least `log 2`. Both coordinates are therefore nonzero and have
opposite signs. Taking their positive absolute values gives (PDAMB.1).

The inverse of the scalar source block is

~~~text
C^(-1)=Delta^(-1)[[e,-g],[-g,d]] tensor I.
~~~

Block multiplication gives the upper-left block of `C^(-1) U C V` as
`Delta^(-1)(de P Pi-g^2 Q Pi)`. Using `P Pi=I` proves the first equality in (PDAMB.2); adding and
subtracting `Delta I` proves the second. Substitution of diagonal and off-diagonal cubic-Cauchy
Gram entries proves (PDAMB.3). Equation (PDAMB.4) is the difference-of-cubes factorization with
`A=(x+y)^2`, `B=4xy`, since `A-B=(x-y)^2`.

## Meaning

Multiplicative source formation identifies prime powers by archimedean decay scale; theta
completion identifies them by prime label. Near-collision of the first without collision of the
second forces finite inner modular transports toward infinity. Finite determinant remains one,
so the only possible invariant is a relative cofinal boundary.

This is not the earlier reflected off-diagonal Euler holonomy. That object is the flat scalar
coboundary `exp(a(lambda_j-lambda_i))`; its uniform boundedness is already equivalent to RH. Here
same-prime depth motion is invisible to theta, the full cubic-Cauchy inverse Gram supplies the
singular coefficient, and fixed cross-prime frame mismatch survives rate coalescence. No divisor
is used in (PDAMB.1)--(PDAMB.5).

## Lean certificate

- `formal/GaloisForLFunctions/HTGeometry/TwoSiteModularHolonomyEscape.lean`
  proves (PDAMB.2)--(PDAMB.4) and quantitative relative-capacity escape.
- `formal/GaloisForLFunctions/RHTower/PrimeDepthAliasingModularEscape.lean`
  proves positive-depth `2/3` collisions, unbounded literal cubic-Cauchy capacity, nonzero
  two-prime theta mismatch for every `a!=0`, and (PDAMB.5)--(PDAMB.6).

Direct source checks and exact target builds pass. Axiom audit reports only `propext`,
`Classical.choice`, and `Quot.sound`.

## Non-claim

This does not prove that Xi completion requires bounded/regular modular transport and does not
identify the cofinal cubic boundary with zero multiplicity. Those are the remaining RH interfaces.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.TwoSiteModularHolonomyEscape`, `GaloisForLFunctions.RHTower.PrimeDepthAliasingModularEscape`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.HTGeometry.TwoSiteModularHolonomyEscape` (16) and
`GaloisForLFunctions.RHTower.PrimeDepthAliasingModularEscape` (14); axiom audit clean.

| Claim | Lean declaration |
|-|-|
| (PDAMB.1) `0 < ∣m log 2 - n log 3∣ < ε`, `m, n > 0` | `exists_two_three_positive_depth_collision` (via `log_two_le_abs_kummerFreq_of_mul_nonneg`) |
| (PDAMB.2) retained block `= (deI - g²QΠ)/Δ = I + (g²/Δ)(I - QΠ)` | `twoSite_modularHolonomy_retained_block`, `twoSite_modularHolonomy_retained_block_eq_one_add` |
| (PDAMB.3) cubic-Cauchy capacity | `cubicCauchyGramCapacity_eq` |
| (PDAMB.4) factorization | `cubicCauchyDenominator_factor`, `cubicCauchyDenominator_pos` |
| capacity diverges as rates coalesce | `cubicCauchyRelativeCapacity_gt`, `cubicCauchyRelativeCapacity_abs_sub_div_add_eq`, `exists_two_three_primeDepth_cubicCauchyCapacity_gt` |
| fixed nonzero `2/3` theta mismatch for `a ≠ 0` | `primeBurnolThetaTwoThreeMismatch_ne_zero`, `exists_primeBurnolThetaTwoThreeMismatch_entry_ne_zero` |
| (PDAMB.5) unbounded correction entry | `exists_two_three_thetaModularEscapeCoefficient_gt` |
| (PDAMB.6) admissible iff `a = 0` | `PrimeDepthThetaModularAdmissible`, `primeDepthThetaModularAdmissible_iff` |

## Log

- 2026-09-28 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
