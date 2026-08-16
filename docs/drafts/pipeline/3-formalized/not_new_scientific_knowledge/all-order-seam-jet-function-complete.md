# All-Order Seam Jet Is Function-Complete

- **ID:** all-order-seam-jet-function-complete
- **Stage:** 3-formalized
- **Type:** THEOREM (paper) / landscape-proof guardrail
- **Source:** `seam-log-hankel-rh-equivalence.md`;
  `shifted-reciprocal-moments-determine-divisor.md`;
  `rh-landscape-proof-gate.md`
- **Statement:** For an even entire function nonzero at the seam centre, the
  full seam-log jet determines the function up to its central scalar, hence
  determines the zero divisor. Therefore an all-order seam-log input is not a
  softer source landscape unless those coefficients are produced from
  independent Euler/Gamma/functional-equation data.

## Setup

Let `F(w)` be an even entire function with `F(0) != 0`. Let `Phi` be the
entire function satisfying

`F(w)=Phi(w^2)`.

Define the local seam-log germ

`L(z)=log(Phi(z)/Phi(0))`

near `z=0`, using the branch with `L(0)=0`. Write

`L(z)=sum_{k>=1} ell_k z^k`

as a germ.

## Theorem

The scalar `F(0)` together with the full coefficient sequence `(ell_k)_{k>=1}`
determines `F`.

If the scalar is omitted, `(ell_k)_{k>=1}` determines `F` up to multiplication
by a nonzero constant and therefore determines its zero divisor with
multiplicity.

## Proof

The coefficients `(ell_k)` determine the formal Taylor series of `L` at `0`.
Exponentiating formal power series determines the Taylor series

`exp(L(z)) = Phi(z)/Phi(0)`.

Thus two candidates `Phi_1` and `Phi_2` with the same scalar and the same
seam-log coefficients have the same Taylor series at `0`. Since both are
entire, the identity theorem gives

`Phi_1=Phi_2`

on the whole plane. Hence

`F_1(w)=Phi_1(w^2)=Phi_2(w^2)=F_2(w)`.

If the scalar is not specified, the same argument gives

`Phi_1/Phi_1(0)=Phi_2/Phi_2(0)`,

so the functions differ only by a nonzero multiplicative constant. Such a
constant does not change the zero divisor.

## Consequence For The RH Landscape Route

The canonical seam-log coefficients of

`Xi(w)=xi(1/2+w)`

are valid source coordinates only if a proof constructs them from the completed
Euler/Gamma/functional-equation source, or constructs an equivalent completed
boundary object, before using zero localization.

They are not by themselves weaker than the completed function. As all-order
data, they determine `Xi` up to scale and therefore determine the reciprocal
zero divisor. Proving positivity from the all-order seam-log jet after it is
given as data is movement inside a complete chart of the same object, not a
landscape selection theorem.

The non-mirror theorem still has to explain why the source-produced seam-log
germ lands in the shifted Stieltjes/Markov cone. The extraction of the germ is
not that positivity theorem.

## Novelty Status

The mathematical mechanism is classical: formal exponentiation plus the identity
theorem for entire functions. This card does not claim a new analytic theorem.

Its significance is route hygiene. It identifies a source-coordinate input that
is already function-complete, so it blocks a proof script that would receive the
all-order seam-log jet and then claim to have selected the zero divisor.

## Theatre Test

For any proof that starts from the all-order seam-log jet:

1. Was the jet derived from independent Euler/Gamma/FE data, or was it read from
   the completed function?
2. Does the argument use the full all-order jet as input and then infer the
   zero divisor's positivity?
3. If yes, the proof has used function-complete data. The missing step is the
   source theorem producing the positivity, not the seam-log coordinate change.

## Gates

- [x] 0 -> 1 in-progress: all-order seam-log coordinate risk isolated.
- [x] 1 -> 2 fully-proven: formal power series and identity-theorem proof
  written.
- [x] 2 -> 3 formalized: `RHTower/SeamJetFunctionComplete.lean`.

## Log

- 2026-06-24 -- Codex: created under the active RH continuation using the
  minimal-counterexample move. The card blocks the route that treats an
  all-order seam-log jet as a source landscape merely because it is centered at
  the seam.

## 2026-08-16 Lean closure

`RHTower/SeamJetFunctionComplete.lean` proves the card unconditionally, in the analytic form rather
than through formal power series.

A seam-log germ for an entire `Phi` with `Phi 0 != 0` is rendered exactly as the card defines it:
a function `L` with `exp (L z) = Phi z / Phi 0` near the origin.

- `eventuallyEq_of_iteratedDeriv_eq`: two holomorphic germs at the origin with the same Taylor
  coefficients agree near the origin.  This is the card's "the coefficients `(ell_k)` determine the
  formal Taylor series of `L`", obtained from `Complex.taylorSeries_eq_on_ball'` instead of a formal
  power-series development.
- `seamJet_function_complete`: equal seam-log germs give `Phi_1 / Phi_1(0) = Phi_2 / Phi_2(0)` — the
  card's exponentiation step is the pointwise identity `exp L_1 = exp L_2` near `0`, and the
  extension to the whole plane is the identity theorem
  (`AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq`, packaged as `entire_eq_of_eventuallyEq`).
- `seamJet_proportional`: `Phi_1 = (Phi_1(0)/Phi_2(0)) Phi_2`, the "up to a nonzero constant" clause.
- `seamJet_zero_set_eq`: the zero set — hence the zero divisor — is determined.
- `seamJet_even_function_complete`: with the central scalar prescribed, the even function
  `F w = Phi (w^2)` itself is determined.

`entire_eq_of_iteratedDeriv_eq` records the same completeness for entire functions directly from
their Taylor coefficients at the origin.  Axioms: `propext`, `Classical.choice`, `Quot.sound`.
