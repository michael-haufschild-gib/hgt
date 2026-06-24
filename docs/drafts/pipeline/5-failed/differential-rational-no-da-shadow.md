# Differential-rational no-DA-shadow theorem

- **ID:** differential-rational-no-da-shadow
- **Stage:** 5-failed
- **Type:** SOURCE-KILLED THEOREM / USEFUL LEMMA
- **Source:** `ht-c19-differential-galois-orbit-noncollapse`; entropy draw C19; generic HT structure
- **Statement:** In the differential rational field of one differential indeterminate, every nonconstant
  differential-rational observable is again differentially transcendental over the base.

## Goal

Make the C18/C19 "no hidden finite DA coordinate" idea precise in the clean generic model.

If `Y` is the generic hypertranscendental object over a differential field `K`, then no finite
differential-rational measurement

`R(Y,Y',...,Y^(r))`

can land in a differentially algebraic finite handle unless it was already constant over `K`. Generic HT
therefore has no **DA shadow** visible through finite differential-rational observables. Any nonconstant
observable remains HT.

This does not claim the same for every special HT function. It is the generic / differential-indeterminate
model of hypertranscendence.

## Theorem `[PROVED HERE]`

Let `(K, D)` be a differential field of characteristic `0`, and let

`K<Y> = K(Y_0,Y_1,Y_2,...)`

be the differential rational function field with `D(Y_i)=Y_{i+1}` and `Y=Y_0`.
If

`R in K(Y_0,...,Y_r) \ K`

is nonconstant, then `R` is differentially transcendental over `K`. More strongly, for every `n >= 0`,

`R, D R, ..., D^n R`

are algebraically independent over `K`.

Equivalently:

`K<Y>_DA over K = K`.

There is no nonconstant differentially algebraic element inside the differential-rational field of a
differential indeterminate.

## Proof

Choose `r` minimal such that `R in K(Y_0,...,Y_r)`. Since `R notin K(Y_0,...,Y_{r-1})`, its formal partial
derivative with respect to the highest jet is nonzero:

`partial R / partial Y_r != 0`.

For each `n >= 1`, the derivative `D^n R` belongs to `K(Y_0,...,Y_{r+n})` and depends on the newest jet
`Y_{r+n}` with coefficient `partial R / partial Y_r`. More precisely,

`D^n R = (partial R / partial Y_r) Y_{r+n} + B_n`

where `B_n in K(Y_0,...,Y_{r+n-1})`. This follows by induction from the chain rule: applying `D` shifts the
highest jet one step up and differentiates the previous highest-jet dependence.

We prove algebraic independence of `R,DR,...,D^nR` by induction on `n`.

For `n=0`, if `R` were algebraic over `K`, then as a rational function in the algebraically independent
variables `Y_0,...,Y_r` it would be constant over `K`, contradiction.

Assume `R,DR,...,D^{n-1}R` are algebraically independent over `K`, and suppose

`P(R,DR,...,D^nR)=0`

for some polynomial `P in K[T_0,...,T_n]`. View the left side as a rational function of the newest variable
`Y_{r+n}` over the field `K(Y_0,...,Y_{r+n-1})`. The functions `R,DR,...,D^{n-1}R` do not involve
`Y_{r+n}`, while `D^nR` is affine in `Y_{r+n}` with nonzero coefficient. Hence `D^nR` is transcendental over
`K(Y_0,...,Y_{r+n-1})`, so `P` must be the zero polynomial in its last variable after substituting
`R,...,D^{n-1}R`.

Thus every coefficient gives a polynomial relation among `R,DR,...,D^{n-1}R`. By the induction hypothesis all
coefficients vanish. Hence `P=0`.

So `R,DR,...,D^nR` are algebraically independent for every `n`, and `R` is differentially transcendental over
`K`. ∎

## Consequences

1. **Generic no-shadow principle.** The differential-indeterminate model of HT has no nonconstant finite
   differential-rational observable that collapses to DA.
2. **C18/C19 clean core.** Any proposed finite DA coordinate or algebraic quotient of the generic HT orbit
   must either be base-constant or use structure outside finite differential-rational observation.
3. **Boundary against overclaiming.** This theorem is generic. Special HT functions can have functional,
   difference, or infinite-order structure; the theorem only rules out DA shadows internal to `K<Y>`.

## Source boundary / source kill

The result is elementary differential algebra and is source-killed as a new theorem by ADH, *Asymptotic
Differential Algebra and Model Theory of Transseries*, Lemma 4.1.5:

> If `y` is differentially transcendental over `K` and `z in K<y>`, `z notin K`, then `y` is differentially
> algebraic over `K<z>`, and therefore `z` is differentially transcendental over `K`.

This is exactly the no-DA-shadow principle. Taking `y=Y` and `z=R(Y,...,Y^(r))` gives the card's theorem
immediately.

Standard references also define `K<Y>` as the fraction field of `K{Y}=K[Y,Y',Y'',...]`, and define
differential algebraicity by finite transcendence degree of the generated differential field. The statement
can be read as the special fact:

`R notin K` inside `K<Y>` implies `trdeg_K K<R> = infinity`.

Search for `"differential rational function field" "differential indeterminate"`, `"differential Luroth
theorem"`, and `"nonconstant differential rational function" "differentially transcendental"` also returns
Ritt differential Luroth and modern effective versions. But ADH Lemma 4.1.5 is already the exact source kill.

Final grade: **search/useful lemma**, not a new HGT theorem. The formulation remains useful as vocabulary:
generic HT has no nonconstant finite differential-rational DA shadow. It cannot satisfy the goal's novelty
gate.

## Gates

- [x] 0 -> 1 in-progress: entropy-selected C19; theorem stated precisely; proof core written.
- [x] 1 -> 5 source-killed: ADH Lemma 4.1.5 states the same no-shadow principle.
- [ ] 2 -> 3 formalized: formal algebraic independence of the derivative sequence in a rational function
  field with shift derivation.
- [ ] 3 -> 4 publication-ready: integrate as the C18/C19 generic model theorem for HT.

## Log

- 2026-06-24 — Created by Haiku from entropy draw C19. The original orbit-quotient conjecture was too vague;
  this extracts a provable generic core.
- 2026-06-24 — Source-killed by ADH Lemma 4.1.5. Moved to failed/search. Keep as vocabulary, not as new
  theorem.
