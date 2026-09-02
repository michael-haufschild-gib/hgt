# Pre-divisor Meyer--Koszul completion-escape law

- **ID:** `ULF-MKCE-1`
- **Stage:** 3-formalized
- **Type:** unconditional comparison-defect construction and Xi specialization law
- **Lean:** `GaloisForLFunctions.HTGeometry.PreDivisorMeyerKoszulCompletionEscape`; verified

## 1. Higher-law interpretation

Corpus does not exhibit one completion.  It exhibits an injective strong-source realization

`j : S -> H`

from all-weight Meyer cochains into Hilbert `L2`, together with prime Koszul operators `d_s` on
`S` and `D_s` on `H` satisfying `j d_s = D_s j` for every spectral parameter `s`, before divisor
specialization.  Hilbert inversion can therefore lose source provenance even though forward
transport preserves it.

The canonical defect is not a chosen inverse or fitted observable.  It is the quotient

`E_s(p) = D_s(p)^(-1)(jS) / jS`.

It measures vectors created by analytic completion whose forward Koszul image returns to the
arithmetic/source image.  This is the first literal `complete-then-invert` versus
`invert-in-source` comparison object already forced by corpus maps.

## 2. Construction

For a prime `p` and arbitrary `s in C`, define

`D_s(p) = U_(log p) - delta_s(p) I`

on `H=L2(R)`, where `delta_s(p)=p^(1/2-s)`, and

`d_s(p) = T_(-log p) - delta_s(p) I`

on strong Meyer source `S`.  Existing half-density intertwining gives

`j d_s(p) = D_s(p) j`.

Let `R=jS`, `P_s(p)=D_s(p)^(-1)(R)`, and

`E_s(p)=P_s(p)/R`, realized as image of `P_s(p)` in `H/R`.

Intertwining proves `R <= P_s(p)`, so quotient is canonical for every `s`; no zero set or RH
hypothesis enters its definition.

## 3. Exact vanishing theorem

If `D_s(p)` is bijective, then

`E_s(p)=0`

if and only if its analytic inverse preserves strong-source provenance, equivalently:

for every `y in R`, there exists `x in R` with `D_s(p)x=y`.

Because `j` is injective and `j d_s=D_s j`, this is further equivalent to surjectivity of the
source Koszul coordinate `d_s(p)`.  Thus escape vanishing and source-cokernel vanishing are exactly
the same law whenever analytic coordinate is invertible.

### Proof

If `E_s(p)=0`, then `P_s(p)<=R`.  Given `y in R`, bijectivity supplies the unique `x in H` with
`D_s(p)x=y`.  Since `y in R`, `x in P_s(p)`, hence `x in R`.

Conversely assume inverse preservation.  If `x in P_s(p)`, then `D_s(p)x in R`; preservation gives
`z in R` with `D_s(p)z=D_s(p)x`.  Injectivity gives `z=x`, hence `x in R`.  Thus `P_s(p)<=R` and the
quotient vanishes.  QED.

For final equivalence, source surjectivity sends `g in S` to `d_s(f)=g`; intertwining sends this to
`D_s(jf)=jg`, proving inverse preservation.  Conversely inverse preservation applied to `jg`
produces `jf in R` with `D_s(jf)=jg`; intertwining and injectivity of `j` give `d_s(f)=g`.  QED.

## 4. Xi specialization law

At every Xi divisor `rho` and prime `p`, if `Re rho != 1/2`, then `D_rho(p)` is a unit.  Existing
Meyer descent proves that its inverse cannot preserve strong-source image.  By the exact vanishing
theorem,

`E_rho(p) != 0`.

Equivalently, `E_rho(p)=0` implies `Re rho=1/2`.  This is a closed unconditional theorem quantified
over every Xi divisor and every prime.

## 5. What this proves and what it does not

This proves a pre-divisor carrier and exact specialization law.  It does **not** prove RH: no
source law yet forces `E_rho(p)=0`.  Merely renaming the existing preservation endpoint as a
quotient would be theatre.

The gain is structural and falsifiable.  Any completion-index mechanism claiming to close RH must
now construct a source-native formation map into this exact quotient and prove its Xi-specialized
class vanishes.  If proposed finite formation remains uniformly exact after Hilbert completion,
the quotient is zero trivially and cannot encode horizontal grade; if it merely assumes inverse
preservation, it has restated the endpoint.  Surviving mechanism must instead identify `E_s(p)` as
an independently controlled boundary/transgression class.

## 6. Exact RH closure obligation

Required next law:

1. lift prime-packet Frobenius--Verschiebung formation to the pre-divisor Meyer square;
2. map its derived completion boundary canonically onto `E_s(p)`;
3. prove integral/perfect formation makes that boundary class vanish at every Xi specialization;
4. conclude `E_rho(p)=0`, hence `Re rho=1/2` for every Xi divisor and RH.

Steps 1--3 are open.  Step 4 is now formally closed.

## Log

- 2026-09-02 -- all-`s` comparison quotient constructed; vanishing classified under analytic
  invertibility; off-line Xi specialization proved nonzero.
