# The eleven flip is negative at every fixed ratio at least 99/100

- **ID:** bounded-overlap-eleven-flip-negativity
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ../1-in-progress/bounded-overlap-complete-weil-and-prime-flips.md
- **Statement:** For the stated plateau profile and every fixed `c≥99/100`, every sufficiently
  large horizon has an explicit negative atomic test for the complete eleven-flip form.

## Goal

Decide the requested eleven-flip cases at `cZero=1+10⁻¹⁸` and `2`. Both fail eventual
nonnegativity. The zeta positivity problem at ratio two remains open in the parent card.

## Gates

- [x] In progress: the trial and its signed prime-power cancellation were recorded on the parent card.
- [x] Fully proven: the complete argument below has no open mathematical input.
- [x] Formalized: `ElevenFlipAtEveryHorizon.lean` passed `lake --old env lean`; both requested
  theorems have only `propext`, `Classical.choice`, and `Quot.sound` in `#print axioms`.

## Proof

Write `M=integral φ²`, `B=bumpRobin φ 1/M`, and `q=(integral φ)²/M`, with
`φ=transMetzlerProfile`. Set `r=99/100` and

`F(n)=1-2*1_(11|n)+2*1_(121|n)`.

Then `F²=1`, its mean is `a=101/121`, and its Ramanujan expansion has conductors
`1,11,121`. The squared normalized coefficients sum to one, and their total prime
excitation is `4*log(11)/11`. The actual complete untwisted form therefore satisfies

`W(atomicTest N (F/sqrt) (atomDilate φ (r/N))) / ((r/N)*log(N)*M)
  → B-log(2*pi*r)+4*log(11)/11+r*q*a²`.

At separated widths the twisted-minus-untwisted form is exactly its signed prime
correction; Gamma and both poles are retained. The first eleven-power correlation is
`F(n)*F(11*n)=-1+2*1_(121|n)`. Its leading negative contribution cancels the prime
excitation. Bounding the remaining odd powers gives the normalized upper limit

`B-log(2*pi*r)+r*q*a²
  +4*log(11)*(2/11³+1/(11²*10))`.

The proved bounds `B≤21/20`, `q≤1`, `log(2*pi)>9/5`, `-log(r)≤1/99`,
`a²<7/10`, and the last tail term `<1/40` make this strictly negative.
Thus the actual complete twisted energy is eventually negative at `r`.

The finite packet limit also holds along any horizons tending to infinity and ratios
tending to `r`. For fixed `c≥r`, put `H_N=floor((r/c)*N)` and extend `F(n)/sqrt(n)`
by zero above `H_N`. Its effective ratio is `r_N=c*H_N/N→r`, and
`r_N/H_N=c/N` once `H_N>0`. Exact zero padding identifies the tests, proving eventual
negativity at `c`. This applies to both requested ratios.

## Lean declarations

All declarations below lie in
`GaloisForLFunctions.TransMetzlerWeilPositivity.BoundedOverlap`.

- `eventually_elevenFlip_negative_of_ratio`
- `eventually_elevenFlip_negative_two`
- `eventually_elevenFlip_negative_cZero`
- `eventually_elevenFlip_negative_variable`
- `primeSquareTrial_complete_correction`
- `primeSquareTrial_complete_le`
- `elevenTrialUpperMargin_neg`

The result is imported by `GaloisForLFunctions/TransMetzlerWeilPositivity.lean`.
The complete theorem has no RH, prime-distribution, or missing analytic premise.

## Consequence

Both requested ratios fail eventual nonnegativity. The prime-matrix sign conjugacy
does not imply invisibility of the complete form:
the unchanged Gamma and pole terms must also be included.
