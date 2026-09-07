# CCM-FU: source-local two-prime blocks

- **Stage:** 1-in-progress
- **Parent:** [initial two-prime ceiling](ccm-fu-initial-small-subset-ceiling.md)
- **Frozen question:** Does every original two-prime cofactor block contract? Is `K_p(N)<=2 K_1(N)` true for every prime p and natural cutoff N, providing a sufficient source comparison?
- **Method:** Recover original signed source coefficients from all saved subset energies using the already checked late-edge head reconstruction and finite subset inversion. Read the data only; regenerate no channels or greedy paths. Use the original absolute energy tolerance. Numerical results guide an independent analytic proof and are never Lean premises.

The block statement is sufficient for the two-prime ceiling after summing over squarefree cofactors. A failed block would require compensation between cofactors and would not refute the aggregate two-prime statement. Any obstruction must retain an exact positive classification or replacement bound before this sufficient approach is retired.

## Current evidence and sharper source question

All 6562 saved cofactor blocks pass, covering all 627 prime pairs through32; maximum aggregate energy reconstruction error is about 3.71e-14. These finite checks do not settle the all-cutoff assertion.

A sufficient arithmetic comparison is `K_(pd)(M)<=2 K_d(M)` for every prime p and positive d. For a block a,b,c,e at d,pd,qd,pqd, it gives `b<=2a`, `c<=2a`, and `e<=2b,2c`; these comparisons imply `ae+bc<=(a+e)(b+c)` and hence the desired square bound. The stored-data diagnostic tests that dilation comparison on every saved squarefree source pair. This is a sufficient comparison, not an established property of unsigned positivity.

All 417 saved active source pairs satisfy that sufficient comparison. The largest observed child/parent ratio is about 1.31933, at M=7,p=2,d=1. The available analytic upper and lower constants do not prove a factor of two.

The bounded screen extends only the first-prime questions to M=33..1024: every actual squarefree prime pair is tested against the factor-two comparison, and every first-prime geometric reserve against its original diagonal. The one-dimensional divisor-defect and unit-clock table is computed and saved once, and every dilated channel is obtained by exact clipped interpolation. No subset enumeration or greedy search is repeated. Each original diagonal is checked against the already saved greedy data. This extended range is numerical guidance only.

That bounded screen passes all 617453 source pairs and all 95747 first-prime reserve states. Every original diagonal agrees with the saved greedy data. The maximum observed dilation ratio is again about 1.31933, now at M=371,p=2,d=53, an exact dilation of the cutoff-seven shape. The table and all first-prime states are saved; no repeat run is needed without a different question.

Universal first-prime geometric certification is nevertheless
[false analytically](../5-failed/ccm-fu-universal-first-prime-certificate.md):
at M=12p it fails for every sufficiently large prime p, while ordinary
first-prime energy still contracts. This rejects that sufficient reserve
estimate, not the factor-two channel comparison or the actual two-prime
energy ceiling. Their all-cutoff proofs remain open.

## Exact paper reduction

For nonnegative a,b,c,e satisfying `b,c<=2a` and `e<=2b,2c`, put x=b+c. Then `e<=x` and `bc<=ax`. If a<=x, the needed cross reserve is `ax-bc+e(x-a)>=0`. If x<=a, it is `(a-x)(x-e)+x^2-bc>=0`. Thus `(a-b-c+e)^2<=a^2+b^2+c^2+e^2`.

The factor two is sharp for this local comparison: for any kappa>2, the nonnegative block `(1,kappa,kappa,0)` meets the factor-kappa edge bounds but has positive square excess `2 kappa (kappa-2)`. This is a sharp sufficient-class classification, not an obstruction to the actual source.

Exact clipped interpolation has the same nonnegative weights in parent and child channels. Therefore `K_p(N)<=kappa K_1(N)` at both adjacent quotient cutoffs implies `K_(pd)(M)<=kappa K_d(M)` at arbitrary M,d. The universal dilation comparison is equivalent to the unit-cofactor comparison. Every original oriented fibre equals K at the product of its retained prime label. Splitting the original prime cube into all four-coordinate blocks then transfers a proved unit factor-two comparison to every original two-prime ceiling.

The [exact reduction and sharp class boundary](../3-formalized/ccm-fu-two-prime-local-criterion.md) are closed in Lean. The literal source satisfies the unconditional alternative: either its two-prime energy meets the original ceiling, or one of those primes r has `2 K_1(N)<K_r(N)` at an active cutoff `r<N<=M`. The reduction includes every cofactor and clipped endpoint. The universal unit comparison is the missing arithmetic theorem; the alternative does not eliminate a unit-channel failure. It controls two initial mergers only; no complete growing schedule or SD1 conclusion follows yet.

## Current analytic source bounds

The [second-centered hyperbola certificate](../3-formalized/ccm-fu-second-centered-hyperbola.md) retains the first modular primitive's exact mean and its moving terminal residue. A periodic cubic primitive bounds the remaining half-order error by `1/(48d)` per modulus, so summing all square births costs only a harmonic error. The actual centered Abel term lies between square-root coefficients `-5/96` and `-1/48`, up to logarithmic error, and tends to negative infinity.

The [exact smooth mean and bounded-quotient theorem](../3-formalized/ccm-fu-smooth-square-block-mean.md) identifies `a=log(2*pi)/2-gamma-1/6>1/6` and proves `|smoothAbel(M)-a sqrt(M)|<=9log(M+1)+25+|a|`. The complete unit channel has lower coefficient `a-5/48` and upper coefficient `a-1/24`, up to logarithmic error. The strict factor-two margin gives one universal threshold T such that `M/p>=T` implies `K_p(M)<=2K_1(M)` for every positive p, including clipped endpoints. Every original two-prime ceiling failure must therefore have a unit witness at `r<N<=M` with `N/r<T`.

The [large first-prime orientation theorem](../3-formalized/ccm-fu-large-prime-orientation.md) proves `K_(pd)(M)<=K_d(M)` for every cofactor whenever M is above one common threshold and `M<=5p`. Analytic endpoint ceilings through5 and the exact parent lower bound cover all clipped phases. Every retained sign survives this first prime, so every distinct second prime contracts energy and meets the original ceiling. Hence any two-prime ceiling failure at large parent cutoffs requires both primes below M/5. Unit factor-two failures there must lie in `5<=M/p<T`.

The [signed terminal modular mean](../3-formalized/ccm-fu-terminal-modular-mean.md) sharpens the unit coefficient band to the exact limit `c=log(2*pi)/2-gamma-1/4`. The complete terminal residue is `o(M)`, and the centered hyperbola has coefficient `-1/24`. One common quotient threshold gives `|K_d(M)-c*sqrt(M)|<=epsilon*sqrt(M)` for every positive dilation d with sufficiently large `M/d`, including clipped endpoints. The actual unit coefficient is therefore determined; no source coefficient or computed value is assumed.

The [remaining middle quotient profiles](ccm-fu-bounded-quotient-profiles.md), finite parent regime and all-cutoff ceiling remain open. A saved-vector diagnostic supports the candidate global `K_1(N)<=sqrt(N)/8` bound through1024 but rejects the sufficient prefix envelope at 16 cutoffs. The exact limit above does not establish that global ceiling. None of those data is a Lean premise and no channels were regenerated.
