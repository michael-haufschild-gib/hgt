# HB: positive-delay characteristic source/current balance

Status: analytical conjecture/proof loop. Complete physical extinction and RH remain unproved. Frontier map read only.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hardest target remains the complete physical current cancellation. The [zero-delay radial contact](hb-zero-delay-current-match.md) is now explicit. This card attacks the remaining positive-delay direct and image contacts and their comparison with the physical cross-currents in the [finite-clock transfer](hb-reduced-source-clock-transfer.md).

## Conjecture: joint characteristic transport assembles the remaining contacts

For a positive delay `h`, put `beta=tanh(h/2)` and `W_h(u)=(u+beta)/(1+beta*u)`. The direct characteristic is `w=W_h(u)`, with `0<=u<=1`; the image characteristic is `w=beta`. Both use `dw/dh=(1-w²)/2`. Their original native-kernel normal derivatives are respectively `w-u` and `u+w`.

Use the actual source weights `p_s=u(1+u)^(2s)`, `B_s=p_s b_s`, `b_s=2k_s u(3+delta*u)/(1+u)`, with `t=-s-3`. Their primitives `I_s(u)=integral_0^u p_s`, `J_s(u)=2k_s u³(1+u)^(2s)`, and `K_s(u)=integral_0^u xB_s(x)` are the original functions in `RHTower.D4BMZeroDelayCurrent`.

At a characteristic, the corrected source bracket has zeroth-jet density

```
exp(2s h)*[(alpha_s p_s(u)B_t(w)-alpha_t B_s(u)p_t(w))*J_V(h)
 +B_s(u)B_t(w)*((2s+6)*J_V(h)-J_V'(h)-E_V(h))]
```

and first-jet density

```
exp(2s h)*B_s(u)B_t(w)*Z_h*J_V(h)/2.
```

Each is multiplied by `(1-w²)/2` when the original `w` integral is written in `h`. Take direct minus image, then subtract the reversed ordered branch. The actual outer angular `RQ` and `R Delta Q`, the physical source normalization and all other current faces remain attached.

The candidate mechanism is a bilinear identity for the transported source primitives on this complete direct-minus-image domain. It must produce the physical cross-current traces, not an independently assigned zero.

## One-coordinate primitive test

The earlier candidate of a primitive `r0(q)J_V(h(q))+r1(q)J_V'(h(q))` along one optical radial coordinate does not close by itself. On the direct sheet, `u=q-d`, `w=(q-L)/L`, `a=d-1`, and `h'= -a/(q(q-a))`. If the density coefficients of `J,J',J''` are `D0,D1,-D2`, the highest two jets force `r1=-D2/h'` and `r0=(D1-r1')/h'`. A residual `D0-r0'` remains. At the actual `u=0` edge its first-jet compatibility involves `alpha_s-12k_s*d/(d-1)`, so dropping that residual would lose boundary data. No no-go theorem or route retirement is claimed: the joint characteristic/physical-current problem is the retained target.

## Verification scope

The displayed characteristic transport and source bracket are analytical identities under inspection. No new Lean result is claimed by this card. Existing zero-delay theorems are reused without rebuilding or re-auditing them.
