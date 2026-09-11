# HB: uniform original spin-two delay transport

Stage: 3-formalized for uniform original finite-delay bulk domination. Complete physical-current cancellation and RH remain unproved. Frontier map read only.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hardest target is complete physical-current cancellation with independent SS/SV/VV amplitudes. The [proved full finite delay transfer](hb-full-spin-two-delay-transfer.md) leaves its literal bulk under radial and angular integrals. This attack proves uniform bounds through the characteristic corner and towards the horizon, needed to transport that bulk and compare the physical currents.

## Analytical conjecture loop

1. Normalize the actual geometric coefficients. With `t=h-x+y`, `d=x-y_e`, `C=cosh t`, `S=sinh t`, define `r=(C-cosh d)/S` and `b=C(C-cosh d)/S^2`. Causality gives `0<=r<=1`, `0<=b<=1`, `0<=3b^2-r^2<=2`. The exact original primitive factorization turns the bulk into `U(Z)[r^2 W''-3rb W'+(3b^2-r^2)W]`. These coefficients have uniform bounds despite the nonzero diagonal bulk contact.
2. Bound the original invariant uniformly in radii at finite delay. Set `u=-tanh x`, `w=-tanh y` for physical `x,y<=0`. Direct expansion gives `Z_e=P exp(h)+Q exp(-h)+(if image then -u*w else u*w)`, where `P=(1+u)(1-w)/2`, `Q=(1-u)(1+w)/2`, `P+Q=1-u*w`. Since `0<=u,w<=1`, `h>=0`, one gets `Z_e<=exp(h)`. Causality supplies the lower bound one. Thus `h<=V` confines every native argument to `[1,exp(V)]` independently of both radii.
3. Use the actual native moment and source-clock continuity on the resulting compact sets to produce uniform bounds. Then transport the finite radial domain and compare with the original lift/source-contact/angular Green currents. No current is assumed zero; an estimate alone does not establish physical extinction.

The geometric bound, finite invariant confinement, original source moments, original clock jets and final uniform bulk bound are now proved in Lean. Physical boundary-limit transport and cancellation remain open. No numerical computation is used.

## Original clock derivative closure

The compact-integral search located `HTGeometry.hasDerivAt_parametric_intervalIntegral` in `ClockParametricDerivative.lean`. Its jointly continuous integrand/derivative form supplies exactly the needed differentiation. To use it without changing the clock, multiply each actual profile by `1+u`:

```
G_s(u,v)=(1+u) g_s(u,v)
 =exp(2sv)[eta_s(1+u) chi(v)-s(s-1)u(3+(2s+3)u)chi'(v)/2].
```

The displayed right side is globally smooth in `u,v`. In the fixed integration variable `t in [0,1]`, let `K(u,w,h,t)=G_s(u,h+(V-h)t)G_(-s-3)(w,(V-h)t)` and `I_j=integral_0^1 partial_h^j K dt`. Compact differentiation and the actual moving interval give

```
(1+u)(1+w) W      =(V-h) I_0,
(1+u)(1+w) W'     =-I_0+(V-h) I_1,
(1+u)(1+w) W''    =-2 I_1+(V-h) I_2.
```

Every numerator is jointly continuous in `(u,w,h)`. On `[0,1]^2 x [0,V]`, the denominator is positive, so the three original jets have a common compact bound. Combine this with `Z in [1,exp(V)]`, the exact source-moment bound and the geometric coefficients to derive

```
exists C>0, forall image, x,y<=0, a_image_or_direct<=h<=V,
  norm(delayBulk(image,q,branch,x,y,V,X,k,h)) <= C.
```

The constant depends on the literal zero copy, branch, angular base point and finite cutoff. It is independent of both radii and causal delay in that window. No uniform infinite-time or global cusp bound is asserted. The nonzero limiting diagonal bulk contact remains retained; joint continuity at that corner is unnecessary for this estimate.

## Search applicability

Own deep queries: broad OR `removable domination`; `bound integral source moments uniformly on compact parameter sets`; the single term `invariant` in the BM family; and `smooth dependence of a compact parameter integral under differentiation`. Candidate lemmas, source arguments, methods, proof ideas and ingredient sets were inspected. Coverage was partial: 56,480 files, 390 stale/pending source files, incomplete semantic coverage and mostly source-only compiler metadata. Proposed reflection, neutral-moment and modular-invariance groups did not supply the required original radial bound. The existing native quadratic primitive bound supplies the source moment estimate, and the public compact parametric derivative theorem supplies both clock derivatives.

Own broad arXiv words were symmetrizer and transversality, with 2026 filters. [Li, How much randomness is needed to symmetrize a random variable?](https://arxiv.org/abs/2607.17576) (July 2026) converts exponential convolution into a differential constraint. Its probability positivity is unavailable for the complex bilinear clock; no entropy or positivity conclusion was imported. [Huang, Song and Chen, Symplectic Transversality and Endpoint Green Estimates for Finite-Horizon Pontryagin Systems](https://arxiv.org/abs/2606.17762) (June 2026) retains endpoint corrections in weighted Green estimates; its endpoint inverse assumptions have not been established for HB. [Ross, Transversality Conditions for Boundary Constraints Defined by Differential Equations](https://arxiv.org/abs/2609.04084) (September 2026; abstract inspected) distinguishes clock coordination in endpoint conditions. None is a Lean proof premise.

## Lean certificate

[ThetaCuspHawkingBMSpinTwoUniformDelay](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSpinTwoUniformDelay.lean), namespace `RHTower.D4BMSpinTwoUniformDelay`, contains the following eleven uniform-bound theorems:

- `causal_coefficient_bounds`: all three original geometric coefficients, on the entire closed causal cone.
- `delay_bulk_normalized`, `delay_bulk_bound`: equality with the literal transferred bulk and its coefficient estimate.
- `delay_invariant_formula`, `delay_invariant_bounds`, `delay_invariant_finite_range`: exact compact-radius formula and uniform interval `[1,exp(V)]`.
- `source_moments_bounded`, `finite_delay_source_moments`: both original moments, using the previously proved primitive zero orders and their actual characteristic values.
- `finite_delay_bulk_clock_bound`: uniform source/geometric bound with the original clock jets retained.
- `finite_clock_jet_bound`: joint compact control of the actual clock and both delay derivatives.
- `finite_delay_bulk_uniform`: one positive constant for both full physical radial domains and every causal delay in the fixed finite window.

No boundary vanishing, smoothness, integrability, derivative bound or cancellation is supplied as a theorem premise. The physical radius and finite window restrictions are intrinsic domain types. The old diagonal contact is not redefined or forced to vanish; the proof controls the original bulk without requiring joint continuity at that corner.

Scratch checking passed. The exact isolated new leaf built without warnings in 72 seconds, three jobs, using 4,137 cached own modules, 20,538 artifact links and twelve dependency path packages. No existing leaf, dependency or umbrella build ran. Only the eleven new public theorems were axiom-audited in a separate scratch file; each reported only `propext`, `Classical.choice`, and `Quot.sound`. Verified source and five artifacts were installed byte-identically. The new umbrella import was added once without building it. Indexing completed with one changed file; the generated API includes the clock-jet and full uniform-bulk theorems. Formal lint passed with existing large-file warnings, and fifteen local document links passed. All owned handles reached terminal status and the owned Lean/Lake process check was clear. Scratch, audit and search-result files were removed. The frontier map and universal ledger were not edited. No mathematical computation ran.

## Formalized original horizon transport

The [original full-source horizon theorem](hb-original-delay-horizon.md) now proves the invariant and actual clock-jet limits, the exact branch-specific horizon bulk, transport through each finite causal interval, and the limit of the original signed native spin-two source action. At fixed finite source radius, the actual bulk has the limiting clock factor `(partial_h-1)(partial_h-2)`; both causal starts and all onset derivatives are retained.

The uniform bound above supplies the derived majorant for that transport. Integrating against the complete physical radial/angular measure and identifying the remaining lift, source-contact, angular and temporal currents remain open. No unique joint two-radius horizon limit or current cancellation is asserted.
