# HB: source-derived upper trace of the native nonconstant cusp current

- **ID:** HB-QNCT
- **Stage:** 3-formalized
- **Type:** FORMALIZED native bilinear trace; complete physical-action extinction remains open
- **Parent:** [HB-QNCE](../3-formalized/hb-native-weighted-cusp-energy.md)
- **Route:** Literal theta source → Xi occurrence → retained spin two → physical causal/left-QNM action → common Hawking-clock extinction → RH

## Hard obstacle

The previous turn derived weighted integrability of the original native
nonconstant gradient energy. This controls current products in integral norm
but does not by itself give an upper cusp trace. The present target is to
produce that trace from the original forced equation, with both branches and
all signed forcing terms retained.

For the two original responses R_a,R_b, let M denote the period-one mean and
Cov(F,G)=M(FG)-M(F)M(G), a complex bilinear covariance without conjugation.
Define J_ab=Cov(∂y R_a,R_b). This is exactly the remainder after subtracting
the native mean product from the original bilinear vertical current.

The source PDE and cancellation of periodic horizontal side flux give

```
J_ab' = Cov(∂y R_a,∂y R_b) + Cov(∂x R_a,∂x R_b)
      + α_a/y² Cov(R_a,R_b) + 1/y² Cov(F_a,R_b).
```

Here F_a is the original complete cusp-subtracted forcing. No homogeneous
Maass equation, conjugacy of branches or RH consequence may replace this
forced identity.

## Conjecture → proof strategy

1. Prove the exact covariance identity with finite integrals. Keep the native
   mean current explicitly; it need not vanish.
2. The inequality 2|uv|≤|u|²+|v|² bounds covariance by centered slice energies.
   Independent Parseval identifies those centered energies with the proved
   nonconstant mass/gradient sums. Original forcing Parseval bounds its loss.
3. Source-weighted energy and mass admission then give weighted L1 control
   of both J_ab and J_ab'. Differentiating a polynomial weight introduces
   only another admitted current term.
4. Apply the installed improper-integral theorem: a function and its derivative
   integrable on a half-line force its limit to zero. This supplies the trace,
   rather than assuming one or inferring it from L1 alone.
5. Restore the exact native mean current and form the original coefficient
   combination β J_true,false − α J_false,true. Then transfer to the complete
   physical tested current, retaining theta/test derivatives, source contacts,
   retained spin two and other independent nonlinear channels.

The complete fixed-clock extinction theorem is still open. Angular tail
cutoffs are auxiliary estimates; the physical Hawking clock remains unchanged.

## Search applicability

Deep current/derivative search completed its stages but reported unavailable
semantic coverage; compiler coverage is predominantly source-only. Candidate,
method/source and ingredient views were inspected. The suggested Schwartz
field and homogeneous Maass-current theorems have unproved or incompatible
source premises here. They cannot produce native forced derivative admission.
A separate variance search returned finite deck-average results, not the
period-one complex covariance needed here. Direct installed mathlib
`tendsto_zero_of_hasDerivAt_of_integrableOn_Ioi` matches the final trace step;
its two integrability premises must be proved from this original source.

Broad arXiv virial/trace/dissipation searches returned recent observational
astrophysics and numerical cloud models, with no applicable source-current
cancellation. No source conclusion is inferred from those results.

## Source proof and optimization, 12 September 2026

The paper proof and Lean proof are dependency-closed for the native bilinear
remainder. The assembled scratch and exact isolated leaf audit passed with
default resource settings and no diagnostics.

For period-one means define U_b as the complete nonconstant mass and E_b as
its admitted first-gradient energy. Finite-cell centering and the existing
Parseval identities give exactly

```
Var(R_b) = U_b,
2 Var(partial_y R_b) + Var(partial_x R_b) = E_b.
```

Thus no new interchange of an infinite sum and a height integral is needed
for the covariance estimate. The nonzero integer frequency gap also gives
U_b <= E_b. With Fmass_a the complete original forcing slice divided by y^4,
the original forced identity above implies, for y>1,

```
|J_ab| <= E_a + E_b,
|J_ab'| <= (|alpha_a|+2)(E_a+E_b) + y^4 Fmass_a.
```

These are estimates of the complex bilinear current, with no conjugacy
assumption on the two branches. Positivity is used only in bounding norms.
The signed forcing covariance remains present in the derivative identity.

For each natural N, original source admission supplies a common cusp tail on
which y^(2(N+1))(E_a+E_b) is integrable. The forcing estimate at index N+2
bounds y^N y^4 Fmass_a by C/y^2. Since both N and N-1 are at most 2(N+1),
this proves integrability of

```
y^N J_ab,
N y^(N-1) J_ab + y^N J_ab'.
```

The installed improper-integral theorem then forces y^N J_ab -> 0. This uses
both integrabilities; an L1-only trace inference is explicitly rejected.

Actual modular translation also preserves the vertical derivative, by
differentiating the original period identity locally in positive height.
It therefore transports the product integral from [0,1] to the original
[-1/2,1/2] cusp cell. The zero Fourier coefficient and its derivative coincide
there with the original native response mean. Consequently the retained
native cusp flux satisfies

```
M_original[(partial_y R_a) R_b]
  = (M_original R_a)' (M_original R_b) + J_ab,
y^N {M_original[(partial_y R_a)R_b]
      -(M_original R_a)'(M_original R_b)} -> 0.
```

This horizontal modular translation is not a physical-clock translation.
Nothing here assigns zero to the native mean product, the full scalar-tested
current, or the complete radiative left-QNM action. The next attachment must
restore the cusp particular solution, the physical scalar test and its tail,
Q-contact terms and remaining current faces. The source-predeclared common
Hawking clock is unchanged.

Lean optimization: fixed pointwise function types at integral and derivative
interfaces; used a typed directional-smoothness lemma to prevent repeated
eta-expanded fderiv expressions; reused the exact gradient decomposition
instead of reproving modal summability. No heartbeat, recursion-depth or
transparency overrides are used.

## Additional search audit

The deep bilinear-current search completed all stages, with compiler results
predominantly source-only and semantic coverage unmeasured within its reporting
budget. Candidate, source-method and ingredient views were inspected. Its
Gaussian covariance ingredients require different fields/measures; its
homogeneous covariance-energy equation and chamber radial boundary hypotheses
do not supply this forced angular source law. Those suggestions were not
substituted for source proofs.

A broad Sobolev search found Frank–Koskela–Mishra,
[Sobolev extensions, interpolation inequalities and consequences](https://arxiv.org/html/2606.17738v1)
(June 2026). Theorem 1 concerns interpolation on extension domains for p>1;
Corollary 3 retains the mean explicitly. It does not supply this p=1 current
trace or physical-clock invariance. The present trace follows instead from
the actual source PDE and the already installed one-dimensional improper
integral theorem.

## Next source attachment

On the original cusp cell above height 3, the constructed complete angular
responses satisfy H_b(x,y)=P_b(y)+R_b(x,y), with P_b the original cusp
particular solution. Covariance is unchanged by adding a height-only term.
Differentiating this source equality locally gives the precise next target:

```
M_original[(partial_y H_a) H_b]
  -(M_original H_a)'(M_original H_b) = J_ab.
```

This target restores both complete response corrections without changing their
native coefficients. It is not yet formalized in this leaf. For the actual
angular Green current, its native-native contribution has the unchanged
coefficients alpha_b J_ab-alpha_a J_ba. The additional Q-contact pairings and
nonconstant physical scalar-test factor are separate current products; this
leaf has not shown their upper trace or complete-action cancellation. Source
work and other horizon/characteristic faces also remain in the full balance.

## Exact leaf verification

Module: `GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMQuarticNativeCuspCurrent`.
The assembled `/tmp` scratch passed `lake env lean`; the final isolated
`lake build GaloisForLFunctions.RHTower.ThetaCusp.ThetaCuspHawkingBMQuarticNativeCuspCurrent`
passed in 117 seconds using cached dependencies. Artifacts were published;
the temporary audit directory was removed. One RHTower umbrella import was
added, without building the umbrella or any full project.

Source SHA256:
`dd422d0b5162e5572171bc30f4721e46af47724cb26a309e8db7b9fa8dd30945`.
The leaf has four public definitions and seven public theorems. No heartbeat,
recursion-depth or transparency override, numerical experiment, computation
certificate, or axiom-report command was used. All owned Lean processes have
finished. Shared-tree index and lint results are recorded below separately.

Final index refreshed 17 changed shared-tree files; all 11 new API rows and
exactly one umbrella import were verified. The source hash remained unchanged.
`lint --check-generated` exited 1 on these four different unreachable modules:

- `GaloisForLFunctions.RHTower.MaassCircleKernel`
- `GaloisForLFunctions.RHTower.MaassCircleTransfer`
- `GaloisForLFunctions.HTGeometry.CompactSmoothParameterIntegral`
- `GaloisForLFunctions.HTGeometry.InversePowerCancellation`

No unrelated in-progress source was changed to clear this shared-tree gate.
Existing large-file warnings also remain. Global lint success is not claimed.
All owned Lean, search, index and lint processes completed. The exact new leaf
passed independently with no diagnostics.
