# CLG/TTF unwindowed moments and complete signed source jets

- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** At every critical aperture, the complete signed derivative hierarchy of the literal center-mixed theta source at difference zero determines the global Fourier-current sign. Positivity of this hierarchy at every critical aperture is equivalent to RH. Its first five-dimensional Hankel section is unconditionally positive definite.
- **Capstones:** `RHTower.thetaCuspCenterMixedSignedJetCone_iff_riemannHypothesis` and `RHTower.thetaCuspCenterMixedSignedHankel_five_posDef` in `ThetaCuspCenterMixedSignedJetCompleteness`.
- **Exact proof chain:** Literal theta source → full signed source-jet cone ↔ raw current Hankel cone ↔ global Fourier-current sign ↔ Xi Bezoutian orientation ↔ RH. The analytic arrows are proved; the all-order positive cone is not.

## Dependency-closed proof

For a continuous real density `J` with `|J(x)|≤C exp(-ε|x|)`, `ε>0`, every raw moment is integrable. Use the positive Laplace reference measure `dμ=exp(-ε|x|/2) dx` and multiplier `g(x)=exp(ε|x|/2) J(x)`. The measure is finite, charges every nonempty open set, and integrates `exp(ε|x|/4)`; the multiplier is continuous and bounded by `C`. Integration against `g dμ` is exactly integration against `J dx`.

Complete real Hankel positivity is positivity on real polynomial squares. Each complex polynomial modulus square is the sum of two real polynomial squares. The corpus theorem `HTGeometry.ae_nonneg_of_forall_sq_poly_integral_nonneg`, based on polynomial density from one local exponential window, therefore gives `g≥0` almost everywhere. Continuity and positive measure on open sets make this pointwise. The positive reference density returns `J≥0`. Conversely a nonnegative `J` integrates every polynomial square nonnegatively. `UnwindowedHankelSignCone` formalizes this exact equivalence; the tested moments contain no Gaussian window.

`XiHorizontalStripDecay` and `XiCDerivStripDecay` give uniform exponential bounds for Xi and its derivative on every closed aperture substrip. The literal Hedenmalm current is bounded by twice their norm product, giving exponential current decay. Taking the source shift parameter `δ=π/8` gives a positive current decay rate `π/4`. `HedenmalmRawHankelRH` applies the generic sign theorem with all decay and integrability inputs discharged.

Write `f_a` for the actual center-mixed density and `F_a(x)=f_a(x/2)` for the existing Schwartz autocorrelation tangent. The latter identity also proves all-order smoothness of `f_a`. Fourier inversion applied to each iterated Schwartz derivative gives its exact moment identity at zero. The change of frequency `b=2πξ` and the source scaling `x=2t` yield

`(2I)^n m_n = 2π f_a^(n)(0)`,

where `m_n=∫ b^n J_a(b) db`. Multiplication by `(-I/2)^n` and taking real parts gives

`m_n = 2π·2^(-n)·s_n`,

` s_(2k)=(-1)^k f_a^(2k)(0),  s_(2k+1)=0`.

Multiplying moments by a positive constant and an invertible geometric scale is an exact diagonal change of every finite Hankel quadratic form. Thus the complete raw cone is exactly the complete signed source-jet cone. The existing Fourier-current/Bezoutian orientation equivalence finishes the RH equivalence.

Finally, at rank five the already proved factorial-normalized translation jet matrix is positive definite. Diagonal entries `i!·(-1)^floor(i/2)` turn it into the Hankel matrix `s_(i+j)`. Evenness supplies the vanishing odd derivatives; the exact diagonal congruence is invertible. This identifies the previous five-point result as a strict section of the same complete hierarchy, with no extra source-sign premise.

## Scope and remaining producer

The decisive missing theorem is positivity of the signed hierarchy at every order and every `0<a<1/2`. The finite five-dimensional section does not supply this. Fourier incidence, exponential decay, moment determinacy, and the global sign implication require no further assumption in this endpoint. General-packet/cofinal constructions and the separate C5 orientation fronts remain alternate approaches.

This hierarchy is the Fourier-signed jet of the literal center-mixed density. It is not the generic reflected-source Hankel hierarchy whose proposed real-rootedness implication has corpus counterexamples.

## Verification

- All three new production modules pass direct `lake env lean` checks without warnings; only their needed oleans were generated.
- Both new capstones report only `propext`, `Classical.choice`, and `Quot.sound` under `#print axioms`.
- All three modules are wired into the RHTower umbrella without building it.
- No numerical oracle, added axiom, full build, umbrella build, or cascading rebuild.
- Public declaration names have no outside-module conflicts; `git diff --check` passes; corpus indexes refreshed.
- Formal lint currently reports an unrelated, concurrently added module unreachable from its umbrella: `RHTower.HarmonicSecondErrorBounds`. All three modules here are wired.
- Owned scratch files removed; no owned Lean/lake processes remain.
