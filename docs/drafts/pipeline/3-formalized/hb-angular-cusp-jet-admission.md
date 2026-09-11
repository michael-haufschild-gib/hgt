# HB: actual angular cusp jets

Stage: 3-formalized. Four unconditional Lean theorems prove weighted bounds and cusp limits for every derivative word of the literal squared-source remainder and its retained spin-two image. Frontier map read only.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

The hard target remains `2 Omega(B(p,p)/2,B(m,m)/2)=0`, with independent SS/SV/VV amplitudes and every physical current retained. Source-time/radial interchange is formalized in [its card](hb-source-time-radial-interchange.md). Angular cusp currents require derivative estimates, not only value decay.

## Formalized statement

For every finite word of horizontal/height coordinate derivatives, every complex height weight, and every positive lower height, the differentiated literal squared-source remainder is uniformly bounded over the complete horizontal line and height half-strip. Both Weyl powers, their cross terms with the full infinite signed Fourier tail, and the tail-square term are retained.

## Proof mechanism

The corpus supplies `value_hasFDerivAt`, `valueGradient`, and `weighted_value_bounded`. Horizontal differentiation increments the Fourier index degree. Height differentiation shifts the real height exponent and Bessel order by one. Finite sums, complex scalar multiples, products, and complex height powers times these full families therefore form a class closed under actual coordinate differentiation. Every member has all complex weighted bounds. Express `squareRemainder = 2 principal * tail + tail^2` inside that class and induct on the derivative word.

This is an estimate on actual derivatives of the infinite source, not a finite Fourier truncation or an admitted packet. [Native mean cusp-jet transport](hb-native-cusp-jet-transport.md) is also formalized. The principal angular current, full modular Green integration and final cancellation still need their own proofs.

## Searches and applicability

Broad automorphic/cusp searches and deep Green-current search found exact modular edge cancellation for absolute-convergence Eisenstein pairs, and full native circle-mean modular invariance. Their source types do not directly give the current full-source/native-kernel pairing. The existing cusp exponential jet packet has an unconstructed source-specific admission; the derivative-stable infinite Bessel family supplies a direct route around that missing admission.

The full native mean has three principal powers `2q`, `1`, `2-2q`; rapid remainder estimates alone do not remove those principal angular fluxes.

## Dependency-closed analytical proof

Let `V(u,nu,a,d,sign)` denote the corpus's complete signed Fourier–Bessel family. Its actual derivatives satisfy

```
partial_X V = horizontalRate(sign) V(u,nu,a,d+1,sign),
partial_Y V = a V(u,nu,a-1,d,sign)
              - pi [V(u,nu+1,a,d+1,sign)+V(u,nu-1,a,d+1,sign)].
```

Every family on the right has a uniform bound after multiplication by `Y^w`, for every complex `w` and every fixed positive lower height. Define the generated class using zero, these full families, sums, constant multiples, multiplication by `Y^w`, products, and equality on the open positive-height chart. The product rule and `partial_Y Y^w = w Y^(w-1)` prove closure under actual coordinate differentiation. Equality on the chart transfers derivatives through equality of germs, including at every higher order.

Weighted bounds are preserved by each constructor. For a product, give the first factor weight `w` and the second weight zero. For multiplication by `Y^v`, use the already available bound at weight `w+v`. This proves a bound for every derivative word by induction, without truncating the infinite Fourier series.

The original signed scalar tail is twice the sum of the two `a=1/2,d=0,nu=u` families. Multiplication by either Weyl principal term stays in the class. Hence the literal identity `squareRemainder = 2 principal * tail + tail^2` admits the full squared-source remainder. Closure under `Delta = Y^2(partial_XX+partial_YY)` admits its retained fourth-order image `-Delta(Delta-2) squareRemainder` and every further derivative.

For any such derivative `f`, the bound at weight `w+1` gives `|Y^w f(X,Y)| <= C/Y` for `Y>=1`. Thus `Y^w f(X(Y),Y)` tends to zero for every horizontal path `X`, with no regularity assumption on that path.

## Exact remaining bridge

[Transport through the literal circle average](hb-native-cusp-jet-transport.md) is now formalized for every radius/base-coordinate derivative, uniformly on compact radius ranges. The three principal powers remain explicit. Their angular Green flux and invariant-coordinate characteristic admission still require proof.

## Literature and search limits

The broad recent-paper search examined Kanigowski–Loyd, [Visible Measures along Omega(n) and Distribution of Horocycle Orbits](https://arxiv.org/abs/2608.11382), submitted August 2026. No theorem from that paper is used in this proof. The formal argument uses the installed corpus's exact Bessel derivative formulas and weighted estimates.

The corpus searches were partial: broad retrieval reported incomplete source/semantic indexing; two deep derivative searches reached their time budgets. Candidate source statements and actual Lean checks, rather than search coverage or generated method descriptions, determine applicability here.

## Lean certificate

Module: [ThetaCuspHawkingBMSquareCuspJets.lean](../../../../formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingBMSquareCuspJets.lean), namespace `RHTower.D4BMSquareCuspJets`.

- `squareRemainder_jet_weighted_bound`
- `spinTwoRemainder_jet_weighted_bound`
- `squareRemainder_jet_tendsto_zero`
- `spinTwoRemainder_jet_tendsto_zero`

The theorems quantify over the original complex source parameter, every complex weight and every finite derivative word. No source decay, smoothness, summability or radiation premise is supplied by the caller. For the physical half-square at an actual Xi copy, specialize the source parameter to `center q` and retain the factor `1/2`.

Scratch `lake env lean` passed. The final exact-module `lake build GaloisForLFunctions.RHTower.ThetaCuspHawkingBMSquareCuspJets` passed without warnings in 24 seconds (three jobs). The 3,466 cached own-module imports were frozen; no dependency or umbrella build ran. A separate scratch axiom audit of only these four new theorems reported exactly `propext`, `Classical.choice`, and `Quot.sound` for each. The verified source and five artifacts were copied byte-identically into the corpus, and the module was wired into `RHTower.lean`.

Source indexing completed (three changed files, no removals). Whole static `scripts/formal_tools.py lint` passed with existing large-file warnings. Fifteen local documentation links, edited-file whitespace and the single umbrella import were checked. Every owned Lean/Lake/search process completed, and scratch sources, cached-import links and search outputs were removed.

Complete physical-current cancellation, fixed Hawking-clock extinction and RH remain unproved.
