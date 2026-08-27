# RBH signed three-scale receiver cone (2026-08-27)

Formalized `GaloisForLFunctions.RHTower.ReflectedBiHeatSignedThreeScaleReceiverCone` and wired it into `RHTower.lean`.

Cross-route transfer: for `F(t)=a sinh t+b sinh(2t)+c sinh(3t)`, triple-angle gives

`F(t)=sinh(t) [4c cosh(t)^2+2b cosh(t)+(a-c)]`.

Proved new general infrastructure `quadratic_ne_zero_on_one_iff`: a real quadratic is nonzero for every `x>1` iff either it or its negative belongs to the complete PW-B `quadraticPositiveOnOneCondition`. Necessity uses continuity and IVT to prove sign constancy.

Therefore the complete RBH three-scale wall-selective cone is exactly the PW-B half-line cone applied to `(4c,2b,a-c)` or its negative. Also proved all-natural-power aperture normalization:

`x^(n/2) (L(x^n)^2-R(x^n)^2) = 2 |C(rho)|^2 sinh(n log(x)(Re(rho)-1/2))`.

This gives physical three-aperture factorization and RH equivalence for every cone triple. Signed boundary ray `(-3,0,1)` yields `sinh(3t)-3sinh(t)=4sinh(t)^3` and an exact RH receiver.

Direct check and targeted build passed. Seven principal theorems audited with only `propext`, `Classical.choice`, `Quot.sound`. Card: `docs/drafts/pipeline/3-formalized/reflected-bi-heat-signed-three-scale-receiver-cone.md`. Frontier map remained read-only.