# HB: native theta-source circle mean and Riemann kernel

Status: 21 unconditional identities formalized in four modules. Full physical pairing, fixed Hawking-clock extinction and RH remain unproved.

Proof chain: literal theta-cusp source → Xi occurrence → retained spin-two source → physical causal radial/left-QNM action → fixed Hawking-clock extinction → RH.

## Positive result and cancellation target

The original theta half-square now has an explicit angular circle mean whose actual base-point Laplacian commutes with averaging. Composing this mean with the original causal invariant gives a Riemann kernel satisfying the BM time/tortoise wave equation in the strict characteristic interior. Its characteristic value is the literal original half-square, and the direct and reflected kernels cancel at the original AdS endpoint.

This supplies the full-source kernel needed for the common producer on both legs of the mixed source pairing. All angular derivatives are those of the actual theta field. No angular eigenvalue is assigned to its square, and no smoothness, differentiation-under-integral, or kernel-equation assumption is supplied to the public identities.

## Exact Lean scope

All declarations are in `RHTower.D4BMNativeCircle`, under `GaloisForLFunctions.RHTower` modules:

- `ThetaCuspHawkingBMNativeCircleChart`: nine public identities prove strict positivity of the circle denominator, actual radial and angular chart derivatives, the polar principal and connection identities, and the base-point Laplacian correction coefficients.
- `ThetaCuspHawkingBMNativeCircleSource`: four public identities prove global smoothness of the actual pulled-back source in radius, angle, horizontal coordinate and logarithmic height; its Darboux integrand; its base-point Laplacian integrand; and its horizontal derivative.
- `ThetaCuspHawkingBMNativeCircleMean`: five public identities prove `mean_radial_action`, `mean_laplacian_commutes`, `mean_darboux`, `mean_zero`, and `mean_radial_smooth`. Compact domination and periodic endpoint cancellation are discharged in the proofs.
- `ThetaCuspHawkingBMNativeCircleRiemannKernel`: `nativeRiemannKernel_wave`, `nativeRiemannKernel_characteristic`, and `nativeRiemannKernel_AdS` prove the full-source interior wave equation, original-source characteristic normalization, and reflected endpoint cancellation.

Writing `Q=fullSquarePotential q`, `Y=exp k`, `m(d;X,Y)` for the native circle mean, and `Z=(cosh h+sinh x sinh y)/(cosh x cosh y)`, the proved equations are

```
sinh(d)^2 m_dd+sinh(d)cosh(d)m_d=sinh(d)^2 Delta m,
Delta m=mean_d(Delta Q),
m(0;X,Y)=Q(X,Y),
R(h,x,y;X,Y)=m(arcosh Z;X,Y),
R_hh-R_xx-Delta R/cosh(x)^2=0,  Z>1.
```

The kernel theorem's point is bundled in `InteriorPoint`, the strict native chart inside the original forward characteristic cone. The characteristic and AdS value identities hold for all real coordinates appearing in their statements. Logarithmic height covers every positive original height.

## Further analytical proof and remaining obstacle

The [active cancellation card](../1-in-progress/hb-native-circle-green-kernel.md) derives a regular integral formula at `Z=1` and proves all right characteristic jets on paper. In particular,

```
partial_Z M_Q(1)=Delta Q/2,
partial_Z^2 M_Q(1)=Delta(Delta-2)Q/8.
```

The first right derivative, its interior limit and both original-coordinate source-normal contacts are now [formalized in two further modules](hb-native-characteristic-contacts.md). The second jet identifies the same angular polynomial that occurs in the coexact mixed symplectic pairing; its all-orders regularity proof and the two-leg producer transfer remain analytical. The totalized `arcosh` definition outside `Z>=1` is not used to claim an ordinary two-sided characteristic derivative.

The next cancellation calculation must combine the interior two-leg action, its moving characteristic contacts, and the full Einstein-current boundary terms. Identification with the actual forced retarded/advanced inverse, full-domain integrability, retained cusp fluxes, and every independent SS/SV/VV coefficient remain required. None of the new kernel identities asserts that the physical pairing vanishes.

## Validation

All four scratch sources passed sequential foreground `lake env lean` checks without warnings. Final audits used only `lake build` on each exact new module, with 3938 existing own-corpus dependency modules frozen. Chart, source, mean and kernel completed in 12, 39, 17 and 41 seconds respectively. No old dependency, full or umbrella rebuild ran.

Only the 21 newly created public theorems were axiom-audited. Each reports exactly `propext`, `Classical.choice`, and `Quot.sound`. Installed sources and olean/ilean artifacts were byte-compared with the audited files. All four imports are wired into RHTower without building it. No mathematical computation was used.

The corpus index was refreshed. Static `scripts/formal_tools.py lint` and scoped whitespace checks passed; lint retained 141 existing file-size warnings. All owned Lean/Lake processes exited. The owned scratch and frozen-cache audit workspace were removed. The frontier map was not edited.
