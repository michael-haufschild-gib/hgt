# Signed native-delay bulk: outcome

## Result

The complete signed delay/source-spin-two sector currently proved in Lean is not a standalone zeta-zero diagnostic. It is nonzero at each of zeta zeros 1–8 in the base section, admits both zeta-height and non-zeta roots after section tuning, and has no zero that persists across the tested sections. The arithmetic Fourier tail is sometimes decisive, but it supplies no section-independent selection by itself.

This rejects H1 and H2 of the frozen protocol. H3 is also rejected in the base sample: direct-minus-image subtraction usually removes almost none of the sheet magnitude. H4 survives only as a structural warning—nonconstant Fourier modes materially change the action—but not as an observed zeta/control discriminator.

## Computed object and scope

For each height `gamma`, the code evaluates the normalized completed Eisenstein scalar, its exact second jets, the hyperbolic spin-two density of its half-square, the angular circle mean at the Lean `delayArgument`, the literal smooth finite clock convolution, both causal sheets, direct-minus-image signing, and complementary ordered-branch antisymmetrization. Characteristic and terminal delay currents vanish by the current Lean theorem. Multiplying the normalized result by the recorded nonzero `|Lambda(1+2i gamma)|^2` restores the physical source normalization without changing zeros or relative residuals.

This is the whole sector of `D4BMSpinTwoDelay.signed_delay_finite_transfer`, not the whole HB action. Physical lift/response cross-currents and outer modular angular Green faces remain unassembled.

## Main observations

- Base section `(x,y,X,k,V)=(-0.4,-0.6,0.13,1.5,2)`: zeta zeros 1–8 have relative ordered residuals `0.90813, 0.37749, 0.34085, 0.49289, 0.99994, 0.59273, 0.99896, 0.92064`; median `0.75043`. Eight local-spacing controls have median `0.59843`. No zeta value vanishes.
- Across eight sections, zero1 remains nonzero with residual `0.851–0.991`. Zero4 ranges from a validated near-hit `0.03950` in the image-short section to `0.99245` in the diagonal section and changes sign. A small pointwise residual is therefore not a stable selector.
- Stronger quadrature locates a fixed-base non-zeta sign-change root in `gamma in [15.075,15.1125]`. Both signs survive a horizontal shift `X:0.13→0.31`; the diagonal radial section makes both endpoints same-sign with residuals `0.97375` and `0.97535`. Height scanning found eight sign-change intervals among fourteen adjacent intervals from `gamma=10` to `45`. The action has its own dense, movable spectrum.
- At actual zeta height 1, varying cusp coordinate gives a stable `k` root bracket `(1.7802,1.9)`; at zeta height 4, the bracket is `(1.5,1.5699)`. The disjoint brackets already exclude one common `k` for those two heights. Four of eight low-height controls also cross the first coarse bracket. Geometry can manufacture action zeros at zeta and non-zeta heights.
- Direct-minus-image sheet-cancellation ratios have zeta/control medians `0.99645/0.99030` in the base sample; values near one mean almost no cancellation. The validated zero4 image-short near-hit has sheet ratio `0.98204`, so its `0.03950` residual comes from complementary branch antisymmetry, not direct/image cancellation.
- Nonconstant Fourier modes reverse the sign at zero4 in the base section: the principal-only and full ordered values have opposite signs, with tail leverage `1`. The same happens at several controls and higher scan heights. Principal-cusp truncation cannot identify this action.
- Complementary conjugacy error is numerically zero throughout. This forces the ordered action to the imaginary axis, reducing a complex zero test to one real equation; it does not choose arithmetic heights.

## Validation

- Zero1 base convergence: relative residual `0.90811574 → 0.90807886 → 0.90807892` over three crossed resolutions.
- Zero4 base convergence: `0.49289488 → 0.49286114`; zero4 image-short convergence: `0.04048297 → 0.03923731 → 0.03949658`.
- Independent source checks: scalar eigen-equation relative error `1.71e-15`; vertical derivative `3.07e-16`; modular-reduction scalar/spin errors `4.92e-15/5.52e-16`; analytic versus numerical principal circle mean `3.91e-11`.
- The non-zeta bracket signs survived a stronger run: ordered imaginary parts `+1.16036e9` and `-3.46966e8` at its endpoints.
- All completed runs used finite timeouts and up to 16 independent workers. Results are numerical observations, not interval certificates.

## Landscape consequence

The computed HB sector lives on a high-dimensional nodal geometry in `(spectral height, radial section, angular base point, cusp scale, terminal time)`. Complementary symmetry supplies a critical-line phase reduction, while section parameters generate plentiful intersections. Consequently, “the action vanishes at a zeta zero for one geometry” is cheap evidence: the same mechanism produces non-zeta roots and moves or removes them under admissible section changes.

For HB identification, any claimed receiver diagnostic must now reproduce the assembled all-face action and explain whether the large surviving delay term is canceled by physical lift/response and outer angular currents. For HB selection, the decisive object must be section-independent—most plausibly a global flux/cohomological identity or a synchronized family of face cancellations—not a pointwise scalar residual.

If the later all-face action remains nonzero at actual Xi parameters, that falsifies this HB extinction route, not RH. If it cancels, RH still requires a source-side theorem that permits known critical-line zeros while excluding off-line zeros for a reason independent of RH. Numerical falsification of RH itself would require a certified off-critical zero of zeta; none is claimed here.

