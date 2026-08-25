# Fifth cold Malgrange orientation (2026-08-25)

Solved and formalized next previously absent cold irregular-RH datum.
- With `A=u1`, `B=u2`, `C=u3`, `D=u4`, `E=u5`, order-nine theta/Xi recurrence gives:
  `362880*m4 = E -45*A*D +1260*A^2*C -210*B*C +3150*A*B^2 -18900*A^3*B +22680*A^5`.
- Forced first-jet subtraction cancels `A^5/16` exactly, and residual numerator factors:
  `(E-45*A*D) + 210*(6*A^2-B)*(C-15*A*B)`.
- Existing strict contractions give `B<6A^2` and `C<15AB`.
- Added exact higher contraction `u5<45*A*D`, proved from strict factorial moment ratios `r10*r9<r2*r1`.
- Both summands are strictly negative, so `m4-m0^5/16<0` and fifth cold target `12*(m4-m0^5/16)<0`.

Supporting declaration added to `RoutePPrimitiveGammaJuliaStokesPrimeGammaWallCubicResidualNegativeOrientation.lean`: `thetaCuspRawEvenMoment_five_mul_zero_lt_fortyFive_mul_one_mul_four`.
New module: `formal/GaloisForLFunctions/RHTower/RoutePPrimitiveGammaJuliaStokesPrimeGammaWallQuinticMalgrangeNegativeOrientation.lean`.
Stage-3 card: `docs/drafts/pipeline/3-formalized/route-p-prime-gamma-wall-quintic-malgrange-negative-orientation.md`.
Targeted checks passed. Four created declarations depend only on `[propext, Classical.choice, Quot.sound]`. Scratch/new emitted olean removed; existing supporting cubic olean was updated by direct targeted compile. No Lake target or umbrella build.

Corpus had all-order law and orientations through fourth jet, no m4 formula/fifth sign. Primary audit found general irregular RH/tau sources only; absence is inference.
Frontier map remained read-only for this agent; concurrent external modifications are present and must be preserved.