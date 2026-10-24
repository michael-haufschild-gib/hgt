# The full real Weil aperture domain has an actual CHMD lift

- **ID:** chmd-real-aperture-domain
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** At every positive aperture, the completed real smooth CCM core equals the complete form-domain vectors with real physical representatives. Every such vector has a unique completed CHMD graph lift preserving the full quotient Weil energy. Every complex form vector decomposes into two such real lifts, with additive full Weil energy.

## Route and exact contribution

CHMD odd theta–Doob positivity implies RH. Reflected-prime collar payment,
primitive half-Rayleigh control and oneL-defect payment remain open.

The fixed-aperture quotient landing theorem previously identified two
completions of the common real smooth core. This theorem removes the
remaining closure-membership assumption: reality of the physical CCM
representative is the entire domain condition. It also produces lifts for
arbitrary complex form-domain states by their real and imaginary parts.
No positivity or aperture-uniform estimate is claimed.

## Complete paper proof

Fix a positive aperture `a`. Write `H` for the complex archimedean form
Hilbert space with support in `[-a,a]`, `J:H -> L2(R,C)` for its injective
physical embedding, and `S` for the closed real span of the real smooth
strict-interior core.

1. **Real mixed inner products.** On real smooth sources, the full Weil
   mixed pairing is real. Each finite prime translation pairing is an
   integral of real functions; both polar coefficients are real
   exponential moments; the remaining scalar L2 term is real. In
   `W(u,v)=<u,v>_H+<B Ju,Jv>`, subtract those real bounded-remainder terms
   to obtain `Im <u,v>_H=0`. Continuity in both variables extends this to
   `u,v in S`. Therefore `S` and `iS` are orthogonal in the underlying real
   Hilbert space. The same continuity argument proves `W(S,S) subset R`.

2. **Projection is physical real part.** Let `P` be real orthogonal
   projection onto `S`. Every smooth complex source has smooth real and
   imaginary parts, so its exact form vector is `u_R+i u_I`, with both
   parts in `S`. Orthogonality gives `P(u_R+i u_I)=u_R`. Hence
   `J P u=Re(Ju)` on the smooth complex core. That core is dense in `H`
   in the form norm; both sides are continuous. The identity holds on
   all of `H`.

3. **Intrinsic real domain.** If `u in S`, then `P u=u`, so `J u` is real
   almost everywhere. Conversely, if `J u` is real, the projection
   identity gives `J P u=J u`; injectivity of `J` gives `P u=u`, hence
   `u in S`. This proves the exact domain equality.

4. **Actual graph admission and uniqueness.** Apply the existing
   continuous linear equivalence between the real graph-core completion
   and `S`. On the dense core its physical coordinate is `J`; continuity
   extends that equality. The inverse equivalence therefore lifts any
   real physical form vector to the actual CHMD graph. Injectivity of
   the graph physical-source map makes the lift unique. The existing
   completed quotient theorem preserves the full Weil form, including
   every prime term and both polar terms.

5. **Arbitrary complex states.** For arbitrary `u in H`, let `r=P u` and
   `s=P(-i u)`. The physical identity and injectivity of `J` give
   `u=r+i s`. Orthogonality gives `||u||^2=||r||^2+||s||^2`. Reality of
   `W(S,S)` cancels the imaginary cross terms, giving
   `W(u,u)=W(r,r)+W(s,s)`. The two real graph lifts consequently realize
   the physical complex source and its complete signed energy.

All inputs are existing unconditional Hilbert-space, smooth-density and
literal arithmetic-form theorems. Reality specifies a domain; it is not
an assumed arithmetic inequality. The final complex statement has no
reality restriction on its input.

## Checked Lean declarations

Module: `GaloisForLFunctions/RHTower/CHMDRealApertureDomain.lean`.

- `aperture_core_inner_im_eq_zero`
- `apertureWeilCompletion_inner_im_eq_zero`
- `apertureRealPart_physical`
- `mem_apertureWeilCompletion_iff_im_eq_zero_ae`
- `apertureGraphWeilEquiv_physical`
- `existsUnique_real_aperture_lift`
- `exists_apertureWeilCompletion_complex_decomposition`
- `apertureWeilCompletion_weil_im_eq_zero`
- `exists_aperture_graph_pair_preserving_weil`

## Gates

- [x] Dependency-closed paper proof.
- [x] Complete candidate passes direct Lean check.
- [x] Transitive axioms contain only `propext`, `Classical.choice`, `Quot.sound`.
- [x] Actual repository leaf passes final direct check, exit 0 without diagnostics.
- [x] Finished module imported by RHTower umbrella; umbrella not compiled.

Validation: `lake --old env lean GaloisForLFunctions/RHTower/CHMDRealApertureDomain.lean`
from `formal/`. Audited the core inner-product theorem, physical projection,
intrinsic real-domain equality, unique lift and complex two-lift theorem
with `#print axioms`. Placeholder and proof-budget scans are clean.

No external novelty claim or numerical experiment is part of this result.
