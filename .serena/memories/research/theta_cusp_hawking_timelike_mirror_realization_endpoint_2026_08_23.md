# Theta-cusp Hawking timelike mirror realization endpoint (2026-08-23)

New Lean endpoint: `formal/GaloisForLFunctions/RHTower/ThetaCuspHawkingTimelikeMirrorRealizationEndpoint.lean`.

Unconditional survivor: the ray family `p_lambda(v)=v+lambda*thetaCuspFullSource(v)` has an explicit nonempty open coupling interval `|lambda| < (thetaCuspDerivativeExpConstant 1 + 1)^(-1)` on which `p'_lambda(v)>0` globally. Therefore the ray map is strictly increasing, its Minkowski worldline is future-directed, and its coordinate velocity has absolute value `<1` everywhere.

The configuration and slope coupling tangents are exactly `thetaCuspFullSource` and its derivative. Existing moving-mirror Born theorem then identifies the physical family tangent with `2*i*omega_out*omega_in*XiC(omega_out+omega_in)`.

Interpretation: this upgrades the Hawking route from a post-hoc Fourier analogy to an actual open family of physical timelike mirrors whose dynamical-Casimir/Hawking pair-emission tangent carries Xi.

Falsified producer mechanisms: generic timelikeness, CCR completion, KMS/FDR, HBT/Gram positivity, and causal passive scattering do not force resonances to the real axis; they hold for generic mirror data or preserve inner/all-pass freedom.

Open core: derive a theta-specific positive storage/port identity linking this mirror's pair block, conformal-anomaly generator, and boundary Green current. Generic conservative/unitary dilation is insufficient because self-adjoint scattering systems can have complex resonances.

Verification: direct `lake env lean GaloisForLFunctions/RHTower/ThetaCuspHawkingTimelikeMirrorRealizationEndpoint.lean` exits 0. Forbidden-declaration scan clean. Key theorems depend only on standard mathlib axioms `[propext, Classical.choice, Quot.sound]`. Umbrella `RHTower.lean` imports endpoint; file was already dirty from unrelated work, preserved.

Related prior memory: `mem:research/theta_cusp_hawking_partner_coherence_rigidity_endpoint_2026_08_23`.