# Mass-shifted terminal-source amplification (2026-08-13)

Formal module: `formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionTerminalSourceAmplification.lean`
Umbrella: `formal/GaloisForLFunctions/RHTower.lean`
Card: `docs/drafts/pipeline/3-formalized/mass-shifted-terminal-source-amplification-polarization.md`
Report: `docs/reports/mass-shifted-spectral-trace-route.md`, §9.3 addendum “Terminal-source amplification and moving-apex polarization”.

Core unconditional laws, with terminal resistance r_x, hard coordinate t=yx, terminal product Gamma_x, preceding norm h_(n-1), and intrinsic source GammaHat_x=y^3 Gamma_x/h_(n-1):
- r_x GammaHat_x = t_x^4.
- Actual root worldline: x^2 u'_x = 2 n beta_n r_x, u=x^-1-y.
- Resistance-free source action: u'_x GammaHat_x = 2 n beta_n y^2 t_x^2.
- Sedrakyan: (sum t^2)^2 <= sum GammaHat; projective root spread squared <= aggregate source.
- Every resistance share <=1, so t>1 implies GammaHat>1: resistance collapse amplifies source rather than hiding super-apex leakage.
- Centered source action A^partial := u' GammaHat - 2 n beta_n y^2 satisfies
  A^partial = 2 n beta_n y^2(t^2-1)
            = -2 n beta_n y^2 x(t+1)u.
  Thus A^partial>0 iff u<0 iff t>1 for positive nodes.
- If y_k→∞, u_k→d, x_k=(y_k+u_k)^-1, then y_k[(y_k/(y_k+u_k))^2-1]→-2d. Bounded negative hard root retains finite positive normalized source signature.

This is an arithmetic source law, not an orientation map: actual root velocity is multiplied by actual Padé-residue/current-adjacent completed P^sharp source capacity, then endogenous moving-apex vacuum is subtracted.

Exact remaining RH wall: no theorem provides a cross-degree, source-preserving renewal budget for signed centered nodal actions. Needed: (1) degree-renewal budget charging cofinal positive actions without summable weights, (2) literal completed-Xi no-recurrence for bounded super-apex actions, or (3) pre-reflection prime–Gamma bilinear decomposition into centered nodal action plus nonnegative degree-proper bulk.

Audits:
- `lake env lean` passes with zero warnings.
- Targeted `lake build GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionTerminalSourceAmplification` passes.
- Axiom audit: only propext, Classical.choice, Quot.sound.
- No sorry/admit/axiom/opaque/unsafe in module.
- Global lint currently fails only unrelated concurrent umbrella gaps in RHTower.Sieve.* and SuzukiCanonicalL1TranslationGenerator / SuzukiCanonicalLogSourceL1Derivative; our module is umbrella-reachable and absent from errors.
- No computation used.