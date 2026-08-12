# Mass-shifted hard-edge worldline/source conservation (2026-08-12)

Created corpus-native arithmetic producer for §9.3, before reflection aggregation.

Key identities for actual degree-n inverse-Hankel admission P_n(y), differentiable nonzero root branch x(y), u=x^{-1}-y, h_n=L_y(P_n²), Christoffel weight λ, and Γ=y x⁴ λ P_n'(x)²:
- ∂_y P_n(y,x) = x² P_n'(x) + 2 n β_n P_{n-1}(x).
- finite-block confluent CD: β_n λ P_n'(x) P_{n-1}(x)=h_n.
- exact source/worldline conservation: u' Γ = 2 n y x² h_n.
- with existing ρ C_eff=Γ: u' ρ C_eff = 2 n y x² h_n.
- normalized: u'(Γ/h_n)=2 n y x².
- y=w²: dot(u)(Γ/h_n)=4 n w³ x².
- any positive speed cap dot(u)≤K implies Γ/h_n ≥ 4 n w³ x²/K.
- if x=(w²+u)⁻¹, u/w²→0, n/w→c, forcing tends 4c.

Interpretation: terminal mass is inverse root mobility. Its extinction is possible only through nonproper parabolic root-speed escape. Fixed integral-Lipschitz controls quadratic forms, not growing-degree root mobility. Remaining exact burden: source-specific parabolic hard-root speed tightness / equivalent uniform normalized coefficient-flow bound. RH remains open.

Files:
- formal/GaloisForLFunctions/HTGeometry/FiniteConfluentDarboux.lean
- formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionHardEdgeWorldlineSourceLaw.lean
- docs/drafts/pipeline/3-formalized/mass-shifted-hard-edge-worldline-source-conservation.md
- report addendum equations 9.3.651–9.3.658.

Both modules pass direct lake env lean and targeted lake build. Ten capstones audit to propext, Classical.choice, Quot.sound only. Formal lint recognizes new umbrella imports; repo-wide lint remains red on unrelated concurrent unreachable modules.