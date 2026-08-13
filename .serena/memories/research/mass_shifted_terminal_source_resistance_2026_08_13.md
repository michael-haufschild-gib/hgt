# Mass-shifted adaptive terminal-source resistance law

Formalized source-first terminal probability law for §9.3.

Files:
- formal/GaloisForLFunctions/HTGeometry/GaussTerminalSourceResistance.lean
- formal/GaloisForLFunctions/RHTower/XiShiftedCanonicalAdmissionTerminalSourceResistance.lean
- docs/drafts/pipeline/3-formalized/mass-shifted-adaptive-terminal-source-resistance-law.md
- docs/reports/mass-shifted-spectral-trace-route.md, equations (9.3.754)–(9.3.756)

For current monic orthogonal admission P_n and root x:
r_{n,x} = lambda_x P_{n-1}(x)^2 / h_{n-1}.
Finite positive chamber proves r>0, sum r=1,
r=P_{n-1}(x)/P_n'(x)=-P_{n+1}(x)/(beta_n P_n'(x)).

Literal vacuum-free completed source product Gamma_x=rho_x C_eff^circ satisfies:
r_{n,x} Gamma_x = w^2 x^4 h_{n-1}.
Under w != 0 and all hard nodes nonzero:
sum_x [w^2 x^4 h_{n-1}/Gamma_x] = 1.

Sharp no-go: two-root interlacing realizes every theta in (0,1), so generic positivity/interlacing gives no uniform selected-share floor. Exact residual is shifted-Xi arithmetic localization/tightness, or use collapse of adjacent/current ratio in parity-doubled radical/contact-order branch.

Verification:
- direct lake env lean checks pass
- targeted lake build for both modules passes
- axiom audit only propext, Classical.choice, Quot.sound
- repository lint sees new modules but fails on unrelated concurrent unwired RHTower modules
- no sorry/admit/axiom/opaque/unsafe in new modules
