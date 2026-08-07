# Route R: Burnol Cartier two-head Stokes contraction (2026-08-07)

Formalized `RHTower/BurnolCartierZeroTransferHeadPolarization.lean` and wired it into `RHTower.lean`.

New source-native object: canonical aperture head coefficient `a⁻¹ ⟨1_(0,a),f⟩`, its cosine mate, and fixed positive energy `E_a(f)=|h_a(f)|²+|h_a(Cf)|²`.

For fixed subwindow atom at `a=1/2`, `E(f0)=1+(log 2)^2`. At a hypothetical right-half Xi divisor, Cartier zero-transfer gives exact energy `|alpha|²+(log 2)²|beta|²`, with `|alpha||beta|=1`, `|alpha|>1`, `|beta|<1`. Lean proves strict amplification unconditionally. Thus the one-sided source law `E(U_rho f0) ≤ E(f0)` implies former separate forward-head norm conservation and RH.

Conjecture loop: projective-unipotent invariant line failed (already equivalent to hidden coefficient vanishing); ambient isometry/head projection commutation failed (explicit gain refutes it); two-head positive non-amplification survived and strictly weakens coordinate equality to one canonical one-sided inequality.

Open scientific core: derive `BurnolXiCartierZeroTransferGammaHeadEnergyNonamplification` independently from pre-divisor Euler–Gamma–Stokes structure. Do not infer it from L2 isometry, Sonin landing, RH, or critical-line placement.

Verification: targeted `lake env lean` and `lake build` green; formal lint green. Audited capstones use `[propext, Classical.choice, Quot.sound]`. Card: `docs/drafts/pipeline/3-formalized/new_scientific_knowledge/burnol/burnol-cartier-two-head-stokes-contraction.md`.