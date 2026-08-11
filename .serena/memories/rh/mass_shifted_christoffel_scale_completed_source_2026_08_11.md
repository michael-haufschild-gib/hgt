# Mass-shifted Christoffel-scale-completed source (2026-08-11)

Formal modules:
- `RHTower.XiShiftedCanonicalAdmissionRelativeSourceCoercivity`
- `RHTower.XiShiftedCanonicalAdmissionScaleCompletedArithmeticSource`

Key unconditional facts:
1. Literal mass-scaled rational–Gamma minus von Mangoldt relative source equals current normalized adaptive Jacobi energy exactly inside one `(n+2)` positive Hankel chamber:
   `relativeArithmeticSource w n = adaptiveOrthoJacobiEnergy s n`.
2. Norm division removes amplitude gauge but not coordinate gauge. For positive dilated arcsine moments `c_k^(r)=r^k c_k` and actual canonical admission `p_n^(r)=r^n p_n(X/r)`,
   `source/norm = r²(n+3/8)`.
3. Thus `source/norm > n` iff `8n(1-r²)<3r²`; every fixed `0<r<1` fails cofinally. The prior claim that constant quotient tolerance creates a degree-uniform open neighborhood is false. It still demands inverse-degree coordinate accuracy.
4. Current admission Christoffel scale
   `kappa_n=16 N_(n+1)/N_n=16 beta_(n+1)`
   has the same coordinate weight. Scale-completed literal source
   `C_n=relativeArithmeticSource/kappa_n`
   equals `E_n/(16 beta_(n+1))`, is positive in every finite positive chamber, and is exactly `n+3/8` for every nonzero dilated arcsine family.
5. Recession-free covariant coercivity:
   `(n+1) beta_(n+1) < E_n = relativeArithmeticSource`, hence `(n+1)/16 < C_n`.
   Proof uses strict `beta_n>0` plus nonnegative remaining Jacobi-energy summands.

Scientific interpretation:
- amplitude gauge and coordinate gauge are now separated and closed.
- Remaining §9.3 obstruction is shape-only admission holonomy: a frozen flag emitted at a crossing need not remain current admission later.
- Quantitative calibrated target `C_n>n` is exactly `E_n>16n beta_(n+1)`, not supplied by generic positivity.
- Sign closure needs an outgoing-ray law covariant under current Christoffel scale, not orientation or fixed reporting.

Docs:
- report §9.3 equations (9.3.419)–(9.3.426)
- stage-3 cards `mass-shifted-canonical-relative-source-coercivity.md` and `mass-shifted-christoffel-scale-completed-source.md`

Verification:
- direct Lean checks pass
- targeted builds pass
- audited capstones depend only on `propext`, `Classical.choice`, `Quot.sound`
- full lint failed only on unrelated concurrently un-wired modules; these modules were not lint errors.
- no computation, RH hypothesis, sorry/admit/axiom/opaque/unsafe.
