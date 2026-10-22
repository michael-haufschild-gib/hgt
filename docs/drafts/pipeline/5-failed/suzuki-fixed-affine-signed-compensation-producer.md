# Failed route: fixed-affine Suzuki signed compensation as an upstream producer

- **ID:** SWA-FIXED-AFFINE-COMPENSATION-PRODUCER-NOGO
- **Status:** TERMINAL ROUTE CLASS `[LEAN-PROVED]`
- **Parent:** `SUZUKI-FE-REFLECTED-WALL-WARD-ASSEMBLY`

## Proposed route

Choose fixed real coefficients `a,b` and use

`K_N(a,b)=a C_N+b E_N`

to cancel the positive Suzuki transition core `C_N`, hoping the corrected residual is a nonzero
nonnegative bounded source upstream of the shared HB/FZZ-P/PW-B/RBH Ward endpoint.

## Killing theorem and mechanism

Lean theorem:
`suzukiFixedAffineSignedCompensation_routeClassification`.

The unconditional limit `E_N/C_N -> 0` gives

`K_N(a,b)/C_N -> a`.

Therefore core saturation forces `a=1`.  The residual then has the exact normal form

`C_N-K_N(1,b)=-b E_N`.

All coefficient choices are terminal:

- `b<0`: positive nontrivial residual; boundedness is exactly RH;
- `b=0`: residual is identically zero, erasing the source;
- `b>0`: residual is nonpositive and upper bounded by zero unconditionally, so the criterion is
  sign-reversed and vacuous.

No fixed affine coefficient choice supplies a new source estimate between transition-core
cancellation and RH.

## Strongest positive survivor

The full coefficient-plane classification is the survivor.  It proves exact rigidity of relative
core cancellation and identifies the aligned residual `E_N` as the unique positive nontrivial
fixed-affine quotient, up to positive scalar multiplication.

New insight: coefficient tuning has no remaining mathematical freedom.  Any viable successor must
change representation before energy projection: scale-dependent, nonlinear, singular, or nonlocal
compensation.  This boundary was not present in the internal corpus or the audited Suzuki
literature.

Paper and Lean status:

- complete proof and audits:
  `docs/drafts/pipeline/3-formalized/suzuki-fixed-affine-signed-compensation-classification.md`;
- Lean module:
  `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiFixedAffineSignedCompensationClassification.lean`;
- direct check, targeted build, axiom audit, and umbrella wiring passed.

## Route consequence

Fixed-affine signed compensation is retired for the exact chain

`Suzuki source` → `transition-core/Ward compensation` → `HB/FZZ-P/PW-B/RBH common Ward endpoint`
→ `RH`.

The surviving open source problem remains boundedness of `E_N` itself, equivalently RH; it cannot be
reduced by constant affine mixing.

