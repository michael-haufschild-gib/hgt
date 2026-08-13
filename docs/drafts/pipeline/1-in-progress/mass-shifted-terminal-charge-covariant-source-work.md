# Mass-shifted terminal-charge covariant source work

- **ID:** MS-TCCSW
- **Stage:** 1-in-progress
- **Type:** CONJECTURE
- **Source:** `docs/reports/mass-shifted-spectral-trace-route.md` §9.3 exact open core
- **Statement:** Terminal adaptive-mixed source charge has an exact division-free adjacent-norm Wronskian derivative law requiring only admitted solve blocks; at an order-`d` strict contact, its cleared source work has order exactly `d-1` and positive leading coefficient.

## Goal

Replace unavailable future-block effectivity coercivity by a source-first law for motion of the
terminal channel itself.  Current and newborn canonical amplitudes are admitted first; their raw
norm fluxes are formed from odd Gamma arithmetic; only then are they paired bilinearly.  No
orientation map, reflection aggregate, finite reporter, or Jacobi quotient is primitive.

## Gates

- [x] 0 → 1  in-progress: exact socket and hostile counterroute identified
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, targeted `lake build` green, axiom audit PASS
- [ ] 3 → 4  publication-ready: standalone paper and external novelty audit

## Frozen conjectures

Let `H_k(y)` be current canonical admission norm, `Phi_k(y)` its division-free norm flux, and

`W_N(y) = H_N(y) Phi_(N+1)(y) - H_(N+1)(y) Phi_N(y)`.

1. **[C1 — exact work law]** Wherever `H_N(y) != 0` and the two solve determinants are nonzero,
   `d(H_(N+1)/H_N)/dy = W_N/H_N^2`.  Consequently derivative of terminal source charge
   `4(N+1) H_(N+1)/H_N` is `4(N+1)W_N/H_N^2`.
2. **[C2 — contact-order descent]** At an occupied strict frontier with
   `H_(N+1)(y+u) ~ C u^d`, `C>0`, and `H_N(y)>0`,
   `W_N(y+u)/u^(d-1) -> d H_N(y) C > 0`.
3. **[C3 — Fisher payment]** Existing top adaptive source action pays
   `(W_N^2)/(H_N^2 H_(N+1))` with degree-proper constant using no next positive block.

## Conjecture loop

- **C3 failed structurally.**  The quotient is terminal Fisher density.  At simple contact it is
  asymptotic to a positive multiple of `1/u`, whereas existing source action has finite outgoing
  capital.  No local finite source-payment inequality of this form can hold.
- **Positive survivor:** C1 lowers all top-effectivity dependence into a division-free bilinear
  source work.  C2 lowers every finite contact order by exactly one and preserves positive native
  residue.  Iterating covariant source work, not normalizing by terminal charge, is the only local
  contact-extraction operation compatible with finite source capital.

## Approach

Use corpus theorem
`hasDerivAt_xiShiftedCanonicalAdmissionNorm_eq_normFlux_of_det` independently at degrees `N` and
`N+1`, then quotient rule.  For C2, use determinant power series at strict contact and differentiate
the first live term; multiply by continuous positive head norm.  Audit whether existing
all-contact determinant-jet source theorem supplies the required differentiated coefficient
without introducing a future positivity hypothesis.

## Log

- 2026-08-13 — C3 falsified by exact simple-contact asymptotics; C1/C2 frozen as strongest
  division-free survivor.
