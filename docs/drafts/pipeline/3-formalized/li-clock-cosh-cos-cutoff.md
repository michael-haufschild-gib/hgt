# Strict scalar cosh–cos cutoff positivity

- **ID:** LI-CLOCK-COSH-COS-CUTOFF
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [actual cutoff and marking boundary](../2-fully-proven/li-clock-cutoff-marking-boundary.md), scalar I8.
- **Statement:** For v>=0, u>=v, u>0, a>=v and T>0, the finite integral of exp(-at)(1-cos(ut)cosh(vt))/t over [0,T] is strictly positive.

## Gates

- [x] Exact finite-cutoff paper proof and complete independent audits.
- [x] Complete source review: two public and32 private declarations.
- [x] Named build, direct compile, imported public axioms and catalog integration.
- [ ] Publication and external novelty audit.

## Formal source and evidence

`formal/GaloisForLFunctions/RHTower/LiClockCoshCosCutoff.lean`,469 lines,
SHA256 `6ad7f818f996a6fdd4fe60c2df57e6607ba2b8b63af62c24f8485235f9e00d0b`.
Public definition `liClockCoshCosCutoff` and theorem
`liClockCoshCosCutoff_pos` retain the exact finite integral and full domains,
including a=v, u=v and v=0. Complete source/factor/admission audits passed.
The only final syntax delta removed a redundant noncomputable modifier
inside the existing noncomputable section so the definition is indexed;
every proof/type/body otherwise remains byte-identical to audited source.

Named16508/direct52393/importedALL2axes24247 terminal0, no own diagnostics;
all34 scratch and both public axiom reports foundational only. Unique
umbrella import, index83798 and both actual API rows verified. Lint4300
reports10 unrelated unreachable modules; no scalar issue. Full final
certificate: `/tmp/li_root_cosh_cos_cutoff_final_certificate.md`.

## Boundary

This proves the scalar positive building block. Full actual-source cutoff,
marking classification and inverse remainder retain separate Lean work.
Original undamped-source positivity and RH remain OPEN.

- 2026-10-01 — Scalar survivor locally finalized and integrated.
