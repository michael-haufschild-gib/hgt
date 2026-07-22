# Suzuki affine resolvent Krein defect

- **ID:** `suzuki-affine-resolvent-krein-defect`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED] [UNCONDITIONAL]`
- **Paper proof:** `../../2-fully-proven/new_scientific_knowledge/suzuki-affine-resolvent-krein-defect.md`
- **Lean:** `formal/GaloisForLFunctions/RHTower/SuzukiAffineResolventKreinDefect.lean`

## Formal content

For `R_λ(t)=1/(t-λ)` and two-shift affine extrapolation, Lean proves

```text
R_0(t)-[βR_α(t)-αR_β(t)]/(β-α)
=αβ/[t(t-α)(t-β)].
```

Under `α<β<0`, `β<t`, `t≠0`, it proves exact positive and negative sign equivalences with `t`.
It also proves:

- ordinary resolvent gap is negative of defect;
- anti-resolvent gap is defect;
- arbitrary global-target gap equals local Krein defect plus global/local weld correction;
- nonnegativity iff weld correction dominates exact negative defect;
- every negative node creates positive compensation debt and rules out bare nonnegative square.

No `sorry`, axiom, RH premise, numerical computation, or divisor substitution occurs.

## Open boundary

Formalization does not prove source-specific completion identity
`SUZUKI-GLOBAL-LOCAL-KREIN-WELD`.  That identity is current RH-bearing frontier.
