# Positive nonlocal FZZ reflection collapses to reciprocal delay

- **ID:** FZZ-P-NONLOCAL-POSITIVE-COLLAPSE
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `FZZCigarParityDelaySourceContinuation` · `ThetaCuspHawkingFZZParityLocalTemperedFEReflectionNoGo`
- **Statement:** Every finite positive nonlocal kernel reproducing the literal parity-delay reflected Mellin densities through grades zero, one, and two is concentrated at reciprocal delay; its total mass is the unique exponentially singular local reflection weight.

## Goal

Kill the positive nonlocal-completion survivor in the FZZ-P chain

`literal FZZ parity-delay source → nonlocal FE reflection → universal reflected-information stationarity → FZZ Mellin completeness → RH`.

This is pre-divisor and source-pure. It assumes neither an Xi zero nor RH. Only signed/distributional nonlocal reflection or the forced essential-singularity local law survives.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: Lean module and theorem, targeted `lake build` green, axiom audit clean
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Approach

For positive delay `t`, let `K_t` be a finite positive kernel on positive delays and suppose its Fermi-weighted moments are

`∫ F(u) dK_t = t⁻¹F(t)`, `∫ uF(u) dK_t = t⁻²F(t)`, and `∫ u²F(u) dK_t = t⁻³F(t)`.

With `a=t⁻¹`, expansion gives

`∫ (u-a)² F(u) dK_t = 0`.

The integrand is nonnegative and `F(u)>0`, so `K_t` is concentrated at `u=a`. The grade-zero identity fixes its total mass as

`a F(t) / F(a) = t⁻¹ (exp(t⁻¹)+1)/(exp(t)+1)`,

exactly the unique local weight already proved to dominate every polynomial ultraviolet scale.

## No-go closure

- **Exact killing theorem/mechanism:** `no_polynomiallyTempered_FZZCigarParityPositiveNonlocalFEReflectionData`; positivity turns three adjacent reflected Mellin rows into zero conditional variance, erasing all nonlocal spread.
- **Strongest positive survivor:** `kernel_eq_atom` and `kernelMass_eq` classify every allowed kernel exactly; `fzzCigarParityForcedLocalFEReflectionData` constructs the singular reciprocal-delay survivor. Signed/distributional nonlocal completion remains outside theorem.
- **New insight:** Positive nonlocality cannot regularize the FZZ functional-equation reflection. Three source moments force deterministic reciprocal transport before analytic continuation.
- **Status:** `[PROVED HERE]` in `ThetaCuspHawkingFZZParityPositiveNonlocalFEReflectionCollapse.lean`. Direct Lean check and targeted module build pass. Four key declarations have axioms only `propext`, `Classical.choice`, `Quot.sound`. Module is wired into `RHTower.lean`. Global lint reports unrelated concurrent unwired modules and no error for this module.

## Novelty audit

Zero-variance/Dirac rigidity is classical. FZZ duality, cigar reflection operators, and Mellin/Hankel reflection are established literature. Search found no prior application of these three Fermi-weighted reflected rows to classify positive FZZ nonlocal kernels or close this RH-route loophole. Novelty claim is limited to that source-specific classification and consequence.

## Log

- 2026-08-30 — corpus audit rejected duplicate HB fixed-form conjectures and isolated positive nonlocal FZZ completion as harder live producer.
- 2026-08-30 — paper proof closed by exact Fermi-weighted variance identity.
- 2026-08-30 — formalized, axiom-audited, wired, and targeted-build verified.
