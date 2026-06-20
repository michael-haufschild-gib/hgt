# Finite-kernel integral noncapture — no finite DA-kernel integral machine

- **ID:** ht-c05-integral-kernel-noncapture
- **Stage:** 0-backlog
- **Type:** CONJECTURE
- **Source:** ../../door/bucket-hypertranscendence.md · C05
- **Statement:** Generic `f ∈ HT_K` is not the solution of a finite algebraic integral equation with differentially algebraic kernel(s) `∫_a^x K_i(x,t,f(t),…,f^{(r)}(t))dt` combined algebraically over `K`.

## Goal
Block a **finite integral handle** reconstructing `f` from a DA kernel and finitely many integral operations. Door: HT does not forbid integral equations, so generic absence of a *finite algebraic* one is a real claim.

## Door grade (hint)
**BRIDGE-likely.** Differentiating an integral equation usually removes the integral and yields a differential equation.

## Approach
Elimination test: differentiate the integral equation `r+1` times (Leibniz on the kernel) to eliminate `∫`; if a differential polynomial in `f` results ⇒ Hölder ⇒ BRIDGE. The surviving case is a kernel whose DA structure resists differentiation-to-finite-order. Methods: 6 ask what action, 14 weaken, 18 look for the right theorem (Volterra/elimination).

## Gates
- [ ] 0 → 1  in-progress: well-posed over a fixed base K and function category; source-pure; attack idea; Door passport sketch
- [ ] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean theorem, `lake build` green, `check_axioms.sh` PASS
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Cross-references
- `../../door/bucket-hypertranscendence.md` · C05; C02, C06 (functional/transform handles).

## Log
- 2026-06-20 — created in 0-backlog from bucket C05.
