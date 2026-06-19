# Ticket: three-way split of the omega-splits ticket + index/status update

**Date:** 2026-06-19 (user-directed: "split the ticket — the part provably false, the part with paper proof, the part still open")
**Type:** disposition + index/status update (do not edit door/00-* directly — race avoidance)

## The split (three definite homes)
1. **Provably false** → `../5-failed/omega-splits-wild-kernel-freeness.md`. The `K`-freeness/`H²(free)=0` route (§Y: the wild kernel is pro-unipotent over ℚ ⟹ its neutrality gerbe is trivial `H^i(ℚ,U)=0`, so `H²(free)=0` is irrelevant — no Galois bypass of Schanuel) and Moonshot 2 (`F₁`=Stokes automorphism, refuted by A5). A "SPLIT DISPOSITION" table was added at the top of that card.
2. **Paper-proven** → NEW `../0-backlog/archimedean-wild-monodromy-tate-local.md` (THEOREM paper, BRIDGE): **A5** (the archimedean wild monodromy of `Λ`'s factors is **Tate-local** — Γ-Stirling and `E_1` Stokes constants are `2πi`-powers; `γ_E` is a **global `Ext¹` regulator**, not local Stokes) + the **Carlson/Tate-shift dictionary** `dim gr^n Ext¹(ℚ,M⊗ℚ(n))=h^n_{irr}(M)` with finite-motive saturation.
3. **Still open (apex)** → NEW dedicated open-core ticket `../0-backlog/dss-cross-equals-schanuel-prime-logs.md` (the open conjecture itself, moved back to backlog out of `5-failed`), with the **live approach + proven reductions** in `../0-backlog/f1-inversion-single-prime-stieltjes-collapse.md`. Together they carry the **proven corank reductions** and the **open apex**:
   - **THEOREM (proven):** `trdeg\{Stieltjes\,of\,ζ_S\}=trdeg\,ℚ(\log p:p∈S)` for Euler truncations `ζ_S=∏_{p∈S}1/(1-p^{-s})`; corank-1 collapse exact (`γ_n^{(q)}=B_n^+(\log q)^n/n!`, trdeg 1); corank-2 rung exact with a **Gelfond–Schneider transcendence floor** (`γ_0^{(2,3)}` transcendental via `\log2/\log3`), `trdeg=2 ⟺ \{\log2,\log3\}` alg-indep.
   - **The F₁ inversion:** a single Frobenius collapses `trdeg` to 1 — so the *missing* F₁ is the **mechanism** of DSS, not the obstacle.
   - **OPEN apex:** `corank ∞ ⟹ trdeg ∞` = **DSS-cross = Schanuel for prime-logs** (Fields-Medal). Not proven, not faked.

## Status/door note (suggested)
- `00-status`: mark the `K`-freeness/`H²(free)=0` route **FALSIFIED** (a new `5-failed` row); add the **corank=trdeg reduction** as a proven BRIDGE row sharpening #125 (`trdeg=corank` now an exact identity for Euler truncations, with proven corank-1/corank-2-floor); add A5 (Tate-local) as a proven BRIDGE row in the seam bucket. **No NATIVE/C5 count change.**
- **#125 sharpening:** the seam's `trdeg=corank` is no longer only asserted — it is **proven for the Euler-truncated model**, and the apex is pinned exactly as **Schanuel-for-prime-logs** with a Gelfond–Schneider floor at rung 2.
- **Reconception to record (bucket-the-seam / #128):** the missing single Frobenius `F₁` is **DSS-generating-by-its-absence**, not DSS-proving-by-its-presence — its existence would algebraize the `γ_n` (trdeg 1) and kill DSS.

## Net
omega-splits ticket fully dispositioned: **1 falsification** (5-failed), **2 paper-proven extracts** (A5+dictionary card; the corank-reduction theorem in f1-inversion), **1 open apex** (Schanuel-for-prime-logs, in f1-inversion). No native/C5 count change.
