# DSS-cross = Schanuel for prime-logs (the open apex — `ω_mot=0` / `K` free)

- **ID:** dss-cross-equals-schanuel-prime-logs
- **Stage:** 0-backlog (the **still-open part** of the split `omega-splits` ticket — moved here from `5-failed`, where only the falsified route remains)
- **Type:** OPEN CORE / CONJECTURE (native) — **FIELDS MEDAL.** Honest status: the *reduction* to this statement is **proven**; the statement itself is **open** and is **not** to be faked (it implies the algebraic independence of `{ζ(odd)}`-class data).
- **Priority:** FIELDS MEDAL
- **Source:** the three-way split of `omega-splits-wild-kernel-freeness.md` (user-directed 2026-06-19); the proven corank reduction in `f1-inversion-single-prime-stieltjes-collapse.md`; `compute-omega-h2-gl.md` §U/§V; `corank-seam-invariant.md` (#125); ../../door/bucket-the-seam-archimedean-obstruction.md

## The open conjecture
> **`ω_mot = 0 ⟺ K` (wild kernel) free ⟺ DSS-cross ⟺ `trdeg_ℚ\{γ_n\} = ∞` ⟺ Schanuel for prime-logs** (`{\log p}` algebraically independent).

## What is PROVEN (the reduction — see `f1-inversion…`)
- **`trdeg\{Stieltjes\,of\,ζ_S\} = trdeg\,ℚ(\log p:p∈S)`** for Euler truncations `ζ_S=∏_{p∈S}1/(1-p^{-s})` (symmetric-function generation). So the apex `corank ∞ ⟹ trdeg ∞` **is exactly** Schanuel-for-prime-logs — *derived, not assumed.*
- **corank-1 (one Frobenius):** `γ_n^{(q)}=B_n^{+}(\log q)^n/n!` — `trdeg 1` (proven, Bernoulli). ⟹ the **F₁ inversion**: a single Frobenius would *collapse* `trdeg` to 1 and **destroy** DSS; its absence is the *mechanism*, not the obstacle.
- **corank-2 rung:** `trdeg ≥ 1` PROVEN (Gelfond–Schneider: `γ_0^{(2,3)}` transcendental via `\log2/\log3`); `trdeg=2 ⟺ \{\log2,\log3\}` algebraically independent — the first **open** Schanuel rung.
- **Hölder:** `ζ` not D-finite ⟹ `{γ_n}` not P-recursive (no recurrence-relations).

## What is FALSE (ruled-out routes — see `5-failed/omega-splits…`)
- The `K`-freeness/`H²(free Lie)=0` Galois route (trivial unipotent gerbe — no Schanuel bypass).
- `F₁` = the Stokes automorphism (the local wild monodromy is Tate — A5).

## The honest target (the only piece that is open and not Fields-Medal-immediate)
The **monotonicity / corank→trdeg lower bound**: *each genuinely new `ℚ`-independent `\log p` lifts `trdeg\{γ_n\}` by ≥1.* Its first rung (`corank 1 → 2`) = "`\log2,\log3` algebraically independent" — open even there. Proven floor: corank-1 exact, corank-2 transcendence (G-S). **Attack the rungs; do not try to construct `F₁` (self-defeating).**

## Cross-references
- `f1-inversion-single-prime-stieltjes-collapse.md` — the proven reductions + the inversion (the live approach to this apex).
- `archimedean-wild-monodromy-tate-local.md` — A5 + the Ext–Hodge dictionary (paper-proven; rules out the local/Stokes attack).
- `../5-failed/omega-splits-wild-kernel-freeness.md` — the falsified `K`-freeness route.
- `corank-seam-invariant.md` (#125), `compute-omega-h2-gl.md` §U/§V — the seam / `ω` program.

## Gates
- [ ] 0 → 1: the apex is well-posed and *reduced* (= Schanuel for prime-logs, proven reduction); the open content is the monotonicity rungs.
- [ ] 1 → 2: a rung (`corank 2`, i.e. `\log2,\log3` alg-indep) — Fields-Medal; **not** to be fabricated.

## Log
- 2026-06-19 — created as **Part 3 (still open)** of the omega-splits three-way split (user: "move the still open part ticket back into backlog"). States the open apex `ω_mot=0 ⟺ DSS-cross ⟺ Schanuel for prime-logs`, with the **proven reduction** and **proven floors** (corank-1 exact, corank-2 Gelfond–Schneider) cross-referenced, and the falsified/proven parts pointed to their homes. The apex is open and explicitly not to be faked.
