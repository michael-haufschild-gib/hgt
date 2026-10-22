# Theorem M = the proven with-margin endpoint of the no-margin / S_d structure

- **ID:** theorem-m-with-margin-endpoint
- **Stage:** 0-backlog (self-authored 2026-06-19; awaiting pipeline vetting)
- **Type:** STRUCTURAL (connection) — claimed Door grade **BRIDGE**; anchors the no-margin/#104 program to a proven, machine-verified theorem and names the exact gap to RH
- **Source:** `publications/theorem-m/docs/preprint/main.tex` (Haufschild, *Unconditional hyperbolicity of the critical Laguerre family*, 2026, Lean-verified, read in full); relates `dewitt-supermetric-no-margin.md` (Findings 3c/4), `finite-free-convolution-flow.md` (#104), `c5-jensen-prime-kernel.md`; ../../../../door/bucket-the-no-margin.md
- **Statement:** Theorem M proves unconditional hyperbolicity of a **positive** moment deformation of the archimedean Hermite carrier via energy + sign-transfer. It is the proven, with-margin, sign-definite case of the exact `A_d`/`S_d` structure whose zero-margin, signed boundary is RH. The two obstructions to transferring its proof to RH are named precisely: **sign-definiteness** and **margin**.

## What Theorem M is
`C_d(w)=₁F₁(−d;½;w²/4d)=He_{2d}(w/√{2d})/He_{2d}(0)` — the critical Laguerre family = rescaled even Hermite, the **archimedean carrier** (even, deg `2d`, `C_d(0)=1`, real simple zeros). Deformation `Ψ_d(w)=𝔼[C_d(√U·w)]=p·C_d(w)+∫_{(0,1]}C_d(vw)dμ(v)`, where `U∈(0,1]` is compound-Poisson with **atom `p=Prob(U=1)=√(2/e)=0.858`**, `μ≥0` of mass `1−p`. **Theorem M (Lean, 0-sorry, Nanoda-rechecked): all `2d` zeros of `Ψ_d` are real, every `d`.**
Mechanism: energy `E=C_d²+C_d'²`, `E'=(x/d)C_d'²≥0`, `E(0)=1` ⟹ **`|C_d(c)|≥1`** at each critical point `c` + **segment domination `|C_d(vc)|≤|C_d(c)|`** (`v∈[0,1]`); then `p>½` (the single inequality `8>e`) ⟹ `|Ψ_d(c)−pC_d(c)|≤(1−p)|C_d(c)|<p|C_d(c)|` ⟹ `Ψ_d` copies `C_d`'s critical signs ⟹ `d` sign changes ⟹ hyperbolic.

## The identification with the no-margin / S_d structure (Finding 3c, #104)
- `C_d` **is** the archimedean Hankel carrier `A_d` (the GORZ→Hermite limit defining `A_d`, #104). Theorem M's floor `|C_d(c)|≥1` is the **same floor Wheeler's #104 reuses** for the ζ sign-transfer.
- Theorem M's deformation is a **positive measure** `μ≥0` (averaging of down-scaled copies — RH-blind). ζ's prime fluctuation `δH_d` is **signed/oscillatory** (the mixed-sign combination modes, support `≤d`).
- Theorem M sits **strictly inside the positive cone**: `λ_min(S_d)>−1`, uniform factor-6 margin `(1−p)/p=0.166` (preprint Rem. sharpness). ζ sits **on the Sylvester floor**: `inf_{d,t}λ_min(S_d)=−1`, the no-margin, atom `p→½⁺` (Finding 3c).

## The two obstructions to transferring the proof to RH (the payoff)
1. **Sign-definiteness (amplitude vs phase).** Theorem M controls the deformation by an **amplitude** bound (segment domination, unconditional). The ζ perturbation at the critical points, `sup_t|D_d(c_m;t)|` (`c5-jensen-prime-kernel` §6), is a **phase-cancellation** quantity — it **diverges absolutely** (`Σ_p p^{-1/2}(log p)^a=∞`), so no amplitude/triangle bound can exist; only phase cancellation can control it.
2. **Margin (`p>½` vs `p=½`).** Theorem M's atom `p=√(2/e)>½` has room. RH is the **boundary** `p→½` — the no-margin, `inf λ_min(S_d)=−1` reached exactly (Finding 3c; the lower half `λ_c≥1` = Rodgers–Tao).

**Net.** Theorem M is the machine-verified proof that the **energy + sign-transfer architecture is sound** — it yields unconditional hyperbolicity in the **amplitude-controlled, with-margin** regime. RH is the **same architecture** at the **phase-cancellation, zero-margin** boundary. The exact gap is *amplitude control (proven) vs phase-cancellation control (open)* = Wheeler's #104 open crux = the `c5-jensen` §6 divergence — now anchored to a proven theorem. Theorem M certifies the route is **not vacuous** and isolates the gap as phase-cancellation at zero margin, not a flaw in the mechanism.

## Coda — pair-specificity (a constraint, not a generative rule)
Theorem M's `(M_k)` is provably **not** a Pólya–Schur multiplier sequence (moment sequences are log-convex, multiplier sequences log-concave); hyperbolicity is a property of the **pair** (sequence, family), not of a universal preserver. So RH-positivity too is pair-specific (the prime sequence × the ζ carrier), not a generative rule — consistent with the charter's *"fixed by a constraint, not propagated by a flow."* The atom `p` is the weight on the un-rescaled archimedean carrier; **RH ⟺ the effective atom is exactly `½` (Theorem M's inequality at its boundary), saved by phase-cancellation of the signed prime fluctuation** — a concrete Theorem-M-anchored reformulation of the no-margin (seed, for `bucket-the-no-margin`).

## Door grade — BRIDGE
Theorem M itself is elementary + Pólya–Schur-adjacent (parents); the connection is a structural identification (no native apparatus). Its worth: it pins the **proven** endpoint of the no-margin program and names the open crux as phase-cancellation-at-zero-margin, sharpening #104's Door-2 line (BRIDGE iff a parent large-values/Halász method gives the phase bound; native iff support-`≤d` near-resonance is essential).

## Gates
- [x] 0 → 1 / 1 → 2: connection established from the read preprint + Findings 3c/4 + #104 + c5-jensen §6. No open dependency (Theorem M is proven; the gap to RH is named, not closed).
- [ ] 2 → 3: n/a (connection card) — the Lean object is Theorem M's own tree (`github.com/michael-haufschild-gib/theorem-m`, 0-sorry).

## Cross-references
- `dewitt-supermetric-no-margin.md` Finding 3c — the `A_d`/`S_d`/`λ_c` identity this anchors.
- `finite-free-convolution-flow.md` (#104) — the signed, zero-margin ζ carrier; its energy floor reuses Theorem M's `|C_d(c)|≥1`.
- `c5-jensen-prime-kernel.md` §6 — `sup_t|D_d(c_m;t)|`, the phase-cancellation quantity (the obstruction-1 object).
- `../../../../door/bucket-the-no-margin.md` — the home for the "effective atom = ½" reformulation.

## Log
- 2026-06-19 — created from a full read of the Theorem M preprint, after the DeWitt-supermetric / `S_d` / `λ_c` synthesis. Identifies Theorem M as the proven with-margin, sign-definite endpoint of the no-margin/#104 structure (`C_d=A_d`, shared floor `|C_d(c)|≥1`), and names the two obstructions to RH-transfer (sign-definiteness = amplitude-vs-phase; margin = `p>½` vs `p=½`). BRIDGE. No web search.

## R10 finding (2026-06-20, novelty loop) — the carrier is cosine; the no-margin is π²/(8d); margin is a red herring `[BRIDGE]`

The crude floor `|C_d(c)|≥1` that Theorem M relies on is the amplitude of a **cosine**, and its slack is computable.

**Lemma A (carrier = cosine).** `C_d` obeys the rescaled Hermite ODE `f''−(w/2d)f'+f=0`; as `d→∞`, `f''+f=0`,
`f(0)=1`, `f'(0)=0` ⟹ **`C_d(w)→cos w`** on compacts. The floor `|C_d|≥1` is cosine's amplitude; the innermost
valley → cosine's valley `(π,−1)`. (`C_d''(0)=−1` for all d.)

**Lemma B (valley law).** Perturbation `f=cos w+f_1/d`, `f_1''+f_1=−(w/2)sin w`, `f_1(0)=f_1'(0)=0` ⟹
`f_1(w)=(w²/8)cos w−(w/8)sin w`, `f_1(π)=−π²/8`. So **`V_d := |`shallowest valley`| = 1 + π²/(8d) + O(1/d²)`**,
at `w=π+O(1/d)`. Numerically confirmed: `d·(V_d−1)→π²/8=1.23370` to 4 digits (d=50..640, local mpmath).

**Corollary (threshold not sharp; relaxes p>½ → p≥½).** Constant-shift `Ψ_d^0=pC_d+(1−p)` is hyperbolic iff
`p≥1/(1+V_d)=½−π²/(32d)<½`. At `p=½` exactly it is hyperbolic for **every finite d** (all valleys `<−1`
strictly), with margin `V_d−1=π²/(8d)`; the no-margin (double zero at the cosine valley) appears only as
`d→∞`. For general non-degenerate `μ`, strict segment domination gives hyperbolicity at `p=½` too. So Theorem
M's `p>½` is sufficient-not-necessary; the necessary margin is `π²/(8d)→0`.

**Reframing — DEMOTES obstruction 2 (margin).** The two stated obstructions are NOT co-equal. Margin is
benign: the proven *positive* deformation reaches `p=½` with vanishing margin `π²/(8d)` and stays hyperbolic
(the cosine floor protects it). The no-margin `p→½` is an `O(1/d)` feature shared by Theorem M's own positive
world — not the wall. **The sole genuine obstruction to RH is obstruction 1 (sign/phase):** the signed prime
`δH_d` removes the cosine-valley protection (its averaged contribution is not amplitude-dominated), so only
phase cancellation can keep the zeros real. *Margin is asymptotically free; the wall is the sign.* Full
derivation + self-judgment (prior ~25, significance ~40, proof ~68) in
`logs/2026-06-20-novelty-generation-loop.md` Round 10.

**Forward lead (the C5 crux, now numeric):** compute the innermost-valley behaviour of the *signed* `δH_d`
carrier and test whether phase cancellation alters the `π²/(8d)` rate or flips the valley-excess sign — that
is the amplitude→phase transition, with a concrete number to chase.
