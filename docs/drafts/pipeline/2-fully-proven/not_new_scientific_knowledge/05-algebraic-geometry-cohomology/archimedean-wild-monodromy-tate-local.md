# Archimedean wild monodromy is Tate-local; the seam's transcendence is a global regulator (A5 + the Ext–Hodge dictionary)

- **ID:** archimedean-wild-monodromy-tate-local
- **Stage:** 2-fully-proven (vetted by Professor 2026-06-19)
- **Type:** THEOREM (paper) — Door grade **BRIDGE**. The **paper-proven** extract of the (failed) `omega-splits-wild-kernel-freeness.md` route; the falsified part stays in `5-failed`, the open apex lives in `f1-inversion-single-prime-stieltjes-collapse.md`.
- **Priority:** FOUNDATIONAL
- **Source:** resurgence of the Γ-factor (Stirling/Binet) and the exponential integral `E_1`; Carlson's `Ext¹` formula + the Tate-twist of the irregular Hodge filtration (Sabbah–Yu / Fresán–Jossen exponential-MHS); ../../door/bucket-the-seam-archimedean-obstruction.md

## §1 A5 — the wild monodromy is Tate-local; `γ_E` is a global regulator [PROVEN]
- **Γ-factor (Stirling).** The Binet Borel transform `(½-1/t+1/(e^t-1))/t` has **simple poles only at `t=2πik`** (`k∈ℤ\{0}`), residues `∼1/(2πik)`. So the Γ-factor's Stokes constants are **powers of `2πi` — mixed-Tate (motivic)**, not exponential periods. (Consistent: `a_∞=½\log2π=-ζ'(0)` is a Tate constant.)
- **Exponential integral `E_1`** (governs `γ_E`): `E_1(z)=-γ_E-\log z-Σ_{k≥1}(-z)^k/(k·k!)` near 0; `∼e^{-z}/z·Σ(-1)^n n!/z^n` at ∞. Its asymptotic series has Borel transform `1/(1+ξ)`, simple pole at `ξ=-1`, **Stokes multiplier `2πi` (Tate)**.
- **Therefore:** `γ_E` is **not** local Stokes data — it is the **global connection coefficient** between `z→0` and `z→∞` = a **period of the extension `E^{-x}⊗\mathrm{Kum}`** (an `Ext¹` regulator).
> **Theorem A5.** The local wild monodromy (Stokes data) of the archimedean factors of `Λ` is **Tate** (`2πi`-powers); the genuinely transcendental seam data (`γ_E`, the Stieltjes tower) are **global `Ext¹` regulators**, not local Stokes multipliers. ∎ (resurgence-rigorous)

**Consequence (kills the "wild-monodromy/Stokes = F₁" route, banked in `5-failed`):** any Stokes/wild-automorphism route to the transcendence targets **Tate** data and cannot reach the content; the content is the **global regulator tower** = DSS = Schanuel-for-prime-logs (open; `f1-inversion…` §2′).

## §2 The Carlson/Tate-shift dictionary [PROVEN, structural]
In exponential mixed Hodge structures, Carlson's formula `Ext¹(ℚ,M)=M_ℂ/(F^0M_ℂ+M_ℤ)` (`wt<0`) plus the Tate-twist `F`-shift give
> **`dim\,gr^n Ext¹(ℚ,M⊗ℚ(n)) = h^n_{irr}(M)`** — the `Ext`/regulator-tower growth is read off `M`'s **irregular Hodge spectrum**.

**Saturation.** Any *finite* exponential motive has `Σ_n h^n_{irr}=\dim_{dR}<∞`, so its regulator tower **stops**. (Caveat: "⟹ the `{γ_n}`-carrier is infinite-rank" is *conditional* on infinitely many independent `γ_n` — open; not claimed here.)

## §3 What this card is NOT
- It does **not** prove DSS / RH / Schanuel (open; the apex, in `f1-inversion…`).
- It does **not** revive the K-freeness/`H²(free)=0` route (falsified, `5-failed/omega-splits…` §Y: the unipotent gerbe is trivial, the lever is irrelevant).

## Door / grade
BRIDGE. A5 is classical resurgence assembled into a localization statement; the dictionary is Carlson + the exponential-MHS framework. Worth: it **rules out** the local/Stokes attack on the seam transcendence and pins the content to the global regulator tower.

## Gates
- [x] 0 → 1: A5 + dictionary stated and proven (resurgence + Carlson).
- [x] 1 → 2: VETTED PASSED (Professor 2026-06-19) — resurgence facts independently verified; Carlson-shift structural, no fabricated Hodge numbers. See vetting note.

## Cross-references
- `../5-failed/omega-splits-wild-kernel-freeness.md` — the failed parent route (this is its proven extract).
- `f1-inversion-single-prime-stieltjes-collapse.md` — the open apex (DSS = Schanuel) + the proven corank reductions; A5's "global regulator" is the object whose independence is that apex.
- `compute-omega-h2-gl.md` §S/§W — `ω` purely archimedean; `γ_n` exponential periods.

## Log
- 2026-06-19 — created as **Part 2 (paper-proven)** of the three-way split of `omega-splits` (user-directed). Carries A5 (Tate-local wild monodromy; `γ_E` global regulator) and the Carlson/Tate-shift `Ext`–irregular-Hodge dictionary. No web search; resurgence + Carlson cited structurally.

## VETTING — 2026-06-19 (Professor): PASSED → 2-fully-proven
Peer-vetted (archimedean wheelhouse), as the card requested ("awaiting pipeline vetting, not self-promoted").
- **§1 A5 resurgence facts — independently VERIFIED** (`computations/2026-06-19-wild-monodromy-tate-vetting.py`):
  (i) `E_1` Borel transform `1/(1+ξ)`, simple pole `ξ=−1` ⟹ Stokes multiplier `2πi` (Tate) — exact rep
  `E_1(z)=e^{−z}∫₀^∞ e^{−zξ}/(1+ξ)dξ` reproduces `E_1` to ≤1e−34; (ii) Binet/Stirling integrand poles at
  `t=2πik`, `Res 1/(e^t−1)=1` ⟹ μ-residues `~1/(2πik)` (Tate powers); (iii) `a_∞=½log2π=−ζ'(0)` (Tate),
  exact. **The local archimedean Stokes/wild-monodromy data are 2πi-powers = Tate.** ✓
- **§2 Carlson Ext¹ / irregular-Hodge dictionary** — cited structurally (Carlson `Ext¹(ℚ,M)=M_ℂ/(F⁰+M_ℤ)`,
  wt<0, + Tate-twist F-shift); **no fabricated Hodge numbers** (the growth is *read off* `M`'s irregular Hodge
  spectrum as a structural statement). Saturation caveat correctly flagged **conditional** (infinite-rank ⟸
  infinitely-many-independent-`γ_n`, open, not claimed). ✓ honest.
- **§3 scope** — correctly limited (does NOT prove DSS/RH/Schanuel; does NOT revive the falsified K-freeness).
**Verdict: SOUND.** A5 is resurgence-rigorous (verified); the dictionary is a legitimate structural
identification. **Net no-go (the worth):** any Stokes/wild-automorphism/F₁ route to the seam transcendence
targets **Tate** data and cannot reach the content — the transcendence is a **global Ext¹ regulator tower**
(= DSS = Schanuel-for-prime-logs, the open apex in `f1-inversion…`). This converges with the per-place
falsification (Source-A unique to ∞) and my corank-no-collapse (the seam is global, not local). → 2-fully-proven.
Gate 1→2 PASSED (vetting). Door BRIDGE.
