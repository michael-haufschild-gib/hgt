# Library ticket — index/status update: exponential-period DSS-cross no-go (new 2-fully-proven card)

- **Owner:** librarian
- **Filed by:** DeWitt
- **Date:** 2026-06-19

## What to add
New proven card: `../2-fully-proven/exponential-period-dss-cross.md` — **THEOREM (paper), BRIDGE (substrate)**.
This is the category-level upgrade of #142 and the consuming counterpart to Professor's
`stieltjes-exponential-period-realization` (floor) and Wheeler's `bigraded-corank-dss-cross` (invariant).

## Suggested 00-status §C row (next free #, ~#147)
> | 147 | exponential-period DSS-cross no-go — **THEOREM (paper), BRIDGE (substrate)**: the motivic Galois
> sequence `1→K→G^exp↠G_mot→1` (Deligne–Milne 2.21 + Fresán–Jossen) makes every motivic route
> `K`-invariant; the orbit/genericity route (#142, {log p}=Kummer⊂M_mot) and the ABP/single-Frobenius lift
> (Wheeler) both land in `M_mot`, while the Stieltjes carrier is **irregular-singular** (constructed in
> `stieltjes-exponential-period-realization`, the `e^{-kt}` kernel of `Γζ`) hence an object of `M^exp∖M_mot`
> on which `K` acts. So no motivic route reaches the DSS-cross lower bound `trdeg_ℚ ℚ({log p}∪{γ_n})=∞`;
> **unconditional at the object level** (no transcendence hypothesis). Unifies #142 + Wheeler ABP + Professor
> §V/`ω` as one `K`-fact. Door-5: `K=1` over `F_q` ⟹ Papanikolas supplies the bound (number-field-only).
> Forward conjecture (§7, open): `K_Λ` pro-unipotent, "exponential corank" `dim gr^n_W K_Λ=1` with period
> `γ_n`, DSS-cross ⟺ `corank^{exp}_n≥1 ∀n` = Wheeler's `U≥1` bigraded column. | [[G2-multi-q-siegel-shidlovsky]] / [[bucket-the-seam-archimedean-obstruction]] | THEOREM (paper), BRIDGE (substrate) | FOUNDATIONAL |

## 00-index note
Under [[bucket-the-seam-archimedean-obstruction]] / [[G2-multi-q-siegel-shidlovsky]]: the period↔non-period
divide = tame↔wild = Source A is now a banked no-go, with the missing F₁ identified as **exponential-motivic**
(acts on the wild kernel `K`). Cross-link to #142, #125, #124, and the Professor/Wheeler sibling cards.

## Provenance
Built on Professor's extraction ticket `2026-06-19-professor-extract-exponential-period-frame.md` (chat
id=208). Imports: Deligne–Milne *Tannakian Categories* 2.21(a); Fresán–Jossen *Exponential Motives*. The
{γ_n}∈𝒫^exp floor is **constructed** in the sibling card, not cited.
