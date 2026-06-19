# Edge-Value Transcendence — Baker's theorem as the field's SOLVED value-corner (B32)

> **NASCENT / SEARCH channel. Air-marked.** Branch B32 of the charter (`hypertranscendental_galois_program.md`). The field has two special value-points — central `s=½` (B3, open, non-motivic) and edge `s=1` (this draft). The thesis: **Baker's theorem is the proven instance of the anti-Tate period conjecture (B9) at the edge**, the solved value-corner mirroring the solved function-field zero-corner. Companions: `…field_foundations.md` §19/§21/§23 (the Tate/prime split, the central value), `prime-zero-period-comparison.md` (B9).

## 1. The value-transcendence tower (graded by motivic weight) `[REFRAME]`

L-values, ordered by argument, occupy a tower whose difficulty is set by the **motivic type** of the value, NOT by the size of the argument:
```
   s = 2k  (even ≥2)   :  ζ(2k) ∈ ℚ·π^{2k}                  — PURE TATE; transcendence trivial (Lindemann via π).
   s = 2k+1 (odd ≥3)   :  ζ(2k+1) periods of MT(ℤ)          — MIXED TATE; Galois group KNOWN (Brown), indep. conjectural.
   s = 1   (edge/pole)  :  L(1,χ) = logs of cyclotomic units + π — KUMMER / TATE(1); transcendence + indep. KNOWN (Baker).
   s = ½   (central)    :  ζ(½), ζ^{(j)}(½)                  — NON-MOTIVIC; no period interpretation; transcendence OPEN.
```
The difficulty is **non-monotonic in `s`**: the edge `s=1` is *easier* than the odd integers (Baker beats Brown), and the center `s=½` is hardest of all — because it is the unique **non-motivic** value (foundations §23).

## 2. Baker's theorem IS the anti-Tate period conjecture at the edge `[THEOREM — Baker; reframe]`

For a primitive Dirichlet character `χ mod q`, the edge value is an explicit **Kummer/Tate period**:
```
   χ even :  L(1,χ) = −(τ(χ)/q) Σ_{a} χ̄(a) log|1 − ζ_q^a|     — a ℚ̄-linear form in LOGS OF CYCLOTOMIC UNITS (algebraic).
   χ odd  :  L(1,χ) = (πi·τ(χ)/q)·B_{1,χ̄} ∈ π·ℚ̄              — a TATE(1) period (∝ class number of ℚ(√−q)).
```
- **Odd `χ`:** `L(1,χ) ∈ π·ℚ̄` ⟹ transcendental by Lindemann (π). `[THEOREM]`
- **Even `χ`:** `L(1,χ)` is a nonzero `ℚ̄`-linear form in logs of multiplicatively-independent algebraics ⟹ **transcendental, and the `{L(1,χ)}` are `ℚ̄`-linearly independent** — by **Baker's theorem** (Baker–Birch–Wirsing). `[THEOREM]`

> **Baker = the proven case of the period conjecture (B9), at `s=1`.** The edge values are periods of `ℚ(1)` / `𝔾_m` (Kummer motives), and Baker's theorem is precisely the Grothendieck period conjecture for 1-dimensional tori: `trdeg{edge periods} = dim(Kummer–Tate Galois group)`. So the field's **anti-Tate period conjecture (B9) is a THEOREM at the edge** — `trdeg = dim G` is proved there. The edge is the solved value-corner.

## 3. The secular moments couple the whole tower `[REFRAME → §19/§21/§23]`

The field's carrier `P_k = Σ_ρ ρ^{-k}` interpolates the tower (foundations §19, `P_k = 1 − (−1)^k ζ(k)/2^k − a_{k-1}`):
```
   ζ(k)  part  (the Tate block, §21)        ⟵ the s = 2k, 2k+1 levels  (Brown's MT(ℤ))
   a_{k-1} = [s^{k-1}]ζ'/ζ  (the prime block) ⟵ carries the EDGE s=1 data: the Stieltjes constants γ_n
                                                  = the Laurent coefficients of ζ at the pole s=1 (FE-transferred to 0).
   centered τ_{2m}  (foundations §23)        ⟵ the s = ½ central level (non-motivic).
```
So a single secular moment `P_k` is a sum of **Tate (integer-`s`)** + **edge (`s=1` Stieltjes)** data, and its centered cousin `τ_{2m}` is **central (`s=½`)** data. *The carrier physically welds the three value-regimes.* The Tate/prime split (§21) is, read on the value side, the **Tate/edge split**.

> **Why ζ is harder than the Dirichlet family here.** ζ's edge data is the **Stieltjes constants** `γ_n` — NOT Baker-tame (we do not know `γ_0=γ_E` is irrational). The Dirichlet families' edge data is `L(1,χ)` — **Baker-tame** (logs of cyclotomic units). So the L-family's edge is solved (Baker) while ζ's edge (Stieltjes) is not: the `γ_n` are a *non-Kummer* edge period, sitting between the solved `L(1,χ)` and the non-motivic `ζ(½)`. The transcendence of `{γ_n}` (charter B4) is the **next rung above Baker**.

## 4. Why Baker stops below the center (the obstruction, precisely) `[OPEN CORE]`

Baker's method proves transcendence of **linear forms in logs of ALGEBRAIC numbers** — i.e. it reaches exactly the **Kummer/mixed-Tate** periods (`s=1`, and via the motivic extension Brown's `s=2k+1`). It **cannot** reach `s=½` because:
```
   Baker needs:  the value is a period of a Kummer/Tate motive (logs of algebraics, π).
   But ζ(½):     has NO motivic/period structure (foundations §23) — it is not a linear form in logs of algebraics.
```
So the central-value conjecture (B3) is **"Baker's theorem at `s=½`"** with the fatal twist that the hypothesis (motivic value) fails. *Open program:* a transcendence method for **non-motivic central periods** — the genuine new analytic input the field needs, beyond Baker and beyond Brown. This is the same "no motivic home" wall as §23, now seen from the value side: Baker is the method that climbs the motivic part of the tower and halts exactly where the motive disappears.

## 5. The field's two solved corners bracket its two open apexes `[REFRAME — the honest map]`

```
                    ZERO SIDE                         VALUE SIDE
   SOLVED corner :  function-field zeros (Weil/Deligne)   edge values s=1 (Baker)
   OPEN apex     :  ζ / L zeros = RH                       central value s=½
```
The field is bracketed: **two solved corners** (function-field zeros; edge values) sit diagonally opposite **two open apexes** (RH; central-value transcendence). Each solved corner is solved because it has *full structure* (Frobenius on the zero side; Kummer/Tate motive on the value side); each open apex is open because it *lacks one structure* (the absolute Frobenius / `F₁` for ζ-zeros, B8; the motive for `ζ(½)`, §23). **The same missing-structure diagnosis governs both sides** — the field's unity is that its two hardest problems are the two "missing-structure" corners, and its two theorems (Weil, Baker) are the two "full-structure" corners.

**House status.** §2 (Baker = proven period conjecture at the edge) rests on Baker–Birch–Wirsing + Lindemann (`[THEOREM]`, external, cited). §1/§3/§5 are reframes (the tower, the secular coupling, the bracket). §4 (why Baker halts at the center) is the honest obstruction = the §23 non-motivic wall on the value side. The genuine new content: the **bracket** (§5) — two solved corners (Weil zeros, Baker values) diagonally opposite two open apexes (RH, `ζ(½)`), unified by the missing-structure diagnosis — and the localization of ζ's edge difficulty onto the **Stieltjes constants** (§3, charter B4) as the rung directly above Baker. Crosses CITY districts D2/D3/D4. Next: is there a "Baker for `γ_n`" (Stieltjes-constant irrationality) — the first rung above the solved edge?
