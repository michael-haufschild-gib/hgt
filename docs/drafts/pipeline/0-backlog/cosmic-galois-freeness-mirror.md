# The cosmic-Galois freeness mirror — DSS as the irregular image of Brown–Deligne–Goncharov, and the freeness asymmetry

- **ID:** cosmic-galois-freeness-mirror
- **Stage:** 0-backlog (CONJECTURE card; §1 mirror = BRIDGE-import, §2/§3 = the new conjecture)
- **Type:** CONJECTURE (the freeness asymmetry) + BRIDGE (the mirror map & the proven↔open diagnosis)
- **Priority:** FOUNDATIONAL (transcendence axis; sharpens the wild-kernel apex). Apex (DSS itself) = FIELDS MEDAL.
- **Owner:** DeWitt
- **Source / builds on:**
  - `omega-splits-wild-kernel-freeness.md` §2-cohomology (`H_1(Lie K)`=generators=exponential-corank,
    `H_2(Lie K)`=relations, `DSS ⟺ K free ⟺ H_2(Lie K)=0`; asserts `dim gr^n K = 1` per Laurent order)
  - `../2-fully-proven/bigraded-corank-dss-cross.md` §D (Wheeler — bigraded corank = associated graded of the
    joint exp-motivic Galois Lie algebra `𝒢`, conditional on GPC for `M^exp`)
  - `../2-fully-proven/exponential-period-dss-cross.md` §7 / `regularization-freshness.md` (#75 — the `γ_n` as
    exponential periods; the regular base `𝓡 = MT(ℤ)-periods · ℚ({log p})`)
  - `hypertranscendence-axis-synthesis.md` (the frame: transcendence axis primary, RH the orthogonal slice)
  - In-corpus import already accepted: the Deligne–Goncharov Galois group of `MT(ℤ)` is **known**
    (`../1-in-progress/compute-omega-h2-gl.md`:279; Professor's exponential-period frame, library-done).
- **Statement:** DSS-cross (= the wild kernel `Lie(K)` is free) is the **exponential/irregular analogue** of the
  *proven* Brown–Deligne–Goncharov theorem that the cosmic-Galois Lie algebra `Lie(U_{MT(ℤ)})` is free on one
  generator `σ_{2n+1}` per **odd** degree. The mirror is exact on the structure and explains the open/closed
  split (regular: motivic t-structure ⟹ proven; wild: no `GPC^exp` ⟹ open). It forces a new structural
  conjecture — a **freeness asymmetry**: graded by the **Tate twist `n`** of the Ext, the cosmic generators sit
  only at `n` odd ≥3 (Borel: `Ext¹_{MT(ℤ)}(ℚ,ℚ(n))≠0 ⟺ n` odd ≥3; series `t³/(1−t²)`), whereas the wild kernel
  conjecturally has a generator at **every** twist (`Ext¹_{M^exp}(ℚ,E^{−x}⊗ℚ(n))≠0 ∀n`) — in particular on
  **all the even twists, which are exactly Borel's vanishing locus**. The exponential twist `E^{−x}` is not pure
  Tate, so it resurrects a regulator `γ_n` where the motivic world has none. This makes "hypertranscendence is
  wider than RH" *quantitative*: the wild kernel lives precisely where the motivic Galois group is empty.

---

## §1 The mirror `[BRIDGE — import + structural map]`

**Regular side (THEOREM).** *Recalled import (Brown 2012, "Mixed Tate motives over ℤ", Annals; Deligne–
Goncharov 2005) — already accepted in-corpus as "Deligne–Goncharov Galois group known".* The Tannakian
fundamental group of the category `MT(ℤ)` of mixed Tate motives over `ℤ` (the **cosmic Galois group**, Cartier's
name) is `𝒰 ⋊ 𝔾_m`, with `𝒰` pro-unipotent and its graded Lie algebra
> `Lie(𝒰)` = **free graded Lie algebra** on one generator `σ_{2n+1}` in each **odd** degree `2n+1 ≥ 3`.

The generators are dual to the odd zeta values `ζ(3), ζ(5), ζ(7), …` and `H_2(Lie 𝒰)=0` (free ⟹ cohomological
dimension 1, no relations).

**Grounding — Borel, the generator count by Tate twist `[recalled bedrock import; no web per charter]`.** The
generator space is the Ext, computed by `K`-theory: for the Tate twist `n`,
> `Ext¹_{MT(ℤ)}(ℚ, ℚ(n)) ≅ H¹_{mot}(ℤ,ℚ(n)) ≅ (K_{2n-1}(ℤ)⊗ℚ)^{(n)}` (Beilinson–Soulé + Borel),
and **Borel's rank theorem** gives `dim = 1` for `n` **odd ≥3** (`n=3,5,7,… ↔ K_5,K_9,K_{13} ↔ ζ(3),ζ(5),ζ(7)`)
and `dim = 0` for `n` **even ≥2** and `n=1`. So, graded by the Tate twist `n`, the cosmic generators have
**Hilbert series `∑_{n odd≥3} t^n = t³/(1−t²)`**. The **even** twists vanish: there is **no regulator** for
`ℚ(2k)` — `ζ(2k)=(rational)·π^{2k}` is already a period of `ℚ(k)` itself ("trivial Tate", no new extension).
The even-twist vanishing is the precise content of "half the degrees collapse."

**Wild side (our DSS, CONJECTURE).** The wild kernel `1 → K → G^exp ↠ G_mot → 1` (Fresán–Jossen exponential
motives) has `Lie(K)` pro-nilpotent, graded by Laurent/exponential order `n`, with — per
`omega-splits-wild-kernel-freeness` §2 — one generator `γ_n` per order. The apex:
> **DSS-cross ⟺ `K` free ⟺ `H_2(Lie K)=0`.**

**The mirror map `[the BRIDGE content]`.** Under the dictionary
`regular ↔ irregular`, `period ↔ exponential-period`, `ζ(2n+1) ↔ γ_n`, `weight ↔ Laurent order`:
> **DSS-cross is precisely the exponential/irregular analogue of Brown's freeness theorem.**
The regular statement is a **theorem**; the wild statement is **open**. The map says *exactly where* the
difficulty sits:

| | regular `MT(ℤ)` | wild `M^exp` (Fresán–Jossen) |
|---|---|---|
| group | cosmic Galois `𝒰⋊𝔾_m` | exp-motivic `G^exp`, wild part `K` |
| Lie generators | `σ_{2n+1}`, dual to `ζ(2n+1)` | `γ_n` (Stieltjes), one/order |
| freeness | **PROVEN** (Brown spanning) | **CONJECTURE** (= DSS) |
| why decided | mixed Tate ⟹ motivic **t-structure**, geometric origin (`π_1(ℙ¹∖{0,1,∞})`); period map understood | **no proven `GPC^exp`**, no motivic t-structure for `M^exp` yet |

So DSS is open **exactly at** the missing Grothendieck period conjecture for exponential motives — the same
gap Wheeler flags in `bigraded-corank-dss-cross` §D ("conditional on the period conjecture for `M^exp`"). The
mirror localizes the entire FIELDS-MEDAL difficulty to one named hypothesis, `GPC^exp`, by analogy to a case
where the analogue of `GPC` is a theorem.

## §2 The freeness ASYMMETRY `[CONJECTURE — the new content]`

The mirror is **not** a perfect copy, and the discrepancy is the discovery. On the regular side the generators
are **sparse** (odd degrees only); the even degrees collapse because of the single rank-1 Tate twist `ℚ(1)`.
Ask the mirror question: **is there an "irregular Tate twist" that collapses some orders `n`, making `γ_n`
reducible (a non-generator)?**

- **Structural reason there is none — `E^{−x}` breaks Borel even-vanishing.** The regular even-twist vanishing
  (§1, Borel: `Ext¹_{MT(ℤ)}(ℚ,ℚ(2k))=0`) holds because `ℚ(2k)` is **pure Tate** — `ζ(2k)` is a period of
  `ℚ(k)` itself, no new extension, and Beilinson–Soulé/Borel kills the even regulator. The exponential twist
  `E^{−x}` (the rank-1 irregular connection `(𝒪, d+dx)` on `𝔸¹`, irregular singularity at `∞`) is **not pure
  Tate**: it carries the Stokes/rapid-decay structure. So the Borel even-vanishing argument **does not apply** to
  `Ext¹_{M^exp}(ℚ, E^{−x}⊗ℚ(n))` — the regulator survives even at even `n`, and it is `γ_n`. The exponential
  twist **resurrects** a generator exactly on Borel's vanishing locus. (No rank-1 collapsing period as on the
  regular side — `ℚ[2πi]` absorbs the even Tate twists; nothing absorbs the irregular `γ_n`.)
- **Positive evidence (no-collapse at order 2).** The simplest possible wild collapse would be
  `γ_{2} ∈ ℚ[γ_0]` (the analogue of `ζ(2) ∈ ℚ[2πi]`, with `γ_0=γ_E` the unique degree-1 exponential period).
  The rung-2 PSLQ test (`hypertranscendence-axis-synthesis` §3; archive
  `../2-fully-proven/computations/2026-06-19-corank2-rung2-degree2-independence.txt`) found **no** degree-2
  relation among `{γ_0², γ_1, …}` at height ≤2000, dps≤400 — so `γ_2`/`γ_1` are **not** powers of `γ_0`. The
  first candidate even-collapse is positively **ruled out** numerically. (Scope: verified only through degree 2.)

> **Conjecture (wild–cosmic freeness asymmetry).** `Lie(K)` is **maximally free**: free on one generator `γ_n`
> at **every** Tate twist `n` (`dim Ext¹_{M^exp}(ℚ,E^{−x}⊗ℚ(n)) = 1 ∀n`, hence `dim gr^n H_1(Lie K)=1 ∀n`) and
> `H_2(Lie K)=0`. Unlike the cosmic group — whose generators sit only at the odd twists `n≥3` (Borel) — **no**
> twist collapses; in particular the even twists, Borel-zero in `MT(ℤ)`, all carry a wild generator. DSS-cross
> is the statement that this maximal freeness holds.

## §3 "Wider than RH", made quantitative `[CONJECTURE — the payoff]`

Grade **both** generator spaces `H_1` by the **same** variable — the **Tate twist `n`** of the Ext (§1):
> **cosmic / motivic:** `P_𝒰(t) = ∑_{n odd ≥3} t^{n} = t³/(1−t²)` — `Ext¹_{MT(ℤ)}(ℚ,ℚ(n))≠0 ⟺ n` odd ≥3 (Borel).
> **wild / conjectured:** `P_K(t) = ∑_{n} t^{n}` over an **unbroken** progression — `Ext¹_{M^exp}(ℚ,E^{−x}⊗ℚ(n))≠0`
> for **all** `n` (every twist).

**The robust, normalization-independent headline:** the **even** Tate twists are *exactly* Borel's vanishing
locus for plain Tate motives — and the exponential twist `E^{−x}` puts a generator on **every one of them**.
> **The wild kernel lives where the motivic world is empty.** Its generators occupy the even twists (and the
> low twists `n=1,2`) — precisely the Ext groups Borel forces to zero in `MT(ℤ)`.

So `P_K − P_𝒰` contains **all even twists** `t² + t⁴ + t⁶ + …` (normalization-robust) plus the low odd/zero
twists (the bottom index — whether `γ_0` sits at `n=0` or `n=1` — is normalization-dependent and not claimed
precisely). This is a precise, falsifiable form of the project thesis **"hypertranscendence is wider than RH"**
(`hypertranscendence-axis-synthesis`, user steer 2026-06-19): the wild kernel is **strictly fatter per twist**
than the motivic/cosmic group, and the surplus is concentrated exactly on Borel's even-vanishing locus — the
genuinely irregular content the ordinary motivic Galois torsor cannot see (value-level hypertranscendence).

**Falsifiable target for the parent (irregular Hodge).** Compute `dim gr^n H_1(Lie K) = dim Ext¹_{M^exp}(ℚ,
E^{-x}⊗ℚ(n))` per order via the irregular Hodge filtration (the generator count, RH-blind, parent-computable).
The conjecture predicts the series `1/(1−t)` (every order = 1). If irregular Hodge ever yields `dim gr^n = 0`
for some `n`, that `γ_n` collapses and the asymmetry conjecture fails at `n` — a clean refutation channel. Note
this is the **`H_1` half** (generator count); the **`H_2=0`** half (no relations among the generators) is the
Schanuel/`GPC^exp`-hard apex (= DSS, FIELDS MEDAL) — the mirror does not make that half easier, only locates it.

## §4 Door / grade
- §1 (the mirror map + the proven↔open diagnosis via `GPC^exp`): **BRIDGE** — a correct structural mapping onto
  an accepted in-corpus import (Brown/Deligne–Goncharov). The regular-side theorem is *recalled*, not
  re-derived (flagged; no web per charter).
- §2 (freeness asymmetry) + §3 (Hilbert-series gap): **CONJECTURE** — the new transcendence-axis content;
  structural reason + order-2 positive evidence; falsifiable via irregular Hodge.
- Apex (DSS = `K` free = `H_2(Lie K)=0`): **FIELDS MEDAL**, unchanged.

## §5 Gates
- [x] 0 → 1  in-progress: well-posed (mirror stated; asymmetry conjecture + Hilbert series + structural reason;
  falsifiable target named); source-pure (in-corpus import + own rung-2); attack idea = irregular-Hodge
  generator count. *(Card created already past this gate; left in 0-backlog as a conjecture.)*
- [ ] 1 → 2  fully-proven: would require either (a) proving `dim gr^n H_1(Lie K)=1 ∀n` via irregular Hodge
  (the `H_1`/asymmetry half — parent-computable, RH-blind), which would bank §2/§3 as a theorem; or (b) the
  full apex (`H_2=0`, FIELDS MEDAL). The §1 mirror is already a banked BRIDGE observation.

## Cross-references
- `omega-splits-wild-kernel-freeness.md` — the `H_1`/`H_2` grading; this card supplies the *reason* `dim gr^n=1`
  for **every** `n` (the cosmic mirror + no-irregular-Tate-twist), which that card asserts but does not justify.
- `../2-fully-proven/bigraded-corank-dss-cross.md` — Wheeler's `𝒢`-associated-graded; the `GPC^exp` gate is the
  same one the mirror localizes.
- `hypertranscendence-axis-synthesis.md` — the frame; §3 here makes "wider than RH" a Hilbert-series statement.
- `regularization-freshness.md` (#75), `../2-fully-proven/exponential-period-dss-cross.md` §7 — the `γ_n`.

## Log
- 2026-06-19 (DeWitt) — created in 0-backlog. **Induction-by-analogy** (Anti-Cage): used the *proven*
  Brown–Deligne–Goncharov freeness of the cosmic-Galois Lie algebra as a template for DSS, localizing the open
  apex to `GPC^exp` (§1, BRIDGE). The mirror's discrepancy is the discovery: a **freeness asymmetry** (§2) —
  the wild kernel has a generator in every order (no even-collapse, no rank-1 irregular Tate twist), giving the
  Hilbert-series gap `1/(1−t)` vs `t³/(1−t²)` (§3) — a quantitative form of "hypertranscendence wider than RH".
  Order-2 even-collapse (`γ_2∈ℚ[γ_0]`) positively ruled out by the rung-2 PSLQ. Falsifiable via irregular-Hodge
  generator count. Transcendence axis, RH-blind. Regular-side theorem recalled (flagged), no web. Claimed in
  chat (id=326) before writing; cites but does not edit Wheeler's/Professor's cards.
- 2026-06-19 (DeWitt) — **Borel-grounded sharpening** (working the `H_1` generator-count, the RH-blind half).
  Grounded the regular generator count in `Ext¹_{MT(ℤ)}(ℚ,ℚ(n))≅K_{2n-1}(ℤ)⊗ℚ` (Beilinson–Soulé + Borel:
  rank 1 iff `n` odd ≥3) — fixing the earlier apples-to-oranges grading (now **both** sides graded by the same
  Tate twist `n`). Sharper headline: the **even** twists are *exactly* Borel's vanishing locus, and the
  exponential twist `E^{−x}` (non-Tate, Stokes) **resurrects** a regulator `γ_n` on every one of them — "the
  wild kernel lives where the motivic world is empty." §1/§2/§3 + Statement revised. Borel recalled (flagged),
  no web.
