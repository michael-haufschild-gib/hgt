# The cosmic-Galois freeness mirror — DSS as the irregular image of Brown–Deligne–Goncharov, and the freeness asymmetry

- **ID:** cosmic-galois-freeness-mirror
- **Stage:** 0-backlog (CONJECTURE card; §1 mirror = BRIDGE-import, §2/§3 = the new conjecture)
- **Type:** CONJECTURE (the freeness asymmetry) + BRIDGE (the mirror map & the proven↔open diagnosis)
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
mirror localizes the entire open gap to one named hypothesis, `GPC^exp`, by analogy to a case
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
Schanuel/`GPC^exp`-open apex (= DSS, open) — the mirror does not make that half easier, only locates it.

## §4 Door / grade
- §1 (the mirror map + the proven↔open diagnosis via `GPC^exp`): **BRIDGE** — a correct structural mapping onto
  an accepted in-corpus import (Brown/Deligne–Goncharov). The regular-side theorem is *recalled*, not
  re-derived (flagged; no web per charter).
- §2 (freeness asymmetry) + §3 (Hilbert-series gap): **CONJECTURE** — the new transcendence-axis content;
  structural reason + order-2 positive evidence; falsifiable via irregular Hodge.
- Apex (DSS = `K` free = `H_2(Lie K)=0`): **open**, unchanged.

## §5 Gates
- [x] 0 → 1  in-progress: well-posed (mirror stated; asymmetry conjecture + Hilbert series + structural reason;
  falsifiable target named); source-pure (in-corpus import + own rung-2); attack idea = irregular-Hodge
  generator count. *(Card created already past this gate; left in 0-backlog as a conjecture.)*
- [ ] 1 → 2  fully-proven: would require either (a) proving `dim gr^n H_1(Lie K)=1 ∀n` via irregular Hodge
  (the `H_1`/asymmetry half — parent-computable, RH-blind), which would bank §2/§3 as a theorem; or (b) the
  full apex (`H_2=0`, open). The §1 mirror is already a banked BRIDGE observation.

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
- 2026-06-20 (novelty-loop R03) — **Mechanism for the freeness asymmetry: F∞-parity breaking by the
  unipotent Stokes structure** (full piece in `logs/2026-06-20-novelty-generation-loop.md`). The even/odd
  Tate-twist grading is the **F∞ (complex-conjugation) eigenvalue (−1)ⁿ**; Borel regulators live in the
  F∞-odd part (verified: ζ(2k)/π^{2k}∈ℚ collapse, ζ(odd) don't). The wild surplus on the **even** twists
  exists because E^{−x}'s **Stokes matrices are unipotent** — not an F∞-eigenvector, so they mix parities
  and resurrect γ_{2k} where motives are F∞-even-empty. Quantitative: wild generator density = **2×** cosmic
  (factor 2 = index of the even sublattice); "wider than RH" = "the wild kernel restores the F∞-even half
  motives discard". Comb identity: P_𝒰 = oddpart(P_K) − t, surplus = evenpart(P_K) = 1/(1−t²). H₁-half
  reduction (method 21): dim gr^n=1 ∀n ⟸ Stokes matrix of E^{−x}⊗ℚ(n) ≠ identity ∀n (RH-blind, irregular-
  Hodge-computable, far below the H₂=0 apex). Cross-links R01: Stokes-unipotent = log monodromy = R01's
  marginal-stratum K-generator (same archimedean unipotent). ~60–70% prior-true; F∞/Borel/Stokes-unipotent
  facts proven, mechanism conjectural.

## R-DeWitt-2026-06-20 (Phase-0 baseline tick) — correcting the R03 reduction; the H₁-half handle is irregular Hodge, not "Stokes ≠ identity"

Interrogated the R03 forward-lead ("`dim gr^n=1 ∀n ⟸ Stokes matrix of `E^{−x}⊗ℚ(n) ≠ identity ∀n`"). It has two
errors; fixing them re-grades the H₁ half and hands the parent a *correct* computable invariant.

**Error 1 — wrong object (rank-1).** `E^{−x}⊗ℚ(n)` is **rank 1**: a single exponential factor `e^{−x}` (the Tate
twist `ℚ(n)` is rank 1, regular-singular, and only shifts weight). A rank-1 irregular connection has **no Stokes
phenomenon** — Stokes matrices encode the mixing of solutions with *distinct* exponential growth rates `e^{q_i}`,
and with one exponent there is nothing to mix, so its Stokes matrix is the **identity for every `n`**. As written
the reduction's hypothesis is vacuously false, i.e. it does not bear on `dim gr^n`. `[PROVED — elementary Stokes
theory; recalled-standard, flagged, no web]`

**The right object — the rank-`(n+1)` extension.** The generator `γ_n` is the order-`n` **off-diagonal Stokes
multiplier** of the connection
> `V_n := E^{−x} ⊗ Log^{(n)}` on `𝔾_m`,  `Log^{(n)}` = the unipotent log-tower (flat sections `1,\log x,…,(\log
> x)^n/n!`), `E^{−x} = (𝒪,d+dx)`,
which is exactly the `∂_s`-derivative tower of the Γ-integral at `s=1` (`x^{s-1}=Σ(s-1)^k(\log x)^k/k!`, so
`∂_s^k|_{s=1}` extracts the `(\log x)^k`-moment `J_k`; this is `exponential-period-dss-cross` §2′/§7(U), Professor's
floor). `V_n` has **two** formal exponents (`e^0` from the unit/log part, `e^{−x}` from the irregular part), so its
Stokes matrix at `∞` is a genuine non-trivial unipotent `(n+1)×(n+1)` matrix whose super-diagonal entries are the
regularized moments `J_k` — the wild generators. **So the apex reformulates cleanly:** `H_2(Lie K)=0` (= DSS-cross)
⟺ the **Stokes multipliers of the Gamma connection `V_∞` are algebraically independent**. `[BRIDGE — faithful
reformulation; wires the native apex to isomonodromy/Stokes-data parent technique]`

**Error 2 — de Rham ≠ Tannakian (the decisive one).** Even on `V_n`, Stokes-non-triviality is a statement about the
**de Rham / differential-module** structure (the connection is not a direct sum of its formal pieces) — and that is
**unconditional and total**: `V_n` is non-split as a connection for every `n`, even/odd alike (the log-tower is
de-Rham-non-split at every rung, and tensoring by the invertible `E^{−x}` preserves it). But `dim gr^n H_1(Lie K)`
is a **Tannakian/motivic** Ext in `M^exp`, which can be *strictly smaller* than the de Rham Ext: motivic relations
split things the connection does not (this is exactly how Borel gets `Ext¹_{MT(ℤ)}(ℚ,ℚ(2k))=0` while the de Rham
Tate extension is non-trivial). **The gap de Rham→Tannakian is precisely GPC^exp.** Therefore "Stokes ≠ identity"
does **not** discharge the H₁ half below the apex; it only re-proves the (easy, unconditional) de Rham
non-splitness. The even-twist surplus — the heart of "wider than RH" §3 — is **GPC^exp-hard**, not parent-easy.
This **demotes** the R03 claim that the H₁ half is "far below the `H_2=0` apex": *only the odd twits `n≥3` are
pinned below the apex* (there Borel/motivic input already gives the cosmic generators); the even surplus shares the
apex's conditionality. `[PROVED structural diagnosis; corrects this card's §3 "falsifiable target" and R03]`

**The constructive replacement (the correct RH-blind handle).** What *is* parent-computable and finer than bare de
Rham is the **irregular Hodge filtration** `F^•_{irr}` (Sabbah; Esnault–Sabbah–Yu; Fresán–Jossen) of `V_n`. The
generator-count target should be stated as an **irregular Hodge number**:
> **[CONJECTURE, sharpened] `dim gr^n H_1(Lie K) = 1 ∀n` ⟸ the irregular Hodge number `gr^p_{F_irr} V_n` is the
> single jump `1` at the order-`n` step, for all `n` (including even `n`), where on the motivic locus the same
> filtration reproduces Borel (jumps only at odd `n≥3`).**
The even-twist surplus is then `[the even jumps of F_irr(E^{−x}⊗Log) that F_irr(ℚ(•)) lacks]` — a number an
irregular-Hodge computation returns, RH-blind, and the decisive refutation channel (a vanishing even jump kills the
asymmetry at that `n`). This replaces R03's flawed "Stokes ≠ identity" with a correct, computable invariant and is
the right hand-off to the parent (irregular Hodge), distinct from the analytic Nesterenko `H_C` lane.

**Net (honest grade).** No new theorem this tick. Output = (i) a corrected, faithful **Stokes reformulation** of
the DSS apex (`H_2=0` ⟺ Stokes multipliers of the Γ-connection alg-indep) — BRIDGE; (ii) a **re-grading** that the
H₁-half even surplus is GPC^exp-hard, not parent-easy (corrects §3/R03); (iii) the **irregular Hodge number** as
the correct replacement handle. Discarded en route (attack-as-false): an FE/F∞-parity constraint on `H_2` (conflates
the FE involution `s↔1−s` with complex conjugation `F∞`), and an FE-remainder-parity idea (reduces to Euler
`ζ(2k)∈ℚπ^{2k}`). Recalled-standard facts (Stokes needs ≥2 exponents; irregular Hodge filtration exists for `M^exp`)
flagged, no web per charter — to be source-pinned before any promotion past BRIDGE.

### R-DeWitt-2026-06-20 addendum — PSLQ data: even-twist Stieltjes constants are FRESH vs cosmic+tame (extends the order-2 check)

Ran the decisive test for the §2/§3 even-twist surplus (runpod, bounded; archive
`computations/2026-06-20-freeness-even-surplus-pslq.txt`). The prior evidence in this card tested only
`γ_2 ∉ ℚ[γ_0]` (one variable, degree 2). Extended to the cosmic+tame alphabet and to `γ_4`:

| test | target | alphabet (deg ≤2, height ≤10⁶, dps 300) | result |
|---|---|---|---|
| A | — | linear over `{γ_0..γ_4, log2π, π², ζ(3), ζ(5), 1}` | **no relation** |
| D | `γ_2` | cosmic+tame `{log2π, π², ζ(3), ζ(5)}` only | **FRESH** (no deg-2 relation) |
| D′ | `γ_4` | cosmic+tame `{log2π, π², ζ(3), ζ(5)}` only | **FRESH** |
| B | `γ_2` | `{γ_0, γ_1, log2π, π², ζ(3)}` | **FRESH** (irreducible at deg 2) |
| C | `γ_4` | `{γ_0,γ_1,γ_2,γ_3, log2π, π², ζ(3)}` | **FRESH** (irreducible at deg 2) |

**Reading (the sharpest is D/D′).** The even-order `γ_2, γ_4` are not degree-2 expressions in the
*cosmic generators + tame periods* — i.e. they are not "secretly cosmic." This is exactly what the §2
freeness asymmetry predicts: the wild kernel carries genuine new generators on the **even** twists, where
the motivic/cosmic world (Borel `Ext¹_{MT(ℤ)}(ℚ,ℚ(2k))=0`) is empty. The first candidate even-collapse is
ruled out more broadly than before (not just vs `γ_0`, but vs the whole cosmic+tame alphabet).

**Honest grade.** This is **bounded numerical evidence**, not a proof: degree ≤2, height ≤10⁶, dps 300; a
PSLQ "no relation" is absence of a *low-complexity* relation, never algebraic independence (the GPC^exp
apex). It is decisive in the refutation direction only (a relation would have killed the asymmetry at that
order — none appeared). A degree-3 strengthening (dps 400, height ≤10⁸) is running. The result **supports**
the conjecture and tightens its first falsification window; it does not promote anything past CONJECTURE.

### R-DeWitt-2026-06-20 (3) — the wild surplus is the ζ-WEIGHTING, not the bare Γ; correcting my Stokes wording

Degree-3 PSLQ (dps 400, height ≤10⁸) confirms the even surplus more strongly: `γ_2` AND `γ_4` are FRESH
vs the cosmic+tame alphabet `{log2π, π², ζ(3), ζ(5)}` at degree ≤3 (no relation). Archive
`computations/2026-06-20-freeness-even-surplus-pslq.txt`.

**The clarifying contrast (verified).** The *plain archimedean* Γ-derivative tower lands entirely in the
cosmic+tame ring — checked by PSLQ:
> `Γ''(1) = γ² + π²/6`,  `Γ'''(1) = −γ³ − γπ²/2 − 2ζ(3)`,  and in general `{Γ^{(k)}(1)} ⊂ ℚ[γ, π, ζ(odd)]`
> (standard: `\log Γ(1+s) = −γs + Σ_{k≥2} ζ(k)s^k/k`).
So **Source A alone (the bare Γ) produces only cosmic/tame periods** — no wild surplus. The *Stieltjes*
tower `{γ_n}` (PSLQ-fresh vs that ring) comes instead from the **ζ-weighted** exponential kernel
`1/(e^t−1) = Σ_{k≥1} e^{−kt}` — the **infinite tower of exponential rates** `e^{−kt}`, the analytic shadow
of "all the prime-like rates at once" (Source B). 

> **[CONJECTURE, sharpened — Door-4 localization]** The wild surplus on the even twists is produced by the
> **coupling of the archimedean exponential `e^{−x}` to the infinite rate-tower `Σ_k e^{−kt}`** (= the
> ζ-weight), i.e. by the **native weld Source A × Source B**, not by either source alone. The bare-Γ tower
> (Source A alone) is the cosmic/tame shadow `ℚ[γ,π,ζ(odd)]`; the ζ-weighting de-trivializes the even
> twists and yields the fresh `γ_n`. This makes the §3 "wild kernel lives where the motivic world is empty"
> a statement about the **weld**, consistent with the field's native-zone thesis (Door-4) — and gives a
> concrete analytic witness: removing the rate-tower (using `Γ` not `Γζ`) collapses the surplus to cosmic.

**Self-correction.** My R-DeWitt-2026-06-20(1) reformulation said "Stokes multipliers of the **Gamma**
connection." That is the *bare-Γ* connection `E^{−x}⊗Log^{(n)}`, whose periods are the cosmic/tame
`Γ^{(k)}(1)` — NOT the wild `γ_n`. The correct carrier of the wild generators is the **ζ-weighted**
exponential connection (kernel `Σ_k e^{−kt}`, the irregular family of `Γ(s)ζ(s)`); its Stokes/irregular-Hodge
data are the `γ_n`. So the apex reformulation is: **DSS-cross ⟺ the Stokes multipliers of the ζ-weighted
exponential connection are algebraically independent over `ℚ({log p})`** — and the bare-Γ Stokes data are the
(reducible) cosmic/tame shadow. The irregular-Hodge handle (R-DeWitt(2)) likewise applies to the ζ-weighted
connection, not the bare Γ.

### R-DeWitt-2026-06-20 (4) — analytic mechanism of the weld-localization: the wild content is born at the s=1 edge, only in the infinite rate-tower

Sharpening the weld-localization with the exact analytic mechanism (the **weaken** move: the finite-rate
version is decidable and reduces the question).

> **Mechanism.** The bare-Γ kernel `e^{−t}` is **regular at `t=0`** ⟹ its Mellin `Γ(s)` is regular at `s=1`
> ⟹ no Stieltjes pole, periods are the cosmic/tame `Γ^{(k)}(1)`. The ζ-weighted kernel
> `1/(e^t−1) = Σ_{k≥1} e^{−kt}` has a **simple pole at `t=0`** (`~1/t`), which exists **only because
> infinitely many rates are summed** — every finite truncation `Σ_{k=1}^N e^{−kt}` is regular at `t=0`. That
> `t=0` pole is exactly the `s=1` pole of `ζ`, and the **Stieltjes `γ_n` are its Laurent coefficients**. So the
> wild content is supported entirely at the **`s=1` edge**, and is created by the **infinite** rate-tower.

**Decidable half (proven, but reduces to known).** The finite truncation `Σ_{k=1}^N e^{−kt}` has Mellin
`Γ(s)·Σ_{k=1}^N k^{−s}` = (regular at `s=1`) ⟹ its "Stieltjes constants" are combinations of `{Γ^{(k)}(1),
(\log k)^j}` = **cosmic/tame**. This is the analytic face of `#212` (finite Euler-truncated Stieltjes field =
`trdeg ℚ(\log p)`, tame). **No wild surplus at finite `N`.** `[PROVED; reduces to #212 + classical pole]`

**The novel increment (honest).** Not the classical pole fact — the **localization**: it pins the §2/§3 even
surplus to (i) the `s=1` edge and (ii) the `N→∞` pole-formation, i.e. the infinite rate-tower (Source B) is
*necessary* for any wild content, the single archimedean rate (Source A) giving only cosmic/tame. This is the
analytic witness of the Door-4 weld claim (R-DeWitt(3)) and ties the value-axis surplus to the field's own
`s=1`-edge / no-margin locus. It does **not** prove transcendence (the `γ_n ∉ 𝓡` apex stays walled — it
reduces to open irrationality of the Stieltjes constants). Grade: STRUCTURAL mechanism (BRIDGE-ish), the
finite half PROVED (= #212), the localization framing the new part.

### R-DeWitt-2026-06-20 (5) — GUARDRAIL (Popper-forced collision tacking×avalanche × freeness): the differential/Stokes axis reaches H₁, is blind to H₂

Popper forced the apex (freeness `H_2(Lie K)=0`) against SAILING-TACKING + AVALANCHE-FRACTURE on the
differential axis. Generated an exact identity, then killed it; the residue is a guardrail with a mechanism.

**Exact differential identity (generated).** AVALANCHE-FRACTURE = the **Stokes phenomenon**: the recessive
(exp-small) solution is silent below threshold (inside a Stokes sector) and switches on discontinuously across
a Stokes line (the cascade); the `γ_n` are the Stokes/cascade amplitudes. TACKING = that recessive direction
is unreachable by any continuous flow in a sector ("no-go zone"), reached only by the discrete tack of crossing
a Stokes line — "fixed by a constraint, not propagated by a flow," literally, ∂_s-differential (NOT the dead
geometric monodromy of `moonshot-2pi-monodromy-frobenius`).

**Killed (three ways).** (i) Verified (R-DeWitt(3)): the bare single-exponential `e^{−x}` Stokes/period data
are the Γ-derivatives `Γ^{(k)}(1)` = **cosmic/tame** — the single-place avalanche gives tame, not the wild
`γ_n` (which need the infinite ζ-rate-tower). (ii) Corpus: the archimedean Stokes/index/`ω` is the **tame
realization/F₁ face** (`2pi-monodromy` card), not freeness. (iii) Structural: the identity lands on **H₁** (the
generators appear at the `s=1` threshold); freeness is **H₂**. Functional freeness of the ∂_s-tower =
hypertranscendence = **Hölder** (proven, the O side); value-freeness at `s=1` = **Schanuel/F₁** (the V side,
apex). The avalanche threshold IS the O→V specialization wall.

> **GUARDRAIL.** The differential/Stokes/avalanche axis is the **O (Hölder/functional/H₁)** side. Every
> structural invariant the team has reached — Hilbert series (my tick-3 even-surplus), Stokes data (my tick-1),
> monodromy (dead 2πiℤ route), zero-count / growth-geometry (Wheeler's killed Schwarz) — computes **H₁ /
> generators** and is **structurally blind to H₂** (value-freeness = Schanuel = the F₁ specialization). This
> unifies why all these bridges die on one wall. **Prediction:** no differential/geometric/spectral collision
> crosses O→V; only an arithmetic specialization (the missing F₁ / a Schanuel input) does. (Refines, with a
> Stokes/avalanche mechanism + an attack-classification, the known O/V dichotomy of `keystone-is-value-relational`
> — does not merely restate it: it predicts which *attacks* are a priori H₁-blind.)

**Surviving localization (labelled, not proven).** The collision sharply LOCATES H₂: `σ_p` alone are
flat/abelian (commute) ⟹ abelian = maximal relations = the *opposite* of free. So freeness cannot come from
the prime base; it must come from the **∂_s × σ_p weld being maximally non-abelian (free)**. [CONJECTURE,
Door-4] value-freeness = the infinite-σ_p×∂_s weld is free — functionally accessible (Ax-Schanuel/Hölder),
value-specialization at `s=1` is the F₁ wall. A location to aim, not a proof. (Distinct from
`lambda-difference-differential-hypertranscendence`, which REDUCED to one prime; this is the infinite coupling.)
