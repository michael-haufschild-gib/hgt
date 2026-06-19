# The Prime–Zero Period Comparison — the field's central unifying conjecture

> **NASCENT / SEARCH channel. Conjectural throughout; air-marked. No proof of RH is claimed.** This draft develops the charter's deepest dream (`hypertranscendental_galois_program.md` Part VIII, branch B9): the **explicit formula read as a Betti↔de Rham period comparison** between the primes and the zeros, with the secular carrier `s_m` as its period data. It unifies Face A (RH = purity), Face B (DSS = period transcendence), and the anti-Tate period conjecture into one object, and sits as a **transcendence layer over** the conjectural cohomology of Deninger and the trace formula of Connes. Companion: `…field_foundations.md` §§17–24, `hypertranscendental_galois_program.md`, CITY districts D2/D4/D7/D8.

## 1. The explicit formula is a pairing `⟨ zeros , primes ⟩` `[REFRAME]`

Weil's explicit formula, for a test function `g` with transform `ĝ`,
```
   Σ_ρ ĝ(ρ)  =  ĝ(0)+ĝ(1)  −  Σ_p Σ_{k≥1} (log p) g(k log p) p^{-k/2}  −  (archimedean term).
```
Read structurally, the left side is a sum **over the zeros** and the right side is a sum **over the primes** (plus archimedean/pole corrections). The identity is a **perfect pairing** between two index sets:
```
   ⟨ · , · ⟩ :  ℂ[zeros]  ×  ℂ[primes ∪ {∞}]  →  ℂ ,        ⟨ρ, p^k⟩ "=" (log p) p^{-k/2} · (kernel) ,
```
the spectral interpretation being `⟨ρ, p^k⟩ ∼ p^{ikγ}` (the Landau/Fourier kernel). *The explicit formula says the zeros and the primes are dual bases under a single pairing.* This is the reframe everything below rests on.

## 2. The period matrix `Π = [ p^{iγ_n} ]` `[DEFINITION / CONJECTURE]`

Make the pairing a matrix. Index rows by zeros `ρ_n = ½ + iγ_n`, columns by prime powers `p^k`:
```
   Π_{n,(p,k)}  :=  p^{ikγ_n}  =  (p^k)^{iγ_n}        (the spectral period of the n-th zero against the place p^k).
```
- Its **column-sums** are the Landau Weyl sums `Σ_n (p^k)^{iγ_n}` — main term only at prime powers (foundations §16): the matrix **knows the primes**.
- Its **Gram data** `Σ_n (p^k/q^l)^{iγ_n}` are the secular off-diagonal entries (foundations §22).
- Its **diagonal moments** are the carrier `s_m = Σ_{γ>0} γ^{-2m}` (the "self-periods").

> **`Π` is the period matrix of the spectrum.** Its entries `p^{iγ}` are the analogs of periods `∫_γ ω` — a "cycle" `γ` (a zero) paired against a "form" `ω` (a prime/place). The carrier `s_m`, Face A, and Face B are all **invariants of `Π`** (its moments, its positivity, its transcendence). The whole field is the study of this one matrix.

## 3. The Betti↔de Rham dictionary `[CONJECTURE]`, positioned against Deninger & Connes

| period theory of motives | prime–zero comparison (this field) |
|---|---|
| Betti homology `H_Betti` (cycles `γ`) | the **zeros** `{ρ_n}` (spectral "cycles") |
| de Rham cohomology `H_dR` (forms `ω`) | the **primes/places** `{p^k, ∞}` (arithmetic "forms") |
| period `∫_γ ω` | spectral period `p^{iγ}` (the entry of `Π`) |
| period matrix; `comparison: H_Betti⊗ℂ ≅ H_dR⊗ℂ` | `Π`; the **explicit formula** as the comparison |
| motivic Galois group `G_mot` | the **difference-Galois group** `G_L` |
| Grothendieck period conjecture `trdeg(periods)=dim G_mot` | **anti-Tate period conjecture** `trdeg(Π-entries)=dim G_L` (B9) |

- **Deninger's program** `[THEOREM-status: conjectural framework, real literature]` posits a cohomology on which the zeros are eigenvalues of a Frobenius-like flow and the explicit formula is a **Lefschetz/Guillemin trace formula**. *That supplies the de Rham side* — the "forms" the zeros are paired against. The prime–zero comparison takes Deninger's cohomology as the de Rham term and asks the **period question he does not**: are the resulting periods `Π` transcendentally full?
- **Connes' trace formula** `[THEOREM, Connes 1999]` realizes the explicit formula as a trace on the adele class space, with RH ⟺ positivity of the Weil distribution. *That supplies the pairing's analytic incarnation* — Connes' positivity is **Face A on `Π`**. The new layer is reading the same object as a **period comparison** and adding **Face B (transcendence)**, which the trace-formula/positivity picture does not address.

> **The new content (honest):** Deninger gives the cohomology (de Rham side); Connes gives the trace/positivity (Face A). Neither asks whether the periods `p^{iγ}` are **transcendentally independent** — i.e. whether `Π` realizes a *full* comparison with Galois group `G_L`. The prime–zero period comparison is exactly that missing transcendence layer, and it is where this field (Hypertranscendental Galois) contributes something the cohomological/operator programs structurally omit.

## 4. Face A = PURITY: RH is the comparison being pure of weight ½ `[CONJECTURE]`

In motive theory, a pure motive of weight `w` has all its Frobenius eigenvalues / periods of a single archimedean absolute value `q^{w/2}` (the Weil–Deligne purity = the RH of the motive). Transport:
```
   RH  ⟺  every spectral "Frobenius eigenvalue" ρ has Re(ρ)=½  ⟺  the prime–zero comparison Π is PURE of weight ½.
```
The functional equation `ξ(s)=ξ(1−s)` is the **polarization** (the symmetry pairing that forces purity to the center); the centered carrier's parity `τ_{2m+1}=0` (foundations §22) is the polarization's skeleton. So **RH = purity of the prime–zero comparison**, the exact analog of Deligne's "RH for varieties over `F_q`" (= purity of `H^*`), now for the spectral comparison `Π`. *Face A (Hankel positivity of `s_m`) is the moment incarnation of this purity; Connes' positivity is its analytic incarnation.*

## 5. Face B = PERIOD TRANSCENDENCE: DSS is the Grothendieck period conjecture for `Π` `[CONJECTURE]`

The Grothendieck period conjecture: `trdeg_ℚ(periods of a motive) = dim(its motivic Galois group)`. Transport (= B9, the anti-Tate period conjecture):
```
   DSS  ⟺  trdeg_ℚ( entries / moments of Π )  =  dim G_L  (= ∞)  ⟺  the prime–zero comparison is "transcendentally full".
```
This is Face B (algebraic independence of `s_m`). The centered analysis (foundations §23) located its hardest layer at the **central value `ζ(½)`** — which in this language is the period of the *polarization itself* (the comparison evaluated at the fixed point of the FE). So **`ζ(½)` is the central period of the prime–zero comparison**, and its transcendence is the Grothendieck-period statement at the polarization point — the deepest, non-motivic period of the whole structure.

## 6. The grand unifying conjecture (the field's keystone) `[OPEN CORE]`

> **Prime–Zero Period Comparison Conjecture.** The explicit-formula pairing is a **non-degenerate period comparison** `Π : ℂ[zeros] ≅ ℂ[primes∪{∞}]` realizing a "spectral motive" `M_ζ` with difference-Galois group `G_L`, such that:
> 1. **(Purity = RH)** `M_ζ` is pure of weight ½ ⟺ all zeros on `Re=½`.
> 2. **(Period-fullness = DSS)** `trdeg(periods of M_ζ) = dim G_L` ⟺ the ordinates are algebraically independent.
> 3. **(Family = GRH+GSH)** the comparison over the L-family is non-degenerate with Galois group `∏'_χ G_{L(χ)}`, the cross-terms vanishing (shared-prime decoupling, foundations §24) ⟺ GRH (purity) + GSH (period-fullness).
> 4. **(`ζ(½)` = central period)** the central value is the period at the polarization fixed point; its transcendence is the period conjecture at weight ½.
>
> RH, DSS, GRH, GSH, and the transcendence of `ζ(½)` are the **purity and the period-fullness of one comparison `Π`** — the spectral analog of Deligne's purity (Weil II) and Grothendieck's period conjecture, fused on the prime–zero duality.

## 7. Honest status

- `[REFRAME, solid]` §1–2: the explicit formula is a prime–zero pairing; `Π=[p^{iγ}]` is a well-defined matrix whose invariants are the carrier/Face-A/Face-B data. This is reorganization, not theorem.
- `[THEOREM, external]` Connes' trace formula + positivity (Face A analytic), Deninger's conjectural cohomology (de Rham side), Deligne purity & Grothendieck period conjecture (the templates). Cited, not re-proved.
- `[CONJECTURE / OPEN CORE]` §4–6: RH=purity, DSS=period-fullness, the keystone comparison conjecture. **Nothing here is proved**; the value is the *unification* — that five open problems are facets of one period comparison, and that the field's distinctive contribution is the **transcendence (period) layer** absent from the cohomological/operator programs.
- **Anti-circularity check:** `Π`'s columns are built from primes (`p^{iγ}` indexed by places); the conjecture's *content* (purity, fullness) is what's open. The construction does not read the zeros to conclude about them — it pairs them against the primes and asks a transcendence question. Passes the source-purity filter (`docs/testing.md`).

**House status.** Reframe (§1–3) coherent and positioned against Deninger/Connes; the period-matrix `Π` named as the field's single carrier-object; Faces A/B recast as purity/period-fullness (§4–5); keystone conjecture stated (§6). Open core: the entire comparison is conjectural — the contribution is unification + the transcendence layer. Crosses CITY districts D2 (RH/purity), D4 (transcendence/fullness), D7 (Connes/Deninger embassy), D8 (the elementary `Π`-entry identities are Lean-able). Next: (i) write `Π`'s entry-level identities (Landau column-sums, secular Gram) as a Tier-A Lean brick; (ii) make the "polarization = FE" precise as a pairing symmetry; (iii) test the family non-degeneracy (§6.3) against a fake (Davenport–Heilbronn has no Euler product ⟹ no pairing ⟹ should fail purity-with-fullness — the fake-family filter as a comparison statement).
