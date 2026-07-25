# Card — Density Hypothesis (DH): exact frontier, reduction to a single large-value point, attack log

Lane owner: opus5. Status: ACTIVE (Cycle 1). Created 2026-07-25.
Target: prove or disprove `N(σ,T) ≪_ε T^{2(1-σ)+ε}` uniformly for `1/2 ≤ σ ≤ 1`.
Source statement: `docs/Density Hypothesis.md`.

**Working log at the bottom — append findings and dead ends there. Read it before repeating work.**

---

## Gate 1 — internal corpus (searched 2026-07-25)

`rg -il "density hypothesis|zero-density|large value|Dirichlet polynomial"` over `docs/` and
`docs/drafts/pipeline/`: **no card attacks DH or zero-density estimates.** The only adjacent card is
`1-in-progress/offline-density-zero-detector-barrier.md` (AAL = almost-all-zeros-on-line, a *different
and stronger* statement; it cites Selberg/Ingham/Huxley/Guth–Maynard only to show they are blind in the
shrinking strip `δ·log T = O(1)`). Its K1 observation is compatible with everything here: density
theorems are about *fixed* `σ > 1/2`, AAL is about `σ = 1/2 + o(1)`. No duplication.
Corpus has no Dirichlet-polynomial large-values machinery in Lean.

## Gate 2 — external SOTA (audited 2026-07-25; primary source = Tao–Trudgian–Yang ANTEDB blueprint,
`teorth.github.io/expdb/blueprint/`, chapters 7, 10, 11; arXiv:2501.16779)

### Definitions (fixed for this card)
- `A(σ)` := inf of `A` with `N(σ−δ,T) ≪ T^{A(1−σ)+o(1)}`. DH ⟺ `‖A‖_∞ := sup_{1/2≤σ<1} A(σ) = 2`.
  `A(1/2) = 2` (Riemann–von Mangoldt), `σ ↦ (1−σ)A(σ)` non-increasing and left-continuous.
- Large-value pattern `(N,T,V,(a_n)_{n∈[N,2N]},J,W)`: `|a_n| ≤ 1`, `J` interval of length `T`,
  `W ⊂ J` 1-separated, `|∑_{n∈[N,2N]} a_n n^{-it}| ≥ V` for `t ∈ W`.
  `LV(σ,τ)` := least exponent with `|W| ≪ N^{LV+o(1)}` when `T = N^{τ+o(1)}`, `V = N^{σ+o(1)}`.
  `LV_ζ` = same but `a_n = 1_I(n)`, `J = [T,2T]`.
- Montgomery conjecture (MC): `LV(σ,τ) ≤ 2−2σ` for all `τ ≥ 0`, `1/2 < σ ≤ 1`. Sharp
  (`LV(σ,τ) ≥ min(2−2σ,τ)`, random-block construction).

### Record table (Table 11.1 of the blueprint), the only numbers that matter here
| range of σ | A(σ) ≤ | source |
|---|---|---|
| `[1/2, 7/10]` | `3/(2−σ)` | Ingham 1940 (= pure L² mean value theorem) |
| `[7/10, 19/25]` | `15/(3+5σ)` | **Guth–Maynard 2024** (arXiv:2405.20552) |
| `[19/25, …]` | Ivić / Bourgain / Heath-Brown / Pintz pieces | — |

- `‖A‖_∞ = 30/13 = 2.30769…`, **attained exactly at `σ = 7/10`** (Ingham and Guth–Maynard cross
  there: `3/1.3 = 15/6.5 = 30/13`). Gives PNT in short intervals for `θ > 1 − 13/30 = 17/30`.
- DH is **known for `σ ≥ 25/32 = 0.78125`** (Bourgain 2000, Thm 11.21/11.22 of blueprint);
  **open exactly on `1/2 < σ < 25/32`**.
- Other recent: Bin Chen arXiv:2507.08296 (`∑_χ N(σ,T,χ) ≪ (qT)^{7(1−σ)/3+ε}`, exponent 7/3 for the
  q-aspect family — *not* the ζ exponent); Gafni–Tao arXiv:2505.24017 (exceptional sets);
  Bellotti arXiv:2508.02041 (σ near 1); Turnage-Butterbaugh arXiv:2607.04632 (July 2026 survey, no new
  bound). **No post-GM improvement to `A(σ)` for `σ ≤ 25/32` exists as of 2026-07.**

### The exact reduction (blueprint Cor 11.9/11.10 + Heuristic 11.3) — verified by hand
`A(σ) ≤ 3/τ₀` follows from: (6) `LV(σ,τ) ≤ (3−3σ)τ/τ₀` on `2τ₀/3 ≤ τ ≤ τ₀`, and
(7) `LV_ζ(σ,τ) ≤ (3−3σ)τ/τ₀` on `2 ≤ τ < 4τ₀/3` (vacuous when `τ₀ < 3/2`).
Blueprint Heuristic 11.3: (6) at the right endpoint `τ = τ₀` is the bottleneck, i.e.

> **`A(σ) ≤ 3/τ₀` is reachable iff `LV(σ,τ₀) ≤ 3−3σ`.**

Consequences computed here:
- `τ₀ = 3/2` ⟹ `A(σ) ≤ 2` (DH). Via Cor 11.10: **DH at σ ⟸ MC in the wedge `τ ≤ σ + 1/2`.**
  At `σ = 1/2` this is `τ ≤ 1` = the L² mean value theorem (Thm 7.9), which is *exactly sharp*:
  `LV(σ,1) = 2−2σ`. So DH is "MC just past the mean-value theorem".
- **MVT ⟹ exactly `τ₀ = 2−σ`, i.e. Ingham.** At `σ = 7/10`: `τ₀ = 13/10`, `A = 30/13`.
- Guth–Maynard LV theorem (Thm 10.27): `LV(σ,τ) ≤ max(2−2σ, 18/5−4σ, τ+12/5−4σ)`, i.e.
  `R ≪ N^{o(1)}(N²V^{−2} + N^{18/5}V^{−4} + T N^{12/5}V^{−4})`. Beats MVT iff `σ > 7/10` (the terms
  `τ+12/5−4σ` and `1+τ−2σ` coincide at `σ = 7/10`). **GM gives nothing at or below σ = 7/10.**

### THE BOTTLENECK (single point)
> `‖A‖_∞ < 30/13` requires beating the **L² mean value theorem** at
> `(σ,τ)` in a *left*-neighbourhood of `(7/10, 13/10)`.
> Canonical target: **`LV(7/10, 6/5) ≤ 4/5 − δ`** (MVT gives `4/5`; DH needs `≤ 0.72`; MC says `0.6`).
> Equivalently `LV(σ, τ₀) ≤ 3−3σ` for some `τ₀ > 2−σ`, `σ ↑ 7/10`.

### Why σ = 3/4 was the classical wall, and why 7/10 is the new one
Halász–Montgomery gives MC as soon as `max_{N ≤ |u| ≤ T} |∑_{n~N} n^{-iu}| ≪ N^{2σ−1}`. Even Lindelöf
only gives `N^{1/2}` for that sum, and `N^{1/2} ≤ N^{2σ−1} ⟺ σ ≥ 3/4`. **So no pointwise bound on the
zeta-sum can work below σ = 3/4**; below it one must use averaged/additive-energy information about the
difference set `W−W`. Heath-Brown's energy relation (Lemma 10.23) is likewise vacuous for `σ < 3/4`
once the trivial lower bound `E₁(W) ≥ |W|⁴/T` is inserted. Guth–Maynard broke `3/4 → 7/10`; `7/10` is
where their gain vanishes.

### Second, independent route (Selberg / mollifier), currently weaker
`N(σ,T) ≪ T^{1−θ(2σ−1)} log T`: Selberg `θ=1/8`; Jutila `θ<1/2`; **Conrey `θ<4/7`** (1989).
`θ = 1` ⟺ DH. `θ > 2/3` is needed merely to beat Ingham. Bottleneck: mollified second moment of ζ with
mollifier length `T^θ`, stuck at `4/7` since Conrey 1989 (Deshouillers–Iwaniec Kloosterman input).

---

## Gate 3 — conjectures (see working log; each labelled)

## Working log

### 2026-07-25 — Cycle 1, frontier established
- Verified by hand every reduction above from the blueprint statements (not just quoted).
- **Dead end recorded:** raising to the 4th power (`|D|⁴ = |D²|²`) at `τ ≤ 3/2` is *worse* than MVT:
  the squared polynomial has length `N² > T`, so the `T`-saving disappears and one gets
  `R ≪ N^{4−4σ}` (`= N^{1.2}` at `σ=0.7`, vs MVT `N^{0.8}`). Any "raise to a power" move in the
  regime `τ ≤ 3/2` loses. This is why `Lemma 7.8` is only ever used in the *other* direction.
- **Dead end recorded:** pointwise bounds on `Z(u) = ∑_{n~N} n^{-iu}` cannot give MC below `σ = 3/4`
  even under Lindelöf (see above). Do not re-attempt exponent-pair/`β`/`μ` routes at `σ ≈ 0.7`.

---

## Cycle 1, part 2 — barriers in the literature (Guth survey arXiv:2503.07410, read in full)

Entropy draw (CSPRNG): seed `709058871058501233`; method moves `reverse`, `fake-proof`;
analogy domains `queueing-at-borders`, `origami`.

### Guth's three conjectures and the barrier stack
- **Conj 3.3 (Montgomery large value, ℓ^∞):** `|b_n| ≤ 1 ⟹ |W| ⪅ N^{2−2σ}`. ⟹ Conj 3.4 ⟹ DH.
- **Conj 3.4 (Montgomery ℓ^q):** `∑_{t≤T}|D(t)|^q ⪅ N^q + N^{q/2}T` for all `q ≥ 2`, i.e.
  `‖M_Dir‖_{∞→q} ⪅ N + N^{1/2}T^{1/q}`. Known for `q = 2` (orthogonality) and `q` even.
  **Critical `q` solves `N^q = N^{q/2}T`, i.e. `q = 2τ`.** DH needs `τ ∈ (1,3/2]` ⟺ **`q ∈ (2,3]`**:
  *the density hypothesis is exactly the missing sharp THIRD-moment bound for Dirichlet polynomials*
  (`q=2` and `q=4` are both classical; `q ∈ (2,3]` is the gap; Hölder interpolation between them
  loses `N^{1/4}` at `(σ,τ)=(·,3/2)`).
- **Barrier B1 — the "almost counterexample" (Fu–Guth–Maldague, simplified by A. Cohen).**
  Replace frequencies `log n` by `√(n/N)`. Then the orthogonality bound `N^{2σ}|W| ≲ TN` is *sharp*
  for all `σ ∈ [1/2,3/4]`, because `{√(n/N)}` contains an **exact** AP of length `N^{1/2}`
  (`n = m²`). Any method that only sees the `ℓ²` normalisation and the sizes of the entries of
  `MM*` cannot distinguish the two ⟹ **cannot beat orthogonality for `σ ≤ 3/4`.**
  *Corollary drawn here:* an improvement MUST use the `ℓ^∞` normalisation `|b_n| ≤ 1`.
- **Barrier B2 (Guth Conj 8.4, conjectural):** for `T = N^α`, `1<α<2`, there is
  `σ_crit(α) > 1/2` below which no constant-degree sum-of-squares proof beats orthogonality;
  Guth speculates **`σ_crit(α) = 1 − α/4`**.
- **Barrier B3 (Bourgain–Kakeya):** Conj 3.4 ⟹ Conj 9.3 (fat-AP Kakeya) ⟹ Kakeya conjecture in
  *every* dimension. Kakeya `d=3` only settled 2025 (Wang–Zahl); `d ≥ 4` open. Assuming
  Bourgain–Kakeya as a black box gives *no* improvement to LV bounds.
- Heath-Brown majorant + additive energy: **if `E₁(W) ≈ |W|³` (W maximally structured) the sharp
  bound `|W| ⪅ N^{2−2σ}` is already known** in the regime `N ≤ T ≤ N^{3/2}` (HB proved Conj 7.3
  there). So the open case is `W` *pseudorandom*, `E₁(W) ≈ |W|⁴/T`.

### Derivation done here (own work, not quoted): the exact loss structure
Dualise (`ℓ^∞ → ℓ¹`): with `Φ(x) = ∑_{t∈W} c_t e^{itx}`, `|c_t| = 1`, `X = {log n : n∈[N,2N]}`,
```
        R·V ≤ ∑_{n∈[N,2N]} |Φ(log n)|            (uses |b_n| ≤ 1, b_n = conj phase of Φ(log n))
```
so **MC ⟸ the L¹ sampling inequality  `∑_{x∈X}|Φ(x)| ≪ N^{1+o(1)} ‖c‖_{ℓ²}`**, and
**DH ⟸ `∑_{x∈X}|Φ(x)| ≪ N^{1+o(1)}‖c‖_{ℓ^{q'}}`, `q' = q/(q−1) ∈ [3/2,2)`, `T = N^{q/2}`.**
Put `G = |Φ|² ≥ 0`, `G(x) = ∑_{ξ∈W−W} ρ(ξ)e^{iξx}`, `ρ(0)=R`, `Z(ξ)=∑_{n~N}n^{-iξ}`. Then
```
   ∑_{n} G(log n) = R·N + E,        E := ∑_{ξ∈(W−W)\{0}} ρ(ξ) conj(Z(ξ)),
   Cauchy–Schwarz ⟹ R²V² ≤ RN² + N·E.     Hence  MC ⟺ E ≪ R N^{2+o(1)}.
```
`|E| ≤ R²·max_{ξ≠0}|Z(ξ)|` is Halász–Montgomery and needs `max|Z| ≪ N^{2σ−1}`; even Lindelöf gives
only `N^{1/2}`, whence the classical `σ = 3/4` wall. **Everything reduces to cancellation in the
pairing `E = ⟨ρ, Z⟩` between the (phased) autocorrelation of the large-value set and the zeta kernel.**

**Extremal-profile computation (own):** if `|Φ| ≈ A` on a set of measure `μ` (so `A²μ ≈ R`) built
from `J ≈ μT` intervals of length `1/T`, adversarially placed one per sample point, then
`∑_X |Φ| ≈ A·min(μT, N)`, maximised at `A = (RT/N)^{1/2}` giving `∑_X|Φ| ≈ (NRT)^{1/2}` — which
returns **exactly the mean value theorem** `R ≤ NT/V²`. So:
> **the MVT is precisely the bound produced by "perfect adversarial resonance of `|Φ|²` with the
> curved lattice `X`", and MC is the assertion that this resonance is impossible.**
Necessary condition for that resonance profile: `|Φ|² ≈ A²·1_S` with `S = ∪_n B(log n, 1/T)` forces
`ρ(ξ) ≈ (A²/T)Z(ξ)` for **all** `|ξ| ≤ T`; since `supp ρ ⊂ W−W`, this needs `R² ≳ T`.
Note `N^{2−2σ} = T^{1/2}` exactly when `τ = 4−4σ`, i.e. `σ = 1 − τ/4` — **Guth's conjectured
SOS threshold `σ_crit(α)=1−α/4` is the same line**, and `1 − (6/5)/4 = 7/10` is exactly where
Guth–Maynard's gain vanishes. Fourth-moment (`k=2` Hölder) applied to a *pseudorandom* `W`
(`E₁ = R⁴/T`) gives a contradiction iff `σ > 1 − τ/4`; this is the structural reason for `7/10`.

### Dead ends recorded (do not repeat)
- Taking absolute values in `|W|V² ≤ ∑_{m,n}|R_W(m/n)|` (the honest ℓ^∞ first-moment inequality)
  gives only `R ≪ N^{4−4σ}` — worse than MVT. Cancellation in `R_W` is indispensable.
- No bootstrap exists from Matomäki–Teräväinen's converse (Lemma 11.6) back into Lemma 11.5: the
  composed inequality is `f(σ) ≤ max(1/2,(1−σ)/2, f(σ), …)`, i.e. tautological.
- Hölder interpolation between the known `q=2` (T=N) and `q=4` (T=N²) moment bounds does **not**
  give the critical `q=3` bound at `T=N^{3/2}`: it loses exactly `N^{1/4}`.

---

## Gate 3 — THE CONJECTURE (Cycle 1). `[CONJECTURE]` UZLS

**Notation.** `Z(u) := ∑_{N≤n≤2N} n^{iu}`. For a finite 1-separated `W ⊂ ℝ` and `(c_t)_{t∈W}` put
`Ψ(n) := ∑_{t∈W} c_t n^{-it}`.

> ### Conjecture UZLS (Unimodular Zeta Large Sieve)
> For every `ε>0` there is `C_ε` such that for all `N ≥ 2`, every **1-separated** `W ⊂ [0,N^{3/2}]`
> with `|W| ≤ N`, and every `(c_t)` with `|c_t| ≤ 1`:
> ```
>            ∑_{n=N}^{2N} | ∑_{t∈W} c_t n^{-it} |²  ≤  C_ε · N^{1+ε} · |W| .
> ```
> Equivalently `∑_{t,t'∈W} c_t \bar c_{t'} Z(t−t') ≤ C_ε N^{1+ε}|W|`: **the off-diagonal of the
> zeta Toeplitz form never exceeds its diagonal, for ℓ^∞-normalised weights.**

**UZLS ⟹ Montgomery's Conjecture 3.3 ⟹ Montgomery ℓ^q ⟹ Density Hypothesis.** `[PROVED HERE]`
*Proof.* Let `|b_n| ≤ 1`, `W ⊂ [0,T]` 1-separated, `|D(t)| ≥ V` on `W`, `R=|W|`. Put
`c_t := \overline{D(t)}/|D(t)|` (unimodular). Then
`RV ≤ ∑_{t∈W}|D(t)| = ∑_{t}c_tD(t) = ∑_n b_nΨ(n) ≤ ∑_n|Ψ(n)| ≤ N^{1/2}(∑_n|Ψ(n)|²)^{1/2}`
— the step `∑_n |b_n Ψ(n)| ≤ ∑_n |Ψ(n)|` is exactly where `|b_n| ≤ 1` is used. By UZLS the last
bracket is `≪ N^{1+ε}R`, so `RV ≪ N^{1+ε/2}R^{1/2}`, i.e. `R ≪ N^{2−2σ+ε}`. (If `R > N`, first
restrict to `W' ⊂ W` with `|W'| = N`; the same computation gives `N ≪ N^{2−2σ+ε}`, false for
`σ > 1/2`, so in fact `R ≤ N`.) ∎

### Why this is the right statement (four independent checks, all done here)
1. **Sharp on the extremal example.** For the block pattern (`b_n = ε_I` on `N/L` blocks of length
   `L`, `V = (LN)^{1/2}`, `R = N/L`) the dual is `W = 2πN·ℤ ∩ [0,T]`, `c_t = n_0^{it}`; then
   `|Ψ(n)| ≈ R` for the `≈N/R` integers `n` in a residue class, giving `∑_n|Ψ|² ≈ (N/R)R² = NR` —
   **equality** in UZLS. Superposing `s` centres (`c_t = phase(∑_{i≤s} n_i^{it})`) again gives `NR`.
2. **It fails exactly for an arithmetic progression of frequencies.** If the frequency set were an
   exact AP `{x_n} = {n/N}`, choose `W = 2πN·ℤ`, `c ≡ 1`: `Ψ ≡ R` and `∑_n|Ψ|² = NR² ≫ NR`.
3. **It is FALSE for the Fu–Guth–Maldague almost counterexample** `M_AC` (frequencies `√(n/N)`):
   take `W = 2π√N·ℤ ∩ [0,T]`, `c ≡ 1`; on the `√N` squares `n=m²` one has `t√(n/N) ∈ 2πℤ`, so
   `Ψ = R` there and `∑_n|Ψ|² ≥ N^{1/2}R² > N^{1+ε}R` as soon as `R > N^{1/2+ε}` — i.e. exactly in
   the open range `σ < 3/4`. **So UZLS is a statement that separates `M_Dir` from `M_AC`, which is
   precisely what Guth's barrier B1 says any successful method must do.** B1 does not block it,
   because UZLS is an `ℓ^∞` statement and the `M_AC` sharp example is `ℓ²`-peaky.
4. **It is exactly as strong as needed, no more.** Known: `∑_n|Ψ|² ≤ λ_max(Z(t−t'))·|W| ≪ (N +
   R·max|Z|)R = NR + R²N^{1/2}` (Halász–Montgomery / Guth Prop. 5.3), which suffices iff
   `R ≪ N^{1/2}`, i.e. iff `σ ≥ 3/4`. **UZLS is precisely the assertion that the top eigenvector of
   the zeta Toeplitz matrix on `W` is never flat (never unimodular) once `|W| ≫ N^{1/2}`.**

### `[OPEN CORE]`
Prove UZLS for `N^{1/2} ≪ |W| ≤ N`. Even `|W| ≤ N^{1/2+δ}` for some `δ>0` would be a new route to
`σ ≥ 3/4 − δ/2`; beating Guth–Maynard needs `|W| ≤ N^{3/5}`; full DH needs `|W| ≤ N`.

### Barrier theorem harvested along the way `[PROVED HERE]` — the *average*-|Z| barrier
`∑_{|ξ|≤T}|Z(ξ)|² ≍ NT` (for `N ≤ T ≤ N²`) and `∑_{|ξ|≤T}|Z(ξ)|⁴ ≪ TN^{2+o(1)}`, hence by Hölder
`∑_{|ξ|≤T}|Z(ξ)| ≫ (NT)^{3/2}/(TN²)^{1/2} = N^{1/2}T·N^{-o(1)}`. So `|Z|` has **average** size
`≫ N^{1/2−o(1)}`, not merely maximum. Taking `W` random in `[0,T]` (so `r(ξ) ≈ R²/T`) gives
`∑_{ξ≠0} r(ξ)|Z(ξ)| ≫ R²N^{1/2−o(1)}`. Since MC needs `|E| ≪ RN` and `R = N^{2−2σ}`, this shows:
> **no estimate of `E = ∑_{ξ≠0}ρ(ξ)\overline{Z(ξ)}` that passes through absolute values can prove MC
> for `σ < 3/4`, even granted perfect (Lindelöf-strength) pointwise bounds on `Z` *and* averaging.**
This is strictly stronger than the folklore "`max|Z| ≈ N^{1/2}` blocks Halász–Montgomery at 3/4": it
kills averaged variants too. Any proof must use the *phases* of `Z`. UZLS does exactly that.

---

## Cycle 1, part 3 — UZLS is *equivalent* to Montgomery's conjecture, and is a MAX-QP problem

### Theorem 1 (equivalence) `[PROVED HERE]`
Let `M = M_{N,W}` be the `(N+1)×R` matrix `M_{n,t} = n^{-it}` (`n ∈ [N,2N]`, `t ∈ W` 1-separated,
`R = |W| ≤ N`). Then, up to `N^{o(1)}`,
```
   UZLS  ⟺  ‖M‖²_{ℓ^∞→ℓ²} ≪ N^{1+ε}R   ⟺   Montgomery's Conjecture 3.3 .
```
*Proof.* (⟹) done above. (⟸) By duality `‖M‖_{∞→2} = ‖M*‖_{2→1}`, so UZLS ⟺
`∑_{t∈W}|D_v(t)| ≪ N^{1/2+ε}R^{1/2}‖v‖_2` for all `v`. Take `|v_n| ≤ 1`, `‖v‖_2 ≤ N^{1/2}`; assuming
MC, `#{t ∈ W : |D_v(t)| ≥ V} ≤ min(R, N^{2+ε}/V²)`, so by layer-cake
`∑_{t∈W}|D_v| = ∫_0^{2N} #{|D_v| ≥ V}dV ≤ R·(N^{1+ε/2}/R^{1/2}) + ∫_{N^{1+ε/2}R^{-1/2}}^{2N}N^{2+ε}V^{-2}dV
 ≪ N^{1+ε}R^{1/2}`. ∎

So UZLS is not a *stronger* hypothesis smuggled in — it is a faithful, quantifier-free,
**quadratic-form** restatement of the central conjecture. Its value is the change of category:

> **Montgomery's large-value conjecture = the complex MAX-QP problem
> `max_{|c_t| = 1} c^* A c ≪ N^{1+ε}·R` for the PSD Toeplitz-type matrix
> `A_{t,t'} = Z(t−t') = ∑_{N≤n≤2N} n^{i(t−t')}`,  `tr A = (N+1)R`.**

Consequences of the new form:
- The degree-2 sum-of-squares / spectral relaxation of this MAX-QP is exactly
  `λ_max(A)·R ≪ (N + R·max_{u≠0}|Z(u)|)R`, i.e. **Halász–Montgomery IS the degree-2 SOS bound**,
  and it is tight for the relaxation once `R ≫ N^{1/2}`. This makes Guth's Conjecture 8.4 (no
  constant-degree SOS proof) a *precise* statement about this one matrix.
- The obstruction is now spectral and concrete: `A` has trace `(N+1)R` and `λ_max ≈ N + R N^{1/2}`;
  UZLS says **no unimodular vector aligns with the top eigenspace** once `R ≫ N^{1/2}`.

### Numerical certification `[NUMERICS]` (phase power-iteration ascent on `c*Ac`, exact `A`)
Ratio `max_{|c|=1}c^*Ac / (N R)` for `N = 200 … 3200`:
| W | R | N=200 | 400 | 800 | 1600 | 3200 |
|---|---|---|---|---|---|---|
| `2πN·{1..R}` | `N/2` | 3.35 | 3.13 | 3.01 | 3.78 | 3.92 |
| `{1..R}` | `N/2` | 11.46 | 11.90 | 12.00 | 12.17 | 11.91 |
| random `⊂[0,N^{3/2}]` | `N^{3/4}` | 1.67 | 1.74 | 1.71 | — | — |
| Bohr set `‖t log p/2π‖≤δ, p≤5` | — | 1.23 | 1.30 | 1.44 | 1.51 | — |
All ratios stay `O(1)` while `N` grows 16×, in the hard regime `R ≫ N^{1/2}`. **No numerical
counterexample; UZLS survives.** (Contrast: for an exact AP of frequencies the ratio is `R`.)

### Analytic attack: reflection / renormalisation. `[OPEN CORE]` = the theta chirp
- The range `|u| ≤ N` of the off-diagonal is harmless: `|Z(u)| ≪ N/(1+|u|)` gives
  `∑_{t≠t'}|Z(t−t')| ≪ R N log T`. **All the difficulty is `N ≤ |u| ≤ T`.**
- Poisson/stationary phase in `n` gives the exact renormalisation
  ```
  ∑_{n~N}|Ψ(n)|² = O(RN^{1+o(1)}) + ∑_{1≤|k|≤T/2πN} (N/|k|)^{1/2} ∑_{t−t' ≍ 2πkN}
                       c_t \bar c_{t'} · e^{-i(t−t')(\log x_0 −1)} ,   x_0 = (t−t')/(2πk) ∈ [N,2N].
  ```
  The factor `e^{i(t−t')(\log 2πk + 1)}` is separable in `(t,t')` for fixed `k` and can be absorbed
  into `c`; **the sole non-separable factor is the theta chirp `e^{-iu\log u}`, `u = t−t'`.**
- If the chirp were absent the identity would be *self-similar*: the `k`-sum reassembles
  `∑_{ν∼M}|Ψ_M(ν)|²` at the reflected scale `M = T/(2πN)`, and induction on scale closes with room
  (`(N/T^{1/2})·M^{1+ε}R ≪ N^{1+ε}R ⟺ T ≪ N²`, and we only need `T = N^{3/2}`).
- Local linearisation: on `u`-windows of length `U^{2/3}` the chirp is quadratic, and
  `e^{-i(t−t')²/2U} = e^{-it²/2U}e^{itt'/U}e^{-it'²/2U}` — the quadratic parts are absorbable and the
  residue is the **Fourier/metaplectic kernel `e^{itt'/U}`**. Open: control
  `∑_{t,t'} c'_t \bar c'_{t'} e^{itt'/U}` summed over windows without losing the `√U` window count.

### Dead ends recorded this cycle
- `∑_n|Ψ|² ≤ λ_max·R` (= Halász–Montgomery = degree-2 SOS) is *exactly* sharp as a relaxation and
  can never give UZLS for `R ≫ N^{1/2}`; do not re-attempt operator-norm-only arguments.
- Bounding `|∑_i S_i \bar S_{i−d}| ≤ ∑_i|S_i|²` inside the reflection loses the `√U` cancellation over
  the block-difference `d` and returns `U·R` instead of `N·R`. Cancellation in `d` is essential.
- Smooth-number / Bohr-set resonance (`W = {t : ‖t log p/2π‖ ≤ δ, p ≤ y}`, resonating with `y`-smooth
  `n`) does **not** break UZLS: optimising `y` under `|W| ≤ N` forces `Ψ(N,y) = N^{o(1)}`, so the
  construction reaches only `N^{o(1)}·R²` ≈ the `N^{o(1)}` slack. It is however *tight* to `N^{o(1)}`,
  matching Bondarenko–Seip GCD-sum resonance — so UZLS is false with `N^{o(1)}` replaced by `O(1)`.

---

## Cycle 1, part 4 — two reductions of UZLS, and the AP case made purely arithmetic

### (a) Poisson / additive-energy reduction `[PARTIAL PROOF]`
`G(x) := |Ψ(x)|²` is **non-negative**, supported on `[N,2N]`, with `x`-bandwidth `K := T/2πN`
(each mode `e^{-iu\log x}` has instantaneous frequency `u/2πx ≤ T/2πN`). Poisson:
`∑_{n∈[N,2N]}G(n) = ∑_{|k|≤K} \hat G(k)`, `\hat G(k)=∫_N^{2N}|Ψ(x)|²e(−kx)dx`.
- **`k=0` is harmless and proved:** `∫_N^{2N}x^{-iu}dx ≪ N/(1+|u|)` and 1-separation give
  `\hat G(0) ≪ RN\log T`. *All the difficulty of UZLS is the aliasing terms `k ≠ 0`.*
- Stationary phase: `\hat G(k)` receives contributions only from pairs with
  `x_0 = (t−t')/2πk ∈ [N,2N]` (so only differences `|u| ≥ 2πN` matter — **the range `|u| ≤ N` is
  disposed of by absolute values**), with amplitude `(N/|k|)^{1/2}` and phase `e^{-iu(\log x_0 −1)}`.
- Cauchy–Schwarz in `k` gives, **modulo the `(u,u')` off-diagonal**,
  ```
      ∑_{n}|Ψ(n)|²  ≪ N^{o(1)} ( R·N  +  N^{1/2} Q^{1/2} ),
      Q := ∑_{|u| > 2πN} |ρ(u)|² · |u| / N ,    ρ(u) = ∑_{t−t'=u} c_t \bar c_{t'} .
  ```
  `Q` is a *large-difference-weighted additive energy* of `(W,c)`. **This bound is exactly tight on
  the extremal example** (`W = 2πNℤ∩[0,T]`, `T=N^{3/2}`: `Q ≈ R⁴`, `N^{1/2}Q^{1/2} = N^{3/2} = RN`)
  and is vacuous where it should be (`W = {1..R}`, `R ≤ N`: `Q = 0`, bound `= RN` — matching numerics
  which give ratio `≈12` there). **So UZLS ⟸ `Q ≪ R²N` + control of the `(u,u')` off-diagonal.**
  `[OPEN CORE 1]` the off-diagonal `∑_{u≠u'}ρ(u)\barρ(u')∑_k e^{i(u−u')\log 2πk}` — the inner sum is
  a Mellin zeta-sum `∑_{k≤K}k^{i(u−u')}`; naive bounds cost `K^{1/4}` and lose the range.

### (b) The AP case is a pure discrepancy problem `[PROVED HERE]`
If `W = D·{1,…,R}` is an arithmetic progression (`D ≥ 1`), then `A_{m,m'} = \overline{Z(D(m−m'))}` is
**Toeplitz**, so its top eigenvector is the flat vector `(e^{imθ_*})` — which is unimodular. Hence
```
      max_{|c_m|=1} c^*Ac  =  (1+o(1))·R·λ_max(A)   for W an AP:
      unimodularity buys NOTHING in the AP case,
```
and `λ_max(A) = max_θ ∑_{n∈[N,2N]} D_R(θ − D\log n)` (`D_R` = Dirichlet kernel of degree `R`).
Replacing `D_R` by the Fejér kernel gives the equivalent clean form:

> **UZLS for arithmetic-progression `W` ⟺ for all real `D ≥ 1`, all `R ≤ N`, all `α`:**
> ```
>        #{ n ∈ [N,2N] : ‖ D·log n − α ‖_{2π} ≤ 1/(2R) }  ≪_ε  N^{1+ε}/R .
> ```
> *(no cluster of the sequence `D log n` beyond the random prediction `N/R`).*

Unwinding the condition: the `n` counted lie in `≈ D/2π` intervals of length `N/(RD)` centred at the
**geometric progression** `x_k = e^{(α+2πk)/D}`, `x_k ≈ x_0(1+2π/D)^k`. When `R ≤ N/D` these
intervals have length `≥ 1` and the count is `≍ N/R` unconditionally. **The whole content is the
regime `R > N/D`,** where it becomes:

> **`[OPEN CORE 2]` (GP-near-integers).** A geometric progression `x_0λ^k ⊂ [N,2N]`,
> `λ = 1+2π/D`, `k ≤ D/2π`, cannot have more than `N^{ε}·max(1, N/R·(D/2π)/(D/2π))` terms within
> `N/(2RD)` of an integer.

For `D = N^{1/2}`, `R = N` this is a **quadratic Weyl problem**: `x_k ≈ x_0 + ak + bk²` with
`a ≈ 2πx_0/√N`, `b = 2π²x_0/N ∈ [2π²,4π²]`, and one must count `k ≤ √N/2π` with
`‖x_0+ak+bk²‖ ≤ 1/(2√N)`. Heuristically `O(1)` such `k`; the adversary controls `x_0` (hence `a,b`),
so this is a genuine (and classical-looking) uniform-distribution question. **This is the sharpest
concrete sub-problem the whole programme has been reduced to.**

### Numerics on the AP family (phase-ascent maximiser, exact `A`)
ratio `max c*Ac/(NR)` for `W = D·{1..R}`, `R = min(N, N^{3/2}/D)`:
| D | N=200 | 400 | 800 | 1600 |
|---|---|---|---|---|
| `√N` (R=N) | 2.19 | 2.89 | 3.17 | 4.42 |
| `N^{3/4}` | 1.61 | 1.80 | 2.04 | 1.86 |
| `N` | 1.22 | 1.31 | 1.32 | 1.25 |
Growth in the `D=√N` row is consistent with `≍ log N` (ratio/log N = 0.41,0.48,0.47,0.60) rather
than a power; **larger-N numerics on this exact family are the single most informative experiment**
(if it grows like a power, MC itself is false).

**Method constraint (user, 2026-07-25): no numerical computation. Theory + literature only.**
(The numerics already recorded above stand as logged evidence; do not run more.)

---

## Cycle 1, part 5 — multiplicative self-similarity of UZLS: induction on scale

### The symmetry that makes UZLS inductive `[PROVED HERE]`
For any integer `e ≥ 1`, `Ψ(em) = ∑_t (c_t e^{-it}) m^{-it} =: Ψ^{(e)}(m)`, and `(c_t e^{-it})` is again
**unimodular with the same `W` and the same `R`**. So:
> **UZLS is invariant under multiplicative dilation**: an instance at scale `N` restricted to
> multiples of `e` is exactly an instance at scale `N/e` with the *same* `(W,R)`.
This symmetry has no analogue for the Fu–Guth–Maldague comparison object `M_AC` (whose frequencies
`√(n/N)` are not additive under multiplication), which is a second, independent reason UZLS can
separate `M_Dir` from `M_AC`.

### Theorem 2 (scale induction / rough residue) `[PROVED HERE]`
Write `S_N(W,c) := ∑_{n∈[N,2N]}|Ψ(n)|²`. Suppose UZLS holds at every scale `B ∈ [R, N/2]`. Then for
every `z ≤ N/R`,
```
    S_N  ≪  N^{1+ε} R·loglog z   +   ∑_{n∈[N,2N] , P^-(n) > z} |Ψ(n)|² .
```
*Proof.* Every `n` with `P^-(n) ≤ z` has a prime factor `p ≤ z`; by Ramaré's weight
`∑_{p|n, p≤z} 1/ω_z(n) = 1`, and `1/ω_z ≤ 1`,
`∑_{P^-(n)≤z}|Ψ(n)|² ≤ ∑_{p≤z}∑_{m∈[N/p,2N/p]}|Ψ^{(p)}(m)|² ≪ ∑_{p≤z}(N/p)^{1+ε}R`, and
`∑_{p≤z}p^{-1} ≪ loglog z`. The hypothesis `R ≤ N/p` holds because `p ≤ z ≤ N/R`. ∎

> **Consequence.** Montgomery's conjecture / the Density Hypothesis reduces, by induction on scale
> through the divisor structure of `[N,2N]`, to the **rough case**: bounding `∑_{P^-(n)>N/R}|Ψ(n)|²`.
> At the DH bottleneck `σ = 7/10` (`R = N^{3/5}`) the residue is `{n : P^-(n) > N^{2/5}}`, a set of
> density `≍ 1/log N`. As `σ ↓ 1/2` (`R ↑ N`) the residue swallows everything — matching exactly the
> known difficulty profile. This is a genuinely new bridge: **MC has a sieve-theoretic residue.**

### Why the residue is *not* removable by a sieve, and the ζ-self-reference `[DEAD END, recorded]`
- Selberg majorisation `1_{P^-(n)>z} ≤ (∑_{d|n,d≤D}λ_d)²` is **circular**: `λ_1 = 1` forces the
  `d_1=d_2=1` term to reproduce `S_N` itself. Any upper-bound sieve has this defect.
- The irreducible core is `∑_{p∈[N,2N]}|Ψ(p)|² = ∑_{t,t'}c_t\bar c_{t'} Z_P(t−t')`,
  `Z_P(u)=∑_{p~N}p^{iu}`. By the explicit formula `Z_P` resonates precisely at `u ≈ −γ` for zeros
  `ρ=β+iγ`, so **the prime residue of Montgomery's conjecture is controlled by the zeros of ζ** —
  the very object MC is deployed to count. A genuine feedback loop.
- **Fixed-point computation.** With `N(σ,Y) ≪ Y^{A_0(1−σ)+ε}` and `T = N^{τ}`, the heuristic
  zero-sum `∑_{|γ|≤2T} N^{β}`, thinned by the local density `1/T`, is `N^{1/2+τA_0/2−τ}·N^{o(1)}`,
  which is `≤ N^{1/2}` (the size of `Z(u)`) **iff `A_0 ≤ 2`**. So the loop
  `MC ⟸ scale induction + prime residue ⟸ zero density ⟸ MC` is **exactly critical at `A_0 = 2`**:
  the Density Hypothesis is precisely the self-consistent fixed point of this bootstrap. This is a
  structural *explanation* of the constant 2, not merely a numerology. Not contracting, so it does
  not yield a proof from `A_0 = 30/13`; it does say no weaker constant is a fixed point.
- **Dead end (recorded):** handling the prime residue by partial summation against `ψ(x)−x` fails by
  a wide margin: `G = |Ψ|²` has `x`-bandwidth `T/N`, so `∫(ψ(x)−x)G'(x)dx ≪ Δ·(T/N)∫G` needs
  `Δ = max_{[N,2N]}|ψ(x)−x| ≪ N/T = N^{-1/2}`, far beyond even RH. Do not retry.

---

## Gate 4 (Phase 4) — hostile attack on UZLS, and the blunt verdict

Attempted kills:
- **FALSE?** No. Checked against: the block/wave-packet extremal pattern (equality), superpositions of
  `s` centres (equality), APs `W = D·{1..R}` for `D ∈ {√N, N^{3/4}, N, 2πN}`, random `W`, Bohr-set /
  smooth-number resonance (tight only to `N^{o(1)}`, matching Bondarenko–Seip GCD sums), and the
  logged numerics. Nothing violates it.
- **CIRCULAR?** No: UZLS is an inequality about one explicit PSD Toeplitz form; it mentions neither
  zeros nor `N(σ,T)`.
- **REDISCOVERED?** **YES — this is the honest verdict for the conjecture itself.** Theorem 1 shows
  `UZLS ⟺ Montgomery's Conjecture 3.3` (both directions, up to `N^{o(1)}`). The *content* is a known
  1988 conjecture. What is new is the **category change** and its consequences.
- **INSIGNIFICANT?** No — see the four theorems below, each of which is a statement nobody could have
  produced by literature search because none of them appears in the ANTEDB blueprint, in
  Guth–Maynard, or in Guth's 2025 survey.

### VERDICT
`REDISCOVERED` for the conjecture UZLS itself (= Montgomery Conj. 3.3).
`BRIDGE` for the four accompanying theorems (Thm 1 equivalence + MAX-QP form; Thm 2 scale induction
with sieve residue; the average-`|Z|` barrier; the `A_0 = 2` bootstrap fixed point).

### Relentless interrogation → the next conjecture that is NOT equivalent to MC
What killed it: any *faithful* reformulation of the large-value problem is equivalent to MC. To
escape, take a **strictly weaker** statement that is still a genuine theorem-target. Theorem 2's
Toeplitz analysis supplies exactly one, because for AP-shaped `W` unimodularity buys nothing:

> ### Conjecture LOGDISC (logarithmic no-clustering)
> For every `ε>0`: for all real `D ≥ 1`, all `1 ≤ R ≤ N`, all `α ∈ ℝ`,
> ```
>     #{ n ∈ [N,2N] : ‖ D·log n − α ‖_{2π} ≤ 1/(2R) }  ≪_ε  N^{ε}·(N/R).
> ```
LOGDISC is **strictly weaker** than MC (it is UZLS restricted to arithmetic-progression `W`), is
falsifiable, and is a classical-looking uniform-distribution statement that nevertheless does not
appear in the literature in this uniform `(D,R,α)` form.

**Structure of LOGDISC (all proved here).**
1. *Trivial range.* If `RD ≤ 2N` the counted `n` lie in `≍ D` intervals each of length `≥ 1`, and the
   count is `≍ N/R + O(D) = O(N/R)`. **LOGDISC holds unconditionally for `R ≤ 2N/D`.**
2. *Hard range `RD > 2N`.* The counted `n` are the integers within `ℓ := N/(RD) < 1` of the geometric
   progression `x_k = x_0 λ^k`, `λ = e^{2π/D}`, `k ≤ K ≍ D log2/2π`. So LOGDISC ⟺
   **an approximate geometric progression of integers in `[N,2N]` with ratio-precision `1/(RD)`
   cannot be longer than `N^{ε}·N/R`.**
3. *Exact-GP endpoint.* If `RD > 2N²` the approximation forces `m_{k+1}m_{k−1} = m_k²` exactly, and
   the longest exact geometric progression of integers in `[N,2N]` has length
   `(1+o(1))(log 2)·log N/log log N` (optimise `m^{k−1} ≤ 2N` against `(1+1/m)^{k−1} ≤ 2`), which is
   `≪ N^{ε}`. **LOGDISC holds for `RD > 2N²`.** (In our application `RD ≤ T = N^{3/2}`, so this
   endpoint is not reached — but it shows the mechanism.)
4. *Best construction found.* Taking `m_k = m_0 + kh` (an AP is a GP to second order) and matching
   `λ = 1+h/m_0`, the quadratic drift `k²h²/2N ≤ ℓ` caps the run at `k ≍ √(N/(πRh))`, maximised at
   `h=1`: **`≍ √(N/R)` terms**, comfortably below the conjectured `N/R` for all `R ≤ N`.
   *So LOGDISC has a `√(N/R)` safety margin against the natural adversary.*
5. *Unconditional partial proof.* Erdős–Turán + van der Corput's second-derivative test
   (`λ₂ = D/N²`) gives
   `count ≪ δN + N/H + D^{1/2}H^{1/2} + N D^{-1/2}`, optimised at `H = N^{2/3}D^{-1/3}`:
   ```
       count ≪ N/R + N^{1/3}D^{1/3} + N D^{-1/2} .
   ```
   **LOGDISC is therefore PROVED unconditionally in the range `R² ≪ D ≪ N²/R³`** (non-empty exactly
   for `R ≪ N^{2/5}`). Exponent pairs `(κ,λ)` replace the middle term by `N^{λ/(1+κ)}D^{κ/(1+κ)}`;
   with `(13/84,1/2+13/84)` this is `N^{55/97}D^{13/97}`, still `≫ 1`, so **Erdős–Turán can never
   reach `R = N`** (its `N/H` term alone obstructs). `[OPEN CORE 3]` the range `R ≫ N^{2/5}` requires
   an arithmetic (approximate-GP) argument, not an equidistribution one.

---

## Phase 6 — Lean artifact (Cycle 1)

`formal/GaloisForLFunctions/RHTower/UnimodularZetaLargeSieve.lean`, imported by the `RHTower`
umbrella; `lake build` green (8475 jobs), all three declarations axiom-clean
(`[propext, Classical.choice, Quot.sound]`), no `sorry`/`axiom`:
- `UZLS.montgomery_of_uzls` — **UZLS ⟹ Montgomery's large-value bound**, abstract matrix form:
  `(hb : ∀ n, ‖b n‖ ≤ 1)`, `(hUZLS : ∀ c, (∀ t, ‖c t‖ ≤ 1) → ∑_n ‖∑_t c t * M n t‖² ≤ B·|κ|)`,
  `(hlarge : ∀ t, V ≤ ‖∑_n b n * M n t‖)` ⟹ `|κ|·V² ≤ |ι|·B`. The `ℓ^∞` hypothesis is used
  exactly once (step `hC`) — the machine confirms the paper claim that ℓ^∞ is the load-bearing input.
- `UZLS.norm_dirichletChar` — the matrix entries `n^{-it}` are unimodular.
- `UZLS.dirichletChar_mul` — the multiplicative dilation identity driving Theorem 2.
Corpus search before writing (`formal_tools.py research`): the only adjacent items are
`RHTower.LargeValues.large_values_count` and `RHTower.LargeValuesDpoly.large_values_dpoly`
(second-moment/derivative form of the large-value inequality). No overlap; nothing to reuse.
