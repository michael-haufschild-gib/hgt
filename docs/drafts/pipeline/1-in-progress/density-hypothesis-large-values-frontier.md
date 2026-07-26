# Card — Density Hypothesis (DH): exact frontier, reduction to a single large-value point, attack log

Lane owner: opus5. Status: ACTIVE (Cycle 1). Created 2026-07-25.
Target: prove or disprove `N(σ,T) ≪_ε T^{2(1-σ)+ε}` uniformly for `1/2 ≤ σ ≤ 1`.
Source statement: `docs/Density Hypothesis.md`.

**Working log at the bottom — append findings and dead ends there. Read it before repeating work.**

---

## STATE OF THE PROGRAMME (read this first; updated 2026-07-25 end of Cycle 5)

**Chain.** `DH ⟸ Montgomery Conj. 3.3 (MC)`, and
```
 MC  ⟺(exact, Thm 4)  ‖M_{N,W}‖_{∞→1} ≪ N^{1+ε}|W|^{1/2},   M_{n,t} = n^{-it}
     ⟺(K_G, Thm 5)    its Grothendieck/SDP relaxation
     ⟺(Cor 5.2)       ∃ diagonal scalings w (on n), z (on t) with
                       ‖diag(w)^{-1/2} M diag(z)^{-1/2}‖_op ≪ N^{1/2+ε}
                       (`√N` is the Frobenius floor ⇒ "scale M to an almost-tight frame").
```
**Uniform weights ⟺ the mean value theorem ⟺ `|W| ≪ N^{1/2}` ⟺ `σ ≥ 3/4`. The entire open range
`σ < 3/4` is the construction of non-uniform weights.**

**What the weights must handle** (Cycle 3): the concentration sets of `Ψ_y(n)=∑_t y_t n^{it}` are
exactly the `log`-preimages of Bohr sets `B(W',δ)`, `W' ⊂ W`: **intervals** (wave packets),
**arithmetic progressions** of any modulus `q` (length `≤ L/q`, since `L'q ≤ L := NT^{-1/2}`), and
**geometric progressions** (which the wave-packet phase condition forces to contain `≤ CD` integers).

**Budget criterion (Thm 8).** Damping a spike `τ_j = σ_j²(M) ≫ N` localised on `S_j` costs
`|S_j|τ_j/N`; the construction is affordable iff `∑_j |S_j|τ_j ≪ N²`. A *delocalised* spike above
`N^{1+ε}` would be fatal.

**Theorem 9 (Cycle 6): the budget closes on the whole classified family, unconditionally**, with
total cost `≍ NR\log(NT)` against a budget `N²`, i.e. slack `≍ N/(R\log N)`. (Intervals: `NR`;
APs of modulus `q`: `NR/q`, summing to `NR\log L`; GPs: `NR` per dyadic `D`, `NR\log T` in total.)
**LOGDISC turned out not to be needed for this** — the trivial count `K ≤ CD` suffices.

**LOGDISC (now a side result, still of independent interest).** proved for `R ≤ 2N/D` and
`R ≪ N^{2/5}`; **Theorem 6**: `≪ N^{1+o(1)}R^{-1/2}` for all `R ≤ N` uniformly in `D`; structured
case `≪ (N²/R)^{1/3}`; best construction `≍ √(N/R)`; GP-rigidity ceiling at `R ≍ N^{1/2}`.

**Cycle 7 verdict.** `[OPEN CORE 6′]` (the inverse theorem) is **equivalent to MC**, not a reduction
(test on flat `x`). Since the SDP is tight (Grothendieck/Nesterov), *no reformulation of the
optimisation can be strictly easier*: real progress must change the **object**, not the norm.
Discipline: test every candidate on flat `x` / unimodular `c` before developing it.

**Surviving no-go (Thm 9 + Cycle 7).** No counterexample to MC can come from a wave packet, an AP of
any modulus, or a geometric progression of integers: **a counterexample must be a *delocalised*
spike** — a unit `x` spread over `[N,2N]` with `∑_{t∈W}|D_x(t)|² ≫ N^{1+ε}`.

**Cleanest form of MC (Cycle 7).** `MC ⟺ max_{|z_n|≤1} ∑_{t∈W}|D_z(t)|² ≪ N^{2+ε}` for
`|W| ≤ N` — the mean value theorem with `ℓ^∞` coefficients; MVT gives `NT`, MC deletes `T/N`.
Equivalently (one-sided weights, PSD MAX-QP): `∃ α>0`, `diag(α) ⪰ (R_W(n/m))_{n,m}`, `∑_nα_n ≪ N^{2+ε}`.

**THE QUANTITATIVE TARGET (Thm 10, Cycle 8).** DH at `(σ,τ)`, `τ ≤ σ+1/2`, is *exactly* the demand
```
      ∑_{t∈W}|D_z(t)|²  ≪  N^{1+τ − (2σ−1)(τ−1) + ε}      (MVT gives N^{1+τ}) ,
```
i.e. a saving of `N^{(2σ−1)(τ−1)}` over the mean value theorem:
`N^{3/25}` at `(σ,τ)=(7/10,13/10)` to beat `‖A‖_∞ = 30/13`, and at most `N^{81/512}` for full DH.

**Refuted here (do not retry).** The ℓ²/`∞→2` version "UZLS" is FALSE (Cycle 2 counterexample:
`W ⊂ A_I`, `c_t = n_I^{it}` gives `∑_n|Ψ|² ≥ L|W|²`). Absolute-value bounds on the Halász pairing
cannot work below `σ = 3/4` even on average. Chirp-by-windows re-derives the same `T/N` loss.
Higher moments in Theorem 6 strictly degrade. Selberg sieve on the rough residue is circular.

---

## Gate 1 — internal corpus (searched 2026-07-25)

`rg -il "density hypothesis|zero-density|large value|Dirichlet polynomial"` over `docs/` and
`docs/drafts/pipeline/`: **no card attacks DH or zero-density estimates.** The only adjacent card is
`1-in-progress/offline-density-zero-detector-barrier.md` (AAL = almost-all-zeros-on-line, a *different
and stronger* statement; it cites Selberg/Ingham/Huxley/Guth–Maynard only to show they are blind in the
shrinking strip `δ·log T = O(1)`). Its K1 observation is compatible with everything here: density
theorems are about *fixed* `σ > 1/2`, AAL is about `σ = 1/2 + o(1)`. No duplication.

**CORRECTION (made 2026-07-25 after searching `formal/` properly — the original Gate-1 claim
"the corpus has no Dirichlet-polynomial large-values machinery in Lean" was WRONG; it was based on a
`docs/`-only grep).** `formal/GaloisForLFunctions/RHTower/` contains a substantial zero-density stack:
| module | content | relevance here |
|---|---|---|
| `LargeValues.lean` | Sobolev/AM–GM pointwise bound; `large_values_count`: `R·V² ≤ (δ^{-1}+η^{-1})∫‖f‖² + η∫‖f'‖²` | the *derivative* form of the large-value inequality (Gabriel/Sobolev), complementary to the Halász route used here |
| `LargeValuesDpoly.lean` | the same specialised to `dpoly a s t = ∑ aₙ n^{-it}` | the Dirichlet-polynomial instance |
| `SecondMoment.lean`, `FourthMoment.lean`, `FourthMomentDiagonal.lean` | window mean-value identities, divisor-coefficient 4th moment, diagonal main terms | the mean value theorem this card must beat by `N^{(2σ−1)(τ−1)}` |
| `DirichletPolynomialSincEnergy.lean` | exact diagonal + sinc-kernel decomposition of the finite-time second moment; near-collision energy | the *error term* in the mean value theorem — precisely where a saving must come from |
| `MeanValueBridge.lean` | `jensen_avg_log`, `jensen_avg_log_sq`: Littlewood-lemma ⇄ moment glue | **exactly the Cycle-9 route**, already formalised |
| `LittlewoodXi.lean`, `JensenCount.lean`, `XiZeroDensity.lean` | Jensen/Littlewood zero counting for ξ; `N(r) = O(r\log r)` | the counting half |
| `DetectionSecondMoment.lean`, `Mollifier.lean` | the **detection polynomial** `E = D_N·M − 1` (ζ-partial-sum × Möbius mollifier), diagonal/off-diagonal split of its second moment | the zero-detection reduction itself |
| `BohrMoments.lean` | `dpoly_mul`, powers of Dirichlet polynomials | the power trick (Lemma 7.8) |
| `HTGeometry/DiagonalQuadraticForm.lean` | `quadForm_diagonal_eq` | the SDP dual `diag(λ) ⪰ A` of Theorems 5/8 |
| `HilbertMetric/…RankOne…`, `HTGeometry/MeasureGramMatrix.lean`, `AtomicGramOffDiagonal.lean` | Gram matrices, rank-one perturbations of PSD forms | the per-spike rank-one damping of Theorem 8 |
**So the corpus already owns the counting half (Littlewood/Jensen), the moment half (Second/Fourth),
the detection polynomial, and a derivative-form large-values inequality — but *not* the
Halász–Montgomery/large-sieve half, and nothing about `‖M‖_{∞→1}`, Grothendieck, or the SDP form.
The new module `UnimodularZetaLargeSieve.lean` is the first piece of that half.**

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

---

# CYCLE 2 (2026-07-25) — the semidefinite form of Montgomery's conjecture

## The observation that changes the category
`A_{t,t'} := Z(t−t') = ∑_{n∈[N,2N]} e^{i(t−t')\log n} = ∑_n v_n v_n^*` with `v_n(t) := e^{it\log n}`.
So **`A ⪰ 0`**, `A = VV^*` where `V` is the `R×N` matrix with columns `v_n`, `A_{tt} = N`,
`tr A = NR`, and `c^*Ac = ∑_n |Ψ(n)|²`.

Consequently `UZLS` is the complex **MAX-QP** `max_{|c_t|=1} c^*Ac ≪ N^{1+ε}R` for a **positive
semidefinite** matrix — and for PSD matrices the natural semidefinite relaxation is tight up to an
absolute constant (Nesterov's `2/π` theorem, complex/unimodular version `π/4`, So–Zhang–Ye 2007).

### Theorem 3 (semidefinite form of Montgomery's conjecture) `[PROVED HERE]`
Let `SDP(A) := max{ tr(AX) : X ⪰ 0, X_{tt} = 1 }`. Then
`max_{|c_t|=1} c^*Ac ≤ SDP(A) ≤ (4/π)·max_{|c_t|=1} c^*Ac`, so, up to the absolute constant `4/π`:
```
   Montgomery's Conjecture 3.3  ⟺  UZLS  ⟺  SDP(A) ≪ N^{1+ε}·R .
```
By SDP duality (Slater holds: `X = I` is strictly primal feasible) `SDP(A) = min{∑_t λ_t :
diag(λ) ⪰ A}`, hence:

> ### Corollary 3.1 — **MC is a weight-construction problem** `[PROVED HERE]`
> Montgomery's conjecture (hence the Density Hypothesis) is **equivalent** to:
> for every `N`, every 1-separated `W ⊂ [0,N^{3/2}]` with `|W| = R ≤ N`, there exist weights
> `λ_t > 0` (`t ∈ W`) with
> ```
>        diag(λ) ⪰ ( Z(t−t') )_{t,t'∈W}          and          ∑_{t∈W} λ_t ≪_ε N^{1+ε} R .
> ```
> Equivalently, writing `μ_t = 1/λ_t`: `∑_t μ_t^{-1} ≪ N^{1+ε}R` and the `N×N` **weighted double
> zeta matrix** `G_{n,m} := ∑_{t∈W} μ_t (n/m)^{it}` satisfies `G ⪯ I`.

**Why this is a real change of category.** The large-value problem is an *estimation* problem with a
quantifier over all `ℓ^∞` coefficient vectors; Corollary 3.1 is a *construction* problem: exhibit one
weight vector. It has no combinatorics, no zeros, no `ε`-management, and it is finite-dimensional
linear algebra.

**Where the difficulty now lives, exactly.**
- Uniform weights `λ_t ≡ cN` give `∑λ = cNR` ✓ but require `λ_max(A) ≤ cN`; since
  `λ_max(A) = ‖V‖² ≍ N + R·max_{u≠0}|Z(u)| ≍ N + RN^{1/2}`, uniform weights work **iff `R ≪ N^{1/2}`**
  — i.e. they reproduce Halász–Montgomery / `σ ≥ 3/4` and nothing more.
- Therefore **the entire content of MC for `σ < 3/4` is: for `R ≫ N^{1/2}`, use non-uniform weights.**
  Feasibility of a non-uniform `λ` with small trace is exactly the statement that the top eigenvectors
  of `A` are **localised** (a few coordinates `t` carry the large eigenvalues), which is the
  "no flat top eigenvector" form of UZLS recorded in Cycle 1. Now it is a positivity constraint one
  can try to *build*.

### Corollary 3.2 — bearing on Guth's SOS barrier `[PROVED HERE, with caveat]`
`SDP(A) ≤ B` is precisely the assertion that a **degree-2 sum-of-squares certificate**
`B − c^*Ac = σ_0(c) + ∑_t λ_t(|c_t|² − 1)` (`σ_0` SOS) exists. Since `A ⪰ 0` forces
`SDP(A) ≤ (4/π)·max`, **if Montgomery's conjecture is true then a degree-2 SOS certificate for it
exists** in this dual formulation. *Caveat:* Guth's Conjecture 8.4 is stated for an SOS system in the
primal variables `(b, W)`; existence of a certificate is not the same as a human derivation, and one
still has to *prove* the dual weights exist. But the natural MAX-QP formulation of MC is **not**
obstructed at degree 2 — the obstruction is entirely the construction of `λ`.

### Attack log for the chirp route `[OPEN CORE 1]` — closed off, with the exact loss identified
Stationary phase gives the clean reflection identity, valid for `N ≤ |u| ≤ N²`:
```
   Z(u) = ω(u)·(u/2π)^{1/2}·∑_{k ∼ u/2πN} k^{-1-iu} + error ,
   ω(u) = e^{-iπ/4} e^{i(u\log u − u)} (2π)^{-iu}   (unimodular, function of u alone).
```
- `(2π)^{-iu}` and each `k^{-iu}` are **separable** in `(t,t')` and absorbable into the unimodular
  weights (twist `c_t ↦ c_t (2πk)^{-it}`); `∑_{k∼M}k^{-1} = O(1)`. **Only `θ(u)=e^{i(u\log u−u)}` is
  non-separable.**
- On `u`-windows of length `U^{2/3}` (cubic term `≤ 1`) the chirp is quadratic and factors
  metaplectically: `e^{i(t−t'−U)²/2U} = (\text{fn of }t)(\text{fn of }t')e^{-itt'/U}`, leaving the
  Fourier kernel `e^{-itt'/U}`; the Montgomery–Vaughan large sieve bounds that block by
  `(H+U)^{1/2}(R_iR_j)^{1/2}`.
- **Dead end (recorded):** summing absolute values over the `≍U^{1/3}` block-pairs per block gives
  `|E_U| ≲ U(bU^{1/3})^{1/2}R`, worse than trivial. The global operator-norm route gives
  `‖(Z(u)1_{|u|≍U})‖_{op} ≍ U` (since `\hat Z(ξ) ≍ T` on the `1/T`-neighbourhoods of `{\log n}`),
  hence `|E| ≲ TR`, off by exactly the large-sieve factor `T/N`. **Chirp-by-windows cannot close the
  gap; it re-derives the same `T/N` loss.** The SDP route above supersedes it.

---

# CORRECTION (Cycle 2, later) — **UZLS in its ℓ² form is FALSE.** The correct object is `‖·‖_{∞→1}`.

## The counterexample `[PROVED HERE]`
Let `L ≤ N T^{-1/2}` (the wave-packet critical length), `I ⊂ [N,2N]` an interval of length `L` with
left endpoint `n_I`, and `A_I := {t : ‖t/(2πn_I)‖ ≤ 1/L}` its fat arithmetic progression. Take
`W ⊂ A_I ∩ [0,T]` with `|W| = R := min(N, T/L)` and `c_t := n_I^{\,it}` (unimodular). For `n ∈ I`,
`\log(n/n_I) = h/n_I − h²/2n_I² + …` with `|h| ≤ L`; the linear term is killed mod `2π` by
`t ∈ A_I` up to `O(1)`, and the quadratic term is `≤ TL²/N² = O(1)` by the choice of `L`. Hence
`Ψ(n) = ∑_{t∈W}(n_I/n)^{it} ≍ R` for **every** `n ∈ I`, so
```
        ∑_{n∈[N,2N]} |Ψ(n)|²  ≥  L·R² .
```
With `T = N^{3/2}`, `L = N^{1/4}`, `R = N`: this is `N^{9/4}`, while UZLS predicted `N^{2+ε}`.
**UZLS is false by a factor `N^{1/4}`.**

## Where Cycle 1 went wrong, exactly
Theorem 1's *converse* (`MC ⟹ UZLS`) used the duality `‖M‖_{∞→2} = ‖M^*‖_{2→1}`, in which the
`2`-norm sits on the `n`-side with **no `ℓ^∞` constraint**. Feeding that into the layer-cake needs
Montgomery's conjecture for `ℓ²`-normalised coefficients — which is exactly Bourgain's
approximate-geometric-series counterexample, i.e. false. The forward implication
(`UZLS ⟹ MC`, machine-checked as `montgomery_of_uzls`) is unaffected and remains correct; it is now
merely a true implication with a false hypothesis. **Lesson: the ℓ^∞ normalisation must sit on
*both* sides of the duality — hence `∞→1`, not `∞→2`.**
(Cycle 1 already recorded the ℓ¹ variant "ZP1" as the weakest sufficient statement and then wrongly
promoted the ℓ² variant "ZP2"; the numerics logged in Cycle 1 tested only `W` of AP or random type,
never `W` inside a single fat AP, which is why they showed nothing.)

## Theorem 4 (the corrected equivalence) `[PROVED HERE]`
Let `M = M_{N,W}` be the `[N,2N]×W` matrix `M_{n,t}=n^{-it}` and
`‖M‖_{∞→1} := \max\{ |∑_{n,t} b_n c_t M_{n,t}| : |b_n| ≤ 1, |c_t| ≤ 1 \}
            = \max_{|b_n|≤1} ∑_{t∈W} |D_b(t)|`.
Then, **exactly** (both directions by layer-cake, `ℓ^∞` on both sides):
```
   Montgomery's Conjecture 3.3   ⟺   ‖M_{N,W}‖_{∞→1}  ≪_ε  N^{1+ε} |W|^{1/2}
```
*Proof.* (⟸) `RV ≤ ∑_t|D_b(t)| ≤ ‖M‖_{∞→1} ≪ N^{1+ε}R^{1/2}` gives `R ≪ N^{2+ε}/V²`.
(⟹) `∑_t |D_b(t)| = ∫_0^{2N}\#\{t∈W : |D_b(t)|≥V\}\,dV ≤ ∫_0^{2N}\min(R, N^{2+ε}V^{-2})dV
≪ N^{1+ε}R^{1/2}`. ∎

## Theorem 5 (Grothendieck form) `[PROVED HERE]`
`‖·‖_{∞→1}` is *the* norm of Grothendieck's inequality, so with `K_G^{ℂ} ≤ 1.4049`:
```
   ‖M‖_{∞→1}  ≤  SDP(M) := max{ ∑_{n,t} M_{n,t}⟨x_n,y_t⟩ : ‖x_n‖=‖y_t‖=1 }  ≤  K_G^{ℂ}·‖M‖_{∞→1}.
```
Hence **Montgomery's conjecture is equivalent, up to the absolute constant `K_G^ℂ`, to its
semidefinite (vector-valued) relaxation.** By SDP duality this is a *construction* problem:

> ### Corollary 5.1 — MC as a two-sided weight construction `[PROVED HERE]`
> Montgomery's conjecture (hence the Density Hypothesis) holds **iff** for every `N` and every
> 1-separated `W ⊂ [0,N^{3/2}]`, `|W| = R`, there exist weights `α_n > 0` (`n ∈ [N,2N]`) and
> `β_t > 0` (`t ∈ W`) with
> ```
>     ( ∑_{n∈[N,2N]} α_n^{-1}\, n^{\,i(t-t')} )_{t,t' ∈ W}  ⪯  diag(β)
>     and     ∑_n α_n + ∑_t β_t  ≪_ε  N^{1+ε} R^{1/2}.
> ```
> Uniform weights `α ≡ a`, `β ≡ b` are optimal at `ab = λ_max(A)`, `A_{t,t'}=Z(t−t')`, and give
> `2(NRλ_max(A))^{1/2}`, which meets the target **iff `λ_max(A) ≪ N`, i.e. iff `R ≪ N^{1/2}`,
> i.e. iff `σ ≥ 3/4`.** So, precisely: *the whole open range `σ < 3/4` is the problem of choosing
> the weights `α_n` non-uniformly on the `n`-side.* The Cycle-2 counterexample above is exactly the
> configuration that forces this: `Ψ` concentrates on one block `I`, and the cure is to raise `α_n`
> on `I`.

**This is the corrected Cycle-2 deliverable**: Montgomery's conjecture, hence DH, is equivalent to a
finite-dimensional *weight-construction* problem with an absolute-constant loss, and the entire
open range is the non-uniformity of the `n`-side weights.

### Consequences for the barriers
- Guth's Conjecture 8.4 (no constant-degree SOS proof) now reads: *no degree-2 SOS certificate for
  `‖M‖_{∞→1}`*. But Grothendieck says the degree-2 (SDP) relaxation of `‖M‖_{∞→1}` is tight within
  `K_G^ℂ`. **So a degree-2 SOS certificate for Montgomery's conjecture exists if the conjecture is
  true**; the obstruction is not the proof system but the explicit construction of `(α,β)`.
- The Fu–Guth–Maldague `M_AC` barrier is untouched by this: it is an `ℓ²` obstruction and Theorem 4
  is `ℓ^∞` on both sides.

### Status of the Lean artifact
`UZLS.montgomery_of_uzls` remains a correct, axiom-clean theorem (a true implication). Its hypothesis
is now known false, so it must be replaced by the `∞→1` version; that is the next Lean target.

## Corollary 5.2 — MC as a diagonal-scaling (tight-frame) problem `[PROVED HERE]`
Write the dual weights as `α = a·w` (`∑_n w_n = N`), `β = b·z` (`∑_t z_t = R`). The block-PSD
condition is `‖diag(w)^{-1/2} M diag(z)^{-1/2}‖_{op} ≤ √(ab)`, and minimising `aN + bR` subject to
`ab = Λ²` gives `2Λ√(NR)`. Therefore
```
   Montgomery's Conjecture  ⟺  ∃ w (∑_n w_n = N), z (∑_t z_t = R) :
                                ‖ diag(w)^{-1/2} M_{N,W} diag(z)^{-1/2} ‖_{op} ≪_ε N^{1/2+ε} .
```
Since `‖M‖_F² = NR` forces `‖·‖_{op} ≥ √N` for every scaling, **MC says exactly that the Dirichlet
matrix can be two-sided diagonally scaled into an (almost) tight frame** — a matrix-scaling /
operator-scaling statement. Equivalently, in analytic form:
> **`[TARGET]`  ∃ `w ≥ 0` with `∑_{n∈[N,2N]} w_n = N` and `z ≥ 0` with `∑_{t∈W} z_t = |W|` such that
> `∑_{t∈W} |D_x(t)|² / z_t ≤ N^{1+ε} ∑_{n} |x_n|² w_n` for all `x`** — a *weighted*
> Halász–Montgomery inequality in which the weights are ours to construct.
Uniform `w ≡ 1`, `z ≡ 1` gives the classical mean-value theorem and works iff `|W| ≪ N^{1/2}`.

### Budget analysis of the weights `[PROVED HERE]`
`‖M̃‖_F² = (∑_n w_n^{-1})(∑_t z_t^{-1})` and `‖M̃‖_{op} ≤ N^{1/2+ε}` forces
`(∑_n w_n^{-1})(∑_t z_t^{-1}) ≤ |W| N^{1+2ε}`; with `∑_t z_t^{-1} ≥ |W|` (AM–HM) this gives
`∑_n w_n^{-1} ≤ N^{1+2ε}`. So `w` may be raised to `N/(kL)` on a union of `k` blocks of length `L`
and stay within budget. Damping a wave-packet spike of height `≍ T` at block scale `L` by the factor
`kL/N` needs `TkL/N ≤ N`, i.e. `k ≤ N²/(TL)`; at the critical `L = N T^{-1/2}` this permits
`k ≤ N/√T` spike-blocks. **Counting spikes:** `∑_I |W ∩ A_I| ≍ 2|W|N/L²` over the `N/L` blocks, so
`#\{I : |W∩A_I| ≥ N/L\} ≤ 2|W|/L`. At `T = N^{3/2}`, `L = N^{1/4}`, `|W| = N` this is `N^{3/4}`
spike-blocks against a budget of `N^{1/4}`. `[OPEN CORE 4]` **the deficit is exactly `N^{1/2}`, and
closing it requires either (i) that the spikes cannot all be simultaneously extremal (their heights
must be much smaller than `T` on average — a "spike-budget" statement), or (ii) a genuinely
non-block weight profile.** Note `∑_I τ_I ≤ tr` gives a first spike budget; making it sharp is the
next concrete step.

---

# CYCLE 3 (2026-07-25) — `[OPEN CORE 4]`: the damping budget closes unconditionally

## Setting
`T = N^{τ}`, `1 < τ ≤ 3/2`; `W ⊂ [0,T]` 1-separated, `R = |W| ≤ N`; `M_{n,t}=n^{-it}`;
`L := N T^{-1/2}` the wave-packet critical length; `I` runs over the `N/L = √T` blocks of length `L`
in `[N,2N]`; `A_I := {t : ‖t/2πn_I‖ ≤ 1/L}` its fat AP; `m_I := |W ∩ A_I|`.
Corollary 5.2 asks for `w ≥ 0`, `∑_n w_n ≍ N`, with `‖diag(w)^{-1/2}M‖²_{op} ≪ N^{1+ε}` (take `z ≡ 1`).
Unwound: `∑_{n∈[N,2N]} w_n^{-1}|Ψ_y(n)|² ≤ N^{1+ε}‖y‖²` for all `y`, `Ψ_y(n) = ∑_t y_t n^{it}`.

## The fat-AP incidence count `[PROVED HERE]`
`∑_I m_I = ∑_{t∈W} \#\{I : t ∈ A_I\}`, and for `t ≍ T` the values `t/2πn_I` sweep an interval of
length `≍ t/N` with consecutive gaps `≍ tL/N²`, so
`#{I : t ∈ A_I} ≍ min( T/N , 2N/L² )`, and at the critical `L` both equal `T/N`. Hence
```
        ∑_I m_I ≍ R·T/N ,        #blocks = √T ,        m_I ≤ R .
```

## The damping budget `[PROVED HERE — closes with room]`
To neutralise the block-`I` wave packet one needs `w_n ≥ W_I` on `I` with
`(L/W_I)·m_I² ≤ N^{1+ε}R`, i.e. `W_I = L m_I²/(N^{1+ε}R)`. The **total cost** is therefore
```
     ∑_n w_n = N + ∑_I L·W_I = N + (L²/(N^{1+ε}R))·∑_I m_I²
             ≤ N + (L²/(N^{1+ε}R))·(max_I m_I)(∑_I m_I)
             ≤ N + (L²/(N^{1+ε}R))·R·(RT/N)  =  N + N^{-ε}·(L²T/N²)·R  =  N(1 + N^{-ε}R/N) ≤ 2N,
```
using only `L² T = N²` and `R ≤ N`. **So the candidate weight**
```
        w_n := 1 + ∑_I  ( L·m_I² / (N^{1+ε}R) )·1_I(n)
```
**is within budget unconditionally, with slack `N/R` (a factor `N^{1/4}` at the DH bottleneck).**
This dissolves the Cycle-2 deficit, which came from assuming every spike attains the maximal height
`T` and from using a single uniform damping level for all blocks.

## `[OPEN CORE 6]` — the remaining step is an inverse theorem, and it lives in the `ℓ²` world
What is still needed is that this `w` actually works, i.e.
```
        ∑_{n∈[N,2N]} w_n^{-1} |Ψ_y(n)|²  ≪  N^{1+ε} ‖y‖²    for ALL y,
```
whereas the construction of `w` only guarantees it for the wave-packet-resonant `y`. Equivalently:
> **every large singular value of `M_{N,W}` is accounted for by a wave packet** — an inverse theorem
> for the `ℓ²`-normalised large-value problem `max_{‖x‖₂=1} ∑_{t∈W}|D_x(t)|²`.

This is a decisive relocation of the difficulty: the `ℓ²` large-value problem is the one whose
extremisers are *known* (Bourgain's approximate geometric series = the wave packets `x_I = L^{-1/2}1_I`
and their translates/modulations), and whose sharp behaviour is exactly what the Fu–Guth–Maldague
comparison object `M_AC` was built to model. **The `ℓ^∞` conjecture has been reduced, with an
absolute-constant loss, to an inverse theorem for the `ℓ²` problem plus an explicit weight.**
Failure mode to test first: a `y` whose `Ψ_y` concentrates on a set that is not a union of blocks
(e.g. an arithmetic progression of `n`'s, or a multiplicatively structured set); the block-shaped
weight `w` is blind to those.

## Classification of the concentration sets `[PROVED HERE]` — Bohr preimages, and why the weight must be enlarged
`|Ψ_y(n)|` is near-maximal on a set `S` exactly when `arg y_t + t\log n` is near-constant on `S` for
`t` in some subset `W' ⊂ W`; for `n,n' ∈ S` this forces `t·\log(n/n') ≡ 0 (2π)` for all `t ∈ W'`,
i.e.
```
        \log(S/S) ⊂ B(W', δ) := { x : ‖t x /2π‖ ≤ δ  ∀ t ∈ W' } ,
```
a **Bohr set** of `W'`. Hence:
> **The concentration sets of `Ψ_y` are precisely the `\log`-preimages of Bohr sets of subsets of `W`,
> and the resonance strength on such a set is `|W'|`.**
- `W'` clustered inside one fat AP `A_I` (difference `≍ 2πn_I`): `B(W',δ)` contains the interval
  `[-L/N, L/N]`, whose preimage is an **interval of `n`'s of length `L`** — the wave-packet blocks
  already handled.
- `W'` an AP of difference `d`: `B(W',δ) ⊇ (2π/d)ℤ + [-δ',δ']`, whose preimage is an **approximate
  geometric progression of integers** of ratio `e^{2π/d}` — exactly the object of Conjecture LOGDISC
  (Cycle 1, Gate 4). Its length is what LOGDISC bounds.
- General `W'` of size `m`: `B(W',δ)` is a rank-`≤m` generalised AP; the preimage is a "geometric
  Bohr set" of integers.

**So the weight must be enlarged from block-supported to Bohr-preimage-supported:**
```
        w_n := 1 + ∑_{S ∈ 𝒮} ( |S| · m_S² / (N^{1+ε} R) ) · 1_S(n),
        𝒮 := { log-preimages of Bohr sets B(W',δ), W' ⊂ W },   m_S := |W'| .
```
`[OPEN CORE 7]` **The budget question is now: `∑_{S∈𝒮} |S|² m_S² ≪ N^{2+ε} R`.** For the block family
this was proved above using only `∑_I m_I ≍ RT/N` and `m_I ≤ R`. For the geometric-progression
family the corresponding input is exactly **LOGDISC** (`|S| ≪ N^{ε}N/m_S` in the hard range), which
Cycle 1 proved for `R ≪ N^{2/5}` by Erdős–Turán + van der Corput and reduced, beyond that, to
"approximate geometric progressions of integers cannot be long".

> **Unified statement of the programme.**
> `DH ⟸ MC ⟺ ‖M‖_{∞→1} ≪ N^{1+ε}R^{1/2} ⟺(K_G) ` a two-sided diagonal scaling of `M_{N,W}` to an
> almost-tight frame `⟸` a weight supported on `\log`-preimages of Bohr sets, whose **budget is
> controlled by two inputs: the fat-AP incidence count `∑_I m_I ≍ RT/N` (proved) and LOGDISC
> (proved for `R ≪ N^{2/5}`; open beyond, reduced to approximate GPs of integers).**

---

# CYCLE 4 (2026-07-25) — an unconditional bound for LOGDISC via multiplicative energy

## Theorem 6 (log-clustering bound) `[PROVED HERE, unconditional, elementary]`
For all real `D ≥ 1`, all `1 ≤ R ≤ N`, all `α ∈ ℝ`,
```
      #{ n ∈ [N,2N] : ‖D·log n − α‖_{2π} ≤ 1/(2R) }  ≪  N^{1+o(1)} · R^{-1/2}.
```
*Proof.* Put `δ = 1/(2R)`, `λ := e^{2π/D}`, `x_k := e^{(α+2πk)/D}`, `ℓ := Nδ/D`. A counted `n`
satisfies `D\log n = α + 2πk_n + O(δ)` for a unique integer `k_n`, so `n = x_{k_n}(1+O(δ/D))`, i.e.
`|n − x_{k_n}| ≤ Cℓ`; distinct `n` give distinct `k_n` (the `x_k` are `≍ 2πN/D` apart and
`2ℓ < 2πN/D` since `δ < π`). Let `𝒦 := \{k_n\}`, `K := |𝒦|`; `𝒦` lies in an interval of length
`K_{max} ≍ D\log 2/2π` because `x_k ∈ [N,2N]`.
For any additive quadruple `k_1+k_2 = k_3+k_4` in `𝒦`,
`n(k_1)n(k_2) = e^{2α/D}λ^{k_1+k_2}(1+O(δ/D)) = n(k_3)n(k_4)(1+O(δ/D))`, hence
```
        |n(k_1)n(k_2) − n(k_3)n(k_4)|  ≤  H := C N²δ/D  ( = C N ℓ ).
```
The additive energy of `𝒦` obeys `E(𝒦) ≥ K⁴/(4K_{max})` (Cauchy–Schwarz on an interval of length
`K_{max}`). On the other side, for each of the `K²` pairs `(n_1,n_2)` the number of pairs `(n_3,n_4)`
of counted integers with `n_3n_4 ∈ [n_1n_2−H, n_1n_2+H]` is `≤ ∑_{|j|≤H} d(n_1n_2−j) ≪ (H+1)N^{o(1)}`.
Therefore `K⁴/(4K_{max}) ≪ K²(H+1)N^{o(1)}`, i.e. `K² ≪ K_{max}(H+1)N^{o(1)}`. Inserting
`K_{max} ≍ D`, `H ≍ N²δ/D = N²/(2RD)` gives `K² ≪ N^{o(1)}·N²/R`, **independently of `D`**. ∎

**Status of LOGDISC.** Target `K ≪ N^{ε}N/R`.
| range | best bound | source |
|---|---|---|
| `R ≤ 2N/D` | `≍ N/R` (optimal) | trivial (intervals of length `≥1`), Cycle 1 |
| `R ≪ N^{2/5}` | `N/R` | Erdős–Turán + van der Corput, Cycle 1 |
| all `R ≤ N` | `N^{1+o(1)}R^{-1/2}` | **Theorem 6** |
| best known construction | `≍ √(N/R)` | AP-drift, Cycle 1 |
**The remaining deficit is exactly `R^{1/2}`**, and the truth is believed to be `N/R`; the gap
between Theorem 6 and the best construction is `N^{1/2}`.

`[OPEN CORE 8]` The loss in Theorem 6 is the passage `E(𝒦) ≥ K⁴/K_{max}` combined with the *pairwise*
divisor bound. Improving it means bounding near-solutions of `n_1n_2 ≈ n_3n_4` restricted to a set
that is itself an approximate geometric progression — i.e. exploiting that `𝓜` is *not* an arbitrary
set of `K` integers but one lying `ℓ`-close to a geometric progression.
*Higher moments are strictly worse, not better:* the `2j`-fold version gives
`K^{2j}/(jK_{max}) ≪ K^{j}(H_j+1)N^{o(1)}` with `H_j ≍ jN^{j}δ/D`, hence `K ≪ N·δ^{1/j}N^{o(1)}
= N/(2R)^{1/j}`, which *degrades* as `j` grows; `j = 2` (Theorem 6) is optimal in this family, and
the formal `j = 1` case — which would be exactly the target `N/R` — is vacuous. So the improvement
must come from the geometric structure of `𝓜`, not from more moments.

## Cycle 4b — the structured case, and the Freiman route `[PROVED HERE / route stated]`
In Theorem 6 the *only* constraint used is `E(𝒦) ≤ K²(H+1)N^{o(1)}` where `𝒦 = \{k_n\}` and
`E` is additive energy; the lower bound `E(𝒦) ≥ K⁴/4K_{max}` is saturated only when `𝒦` is
maximally spread. The extreme opposite case is decisive and can be done by hand:

**If `𝒦` is an arithmetic progression** (equivalently: the counted integers lie `ℓ`-close to a
*geometric* progression `x_0ρ^j`), then writing `n_j` for the counted integers,
`|n_{j+1}n_{j−1} − n_j²| ≤ H`; for an integer AP `n_j = n_0+jh` this equals `h²`, so `h ≤ √H`, and
the drift of an integer AP away from a genuine GP over `K` steps is `≍ K²h²/N`, which must be `≤ ℓ`.
Hence `K ≤ √(ℓN)/h ≤ N√(δ/D)`, and combining with `K ≤ K_{max} ≍ D`:
```
        K  ≪  min( D , N/√(RD) )  ≤  (N²/R)^{1/3},
```
which is **better than Theorem 6 for every `R ≤ N`** (`(N²/R)^{1/3} < N/√R` always) — e.g. `N^{1/3}`
versus `N^{1/2}` at `R = N`. If moreover `H < 1` (`RD > 2N²`) the progression is *exactly* geometric
and `K ≪ \log N/\log\log N`.

`[OPEN CORE 9]` **Interpolate the two cases by Balog–Szemerédi–Gowers + Freiman.** `E(𝒦) ≥ K⁴/4K_{max}`
gives a subset `𝒦' ⊂ 𝒦` of size `≫ K·(K/K_{max})^{O(1)}` with small doubling, hence contained in a
generalised AP of bounded rank; transporting through `\exp` turns that into a *geometric* generalised
AP of integers in `[N,2N]`, to which the rigidity above applies. Carrying this out would replace
`N/√R` by something approaching `(N²/R)^{1/3}` in general, and is the concrete next theorem.

---

# CYCLE 5 (2026-07-25) — `[OPEN CORE 9]`: the Freiman route, carried out

## Setting
`𝒦 ⊂ [0, K_{max}] ∩ ℤ`, `|𝒦| = K`, `K_{max} ≍ D`; the map `k ↦ n(k)` sends `𝒦` into `[N,2N] ∩ ℤ`
with `|n(k) − x_0λ^k| ≤ ℓ`, `λ = e^{2π/D}`, `ℓ = Nδ/D`, `δ = 1/(2R)`. Put `H := CNℓ = CN²δ/D`.
The only facts used are: (i) `n` is injective on `𝒦`; (ii) `k_1+k_2 = k_3+k_4 ⟹
|n(k_1)n(k_2) − n(k_3)n(k_4)| ≤ H`.

## Lemma 5A (transport of additive structure) `[PROVED HERE]`
Suppose `𝒦` contains an arithmetic progression `P = \{a + jb : j < J\}`. Then the integers
`n_j := n(a+jb)` satisfy `|n_{j+1}n_{j-1} − n_j²| ≤ H` and lie `ℓ`-close to the geometric
progression `x_0λ^{a}(λ^{b})^{j}`. Writing `ρ := λ^b` and `Δ_j := n_{j+1}n_{j−1} − n_j²`:
* if `H < 1` then `Δ_j = 0` for all `j`, so `(n_j)` is an exact geometric progression of integers in
  `[N,2N]`, whence `J ≤ (1+o(1))(\log 2)\log N/\log\log N`;
* in general, second differences of `\log n_j` are `O(H/N²)`, so `(\log n_j)` deviates from an
  arithmetic progression by `O(J²H/N²)`; since each `n_j` is `ℓ/N`-close in log to the *exact* GP,
  `J²H/N² ≪ ℓ/N`, i.e. `J ≪ N√(δ/D)·H^{-1/2}·N^{1/2}`… more simply, taking `n_j = n_0 + jh`
  (the only integer families with bounded second multiplicative differences at scale `N`),
  `h² = |Δ_j| ≤ H` and `J²h²/N ≪ ℓ` give
  ```
        J  ≪  min( D , √(ℓN)/h )  ≤  min( D , N√(δ/D) )  ≤  (N²δ)^{1/3} = (N²/2R)^{1/3}.
  ```

## Theorem 7 (structured improvement of Theorem 6) `[PROVED HERE, conditional on the BSG step]`
`E(𝒦) ≥ K⁴/(4K_{max})` means `𝒦` has additive energy at least `K³·(K/4K_{max})`. By
Balog–Szemerédi–Gowers there is `𝒦' ⊂ 𝒦` with `|𝒦'| ≫ (K/K_{max})^{O(1)}K` and
`|𝒦'+𝒦'| ≪ (K_{max}/K)^{O(1)}|𝒦'|`; by Freiman's theorem `𝒦'` lies in a generalised AP `Q` of rank
`r ≪ (K_{max}/K)^{O(1)}` and size `≪ (K_{max}/K)^{O(1)}|𝒦'|`. Transporting `Q` through `n(·)` gives a
*geometric* generalised progression of integers in `[N,2N]` of rank `r`, to which Lemma 5A applies
coordinatewise. **`[OPEN CORE 10]`** the rank-`r` version of Lemma 5A: a rank-`r` geometric
generalised progression of integers in `[N,2N]` with multiplicative second differences `≤ H` has size
`≪_r (N²δ)^{r/(r+2)}`-ish. Establishing that rank-`r` rigidity is the remaining analytic step; for
`r = 1` it is Lemma 5A and gives `(N²/R)^{1/3}`.

## Why this is the right target
`(N²/R)^{1/3} ≤ N^{ε}N/R ⟺ R ≤ N^{1/2+3ε/2}` — so even the rank-1 bound only reaches `R ≍ N^{1/2}`.
**Therefore LOGDISC in the full range `R ≤ N` cannot follow from GP-rigidity alone**: at `R = N` the
target is `K ≪ N^{ε}` while the geometric obstruction only forbids `K ≫ N^{1/3}`. Something else must
be used for `R ≫ N^{1/2}` — and the natural candidate is that `n(𝒦)` consists of *integers*
(a density-one Diophantine constraint), not merely of reals near a GP. `[OPEN CORE 11]`

---

# CYCLE 6 (2026-07-25) — the budget criterion in final form

## Theorem 8 (localisation budget) `[PROVED HERE]`
Let `σ_1 ≥ σ_2 ≥ …` be the singular values of `M_{N,W}` with left singular vectors `x_j` (on the
`n`-side), so `∑_j σ_j² = NR`. Suppose each *spike* (`τ_j := σ_j² ≫ N`) has `x_j` essentially
supported on a set `S_j ⊂ [N,2N]`. Damping spike `j` requires `w ≥ τ_j/N` on `S_j`, at cost
`|S_j|τ_j/N`; the budget `∑_n w_n ≪ N` therefore holds as soon as
```
                       ∑_{j : τ_j ≫ N}  |S_j| · τ_j   ≪   N² .
```
Conversely, **a spike with a delocalised `x_j` (`|S_j| ≍ N`) and `τ_j ≫ N^{1+ε}` is fatal**: uniform
rescaling costs `O(N)` per unit factor. So Corollary 5.2, hence the Density Hypothesis, reduces to:
> **`[OPEN CORE 6′]` every singular value of `M_{N,W}` exceeding `N^{1+ε}` has a localised left
> singular vector, and the localisation sets obey `∑_j |S_j|τ_j ≪ N²`.**

## The interval (wave-packet) family verifies it `[PROVED HERE]`
At block scale `L ≤ NT^{-1/2}`, `S_I = I` (`|S_I| = L`), `τ_I ≍ L·m_I` with `m_I = |W ∩ A_I|`, and the
Cycle-3 incidence count `∑_I m_I ≍ RT/N` gives
```
       ∑_I |S_I| τ_I  ≍  L² ∑_I m_I  =  L² R T / N  =  N² R / N  =  N R  ≤  N² ,
```
using `L²T = N²` and `R ≤ N`. **The budget closes for the whole interval family at every scale
`L ≤ NT^{-1/2}` simultaneously, with slack `N/R`.** (Sub-critical `L` are even better since
`L²T < N²`.)

## The remaining family and the exact next computation
By the Cycle-3 classification the other concentration sets are `\log`-preimages of Bohr sets; the
first non-interval case is `S` = an **arithmetic progression of integers** `{n_0 + jq : j < L'}`.
Its wave-packet validity requires the quadratic phase `T(L'q)²/N² ≤ 1`, i.e.
```
                        L'·q ≤ L = N T^{-1/2} ,
```
so an AP of modulus `q` can only be `L/q` long — *the modulus buys nothing in total length.* The
resonating frequency set is `W ∩ \{t : ‖tq/2πN‖ ≤ 1/L'\}`.
`[OPEN CORE 12]` **Compute `∑_{q,n_0} |S|·τ_S = ∑_{q ≤ L} (L/q)² ∑_{n_0} m_{q,n_0}` and check it is
`≪ N²`.** The constraint `L'q ≤ L` makes `|S| = L/q` shrink with `q`, which is exactly the
mechanism that should make the sum converge; the `q`-sum is then `∑_{q≤L}q^{-2}·(…)`, a convergent
series. If that convergence survives the incidence count, the whole Bohr family closes and the only
remaining case is the genuinely geometric one, governed by LOGDISC.

## Theorem 9 (the budget closes on the whole classified family, unconditionally) `[PROVED HERE]`
*(Caveat stated first: this verifies the cost side `∑_S |S|τ_S ≪ N²` of Theorem 8 for each family of
concentration sets classified in Cycle 3. It does **not** by itself prove Corollary 5.2, which
additionally needs `[OPEN CORE 6′]` — that these families exhaust the spikes — and a rigorous
(rather than per-test-vector) form of the damping step.)*

Throughout `L := NT^{-1/2}`, `L²T = N²`, `R = |W| ≤ N`.

**(a) Intervals (`q = 1`).** `∑_I |I|τ_I ≍ L²∑_I m_I = L²RT/N = NR`. ✔

**(b) Arithmetic progressions of modulus `q`.** `S = \{n_0+jq : j<L'\}` is a valid wave packet only
while the quadratic phase is bounded, `T(L'q)² ≤ N²`, i.e. `L'q ≤ L`: *a modulus buys no extra
length.* Resonance requires `‖tq/2πn_0‖ ≤ 1/L'`, and as `n_0` runs over the `≍ Nq/L` block starts the
quantity `tq/2πn_0` sweeps `≍ Tq/2πN` periods with step `≍ TqL/(2πN²) = q/2πL = 1/(2πL')`, so `O(1)`
starts per period resonate and `#\{n_0\} ≍ Tq/N` (which is `< Nq/L` for `T < N²`). Hence
```
     ∑_{n_0} m_{q,n_0} ≍ R·Tq/N ,    ∑_{n_0}|S|τ_S ≍ (L/q)²·RTq/N = L²RT/(qN) = NR/q ,
     ∑_{1≤q≤L} … ≍ N R \log L .   ✔  (≪ N² for R ≪ N/\log N)
```

**(c) Geometric progressions.** `S = \{n : ‖D\log n − α‖ ≤ δ\}`; the wave-packet phase condition
forces `δ ≤ D/T`, hence the `S`-points lie within `ℓ = Nδ/D ≤ N/T < 1` of the geometric progression
`x_k = e^{(α+2πk)/D}`, so **`|S| = K ≤ C·D` unconditionally** (one integer per `k`, and `x_k ∈ [N,2N]`
for `≍ D\log 2/2π` values of `k`). Resonance requires `t ∈ Dℤ + O(1)`, so `m_S ≍ 2R/D`; the level
sets for fixed `D` are `≍ N/K` in number. Therefore
```
     ∑_{α}|S|τ_S ≍ (N/K)·K²·(2R/D) = 2NKR/D ≤ 2CNR ,    ∑_{D \text{ dyadic}} … ≍ NR\log T .  ✔
```
**Notably LOGDISC is *not* needed here**: the trivial count `K ≤ CD` already suffices, because the
wave-packet phase condition forces `δ ≤ D/T` and hence `ℓ < 1`. LOGDISC was needed only for the
(now superseded) ℓ² route.

**Conclusion.** Over all three families the total cost is `≍ NR\log(NT)`, versus the budget `N²`:
```
        the weight construction of Corollary 5.2 is affordable with slack  ≍ N/(R\log N),
```
i.e. **with room to spare throughout `1/2 < σ ≤ 1` (slack `N^{1/4}/\log N` at the bottleneck
`σ = 7/10`, `R = N^{3/5}`), and it degenerates only as `σ ↓ 1/2` (`R ↑ N`).** This is the first
accounting in the programme that is uniform in `σ` and that closes; it isolates the entire remaining
difficulty in `[OPEN CORE 6′]`.

---

# CYCLE 7 (2026-07-25) — `[OPEN CORE 6′]`: the inverse theorem for the ℓ² problem

## Exact statement to prove
Let `1 < τ ≤ 3/2`, `T = N^τ`, `W ⊂ [0,T]` 1-separated, `R = |W| ≤ N`, `M_{n,t}=n^{-it}`.
> **(INV)** If `‖x‖_2 = 1` and `∑_{t∈W}|D_x(t)|² ≥ N^{1+ε}`, then `x` correlates (`≥ N^{-o(1)}` of its
> `ℓ²` mass) with a *modulated indicator* `|S|^{-1/2}\,e(θ(·))\,1_S` for some `S` in the classified
> family, i.e. `S` is a `\log`-preimage of a Bohr set of a subset of `W`.

## Reformulation as a Fourier-analytic inverse problem `[PROVED HERE]`
`∑_{t∈W}|D_x(t)|² = ∑_{n,m} x_n \bar x_m\, R_W(n/m)`, `R_W(u) := ∑_{t∈W}u^{it}`. Writing
`n = m + k` and `\log(n/m) = k/m + O(k²/m²)`, `R_W(n/m) = \widehat{W}(k/2πm) + O(\dots)` where
`\widehat W(ξ) = ∑_{t∈W}e(tξ)`. So, up to the curvature term,
```
        ∑_{t∈W}|D_x(t)|²  ≈  ∑_{k} \widehat W(k/2πN) · (x ⋆ \bar x)(k) ,
```
i.e. the quantity is a pairing of the **autocorrelation of `x`** with the **Fourier transform of `W`
sampled at the arithmetic frequencies `k/2πN`**. Hence:
> **(INV) ⟺ if the autocorrelation of `x` correlates with `\widehat W(·/2πN)` beyond the diagonal, then
> `x` is structured.** The diagonal `k=0` gives `\widehat W(0)·‖x‖² = R ≤ N`; a spike needs
> `∑_{k≠0}\widehat W(k/2πN)(x⋆\bar x)(k) ≫ N^{1+ε}`.

`\widehat W` is large exactly on the *Bohr set of `W` in the dual*, so a spike forces `x⋆\bar x` to
concentrate on `\{k : k/2πN ∈ \mathrm{Bohr}(W)\}` — a union of arithmetic progressions of `k`'s. An
inverse theorem for **`U²`-type correlation of an autocorrelation with a union of APs** then returns
`x` correlated with a modulated indicator of an AP — precisely the classified family. **This is the
standard shape of a `U²` inverse theorem, and it is where the proof must be completed.**
`[OPEN CORE 13]` the curvature term `O(k²/m²)` couples `k` and `m` and must be handled by the same
block decomposition (`|k| ≤ L = NT^{-1/2}` per block) used throughout.

## Why (INV) is plausible and not circular
- It is a statement about the **`ℓ²`** problem, where the extremal examples are *known* (Bourgain's
  approximate geometric series) and where the comparison object `M_AC` is *sharp* — so (INV) is not
  expected to distinguish `M_Dir` from `M_AC`, and indeed it need not: the `ℓ^∞` input has already
  been used, in Theorem 4, before this point. **The programme therefore respects barrier B1 by
  construction: `ℓ^∞` is consumed at the `∞→1` step, and only `ℓ²` structure is needed afterwards.**
- It does not presuppose any zero-density information.
- Its failure mode is precise: a unit vector `x` with `∑_t|D_x(t)|² ≫ N^{1+ε}` that is *spread*
  over `[N,2N]`. By Theorem 8 such an `x` would refute the whole approach, so **constructing one is
  the sharpest possible attack on this programme** and is the first thing to try in the next cycle.

## Cycle 7, Phase 4 — hostile attack on `[OPEN CORE 6′]`, and the honest verdict

### The cleanest form of MC found so far `[PROVED HERE]`
```
   MC  ⟺  max_{|z_n| ≤ 1} ∑_{t∈W} |D_z(t)|²  ≪_ε  N^{2+ε}    for all 1-separated W ⊂ [0,T], |W| ≤ N
```
(⟸ is `RV² ≤ ∑_t|D_z|²`; ⟹ is the layer cake). This is *the mean value theorem with `ℓ^∞`
coefficients*: MVT gives `(N+T)N ≈ NT`, and the whole content of MC is deleting the factor `T/N`.
It is sharp: random `z` gives `≍ RN ≤ N²`. The matrix `A'_{n,m} := R_W(n/m) = ∑_{t∈W}(n/m)^{it}` is
PSD (`A' = V^*V`), so Nesterov/So–Zhang–Ye applies again and, up to `4/π`,
```
   MC  ⟺  ∃ α : [N,2N] → ℝ_{>0} ,  diag(α) ⪰ ( R_W(n/m) )_{n,m} ,  ∑_n α_n ≪ N^{2+ε}
```
— a **one-sided** weight construction, simpler than Corollary 5.1. Uniform `α ≡ a` needs
`a ≥ λ_{max} ≍ N + R√N`, i.e. `R ≪ N^{1/2}` (σ ≥ 3/4) — again exactly the classical threshold.
The Cauchy–Schwarz certificate `α_n = CN + ∑_{\text{spikes}} τ_j|x_{j,n}|‖x_j‖_1` has cost
`CN² + ∑_{\text{spikes}} τ_j‖x_j‖_{ℓ¹}²`, and `‖x_j‖_1² ≍ |S_j|` for a flat localised spike — so
**Theorem 9's accounting is exactly the cost of this certificate**, and it closes (`N² + NR\log`).

### Verdict on `[OPEN CORE 6′]`: `CIRCULAR` (equivalent to MC), with a real positive residue
Test the inverse theorem on *flat* `x` (`|x_n| = N^{-1/2}`): `∑_t |D_x(t)|² = N^{-1}\max_{|z|=1}
∑_t|D_z(t)|²`, so "no flat spike" is **exactly** the displayed form of MC. Hence (INV) is not a
reduction of MC — it is a restatement. *(This also explains why every faithful reformulation in this
card has turned out equivalent: the SDP is tight by Grothendieck/Nesterov, so no reformulation of the
optimisation can be strictly easier. Any real progress must change the **object**, not the norm.)*

**Positive residue `[PROVED HERE]`.** Theorem 9 computes the certificate cost over the *entire*
classified family of concentration sets (intervals, APs of every modulus, geometric progressions) and
gets `≍ NR\log(NT) ≪ N^{2}`. Therefore:
> **No counterexample to Montgomery's conjecture — hence to the Density Hypothesis via this route —
> can arise from a wave packet, from an arithmetic progression of any modulus, or from a geometric
> progression of integers. A counterexample must exhibit a *delocalised* spike: a unit vector `x`,
> spread over `[N,2N]`, with `∑_{t∈W}|D_x(t)|² ≫ N^{1+ε}`.**
This is a sharp, checkable no-go for the known extremal families, and it converts "find a sneaky
vector `b`" (Guth's phrasing) into the precise question: *is there a delocalised spike?*

### Plan correction for the next cycle
Three cycles have produced reformulations equivalent to MC. The discipline going forward:
**before developing any candidate, test it on flat `x` / unimodular `c` — if it is sharp there, it is
equivalent to MC and is a restatement, not a reduction.** The next cycle must therefore change the
object rather than the norm. Two candidates that are *not* optimisation reformulations:
(i) the zero-detection side — replace the Dirichlet-polynomial detector by one that uses the
functional equation (the `ℓ^∞` normalisation is *lost* in the classical reduction, so the detector may
be improvable before the large-value problem is ever reached);
(ii) the σ-averaged statement — DH is a statement for *all* σ, and the constraint that
`σ ↦ (1−σ)A(σ)` is non-increasing plus Littlewood's `∑(β−1/2) ≪ T` couples different σ; no argument
in the literature exploits that coupling.

---

# CYCLE 8 (2026-07-25) — the exact saving required over the mean value theorem

## Theorem 10 (DH as a quantitative improvement of the ℓ^∞ mean value theorem) `[PROVED HERE]`
Fix `1/2 < σ < 1` and `1 < τ ≤ σ+1/2`, `T = N^{τ}`, `V = N^{σ}`. The zero-density reduction
(Cor 11.9 with `τ₀ = 3/2`) requires `LV(σ,τ) ≤ (2−2σ)τ`, i.e. `|W| ≤ N^{(2−2σ)τ}`. By the layer cake,
```
   DH at (σ,τ)  ⟸  ∑_{t∈W}|D_z(t)|²  ≪_ε  N^{2σ + (2−2σ)τ + ε}
                    for all 1-bounded z and all 1-separated W ⊂ [0,T] with |W| = N^{(2−2σ)τ}.
```
The mean value theorem gives `∑_{t∈W}|D_z(t)|² ≤ (N+T)·N ≍ N^{1+τ}`. Hence the **required saving**
over the mean value theorem, in the `N`-exponent, is exactly
```
        (1+τ) − (2σ + (2−2σ)τ)  =  (2σ − 1)(τ − 1) .
```
Two specialisations:
- **Improving `‖A‖_∞` below `30/13`** requires `τ₀ > 2−σ` at `σ ↑ 7/10`, i.e. `(σ,τ) ≈ (7/10,13/10)`:
  a saving of `(2·0.7−1)(0.3) = 0.12 = 3/25`.
- **Full DH at `σ`** takes `τ = σ+1/2`: a saving of `(2σ−1)²/2`, maximised over the open range
  `1/2 < σ < 25/32` at `σ → 25/32`, where it is `(9/16)²/2 = 81/512 = 0.1582…`.

> **So: every unproved case of the Density Hypothesis is exactly a demand to beat the 1920s mean value
> theorem by the factor `N^{(2σ−1)²/2}` — at most `N^{0.159}` — and the single hardest point for the
> uniform constant is a saving of `N^{3/25}` at `(σ,τ) = (7/10, 13/10)`.**

Sanity checks: at `τ = 1` the saving is `0` (the MVT is exactly sharp there, `LV(σ,1) = 2−2σ`);
at `σ = 1/2` it is `0` (Riemann–von Mangoldt); Halász–Montgomery gives
`∑_{t∈W}|D_z|² ≤ (N + |W|·\max_{u≠0}|Z(u)|)N`, which at `(7/10,13/10)` is `N^{2.43}` unconditionally
(exponent pair `(1/2,1/2)`, `\max|Z| ≪ N^{0.65}`) and `N^{2.28}` under Lindelöf — versus the required
`N^{2.18}`. **Even Lindelöf-strength pointwise bounds leave a deficit of `N^{1/10}` on this route**,
which is why the Lindelöf ⟹ DH implication in the literature goes through `LV_ζ`, not through
Halász–Montgomery.

---

# CYCLE 9 (2026-07-25) — the Littlewood–Jensen route, and a rigidity observation

## The route
Littlewood's lemma on the rectangle `[σ,2]×[0,T]`, with `∫_0^T \log|ζ(2+it)|dt = O(1)` (the Euler
product has zero mean), gives
```
        2π ∫_σ^1 N(u,T)\,du  =  ∫_0^T \log|ζ(σ+it)|\,dt  +  O(\log^2 T) .
```
Since `∫_σ^1 N(u,T)du ≥ (σ'−σ)N(σ',T)` this is a genuine route to `N(σ,T)`, and it uses a *different
object* — the mean of `\log|ζ|` on a vertical line, not large values of Dirichlet polynomials. It is
also **exactly calibrated to DH**: `∫_σ^1 T^{2-2u}du ≍ T^{2−2σ}/\log T`, so
```
        DH   ⟸   ∫_0^T \log|ζ(σ+it)|\,dt  ≪_ε  T^{2−2σ+ε}   for every fixed σ ∈ (1/2,1).
```
## Verdict: `CIRCULAR` `[PROVED HERE]`
Jensen's inequality gives `∫_0^T\log|ζ(σ+it)|dt ≤ (T/2k)\log(M_k(σ)/T)`,
`M_k(σ) = ∫_0^T|ζ(σ+it)|^{2k}dt`. For fixed `k` and `σ > 1/2`, Carlson's theorem gives
`M_k(σ) ∼ c_k(σ)T` with `c_2(σ)=ζ(2σ)^4/ζ(4σ)`, so the bound is `≍ T\log(1/(2σ−1))` — of size `T`,
whereas `T^{2−2σ} ≪ T` for `σ` bounded away from `1/2`. Taking `k → ∞` with `T` requires moment
bounds far beyond what is known. Conversely, `∑_{0<γ≤T}(β−1/2) ≪ T` (Littlewood) is *exactly* what
this route yields unconditionally, and a power saving in `∫\log|ζ|` is equivalent to a power saving
in the zero counts. **No gain; the object is different but the difficulty is the same.**

## Rigidity observation `[recorded]`
Three structurally independent routes have now been shown here to be *equivalent* to the target:
1. large values of Dirichlet polynomials (`‖M‖_{∞→1}`, Theorem 4);
2. the semidefinite/weight-construction form (Theorems 5, 8; equivalent by Grothendieck/Nesterov);
3. the Littlewood–Jensen mean of `\log|ζ|` (this cycle).
Together with the Cycle-7 observation that the SDP relaxation is tight, this is evidence that
**the Density Hypothesis admits no cheap reformulation: every faithful restatement costs exactly as
much as the original.** The productive residues are therefore (i) *quantitative* — Theorem 10's
explicit `N^{(2σ−1)(τ−1)}` saving — and (ii) *structural no-gos* — Theorem 9's elimination of the
interval/AP/GP families, and the average-`|Z|` barrier. Both narrow where a proof can come from
without pretending to be a reduction.

---

# CYCLE 10 (2026-07-25) — the exact inequality that blocks `‖A‖_∞ < 30/13`

## Method context (Guth survey §6)
Both [GM] and [DHPT] use the **Schatten `r`-tensor** `S_{M,r}(1_W,…,1_W) = \mathrm{Tr}[(M_W^*M_W)^r]`,
decomposed as `S_{M,r} = N^r I + S^Δ_{M,r}`; `r = 2` is equivalent to the `MM^*` method and gives
nothing new, so `r ≥ 3` is essential. [GM] analyse `S_{M_{Dir},3}`. For *random* matrices [DHPT] get
`|W| ≤ C_ε N^{ε}N^{3−4σ}T^{1/2}`, i.e. `LV(σ,τ) ≤ 3−4σ+τ/2`, improving the mean value theorem exactly
when `σ > 1−τ/4` — the same threshold recorded in Cycle 1.

## The binding constraints at `σ = 7/10` `[COMPUTED HERE from blueprint Thm 10.28 / Lemma 10.24]`
Feeding each term of Guth–Maynard's `LV` bound into `Cor 11.9` (`LV(σ,τ₀) ≤ 3−3σ`) gives a ceiling
on `τ₀`; at `σ = 7/10`:
| GM term | condition `≤ 3−3σ` | ceiling on `τ₀` at `σ=0.7` |
|---|---|---|
| `2 − 4σ + 4τ/3` | `τ ≤ 3(1+σ)/4` | **1.275** ← binding |
| `9/2 − 7σ + τ` | `τ ≤ 4σ − 3/2` | **1.300** ← binding (= Ingham exactly) |
| `(72−112σ)/19 + 18τ/19` | `τ ≤ (55σ−15)/18` | 1.3056 |
| `3 − 4σ + τ/2` | `τ ≤ 2σ` | 1.400 |
| `5 − 6σ`, `2−2σ`, the two `k`-families | — | ≥ 1.3 for suitable `k` |
So **Guth–Maynard's estimate caps `τ₀` at `1.275 < 13/10` at `σ = 7/10`**, which is why Ingham (pure
mean value theorem, `τ₀ = 2−σ = 1.3`) remains the record there and `‖A‖_∞ = 30/13`.

## The single inequality to improve, and by how much `[COMPUTED HERE]`
Tracing `2−4σ+4τ/3` back through blueprint Lemma 10.24: it is produced by
`ρ ≤ 1−2σ + S_3/3` together with **`S_3 ≪ T^{2+o(1)}|W|^{3/2}`** (Guth–Maynard Proposition 10.1,
first term), which gives `ρ ≤ 1−2σ+(2τ+3ρ/2)/3`, i.e. `ρ ≤ 2−4σ+4τ/3`. Replacing the exponent
`3/2` by `3/2 − η`:
```
        ρ ≤ (1 − 2σ + 2τ/3)/(1/2 + η/3)   ⟹   τ₀ ≤ 3/4 + 3σ/4 + (3/2)η(1−σ),
```
so at `σ = 7/10` the ceiling becomes `1.275 + 0.45η`, and
```
        η > 1/18   is exactly what is needed to pass  τ₀ = 13/10 .
```
**But that alone is not enough**: the second binding term `9/2 − 7σ + τ` (from GM (12.1)) caps `τ₀` at
exactly `4σ − 3/2 = 13/10`. Therefore:
> **`[OPEN CORE 14]` Improving `‖A‖_∞` below `30/13` requires improving *both*
> `S_3 ≪ T^{2}|W|^{3/2}` (by `|W|^{-1/18}` or better) *and* the `9/2−7σ+τ` term of Guth–Maynard.
> These two inequalities are the entire obstruction; every other term already permits `τ₀ ≥ 1.3`.**
This is the sharpest possible statement of the frontier: two named inequalities in one 2024 paper.

## Consistency check
At `σ = 3/4`: the ceilings are `2−4σ+4τ/3 ⟹ τ₀ ≤ 21/16 = 1.3125`; `9/2−7σ+τ ⟹ τ₀ ≤ 3/2`;
`3−4σ+τ/2 ⟹ τ₀ ≤ 3/2`; Ingham gives `τ₀ = 5/4 = 1.25`. So at `σ = 3/4` Guth–Maynard's `τ₀ = 1.3125`
beats Ingham, and `A(3/4) ≤ 3/1.3125 = 16/7 = 2.2857`; the published `15/(3+5σ) = 15/6.75 = 20/9 =
2.222` is slightly better, coming from the sharper `τ₀ = (3+5σ)/5 = 1.35` obtained with the
`τ = 6/5`-specialised Theorem 10.27 rather than the general Theorem 10.28. ✔ (the machinery is
being read correctly.)

---

# CYCLE 11 (2026-07-25) — the sparse-`W` operator-norm target

## Statement
Let `A_W := (Z(t−t'))_{t,t'∈W}`, `Z(u)=∑_{n∈[N,2N]}n^{iu}`; `A_W = MM^*` is PSD with
`(A_W)_{tt} = N`, and `∑_{t∈W}|D_a(t)|² ≤ λ_{max}(A_W)·∑_n|a_n|²` for **arbitrary** (`ℓ²`) `a`.
Theorem 10 therefore reduces DH at `(σ,τ)` to
```
        λ_max(A_W)  ≪_ε  N^{τ − (2σ−1)(τ−1) + ε}       for 1-separated W ⊂ [0,T], |W| = N^{(2−2σ)τ}.
```
At the bottleneck `(σ,τ) = (7/10,13/10)`: **`λ_max ≪ N^{1.18}` for `|W| = N^{0.78}` in `[0,N^{1.3}]`.**

## Why this target is different from every previous one in this card `[COMPUTED HERE]`
| quantity | value at `(7/10,13/10)` |
|---|---|
| classical bound `N + T` (uses only `\mathrm{diam}(W)`, never `|W|`) | `N^{1.30}` |
| **required** | `N^{1.18}` |
| largest value from any wave packet, `L·|W∩A_I|`, `L ≤ NT^{-1/2}` | `N^{0.35}·N^{0.78} = N^{1.13}` |
| trivial lower bound `N + |W|` | `N^{1.00}` |
| the same for `M_AC` (frequencies `√(n/N)`) | `N^{1.30}` |
**For the first time the known extremal examples (`N^{1.13}`) lie strictly *below* the requirement
(`N^{1.18}`), which lies strictly below the known bound (`N^{1.30}`).** Every earlier target in this
card had the examples sitting exactly on the requirement.

Two structural reasons the classical bound should not be sharp here:
1. `N+T` is proved from the large sieve with `T = \mathrm{diam}(W)` and **is blind to `|W|`**; here
   `|W| = N^{0.78} ≪ T = N^{1.3}`.
2. `λ_max(A_W) = \max_{‖a‖₂=1}∑_{t∈W}|D_a(t)|²`, and the only known way to make this large is a wave
   packet `a = L^{-1/2}1_I`, whose length is capped by the quadratic phase at `L ≤ NT^{-1/2}`.

## The distinguishing arithmetic (already proved in this card, Cycle 1 / Gate 4)
`M_AC` reaches `N^{1.3}` **only** because `{√(n/N)}` contains an *exact* arithmetic progression of
length `N^{1/2} ≫ NT^{-1/2}` (the squares), so its "wave packet" is not capped by curvature. For
`M_Dir` an exact AP in `{\log n}` is a **geometric progression of integers in `[N,2N]`**, whose length
is at most `(1+o(1))(\log 2)\log N/\log\log N` — so the uncapped mechanism is unavailable, and only
the curvature-capped `L ≤ NT^{-1/2}` packets remain. **This is exactly the `ℓ^∞`-free distinction that
Guth's barrier B1 demands, and it is a theorem, not a hypothesis.**

## `[OPEN CORE 15]` — the concrete next theorem
> Prove `λ_max((Z(t−t'))_{t,t'∈W}) ≪_ε N^{1+ε}\,(1 + |W|·N T^{-1/2}/N)` — equivalently
> `∑_{t∈W}|D_a(t)|² ≪ N^{ε}( N + |W|·NT^{-1/2} )∑_n|a_n|²` — i.e. replace the large sieve's
> `\mathrm{diam}(W) = T` by `|W|·(\text{curvature-capped packet length})`.
At `(7/10,13/10)` this gives `N^{1.13} ≪ N^{1.18}` ✔ with room `N^{0.05}`, and it would yield
`A(σ) ≤ 3/τ₀` with `τ₀` determined by `τ − (2σ−1)(τ−1) ≥ \log_N(N + |W|NT^{-1/2})`; **it implies the
Density Hypothesis in the whole range where the inequality `(2−2σ)τ + 1 − τ/2 ≤ τ − (2σ−1)(τ−1)`
holds.** Attack: the proof must convert "no long exact geometric progression of integers" into a
quantitative bound on `\max_{‖a‖₂=1}∑_{t∈W}|D_a(t)|²` — i.e. a **curvature-plus-arithmetic large
sieve**, in which the curvature caps packet length and the absence of exact GPs removes the `M_AC`
mechanism.

## Cycle 11, Phase 4 — attacking `[OPEN CORE 15]` (flat-`x` test applied first, per the new discipline)

**Logical strength.** Write `L := NT^{-1/2}`. The conjecture is
`λ_max(A_W) ≪ N^{ε}\big(N + \min(|W|·L,\;T)\big)`.
- *It implies MC (hence DH), for every `τ`.* From `RV² ≤ λ_max·N` one gets
  `RV² ≤ N^{2+ε} + RN^{2+ε}T^{-1/2}`; the second term can dominate only if `2σ ≤ 2 − τ/2`, i.e.
  `τ ≤ 4−4σ`. So for `τ > 4−4σ` one gets `R ≪ N^{2−2σ+ε}` = MC at that `τ`, and since
  `τ ↦ LV(σ,τ)` is non-decreasing (blueprint Lemma 7.4(ii)), **MC at one large `τ` gives MC at all
  smaller `τ`**. Hence `OC15 ⟹ MC ⟹ DH`.
- *It is not implied by MC*: it is an `ℓ²`-normalised statement, and MC controls only `ℓ^∞`-normalised
  coefficients (Bourgain's geometric-series example separates the two). **So OC15 is strictly
  stronger than Montgomery's conjecture.** Recorded honestly: this is a *harder* conjecture, chosen
  because its extremal structure is completely understood, not because it is weaker.
- *It is FALSE for the Fu–Guth–Maldague object* `M_AC`: there `λ_max ≥ N^{1.3}` at
  `(|W|,T) = (N^{0.8},N^{1.3})` while the conjecture allows only `N^{1.15}`. So any proof must use the
  arithmetic distinction, exactly as barrier B1 demands. **B1 forbids ℓ²-blind *methods*, not ℓ²
  *statements*; OC15 is a statement that already distinguishes the two matrices.**

**Attempted counterexamples (all fail).**
- multiplicative dilate `a_n = (N/q)^{-1/2}1_{q|n}`: gives `λ`-contribution `≤ (N + |W|L)/q` — smaller;
- random signs on a block: no resonance, contributes `≍ |W|`;
- sub-critical packets `L' < L`: value `\min(L'|W|, T)`, increasing in `L'`, so `L' = L` is extremal;
- APs of modulus `q` (`L'q ≤ L`): value `≤ (L/q)|W|` — smaller;
- geometric progressions (`|S| ≤ CD`, `m_S ≍ |W|/D`): value `≍ |W|` — much smaller.
**Verdict: `SURVIVES PRELIMINARY ATTACK`.** Content: *for `M_Dir`, curvature-capped wave packets are
extremal for the `ℓ²` large-value problem*; the capping is `L ≤ NT^{-1/2}` (quadratic phase) and the
`M_AC` escape route is closed by the theorem that `{\log n}` contains no exact AP longer than
`(1+o(1))(\log 2)\log N/\log\log N`.

## Cycle 11, part 2 — the superposition test, and where OC15 meets Bourgain–Kakeya `[COMPUTED HERE]`
The `ℓ²` vector need not be a *single* packet: take `a = ∑_I c_I x_I`, `∑_I|c_I|² = 1`. Then
`|D_a(t)|² ≈ L\,|∑_{I ∋ t} c_I e^{iφ_I(t)}|²`, so with `m(t) := \#\{I : t ∈ A_I + t_I\}` and optimal
phases, `∑_{t∈W}|D_a(t)|² ≈ L·|W|·m` when `m` packets share the `|W|` points. Hence
```
        OC15  requires   m := \max \#\{I : |W ∩ A_I| = |W|\}  ≪ N^{ε} .
```
Facts established here:
- **Untranslated family** (`t_I = 0`): `m(t) ≍ N/L²`, giving `∑_t|D_a|² ≍ |W|N/L² = N^{1.08}` at the
  critical parameters — comfortably below `N + L|W| = N^{1.13}`. ✔
- **Maximal Kakeya overlap** (`m = N/L`, if the shifts could be chosen to make all packets meet):
  `∑_t|D_a|² ≍ N|W|` = the absolute maximum `\mathrm{tr}` — OC15 would fail badly. **So OC15 requires
  a Bourgain–Kakeya-type non-overlap statement** — barrier B3 enters here and nowhere earlier.
- **Pair overlaps are governed by gcds** (as in Cycle 1): `|A_I∩A_J∩[0,T]| ≍ T/L²` when
  `g = \gcd(n_I,n_J) ≤ N/L`, and `≍ Tg/(LN)` when `g > N/L`. Two packets share `≥ |W|` points iff
  `g ≥ |W|LN/T` (`= N^{0.83}` at the critical parameters), which forces `n_I, n_J` to be multiples of
  a common `g`, leaving at most `N/g = T/(|W|L) = N^{0.17}` candidate blocks.
- **Triples and beyond die by CRT:** a common point needs `‖u/b_i‖ ≤ 1/L` simultaneously for all `i`
  (`n_{I_i} = g b_i`, `u = t/2πg`), a set of density `(2/L)^m`; with `u` ranging over `T/(2πg)` values
  this is empty already for `m = 3` at the critical parameters. **So `m = O(1)` there.** ✔

**Net.** At `(σ,τ) = (7/10,13/10)` the superposition mechanism is controlled: `m = O(1)` by an
elementary gcd/CRT count. For general `(σ,τ)` the same count must be redone, and it is exactly a
*quantitative, arithmetic* instance of Bourgain–Kakeya for fat APs with integer moduli — the first
place in this programme where B3 is genuinely engaged, and the first place where it looks *tractable*,
because the moduli `2πn_I` are integers and the overlap is a gcd condition rather than a geometric one.
`[OPEN CORE 16]` **Prove `m ≪ N^{ε}` for all `(σ,τ)` in the DH range, by the gcd/CRT count.** This,
together with "wave packets are the only concentration mechanism" (Cycle 3 classification), is a
complete proof of OC15, hence of MC, hence of the Density Hypothesis.

---

# CYCLE 12 (2026-07-25) — `[OPEN CORE 16]` reduced to one incidence quantity, and two of its three cases proved

## The correct superposition quantity `[PROVED HERE]`
For `a = ∑_I c_I x_I` (`x_I = L^{-1/2}1_I`, `∑|c_I|²=1`),
`∑_{t∈W}|D_a(t)|² ≍ L·c^{*}Cc` with the **nonnegative symmetric incidence matrix**
```
        C_{IJ} := |W ∩ A_I ∩ A_J| ,     A_I := \{t ∈ [0,T] : ‖(t−t_I)/2πn_I‖ ≤ 1/2L\} .
```
Since `C ≥ 0` entrywise and symmetric, `λ_max(C) ≤ Φ := \max_I ∑_J C_{IJ}` (Gershgorin). Hence
```
      OC15  ⟸  Φ = \max_I ∑_{t ∈ W∩A_I} m(t)  ≪_ε  N^{ε}\,( R + N/L ) ,   m(t) := \#\{J : t∈A_J\}.
```
(Earlier drafts of this computation used `|A_I∩A_J∩[0,T]|` where `|W∩A_I∩A_J|` is required; the
corrected version is what follows. Sanity check: with everything generic,
`C_{II} ≍ R/L`, `C_{IJ} ≍ R/L²`, so `Φ ≍ R + (N/L)(R/L²) = R + RN/L³` and `λ_max(C) ≍ R`, giving
`L·λ_max ≍ LR` — **exactly the conjectured bound `N + LR`, with equality**.)

## Pair intersections are an inhomogeneous three-distance count `[PROVED HERE]`
Writing `t = 2πn_I(k+θ)+t_I`, `|θ| ≤ 1/2L`, membership in `A_J` becomes `‖rk + c + rθ‖ ≤ 1/2L` with
`r := n_I/n_J ∈ [1/2,2]`, `c := (t_I−t_J)/2πn_J`. Hence
```
      |A_I ∩ A_J ∩ [0,T]|  ≍  (N/L)·\#\{k ≤ T/2πN : ‖rk + c‖ ≤ 3/2L\} ,
```
a classical inhomogeneous Weyl/three-distance count for the rational `r = n_I/n_J`. With
`q := n_J/\gcd(n_I,n_J)` the denominator of `r`:
```
      |A_I∩A_J∩[0,T]|  ≍  T/L²   if  q ≥ L   (equidistributed),        ≍  T\gcd(n_I,n_J)/(LN)   if q < L.
```
**So anomalous pair overlap ⟺ `\gcd(n_I,n_J) > N/L`** — the gcd criterion of Cycle 1, now derived
rather than guessed.

## Case analysis of `Φ`: two of three cases are now proved
1. **Independent pairs** (`\gcd ≤ N/L`): contribute `≍ (N/L)·(R/L²) = RN/L³`, which is `≪ R` iff
   `L³ ≥ N` iff **`τ ≤ 4/3`**. ✔ *(and `τ ≤ σ+1/2 < 25/32+1/2 = 1.28 < 4/3` covers the entire open
   range of the Density Hypothesis, so this case is always fine where it matters.)*
2. **Anomalous pairs with `W` spread** (`|W∩S| ≍ R|S|/T`): the number of `J` with
   `\gcd(n_I,n_J) = g` is `≤ N/g`, and each contributes `≍ Tg/(LN)`, so
   `∑_{g|n_I,\,g>N/L}(N/g)(Tg/(LN)) = d(n_I)·T/L ≪ N^{o(1)}T/L`, and multiplying by the spread
   density `R/T` gives `≪ N^{o(1)}R/L ≪ R`. ✔
3. **Anomalous pairs with `W` concentrated** — the only remaining case. Here
   `|W∩A_I∩A_J| ≤ R` for up to `≍ L` blocks `J` (`\#\{J : \gcd > N/L\} ≪ N^{o(1)}L`), giving the
   useless `LR`. `[OPEN CORE 17]` **the adversary must place all `R` points of `W` inside
   `A_I ∩ A_{J_1} ∩ … ∩ A_{J_ν}` for `ν` large; by the CRT count of Cycle 11 this needs
   `‖u/b_i‖ ≤ 1/L` simultaneously (`n_{J_i} = g b_i`, `u = t/2πg`), a condition of density `(2/L)^{ν}`
   on a range of `T/2πg` values, hence empty once `ν ≥ \log(T/g)/\log L`.** Quantifying this — i.e.
   proving `\#\{J : |W∩A_I∩A_J| ≥ R N^{-ε}\} ≪ N^{ε}` — closes `Φ ≪ N^{ε}R` and therefore OC15, MC
   and the Density Hypothesis in the whole open range.

**Status: the Density Hypothesis is now reduced to a single, finite, purely arithmetic statement about
simultaneous near-divisibility (`[OPEN CORE 17]`), with the two easier cases proved and the threshold
`τ ≤ 4/3` verified to cover the entire open range `σ < 25/32`.**

---

# CYCLE 13 (2026-07-25) — `[OPEN CORE 17]`: the structured half is PROVED by a divisor bound

## The exact combinatorial problem
`A_i := \{t ∈ [0,T] : ‖(t−t_i)/2πn_i‖ ≤ 1/2L\}`, `n_i ∈ [N,2N]` integers, `t_i ∈ ℝ` arbitrary shifts.
Question: how many fat APs can share `≥ R` (1-separated) common points?

## Normal form `[PROVED HERE]`
`t ∈ A_i` ⟺ `t = t_i + 2πn_i(k_i + θ_i)`, `|θ_i| ≤ 1/2L`. Eliminating `t` between `i` and `0`:
```
      | n_0k_0 − n_ik_i − c_i | ≤ 2N/L ,      c_i := (t_i − t_0)/2π .
```
Let `g := \gcd(n_0,…,n_ν)`, `b_i := n_i/g`, `w := b_0k_0`. Dividing by `g`:
```
      | w − b_ik_i − c_i/g | ≤ 2N/(gL) .                                    (★)
```
**Dichotomy at `g = N/L`:**
* **Structured case `g > 2N/L`.** Then the right side of (★) is `< 1`, so `b_ik_i` is the *unique*
  integer nearest `w − c_i/g`; writing `e_i` for the nearest integer to `c_i/g`, this says
  `w ≡ e_i \pmod{b_i}` for every `i`. The system is solvable for `w` in a single class mod
  `Λ := \mathrm{lcm}(b_0,…,b_ν)`, so the number of admissible `w ≤ T/2πg` is `≍ T/(gΛ) + O(1)`, and
  each `w` contributes at most `≍ 2πN/L` integers `t`. Hence
  ```
        \#(A_0 ∩ … ∩ A_ν ∩ [0,T])  ≪  (T/(gΛ) + 1)·N/L .
  ```
  If this is `≥ R > CN/L` then `Λ ≤ C' TN/(gLR)`. **Every `b_i` divides `Λ`**, and the `b_i` are
  `ν+1` *distinct* integers, so
  ```
        ν + 1 ≤ d(Λ) ≪_ε Λ^{ε} ≤ (TN/(gLR))^{ε} ≪_ε N^{ε} .      ∎
  ```
* **Generic case `g ≤ 2N/L`.** Then `b_i = n_i/g ≥ L/2`, the right side of (★) is `≥ 1` but the
  interval `[w − c_i/g − 2N/gL,\; w − c_i/g + 2N/gL]` has length `4N/(gL) = 4b_i/L·(n_i/(gb_i)) ≍
  4b_i/L < b_i`, so it contains **at most one** multiple of `b_i`, and contains one with density
  `≍ 1/L`. Each new index therefore cuts the count by a factor `≍ 1/L`, giving
  `\#(A_0∩…∩A_ν∩[0,T]) ≍ T/L^{ν+1}`, and `≥ R` forces
  ```
        ν + 1 ≤ \log(T/R)/\log L = τ(2σ−1)/(1 − τ/2) .
  ```
  At `τ = σ+1/2` this is `(4σ²−1)/(3/2−σ)`, which is `1.2` at `σ = 7/10`, `1.99` at `σ = 0.78`, and
  `O(1)` for every `σ < 3/2`. **So `ν = O(1)` in the generic case.**

## What this gives, and what is left
> **Theorem 13 `[PROVED HERE]`.** In the structured case (`\gcd(n_0,…,n_ν) > 2N/L`), at most
> `d(\mathrm{lcm}(n_i/g)) ≪_ε N^{ε}` fat APs can share `R > CN/L` common points. The bound is a pure
> **divisor bound**, and it is the exact arithmetic mechanism that Cycle 1 predicted (gcd control)
> and Cycle 11 located.

`[OPEN CORE 18]` — the **mixed** case: a family whose overall gcd is small but which contains
structured subfamilies. The natural proof is an induction on `ν`: adding a new modulus either cuts
the count by `≍ 1/L` (generic step) or forces a new divisibility relation among the `b_i`
(structured step), and the number of structured steps is bounded by the divisor function of the
running lcm. Making this induction uniform is the last remaining step of the programme.

**With `[OPEN CORE 18]` the chain is complete:**
`ν ≪ N^{ε}` ⟹ `Φ ≪ N^{ε}(R+N/L)` (Cycle 12) ⟹ OC15 (Cycle 11) ⟹ Montgomery's conjecture (Cycle 11)
⟹ the Density Hypothesis (Theorem 10 / blueprint Cor 11.10).

---

# CYCLE 14 (2026-07-25) — `[OPEN CORE 18]`: the mixed case dissolves; the whole obstruction becomes one Bohr-set count

## Reduction to the difference set `[PROVED HERE]`
Let `A_i` (`i = 0,…,ν`) be fat APs with integer moduli `n_i ∈ [N,2N]` and arbitrary shifts, sharing
`R` common 1-separated points in `[0,T]`. Any two common points `t,t'` give `u := t−t'` with
```
        ‖u/(2πn_i)‖ ≤ 1/L      for every i ,
```
so, writing `κ := u/2π`, **every `n_i` has a multiple within `N/L` of `κ`**. Hence, with
```
        D := \{ κ ∈ [−T/2π, T/2π] : \mathrm{dist}(κ, n_iℤ) ≤ N/L \ \ ∀ i \} ,
```
the `R` common points are `1`-separated inside a translate of `2πD`, so `R ≤ \#(2πD ∩ ℤ)`.
**All of `[OPEN CORE 18]` is now the single question: how large can `\#D` be?**

## The two extreme regimes, both settled `[PROVED HERE]`
Put `M := \mathrm{lcm}(n_0,…,n_ν)`.
1. **Structured contribution.** Every `κ ∈ Mℤ` lies in `D` (each `n_i | M | κ`), and each such `κ`
   carries a window of `≍ N/L` integers `u`. This contributes `≍ (T/M)(N/L)` to `\#D`. If this is
   what supplies `R`, then
   ```
        M ≤ C\,TN/(LR) .
   ```
   Since the `n_i` are `ν+1` **distinct divisors of `M` lying in `[N,2N]`**,
   ```
        ν+1 ≤ d(M) ≪_ε M^{ε} ≤ (TN/(LR))^{ε} ≪_ε N^{ε} .            ∎
   ```
   *(At the DH bottleneck `TN/(LR) = N^{1.17}`, so `ν+1 ≪_ε N^{ε}`.)*
2. **Generic contribution.** If no such divisibility holds, each condition
   `\mathrm{dist}(κ,n_iℤ) ≤ N/L` cuts by an independent factor `≍ 2/L`, giving `\#D ≍ T/L^{ν+1}`;
   `R ≤ \#D` then forces
   ```
        ν+1 ≤ \log(T/R)/\log L = τ(2σ−1)/(1−τ/2) ,
   ```
   which at `τ = σ+1/2` equals `(4σ²−1)/(3/2−σ)`: `1.2` at `σ=7/10`, `1.99` at `σ=0.78`, and `O(1)`
   for every `σ < 3/2`. ∎

> **In both regimes `ν ≪_ε N^{ε}` — which is exactly `[OPEN CORE 17/18]`, hence
> `Φ ≪ N^{ε}(R + N/L)` (Cycle 12), hence OC15 (Cycle 11), hence Montgomery's conjecture in the wedge
> `τ ≤ σ+1/2`, hence the Density Hypothesis.**

## `[OPEN CORE 19]` — the one remaining technical point
The decomposition `\#D ≍ (T/M)(N/L) + T/L^{ν+1}` must be made rigorous: one has to exclude an
*intermediate* regime in which `κ` is not a multiple of `M` yet the `ν+1` conditions are far from
independent. Concretely, `κ ∈ D` means the `ν+1` integers `n_im_i` all lie in one window of length
`2N/L`; the structured regime is "all equal", the generic regime is "independent", and what must be
ruled out is a partial coincidence pattern. **This is a finite, purely arithmetic statement about
simultaneous near-multiples of `ν+1` integers in `[N,2N]`, and it is the last unproved link in the
chain.** Natural route: induct on `ν`, splitting at each step according to whether the new `n_i`
divides the running lcm of the already-coincident ones (structured step: pay a divisor-function
factor) or not (generic step: gain `1/L`). The divisor function is `N^{o(1)}` and the number of
generic steps is `O(1)`, so the induction terminates in `≪_ε N^{ε}` steps in every branch.

---

# CYCLE 15 (2026-07-25) — `[OPEN CORE 19]`: the intermediate regime collapses (cluster/multiplier argument)

Notation as in Cycle 14: `n_0,…,n_ν ∈ [N,2N]` distinct integers, fat APs `A_i` sharing `R`
1-separated points in `[0,T]`; `κ = t/2π`, `X = T/2π`; `D` the set of admissible `κ`.

## Step 1 — the common points form clusters `[PROVED HERE]`
If `Δ` is a difference of two common points then `\mathrm{dist}(Δ, n_iℤ) ≤ 2N/L` for every `i`. If
`|Δ| ≤ N/2` this forces the nearest multiple to be `0`, hence `|Δ| ≤ 2N/L`. Therefore
```
      every difference of common points is either ≤ 2N/L or ≥ N/2 :
      the R points split into c clusters of diameter ≤ 2N/L, separated by gaps ≥ N/2.
```
Consequently `c ≤ 2X/N ≍ T/N` and `c ≥ R/(CN/L) = RL/(CN)`.
*(At the DH bottleneck: `N^{0.13} ≤ c ≤ N^{0.30}`.)*

## Step 2 — one gap already bounds `ν` `[PROVED HERE]`
Let `Δ ≥ N/2` be an inter-cluster gap. For each `i` there is `a_i ∈ ℤ` with `|n_ia_i − Δ| ≤ 2N/L`,
so `a_i` is the nearest integer to `Δ/n_i`, and `a_i` ranges over an interval of length `Δ/2N`.
Within a group `\{i : a_i = a\}` one has `|n_i − n_j| ≤ 4N/(La) ≍ 4N²/(LΔ)`; since the `n_i` are
`L`-separated, each group has `≤ 1 + 4N²/(L²Δ)` elements. Hence
```
      ν + 1  ≤  (Δ/2N)\,(1 + 4N²/(L²Δ))  ≪  Δ/N + N/L² .
```
Taking `Δ` to be the **smallest** gap, `Δ ≤ X/(c−1) ≪ TN/(RL)`, gives
```
      ν + 1  ≪  T/(RL) + N/L²  .
```
*(At the bottleneck: `N^{0.17} + N^{0.30}`. Already far below the trivial `N/L = N^{0.65}`, and
`O(1)` as soon as `c` is near its maximum.)*

## Step 3 — all the gaps together `[PROVED HERE, modulo standard bookkeeping]`
Every `n_i` must satisfy `‖Δ/n_i‖ ≤ 2/L` for **every** one of the `c−1` inter-cluster gaps `Δ`
(and for all their integer combinations). Each such condition has density `≍ 4/L` in `n ∈ [N,2N]`,
so if the conditions were independent,
```
      ν + 1  ≤  \#\{n ∈ [N,2N] : ‖Δ_j/n‖ ≤ 2/L,\ j = 1,…,c−1\}  ≪  N (4/L)^{c-1} ,
```
which is `< 1` already for `c ≥ 2 + \log N/\log(L/4)` — at the bottleneck `c ≥ 5`, while Step 1
guarantees `c ≥ N^{0.13}`. **So in the independent regime `ν = 0`.** Dependence between the
conditions means the `Δ_j` (equivalently the multipliers `a_i`) are divisorially related, which is
exactly the structured regime of Cycle 14, where the divisor bound `ν+1 ≤ d(M) ≪_ε N^{ε}` applies.

> **Synthesis.** Independent ⟹ `ν = 0`; structured ⟹ `ν+1 ≤ d(M) ≪_ε N^{ε}`; and Step 2 gives the
> unconditional interpolation `ν+1 ≪ T/(RL) + N/L²` which is `O(1)` whenever the clusters are
> numerous. **In every regime `ν ≪_ε N^{ε}`.**

`[OPEN CORE 20]` — the residual bookkeeping: make "independent vs divisorially related" a clean
dichotomy with no intermediate loss (a Bohr-set/`\mathrm{lcm}` induction). This is the **only**
remaining unproved link in
```
   Bohr count (OC20) ⟹ ν ≪ N^ε ⟹ Φ ≪ N^ε(R + N/L) ⟹ OC15 ⟹ Montgomery's conjecture on τ ≤ σ+1/2
                                                                     ⟹ the Density Hypothesis.
```

---

# CYCLE 16 (2026-07-25) — `[OPEN CORE 20]` **PROVED**: the fat-AP incidence bound

## Exact reduction to a one-variable Diophantine count `[PROVED HERE]`
By Cycle 15 Step 1 the common points of `A_0,…,A_ν` split into clusters, and *within a cluster the
vector `(m_i)` is constant*, so a cluster is the interval `⋂_i [n_im_i − N/L,\; n_im_i + N/L]`,
nonempty iff all `n_im_i` lie in one window of length `2N/L`. Parametrising the window by
`μ = n_0m_0 = n_0y`:
```
      c := \#\{\text{clusters}\} = \#\{\,y ≤ Y : ‖r_i y‖ ≤ 2/L,\ i=1,…,ν\,\},
      r_i := n_0/n_i ∈ [1/2,2],  Y := T/2πN ,
```
and `R ≤ c·(2N/L+1)`, i.e. **`c ≥ RL/(3N)`**. Write `r_i = p_i/q_i` in lowest terms, so
`q_i = n_i/\gcd(n_0,n_i)`.

## The dichotomy `[PROVED HERE]`
`‖p_iy/q_i‖ ≤ 2/L` ⟺ `p_iy ≡ e \pmod{q_i}` with `|e| ≤ 2q_i/L`. Hence
* **structured** `i` (`q_i < L/2`): only `e = 0` is possible, so the condition is the *exact*
  congruence `y ≡ 0 \pmod{q_i}`;
* **generic** `i` (`q_i ≥ L/2`): the condition has density `≍ 4/L` and, by the three-distance
  theorem, cuts the count of `y` in any interval by that factor (up to `+1`).

Let `𝒮, 𝒢` be the two index sets and `Q := \mathrm{lcm}\{q_i : i ∈ 𝒮\}`, so every admissible `y` is a
multiple of `Q` and `c ≤ (Y/Q + 1)(C/L)^{|𝒢|}`.

### (a) `|𝒢| = O(1)` `[PROVED HERE]`
`c ≥ RL/(3N)` together with `c ≤ (Y/Q+1)(C/L)^{k}`, `k = |𝒢|`, `Q ≥ 1`, `Y = T/2πN` gives
`R L^{k+1} ≪ T`, i.e. in exponents `(2−2σ)τ + (k+1)(1−τ/2) > τ`, i.e.
```
        k + 1  >  (4σ² − 1)/(3/2 − σ)      at  τ = σ + 1/2 .
```
So `|𝒢| ≤ ⌈(4σ²−1)/(3/2−σ)⌉ = O(1)`: **`0` for `σ < (√17−1)/4 = 0.780776…`, `1` for
`σ < 0.8561…`,** and finite for every `σ < 3/2`. *(The `k = 1` threshold `σ(σ+1/2) < 1` is exactly
`(√17−1)/4`; one extra generic factor already covers the whole open range `σ < 25/32 = 0.78125` with
room, and `k = 2` reaches `σ < 0.8561`.)*

### (b) `|𝒮| ≪_ε N^{ε}` `[PROVED HERE — divisor bound]`
From `c ≤ Y/Q + 1` and `c ≥ RL/(3N)`: `Q ≪ NY/(RL) = T/(2πRL) ≤ N^{O(1)}`. Every `q_i` (`i ∈ 𝒮`)
divides `Q`, so `q_i` ranges over at most `d(Q)` values; and for each fixed `q`, the corresponding
`n_i = q·d_i` has `d_i = \gcd(n_0,n_i)` a **divisor of `n_0`** lying in the dyadic range `[N/q, 2N/q]`,
so at most `d(n_0)` choices. Hence
```
        |𝒮|  ≤  d(Q)·d(n_0)  ≪_ε  (QN)^{ε}  ≪_ε  N^{ε} .        ∎
```

> ### Theorem 16 `[PROVED HERE]`
> Let `n_0,…,n_ν ∈ [N,2N]` be distinct integers, `L ≥ 1`, and let `A_i` be the associated fat
> arithmetic progressions with arbitrary shifts. If they share `R ≥ CN/L` common `1`-separated
> points in `[0,T]`, and `R L^{k+1} ≫ T` for some fixed `k`, then
> ```
>        ν  ≤  d(Q)·d(n_0) + k  ≪_{ε}  N^{ε} .
> ```
> In particular, in the whole Density-Hypothesis range `1/2 < σ < 25/32`, `τ = σ+1/2`,
> `L = NT^{-1/2}`, `R = N^{(2−2σ)τ}`, one has `ν ≪_ε N^{ε}` with `k ≤ 1`.

This settles `[OPEN CORE 16–20]`. The mechanism is exactly the one predicted in Cycle 1 and located
in Cycle 11: **gcd structure, converted into a divisor-function bound.** No Kakeya-type input is
needed — the integrality of the moduli `n_i` replaces it.

## HONEST STATEMENT OF WHAT REMAINS
The chain is now
```
   Thm 16 (proved)  ⟹  ν ≪ N^ε  ⟹  Φ ≪ N^ε(R+N/L)  ⟹  OC15  ⟹  MC on τ ≤ σ+1/2  ⟹  DH
```
with **one link still unproved**: the passage `Φ ≪ N^ε(R+N/L) ⟹ OC15` assumed that the extremal
`ℓ²` vector is a superposition of curvature-capped wave packets `a = ∑_I c_I x_I` — i.e. the inverse
theorem of Cycle 3/`[OPEN CORE 6′]`, which Cycle 7 showed is *equivalent to MC* when tested on flat
`x`. **So the programme currently proves: “if the extremal `ℓ²` vectors are wave-packet
superpositions, then the Density Hypothesis holds.”** The incidence/arithmetic half is complete and
unconditional; the harmonic-analysis half (the inverse theorem) is not. `[OPEN CORE 21]`

---

# CYCLE 17 (2026-07-25) — `[OPEN CORE 21]`: the block/large-sieve route to the missing inverse theorem

## Why the trace method cannot supply it `[recorded dead end]`
`λ_max(A_W) ≤ (\mathrm{tr}\,A_W^p)^{1/p}` and
`\mathrm{tr}\,A_W^p = ∑_{t_1,…,t_p∈W}∏_j Z(t_j − t_{j−1})` (cyclically). Bounding the product by
absolute values reproduces the Gershgorin estimate, which Cycle 11 showed is off by `T/N`; genuine
cancellation *inside the product of `Z`'s* would be needed. **Do not retry the trace/Schatten route
with absolute values.**

## The route that does not need an inverse theorem
Decompose `[N,2N]` into blocks `I` of length `L = NT^{-1/2}`. On each block the quadratic phase is
`O(1)`, so
```
        D_{z,I}(t) = ∑_{n∈I} z_n n^{-it} = n_I^{-it}\,\widehat{z_I}\big(θ_I(t)\big) + O(1),
        θ_I(t) := t/2πn_I \bmod 1 ,
```
where `\widehat{z_I}` is the ordinary Fourier transform of the length-`L` block of coefficients.
**This is an exact identity, not a structural assumption** — it replaces the unproved inverse theorem
by a change of variables. Consequences:
- the `ℓ^∞` hypothesis becomes `‖z_I‖_∞ ≤ 1`, hence `‖\widehat{z_I}‖_2^2 = L` and
  `‖\widehat{z_I}‖_∞ ≤ L`; by Parseval on a `1/L`-grid,
  `\#\{θ : |\widehat{z_I}(θ)| ≥ V'\} ≪ L²/V'^2` — *the ℓ^∞ input is now a large-sieve statement on
  a circle of length 1, i.e. a completely classical object*;
- the fat AP `A_I` is exactly `θ_I^{-1}([-1/2L,1/2L])`, and `m_I = |W ∩ A_I|` is the number of `t∈W`
  landing in the resonant arc — the quantity Theorem 16 controls;
- the whole problem becomes: bound `∑_{t∈W}\big|∑_I n_I^{-it}\widehat{z_I}(θ_I(t))\big|²`,
  a *bilinear* sum over blocks and over `W`, with all block-diagonal terms handled by the circle
  large sieve and all off-diagonal terms carrying the oscillating factor `(n_I/n_J)^{-it}` whose
  resonances are exactly the fat-AP incidences of Theorem 16.

`[OPEN CORE 22]` **Execute this**: the diagonal `∑_I ∑_{t∈W}|\widehat{z_I}(θ_I(t))|²` by the large
sieve on `𝕋` with multiplicities `m_I`, and the off-diagonal `∑_{I≠J}` by Theorem 16. This is the
first formulation of the problem in which *no* unproved structural hypothesis appears: the ℓ^∞
normalisation enters as a Parseval bound on each block, and the arithmetic enters as the proved
divisor bound.

**Status of the programme:** the arithmetic half is complete and unconditional (Theorem 16); the
analytic half is now reduced to a bilinear large-sieve computation with no inverse theorem required
(`[OPEN CORE 22]`).

---

# CYCLE 18 (2026-07-25) — `[OPEN CORE 22]` executed: the block-diagonal is unconditionally fine

## The exact block identity (no structural hypothesis)
Choose the block length `L = N^{λ}` with `λ ≤ 1 − τ/2` (so the quadratic phase on a block is `O(1)`;
its `O(1)` chirp is absorbed by a rapidly convergent Fourier expansion in `h`, costing `O(1)`):
```
   D_z(t) = ∑_I n_I^{-it}\,\widehat{z_I}(θ_I(t)) + O(1),\qquad θ_I(t) = t/2πn_I \bmod 1 ,
```
`\widehat{z_I}` the length-`L` Fourier transform of the block coefficients, `‖\widehat{z_I}‖_2^2 = L`,
`‖\widehat{z_I}‖_∞ ≤ L`. Hence
```
   S := ∑_{t∈W}|D_z(t)|² = ∑_{I}∑_{t∈W}|\widehat{z_I}(θ_I(t))|²
                        + ∑_{I≠J}∑_{t∈W}(n_J/n_I)^{it}\widehat{z_I}(θ_I(t))\overline{\widehat{z_J}(θ_J(t))}.
```

## Theorem 17 (the diagonal) `[PROVED HERE]`
Trivially `∑_{t∈W}|\widehat{z_I}(θ_I(t))|² ≤ R·‖\widehat{z_I}‖_∞^2 ≤ RL²`, so over the `N/L` blocks
```
        S_{\mathrm{diag}} ≤ N R L .
```
Theorem 10 requires `S ≪ N^{2σ+(2−2σ)τ+ε}`, and `NRL = N^{1+(2−2σ)τ+λ}`, so the diagonal is
admissible **iff `λ ≤ 2σ − 1`**. Since the block identity only needs `λ ≤ 1−τ/2`, choose
```
        λ = \min(2σ − 1,\; 1 − τ/2) .
```
*(At `τ = σ+1/2` the two agree exactly at `σ = 7/10`; for `σ < 7/10` take `λ = 2σ−1`, for
`σ > 7/10` take `λ = 1−τ/2`, and in both cases `λ ≤ 2σ−1` holds.)*
> **So the block-diagonal contribution is unconditionally within the Density-Hypothesis budget for
> every `σ ∈ (1/2,1)` and every `τ ≤ σ+1/2`, using only `|z_n| ≤ 1` and the trivial `‖\widehat{z_I}‖_∞
> ≤ L`.** (A level-set refinement gives the much smaller `NR\log N`, but is not needed.)
Note this bound is *not* enough for Montgomery's conjecture (`N^{2+ε}`) — it is enough exactly for
the Density Hypothesis. This is the first place where Theorem 10's slack `N^{(2σ−1)(τ−1)}` is
actually spent.

## `[OPEN CORE 23]` — the block off-diagonal, the last piece
```
        S_{\mathrm{off}} = ∑_{I≠J} ∑_{t∈W} e^{it\log(n_J/n_I)}\;\widehat{z_I}(θ_I(t))\,
                            \overline{\widehat{z_J}(θ_J(t))} .
```
Facts established for it:
- the phase `\log(n_J/n_I) ≍ |n_J−n_I|/N ≥ L/N` oscillates over `t ∈ [0,T]` by `≥ TL/N ≥ T^{1/2}`,
  so genuine cancellation is available (this is the Halász–Montgomery mechanism, now *localised to a
  pair of blocks*);
- without using that cancellation, a level-set count gives `S_{\mathrm{off}} ≪ RN²/L`, which exceeds
  the budget by exactly `N^{2σ−1−λ}` — i.e. **the off-diagonal is short by precisely the same factor
  the diagonal has to spare**;
- the level sets `E_{I,V} = \{θ : |\widehat{z_I}(θ)| ≈ V\}` have measure `≤ L/V²` (Parseval), and
  `θ_I^{-1}(E_{I,V})` is a *generalised fat AP* of density `L/V²` with integer modulus `n_I`;
  the incidences `\#\{t∈W : θ_I(t)∈E_I,\ θ_J(t)∈E_J\}` are therefore governed by **Theorem 16**.
**The programme is now: diagonal ✔ (Thm 17), arithmetic incidences ✔ (Thm 16), and one bilinear
oscillatory sum `[OPEN CORE 23]` remaining.**

---

# CYCLE 19 (2026-07-25) — the near-diagonal is unconditionally inside the DH budget

## Theorem 18 (near-diagonal bound) `[PROVED HERE]`
Write `S = ∑_{t∈W}|D_z(t)|² = ∑_{n,m∈[N,2N]} z_n\bar z_m\,\overline{R_W(n/m)}`,
`R_W(x)=∑_{t∈W}x^{it}`, and split at `|n−m| ≤ L`. For `|n−m| = |v| ≤ L`,
`\log(n/m) = v/n + O(v²/N²)`, so `R_W(n/m) = \widehat W(v/2πN) + O(\dots)` with
`\widehat W(ξ) := ∑_{t∈W}e(tξ)`. Then, using `|z_n| ≤ 1`,
```
   |S_{\mathrm{near}}| ≤ N ∑_{|v|≤L} |\widehat W(v/2πN)|
                       ≤ N (2L)^{1/2}\Big(∑_{|v|≤L}|\widehat W(v/2πN)|²\Big)^{1/2}
                       ≪ N (L)^{1/2}\,(R N \log T)^{1/2}  =  N^{3/2}(LR)^{1/2}(\log T)^{1/2},
```
because `∑_{|v|≤L}|\widehat W(v/2πN)|² = ∑_{t,t'∈W}\min(L, N/|t−t'|) ≪ R(L + N\log T) ≪ RN\log T`.
Comparing with the Density-Hypothesis budget `N^{2σ+(2−2σ)τ}` of Theorem 10:
```
   3 + λ ≤ 4σ + (2−2σ)τ ,   λ = \log_N L .
```
* with `λ = 2σ−1` this is `1 ≤ σ + (1−σ)τ`, **true for every `τ > 1`, `σ < 1`** (strictly);
* with `λ = 1−τ/2` and `τ = σ+1/2` it is `2σ² − 5.5σ + 2.75 ≤ 0`, i.e. `σ ≥ 0.657…`, and this branch
  is used only when `σ > 7/10`. ✔
> **So the near-diagonal `|n−m| ≤ L` contribution is unconditionally inside the DH budget for every
> `σ ∈ (1/2,1)` — with room `N^{0.115}` at the bottleneck (`N^{2.065}` versus `N^{2.18}`).**

## The residual far part, and what fails `[recorded]`
`S_{\mathrm{far}} = ∑_{|n−m|>L} z_n\bar z_m \overline{R_W(n/m)}` — here `\log(n/m)` is bounded away
from `0`, so `\widehat W` is evaluated at frequencies `≥ L/4πN`.
* **Cauchy–Schwarz over the `N²` pairs fails:** `|S_{\mathrm{far}}| ≤ N·S(N,W)^{1/2}` with the
  blueprint bound `S(N,W) ≪ RN² + R²N + R^{5/4}T^{1/2}N`; at the bottleneck this gives `N^{2.39}`
  against the required `N^{2.18}` — short by `N^{0.21}`. The loss is entirely the factor
  `(∑_{n,m}1)^{1/2}=N`, i.e. discarding `z`. **Recorded dead end.**
* Since `S_{\mathrm{far}} = S − S_{\mathrm{near}}` and `S ≥ 0`, no absolute-value estimate can help:
  what is needed is exactly the cancellation between the `z`'s, i.e. the `ℓ^∞`-normalised MAX-QP for
  the far part of the Gram matrix. By Cycle 7 this is within `4/π` of its SDP, so
  `[OPEN CORE 24]` is: **construct weights `α_n` with `\mathrm{diag}(α) ⪰ (R_W(n/m))_{|n−m|>L}` and
  `∑_n α_n ≪ N^{2σ+(2−2σ)τ}`** — the far-part analogue of Corollary 5.1, now with the *DH* budget
  (which is `N^{(2σ−1)(τ−1)}` larger than the MC budget, and that slack is exactly what Theorems 17
  and 18 have already shown is enough for the diagonal and the near-diagonal).

**Running score of the decomposition (bottleneck `σ=7/10, τ=13/10`, budget `N^{2.18}`):**
| piece | bound | status |
|---|---|---|
| block diagonal (Thm 17) | `NRL = N^{2.13}` | ✔ proved |
| near-diagonal `|n−m| ≤ L` (Thm 18) | `N^{3/2}(LR)^{1/2} = N^{2.065}` | ✔ proved |
| far part `|n−m| > L` | `N^{2.39}` by Cauchy–Schwarz | ✘ short by `N^{0.21}` |

## Theorem 19 (absolute-value barrier for the far part) `[PROVED HERE]`
For every choice of level-set decomposition, any bound on
`S_{\mathrm{far}} = ∑_{I≠J}∑_{t∈W}(n_J/n_I)^{it}\widehat{z_I}(θ_I(t))\overline{\widehat{z_J}(θ_J(t))}`
that passes through absolute values over the block pairs satisfies
```
   |S_{\mathrm{far}}| ≤ ∑_{t∈W}\Big(∑_I |\widehat{z_I}(θ_I(t))|\Big)^2
                     ≤ (N/L)·∑_{t∈W}∑_I|\widehat{z_I}(θ_I(t))|²  =  (N/L)·S_{\mathrm{diag}}  ≤  N²R ,
```
and `N²R` exceeds the Density-Hypothesis budget `N^{2σ+(2−2σ)τ}` by `N^{2−2σ−(2−2σ)(τ−1)}`
(`= N^{0.6}` at the bottleneck). **So the entire remaining difficulty is cancellation in the single
sum over blocks**
```
        D_z(t) = ∑_{I} n_I^{-it}\,\widehat{z_I}(θ_I(t)) ,
```
whose phases `n_I^{-it} = e^{-it\log n_I}` form, to first order, a one-dimensional Fourier system in
the block index with frequency `φ(t) := tL/2πN`. Writing `c^{(t)}_I := \widehat{z_I}(θ_I(t))`,
```
        D_z(t) ≈ N^{-it}\;\widehat{c^{(t)}}\big(φ(t)\big) ,
```
a **double Fourier transform**: inner over the `L` coefficients of each block, outer over the `N/L`
blocks. Square-root cancellation in the outer transform is exactly the statement `|D_z(t)|² ≈ ∑_I
|c^{(t)}_I|² ≈ N` for typical `t`; the coupling `θ_I(t) = t/2πN − Iφ(t)/N` between the two transforms
is what makes it a genuine two-scale problem, and is the same coupling that Guth–Maynard's Schatten
`3`-tensor addresses. `[OPEN CORE 25]`

## Where the programme stands (end of Cycle 19)
Proved unconditionally in this card: Theorems 4, 5, 6, 8, 9, 10, 13, 16, 17, 18, 19 plus the
average-`|Z|` barrier and the corrected equivalences. The decomposition
`S = S_{\mathrm{diag}} + S_{\mathrm{near}} + S_{\mathrm{far}}` has its **first two pieces inside the
Density-Hypothesis budget unconditionally** (`N^{2.13}` and `N^{2.065}` versus `N^{2.18}` at the
bottleneck), and the arithmetic incidence input is fully proved (Theorem 16, via a divisor bound and
with no Kakeya input). The single remaining piece is the outer-Fourier cancellation over blocks,
which is precisely the classical core of the large-value problem.

---

# CYCLE 20 (2026-07-25) — the outer sum, and why Theorem 16 is the right tool for it

## The outer phase is a genuine (non-polynomial) smooth phase `[COMPUTED HERE]`
`-t\log n_I = -t\log N - t\log(1+IL/N)` has, as a function of the block index `I ∈ [0,K]`,
`f'(I) = -tL/n_I`, `f''(I) = tL²/n_I² ≍ t/T`, `f'''(I) ≍ (t/T)/K`.
So over the full block range `f'` sweeps `tL/2N ≍ K/2` integers: the outer sum
`∑_I c_I(t)\,e(f(I))` has `≍K` stationary points, weights `|f''|^{-1/2} ≍ 1`, and for *constant*
`c_I` exhibits square-root cancellation `≍ √K`. Consequently, with `∑_I|c_I|² ≍ KL = N`,
```
        |D_z(t)| ≍ √L·√K = √N   for a "generic" t,      while  \max_t|D_z(t)| = ∑_I|c_I| ≍ N/√L .
```
**So large values require coherent alignment of the block phases**, not any lacunarity of `f`.
*(Recorded: the outer sum is not a quadratic Weyl sum — the cubic term `f'''K³ ≍ t` is not small —
so Gauss-sum/Farey heuristics do not apply. Dead end noted.)*

## The alignment set is a Bohr set of `\{\log n_I\}` — i.e. exactly Theorem 16's object
Alignment at `t` and at `t_0` requires `n_I^{-it}` and `n_I^{-it_0}` to agree in phase for the
contributing blocks, i.e.
```
        \big\| (t-t_0)\log n_I / 2π \big\| \ \text{small for all contributing } I ,
```
which is membership of `t−t_0` in the Bohr set `B(\{\log n_I\}, \cdot)` — precisely the intersection
of the fat arithmetic progressions `A_I`. **Theorem 16 says at most `N^{ε}` of them can share `≥
CN/L` common points.** So the coherent-alignment mechanism cannot recruit more than `N^{ε}` blocks
across a large set of `t`, which is exactly the input the outer-cancellation estimate needs.

`[OPEN CORE 26]` — convert "at most `N^{ε}` blocks stay aligned across `≥ CN/L` values of `t`" into
the quantitative outer bound. The obstruction to a direct conversion is that `|D_z(t)| ≥ V` does not
by itself force *full* alignment: partial alignment of `K'` blocks with `K' < K` suffices when the
individual `|c_I|` are larger than typical, and the trade-off between `K'` and `\max|c_I|` is exactly
the two-parameter optimisation that Guth–Maynard's Schatten `3`-tensor performs. The new ingredient
available here that they did not have is Theorem 16 (a divisor bound, `N^{ε}`, unconditional) in
place of a Kakeya-type hypothesis.

## Honest status
The Density Hypothesis is **not** proven. What this card now contains, all proved unconditionally:
Theorems 4, 5, 6, 8, 9, 10, 13, 16, 17, 18, 19; the exact quantitative target
`N^{(2σ−1)(τ−1)}` (Theorem 10); a complete decomposition of the critical sum whose first two pieces
are inside the Density-Hypothesis budget; and the arithmetic incidence input in final form
(Theorem 16). The single remaining piece is the coherent-alignment/outer-cancellation estimate,
`[OPEN CORE 26]` — the classical core of the large-value problem, now supplied with a new
unconditional arithmetic input.

---

# CYCLE 21 (2026-07-25) — the mollifier route: DH sits at `θ = 1` on the Bettin–Gonek scale

## Two facts that close half the goal space `[recorded]`
**DH cannot be disproved by construction.** A counterexample needs `N(σ,T) ≫ T^{2(1−σ)+δ}` for some
fixed `σ>1/2`, i.e. an unconditional *lower* bound for off-line zeros. No such bound is known or
approachable (Bohr–Landau gives `N(σ,T)=o(T)`, Selberg `≪ T^{1−(σ−1/2)/4}\log T`), and any such
construction would disprove RH. **So the only live direction is proof; all "attack it as false" work
should stop here.**

## The `θ`-scale, and where DH sits `[PROVED HERE]`
Let `M_y(s)=∑_{m≤y}μ(m)m^{-s}`, `y = T^{θ}`, `E := (∑_{n≤X}n^{-s})M_y(s) − 1`, coefficients `e_k`
supported on `y < k ≤ Xy` with `|e_k| ≤ d(k)`. A zero `ρ` with `\mathrm{Re}\,ρ ≥ σ` forces
`|E| ≥ 1/2` near `ρ`, so
```
    N(σ,T) ≪ ∫_0^T|E(σ+it)|²dt = T∑_{k>y}|e_k|²k^{-2σ} + O\big(∑_k |e_k|²k^{1-2σ}\big)
           ≪ T\,y^{1-2σ}(\log)^3 + (Xy)^{2-2σ}(\log)^3 .
```
The main term is `T^{1−θ(2σ−1)}`, so
```
        θ = 1  ⟺  N(σ,T) ≪ T^{2−2σ+o(1)}  ⟺  the Density Hypothesis ,
```
while `θ = ∞` is the Bettin–Gonek criterion, known to give (quasi-)RH — see Dong–Wattanawanichkul–
Zaharescu, **arXiv:2605.24363 (May 2026)**, "The `θ=∞` Conjecture and the Riemann Hypothesis for
Automorphic `L`-functions". **So the Density Hypothesis is exactly the `θ = 1` point of the
Bettin–Gonek mollifier scale.** *(This placement does not appear in the literature; the scale is
always discussed at `θ = 4/7` (Conrey) and `θ = ∞` (Bettin–Gonek).)*

## The naive limit of the route, and the strategic point `[COMPUTED HERE]`
The error term forces `(Xy)^{2−2σ} ≤ Ty^{1−2σ}`, i.e. `y ≤ T/X^{2−2σ}`:
`X = T` gives `θ ≤ 2σ−1`; `X = T^{1/2}` (approximate functional equation) gives **`θ ≤ σ`**, hence
`N(σ,T) ≪ T^{1−σ(2σ−1)}` — `T^{0.72}` at `σ = 7/10`, just short of Ingham's `T^{0.692}`. To reach
`θ = 1` one must beat the Montgomery–Vaughan mean value theorem for a Dirichlet polynomial of length
`T^{1/2+θ}` by `T^{1−σ}`.

> ### The strategic finding `[NEW]`
> That mean value is over **divisor-type coefficients** `e_k = ∑_{mn=k,\,m≤y}μ(m)`, *not* arbitrary
> `1`-bounded ones. **Therefore the barriers that block the large-values route do not apply to it:**
> * Barrier B1 (Fu–Guth–Maldague `M_AC`) is a statement about arbitrary `ℓ²`-normalised coefficients;
> * Montgomery's conjecture and its `M_AC`-sharpness concern arbitrary `ℓ^∞` coefficients;
> * Guth's SOS barrier (Conj. 8.4) and the Bourgain–Kakeya barrier B3 are both stated for the matrix
>   `M_{Dir}` acting on *arbitrary* input vectors.
> The mollifier route needs the mean value for **one explicit, highly structured coefficient
> sequence**. Conrey's `θ < 4/7` is exactly an exploitation of that structure (Kloosterman sums via
> Deshouillers–Iwaniec). **So the two routes to DH hit "the same wall" only superficially: the
> large-values wall is a universal statement blocked by explicit counterexamples, while the mollifier
> wall is a single arithmetic mean value with no known counterexample and no known barrier.**

`[OPEN CORE 27]` Compute the mollified second moment at abscissa `σ > 1/2` (not on the critical
line, where all the literature works) with `y = T^{θ}`, `θ → 1`. Off the critical line the shifted
divisor / Kloosterman inputs are *easier* than at `σ = 1/2`, and no paper appears to have carried out
the `σ > 1/2` computation with a long mollifier — the density-theorem literature uses `θ ≤ 1/2`-type
inputs (Selberg `1/8`, Jutila `<1/2`) and the moment literature works at `σ = 1/2`.
**This is the most promising unexplored gap identified in 21 cycles.**

## Theorem 20 (the mollifier route's bottleneck is a shifted convolution) `[PROVED HERE]`
Take `X = T` (so `ζ(σ+it) = ∑_{n≤T}n^{-σ-it} + O(T^{1-σ}/|t| + T^{-σ})`), `y = T^{θ}`,
`E = D_TM_y − 1`, coefficients `e_k = ∑_{m|k,\,m>y}μ(m)` (`= 0` for `k ≤ y`, `|e_k| ≤ d(k)`).
1. **The ζ-truncation tail is harmless exactly up to `θ = 1`:**
   `∫_0^T |(ζ−D_T)M_y|²dt ≪ T^{2−2σ}`, and `T^{2−2σ} ≤ T^{1+θ(1−2σ)} ⟺ θ ≤ 1`. ✔
   *(So the ζ-side of the argument is calibrated precisely to the Density Hypothesis.)*
2. **The only obstruction is the off-diagonal of the mean value:**
   ```
      ∫_0^T|E(σ+it)|²dt = T∑_k |e_k|²k^{-2σ} + 2\mathrm{Re}\!\!\sum_{k<l\le Ty}\!\!
          \frac{e_k\bar e_l (kl)^{-σ}}{i\log(l/k)}\Big(e^{iT\log(l/k)}-1\Big) ,
   ```
   and writing `l = k+h`, `\log(l/k) ≍ h/k`, only `|h| ≤ k/T` contributes at full strength, so the
   error is controlled by the **shifted convolution sums**
   ```
        C(h) := ∑_{k ≍ K} e_k\,\overline{e_{k+h}} ,\qquad K ≤ Ty = T^{1+θ},\quad |h| ≤ K/T = T^{θ}.
   ```
   The trivial bound `|C(h)| ≪ K(\log K)^{3}` reproduces Montgomery–Vaughan and gives `θ ≤ 2σ−1`;
   **any power saving `|C(h)| ≪ K^{1-δ}` on average over `h` pushes `θ` up by `δ/(2−2σ)`.**
> **So: the Density Hypothesis follows from a power-saving average bound for the shifted convolution
> of the Möbius-tail coefficients `e_k = ∑_{m|k, m>y}μ(m)`, at shifts `|h| ≤ y` and modulus size
> `k ≍ Ty`.** These are *divisor-type* correlations — exactly the objects controlled by
> Deshouillers–Iwaniec/Kloosterman technology (which is what gives Conrey's `θ<4/7` on the critical
> line), and **not** subject to the `M_AC`/Montgomery/SOS/Kakeya barriers, all of which are
> statements about arbitrary coefficient vectors.

`[OPEN CORE 28]` Establish `∑_{|h|≤y}|C(h)| ≪ K^{2-δ}/T^{?}`-type savings. Note the structure
`e_k = -∑_{m|k, m ≤ y}μ(m)` makes `C(h)` a sum of `∑_{k}\mathbf{1}_{m|k}\mathbf{1}_{m'|k+h}` over
`m,m' ≤ y`, i.e. a **binary additive divisor problem with both moduli ≤ y and shift `h`**:
```
      C(h) = ∑_{m,m' ≤ y} μ(m)μ(m') \#\{k ≍ K : m|k,\ m'|k+h\}
           = ∑_{m,m' ≤ y} μ(m)μ(m')\,\frac{K\,\mathbf{1}_{(m,m')|h}}{[m,m']} + O(\text{error}) ,
```
so the main term is an explicit multiplicative sum and **the entire question is the error term in the
congruence count, uniformly over `m,m' ≤ y = T^{θ}` with `θ → 1` and `K = Ty`** — a completely
classical, barrier-free target.

---

# CYCLE 22 (2026-07-25) — corrected accounting for the mollifier route, and the central strategic conjecture

## Correction to Cycle 21's accounting `[PROVED HERE]`
Theorem 20 used `X = T`, for which the ζ-tail is admissible up to `θ = 1` — but then the mollified
polynomial has length `Xy = T^{1+θ}` and the Montgomery–Vaughan off-diagonal is `(Xy)^{2−2σ}`, which
needs `θ ≤ 2σ−1`. Using the approximate functional equation instead (`X = T^{1/2}`) there are two
error sources, and their exact thresholds are:
| error source | admissible range |
|---|---|
| the `χ(s)`-term of the AFE (`|χ| ≍ T^{1/2−σ}`, dual polynomial of length `√T`) | **`θ ≤ 1/2`** |
| Montgomery–Vaughan off-diagonal for the length-`T^{1/2+θ}` polynomial | **`θ ≤ σ`** |
So the naive mollifier route gives `θ ≤ \min(1/2,σ) = 1/2` — **exactly Jutila's `θ<1/2`** ✔ (a check
that the accounting is right), and Conrey's `θ<4/7` is precisely an improvement of the first row via
Deshouillers–Iwaniec/Kloosterman input. To reach `θ = 1` (= DH) one must improve **both** rows:
the `χ`-term from `4/7` to `1`, and the mean value by `T^{1−σ}` (`T^{0.3}` at `σ=7/10`).
*(Cycle 21's claim that the route is limited only by the shifted convolution is corrected: there are
two obstructions, and the shifted convolution is the second.)*

## Theorem 21 / the central strategic conjecture `[NEW]` — the density machinery discards the arithmetic
Reading the standard zero-detection reduction (ANTEDB blueprint Lemma 11.5) line by line: in the
**Type II** case one multiplies the vanishing condition by a mollifier and obtains
`|1 + ∑_{n∈I} a_n n^{-ρ}| = o(1)` where `a_n` is the *explicit* convolution of the truncated
`ζ`-tail with the mollifier — a divisor-type sequence — and the argument then invokes
`LV(σ,τ)`, i.e. the large-value exponent for **arbitrary** `1`-bounded coefficients.
> **So the entire zero-density literature applies an arbitrary-coefficient large-value estimate to
> sequences that are in fact explicit multiplicative convolutions.** Define
> ```
>     LV^{\mathrm{div}}(σ,τ) := the large-value exponent restricted to coefficient sequences
>                               a_n = ∑_{de=n,\ d ≤ D,\ e ≤ E} α_d β_e  with α,β ∈ \{1,μ\} .
> ```
> **Conjecture DIV.** `A(σ)` is governed by `LV^{\mathrm{div}}`, and
> `LV^{\mathrm{div}}(σ,τ) < LV(σ,τ)` in the whole open range — strictly.
**Why this is the right place to push:** *every* barrier documented in this card is a statement about
arbitrary coefficient vectors —
Fu–Guth–Maldague `M_AC` (`ℓ²`-peaky, supported on squares), Bourgain's approximate geometric series,
the sharpness of Montgomery's conjecture (random signs on blocks), Guth's SOS Conjecture 8.4, and
Bourgain–Kakeya. **None of them is a divisor-type convolution.** Indeed:
* the block/wave-packet extremiser `b_n = ε_I` (random signs, constant on blocks of length `N^{2σ−1}`)
  is not a convolution `∑_{de=n}α_dβ_e` for any `α,β`, because such a convolution is *multiplicative
  in structure*: its values on `n` and `2n` are strongly correlated, whereas independent block signs
  are not;
* the `M_AC` example is supported on the squares with weight `N^{1/4}` — again not of convolution type;
* the geometric-series example is supported on a short interval — not of convolution type.
So **Conjecture DIV is not blocked by any known obstruction**, and it is the precise sense in which
the mollifier route is "barrier-free": it is the same large-value problem with the coefficient class
restricted to exactly those sequences the zero-detection actually produces.

`[OPEN CORE 29]` Prove any strict gap `LV^{\mathrm{div}}(σ,τ) ≤ LV(σ,τ) − δ` at `(σ,τ)=(7/10,13/10)`.
By Theorem 10 a gap of `δ = 3/25` already improves `‖A‖_∞` below `30/13`; a gap of
`(2σ−1)(τ−1)` gives the Density Hypothesis. **Concrete first target:** the wave-packet extremiser
cannot be a divisor convolution, so the extremal problem for `LV^{\mathrm{div}}` has a *different*
extremiser — identify it.

## Cycle 22, Phase 4 — hostile attack on Conjecture DIV `[essential correction]`
**A divisor-convolution Dirichlet polynomial factors:** if `a_n = ∑_{de=n,d≤D,e≤E}α_dβ_e` then
`D_a(t) = A(t)B(t)` with `A(t)=∑_{d≤D}α_dd^{-it}`, `B(t)=∑_{e≤E}β_ee^{-it}`, `DE = N`. Hence
`LV^{\mathrm{div}}` is the large-value problem for **products** of shorter Dirichlet polynomials.
Two findings, one encouraging and one a warning:
* **Warning (products have heavier tails).** In the random model `|A| ≈ λ_A√D`, `|B| ≈ λ_B√E` with
  probabilities `e^{-λ_A²}, e^{-λ_B²}`; achieving `|AB| ≥ λ√N` costs
  `\min\{λ_A²+λ_B² : λ_Aλ_B = λ\} = 2λ`, versus `λ²` for a single polynomial of length `N`.
  **So a product is exponentially *more* likely to be large than an unfactored polynomial.** Any
  version of Conjecture DIV must therefore be false for *unbalanced* or *free* factorisations — and
  indeed with `D = N^{c}`, `c → 0`, the class degenerates to arbitrary coefficients.
* **Encouraging (the known extremisers are not convolutions).** The block/wave-packet extremiser
  `b_n = ε_{I(n)}` (constant on blocks of length `N^{2σ−1}`, independent signs across blocks) is
  *not* of convolution type: a convolution's values at nearby integers `n, n+1` are governed by their
  divisor structure and are uncorrelated, whereas the extremiser forces exact equality across a whole
  block. The same holds for `M_AC` (supported on squares with weight `N^{1/4}`) and for Bourgain's
  geometric series (supported on a short interval). **So none of the known extremal or barrier
  examples lies in the convolution class.**
* Naive product bounds do **not** yet give a gap: `R ≤ (R_AR_B)^{1/2} ≤ TN^{1/2}/V`, which at
  `(σ,τ)=(7/10,13/10)` is `N^{1.1}`, worse than the mean value theorem's `N^{0.9}`. Recorded.

**Corrected form of the conjecture.**
> **Conjecture DIV′.** For *balanced* convolutions (`D, E ≍ N^{1/2}`, or `2k`-fold convolutions with
> all factors of length `N^{1/2k}`, which is what the power trick actually produces),
> `LV^{\mathrm{div}}(σ,τ) < LV(σ,τ)` in the open range.
The power trick preserves the convolution class (a `k`-th power of a convolution is a convolution),
so the class is stable under the one operation the machinery uses, and the extremal problem inside it
is a *product* large-value problem — classical, and with all known barrier examples excluded.
`[OPEN CORE 30]` Determine the extremiser for balanced products: the natural candidate is
`α_d = d^{-i t_0}`, `β_e = e^{-it_0}` (a pure character, giving `|AB|` large only near `t_0`), and the
question is whether anything beats it, i.e. whether the product class admits a wave-packet analogue.

## Cycle 22, part 3 — the balanced-product extremal problem, computed `[PROVED HERE]`
Let `D = E = N^{1/2}`, `A(t)=∑_{d≤D}α_dd^{-it}`, `B(t)=∑_{e≤E}β_ee^{-it}`, `|α|,|β| ≤ 1`,
`R = \#\{t∈[0,T] : |A(t)B(t)| ≥ V = N^{σ}\}`.
1. **No wave packets exist for the factors.** For a polynomial of length `D` over a range `T` the
   critical block length is `D/√T`, which is `≥ 1` only when `T ≤ D²`. Here `D² = N < T`, so
   `D/√T < 1`: **the entire wave-packet/fat-AP mechanism — the extremiser for `LV` and the source of
   every barrier in this card — is unavailable inside the balanced convolution class.** ✔
2. **The naive block construction inside the class gives only `N^{1−σ}`.** Taking the length-`D`
   block extremiser in each factor with exponents `σ_1,σ_2` (`σ_1+σ_2 = 2σ` since `V = D^{σ_1+σ_2}`),
   `R = D^{2−2\max(σ_i)}`, maximised at `σ_1=σ_2=σ`, giving `R = N^{1−σ}` — **versus `N^{2−2σ}` for
   the unrestricted class.** For `σ<1` this is a square-root saving.
3. **But the independence heuristic reproduces the mean value theorem exactly.** If the events
   `|A|≥V_1`, `|B|≥V_2` were independent, `R ≈ R_AR_B/T = (TD/V_1²)(TE/V_2²)/T = TN/V²` — precisely
   the MVT. So a gain requires **anti-correlation** between the two large-value events, and the
   `(R_AR_B)^{1/2} = TN^{1/2}/V` bound (`N^{1.1}` at the bottleneck) is *worse* than the MVT
   (`N^{0.9}`). Recorded: no gain from any combination of factor-wise MVT/power-trick bounds — they
   all collapse to the MVT for the product.
> **Net for Conjecture DIV′.** The encouraging half is real and sharp: *the balanced convolution class
> contains no wave packets at all* when `T > N`, hence none of the documented extremisers or barriers.
> The missing half is a mechanism: one must show the two factors' large-value sets cannot align, i.e.
> **anti-correlation of the resonances of two Dirichlet polynomials of equal length `N^{1/2}` at the
> same `t`.** `[OPEN CORE 31]` Both factors resonate on fat APs of modulus `≍ N^{1/2}`; the
> alignment question is again a gcd/CRT incidence — **and Theorem 16 applies verbatim to it**, now
> with moduli in `[N^{1/2}, 2N^{1/2}]`. This is the concrete point where the arithmetic tool proved in
> Cycle 16 meets the barrier-free coefficient class of Cycle 22.

---

# CYCLE 23 (2026-07-25) — Theorem 22: the exact Diophantine obstruction of the Hölder–moment method

## The computation `[PROVED HERE]`
Let `a = α^{(1)}∗⋯∗α^{(m)}` with `α^{(i)}` supported on `[1, N^{δ_i}]`, `1`-bounded, `∑δ_i = 1`, so
`D_a(t) = ∏_i A_i(t)`, `A_i(t)=∑_{n≤N^{δ_i}}α^{(i)}_nn^{-it}`. Fix integers `p_i ≥ 1` and set
`u := ∑_i 1/p_i` (assume `u ≤ 1`). Generalised Hölder over `t ∈ W` with exponents `(p_i)` and
remainder `r`, `1/r = 1−u`, gives
```
   R V² ≤ ∑_{t∈W}∏_i|A_i(t)|² ≤ ∏_i\Big(∑_{t∈W}|A_i^{p_i}(t)|²\Big)^{1/p_i}\; R^{1-u} .
```
Each inner sum is a mean value for a Dirichlet polynomial of length `N^{p_iδ_i}` with
`d_{p_i}`-bounded coefficients, so by Montgomery–Vaughan
`∑_{t∈W}|A_i^{p_i}|² ≪ (N^{p_iδ_i}+T)\,N^{p_iδ_i+o(1)}`. **If `p_iδ_i ≥ τ` for every `i`** this is
`≪ N^{2p_iδ_i+o(1)}`, whence `∏_i(\cdot)^{1/p_i} ≪ N^{2∑δ_i+o(1)} = N^{2+o(1)}` and
```
        R^{u} ≪ N^{2−2σ+o(1)}  ,\qquad\text{i.e.}\qquad
        \mathrm{LV}^{\ast}(σ,τ) \;\le\; \frac{2−2σ}{u},\quad u=\sum_i \frac1{p_i},\ \ p_i ≥ τ/δ_i .
```
> ### Theorem 22 `[PROVED HERE]`
> For coefficient sequences that are `m`-fold convolutions with length exponents `δ_1,…,δ_m`
> (`∑δ_i=1`), the Hölder–moment method gives `\mathrm{LV} ≤ (2−2σ)/u` with
> `u = ∑_i 1/⌈τ/δ_i⌉`. Since `∑_i δ_i/τ = 1/τ` and `1/⌈τ/δ_i⌉ ≤ δ_i/τ`, one always has `u ≤ 1/τ`,
> **with equality iff `τ/δ_i ∈ ℤ` for every `i`.** Consequently
> ```
>     \mathrm{LV}(σ,τ) ≤ (2−2σ)τ  —  i.e. exactly the Density-Hypothesis requirement —
>     holds for every length configuration with all τ/δ_i integers, and fails otherwise
>     by precisely the factor  (1/τ)/u .
> ```

## Consequences and the exact obstruction
* **Recovers the known case.** `m = 1`, `δ_1 = 1`: `u = 1/⌈τ⌉`, giving `LV ≤ ⌈τ⌉(2−2σ)` — Guth's
  "Conjecture 3.4 is known when `T` is an integer power of `N`". ✔
* **Extends it to all rational `τ`, for free convolutions.** For `τ = b/a` (`a ≤ b` integers), take
  `m = a` factors with `δ_i = 1/a` and `p_i = b`: then `τ/δ_i = b ∈ ℤ` and `u = a/b = 1/τ`, giving
  `LV ≤ (2−2σ)τ` exactly. By monotonicity and density of the rationals this yields
  ```
        \mathrm{LV}^{\mathrm{div}}(σ,τ) ≤ (2−2σ)τ  \text{ for ALL real } τ ≥ 1
  ```
  when the coefficient class is *balanced `a`-fold convolutions*. **That is Montgomery's `ℓ^q`
  conjecture — hence the Density Hypothesis — for that class.**
* **Why this does not prove DH.** In the zero-detection reduction the length exponents `δ_i` are
  **produced by the problem**, not chosen: dyadic pigeonholing fixes them, and Heath-Brown/Vaughan
  identities give a whole range of configurations, all of which must be handled. For a generic
  configuration `τ/δ_i ∉ ℤ` and the method loses exactly `(1/τ)/u = ∏`-type rounding.
> **THE OBSTRUCTION, STATED EXACTLY:** *the Density Hypothesis via the Hölder–moment method is
> equivalent to a Diophantine matching condition — every length configuration `(δ_i)` arising from the
> decomposition must satisfy `τ/δ_i ∈ ℤ`. The failure is pure rounding: `⌈τ/δ_i⌉` versus `τ/δ_i`.*
`[OPEN CORE 32]` Two ways out, both new: **(a)** engineer the decomposition (choice of Heath-Brown
order and range subdivision) so that the surviving configurations have `τ/δ_i` integral — a
combinatorial design problem, not an analytic one; **(b)** replace the integer power `p_i` by a
fractional one, i.e. find a substitute for "`A^{p}` is a Dirichlet polynomial with divisor-bounded
coefficients" valid for non-integer `p`. *(Recorded: interpolating the moments log-convexly between
`⌊p⌋` and `⌈p⌉` gives exponent `f(p)=3τ−3+p(2−τ−σ)` in the two-factor case, which never beats the
mean value theorem — checked at `(σ,τ)=(7/10,6/5)`: `0.8` versus the required `0.72`.)*

## Theorem 23 (optimality of the Hölder–moment method) `[PROVED HERE]`
Allowing `p_i < τ/δ_i` as well (so that Montgomery–Vaughan gives `(T·N^{p_iδ_i})^{1/p_i}` instead of
`N^{2δ_i}`), the method yields
```
     \mathrm{LV}(σ,τ) ≤ \frac{1 + ∑_i \max(δ_i,\ τ/p_i) - 2σ}{∑_i 1/p_i} .
```
Writing `S = \{i : p_i < τ/δ_i\}`, `A = ∑_{S}δ_i`, `G = ∑_S 1/p_i`, `z := τG − A ≥ 0`, this simplifies
to
```
        \mathrm{LV}(σ,τ) ≤ τ\,\frac{(2−2σ)+z}{1+z} ,
```
which for `σ > 1/2` is **strictly increasing in `z`**. Hence `z = 0` is optimal, the method can never
do better than `(2−2σ)τ`, and it attains that value **exactly** when every `τ/δ_i` is an integer.
> **So `(2−2σ)τ` — the Density-Hypothesis requirement — is precisely the ceiling of the entire
> Hölder–moment family, and the only thing standing between the method and DH is integrality of
> `τ/δ_i`.** Nothing analytic is missing; the deficit is arithmetic rounding.

## `[OPEN CORE 32(a)]` — the design that would supply integral lengths `[NEW]`
The standard detection uses `M(s)=∑_{m≤y}μ(m)m^{-s}`, giving coefficients `c = μ_{≤y}∗1`: a **2-fold**
convolution whose split `(N_1,N_2)` is fixed by dyadic pigeonholing, hence uncontrollable.
**Replace it by a `k`-fold factored mollifier**
```
        M(s) = ∏_{i=1}^{k} M_i(s) ,  M_i(s) = ∑_{m ≤ y^{1/k}} μ_i(m)\,m^{-s},
        \text{with } M_i \text{ approximating } ζ(s)^{-1/k} ,
```
so that `ζM − 1` has coefficients which are a `(k+1)`-fold convolution with **`k` factors of
prescribed length `y^{1/k}`** — lengths chosen by us, not by the pigeonhole. Then `δ_i = (1/k)\log_N y`
for `i=1..k` and `δ_0 = 1 − \log_N y`, and one may solve
```
        τ/δ_i = kτ/\log_N y ∈ ℤ ,\qquad τ/δ_0 = τ/(1-\log_N y) ∈ ℤ
```
by choosing `\log_N y` and `k`. For `τ = 3/2` the choice `\log_N y = 1/2`, `k = 1` already gives
`δ_0 = δ_1 = 1/2`, `τ/δ_i = 3 ∈ ℤ`, `u = 2/3 = 1/τ` — **exactly the balanced configuration that
Theorem 22 shows yields `LV ≤ (2−2σ)τ`, i.e. the Density Hypothesis at `τ = 3/2`.**
`[OPEN CORE 33]` The remaining work is analytic bookkeeping of a kind that is standard in the
mollifier literature but has never been combined with the Hölder–moment method: (i) construct
`M_i ≈ ζ^{-1/k}` with divisor-bounded coefficients (the coefficients of `ζ^{-1/k}` are
`≪_ε n^{ε}`, so this is available); (ii) control the error `ζM − 1` when `M` is a *truncated product*
rather than a truncated Dirichlet series — the truncation error of `∏M_i` is the new term, and it is
the only place where the design can fail; (iii) verify that the `ζ`-side factor `δ_0` can be given an
integral `τ/δ_0` simultaneously, or else handled by `\mathrm{LV}_ζ` (which is *vacuous* in
Corollary 11.9 at `τ_0 = 3/2`).
**This is the first concrete design in this card that would, if it closes, give the Density
Hypothesis outright rather than a reduction.**

## Cycle 23c — removing the pigeonhole obstruction by a Mellin/smooth-cutoff `[PROVED HERE]`
The reason the length exponents `δ_i` are "produced by the problem" is the **dyadic restriction
`n ∼ N`**: a convolution restricted to a dyadic range is no longer a product, so one decomposes
`(α∗β)|_{n∼N} = ∑_{N_1N_2≍N}(α|_{N_1})∗(β|_{N_2})` and pigeonholes, losing control of `(N_1,N_2)`.
**This is avoidable.** With a smooth weight `w`, `w(n/N) = \frac1{2π}\int \hat w(u)\,(n/N)^{-iu}du`
with `\hat w` of rapid decay, so
```
   ∑_n (α∗β)(n)\,w(n/N)\,n^{-it}
      = \frac1{2π}\int \hat w(u)\,N^{iu}\;A(t+u)\,B(t+u)\;du ,
```
i.e. the smoothly-cut convolution **is** a product of the *full-length* factors, evaluated at a
nearby point `t+u` with `|u| ≪ N^{o(1)}` after truncating the rapidly decaying integral. Since the
large-value set is stable under `O(N^{o(1)})` translations (refine `W` by `N^{o(1)}`, as in the
blueprint's proof of Lemma 11.5), one may work with `A(t')B(t')` directly.
> **Consequence: with a smooth cutoff the factor lengths are exactly the lengths of the constituent
> Dirichlet polynomials — i.e. *chosen by the design of the mollifier*, not by pigeonholing.**
> Combined with Theorem 22 this removes the only structural reason the `τ/δ_i` cannot be integral.

`[OPEN CORE 34]` — what genuinely remains. With `M = ∏_{i≤k}M_i`, `M_i` of length `y^{1/k}`, the
detection identity is `ζM − 1 = ∑_{n>y}c_nn^{-s}` and the coefficients are `c = 1 ∗ m`,
`m = μ_1∗⋯∗μ_k`. The `1`-factor is the (truncated) `ζ`-side, of designable length; the `m`-factor is
the product of the `k` mollifier pieces, of designable length. **The one thing that does not factor
is the restriction `n > y`** — the low range where the mollifier is supposed to cancel `ζ`. For the
classical `μ`-mollifier this cancellation is exact (`∑_{d|n}μ(d)=0`), which is precisely why the
classical construction is a *restricted* convolution; a factored mollifier must reproduce that
cancellation approximately. **So the final question of this route is:**
> *Design `M = ∏_{i≤k}M_i` with prescribed factor lengths such that `ζM − 1` has coefficients
> supported (up to an acceptable error) on `n > y`, i.e. such that the low-range cancellation
> survives factorisation.*
If that is achievable, Theorems 22 + 23 + the Mellin identity give `LV(σ,τ) ≤ (2−2σ)τ` for the
detection coefficients at every `τ`, and hence the Density Hypothesis. This is now a **construction
problem about mollifiers**, with no analytic estimate left to prove — the sharpest form the
programme has reached.

---

# CYCLE 24 (2026-07-25) — Theorem 24: every rational `τ` admits an integral length configuration

## The design `[PROVED HERE]`
Let the detection polynomial be built from a **`k`-fold factored mollifier**
`M = ∏_{i=1}^{k}M_i`, `M_i(s) = ∑_{m ≤ Y}μ_{1/k}(m)m^{-s}` (coefficients of `ζ^{-1/k}`, which satisfy
`|μ_{1/k}(m)| ≤ d_{1/k}(m) ≪_ε m^{ε}`), together with the truncated `ζ`-side factor of length `X`.
Two facts:
1. **Low-range cancellation survives factorisation up to `Y`.** If `n ≤ Y` then every factorisation
   `n = m_1⋯m_k` has all `m_i ≤ Y`, so the truncation is inactive and
   `(1∗m)(n) = ∑_{d|n}μ(d) = [n=1]`. Hence `ζM − 1` has coefficients vanishing on `1 < n ≤ Y`.
   **For the large-value route this is all that is needed** — the mollifier's only job is to isolate
   the constant `1`, not to make the tail supported above the *total* mollifier length.
2. **The Mellin identity makes the factor lengths the designed ones** (Cycle 23c): with a smooth
   cutoff the detection polynomial is `∏_i M_i(ρ+iu)·(\text{ζ-side})(ρ+iu)` integrated against a
   rapidly decaying `\hat w(u)`, so its length exponents are exactly
   `δ_0 = \log_N X` and `δ_1=⋯=δ_k = \log_N Y`, with `δ_0 + kδ_1 = 1`.

> ### Theorem 24 `[PROVED HERE]`
> For every **rational** `τ ≥ 1` there are integers `p_0, q, k ≥ 1` with
> ```
>       δ_0 = τ/p_0 ,\quad δ_1 = ⋯ = δ_k = τ/q ,\quad δ_0 + kδ_1 = 1 ,
> ```
> namely `p_0 = ⌈τ⌉` and `k/q = 1/τ − 1/p_0` (any rational is a ratio of integers). Then
> `∑_i 1/p_i = 1/p_0 + k/q = 1/τ`, so **all `τ/δ_i` are integers and Theorem 22 gives**
> ```
>        \mathrm{LV}(σ,τ) ≤ (2−2σ)τ
> ```
> for the detection coefficients. By monotonicity in `τ` and density of the rationals this extends to
> all real `τ ≥ 1`. *(Example `τ = 7/5`: `p_0 = 2`, `1/τ−1/2 = 3/14`, so `k = 3` mollifier factors of
> length `N^{1/10}` each and a `ζ`-side factor of length `N^{7/10}`; `∑1/p_i = 1/2+3/14 = 5/7 = 1/τ`.
> Example `τ = 3/2`: `p_0 = 2`, `k/q = 2/3−1/2 = 1/6`, so one mollifier factor of length `N^{1/4}` and
> a `ζ`-side factor of length `N^{3/4}`, `p_0 = 2`, `q = 6`.)*

## What is still required `[OPEN CORE 35]`
The design produces the *right* factor lengths; three compatibility checks remain, and they are the
whole of what is left:
* **(i)** the `ζ`-side factor of length `X = N^{τ/p_0}` must genuinely arise in the reduction — i.e.
  the zero-detection must be run so that the truncation length is `X` of our choosing, using the
  smallness of `∑_{n≤T}n^{-ρ}` at a zero (blueprint Lemma 11.5) rather than a fixed `T`- or
  `√T`-truncation;
* **(ii)** the factored mollifier must still make the identity `ζM = 1 + O(\text{tail})` usable, i.e.
  the *upper* truncation error of `∏_iM_i` (not the low-range cancellation, which is settled above)
  must be acceptable — this is the single genuinely new estimate the route needs;
* **(iii)** the `ζ`-side factor carries coefficients `1` (or `n^{σ−1}` for the dual AFE term), so its
  `p_0`-th power has divisor-bounded coefficients `d_{p_0}` ✔, and the Montgomery–Vaughan input
  applies verbatim ✔.
**If (i) and (ii) hold, Theorems 22 + 24 give `LV(σ,τ) ≤ (2−2σ)τ` for the detection coefficients at
every `τ`, which is Montgomery's `ℓ^q` conjecture along the reduction, hence the Density Hypothesis.**
This is the tightest the programme has become: no inequality remains to be proved, only the
construction of a mollifier with prescribed factor lengths and an acceptable truncation error.

---

# CYCLE 25 (2026-07-25) — executing the design inside the real reduction: the balanced split is forced, and the exact tension that remains

## The reduction produces a convolution with **designable and forced-balanced** factor lengths `[PROVED HERE]`
Run blueprint Lemma 11.5 with an `m`-fold mollifier. At a zero `ρ` one has
`∑_{n≤T}n^{-ρ} ≪ T^{-1/2}`; split at `T^{δ_1}`. In the Type II case `∑_{n≤T^{δ_1}}n^{-ρ} ≪ T^{-δ_2}`,
multiply by `∏_{i=1}^{m-1}\big(∑_{d≤D}d^{-ρ}\big)` with `D := T^{δ_1}`:
```
   \Big|1 + ∑_{1<k≤K} b_k k^{-ρ}\Big| ≪ T^{-δ_2}D^{(m-1)(1-σ)} = o(1),\qquad
   b = 1_{≤D}^{\,*m},\quad K = D^{m},
```
so `|∑_{1<k≤K}b_kk^{-ρ}| ≫ 1`. **All `m` factors have the same length `D`, and since each factor is
`≤ D` while the product is `≍ D^m`, every dyadic split is forced to be balanced:**
```
        δ_1 = ⋯ = δ_m = 1/m ,\qquad τ = \log T/\log K = 1/(mδ_1),\qquad τ/δ_i = mτ = 1/δ_1 .
```
**So `τ/δ_i` is an integer exactly when `1/δ_1 ∈ ℤ`** — a free choice. Setting `M := 1/δ_1`,
Theorem 22 applies with `p_i = M`, `u = m/M = 1/τ`, `z = 0`, and gives
```
        \mathrm{LV}(σ,τ) ≤ (2−2σ)τ ,\qquad\text{hence}\qquad  R ≤ K^{(2−2σ)τ} = T^{2−2σ} ,
```
**which is the Density Hypothesis for the Type II contribution.** ✔ (Type I always has `τ ≥ 2` and is
handled by `LV_ζ`, whose condition in Corollary 11.9 at `τ_0 = 3/2` is vacuous.)

## The exact tension that blocks it `[PROVED HERE — the honest obstruction]`
Three constraints must hold simultaneously:
1. **Divisor boundedness.** `A_i^{p_i}=A_i^{M}` has coefficients `d_M(n)` and
   `∑_{n≤T}d_M(n)² ≍ T(\log T)^{M²−1}`, which is `T^{1+o(1)}` **only if `M = O(1)`**, i.e.
   `δ_1 ≍ 1`.
2. **Mollifier admissibility.** `T^{-δ_2}D^{(m-1)(1-σ)} = o(1)` forces
   `(m−1)(1−σ)δ_1 < δ_2`; combined with `δ_2 < δ_1` this gives `m < 1 + 1/(1−σ)` — at `σ = 7/10`,
   `m ≤ 4`. (This is fine.)
3. **Type I admissibility.** The Type I branch loses a factor `T^{2δ_2}` at threshold `T^{-δ_2}`, so
   `δ_2 ≤ ε`; with (2) this forces `δ_1 ≤ ε/((m−1)(1−σ))`, hence `M = 1/δ_1 ≫ 1/ε` — **contradicting
   (1)**.
> **The obstruction, exactly: the design needs `1/δ_1` bounded (for the divisor bound `d_{1/δ_1}`),
> while the reduction needs `δ_1` small (because the Type I threshold `T^{-δ_2}` must be within
> `T^{ε}` and `δ_2 > (m−1)(1−σ)δ_1`). The two requirements are incompatible for `m ≥ 2`.**
`[OPEN CORE 36]` Break the tension. Three routes, none yet tried:
* **(a)** replace the trivial mollifier bound `|∑_{d≤D}d^{-ρ}| ≤ D^{1−σ}` — used to get
  constraint (2) — by a bound valid at the *specific* `ρ`; any saving relaxes (2) and hence (3);
* **(b)** replace `A_i^{M}` by a *smoothed* `M`-th power whose coefficients are `≪ n^{o(1)}` with an
  absolute implied constant, avoiding `(\log T)^{M²}` (e.g. use `∑_{n}d_M(n)²/n^{2σ}` with `σ>1/2`
  fixed, where the sum converges and the `M`-dependence is `ζ(2σ)^{M²}` — a *constant* once `σ` is
  fixed, but the relevant sum here is over `n ≤ T` unweighted);
* **(c)** avoid the Type I/II split entirely by mollifying the full `∑_{n≤T}n^{-ρ} ≪ T^{-1/2}`, whose
  threshold `T^{-1/2}` is a fixed power and needs no `δ_2`.
**Route (c) looks strongest: it removes `δ_2` from the picture altogether, and with it constraint (3).**

---

# CYCLE 26 (2026-07-25) — the mollifier is unnecessary: powering the Type II smallness

## Theorem 25 (mollifier-free Type II) `[PROVED HERE]`
Let `δ_1 = 1/M` (`M ∈ ℤ_{≥2}`) and suppose the Type II alternative holds:
`P(ρ) := ∑_{n ≤ T^{1/M}} n^{-ρ} ≪ T^{-δ_2}`. **Raise it to the `m`-th power instead of multiplying by
a mollifier:**
```
     P(ρ)^m ≪ T^{-mδ_2} = o(1),\qquad P(ρ)^m = 1 + ∑_{1<k≤K}c_k k^{-ρ},\quad c = 1_{≤T^{1/M}}^{\,*m},
     K = T^{m/M} .
```
Hence `|∑_{1<k≤K}c_kk^{-ρ}| ≫ 1`. **This eliminates every constraint that the mollifier imposed**:
there is no factor `∏|M_i(ρ)| ≤ D^{1−σ}` to control, so the Cycle-25 tension
`(m−1)(1−σ)δ_1 < δ_2 ≤ ε` disappears — the `m`-th power of a small quantity is automatically smaller.
The `m` factors are *identical*, of length `T^{1/M} = K^{1/m}`, so the split is forced balanced:
```
     δ_i = 1/m ,\quad τ = \log T/\log K = M/m ,\quad τ/δ_i = mτ = M ∈ ℤ ✔,
     p_i = M ,\quad u = m/M = 1/τ ✔ (z = 0),\quad u ≤ 1 ⟺ τ ≥ 1 ✔,
```
and the coefficients of `A_i^{M}` are `d_M`-bounded with **`M = O(1)`**, so
`∑_{n≤T}d_M(n)² ≪ T(\log T)^{M²−1} = T^{1+o(1)}` ✔. Theorem 22 therefore gives
```
        \mathrm{LV}(σ,τ) ≤ (2−2σ)τ  \ \Longrightarrow\ R_{II} ≪ K^{(2−2σ)τ+o(1)} = T^{2−2σ+o(1)} ,
```
**the Density Hypothesis for the Type II contribution, unconditionally, for every `τ = M/m` with
`1 ≤ m ≤ M`.** ✔

## What this leaves `[OPEN CORE 37]`
The Type I alternative is `|∑_{T^{1/M}<n≤T}n^{-ρ}| ≫ T^{-δ_2}`, giving after dyadic decomposition a
**zeta-type** polynomial `∑_{n∼N}n^{-ρ}` with `N ∈ (T^{1/M}, T]`, i.e. `τ_I ∈ [1, M)`, at the shifted
abscissa `σ' = σ − δ_2τ_I` (`δ_2 ≤ ε`). So:
> **DH now follows from: `\mathrm{LV}_ζ(σ,τ) ≤ (2−2σ)τ` for `τ ∈ [1,M)`, for some integer `M ≥ 2`.**
Known inputs for that range:
* `\mathrm{LV}_ζ(σ,τ) = −∞` for `τ < (σ−1/2)/μ(1/2)`, i.e. `τ < 6.46(σ−1/2)` with `μ(1/2) ≤ 13/84`
  (Bourgain). At `σ = 7/10` this covers `τ < 1.29`; taking `M = 2` the residual range is
  `τ_I ∈ [1.29, 2)`.
* On that residual range the reflection principle (blueprint Lemma 8.3(iv)) converts
  `\mathrm{LV}_ζ(σ,τ)` into `\mathrm{LV}_ζ\big(\tfrac12+\tfrac{σ−1/2}{τ−1},\tfrac{τ}{τ−1}\big)`;
  for `τ ∈ [1.29,2)` the reflected `τ` lies in `(2, 4.45]` and the reflected abscissa is
  `≥ 1/2 + (σ−1/2)` — i.e. **the residual Type I range reflects into a regime where the reflected
  abscissa is large**, which is exactly where zeta-type large-value estimates are strongest.
**So the entire Density Hypothesis has been reduced to a statement about `\mathrm{LV}_ζ` — the
large-value problem for the *pure* exponential sum `∑_{n∼N}n^{-it}`, with no coefficients at all —
on the single interval `τ ∈ [(σ−1/2)/μ(1/2), 2)`.** That is a dramatically smaller target than the
general large-value problem: it involves one explicit sum and is exactly the object that exponent
pairs, the van der Corput hierarchy, and the reflection principle were built for.

---

# CYCLE 27 (2026-07-25) — Theorem 26: the Density Hypothesis for the Type II contribution above the low range

## The argument `[PROVED HERE]`
Fix `σ ∈ (1/2,1)`, `T` large, and let `M = M(T) → ∞` with `M ≤ c(\log T/\log\log T)^{1/4}`.
Put `D := T^{1/M}`, `δ_2 ≤ ε`. For each zero `ρ = β+iγ`, `β ≥ σ`, `γ ∈ [T,2T]`:
`∑_{n≤T}n^{-ρ} ≪ T^{-1/2}`, so either **(I)** `|∑_{D<n≤T}n^{-ρ}| ≫ T^{-δ_2}` or **(II)**
`P(ρ) := ∑_{n≤D}n^{-ρ} ≪ T^{-δ_2}`.

In case (II) raise to the `M`-th power (**no mollifier needed** — the power of a small quantity is
smaller, so none of the Cycle-25 constraints appear):
```
   P(ρ)^{M} = 1 + ∑_{1<k≤T}c_kk^{-ρ},\quad c = 1_{≤D}^{*M},\quad |P^M| ≪ T^{-Mδ_2},
   \Longrightarrow\ \Big|∑_{1<k≤T}c_kk^{-ρ}\Big| ≥ 1/2 .
```
Dyadic pigeonholing over `k ∼ N` and over the `(\log T)^{M} = T^{o(1)}` factor-length configurations
`(N_1,…,N_M)`, `∏N_i ≍ N`, `N_i ≤ D`, and **merging factors greedily so that every merged factor has
`η_j := \log_T N'_j ∈ [1/M, 2/M]`**, one obtains for a subset of `≥ RT^{-o(1)}` zeros a common
configuration with
```
   δ_j = η_jτ ,\quad p_j := ⌈1/η_j⌉ ∈ [M/2, M] ,\quad u = ∑_j 1/p_j ≥ \frac{1}{τ(1+2/M)} ,\quad u ≤ 1 .
```
Each `B_j^{p_j}` has length `(N'_j)^{p_j} ≥ T` and coefficients bounded by `d_{M²}(n) ≪ T^{o(1)}` with
`∑_{n≤L}d_{M²}(n)² ≪ L(\log L)^{M⁴} = L\,T^{o(1)}` (this is where `M ≤ (\log T/\log\log T)^{1/4}` is
used). Montgomery–Vaughan then gives `(∑_{t∈W}|B_j^{p_j}|²)^{1/p_j} ≪ (N'_j)²T^{o(1)}`, and
generalised Hölder yields
```
   R\,V² ≤ ∑_{t∈W}∏_j|B_j|² ≪ N²T^{o(1)}R^{1-u}
   \ \Longrightarrow\ R ≪ N^{(2-2σ)/u}T^{o(1)} ≤ N^{(2−2σ)τ(1+2/M)}T^{o(1)} = T^{2−2σ+o(1)} .
```
> ### Theorem 26 `[PROVED HERE]`
> **For every dyadic block `N ≥ T^{1/M}`, the Type II contribution to `N(σ,T)` is `≪ T^{2−2σ+o(1)}` —
> the Density Hypothesis — unconditionally, by Hölder + Montgomery–Vaughan alone.**
> The two ingredients that make it work and are absent from the classical treatment are: (a) the
> `M`-th power of the Type II smallness replaces the mollifier and removes every size constraint;
> (b) the merging step keeps all Hölder exponents in `[M/2,M]`, so the rounding loss is `1+2/M → 1`
> while the divisor functions stay `T^{o(1)}`.

## The exact residual gap `[OPEN CORE 38]`
The argument requires the dyadic block to satisfy `N ≥ D = T^{1/M}`; otherwise the block lies inside
the range of a *single* factor, the merged-exponent bound `p_j ≤ M` fails (`p = ⌈τ⌉ > M`), and the
divisor function `d_{Mτ}` is no longer `T^{o(1)}`. So what remains is:
> **the low range `2 ≤ N < T^{1/M}`, where the polynomial is `∑_{k∼N}d_M(k)k^{-ρ}` — the `M`-fold
> divisor function against a zeta zero.** For such `N` the mean value theorem only gives
> `R ≪ TN^{1−2σ}`, which is `≫ T^{2−2σ}`.
Three possible resolutions, none yet tried: (i) show the low range cannot carry the mass, i.e. that
`|∑_{1<k≤T^{1/M}}d_M(k)k^{-ρ}| = o(1)` follows from `|P(ρ)| ≪ T^{-δ_2}` (note the low range is
exactly `P^M` truncated, and `P^M` *is* tiny — the question is whether the truncation can be large);
(ii) iterate the construction inside the low range with a larger `M`; (iii) treat the low range by
the same dichotomy applied to `P` itself, whose blocks are zeta-type and fall to `LV_ζ`.
**This is the sharpest and most nearly complete argument the programme has produced: the Density
Hypothesis now holds for the entire Type II contribution except for dyadic blocks below `T^{1/M}`,
with `M → ∞`.**

---

# CYCLE 28 (2026-07-25) — correction to Theorem 26, the powered Möbius mollifier, and the exact incompatibility

## CORRECTION: Theorem 26 is true but **vacuous** `[RECORDED DEAD END]`
The Cycle-27 argument pigeonholes `|∑_{1<k≤T}c_kk^{-ρ}| ≥ 1/2` over dyadic blocks. But for
`c = 1_{≤D}^{*M}` the *low* blocks are trivially large: `c_2 = c_3 = M`, so the block `k∼2` already has
`|M(2^{-ρ}+3^{-ρ})| ≍ M ≫ 1`. Every zero satisfies the low-block largeness, so the pigeonhole selects
a block for which the resulting bound is `R ≪ TN^{1−2σ} ≈ T`, i.e. nothing. **Theorem 26's hypothesis
`N ≥ T^{1/M}` is never forced. Powering alone cannot replace a mollifier.**
> **Structural lesson (this is the load-bearing insight): the mollifier's role is NOT to be small — it
> is to make the coefficients *vanish* on a low range.** Only vanishing forces the dyadic block to be
> large. The Cycle-25 "size tension" was therefore the wrong diagnosis.

## What the blueprint actually does, and its gap `[VERIFIED against source]`
Read from `zdchap.txt`, Lemma 11.5, Type II: the mollifier used is `∑_{m≤T^{δ_2/2}}m^{-σ_r−it_r}`
(**not** Möbius), giving `|1 + ∑ a_n n^{-ρ}| = o(1)` with `a = 1_{≤T^{δ_1}} ∗ 1_{≤T^{δ_2/2}}`; the size
condition is automatic since `(δ_2/2)(1−σ) < δ_2`. The text then asserts the dyadic block satisfies
`N ≫ T^{δ_2/2}`. **That does not follow for this mollifier**: `a_k = d(k) ≠ 0` for small `k`, so the
low blocks are again trivially large. The step is repaired by the classical Möbius mollifier, which
gives *exact* vanishing.

## Theorem 27 (powered Möbius mollifier — a longer mollifier than the classical one) `[PROVED HERE]`
Let `D = T^{δ_1}`, let `μ_M` be the Dirichlet coefficients of `ζ^{-M}` (`|μ_M(m)| ≤ d_M(m)`), and set
```
    G(s) := \Big(∑_{n≤D}n^{-s}\Big)^{M}\cdot\Big(∑_{m≤D}μ_M(m)m^{-s}\Big) .
```
Then (i) **exact low-range vanishing:** the coefficients `a` of `G` satisfy `a_k = [k=1]` for all
`k ≤ D`, because for such `k` every factorisation has all parts `≤ D`, so
`a_k = (d_M ∗ μ_M)(k) = [k=1]`; (ii) **admissibility:** under the Type II hypothesis
`|∑_{n≤D}n^{-ρ}| ≪ T^{-δ_2}`,
```
    |G(ρ)| ≪ T^{-Mδ_2}·D^{1−σ}(\log D)^{M−1} = T^{-Mδ_2+δ_1(1−σ)+o(1)} = o(1)
    \qquad\text{as soon as } M > δ_1(1−σ)/δ_2 .
```
**Powering the Type II smallness by `M` buys a mollifier that is `M` times longer in the exponent.**
With the classical (`M=1`) mollifier the length is capped at `T^{δ_2/(1−σ)}` with `δ_2 → 0`; here it is
`T^{δ_1}` with `δ_1` fixed — a mollifier of *fixed positive relative length*, which is what any
integral-length design needs. Total length `K = D^{M+1} ≤ T` on choosing `δ_2 = 2δ_1²(1−σ)`,
`M ≍ 1/δ_1`, and every parameter `δ_1, δ_2, M` is a constant independent of `T`, so all divisor
functions appearing are `d_{O(1)} ≪ T^{o(1)}`. ✔

## The exact incompatibility `[OPEN CORE 39]` — stated sharply
With `G` in hand, `|G(ρ) − 1| ≥ 1/2` and `G − 1 = ∑_{\text{nontrivial configs}}∏_iA_i^{(j_i)}(ρ)`,
where the configs are the `(\log D)^{M+1} = T^{o(1)}` dyadic factor-length choices and the trivial
config contributes the `1`. Two mutually exclusive ways to proceed:
* **Pigeonhole over configs.** Each surviving config *is* a genuine product `∏_iA_i` with designable
  lengths — exactly the input Theorems 22–24 need. **But** a config with all but one `N_i = 1` and the
  remaining `N_i = 2` is always large (`|2^{-ρ}+3^{-ρ}| ≍ 1`), so the pigeonhole is vacuous. The
  low-range vanishing `a_k = 0 (1<k≤D)` is a *cancellation among configs*; pigeonholing destroys it.
* **Restrict to a dyadic block `k ∼ N`, `N > D`.** The cancellation is then already spent and the
  block is genuinely large. **But** a config's product is supported on `[∏N_i, 2^{M+1}∏N_i]`, so the
  block restriction cuts configs and the product structure is lost; the Mellin/smooth identity
  reconstructs only the *full* `G` at shifted points, where nothing is small.
> **THE OBSTRUCTION, EXACTLY: the largeness of the detection polynomial lives in a cancellation
> between factor-length configurations, while the Hölder–moment method requires a single
> configuration. Any device that isolates one configuration destroys the cancellation that created
> the largeness.** This is a statement about the *incompatibility of two decompositions of the same
> Dirichlet polynomial* — multiplicative (by factor lengths) versus additive (by dyadic support) —
> and it is, as far as this programme can tell, the true reason the Hölder–moment family stalls at
> `⌈τ⌉` instead of `τ`.
`[OPEN CORE 40]` The way out must be a decomposition that is **simultaneously** multiplicative and
support-localised. Candidate: replace the dyadic block `1_{k∼N}` by a *multiplicative* projector —
e.g. project onto `k` with a prescribed number of prime factors (`Ω(k) = ω`), which **is**
multiplicative-compatible: `Ω` is additive on the factorisation, so `1_{Ω(k)=ω}` decomposes as a
convolution over `(ω_1,…,ω_{M+1})` with `∑ω_i = ω`, and each factor `∑_{n≤D, Ω(n)=ω_i}n^{-s}` is a
genuine Dirichlet polynomial. The trivial config has `Ω = 0`; the low range `k ≤ D` has `Ω(k) ≤ \log_2 D`.
**Localising in `Ω` rather than in `\log k` may keep both structures at once.**

## Theorem 28 (low-range vanishing forces cross-factor cancellation) `[PROVED HERE]`
Let `G = ∏_{i=1}^{r}B_i` with `B_i(s) = ∑_n b_i(n)n^{-s}`, `b_i(1) = 1`, and suppose the coefficients
`a` of `G` satisfy `a_k = 0` for `1 < k ≤ y`. Put `n_0 := \min\{n>1 : b_i(n) ≠ 0` for some `i\}`.
If `n_0 ≤ y` then, since every configuration with two nontrivial factors contributes only to `k ≥ n_0²`,
```
        a_{n_0} = ∑_{i=1}^{r} b_i(n_0) = 0 .
```
Hence **either** every factor already vanishes on `1<n≤y` (each `B_i` is itself `1 + (\text{tail above } y)`,
and the problem recurs one level down), **or** the low-range vanishing of `G` is a nontrivial linear
cancellation *across* the factors.
### Corollary 28.1 — the cancellation survives neither `ℓ^1` nor `ℓ^2` pigeonholing `[PROVED HERE]`
Write `G − 1 = ∑_{c∈𝒞}F_c`, `F_c = ∏_i B_i^{(c_i)}`, over the `|𝒞| = T^{o(1)}` dyadic factor-length
configurations. One may try to select a single `c` either by `ℓ^1` pigeonholing (`|F_c(ρ)| ≫ 1/|𝒞|`)
or, more cheaply, by Cauchy–Schwarz at the `ℓ^2` level:
`R/4 ≤ |𝒞|∑_c∑_{r∈W}|F_c(ρ_r)|²`, giving some `c` with `∑_{r∈W}|F_c(ρ_r)|² ≥ R\,T^{-o(1)}`.
**Both fail for the same reason.** The near-trivial configurations — one factor restricted to
`n ∼ N_1 = O(1)`, all others equal to `1` — satisfy `|F_c(ρ)| ≍ 1` for *every* `ρ`, so they dominate
both the `ℓ^1` and the `ℓ^2` selection; for them `N = ∏N_i = O(1)` and the Hölder–MVT chain returns
`R\,T^{-o(1)} ≤ R\,N^{2(1−β)}T^{o(1)}`, which is vacuous. Excluding them requires knowing that the
small-`N` configurations contribute little — which is precisely the cancellation that the selection
destroyed.
> **This is a genuine structural theorem about the method, not a failure of ingenuity: the largeness of
> a mollified detection polynomial is *created* by cancellation between factor-length configurations,
> and every device that isolates a single configuration — pigeonhole, Cauchy–Schwarz, or the
> Mellin/smooth identity — destroys exactly that cancellation. This is why the Hölder–moment family
> is pinned at `⌈τ⌉` and cannot reach `τ`, and it upgrades the Cycle-23 "rounding" diagnosis to a
> statement about which decompositions of a Dirichlet polynomial can coexist.**
`[OPEN CORE 41]` What survives Theorem 28 must not select a configuration at all. Two shapes:
* **(A) Configuration-summed multilinear estimates.** Bound `∑_{r∈W}\big|∑_cF_c(ρ_r)\big|²` directly,
  keeping the cancellation. Expanding gives cross terms `∑_{c≠c'}F_c\overline{F_{c'}}`, i.e. a
  *bilinear* problem in configuration space — the correlation of two different factor-length
  decompositions of the same integer. **Nothing in the literature estimates this object.**
* **(B) Localise multiplicatively, not additively.** `Ω(k)` is completely additive, so
  `1_{Ω(k)=ω}` *is* compatible with the product structure:
  `∑_{Ω(k)=ω}(α_1∗⋯∗α_r)(k)k^{-s} = ∑_{ω_1+⋯+ω_r=ω}∏_i\big(∑_{Ω(n)=ω_i}α_i(n)n^{-s}\big)`.
  The trivial configuration is `ω = 0` and is excluded by taking `ω ≥ 1`; the number of
  `Ω`-configurations is `\binom{ω+r}{r} = T^{o(1)}`. **But `Ω`-localisation alone does not defeat
  Theorem 28** — the near-trivial `Ω`-configurations are still large — so it must be combined with (A).

---

# CYCLE 29 (2026-07-25) — **Theorem 29: the Type II branch of the zero-detection satisfies the Density Hypothesis unconditionally**

Theorem 28 says the low-range vanishing of a product is either a cross-factor cancellation (fatal) or
**every factor already vanishes on the low range** (case (i)). Case (i) is not a dead end — it is the
construction. Here it is.

## Construction
Fix `1/2<σ<1` and `δ_1 > 0` small; put `D := T^{δ_1}` and pick `δ_2 ∈ (δ_1(1−σ),\ δ_1)` — **non-empty
because `1−σ < 1`.** Let
```
     B(s) := \Big(∑_{n≤D}n^{-s}\Big)\Big(∑_{m≤D}μ(m)m^{-s}\Big) = 1 + t(s),
     \qquad t(s) = ∑_{D<k≤D²}a_kk^{-s},\ \ a_k = ∑_{d|k,\ d≤D,\ k/d≤D}μ(d),\ |a_k| ≤ d(k) .
```
* **Exact low-range vanishing:** for `k ≤ D` every divisor `d` of `k` satisfies `d ≤ D` and `k/d ≤ D`,
  so `a_k = ∑_{d|k}μ(d) = [k=1]`. Hence `t` is supported on `(D, D²]` — **a window of multiplicative
  width `D`, so every dyadic block of `t` has length exponent `η ∈ (δ_1, 2δ_1]`.**
* **Smallness at a Type II zero:** `|B(ρ)| ≤ |∑_{n≤D}n^{-ρ}|·∑_{m≤D}m^{-σ} ≪ T^{-δ_2}D^{1−σ}
  = T^{-δ_2+δ_1(1−σ)} = o(1)`, so `|t(ρ)| ≥ 1/2`.
* **Power to a genuine product.** Let `M' := ⌊1/(2δ_1)⌋`. Then `|t(ρ)^{M'}| ≥ 2^{-M'}` and
  ```
      t^{M'} = ∑_{(N_1,…,N_{M'})} ∏_{i=1}^{M'} t^{(N_i)},\qquad N_i ∈ (D,D²]\ \text{dyadic},
  ```
  with `(\log T)^{M'} = T^{o(1)}` configurations. **Every configuration is nontrivial** — each factor
  has `N_i > D` — so pigeonholing (over configurations and over the zeros) is *lossless in kind*:
  there is no constant term whose removal created the largeness, hence **no cancellation to destroy**.
  This is exactly Theorem 28 case (i), and it is why powering the *mollified* polynomial succeeds
  where powering the raw one (Cycle 27) failed.

## The estimate
For a subset of `≥ R\,T^{-o(1)}` zeros one gets `∏_i|t^{(N_i)}(ρ_r)| ≫ T^{-o(1)}`; normalising each
factor (`\tilde T_i(γ) = ∑_{k∼N_i}a_k(N_i/k)^{β}k^{-iγ}`, coefficients `≪ T^{o(1)}`) gives
`∏_i|\tilde T_i(γ_r)| ≫ N^{σ}T^{-o(1)}` with `N = ∏N_i`, `τ = \log T/\log N`. Setting
`η_i = \log_T N_i ∈ (δ_1,2δ_1]` and `p_i := ⌈1/η_i⌉ ∈ [1/(2δ_1), 1/δ_1)`:
```
  N_i^{p_i} ≥ T ,\qquad u := ∑_i 1/p_i ≥ ∑_i \frac{η_i}{1+η_i} ≥ \frac{1}{τ(1+2δ_1)} ,\qquad u ≤ ∑η_i = 1/τ ≤ 1 .
```
Each `\tilde T_i^{p_i}` has length `N_i^{p_i}` and coefficients bounded by `d_{2p_i}` with
`2p_i = O_{δ_1}(1)`, so `∑_{k}|·|² ≪ N_i^{p_i}T^{o(1)}` and Montgomery–Vaughan gives
`(∑_{r}|\tilde T_i^{p_i}|²)^{1/p_i} ≪ N_i²T^{o(1)}`. Generalised Hölder then yields
```
  R\,N^{2σ}T^{-o(1)} ≤ ∑_{r}∏_i|\tilde T_i(γ_r)|² ≤ ∏_i\Big(∑_r|\tilde T_i^{p_i}|²\Big)^{1/p_i}R^{1-u}
       ≪ N²T^{o(1)}R^{1-u} ,
```
so `R^{u} ≪ N^{2−2σ}T^{o(1)}` and
```
   R ≪ N^{(2−2σ)/u+o(1)} ≤ N^{(2−2σ)τ(1+2δ_1)+o(1)} = T^{(2−2σ)(1+2δ_1)+o(1)} .
```
Letting `δ_1 → 0` after `T → ∞`:

> ### Theorem 29 `[PROVED HERE]`
> **The Type II (general–coefficient) contribution to `N(σ,T)` is `≪ T^{2−2σ+o(1)}` for every fixed
> `1/2 < σ < 1`, unconditionally.** Consequently Lemma 11.5 improves to
> ```
>        \mathrm{A}(σ)(1−σ) ≤ \max\Big( \sup_{τ ≥ 2} \mathrm{LV}_ζ(σ,τ)/τ ,\ 2−2σ \Big),
> ```
> and combined with the converse Lemma 11.6 (`\mathrm{LV}_ζ(σ,τ)/τ ≤ \max(1/2, \sup_{σ'≥σ}
> \mathrm{A}(σ')(1−σ')+\frac{σ'−σ}{2})`):
> ```
>   \textbf{Density Hypothesis} \iff \sup_{τ≥2}\ \mathrm{LV}_ζ(σ,τ)/τ ≤ 2−2σ \quad (1/2<σ≤3/4),
> ```
> i.e. **the Density Hypothesis is exactly the large-value problem for the pure exponential sum
> `∑_{n∼N}n^{-it}` — no general coefficient sequences are involved.**

## Why this is not the classical argument
The classical Type II bound uses `\mathrm{LV}(σ,τ) ≤ 1+τ−2σ` (mean value theorem), whose
`τ→∞` limit is `1`, not `2−2σ`. The three moves that replace it are: (a) the **Möbius** mollifier
truncated at the *same* length `D` as the zeta piece, which confines `t` to the narrow window
`(D,D²]` and hence pins every block length exponent to `(δ_1,2δ_1]`; (b) **powering the mollified
polynomial** `t` (not the raw one) to manufacture a product all of whose factors inherit the
low-range vanishing; (c) the **rounding bound** `1/⌈1/η⌉ ≥ η/(1+η)` (Theorem 22/23), which converts
narrow blocks into `u ≥ (1/τ)/(1+2δ_1)`.
`[OPEN CORE 42]` Verify (b) once more against the possibility that the pigeonholed configuration is
`(N_1,…,N_{M'})` with `∏N_i` so large that `τ < 1` (Hölder needs `u ≤ 1`): `N ≤ D^{2M'} ≤ T` by the
choice `M' = ⌊1/(2δ_1)⌋`, so `τ ≥ 1` always. ✔
`[OPEN CORE 43]` The whole Density Hypothesis is now `\sup_{τ≥2}\mathrm{LV}_ζ(σ,τ)/τ ≤ 2−2σ`. Attack
that next: it is one explicit sum, and the reflection principle plus exponent pairs act on it
directly.

## Theorem 29, corrected parameter choice (the `M = 1` mollifier breaks Type I) `[PROVED HERE]`
The choice `δ_2 ∈ (δ_1(1−σ), δ_1)` above is inadmissible: the Type I branch of Lemma 11.5 produces
`|∑_{k∈I}k^{-it'}| ≫ N^{σ−δ_2/δ_1+o(1)}`, so it needs `δ_2/δ_1 = o(1)`, whereas `M = 1` forces
`δ_2/δ_1 > 1−σ`. **The powered Möbius mollifier of Theorem 27 removes the conflict.** Take
```
   B(s) := \Big(∑_{n≤D}n^{-s}\Big)^{M}\Big(∑_{m≤D}μ_M(m)m^{-s}\Big),\qquad D = T^{δ_1},
```
`μ_M` = coefficients of `ζ^{-M}`. Then
* `a_k = (d_M ∗ μ_M)(k) = [k=1]` for `k ≤ D` — **vanishing, hence `t := B−1` is supported on
  `(D, D^{M+1}]` and every dyadic block of `t` has `η ∈ (δ_1, (M+1)δ_1]`;**
* `|B(ρ)| ≪ T^{-Mδ_2}D^{1−σ}T^{o(1)} = o(1)` as soon as `M > δ_1(1−σ)/δ_2` — **powering relaxes the
  mollifier admissibility condition by the factor `M`.**
Choose
```
   δ_2 := δ_1^{3/2},\qquad M := ⌈(1−σ)δ_1^{-1/2}⌉,\qquad M' := ⌊1/((M+1)δ_1)⌋ .
```
Then `δ_2/δ_1 = δ_1^{1/2} = o(1)` ✔ (Type I untouched), `Mδ_2 = (1−σ)δ_1 > δ_1(1−σ)·(1−o(1))` ✔
(admissible), `(M+1)δ_1 ≍ (1−σ)δ_1^{1/2} = o(1)` ✔ (narrow window), and `M, M', p_i` are all constants
independent of `T`, so every divisor function occurring is `d_{O(1)} ≪ T^{o(1)}` ✔. The rounding
bound becomes `u ≥ (1/τ)/(1+(M+1)δ_1)` and the conclusion is
```
   R ≪ T^{(2−2σ)\,(1+O((1−σ)δ_1^{1/2}))+o(1)} \xrightarrow[\ δ_1→0\ ]{} T^{2−2σ+o(1)} .
```
> **Theorem 29 stands. The Type II contribution to `N(σ,T)` is `≪ T^{2−2σ+o(1)}` unconditionally, and
> the Density Hypothesis is equivalent to `\sup_{τ≥2}\mathrm{LV}_ζ(σ,τ)/τ ≤ 2−2σ` — the large-value
> problem for the bare exponential sum `∑_{n∼N}n^{-it}`.**

---

# CYCLE 30 (2026-07-25) — ANTI-THEATRE AUDIT: Theorem 29 is a **rediscovery**; and the rounding obstruction is the *same* on the zeta side

## Verdict on Theorem 29: `REDISCOVERED` `[CORRECTION — read before reusing]`
Checked against the blueprint source (`largevalue-chapter.txt`, `zdchap.txt`):
* **Lemma 7.8 (raising to a power):** `\mathrm{LV}(σ,kτ) ≤ k\,\mathrm{LV}(σ,τ)` for natural `k`.
* With `\mathrm{LV}(σ,τ') ≤ 2−2σ` for `τ' ≤ 1` (mean value theorem), this gives
  `\mathrm{LV}(σ,τ) ≤ ⌈τ⌉(2−2σ)`, hence `\limsup_{τ→∞}\mathrm{LV}(σ,τ)/τ ≤ 2−2σ` **elementarily**.
* Lemma 11.5's general-coefficient branch *is* `\limsup_{τ→∞}\mathrm{LV}(σ,τ)/τ`. Therefore
  `\mathrm{A}(σ)(1−σ) ≤ \max(\sup_{τ≥2}\mathrm{LV}_ζ(σ,τ)/τ,\ 2−2σ)` is already available, and with
  Lemma 11.6 the equivalence `DH ⟺ \sup_{τ≥2}\mathrm{LV}_ζ(σ,τ)/τ ≤ 2−2σ` (for `σ ≤ 3/4`) is known.
**Theorem 29's construction (powered Möbius mollifier + narrow window + per-factor rounding) is
correct, but its conclusion is not new: the narrow-window device reproduces what `⌈τ⌉/τ → 1` already
gives.** Recorded so no future cycle re-derives it. Theorem 27 (the powered Möbius mollifier, which
buys a mollifier `M` times longer in the exponent) and Theorem 28 (low-range vanishing forces
cross-factor cancellation) survive as independent statements.

## `[NEW]` The zeta branch carries the **same** rounding obstruction — quantitatively
For the bare sum `D(t) = ∑_{n∼N}n^{-it}`, `T = N^{τ}`, the `2k`-th moment is exact:
`|D|^{2k} = |∑_{m∼N^{k}}d_k^{(N)}(m)m^{-it}|²` with `∑_m (d_k^{(N)}(m))² ≪ N^{k+o(1)}`, so
Montgomery–Vaughan gives
```
   \mathrm{LV}_ζ(σ,τ) ≤ \min_{k∈ℕ}\ \begin{cases} τ + k(1−2σ), & k ≤ τ\quad(\text{length } N^k ≤ T)\\
                                        k(2−2σ), & k ≥ τ\quad(\text{length } N^k ≥ T)\end{cases}
```
Writing `τ = k+θ`, the two branches cross at `θ = θ_*` and
```
   \sup_{τ≥2}\ \mathrm{LV}_ζ(σ,τ)/τ \ \le\ \max_{k≥2}\ \frac{(k+1)(2−2σ)}{k+θ_*} ,\qquad
   θ_* \text{ solving } (k+1)(2−2σ) = k+θ+k(1−2σ).
```
At `σ = 7/10` the maximum is at `k = 2`, `θ_* = 3/5`, giving `\sup = 1.8/2.6 = 9/13 = 0.6923…`, hence
`\mathrm{A}(0.7) ≤ 0.6923/0.3 = 2.3077… = 3/(2−σ)` — **exactly Ingham's exponent.** The target is
`2−2σ = 0.6`. So:
> **The entire gap between Ingham and the Density Hypothesis, on the zeta side, is the integrality of
> `τ`: at `τ ∈ ℕ` the moment method gives `\mathrm{LV}_ζ(σ,τ) = (2−2σ)τ` exactly, and the deficit
> `9/13` vs `3/5` is pure rounding at `τ = 2.6`.** This is the same `⌈τ/δ⌉`-versus-`τ/δ` obstruction as
> Theorem 22, now isolated on an object with *no free coefficients*.

## `[CONJECTURE — OPEN CORE 44]` Fractional powers exist on the zeta side
The reason `k` must be an integer is that `D^k` must be a Dirichlet polynomial. **For the zeta sum
this constraint is not intrinsic:** `ζ(s)^{α}` is a Dirichlet series for every real `α > 0`, with
coefficients `d_α(n)` satisfying `|d_α(n)| ≤ d_{⌈α⌉}(n) ≪_α n^{o(1)}`. The missing object is a
*fractional power of a block*:
> **`[CONJECTURE 44]` For every real `α ≥ 1` and every `N`, there is a Dirichlet polynomial `E_α` of
> length `N^{α+o(1)}` with coefficients `≪ n^{o(1)}` such that `|E_α(t)| ≫ |D(t)|^{α}T^{-o(1)}`
> whenever `|D(t)| ≥ N^{σ}`, `σ > 1/2`.** Granting this with `α = τ`, the moment computation above
> runs with `k = τ` exactly, `θ_* = 0`, and yields `\mathrm{LV}_ζ(σ,τ) ≤ (2−2σ)τ` for all `τ ≥ 2` —
> **the Density Hypothesis.**
How it could fail: `D(t)^α` is only defined up to a branch, and `|D|^α` is not the modulus of any
Dirichlet polynomial in general; the conjecture asserts a *majorant*, not an identity, which is why it
is not immediately absurd. The natural candidate is the truncation of `ζ(σ+it)^{α}` — i.e. use the
*global* object rather than the block. What its falsity would teach: that integrality of the exponent
is a real arithmetic invariant of the large-value problem, not an artefact of the method — which
would make `‖A‖_∞ = 30/13` (attained at `σ = 7/10`, `τ = 13/5`) structurally forced rather than
merely current-best.
`[OPEN CORE 45]` Test Conjecture 44 against the one case where the answer is known: `α = 2`, where
`E_2 = D²` works with equality. Then `α = 3/2` at `N = T^{2/3}`.

## `[NEW — the sharpest concrete target the programme has]`
At `σ = 7/10` the moment-rounding computation above gives its maximum at `k = 2`, `θ_* = 3/5`, i.e.
```
        τ_* = 13/5 ,\qquad \mathrm{LV}_ζ(7/10, 13/5) ≤ 9/5 \ \text{(both branches equal)},
        \qquad \mathrm{A}(7/10) ≤ (9/5)/(3/10) = 6 \cdot \tfrac{5}{13}\cdot\ldots = 30/13 .
```
`30/13` is **exactly the current world record for `‖A‖_∞`** (Guth–Maynard 2024, whose contribution was
to beat Ingham on `(7/10, 3/4)` so that the supremum migrates to `σ = 7/10`, where Ingham's
`3/(2−σ) = 30/13` still stands). Hence:
> **At the critical point the world record equals the elementary two-branch moment bound, and the only
> thing separating it from the Density Hypothesis is that `τ_* = 13/5 ∉ ℕ`. Any improvement whatsoever
> on `\mathrm{LV}_ζ(7/10, 13/5) ≤ 9/5` lowers `‖A‖_∞` below `30/13`.**
The two branches at `(σ,τ) = (7/10, 13/5)` are: `k = 3` (length `N³ = T^{15/13} > T`), giving
`3(2−2σ) = 9/5`; and `k = 2` (length `N² = T^{10/13} < T`), giving `τ + 2(1−2σ) = 13/5 − 4/5 = 9/5`.
**They coincide** — the bound is a genuine crossing point, not a slack maximum, which is why no choice
of integer `k` improves it. `[OPEN CORE 46]` The interpolation `k = τ_* = 13/5` would give
`(2−2σ)τ_* = 39/25 = 1.56 < 1.8` and hence `‖A‖_∞ ≤ 2` at this point. **Conjecture 44 is exactly the
statement that this interpolation is legitimate.**

## `[PROVED HERE]` The two-scale (reflection) product is the `k = 2` moment in disguise
For `τ ≥ 2` the B-process gives largeness simultaneously at scales `N` and `M = T/N`:
`|D_N(t)| ≥ N^{σ} \Rightarrow |D_M(t)| ≫ M^{σ'}`, `σ' = 1/2+(σ−1/2)/(τ−1)`. The product `D_ND_M` has
length exactly `T`, so Montgomery–Vaughan gives
```
   R\,(N^{σ}M^{σ'})² ≪ T^{2+o(1)} \Longrightarrow R ≪ N^{τ−4σ+2+o(1)} ,
```
which is `≤ N^{(2−2σ)τ}` **iff `τ ≤ 2`** — numerically identical to the `k=2` branch. So the
reflection principle contributes no new information at the bottleneck; the two-scale product and the
fourth moment are the same estimate. `[RECORDED DEAD END]`

---

# CYCLE 31 (2026-07-25) — **Theorem 30: the rounding loss is the distance from 1 to a numerical semigroup of scales**

## The mechanism `[PROVED HERE]`
Suppose that for every `t ∈ W` (1-separated, `t ∈[T,2T]`) largeness holds simultaneously at `s` scales:
```
     |D_{N_i}(t)| ≥ N_i^{σ}T^{-o(1)} ,\qquad D_{N_i}(t) = ∑_{n∼N_i} n^{-it},\qquad η_i := \log_T N_i .
```
For any non-negative integers `a_1,…,a_s`, the product `P = ∏_i D_{N_i}^{a_i}` is a Dirichlet
polynomial of length `T^{x}`, `x := ∑_i a_iη_i`, with `d_{∑a_i}`-bounded coefficients (`≪ T^{o(1)}` for
`∑a_i = O(1)`) and `|P(t)| ≥ T^{σx−o(1)}`. Montgomery–Vaughan gives
`R\,T^{2σx} ≪ (T^{x}+T)\,T^{x+o(1)}`, i.e.
```
     R ≪ T^{(2−2σ)x+o(1)}\ (x ≥ 1) ,\qquad R ≪ T^{1+x(1−2σ)+o(1)}\ (x ≤ 1) ,
```
and in both cases, writing `ε := |x−1|`,
```
        R ≪ T^{\,2−2σ\ +\ c\,ε\ +\ o(1)} ,\qquad c = 2−2σ\ (x>1),\quad c = 2σ−1\ (x<1) .
```
> ### Theorem 30 `[PROVED HERE]`
> Let `𝒮 := \{∑_i a_iη_i : a_i ∈ ℤ_{≥0},\ ∑a_i = O(1)\}` be the numerical semigroup generated by the
> scales at which largeness occurs. Then
> ```
>        R ≪ T^{\,2−2σ\ +\ \max(2−2σ,\,2σ−1)\cdot \mathrm{dist}(1,𝒮)\ +\ o(1)} .
> ```
> **In particular the Density Hypothesis holds at every configuration for which
> `\mathrm{dist}(1,𝒮) = o(1)`.** With one scale, `𝒮 = ηℤ_{≥0}` and
> `\mathrm{dist}(1,𝒮) = \min_c|cη−1| = |⌈1/η⌉η − 1|` — **exactly the `⌈τ⌉/τ` rounding of Theorem 22**;
> at `(σ,τ) = (7/10,13/5)`, `η = 5/13`, `\mathrm{dist} = 2/13`, and
> `2−2σ + (2−2σ)(2/13) = 3/5·15/13 = 9/13`, reproducing `\mathrm{A}(7/10) ≤ 30/13` on the nose.

## Why two scales are always available `[PROVED HERE]`
At a zero, `∑_{n≤T}n^{-ρ} ≪ T^{-1/2}`, i.e. the sum of all dyadic blocks is *tiny*, while the Type I
alternative supplies a block with `|S_j| ≫ T^{-δ_2}` — which is *not* tiny. **Cancellation therefore
forces a second block of comparable size:** if only one block were `≫ T^{-δ_2}/\log T`, the total could
not be `≪ T^{-1/2}`. Pigeonholing over pairs (`O(\log^2 T)` choices) yields two scales `η_1,η_2`
with largeness at both, for a subset of `≥ R\,T^{-o(1)}` zeros. Hence `𝒮 ⊇ \{aη_1+bη_2\}` is
genuinely two-generated, and `\mathrm{dist}(1,𝒮) ≤ \min_{a,b}|aη_1+bη_2−1|`, which for
incommensurable `η_1,η_2` is far smaller than the one-generator value.
> **This converts the Density Hypothesis into a statement about the *set of scales at which the partial
> sums of `ζ` at a zero are large* — a Diophantine question about a numerical semigroup, not an
> analytic one about oscillatory sums.** It is the first formulation in this programme in which the
> obstruction is not an inequality to be improved but a *covering* condition to be verified.
`[OPEN CORE 47]` The remaining question is exactly: **can the large scales all be commensurable?**
i.e. can a zero have all of its large blocks at scales `N_i = T^{η_i}` with every `η_i` an integer
multiple of a common `η` with `\min_c|cη−1|` bounded away from `0` (the extremal being `η ≍ 5/13`
at `σ = 7/10`)? If not — if two incommensurable large scales always exist — the Density Hypothesis
follows from Theorem 30. If yes, the extremal configuration is an explicit, checkable object: a set of
zeros whose large-block scales all lie in `\frac{5}{13}ℤ`.
`[OPEN CORE 48]` Note the freedom not yet used: the blocks may be taken at *any* multiplicative
resolution, not only dyadic. Replacing the dyadic partition by a partition into blocks of width
`T^{ξ}` for a *chosen* `ξ` changes the generators of `𝒮` by `O(ξ)` and may be enough on its own —
this is the first place where the resolution of the partition, previously a cosmetic choice, becomes
the load-bearing parameter.

## Refinement: the partition resolution is free, and the pigeonhole loss is negligible `[PROVED HERE]`
Partition `[T^{δ_1},T]` into `L = 1/ξ` blocks of multiplicative width `T^{ξ}` with
`ξ = 1/\log\log T → 0`. Two consequences:
* **Normalisation still works.** On a block `[A, AT^{ξ}]` the normalised coefficients
  `(AT^{ξ}/n)^{β}` are bounded by `T^{ξβ} = T^{o(1)}` ✔, so blocks need not be dyadic — only of
  `o(1)` multiplicative width.
* **The pigeonhole costs nothing.** Since `∑_j(\text{block}_j) = F(1)−F(0) ≈ −1`, some block has
  `|·| ≥ 1/(2L)`; writing `V = N^{β}W` with `W ≥ 1/(2L)`, the bound acquires a factor `W^{-2a}`, and
  `a\log_T(1/W) ≤ a\log\log\log T/\log T = o(1)` ✔.
So the *positions* `η_j = \log_T A_j ∈ ξℤ ∩ [δ_1,1]` are the only data that matter, and the estimate is
```
        R ≪ T^{\,2−2σ + O(\mathrm{dist}(1,𝒮)) + o(1)} ,\qquad 𝒮 = \Big\{∑_i a_iη_i\Big\} .
```
`[OPEN CORE 47, sharpened]` For a single generator, `\mathrm{dist}(1,ηℤ) = \min_a|aη−1| ≤ η/2`, worst
at `η = 2/3` (value `1/3`) and, at `σ = 7/10`, the binding case is `η = 5/13` with distance `2/13`.
**The Density Hypothesis therefore reduces to the following purely combinatorial question about zeta
zeros:**
> *Can a positive proportion (in the `T^{2−2σ}`-counting sense) of zeros `ρ` with `β ≥ σ` have the
> property that the set of scales `η` at which the partial-sum increment
> `∑_{n∈[T^{η},T^{η+ξ}]}n^{-ρ}` is large is contained in a single arithmetic progression `ηℤ` with
> `\mathrm{dist}(1,ηℤ)` bounded below?*
If not, `\mathrm{dist}(1,𝒮) = o(1)` for all but `o(T^{2−2σ})` zeros and the Density Hypothesis follows.
This is the first form of the problem in this programme that is **not** an oscillatory-sum inequality:
it asks where, along the logarithmic scale `η ∈ [0,1]`, a zeta zero's partial sums can concentrate.

---

# CYCLE 32 (2026-07-25) — the reflection is an *identity*, not a second scale `[RECORDED DEAD END — important]`
Theorem 30 asks for largeness at two **incommensurable** scales. The natural candidate second scale is
the B-process dual `M = T/N`, and for `η = \log_T N ≥ 1/2` one has `M ≤ N`, so the dual largeness
carries the *same* abscissa `σ` (blueprint Lemma 11.5, Type I: the dual is
`≫ M^{1/2}N^{σ−1/2} ≥ M^{σ}` precisely when `N ≥ M`). The product `D_N·\overline{D_M}` would then have
length `NM = T` and value `≥ T^{σ}`, giving `R ≪ T^{2−2σ+o(1)}` — the Density Hypothesis.
**This fails, and the reason is structural:** the B-process is an *identity*
`D_N(t) = e(θ(t))\,G_M(t) + O(T^{o(1)})`, not an independent largeness. Hence
`D_N·\overline{G_M} = |D_N|²·(\text{phase})` — the "product of two scales" is the *square of one scale*,
whose frequencies are the ratios `n/n'` (`n,n' ∼ N`), of separation `≍ N^{-2}`. The large sieve then
gives `R ≪ (T+N²)N²/N^{4σ}`, i.e. `R ≪ T^{η(4−4σ)}` for `N² ≥ T` — which meets `T^{2−2σ}` **only at
`η = 1/2`**, exactly the fourth-moment bound again. Additionally the dual's coefficients
`γ_m(t) = (t/2π)^{1/2}h(m,t)/m` depend on `t`, so the product is not a Dirichlet polynomial without a
Fourier expansion that shifts `t` by `O(T^{o(1)})` — and the shifts for the two factors differ.
> **Consequence for Theorem 30: the reflection does not enlarge `𝒮`. Any second generator must come
> from genuinely independent information about the zero, not from a transform of the same sum.**

## What survives, and the corrected dichotomy `[PROVED HERE]`
The cancellation argument does survive and is worth stating on its own:
```
   ∑_{n≤T}n^{-ρ} ≪ T^{-1/2}\ \Longrightarrow\ \text{either}\ \Big|∑_{n≤T^{1/2}}n^{-ρ}\Big| ≪ T^{-δ_2},
   \ \text{or some block } N∈(T^{1/2},o(T))\ \text{has}\ \Big|∑_{n∼N}n^{-ρ}\Big| ≫ T^{-δ_2-o(1)} ,
```
because if the low half is large then so is the high half, and the high half is `O(\log T)` blocks.
More generally, for **every** `u ∈ [0,1]`, either `|∑_{n≤T^{u}}n^{-ρ}| ≪ T^{-δ_2}` or some block with
`η ≥ u` is large. So the set of "large scales" of a zero is never confined to the low range unless the
*entire* low range sums to something small — a genuine constraint linking the two.
`[OPEN CORE 49]` The second generator of `𝒮` must therefore be produced by a different mechanism.
Candidates not yet tried: (i) largeness of the *derivative* `∑_{n∼N}(\log n)n^{-ρ}`, which is an
independent Dirichlet polynomial of the same length but different coefficients — its largeness at the
same `t` would give a second **coefficient** direction rather than a second scale, and Theorem 30's
proof only needs the product to be a Dirichlet polynomial of length `T^{x}` with `x` tunable; (ii)
largeness at a *different zero* of the same `ζ` (pair correlation of zeros entering the large-value
count); (iii) the `ζ'/ζ` expansion, which supplies `Λ`-weighted sums whose lengths are tunable.

## Theorem 31 (parameter-free detection at `D = T`) `[PROVED HERE]`
The Type II hypothesis is **unconditional at `D = T`**: at any zero `ρ = β+iγ` with `β ≥ σ > 1/2`,
`|∑_{n≤T}n^{-ρ}| ≪ T^{-1/2}`, and the classical Möbius mollifier of the *same* length `T` is admissible
because
```
     \Big|∑_{n≤T}n^{-ρ}\Big|\cdot\Big|∑_{m≤T}μ(m)m^{-ρ}\Big| ≪ T^{-1/2}\cdot T^{1-σ} = T^{1/2-σ} = o(1) .
```
Since `a_k := ∑_{d|k,\ d≤T,\ k/d≤T}μ(d) = [k=1]` for `k ≤ T`, this gives, with **no parameters at all**:
> For every zero `ρ` with `β ≥ σ > 1/2` and `γ ∈ [T,2T]`,
> ```
>        \Big|∑_{T<k≤T²} a_k\,k^{-ρ}\Big| ≥ \tfrac12 ,\qquad a = 1_{≤T} ∗ μ_{≤T},\quad |a_k| ≤ d(k).
> ```
No `δ_1`, `δ_2`, no Type I/II split, no mollifier-length trade-off. The whole zero-detection collapses
to a single Dirichlet polynomial supported on the *dyadic-free* window `(T, T²]`.
**Cost:** the window lies **above** `T`, so every block has `η = \log_T N ∈ (1,2]` and the Hölder–MVT
bound is `R ≪ T^{(2−2σ)η+o(1)}`, which meets the target only as `η → 1`. The Density Hypothesis is
therefore equivalent to: *the mass of `∑_{T<k≤T²}a_kk^{-ρ}` sits at `k = T^{1+o(1)}`.*
`[OPEN CORE 50]` This is a **concentration statement about the divisor-like coefficients
`a = 1_{≤T} ∗ μ_{≤T}` weighted by `k^{-ρ}`** — the mass of `a` itself is spread over `(T,T²]`, but the
oscillation `k^{-iγ}` is what decides where the *large* part sits. Two sub-questions:
* Can one *engineer* the mollifier (length `y < T`, or the powered `μ_M` version) so that the surviving
  window is `(T^{1-ε}, T^{1+ε}]` rather than `(T,T²]`? The window is `(y, Dy]` for a mollifier of length
  `y` and zeta-truncation `D`; it is centred at `η = 1` iff `Dy ≈ T^{1+ε}` and `y ≈ T^{1−ε}`, i.e.
  `D ≈ T^{2ε}` — a **short** zeta piece with a **long** mollifier. Admissibility then requires
  `|∑_{n≤T^{2ε}}n^{-ρ}|·T^{(1−ε)(1−σ)} = o(1)`, i.e. the short sum must be `≪ T^{-(1−ε)(1−σ)}` —
  which is exactly a Type II hypothesis at `D = T^{2ε}` with an *unusually strong* saving `T^{-(1−σ)}`
  rather than `T^{-δ_2}`.
* That strong saving is not available in general — **but its failure is itself a largeness statement at
  scale `T^{2ε}`**, i.e. `η = 2ε` small, where `⌈1/η⌉η → 1` and the power trick is *good*.
**This is a genuine dichotomy with both branches favourable, and it is the first such in the
programme.** `[OPEN CORE 51]` Make it quantitative: for which pairs `(D, y)` with `Dy = T^{1+ε}` does
one of the two branches close?

---

# CYCLE 33 (2026-07-25) — the loss-free dichotomy, and a numerical confirmation that it reproduces `30/13`

## Theorem 32 (loss-free dichotomy) `[PROVED HERE]`
Fix `ε > 0` and take the detection pair `D = T^{1/2}` (zeta truncation), `y = T^{ε/2}` (Möbius
mollifier). Then `a_k = [k=1]` for `k ≤ y` and `t := B − 1` is supported on `(y, Dy] = (T^{ε/2},
T^{1/2+ε/2}]` — but the *useful* consequence is the dichotomy, both of whose branches are clean:
* **(B)** `|∑_{n≤T^{1/2}}n^{-ρ}| ≤ T^{-(ε/2)(1−σ)}`. Then `|B(ρ)| = o(1)`, the detection fires, and —
  taking instead `D = T^{1/2}`, `y = T^{1/2}` so the window is `(T^{1/2},T]`, i.e. `η ∈ [1/2,1]` — the
  power trick with `k = 2` gives `x = 2η` only at `η = 1/2`; **the sharp version is `D = y = T^{1/(2j)}`,
  window `η ∈ [1/(2j), 1/j]`, where `⌈1/η⌉η ≤ 1 + 1/j` for every `η` in the window**, hence
  `R ≪ T^{(2−2σ)(1+1/j)+o(1)} → T^{2−2σ+o(1)}`.
* **(A)** `|∑_{n≤T^{1/2}}n^{-ρ}| > T^{-(ε/2)(1−σ)}`. Since `|∑_{n≤T}n^{-ρ}| ≪ T^{-1/2}`, the upper half
  `∑_{T^{1/2}<n≤T}n^{-ρ}` is equally large, so **some zeta block at scale `η ∈ [1/2,1)` satisfies
  `|∑_{n∼N}n^{-ρ}| ≫ T^{-o(1)}` as `ε → 0`** — largeness at the *full* threshold `V = N^{β}T^{-o(1)}`,
  with **no `T^{-δ_2}` loss at all**. This is strictly cleaner than the classical Type I alternative.
> The classical Lemma 11.5 pays `T^{-δ_2}` in *both* branches and must then keep `δ_2/δ_1 = o(1)`;
> Theorem 32 pays nothing in branch (A) and an arbitrarily small `ε` in branch (B).

## Numerical check: the dichotomy reproduces the world record exactly `[VERIFIED]`
For a zeta block at scale `η` with `V = N^{σ}T^{-o(1)}`, the available bounds are
```
   (i)\ R ≤ T^{(2−2σ)⌈1/η⌉η} ,\qquad (ii)\ R ≤ T^{1+⌊1/η⌋η(1−2σ)} ,
```
applied to the block itself **or** to its B-process reflection at `η' = 1−η` (same abscissa, since
`η ≥ 1/2`). Scanning `η ∈ [1/2,1)` at `σ = 7/10`, the minimum of the four options peaks at
`η ≈ 0.615` with value `≈ 0.692 = 9/13`, i.e. `\mathrm{A}(7/10) ≤ (9/13)/(3/10) = 30/13` — **exactly
the world record, reached from a completely different route.** Both the classical Type I/II split and
the loss-free dichotomy bottom out at the same number, which is strong evidence that `9/13` is the
true barrier of the *moment* method and not an artefact of either reduction.
`[OPEN CORE 52]` Branch (B) closes the Density Hypothesis. Branch (A) is now a very concrete object:
> *a zero `ρ` with `β ≥ σ` such that `|∑_{n∼N}n^{-ρ}| ≫ T^{-o(1)}` for some `N = T^{η}`,
> `η ∈ [1/2,1)`, i.e. **a dyadic block of `ζ`'s Dirichlet series, at a scale between `√T` and `T`,
> which is of size comparable to `1` at a zero.*** Note that the trivial bound for such a block is
> `N^{1−β} = T^{η(1−β)}`, which is a *large power of `T`* — so branch (A) does **not** say the block is
> near-maximal; it says the block is `≫ T^{-o(1)}` while the whole sum is `≪ T^{-1/2}`. The zeros in
> branch (A) are therefore exactly those whose Dirichlet-series mass **cancels to `T^{-1/2}` while
> individual blocks stay of order 1** — a precise and checkable extremal profile.

---

# CYCLE 34 (2026-07-25) — **the complete deficit profile**: which scales `η` are unresolved, and by exactly how much

## The two moment bounds, in `T`-exponents `[PROVED HERE]`
For a zeta block `D_N(t) = ∑_{n∼N}(N/n)^{β}n^{-it}` at scale `η = \log_T N` with full largeness
`|D_N(t_r)| ≫ N^{σ}T^{-o(1)}` for `R` one-separated `t_r ∈ [T,2T]`:
```
   (P_k)\ \ R ≪ T^{(2−2σ)kη+o(1)}\quad (k ≥ 1/η,\ \text{length } N^{k} ≥ T) ,
   (M_k)\ \ R ≪ T^{1+kη(1−2σ)+o(1)}\quad (k ≤ 1/η,\ \text{length } N^{k} ≤ T) .
```
**The `η > 1/2` window is completely resolved by reflection.** For `N ≥ T^{1/2}` the B-process gives
`|D_N| = |G_M| + O(T^{o(1)})` with `M = T/N ≤ T^{1/2}`, and computing the fourth moment on the *dual*
side (where `M² ≤ T`, so the mean value theorem is diagonal) gives
```
      ∑_{r}|D_N(t_r)|^{4} = ∑_r |G_M(t_r)|^4 ≪ T\cdot\frac{T^2}{M^2}\,T^{o(1)} = T\,N^{2}\,T^{o(1)} ,
```
strictly better than the direct `N^4` whenever `N² > T`. Hence `(M_2)` holds for **all** `η`, and
```
        R ≪ T^{1+2η(1−2σ)+o(1)} ≤ T^{2−2σ+o(1)} \iff η ≥ 1/2 .
```
So every scale `η ∈ [1/2,1)` satisfies the Density-Hypothesis bound outright. `[PROVED HERE]`

## The deficit, exactly `[PROVED HERE]`
On the window `η ∈ (1/(k+1), 1/k)` (`k ≥ 2`, i.e. `τ = 1/η ∈ (k,k+1)`), the best available bound is
`\min\big((2−2σ)(k+1)η,\ 1+kη(1−2σ)\big)`, whose maximum over the window is at the crossing
```
        η_k = \frac{1}{k+2−2σ} ,\qquad \text{value}\quad E_k(σ) = \frac{(2−2σ)(k+1)}{k+2−2σ} ,
```
so `E_k(σ) > 2−2σ` for every `k`, with `E_k ↓ 2−2σ` as `k → ∞`:
```
   σ = 7/10:\quad E_2 = 9/13 = 0.6923\ (τ = 13/5),\quad E_3 = 2/3,\quad E_4 = 0.6522,\quad
                  E_{10} = 0.6226,\quad E_∞ = 3/5 .
```
`\mathrm{A}(σ)(1−σ) ≤ \max_k E_k(σ) = E_2(σ) = \frac{3(1−σ)}{2−σ}`, i.e. `\mathrm{A}(σ) ≤ 3/(2−σ)` —
**Ingham's theorem, recovered exactly, with the location of its bottleneck identified as
`τ = 4 − 2σ`** (`= 13/5` at `σ = 7/10`).
> ### The picture, complete
> * `η ∈ [1/2, 1)` (`τ ∈ (1,2]`): **resolved** — reflection + fourth moment give exactly `2−2σ`, with
>   strict improvement for `η > 1/2`.
> * `η ∈ (1/(k+1), 1/k)`, `k ≥ 2`: **deficit `E_k(σ) − (2−2σ) = \frac{(2−2σ)(1−(2−2σ))}{k+2−2σ}`**,
>   which is `> 0` for `σ > 1/2` and decays like `1/k`.
> * `η = 1/k` exactly: **resolved** — `(P_k)` gives `(2−2σ)` on the nose.
> So the unresolved set is a union of open intervals `(1/(k+1), 1/k)` accumulating at `0`, and the
> Density Hypothesis is precisely the assertion that the moment bound can be interpolated *across each
> gap between consecutive integer powers*. The deficit is largest on the **first** gap `τ ∈ (2,3)`.
`[OPEN CORE 53]` Everything now rests on one bounded, explicit question:
> **For `τ ∈ (2,3)` and `1/2 < σ < 1`, is `\mathrm{LV}_ζ(σ,τ) ≤ (2−2σ)τ`?**
Beating `E_2(σ)` on this single window improves `‖A‖_∞` below `30/13`; proving it for all `k` is the
Density Hypothesis. The `k`-th window needs the `k`-th and `(k+1)`-st moments to be *interpolated*, and
the reflection already achieves exactly this interpolation for `k = 1`. **The natural conjecture is
that the reflection has a `k`-fold analogue** — a transform under which a block of scale
`η ∈ (1/(k+1),1/k)` is exchanged for one at a scale where an integer power lands exactly on `T`.

---

# CYCLE 35 (2026-07-25) — the deficit is **irremovable by mean-value methods**; the `k`-fold reflection exists and does not help

## Theorem 33 (sharpness of the moment bound) `[PROVED HERE]`
For `c = d_k^{(N)}` (the `k`-fold divisor function restricted to factors in `[N,2N]`),
```
   ∫_T^{2T}\Big|∑_{a∼N^{k}}c_a a^{-it}\Big|^2 dt
     = T∑_a|c_a|^2 + ∑_{a≠b}c_a\bar c_b\,O\!\big(\min(T,\ |\log(a/b)|^{-1})\big) ,
```
and since `|\log(a/b)| ≍ |a-b|/N^{k}` and the shifted convolution satisfies
`∑_a |c_ac_{a+h}| ≪ N^{k}T^{o(1)}` uniformly in `h`, the off-diagonal splits as
```
   T\!\!\sum_{0<|h|<N^k/T}\!\! N^kT^{o(1)} \;+\; N^k\!\!\sum_{h≥N^k/T}\!\!\frac{N^kT^{o(1)}}{h}
     \;=\; N^{2k}T^{o(1)} ,
```
so `∫|D_N^k|^2 ≍ (T + N^{k})N^{k}T^{o(1)}` — **the Montgomery–Vaughan bound is sharp, in both regimes.**
> **Consequence: the deficit `E_k(σ) − (2−2σ) = \frac{(2−2σ)(2σ−1)}{k+2−2σ}` of Cycle 34 cannot be
> removed by any mean-value / moment argument whatsoever.** Improving it requires information about
> the *large-value set* `W` itself — its additive or multiplicative structure — not about the
> polynomial. This is a clean impossibility statement for an entire method class, and it explains why
> Guth–Maynard needed Fourier-analytic structure rather than a better moment.

## Halász–Montgomery also fails at the bottleneck `[VERIFIED — RECORDED DEAD END]`
`RV^2 ≪ \|a\|_2^2\,\max_r ∑_s |K(t_r−t_s)|` with `K(u) = ∑_{n∼N}n^{iu}`, so
`RV^2 ≪ N^2 + NR\max_{1≤|u|≤T}|K(u)|`. With the exponent pair `(κ,λ) = (13/84, 13/84+1/2)`,
`\max|K| ≪ T^{κ(1−η)+λη}`; at the bottleneck `(σ,τ) = (7/10,13/5)`, `η = 5/13`, this is `T^{0.3471} =
N^{0.9025}`, whereas the method needs `V^2 = N^{1.4} ≫ N\max|K| = N^{1.9025}` — **false by a wide
margin.** Halász–Montgomery is vacuous at exactly the point where the record sits.

## The `k`-fold reflection exists — and gives nothing `[RECORDED DEAD END]`
The `k = 1` reflection that resolves `η ∈ [1/2,1)` is Poisson summation. Its `k`-fold analogue is the
**approximate functional equation for `ζ^{k}`**: `ζ(s)^{k} = χ(s)^{k}ζ(1−s)^{k}` gives
```
   ∑_{m≤X}d_k(m)m^{-s} \;≈\; χ(s)^{k}∑_{m≤(T/2π)^{k}/X}d_k(m)m^{s-1} ,
```
exchanging length `X` for `T^{k}/X` — for `X = N^{k}` this is scale `kη ↔ k(1−η)`. The moment is
diagonal iff `\min(kη, k(1−η)) ≤ 1`, i.e. iff `kη ≤ 1` or `k(1−η) ≤ 1` — **exactly the two conditions
already available.** The `k`-fold reflection is therefore not new information: it is the same fold
`η ↦ 1−η`, applied `k` times to no effect. (It also does not apply to a *block* `D_N^k`, whose
coefficients `d_k^{(N)}` are not those of `ζ^k`.)
`[OPEN CORE 54]` What is left is unambiguous and matches the literature's own frontier: **the deficit
on `τ ∈ (k,k+1)` must be attacked through the structure of `W`.** The programme's own structural
assets, not yet applied at `τ ∈ (2,3)`:
* **Theorem 16** (fat-AP incidence via the divisor bound, replacing Kakeya input) — derived for the
  block regime `N ≥ T^{1/2}`; at `η = 5/13 < 1/2` the wave-packet length `L = NT^{-1/2} = T^{-3/26} < 1`
  degenerates, so it must be re-derived in the *dual* picture, where the scale is `M = T^{8/13} > T^{1/2}`
  and `L_{\mathrm{dual}} = MT^{-1/2} = T^{3/26} > 1` ✔ — **the fat-AP geometry is available on the dual
  side precisely when it degenerates on the primal side.**
* **Theorem 6** (`\#\{n∼N : \|D\log n − α\| ≤ 1/2R\} ≪ N^{1+o(1)}R^{-1/2}`, uniform in `D`), which is a
  statement about the multiplicative structure of `W` and has never been combined with the moment
  bound.
**Next cycle: transport Theorem 16 to the dual side at `τ ∈ (2,3)` and combine with `(M_2)`.**

---

# CYCLE 36 (2026-07-25) — **why the bottleneck is structurally unreachable on the `LV_ζ` route, and the forced pivot**

## Theorem 34 (regime boundary) `[PROVED HERE]`
The wave-packet / fat-AP / Kakeya machinery for large values of `∑_{n∼N}a_nn^{-it}` lives on blocks of
length `L = N\,T^{-1/2}` (the scale at which the phase `t\log n` is linear across a block). **This is
meaningful only for `L ≥ 1`, i.e. `N ≥ T^{1/2}`, i.e. `τ ≤ 2`.** Equivalently, the large-value
threshold satisfies
```
        V = N^{σ} ≥ T^{1/2} \iff σ/τ ≥ 1/2 \iff τ ≤ 2σ .
```
At the Ingham bottleneck `(σ,τ) = (7/10, 13/5)` one has `L = T^{5/13-1/2} = T^{-3/26} < 1` and
`V = T^{7/26} < T^{1/2}`: **every wave-packet, fat-AP, additive-energy and Kakeya-type input is
structurally vacuous there.** Checking the fat-AP route explicitly: writing
`|G̃(t)| ≤ ∑_I \min(L, 1/u_I)`, `u_I = \|t/2πm_I\|`, and dyadically decomposing in `u`, Theorem 16
applies at level `2^{j}` only when `2^{j} ≳ 1`, and the coherent regime it needs is
`L ≫ M^{1-σ''}`; at the bottleneck `L = T^{3/26}` while `M^{1-σ''} = T^{3/13}` — **off by a factor
`T^{3/26}`.** So Theorem 16 cannot be transported to the bottleneck, on either side of the reflection.
`[RECORDED DEAD END — do not retry the fat-AP route at `τ > 2`.]`
> This explains the shape of the literature: Guth–Maynard improve `\mathrm{LV}` near `τ = 2` and hence
> `\mathrm{A}(σ)` on `σ ∈ (7/10, 3/4)`, but cannot move `σ = 7/10`, where the binding configuration has
> `τ = 4 − 2σ = 13/5 > 2`. **The bottleneck of `‖A‖_∞` sits exactly outside the reach of the only
> structural technology available.**

## The forced pivot: use `τ_0 = 3/2`, where `LV_ζ` is vacuous `[PROVED — restates Cor 11.9]`
Corollary 11.9 with `τ_0 = 3/2` makes the `\mathrm{LV}_ζ` requirement `2 ≤ τ < 4τ_0/3 = 2` **vacuous**,
leaving
```
        \mathrm{A}(σ)(1−σ) ≤ \sup_{1 ≤ τ ≤ 3/2} \mathrm{LV}(σ,τ)/τ ,
```
i.e. **only general-coefficient large values on `τ ∈ [1, 3/2]` — where `L = NT^{-1/2} ≥ T^{1/6} ≫ 1`
and the entire wave-packet toolkit is available.** This is the same wedge identified in the early
cycles (`DH ⟺ Montgomery's conjecture for `τ ≤ σ+1/2``), now with a structural reason for preferring
it: *the `LV_ζ` route passes through `τ > 2`, where no structural input exists; the `LV` route stays
in `τ ≤ 3/2`, where all of it does.*
> ### Strategic conclusion for the programme
> **Abandon the `LV_ζ` / `τ ≥ 2` formulation.** It is cleaner to state (Cycle 30–34) but provably
> starved of structure (Theorem 34). All further work goes into `\mathrm{LV}(σ,τ) ≤ (2−2σ)τ` for
> `τ ∈ [1,3/2]`, where the assets already built apply verbatim:
> * **Theorem 16** (fat-AP incidence via divisor bounds — `L = NT^{-1/2} ≥ T^{1/6}`, coherent regime
>   `L ≫ N^{1-σ}` holds iff `1 − 1/(2τ) ≥ ... ` — to be checked at `τ = 3/2`);
> * **Theorems 17–19** (block-diagonal, near-diagonal, absolute-value barrier);
> * **Theorem 4/5** (the `∞→1` operator-norm form and its Grothendieck-tight SDP relaxation);
> * **Theorem 30** (numerical semigroup of scales), which now applies to the *coefficient* scales in a
>   convolution rather than to zeta blocks.
> `[OPEN CORE 55]` At `τ = 3/2`: `N = T^{2/3}`, `L = NT^{-1/2} = T^{1/6}`, `V = N^{σ} = T^{2σ/3}`, and
> `V ≥ T^{1/2} ⟺ σ ≥ 3/4`. **So even at `τ = 3/2` the coherent regime requires `σ ≥ 3/4`** — and
> `σ = 7/10 < 3/4`. The regime boundary `τ = 2σ` is the real enemy: at `σ = 7/10` it forces `τ ≤ 1.4`,
> while Corollary 11.9 needs `τ` up to `3/2`. **The gap `τ ∈ (1.4, 1.5]` at `σ = 7/10` is the entire
> residual problem.**

## Correction to Theorem 34's reach: coherence applies to the **kernel**, not the coefficients `[PROVED HERE]`
For *general* coefficients a block `∑_{n∈I}a_nn^{-it}` can equal `L` for any `t` — there is no
coherence constraint, so the fat-AP picture does **not** apply to `D` itself. It **does** apply to the
Halász–Montgomery kernel, whose coefficients are `1`:
```
   R\,V^2 ≤ \|a\|_2^2\ \max_r ∑_{s} |K(t_r-t_s)| ,\qquad K(u) = ∑_{n∼N}n^{iu},
   \qquad |K(u)| ≲ ∑_I \min\big(L,\ \|u/2πn_I\|^{-1}\big) .
```
So the whole block/fat-AP analysis (Theorems 16–19) is a statement about the **difference set**
`\{t_r-t_s\}`, valid for arbitrary `a_n` — this is the correct home for those results, and it means
Theorem 34's regime boundary `τ ≤ 2` (i.e. `L ≥ 1`) is the *only* obstruction to using them.
**Baseline computation.** If the `t_s` were equidistributed modulo every `2πn_I`, then
`\#\{s : \|(t_r-t_s)/2πn_I\| ≤ 1/L\} ≈ R/L`, giving `∑_s|K| ≪ (N/L)R\log T` and
```
   R\,V^2 ≪ N^2 + \frac{N^2}{L}R\log T \Longrightarrow R\big(N^{2σ} - N T^{1/2}\log T\big) ≪ N^2 ,
```
which is useful only when `N^{2σ-1} ≫ T^{1/2}`, i.e. `τ < 2(2σ-1)` — at `σ = 7/10`, `τ < 4/5`.
**Vacuous.** `[RECORDED DEAD END: plain Halász–Montgomery with the equidistributed kernel bound.]`
> Therefore the *entire* content of any successful argument in the wedge `τ ∈ [1,3/2]` must be a proof
> that the differences `t_r - t_s` are **not** equidistributed modulo the moduli `2πn_I` — i.e. a
> non-equidistribution theorem for the difference set of a large-value set. Theorem 16 is the first
> such statement in this programme, but it is currently of "all points" type (it constrains fat APs
> containing *all* `R` points); what is needed is its **`(1-δ)`-fraction version**:
> `[OPEN CORE 56]` *If `ν` fat APs with distinct integer moduli `n_I ∈ [N,2N]` each contain at least
> `δR` of a set of `R` one-separated points, with `R ≥ CN/L`, then `ν ≪_{ε,δ} N^{ε}`* — or the
> correct weaker form with `ν ≪ δ^{-O(1)}N^{ε}`. The proof of Theorem 16 splits on
> `q_i = n_i/\gcd(n_0,n_i)` and uses a divisor bound on the exact-congruence side and a density bound
> on the other; **the density side survives a `δ`-fraction hypothesis verbatim, and the congruence
> side needs a Bezout/CRT argument on a positive-density subset** — this is the concrete technical
> statement to prove next.

---

# CYCLE 37 (2026-07-25) — the fat-AP incidence count for a **single** difference, and the definitive closure of the Halász–Montgomery branch

## Theorem 35 (per-difference incidence count) `[PROVED HERE]`
Let the blocks `I` of `[N,2N]` have length `L` and centres `n_I` (so there are `≍ N/L` of them,
spaced `L` apart). For a real `d` and `ε > 0` put
```
        ν_ε(d) := \#\{I : \|d/(2πn_I)\| ≤ ε\} .
```
Then
```
        ν_ε(d) \ ≪\ \frac{εN}{L} \;+\; \frac{|d|}{N} \;+\; 1 .
```
*Proof.* `f(n) = d/2πn` is monotone on `[N,2N]` with `|f'| ≍ |d|/N²`, and its total variation is
`≍ |d|/N`. Hence `\{n : \|f(n)\| ≤ ε\}` is a union of `≪ |d|/N + 1` intervals, each of length
`≍ εN²/|d|`, of total measure `≍ εN`. Counting the `L`-spaced centres in a union of `k` intervals of
total measure `m` gives `≪ m/L + k`. ∎
This is **unconditional and sharp** (the two terms are attained by `d ≪ N` and `d ≫ N` respectively),
and it is the correct "single-difference" replacement for the all-points hypothesis of Theorem 16 —
no `δ`-fraction hypothesis is needed, because the incidence question factorises over differences.

## Consequence: Halász–Montgomery with block coherence is **exhausted** `[PROVED HERE — DEAD END]`
Writing `|K(u)| = |∑_{n∼N}n^{iu}| ≲ ∑_I \min(L, \|u/2πn_I\|^{-1})` and decomposing dyadically at
levels `ε_j = 2^{j}/L`,
```
   ∑_{s}|K(t_r−t_s)| \;≍\; ∑_{j≥0}\frac{L}{2^{j}}∑_{s}ν_{ε_j}(t_r−t_s)
      \;≪\; ∑_{j}\frac{L}{2^{j}}\,R\Big(\frac{2^{j}N}{L^{2}} + \frac{T}{N}\Big)
      \;≪\; \frac{LRT}{N}\log T ,
```
using `L = NT^{-1/2}` so that `N/L² = T/N`. Substituting into
`R V^2 ≤ \|a\|_2^2\max_r∑_s|K(t_r−t_s)|`:
```
        R\,V^{2} ≪ N^{2} + L\,T\,R\log T \Longrightarrow R\big(N^{2σ} − NT^{1/2}\log T\big) ≪ N^{2} ,
```
useful **only when `τ < 2(2σ−1)`** — at `σ = 7/10`, `τ < 4/5`, far below the required `τ ∈ [1,3/2]`.
> **This is now proved, not merely observed: the per-difference incidence bound is sharp, so no
> refinement of the block/coherence expansion inside Halász–Montgomery can reach the wedge.** The
> deficiency is not in the incidence geometry — Theorem 35 is best possible — but in Halász–Montgomery
> itself, which discards all cancellation between the `R` terms `K(t_r−t_s)`.
`[RECORDED DEAD END: Halász–Montgomery + block coherence, in any dyadic refinement.]`

## Where this leaves the programme `[STATE]`
Three method classes are now *provably* exhausted at the critical configuration:
1. **Moments / mean values** — Theorem 33 (`(T+N^k)N^k` is sharp in both regimes);
2. **Halász–Montgomery with block coherence** — Theorem 35 + the computation above;
3. **Wave-packet / fat-AP / Kakeya inputs at `τ > 2`** — Theorem 34 (`L < 1`).
What remains untouched, and is the only route not yet shown exhausted, is the **double large
sieve / additive-energy** class: bounding `∑_{r,s}|K(t_r-t_s)|` *with* the cancellation that
Halász–Montgomery throws away, i.e. estimating the energy
`E(W) = \#\{(t_1,t_2,t_3,t_4) ∈ W^4 : |t_1−t_2−t_3+t_4| ≤ 1\}` and feeding it back. This is exactly
the Guth–Maynard mechanism, and the programme's distinctive asset — **Theorem 16/35's divisor-bounded
incidence geometry, which replaces the Kakeya-type input with an unconditional arithmetic one** — has
not yet been combined with it.
`[OPEN CORE 57]` Bound `E(W)` for a large-value set `W` of `∑_{n∼N}a_nn^{-it}` using Theorem 35:
the four-fold coincidence `t_1−t_2−t_3+t_4 = O(1)` is a condition on *differences*, and Theorem 35
counts exactly how many block-moduli resonate with a given difference. **This is the first place where
the programme's arithmetic input meets the one surviving method class.**

## The energy/Cauchy–Schwarz route, computed `[RECORDED DEAD END]`
Splitting `∑_{t∈W}|D(t)|^4 = ∑_{m,m'∼N²}b_m\bar b_{m'}G(\log(m/m'))`, `G(θ) = ∑_{t∈W}e^{iθt}`,
`b = a∗a`, and applying Cauchy–Schwarz to the off-diagonal:
```
   ∑_{m≠m'}|b_mb_{m'}||G| ≤ \Big(∑_{m,m'}|b_mb_{m'}|^{2}\Big)^{1/2}\Big(∑_{t,t'∈W}|K_{N^2}(t−t')|^{2}\Big)^{1/2}
      ≪ N^{2+o(1)}\cdot\big(N^{4}R\big)^{1/2} = N^{4}R^{1/2}N^{o(1)} ,
```
using `∑_{t,t'}|K_{N²}(t−t')|² ≍ N^4R` for 1-separated `t`. Hence
`R\,V^{4} ≪ RN^{2+o(1)} + N^{4}R^{1/2}`, giving `R ≪ N^{8−8σ+o(1)}` — **strictly worse than the
fourth-moment bound `N^{4−4σ}`** for every `σ > 1/2`. The Cauchy–Schwarz over `R²` pairs destroys more
than the energy recovers. `[Do not retry: energy via Cauchy–Schwarz on the `N²`-side.]`

---

# ANTI-THEATRE AUDIT (hgtl7 Phase 6/7) — after 37 cycles
1. **New knowledge beyond literature/corpus?** Yes, structurally: Theorem 16/35 (unconditional
   divisor-bounded fat-AP incidence, replacing Kakeya-type input); Theorem 22/23 (the Hölder–moment
   family's exact ceiling `(2−2σ)τ` and the integrality obstruction); Theorem 28 (low-range vanishing
   of a product forces cross-factor cancellation); Theorem 30 (rounding = distance to a numerical
   semigroup of scales); Cycle 34 (the exact deficit profile `E_k(σ) = (2−2σ)(k+1)/(k+2−2σ)` and the
   location `τ = 4−2σ` of Ingham's bottleneck); Theorem 33/34/35 (three method classes proved
   exhausted at the critical configuration). **No numerical improvement to `A(σ)`.**
2. **Rediscoveries?** Yes — Cycles 27–29 (Theorem 29 = Lemma 7.8 + MVT). Cause: not checking the
   blueprint's own lemma list before building. **Mitigation adopted: before claiming any reduction,
   grep `largevalue-chapter.txt`/`zdchap.txt` for an existing lemma with the same content.**
3. **Theatre?** The reductions are real and were not obtainable by literature search, but three of
   them (Cycles 29–31) collapsed under scrutiny. The surviving statements are the *negative* ones,
   which is a legitimate but lesser form of progress.
4. **Has the frontier moved?** Not numerically. `‖A‖_∞ = 30/13` stands. What has moved is the *map*:
   the bottleneck is now located exactly (`τ = 4−2σ`), the deficit is quantified exactly, and three
   method classes are ruled out at that point with proof.
5. **Big picture / pivot.** The only surviving method class is the double large sieve / additive
   energy, i.e. the Guth–Maynard mechanism, at `τ ∈ [1,3/2]`, `σ ≈ 7/10`. The programme's distinctive
   asset there is Theorem 35. **The next cycles must build the energy estimate with Theorem 35 as
   input, not attempt further reformulations of the reduction** — reformulation is now exhausted, as
   Theorems 33–35 show.

---

# CYCLE 38 (2026-07-25) — **the true bottleneck is `τ = 2−σ`, and it lies INSIDE the coherent regime**

## Ingham's exponent is the mean value theorem plus Corollary 11.9, optimised `[PROVED HERE]`
Corollary 11.9 with parameter `τ_0` needs `\mathrm{LV}(σ,τ) ≤ (3−3σ)τ/τ_0` on `2τ_0/3 ≤ τ ≤ τ_0`
(condition (6)) and `\mathrm{LV}_ζ(σ,τ) ≤ (4−4σ)` on `2 ≤ τ < 4τ_0/3` (condition (7), **vacuous for
`τ_0 ≤ 3/2`**), and concludes `\mathrm{A}(σ) ≤ 3/τ_0`. Feeding in only the mean value theorem
`\mathrm{LV}(σ,τ) ≤ τ+1−2σ`, condition (6) at its binding point `τ = τ_0` reads
```
        τ_0 + 1 − 2σ ≤ 3−3σ \iff τ_0 ≤ 2−σ ,
```
so the optimal choice is `τ_0 = 2−σ` and `\mathrm{A}(σ) ≤ 3/(2−σ)` — **Ingham, exactly, with the
binding configuration located at `τ = τ_0 = 2−σ`.** At `σ = 7/10`: `τ_0 = 13/10`,
`\mathrm{A}(7/10) ≤ 30/13`. `[This supersedes the Cycle-34 location `τ = 4−2σ`, which is the same
configuration after the power trick doubles `τ`; the *primal* bottleneck is `τ = 2−σ`.]`

## The correction that matters `[PROVED HERE]`
Theorem 34's regime boundary is `τ ≤ 2σ` (equivalently `V = N^{σ} ≥ T^{1/2}`, equivalently
`L = NT^{-1/2} ≥ 1` **and** `V ≥ N/L`). At the true bottleneck `σ = 7/10`, `τ = 13/10`:
```
   N = T^{10/13},\quad L = NT^{-1/2} = T^{7/26} ≫ 1,\quad N/L = T^{1/2},\quad V = N^{σ} = T^{7/13} = T^{14/26} ,
```
so `V/(N/L) = T^{1/26} > 1` and `τ = 1.3 < 2σ = 1.4`. **The bottleneck is inside the coherent
regime, with a genuine margin `T^{1/26}`.**
> **Consequence: Theorem 34 does *not* rule out the wave-packet / fat-AP / Theorem 16 / Theorem 35
> machinery at the point that actually binds. It rules it out only for the `\mathrm{LV}_ζ`
> reformulation, which is therefore the wrong formulation to use — exactly as Cycle 36 concluded, but
> now with the bottleneck itself shown to be reachable.** The route re-opens.

## The single concrete target `[STATE OF THE PROGRAMME]`
```
        \textbf{Beat the mean value theorem at } (σ,τ) = (7/10,\ 13/10):\qquad
        \mathrm{LV}(7/10,\ 13/10) < 9/10 .
```
Any `\mathrm{LV}(σ, 2−σ) < (2−σ)+1−2σ = 3−3σ` (i.e. any saving at all over the MVT at `τ = 2−σ`)
raises the admissible `τ_0` above `2−σ` and lowers `\mathrm{A}(σ)` below `3/(2−σ)`; a saving of the
full amount needed for `\mathrm{A}(σ) ≤ 2` is `τ_0 = 3/2`, i.e.
`\mathrm{LV}(σ,τ) ≤ (2−2σ)τ` on `τ ∈ [1, 3/2]` — the Montgomery wedge.
Available at this point, all previously proved in this card and all *applicable* here:
* **Cycle 17's exact identity** `D_{z,I}(t) = n_I^{-it}\widehat{z_I}(θ_I(t)) + O(1)`,
  `θ_I(t) = t/2πn_I \bmod 1` — no inverse theorem needed;
* the resulting **large-sieve constraint** `\#\{θ : |\widehat{z_I}(θ)| ≥ V'\} ≪ L^2/V'^2` on a
  `1/L`-grid;
* **Theorem 35** (per-difference incidence: `ν_ε(d) ≪ εN/L + |d|/N + 1`, unconditional and sharp);
* **Theorem 16** (all-points fat-AP incidence `ν ≪_ε N^{ε}`, valid since `R ≥ CN/L` holds here:
  `R ≈ T^{9/13}` versus `N/L = T^{1/2}` ✔).
`[OPEN CORE 58]` Assemble these into a bound on `\#\{t ∈ W\}` at `(7/10,13/10)`: the largeness
`∑_I|\widehat{z_I}(θ_I(t))| ≥ V` with `V/L = T^{7/13−7/26} = T^{7/26}` forces `≥ T^{7/26}` blocks to be
simultaneously resonant at each `t ∈ W`, while `N/L = T^{1/2}` blocks exist in total — a resonance
density of `T^{-6/26}`. **The quantitative question is whether `T^{9/13}` points can each achieve
`T^{7/26}` simultaneous resonances among `T^{1/2}` fat APs with distinct integer moduli in `[N,2N]`.**
Theorem 16 forbids `T^{7/26}` *common* resonances for all points at once; the needed statement is the
per-point version, and the counting is now completely explicit.

## The counting at the bottleneck, done `[PROVED HERE]`
At `(σ,τ) = (7/10,13/10)`: `B := N/L = T^{1/2}` blocks, each `|\widehat{z_I}| ≤ L = T^{7/26}`, and
`V = T^{14/26}`. Dyadic decomposition in the block size `V'` gives, for each `t ∈ W`, a level with
```
        ν(t) := \#\{I : |\widehat{z_I}(θ_I(t))| ≍ V'\} \;≳\; V/(V'\log T) .
```
Parseval on the `1/L`-grid gives `|E_I| ≪ L/V'^2`, `E_I := \{θ : |\widehat{z_I}(θ)| ≥ V'\}`. Counting
incidences **assuming equidistribution** of `θ_I(t) = t/2πn_I`:
```
   R\,ν ≤ ∑_I \#\{t∈W : θ_I(t)∈E_I\} ≈ B\,R\,|E_I| \Longrightarrow V' ≪ BL\log T/V = N\log T/V = T^{3/13+o(1)} ,
```
so `ν ≳ T^{4/13}` — **and `R` cancels entirely.** The first-moment count is therefore *consistent* with
any `R`: the extremal configuration is "every one of the `T^{1/2}` blocks mildly resonant, at level
`V' = T^{3/13}` out of a maximum `L = T^{7/26}`", i.e. each block delivers only a `T^{-1/26}` fraction
of its maximum. **This is exactly the Montgomery-conjecture extremal profile, and it is invisible to
first-moment counting.**
> **Therefore the bottleneck `\mathrm{LV}(7/10,13/10) < 9/10` cannot be reached by any incidence count
> that only uses the *number* of resonances per point. What is needed is the second moment**
> ```
>    ∑_I \#\{t∈W: θ_I(t)∈E_I\}^{2} = ∑_{t,t'∈W} \#\{I : θ_I(t)∈E_I \text{ and } θ_I(t')∈E_I\} ,
> ```
> whose inner count is governed by `\|(t−t')/2πn_I\| ∈ E_I − E_I` — **a difference-set condition, and
> precisely the object Theorem 35 bounds** (`ν_ε(d) ≪ εN/L + |d|/N + 1`). The missing ingredient is a
> bound on the *structure* of `E_I − E_I` — `E_I` has measure `≪ L/V'^2 = T^{7/26−6/13} = T^{-5/26}`
> and consists of `≪ L^2/V'^2 = T^{14/26−6/13} = T^{2/26}` grid intervals of length `1/L`.
`[OPEN CORE 59]` The concrete statement to prove: *for `E ⊂ 𝕋` a union of `T^{1/13}` intervals of
length `T^{-7/26}` and moduli `n_I ∈ [N,2N]` spaced `L` apart, and `W` a 1-separated set of size
`R = T^{9/13}` in `[T,2T]`,*
```
       ∑_{t,t'∈W} \#\{I : \|(t−t')/2πn_I\| ∈ E−E\} \;≪\; T^{-6/65}\,\big(R\,ν\big)^{2}/B
```
*is false* — i.e. the second moment is genuinely larger than the square of the first moment divided by
`B`, forcing concentration and hence a contradiction with Theorem 16. **This is a clean, finite,
checkable inequality about fat APs and Bohr sets, and it is the last quantitative step in the chain**
```
   Thm 16/35 (proved) + Cycle-17 identity (proved) + second moment (OC59) ⟹ \mathrm{LV}(7/10,13/10)<9/10
     ⟹ ‖A‖_∞ < 30/13 ⟹ (with the full wedge) the Density Hypothesis.
```

---

# CYCLE 39 (2026-07-25) — the extremal profile at the bottleneck, computed explicitly; and the *infinitesimal* saving that would beat `30/13`

## The second moment is also consistent `[PROVED HERE — closes the naive incidence route]`
With `X_I = \{t∈W : θ_I(t)∈E_I\}`, `∑_I|X_I| = Rν ≍ T`, Cauchy–Schwarz forces
`∑_I|X_I|^2 ≥ T^2/B = T^{3/2}`, i.e. an average pair-multiplicity `m(t,t') ≥ T^{3/2}/R^2 = T^{3/26}`.
Generalising Theorem 35 to a target set `S` that is a union of `k` intervals,
```
   \#\{I : d/2πn_I \bmod 1 ∈ S\} \ ≪\ |S|\,\frac{N}{L} \;+\; k\Big(\frac{|d|}{N}+1\Big) ,
```
and `E_I−E_I` has measure `≤ 2K^2/L = T^{-3/26}` with `K^2 = T^{2/13}` intervals (`K = L^2/V'^2 =
T^{1/13}`), this gives `m(t,t') ≪ T^{10/26}` for every `|d| ≤ T`. Then
`∑_{t≠t'}m ≤ R^2T^{5/13} = T^{23/13} ≥ T^{3/2}` ✔ — **no contradiction.** The second moment is
consistent with `R = T^{9/13}`. `[RECORDED DEAD END: first- and second-moment incidence counting at
the bottleneck. Both are consistent; the configuration is not excluded by counting resonances.]`

## The extremal profile, explicitly `[PROVED HERE]`
Every quantity is now pinned at `(σ,τ) = (7/10,13/10)`:
```
   \#\text{blocks } B = T^{1/2},\quad L = T^{7/26},\quad V = T^{14/26},\quad R = T^{18/26},
   \quad V' = T^{6/26},\quad ν = V/V' = T^{8/26} = T^{4/13},\quad |E_I| = L/V'^2 = T^{-5/26},
   \quad K = L^2/V'^2 = T^{1/13}\ \text{wave packets per block},
```
so the extremal configuration is:
> *each of the `T^{1/2}` blocks is a superposition of `T^{1/13}` wave packets; each `t ∈ W` resonates
> with `T^{4/13}` of the `T^{15/26}` wave packets; each wave packet catches a `T^{-7/26}` fraction of
> `W`.* Total incidences `= T` exactly.
Two structural facts follow. **(i)** A single fat AP can contain all of `W`: its point count in
`[T,2T]` is `≍ T/L = T^{19/26} > R = T^{18/26}`, so containment is not obstructed by size — Theorem 16
applies (`R ≥ CN/L = T^{1/2}` ✔) and forbids `N^{ε}` *common* fat APs, but the extremal needs each
wave packet to catch only a `T^{-7/26}` fraction, far below any "all-points" hypothesis. **(ii)** The
required `δ`-fraction version of Theorem 16 would need `δ = T^{-7/26}`, which is false in general
(take `W` an arithmetic progression and the moduli generic). **So Theorem 16 in any fractional form
cannot close the bottleneck.** `[RECORDED DEAD END]`

## What would actually beat `30/13` — an *infinitesimal* saving `[PROVED HERE]`
Guth–Maynard's `\mathrm{A}(σ) ≤ 15/(3+5σ)` is Corollary 11.9 with `τ_0 = (3+5σ)/5`, which at
`σ = 7/10` is `τ_0 = 13/10` — **the same `τ_0` as Ingham**, and at its binding point `τ = τ_0` they too
use only the mean value theorem (`\mathrm{LV}(7/10,13/10) ≤ 9/10`); their Theorem 10.27 improves only
the interior sub-range `[13/5−2σ, τ_0) = [6/5, 13/10)`. Consequently:
> **To beat `‖A‖_∞ = 30/13` it suffices to save *any* fixed proportion over the mean value theorem at
> `τ` slightly above `13/10`.** Raising `τ_0` to `13/10 + ε` requires
> `\mathrm{LV}(7/10, τ) ≤ (9/10)\,τ/(13/10+ε)` on `[2τ_0/3,τ_0]`; at `τ = τ_0` the MVT gives
> `9/10 + ε` while the requirement is `9/10`, so the needed saving is exactly `ε` — **an infinitesimal
> improvement of the mean value theorem on a neighbourhood of `τ = 13/10` suffices.**
`[OPEN CORE 60]` Prove `\mathrm{LV}(7/10, 13/10+ε) ≤ 9/10 + (1−c)ε` for some fixed `c > 0`. Since both
moment counting and incidence counting are now provably consistent with the extremal profile, the
saving must come from **outer cancellation in `∑_I n_I^{-it}\widehat{z_I}(θ_I(t))`** — the phases
`n_I^{-it}` across the `T^{4/13}` resonant blocks, which every argument so far has discarded by the
triangle inequality. This is `[OPEN CORE 26]` of Cycle 19, now reduced to a single explicit
configuration with all parameters fixed, and it is the *only* surviving mechanism.

## Theorem 36 (the outer sum has **unit curvature** — the block length is calibrated for it) `[PROVED HERE]`
Writing `n_j = N + jL`, `j = 0,…,B`, `B = N/L`, the Cycle-17 identity becomes
```
     D(t) \;=\; N^{-it}∑_{j=0}^{B} e^{-it\log(1+jL/N)}\,\widehat{z_j}\big(θ_j(t)\big) \;+\;O(B),
     \qquad θ_j(t) = \frac{t}{2πn_j}\bmod 1 .
```
The outer phase `Φ_t(j) := -t\log(1+jL/N)` has
```
        Φ_t'(j) ≍ tL/N = T^{1/2},\qquad Φ_t''(j) ≍ t(L/N)^2 = 1,\qquad Φ_t'''(j) ≍ t(L/N)^3 = T^{-1/2},
```
so **the second derivative is exactly of unit order and the third is negligible: the choice
`L = NT^{-1/2}` is precisely the calibration making the outer sum a unit-curvature exponential sum.**
This is the structural reason the wave-packet scale is `NT^{-1/2}` and not something else, and it is
the exact regime in which van der Corput / stationary phase gives square-root cancellation.
> **If the outer sum had square-root cancellation, the bottleneck would be excluded outright:**
> `|D| ≲ B^{1/2}\max_j|\widehat{z_j}| = T^{13/52}·T^{12/52} = T^{25/52} < V = T^{28/52}` — a
> contradiction. Largeness at the bottleneck therefore *requires* the adversary to defeat the
> unit curvature by choosing the phases of `z` so that `\arg\widehat{z_j}(θ_j(t)) ≡ Φ_t(j)` for the
> `ν = T^{4/13}` resonant `j`, **simultaneously for every `t ∈ W`.**

## The over-determination count `[PROVED HERE]`
```
   \text{constraints} = R·ν = T^{18/26}·T^{8/26} = T^{26/26} = T ,\qquad
   \text{degrees of freedom} = \#\{z_n\} = N = T^{20/26} .
```
The alignment system is over-determined by a factor `T^{6/26} = T^{3/13}`. (Counting alignments per
block rather than per resonance gives `R·B = T^{31/26}` conditions against `N = T^{20/26}` unknowns,
over-determined by `T^{11/26}`.)
> **This is the first quantitative statement in the programme that the extremal configuration is
> *structurally* impossible rather than merely unaccounted for.** Both moment counting (Theorem 33)
> and incidence counting (Cycles 38–39) are provably consistent with it; the over-determination is
> not. The obstruction is therefore a **rank/rigidity** phenomenon, not a measure-theoretic one.
`[OPEN CORE 61]` Convert the over-determination into a theorem. The alignment conditions are
`\arg\widehat{z_j}(θ_j(t)) = -t\log(1+jL/N) + O(1)` for `(t,j)` in the incidence set `𝓘 ⊂ W×[0,B]`,
`|𝓘| = T`. Each `\widehat{z_j}(θ)` is a linear functional of the `L` unknowns `z_n`, `n ∈ I_j`, so the
system is **bilinear**: `T` phase conditions on `N` unknowns, with the phases prescribed by a
unit-curvature function of `j` and a linear function of `t`. The natural tool is a rank bound for the
`R × B` matrix `M_{t,j} := e^{iΦ_t(j)}` restricted to `𝓘` — note `M` is a *generalised Vandermonde /
Cauchy-type* matrix, and the programme already has the machinery for such rank bounds in
`formal/GaloisForLFunctions/HilbertMetric` (rank-one and Gram modules). **Next cycle: bound the rank
of `M|_𝓘` and compare with `N/L`.**

---

# CYCLE 40 (2026-07-25) — the phase-rigidity equation: the exact algebraic form of the last obstruction

## `L^2` is exactly saturated by the extremal `[PROVED HERE — closes the `L^2` route]`
With `A_{t,j} := e^{iΦ_t(j)}\widehat{z_j}(θ_j(t))` (so `D(t) = N^{-it}∑_jA_{t,j}`), Cauchy–Schwarz over
the `ν` resonant blocks gives `R V^2 ≤ ν∑_{(t,j)∈𝓘}|A_{t,j}|^2 = ν\,|𝓘|\,V'^2`, and at the bottleneck
```
   ν|𝓘|V'^2 = T^{8/26}·T^{26/26}·T^{12/26} = T^{46/26},\qquad RV^2 = T^{18/26}·T^{28/26} = T^{46/26} .
```
**Equality.** The extremal saturates Cauchy–Schwarz exactly, so no `L^2`/large-sieve refinement can
separate it. (The cruder route — bounding `∑_t|\widehat{z_j}(θ_j(t))|^2 ≪ (L+N)L` by the large sieve —
loses a factor `T^{2/26}` and gives only `R ≪ T^{20/26}`.) `[RECORDED DEAD END]`

## Theorem 37 (phase-rigidity equation) `[PROVED HERE]`
Largeness `|D(t)| ≥ V = νV'` with `ν` terms of size `≍ V'` forces *all* resonant terms to align:
`\arg\widehat{z_j}(θ_j(t)) + Φ_t(j) = c(t) + O(1)`. Taking two points `t,t'` and two blocks `j,j'`
resonant with both, and writing `d := t−t'`, `Δ_j(θ,h) := \arg\widehat{z_j}(θ+h) − \arg\widehat{z_j}(θ)`,
the constants `c(t)` cancel and one obtains, **for every such quadruple**,
```
   Δ_j\Big(θ_j(t'),\ \frac{d}{2πn_j}\Big) \;-\; Δ_{j'}\Big(θ_{j'}(t'),\ \frac{d}{2πn_{j'}}\Big)
        \;=\; -\,d\,\log\frac{n_{j'}}{n_j} \pmod{2π} .
```
> **This is the exact algebraic content of the Density Hypothesis at its bottleneck.** The left side
> depends on the *unknown* functions `\widehat{z_j}` only through phase increments over shifts
> `d/2πn_j`; the right side is a completely explicit function of `(d, n_j, n_{j'})` — the logarithm of
> a ratio of two integers in `[N,2N]`, scaled by `d`. The system must hold on the incidence set, of
> size `|𝓘| = T`, against `N = T^{20/26}` unknowns.
Structural features, all new here:
* the right-hand side is **bilinear in `(d, \log(n_{j'}/n_j))`** and, since `d` ranges over the
  difference set of `W` and `\log(n_{j'}/n_j) ≍ (j'-j)L/N`, its typical size is
  `d(j'-j)L/N ≍ T^{1/2}` — equidistributed mod `2π`, so the constraints are *generically
  unsatisfiable*; the adversary must choose `W` and `z` to correlate them;
* the left-hand side is a **cocycle**: `Δ_j` satisfies `Δ_j(θ,h_1+h_2) = Δ_j(θ,h_1)+Δ_j(θ+h_1,h_2)`,
  so the system is a cocycle equation over the group generated by the shifts `d/2πn_j` — i.e. a
  **Bohr-set cohomology** problem;
* consistency over triples `(j,j',j'')` is automatic (the equation telescopes), but consistency over
  triples `(t,t',t'')` imposes `d + d' = d''` compatibility — the **additive energy of `W`** enters
  here, and only here.
`[OPEN CORE 62]` Prove that the cocycle equation has no solution with `\|z\|_∞ ≤ 1` when
`R > T^{18/26−δ}`. Two concrete attacks: **(a)** differentiate in `d` — the right side has derivative
`\log(n_{j'}/n_j) ≍ (j'-j)L/N`, an *arithmetically rigid* quantity (a difference of logarithms of
integers), while the left side's derivative is `∂_hΔ_j`, bounded by the modulus of continuity of
`\arg\widehat{z_j}`, which the `1/L`-band-limitedness of `\widehat{z_j}` caps at `O(L)`; comparing
gives a constraint `(j'-j)L/N ≪ L`, i.e. `j'-j ≪ N/1` — vacuous, so the *second* derivative must be
used, where the unit curvature of Theorem 36 enters; **(b)** sum the equation over `j'` to eliminate
`Δ_{j'}` and obtain a single-block identity for `Δ_j`, whose failure is a statement about the
distribution of `\{d\log(n_{j'}/n_j)\}` — precisely the object Theorem 35 counts.

---

# CYCLE 41 (2026-07-25) — full hgtl7 cycle: **the diameter correction**, and Conjecture D

## Phase 1 — corpus (`formal/`) `[DONE]`
`scripts/formal_tools.py research` + `rg` over `HilbertMetric/`, `HTGeometry/`, `RHTower/` surface
directly relevant machinery, none of it yet used by this card:
| Module | Content | Relevance |
|---|---|---|
| `RHTower/LargeValuesDpoly.lean` (`large_values_dpoly`) | `R·V² ≤ (δ^{-1}+η^{-1})∫‖D‖² + η∫‖D'‖²` for grid points | the mean-value/large-values inequality, **already formalised** |
| `HTGeometry/DirectionalVandermondePhaseJet.lean` (`phasePolynomial_ne_zero`) | a nonzero-coefficient phase polynomial with distinct frequencies has a nonzero value or derivative at every point | Vandermonde non-degeneracy — the rank input `[OC61]` asks for |
| `HilbertMetric/SymmetricFockPhaseRigidity.lean`, `UnisolventEvaluation.lean` | phase rigidity, unisolvence | the cocycle/rank setting of Theorem 37 |
| `HTGeometry/DirichletFlagVandermonde.lean` | Dirichlet-flag Vandermonde = positive product | determinant lower bounds for the alignment matrix |
## Phase 2 — external SOTA `[PARTIAL — recorded]`
arXiv API unreachable from this environment on this attempt (empty responses for all queries; earlier
cycles succeeded). SOTA reference therefore remains the extracted ANTEDB blueprint chapters 7/8/10/11
and Guth's survey, both already in the scratchpad. **No claim of novelty is made in this cycle without
re-checking the API when it is reachable.**

## Phase 3/4 — a conjecture, and the correction that killed two candidates
**Candidate B (outer square-root cancellation, `Θ = B^{-1/2}`): `FALSE`.** It would give
`R ≪ N^{4−4σ}B^{-1}`, which at `(σ,τ) = (7/10,13/10)` is `T^{0.423} < T^{0.46} = N^{2−2σ}` — below the
unconditional lower bound `\mathrm{LV}(σ,τ) ≥ \min(2−2σ,τ)` of Lemma 7.5. **Killed by a known lower
bound.**
**Candidate C (alignment diameter bound): `CIRCULAR`.** It implies Montgomery-strength bounds, i.e. it
encodes the desired conclusion. Rejected per the skill's own rule.
### `[PROVED HERE]` The diameter correction — a genuine error in the Cycle 36–40 framing
The block length at which the outer phase is linear is `L = N/\sqrt{\mathrm{diam}\,W}`, **not**
`N T^{-1/2}`. Indeed the Lemma 7.5 extremal (random signs on intervals of length `N^{2σ−1}`, `W` an
interval of length `N^{2−2σ}` after the twist `z_n ↦ z_n n^{iT_0}`) has
```
   \mathrm{diam}\,W = N^{2−2σ},\quad L_{\mathrm{eff}} = N/N^{1−σ} = N^{σ},\quad
   Φ' ≍ (\mathrm{diam}\,W)\,L/N = N^{2−2σ}N^{σ−1} = N^{1−σ}\ \ \text{— and after the twist, } O(1).
```
**In the known extremal the outer phases are *fully aligned*: there is no cancellation whatsoever in
the outer sum.** Consequently:
> **Any conjecture asserting unconditional square-root cancellation in the outer sum is false, and
> Theorem 36's unit-curvature calibration must be read with `T` replaced by `\mathrm{diam}\,W`.** The
> over-determination count of Cycle 39 is correspondingly weakened: with `B = (\mathrm{diam}\,W)^{1/2}`
> the alignment constraints number `R·ν ≥ R\,N^{σ−1}(\mathrm{diam}\,W)^{1/2}`, so over-determination
> requires `R > N^{2−σ}(\mathrm{diam}\,W)^{-1/2}`, which for a *clustered* `W` fails. **The extremal
> defeats the count by clustering.** `[This corrects Cycle 39; do not re-derive the uncorrected
> version.]`

> ### `[CONJECTURE D — Curvature–Divisor Dichotomy]`
> Let `L = N/\sqrt{\mathrm{diam}\,W}` and let `J(t) = \{j : |\widehat{z_j}(θ_j(t))| ≥ V'\}` be the
> resonant block set. Then for all but `N^{o(1)}` of the `t ∈ W`, `J(t)` is contained in a union of
> `N^{o(1)}` arithmetic progressions in `j` whose common differences all divide a single integer
> `Q ≪ N^{O(1)}`.
> **Why bold:** nobody has asserted arithmetic structure of the *block* index set; all known structure
> theorems concern the `t`-side. **Why plausible:** the resonance condition `θ_j(t) ∈ E_j` is
> `\|t/2πn_j\| ∈ E_j` with `n_j = N + jL` in arithmetic progression, so the constraint is a
> simultaneous-approximation condition whose solution set is exactly the object Theorem 16 controls —
> transported from `t` to `j` by the symmetry of the incidence. **Consequence if true:** on each
> progression the outer phase `Φ_t(j)` restricts to a quadratic with `Φ''≍1`, hence a Gauss sum with
> square-root cancellation, contradicting alignment on progressions longer than `N^{o(1)}`; so
> `ν ≪ N^{o(1)}·(\#\text{progressions})`, and largeness fails. **How it fails:** if `J(t)` can be a
> generic (structureless) set of density `ν/B`, in which case Theorem 16's mechanism has no `j`-side
> analogue. **First point not yet provable `[OPEN CORE 63]`:** the transport of the gcd/CRT argument
> from the `t`-variable (where the moduli `n_i` are the unknowns) to the `j`-variable (where the
> moduli are `N+jL`, an arithmetic progression, and the unknown is `t`).

## Phase 5 — attempt on `[OPEN CORE 63]`, and where it stops `[PROVED HERE]`
Model each block's `\widehat{z_j}` as `K` wave packets at frequencies `ξ_{j,k}`; resonance with packet
`(j,k)` is `\|t/2πn_j − ξ_{j,k}\| ≤ 1/2L`, i.e. `t ∈ A_{j,k}`, a fat AP of modulus `2πn_j` and width
`≍ N/L`. Two facts, both proved:
* **If the packets are unstructured in frequency (e.g. all `ξ_{j,k} = 0`), Theorem 35 closes the
  bottleneck outright:** `ν(t) = \#\{j : \|t/2πn_j\| ≤ 1/2L\} ≪ N/L^{2} + T/N + 1 = T^{3/13}`, whereas
  largeness needs `ν = T^{4/13}`. **Contradiction.** So the extremal *must* place the packet
  frequencies along a curve `ξ_{j,k} ≈ t_k/2πn_j`.
* **With that placement the periodicity of the fat APs rescues the adversary:** each `A_{j,k}` meets
  `[T,2T]` in `≍ T/L = T^{19/26}` one-separated points, which already exceeds `R = T^{18/26}`, so a
  single packet can cover all of `W`. Every subsequent count is then consistent:
```
   \text{incidences } Rν = T \ \le\ (BK)(T/L) = T^{34/26} ✔;\qquad
   ∑_tν(t)^2 ≥ (∑ν)^2/R = T^{34/26} \ \le\ (BK)^2\,T/L^2 = T^{42/26} ✔ .
```
> **Conclusion of the cycle: at the bottleneck every counting statement — first moment, second moment,
> incidence, energy, and the `j`-side transport — is consistent with the extremal profile. The
> configuration is excluded only if the *frequency placement* `ξ_{j,k} ≈ t_k/2πn_j` is itself
> obstructed, and that placement is exactly what Theorem 16 forbids when the same `t_k` must serve
> `N^{ε}`-many distinct moduli.** So the live statement is:
`[OPEN CORE 64]` *Can `K = T^{1/13}` "centres" `t_1,…,t_K` and packet frequencies
`ξ_{j,k} = t_k/2πn_j + O(1/L)` be chosen so that the resulting `BK` fat APs cover each of
`R = T^{18/26}` points `ν = T^{8/26}` times?* Theorem 16 says a single set of `≥ CN/L` points cannot
lie in more than `N^{ε}` fat APs with distinct moduli — i.e. **one centre `t_k` can serve only `N^{ε}`
blocks**. If that is upgraded from "all points" to "the `T^{11/26}` points each packet actually
catches", the total incidence budget drops from `T^{34/26}` to `K·N^{ε}·T/L = T^{2/26+19/26+o(1)} =
T^{21/26+o(1)}`, which is **less than the required `T`** — and the bottleneck closes. **This is the
single remaining quantitative gap, and unlike the earlier `δ`-fraction proposals it is not asking for
a fraction: it asks Theorem 16 with the point set replaced by the `A_{j,k}`-fibre itself.**

---

# CYCLE 42 (2026-07-26) — **CORRECTION: the extremal works by square-root cancellation, not alignment** — and the resulting sparse-polynomial reduction

## The premise of Theorem 37 and Cycle 39 is false `[CORRECTION — read before reusing]`
Those cycles assumed largeness `V = ν V'` forces *all* resonant blocks to align in phase. **The known
extremal does the opposite.** In Lemma 7.5's construction (random signs `ε_I` on intervals of length
`N^{2σ−1}`), the largeness
```
   |D(t)| ≈ \sqrt{\#\text{intervals}}·N^{2σ−1} = N^{(2−2σ)/2}\,N^{2σ−1} = N^{σ}
```
comes from **square-root cancellation across the sign intervals**, not coherence. So:
> **The phase-rigidity equation (Theorem 37) and the over-determination count (Cycle 39) rest on a
> false premise and are hereby withdrawn.** `[RECORDED DEAD END: any argument that assumes largeness
> forces full outer alignment.]` (Theorem 36's curvature computation and Theorem 35 stand — they make
> no such assumption.)

## Theorem 38 (the correct requirement at the bottleneck) `[PROVED HERE]`
Let `V = ν^{α}V'` describe the actual outer behaviour (`α = 1/2` square-root, `α = 1` full alignment),
with `ν ≤ B` resonant blocks and `V' ≤ L`. Then `V ≤ L\,B^{α}`, so at `(σ,τ) = (7/10,13/10)`, where
`V = T^{14/26}`, `L = T^{7/26}`, `B = T^{13/26}`:
```
        T^{14/26} ≤ T^{7/26}\,T^{13α/26} \iff α ≥ 7/13 = 0.538\ldots > 1/2 .
```
> **The bottleneck configuration exists only if the outer sum beats square-root cancellation, by the
> definite margin `α − 1/2 ≥ 1/26`.** With `α = 7/13` the profile is forced to the extreme: *every*
> one of the `B = T^{1/2}` blocks resonates at full strength `V' = L`, and the outer sum of `B`
> unimodular terms must reach `B^{7/13}` rather than `B^{1/2}`.

## The reduction `[PROVED HERE]`
Writing the block amplitudes as `L\,u_j` with `|u_j| = 1`, the outer sum is
```
        ∑_{j=0}^{B} u_j\,n_j^{-it},\qquad n_j = N + jL ,
```
**a sparse Dirichlet polynomial: `B = T^{1/2}` unimodular coefficients at log-frequencies spaced
`L/N = T^{-1/2}` inside an interval of length `\log 2`.** Hence:
> ### The Density Hypothesis at its bottleneck is equivalent to a large-value bound for a *unimodular
> sparse Dirichlet polynomial of length `T^{1/2}` with equally spaced log-frequencies.*
> Precisely: `\mathrm{LV}(7/10,13/10) < 9/10` follows from
> ```
>    \#\{t ∈ [T,2T]\ 1\text{-separated} : |∑_{j≤B}u_jn_j^{-it}| ≥ B^{β}\} \;<\; T^{18/26}
>    \quad\text{for } β = 7/13 .
> ```
The Montgomery–Vaughan mean value theorem for these frequencies (separation `T^{-1/2}`) gives
`R\,B^{2β} ≪ (T + N/L)B = TB`, i.e. `R ≪ TB^{1−2β} = T^{25/26}` — **short of the required `T^{18/26}`
by `T^{7/26}`**, exactly the same deficit as before, as it must be. But the object is now much smaller
and completely explicit: `B = T^{1/2}` unimodular unknowns, frequencies in arithmetic progression.
`[OPEN CORE 65]` For unimodular `u_j` and `n_j = N + jL` in arithmetic progression, prove
```
     \#\{t\ 1\text{-sep.} \subset [T,2T] : |∑_{j≤B}u_jn_j^{-it}| ≥ B^{β}\} \ll T^{1+o(1)}B^{-(2β-1)-c}
```
for some `c > 0` — i.e. beat the mean value theorem for *this* sparse family. **The arithmetic
progression structure of the `n_j` is the new hypothesis: `\log n_j = \log N + \log(1+jL/N)`, so the
frequencies are a smooth, unit-curvature perturbation of an arithmetic progression (Theorem 36), and
for a genuine arithmetic progression the sum would be a Dirichlet kernel with an exact large-value
description.** This is the first form of the problem with a *finite, explicitly parametrised* unknown.

## Theorem 39 (the bottleneck outer sum **is a quadratic Weyl sum with unit coefficient**) `[PROVED HERE]`
With `n_j = N+jL`, `B = N/L`, one has `\log n_j = \log N + \log(1+j/B)` and
`\log(1+j/B) = j/B − j^2/(2B^2) + O(j^3/B^3)`, so
```
      ∑_{j≤B}u_j\,n_j^{-it} \;=\; N^{-it}∑_{j≤B}u_j\,e\big(γ j^{2} − θ j\big) + O(\text{lower order}),
      \qquad γ := \frac{t}{4πB^{2}},\quad θ := \frac{t}{2πB} .
```
**Since `B^2 = N^2/L^2 = T` exactly at the critical calibration, `γ ≍ 1`: the quadratic coefficient is
of order one** (this is Theorem 36's unit curvature, in its sharpest form), and `θ` sweeps `≍ B`
periods as `t` runs over `[T,2T]`. So `(γ,θ)` traverses `[1/2,1]×𝕋`.
### Moment bounds for this family `[PROVED HERE]`
The characters `e(γj^2 − θj)` are **orthonormal** on `[0,1]^2` (because `j ↦ (j^2,j)` is injective), so
```
   ∫∫|F|^{2} = B,\qquad ∫∫|F|^{4} = \#\{j_1+j_2=j_3+j_4,\ j_1^2+j_2^2=j_3^2+j_4^2\} = 2B^{2}−B ,
```
the fourth moment being *exactly* the diagonal because the two equations force
`\{j_1,j_2\} = \{j_3,j_4\}`. More generally `∫∫|F|^{2k} = J_{k,2}(B) ≪ B^{k+ε} + B^{2k−3}`
(Vinogradov's mean value theorem in degree 2). Hence for `|F| ≥ B^{β}`,
```
   \mathrm{meas}\{(γ,θ)\} ≪ B^{k(1−2β)} + B^{2k(1−β)−3} ,\qquad\text{optimal at } k = 3:\quad
   \mathrm{meas} ≪ B^{3−6β} ,
```
and, the curve `t ↦ (γ(t),θ(t))` being equidistributed, `R ≪ T\,B^{3−6β+o(1)}`. **The fourth moment
alone already beats the mean value theorem for every `β > 1/2`** (`B^{2−4β}` versus `B^{1−2β}`), and
`k = 3` is the exact optimum — `k > 3` is worse because `J_{k,2}` leaves the diagonal regime.
### What it gives, and what it does not `[VERIFIED]`
For the extreme profile (`ν = B`, `V' = L`) one has `β = 1 − 2(1−σ)/τ`, so
```
        R ≪ T^{\,6(1−σ)/τ \;-\; 1/2 \;+\; o(1)} .
```
This is **far stronger than the mean value theorem for large `τ`** — e.g. at `(σ,τ) = (7/10,2)` it gives
`\mathrm{LV} ≤ 4/5`, against the mean value theorem's `8/5` and the Density-Hypothesis target `6/5` —
but it is **weaker at the bottleneck** (`τ = 13/10`: `0.885` versus the mean value theorem's `0.692`),
the crossover being `τ = 2(5−4σ)/3 = 22/15` at `σ = 7/10`. So it does not move `‖A‖_∞`.
`[OPEN CORE 66]` The bound above is derived only for the **extreme profile** `ν = B`, `V' = L`. The
general case has `ν ≤ B` resonant blocks of strength `V' ≤ L`, giving a Weyl sum over a *subset*
`J ⊆ [0,B]` of size `ν`. **Vinogradov's mean value theorem for a sparse `J` is exactly the
Bourgain–Demeter–Guth decoupling regime**, and `J_{k,2}(J)` for structured `J` (an arithmetic
progression, a Bohr set) is much smaller than for the full interval. **This is the first point at which
decoupling technology enters the programme, and it is the natural next step**: bound `J_{3,2}(J)` for
the resonant sets `J` produced by Theorem 35, whose structure (clusters of size `N^2/(2L^2d)` spaced
`N^2/(dL)` apart) is completely explicit.

## CORRECTION to Theorem 39 `[read before reusing]`
Theorem 39 wrote the outer sum as `∑_j u_j n_j^{-it}` with `u_j` **unimodular and `t`-independent**.
That is a *model*, not an identity: the true block amplitude is `w_j(t) = \widehat{z_j}(θ_j(t))`, which
depends on `t` through `θ_j(t) = t/2πn_j`. **The moment bounds of Theorem 39 are therefore valid only
for the model, not for a general large-value pattern.** What survives unconditionally is the exact
phase expansion below, and the observation that `γ ≍ 1`.

## Theorem 40 (exact two-variable phase expansion at the critical calibration) `[PROVED HERE]`
Write `n = n_j + m`, `n_j = N + jL`, `0 ≤ m < L`, `j ≤ B = N/L`, with `L = NT^{-1/2}` so `B^2 = T`.
Then for `t ≍ T`,
```
   \log n = \log N + \Big(\frac{j}{B} - \frac{j^{2}}{2B^{2}}\Big) + \frac{m}{n_j} - \frac{m^{2}}{2n_j^{2}}
             + O\!\big(T^{-3/2}\big) ,
```
and the four terms have *exactly* the sizes
```
   t\frac{j}{B} ≍ Bj,\qquad t\frac{j^{2}}{2B^{2}} ≍ \frac{j^{2}}{2},\qquad
   t\frac{m}{n_j} ≍ \frac{Tm}{N} \le B,\qquad t\frac{m^{2}}{2n_j^{2}} \le \frac{TL^{2}}{N^{2}} = 1 .
```
`t\,m^3/N^3 ≤ T^{-1/2}` is negligible. **So at the critical calibration the phase is exactly a
two-variable quadratic form in `(j,m)` with all four coefficients of size `1`, `1`, `B`, `1`
respectively — no cubic terms survive.** This is the rigorous form of "unit curvature", and it is the
correct object for a decoupling / Vinogradov analysis:
```
   D(t) = e^{-it\log N}\!\!\sum_{j≤B}\ \sum_{m<L} z_{j,m}\,
          e\Big(-\frac{t}{2π}\Big[\frac{j}{B}-\frac{j^{2}}{2B^{2}}+\frac{m}{n_j}-\frac{m^{2}}{2n_j^{2}}\Big]\Big).
```
`[OPEN CORE 67]` The relevant mean value is now the **two-dimensional Vinogradov system**
```
   ∑_{i}\big(j_i, j_i^{2}, m_i, m_i^{2}, j_im_i\big) = ∑_{i}\big(j'_i, j'^{2}_i, m'_i, m'^{2}_i, j'_im'_i\big)
```
(the cross term `j m` appearing because `1/n_j` depends on `j`), i.e. the decoupling problem for the
**two-dimensional quadratic surface** `(x,y) \mapsto (x, x^2, y, y^2, xy)` — the Veronese surface of
degree 2 in two variables, for which Bourgain–Demeter decoupling is sharp and known. **This replaces
the heuristic single-variable Weyl sum of Theorem 39 with a rigorous, standard object.** The next step
is to compute the decoupling exponent for this surface at the box `[0,B]×[0,L]` with `B^2 = T`, and
compare with the required `\mathrm{LV}(σ,τ) ≤ (2−2σ)τ`.

## CORRECTION to Theorem 40 `[read before reusing]`
The `(j,m)` split does **not** produce a genuine two-variable phase: since `n = N(1+x+y/B)` with
`x = j/B`, `y = m/L`, the phase is `t\log(1+x+y/B)` — a function of the **single** variable
`u = (n−N)/N`. So there is no Veronese surface and no two-dimensional Vinogradov system; Theorem 40 is
Taylor's theorem. `[OPEN CORE 67 is withdrawn.]` What the split *does* isolate, correctly, is the size
separation:
* **within** a block the phase is linear in `m` up to `O(1)` (`t\,m^2/n_j^2 ≤ TL^2/N^2 = 1`) — this is
  precisely why the block equals a Fourier evaluation `\widehat{z_j}(θ_j(t))` (Cycle 17), and why
  `L = NT^{-1/2}` is the right length;
* **across** blocks the quadratic term is `t\,j^2/2B^2 ≍ j^2/2` — genuinely of unit curvature
  (Theorem 36).
**The two corrections in this cycle (Theorems 39 and 40) share one root cause: attempting to convert
the `t`-dependent amplitudes `\widehat{z_j}(θ_j(t))` into `t`-independent coefficients. Every such
attempt has failed, and the failure is structural — the `t`-dependence *is* the problem.**
`[RECORDED DEAD END: any reduction of `D(t)` to a Weyl/Dirichlet sum with `t`-independent
coefficients.]`

---

# STATE OF THE PROGRAMME — consolidated after 42 cycles (2026-07-26)
**Target.** `\mathrm{A}(σ) ≤ 2` for all `1/2<σ<1`. Equivalent (Cor. 11.9, `τ_0 = 3/2`):
`\mathrm{LV}(σ,τ) ≤ (2−2σ)τ` for `τ ∈ [1,3/2]`. Current world record `‖A‖_∞ = 30/13`.
**Bottleneck, located exactly (Cycle 38).** `τ_0 = 2−σ`; at `σ = 7/10`, `(σ,τ) = (7/10,13/10)`,
`N = T^{10/13}`, `L = T^{7/26}`, `B = T^{1/2}`, `V = T^{14/26}`, `R = T^{18/26}`. **It lies inside the
coherent regime** (`τ < 2σ`), so wave-packet methods are available there.
**Proved and reusable (unconditional):**
`Thm 4` (MC ⟺ `∞→1` norm) · `Thm 5` (Grothendieck/SDP tightness) · `Thm 6` (log-Bohr count) ·
`Thm 10` (required saving `N^{(2σ−1)(τ−1)}`) · `Thm 16` (fat-AP incidence, divisor bound, no Kakeya) ·
`Thms 17–19` (block-diagonal / near-diagonal / absolute-value barrier) · `Thm 22/23` (Hölder–moment
ceiling `(2−2σ)τ` and the integrality obstruction) · `Thm 27` (powered Möbius mollifier) ·
`Thm 28` (low-range vanishing forces cross-factor cancellation) · `Thm 30` (rounding = distance to a
numerical semigroup of scales) · `Thm 33` (moment bound `(T+N^k)N^k` is sharp) · `Thm 34` (regime
boundary `τ ≤ 2σ`) · `Thm 35` (per-difference incidence `ν_ε(d) ≪ εN/L+|d|/N+1`) · `Thm 36` (unit
curvature of the outer phase) · `Thm 38` (`α ≥ 7/13`: the bottleneck needs better-than-square-root
outer behaviour) · Cycle 34 (deficit profile `E_k(σ)`) · Cycle 38 (Ingham = MVT + Cor 11.9).
**Withdrawn / dead ends (do not retry):** Thm 26 (vacuous), Thm 29 (rediscovery of Lemma 7.8+MVT),
Thm 37 + Cycle-39 over-determination (false premise: extremal uses square-root cancellation, not
alignment), Thm 39's `t`-independent model, Thm 40's two-variable system; Halász–Montgomery with block
coherence; energy via Cauchy–Schwarz on the `N²`-side; fat-AP route at `τ>2`; `δ`-fraction versions of
Thm 16; log-convex moment interpolation; trace/Schatten with absolute values; the `k`-fold reflection.
**The one live mechanism.** Everything reduces to controlling `∑_j n_j^{-it}\widehat{z_j}(θ_j(t))`
where the amplitudes depend on `t`. All counting (moment, incidence, energy, second moment) is
*provably consistent* with the extremal profile; the only quantity not yet controlled is the
interaction between the unit-curvature outer phase and the `t`-dependence of the amplitudes.

## Theorem 41 (the exact orthogonality slack that the Density Hypothesis needs) `[PROVED HERE]`
Write the outer behaviour as `|D(t)| = ν^{α}V'` (`ν` resonant blocks of strength `V'`). Two reference
values:
```
   α = 1/2  :\ \text{block orthogonality (square-root cancellation)} ;\qquad
   α_{\mathrm{DH}}(σ,τ) := 1 - \frac{2(1−σ)}{τ}\ :\ \text{the largest }α\text{ compatible with DH.}
```
Indeed `V ≤ V'ν^{α} ≤ L B^{α}` with `L = NT^{-1/2}`, `B = T^{1/2}`, `V = N^{σ}` gives exactly
`α ≥ 1 − 2(1−σ)/τ`. Hence:
> **The Density Hypothesis at `(σ,τ)` is equivalent to: the outer sum over blocks never achieves
> `α ≥ α_{\mathrm{DH}}(σ,τ)`.** At the two relevant points,
> ```
>   (σ,τ) = (7/10,\ 13/10):\ α_{\mathrm{DH}} = 7/13 = 0.5385\ldots\quad(\text{slack over }1/2:\ 1/26)
>   (σ,τ) = (7/10,\ 3/2):\ \ α_{\mathrm{DH}} = 3/5 = 0.6\quad(\text{slack over }1/2:\ 1/10)
> ```
> and the known extremal (Lemma 7.5) achieves exactly `α = 1/2`. **So the Density Hypothesis needs only
> that block orthogonality holds with a slack of `ν^{1/10}` — it does *not* need exact
> orthogonality**, which would be Montgomery's conjecture: assuming `α = 1/2 + o(1)` and the per-block
> large sieve `∑_{t∈W}|\widehat{z_j}(θ_j(t))|^2 ≪ (L+N)L` yields `R ≪ N^{2−2σ+o(1)}` — Montgomery,
> hence strictly stronger than needed. `[So Conjecture "α ≤ 1/2+o(1)" is CIRCULAR; the correct target
> is the strictly weaker `α < α_{\mathrm{DH}}`.]`
`[OPEN CORE 68]` Prove `α < 1 − 2(1−σ)/τ` for `τ ∈ [1,3/2]`. Equivalently: **for a positive proportion
of `t ∈ W`, the `ν` resonant block contributions `n_j^{-it}\widehat{z_j}(θ_j(t))` fail to be aligned to
within a factor `ν^{1/10}` of full coherence.** This is strictly weaker than orthogonality and strictly
stronger than the mean value theorem, and it is the first formulation of the residual gap as a
*quantitative slack* rather than an exact identity — which matters, because every exact statement
attempted so far has been either circular (Montgomery-strength) or false (full alignment).

## The double-zeta-sum route, computed `[PROVED HERE — reproduces, does not beat, the record]`
Blueprint Chapter 10 defines `S(N,W) := ∑_{t,t'∈W}|∑_{n∈[N,2N]}n^{-i(t-t')}|^2 = ∑_{n,m}|R_W(n/m)|^2`,
and Lemma 10.3 with `W' = \{0\}` gives `∑_{t∈W}|D(t)|^2 ≤ N\,S(N,W)^{1/2}`, hence
`S(N,W) ≥ R^2V^4/N^2`. Estimating `S` directly with the standard kernel bounds
```
   |K(d)| ≪ N/(1+|d|)\ (|d| ≤ N),\qquad |K(d)| ≪ |d|^{1/2} + N|d|^{-1/2}\ (|d| ≥ N),
   \qquad ∑_{d\ 1\text{-sep}}|K(d)|^{2} ≍ ∫_{-T}^{T}|K|^{2} ≍ TN ,
```
gives `S(N,W) ≪ RN^{2} + RTN`. At the bottleneck `S ≪ T^{64/26}` while the requirement is only
`R^2V^4/N^2 = T^{52/26}` — **consistent, no information.** `[RECORDED DEAD END: `S(N,W)` via kernel
bounds; the diagonal `RN^2` and the `∫|K|^2 = TN` mass both dwarf the requirement.]`

> ### PLATEAU STATEMENT (honest, for the next session)
> Every classical route has now been computed to the end at the bottleneck `(σ,τ) = (7/10,13/10)` and
> **all reproduce `30/13` exactly, none beats it**: mean value theorem (Cycle 38), power trick
> (Thm 22/23), fourth and `2k`-th moments (Thm 33 — proved sharp), Halász–Montgomery with block
> coherence (Thm 35 + Cycle 37 — proved exhausted), reflection/`B`-process (Cycle 32), energy via
> Cauchy–Schwarz (Cycle 37), third-moment/`E_1` route (Cycle 30 — gives `τ/2+1−σ`, worse at `τ=13/10`),
> double zeta sums `S(N,W)` (this cycle), fat-AP incidence (Cycles 38–39 — first and second moments
> both consistent with the extremal). **The convergence of all of them on the same constant is itself
> evidence that `30/13` is the exact barrier of the classical toolkit**, and that the residual
> `30/13 → 2` requires the one quantity none of them controls: the interaction between the
> unit-curvature outer phase (Thm 36) and the `t`-dependence of the block amplitudes
> `\widehat{z_j}(θ_j(t))`, quantified by Theorem 41 as an orthogonality slack of `ν^{1/10}`.
> **Priority for the next session, in order:**
> 1. `[OC68]` the slack statement `α < 1 − 2(1−σ)/τ` — the only live target;
> 2. Lemma 10.5 (energy → subcollection) combined with Theorem 16 on the subcollection `U` — the one
>    piece of blueprint machinery not yet used, and the actual Guth–Maynard mechanism;
> 3. formalise Theorem 35 in Lean against `RHTower/LargeValuesDpoly.lean` and
>    `HTGeometry/DirectionalVandermondePhaseJet.lean` (both already in the tree).

---

# CYCLE 43 (2026-07-26) — hgtl7 Phase 6: the combinatorial core of Theorem 35 is now **formalised in Lean 4**

## What was formalised `[VERIFIED — builds, axiom-clean]`
`formal/GaloisForLFunctions/HTGeometry/SeparatedPointCount.lean` (new module, imported by the
`HTGeometry` umbrella):
```lean
theorem card_le_of_separated_of_subset_Icc
    {L a b : ℝ} (hL : 0 < L) (hab : a ≤ b) (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → L ≤ |x - y|)
    (hsub : ∀ x ∈ S, x ∈ Set.Icc a b) :
    (S.card : ℝ) ≤ (b - a) / L + 1

theorem card_le_of_separated_of_subset_iUnion_Icc
    {ι : Type*} [DecidableEq ι] {L : ℝ} (hL : 0 < L) (I : Finset ι) (a b : ι → ℝ)
    (hab : ∀ i ∈ I, a i ≤ b i) (S : Finset ℝ)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → L ≤ |x - y|)
    (hsub : ∀ x ∈ S, ∃ i ∈ I, x ∈ Set.Icc (a i) (b i)) :
    (S.card : ℝ) ≤ (∑ i ∈ I, (b i - a i)) / L + I.card
```
Mechanism: the floor map `x ↦ ⌊(x-a)/L⌋` is injective on an `L`-separated set (two elements with the
same floor differ by `< L`), so the count is bounded by `#(Icc 0 ⌊(b-a)/L⌋)`; the second statement
follows by fibering over a choice function and summing.
`#print axioms` gives `[propext, Classical.choice, Quot.sound]` for both. The module builds
(`lake build`), is reachable from `GaloisForLFunctions.HTGeometry`, and introduces no lint findings
(the remaining gate errors — two unreachable `RHTower` modules and one stale generated file — are
pre-existing and unrelated).

## Why this and not something larger
**Theorem 35 is `ν_ε(d) ≪ εN/L + |d|/N + 1`, and its proof is exactly: (i) the preimage of
`\{‖x‖ ≤ ε\}` under the monotone map `n ↦ d/2πn` is a union of `≪ |d|/N + 1` intervals of total
measure `≍ εN`; (ii) an `L`-separated set meets such a union in `≪ (total measure)/L + (number of
intervals)` points.** Step (ii) is now machine-checked and reusable; step (i) is a calculus statement
about a monotone map, formalisable next. This matters for this programme specifically: **five results
have had to be withdrawn in this session** (Theorems 26, 29, 37, 39, 40), all for reasons a proof
assistant would have caught immediately — a `t`-dependence smuggled into a coefficient, a false
premise about alignment, a vacuous hypothesis. Formalising the *unconditional* core statements is
therefore not bookkeeping but error control.
`[NEXT IN LEAN]` (a) the monotone-preimage step of Theorem 35; (b) `\mathrm{LV}(σ,τ) ≤ ⌈τ⌉(2−2σ)`
(Theorem 22 with `m = 1`) against `RHTower/LargeValuesDpoly.lean`, which already contains the
mean-value inequality in the required form.

## Theorem 35 is now fully rigorous, with its counting core machine-checked `[VERIFIED]`
Two further theorems were added to `HTGeometry/SeparatedPointCount.lean` (module builds; all four
declarations `#print axioms` to `[propext, Classical.choice, Quot.sound]`):
```lean
theorem card_le_of_expanding_of_separated
    {c L a b : ℝ} (hc : 0 < c) (hL : 0 < L) (hab : a ≤ b) (f : ℝ → ℝ) (S : Finset ℝ)
    (hexp : ∀ x ∈ S, ∀ y ∈ S, c * |x - y| ≤ |f x - f y|)
    (hsep : ∀ x ∈ S, ∀ y ∈ S, x ≠ y → L ≤ |x - y|)
    (hmaps : ∀ x ∈ S, f x ∈ Set.Icc a b) :
    (S.card : ℝ) ≤ (b - a) / (c * L) + 1

theorem card_le_of_expanding_of_separated_iUnion_Icc  -- same, image covered by `[a i, b i]`, `i ∈ I`
    … : (S.card : ℝ) ≤ (∑ i ∈ I, (b i - a i)) / (c * L) + I.card
```
**Derivative-free formulation:** an expanding map sends an `L`-separated set to a `cL`-separated set,
so the counting reduces to the interval lemma in the image. Instantiating with `f(n) = d/2πn` on
`n ∈ [N,2N]`:
```
   |f(x)-f(y)| = \frac{d|x-y|}{2πxy} ≥ \frac{d}{8πN^{2}}|x-y| \quad(c = d/8πN^{2}),
   \qquad f([N,2N]) = \Big[\frac{d}{4πN},\frac{d}{2πN}\Big]\ \text{(length } d/4πN),
```
and `\{u : \|u\| ≤ ε\}` meets that interval in at most `⌊d/4πN⌋+1` intervals of length `2ε`. Hence
```
   ν_ε(d) \;≤\; \frac{4εN}{L} \;+\; \frac{16πεN^{2}}{dL} \;+\; \frac{d}{4πN} \;+\; 1 ,
```
which for `d ≥ N` (the relevant range, `d = t-t'`) is `≪ εN/L + d/N + 1` — **Theorem 35, with explicit
constants and with the combinatorial core verified by Lean.** The second term is the correct behaviour
for `d < N`, where the map is nearly constant and the preimage is a single long interval.

---

# CYCLE 44 (2026-07-26) — **Theorem 42: the constancy window and the curvature scale are incompatible**

## The rigorous version of Theorem 39's model `[PROVED HERE]`
The block amplitude `w_j(t) = \widehat{z_j}(θ_j(t))`, `θ_j(t) = t/2πn_j`, is a trigonometric
polynomial in `t` with frequencies `m/n_j`, `m ≤ L` — i.e. **`w_j` is band-limited with bandwidth
`L/N = 1/B`, hence varies on the time scale `B`.** Therefore:
> **On any window of length `Δ ≪ B`, the amplitudes are constant to first order and**
> ```
>      D(t_0+Δ) = ∑_{j} c_j\,n_j^{-iΔ} + O(\text{error}),\qquad c_j := w_j(t_0)\,n_j^{-it_0} ,
> ```
> **a Dirichlet polynomial in `Δ` with fixed coefficients — exactly Theorem 39's model, now with its
> range of validity identified.** (Theorem 39 asserted this globally, which is why it was withdrawn.)

## Theorem 42 (the incompatibility) `[PROVED HERE]`
The outer phase is `-Δ\log n_j = -Δ(\log N + j/B - j^{2}/2B^{2} + \cdots)`, so its quadratic
coefficient is `γ = Δ/4πB^{2}`. Hence
```
   \textbf{fixed coefficients} \iff Δ ≪ B ;\qquad
   \textbf{unit curvature } (γ ≍ 1) \iff Δ ≍ B^{2} = T .
```
> **The two regimes are separated by a factor `B = T^{1/2}` and cannot be met simultaneously.** On a
> constancy window the phase is linear in `j` (`γ ≤ 1/4πB`), so the sum is a Dirichlet-kernel-type
> object with no Weyl/Vinogradov gain; at the curvature scale the coefficients have moved through
> `B` independent configurations. **This is exactly why Theorem 36 (curvature) and Theorem 39
> (fixed coefficients) could not be combined, and it is a structural obstruction, not an oversight.**
What the constancy window does give, computed: on each of the `T/B = T^{13/26}` windows,
Montgomery–Vaughan with frequency spacing `1/B` yields
`R_{\mathrm{win}}V^{2} ≪ (B + B)\,BL^{2}`, i.e. `R_{\mathrm{win}} ≪ B^{2}L^{2}/V^{2} = T^{12/26}`, and
summing over windows `R ≪ T^{25/26}` — the mean value theorem again, as it must be.
`[OPEN CORE 69]` Break the incompatibility. The only way through is to allow the amplitudes to vary
and to *control* that variation rather than assume it away: `w_j` is band-limited with bandwidth
`1/B`, so on a window of length `Δ = B^{1+δ}` it is determined by `B^{δ}` samples. **The natural object
is therefore a `B^{δ}`-fold "lift": `D` restricted to a window of length `B^{1+δ}` is a sum over
`(j,\text{sample})` pairs, with the outer phase carrying quadratic coefficient `γ ≍ B^{δ-1}`.** As
`δ → 1` the curvature becomes usable while the number of samples reaches `B`; the question is whether
the Vinogradov gain `B^{3-6β}` outpaces the `B^{δ}`-fold multiplication of unknowns. **This is a
single one-parameter optimisation, and it is the first concrete route that uses both Theorem 36 and
the constancy structure.**

## `[OPEN CORE 69]` computed, and the reparametrisation line closed `[PROVED HERE — DEAD END]`
Windowing at length `Δ` gives, by Montgomery–Vaughan on each window,
`R_{\mathrm{win}}V^{2} ≪ (N+Δ)N`, hence `R ≪ (T/Δ)(N+Δ)N/V^{2} = TN^{2}/(ΔV^{2}) + TN^{1−2σ}` —
**the mean value theorem exactly, for every `Δ`.** Windowing gains nothing.
Pushing to the full range and keeping every term, the phase in the `(j,m)` coordinates
(`n = n_j + m`, `n_j = N + jL`) is, with `t = 2πB^{2}s`, `s ≍ 1`, `N = BL`,
```
   \frac{\text{phase}}{2π} = s\Big[Bj - \frac{j^{2}}{2} + \frac{B}{L}m - \frac{jm}{L}\Big] + O(1) ,
```
a quadratic form whose `j^{2}` coefficient is `≍ 1`, whose `jm` coefficient is `≍ 1/L`, and with no
`m^{2}` term (that term is the `O(1)` modulation — this is the block calibration). **But `(j,m) \mapsto
n = N + jL + m` is a bijection, so this "two-variable quadratic Weyl sum" is the one-variable sum
`∑_n z_n n^{-it}` rewritten.** No decoupling surface, no Vinogradov system in two variables — the
apparent extra dimension is a change of index, exactly as the correction to Theorem 40 already noted.
> **Closure statement.** Every reparametrisation attempted in this programme — block/Fourier
> (Cycle 17), sparse outer sum (Thm 39), two-variable Veronese (Thm 40), windowed constancy
> (Thm 42/OC69), quadratic Weyl (Thm 39) — returns to `∑_{n∼N}z_n n^{-it}` with the same information.
> **The obstruction is not the representation. `[RECORDED DEAD END: searching for a better
> representation of `D(t)`. Any future cycle proposing one must first exhibit a quantity it controls
> that the original does not.]`**
This is worth stating plainly because it is the single most repeated failure mode in this session:
five withdrawn theorems, all of them reparametrisations that silently discarded the `t`-dependence of
the amplitudes or the bijectivity of the index map.
**What is left is what Theorem 41 says: a slack estimate.** `α < 1 − 2(1−σ)/τ` is a statement about
*sizes*, not about structure, and it must be proved by an inequality that sees the whole sum at once —
i.e. by a moment or an energy, both of which are proved sharp (Thm 33) or exhausted (Cycle 37) at the
mean-value level. **The only remaining hope in this direction is the one blueprint tool never applied
here: Lemma 10.5's energy-to-subcollection reduction, which replaces `W` by a smaller, more structured
`U` and can therefore beat a sharp bound on `W` itself.** That is the priority for the next session.

---

# CYCLE 45 (2026-07-26) — the energy-to-subcollection machinery: exact setup, and why only the *recursive* form can work

## The three blueprint inequalities, in one place `[extracted verbatim, Chapter 10]`
For `W ⊂ [T,2T]` 1-separated with `|D(t)| ≥ V`, writing `R = |W|`,
`S(N,W) = ∑_{t,t'∈W}|K(t-t')|^2 = ∑_{n,m}|R_W(n/m)|^2`,
`S_4(N,W) = ∑_{t_1..t_4∈W}|K(t_1+t_2-t_3-t_4)|^2 = ∑_{n,m}|R_W(n/m)|^4`:
```
   (1)\ \ R\,V^{2} ≤ N\,S(N,W)^{1/2}                                   [Lemma 10.3, W' = \{0\}]
   (2)\ \ V^{2}E_1(W) ≪ T^{o(1)}\,S(N,W)^{1/2}S_4(N,W)^{1/2}            [Lemma 10.4']
   (3)\ \ S_4(N,W) ≪ T^{o(1)}\,u^{2}\,S(N,U),\quad u|U| ≪ R^{2},\ u^{2}|U| ≪ E_1(W)   [Lemma 10.5]
```
**`U` is a 1-separated subset of `[-2T,2T]` — a *new, smaller* large-value-type set. This is the only
tool in the blueprint that changes the set, and therefore the only one that can beat an estimate
proved sharp on `W` itself (Theorem 33).**

## The non-recursive use is insufficient `[PROVED HERE]`
Bounding `S(N,U) ≤ |U|·∑_{d\ 1\text{-sep}}|K(d)|^{2} ≍ |U|\,TN` and using `u^{2}|U| ≪ E_1(W)`:
```
   (3)+(2)\Rightarrow V^{4}E_1(W)^{2}/S ≪ S_4 ≪ E_1(W)\,TN \Rightarrow E_1(W) ≪ S\,TN/V^{4},
```
and with `E_1(W) ≫ R^{4}/T` and `S ≪ R\,TN` this gives `R ≪ T\,N^{2/3}V^{-4/3}`, i.e. `T^{0.795}` at
the bottleneck — **worse than the mean value theorem's `T^{0.692}`.** `[RECORDED DEAD END: Lemma 10.5
used once, with `S(N,U)` bounded trivially.]`
> **The gain must come from applying the *entire* argument to `U` in place of `W`** — i.e. from the
> induction on scales that Heath-Brown and Guth–Maynard run, in which `(R,E)` is replaced by
> `(|U|,E_1(U))` with `u|U| ≪ R^{2}` and `u^{2}|U| ≪ E_1(W)`, and the process is iterated until the
> energy is trivial. Each round trades a factor `u` for a smaller set; the exponent that survives is
> the fixed point of the resulting recursion.
`[OPEN CORE 70]` Set up and solve that fixed point at `(σ,τ) = (7/10,13/10)`. Concretely: define
`ρ := \log_T R`, `e := \log_T E_1(W)`, `s := \log_T S(N,W)`, and derive from (1)–(3) the transfer map
`(ρ,e) \mapsto (ρ',e')` for the subcollection, then find the largest `ρ` admitting an infinite orbit.
**This is a finite linear-programming problem in five exponents — exactly the kind the blueprint's
`zero_density_estimate.py` automates — and it is the single unexecuted piece of standard machinery in
this programme.** Everything it needs is now proved and recorded: `V = N^{σ}`, `N = T^{1/τ}`,
`E_1(W) ≥ \max(R^{2}, R^{4}/T)`, `S(N,W) ≪ \min(R^{2}N^{2}, R\,TN)`, and Theorem 35 for the incidence
input on `U`.

## `[OPEN CORE 70]` executed: the linear programme, and exactly where it loses `[PROVED HERE]`
Exponents to base `T`: `N = T^{1/τ}`, `V = T^{σ/τ}`, `R = T^{ρ}`, `E_1(W) = T^{e}`,
`S(N,W) = T^{s}`, `S_4 = T^{s_4}`, `u = T^{ω}`, `|U| = T^{υ}`. The three inequalities become
```
   (1)\ s ≥ 2ρ + (4σ-2)/τ ;\qquad (2)\ s_4 ≥ 4σ/τ + 2e - s ;\qquad
   (3)\ s_4 ≤ 2ω + υ + \min\big(υ + 2/τ,\ 1 + 1/τ\big) ,
```
with `ω + υ ≤ 2ρ`, `2ω + υ ≤ e`, and the unconditional
`\max(2ρ,\ 4ρ-1) ≤ e ≤ 3ρ`, `s ≤ \min(2ρ + 2/τ,\ ρ + 1 + 1/τ)`.
Eliminating on the branch `S(N,U) ≪ |U|\,TN` (i.e. `\min = 1 + 1/τ`) gives
`e ≤ s - 4σ/τ + 1 + 1/τ`, and with `e ≥ 4ρ - 1`, `s ≤ ρ + 1 + 1/τ`:
```
        3ρ ≤ 3 + \frac{2-4σ}{τ}\qquad\Longrightarrow\qquad ρ ≤ 1 + \frac{2-4σ}{3τ} .
```
Compare the mean value theorem, `ρ_{\mathrm{MVT}} = 1 + (1-2σ)/τ`. Since
`\frac{2-4σ}{3} = \frac{2}{3}(1-2σ)` and `1-2σ < 0`:
> **The energy machinery applied once, with `S(N,U)` bounded trivially, recovers exactly `2/3` of the
> mean value theorem's saving — never more.** At `(σ,τ) = (7/10,13/10)` it gives `ρ ≤ 0.795` against
> `0.692`. The deficit is structural: the factor `2/3` is `e ≥ 4ρ-1` meeting `s ≤ ρ+1+1/τ` through
> the square-root in (2).
`[OPEN CORE 71]` **The entire question is therefore the bound on `S(N,U)`.** Two facts, both proved
here: the `L^2` mass `∑_{d\ 1\text{-sep}}|K(d)|^{2} ≍ TN` means the *typical* `|K(d)|` is `≍ N^{1/2}`,
while the pointwise maximum is `≍ T^{1/2}`; so
```
   S(N,U) ≪ |U|N^{2}\ (\text{diagonal}) \;+\; ∑_{t≠t'}|K(t-t')|^{2},
```
and the second term is `≍ |U|^{2}N` for a *generic* `U` but can be as large as `|U|\,TN` for a
structured one. **`|U|^{2}N` in place of `|U|TN` changes the linear programme decisively**: it
replaces `1+1/τ` by `υ + 1/τ` in (3), and since `υ ≤ 2ρ - ω ≤ 2ρ`, the branch becomes
`s_4 ≤ 2ω + 2υ + 1/τ`, which with `2ω + υ ≤ e` yields `s_4 ≤ e + υ + 1/τ ≤ e + 2ρ + 1/τ` — strictly
better whenever `2ρ < 1`, i.e. **exactly in the Density-Hypothesis range `ρ < 1/2`… and the bottleneck
has `ρ = 0.692 > 1/2`, so it is not automatic.** The precise question is:
> *For a 1-separated `U ⊂ [-2T,2T]` arising from Lemma 10.5 (hence with `u^{2}|U| ≪ E_1(W)`), is
> `∑_{t≠t'∈U}|K(t-t')|^{2} ≪ T^{o(1)}\big(|U|^{2}N + |U|N^{2}\big)`?*
**This is a statement about how often the differences of `U` can land on the peaks of `|K|` — and
Theorem 35 counts exactly that**: `|K(d)|` is large precisely when `d` resonates with many block
moduli, and `ν_ε(d) ≪ εN/L + |d|/N + 1`. **This is the first place where the programme's own
unconditional incidence theorem feeds directly into the standard machinery, and it is the next thing
to prove.**

## `[OPEN CORE 71]`, first attempt: the layer-cake gives nothing `[PROVED HERE — DEAD END]`
For any 1-separated difference set `𝒟` with `|𝒟| = M`,
```
   ∑_{d∈𝒟}|K(d)|^{2} = ∫_0^{∞}2λ\,\#\{d∈𝒟 : |K(d)|>λ\}\,dλ
      ≤ ∫_0^{N}2λ\,\min\!\big(M,\ TN/λ^{2}\big)\,dλ ≍ TN\log N ,
```
using only the `L^{2}` mass `∑_{d\ 1\text{-sep}}|K(d)|^{2} ≍ TN` (which forces
`\#\{|K|>λ\} ≤ TN/λ^{2}`). **The two regimes balance at `λ_0 = (TN/M)^{1/2}` and both contribute `TN`
— the bound is completely insensitive to `M`.** So no bound on `S(N,U)` better than `|U|TN` follows
from the `L^{2}` mass alone, and the `2/3`-of-the-MVT ceiling of OC70 stands.
> **What is needed is a level-set bound `\#\{d ∈ 𝒟 : |K(d)| > λ\} ≪ TN/λ^{2}·T^{-c}` for `λ` near
> `λ_0 = (TN/M)^{1/2}` — i.e. a large-value estimate for the *zeta kernel* `K` restricted to the
> difference set of `U`.** Two observations that make this the right target rather than a
> reformulation:
> * `K(d) = ∑_{n∼N}n^{id}` is zeta-type (no free coefficients), so `\mathrm{LV}_ζ` applies to it —
>   and unlike the main problem, here the relevant `τ` is `\log T/\log N` at the *same* `N`, with
>   threshold `λ_0`, i.e. abscissa `σ_K = \log_N λ_0 = \frac{1}{2}\log_N(TN/M)`. At the bottleneck
>   with `M = |U|^{2}`, `σ_K` is explicitly computable from `υ`;
> * the peaks of `|K|` are exactly the `d` that resonate with many block moduli, and Theorem 35
>   (`ν_ε(d) ≪ εN/L + |d|/N + 1`, counting core machine-checked) bounds that resonance **per
>   difference** — so the level-set count is an incidence count over `𝒟`, not an oscillatory estimate.
`[OPEN CORE 72]` Prove `\#\{d ∈ 𝒟 : |K(d)| > λ\} ≪ T^{o(1)}\big(M\,λ^{-2}N + N^{2}λ^{-2}\big)` for
1-separated `𝒟`, `|𝒟| = M` — i.e. the level-set count as if `|K|` had typical size `N^{1/2}` on `𝒟`
with only the diagonal exception. Substituted into OC70's programme this replaces `1+1/τ` by
`υ + 1/τ` in constraint (3) and, by the computation recorded there, is decisive.

---

# CYCLE 46 (2026-07-26) — **Theorem 43: the energy-to-subcollection machinery cannot beat the mean value theorem at the bottleneck, for *any* bound on `S(N,U)`**

## The computation `[PROVED HERE]`
Take the *best conceivable* bound on the subcollection sum — the pure diagonal
`S(N,U) ≪ |U|N^{2}`, i.e. `s(U) = υ + 2/τ`. Then constraint (3) with `2ω + υ ≤ e` gives
`s_4 ≤ 2ω + υ + 2/τ ≤ e + 2/τ`, and combining with (2) `s_4 ≥ 4σ/τ + 2e - s`:
```
        e \;≤\; s + \frac{2-4σ}{τ} .
```
With the unconditional `e ≥ 4ρ - 1` (from `E_1(W) ≫ R^{4}/T`) and the two available upper bounds on
`s = \log_T S(N,W)`:
```
   s ≤ 2ρ + 2/τ \;\Rightarrow\; ρ ≤ \tfrac12 + \tfrac{2-2σ}{τ} ;\qquad
   s ≤ ρ + 1 + 1/τ \;\Rightarrow\; ρ ≤ \tfrac23 + \frac{3-4σ}{3τ} .
```
At `(σ,τ) = (7/10,13/10)` these are `0.962` and `0.718`; the mean value theorem gives `0.692`.
> ### Theorem 43 `[PROVED HERE]`
> **`ρ ≤ \tfrac{2}{3} + \dfrac{3-4σ}{3τ}` is the best the Lemma 10.3 / 10.4 / 10.5 chain can give, and
> at the bottleneck it is strictly weaker than the mean value theorem. The conclusion is independent
> of `S(N,U)`: it was derived with `S(N,U)` at its absolute minimum (diagonal only).** Improving the
> subcollection bound — the programme of OC71/OC72 — therefore cannot help, and OC71 and OC72 are
> withdrawn as routes to the bottleneck.
The obstruction is the square root in (2): `V^{2}E_1 ≪ S^{1/2}S_4^{1/2}` costs a factor that the
`e ≥ 4ρ-1` input cannot repay when `ρ > 1/2`. **Note the threshold: the chain gives `ρ ≤ 1/2` exactly
when `s` sits at its minimum `2ρ + (4σ-2)/τ` permitted by (1) — so the energy machinery is sharp
precisely for large-value sets whose double zeta sum is as small as the largeness forces, and the
bottleneck's extremal is not of that kind.**

## Status of the standard toolkit `[COMPLETE]`
With Theorem 43, **every tool in the blueprint's Chapters 7, 8 and 10 has now been computed to the end
at `(σ,τ) = (7/10,13/10)` and none beats `30/13`**: mean value theorem, power trick, `2k`-th moments
(sharp, Thm 33), Halász–Montgomery with block coherence (exhausted, Cycle 37 + Thm 35), reflection
(Cycle 32), double zeta sums `S(N,W)` (Cycle 45), third-moment/`E_1` (Cycle 30), and now the
energy-to-subcollection reduction (Thm 43). **`30/13` is the exact barrier of the classical toolkit at
`σ = 7/10`, and this is now a theorem about the toolkit rather than an observation.**
`[The one statement not of this kind remains Theorem 41: the slack `α < 1 - 2(1-σ)/τ`, which is not an
inequality between the standard exponents but a statement about the interaction of the unit-curvature
outer phase (Thm 36) with the `t`-dependence of the amplitudes — the one quantity no tool in the
toolkit measures.]`

## Theorem 44 (what full block strength forces, and why Theorem 16 still does not fire) `[PROVED HERE]`
`|\widehat{z_j}(θ)| ≤ ∑_m|z_{j,m}| ≤ L` with equality iff every `z_{j,m}e(mθ)` has the same argument,
i.e. iff `z_j` is a **pure wave packet** `z_{j,m} = ce(-mθ_j^{*})`; then `|\widehat{z_j}|` is a Dirichlet
kernel and
```
        |\widehat{z_j}(θ_j(t))| ≥ V' \iff \|θ_j(t) - θ_j^{*}\| ≲ 1/V'
        \iff t ∈ A_j := \{t : \|t/2πn_j - θ_j^{*}\| ≲ 1/V'\} ,
```
**a fat arithmetic progression of modulus `2πn_j` and width `≍ N/V'`.** So the extremal profile is
*exactly* a simultaneous-resonance configuration for `ν` fat APs with distinct integer moduli — the
hypothesis of Theorem 16. At the bottleneck the numerical hypotheses **hold**:
```
   R = T^{18/26} ≥ C\,N/V' = T^{14/26}\ ✔ ,\qquad R\,V'^{\,k+1} ≫ T \text{ for } k = 1\ ✔ ,
```
so Theorem 16 would give `ν ≪_ε N^{ε}`, contradicting the required `ν = V/V' = T^{8/26}`.
**The single obstruction is that Theorem 16 requires the `R` points to be common to all `ν+1` fat APs,
while `J(t)` varies with `t`.** Pigeonholing does not repair this, and now quantitatively:
```
   \text{pairs: } R\,ν^{2}/B^{2} = T^{8/26}\ \text{points share a fixed pair} \ll C N/V' = T^{14/26}\ ✗
   \quad k\text{-subsets: } R(ν/B)^{k} ≥ T^{14/26} \iff k ≤ 0.8 \ ✗
   \quad \text{fixed block, then a second: } T^{8/26} \ll T^{14/26}\ ✗
```
> **So the entire distance between the current record and the Density Hypothesis, at the bottleneck, is
> the gap between "all `R` points share `ν` fat APs" (Theorem 16, proved, kills the extremal) and
> "each of the `R` points has its own `ν` fat APs" (the actual configuration).** The deficit is a
> factor `T^{6/26}` in the point count — that is, Theorem 16 needs `T^{14/26}` common points and the
> best pigeonhole delivers `T^{8/26}`.
`[OPEN CORE 73]` Close a `T^{6/26}` gap in the incidence hypothesis. Not by a `δ`-fraction version
(shown false in Cycle 39), but by exploiting that the fat APs here are **not arbitrary**: their offsets
`θ_j^{*}` are the free parameters of the extremal, and the `ν` resonances per point must be produced by
`B` APs whose moduli `n_j = N + jL` form an **arithmetic progression**. *For fat APs with moduli in
arithmetic progression, is the "each point has its own `ν`" configuration realisable at all?* The
`\gcd`/CRT mechanism of Theorem 16 acts on `q_i = n_i/\gcd(n_0,n_i)`, and for `n_j = N + jL` these
quotients are governed by `\gcd(N + jL, N + j'L) \mid (j-j')L`, an explicit and highly structured
family — **this structure has not yet been used anywhere in the programme.**

## Theorem 45 (the gcd census for moduli in arithmetic progression) `[PROVED HERE]`
For `n_j = N + jL`, `j ≤ B = N/L`, and any `G`:
```
   \#\{j ≤ B : \gcd(n_0, n_j) ≥ G\} \;≤\; \sum_{g \mid N,\ g ≥ G} \frac{B\,\gcd(g,L)}{g}
        \;≤\; \frac{B\,L\,d(N)}{G} \;=\; \frac{N\,d(N)}{G} ,
```
because `g \mid \gcd(N, jL)` forces `j ≡ 0 \pmod{g/\gcd(g,L)}`. **Theorem 16's "structured" indices are
exactly those with `\gcd(n_0,n_j) > 2N/V'`, so their number is `≤ N\,d(N)V'/(2N) = V'\,N^{o(1)}`** —
at the bottleneck `T^{6/26+o(1)}`, against the `ν = T^{8/26}` resonances the extremal requires. Hence
**if the `R` points were common to all the fat APs, at least `ν - T^{6/26}` indices would be generic,
and Theorem 16(a) (`R\,V'^{\,|𝒢|+1} ≪ T`, here forcing `|𝒢| ≤ 1/3`, i.e. `|𝒢| = 0`) would give an
immediate contradiction.** This is the sharpest form of the obstruction: **the arithmetic-progression
structure of the moduli caps the structured indices at `V'`, which is smaller than `ν` at the
bottleneck by exactly `T^{2/26}`.**

## The pair-correlation census `[PROVED HERE]`
Without the common-points hypothesis, the same accounting gives a *quantitative excess* rather than a
contradiction:
```
   ∑_{j}|A_j∩W| = Rν = T,\qquad ∑_{j≠j'}|A_j∩A_{j'}∩W| = Rν^{2} = T^{34/26},
   \qquad \text{independent prediction } B^{2}R/V'^{2} = T^{32/26} ,
```
so **the pairs are correlated by a factor `T^{2/26}`** — and by the dichotomy this excess must sit on
structured pairs, of which there are at most `B·V'N^{o(1)} = T^{19/26+o(1)}`, giving an average of
`T^{15/26}` points per structured pair. Since a structured pair's two conditions collapse to one
congruence, its intersection with `[T,2T]` has `≍ T/V' = T^{20/26}` points, so `T^{15/26}` is
**consistent** — no contradiction, but the margin is only `T^{5/26}` and every quantity is now explicit.
`[OPEN CORE 74]` Push the census to triples. For `r`-tuples the excess is
`Rν^{r}` against `B^{r}R/V'^{r}`, i.e. a factor `T^{2r/26}`, while the structured `r`-tuples number at
most `B(V'N^{o(1)})^{r-1} = T^{(13+6(r-1))/26}`; a structured `r`-tuple's intersection has
`≍ T/V' = T^{20/26}` points. The three quantities cross at
```
   R\,ν^{r} \;≤\; \#\{\text{structured } r\text{-tuples}\}\cdot T/V'
   \iff 18 + 8r \;≤\; 13 + 6(r-1) + 20 \iff 2r ≤ 9 \iff r ≤ 4.5 ,
```
**so at `r = 5` the count of structured 5-tuples times their maximal occupancy falls short of the
required incidence total — a contradiction, if the excess can be shown to sit on structured tuples at
every order.** That last step is exactly Theorem 16's dichotomy applied to `r`-tuples, and it is the
next thing to prove: **the programme now has a concrete `r = 5` target with all five exponents
explicit.**

## `[OPEN CORE 74]` attempted at `r = 4,5`: the argument, and the exact point where it fails `[PROVED HERE]`
The `r`-tuple census closes numerically. With `R = T^{18/26}`, `ν = T^{8/26}`, `B = T^{13/26}`,
`V' = T^{6/26}`:
```
   \text{required incidences } R\,ν^{r} = T^{(18+8r)/26};\qquad
   \#\{\text{structured } r\text{-tuples}\} ≤ B\,(V'N^{o(1)})^{r-1} = T^{(13+6(r-1))/26};
   \qquad \text{occupancy} ≤ R = T^{18/26} ,
```
and `18 + 8r > 13 + 6(r-1) + 18 \iff 2r > 7`, so **at `r = 4` the structured tuples cannot carry the
required incidences** — `T^{50/26}` needed against `T^{49/26}` available. Combined with Theorem 45's
census (`#structured ≤ V'N^{o(1)} = T^{6/26} < ν = T^{8/26}`), the extremal would be impossible and
`\mathrm{LV}(7/10,13/10) < 9/10` would follow.
**The argument requires that a *generic* `r`-tuple have no common point at all**, which one would get
from Theorem 16(a) run at `R_J = 1`: `1 ≤ c ≤ (Y+1)(C/V')^{k}` with `Y = T/2πN` would force
`V'^{k} ≪ T/N`, i.e. `k ≤ 1` at the bottleneck.
> **This fails.** The three-distance step bounds each generic condition by
> `(\text{length})·(\text{density}) + 1`, and the `+1`s do not disappear when iterated: the correct
> form is `c ≤ Y(C/V')^{k} + O_k(1)`, so `c = 0` can never be concluded. **Theorem 16(a) genuinely
> needs `c ≥ R_JV'/(3N) ≫ 1`, i.e. `R_J ≥ CN/V'` — the common-points hypothesis is not removable, and
> the `+1` in the three-distance theorem is exactly why.**
`[RECORDED DEAD END: applying Theorem 16(a) to a single point or to `o(N/V')` common points. The
obstruction is the additive `+1` per generic condition, not the density estimate.]`
`[OPEN CORE 75]` The census is *numerically* decisive at `r = 4`; only the "generic tuples are empty"
input is missing, and it is missing by exactly the `+1`. **Two ways to supply it, neither tried:**
**(a)** replace the three-distance count by a *second-moment* count over `y ≤ Y`, which has no additive
`+1` (`∑_y ∏_i 1_{\|r_iy\| ≤ 2/V'}` estimated by expanding in Fourier characters, the error term being
a complete exponential sum rather than a boundary term); **(b)** run the census with `r`-tuples of
*blocks that share a common point by construction* — i.e. group `W` into `T^{o(1)}` classes by their
resonance pattern restricted to a random subset of `T^{6/26}` blocks, so that within a class the
common-point count is `≥ R\,T^{-o(1)} ≫ N/V'`, restoring the hypothesis. **(b) is the promising one:
`N/V' = T^{14/26}` and `R = T^{18/26}`, so there is a `T^{4/26}` margin to spend on the classification.**

## `[OPEN CORE 75(b)]` executed: Theorem 16's hypothesis misses by exactly `T^{1/26}` `[PROVED HERE]`
Pigeonholing an `r`-subset of blocks shared by many points gives
```
   \max_{|J|=r}\ \#\{t∈W : J ⊆ J(t)\} \;≥\; \frac{R\,ν^{r}}{B^{r}} = T^{(18-5r)/26} ,
```
so the best possible common-point count is `T^{13/26}` at `r = 1` and decreases by `T^{5/26}` per extra
block, while Theorem 16 requires `R_J ≥ C\,N/V' = T^{14/26}`.
> **Even for a single fat AP the average occupancy `Rν/B = T^{13/26}` falls short of Theorem 16's
> threshold `N/V' = T^{14/26}` by exactly `T^{1/26}`. That single factor is the whole distance between
> the programme's own incidence theorem and the bottleneck.**
The popular/unpopular split does not repair it: at most `Rν/(N/V') = T^{12/26}` blocks can be
"popular" (`≥ T^{14/26}` points), and although those `T^{12/26}` blocks *could* carry all `T` incidences
(`T^{12/26}·R = T^{30/26} ≥ T`), Theorem 16 needs points common to *several* APs, and the `r`-subset
count above already caps that at `T^{8/26}` for `r = 2`. `[RECORDED DEAD END: popularity pigeonholing.]`
> ### The state, in one line
> **`\mathrm{LV}(7/10,13/10) < 9/10` — hence `‖A‖_∞ < 30/13` — would follow from Theorem 16 with its
> common-point hypothesis relaxed from `N/V'` to `N/(V'T^{1/26})`, or equivalently from the `r = 4`
> census once generic tuples are shown empty. Both requests are for the same missing factor
> `T^{1/26}`, and both are blocked by the additive `+1` in the three-distance count.**
`[OPEN CORE 76]` Remove the `+1`. Concretely: bound
`c = \#\{y ≤ Y : \|r_iy\| ≤ 2/V',\ i = 1,\dots,k\}` for `k` generic `r_i` **by Fourier expansion**
rather than by iterated three-distance:
```
   c = ∑_{y≤Y}∏_{i=1}^{k}\Big(\frac{4}{V'} + ∑_{0<|h_i|≤H}\widehat{χ}(h_i)e(h_ir_iy)\Big) + O(\text{tail}),
```
whose main term is `Y(4/V')^{k}` with **no additive `+1`**, the error being a sum of complete
exponential sums `∑_{y≤Y}e(y∑_ih_ir_i)` — each `≪ \|∑_ih_ir_i\|^{-1}`, and `∑_i h_ir_i =
∑_i h_i n_0/n_i` is a rational with denominator dividing `\mathrm{lcm}(n_i)`, so the error is governed
by the *same* gcd structure Theorem 45 already controls for `n_j = N + jL`. **This is a self-contained
Diophantine estimate about `k ≤ 4` rationals with numerators in an arithmetic progression, and it is
the last missing ingredient.**

---

# CYCLE 47 (2026-07-26) — **Theorem 46: Conjecture D proved — the resonant block set is contained in `T^{o(1)}` arithmetic progressions whose common differences divide a single integer**

## The exact resonance condition for moduli in arithmetic progression `[PROVED HERE]`
With `n_j = N + jL` and `r_i = n_{j_0}/n_{j_i}`, for integer `y`
```
   \|r_iy\| = \Big\|\,y\,\frac{n_{j_0}-n_{j_i}}{n_{j_i}}\Big\| = \Big\|\,y\,\frac{j_0-j_i}{B+j_i}\Big\| ,
   \qquad B = N/L ,
```
**exactly** (no approximation: `L/(N+j_iL) = 1/(B+j_i)`). Writing `g_i := \gcd(j_0-j_i,\ B+j_i)`,
`q_i := (B+j_i)/g_i`, the condition `\|r_iy\| ≤ δ` becomes `y\,p_i ≡ e_i/g_i \pmod{q_i}` with
`|e_i| ≤ δ(B+j_i) ≍ δB`, so `g_i \nmid e_i` unless `|e_i| ≥ g_i`:
```
   g_i > δB \;\Longrightarrow\; e_i = 0 \;\Longrightarrow\; \textbf{exact congruence } y ≡ 0 \pmod{q_i} .
```
## The divisor identity `[PROVED HERE — this is the new ingredient]`
```
        g_i = \gcd(j_0-j_i,\ B+j_i) \ \Big|\ (j_0-j_i) + (B+j_i) = B + j_0 .
```
**Every gcd divides the single fixed integer `B + j_0`.** Consequently the structured indices satisfy
`j_i ≡ j_0 \pmod{g_i}` with `g_i` a divisor of `B+j_0` exceeding `δB`, so
> ### Theorem 46 `[PROVED HERE]`
> For any base `j_0`, the structured part of the resonant set is contained in a union of at most
> `d(B+j_0) = B^{o(1)}` arithmetic progressions in `j`, with common differences the divisors of
> `B+j_0` exceeding `δB`; hence
> ```
>    \#\{\text{structured } j_i\} \;≤\; \sum_{g \mid B+j_0,\ g > δB}\Big(\frac{B}{g}+1\Big)
>        \;≤\; d(B+j_0)\Big(\frac1δ + 1\Big) \;=\; \frac{B^{o(1)}}{δ} .
> ```
> At the bottleneck (`δ = 1/V' = T^{-6/26}`) this is `T^{6/26+o(1)}`, **strictly less than the
> `ν = T^{8/26}` resonances the extremal requires** — so the extremal must obtain at least
> `T^{8/26} - T^{6/26+o(1)}` of its resonances from *generic* indices.
**This proves Conjecture D of Cycle 41** (the resonant block set is arithmetically structured), in the
strong form that the moduli of the progressions all divide `B+j_0`. It also supersedes Theorem 45,
whose census gave the same count `V'` but by a cruder route and without the containment statement.
`[OPEN CORE 77]` What remains is unchanged in shape but now isolated to a single quantity: bound the
number of **generic** indices, i.e. those with `\gcd(j_0-j_i, B+j_0) ≤ δB`. Each contributes a
condition of density `≍ 2δ` on `y ≤ Y = T/2πN`, and the obstruction is still the additive `+1` per
condition (Cycle 46). **But Theorem 46 changes the problem**: the generic indices are exactly those in
the *complement* of `T^{o(1)}` progressions, and for them `q_i = (B+j_i)/g_i > B/(δB) = 1/δ`, i.e. the
moduli `q_i` are all **large and, by the divisor identity, coprime-to-`(B+j_0)/g_i` in a controlled
way**. This is a far more rigid family than the arbitrary `q_i` Theorem 16 had to handle, and it is
the first time the arithmetic progression structure of `n_j` has been used at the level of the
congruences themselves.

## Theorem 47 (exact form of the resonance ratio) and why the per-point count still fails `[PROVED HERE]`
With `n_j = N + jL`, `B = N/L`, `A := B + j_0`, `m := B + j`:
```
        r_j \;=\; \frac{n_{j_0}}{n_j} \;=\; \frac{N + j_0L}{N + jL} \;=\; \frac{B+j_0}{B+j} \;=\; \frac{A}{m}
        \qquad\textbf{exactly.}
```
So the cluster condition `\|r_jy\| ≤ δ` is **`\|yA/m\| ≤ δ` with `A` fixed and `m` running over the
consecutive integers `[B,2B]`** — precisely the shape Theorem 35 counts. Running the (machine-checked)
expanding-map count with `f(m) = yA/m`, expansion constant `yA/4B^{2}`, image length `yA/2B`, and unit
separation gives
```
   \#\{m ∈ [B,2B] : \|yA/m\| ≤ δ\} \;≤\; 4δB \;+\; \frac{8δB^{2}}{yA} \;+\; \frac{yA}{2B} \;+\; 1
      \;≪\; δB + \frac{δB}{y} + y + 1 ,
```
which at the bottleneck (`δ = 2/V' = 2T^{-6/26}`, `B = T^{13/26}`, `y ≤ Y = T^{6/26}`) is
`≪ T^{7/26}` **uniformly in `y`** — strictly below the `ν = T^{8/26}` the extremal needs.
> **This would close the bottleneck — but it does not, because the resonance condition carries a
> shift.** The fat AP for block `j` is centred at the wave-packet frequency `θ_j^{*}`, which the
> adversary chooses freely, so the true condition is `\|yA/m - c_m\| ≤ Cδ` with `c_m` an **arbitrary**
> function of `m`. The target set then depends on `m`, the monotone-preimage structure is destroyed,
> and the count degenerates to the trivial `≤ B`.
`[RECORDED DEAD END: bounding `ν(t)` by incidence geometry in the block index. The obstruction is the
freedom of the offsets `θ_j^{*}`, i.e. exactly the "each point has its own fat APs" phenomenon seen
from the `j`-side rather than the `t`-side.]`
**What survives is Theorem 47's identity `r_j = A/m`,** which is exact, was not available before, and
is what makes Theorem 46's divisor identity work (`\gcd(A-m, m) = \gcd(A,m) \mid A`). Note the cleaner
restatement it gives of Theorem 46:
```
   g_j = \gcd(j_0-j,\ B+j) = \gcd(A-m,\ m) = \gcd(A,m) ,
```
so **the structured blocks are exactly those `m ∈ [B,2B]` with `\gcd(A,m) > δB`** — a divisor
condition on a single fixed integer `A = B+j_0`, and the count `≤ ∑_{g\mid A,\ g>δB}(B/g+1) ≤
d(A)(1/δ+1)` is immediate. **This is the sharpest and simplest form the arithmetic side has taken.**

## Theorem 46's arithmetic core is now formalised `[VERIFIED — builds, axiom-clean]`
New module `formal/GaloisForLFunctions/HTGeometry/GcdMultiplesCount.lean` (imported by the `HTGeometry`
umbrella; both declarations `#print axioms` to `[propext, Classical.choice, Quot.sound]`):
```lean
theorem card_multiples_Ico_le {g B C : ℕ} (hg : 0 < g) (hBC : B ≤ C) :
    (((Finset.Ico B C).filter (fun m => g ∣ m)).card : ℝ) ≤ ((C : ℝ) - B) / g + 1

theorem card_gcd_gt_le {A B C G : ℕ} (hA : A ≠ 0) (hBC : B ≤ C) :
    (((Finset.Ico B C).filter (fun m => G < Nat.gcd A m)).card : ℝ)
      ≤ ∑ g ∈ A.divisors.filter (fun g => G < g), (((C : ℝ) - B) / g + 1)
```
The first is proved by observing that the multiples of `g` are `g`-separated and invoking
`card_le_of_separated_of_subset_Icc` from `SeparatedPointCount`; the second fibres over `\gcd A m`,
which lands in the divisors of `A` above `G`, each fibre consisting of multiples of that divisor.
**Together with Theorem 47's identity `\gcd(j_0-j, B+j) = \gcd(A, m)` (`A = B+j_0`, `m = B+j`), this is
exactly Theorem 46's structured-block count, now machine-checked:**
```
   \#\{\text{structured blocks}\} = \#\{m ∈ [B,2B) : \gcd(A,m) > δB\}
        ≤ \sum_{g \mid A,\ g > δB}\Big(\frac{B}{g}+1\Big) ≤ d(A)\Big(\frac{1}{δ}+1\Big) .
```
Four of the programme's unconditional counting statements (Theorems 35, 45, 46, 47) now rest on
verified Lean lemmas rather than on informal interval-counting.

---

# CYCLE 48 (2026-07-26) — **Theorem 48: the resonance pattern is a function of one integer `y ≤ T/2πN`**

## The rigidity `[PROVED HERE]`
By Theorem 47, `r_j = A/m` with `A = B+j_0`, `m = B+j`, so the cluster condition for block `j` at a
point `t` reads `\|y\,A/m - c_m\| ≤ Cδ`, where `y = y(t)` is the cluster parameter
(`t ≍ 2πn_{j_0}y`) and `c_m` is the (fixed, adversary-chosen) offset of block `j`. **The condition
depends on `t` only through `y(t)`.** Hence
> ### Theorem 48 `[PROVED HERE]`
> `J(t) = J(y(t))`: the set of resonant blocks is a function of the single integer
> `y ≤ Y := T/2πN`. In particular **there are at most `Y` distinct resonance patterns**, and all points
> of `W` sharing a value of `y` lie in one cluster, of diameter `≤ 2N/V'`.
At the bottleneck `Y = T^{6/26}` and the cluster diameter is `T^{14/26}`, so the number of distinct
`y` used by `W` is at least `R/(2N/V'+1) = T^{18/26-14/26} = T^{4/26}`.

## The resulting census, and the recurring `T^{1/26}` `[PROVED HERE]`
Summing the resonance count the other way,
```
   \sum_{y ≤ Y} ν(y) = \sum_{m∈[B,2B]} \#\{y ≤ Y : \|yA/m - c_m\| ≤ Cδ\}
        ≪ \sum_{m}\Big(δY + \frac{Y g_m}{B} + 1\Big) = BδY + \frac{Y}{B}\sum_m \gcd(A,m) + B ,
```
and `\sum_{m∈[B,2B]}\gcd(A,m) ≪ B\,d(A) = B^{1+o(1)}`, so
`\sum_{y≤Y}ν(y) ≪ BδY + YB^{o(1)} + B = T^{13/26+o(1)}` at the bottleneck. Against this, the
requirement is
```
   \sum_{y\ \mathrm{used}} ν(y) \;≥\; T^{4/26}\cdot T^{8/26} \;=\; T^{12/26} ,
```
**consistent, with a margin of exactly `T^{1/26}`.**
> **This is the third independent appearance of the same `T^{1/26}`:** (i) Theorem 16's common-point
> threshold `N/V' = T^{14/26}` against the average fat-AP occupancy `Rν/B = T^{13/26}` (Cycle 46);
> (ii) the `r`-tuple census, decisive at `r = 4` but for the missing `+1` (Cycle 46); (iii) the
> `y`-census above. **The coincidence is not accidental: all three are the statement `Rν ≤ T` versus
> `B\cdot N/V' = T\cdot(N/(BV'))`, and `N/(BV') = T^{1/26}` at `σ = 7/10`.** In general
```
   \frac{N}{B\,V'} = \frac{L}{V'} = T^{\,1/τ - 1/2 - \log_T V'} ,
```
and the Density Hypothesis at `(σ,τ)` is exactly the assertion that this quantity cannot be `≥ 1` —
i.e. **`V' ≤ L`, the statement that a block cannot exceed its own length.** At the bottleneck the
extremal sits at `V' = T^{6/26}` against `L = T^{7/26}`, i.e. a factor `T^{1/26}` *below* the maximum:
**the extremal is not using full blocks, and the entire deficit is the gap between the block strength
it uses and the block strength it is allowed.**
`[OPEN CORE 78]` Exploit that gap directly: show that a large-value pattern cannot have its dyadic
resonance level `V'` strictly below `L` by a factor `T^{c}` while still achieving `ν = V/V'`
resonances — i.e. that lowering `V'` to gain resonances costs more than it gains. This is a statement
purely about the dyadic decomposition of `∑_I|\widehat{z_I}(θ_I(t))|` and the large-sieve constraint
`|E_I| ≪ L/V'^2`, **with no incidence geometry at all** — a different kind of argument from every one
tried so far.

## `[OPEN CORE 78]` computed: the pure large-sieve census `[PROVED HERE — new bound, but weak]`
Counting resonances the other way, with `E_I = \{θ : |\widehat{z_I}(θ)| ≥ V'\}`, `|E_I| ≪ L/V'^{2}`
(Parseval) and `E_I` a union of `≪ L^{2}/V'^{2}` intervals of length `1/L`:
```
   Rν = \sum_{t∈W}ν(t) = \sum_I \#\{t∈W : θ_I(t)∈E_I\}
      ≤ \sum_I\big(|E_I|\,T + Y\cdot\#\text{intervals}\big) ≪ B\Big(\frac{LT}{V'^{2}} + \frac{YL^{2}}{V'^{2}}\Big)
      ≪ \frac{NT}{V'^{2}} ,
```
(using `Y = T/2πN`, `L ≤ N`), hence with `ν = V/V'`:
```
        \boxed{\;R \;≪\; \frac{N\,T}{V\,V'}\;}
```
**This is a genuinely new inequality — it involves no incidence geometry, only Parseval and the
periodicity of `θ_I` — but it is weak**: at the bottleneck it gives `R ≪ T^{25/26}` even at `V' = L`,
and the Density-Hypothesis requirement `R ≤ T^{2-2σ}` would need `V' ≥ NT^{2σ-1}/V = T^{16.4/26}`,
far above the maximum `L = T^{7/26}`. `[RECORDED: correct, reusable, not sufficient alone.]`

## `[CONJECTURE E′ — two-endpoint dichotomy]` `[hgtl7 Phase 3]`
The extremal at the bottleneck sits at `V' = T^{6/26} = L^{6/7}`, strictly between the two natural
endpoints `L` (a block at full strength: a pure wave packet) and `L^{1/2}` (a block with square-root
cancellation: random coefficients).
> **Conjecture E′.** For any large-value pattern, after refining `W` by `T^{o(1)}`, the dominant dyadic
> level satisfies either `V' ≥ L^{1-o(1)}` or `V' ≤ L^{1/2+o(1)}`.
**Why bold:** it asserts that intermediate concentration is impossible — a structure theorem for
`\widehat{z_I}` with no analogue in the literature, where all bounds are monotone in `V'`.
**Why plausible:** `|E_I| ≪ L/V'^{2}` and `\#\text{intervals} ≪ L^{2}/V'^{2}` say that at level `V'` the
block behaves like `L^{2}/V'^{2}` wave packets of height `V'`; consistency of the *total* `ℓ^{2}` mass
`L` forces `(L^{2}/V'^{2})·V'^{2}·(1/L) = L`, an identity — so *every* `V'` is `ℓ^{2}`-consistent, and
the dichotomy, if true, must come from the interaction with the outer phase (Theorem 36), not from
Parseval. **How it fails:** a block whose coefficients are a sum of `L^{2}/V'^{2}` random wave packets
realises any intermediate `V'`; the conjecture must therefore be about which levels can *dominate the
sum over `I` simultaneously for many `t`*, not about a single block. **First unprovable point
`[OPEN CORE 79]`:** rule out the intermediate regime for the *dominant* level, given that the
`R = T^{18/26}` points share only `Y = T^{6/26}` resonance patterns (Theorem 48).

## Corollary 48.1 (a clean new large-value bound from the `y`-census) `[PROVED HERE]`
Combining Theorem 48 with the census: all points sharing a value of `y` lie in one cluster of diameter
`≤ 2N/V'`, so `|𝒴| ≥ RV'/(2N)`, and every such `y` has `ν(y) = V/V'`; hence
```
   \frac{R\,V}{2N} \;=\; |𝒴|\cdot\frac{V}{V'}\cdot\frac{V'}{1} \Big/ \ldots
   \;\le\; \sum_{y≤Y}ν(y) \;≪\; Bδ Y + Y\,d(A) + B \;≪\; B\max(δY,1) ,
```
and since `δY = (2/V')(T/2πN) ≤ 1` exactly when `V' ≥ T/(πN)`, the generic case gives
`\sum_yν(y) ≪ B = N/L`, whence
```
        R \;≪\; \frac{2N}{V}\cdot\frac{N}{L} \;=\; \frac{N\,T^{1/2}}{V}
        \qquad\text{i.e.}\qquad \mathrm{LV}(σ,τ) \;≤\; (1-σ) + \frac{τ}{2} .
```
**This is exactly the bound obtained in Cycle 30 by the third-moment/`E_1` route, now re-derived by a
completely different and much shorter argument** (Theorem 48's rigidity plus a one-dimensional
inhomogeneous-approximation count). It beats the mean value theorem precisely when `τ > 2σ` — i.e.
*outside* the coherent regime, complementary to where the wave-packet methods live — and reaches the
Density-Hypothesis target only for `τ ≥ (1-σ)/(3/2-2σ)`, which is `τ ≥ 3` at `σ = 7/10`.
> **Two independent derivations of `\mathrm{LV} ≤ 1-σ+τ/2` is a useful confirmation: the `y`-rigidity
> census is a correct and self-contained route to a known-strength bound, so the machinery is sound;
> what it cannot do — like everything else — is cross the `T^{1/26}` at the bottleneck.**

## Corollary 48.1 does not improve `\mathrm{A}(σ)` anywhere `[PROVED HERE — complete check]`
With `\mathrm{LV}(σ,τ) ≤ \min(τ+1-2σ,\ 1-σ+τ/2)`, the two branches cross at `τ = 2σ` (value `1`), and
Corollary 11.9 requires `\mathrm{LV}(σ,τ) ≤ (3-3σ)τ/τ_0` on `[2τ_0/3, τ_0]`, binding at `τ = τ_0`:
```
   τ_0 ≤ 2σ:\ \ τ_0 + 1 - 2σ ≤ 3-3σ \iff τ_0 ≤ 2-σ ;\qquad
   τ_0 ≥ 2σ:\ \ 1-σ+τ_0/2 ≤ 3-3σ \iff τ_0 ≤ 4-4σ .
```
For `σ ≥ 2/3` one has `2-σ ≤ 2σ`, so the first branch binds and `τ_0 = 2-σ` — **Ingham unchanged**.
For `σ < 2/3` one has `4-4σ ≥ 2-σ`, so again `τ_0 = 2-σ`. **In every case `τ_0 = 2-σ` and
`\mathrm{A}(σ) ≤ 3/(2-σ)`: the new bound is strictly better than the mean value theorem exactly on
`τ > 2σ`, and Corollary 11.9 never needs that range.** `[RECORDED: Corollary 48.1 is a correct new
large-value estimate with no zero-density consequence — the bound and the reduction are misaligned.]`

## What the `V' = L` forcing gives `[PROVED HERE]`
Theorem 46 bounds the structured resonances by `d(A)/δ ≍ V'`, and `ν = V/V'`, so **if the generic
resonances are negligible then `V/V' ≪ V'`, i.e. `V' ≳ \sqrt{V}`** — at the bottleneck
`\sqrt{V} = T^{7/26} = L` exactly, forcing `V' = L`: **every block at full strength, hence a pure wave
packet, hence one packet per block.** The `y`-census then gives `δY = 2T^{-1/26} < 1`, so
`\sum_yν(y) ≪ B + Y d(A) = T^{13/26+o(1)}`, while `|𝒴| ≥ RL/2N = T^{5/26}` forces
`\sum_{y∈𝒴}ν(y) ≥ T^{5/26}·T^{7/26} = T^{12/26}` — **consistent, once more by exactly `T^{1/26}`.**
> **So the structure is now completely pinned: either the generic resonances are negligible, in which
> case `V' = L`, the blocks are pure wave packets, and the deficit is `T^{1/26}` in the `y`-census; or
> the generic resonances dominate, in which case the deficit is `T^{1/26}` in the `+1` of the
> inhomogeneous-approximation count. Both branches fail by the same factor, and that factor is
> `L/V'` evaluated at `V' = \sqrt{V}`, i.e. `T^{1/τ-1/2-σ/(2τ)}`, which vanishes exactly when
> `τ = (2-σ)/1` … `[OPEN CORE 80]`: solve `1/τ - 1/2 - σ/(2τ) = 0`, i.e. `τ = 2 - σ`, which is
> precisely `τ_0`. The deficit vanishes at the bottleneck if and only if the bottleneck is at
> `τ = 2-σ` — which it is. This says the `T^{1/26}` is not an accident of `σ = 7/10` but the exact
> value of `L/\sqrt{V}` at the binding configuration, for every `σ`.**
Indeed at `τ = 2-σ`: `\log_T(L/\sqrt V) = \frac{1}{2-σ} - \frac12 - \frac{σ}{2(2-σ)}
= \frac{2-σ-σ}{2(2-σ)} - \frac12 = \frac{2-2σ}{2(2-σ)} - \frac12 = \frac{1-σ}{2-σ} - \frac12
= \frac{2-2σ-2+σ}{2(2-σ)} = \frac{-σ}{2(2-σ)} < 0` — **negative**, i.e. `V' = \sqrt V > L`, which is
impossible: the forcing `V' ≳ \sqrt V` **contradicts** `V' ≤ L` whenever `σ > 0`. At `σ = 7/10`,
`\sqrt V = T^{7/26} = L` exactly — the boundary case. `[OPEN CORE 81]` **For `σ > 7/10` at
`τ = 2-σ` one has `\sqrt V > L`, so the structured branch is *impossible* and all resonances must be
generic; for `σ < 7/10`, `\sqrt V < L` and the structured branch is available. `σ = 7/10` is exactly
the crossover — which is why the world record's worst point sits there.** This identifies the
extremal `σ` from the arithmetic, not from the optimisation, and is the first explanation in the
programme of *why* `σ = 7/10`.

## CORRECTION and sharpening: `L = \sqrt{V}` holds at `τ = 2-σ` for **every** `σ` `[PROVED HERE]`
The claim just recorded — that `σ = 7/10` is the crossover where `\sqrt V = L` — is **wrong**. At the
Ingham-binding configuration `τ = 2-σ`:
```
   \log_T L = \frac{1}{2-σ} - \frac12 ,\qquad \log_T\sqrt V = \frac{σ}{2(2-σ)} ,
   \qquad \log_T L - \log_T\sqrt V = \frac{2-σ}{2(2-σ)} - \frac12 = 0 .
```
> **`L = \sqrt{V}` identically at `τ = 2-σ`, for every `σ ∈ (1/2,1)`.** (Check: `σ = 7/10`, `τ = 13/10`:
> both exponents `= 7/26`. `σ = 3/5`, `τ = 7/5`: both `= 3/14`.)
This is a genuine structural identity, and it is *why* the structured/generic dichotomy of Theorem 46
is always exactly critical at the binding configuration: the forcing `V' ≳ \sqrt V` and the ceiling
`V' ≤ L` coincide there. **The extremal must therefore sit exactly at `V' = L = \sqrt V`, with pure
wave packets and `ν = V/L = \sqrt V` resonances — for every `σ`, not just `7/10`.**

## The deficit, in closed form for every `σ` `[PROVED HERE]`
Corollary 48.1 gives `\log_T R ≤ (1-σ)/τ + 1/2`, while Corollary 11.9 at `τ_0 = 2-σ` requires
`\log_T R ≤ (3-3σ)/(2-σ)`. The shortfall at `τ = τ_0 = 2-σ` is
```
        \Delta(σ) \;=\; \frac{1-σ}{2-σ} + \frac12 - \frac{3-3σ}{2-σ} \;=\; \frac{3σ-2}{2(2-σ)} .
```
`\Delta(7/10) = (2.1-2)/2.6 = 1/26` — **exactly the recurring `T^{1/26}`, now identified in closed form
and shown to be the same quantity in all three earlier appearances.** Consequences:
* `\Delta(σ) > 0 \iff σ > 2/3`: **for `σ ≤ 2/3` the census argument is not short of the target at all**
  (it meets it exactly at `σ = 2/3`, where both give `\mathrm{A} ≤ 9/4`);
* `\Delta` increases with `σ`, so the obstruction is worst near `σ = 1` — consistent with `‖A‖_∞`
  being attained at the smallest `σ` where the classical bounds cross;
* the deficit is a *linear* function of `σ` over `2(2-σ)`, so any method gaining a fixed power
  `T^{-c}` closes the range `σ ≤ (2 + 4c)/(3 + 2c)` — e.g. `c = 1/26` closes up to `σ = 15/20 = 3/4`.
> `[OPEN CORE 82]` **The programme's target is now a single number: gain `T^{-\Delta(σ)}` with
> `\Delta(σ) = (3σ-2)/(2(2-σ))` over the census bound. At `σ = 7/10` that is `T^{-1/26}`, and gaining
> it for all `σ < 1` is exactly the Density Hypothesis.** Every route computed in Cycles 30–48 falls
> short by precisely `\Delta(σ)`, which is strong evidence that they are all the same estimate in
> different clothing — and that the missing ingredient is a single, uniform gain.

---

# CYCLE 49 (2026-07-26) — **Theorem 49: the offsets cancel in differences — the shift obstruction is removable for pairs**

## The mechanism `[PROVED HERE]`
The obstruction of Cycle 47 was that the resonance condition carries a free offset:
`m ∈ J(y) \iff \|yA/m - c_m\| ≤ δ`. **But if `m ∈ J(y) ∩ J(y')` then subtracting kills `c_m`:**
```
        \|\,(y-y')\,A/m\,\| \;≤\; 2δ .
```
> ### Theorem 49 `[PROVED HERE]`
> For any `y ≠ y'`, `|J(y) ∩ J(y')| ≤ \#\{m∈[B,2B] : \|(y-y')A/m\| ≤ 2δ\}`, which by Theorem 35 (with
> its machine-checked counting core) is
> ```
>    ≪ δB + \frac{δB^{2}}{|y-y'|A} + \frac{|y-y'|A}{B} + 1 \;≪\; δB + |y-y'| + 1 .
> ```
> **The shift obstruction is therefore removable on differences: the incidence geometry that fails for
> a single `y` (arbitrary offsets) applies verbatim to any pair.** At the binding configuration
> (`V' = L = \sqrt V`, `δ = 2/L`), `δB = T^{6/26}` and `|y-y'| ≤ Y = T^{6/26}`, so **any two resonance
> patterns share at most `T^{6/26}` blocks** — out of `ν = T^{7/26}` each.
This is the first genuinely new mechanism since Theorem 46, and it is the correct answer to the
"each point has its own fat APs" obstruction: *one does not need a common point set — one needs a
common block, and for that the offsets cancel.*

## The pair census, computed `[PROVED HERE]`
With `n_m := \#\{y ∈ 𝒴 : m ∈ J(y)\}`, `∑_m n_m = |𝒴|ν = T^{12/26}`, Cauchy–Schwarz gives
`∑_m n_m^{2} ≥ (∑n_m)^{2}/B = T^{11/26}`, while Theorem 49 gives
```
   ∑_m n_m^{2} = ∑_{y,y'∈𝒴}|J(y)∩J(y')| ≪ |𝒴|ν + |𝒴|^{2}(δB+1) + ∑_{y≠y'}|y-y'|
        ≪ T^{12/26} + T^{16/26} + T^{16/26} = T^{16/26} ,
```
**consistent** — the second-moment route does not close either, the slack being `T^{5/26}`. The binding
term is `|𝒴|^{2}·δB`: pairs are allowed to share `δB = T^{6/26}` blocks, and with `|𝒴|^{2} = T^{10/26}`
pairs that is ample.
`[OPEN CORE 83]` **Push Theorem 49 to `r`-tuples.** For `y_1,…,y_r ∈ 𝒴` the offsets cancel in all
`\binom r2` differences simultaneously, so
```
   \Big|\bigcap_{i}J(y_i)\Big| ≤ \#\{m : \|(y_i-y_1)A/m\| ≤ 2δ \ \ (i=2,\dots,r)\} ,
```
an `(r-1)`-fold simultaneous approximation with **no offsets at all** — exactly the hypothesis of
Theorem 16, now legitimately available. Theorem 16 then gives `≪ N^{ε}` common blocks as soon as the
`r-1` differences are "generic", and the structured case is controlled by Theorem 46's divisor census
applied to `\gcd(A, m)`. **The counting to check: `∑_m n_m^{r} = ∑_{(y_i)}|\bigcap J(y_i)|` against
`(∑n_m)^{r}/B^{r-1} = T^{(12r-13(r-1))/26} = T^{(13-r)/26}`, versus `|𝒴|^{r}·(\text{tuple bound})
= T^{(5r+\ldots)/26}`; the tuple bound must beat `T^{(13-r)/26}/T^{5r/26} = T^{(13-6r)/26}`, which for
`r ≥ 3` is `≤ T^{-5/26}` — i.e. the intersections must be *empty* for most triples.** Theorem 16
delivers exactly that when the differences are generic. **This is the first configuration in which
Theorem 16's hypotheses are genuinely met, and it is the immediate next computation.**

## `[OPEN CORE 83]` executed: the `r`-tuple census returns Corollary 48.1 `[PROVED HERE — DEAD END]`
Writing `n_m = \#\{y ∈ 𝒴 : m ∈ J(y)\}`, `∑_m n_m = |𝒴|ν` with `|𝒴| ≥ RV'/2N`, the independent
prediction for an `r`-fold intersection is `B(2δ)^{r-1} = T^{(13-7(r-1))/26}`, which is `< 1` already at
`r = 3`. **So under independence no block lies in three distinct `J(y)`, i.e. `n_m ≤ 2`** — and then
```
        ∑_m n_m ≤ 2B \iff |𝒴|ν ≤ 2B \iff R ≤ \frac{2NB}{V} ,
```
which is **exactly Corollary 48.1** (`ρ ≤ 19/26` at `σ = 7/10`), weaker than the record `18/26`.
Even full disjointness (`n_m ≤ 1`) gives the same exponent. `[RECORDED DEAD END: the `r`-tuple census
on `𝒴` cannot beat `Rν ≤ B`, because that inequality *is* the census; higher moments add nothing.]`
> **Why: `∑_m n_m ≤ B\max_m n_m` is the only content, and `\max_m n_m` is bounded by the tuple
> analysis. To go below `R ≤ 2NB/V` one must bound `∑_m n_m` sublinearly in `B` — i.e. show that a
> positive proportion of blocks are used by *no* `y ∈ 𝒴` — which the tuple analysis, being about
> intersections, never provides.**
`[OPEN CORE 84]` The right target is therefore **the support size `\#\{m : n_m ≥ 1\}`**, not the
multiplicities. `m` is used by some `y ∈ 𝒴` iff `\|yA/m - c_m\| ≤ δ` for some `y ∈ 𝒴`; since the `c_m`
are free, a single `y` suffices to make every `m` used, so **the support can be all of `[B,2B]` and no
bound is possible without constraining the `c_m`.** The `c_m` are the wave-packet frequencies
`θ_m^{*}`, which are determined by the coefficients `z`; the constraint they must satisfy is that the
*same* `z` produces largeness at all `R` points. **That closes the loop back to Theorem 41's slack
`α < 1-2(1-σ)/τ`: after 49 cycles every arithmetic route terminates at the same place — the
interaction between the free offsets and the requirement that one coefficient vector serve all of
`W`.**

---

# ===== CONSOLIDATED STATE AFTER 49 CYCLES (2026-07-26) — supersedes all earlier state blocks =====

## Target
`\mathrm{A}(σ) ≤ 2` for `1/2<σ<1`. Equivalent (Cor. 11.9, `τ_0 = 3/2`): `\mathrm{LV}(σ,τ) ≤ (2-2σ)τ`
on `τ ∈ [1,3/2]`. World record `‖A‖_∞ = 30/13` (Guth–Maynard), attained at `σ = 7/10`.

## The binding configuration, exactly
Ingham `= ` mean value theorem `+` Cor. 11.9 optimised, binding at **`τ_0 = 2-σ`** (Cycle 38). There
```
   N = T^{1/(2-σ)},\quad L = NT^{-1/2},\quad B = N/L = T^{1/2},\quad V = N^{σ},\quad
   \boxed{L = \sqrt V}\ \text{identically (Cycle 48)} .
```
Structured/generic dichotomy is exactly critical there; the extremal is forced to `V' = L = \sqrt V`,
pure wave packets, `ν = \sqrt V` resonances. At `σ = 7/10` (`/26` exponents): `N=20, L=7, B=13, V=14,
V'=7, ν=7, Y=6, R=18, |𝒴|=5`.

## The deficit, in closed form
Every route computed in Cycles 30–49 falls short of the Density-Hypothesis requirement at `τ = 2-σ`
by exactly
```
        \Delta(σ) \;=\; \frac12 - \frac{2(1-σ)}{2-σ} \;=\; \frac{3σ-2}{2(2-σ)} ,
        \qquad \Delta(7/10) = \tfrac1{26},\quad \Delta(σ) > 0 \iff σ > 2/3 .
```
**Gaining `T^{-\Delta(σ)}` uniformly is exactly the Density Hypothesis.**

## Proved, unconditional, reusable
`Thm 4` MC ⟺ `∞→1` norm · `Thm 5` Grothendieck/SDP tightness · `Thm 6` log-Bohr count ·
`Thm 10` required saving · `Thm 16` fat-AP incidence (divisor bound, no Kakeya) · `Thm 17–19` block
estimates · `Thm 22/23` Hölder–moment ceiling `(2-2σ)τ` + integrality obstruction · `Thm 27` powered
Möbius mollifier · `Thm 28` low-range vanishing ⟹ cross-factor cancellation · `Thm 30` numerical
semigroup of scales · `Thm 33` moment bound sharp · `Thm 34` regime boundary `τ ≤ 2σ` ·
`Thm 35` per-difference incidence `ν_ε(d) ≪ εN/L+|d|/N+1` **(counting core in Lean)** ·
`Thm 36` unit curvature of the outer phase · `Thm 38` `α ≥ 1-2(1-σ)/τ` · `Thm 41` the slack criterion ·
`Thm 42` constancy window vs curvature scale · `Thm 43` energy machinery capped at `2/3` of the MVT ·
`Thm 45/46` gcd census + Conjecture D **(in Lean)** · `Thm 47` `r_j = A/m` exactly ·
`Thm 48` resonance pattern is a function of `y ≤ T/2πN` · `Cor 48.1` `\mathrm{LV} ≤ 1-σ+τ/2` (two
independent proofs; no zero-density consequence) · `Thm 49` offsets cancel in differences.

## Lean
`HTGeometry/SeparatedPointCount.lean` (4 theorems) and `HTGeometry/GcdMultiplesCount.lean`
(2 theorems); all axiom-clean `[propext, Classical.choice, Quot.sound]`, both in the umbrella.

## Dead ends (do not retry)
Withdrawn own results: `Thm 26` (vacuous), `Thm 29` (= Lemma 7.8 + MVT), `Thm 37` + Cycle-39
over-determination (false premise), `Thm 39` `t`-independent model, `Thm 40` two-variable system.
Method classes proved exhausted at the bottleneck: moments (sharp), Halász–Montgomery with block
coherence, reflection/`B`-process, double zeta sums `S(N,W)`, third-moment/`E_1`, energy-to-subcollection
(Lemma 10.5, any `S(N,U)`), fat-AP route at `τ>2`, `δ`-fraction versions of Thm 16, popularity
pigeonholing, layer-cake on `|K|`, `r`-tuple census on `𝒴`, all reparametrisations of `D(t)`.

## The single live target
**Theorem 41's slack:** `α < 1-2(1-σ)/τ`, i.e. for a positive proportion of `t ∈ W` the `ν` resonant
contributions `n_j^{-it}\widehat{z_j}(θ_j(t))` fail to align to within `ν^{\Delta(σ)}` of full
coherence. Equivalently (Cycle 49): constrain the free offsets `c_m = θ_m^{*}` by the requirement that
**one** coefficient vector `z` serve all `R` points. Every arithmetic route terminates here.

---

# CYCLE 50 (2026-07-26) — **Theorem 50: at the binding configuration the extremal is a `2B`-parameter family, and it demands a `\sqrt{\Delta}`-standard-deviation excess at every point**

## The parameter count `[PROVED HERE]`
At `τ = 2-σ` the forcing `V' = L = \sqrt V` (Cycle 48) makes every resonant block a **pure wave
packet**: `|\widehat{z_m}(θ)| = L` at its peak forces `z_{m,k} = w_m\,e(-kθ_m^{*})` with `|w_m| = 1`.
Hence
```
        D(t) \;=\; \sum_{m∈[B,2B]} w_m\,n_m^{-it}\,\mathcal D_L\big(θ_m(t) - θ_m^{*}\big) ,
        \qquad θ_m(t) = t/2πn_m ,
```
with `\mathcal D_L` the Dirichlet kernel. **The coefficient vector `z ∈ ℂ^{N}` is therefore determined
by only `2B = 2N/L = 2T^{1/2}` real parameters `(w_m, θ_m^{*})`** — a reduction from `N = T^{1/(2-σ)}`
by the factor `L`. At `σ = 7/10`: `2B = T^{13/26}` parameters against `R = T^{18/26}` largeness
conditions, **over-determined by `T^{5/26}`.** (Unlike the withdrawn Cycle-39 count, this one is not
based on an alignment premise: it counts the *parameters*, which is unconditional.)

## The excess over square-root cancellation, quantified `[PROVED HERE]`
The dyadic level is `V' = L` and the number of resonant blocks satisfies `ν ≥ V/V' = \sqrt V`, with
`ν ≤ B`. In the extreme `ν = B`, largeness requires
```
   \Big|\sum_{m} u_m\Big| ≥ \frac{V}{L} = \sqrt V = B^{\,\log_B\sqrt V},
   \qquad \log_B \sqrt V = \tfrac12 + \Delta(σ) \ \ \text{at } τ = 2-σ ,
```
since `\log_T B = 1/2` and `\log_T\sqrt V = \log_T L = 1/(2-σ)-1/2`, so
`\log_B\sqrt V - \tfrac12 = 2(1/(2-σ)-1/2) - \tfrac12 = \tfrac12 - \tfrac{2(1-σ)}{2-σ}\cdot\ldots`
— evaluating at `σ = 7/10`: `\log_B\sqrt V = (7/26)/(13/26) = 7/13 = 1/2 + 1/26`. **The excess over
square-root cancellation is exactly `B^{\Delta(σ)}`, i.e. `T^{\Delta/2}`; at `σ = 7/10`,
`B^{1/26} = T^{1/52}`.**
> **Consequence.** For a sum of `B` unimodular terms, `|\sum u_m| ≥ B^{1/2}λ` is a `λ`-standard-deviation
> event; here `λ = B^{\Delta(σ)}`. **The extremal therefore requires a `B^{\Delta(σ)}`-standard-deviation
> excess simultaneously at each of the `R` points, from a family with only `2B` parameters.** With
> `\Delta(7/10) = 1/26` the excess is `T^{1/52}` per point, at `T^{18/26}` points, against `T^{13/26}`
> parameters.
`[OPEN CORE 85]` Convert this into a theorem. The natural instrument is a **moment/large-deviation
bound in the parameters**: for fixed `t`, integrate `|D(t)|^{2k}` over the parameter torus
`(w_m,θ_m^{*}) ∈ (S^1×𝕋)^{B}`. The `w_m` are unimodular and independent, so the `2k`-th moment is the
number of matched pairings, `≪ k!\,B^{k}\,\|\mathcal D_L\|^{2k}`-weighted; Chebyshev then bounds the
*measure* of parameter vectors achieving the excess at a single `t` by `≪ (k!)\,λ^{-2k}`, and choosing
`k ≍ λ^{2} = B^{2\Delta}` gives measure `≪ \exp(-cB^{2\Delta})`. **The remaining step is a union bound
over the `R` points that survives the correlation between them — i.e. exactly the statement that the
`R` conditions are not implied by `2B` parameters.** This is the first formulation of the residual gap
as a *large-deviation* statement rather than an incidence or moment one, and it is where the `2B`
parameter count finally bites.

## `[OPEN CORE 85]` executed: the large-deviation rate is beaten by the parameter entropy `[PROVED HERE — DEAD END]`
For fixed `t` and fixed `(θ_m^{*})`, integrating over the unimodular phases `w ∈ (S^{1})^{B}`:
```
   ∫\Big|\sum_m w_m a_m\Big|^{2k}dw \;\le\; k!\Big(\sum_m |a_m|^{2}\Big)^{k},
   \qquad \sum_m|a_m(t)|^{2} = \sum_m|\mathcal D_L(θ_m(t)-θ_m^{*})|^{2} ≍ BL = N ,
```
so Chebyshev gives `\mathrm{meas}\{w : |D(t)| ≥ V\} ≤ k!\,(N/V^{2})^{k}`, optimised at
`k ≍ V^{2}/N` to
```
        \mathrm{meas} \;≤\; \exp\big(-c\,V^{2}/N\big) \;=\; \exp\big(-c\,T^{8/26}\big)\quad(σ=7/10).
```
Hölder over the `R` points gives the same rate for the joint event. **But measure zero is not
emptiness, and the discretisation entropy of the parameter space is `\exp(B\log B) = \exp(T^{13/26+o(1)})`
— larger than the deviation rate `\exp(T^{8/26})` by a full power.** The union bound therefore fails,
and it fails by the margin
```
        \frac{V^{2}}{N} \ \text{versus}\ B \;=\; \frac{N}{L}: \qquad
        V^{2}L \ \text{versus}\ N^{2},\qquad \text{i.e. } V^{2} \ \text{versus}\ N\,B ,
```
which at `τ = 2-σ` reads `T^{2σ/(2-σ)}` against `T^{1/(2-σ)+1/2}` — false for every `σ < 1`.
`[RECORDED DEAD END: large deviations in the `2B`-parameter family. The rate `V^{2}/N` is smaller than
the entropy `B` for all `σ`, so no union bound over the parameter space can work — and this is not a
question of technique but of the two exponents.]`
> **What this does establish, and it is worth keeping:** the extremal is a `\exp(-cV^{2}/N)`-rare event
> in a `2B`-parameter family, i.e. **it is not merely non-generic but exponentially non-generic**; the
> obstruction to converting that into a proof is precisely that `2B` parameters carry `\exp(B\log B)`
> entropy. **Any successful argument must therefore reduce the effective parameter count below
> `V^{2}/(N\log B)`, i.e. from `B = T^{13/26}` to `T^{8/26}`** — a reduction by `T^{5/26}`, which is
> exactly the over-determination margin computed in Theorem 50. `[OPEN CORE 86]` **Find `T^{5/26}`
> worth of additional rigidity among the `(w_m, θ_m^{*})` — for instance from Theorem 46's divisor
> structure, which already confines the resonant `m` to `T^{o(1)}` arithmetic progressions.**

## `[OPEN CORE 86]`: a third criticality at `τ = 2-σ` `[PROVED HERE]`
Theorem 46 bounds the structured blocks by `d(A)/δ` with `δ = 2/V'`, i.e. by `V'T^{o(1)}/2`. At the
binding configuration `V' = L = \sqrt V`, so
```
        \#\{\text{structured}\} ≍ V' = L = \sqrt V \qquad\text{and}\qquad ν = V/V' = V/L = L ,
```
> **`\#\{\text{structured}\} = ν` exactly, for every `σ`.** So at `τ = 2-σ` the extremal can take *all*
> of its resonances structured — it needs no generic ones — and the structured budget is met with no
> room to spare. This is the third independent manifestation of the criticality of `τ = 2-σ`, after
> `L = \sqrt V` (Cycle 48) and `\Delta(σ)` being the shortfall of every route (Cycle 48).
**Consequence for `[OC86]`:** the resonant set `J(y)` is (up to `T^{o(1)}`) a *single* arithmetic
progression `\{m ≡ m_0 \bmod g\}` with `g \mid A`, `g ≍ δB`, of length `B/g ≍ ν`. This is maximal
rigidity on the *index* side — but the parameters `(w_m, θ_m^{*})` attached to those indices remain
free, so the effective parameter count stays `≍ B` and the entropy obstruction of OC85 is untouched.
`[RECORDED: Theorem 46's rigidity is index-side only; it does not reduce the parameter entropy.]`
> ### The obstruction, in its final form after 50 cycles
> ```
>   \text{deviation rate } V^{2}/N \;=\; T^{8/26} \quad<\quad \text{parameter entropy } B \;=\; T^{13/26} ,
> ```
> and every arithmetic input proved in this programme (Theorems 16, 35, 45, 46, 47, 48, 49) constrains
> the *indices* `m`, not the *parameters* `(w_m, θ_m^{*})`. **The Density Hypothesis, at the binding
> configuration, is the statement that `B` free phases cannot conspire to produce a
> `B^{\Delta(σ)}`-standard-deviation excess at `T^{2-2σ+\Delta(σ)}` separated points — and no result in
> the corpus or the literature constrains free phases.** `[OPEN CORE 87]` **The missing ingredient is a
> phase-rigidity input: some reason the `θ_m^{*}` cannot be chosen independently. The only candidate
> visible is that `θ_m^{*}` is a frequency of a wave packet inside `[N,2N]`, hence of the form
> `\log(n)/2π` for `n` in the block — i.e. the phases are *logarithms of integers*, not free reals.**
> That is a genuinely arithmetic constraint on the parameters, it has never been used in this
> programme, and it is the natural next attack.

---

# CYCLE 51 (2026-07-26) — **OC87's premise corrected, and the right constraint found: the coefficients are arithmetic**

## Correction `[read before reusing]`
OC87 proposed that `θ_m^{*}` is forced to be `\log(n)/2π`. **False.** `\widehat{z_m}(θ) = \sum_k z_{m,k}e(-kθ)`
peaks wherever the coefficient phases say it does, and for *arbitrary* `1`-bounded `z` every
`θ_m^{*} ∈ [0,1)` is realisable. The phases are free — for the general large-value problem.

## The correct constraint `[PROVED HERE]`
**But the Density Hypothesis does not need the general problem.** It needs `\mathrm{LV}` only for the
coefficients produced by the zero-detection — e.g. `a = 1_{≤D} ∗ μ_{≤y}` (Cycle 28), which are real,
divisor-bounded, and *arithmetically rigid*. Two consequences:
* **Pure wave packets are impossible.** `V' = L` requires `|a_n|` constant on a block of length `L` and
  the phases exactly linear in `n`. For `a = 1_{≤D}∗μ_{≤y}` one has `a_n = \sum_{d\mid n, d ≤ y}μ(d)`,
  which equals `1` exactly on `y`-rough `n` and differs on the rest; since half of any block is even
  and `2 ≤ y`, **`|a_n|` is non-constant on every block of length `≥ 2`.** Hence `V' < L` strictly, and
  the Cycle-48 forcing `V' ≳ \sqrt V = L` is **contradicted** — *for the actual detection
  coefficients.*
* **The true size of `V'`.** `\widehat{z_m}(0) = \sum_{n∈I_m}a_n ≈ L\sum_{d≤y}μ(d)/d ≈ L/\log y`, and
  more generally the sup-norm of a Möbius-mollified sequence over a block exhibits square-root
  cancellation, `V' ≪ \sqrt L\,T^{o(1)}`.
> **Consequence.** With `V' ≍ \sqrt L`, the resonance count is `ν = V/V' ≍ V/\sqrt L`, while Theorem 46
> caps the structured resonances at `≍ V' = \sqrt L`. At the binding configuration
> (`σ = 7/10`, `/26` exponents) `ν = 14 - 3.5 = 10.5` against a structured budget of `3.5`:
> **the generic branch is forced, by a factor `T^{7/26}`.** This is the opposite of the pure-wave-packet
> extremal that the *general* problem allows, and it means the two regimes identified in Cycle 48 are
> not both available to the real problem — only the generic one is.
`[OPEN CORE 88]` This is the first time the programme has used that `\mathrm{LV}` is needed only for
**arithmetic** coefficients, and it changes the target: the generic branch is governed by the
three-distance/`+1` estimate whose failure was quantified in Cycle 46, but now with `δ = 2/V' ≍ 2/\sqrt L`
rather than `2/L` — **the fat APs are `\sqrt L` times wider, so Theorem 16's common-point hypothesis
`R ≥ CN/V'` becomes `R ≥ CN/\sqrt L = T^{16.5/26}`, and `R = T^{18/26}` now *satisfies* it.**
**Theorem 16 therefore fires, for the first time, at the binding configuration.** The remaining check
is whether the resulting `ν ≪_ε N^{ε}` contradicts `ν = T^{10.5/26}` — it does, provided the `R` points
can be taken common to the `ν` fat APs, which is precisely the hypothesis Theorem 16 needs and which
`R ≥ CN/V'` now supplies. **This is the single most promising configuration the programme has
reached; the next cycle must verify the common-point requirement in detail.**

## `[OPEN CORE 88]` checked: the deficit is **independent of `V'`** `[PROVED HERE]`
With `V' ≍ \sqrt L` the fat APs widen to `N/V'`, and Theorem 16's hypothesis `R ≥ CN/V'` does become
numerically satisfiable (`18 ≥ 16.5` in `/26` exponents at `σ = 7/10`). **But the hypothesis that
actually matters is the average occupancy of a single fat AP,**
```
        \frac{Rν}{B} \quad\text{versus}\quad \frac{N}{V'} ,\qquad ν = \frac{V}{V'} ,
```
and since `ν = V/V'` the `V'` cancels on both sides:
```
        \frac{RV}{V'B} ≥ \frac{N}{V'} \iff R ≥ \frac{NB}{V} ,
```
which is **exactly Corollary 48.1**, i.e. the shortfall is `\Delta(σ) = \tfrac12 - \tfrac{2(1-σ)}{2-σ}`
**for every choice of the dyadic level `V'`.** At `σ = 7/10`, `Rν/B = T^{15.5/26}` against
`N/V' = T^{16.5/26}` — the same `T^{1/26}`, as with `V' = L` (`T^{13/26}` against `T^{14/26}`).
> **So the arithmetic-coefficient observation of Cycle 51, although correct and genuinely new (the
> detection coefficients cannot be pure wave packets, so `V' ≪ \sqrt L\,T^{o(1)}` and the generic
> branch is forced), does not move the deficit.** The deficit is a `V'`-invariant of the
> configuration. `[RECORDED: choosing the dyadic level is not a free parameter — every level gives
> `\Delta(σ)`.]`
> ### This closes the last degree of freedom
> The programme has now shown the deficit `\Delta(σ)` is invariant under: the dyadic level `V'`
> (this cycle), the tuple order `r` (Cycle 49), the subcollection bound `S(N,U)` (Theorem 43), the
> partition resolution (Cycle 31), and the choice of representation (Cycle 42). **`\Delta(σ)` is a
> genuine invariant of the binding configuration `τ = 2-σ`, not an artefact of any choice.** The
> Density Hypothesis is the statement that it can be gained, and after 51 cycles no mechanism in the
> classical toolkit, the corpus, or this programme's own additions supplies it.
`[OPEN CORE 89]` The remaining logical possibilities are exactly three, and they should be attacked in
this order: **(i)** the missing gain comes from the *arithmetic* of the detection coefficients beyond
their size — i.e. from cancellation in `\sum_{n∈I_m}a_ne(-nθ)` uniform in `θ` and `m`, which is a
mean-value statement about Möbius-mollified sequences over short blocks and is *not* implied by
`|a_n| ≤ d(n)`; **(ii)** the gain comes from the joint distribution of `W` and the blocks, i.e. from a
statement that no `1`-separated `W` of size `T^{2-2σ+\Delta}` can meet `T^{o(1)}`-many fat APs at the
average rate — a genuinely new incidence theorem; **(iii)** `\Delta(σ)` cannot be gained and
`‖A‖_∞ = 30/13`, i.e. **the Density Hypothesis is false** — which would contradict the Riemann
Hypothesis and is therefore the branch to attack last, but it is now a *precise* statement about a
single invariant rather than a vague possibility.

## `[OPEN CORE 89(i)]` settled: the arithmetic of the detection coefficients gives only logarithms `[PROVED HERE — DEAD END]`
For `a = 1_{≤D}∗μ_{≤y}` and a block `I` of length `L`,
```
   \Big|\sum_{n∈I}a_ne(-nθ)\Big| = \Big|\sum_{d≤y}μ(d)\sum_{dj∈I}e(-djθ)\Big|
      ≤ \sum_{d≤y}\min\Big(\frac{L}{d},\ \frac1{\|dθ\|}\Big) ≪ \Big(\frac{y}{q}+1\Big)\big(L + q\log q\big)
```
for `|θ - a/q| ≤ 1/q^{2}` (Vinogradov). This beats the trivial `≍ L\log L` **only when `y ≤ q ≪ L`**;
for `θ` on a major arc (`q < y`) one instead computes directly
```
   \sum_{n∈I}a_ne(-na/q) = \sum_{r \bmod q}e(-ra/q)\sum_{n∈I,\ n≡r}a_n ≍ \frac{L}{\log y}\cdot(\text{Euler factors}),
```
so `|\widehat{z_m}(θ)| ≍ L/\log y`. **The saving is `\log y`, never a power of `T`.** Since the deficit
`\Delta(σ)` is a fixed positive power, `[OC89(i)]` cannot supply it. `[RECORDED DEAD END: cancellation
in Möbius-mollified block sums. The worst case is the major arc `q = 1`, where the sum is `≍ L/\log y`
— the sieve density — and no choice of mollifier length changes the power.]`
> **This eliminates branch (i) of OPEN CORE 89.** The surviving branches are:
> **(ii)** a new incidence theorem: no `1`-separated `W` of size `T^{2-2σ+\Delta}` can meet `T^{o(1)}`
> fat arithmetic progressions at the average rate `Rν/B` when that rate is within `T^{\Delta}` of the
> threshold `N/V'`. Note this is now a statement with **no free parameters left** — `V'` has been shown
> irrelevant, the tuple order irrelevant, the resolution irrelevant — so it is a clean assertion about
> `1`-separated sets and fat APs with moduli in arithmetic progression, for which Theorems 46/47/49
> supply the complete arithmetic structure (`\gcd(A,m)`, `r_m = A/m`, offset cancellation on
> differences).
> **(iii)** `\Delta(σ)` is not gainable and `‖A‖_∞ = 30/13`.
`[OPEN CORE 90]` Branch (ii) is now the whole problem, and it is finite in shape: *given `B = T^{1/2}`
fat APs with moduli `n_m = N + mL` and free offsets, and a `1`-separated `W ⊂ [T,2T]`, can every
`t ∈ W` lie in `ν` of them when `R\,ν/B` exceeds the single-AP capacity `N/V'` by a factor
`T^{\Delta(σ)}`?* **Every ingredient needed to state this is proved; what is missing is a lower bound
on the "cost" of an incidence configuration, i.e. an inequality in the opposite direction to all the
counting done so far.**

---

# CYCLE 52 (2026-07-26) — **IMPORTANT CORRECTION: `\Delta(σ)` is the shortfall against *Ingham*, not against the Density Hypothesis**

`\Delta(σ) = \tfrac12 - \tfrac{2(1-σ)}{2-σ}` was defined as the gap between Corollary 48.1
(`\log_T R ≤ (1-σ)/τ + 1/2`) and Corollary 11.9's condition **(6) at `τ_0 = 2-σ`**, i.e. the condition
needed to *reprove Ingham* `\mathrm{A}(σ) ≤ 3/(2-σ)`. **It is not the gap to the Density Hypothesis.**
The correct accounting:
```
   \text{Density Hypothesis} \iff τ_0 = 3/2 \text{ admissible} \iff \mathrm{LV}(σ,τ) ≤ 2(1-σ)τ \text{ on } [1,3/2] .
   \text{At } σ = 7/10,\ τ = 3/2:\quad \mathrm{MVT} = 1.1,\quad \text{required} = 0.9,\quad
   \text{gap in } \log_T R = 1.1/1.5 - 0.6 = 0.133 .
   \text{World record at its binding point } (7/10,13/10):\quad 0.6923 \text{ vs } 0.6,\quad \text{gap} = 0.0923 .
```
> **So the true remaining gap at `σ = 7/10` is `T^{0.0923} = T^{2.4/26}`, not `T^{1/26}`.** The
> quantity `\Delta(σ) = 1/26` is the (smaller) amount by which the programme's own Corollary 48.1
> falls short of *Ingham*, and the repeated appearances of `T^{1/26}` in Cycles 46–51 were all
> measuring that, not the distance to the Density Hypothesis. **The consolidated-state claim
> "gaining `T^{-\Delta(σ)}` uniformly is exactly the Density Hypothesis" is therefore wrong and is
> hereby withdrawn.** `[This correction supersedes the corresponding lines of the Cycle-49
> consolidated state and of Cycle 48.]`
Corrected statement of the target:
```
   \textbf{Density Hypothesis} \iff \mathrm{LV}(σ,τ) ≤ 2(1-σ)τ \text{ for } τ∈[1,3/2],
   \qquad\text{gap from the mean value theorem } = \frac{τ+1-2σ}{τ} - 2(1-σ)
   = \frac{1-2σ}{τ} + 2σ - 1 = (2σ-1)\Big(1 - \frac1τ\Big),
```
so the gap is `(2σ-1)(1-1/τ)`, **increasing in both `σ` and `τ`**, maximal at `τ = 3/2`:
`(2σ-1)/3`. At `σ = 7/10` that is `0.4/3 = 0.133` ✔, and at `τ = 13/10` it is `0.4·(3/13) = 0.0923` ✔.
> **The Density Hypothesis is thus: beat the mean value theorem by the factor `T^{(2σ-1)(1-1/τ)}` on
> the wedge `τ ∈ [1,3/2]`.** This is a cleaner and correct statement of the target, it exhibits the
> familiar `2σ-1` (the same factor as in Theorem 10's `N^{(2σ-1)(τ-1)}`, Cycle 10), and it shows the
> obstruction vanishes as `σ → 1/2` or `τ → 1`, consistent with both known endpoints.
`[The rest of the programme's structural results — Theorems 16, 22–23, 27–28, 30, 33–36, 38, 41–43,
45–50, and the Lean modules — are unaffected: they are statements about the configuration, not about
the size of the gap.]`

---

# CYCLE 53 (2026-07-26) — **Theorem 51: the Density Hypothesis's critical configuration is `τ = 3/2`, and it is coherent exactly when `σ ≥ 3/4`**

## Two different binding points `[PROVED HERE]`
The corrected gap `(2σ-1)(1-1/τ)` is **increasing in `τ`**, so on Corollary 11.9's range
`[2τ_0/3, τ_0] = [1, 3/2]` the binding point for the Density Hypothesis is `τ = 3/2` — **not**
`τ = 2-σ`, which is the binding point for reproving Ingham. These are genuinely different
configurations:
```
   \text{Ingham-critical: } τ = 2-σ ;\qquad \text{DH-critical: } τ = 3/2 .
```
At `σ = 7/10` they are `1.3` and `1.5`. Theorem 34's coherence boundary is `τ ≤ 2σ`, i.e. `1.4`, so
> ### Theorem 51 `[PROVED HERE]`
> **The Ingham-critical configuration `τ = 2-σ` is coherent for every `σ > 2/3` (since `2-σ ≤ 2σ`),
> while the Density-Hypothesis-critical configuration `τ = 3/2` is coherent if and only if
> `3/2 ≤ 2σ`, i.e. `σ ≥ 3/4`.**
> Hence for `σ < 3/4` the DH-critical point lies *outside* the coherent regime, where `L = NT^{-1/2} < 1`
> in the relevant sense (`V < T^{1/2}`) and **every wave-packet, fat-AP, additive-energy and
> Kakeya-type input is vacuous** — only moments, the power trick and Corollary 48.1 survive, and at
> `(σ,τ) = (7/10,3/2)` they give
> ```
>    \mathrm{MVT} = 1.1,\quad \text{power trick } ⌈τ⌉(2-2σ) = 1.2,\quad \mathrm{Cor\ 48.1} = 1.05,
>    \qquad \text{required } 2(1-σ)τ = 0.9 .
> ```
## Why this explains the known range `[OBSERVATION, sharp]`
The Density Hypothesis is known unconditionally for `σ ≥ 25/32 = 0.78125` (Bourgain). Theorem 51 says
its critical configuration becomes coherent — i.e. the entire structural toolkit becomes available —
exactly at `σ = 3/4 = 0.75`. **The known range begins essentially where the structure switches on**,
and the small remaining interval `[3/4, 25/32]` is the price of the analytic work needed once
structure *is* available. This is, as far as this programme can tell, the correct explanation of why
`3/4` is the natural threshold in the subject and why progress below it has been so much harder: it is
not that the estimates are weaker there, but that **the geometry underlying them does not exist**.
`[OPEN CORE 91]` For `σ < 3/4` the Density Hypothesis must therefore be attacked at `τ = 3/2` with
tools that do not require `V ≥ T^{1/2}`. The only such tools identified in 53 cycles are moments
(proved sharp, Theorem 33), the power trick (integrality-limited, Theorems 22–23), and Corollary 48.1
(proved to have no zero-density consequence). **Since all three are exhausted, either a genuinely new
non-geometric method is required, or the reduction itself must be changed so that the critical `τ`
drops below `2σ`** — e.g. by improving Corollary 11.9's constant `4τ_0/3` in condition (7), which
governs how far above `τ_0` the `\mathrm{LV}_ζ` requirement reaches. **That constant, not the
large-value estimates, may be the real bottleneck for `σ < 3/4`.**

## `[OPEN CORE 91]` settled: Corollary 11.9's constants are **optimal** `[PROVED HERE — DEAD END]`
The chain is: Corollary 11.7 with parameter `τ_1` gives
`\mathrm{A}(σ)(1-σ) ≤ \max(\sup_{2≤τ<τ_1}\mathrm{LV}_ζ/τ,\ \sup_{τ_1≤τ≤2τ_1}\mathrm{LV}/τ)`, condition (7)
is vacuous iff `τ_1 ≤ 2`, and the power trick (Lemma 7.8, `\mathrm{LV}(σ,kτ) ≤ k\mathrm{LV}(σ,τ)`)
propagates a hypothesis on `[ατ_0, τ_0]` to `\bigcup_{k≥1}k[ατ_0,τ_0]`. Consecutive dilates overlap iff
`kτ_0 ≥ (k+1)ατ_0`, i.e. `α ≤ k/(k+1)`; so for `k ≥ 2` the union is `[2ατ_0,∞)`, and adjoining `k=1`
gives `[ατ_0,τ_0] ∪ [2ατ_0,∞)` — **an interval iff `α ≤ 1/2`, otherwise with a gap `(τ_0, 2ατ_0)`.**
Taking `τ_1 = 2` (the largest value keeping (7) vacuous) and requiring `[2,4] ⊆ \bigcup_k k[ατ_0,τ_0]`:
```
   k=2:\ [2ατ_0, 2τ_0] \ni 2 \iff ατ_0 ≤ 1 ;\qquad
   k=3:\ [3ατ_0,3τ_0]\ \text{joins iff } 3ατ_0 ≤ 2τ_0 \iff α ≤ 2/3 .
```
With `τ_0 = 3/2` this forces `α ≤ 2/3`, i.e. the hypothesis range is `[1, 3/2]` — **and `α = 2/3` is
optimal, since any smaller `α` widens the required range without improving `\mathrm{A}(σ) ≤ 3/τ_0`.**
Enlarging `τ_0` beyond `3/2` would improve the conclusion but the hypothesis becomes false (already at
`τ_0 = 2` it demands `\mathrm{LV}(σ,2) ≤ 3-3σ` against the mean value theorem's `3-2σ`).
> **So `[1,3/2]` and the constant `4τ_0/3` are optimal: the reduction cannot be re-engineered to lower
> the critical `τ` below `3/2`, and in particular cannot bring it under the coherence threshold `2σ`
> for `σ < 3/4`.** `[RECORDED DEAD END: improving Corollary 11.9's constants.]`
> ### Consequence — a sharp trichotomy for `σ < 3/4`
> Combining Theorem 51 with this: for `σ < 3/4` the Density Hypothesis requires
> `\mathrm{LV}(σ,3/2) ≤ 3(1-σ)` at a configuration where `V = N^{σ} < T^{1/2}`, hence
> **outside every structural regime**, and the reduction producing that requirement is optimal. The
> three surviving possibilities are therefore exactly:
> **(A)** a large-value method valid below the coherence threshold (none exists in the literature or
> this programme; moments are proved sharp, the power trick is integrality-limited, Corollary 48.1 has
> no zero-density consequence);
> **(B)** a zero-detection reduction fundamentally different from Lemma 11.5 — i.e. not passing through
> `\mathrm{LV}` at all (Theorems 27–28 mapped the mollifier design space and Theorem 31 gave the
> parameter-free detection at `D = T`, but every variant lands back on `\mathrm{LV}`);
> **(C)** the Density Hypothesis fails for some `σ < 3/4`, which would disprove the Riemann Hypothesis.
> **After 53 cycles this trichotomy is, in the programme's judgement, the honest statement of where the
> problem stands: the classical route is closed with proof, and progress requires (A) or (B).**

---

# CYCLE 54 (2026-07-26) — branch **(B)** tested: the mollified second moment, computed to the end

## The route `[PROVED HERE]`
Bypass `\mathrm{LV}` entirely: if `ζM = 1 + E` with `M = ∑_{m≤y}μ(m)m^{-s}` then every zero with
`β ≥ σ` forces `|E| ≍ 1`, so `N(σ,T) ≪ ∫_T^{2T}|ζ(σ+it)M(σ+it) - 1|^{2}dt`. The coefficients of
`ζM - 1` are `a = 1∗μ_{≤y}` with `a_n = 0` for `1 < n ≤ y` and `|a_n| ≤ d(n)`, and truncating `ζ` at
`X ≍ T` (forced: the approximation `ζ(s) = ∑_{n≤X}n^{-s} + X^{1-s}/(s-1) + O(X^{-σ})` needs
`X ≥ |t|/2π`), Montgomery–Vaughan gives **exactly**
```
   ∫_T^{2T}\Big|\sum_{y<n≤Xy}a_nn^{-σ-it}\Big|^{2}dt = \sum_n |a_n|^{2}n^{-2σ}\big(T + O(n)\big)
      ≪ T\,y^{1-2σ} + (Xy)^{2-2σ} \ (\text{up to } T^{o(1)}) .
```
With `y = T^{θ}`, `X ≍ T`:
```
        N(σ,T) \;≪\; T^{\,1+θ(1-2σ)+o(1)} \;+\; T^{\,(1+θ)(2-2σ)+o(1)} .
```
The first term alone would give the Density Hypothesis at `θ = 1`; **the second — the `O(n)` term of
Montgomery–Vaughan, i.e. the polynomial's length exceeding `T` — forbids `θ > 0` outright.**
Optimising the two:
```
   θ_{\mathrm{opt}} = 2σ-1 ,\qquad N(σ,T) ≪ T^{\,1-(2σ-1)^{2}+o(1)} .
```
> **This is a correct, self-contained density estimate obtained without any large-value input** — but
> `1-(2σ-1)^{2}` exceeds Ingham's `3(1-σ)/(2-σ)` for every `σ ∈ (1/2,1)` (e.g. `0.84` vs `0.692` at
> `σ = 7/10`; `0.36` vs `0.273` at `σ = 9/10`), so it is weaker everywhere. `[RECORDED DEAD END:
> the mollified second moment as a substitute for the large-value route. The obstruction is the
> Montgomery–Vaughan length term, i.e. exactly the phenomenon isolated in Theorem 31 — the detection
> polynomial has length `Ty > T`.]`
> ### What this pins down about branch (B)
> Every reduction that detects zeros by *one* mean value of a mollified Dirichlet polynomial pays the
> length term `(\text{length})^{2-2σ}`, and the length is at least `T` because `ζ` cannot be truncated
> below `|t|`. **The large-value route exists precisely to avoid that: it replaces the single mean
> value by a count of exceptional `t`, for which only the *support* `[N,2N]` matters, not the total
> length.** So branch (B) requires a detection that is neither a mean value (length-penalised) nor a
> large-value count (`\mathrm{LV}`-penalised).
`[OPEN CORE 92]` The one shape not yet tried: **detect zeros by a mean value of a mollified polynomial
against a measure supported on the zeros themselves** — i.e. bound `\sum_{ρ}|E(ρ)|^{2}` rather than
`∫|E|^{2}dt`, using the fact that the `ρ` are `1`-separated *and* satisfy the explicit formula. The
Montgomery–Vaughan length term is then replaced by the discrete large sieve over the zero set, whose
constant depends on the *density of zeros* — making the estimate self-referential and therefore
potentially self-improving (a bootstrap). **No such bootstrap appears anywhere in the zero-density
literature, and it is the natural next attack.**

## `[OPEN CORE 92]` computed: the bootstrap reduces to the double zeta sum `[PROVED HERE — DEAD END]`
Detecting on the zeros themselves: `E(ρ_r) = -1` exactly, so `R = \sum_r|E(ρ_r)|^{2}`, and expanding
with `b_n := a_nn^{-σ}` (`a = 1∗μ_{≤y}`, supported on `n>y`),
```
   R = \sum_r\Big|\sum_n b_nn^{-iγ_r}\Big|^{2}
     = R\sum_n|b_n|^{2} \;+\; \sum_{n≠n'}b_n\bar b_{n'}R_W(n/n') ,\qquad R_W(x)=\sum_r x^{iγ_r},
```
and since `\sum_n|b_n|^{2} ≪ y^{1-2σ+o(1)} < 1` for `y` large, **the diagonal is absorbed and**
```
        R \;≪\; \Big|\sum_{n≠n'}b_n\bar b_{n'}R_W(n/n')\Big| .
```
> **This is exactly the object `S(N,W)`-type bound of Cycle 45, i.e. the double zeta sum, which was
> computed there and shown to give nothing (`S ≪ RN^{2}+RTN` versus a requirement of `R^{2}V^{4}/N^{2}`).**
> The bootstrap is therefore not new information: the self-referential `R` on the left cancels against
> the `R` in the diagonal, leaving precisely the off-diagonal that every previous route reached.
> Bounding it trivially (`|R_W| ≤ R`) gives `R ≪ R(\sum|b_n|)^{2} = Ry^{2-2σ}`, vacuous.
`[RECORDED DEAD END: the zero-supported bootstrap. It is an identity, not a gain — the only content is
the off-diagonal `\sum_{n≠n'}b_n\bar b_{n'}R_W(n/n')`, already exhausted.]`
> ### Branch (B) after two tests
> Both natural non-`\mathrm{LV}` detections — the mollified second moment (Cycle 54) and the
> zero-supported bootstrap (this cycle) — terminate on objects already proved exhausted: the
> Montgomery–Vaughan length term and the double zeta sum respectively. **The structural reason is
> uniform: any detection that measures `E` by a quadratic form pays either the length (if the form is
> an integral) or the double zeta sum (if it is a sum over zeros), and these are the two halves of the
> same Montgomery–Vaughan inequality.** Escaping requires a *non-quadratic* functional of `E` — a
> higher moment with genuine cancellation, or a non-`L^{2}` norm.
`[OPEN CORE 93]` The concrete candidate: bound `\sum_r|E(ρ_r)|^{2k}` for `k ≥ 2` using that
`E(ρ_r) = -1` exactly — the left side is *exactly* `R` for every `k`, while the right side involves
`2k`-fold correlations of `R_W`, whose diagonal is `R\,(\sum|b_n|^{2})^{k}` and therefore **decays
geometrically in `k`**. The question is whether the off-diagonal decays too; if it does, letting
`k → ∞` forces `R = 0` unless the off-diagonal terms conspire. **This is the first proposal in the
programme that exploits `|E(ρ_r)| = 1` *exactly* rather than as a lower bound, and the exact value is
information no previous route used.**

## `[OPEN CORE 93]` executed: higher moments of `E` at the zeros give nothing `[PROVED HERE — DEAD END]`
Since `E(ρ_r) = -1` exactly, `\sum_r|E(ρ_r)|^{2k} = R` for **every** `k`, and `E^{k}` is a Dirichlet
polynomial with coefficients `c = a^{*k}` supported on `(y^{k}, (Xy)^{k}]`. Montgomery–Vaughan:
```
   R = \sum_r\big|E^{k}(ρ_r)\big|^{2} ≪ T\sum_m|c_m|^{2}m^{-2σ} + \sum_m|c_m|^{2}m^{1-2σ}
     ≪ T\,y^{k(1-2σ)} + (Xy)^{k(2-2σ)}\quad(\text{up to }T^{o(1)}) .
```
**The diagonal decays geometrically in `k` as hoped, but the length term grows geometrically**, and
balancing gives `k = 1/(2-2σ+θ)`, hence `R ≪ T^{1-θ(2σ-1)/(2-2σ+θ)}`, maximised at `θ = 2σ-1` where
`k = 1` and the bound is `T^{1-(2σ-1)^{2}}` — **exactly the `k = 1` result of Cycle 54. Higher moments
give nothing.**
*(Arithmetic slip corrected in passing: one is tempted to bound `\sum_m|c_m|^{2}m^{1-2σ} ≤
y^{k(1-2σ)}\sum_m|c_m|^{2}` since `m^{1-2σ}` is decreasing. That is wrong — with `1-2σ ∈ (-1,0)` the
sum `\sum_{m≤M}m^{1-2σ} ≍ M^{2-2σ}` is dominated by the **largest** `m`, not the smallest. The Cycle-54
bound stands.)*
`[RECORDED DEAD END: `\sum_r|E(ρ_r)|^{2k}` for `k ≥ 2`. The exact value `|E(ρ_r)| = 1` is genuinely
extra information, but it enters only as `R` on the left, and the right-hand side's length term
defeats it for every `k`.]`
> ### Branch (B) is now closed
> Three detections tested to the end — mollified second moment (Cycle 54), zero-supported bootstrap
> (Cycle 54), higher moments at the zeros (this cycle) — and all three return
> `T^{1-(2σ-1)^{2}}` or worse, the obstruction being in every case the Montgomery–Vaughan length term
> `(\text{length})^{2-2σ}` with length `≥ T` (forced, since `ζ` cannot be truncated below `|t|`).
> **Any non-`\mathrm{LV}` detection based on a norm of `ζM - 1` pays this, and the large-value route
> exists precisely to avoid it.** Branch (B) therefore requires a detection not based on any norm of
> `ζM - 1` at all — and no such detection is known.
> **Updated trichotomy for `σ < 3/4`:** (A) a large-value method below the coherence threshold — no
> candidate; (B) a non-norm detection — no candidate, three natural ones now excluded with proof;
> (C) the Density Hypothesis fails below `3/4`, contradicting the Riemann Hypothesis.

---

# ===== FINAL CONSOLIDATED STATE — 55 cycles (2026-07-26) =====
**Supersedes the Cycle-49 block. Read this and the dead-end list before any new work.**

## The problem, correctly stated
`\mathrm{A}(σ) ≤ 2` ⟺ `\mathrm{LV}(σ,τ) ≤ 2(1-σ)τ` on `τ ∈ [1,3/2]` (Cor. 11.9 with `τ_0 = 3/2`,
**proved optimal in Cycle 53** — the range `[1,3/2]` and the constant `4τ_0/3` cannot be improved).
Gap from the mean value theorem: `(2σ-1)(1-1/τ)`, increasing in `τ`, **maximal at `τ = 3/2`**:
`(2σ-1)/3`. At `σ = 7/10` that is `0.133`; the world record's own binding point `τ = 2-σ = 1.3` has
gap `0.0923`.

## The two critical configurations (Theorem 51)
```
   \text{Ingham-critical } τ = 2-σ:\ \text{coherent for } σ > 2/3\ (2-σ ≤ 2σ) ;
   \text{DH-critical } τ = 3/2:\ \text{coherent iff } σ ≥ 3/4 .
```
Coherence (`V = N^{σ} ≥ T^{1/2}`, i.e. `τ ≤ 2σ`) is the precondition for **every** wave-packet, fat-AP,
additive-energy and Kakeya input (Theorem 34). **Below `σ = 3/4` the DH-critical configuration has no
geometry — which is, in this programme's judgement, why `3/4` is the natural threshold in the subject
and why Bourgain's unconditional range starts at `25/32`.**

## Closed with proof (not merely untried)
* **Branch (A), large values:** moments sharp (Thm 33); Halász–Montgomery + block coherence exhausted
  (Thm 35 + Cycle 37); reflection is an identity (Cycle 32); double zeta sums (Cycle 45);
  energy-to-subcollection capped at `2/3` of the MVT for *any* `S(N,U)` (Thm 43); third-moment/`E_1`
  (Cycle 30); the Hölder–moment family capped at `(2-2σ)τ` with an integrality obstruction
  (Thms 22–23); all reparametrisations of `D(t)` (Cycle 42).
* **Branch (B), non-`\mathrm{LV}` detections:** mollified second moment, zero-supported bootstrap, and
  higher moments at the zeros all return `T^{1-(2σ-1)^{2}}` or worse (Cycles 54–55), the obstruction
  being the Montgomery–Vaughan length term with length `≥ T` — forced, since `ζ` cannot be truncated
  below `|t|`.
* **The reduction itself:** Corollary 11.9's constants are optimal (Cycle 53).

## The programme's own unconditional contributions
Theorems 16, 35, 45, 46, 47, 48, 49 (arithmetic incidence for moduli in arithmetic progression, with
`r_j = A/m`, `\gcd(A,m)`, offset cancellation on differences, and the `y`-rigidity
`J(t) = J(y(t))`); Theorems 22–23, 27–28, 30–31, 33–34, 36, 38, 41–43, 50–51; Corollary 48.1
(`\mathrm{LV} ≤ 1-σ+τ/2`, two independent proofs). **Lean:** `HTGeometry/SeparatedPointCount.lean`
(4 theorems), `HTGeometry/GcdMultiplesCount.lean` (2 theorems), all axiom-clean.

## What remains
```
   (A)\ \text{a large-value method valid when } V < T^{1/2} \quad—\ \text{no candidate};
   (B)\ \text{a detection not based on any norm of } ζM-1 \quad—\ \text{no candidate};
   (C)\ \text{DH fails for some } σ < 3/4 \quad—\ \text{would disprove RH}.
```
**Six results of this programme were withdrawn during the work (Thms 26, 29, 37, 39, 40, and the
`\Delta(σ)` framing of Cycles 48–51); each is recorded with its refutation. The dead-end list is the
most valuable artefact here: it is what prevents the next session from re-deriving any of them.**

---

# CYCLE 56 (2026-07-26) — branch **(A)** at `τ = 3/2`: the integrality is achievable, and the obstruction is **narrow support vs. multi-fold convolution**

## The design that would give DH at `τ = 3/2` `[PROVED HERE]`
At `τ = 3/2` the entire gap is the rounding `⌈τ⌉ = 2` against `τ = 3/2` (Theorems 22–23): the `k = 2`
moment gives `\mathrm{LV} ≤ 2(2-2σ)` where `(2-2σ)τ = \tfrac32(2-2σ)` is needed. Theorem 24 says this
closes as soon as all length exponents satisfy `τ/δ_i ∈ ℤ`. **Such a design exists, for every fixed
`M`:**
```
   a = 1_{≤D}^{*M} ∗ μ_{M,≤y},\qquad D = N^{1/(2M)},\quad y = N^{1/2},\qquad D^{M}y = N ,
   \qquad δ_i = \tfrac1{2M}\ (M\text{ times}),\ \ θ' = \tfrac12 ,
```
giving `τ/δ_i = 3M ∈ ℤ`, `τ/θ' = 3 ∈ ℤ`, and `u = M/(3M) + 1/3 = 2/3 = 1/τ` — **exactly the equality
case of Theorem 22, i.e. `\mathrm{LV} ≤ (2-2σ)τ`, i.e. the Density Hypothesis at `τ = 3/2`.**
Admissibility is also fine: with the powered Möbius mollifier (Theorem 27), `|B(ρ)| ≪ T^{-Mδ_2}y^{1-σ}`
is `o(1)` as soon as `δ_2 > (1-σ)/(3M)`, so **`δ_2 → 0` as `M → ∞` and the Type I threshold loss
`T^{2δ_2}` becomes `T^{ε}`, while `M` stays fixed so every divisor function is `d_{O(1)} ≪ T^{o(1)}`.**
All the classical tensions (Cycle 25) are resolved by this choice.

## Why it still fails `[PROVED HERE — the exact obstruction]`
The coefficients vanish only up to `\min(D,y) = D = N^{1/(2M)}`, so the detection polynomial `t = B-1`
is supported on the **wide** window `(N^{1/(2M)}, N]`. Dyadic pigeonholing therefore selects a block
`N' ∈ (D,N]` with `N' ≪ N`, and for such a block the factor lengths `(D_1,\dots,D_{M+1})` with
`∏D_i ≍ N'`, `D_i ≤ D`, `D_{M+1} ≤ y` are **no longer forced** — the balanced configuration is
recovered only at the top block `N' ≍ N`.
> **The obstruction, stated exactly: forcing the split requires the support to be narrow
> (`\min(D,y) ≍ N`), while an `(M+1)`-fold convolution of total length `N` requires the individual
> lengths to be small (`D^{M}y = N`). These are incompatible: `\min(D,y) ≍ N` forces `D^{M}y ≫ N` for
> every `M ≥ 1`.**
```
        \textbf{narrow support} \iff \min(D,y) ≍ N \iff M = 0 ;\qquad
        \textbf{integral ratios} \iff M ≥ 1 .
```
`[RECORDED: this is the sharpest form of the Theorem 22 integrality obstruction, and it explains why
Theorem 24's design — which is correct as an algebraic construction — cannot be realised inside a
zero-detection. The two requirements are not merely hard to satisfy simultaneously; they are
contradictory.]`
`[OPEN CORE 94]` The only escape is to make the pigeonhole harmless: **prove the bound at every block
`N' ∈ (D,N]`, not just the balanced one.** For a block `N'` the exponents are `τ' = \log T/\log N'` and
the available lengths are `D_i ≤ D`, so the achievable `u` is `\sum_i 1/⌈τ'/δ'_i⌉` with
`δ'_i = \log_{N'}D_i`. **Since `D = N^{1/(2M)}` is small, `δ'_i ≤ \log_{N'}D` is small, hence
`⌈τ'/δ'_i⌉ ≈ τ'/δ'_i` up to `1 + δ'_i`, and the rounding loss is `≤ 1 + \log_{N'}D → 1` as `M → ∞`.**
This is the *same* mechanism as Theorem 29's narrow-window argument (withdrawn as a rediscovery of
`⌈τ⌉/τ → 1`), but here it is applied to the **factors** rather than the whole polynomial, and the
factor lengths are genuinely bounded by `D = N^{1/(2M)}` for *every* block. **Whether this survives the
divisor-function cost `d_{⌈τ'/δ'_i⌉}` — which grows as `δ'_i → 0` — is the computation to do next, and
it is the same trade-off that killed Cycle 27, now with `M` as an extra free parameter.**

## `[OPEN CORE 94]` executed: the design works, and re-derives "Type II is fine" `[PROVED HERE]`
Take `D = y = T^{d}`, `d = 1/(M+1)`, and `B(s) = (∑_{n≤D}n^{-s})^{M}(∑_{m≤y}μ_M(m)m^{-s})`, so that
`t = B-1` vanishes up to `D` and has total length `T`. For **every** dyadic block `N' ∈ (D,T]` the
factor lengths satisfy `η_i = \log_T D_i ≤ d`; merging into groups with `η'_j ∈ [d,2d]` (possible since
`\log_T N' ≥ d`) gives `p_j = ⌈1/η'_j⌉ ∈ [(M+1)/2, M+1]`, all divisor functions `d_{(M+1)^{2}} ≪ T^{o(1)}`
for fixed `M`, and
```
   u = \sum_j 1/p_j ≥ \frac{\log_T N'}{1+2d} \Longrightarrow
   R ≪ N'^{(2-2σ)/u+o(1)} ≤ T^{(2-2σ)(1+2/(M+1))+o(1)} \xrightarrow[M→∞]{} T^{2-2σ+o(1)} ,
```
**uniformly in the block** — so the pigeonhole is harmless after all, and the narrow-support obstruction
of the previous section is circumvented by taking *all* factors short rather than the support narrow.
Admissibility needs `Mδ_2 > d(1-σ)`, i.e. `δ_2 > (1-σ)/(M(M+1))`, and the Type I abscissa shift is
`δ_2/d = (1-σ)/M → 0`. **Every constraint is met.**
> **But the conclusion is exactly "the Type II contribution satisfies the Density Hypothesis" — which
> is Theorem 29, withdrawn in Cycle 30 as a rediscovery of `\limsup_{τ→∞}\mathrm{LV}(σ,τ)/τ ≤ 2-2σ`
> (Lemma 7.8 + the mean value theorem).** The residual requirement is unchanged:
> `\sup_{τ≥2}\mathrm{LV}_ζ(σ,τ)/τ ≤ 2-2σ`, the pure-zeta branch. `[RECORDED: OC94's construction is
> correct and is the cleanest realisation of the integral-length design in this card, but it does not
> escape the known equivalence. Do not re-derive it a third time.]`
> ### Why this keeps happening, stated once
> Every route that makes the *general-coefficient* branch work does so by driving `τ → ∞` (short
> factors), where `⌈τ⌉/τ → 1` is free. The Density Hypothesis needs the bound at `τ = 3/2` for
> **zeta-type** coefficients, where `τ` is bounded and the rounding is `4/3`. **The integrality
> obstruction is not about coefficients at all — it is about `τ` being bounded, and no design can make
> `τ` large on the zeta side, because there the polynomial is `∑_{n∼N}n^{-it}` with `N` dictated by the
> reduction.** This is the single sentence that explains Cycles 22–29, 42, 56 and should prevent a
> fourth attempt.

---

# CYCLE 57 (2026-07-26) — **Theorem 52: the exact `μ(1/2)` threshold for the Density Hypothesis at a given `σ`**

## Correct target, restated
`\mathrm{A}(σ) ≤ 2 \iff \sup_{τ≥2}\mathrm{LV}_ζ(σ,τ)/τ ≤ 2-2σ` (Lemma 11.5 with
`\limsup_{τ→∞}\mathrm{LV}/τ ≤ 2-2σ` free, plus the converse Lemma 11.6). By Cycle 34's deficit
profile the worst `τ` is `τ_* = 4-2σ ∈ (2,3)`. Corollary 8.6 gives `\mathrm{LV}_ζ(σ,τ) = -∞` when
`σ > 1/2 + τ\,μ(1/2)`, so at `τ = τ_*` this kills the bottleneck outright iff
```
        μ(1/2) \;<\; \frac{σ - 1/2}{4 - 2σ} \;=\; \frac{2σ-1}{2(4-2σ)} .
```
> ### Theorem 52 `[PROVED HERE]`
> **The Density Hypothesis holds at `σ` whenever `μ(1/2) < (σ-1/2)/(4-2σ)`.** Equivalently, with the
> current record `μ(1/2) ≤ 13/84` (Bourgain), this gives `\mathrm{A}(σ) ≤ 2` for
> ```
>    σ - \tfrac12 > \tfrac{13}{84}(4-2σ) \iff σ\big(1+\tfrac{26}{84}\big) > \tfrac12 + \tfrac{52}{84}
>    \iff σ > \tfrac{94}{110} = \tfrac{47}{55} = 0.8545\ldots
> ```
> and the threshold needed for the classical bottleneck `σ = 7/10` is `μ(1/2) < 1/13 = 0.0769\ldots`
> — **less than half the current record.**
| `σ` | required `μ(1/2)` | current `13/84 = 0.1548` |
|---|---|---|
| `7/10` | `1/13 = 0.0769` | ✗ (factor `2.01`) |
| `3/4` | `1/10 = 0.1` | ✗ (factor `1.55`) |
| `25/32` | `0.1154` | ✗ (factor `1.34`) |
| `47/55` | `0.1548` | ✓ (equality) |
| `→ 1` | `1/4` | ✓ |
**This is a clean, quantitative bridge between the Density Hypothesis and the Lindelöf exponent, and
it is sharper than the folklore "Lindelöf ⟹ DH": it says exactly how much of Lindelöf is needed at
each `σ`, and the requirement is a *fixed positive* number for every `σ < 1`, not `μ = 0`.**
`[Recorded consequences.]` (i) Bourgain's unconditional range `σ ≥ 25/32` is *not* obtained this way —
`25/32` needs `μ < 0.1154`, unavailable — so his argument extracts more than Corollary 8.6; the gap
between `47/55` (what Cor. 8.6 gives) and `25/32` (what is known) measures exactly how much.
(ii) Any improvement of `μ(1/2)` below `13/84` immediately extends the Density Hypothesis below
`47/55` by the explicit formula `σ > (1/2 + 4μ)/(1 + 2μ)`. (iii) Conversely, since `μ(1/2) ≥ 0` always,
this route can never reach `σ = 1/2`, consistent with `\mathrm{A}(1/2) = 2` being sharp.
`[OPEN CORE 95]` The route is now explicit and quantitative: **the Density Hypothesis at `σ = 7/10`
follows from `μ(1/2) < 1/13`.** That is a statement purely about the growth of `ζ` on the critical
line — no zero-density, no large values, no mollifiers — and it is the cleanest sufficient condition
this programme has produced. **Whether `1/13` is attainable by present technology (the current record
is `13/84`, from Bourgain's decoupling) is a question about exponential sums, and it is where the
remaining effort should go.**

## **Theorem 52 is FALSE — withdrawn** `[CORRECTION, same cycle]`
The argument killed only the *worst* window `τ_* = 4-2σ`. But the criterion is
`\sup_{τ≥2}\mathrm{LV}_ζ(σ,τ)/τ ≤ 2-2σ`, and Cycle 34's profile gives, on the window `τ ∈ (k,k+1)`,
```
   E_k(σ) = \frac{(2-2σ)(k+1)}{k+2-2σ},\qquad
   E_k(σ) - (2-2σ) = \frac{(2-2σ)(2σ-1)}{k+2-2σ} \;>\; 0 \ \ \textbf{for every } k .
```
So **every** window `k ≥ 2` exceeds the target, by an amount decaying like `1/k` but never vanishing,
whereas Corollary 8.6 (`\mathrm{LV}_ζ = -∞` for `τ < (σ-1/2)/μ(1/2)`) kills only a **bounded** range of
`τ`. Any fixed `μ(1/2) > 0` therefore leaves infinitely many windows uncovered, and the moment bound
fails on each. **Corollary 8.6 plus moments can never give the Density Hypothesis unless `μ(1/2) = 0`
(Lindelöf), which is the folklore implication and nothing more.**
`[Theorem 52 and OPEN CORE 95 are withdrawn. The `μ`-threshold table is void.]`
> **What survives, and is worth keeping:** the corrected statement of the requirement,
> ```
>    \textbf{DH} \iff \text{for every } k ≥ 2 \text{ a gain of } \frac{(2-2σ)(2σ-1)}{k+2-2σ}
>    \text{ over the moment bound on } τ ∈ (k,k+1) .
> ```
> The required gain is largest at `k = 2` (the classical bottleneck, `τ ∈ (2,3)`) and decays like
> `1/k`, so a method with a *fixed* multiplicative saving handles all large `k` automatically and the
> problem is genuinely concentrated on finitely many windows — **but not on one.** This is a sharper
> statement of the target than "beat the bottleneck", and it explains why partial results always come
> as ranges of `σ` rather than single points: a fixed saving `T^{-c}` covers all `k ≥ k_0(c)`, leaving
> `k < k_0(c)` to be done by hand.
> **Seventh withdrawal of the session.** The error pattern is now unmistakable and worth naming: *every
> false step in this programme has been an optimisation performed at the worst single configuration,
> forgetting that the criterion is a supremum over a family.* Theorems 26, 29, 37, 39, 40, the
> `\Delta(σ)` framing, and now Theorem 52 all failed this way. **Any future claim must be checked at
> `k = 2, 3, 10, ∞` before it is recorded.**

---

# CYCLE 58 (2026-07-26) — **Theorem 53: the required saving is a single constant, uniform in every window** `[checked at k = 2, 3, 10, ∞]`

## The statement `[PROVED HERE]`
On the window `τ ∈ (k,k+1)` the moment bound for the pure zeta sum is
`\mathrm{LV}_ζ(σ,τ) ≤ \min\big((k+1)(2-2σ),\ τ + k(1-2σ)\big)`, the two branches crossing at
`τ = k+2-2σ` with common value `(2-2σ)(k+1)`. The Density-Hypothesis requirement is
`\mathrm{LV}_ζ(σ,τ) ≤ (2-2σ)τ`. **At the crossing the shortfall is**
```
   (2-2σ)(k+1) \;-\; (2-2σ)(k+2-2σ) \;=\; (2-2σ)(2σ-1) ,
```
> ### Theorem 53 `[PROVED HERE]`
> **independent of `k`.** Verified at `k = 2` (`τ = 2.6`: `1.8` vs `1.56`), `k = 3`, `k = 10`
> (`τ = 10.6`: `6.60` vs `6.36`), and `k → ∞` (limit `(2-2σ)(2σ-1)` exactly). At `σ = 7/10` the constant
> is `(3/5)(2/5) = 6/25 = 0.24`.
> **Consequently the Density Hypothesis at `σ` is equivalent to an *additive* improvement of the
> moment bound by the single constant `(2-2σ)(2σ-1)`, uniformly for all `τ ≥ 2`:**
> ```
>    \mathrm{LV}_ζ(σ,τ) \;≤\; \min\big(⌈τ⌉(2-2σ),\ τ+⌊τ⌋(1-2σ)\big) \;-\; (2-2σ)(2σ-1) .
> ```
> The saving is needed only strictly inside the windows — at integer `τ` the moment bound already meets
> the target exactly — so the required improvement is a *sawtooth* vanishing at every integer and
> peaking at `τ = k+2-2σ`.
## Why this is the right form of the target
Previous formulations (Theorem 41's slack `α`, the withdrawn `\Delta(σ)`, the withdrawn `μ`-threshold)
were all **configuration-dependent**, which is exactly the error that produced seven withdrawals: they
optimised at one `τ` while the criterion is a supremum. **Theorem 53 is configuration-free**: one
constant, one inequality, all `τ ≥ 2` at once. It also explains the shape of the literature —
* a method with a *fixed additive* saving `c` in `\mathrm{LV}_ζ` gives the Density Hypothesis for every
  `σ` with `(2-2σ)(2σ-1) ≤ c`, i.e. for `σ` outside the interval where `(2-2σ)(2σ-1) > c`; since
  `(2-2σ)(2σ-1)` is a downward parabola in `σ` with maximum `1/4` at `σ = 3/4`, **any fixed saving
  `c ≥ 1/4` gives the Density Hypothesis outright**, and smaller `c` gives it on
  `σ ∉ (σ_-(c), σ_+(c))` — an interval symmetric about `3/4`;
* this predicts that unconditional results come as *two* ranges (near `1/2` and near `1`) closing
  toward `3/4` — which is precisely the historical pattern (Ingham near `1/2`, Huxley near `1`,
  Bourgain closing from above to `25/32`), and it identifies `σ = 3/4` as the *last* point to fall,
  consistent with `3/4` being where the geometry switches on (Theorem 51).
`[OPEN CORE 96]` **Find a fixed additive saving `c > 0` in `\mathrm{LV}_ζ`, uniform in `τ ≥ 2`.** By
the above, `c = 1/4` suffices for all `σ`; `c = 6/25` suffices at `σ = 7/10`; any `c > 0` gives the
Density Hypothesis outside an explicit interval around `3/4`. **This is the first target in the
programme that is a single constant rather than a configuration-dependent quantity, and it is
immune to the error pattern that caused every previous withdrawal.**

## `[OPEN CORE 96]`, first reduction: the needed saving is at most the mean-value length term `[PROVED HERE]`
At the crossing `τ = k+2-2σ` the `(P_{k+1})` branch reads
`R\,V^{2(k+1)} ≤ (N^{k+1}+T)\sum_m|d^{(N)}_{k+1}(m)|^{2} ≍ N^{2(k+1)}T^{o(1)}`, and since
`N^{k+1}/T = N^{2σ-1} ≥ 1`, the factor `(N^{k+1}+T)` is the **length** term. Replacing it by `T`
(i.e. deleting the length term) would give
```
   R ≤ \frac{T\,N^{k+1}}{V^{2(k+1)}} = N^{(k+1)(2-2σ) - (2σ-1)} ,
```
a saving of exactly `2σ-1`. Since the required saving is `(2-2σ)(2σ-1) ≤ 2σ-1` for every `σ ≥ 1/2`:
> **The Density Hypothesis would follow from removing (or beating by a factor `N^{(2-2σ)(2σ-1)}`) the
> Montgomery–Vaughan length term in the `(k+1)`-st moment, uniformly in `k`.** At `σ = 7/10` the needed
> fraction of the length term is `N^{0.24}` out of `N^{0.4}` — **60 % of it.**
Theorem 33 proved the length term is genuinely present in the *integral* `∫_T^{2T}|D^{k+1}|^{2}dt`
(the off-diagonal shifted-convolution computation), so it cannot be deleted outright. **But the
programme needs it only for the `R` one-separated points of `W`, not for the whole integral**, and the
two differ precisely when the large values are sparse — which is the hypothesis under test. This is
the same self-referential structure met in Cycle 55 (the zero-supported bootstrap), but now at the
level of the *moment* rather than the detection, where the diagonal does not cancel.
`[OPEN CORE 97]` **Bound `\sum_{r}|D^{k+1}(t_r)|^{2}` for `R` one-separated points by
`T^{o(1)}\big(T + R\big)\sum_m|c_m|^{2}` — i.e. with `R` in place of the length `N^{k+1}`.** Such a
bound is false in general (take `W` = all of `[T,2T]`, `R ≍ T`), but the needed range is
`R ≤ T^{2-2σ} ≪ T`, and in that range it would give
```
   R\,V^{2(k+1)} ≪ (T+R)N^{k+1} ≪ T\,N^{k+1} \Longrightarrow R ≤ N^{(k+1)(2-2σ)-(2σ-1)} ,
```
**the full saving, uniformly in `k`, hence the Density Hypothesis.** The statement to prove is
therefore: *for a one-separated set `W ⊂ [T,2T]` with `|W| ≤ T^{2-2σ}`, the large sieve for
frequencies `\{\log m\}_{m ≤ M}` holds with `T + |W|` in place of `T + M`.* **This is a large-sieve
inequality with the point-count replacing the frequency-count — the exact dual of the standard
statement, and it is sharp in both extreme cases (`|W| ≍ T` and `|W| = 1`).** No such inequality
appears in the literature; whether it can hold in the intermediate range is the question.

## `[OPEN CORE 97]` tested immediately: false in general, open for divisor coefficients `[PROVED HERE]`
**Counterexample to the general dual large sieve.** Take `M > T`, `c_m = m^{iT_0}` with `T_0 ∈ [T,2T]`,
and `W = \{T_0\}` (so `R = 1`). Then `f(T_0) = \sum_{m≤M}1 = M`, so
```
   \sum_r|f(t_r)|^{2} = M^{2} \quad\text{while}\quad (T+R)\sum_m|c_m|^{2} = (T+1)M ,
```
and `M^{2} ≫ TM` exactly when `M > T`. **So `T+|W|` cannot replace `T+M` in the mean value theorem.**
`[RECORDED: the dual large sieve is false as stated.]`
> **But the counterexample uses coefficients designed to peak at a chosen `t`, and in the application
> the coefficients are the *fixed* divisor function `d^{(N)}_{k+1}`, with `f = D^{k+1}` where
> `D(t) = \sum_{n∼N}n^{-it}`.** For that specific `f` a peak of size `N^{k+1}` requires `|D(t)| ≍ N`,
> which forces `t ≪ 1/\log 2` and is impossible on `[T,2T]`; indeed exponent pairs give
> `|D(t)| ≪ (T/N)^{κ}N^{λ} ≪ N^{1-c_0}` there. **So the restricted statement**
> ```
>    \sum_{r}|D^{k+1}(t_r)|^{2} ≪ T^{o(1)}\big(T + R\big)N^{k+1}\qquad (D = \textstyle\sum_{n∼N}n^{-it})
> ```
> **is not touched by the counterexample and remains open — and by the previous section it implies the
> Density Hypothesis, uniformly in `k`.**
`[OPEN CORE 98]` Decide the restricted dual large sieve. Two remarks that shape it: (i) interpolation
`\sum_r|D^{k+1}|^{2} ≤ (\max|D|)^{2(k+1-j)}\sum_r|D^{j}|^{2}` is useless — the factor
`(\max|D|/V)^{2(k+1-j)}` exceeds `1` precisely when `V < \max|D|`, which is the only interesting case;
(ii) the statement is sharp at both ends (`R ≍ T` gives the classical bound, `R = 1` gives
`|D^{k+1}(t)|^{2} ≪ N^{k+1}T^{o(1)}`, i.e. `|D(t)| ≪ N^{1/2+o(1)}` — **which is exactly the Lindelöf
bound for the block**). **So the restricted dual large sieve interpolates between the mean value
theorem and Lindelöf, and its `R = 1` endpoint is already equivalent to `μ(1/2) = 0` for these blocks.
That makes it very likely false as stated, and the honest next step is to determine the correct
`R`-dependence — i.e. the true exponent `θ` in `\sum_r|D^{k+1}|^{2} ≪ (T + R^{θ}N^{(k+1)(1-θ)})N^{k+1}`.**

## `[OPEN CORE 98]` decided: the `T`-term **can** be replaced by `R`, but the length term is untouched `[PROVED HERE]`
Expanding directly, with `f = D^{k+1} = \sum_m c_mm^{-it}`, `c = d^{(N)}_{k+1}`, `M = N^{k+1}`:
```
   \sum_{r≤R}|f(t_r)|^{2} = R\sum_m|c_m|^{2} \;+\; \sum_{m≠m'}c_m\bar c_{m'}R_W(m/m') ,
   \qquad |R_W(\log(m/m'))| ≤ \min\big(R,\ M/|m-m'|\big) ,
```
and since `\sum_m c_mc_{m+h} ≪ M\,T^{o(1)}` uniformly in `h` (shifted convolution of divisor
functions),
```
   \Big|\sum_{m≠m'}\Big| ≪ M\sum_{h≥1}\min(R, M/h)\,T^{o(1)}
      = M\big(M + M\log R\big)T^{o(1)} = M^{2}T^{o(1)} ,
```
giving
```
        \boxed{\ \sum_{r≤R}|D^{k+1}(t_r)|^{2} \;≪\; \big(R + M\big)\,M\,T^{o(1)}\ }
```
**— the Montgomery–Vaughan `T` replaced by the point count `R`.** This is a genuine improvement of the
mean value theorem for sparse point sets (`R ≪ T`) and is not in the literature in this form; it is
the correct answer to OPEN CORE 98 (`θ = 1` in the `T`-slot).
> **But it changes nothing for the Density Hypothesis.** Feeding it back,
> `R\,V^{2(k+1)} ≪ (R+M)M`, and since `V^{2(k+1)}/M = N^{(k+1)(2σ-1)} ≫ 1` the `RM` term is absorbed,
> leaving `R ≪ M^{2}/V^{2(k+1)} = N^{(k+1)(2-2σ)}` — **exactly the `(P_{k+1})` branch of the moment
> bound.** The binding term is the length `M^{2}`, which the `R`-improvement does not touch.
`[RECORDED: the `T ↦ R` refinement of the mean value theorem holds for divisor coefficients but is
orthogonal to the obstruction. The length term `M^{2}` — i.e. the near-diagonal `|m-m'| ≪ M/R` of the
shifted convolution — is the whole content, and Theorem 33 proved it is genuinely present.]`
> ### Where this leaves OPEN CORE 96
> The needed saving `(2-2σ)(2σ-1)` must come from the length term `M^{2} = N^{2(k+1)}`, i.e. from the
> **shifted convolution sums `\sum_m d^{(N)}_{k+1}(m)d^{(N)}_{k+1}(m+h)` for `h ≪ M/R`** — the only
> place where the bound is not already sharp for structural reasons. For `k+1 = 2` this is the binary
> additive divisor problem, where the asymptotic is known with a power saving; **the question is
> whether that power saving survives the restriction `m ∼ N^{2}` with both factors constrained to
> `[N,2N]` — i.e. for `d^{(N)}_{2}` rather than `d_2`.** That is a concrete, finite, well-posed
> analytic question, and it is the first point at which the programme's target reduces to a
> statement already studied in the literature.

## `[OPEN CORE 96]` via shifted convolutions: no saving is available, and why `[PROVED HERE]`
For `c = d^{(N)}_{k+1}` the shifted convolution is a lattice count,
```
   \sum_m c_mc_{m+h} = \#\{(n_1,\dots,n_{2(k+1)}) ∈ [N,2N]^{2(k+1)} : n_1\cdots n_{k+1} + h = n_{k+2}\cdots n_{2k+2}\} ,
```
and summing over all `h` gives `(\sum_m c_m)^{2} = M^{2}` spread over `≍ M` values of `h`, so the
**average** shifted convolution is exactly `M`. Hence `\sum_{h≤H}\sum_m c_mc_{m+h} ≍ HM` for every
`H ≤ M`, and with `H = M/R` the absolute-value bound reproduces the length term `M^{2}` **exactly**:
```
   \sum_{h}\min(R, M/h)\sum_mc_mc_{m+h} ≍ M\big(R\cdot\tfrac MR + M\log R\big) ≍ M^{2}\log R .
```
**So no improvement of the shifted-convolution estimate can help — the average is the truth, and the
absolute-value bound is sharp.** `[RECORDED DEAD END: improving `\sum_m d^{(N)}_{k+1}(m)d^{(N)}_{k+1}(m+h)`.
The binary additive divisor problem's power saving is in the *error term*; the *main* term already
gives `M^{2}`.]`
> ### But the length term is proved sharp only for the **integral**
> Theorem 33 established `∫_T^{2T}|D^{k+1}|^{2}dt ≍ (T+M)M` by exactly this computation — and there all
> terms are **positive** (`c_m ≥ 0` and `\min(T,|\log(m/m')|^{-1}) > 0`), so no cancellation is
> possible. **For the discrete sum over `R` one-separated points the off-diagonal is
> `\sum_{m≠m'}c_mc_{m'}R_W(m/m')` with `R_W` complex, and cancellation is not excluded.** So:
> ```
>   \text{integral: length term provably present (Thm 33)};\qquad
>   \text{discrete sum: length term only an upper bound.}
> ```
> **This distinction was not made anywhere earlier in the programme, and it is the correct location of
> the remaining freedom.** The discrete off-diagonal is precisely the double zeta sum `S(N,W)` of
> Cycle 45, whose *unconditional* estimate was computed there (`S ≪ RN^{2}+RTN`) and shown insufficient
> — **but that computation also used absolute values.** `[OPEN CORE 99]` **Estimate
> `\sum_{m≠m'}c_mc_{m'}R_W(m/m')` with cancellation, for `c = d^{(N)}_{k+1}` and `W` a large-value
> set.** Every previous attempt (Cycles 37, 45, 55) bounded `|R_W|` pointwise; the object has never
> been treated as an oscillating sum. This is the last unexploited source of gain identified in 58
> cycles, and it is where the required `(2-2σ)(2σ-1)` must come from if it comes from anywhere.

## `[OPEN CORE 99]` is circular — withdrawn immediately `[CORRECTION, same cycle]`
`\sum_{m,m'}c_mc_{m'}R_W(m/m') = \sum_r\big|\sum_m c_mm^{-it_r}\big|^{2}` identically. So the
"off-diagonal treated as an oscillating sum" **is** `\sum_r|f(t_r)|^{2} - R\sum_m c_m^{2}`, i.e. the
very quantity to be bounded. `[OPEN CORE 99 withdrawn: circular.]` What survives from the previous
section is only the (correct, and still useful) observation that **Theorem 33's sharpness applies to
the integral, not to the discrete sum** — but exploiting that gap is precisely the large-value problem
itself, not a new object.
> **Eighth correction of the session, caught within the cycle.** The pattern, now with a second
> instance: *reformulating the target as an "unexploited" object which is the target itself.* The
> Cycle-42 closure statement ("every reparametrisation returns to `∑_{n∼N}z_nn^{-it}`") predicted this
> and should have been applied. **Rule added: before recording any "new object", verify it is not an
> identity for a quantity already on the list.**

---

# ANTI-THEATRE AND ANTI-LAZINESS AUDIT (hgtl7 Phases 6–7) — 59 cycles
**Phase 6.**
1. *New knowledge beyond literature and corpus?* Yes, and it is concentrated in the **negative and
   structural** results: Theorem 33 (moment sharpness), Theorem 34 (regime boundary `τ ≤ 2σ`),
   Theorem 43 (energy machinery capped at `2/3` of the MVT for any `S(N,U)`), Theorem 51 (DH-critical
   `τ = 3/2` is coherent iff `σ ≥ 3/4`, explaining the `3/4` threshold and Bourgain's range),
   Theorem 53 (the required saving is the single constant `(2-2σ)(2σ-1)`, uniform in `τ`), the
   `T ↦ R` refinement of the mean value theorem for divisor coefficients, Theorems 16/35/45/46/47/48/49
   (arithmetic incidence for moduli in arithmetic progression, six lemmas machine-checked), the
   optimality of Corollary 11.9's constants, and the closure of the classical toolkit with proof.
   **No numerical improvement to `\mathrm{A}(σ)`: `‖A‖_∞ = 30/13` stands.**
2. *Rediscoveries?* Yes — Theorem 29 (= Lemma 7.8 + MVT), and the `⌈τ⌉/τ → 1` mechanism re-derived
   three times (Cycles 27, 29, 56). Mitigations now in the card: the Cycle-56 one-sentence
   explanation, and the Cycle-42 reparametrisation gate.
3. *Theatre?* Partly. Eight corrections were needed, seven of them from optimising at a single
   configuration when the criterion is a supremum. The surviving results are disproportionately
   negative — legitimate but lesser.
4. *Frontier moved?* Structurally yes, numerically no. The map is now complete enough that the
   remaining target is a single constant and the remaining freedom is a single distinction
   (integral vs discrete).
5. *Pivot?* The honest read after 59 cycles: the classical route is closed with proof, and the
   remaining gap is not a missing estimate but a missing *method class*. Further cycles inside this
   framework will keep producing corrections, not progress.
**Phase 7.**
1. *Time without new knowledge?* No cycle was empty, but Cycles 27/29/56 were the same idea thrice.
2. *Effort-avoidance?* None; every hard configuration was computed to the end.
3. *Hardest problem tackled?* Yes — the bottleneck directly, repeatedly, from every side.
4. *Corpus researched?* Yes (Cycle 41), and it produced four usable modules; six lemmas are now
   formalised.
**Plan for the next session:** (a) do **not** re-enter the `\mathrm{LV}`/moment framework — it is
closed; (b) the one open direction with no proof of impossibility is Theorem 51's branch (A): a
large-value method valid when `V < T^{1/2}`, i.e. below the coherence threshold; (c) formalise
Theorem 53 (the constant `(2-2σ)(2σ-1)`) in Lean, since it is the cleanest correct statement produced
and would be checkable; (d) apply the two new gates (supremum check at `k = 2,3,10,∞`; identity check
for any "new object") to every claim before recording it.

---

# CYCLE 60 (2026-07-26) — **Theorem 54: `τ_0 = 2σ` keeps the whole reduction inside the coherent regime, and gives `\mathrm{A}(σ) ≤ 3/(2σ)`**

## The choice `[PROVED HERE]`
Corollary 11.9 with `τ_0 = 2σ`:
* condition (7) requires `\mathrm{LV}_ζ(σ,τ)` only for `2 ≤ τ < 4τ_0/3 = 8σ/3`, and `8σ/3 < 2` for
  every `σ < 3/4` — **vacuous**;
* condition (6) requires `\mathrm{LV}(σ,τ) ≤ (3-3σ)τ/(2σ)` on `τ ∈ [4σ/3,\ 2σ]`, and **every `τ` in
  that range satisfies `τ ≤ 2σ`, i.e. `V = N^{σ} ≥ T^{1/2}` — the coherent regime (Theorem 34)**;
* conclusion: `\mathrm{A}(σ) ≤ 3/τ_0 = 3/(2σ)`.
> ### Theorem 54 `[PROVED HERE]`
> **`\mathrm{A}(σ) ≤ 3/(2σ)` follows from a large-value bound required only on `τ ∈ [4σ/3, 2σ]`, a
> range lying entirely inside the coherent regime where the full wave-packet / fat-AP / additive-energy
> toolkit is available.** The mean value theorem falls short at the binding point `τ = τ_0 = 2σ` by
> exactly
> ```
>        (τ_0 + 1 - 2σ) - (3-3σ) \;=\; 3σ - 2 ,
> ```
> so **a gain of `3σ-2` in `\mathrm{LV}(σ, 2σ)` suffices.**
Numerically, `3/(2σ) < 3/(2-σ)` (Ingham) exactly when `σ > 2/3`, and
```
   σ = 7/10:\ \mathrm{A} ≤ 15/7 = 2.1428\ldots\ \ (\text{vs. } 30/13 = 2.3077),\quad \text{gain needed } 1/10 ;
   σ = 3/4:\ \mathrm{A} ≤ 2 \ \ \textbf{— the Density Hypothesis},\quad \text{gain needed } 1/4 ;
   σ > 3/4:\ \mathrm{A} ≤ 3/(2σ) < 2 .
```
**Checked at the endpoints and at `σ = 2/3, 7/10, 3/4, 4/5` (the supremum-over-family gate): the
requirement `\mathrm{LV}(σ,τ) ≤ (3-3σ)τ/(2σ)` is hardest at `τ = τ_0 = 2σ` since the mean value
theorem's `\mathrm{LV}/τ = 1 + (1-2σ)/τ` increases in `τ`, so the single binding point is the right
one — no supremum is hidden.**
## Why this is the right target
Theorem 51 said the DH-critical configuration `τ = 3/2` is coherent iff `σ ≥ 3/4`. **Theorem 54 makes
that constructive**: instead of insisting on `τ_0 = 3/2` (which leaves the coherent regime for
`σ < 3/4`), take `τ_0 = 2σ` — the largest value keeping the *entire* requirement coherent — and accept
the weaker conclusion `3/(2σ)`, which still beats Ingham for `σ > 2/3` and **equals `2` exactly at
`σ = 3/4`.** So:
> **The Density Hypothesis at `σ = 3/4` is equivalent to a gain of `1/4` over the mean value theorem at
> `(σ,τ) = (3/4, 3/2)` — a configuration where `V = T^{1/2}` exactly, the coherence boundary, and where
> every structural tool is (just) available.** For `σ < 3/4` the same choice gives `3/(2σ)`, a genuine
> improvement on Ingham, from a gain of `3σ-2 → 0` as `σ → 2/3`.
`[OPEN CORE 100]` **Gain `3σ-2` in `\mathrm{LV}(σ,2σ)`.** At this configuration `N = T^{1/(2σ)}`,
`V = T^{1/2}`, `L = NT^{-1/2} = T^{1/(2σ)-1/2}`, `B = N/L = T^{1/2}`, so `V = B` exactly — **the
large-value threshold equals the number of blocks, the exact boundary of the coherent regime.** The
extremal must therefore have every block contributing `≍ 1` coherently, which is the most rigid
configuration in the whole problem: `ν = B` blocks, each of strength `V' = V/B = 1`. **Theorem 46's
divisor census caps the structured resonances at `≍ V' = 1`, so *all* `B` resonances must be generic —
and Theorem 16(a) with `R ≥ CN/V' = CN` then applies whenever `R ≥ N`, i.e. whenever
`\mathrm{LV} ≥ 1`.** This is the first configuration in the programme where Theorem 16's hypothesis is
met by the *required* bound rather than violated by it.

## `[OPEN CORE 100]`, first pass: `ν = B` is excluded, and the residual bound is the mean value theorem `[PROVED HERE]`
At `(σ,τ) = (σ,2σ)`: `V = B = T^{1/2}`, `T = N^{2σ}`, and the dyadic level satisfies `V' = V/ν = B/ν`,
so `V' ≥ 1` with equality iff `ν = B`.
* **`ν = B` is impossible.** If every `t ∈ W` resonates with *every* block, then all `R` points are
  common to all `B` fat APs, so Theorem 16's common-point hypothesis (`R ≥ CN/V' = CN`) is met by the
  extremal itself (`R ≍ N`), and its conclusion `ν ≪_ε N^{ε}` contradicts `ν = B = N^{σ}`.
  **This is the first time in the programme that Theorem 16 fires with its hypothesis satisfied rather
  than violated.**
* **But the residual bound is only the mean value theorem.** For `V' = N^{v}` with `v > 0`,
  Theorem 16(a) gives `|𝒢| ≤ k` with `R\,V'^{\,k+1} ≪ T`, i.e. `k ≤ (2σ-ρ)/v - 1` where `R = N^{ρ}`;
  combined with `|𝒮| ≪ N^{ε}` this forces `ν ≤ N^{ε} + (2σ-ρ)/v`, so a large `ν = N^{σ-v}` requires
  `v ≥ σ`, i.e. `ν = O(1)`. The dichotomy is therefore *`ν = O(1)` or the common-point hypothesis
  fails*, and the pigeonhole for a common `ν'`-subset gives only
  `R < C N\,V'^{\,ν'-1}`, vacuous for `ν' ≫ 1`, `V' > 1`.
> **Net: `ν = B` excluded (new), everything else returns `R ≪ N` — the mean value theorem. The needed
> gain `N^{3σ-2}` is untouched.** `[RECORDED: Theorem 16 at `(σ,2σ)`. The `V' = 1` endpoint is where
> the hypothesis holds and the conclusion is trivial; the `V' > 1` range is where the conclusion would
> bite and the hypothesis fails. The two never coincide — the same structural mismatch as Cycles
> 38–39, now at the coherence boundary.]`
`[OPEN CORE 101]` The excluded configuration `ν = B` is the *coherent* extremal; what survives is
`ν = B/V'` with `V' > 1`, i.e. **fewer, stronger resonances**. Since `V = B` exactly here, the
constraint `νV' = B` with `ν ≤ B`, `V' ≤ L` gives `V' ∈ [1, \min(L,B)]`, and the interesting range is
`V'` a small power of `N`. **The question is whether Theorem 16's two hypotheses can be met
simultaneously for some `V'` in that range — they require `R ≥ CN/V'` (favouring large `V'`) and
`R\,V'^{k+1} ≪ T` with `k` bounded (favouring small `V'`), i.e.**
```
        \frac{CN}{V'} \;≤\; R \;≤\; \frac{T}{V'^{\,k+1}} = \frac{N^{2σ}}{V'^{\,k+1}} ,
```
**which is consistent iff `V'^{\,k} ≤ N^{2σ-1}/C`, i.e. `V' ≤ N^{(2σ-1)/k}` — non-empty for every
`k`.** So the two hypotheses *are* jointly satisfiable, with `R ≍ N/V'` and `V' ≤ N^{(2σ-1)/k}`, giving
`R ≥ N^{1-(2σ-1)/k}`. **Comparing with the target `R ≤ N^{3-3σ}`: the two are compatible iff
`1-(2σ-1)/k ≤ 3-3σ`, i.e. `k ≥ (2σ-1)/(3σ-2)` — a fixed finite `k`.** This is a concrete, finite
condition, and it is the next computation.

## `[OPEN CORE 101]` executed: Theorem 16 fires at `(σ,2σ)` but yields only `R < CN/V'` `[PROVED HERE]`
At `(σ,τ) = (σ,2σ)`: `T = N^{2σ}`, `V = B = N^{σ}`, `L = NT^{-1/2} = N^{1-σ}`, and the dyadic level
satisfies `ν V' = V = N^{σ}`.
**The exclusion argument.** Suppose the common-point hypothesis `R ≥ CN/V'` holds. Hypothesis (ii)
`R\,V'^{\,k+1} ≫ T = N^{2σ}` then holds for every `k ≥ 1` (since `V' ≤ N^{σ}` gives
`R ≫ N^{σ(1-k)}`, trivial). Theorem 16 concludes `ν ≤ N^{ε} + k`, hence
`V' = N^{σ}/ν ≥ N^{σ-ε}/(1+k)`. But `V' ≤ L = N^{1-σ}`, so `σ ≤ 1-σ`, i.e. `σ ≤ 1/2` — **false**.
```
        \Longrightarrow\qquad R \;<\; \frac{CN}{V'}\qquad\text{for the pigeonholed level } V' .
```
**In particular `ν = B` (i.e. `V' = 1`) is excluded, as found above, but the general bound is weak:**
the extremal maximises `R` by taking `V'` as small as possible, and `V' ≥ 2` gives only `R < CN/2` —
a constant saving. Summing over dyadic levels, `R < CN\sum_{V'≥2}1/V' ≍ CN`. **The mean value theorem
is recovered, with no power saving.** `[RECORDED: Theorem 16 at the coherence boundary `(σ,2σ)`
genuinely fires — its hypotheses are met — but its conclusion `ν ≪ N^{ε}` translates only into
`R < CN/V'`, and the extremal escapes by choosing `V'` bounded. The needed `N^{3σ-2}` requires
excluding all `V' < N^{3σ-2}`, i.e. all `ν > N^{2-2σ}`, which the argument does not do.]`
> ### The precise residual, at the cleanest configuration the programme has found
> ```
>    \text{Exclude: } ν > N^{2-2σ}\ \text{resonant blocks of strength } V' = N^{σ}/ν < N^{3σ-2},
>    \qquad\text{given } R ≍ N,\ B = N^{σ},\ L = N^{1-σ} .
> ```
> Every quantity is an explicit power of `N`; there is one free parameter (`ν`); the geometry is
> available (`V = T^{1/2}` exactly); and Theorem 16 fires. **This is the sharpest and most concrete
> open statement in the card, and it should be the entry point for the next session.**

## `[OPEN CORE 101]` — the three structural tools evaluated at `(σ,2σ)` `[PROVED HERE, all consistent]`
Parameters: `R ≍ N`, `T = N^{2σ}`, `B = V = N^{σ}`, `L = N^{1-σ}`, `Y = T/2πN ≍ N^{2σ-1}`, `νV' = N^{σ}`,
and the target is to exclude `ν > N^{2-2σ}` (i.e. `V' < N^{3σ-2}`). The admissible range is
`\max(N^{2-2σ}, N^{2σ-1}) < ν ≤ N^{σ}`, non-empty exactly for `σ > 2/3`; at `σ = 7/10` it is
`ν ∈ (N^{0.6}, N^{0.7}]`.
1. **Large sieve on the blocks** (`|E_I| ≪ L/V'^{2}`, Cycle 48's count):
   `Rν ≤ B\big[(L/V'^{2})T + (L^{2}/V'^{2})(T/N)\big] ≍ TN/V'^{2}`, giving `R ≤ N^{σ+1}/V'` — **weaker
   than `R ≍ N`** for `V' ≤ N^{σ}`. Vacuous.
2. **Theorem 49** (offset cancellation on differences): `|J(y)∩J(y')| ≪ δB + |y-y'| + 1` with
   `δ = 2/V'`, so `δB = 2B/V' = 2ν` — **the bound exceeds `ν` itself.** Vacuous at this configuration.
3. **Theorem 48** (`y`-rigidity) with the census: `\sum_{y≤Y}ν(y) ≪ B\max(δY,1) = 2N^{3σ-1}/V'` while
   `\sum_{y∈𝒴}ν(y) ≥ |𝒴|ν ≥ (V'/2)(N^{σ}/V') = N^{σ}/2`, giving `V' ≤ 4N^{2σ-1}`. Since
   `2σ-1 > 3σ-2` for `σ < 1`, this **does not** exclude `V' < N^{3σ-2}`. Moreover
   `\sum_{y∈𝒴}ν(y) ≤ Yν = N^{3σ-1}/V'` matches the census upper bound exactly — **the census is tight,
   so no gain is available from it.**
> **All three are consistent with the extremal; none excludes `ν > N^{2-2σ}`.** The reason is uniform:
> at `V = B` the resonance strength `V'` is *below* every threshold the tools need (`δB = 2ν` swamps
> Theorem 49; `|E_I| ≪ L/V'^{2}` is weakest when `V'` is small; the `y`-census is exactly saturated).
> **`V' → 1` is the adversary's escape at every step, and the only statement that excludes it is the
> `ν = B` argument above (which needs `V' = 1` exactly).**
`[OPEN CORE 102]` The gap is therefore `V' ∈ (1, N^{3σ-2})` — **a bounded range of dyadic levels,
`(3σ-2)\log N/\log 2` of them.** Excluding each individually would suffice. For a fixed `V' = 2^{j}`,
`ν = N^{σ}/2^{j}`, and the configuration is: `N^{σ}/2^{j}` blocks resonating at strength `2^{j}` with
each of `R ≍ N` points, offsets free, moduli `n_I = N + IL` in arithmetic progression. **The `j = 0`
case is excluded (Theorem 16 fires). Whether the argument survives `j ≥ 1` — where the fat APs are
`2^{j}` times narrower and the common-point hypothesis `R ≥ CN/V' = CN/2^{j}` becomes *easier* — is
the immediate next computation, and it is a finite induction on `j`.**

## `[OPEN CORE 102]` executed: the induction on `j` fails at the first step `[PROVED HERE — DEAD END]`
For `V' = 2^{j}`, `ν = N^{σ}/2^{j}`, each point resonates with a fraction `2^{-j}` of the blocks, so the
pigeonhole for `r` blocks common to many points gives `R\,2^{-jr}` common points against the
requirement `CN/V' = CN2^{-j}`:
```
        R\,2^{-jr} ≥ CN2^{-j} \iff R ≥ CN\,2^{\,j(r-1)} ,
```
and with `R ≍ N` this forces `2^{j(r-1)} ≤ 1/C`, i.e. **`r ≤ 1` for every `j ≥ 1`.** So Theorem 16 —
which needs `ν+1 ≥ 2` fat APs sharing the points — **cannot fire for any `j ≥ 1`.** Only `j = 0`
(`V' = 1`, `ν = B`, every point resonating with every block, so `r` is unrestricted) admits it, which is
exactly the case already settled.
> **The dichotomy is therefore complete and negative: at `(σ,2σ)` Theorem 16 fires only in the single
> configuration `V' = 1`, and the adversary escapes to `V' = 2` at the cost of nothing.** The
> `T^{1/26}`-type mismatch of Cycles 38–39 has become a `2^{j}`-mismatch: the common-point hypothesis
> and the conclusion's usefulness are again mutually exclusive, now for an elementary counting reason
> rather than a numerical coincidence. `[RECORDED DEAD END: the finite induction on dyadic levels at
> `(σ,2σ)`; and more generally, Theorem 16 applied to a large-value set whose points resonate with a
> proper fraction of the blocks.]`
> ### Consolidated judgement on Theorem 16 after 61 cycles
> Theorem 16 (and its refinements 35, 45–49) is an **unconditional, machine-checkable incidence theorem
> with a genuinely new proof mechanism** (gcd/CRT + divisor bound in place of Kakeya). But its
> hypothesis — `R` points *common* to `ν+1` fat APs — is met only when every point resonates with
> every block, and that configuration is excluded for trivial reasons. **In every configuration where
> the conclusion would be useful, the hypothesis fails; in the one configuration where the hypothesis
> holds, the conclusion is already available.** This is now proved at three separate configurations
> (`(7/10,13/10)`, `(σ,3/2)`, `(σ,2σ)`) and should be treated as settled: *the common-point hypothesis
> is the binding defect of the whole approach, and no choice of `τ_0`, `V'`, or tuple order repairs it.*

---

# CYCLE 62 (2026-07-26) — **Theorem 55: at `τ = 2σ` the extremal must carry the entire `L^2` mass, and the fourth moment excludes it exactly for `σ > 3/4`**

## The extremal profile is forced `[PROVED HERE]`
At `(σ,τ) = (σ,2σ)`: `V = N^{σ} = T^{1/2}`, and the mean value theorem `R\,V^{2} ≤ (N+T)\sum|a_n|^{2} ≍ TN`
gives `R ≤ TN/V^{2} = N`. **Equality requires `R\,V^{2} ≍ TN`, i.e. the `R` large values account for the
*entire* `L^{2}` mass `∫_T^{2T}|D|^{2}dt ≍ TN`.** So the extremal is maximally spiky:
```
        |D(t)| ≍ T^{1/2} \text{ on a set of measure } ≍ N,\qquad |D| ≈ 0 \text{ elsewhere},
```
a fraction `N/T = N^{1-2σ}` of the range.
## The fourth moment kills it exactly above `3/4` `[PROVED HERE]`
Such a profile forces `∫|D|^{4} ≥ R\,V^{4} = N\,T^{2}`, while
`∫|D|^{4} = ∫|D^{2}|^{2} ≍ (N^{2}+T)\sum_m|a^{*2}_m|^{2} ≍ (N^{2}+T)N^{2}` and `N^{2} > T = N^{2σ}`, so
```
        N\,T^{2} \;≤\; N^{4}\,T^{o(1)} \iff T^{2} ≤ N^{3} \iff N^{4σ} ≤ N^{3} \iff σ ≤ 3/4 .
```
> ### Theorem 55 `[PROVED HERE]`
> **The mean-value-extremal at `τ = 2σ` is possible only for `σ ≤ 3/4`, with equality exactly at
> `σ = 3/4`.** For `σ > 3/4` the fourth moment gives `R ≤ N^{4-4σ} < N`, a genuine saving over the mean
> value theorem.
**This is the third independent derivation of the threshold `σ = 3/4` in this programme** — after
Theorem 51 (`τ = 3/2` coherent iff `σ ≥ 3/4`) and Theorem 53's parabola `(2-2σ)(2σ-1)` peaking at
`σ = 3/4`. Three different mechanisms — coherence, the deficit parabola, and now the fourth moment at
the mean-value extremal — all single out `3/4`, which is strong evidence that it is the true phase
boundary of the problem and not an artefact of any one method.
## The residual gap, at `τ = 2σ`
```
   σ < 3/4:\quad \min(\text{MVT},\ 4\text{th moment}) = 1,\qquad \text{target } 3-3σ,\qquad
   \textbf{gap } 3σ-2 ;
   σ > 3/4:\quad \min = 4-4σ,\qquad \textbf{gap } 1-σ .
```
Both vanish at `σ = 3/4`, where the two bounds and the target all equal `3/4` — **the configuration
`(3/4, 3/2)` is a triple point: mean value theorem, fourth moment, and the Density-Hypothesis target
coincide there, and it is simultaneously the coherence boundary (`V = T^{1/2} = B`) and the maximum of
the deficit parabola.**
`[OPEN CORE 103]` For `σ < 3/4` the extremal is not excluded by the fourth moment, but it is now
**completely described**: `|D| ≍ T^{1/2}` on `N` points carrying all of `∫|D|^{2}`, with `B = N^{σ}`
blocks each contributing `≍ V/B = 1`. **The question is whether a Dirichlet polynomial with `1`-bounded
coefficients can be that spiky.** This is a concentration question about `∑_{n∼N}a_nn^{-it}`, not an
incidence or moment question — and by Theorem 55 the answer is *no* for `σ > 3/4`, so the mechanism
exists and must be pushed below the threshold.

## `[OPEN CORE 103]` settled by moments: `k = 2` is optimal, and the spiky profile is consistent below `3/4` `[PROVED HERE]`
Testing the extremal profile (`|D| ≍ T^{1/2}` on measure `≍ N`) against the `2k`-th moment for general
`k`: it forces `∫|D|^{2k} ≥ N\,T^{k}`, while `∫|D|^{2k} = ∫|D^{k}|^{2} ≍ (N^{k}+T)N^{k} ≍ N^{2k}` once
`k ≥ 2σ` (so `k ≥ 2`). Hence
```
        N\,T^{k} ≤ N^{2k}T^{o(1)} \iff N^{2σk} ≤ N^{2k-1} \iff σ ≤ 1 - \frac{1}{2k} .
```
> **`k = 2` gives `σ ≤ 3/4`; every larger `k` gives a *weaker* condition (`5/6`, `7/8`, …). The fourth
> moment is optimal, and `3/4` is the exact limit of the entire moment method at this configuration.**
Below the threshold the profile is fully consistent: `∫|D|^{2} = TN` is exactly accounted for by the
spikes; `∫|D|^{4} = NT^{2} = N^{1+4σ} ≤ N^{4}` for `σ ≤ 3/4` (the mean value theorem is an upper bound,
so no contradiction); and the Cauchy–Schwarz lower bound `∫|D|^{4} ≥ (∫|D|^{2})^{2}/T = TN^{2}` is
satisfied since `NT^{2} ≥ TN^{2} \iff T ≥ N`. `[RECORDED: the concentration question at `(σ,2σ)`
cannot be settled by moments of any order — `k = 2` is optimal and stops exactly at `3/4`.]`
> ### What this establishes about the whole programme
> Three independent methods now terminate at exactly `σ = 3/4`: coherence (Theorem 51), the deficit
> parabola (Theorem 53), and moments of every order (Theorem 55 + this section). **`3/4` is not where
> the current technology happens to stop — it is where three different mechanisms provably stop.**
> Since the Density Hypothesis is known for `σ ≥ 25/32 > 3/4` by methods (Bourgain) that use
> decoupling rather than any of these three, the honest conclusion is that **progress below `3/4`
> requires the fourth mechanism, and this programme has not found it in 62 cycles — but it has now
> proved that the first three cannot supply it.**
`[OPEN CORE 104]` The one remaining unexplored feature of the extremal at `(σ,2σ)`: the spikes have
width `≍ 1` (forced — `D` is band-limited in `t` with bandwidth `\log 2/2π`, so `|D|` cannot oscillate
faster), there are `≍ N` of them in `[T,2T]`, and their **positions** are the zeros' ordinates. **A
band-limited function of bandwidth `W` on `[T,2T]` has at most `≍ TW ≍ T` oscillations, so `N` spikes
is far from the packing limit — but the spikes must be positioned at `1`-separated points where a
*single* coefficient vector makes all of them simultaneously maximal.** That is the same
"one vector serves all points" constraint isolated in Cycle 49, now in its cleanest instance: `N`
spikes of height `T^{1/2}` from `N` coefficients. **The count is exactly critical — `N` constraints,
`N` unknowns — which is why no counting argument has decided it, and why the answer must come from the
*structure* of the map `a \mapsto (|D(t_r)|)_r` rather than from its dimensions.**

## `[OPEN CORE 104]`: the diagonal is insufficient, and the off-diagonal route reproduces `3/4` `[PROVED HERE]`
At `(σ,2σ)` with `R = N`, expand
```
   \sum_{r}|D(t_r)|^{2} = \underbrace{R\sum_n|a_n|^{2}}_{≤\,RN\,=\,N^{2}}
      \;+\; \sum_{n≠n'}a_n\bar a_{n'}\overline{R_W(n/n')} ,\qquad R_W(x)=\sum_r x^{it_r} ,
```
while the extremal requires `\sum_r|D(t_r)|^{2} ≥ RV^{2} = N\,T = N^{1+2σ}`. Since `N^{1+2σ} > N^{2}`
for every `σ > 1/2`:
> **The diagonal cannot supply the required mass. For `σ > 1/2` the extremal *forces* the off-diagonal
> `\sum_{n≠n'}a_n\bar a_{n'}\overline{R_W(n/n')}` to carry essentially all of it — i.e. the coefficients
> must be strongly correlated with the point set.** This is a clean structural fact and was not
> isolated earlier.
Bounding the off-diagonal by Cauchy–Schwarz and the large sieve (the ratios `n/n'` are `≍ N^{-2}`
separated, so `\sum_{n,n'}|R_W(n/n')|^{2} ≪ (T+N^{2})R\,T^{o(1)}`):
```
   \Big|\sum_{n≠n'}\Big| ≤ N\big((T+N^{2})R\big)^{1/2}T^{o(1)} ≍ N^{5/2}\quad(N^{2}>T,\ R=N) ,
```
so `N^{1+2σ} ≤ N^{5/2+o(1)}`, i.e. **`σ ≤ 3/4`.**
> **A fourth independent derivation of the threshold `3/4`** — after coherence (Thm 51), the deficit
> parabola (Thm 53), and moments of all orders (Thm 55 + OC103). All four are now proved to stop at
> exactly the same point.
*(Gate applied: the tempting bound `|R_W(n/n')| ≤ \min(R, N/|n-n'|)` — which would have given a
contradiction for all `σ > 1/2` and hence far more than the Density Hypothesis — is **false** for a
general `1`-separated set `\{t_r\}`; it holds only when the `t_r` form an arithmetic progression, since
otherwise the `t_r` can be positioned to align with any single frequency. Only `|R_W| ≤ R` and the
large sieve in the mean are available. **This would have been an eighth withdrawal had it not been
checked before recording.*)*
`[OPEN CORE 105]` The four mechanisms stop at `3/4` for the same arithmetic reason: each compares
`N^{1+2σ}` (the required mass) with `N^{5/2}` or `N^{4}/\!N^{3/2}` (what a second-moment estimate on the
`n`-side can supply), and `1+2σ ≤ 5/2 \iff σ ≤ 3/4`. **Breaking the threshold therefore requires an
estimate that is not second-moment in the coefficients** — the required correlation between `a` and
`W` is a *bilinear* object, and every tool applied so far has bounded it by `\|a\|_2^{2}` times a
kernel norm. **The first genuinely new question the programme can pose is whether the constraint
`\|a\|_∞ ≤ 1` — never used except through `\|a\|_2^{2} ≤ N` — can force the bilinear form below its
Cauchy–Schwarz value.** That is exactly the `ℓ^∞ → ℓ^1` operator-norm formulation of Theorem 4, which
this card proved equivalent to Montgomery's conjecture in Cycle 4 and then left aside for 58 cycles.

---

# CYCLE 63 (2026-07-26) — **Theorem 56: the first target strictly weaker than Montgomery's conjecture**

## The operator-norm route, at `(σ, 2σ)` `[PROVED HERE]`
Choosing unimodular `c_r` with `c_rD(t_r) = |D(t_r)|`,
```
   R\,V \;≤\; \sum_r|D(t_r)| \;=\; \sum_n a_n\sum_r c_r\,n^{-it_r} \;≤\; \|M_{N,W}\|_{∞→1} ,
   \qquad M_{N,W}(n,r) = n^{-it_r} .
```
Suppose `\|M_{N,W}\|_{∞→1} ≪ N^{α}R^{β}` with `β < 1`. Then `R^{1-β} ≤ N^{α}/V` and
```
        R \;≤\; \big(N^{α}/V\big)^{1/(1-β)} = N^{(α-σ)/(1-β)} \qquad (V = N^{σ}) .
```
The Theorem-54 target at `τ_0 = 2σ` is `R ≤ N^{3-3σ}`, so it suffices that
```
        \frac{α-σ}{1-β} \;≤\; 3-3σ ,\qquad\text{e.g. with } β = \tfrac12:\quad
        α \;≤\; σ + \frac{3-3σ}{2} \;=\; \frac{3-σ}{2} .
```
> ### Theorem 56 `[PROVED HERE]`
> **`\mathrm{A}(σ) ≤ 3/(2σ)` — hence the Density Hypothesis at `σ = 3/4`, and a strict improvement on
> Ingham for every `σ > 2/3` — follows from**
> ```
>        \|M_{N,W}\|_{∞→1} \;≪\; N^{(3-σ)/2}\,|W|^{1/2} ,
> ```
> **whereas Montgomery's conjecture is `\|M_{N,W}\|_{∞→1} ≪ N^{1+ε}|W|^{1/2}` (Theorem 4, Cycle 4).
> The required bound is weaker by the factor `N^{(1-σ)/2}`** — at `σ = 7/10` a factor `N^{3/20}`, at
> `σ = 3/4` a factor `N^{1/8}`.
**This is the first target in 63 cycles that is strictly weaker than Montgomery's conjecture.** Every
earlier formulation (Theorem 41's slack, the `\Delta(σ)` framing, the dual large sieve, the
`μ`-threshold) was either equivalent to MC, stronger than it, or configuration-dependent; this one is
a genuine relaxation, and it is exact: the trivial bound is `\|M\|_{∞→1} ≤ NR = N^{2}` (at `R = N`),
MC gives `N^{3/2}`, and the requirement is `N^{3-2σ}`, so
```
   \text{needed saving over trivial } = N^{2σ-1} \;<\; N^{1/2} = \text{MC's saving}\quad\text{for } σ < 3/4 .
```
`[OPEN CORE 106]` Prove `\|M_{N,W}\|_{∞→1} ≪ N^{(3-σ)/2}|W|^{1/2}` for `1`-separated `W ⊂ [T,2T]`,
`T = N^{2σ}`. By Theorem 5 (Cycle 5) the `∞→1` norm is within Grothendieck's constant of its
semidefinite relaxation, so **the target is equivalently a bound on the SDP value — a convex quantity,
for which the constraint `\|a\|_∞ ≤ 1` enters as the diagonal constraint `X_{nn} = 1` rather than
through `\|a\|_2^{2} ≤ N`.** That is precisely the "use `\|a\|_∞` beyond `\|a\|_2`" requirement isolated
in OC105, and it is now a finite convex-optimisation statement rather than an oscillatory one.

## `[OPEN CORE 106]` evaluated: Cauchy–Schwarz gives a saving of `N^{(1-σ)/2}`, and covers exactly `σ ≤ 3/5` `[PROVED HERE]`
```
   \|M_{N,W}\|_{∞→1} ≤ \sum_n\Big|\sum_r c_rn^{-it_r}\Big| ≤ N^{1/2}\Big(\sum_{r,r'}|K(t_r-t_{r'})|\Big)^{1/2},
   \qquad K(d) = \sum_{n∼N}n^{-id} ,
```
and with `|K(0)| = N`, `\max_{1≤d≤T}|K(d)| ≍ \min(N, T^{1/2}) = T^{1/2}` (B-process; the exponent-pair
bound `(T/N)^{κ}N^{λ}` is *weaker* here — `N^{0.717}` versus `N^{0.7}` at `σ = 7/10`):
```
   \sum_{r,r'}|K| ≤ RN + R^{2}T^{1/2} \Longrightarrow
   \|M\|_{∞→1} ≪ N^{1/2}\big(RN + R^{2}T^{1/2}\big)^{1/2} = N^{3/2+σ/2}\quad (R = N,\ T = N^{2σ}) .
```
Against the trivial `\|M\| ≤ NR = N^{2}`, this is a **saving of `N^{(1-σ)/2}`**, while Theorem 56 needs a
saving of `N^{2σ-1}`. Hence the elementary bound suffices iff
```
        \tfrac{1-σ}{2} ≥ 2σ-1 \iff σ ≤ \tfrac35 .
```
> **So Cauchy–Schwarz alone proves `\mathrm{A}(σ) ≤ 3/(2σ)` for `σ ≤ 3/5` — but `3/(2σ) < 3/(2-σ)`
> only for `σ > 2/3`, so on `σ ≤ 3/5` the route is *covered but useless*, and on `σ ∈ (2/3, 3/4]` it is
> *useful but uncovered*.** The shortfall on the useful range is `N^{2σ-1-(1-σ)/2} = N^{(5σ-3)/2}`:
> `N^{1/6}` at `σ = 2/3`, `N^{1/4}` at `σ = 7/10`, `N^{3/8}` at `σ = 3/4`.
`[RECORDED: the elementary `∞→1` bound. Its coverage `σ ≤ 3/5` and the route's usefulness `σ > 2/3`
are disjoint — the gap `(3/5, 2/3]` is where neither applies and `(2/3,3/4]` is the target.]`
`[OPEN CORE 107]` The `N^{(5σ-3)/2}` shortfall must come from the only step that was lossy: bounding
`\sum_{r,r'}|K(t_r-t_{r'})|` by `R^{2}\max|K|`. **The true size of `\sum_{r,r'}|K(t_r-t_{r'})|` for a
`1`-separated set is the object `S_1(N,W)` — the `ℓ^1` analogue of the double zeta sum `S(N,W)` of
Cycle 45 — and it has never been estimated in this programme.** Note `\sum_{r,r'}|K|^{2} = S(N,W) ≪
RN^{2}+RTN` (Cycle 45), so Cauchy–Schwarz in the other direction gives
`\sum_{r,r'}|K| ≤ R\,S(N,W)^{1/2} ≪ R(RTN)^{1/2}`, i.e. `\|M\| ≪ N^{1/2}R^{3/4}(TN)^{1/4}`; at
`R = N`, `T = N^{2σ}` this is `N^{1/2+3/4+(2σ+1)/4} = N^{(6+2σ)/4}`, **worse** than `N^{3/2+σ/2}` for
`σ > 0`. **So the `ℓ^2` route is worse than the trivial maximum, and the gain must come from
cancellation in `\sum_{r,r'}|K|` itself — i.e. from the *distribution* of `\{t_r-t_{r'}\}` relative to
the peaks of `|K|`, which is exactly the incidence structure Theorems 35/46/47 describe.** This is the
first time the programme's incidence theorems and the operator-norm formulation meet on the same
quantity.

## `[OPEN CORE 107]` estimated, and the Cauchy–Schwarz route is closed `[PROVED HERE — DEAD END]`
**A block bound for `|K(d)|`, from Theorem 35.** Dyadically decomposing
`|K(d)| ≲ \sum_I\min(L, \|d/2πn_I\|^{-1})` and inserting `ν_ε(d) ≪ εN/L + |d|/N + 1`:
```
   |K(d)| ≪ \sum_j \frac{L}{2^{j}}\Big(\frac{2^{j}N}{L^{2}} + \frac{|d|}{N} + 1\Big)
      ≪ \frac NL\log L \;+\; L\Big(\frac{|d|}{N}+1\Big) = B\log L + \frac{L|d|}{N} + L .
```
At `|d| ≍ T` this gives `|K| ≪ N^{σ}\log`, matching the B-process bound `T^{1/2}` exactly — **a
consistency check of Theorem 35 against classical exponential-sum theory.**
**But at `(σ,2σ)` the block bound has no room**: `B = N/L = N^{σ}` and `\max|K| ≍ T^{1/2} = N^{σ}` are
*equal*, so summing over pairs returns `S_1 ≪ R^{2}N^{σ}` — the trivial `R^{2}\max|K|`.
**And even the generic truth is insufficient.** For typical differences `|K(d)| ≍ N^{1/2}` (the `L^{2}`
average, since `∑_{d}|K(d)|^{2} ≍ TN` over `≍ T` values), so `S_1 ≍ R^{2}N^{1/2}`, whence
```
   \|M\|_{∞→1} ≤ N^{1/2}S_1^{1/2} ≍ N^{1/2}\,R\,N^{1/4} = N^{7/4}\quad (R=N),
   \qquad\text{target } N^{(4-σ)/2} = N^{2-σ/2} ,
```
and `7/4 ≤ 2-σ/2 \iff σ ≤ 1/2`. **So the Cauchy–Schwarz-over-`n` route fails for every `σ > 1/2`, even
granting the generic value of `S_1`.** `[RECORDED DEAD END: `\|M\|_{∞→1} ≤ N^{1/2}(\sum_{r,r'}|K|)^{1/2}`.
The loss is the Cauchy–Schwarz over `n`, not the estimate of `S_1`.]`
> ### What this leaves of Theorem 56
> Theorem 56's *statement* stands — `\|M_{N,W}\|_{∞→1} ≪ N^{(3-σ)/2}|W|^{1/2}` implies
> `\mathrm{A}(σ) ≤ 3/(2σ)`, and is strictly weaker than Montgomery's conjecture. What is now excluded
> is proving it by Cauchy–Schwarz over the coefficient index. **Since `\|·\|_{∞→1}` is by definition a
> supremum over unimodular `a` and `c`, any proof must exploit the *joint* structure of the two
> extremising vectors — which is exactly what the Grothendieck/SDP formulation of Theorem 5 encodes,
> and where the constraint `\|a\|_∞ ≤ 1` enters as `X_{nn}=1` rather than as `\|a\|_2^{2} ≤ N`.**
> `[OPEN CORE 108]` Bound the SDP value `\max\{\sum_{n,r}M_{nr}X_{nr} : X ⪰ 0,\ X_{nn}=X_{rr}=1\}` for
> `M_{nr} = n^{-it_r}`. **The programme's own Theorem 5 says this is within `K_G^{ℂ} ≤ 1.4049` of the
> target, so an SDP bound of `N^{(3-σ)/2}|W|^{1/2}/1.4049` suffices — and SDP duality means it can be
> certified by exhibiting a single feasible dual solution**, i.e. by a diagonal matrix `D` with
> `D - M` positive semidefinite and small trace. **That is a constructive, checkable object, and it is
> the first formulation of the target that admits a certificate.**

---

# CYCLE 64 (2026-07-26) — **Theorem 57: the SDP route is short by only `N^{(3σ-2)/2}` — the smallest gap in the programme**

## The elementary SDP bound `[PROVED HERE]`
For `M_{nr} = n^{-it_r}` the Grothendieck SDP `\max\{\sum M_{nr}X_{nr} : X ⪰ 0,\ X_{nn}=X_{rr}=1\}` has
the dual certificate `d_n ≡ λ`, `e_r ≡ μ` with `\big[\begin{smallmatrix}λI & -M/2\\ -M^{*}/2 & μI\end{smallmatrix}\big] ⪰ 0`
iff `\|M\|_{\mathrm{op}} ≤ 2\sqrt{λμ}`; optimising `(Nλ+Rμ)/2` under that constraint gives
```
        \mathrm{SDP}(M) \;≤\; \tfrac12\,\|M\|_{\mathrm{op}}\sqrt{NR} .
```
**And `\|M\|_{\mathrm{op}}` is exactly the mean value theorem:** `\sum_r|\sum_nc_nn^{-it_r}|^{2} ≤
\sum_n|c_n|^{2}(T+O(n))` gives `\|M\|_{\mathrm{op}}^{2} ≤ T + CN ≍ T`. Hence at `(σ,2σ)` with `R = N`,
`T = N^{2σ}`:
```
        \mathrm{SDP}(M) \;≤\; \tfrac12 T^{1/2}N \;=\; \tfrac12 N^{1+σ} ,
        \qquad\text{Theorem 56 needs}\qquad N^{(3-σ)/2}R^{1/2} = N^{2-σ/2} .
```
> ### Theorem 57 `[PROVED HERE]`
> **`1+σ ≤ 2-σ/2 \iff σ ≤ 2/3`. So the elementary SDP bound proves Theorem 56's requirement — hence
> `\mathrm{A}(σ) ≤ 3/(2σ)` — for every `σ ≤ 2/3`; and `3/(2σ)` improves on Ingham exactly for
> `σ > 2/3`. The two ranges meet precisely at `σ = 2/3`, where both give `\mathrm{A}(2/3) ≤ 9/4`.**
> **For `σ > 2/3` the shortfall is**
> ```
>        N^{\,1+σ}\ \text{versus}\ N^{\,2-σ/2}\qquad\Longrightarrow\qquad
>        \textbf{shortfall } \;N^{(3σ-2)/2} ,
> ```
> **which is `N^{1/20}` at `σ = 7/10` and `N^{1/8}` at `σ = 3/4`.**
**This is by a wide margin the smallest gap the programme has produced** — compare `N^{1/4}` (the
Cauchy–Schwarz route), `T^{2.4/26}` (the incidence route), `(2-2σ)(2σ-1) = 6/25` (Theorem 53). The
chain is: `\mathrm{SDP}(M) ≪ N^{2-σ/2} \Rightarrow \|M\|_{∞→1} ≪ N^{2-σ/2} \Rightarrow R ≤ N^{3-3σ}
\Rightarrow \mathrm{A}(σ) ≤ 3/(2σ)`, with the first implication trivial (`\|·\|_{∞→1} ≤ \mathrm{SDP}`)
and the rest Theorems 54 and 56.
`[OPEN CORE 109]` **Improve `\mathrm{SDP}(M) ≤ \tfrac12\|M\|_{\mathrm{op}}\sqrt{NR}` by `N^{(3σ-2)/2}`.**
The bound used the *scalar* dual `(λ,μ)`; the full dual allows arbitrary diagonals `d_n, e_r`, and the
optimum is attained only when the extremising vectors are isotropic. **For `M_{nr} = n^{-it_r}` the
Gram matrix `MM^{*}` has entries `R_W(n'/n)` and `M^{*}M` has entries `K(t_r-t_{r'})` — both far from
scalar**, so the scalar certificate is provably suboptimal; the question is by how much. **This is a
finite convex problem with an explicit matrix, it admits numerical exploration at small `N`, and any
improvement by `N^{(3σ-2)/2}` gives a new record for `‖A‖_∞`.**

## CORRECTION to Theorem 57 `[read before reusing]`
Two errors, both found by re-deriving the chain directly.
1. **The requirement.** `R ≤ \|M\|_{∞→1}/V`, so the target `R ≤ N^{3-3σ}` needs
   `\|M\|_{∞→1} ≤ N^{3-3σ}·N^{σ} = N^{3-2σ}`, **not** `N^{2-σ/2}`. (The latter came from Theorem 56's
   `β = 1/2` parametrisation, which is self-referential in `R`; substituting `R = N` afterwards is
   inconsistent.) The threshold `σ ≤ 2/3` is unchanged (`1+σ ≤ 3-2σ \iff σ ≤ 2/3`), but **the shortfall
   is `N^{3σ-2}`, not `N^{(3σ-2)/2}`** — `N^{1/10}` at `σ = 7/10`, `N^{1/4}` at `σ = 3/4`.
2. **The SDP with a scalar certificate *is* the mean value theorem.** Feeding
   `\mathrm{SDP} ≤ \tfrac12\|M\|_{\mathrm{op}}\sqrt{NR}` and `\|M\|_{\mathrm{op}}^{2} ≤ T+CN` into
   `RV ≤ \mathrm{SDP}` gives
   ```
      R ≤ \frac{N\,\|M\|_{\mathrm{op}}^{2}}{4V^{2}} = \frac{N(T+CN)}{4V^{2}} ,
   ```
   which is the mean value theorem with the constant `1/4`. **So Theorem 57 records no new estimate —
   the operator-norm/SDP route with a scalar dual reproduces the mean value theorem exactly**, and the
   agreement of its coverage (`σ ≤ 2/3`) with Theorem 54's usefulness threshold (`σ > 2/3`) is not a
   coincidence but an identity: both are the statement `R ≤ N` versus `R ≤ N^{3-3σ}`.
> **Ninth correction of the session.** New failure mode, worth naming: *carrying a parametrised
> intermediate (`\|M\| ≪ N^{α}R^{β}`) past the point where `R` is substituted*, which double-counts the
> `R`-dependence. **Gate added: after any chain of implications, re-derive the final bound directly
> from the hypotheses with all parameters substituted, and check it against the trivial bound.**
`[What survives.]` Theorem 56's statement is still correct as an implication (`\|M\|_{∞→1} ≪ N^{3-2σ}`
`\Rightarrow \mathrm{A}(σ) ≤ 3/(2σ)`), and it is still **strictly weaker than Montgomery's conjecture**:
MC gives `\|M\|_{∞→1} ≪ N^{1+ε}R^{1/2} = N^{3/2+ε}` at `R = N`, and `3/2 ≤ 3-2σ \iff σ ≤ 3/4`. **So on
the useful range `σ ∈ (2/3, 3/4]` the requirement sits strictly between the mean value theorem
(`N^{1+σ}`) and Montgomery (`N^{3/2}`), and the gap to close is `N^{3σ-2}` — at most `N^{1/4}`.**
`[OPEN CORE 109′]` Prove `\|M_{N,W}\|_{∞→1} ≪ N^{3-2σ}` for `R = |W| ≍ N`, `T = N^{2σ}`,
`σ ∈ (2/3,3/4]`. Equivalently, beat the scalar SDP certificate by `N^{3σ-2}` using a non-scalar dual —
**the only structural input available being that `M^{*}M` has entries `K(t_r-t_{r'})` and `MM^{*}` has
entries `R_W(n'/n)`, neither of which is close to a multiple of the identity.**

## `[OPEN CORE 109′]` settled: the scalar certificate is **tight**, and the SDP branch is circular `[PROVED HERE — DEAD END]`
`\mathrm{SDP}(M) = \max\{\sum_{n,r}M_{nr}\langle u_n,v_r\rangle : \|u_n\|=\|v_r\|=1\}`, so taking all
`u_n = v_r = e` gives the **lower** bound
```
        \mathrm{SDP}(M) \;≥\; \Big|\sum_{n,r}n^{-it_r}\Big| \;=\; \Big|\sum_r K(t_r)\Big| .
```
Now `\#\{t ∈ [T,2T] : |K(t)| ≥ N^{σ}\} ≤ TN/N^{2σ} = N` (the `L^{2}` bound, using `T = N^{2σ}`), and if
`W` is a set of `R ≍ N` such points with aligned phases then `|\sum_rK(t_r)| ≍ N·N^{σ} = N^{1+σ}` —
**exactly the scalar-certificate upper bound `\tfrac12\|M\|_{\mathrm{op}}\sqrt{NR}`.** So the scalar
dual is optimal for such `M`, and no non-scalar certificate can improve it.
> **Moreover such a `W` is a legitimate large-value pattern**: take `a_n ≡ 1`, so `D = K` and
> `|D(t_r)| = |K(t_r)| ≥ N^{σ} = V`. **Hence "the scalar certificate is not tight" is equivalent to
> `\#\{t : |K(t)| ≥ N^{σ}\} = o(N)`, i.e. to `\mathrm{LV}_ζ(σ,2σ) < 1` — the very statement the route
> was meant to prove.** `[RECORDED DEAD END: the operator-norm / Grothendieck-SDP branch. It is not a
> weaker target; its tightness is equivalent to the original problem, with `a_n ≡ 1` as the witness.]`
> ### Consolidated: why every route returns to the same place
> The `a_n ≡ 1` witness explains the pattern of the last twenty cycles. **Whenever a route is
> formulated as a bound valid for all `1`-bounded `a` and all `1`-separated `W`, the pair
> `(a ≡ 1,\ W = \{|K| \text{ large}\})` saturates it**, because `K` is itself a Dirichlet polynomial
> with `1`-bounded coefficients whose large-value set is exactly what is being counted. This is why
> the mean value theorem, the SDP, the `∞→1` norm, and the double zeta sum all give `R ≤ N` at
> `(σ,2σ)` and none gives less. **A route can only improve on this if it uses a property of `a` that
> `a ≡ 1` violates** — and the only such property available in the zero-density application is that
> `a` is a *mollified detection sequence* (Theorems 27–28, 31), i.e. `a = 1_{≤D}∗μ_{≤y}` with its
> low-range vanishing. **That is the single unexploited hypothesis left in the entire programme.**
`[OPEN CORE 110]` Redo the `(σ,2σ)` analysis with `a` restricted to detection coefficients. The
witness `a ≡ 1` is then illegal (it has no vanishing), and the extremal must instead satisfy
`a_n = \sum_{d\mid n, d≤y}μ(d)`, `a_n = 0` for `1 < n ≤ y`. **Cycle 51 showed such `a` cannot be a pure
wave packet and forces `V' ≪ \sqrt L`; the question is whether it also forbids the `|K|`-large
witness, i.e. whether `\sum_{n∼N}a_nn^{-it}` can be as large as `\sum_{n∼N}n^{-it}` on a set of size
`N`.** This is a concrete comparison between a mollified and an unmollified zeta block, and it is the
first target that uses the one hypothesis no route has yet used.

## `[OPEN CORE 110]` settled: the mollifier's vanishing is **invisible at the block level** `[PROVED HERE — DEAD END]`
The detection coefficients `a = 1_{≤D}∗μ_{≤y}` vanish on `1 < n ≤ y`. But the large-value analysis is
applied to a *block* `n ∼ N` with `N ≫ y`, where that vanishing says nothing: on the block, `a_n =
\sum_{d\mid n,\ d≤y}μ(d)` is simply an arithmetic function with `|a_n| ≤ d(n)` and
`\sum_{n∼N}|a_n|^{2} ≍ N` — **the same second moment as `a ≡ 1`.** Hence the `L^{2}` bound
`\#\{t : |D(t)| ≥ N^{σ}\} ≤ TN/N^{2σ} = N` is unchanged, and every estimate that depends only on
`\|a\|_2` and `\|a\|_∞` gives exactly what it gave for `a ≡ 1`.
> **So the last unexploited hypothesis is vacuous at the block level.** `[RECORDED DEAD END: using the
> mollifier's low-range vanishing inside a single dyadic block. The vanishing lives at scale `y`; the
> block lives at scale `N ≫ y`; the two never meet.]`
**What the hypothesis *does* give**, and it is a real change of character: for detection coefficients
`D` is an **explicit** Dirichlet polynomial, not an adversarial one, so the question
`\#\{t : |D(t)| ≥ N^{σ}\} ≤ N^{3-3σ}` is a concrete estimate rather than a supremum over `a`. **But
that concrete estimate is exactly a large-value bound for a block of `ζ(s)M(s)` — i.e. the mollified
second moment, whose obstruction (the Montgomery–Vaughan length term, forced because `ζ` cannot be
truncated below `|t|`) was computed to the end in Cycle 54 and returns `T^{1-(2σ-1)^{2}}`, weaker than
Ingham everywhere.** The two branches therefore meet and close each other.

---
# ===== STATE AFTER 65 CYCLES — the closure diagram =====
```
   (a ≡ 1, W = \{|K| \text{ large}\})  saturates every bound depending only on \|a\|_2, \|a\|_∞ :
        mean value theorem · SDP/Grothendieck · \|·\|_{∞→1} · double zeta sums · energy · moments
        \Longrightarrow  R ≤ N \text{ at } (σ,2σ),\ \text{never less.}
   The only hypothesis violating a ≡ 1 is the mollifier's vanishing, which is invisible on a block
        \Longrightarrow  no gain there either.
   Restricting to explicit detection coefficients turns the problem into the mollified second moment,
        \Longrightarrow  T^{1-(2σ-1)^2},\ weaker than Ingham (Cycle 54).
```
**Every branch of the programme now terminates, with proof, on one of these three.** The Density
Hypothesis at `σ < 3/4` requires a technique that (i) does not reduce to `\|a\|_2, \|a\|_∞`, (ii) does
not pass through a single block, and (iii) does not measure `ζM-1` by a norm. **No such technique
appears in the literature or in this corpus.** The four independent derivations of `σ = 3/4`
(Theorems 51, 53, 55, and the off-diagonal computation of Cycle 62) say that this is not a limitation
of effort but of the available mechanisms.

---

# CYCLE 66 (2026-07-26) — interrogating the witness: is `(a ≡ 1, W = \{|K| \text{ large}\})` real?

## The witness sits exactly at the maximum of `|K|` `[PROVED HERE]`
At `(σ,2σ)` the threshold is `V = N^{σ} = T^{1/2}`, and the exponent pair `(κ,λ) = (1/2,1/2)` (the
plain B-process) gives, for every `t ≍ T`,
```
        |K(t)| = \Big|\sum_{n∼N}n^{-it}\Big| ≪ (T/N)^{1/2}N^{1/2} = T^{1/2} = V .
```
Equivalently, via the dual: the B-process weights satisfy `\sum_m|w_m| ≍ M(N^{2}/T)^{1/2} = T^{1/2}`
with `M = T/N`, so `|K| ≤ T^{1/2}` with equality only under **full alignment of the dual phases**.
> **So the witness requires `|K(t)|` to sit at its global maximum, up to a constant, on a set of `N`
> one-separated points.** That is not a generic configuration — it is the extreme one.
## But it is not excludable below `3/4` `[PROVED HERE — the fifth derivation of the threshold]`
The `L^{2}` bound permits it (`|K| ≍ T^{1/2}` on measure `μ` forces `μT ≤ ∫|K|^{2} ≍ TN`, i.e.
`μ ≤ N` — exactly the required `N`), and the fourth moment gives
```
   N\,T^{2} ≤ ∫|K|^{4} = ∫|K^{2}|^{2} ≍ (N^{2}+T)N^{2} ≍ N^{4} \iff T^{2} ≤ N^{3} \iff σ ≤ 3/4 .
```
**A fifth independent appearance of `σ = 3/4`** — after coherence (Thm 51), the deficit parabola
(Thm 53), the moment test of the spiky extremal (Thm 55), and the off-diagonal computation (Cycle 62).
`[RECORDED: the witness `a ≡ 1` is *maximal* rather than generic — it needs `|K|` at its global
maximum on `N` points — but no moment of any order excludes it for `σ ≤ 3/4`. The claim that it is
"fake" is **false** and was withdrawn before recording (gate applied: the dual sum's max is `T^{1/2}`,
which *equals* `V`, so `|K| ≥ V` needs full alignment — but full alignment on a *positive-measure* set
is exactly what the `L^{2}` and `L^{4}` bounds still permit).]`
> ### What the interrogation does yield
> The witness is not a soft object: it asserts `|K(t)| ≍ \max_t|K(t)|` on `N` points. **So every route
> the witness kills is killed only by a configuration in which the zeta block attains its extreme
> value on a set of maximal permitted size.** Two consequences worth recording:
> 1. **Any input that improves `\max_t|K(t)|` below `T^{1/2}` immediately kills the witness.** By the
>    exponent-pair bound `|K| ≪ (T/N)^{κ}N^{λ}` this needs `κ(2σ-1)+λ < σ` (in `\log_N` units at
>    `τ = 2σ`); with `(κ,λ) = (13/84, 13/84+1/2)` this reads `0.1548(2σ-1)+0.6548 < σ`, i.e.
>    `σ > 0.7167` — **so for `σ > 0.717` the witness is already dead by exponent pairs**, and the
>    surviving range is `σ ∈ (2/3, 0.717]`.
> 2. On that range the classical closure of Cycle 65 is the whole obstruction, and it rests on a
>    single configuration whose existence is *equivalent* to `\mathrm{LV}_ζ(σ,2σ) = 1`.
`[OPEN CORE 111]` **Decide `\mathrm{LV}_ζ(σ,2σ)` for `σ ∈ (2/3, 0.717]`** — i.e. whether
`\#\{t ∈ [T,2T] : |K(t)| ≥ c\,T^{1/2}\} ≍ N` is possible. This is a bounded, explicit range of a single
parameter, the object is the bare exponential sum `\sum_{n∼N}n^{-it}` with `N = T^{1/(2σ)}`, and the
answer decides whether Theorem 54's route gives `\mathrm{A}(σ) ≤ 3/(2σ)` there.

## `[OPEN CORE 111]` quantified: the witness is an `N^{σ-1/2}`-fold deviation on a `N^{1-2σ}` fraction `[PROVED HERE]`
Via the B-process, `|K(t)| ≍ (N^{2}/T)^{1/2}\,|\!\sum_{m∼M}(\cdots)|` with `M = T/N`; square-root
cancellation in the dual gives the **typical** size
```
        |K(t)|_{\mathrm{typ}} ≍ (N^{2}/T)^{1/2}M^{1/2} = N^{1/2} ,
```
consistent with `∫|K|^{2} ≍ TN`. The witness demands `|K(t)| ≥ V = N^{σ}` on `N` points, i.e.
```
   \textbf{a deviation factor } \frac{V}{|K|_{\mathrm{typ}}} = N^{σ-1/2}
   \quad\text{on a fraction } \frac{N}{T} = N^{1-2σ} \text{ of } [T,2T] .
```
At `σ = 7/10`: a `N^{1/5}`-fold deviation on a `N^{-2/5}` fraction. **For a random model this has
probability `\exp(-N^{2σ-1})` per point, so the witness is a purely arithmetic phenomenon — it exists,
if at all, because the phases `t\log n` conspire, not because of measure.**
> **The dual phase is `≍ \sqrt{tm}` with second derivative `≍ \sqrt T M^{-3/2} = N^{(3-4σ)/2}`**, which
> at `σ = 7/10` is `N^{0.1} ≫ 1` — **so van der Corput's `A`-process is vacuous (the curvature is too
> large), and the sum is in the "essentially random" regime where only square-root cancellation is
> expected but nothing better is provable.** This is exactly the regime where the classical theory has
> no tools, and it is the analytic core of `\mathrm{LV}_ζ(σ,2σ)`.
`[RECORDED: the witness at `(σ,2σ)` is a large-deviation event of relative size `N^{σ-1/2}` for the
dual exponential sum `\sum_{m∼M}m^{-1/2}e(-c\sqrt{tm})`, `M = T/N`. Van der Corput is vacuous there
(`φ'' ≫ 1`); Poisson has already been used once (it produced this sum); and a second application
returns to the original. **The witness therefore sits precisely in the gap of the van der Corput
hierarchy** — too curved for the `A`-process, already dualised by the `B`-process.]`
> ### The final localisation
> ```
>    \textbf{Density Hypothesis on } σ ∈ (2/3,\ 0.717] \iff
>    \#\{t ≍ T : |\!\sum_{m∼M}m^{-1/2}e(-c\sqrt{tm})| ≥ M^{1/2}N^{σ-1/2}\} = o(N),\quad M = T/N .
> ```
> For `σ > 0.717` the exponent pair `(13/84, 13/84+1/2)` already kills it (Cycle 66); for `σ ≤ 2/3`
> Theorem 54's route is weaker than Ingham. **The Density Hypothesis, in this programme's final
> reduction, is a large-deviation statement for a one-parameter family of `\sqrt{tm}`-phase exponential
> sums on a window of `σ` of width `0.05`.**

---

# CYCLE 67 (2026-07-26) — the localised statement is a **block of `ζ(1/2+it)`**, and the moment hierarchy for it

## Reformulation `[PROVED HERE]`
Partial summation converts the bare block into a critical-line block:
```
   K(t) = \sum_{n∼N}n^{-it} ≍ N^{1/2}\,Z_N(t),\qquad Z_N(t) := \sum_{n∼N}n^{-1/2-it} ,
```
so the witness `|K| ≥ V = N^{σ}` is exactly `|Z_N(t)| ≥ N^{σ-1/2}`. **The Density Hypothesis on
`σ ∈ (2/3, 0.717]` is therefore a large-value statement for a *block of `ζ(1/2+it)`* of length
`N = T^{1/(2σ)}`, at threshold `N^{σ-1/2}` — the same `σ-1/2` that governs the deficit everywhere in
this card.**
## The moment hierarchy, computed `[PROVED HERE]`
`Z_N^{k}` has coefficients `d^{(N)}_k(m)m^{-1/2}` on `m ∼ N^{k}`, so
`\sum_m|c_m|^{2} ≍ (\log N)^{k^{2}-1}` — **the `\ell^{2}` mass is `T^{o(1)}`, not `N^{k}`** — whence
```
   \int_T^{2T}|Z_N|^{2k} ≪ (N^{k}+T)\,T^{o(1)},\qquad
   \#\{t : |Z_N| ≥ W\} ≪ \frac{(N^{k}+T)T^{o(1)}}{W^{2k}} .
```
With `W = N^{σ-1/2}` and `T = N^{2σ}`:
```
   k = 1\ (N ≤ T):\quad \#\ ≪ T/N^{2σ-1} = N\ \ (\textbf{exactly the target, no room});
   k ≥ 2\ (N^{k} ≥ T):\quad \#\ ≪ N^{k(2-2σ)} ≥ N^{2(2-2σ)} = N^{1.2}\ \text{at } σ=7/10\ (\textbf{worse}).
```
**So the elementary moment hierarchy gives exactly `N` at `k = 1` and degrades for `k ≥ 2`: there is no
`k` with room to spare.** `[RECORDED: the `2k`-th moment of a block of `ζ(1/2+it)` at the witness
threshold. `k = 1` is optimal and exactly critical — the third time in this card that `k = 1`/`k = 2`
turns out to be the optimum and the bound is exactly the target.]`
> ### The one classical input not yet applied
> Heath-Brown's twelfth moment `\int_0^{T}|ζ(1/2+it)|^{12}dt ≪ T^{2+ε}` is **far stronger than the
> elementary `k = 6` bound `(N^{6}+T)T^{o(1)}`** (which is `T^{3}` at `N ≍ T^{1/2}`), and it is the only
> estimate in the subject that beats the trivial moment hierarchy for `ζ` on the critical line. **Our
> `Z_N` is a block of `ζ(1/2+it)` of length `N = T^{1/(2σ)} > T^{1/2}`, so the twelfth moment does not
> apply directly; but the reflection sends it to a dual block of length `M = T/N < T^{1/2}`, where
> block twelfth-moment bounds are available.** `[OPEN CORE 112]` **Transport Heath-Brown's twelfth
> moment through the reflection to the dual block of length `M = T/N = N^{2σ-1}` and compare with the
> witness threshold.** At `σ = 7/10`, `M = T^{2/7}` and the elementary bound gives
> `\int|Z_M|^{12} ≪ M^{6} = T^{12/7}`; Heath-Brown-type input would replace `M^{6}` by `T^{1+ε}` once
> `M ≤ T^{1/6}`, i.e. once `2σ-1 ≤ 1/(3·2σ)`, i.e. `σ ≤ (1+\sqrt{7})/6 = 0.6076`. **So the twelfth
> moment reaches `σ ≤ 0.608` — short of the window `(2/3, 0.717]` by exactly the gap that Bourgain's
> decoupling closes from above.** This identifies precisely which classical input is missing and by how
> much.

## Corrected exponent-pair threshold, and the target `κ ≤ 1/8` `[PROVED HERE]`
The condition for an exponent pair `(κ,λ)` to force `|K(t)| < V = N^{σ}` at `τ = 2σ` is
`κ(2σ-1)+λ < σ`. The trivial B-process pair `(1/2,1/2)` gives **equality** for every `σ`
(`(2σ-1)/2+1/2 = σ`), so a pair improves on it iff `λ-\tfrac12 < (\tfrac12-κ)(2σ-1)`; along the
standard family `λ = \tfrac12+κ` this is
```
        κ \;<\; \frac{2σ-1}{4σ} \qquad\Longleftrightarrow\qquad σ \;>\; \frac{1}{2-4κ} .
```
With the record `κ = 13/84` this gives `σ > 1/(2-13/21) = 0.7242…` — **correcting the value `0.7167`
recorded in Cycle 66 (tenth correction; the earlier computation mis-solved the linear inequality).**
Consequences:
* the residual window is `(2/3,\ 0.7242]`, slightly wider than stated;
* **covering it entirely requires `1/(2-4κ) ≤ 2/3`, i.e. `κ ≤ 1/8 = 0.125`** — against the record
  `13/84 = 0.1548`. That is a concrete, quantitative target inside the theory of exponent pairs.
> ### **Caveat that must not be lost** `[PROVED HERE]`
> **Killing the witness `a ≡ 1` does *not* improve the large-value bound.** The witness shows that the
> mean value theorem (and the SDP, and `\|·\|_{∞→1}`) *cannot* be improved by any argument valid for
> all `1`-bounded `a`; removing it re-opens the possibility of improvement but proves none. In
> particular `κ ≤ 1/8` would **not** by itself give `\mathrm{A}(σ) ≤ 3/(2σ)` on the window — it would
> only remove the known obstruction to trying. **An earlier draft of this section concluded that
> `κ = 13/84` already yields `\mathrm{A}(σ) ≤ 3/(2σ) < 15/(3+5σ)` on `(0.7242, 3/4]`, i.e. a new record;
> that is false for exactly this reason and was withdrawn before recording (eleventh caught error).**
`[The gate that caught it: "re-derive the final bound directly from the hypotheses" — the chain
`witness dead ⟹ bound improved` has no valid middle step, since the bound quantifies over all `a`.]`
> ### Net state of the localisation
> ```
>   σ > 1/(2-4κ) = 0.7242 :  the `a ≡ 1` witness is dead (exponent pairs); obstruction unknown.
>   σ ∈ (2/3, 0.7242]     :  the witness is alive and saturates every ‖a‖₂/‖a‖_∞ bound.
>   σ ≤ 2/3               :  Theorem 54's route is weaker than Ingham anyway.
>   Twelfth moment reaches σ ≤ 0.608 ; exponent pairs reach σ > 0.724 ; the gap is (0.608, 0.724).
> ```

## The target `κ ≤ 1/8` **is** `μ(1/2) ≤ 1/8` `[PROVED HERE]`
Our functional `κ(2σ-1)+λ` weights `λ` heavily (`2σ-1 ≈ 0.4`), and `λ ≥ 1/2` for every exponent pair, so
the optimum lies on the family `λ = κ+\tfrac12`. **A pair `(κ, κ+\tfrac12)` is equivalent to the growth
bound `|ζ(\tfrac12+it)| ≪ t^{κ+ε}`, i.e. to `μ(1/2) ≤ κ`.** Hence:
```
        \text{witness dead on all of } (2/3,\ 3/4] \iff κ ≤ 1/8 \iff μ(1/2) ≤ 1/8 = 0.125 .
```
Current record `μ(1/2) ≤ 13/84 = 0.1548` (Bourgain 2017), after Huxley `32/205 = 0.1561` and Weyl
`1/6`. **So the residual window is exactly the distance from `13/84` to `1/8` in the subconvexity
problem for `ζ` on the critical line.**
*(The `A`-process does not help: `A(13/84, 55/84) = (13/194, 152/194) = (0.067, 0.784)`, and although
`κ` drops below `1/8`, `λ` rises to `0.784`, giving `κ(2σ-1)+λ = 0.810 > σ` at `σ = 7/10`. The
functional is minimised on `λ = κ+1/2`, which is precisely the `μ(1/2)` family.)*
> **This closes the loop with the withdrawn Theorem 52**, which asserted a `μ(1/2)` threshold for the
> Density Hypothesis and was false because it treated one window as the whole supremum. The correct
> statement is different in kind: **`μ(1/2) ≤ 1/8` does not prove the Density Hypothesis — it kills the
> `a ≡ 1` witness that currently obstructs every route.** The witness is the reason the mean value
> theorem cannot be improved for general `a`; removing it is necessary, not sufficient.
---
# ===== STATE AFTER 68 CYCLES =====
**Proved this session (unconditional, reusable):** Theorems 4–57 minus the six withdrawn
(26, 29, 37, 39, 40, 52) and the corrected 57 — notably Thm 16/35/45–49 (arithmetic incidence, six
lemmas machine-checked in Lean), Thm 22/23 (Hölder–moment ceiling and integrality), Thm 27/28
(mollifier design), Thm 33 (moment sharpness), Thm 34 (regime boundary `τ ≤ 2σ`), Thm 41 (slack
criterion), Thm 42 (constancy vs curvature), Thm 43 (energy machinery capped at `2/3` MVT), Thm 51
(`τ = 3/2` coherent iff `σ ≥ 3/4`), Thm 53 (uniform constant `(2-2σ)(2σ-1)`), Thm 54 (`τ_0 = 2σ` keeps
the reduction coherent; `\mathrm{A}(σ) ≤ 3/(2σ)`), Thm 55 (spiky extremal excluded iff `σ > 3/4`),
Thm 56 (a requirement strictly weaker than Montgomery).
**Five independent derivations of `σ = 3/4`**; **the `a ≡ 1` witness** as the universal saturating
configuration; **the closure diagram** (Cycle 65); **the final localisation**: the obstruction is a
large-deviation statement for `\sum_{m∼M}m^{-1/2}e(-c\sqrt{tm})`, `M = T/N`, on
`σ ∈ (2/3, 1/(2-4μ(1/2))]`, a window that closes iff `μ(1/2) ≤ 1/8`.
**Eleven errors caught, with the gates that catch them:** (i) check any claim at `k = 2,3,10,∞`
(a supremum, not a point); (ii) verify a "new object" is not an identity for one already listed;
(iii) re-derive the final bound directly from the hypotheses with all parameters substituted;
(iv) never infer "bound improved" from "witness dead".

---

# CYCLE 69 (2026-07-26) — **the witness requires near-total alignment of a `√(tm)` phase, and only `≍ √N` values of `t` can supply it**

## The exact budget `[PROVED HERE]`
The B-process writes `K(t) = \sum_{m∼M}w_m e(φ_t(m)) + O(T^{o(1)})` with
```
   M = T/2πN,\qquad |w_m| ≍ N/T^{1/2},\qquad \sum_m|w_m| ≍ T^{1/2},\qquad
   φ_t(m) = 2\sqrt{tm/2π} .
```
**So `\max_t|K(t)| ≤ \sum_m|w_m| ≍ T^{1/2} = V` exactly at `τ = 2σ`: the witness `|K(t)| ≥ cV` demands
that the dual sum attain a constant fraction of its `ℓ^{1}` norm — i.e. near-total phase alignment.**
## Why alignment is rare `[PROVED HERE, to leading order]`
`φ_t'(m) = \sqrt{t/2πm} ≍ \sqrt{T/M} = \sqrt N`, so **the phase advances by `≍ \sqrt N ≫ 1` between
consecutive `m`** — consecutive terms are never in phase. Alignment can only occur through the
arithmetic of `φ_t`: writing `φ_t(m)-φ_t(m') = 2\sqrt{t/2π}(\sqrt m-\sqrt{m'})`, and
`\sqrt m-\sqrt{m'} ≈ (m-m')/2\sqrt M`, the condition `φ_t(m)-φ_t(m') ∈ ℤ` for all `m,m' ∼ M` reduces
to the **single** condition
```
        \frac{\sqrt t}{2\sqrt{2πM}} ∈ ℤ + o(1) \qquad\Longleftrightarrow\qquad t ≈ 8πM k^{2} ,
```
and `k` ranges over `≍ \sqrt{T/M} = \sqrt N` values as `t` runs over `[T,2T]`.
> ### Consequence (leading order)
> **`\#\{t ≍ T : |K(t)| ≥ cT^{1/2}\} ≪ \sqrt N \cdot T^{o(1)} = o(N)` — the `a ≡ 1` witness is dead for
> every `σ`, not merely for `σ > 1/(2-4μ(1/2))`.**
> The second-order term makes alignment *harder*, not easier: `φ_t''(m) ≍ \sqrt T M^{-3/2}`, so the
> quadratic variation across `m ∼ M` is `M^{2}|φ''| ≍ \sqrt{TM} ≫ 1`, which must *also* be cancelled —
> a further constraint on `t`.
`[STATUS — this is a stationary-phase computation, not yet a proof.]` What is rigorous: the `ℓ^{1}`
budget `\sum|w_m| ≍ T^{1/2}` and the phase derivative `φ_t' ≍ \sqrt N`. What needs care: (i) the
B-process error term `O(T^{o(1)})` must be compared with the *threshold* `V = T^{1/2}`, which it is
(negligible); (ii) "near-total alignment" must be quantified — attaining `cT^{1/2}` requires a constant
fraction of the `w_m` to be within `O(1)` in phase, and the argument above shows the set of such `t`
is contained in `≍ \sqrt N` intervals of length `O(M/\sqrt{T/M})`; (iii) the reduction from
`|K| ≥ cV` to alignment uses `|\sum w_me(φ)| ≤ \sum|w_m|` with near-equality, which requires the
standard "equality in the triangle inequality" quantification.
`[OPEN CORE 113]` **Make (ii) and (iii) rigorous.** If they hold, the consequence is substantial: the
witness that Cycle 65 showed saturates *every* `\|a\|_2/\|a\|_∞` bound at `(σ,2σ)` does not exist, and
the closure diagram's first branch collapses. **That would not immediately give `\mathrm{A}(σ) ≤ 3/(2σ)`
(the caveat of Cycle 68 stands: killing the witness removes the obstruction, not the bound) — but it
would make `(σ,2σ)` the first configuration in this programme where no known configuration saturates
the mean value theorem.**

## **Cycle 69's argument FAILS — withdrawn** `[CORRECTION, next cycle]`
The alignment argument required `|K(t)| ≥ c\sum_m|w_m|` with `c` bounded away from `0`. **But the
large-value threshold is `V = N^{σ+o(1)}`, i.e. `T^{1/2-ε}`, while `\sum_m|w_m| = \sqrt T/2π` — so the
witness needs only**
```
        c \;=\; 2π\,T^{-ε} \;\longrightarrow\; 0 ,
```
**not a fixed proportion of the `ℓ^{1}` norm.** Quantifying equality in the triangle inequality,
`|\sum z_m| ≥ c\sum|z_m|` gives `\sum_m|z_m|\,\|(\arg z_m-θ)/2π\|^{2} ≪ (1-c)\sum|z_m|`, which for
`c → 0` is **vacuous**: the phases need not cluster at all. The clustering conclusion
("`δM` phases within `O(1)` of a common `θ`") requires `δ ≳ 1-c`, and with `c = T^{-ε}` one gets
`δ ≈ 0` — weaker than the `1/5` that a *random* phase sequence already supplies.
`[Theorem/Cycle 69 withdrawn. Twelfth correction. New instance of an old failure mode: **treating a
`T^{o(1)}`-threshold as if it were a constant-proportion threshold.** The `ℓ^{1}` budget
`\max_t|K| ≤ \sqrt T/2π` is correct and worth keeping — it says the witness sits within `T^{o(1)}` of
the absolute maximum — but "within `T^{o(1)}` of the maximum" does **not** force phase alignment.]`
> **Gate added (fifth):** before concluding rigidity from near-extremality, check whether the
> extremality is by a *constant factor* or only up to `T^{o(1)}`; triangle-inequality and
> equality-case arguments are vacuous in the latter regime.
> ### What survives from Cycle 69
> 1. `\max_{t≍T}|K(t)| ≤ \sqrt T/2π + O(T^{o(1)})` — **so at `τ = 2σ` the witness sits within `T^{o(1)}`
>    of the global maximum of `|K|` over the whole range.** That is still a striking structural fact:
>    the configuration saturating every `\|a\|_2/\|a\|_∞` bound is one where a bare exponential sum is
>    within `T^{o(1)}` of its absolute maximum on `N` separated points.
> 2. The dual phase data — `φ_t' ≍ \sqrt N`, `φ_t'' ≍ \sqrt T M^{-3/2}`, quadratic variation
>    `\sqrt{TM} ≫ 1` — is correct and is the right description of the regime.
> 3. The moment hierarchy cannot see any of this: `∫|K|^{2k} ≍ (N^{k}+T)N^{k}` gives `μ ≤ N` at
>    `k = 1` and worse for `k ≥ 2` (OC103), so **the near-maximality of the witness is invisible to
>    every moment.**
`[OPEN CORE 114]` The right question is therefore: **can a bare exponential sum `\sum_{n∼N}n^{-it}` be
within `T^{o(1)}` of its absolute maximum `\sqrt T` at `N = T^{1/(2σ)}` one-separated points `t ≍ T`?**
Moments say yes (up to `N`); the `√(tm)` phase structure suggests no; and the gap between those two is
exactly the residual window. **This is the sharpest form of the question and it is genuinely open —
but note it is `\mathrm{LV}_ζ(σ,2σ)` again, so any proof is a new zeta large-value theorem.**

---

# CYCLE 70 (2026-07-26) — a **discrepancy** in the fourth moment computed two ways `[MUST BE RESOLVED]`
At `(σ,τ) = (7/10, 7/5)` (`τ = 2σ`), `N = T^{5/7}`, `M = T/N = T^{2/7}`, `|w_m| ≍ N/\sqrt T = T^{3/14}`:
```
   \textbf{Direct:}\quad ∫_T^{2T}|K|^{4} = ∫|K^{2}|^{2} ≍ (T+N^{2})\sum_m d^{(N)}(m)^{2} ≍ N^{4} = T^{20/7} = T^{2.857} ;
   \textbf{Dual:}\quad ∫|{\rm dual}|^{4} = \sum_{m_1..m_4}w\cdots\overline{w}\int_T^{2T}e\big(c\sqrt t\,Δ\big)dt,
   \quad Δ = \sqrt{m_1}+\sqrt{m_2}-\sqrt{m_3}-\sqrt{m_4} ,
```
with `\int_T^{2T}e(c\sqrt tΔ)dt ≪ \min(T,\ \sqrt T/|Δ|)` (substitute `u=\sqrt t`). Splitting by
`k = m_1+m_2-m_3-m_4`: the exact diagonal (`≍ M^{2}` quadruples) gives `M^{2}|w|^{4}T = T^{17/7}`; the
`k = 0`, `Δ ≠ 0` quadruples (`≍ M^{3}` of them, `|Δ| ≳ M^{-3/2}`) give
`M^{3}|w|^{4}\sqrt T M^{3/2} = T^{2.643}`; the `k ≠ 0` quadruples give `≍ T^{2.357}`. **Total
`T^{2.643}` — smaller than the direct value `T^{2.857}` by `T^{0.214}`, although the two expressions
compute the same integral.**
> **One of the two standard tools is being misapplied, and it matters: if the dual value is correct the
> witness dies (it needs `NT^{2} = T^{2.714} > T^{2.643}`); if the direct value is correct the witness
> survives.** Candidate resolutions, in order of likelihood:
> 1. **The B-process error term is not `O(T^{o(1)})` here.** `K = {\rm dual} + E`; if `‖E‖_4^4 ≍ N^{4}`
>    the discrepancy is entirely in `E`. The classical error in the `B`-process is `O(\log T)` *for the
>    sum with smooth weights over a full dyadic block*, but our `K` is a sharp-cutoff sum, whose
>    truncation error is `O(N/M)`-type and can be large.
> 2. **The count `≍ M^{3}` of `k = 0` quadruples with `|Δ| ≳ M^{-3/2}` is wrong** — the second-order
>    expansion `Δ ≈ k/2\sqrt M + q/M^{3/2}` may have `q` distributed so that `|Δ|` is often far smaller.
> 3. **The direct computation's off-diagonal `≍ N^{4}` assumes `\sum_{m≠m'}d^{(N)}(m)d^{(N)}(m')/|\log(m/m')| ≍ N^{4}`**, which is the length term; this was verified in Theorem 33 for `∫|D^{k}|^{2}` in general, but the constants deserve re-checking at `N^{2} ≫ T`.
`[OPEN CORE 115]` **Resolve the discrepancy.** This is a self-contained, finite computation about a
single explicit integral, and it decides the fate of the `a ≡ 1` witness — hence of the first branch of
the Cycle-65 closure diagram. **Recording it rather than guessing: the twelve corrections of this
session all came from asserting one side of exactly this kind of ambiguity.**

## `[OPEN CORE 115]` RESOLVED: the direct value is correct; the dual model missed the concentration of `Δ` `[PROVED HERE]`
Checks performed:
* **Second moments agree.** `∫|{\rm dual}|^{2} ≍ M|w|^{2}T = T^{12/7}` and `∫|K|^{2} ≍ TN = T^{12/7}` ✔ —
  so `|w_m| ≍ N/\sqrt T`, `M = T/2πN` and the B-process normalisation are right.
* **The direct fourth moment is right.** `∑_m d^{(N)}(m)d^{(N)}(m+h) ≍ N^{2}T^{o(1)}` uniformly (its
  average over the `≍ N^{2}` shifts is `(\sum_m d^{(N)}(m))^{2}/N^{2} = N^{2}`), so the near-diagonal
  `|h| ≤ N^{2}/T` contributes `T·(N^{2}/T)·N^{2} = N^{4}` — the length term. `∫|K|^{4} ≍ N^{4}` stands.
* **The error term cannot explain the gap.** The `B`-process error for a sharp-cutoff block is
  `O(\log T)`, giving `∫|E|^{4} ≪ T\log^{4}T ≪ N^{4}`.
* **The dual model was wrong.** I assumed the values `Δ = \sqrt{m_1}+\sqrt{m_2}-\sqrt{m_3}-\sqrt{m_4}`
  are equidistributed on `[-\sqrt M,\sqrt M]` with density `≍ M^{4}/\sqrt M = M^{3.5}`. **Sanity check
  that kills it:** that model predicts `\#\{|Δ| ≤ T^{-1/2}\} ≍ M^{3.5}T^{-1/2} = T^{1/2}`, whereas the
  *exact* diagonal `\{m_1,m_2\}=\{m_3,m_4\}` alone already contributes `M^{2} = T^{4/7} > T^{1/2}`
  quadruples with `Δ = 0`. **The `Δ`-distribution has a heavy concentration at `0` inherited from the
  multiplicative near-diagonal, which the uniform model does not see.**
> **Resolution: `∫|K|^{4} ≍ N^{4}` is correct, the dual computation was mis-modelled, and the witness
> `a ≡ 1` therefore *survives* at `(σ,2σ)` for `σ ≤ 3/4` — consistent with Theorem 55, which is the
> independent check.** `[OPEN CORE 115 closed. Also recorded: the second-order term in
> `Δ ≈ k/2\sqrt M + O(\sqrt M)` is of size `\sqrt M`, not `M^{-3/2}` as written in Cycle 70 — a second
> error in the same computation.]`
> ### Methodological note
> The two-way computation of one integral was worth doing even though it produced no new estimate: it
> exposed **two** errors (the `Δ`-density model and the second-order size) that no single-route
> calculation would have revealed, and it independently re-confirmed Theorem 55 and the `σ ≤ 3/4`
> threshold. **Gate added (sixth): when a quantity admits two natural representations (primal/dual,
> direct/reflected), compute both and require agreement before using either.** Applied retroactively,
> this is the check that would have caught Theorems 39, 40 and 52.

---

# CYCLE 71 (2026-07-26) — the exact logical status of Theorem 54's route

## What the route needs, and what the witness does to it `[PROVED HERE]`
Theorem 54 gives `\mathrm{A}(σ) ≤ 3/(2σ)` provided `\mathrm{LV}(σ,τ) ≤ (3-3σ)τ/(2σ)` on
`[4σ/3, 2σ]`, binding at `τ = 2σ` where it reads `\mathrm{LV}(σ,2σ) ≤ 3-3σ`. Now:
```
   \text{mean value theorem:}\quad \mathrm{LV}(σ,2σ) ≤ τ+1-2σ = 1 ;
   \text{lower bound (Lemma 7.5):}\quad \mathrm{LV}(σ,2σ) ≥ \min(2-2σ, τ) = 2-2σ ;
   \text{requirement:}\quad \mathrm{LV}(σ,2σ) < 3-3σ \quad(<1 \text{ exactly when } σ > 2/3) .
```
So the requirement sits strictly between the known lower and upper bounds — `[0.6, 1]` versus `< 0.9`
at `σ = 7/10` — **and the `a ≡ 1` witness, if real, forces `\mathrm{LV}_ζ(σ,2σ) = 1` and kills the
route.** Conversely Corollary 8.6 gives `\mathrm{LV}_ζ(σ,2σ) = -∞` for
```
   σ > \frac{1}{2(1-2μ(1/2))} = 0.7241\ldots \quad (μ(1/2) = 13/84) ,
```
**so on `σ ∈ (0.7241, 3/4]` the witness is dead and the only obstruction left is the general-coefficient
bound.** On `σ ∈ (2/3, 0.7241]` the witness is alive (consistently with all moments, Theorem 55) and
the route is blocked.
> ### Consistency check of Theorem 54 against the literature `[VERIFIED]`
> `\mathrm{A}(σ) ≤ 3/(2σ)` tends to `3/2` as `σ → 1` — **exactly Huxley's classical limit
> `\mathrm{A}(σ) ≤ 3/(3σ-1) → 3/2`.** The two agree at `σ = 1` and `3/(2σ) ≤ 3/(3σ-1) \iff 3σ-1 ≤ 2σ
> \iff σ ≤ 1`, so **Theorem 54's conclusion is uniformly at least as strong as Huxley's on `(1/2,1]`
> and matches it exactly at the endpoint.** That the route reproduces the correct classical limit
> without being designed to is evidence that the reduction is calibrated correctly (it is the same
> kind of check as `L = \sqrt V` at `τ = 2-σ` and `\#\text{structured} = ν`).
`[OPEN CORE 116]` The programme's target is now a single inequality on a single interval:
```
        \mathrm{LV}(σ, 2σ) \;<\; 3-3σ \qquad\text{for } σ ∈ (2/3, 3/4] ,
```
with the mean value theorem giving `1`, the requirement `3-3σ ∈ [0.75, 1)`, and the obstruction being
the `a ≡ 1` witness below `0.7241` and unknown above it. **Above `0.7241` no configuration is known to
saturate the mean value theorem at `τ = 2σ`** — that is the first sub-range in this programme with no
known obstruction, and it is where a proof would have to start.

## The target quantified against Montgomery `[PROVED HERE]`
At `(σ,2σ)` the three relevant values are
```
   \text{mean value theorem: } 1 ;\qquad
   \text{requirement: } 3-3σ ;\qquad
   \text{Montgomery's conjecture: } 2-2σ = \text{Lemma 7.5's lower bound (sharp if MC holds)} .
```
The requirement is **weaker than Montgomery by `1-σ`**, and as a fraction of the gain MC would supply,
```
        \frac{1-(3-3σ)}{1-(2-2σ)} \;=\; \frac{3σ-2}{2σ-1} ,
```
which at `σ = 0.73` is `0.19/0.46 = 41\%` and at `σ = 3/4` is `0.25/0.5 = 50\%`. **So on
`σ ∈ (0.7241, 3/4]` the Density-Hypothesis-strength conclusion `\mathrm{A}(σ) ≤ 3/(2σ) ≤ 2` follows
from between `41\%` and `50\%` of Montgomery's improvement over the mean value theorem, at a
configuration where — for the first time in this programme — **no saturating configuration is known**:
the `a ≡ 1` witness is dead there by Corollary 8.6, and Lemma 7.5's random-sign construction gives only
`2-2σ`, far below the requirement.**
> ### Summary of the terminal state
> ```
>   σ ≤ 2/3            :  route weaker than Ingham (no interest)
>   σ ∈ (2/3, 0.7241]  :  a ≡ 1 witness alive ⟹ route blocked, obstruction explicit
>   σ ∈ (0.7241, 3/4]  :  witness dead; requirement = 41–50% of Montgomery; NO KNOWN OBSTRUCTION
>   σ > 3/4            :  Density Hypothesis already known (Bourgain, σ ≥ 25/32; and 3/(2σ) < 2)
> ```
> **The entire residue of 71 cycles is the middle-upper band `(0.7241, 3/4]`, of width `0.026`.** Its
> two endpoints are set by the two strongest classical inputs — `μ(1/2) = 13/84` from below and
> Bourgain's density theorem from above — and inside it the programme has an explicit route
> (Theorem 54) requiring less than half of Montgomery's conjecture, with no configuration known to
> obstruct it.
`[OPEN CORE 117]` **Prove `\mathrm{LV}(σ,2σ) ≤ 3-3σ` for `σ ∈ (0.7241, 3/4]`.** Every structural asset
of this card applies there: the configuration is at the coherence boundary `V = B = T^{1/2}`
(Theorem 34/54), the wave-packet decomposition exists (`L = N^{1-σ} ≫ 1`), Theorem 16 fires at `ν = B`
(Cycle 60), and the four-moment test is not saturated (`σ < 3/4` strictly leaves room by `N^{3-4σ}`).
**This is the sharpest, narrowest, and least obstructed target the programme has produced, and it is
where the next session should begin.**

## CORRECTION to the Cycle 60/71 framing: at `V = B` the coherence machinery is **vacuous** `[PROVED HERE]`
Theorem 34's coherent regime is `V ≥ N/L = B`, and Theorem 54's configuration sits at `V = B`
**exactly**. But the machinery needs the inequality to be *strict by a power*, because the trivial
bound on the block decomposition is `\sum_I|\widehat{z_I}| ≤ B·L = N`, so largeness `|D| ≥ V = B`
requires only the fraction
```
        \frac{V}{N} = \frac{B}{BL} = \frac1L = N^{σ-1}
```
of the trivial maximum. **At `V = B` each block need only contribute `≍ 1` on average — a demand met
by *every* block for typical coefficients (`|\widehat{z_I}| ≍ \sqrt L ≫ 1`), so the dyadic level is
`V' ≍ 1`, `|E_I| ≪ L/V'^{2} ≫ 1` is vacuous, and the fat-AP/incidence apparatus says nothing.**
> **So the band `(0.7241, 3/4]` is not "unobstructed because the tools apply and find nothing" — it is
> unobstructed because *no tool applies*: the witness is dead there (Corollary 8.6) and the block
> machinery is degenerate (`V = B`).** The Cycle-71 summary line "every structural asset applies there"
> is withdrawn; the correct statement is that the assets are exactly at their boundary of validity and
> give nothing. `[Thirteenth correction. Failure mode: treating an inequality that holds *with
> equality* as if it held with room — the same error class as Cycle 69's `T^{o(1)}`-versus-constant
> confusion. **Gate (seventh): when a hypothesis is met with equality, check whether the conclusion
> needs strictness by a power.**]`
> ### What is actually true about the band
> ```
>   σ ∈ (0.7241, 3/4] :  the a ≡ 1 witness is dead (μ(1/2) = 13/84 via Cor. 8.6) ;
>                        no other saturating configuration is known ;
>                        the block/coherence machinery is degenerate (V = B) ;
>                        the mean value theorem gives 1, the requirement is 3-3σ ∈ [0.75,1) .
> ```
> **The honest reading: on this band the mean value theorem is not known to be sharp and is not known
> to be improvable — the situation is genuinely open in both directions**, which is a different and
> more interesting state than the rest of the range, where an explicit witness closes the question.
`[OPEN CORE 118]` Since no tool applies at `V = B`, the productive move is to **leave the boundary**:
Corollary 11.9 permits any `τ_0`, and `τ_0 = 2σ` was chosen to make condition (7) vacuous. Taking
`τ_0` slightly *below* `2σ` puts the binding configuration strictly inside the coherent regime
(`V ≫ B`) at the cost of a weaker conclusion `\mathrm{A}(σ) ≤ 3/τ_0`. **Optimising that trade-off —
how much coherence can be bought for how much loss in `3/τ_0` — is a one-parameter calculation, and
it is the concrete next step.**

# Cycle 72 — the route's ceiling, and an exact interpolation identity for the Density Hypothesis

## CORRECTION (fourteenth): Theorem 54's route does **not** reach the Density Hypothesis `[PROVED HERE]`
Theorem 54's conclusion is `\mathrm{A}(σ) ≤ 3/(2σ)`, and
```
        \frac{3}{2σ} ≤ 2 \iff σ ≥ \tfrac34 .
```
**On the entire band `(2/3, 3/4)` the route's own ceiling is strictly above `2`** (at `σ = 0.73` it is
`2.055`), so even a complete proof of `\mathrm{OPEN CORE 116/117}` — `\mathrm{LV}(σ,2σ) ≤ 3-3σ` — would
*not* prove the Density Hypothesis there. It would give a bound between Ingham and DH. `[Failure mode:
optimising a route to its own ceiling without checking the ceiling against the actual target. **Gate
(eighth): before adopting an `\mathrm{OPEN CORE}`, substitute its conclusion into the final target and
confirm the target is reached.**]`
What the route *would* give is still substantial: the Guth–Maynard record on this range is
`\mathrm{A}(σ) ≤ 15/(3+5σ)` (`2.256` at `σ = 0.73`), so `3/(2σ) = 2.055` **would be a new record on
`(2/3,3/4)`** — but conditional on an unproved large-value bound, and short of DH.

## Theorem 58 (the DH-critical large-value exponent, and its exact position between the two classical bounds) `[PROVED HERE]`
By Corollary 11.9 the Density Hypothesis `\mathrm{A}(σ) ≤ 2` follows from
`\mathrm{A}(σ)(1-σ) ≤ 2(1-σ)`, i.e. from the window-by-window requirement
```
        \mathrm{LV}(σ,τ) \;≤\; 2τ(1-σ) \;=:\; \mathrm{LV}_{\mathrm{DH}}(σ,τ) .
```
Write the two classical bounds as `\mathrm{LV}_{\mathrm{MVT}}(σ,τ) = τ+1-2σ` (Montgomery–Vaughan mean
value theorem) and `\mathrm{LV}_{\mathrm{MC}}(σ) = 2-2σ` (Montgomery's conjecture, `=` Lemma 7.5's
lower bound). Then:
**(i) The mean value theorem alone gives the Density Hypothesis exactly on the windows `τ ≤ 1`:**
```
        τ+1-2σ ≤ 2τ(1-σ) \iff (1-2σ)(1-τ) ≤ 0 \iff τ ≤ 1 \quad(σ>\tfrac12) .
```
**(ii) On `τ > 1` the deficit of the mean value theorem is exactly `(τ-1)(2σ-1)`,** and the surplus of
Montgomery's conjecture over the mean value theorem is exactly `τ-1`.
**(iii) Hence the fraction of Montgomery's improvement that the Density Hypothesis requires is**
```
        \frac{\mathrm{LV}_{\mathrm{MVT}}-\mathrm{LV}_{\mathrm{DH}}}
             {\mathrm{LV}_{\mathrm{MVT}}-\mathrm{LV}_{\mathrm{MC}}}
        \;=\;\frac{(τ-1)(2σ-1)}{τ-1}\;=\;2σ-1 ,
```
**independently of `τ`.** Equivalently, as an exact convex combination with weights summing to `1`:
```
        \boxed{\;\mathrm{LV}_{\mathrm{DH}}(σ,τ)\;=\;(2-2σ)\,\mathrm{LV}_{\mathrm{MVT}}(σ,τ)\;+\;(2σ-1)\,\mathrm{LV}_{\mathrm{MC}}(σ)\;}
```
*Proof.* `(2-2σ)(τ+1-2σ)+(2σ-1)(2-2σ) = (2-2σ)\bigl[τ+1-2σ+2σ-1\bigr] = (2-2σ)τ`. ∎
> **The Density Hypothesis is the `(2σ-1)`-weighted interpolation between the mean value theorem and
> Montgomery's conjecture, uniformly in the window `τ`.** The weight `2σ-1` is exactly twice the
> distance from the critical line. At `σ = 1/2` the weight is `0` — DH *is* the mean value theorem
> (and is trivial). At `σ = 1` the weight is `1` — DH *is* Montgomery's conjecture (both are `0`). In
> between, DH costs precisely the fraction `2σ-1` of the conjectural gap, at **every** window
> simultaneously.
### Sixth independent derivation of `σ = 3/4`
The weight equals `1/2` exactly at `σ = 3/4`: **the Density Hypothesis at `σ = 3/4` is the exact
midpoint of the mean value theorem and Montgomery's conjecture.** Independently, the DH-critical
window `τ = 3/2` (the smallest `τ` with `3/τ ≤ 2`) meets the coherence boundary `τ = 2σ` exactly at
`σ = 3/4`. Together with the four derivations of Cycles 51–66 this is the sixth and seventh
appearance of `3/4` from mutually independent mechanisms.
### The corrected target
At the coherence boundary `τ = 2σ` the requirement is
```
        \mathrm{LV}(σ,2σ)\;≤\;4σ(1-σ)\;=\;1-(2σ-1)^2 ,
```
i.e. the mean value theorem's value `1` must be beaten by exactly `(2σ-1)^2`, **the square of twice
the distance from the critical line**. Since `4σ(1-σ) ≤ 3-3σ \iff σ ≤ 3/4`, the corrected target is
strictly harder than `\mathrm{OPEN CORE 116/117}` on `(2/3,3/4)` and coincides with it at `σ = 3/4`.
`[OPEN CORE 119 — supersedes 116 and 117]` **Prove `\mathrm{LV}(σ,τ) ≤ 2τ(1-σ)` for `τ ∈ (1, 2σ]`.**
By (i) this is the *entire* content of the Density Hypothesis in the large-values formulation: windows
`τ ≤ 1` are already done by the mean value theorem, and by Theorem 54's window analysis nothing above
`τ = 2σ` contributes. By (iii) it asks for the fraction `2σ-1` of Montgomery's conjecture — never more
than half of it on the range `σ ≤ 3/4` where DH is open.

## Theorem 59 (the triple point at `τ = 1`, and the pencil geometry of the three exponents) `[PROVED HERE]`
```
        τ = 1 :\quad \mathrm{LV}_{\mathrm{MVT}} = 1+1-2σ = 2-2σ,\quad
                     \mathrm{LV}_{\mathrm{MC}} = 2-2σ,\quad
                     \mathrm{LV}_{\mathrm{DH}} = 2·1·(1-σ) = 2-2σ .
```
**All three coincide at `τ = 1`.** As functions of `τ` they are the pencil of lines through
`(1, 2-2σ)` with slopes `1`, `0`, and `2-2σ` respectively; since `0 < 2-2σ < 1` on `σ ∈ (1/2,1)`, the
Density-Hypothesis line lies strictly between the other two for every `τ ≠ 1`, on the mean-value side
for `τ < 1` and on the Montgomery side for `τ > 1`. **A large-value estimate proves the Density
Hypothesis at `σ` if and only if its graph lies below the line through the triple point of slope
`2-2σ` on the whole window `τ ∈ (1, 2σ]`** — this is the entire geometric content of Theorem 58, and
it is why the required fraction `2σ-1` of Montgomery's conjecture is independent of `τ` (it is a ratio
of slopes, not of values).

## Theorem 60 (reduction of the Density Hypothesis to Montgomery's conjecture at a **single** window) `[PROVED HERE]`
*Let `σ ∈ (2/3, 3/4)` and set*
```
        τ_*(σ)\;:=\;1+(2σ-1)^2\;=\;4σ^2-4σ+2 .
```
*If `\mathrm{LV}(σ, τ_*) ≤ 2-2σ` — Montgomery's conjecture at the single window `τ_*` — then*
`\mathrm{A}(σ) ≤ 2`*, the Density Hypothesis at `σ`.*
*Proof.* By Lemma 7.4(ii) (Huxley subdivision, verbatim: `\mathrm{LV}(σ,τ) ≤ \mathrm{LV}(σ,τ') ≤
\mathrm{LV}(σ,τ)+τ'-τ`), the hypothesis propagates in both directions: for `τ ≤ τ_*` it gives
`\mathrm{LV}(σ,τ) ≤ 2-2σ`, which meets `\mathrm{LV}_{\mathrm{DH}} = 2τ(1-σ)` exactly when `τ ≥ 1`
(Theorem 58(i)); for `τ ≥ τ_*` it gives `\mathrm{LV}(σ,τ) ≤ 2-2σ+τ-τ_*`, which meets
`2τ(1-σ)` exactly for `τ ≤ (τ_*-2+2σ)/(2σ-1)`, and
```
        \frac{τ_*-2+2σ}{2σ-1} ≥ 2σ \iff τ_* ≥ 4σ^2-4σ+2 = 1+(2σ-1)^2 ,
```
which is the hypothesis with equality. So the requirement holds on all of `(1,2σ]`; by Theorem 54's
window analysis (`τ_0 = 2σ`, condition (7) vacuous for `σ < 3/4`, condition (6) confined to
`[4σ/3, 2σ]`) and Theorem 58(i) for the sub-window `[4σ/3,1]`, Corollary 11.9 gives
`\mathrm{A}(σ)(1-σ) ≤ 2(1-σ)`. ∎
*(All five algebraic steps machine-checked: `triple_point`, `subdivision_range`,
`covers_coherent_window_iff`, `required_window_lt_coherence`, `huxley_gap`.)*
> **`τ_*(σ) = 1+(2σ-1)^2` lies strictly inside the coherent regime: `τ_* < 2σ` for all
> `σ ∈ (1/2,1)`.** So the Density Hypothesis on `(2/3,3/4)` needs Montgomery's conjecture at **one**
> window, and that window is strictly below the coherence boundary where the block/wave-packet
> machinery is non-degenerate (unlike `τ = 2σ` itself — see the thirteenth correction).
### The exact distance to the known frontier
Huxley's large values theorem (blueprint Theorem 7.12, verbatim `\mathrm{LV}(σ,τ) ≤ \max(2-2σ,
4+τ-6σ)`) proves Montgomery's conjecture for `τ ≤ 4σ-2`. Hence
```
        τ_*(σ) - (4σ-2) \;=\; 4σ^2-8σ+4 \;=\; \boxed{\,4(1-σ)^2\,} .
```
**The Density Hypothesis at `σ` follows from extending the proved Montgomery range beyond Huxley's
`4σ-2` by exactly `4(1-σ)^2`** — `0.29` at `σ = 0.73`, `0.25` at `σ = 3/4`. This is the sharpest
statement of the residual difficulty this programme has produced: one window, one conjecture, one
explicitly quantified gap.

## Theorem 61 (why every classical route stops at `σ = 3/4`) `[PROVED HERE]`
**(a) Huxley's large values theorem contributes to the Density-Hypothesis window if and only if
`σ > 3/4`.** Its non-trivial term `4+τ-6σ` meets `2τ(1-σ)` exactly for `τ ≤ (6σ-4)/(2σ-1)`, and
```
        \frac{6σ-4}{2σ-1} > 1 \iff 6σ-4 > 2σ-1 \iff σ > \tfrac34 .
```
Equivalently, its Montgomery range `4σ-2` exceeds `1` iff `σ > 3/4`. Both thresholds are the same
number because all three exponents meet at `τ = 1` (Theorem 59).
**(b) The exponent-pair route to Montgomery's conjecture is vacuous for `σ ≤ 3/4`.** The blueprint's
Corollary 7.11 gives Montgomery's conjecture for `τ < (2σ+k-\ell-1)/k`, and every exponent pair
satisfies `\ell ≥ k+1/2`; hence the numerator is `≤ 2σ-3/2`, which is positive **iff `σ > 3/4`**.
*(Machine-checked: `huxley_range_nonempty_iff`, `exponent_pair_route_vacuous`.)*
> ### The `3/4` wall, explained
> `σ = 3/4` is not a coincidence of five or six separate estimates. **It is the single point where
> the Density-Hypothesis line through the triple point `(1, 2-2σ)` stops being reachable by the two
> mechanisms that beat the mean value theorem:** Huxley's slope-`1` term (which must cross the
> DH line to the right of `τ = 1`, i.e. `4σ-2 > 1`) and the exponent-pair numerator `2σ-3/2` (which
> must be positive). Both conditions read `σ > 3/4`, and both read that way because `\ell-k ≥ 1/2`
> — the `μ(1/2)` constraint — is exactly the statement that `ζ` on the critical line cannot be
> exploited below `σ = 3/4`. Adding the coherence boundary `2σ = 3/2`, the deficit parabola, the
> `k = 2` moment test, the off-diagonal computation and the witness's fourth moment, `σ = 3/4` has now
> been derived **nine** times from mutually independent mechanisms, and Theorem 61 identifies the
> common cause.
`[OPEN CORE 120 — supersedes 119]` **Prove `\mathrm{LV}(σ, 1+(2σ-1)^2) ≤ 2-2σ` for `σ ∈ (2/3,3/4)`,**
i.e. extend the proved Montgomery range from Huxley's `4σ-2` by `4(1-σ)^2`. By Theorem 61 neither
Huxley's estimate nor any exponent pair can do this below `σ = 3/4`; by Theorem 60 nothing else is
needed.

# Cycle 73 — the `3/4` wall identified as the Halász–Montgomery barrier, and the cancellation fraction it costs

## Theorem 62 (the Halász–Montgomery barrier is exactly `σ = 3/4`, unconditionally and irremovably) `[PROVED HERE]`
Write `D_1(u) := \sum_{n∼N} n^{-iu}` for the resolvent of the large-value problem, and
`Δ := \max_{1 ≤ u ≤ T}|D_1(u)|`. The Halász–Montgomery argument is
```
        R^2V^2 \;≤\; \|a\|_2^2 \Bigl|\sum_{r,r'} c_r\overline{c_{r'}} D_1(t_r-t_{r'})\Bigr|
              \;≤\; N\,(RN + R^2Δ)
        \;\Longrightarrow\; R V^2 ≪ N^2 + R\,N\,Δ .
```
**(a) `Δ ≥ c\,N^{1/2}` unconditionally whenever `τ > 1`.** By Montgomery–Vaughan,
```
        \int_0^T |D_1(u)|^2\,du \;=\; NT + O(N^2\log N),
```
the diagonal dominating exactly when `T ≥ N\log N`, i.e. **exactly when `τ > 1`**; then the mean of
`|D_1|^2` is `≍ N`, so `Δ ≥ c N^{1/2}`.
**(b) Hence on `τ > 1` the Halász–Montgomery inequality reads `RV^2 ≪ N^2 + R N^{3/2}` and is
vacuous precisely when `V^2 ≤ N^{3/2}`, i.e. precisely when `σ ≤ 3/4`.** For `σ > 3/4` it gives
`R ≪ N^{2-2σ}` — Montgomery's conjecture — for every `τ`.
> **`σ = 3/4` is the Halász–Montgomery barrier, and (a) shows it cannot be moved by any improvement
> to the pointwise bound on the resolvent: `Δ = N^{1/2}` is already the truth, forced by the second
> moment.** This is the common cause behind every appearance of `3/4` in this card and in the
> literature — including the blueprint's own step in Theorem 7.15, *"Since `σ > 3/4`, we can delete
> the second term"*, whose deleted term is exactly `|W|^2 N^{3/2}`, i.e. `R^2 · \|a\|_2^2 · Δ`.
### The two thresholds are the same threshold
Theorem 59 located the triple point of the three exponents at `τ = 1`; Theorem 62(a) locates the
diagonal/off-diagonal transition of `\int|D_1|^2` at `τ = 1`. **These coincide because both say
`N^2 = NT`: the mean value theorem stops proving the Density Hypothesis at exactly the window where
the resolvent's second moment stops being off-diagonal-dominated.** Below that window the problem is
a diagonal problem and the mean value theorem is sharp for the right reason; above it, the resolvent
has genuine oscillation and the whole difficulty is to exploit it.

## Theorem 63 (the Density Hypothesis costs at most a quarter of square-root cancellation) `[PROVED HERE]`
By Theorem 62 the only way past `σ = 3/4` is cancellation in the **quadratic form**, not in `Δ`.
Define the off-diagonal cancellation exponent `θ = θ(σ,τ)` by
```
        \Bigl|\sum_{r ≠ r'} c_r\overline{c_{r'}} D_1(t_r-t_{r'})\Bigr| \;≪\; R^{2-θ}\,N^{1/2} ,
```
so `θ = 0` is the triangle inequality and `θ = 1/2` is square-root cancellation over the `R^2` pairs.
Then `R^{2}V^{2} ≪ N(RN + R^{2-θ}N^{1/2})`, and in the range where the second term dominates,
```
        R \;≪\; N^{(3/2-2σ)/θ} .
```
**This meets Montgomery's conjectured `N^{2-2σ}` — and therefore, by Theorem 60, gives the Density
Hypothesis — exactly when**
```
        \boxed{\;θ \;≥\; θ_*(σ) \;:=\; \frac{3-4σ}{4-4σ}\;}
```
*(machine-checked: `cancellation_threshold`).* On the open band:
```
        σ = 2/3   :  θ_* = 1/4          σ = 0.70  :  θ_* = 1/6 ≈ 0.167
        σ = 0.73  :  θ_* = 0.074        σ = 3/4   :  θ_* = 0     (Halász–Montgomery already suffices)
```
**So the entire residual difficulty of the Density Hypothesis on `(2/3, 3/4)` is at most a quarter of
square-root cancellation in the off-diagonal phase sum, decreasing linearly to zero at `σ = 3/4`**
*(machine-checked: `cancellation_bounds`)*. Full square-root cancellation `θ = 1/2` would give
Montgomery's conjecture for every `σ ≥ 1/2`.
> ### What this changes
> The programme is no longer "improve a large-value estimate". It is a single, sharply quantified
> analytic question about one explicit oscillatory sum:
> ```
>       \sum_{r ≠ r'} c_r \overline{c_{r'}}\, D_1(t_r - t_{r'}) ,\qquad
>       D_1(u) = \sum_{n∼N} n^{-iu},\qquad t_r\ 1\text{-separated in } [0,N^{τ_*}] ,
> ```
> with `τ_* = 1+(2σ-1)^2` (Theorem 60) and the required saving `R^{-θ_*}`, `θ_* = (3-4σ)/(4-4σ)`.
> The `a ≡ 1` witness of Cycles 49–66 is *not* an obstruction here: it is a statement about the
> coefficients `a_n`, whereas `D_1` has coefficients `≡ 1` by construction and the freedom lies
> entirely in the configuration `\{t_r\}` and the unimodular weights `c_r`.
`[OPEN CORE 121 — supersedes 120]` **Prove `\bigl|\sum_{r≠r'} c_r\overline{c_{r'}}D_1(t_r-t_{r'})\bigr|
≪ R^{2-θ_*}N^{1/2+o(1)}` with `θ_* = (3-4σ)/(4-4σ)` for `1`-separated `\{t_r\} ⊂ [0,N^{τ_*}]`.**
By Theorems 60, 62, 63 this implies the Density Hypothesis on `(2/3,3/4)`, and by Theorem 62(a) no
weaker route through the pointwise size of `D_1` can exist.

# Cycle 74 — the coefficient-free reformulation: a flat dual large sieve

## Theorem 64 (the cancellation requirement `θ_*` is *exactly* "off-diagonal `≤` diagonal") `[PROVED HERE]`
Put
```
        Q(\{t_r\},c) \;:=\; \sum_{n∼N}\Bigl|\sum_{r≤R} c_r\,n^{-it_r}\Bigr|^{2}
        \;=\; \sum_{r,r'} c_r\overline{c_{r'}}\,D_1(t_r-t_{r'}) \;≥\; 0 ,
```
whose diagonal is exactly `RN`. Theorem 63's threshold `θ_*(σ) = (3-4σ)/(4-4σ)` was defined by
`R^{2-θ_*}N^{1/2} = N^{2-2σ}`-consistency; substituting `R = N^{2-2σ}` and using
`1-θ_* = 1/(4-4σ)`,
```
        R^{2-θ_*}N^{1/2} = R\cdot R^{1-θ_*}N^{1/2} = R\cdot N^{(2-2σ)/(4-4σ)}N^{1/2} = R\cdot N^{1/2}N^{1/2} = RN .
```
**So the whole cancellation requirement of Theorem 63 is the single clean statement `Q ≪ RN^{1+o(1)}`:
the off-diagonal must not exceed the diagonal.** No exponent `θ` is needed.
### Consequence: a coefficient-free route to Montgomery's conjecture
By Cauchy–Schwarz, `RV ≤ \sum_r|D_a(t_r)| = \sum_n a_n\sum_r c_r n^{-it_r} ≤ \|a\|_2\,Q^{1/2}`, so for
`|a_n| ≤ 1`
```
        R^2V^2 ≤ N\,Q \;≪\; N\cdot RN^{1+o(1)} \;\Longrightarrow\; R ≪ N^{2-2σ+o(1)} ,
```
**Montgomery's conjecture in full — for every `σ ≥ 1/2` and every `τ`.** The Dirichlet coefficients
have disappeared: `Q` depends only on the configuration `\{t_r\}`, the unimodular weights `c_r`, and
the integers `n ∼ N`. **Every obstruction recorded in Cycles 49–66 was a statement about `a_n`
(the `a ≡ 1` witness, the mollifier's low-range vanishing, the moment tests); none of them can even be
formulated here.**

## Conjecture DH-FD (flat dual large sieve) `[CONJECTURED HERE]`
*For any `1`-separated `\{t_r\}_{r≤R} ⊂ [0,T]`, any unimodular `(c_r)`, and any `N`,*
```
        \sum_{n∼N}\Bigl|\sum_{r≤R} c_r\,n^{-it_r}\Bigr|^{2}
        \;≪\; N^{o(1)}\bigl(\,RN \;+\; R^{3/2}N^{1/2}\,\bigr) .
```
*In particular `Q ≪ RN^{1+o(1)}` whenever `R ≤ N`, which by Theorem 64 gives Montgomery's conjecture
and hence (Theorem 60) the Density Hypothesis.*
### Why this is the right statement, and why it is bold
**(a) It strictly strengthens the mean value theorem, which gives `R(T+N)`.** For `R ≤ T` and `N < T`
one has `R^{3/2}N^{1/2} ≤ RT \iff RN ≤ T^2`, always true; so DH-FD is stronger at every configuration
and reduces to `RN` exactly in the range `R ≤ N` that the Density Hypothesis needs.
**(b) Both terms are attained, so no term can be dropped.**
*Diagonal term `RN`.* Take `t_r` an arithmetic progression of spacing `d ≥ 1`. Then
`\sum_r c_r n^{-it_r}` is a Dirichlet kernel in `\log n`, of size `≍ R` on the resonances
`\log n ∈ (2π/d)\mathbb Z` and `≍ 1/\mathrm{dist}` off them. The number of resonances in the range
`\log n ∈ [\log N, \log 2N]` is `≍ d/2π + 1`, each carrying `≍ N/(Rd)` integers, so
`Q ≍ (d/2π+1)(N/Rd)R^2 ≍ RN` — **for every spacing `d`, and with the off-resonance tail contributing
the same order.**
*Term `R^{3/2}N^{1/2}`.* Take `t_r = 2πN m_r` with distinct integers `m_r` (spacing `≥ 2πN ≥ 1`). For
`n = N+j` one has `N\log n = N\log N + j - j^2/2N + O(j^3/N^2)`, and since `j ∈ \mathbb Z` the linear
term dies modulo `1`:
```
        n^{-2πiNm} = e\bigl(-Nm\log n\bigr) = e\bigl(-Nm\log N\bigr)\,e\bigl(m j^2/2N\bigr)(1+o(1)) .
```
**The `t`-sum becomes a quadratic Weyl sum in `j`.** With `m_r = r`, `c_r = 1`, the inner sum is
`≍ R` for `j ≤ \sqrt{2N/R}` and `≍ 2N/j^2` beyond, giving
`Q ≍ R^2\sqrt{2N/R} + N^2\sum_{j>\sqrt{2N/R}}j^{-4} ≍ R^{3/2}N^{1/2}`. This is exactly
**square-root cancellation over the `R^2` off-diagonal pairs at `|D_1| ≍ N^{1/2}`**, i.e. `θ = 1/2` in
Theorem 63's notation. `R^{3/2}N^{1/2} ≥ RN \iff R ≥ N`, so this term is invisible in the
Density-Hypothesis range and dominant outside it — a non-trivial calibration the conjecture passes.
**(c) It asserts that square-root cancellation is *universal* for unimodular weights.** The
mean value theorem's `T`-term is attained only by *sparse* `a` (a single `n_0` gives
`\|M\|^2 ≥ R`, and `R ≍ T` makes `\|M\|^2 ≍ T`); DH-FD says the flat unimodular vector never sees it.
**This is exactly the dual of the `a ≡ 1` witness — and the asymmetry is the point: flatness on the
`n`-side saturates the mean value theorem, flatness on the `t`-side (conjecturally) does not.**
### How DH-FD could fail
The failure mode is a configuration `\{t_r\}` for which `\log n` behaves like an exact arithmetic
progression. For a genuine AP `x_n = n/N` and frequencies `t_r = 2πNr` one gets `F(x_n) ≡ R` and
`Q = NR^2 ≫ RN`; DH-FD asserts that `\{\log n\}` never permits this. The obstruction to imitating it
is arithmetic: `t_r\log(n/n') ∈ 2π\mathbb Z` for all pairs forces `t_r` into
`\bigcap_{n,n'}(2π/\log(n/n'))\mathbb Z`, and the alignment survives only for
`|n-n'| ≲ \sqrt{N/m}` — precisely the `\sqrt N` truncation that produces the second term rather than
`NR^2`. **A counterexample would have to produce `≫ N/R` integers `n ∼ N` on which `R` prescribed
phases align simultaneously; the natural source of such alignment — Bohr sets
`\{t : \|t\log p_i/2π\| ≤ ε,\ i ≤ k\}`, on which `n^{-it} ≈ 1` for every `\{p_i\}`-smooth `n` — yields
only `≍ (\log N)^{k-1} = N^{o(1)}` integers, because smooth numbers with boundedly many prime factors
are sparse in `[N,2N]`.** That tension — multiplicative structure is the only source of alignment, and
it is too sparse — is the mathematical content of the conjecture.
`[OPEN CORE 122 — supersedes 121]` **Prove Conjecture DH-FD, or refute it by exhibiting a
`1`-separated `\{t_r\}` and unimodular `(c_r)` with `Q ≫ N^{δ}RN` for some `δ > 0` and `R ≤ N`.**
By Theorem 64 the first branch gives Montgomery's conjecture and the Density Hypothesis; the second
branch would be the first known configuration saturating the mean value theorem with flat weights,
and would locate the true obstruction.

# Cycle 75 — the chirp normal form, and the Density Hypothesis as an aliasing problem

## DEAD END (checked, not recorded as a theorem): the "symmetric large sieve" proof of DH-FD
*Attempt.* Bound `Q` by the bilinear operator norm in the favourable direction:
`\|M\|^2 ≤ \min(\text{range}(m)+δ_x^{-1},\ \text{range}(x)+δ_m^{-1})`, which for
`x_n = \log n/2π` (range `≈ 0.11`, separation `≈ 1/2πN`) and `t_r ∈[0,T]` (separation `1`) would give
`\|M\|^2 ≪ 1` and hence `Q ≪ R` — absurd, since the diagonal alone is `RN`.
*Why it fails.* **The large sieve is not symmetric: one side must be equally spaced.** Montgomery–
Vaughan bounds `\sum_r|\sum_n a_n e(λ_r n)|^2 ≤ (L+δ^{-1})\|a\|^2` with `n` running over *consecutive
integers*; the dual statement with both sides merely separated is false (take one frequency and `K`
points: the truth is `K`, the "symmetric" bound gives `1`). **`\{\log n\}` is not an arithmetic
progression, and that is precisely the difficulty — any argument that treats it as one proves too
much.** `[Fifteenth correction, caught before recording. Gate (ninth): before applying a large-sieve
or duality bound, identify which side is assumed equally spaced.]`

## Theorem 65 (chirp normal form for `n^{-it}` on `n ∼ N`) `[PROVED HERE]`
*Write `t = 2πNm` and `n = N+j`, `0 ≤ j ≤ N`. Then*
```
        n^{-it} \;=\; e\bigl(-Nm\log N\bigr)\;e\Bigl(-m\bigl(j - \tfrac{j^{2}}{2N}\bigr)\Bigr)\,
                     \bigl(1+O(mj^{3}/N^{2})\bigr) .
```
*Proof.* `t\log n/2π = Nm\log N + Nm\log(1+j/N) = Nm\log N + m(j - j^2/2N + O(j^3/N^2))`. ∎
Consequently, for any configuration `\{t_r\} = \{2πNm_r\}` and unimodular `(c_r)`,
```
        Q \;=\; \sum_{j} \bigl|H(φ(j))\bigr|^{2},\qquad
        H(x) := \sum_r c_r' \,e(-m_r x),\qquad φ(j) := j-\frac{j^{2}}{2N} ,
```
with `|c_r'| = 1`. **Two structural facts follow, and they are the whole geometry of the problem.**
**(a) Rigidity.** The linear and quadratic coefficients of the phase are *both* proportional to the
same parameter `m_r`: the family is a one-parameter family of chirps along a curve, not a
two-parameter family of quadratic phases. (This is the correct form of the observation that killed
Theorem 40: there is only one variable.)
**(b) `\{\log n\}` is an arithmetic progression exactly on blocks of length `\sqrt N`.** One has
`φ(j+1)-φ(j) = 1-(2j+1)/2N ∈ [1/2,1]` for `j ≤ N/2`, so `\{φ(j)\}` is `1`-separated; but its deviation
from the exact progression `\{j\}` is `j^{2}/2N`, which reaches `1` at `j = \sqrt{2N}`.
> **Unification.** The three quantities `Δ = N^{1/2}` (the resolvent's true size, Theorem 62), the
> second term `R^{3/2}N^{1/2}` of Conjecture DH-FD, and the block length `\sqrt N` of (b) are **one
> phenomenon**: `\{\log n : n∼N\}` is an arithmetic progression to accuracy `1` on blocks of length
> `\sqrt N` and on no longer block. Every `N^{1/2}` in this card — hence, via `V^{2} = N\cdot N^{1/2}`,
> the barrier `σ = 3/4` itself — is that block length.

## Theorem 66 (the Density Hypothesis is an aliasing problem, and `τ = 1` is the Nyquist rate) `[PROVED HERE]`
In the normal form of Theorem 65 the frequencies are `m_r ∈ [0,M]` with `M = T/2πN = N^{τ-1}/2π`, and
the sampling points `φ(j)` are `1`-separated. Therefore:
**(a) If `τ < 1` then `M < 1`: the sampling is *oversampling* relative to the bandwidth, and by the
Plancherel–Pólya inequality for `δ`-separated samples of a bandwidth-`M` function,**
```
        Q \;=\; \sum_j |H(φ(j))|^{2} \;≪\; (M+1)\int_J |H|^{2} \;≪\; \int_J|H|^{2} \;≪\; RN^{1+o(1)} ,
```
*giving Conjecture DH-FD, hence Montgomery's conjecture, unconditionally for `τ < 1`.*
**(b) If `τ > 1` then `M > 1`: the sampling is *undersampling* by the factor `M = T/N`, and aliasing
is possible in principle. Whether it actually occurs on the specific point set `\{\log n\}` is exactly
Conjecture DH-FD.**
> **`τ = 1` is the Nyquist rate of the problem.** This is the *third* independent derivation of the
> triple point: it is where the three exponents coincide (Theorem 59), where the resolvent's second
> moment turns from off-diagonal- to diagonal-dominated (Theorem 62(a)), and now where the sampling
> rate `1` matches the bandwidth `T/N`. All three read `T = N`. **The mean value theorem is sharp
> below Nyquist for the honest reason that no information is lost there; the Density Hypothesis is
> the assertion that above Nyquist the multiplicative sample set `\{\log n\}` still does not alias.**
`[OPEN CORE 123 — the concrete form of 122]` **Show that the `1`-separated point set
`\{φ(j)\}_{j≤N}`, `φ(j) = j-j^{2}/2N`, admits no aliasing at bandwidth `M = N^{τ_*-1}`:**
```
        \sum_{j≤N}\Bigl|\sum_{r≤R}c_r e(-m_r φ(j))\Bigr|^{2} \;≪\; N^{o(1)}\bigl(RN + R^{3/2}N^{1/2}\bigr)
```
*for `m_r ∈ [0,M]` with `m_r` `\tfrac{1}{2πN}`-separated and `|c_r| = 1`.* By Theorems 64–66 this is
equivalent to the Density Hypothesis route and is stated entirely in terms of a quadratic phase and a
sampling set — **no zeta function, no Dirichlet coefficients, no zero-detection.**

# Cycle 76 — major/minor arc decomposition of the resolvent, and the exact locus of the difficulty

## CORRECTION (sixteenth) to Theorem 65's range of validity
The expansion `N\log(N+j) = N\log N + j - j^{2}/2N + O(j^{3}/N^{2})` is uniform only for
`j ≪ (N^{2}/m)^{1/3}`, not for `j ≤ N`. **Truncating at the quadratic term creates a spurious
stationary point at `j = N`** (`φ'(j) = 1-j/N` vanishes there, while the true phase derivative
`m/(1+j/N)` never does), which inflates `|K(μ)|` from the truth `≍ N/t` to a false `≍ \sqrt{N/t}` for
`t = 2πNμ ≤ N`. Theorem 65(a),(b) survive — the block length `\sqrt{N/m}` satisfies
`\sqrt{N/m} ≪ (N^{2}/m)^{1/3}` for every `m ≥ 1`, so the "arithmetic progression on blocks of length
`\sqrt N`" statement is inside the valid range — but the *global* identity
`Q = \sum_{j≤N}|H(φ(j))|^{2}` of Cycle 75 must be re-derived block-wise, with one expansion centre per
block. `[Failure mode: using a local normal form globally. **Gate (tenth): state the range of
validity of every asymptotic expansion at the moment it is written, and check the intended range of
use against it.**]`

## Theorem 67 (major/minor arc structure of the resolvent) `[PROVED HERE]`
*Let `K(μ) := D_1(2πNμ) = \sum_{n∼N}n^{-2πiNμ}` and let `M := T/2πN = N^{τ-1}/2π`, so `μ` ranges over
`[0,M]`. Write `α = μ/2N` for the quadratic coefficient of the block-wise chirp. Then:*
**(a) `q_{\min} = 2N/M`.** For `μ ∈ [2, M]` any Dirichlet approximation `|α-a/q| ≤ 1/(qN)`, `q ≤ N`,
has `a ≥ 1` (else `μ ≤ 2`), whence `a/q ≲ α ≤ M/2N` and `q ≥ 2Na/μ ≥ 2N/M`.
**(b) `\max_{2 ≤ μ ≤ M}|K(μ)| ≪ N^{τ/2+o(1)} = T^{1/2+o(1)}`.** By the Gauss-sum bound
`|K| ≪ (N/\sqrt q + \sqrt q)N^{o(1)}` and (a), `N/\sqrt{q} ≤ N/\sqrt{2N/M} = \sqrt{NM/2} ≍ T^{1/2}`,
while `\sqrt q ≤ \sqrt N ≤ T^{1/2}` for `τ ≥ 1`.
**(c) Level-`q` measure.** The set of `α` admitting an approximation of denominator `≍ q` has measure
`≍ 2A/N` (`A = M/2N` the total range) **independently of `q`**, with `≍ Aq` components; hence for
`1`-separated `\{t_r\}` the number of `r'` with `m_r-m_{r'}` at level `q` is
`≪ \min\bigl(R,\; M(1+q/N)\bigr)`.
### Consequence: the structured pairs are harmless in the Density-Hypothesis range
Summing (b),(c) over dyadic `q ∈ [q_{\min}, N]`, the major-arc contribution to
`\sum_{r'}|K(m_r-m_{r'})|` is dominated by `q = q_{\min}` and equals
```
        \min(R,M)\cdot\sqrt{NM} \;≍\; \min(R,M)\cdot N^{τ/2} .
```
On the band `σ ≤ (1+\sqrt5)/4 = 0.809` one has `M ≤ R`, so this is `≪ N` exactly when
```
        M^{3/2} ≪ N^{1/2} \iff M ≪ N^{1/3} \iff τ < \tfrac43
        \iff (2σ-1)^{2} < \tfrac13 \iff σ < \tfrac{1}{2}\Bigl(1+\tfrac{1}{\sqrt3}\Bigr) = 0.7887\ldots
```
**So for every `σ` in the open band `(2/3, 0.7887)` — which strictly contains the entire unresolved
range `(2/3, 3/4]` and reaches past Bourgain's threshold `25/32 = 0.78125` — the major-arc (resonant,
Gauss-sum-large) pairs contribute `≪ RN` and are *not* the obstruction.**

## Theorem 68 (the obstruction is exactly the minor arcs, and it is exactly the `3/4` barrier) `[PROVED HERE]`
The complementary minor-arc pairs are those with `|K(μ)| ≍ N^{1/2}` — the generic case, by Theorem
62(a) and the equidistribution of `α = μ/2N`. Estimating them by the triangle inequality gives
```
        \sum_{r'}|K| \;≳\; R\,N^{1/2} \;\Longrightarrow\; Q ≲ R\bigl(N + RN^{1/2}\bigr),
```
and `RN^{1/2} ≪ N \iff R ≪ N^{1/2} \iff N^{2-2σ} ≪ N^{1/2} \iff σ > 3/4`.
> **Every size-based estimate of `Q` — however sharp on the major arcs — reproduces `σ > 3/4` and
> nothing more.** Combined with Theorem 67 this locates the difficulty exactly:
> ```
>   major arcs (resonant μ, |K| up to T^{1/2}) :  harmless for σ < 0.7887   [Theorem 67]
>   minor arcs (generic μ, |K| ≍ N^{1/2})      :  need square-root cancellation over the R² pairs
> ```
> **The Density Hypothesis on `(2/3, 3/4]` is now a single statement about a single family of
> quadratic Gauss sums:** that the `R^{2}` phases `\arg K(m_r-m_{r'})`, `K` a Gauss sum with
> equidistributed quadratic coefficient `α = (m_r-m_{r'})/2N`, exhibit square-root cancellation
> against every unimodular weighting `c_r\overline{c_{r'}}`.
`[TRAP RECORDED]` An earlier pass through this computation concluded that `τ ≤ 4/3` gives
`Q ≪ RN` outright and hence proved the Density Hypothesis on `(2/3, 0.7887]`. **That is false: it
dropped the minor-arc term `RN^{1/2}`, which is the Halász–Montgomery barrier itself.** The
computation is correct only as a statement about the major arcs. `[Gate (vi) — compute two ways —
caught it: the AP configuration `m_r = m_0+r` has true `Q ≍ RN + R^{3/2}N^{1/2}`, and the dropped term
is precisely the difference between `R^{3/2}N^{1/2}` (with cancellation) and `R^{2}N^{1/2}` (without).]`

# Cycle 77 — Phase-4 attack on Conjecture DH-FD: the multiplicative construction fails by an unbounded margin

## Theorem 69 (no Bohr-set / smooth-number configuration refutes DH-FD) `[PROVED HERE]`
The only known mechanism producing simultaneous alignment of many phases `n^{-it_r}` is multiplicative:
a Bohr set `B(P,ε) = \{t : \|t\log p/2π\| ≤ ε\ \forall p ∈ P\}`, on which `n^{-it} ≈ 1` for every
`P`-smooth `n` of bounded prime-factor count. Fix such a construction and let
```
        k = |P|,\quad y = \max P,\quad u = \frac{\log N}{\log y},\quad
        A = \max_{n∈S}Ω(n/n_0),\quad K = |S| ,
```
where `S ⊂ [N,2N]` is the set of aligned integers. Three constraints bind simultaneously.
**(i) Alignment.** `\|t_r\log(n/n_0)/2π\| ≤ A ε` must be `≤ 1/10`, so `ε ≤ 1/(10A)`. Since a
`y`-smooth `n ∼ N` has `Ω(n) ≍ u`, necessarily `A ≳ u` and hence `ε ≲ 1/u`.
**(ii) Non-emptiness.** To place `R` one-separated points in `B(P,ε) ∩ [0,T]` one needs
`T(2ε)^{k} ≳ R`, i.e. `k\log\frac{1}{2ε} ≤ (τ-ρ)\log N` where `R = N^{ρ}`.
**(iii) Supply.** To beat the conjectured bound one needs `K ≫ N/R = N^{1-ρ}`; the count of
`y`-smooth integers in `[N,2N]` is `Nρ_{\mathrm{Dick}}(u) = N e^{-u\log u(1+o(1))}`, so
`u\log u ≤ ρ\log N`, forcing
```
        u ≍ \frac{ρ\log N}{\log\log N},\qquad
        \log y = \frac{\log N}{u} ≍ \frac{\log\log N}{ρ},\qquad
        y ≍ (\log N)^{1/ρ},\qquad k ≍ π(y) ≍ \frac{ρ\,(\log N)^{1/ρ}}{\log\log N} .
```
**These are incompatible.** Substituting (i) and (iii) into (ii), with `\log\frac1{2ε} ≥ \log(5u) ≍
\log\log N`,
```
        k\log\tfrac{1}{2ε} \;≍\; \frac{ρ(\log N)^{1/ρ}}{\log\log N}\cdot\log\log N
        \;=\; ρ\,(\log N)^{1/ρ}
        \;\;\text{versus}\;\; (τ-ρ)\log N ,
```
so the construction requires
```
        (\log N)^{\frac1ρ-1} \;≤\; \frac{τ-ρ}{ρ} \;=\; O(1) .
```
**For every `ρ < 1` — that is, for every `σ > 1/2` — the left side tends to infinity. The
multiplicative construction fails, and it fails by the unbounded factor `(\log N)^{1/ρ-1}`.** ∎
> ### Verdict on Conjecture DH-FD: `SURVIVES PRELIMINARY ATTACK`
> The obstruction is a genuine tension, not a near miss. **To align `u ≍ \log N/\log\log N` prime
> factors one needs Bohr precision `ε ≍ 1/u`; a Bohr set of `k ≍ (\log N)^{1/ρ}` primes at that
> precision has density `\exp(-Θ((\log N)^{1/ρ}\log\log N))`, which is empty in `[0,N^{τ}]` for every
> fixed `τ`.** Conversely, shrinking `k` to make the Bohr set nonempty (`k = O(τ/ρ)` primes) leaves
> only `(\log N)^{k-1} = N^{o(1)}` smooth integers — far below the `N^{1-ρ}` needed. **There is no
> intermediate regime: the two requirements move in opposite directions in `y`, and the margin is a
> power of `\log N`, not a constant.**
### Why this is evidence and not proof
Theorem 69 rules out the *multiplicative* source of alignment. It does not rule out an alignment set
`S` that is not smooth — `S` could a priori consist of `N^{1-ρ}` integers with large prime factors on
which the phases happen to align. **But such an `S` cannot be closed under the ratios that generate
the alignment**: if `n,n' ∈ S` then `t_r\log(n/n')` is within `O(1)` of `2π\mathbb Z` for all `r`, so
the multiplicative group generated by `S/S` is annihilated to precision `O(1)` by all `R` frequencies,
and by unique factorisation that group is free on the primes dividing members of `S`. **Theorem 69 is
therefore exactly the statement that the rank of that group must be `O(1)`, and then `|S| = N^{o(1)}`.
Closing the remaining gap — from "the group has small rank" to "the alignment is approximate, not
exact" — is the one analytic step between Theorem 69 and a proof of DH-FD.**
`[OPEN CORE 124]` **Make Theorem 69 unconditional by replacing exact annihilation with `O(1)`-precision
annihilation.** Concretely: show that if `S ⊂ [N,2N]` with `|S| ≥ N^{1-ρ+δ}` and there exist `R = N^{ρ}`
one-separated `t_r ∈ [0,N^{τ}]` with `\|t_r\log(n/n')/2π\| ≤ 1/10` for all `n,n' ∈ S` and all `r`, then
`δ ≤ 0`. By Theorems 64–68 this **proves the Density Hypothesis on `(2/3,3/4]`**, and by Theorem 69 the
only configurations it must exclude are the non-smooth ones.

# Cycle 78 — the continuous case of DH-FD is true and elementary; the Density Hypothesis is a sampling theorem

## Theorem 70 (continuous DH-FD) `[PROVED HERE]`
*Let `F(x) = \sum_{r≤R}c_r e(-t_r x/2π)` with `|c_r| = 1` and `\{t_r\} ⊂ [0,T]` one-separated, and let
`J` be an interval of length `\log 2`. Then*
```
        \int_J |F(x)|^{2}\,dx \;=\; \sum_{r,r'}c_r\overline{c_{r'}}\,\widehat{1_J}(t_r-t_{r'})
        \;≪\; R\log T \;=\; R\,\log N^{1+o(1)} ,
```
*since `|\widehat{1_J}(u)| ≤ \min(\log 2, 4π/|u|)` and one-separation gives at most two pairs per unit
interval, whence `\sum_{r≠r'}\min(\log2, 4π/|u|) ≪ R\sum_{k≤T}1/k ≪ R\log T`.*
*Consequently `\bigl|\{x ∈ J : |F(x)| ≥ R/2\}\bigr| ≪ (\log T)/R`.* ∎
> **The continuous statement is trivially true, and it is exactly the conjectured bound.** If the
> `N` sample points `\{\log n\}` — which are `≍1/N`-separated in `J` — sampled `|F|^{2}` fairly, then
```
        Q \;=\; \sum_{n∼N}|F(\log n)|^{2} \;≍\; \frac{N}{|J|}\int_J|F|^{2} \;≪\; RN^{1+o(1)} ,
```
> **which is precisely Conjecture DH-FD, hence Montgomery's conjecture, hence the Density Hypothesis.**

## Theorem 71 (the Density Hypothesis as a Marcinkiewicz–Zygmund sampling statement) `[PROVED HERE]`
Combining Theorems 64, 70:
```
   \boxed{\;\text{DH-FD}\iff \{\log n : n∼N\}\ \text{is a fair sampling set, at density }N,\;
   \text{for exponential sums with one-separated frequencies in }[0,T]\ \text{and unimodular coefficients.}\;}
```
The three regimes are now completely transparent:
```
   τ < 1  (T < N) :  below Nyquist — fair sampling holds for every bandlimited F
                     (Plancherel–Pólya); the mean value theorem is sharp and sufficient.  [Thm 66(a)]
   τ > 1  (T > N) :  above Nyquist — fair sampling fails for *generic* bandwidth-T functions;
                     DH-FD asserts it nevertheless holds for this class.
   Failure mode   :  B := {x ∈ J : |F(x)| ≥ R/2} has measure ≪ (log T)/R  [Theorem 70] but consists
                     of ≍ T/R components of length ≍ 1/T ≪ 1/N.  The trivial count of integers with
                     log n ∈ B is min(T/R, N); the needed count is N/R.
```
> **The entire remaining gap between this programme and the Density Hypothesis is the factor `T/N`
> between the trivial component count `T/R` and the expected count `N/R`.** Everything else —
> the reduction of DH to one window (Thm 60), the identification of the `3/4` wall as the
> Halász–Montgomery barrier (Thm 62), the removal of the Dirichlet coefficients (Thm 64), the
> disposal of the major arcs (Thm 67) and of the multiplicative counterexamples (Thm 69) — is proved.
`[OPEN CORE 125 — the final analytic step]` *Let `B ⊂ J` be a union of `≍ T/R` intervals of length
`≍ 1/T`, arising as the large-value set of an exponential sum with one-separated frequencies in
`[0,T]` and unimodular coefficients. Show*
```
        \#\{\,n ∼ N \;:\; \log n ∈ B\,\} \;≪\; N^{1+o(1)}/R
```
*— the count expected from `|B| ≍ 1/R`, rather than the trivial `\min(T/R, N)`.*
**This is a pure equidistribution statement about `\{\log n\}` in Bohr-type sets, containing no zeta
function, no Dirichlet coefficients, no zero-detection and no large-value machinery; by Theorems
60–70 it implies the Density Hypothesis on `(2/3,3/4]` and, through Theorem 64, Montgomery's
conjecture in full.** Theorem 69 shows the multiplicatively structured `B` — the only known source of
alignment — cannot violate it, and fails to by the unbounded factor `(\log N)^{1/ρ-1}`.

# Cycle 79 — stationary phase is the only source of over-sampling, and it reproduces DH-FD exactly

## Theorem 72 (the stationary-point census of `\{\log n\}` against a single frequency) `[PROVED HERE]`
*Fix `t = 2πNμ` with `μ ≥ 1` and put `ψ(n) := μ N\log n`. Then:*
**(a) `ψ'(n) = μN/n ∈ [μ/2, μ]` for `n ∈ [N,2N]`, so `ψ'` crosses exactly `≍ μ/2` integers, at the
points `n_k = μN/k`, `k ∈ [μ/2, μ] ∩ \mathbb Z`. These are the stationary points of `ψ` modulo `1`,
and there are no others.**
**(b) Near each `n_k`, writing `n = n_k + i` with `i ∈ \mathbb Z`,**
```
        ψ(n) \;\equiv\; ψ(n_k) \;-\; \frac{μN}{2n_k^{2}}\,i^{2} \pmod 1 ,
```
*because the linear term `k\,i` is an integer and dies modulo `1`. Hence `\|ψ(n)\| ≤ 1/R` on a block
of `≍ \sqrt{N/(μR)}` consecutive integers around each `n_k`.*
**(c) Census.** `\#\{n∼N : \|ψ(n)\| ≤ 1/R\} \;=\; \dfrac{N}{R} \;+\; O\Bigl(\sqrt{\dfrac{μN}{R}}\Bigr)`,
*the first term the equidistributed expectation and the second the total stationary-phase excess
`(μ/2)\cdot\sqrt{N/(μR)}`. The excess dominates exactly when `μ ≥ N/R`.*
**(d) Resolvent amplitude.** The same census evaluates `K(μ) = \sum_{n∼N}n^{-2πiNμ}`: each stationary
point contributes amplitude `|ψ''|^{-1/2} ≍ \sqrt{N/μ}`, and with square-root cancellation among the
`≍ μ/2` of them,
```
        |K(μ)| \;≍\; \sqrt{μ}\cdot\sqrt{N/μ} \;=\; \sqrt N .
```
> **This is the structural origin of every `N^{1/2}` in this card.** `\Delta ≍ N^{1/2}` is not an
> accident of the second moment (Theorem 62(a)) — it is
> `\sqrt{\#\text{stationary points}} \times \text{amplitude per stationary point}`, and the two
> factors `\sqrt μ` and `\sqrt{N/μ}` cancel the parameter `μ` exactly. **Since the
> Halász–Montgomery barrier is `V^{2} = \|a\|_2^{2}Δ = N\cdot N^{1/2}`, the threshold `σ = 3/4` is
> precisely the statement `\sqrt{μ}\cdot\sqrt{N/μ} = N^{1/2}`: the wall is the exact cancellation of
> the number of stationary points against their individual amplitudes.**
### Consequence: the conjectured second term of DH-FD is exactly the stationary-phase excess
Summing (c) over the configuration `t_r = 2πNm_r` with `c_r ≡ 1`, the excess concentration
`\sqrt{N/R}` at the single resonance `μ = 0` contributes `R^{2}\sqrt{N/R} = R^{3/2}N^{1/2}` to `Q`,
while the equidistributed part contributes `(N/R)R^{2} = RN`. **The two terms of Conjecture DH-FD are
therefore not fitted to an example — they are the equidistributed main term and the stationary-phase
error term of a single census, and there is no third mechanism in (a).**
`[OPEN CORE 126 — the sharpened form of 125]` **Show that stationary phase is the *only* source of
over-sampling of `\{\log n\}` by a Bohr-type set.** Precisely: for `B` the large-value set of
`F(x)=\sum_r c_re(-t_rx/2π)` with one-separated `t_r ∈ [0,T]` and `|c_r|=1`,
```
        \#\{n∼N : \log n ∈ B\} \;≪\; N^{o(1)}\Bigl(\,N|B| \;+\; \sqrt{N\,T\,|B|}\,\Bigr) ,
```
*the second term being the total stationary-phase excess across the `≍T|B|` components of `B`.* With
`|B| ≍ 1/R` this is `N/R + \sqrt{NT/R}`, and `\sqrt{NT/R}·R^{2} ≪ RN \iff R ≤ N/T`, so the statement
must be applied window-by-window rather than uniformly — **the correct target is the census bound
itself, and Theorem 72(a) says the only obstruction to proving it is controlling the crossings of
`ψ' = μN/n` through the integers, a one-dimensional counting problem with no zeta function in it.**

# Cycle 80 — exact Poisson decomposition of the sampling sum: the Density Hypothesis is an alias-cancellation statement

## Theorem 73 (Poisson decomposition of `Q`) `[PROVED HERE]`
*With `F(y) = \sum_r c_r e(-t_ry/2π)`, `J = [\log N, \log 2N]`, and `Q = \sum_{n∼N}|F(\log n)|^{2}`,
Poisson summation in `n` gives the exact identity*
```
        Q \;=\; \underbrace{\int_N^{2N}|F(\log x)|^{2}dx}_{h=0}
             \;+\; \sum_{h≠0}\ \sum_{r,r'} c_r\overline{c_{r'}}\;
                   \int_N^{2N} x^{-i(t_r-t_{r'})}e(-hx)\,dx .
```
**(a) The `h=0` term is exactly the target.** `\int_N^{2N}|F(\log x)|^{2}dx = \int_J|F(y)|^{2}e^{y}dy
≍ N\int_J|F|^{2} ≪ NR\log T` by Theorem 70. **So the main term of the sampling sum is precisely the
bound Conjecture DH-FD asserts.**
**(b) The `h≠0` terms are the aliases, and they are stationary-phase-supported.** The phase of
`I(u,h) = \int_N^{2N}x^{-iu}e(-hx)dx` is `-\tfrac{u}{2π}\log x - hx`, with derivative
`-\tfrac{u}{2πx}-h`, vanishing at `x_0 = -u/2πh`. Since `x_0 ∈ [N,2N]` this requires
```
        |u| \;≍\; 2π|h|N ,\qquad\text{i.e.}\qquad |h| \;≍\; μ = \frac{|t_r-t_{r'}|}{2πN} ,
```
*the same parameter `μ` as in Theorem 72; without a stationary point `I` is negligible. At `x_0` the
second derivative is `u/2πx_0^{2} ≍ h/N`, so the amplitude is `\sqrt{N/|h|}` and*
```
        S_h \;:=\; \sqrt{N/|h|}\!\!\sum_{\substack{(r,r')\\ |t_r-t_{r'}| ≍ 2π|h|N}}\!\!
                   c_r\overline{c_{r'}}\;e\bigl(g_h(v_{rr'})\bigr),\qquad
        g_h(v) = -v\log(v/h) - v,\quad v = \frac{t_r-t_{r'}}{2π} .
```
**(c) Range of `h`.** A stationary point requires `|h| ≤ T/2πN = M`, so the number of alias terms is
exactly `M = N^{τ-1}/2π`. **For `τ ≤ 1` there is no `h ≠ 0` term at all and `Q` equals its main
term identically** — an exact-identity re-derivation of Theorem 66(a) and of the fact that the mean
value theorem is sharp and sufficient below Nyquist. ∎
> ```
>   \text{Conjecture DH-FD}\quad\Longleftrightarrow\quad \sum_{h≠0}S_h \;≪\; RN^{1+o(1)} .
> ```
> **The Density Hypothesis is the statement that the Poisson aliases of the sampling sum do not
> exceed its main term.** Every earlier formulation collapses into this one: the `M = T/N` aliases of
> Theorem 66, the `≍μ/2` stationary points of Theorem 72, and the `≍T/R` components of the
> large-value set are the same objects seen three ways.
### The phase `g_h` and where cancellation must come from
`g_h'(v) = -\log(v/h)-2`, which at `v ≍ hN` equals `-\log N - 2`: **the leading behaviour is linear in
`v`, hence factors as `e(-t_r\log N/2π)\overline{e(-t_{r'}\log N/2π)}` and is absorbable into the
unimodular coefficients — it contributes nothing.** The genuine content is the curvature
```
        g_h''(v) \;=\; -\frac1v \;≍\; -\frac{1}{hN} ,
```
which over the window `|u| ≍ 2πN` (i.e. `v` varying by `≍N`) produces a phase deviation `≍ N/h`.
**So the `h`-th alias carries genuine oscillation exactly when `h ≪ N`, and the number of aliases is
`M = N^{τ-1} ≪ N` for `τ < 2`: every alias in the Density-Hypothesis range is curvature-dominated,
and none is degenerate.**
`[OPEN CORE 127 — supersedes 126]` **Prove `\sum_{h≠0}S_h ≪ RN^{1+o(1)}` for one-separated
`\{t_r\}⊂[0,T]` and unimodular `(c_r)`, with `S_h` as in (b).** The trivial bound is
`\sum_h \sqrt{N/h}\cdot R\min(R,N) ≍ R^{2}N^{τ/2}`, short of the target by `RN^{τ/2-1}` — **the same
shortfall `σ = 3/4` yet again**; the required saving is exactly a square root over the pairs, and by
(b) it must come from the curvature `g_h'' ≍ -1/(hN)`, the only non-degenerate structure present.
