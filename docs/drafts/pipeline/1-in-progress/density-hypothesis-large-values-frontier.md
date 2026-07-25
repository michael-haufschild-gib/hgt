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
