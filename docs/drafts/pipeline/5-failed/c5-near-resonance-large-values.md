# The C5★ near-resonance lane — which sub-object the integer-gap bound controls

- **ID:** c5-near-resonance-large-values
- **Stage:** 1-in-progress
- **Type:** STRUCTURAL clarification / routing connector (NOT a new theorem — localizes existing
  support-extraction-log results to the kernel hand-off; feeds C5★; DeWitt's near-resonance lane)
- **Priority:** FOUNDATIONAL
- **Source:** the hand-off in `../2-fully-proven/c5-jensen-prime-kernel.md` §4 (Professor) and the shared
  target in `finite-free-convolution-flow.md` (Wheeler, chat id=61) · 00-status #104, #113, #120
- **One sentence.** The integer-gap / height bound `|Σ_p a_p log p| ≥ H(a)^{-1}` rigorously controls the
  **RH-blind variance** side of the prime deformation (small divisors / cohomological solvability), **not**
  the **RH-bearing single-orbit sup** — which is a large-values (resonance-method) problem; this pins exactly
  what the near-resonance lane can and cannot deliver.
- **NOT a new finding — a connector.** The core conclusions here are **already established** in
  `../../support-extraction-log.md` and the board; this card only *localizes* them to Professor's kernel
  hand-off. Graded **STRUCTURAL clarification (no new theorem)**, validated against the corpus 2026-06-19.

## §0 Prior work this rests on (validated against support-extraction-log.md)
- **Prime-side RH-blindness is a structural theorem** (log lines ~822–827, #89): "multiplicative-only tools
  (Euler product, prime sums, ζ-values) are structurally **blind** to both apex obstructions (wrong side of
  the seam); the live SEEDs are archimedean." My §3 "integer-gap variance is RH-blind" is an **instance**.
- **The two-heights diagnostic** (log ~1066–1071): the **Kronecker height** (geometric, B7) vanishes on the
  whole canonical locus ⟹ RH-blind, cannot separate zeros / bound an auxiliary below; the **Liouville /
  transcendence height** (secular periods, B2) is what is needed. My §4 = this, in the deformation language.
- **The "Kronecker→Liouville upgrade = one missing uniform bound"** (log ~1079–1085, SEED): closing the gap
  = a height that *separates* (uniform floor) = the uniform multiplicity/equidistribution estimate. My §5
  `S_d`-normalization question **is** this upgrade, localized to the finite-free carrier.
- **Kronecker–Weyl resonance of ℚ-independent frequencies** (log ~1372): the density mechanism of §2.
- **Board:** #120 (L²/coboundary RH-blind, `σ>¾`), #113 (reducibility ⟺ RH refuted; RH relocated to
  single-orbit positivity), #104 (det `H_d`).

**So the genuine increment of this card** is only: (i) mapping Professor's kernel `D_d(c_m;t)` onto the
known prime-side-blindness (the axis-mode sup is large-values, §2), and (ii) the precise statement that the
`S_d`-normalization question = the known Kronecker→Liouville uniform-bound wall, now localized to the
bounded-degree finite-free carrier (§5). No new mathematics; a routing correction for the hand-off.

---

## §1 The object (from the kernel hand-off)
Shared target (Wheeler/Professor): control the prime deformation `D_d(c_m;t) = Σ_p p^{−1/2} K_d(c_m;p;t)
e^{−it log p}` (single-prime/axis frequencies `{log p}`, amplitude `p^{−1/2}·poly_{≤d}(log p)`) against the
archimedean floor `min_m|C_d(c_m)| ≥ 1` / the Hermite gap `Δ_l ≍ d^{−1/6}`, **uniformly in d**.

## §2 The axis-mode sup is large-values, not near-resonance (rigorous)
The frequencies `{log p}` are ℚ-independent (unique factorization), so the Kronecker–Weyl flow
`t ↦ (t log p mod 2π)_p` is **dense in `𝕋^∞`**. Hence for any Bohr sum with these frequencies,
```
   sup_{t∈ℝ} |Σ_p a_p e^{−it log p}|  =  sup_{θ∈𝕋^∞} |Σ_p a_p e^{−i⟨a-basis,θ⟩}|
```
— the sup over **all** `t` equals the sup over the whole torus. For the regularized `log ζ(½+it)`-type sum
this is **unbounded** as the `t`-window grows (Bondarenko–Seip: `max_{[0,T]}|ζ(½+it)| ≥ exp(c√(log T·
loglog T))`). So `sup_t |D_d| < floor` over all `t` is **false for every d** (it fails at the rare
large-value `t`) — this is precisely Professor's **first-order breakdown**, not an RH violation (higher-order
terms hold the roots apart there). **The near-resonance does not "forbid smallness" of an axis-mode sum.**

## §3 The split: variance (RH-blind) vs single-orbit sup (RH-bearing)
The combination-mode object — products of `≤d` displacements, i.e. `det H_d` entries — has frequencies
`a·ℓ = Σ_p a_p log p`, `‖a‖₁ ≤ 2d`. Two different quantities:

- **Variance / L² / cohomological-solvability.** `E_t‖δH_d‖²= Σ_a |ĉ_a|²`, and the coboundary/transfer
  regularity is `Σ_a |ĉ_a|²/|a·ℓ|²`. Here the **height bound** `|a·ℓ| ≥ H(a)^{-1} ≥ P_S^{-2d}` (unique
  factorization, my proven lane) controls the **small divisors** and the solvability. **But this is exactly
  the object proven RH-BLIND** (#120: coboundary norm converges iff `σ>¾`, `𝕋^∞`-variance; #113:
  reducibility ⟺ RH refuted). So the integer-gap bound, applied here, lands on the RH-blind half.

- **Single-orbit sup / positivity.** RH was **relocated** (#104/#113) to the single-orbit positivity of
  `det H_d` (Wheeler's `λ_min(S_d) ≥ −1 ∀d,t`), i.e. to the **sup**, which by §2 is a **large-values**
  statement. The height/integer-gap bound does **not** bound a large-values sup (the sup is set by
  constructive phase-alignment, not by divisors being bounded below).

## §4 Consequence — the correct division of tools
> **The integer-gap / height bound controls the RH-blind variance (small divisors, cohomological
> solvability); the RH-bearing single-orbit sup is a large-values problem requiring resonance-method /
> GCD-sum technology (Soundararajan; Bondarenko–Seip), not an integer-gap bound.**

This is consistent with the field's own prior findings (#113/#120: the L²/reducibility handle is RH-blind;
RH lives in the single-orbit positivity). It says the near-resonance hand-off, taken as a bound on the sup,
cannot bite; what it *can* deliver rigorously is the variance/small-divisor control (the RH-blind backbone),
plus the **input data** (the height-separated frequencies) that any resonance-method sup bound must use.

## §5 The open question to Wheeler (the S_d normalization)
Does the archimedean normalization `S_d = A_d^{−1/2} δH_d A_d^{−1/2}` move the RH content into an object with
a **bounded** sup (so a height-controlled bound can bite), or does `S_d`'s sup remain a large-values problem?
- If `A_d^{−1/2}` damps the large-values (the archimedean Hermite measure suppresses the rare-`t` spikes at
  the Hermite nodes `c_m`), the relevant sup may be **bounded**, and then the bounded-degree height structure
  controls it — the integer-gap lane bites after all.
- If not, the RH-bearing sup needs resonance-method technology and the integer-gap lane only supplies the
  frequency-separation input.
This is the decision point for whether C5★'s crux is an integer-gap theorem (my lane closes it) or a
large-values theorem (new technology). **Pinning it is the next step.**

### §5 RESOLVED (2026-06-19) — the normalization does NOT make the integer-gap bite (answer: large-values)
Wheeler's gap-difference carrier `(GD)` (chat id=89) is exactly the normalization test, and it resolves
**negatively**. The collision quantity is `Δε_l = ε_l − ε_{l+1}`, per-prime amplitude
`p^{−1/2}|K_d(r_l;p) − K_d(r_{l+1};p)| ≈ p^{−1/2}·Δ_l·|∂_r K_d(p)|`. So the normalized quantity `(GD)` needs
`<1`, namely `Δε_l/Δ_l`, has amplitude `p^{−1/2}|∂_r K_d(p)|` — **the gap `Δ_l` cancels, restoring the
`p^{−1/2}` scale.** So `(GD)` reduces to an **upper** bound `sup_t|Σ_p p^{−1/2}(∂_r K_d) e^{−it log p}| < 1`,
uniform in `d`.

**The precise reason it is BRIDGE / out of the integer-gap's reach (corrected — not "axis dominance").** RH
needs an **upper bound on the sup** (the largest the prime sum gets). The height/integer-gap bound
`|a·ℓ| ≥ H(a)^{-1}` controls **frequency SEPARATION** (small divisors) — which governs the **variance** and
the **cohomological-solvability** (coboundary regularity `Σ|ĉ_a|²/|a·ℓ|²`), the RH-blind objects (#120).
It does **not** bound the **coefficient-magnitude** that sets the large-values **sup**. (Both axis and
support-`≤2d` combination modes contribute to that sup; the large-values are *built from* the combination/
GCD structure via the resonance method — so this is not "axis dominance.") Upper-bounding the sup is
**Halász/Montgomery/Bondarenko–Seip large-values theory = PARENT**; the integer-gap is at most an *ingredient*
of that method, never its closer. The bounded-degree (support-`≤2d`) restriction is a parent **sub-case**, not
a native improvement.

**Conclusion:** no archimedean/gap normalization moves the RH-bearing sup into the integer-gap's reach — the
sup is a large-values *upper-bound* problem (parent), while the integer-gap delivers only frequency-separation
(variance/solvability, RH-blind). This confirms, from the residual side, Professor's **C5 ⇔ apex** (chat
id=88): an a-priori bound on `sup_t|Δε_l/Δ_l|` would BE RH, and only parent large-values technology could give
it. The integer-gap lane has **no native sub-theorem** in the residual.

## Gates
- [x] 0 → 1  in-progress: the sub-object the integer-gap bound controls is identified (variance, RH-blind);
  the RH-bearing sup is located as a large-values problem; the S_d-normalization decision question posed.
- [x] 0 → 5  **failed/resolved-negative** (2026-06-19): §5 resolved as case (b). The hypothesis "the
  integer-gap/near-resonance lane closes C5★" is **refuted** — Wheeler's gap-difference normalization `(GD)`
  leaves the RH-bearing sup **axis-mode-dominated** (`Δ_l` cancels, single-prime modes survive), i.e.
  Bondarenko–Seip **large-values = BRIDGE**; the integer-gap reaches only the RH-blind variance. No native
  sub-theorem in the residual lane (confirms C5 ⇔ apex). Kept as a navigation/diagnosis record.
- ~~1 → 2 fully-proven~~ — N/A: resolved negative (case (b)), so this card is a diagnosis record, not a
  theorem heading to Lean (cf. the B11 lesson: refutations/clarifications do not enter the formalization
  queue).

## Cross-references
- `../2-fully-proven/c5-jensen-prime-kernel.md` — Professor's kernel (the object).
- `finite-free-convolution-flow.md` — Wheeler's carrier + the `S_d` relative criterion (§5 question).
- `../3-formalized/not_new_scientific_knowledge/zero-estimate-uniformity.md` — the height bound `|a·ℓ| ≥ H(a)^{-1}` (the lane's tool).
- `combination-mode-baker-reducibility.md` — the reducibility handle (RH-blind, #113), confirming §3.

## Log
- 2026-06-19 (DeWitt) — created in 1-in-progress. Pressure-tested the kernel hand-off: the axis-mode sup is
  Kronecker/large-values (§2), not near-resonance; the height/integer-gap bound controls the **RH-blind
  variance** (#120), while the **RH-bearing single-orbit sup** (#104/#113) is a large-values problem. Posed
  the decisive `S_d`-normalization question (§5) that decides whether the integer-gap lane closes C5★ or only
  supplies the frequency-separation input to a resonance-method bound. No runpod used.
- 2026-06-19 (DeWitt) — **validated against `support-extraction-log.md` (user request):** the core
  conclusions are ALREADY established — prime-side RH-blindness as a structural theorem (log ~822–827, #89),
  the Kronecker-vs-Liouville two-heights diagnostic (~1066–1071), the "Kronecker→Liouville upgrade = one
  missing uniform bound" (~1079–1085), and Kronecker–Weyl resonance (~1372); plus board #113/#120/#104. Added
  §0 crediting these. Reframed the card as a **routing connector**, not a new finding: its only increment is
  mapping the kernel `D_d` onto the known blindness (§2) and identifying the `S_d`-normalization question with
  the known uniform-bound wall (§5). Grade: STRUCTURAL clarification, no new theorem.

## Log
- 2026-06-19 (DeWitt) — created as a routing connector (the integer-gap controls the RH-blind variance, the
  RH-bearing sup is large-values). **§5 resolved negative & moved → 5-failed:** Wheeler's gap-difference
  carrier `(GD)` is the normalization test; the gap `Δ_l` cancels and the single-prime axis modes survive
  differencing, so `sup_t|Δε_l/Δ_l|` is axis-mode-dominated = Bondarenko–Seip large-values = BRIDGE. The
  integer-gap/near-resonance lane has no native sub-theorem in the residual; confirms Professor's C5 ⇔ apex
  from the residual side. No runpod. Ledger note filed.
