# 36 — (S-mono) with Explicit Constants, Part II: Response, Tail, Assembly

**Register: SEARCH → promotion draft** (continues doc 35; completes the 1→2 gate for
steps (c), (d), (e)). Tasks #138/#142. **Correction found by this write-out:** doc 31
§5's (χ2) chase mis-evaluated the small-argument asymptotic (φ(u) ~ 1/u³, not 8/u³ —
the 8 belongs to φ(dist/2) in the distance variable) and its factor-40 conclusion does
not survive with correct constants. The repaired argument below is stronger in
structure: a shifted pairing makes every bracket ≤ 0 termwise, the endpoint margin is
EXACT from AM–GM, and the response bound holds on an explicit band, with the far-end
regime delegated to doc 28 (L3) exactly as doc 29(e) anticipated. Notation of doc 35;
δ := δ_i, M := d − i − 1 (number of ahead poles), s := s_i ∈ (0, δ/2).

## 1. Lemma A′ — the exact endpoint margin (AM–GM, no constants to chase)

**Lemma A′.** Under (F1)+(F2)(i): s_i ≤ δ/2 − log cosh(δ/2). In particular, since
log cosh x ≥ x²/2 − x⁴/12 and δ ≤ 1: **δ/2 − s_i ≥ δ²/9.**

*Proof.* Doc 35 Lemma A stage (i) gives c_i > m := (α_i + α_{i+1})/2 in
x-coordinates. Exactly: log m − (t_i + t_{i+1})/2 = log( (e^{t_i}+e^{t_{i+1}})/2 ) −
(t_i+t_{i+1})/2 = log cosh(δ/2). Hence t*_i = log c_i > (t_i+t_{i+1})/2 +
log cosh(δ/2), i.e. s_i < δ/2 − log cosh(δ/2). The numeric form: for 0 < x ≤ 1/2,
log cosh x ≥ x²/2 − x⁴/12 ≥ (x²/2)(1 − 1/24) and (δ²/8)(23/24) ≥ δ²/9. ∎

The margin is not an estimate — log cosh(δ/2) is the exact arithmetic–geometric gap of
the two gap endpoints. The constraint (position right of the x-midpoint) yields the
log-margin for free; nothing about the field beyond (F2)(i) enters.

## 2. Step (c): the response bound dW/ds < 0, corrected pairing

Recall 4·dW/ds = Σ_{k=1}^{i} φ((B_k−s)/2) − φ(s/2) − Σ_{j=1}^{M} φ((A_j+s)/2),
φ = csch²·coth (doc 35 (T5)). Additional toolbox item:

**(T7)** |φ′(v)| = csch²(v)·(2 + 3csch²(v)); hence
3/v⁴ − 6/v² ≤ 3·csch⁴(v) ≤ |φ′(v)| ≤ 3/v⁴ + 2/v², and |φ′| is decreasing.
*Proof.* φ′ = −2csch²coth² − csch⁴ = −csch²(2coth²+csch²) = −csch²(2+3csch²) using
coth² = 1 + csch². Bounds by (T2). Monotonicity: each factor decreasing. ∎

**Lemma D (response, on the band).** Assume (F1)–(F4), δ ≤ 1, s ∈ (0, δ/2 − δ²/9],
and **M ≥ M₀ := ⌈2/√δ⌉**. Then
4·dW/ds ≤ −(δ²/9)·(24/δ⁴) + 4/((M+1)²δ³) ≤ −8/(3δ²) + 1/δ² ≤ −5/(3δ²),
i.e. **dW/ds ≤ −5/(12δ²) < 0.**

*Proof.* Shifted pairing:
4·dW/ds = [φ((B_1−s)/2) − φ(s/2)]
  + Σ_{k=2}^{M+1} [φ((B_k−s)/2) − φ((A_{k−1}+s)/2)]
  + Σ_{k=M+2}^{i} φ((B_k−s)/2).

(i) *Every pair bracket ≤ 0.* For k ≥ 2: B_k − A_{k−1} = δ_i +
Σ_{l=1}^{k−1}(δ_{i−l} − δ_{i+l}) ≥ δ_i > 2s by (F2)(ii) termwise; hence
(B_k − s)/2 > (A_{k−1} + s)/2 and φ decreasing kills the bracket.

(ii) *The first bracket carries the margin.* B_1 − s = δ − s and δ − 2s ≥ 2δ²/9
(Lemma A′). By the mean value theorem and (T7) monotonicity:
φ((δ−s)/2) − φ(s/2) ≤ −((δ−2s)/2)·|φ′((δ−s)/2)|. Since (δ−s)/2 ≤ δ/2 ≤ 1/2:
|φ′((δ−s)/2)| ≥ 3·(2/δ)⁴ − 6·(2/δ)² = 48/δ⁴ − 24/δ² ≥ 24/δ⁴ (δ ≤ 1). Hence the
first bracket ≤ −(δ²/9)·(24/δ⁴) = −8/(3δ²).

(iii) *Unpaired far-behind terms.* For k ≥ M+2: B_k ≥ kδ ((F2)(ii): behind gaps
≥ δ_i), so (B_k − s)/2 ≥ (2k−1)δ/4 and by (T5), φ ≤ 1/v³ + 1/(3v) ≤ (1/v³)(1 + v²/3)
≤ (4/3)/v³ for v ≤ 1, while for v ≥ 1, φ(v) ≤ 1.314·5.36·e^{−2v} ≤ 7.05e^{−2v}
((T4)) ≤ (4/3)/v³ as well (7.05e^{−2v}v³ ≤ 7.05·(27/8)e^{−6}·… ≤ 4/3 for v ≥ 1, since
v³e^{−2v} is maximized at v = 3/2 where it is 0.168, and 7.05·0.168 = 1.18 ≤ 4/3). So
uniformly φ(v) ≤ (4/3)/v³ for all v > 0 here, and
Σ_{k≥M+2} φ((2k−1)δ/4) ≤ (4/3)·(64/δ³)·Σ_{k≥M+2} 1/(2k−1)³
≤ (256/(3δ³))·(1/(4(2M+2)²))·2 ≤ 32/(3(M+1)²δ³) ≤ 4/((M+1)²δ³),
using Σ_{k≥m} (2k−1)^{−3} ≤ ∫_{m−1}^{∞}(2x−1)^{−3}dx = 1/(4(2m−3)²) and folding.

(iv) *Assembly.* With M + 1 ≥ 2/√δ: 4/((M+1)²δ³) ≤ 4δ/(4δ³) = 1/δ². Total:
4·dW/ds ≤ −8/(3δ²) + 1/δ² = −5/(3δ²). ∎

**Remark (sharpness of the band).** At M = O(1) and δ small the unpaired sum genuinely
exceeds the margin — dW/ds < 0 is FALSE near the field edge, and doc 29(c)'s unbanded
claim was an overstatement (its own §(e) already routed the M = O(1) regime through
doc 28 (L3)). The band M ≥ 2/√δ is where the response argument lives; §5 handles the
complement.

## 3. Step (d): the swap term, explicit

**Lemma E.** At fixed s, |W_{i+1}(s) − W_i(s)| ≤ Σ (single-gap coth-increment terms of
the W-ledger) ≤ (C₀/4)·(same structure as doc 35 Lemma B with csch² replaced by |dcsch²|
= 2φ) + ¼[csch²((B̄−s)/2) + csch²((Ā+s)/2)], where B̄, Ā are the swapped far/near
extreme distances. Crudely and sufficiently: under (F1)–(F4),
**|swap| ≤ 8C₀(1 + log(5/δ̂))·(2/δ) + 4/((M+1)²δ²).**

*Proof sketch (constants folded as in doc 35 Lemma B).* The W-ledger is the term-by-term
derivative of the G-ledger (doc 30 §1): the same gap increments Λ_j, Σ_k now weighted by
|d/dx csch²(x/2)| = φ(x/2) ≤ (4/3)(2/x)³-type bounds instead of csch²(x/2)/2; running
the identical two-range summation multiplies Lemma B's bound by the extra scale
max φ/csch² ≤ coth ≤ 2/δ-order on the near range; the two swap-extreme csch² terms are
bounded by (T2)/(T4) at distances ≥ (M+1)δ/2 as in §2(iii). ∎

## 4. Step (e): assembly — ΔS > 0 on the band

**Theorem S (monotone energy, explicit).** Assume (F1)–(F4), (M) of doc 35, δ ≤ 1,
and M ≥ M₀ = ⌈2/√δ⌉. Then

> S_{i+1} − S_i = W_{i+1}(s_{i+1}) − W_i(s_i) > 0,

quantitatively ≥ (5/(12δ²))·(s_i − s_{i+1}) − |swap| with the two lower bounds
(march increment: doc 35 Thm B′; swap: Lemma E), and the balance closes because the
march increment carries the cushion:

*Proof.* Split W_{i+1}(s_{i+1}) − W_i(s_i) = [W_{i+1}(s_{i+1}) − W_{i+1}(s_i)] +
[W_{i+1}(s_i) − W_i(s_i)]. The second bracket is the swap (Lemma E). The first is
∫_{s_{i+1}}^{s_i} (−dW_{i+1}/ds) ds ≥ (s_i − s_{i+1})·(5/(12δ²)) by Lemma D (applied
to the (i+1)-field, whose band parameter is M−1 ≥ M₀−1; take M₀+1 in the hypothesis to
be safe). The march increment: s_i − s_{i+1} ≥ ΔG(s_i)/(2W̄) ≥ (0.417/δ)/(2W̄) with
W̄ = W_{i+1} evaluated at its sup on [s_{i+1}, s_i]; by Lemma D W_{i+1} is decreasing
there, so W̄ = W_{i+1}(s_{i+1}) ≤ ¼[4/s_{i+1}² + Σ_behind 4/(B−s)² + Σ_ahead 4/(A+s)²]
≤ 1/s_{i+1}² + (2π²/3)/δ² ((T2) + gap floors as in §2(iii)). Two cases:

- If s_{i+1} ≥ s_i/4: W̄ ≤ 16/s_i² + 7/δ² ≤ 71/δ²·(δ/(2s_i))²-fold — every factor
  explicit; then ΔS ≥ (0.417/δ)·(5/(12δ²))/(2·(16/s_i² + 7/δ²)) − |swap|, and with
  s_i ≥ s_min > 0 tracked per carrier this is an explicit positive-vs-C₀ comparison of
  the same shape as (M): it holds whenever
  **(M′): |swap|·δ³·(16(δ/s_i)² + 7)·(24/5)·(1/0.417) < 1,**
  which the per-carrier check verifies alongside (M) (both are dominated-by-cushion
  statements; for c/j-model fields LHS = O(C₀ log(1/δ)·δ²) → 0).
- If s_{i+1} < s_i/4: compare directly. W_{i+1}(s_{i+1}) ≥ ¼csch²(s_{i+1}/2) ≥
  1/s_{i+1}² − ¼ ≥ 16/s_i² − ¼, while W_i(s_i) ≤ 1/s_i² + 7/δ². Since s_i ≤ δ/2:
  16/s_i² − 1/s_i² − 7/δ² ≥ 15/s_i² − 7/δ² ≥ 60/δ² − 7/δ² > 0. So ΔS ≥ 53/δ² − ¼ > 0
  outright — a large-jump step is automatically monotone. ∎

## 5. The far-end regime M < M₀ — delegated, and why that is sound

For M < M₀ = ⌈2/√δ⌉ the equilibrium has at most 2/√δ poles ahead: this is doc 28
(L3)'s regime (the direct far-end argument: with O(1) ahead poles the section is a
perturbed one-sided Hermite configuration and doc 25 Thm B's cluster margins apply
directly; no march is needed because the remaining equilibria are within the last
cluster's tracked range). The reader-exactness consumer (doc 24 §3 counting: T counts
margin-1 crossings along OUTER equilibria) needs (S-mono) only up to the last index
where margin ~ 1 can occur; doc 25's clearance places the transition inside the band
M ≥ M₀ for d ≥ d₀ explicit per carrier. The per-carrier protocol therefore checks:
(i) (F1)–(F4); (ii) (M) and (M′) at every outer index of the window; (iii) that the
margin-transition index sits in the band (a finite evaluation of the doc 24 margin at
the band edge). Items (i)–(iii) are finite numeric checks — the same kind the #136/#140
instance already performs.

## 6. Status of the 1→2 gate after Part II

- Steps (a) [Lemma A, doc 35], (a′) [Lemma A′], (b′) [Thm B′ + (M)], (c) [Lemma D, on
  the band, with the corrected pairing], (d) [Lemma E], (e) [Theorem S + (M′), two-case
  split] — all explicit, all elementary, complete proofs in-line except Lemma E's
  folding (same summation as Lemma B run once more with the φ-weight — mechanical).
- CORRECTIONS this gate produced: doc 31 §5 (χ2) constants were wrong (asymptotic
  variable slip); doc 29(c) claim needed the band restriction; both structures were
  repaired here with stronger, exact tools (AM–GM margin; shifted pairing).
- Remaining before the card moves 1→2: (α) write Lemma E's folding in full (one
  summation, doc 35 Lemma B pattern); (β) the per-carrier protocol run on the #136/#140
  u-plane window ((F1)–(F4), (M), (M′), band placement — finite numerics, pre-register
  first); (γ) doc 34 Lemma R constants (R1)–(R4) (independent thread, #139).
Next object: (α), then pre-register (β).

## 7. The folding done: the swap has a SIGN, and the closure map (supersedes §3–§4's constants)

Folding Lemma E properly turned it into a stronger statement than the sketch of §3.

**Lemma E′ (swap sign).** At fixed s, in the W-ledger of the step i → i+1 (the term-by-
term difference mirroring doc 30 §1):

- every behind drift term is ≥ 0 (newB_k = B_k − Σ_k ≤ B_k: distances shrink, csch²
  grows);
- every ahead drift term is ≥ 0 (newA_j = A_j − Λ_j ≤ A_j: same);
- the new far-behind extra is ≥ 0;
- the ONLY negative piece is the removed far-ahead term
  R := ¼·csch²((A_{d−i−1} + s)/2), and by (T2)+(F4):
  **R ≤ 1/(A_{d−i−1} + s)² ≤ 4/(M²δ̂²) ≤ 16/(M²δ²)**, M := d−i−1.

Hence W_{i+1}(s) − W_i(s) ≥ −16/(M²δ²). No gap-variation lower bounds are needed —
the sign structure does the work that §3's magnitude estimate could not. ∎

**Sharpened W-bound.** For s ∈ (0, δ/2): W(s) ≤ 1/s² + 4.9/δ² + 6.6/δ̂² ≤
1/s² + 31/δ² (distances B_k − s ≥ (2k−1)δ/2, A_j + s ≥ jδ̂/2, (T2), Σ(2k−1)⁻² = π²/8,
ζ(2)). In the endpoint band s ≥ δ/3 this gives W̄ ≤ 40/δ².

**Theorem S′ (assembly, three regimes).** Assume (F1)–(F4), (M), δ ≤ 1, C₀δ_j ≤ 1/4
on the window. With increment ≥ ΔG/(2W̄) ≥ 0.417·δ/80 = 5.2·10⁻³·δ (doc 35 Thm B′ +
the sharpened W̄):

1. **Deep band** s_i ≤ δ/3: the pole-dominated response |dW/ds| ≥ 1.4/s_i³ ≥ 38/δ³
   gives ΔS ≥ 5.2·10⁻³δ·38/δ³ − 16/(M²δ²) = 0.2/δ² − 16/(M²δ²) > 0 for **M ≥ 9**.
2. **Endpoint band** s_i ∈ (δ/3, δ/2 − δ²/9]: Lemma D's |dW/ds| ≥ 5/(12δ²) gives
   ΔS ≥ 2.2·10⁻³/δ − 16/(M²δ²) > 0 for **M ≥ 86/√δ**.
3. **Far tip** M < 86/√δ: not covered by these constants — the residual band, named
   **(E-band)**. Routes: doc 28 (L3)'s far-end argument (currently O(1) poles; needs
   extension to M ~ 1/√δ), or the per-carrier numeric check (finite: evaluate ΔS
   directly at the ≤ 86/√δ tip indices of the window).

On c/j model fields δ = c/i, so regime 2's band M ≥ 86√(i/c) covers all
i ≤ d − 87√(d/c): the theorem covers the outer half except the last ~87√(d/c) indices.

**Honest ledger of what the 1→2 gate has established.** (S-mono) on (F)-fields is now
PROVED WITH EXPLICIT CONSTANTS on regimes 1–2 (the outer half minus the (E-band) tip),
with hypotheses (F1)–(F4) + (M) + C₀δ ≤ 1/4, all per-carrier checkable by finite
numerics. The write-out corrected three outline claims (doc 31 §5 (χ2) constants; doc
29(c) unbanded response; §3's swap magnitude — now a sign lemma). The residual is
sharply localized: (E-band) — the last O(√d) indices — where either (L3) extends or
the instance protocol evaluates directly. The reader-exactness consumer needs T = 1 on
the whole outer march; whether the margin-1 crossing can sit inside (E-band) is a
per-carrier question (the #136/#140 window instance: check band placement numerically,
pre-registered). Next objects: (E-band) closure via (L3)-extension [new task], then
the per-carrier protocol run.
