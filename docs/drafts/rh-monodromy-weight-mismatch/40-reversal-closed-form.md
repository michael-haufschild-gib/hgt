# 40 — The Reversal in Closed Form: Theorem B⁗ at All C₀ ≤ 1/2

**Register: SEARCH → promotion draft** (task #147; completes the doc 39 program).
Certification: `computations/mwm/reversal_truth.py` closed-form block
(pre-registered P-R7/P-R8/P-R9; all PASS after one numerics repair noted in §4).
Supersedes doc 37 Theorem B″'s range (M″: C₀ ≤ 1/10) and its "per-index
evaluation below c = 10" delegation; resolves doc 39 §6's 3/4-conjecture.

## 1. The exact continuum reversal

Per matched pair (ledger of doc 37 §1 / `ledger_regroup`), with w = −f′,
f = coth(·/2), and increments D_k, E_k = O(1/i):

loss_k − gain_k = E_k·w(v_k) − D_k·w(u_k) + O(1/i²)-per-term,

and for the c/j profile (δ_j = c/j, C₀ = 1/c), in ξ = (k+1)/i ∈ (0, ξ_A],
ξ_A = (1−θ)/θ, θ = i/d ≥ 1/2:

u(ξ) = −c·log(1−ξ) − s, v(ξ) = c·log(1+ξ) + s,
i·D = cξ/(1−ξ), i·E = cξ/(1+ξ).

> **R(θ, c, s) := ∫₀^{ξ_A} cξ·[ w(v(ξ))/(1+ξ) − w(u(ξ))/(1−ξ) ]⁺ dξ**

is the d → ∞ reversal.

**s-monotonicity [PROVED HERE, discrete level].** loss_k = g(v_k, E_k) with v_k
increasing in s and g decreasing in its first argument; gain_k = g(u_k, D_k) with
u_k decreasing in s. So loss_k − gain_k is decreasing in s pairwise (all arguments
stay positive: u_k − D_k ≥ δ_{i+1} − s > δ/2). Hence sup over s ∈ (0, δ/2) is the
s → 0⁺ value: **R(θ, c, 0) bounds every band**.

## 2. c = 2: closed form [PROVED HERE]

At c = 2, s = 0 the kernels are algebraic: sinh(log(1+ξ)) = ξ(2+ξ)/(2(1+ξ)),
sinh(−log(1−ξ)) = ξ(2−ξ)/(2(1−ξ)), so

w(v)·(1+ξ)⁻¹·2ξ = 4(1+ξ)/(ξ(2+ξ)²), w(u)·(1−ξ)⁻¹·2ξ = 4(1−ξ)/(ξ(2−ξ)²),

integrand = (4/ξ)[(1+ξ)(2−ξ)² − (1−ξ)(2+ξ)²]/(4−ξ²)² = **8ξ²/(4−ξ²)²** — positive
on (0,1): in the continuum EVERY pair is a net loss; the ⁺ is inactive and the
reversal is the whole integral. Antiderivative (verified by differentiation:
d/dξ[4ξ/(4−ξ²)] = 4(4+ξ²)/(4−ξ²)², d/dξ log((2+ξ)/(2−ξ)) = 4(4−ξ²)/(4−ξ²)²):

> **R(θ, 2, 0) = 4ξ_A/(4−ξ_A²) − log((2+ξ_A)/(2−ξ_A)),  ξ_A = (1−θ)/θ.**
> At the (F1) edge θ = 1/2: **R = 4/3 − log 3 = 0.2347210446652…**

## 3. The 3/4 conjecture: refuted and explained

Doc 39 §6 conjectured the per-pair credit/debit ratio is exactly 3/4. The 3/4 was
an artifact of mixing the exact w with the UNIFORM bound F″ ≤ (16/3)/x³; the
exact small-x asymptote is F″ ~ 4/x³, and with exact kernels the near-range ratio
is 1 + O(ξ): the deficit is second-order pointwise, and the reversal is carried
by the full-range integral of §2, not by a constant-fraction deficit. Doc 39's
Lemma H‡′ chain (†) remains true; its role shrinks to controlling the O(1/i)
remainder (§5). The doc 39 §3 far-tail picture survives as the d-saturation
mechanism; §6's "uniform quarter deficit" phrasing is superseded by this section.

## 4. Certification (all pre-registered)

- **P-R9 PASS**: mpmath quadrature of the exact integrand = closed form to
  1.7·10⁻¹⁹ at θ ∈ {0.5, 0.6, 0.75}. (First attempt showed ~10⁻³ discrepancies —
  catastrophic cancellation at the ξ → 0 endpoint under tanh–sinh nodes at
  dps 30; repaired by head-series cutoff + node splitting at dps 60. Lesson
  recorded: this integrand is a difference of two ~1/ξ terms.)
- **P-R8 PASS**: sup over the class at the edge: **B*(1/2) := sup_{c≥2}
  R(1/2, c, 0) = 0.247355, attained at c = 2.5** — strictly below 1/4. The sup
  over c is interior (c = 2: 0.2347; c = 2.5: 0.2474; c = 4: 0.2102; c = 8:
  0.0938), matching the discrete main run's observation that c = 3 beat c = 2.
- **P-R7 PASS**: discrete ledger at d = 10⁴, c = 2, θ = 1/2, s = 0.001δ gives
  0.234071 — under the continuum value by 6.5·10⁻⁴ ≈ 3.3/i: the O(1/i)
  remainder is real with empirical constant K ≈ 3.3, and the discrete sequence
  d = 150…10⁴ (0.1811, 0.2113, 0.2241, 0.2299, 0.2341) converges to the closed
  form from below.

## 5. Theorem B⁗ (paper statement)

> **Theorem B⁗.** For (F7)-class fields (c/j-type profile, c ≥ 2, i.e. every
> C₀ ≤ 1/2), one-sided index θ = i/d ≥ 1/2, and every s ∈ (0, δ/2):
> Σ_k (loss_k − gain_k)⁺ ≤ B*(θ) + K/i, with B*(1/2) = 0.2474 < 1/4 and B*
> decreasing in θ (θ = 0.6: ≤ 0.057; θ = 0.75: ≤ 0.0064). Consequently
> **ΔG(s) ≥ 2 + [tip cushion] − 1/4 − K/i ≥ 7/4 − K/i > 1** for i ≥ 4K ≈ 13.

Proof status: continuum identity + c = 2 closed form + s-monotonicity [PROVED
HERE]; certified numerics for the c-sup and K. **Two elementary write-outs
remain** for full 1→2 grade:
- **(B⁗-a)** the c-sup lemma: R(θ, ·, 0) has a single interior maximum on
  [2, ∞) with value < 1/4 at θ = 1/2 (1-D calculus on the explicit integrand;
  certified numerically above);
- **(B⁗-b)** the remainder constant K: three O(1/i) sources — per-pair O(E²F″)
  via the (†) chain, Riemann-sum error (BV of the integrand), harmonic-vs-log
  position shifts — each bounded by the same master integral; empirical total
  K ≈ 3.3.

**What it supersedes.** Doc 37's (M″) threshold C₀ ≤ 1/10 and the per-index
finite evaluation for c < 10: the bulk march ΔG > 0 (indeed ≥ 7/4) now holds on
paper for the ACTUAL carrier class C₀ ≤ 1/2. The per-carrier protocol's march
clause reduces to: verify (F)-hypotheses + i ≥ i₀ = ⌈4K⌉ on the window.

## 6. What this opens

1. (B⁗-a) and (B⁗-b) — contained calculus write-outs; then the (S-mono) arc is
   theorem-complete in the bulk at actual-carrier constants, and Theorem S′'s
   regime map consumes ΔG ≥ 1 directly.
2. **The tip through the same lens**: R(θ → 1, c, 0) → 0 quadratically in
   ξ_A — the reversal DIES at the tip while the far-ahead cushion grows
   (0.63/(Mδ̂)): the tip is doubly protected. Re-price (E-band) #145 with this
   pairing: the E-band's danger regime has small M (short ahead field), which is
   exactly small ξ_A here.
3. Lean: the c = 2 closed form is one `deriv` check + interval arithmetic on
   4/3 − log 3 < 1/4; the LedgerConvex shells consume the resulting bound as
   the `reversal ≤ …` hypothesis. Queue behind the codex agent's #143 stack.
4. The interior maximum at c ≈ 2.5 is a curious invariant of the class —
   [CONJECTURE] it is the balance point between weight strength (small c) and
   drop size (large C₀ = 1/c); whether c ≈ 2.5-fields are extremal for OTHER
   ledger quantities (response, swap) is one cheap probe away.
