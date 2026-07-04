
## 6. Correction to §4, same session: the near/far split is WRONG — the deficit is uniform

Attack-as-false on §4's (REV-near), before anything builds on it. The per-pair
balance, exact chain (MVT + monotonicity of w = −f′ and F″ = w′-magnitude only):

> g(u,D) − g(v,E) ≥ (D−E)·w(u) − E·(u−v)⁺·F″(v−E)          (†)

For the c/j model at s → 0, per matched index k (x = (k+1)c/i the position):
credit (D−E)w(u) ≈ [2c(k+1)²/i³]·[2/x²], debit E(u−v)F″ ≈
[c(k+1)/i²]·[c(k+1)²/i²]·[(16/3)/x³]; the ratio credit/debit = **3/4 at every
scale k**. Per-pair domination FAILS uniformly on the near range at small s —
(REV-near) as stated in §4 is false there. The uncovered quarter of the debit,
16/(3ci) per index over ~i indices with the log/exp cutoffs, sums to ≈ 0.2 at
c = 2, θ = 1/2 — this IS the measured reversal (0.21), not a far-tail effect.
argmax_s at the small-s end (P-R5/P-R6) is this deficit unshielded by the 2s
credit. §3's far-tail picture survives as the d-saturation mechanism; the near
deficit is the bulk of the value.

**Re-cut once more (Lemma H‡′, single bound, no split):**

> Σ_k (loss_k − gain_k)⁺ ≤ Σ_k [E_k·(S_k − 2s)⁺·F″(v_k − E_k) − (D_k − E_k)·w(u_k)]⁺

with every quantity explicit in the gap profile. The chain (†) is complete
elementary analysis (proved in-line above); what remains for Theorem B⁗ is the
CONTINUUM EVALUATION of the right side for (F7)-class profiles (c/j-type,
log-convex) with a Riemann-sum remainder — one explicit 1-D integral,
B(θ, c, s), certified numerically at B(1/2, 2, 0⁺) ≈ 0.23. Deliverable
unchanged: ΔG ≥ 2 − B ≥ 7/4 on the model class for all C₀ ≤ 1/2; route now
honest. The 3/4 ratio itself is suspicious-clean — [CONJECTURE] it is exactly
3/4 in the continuum limit (from 2·2/(16/3) = 3/4), making the deficit integral
(1/4)·∫debit — check in the closed-form pass.

**[Answered next session-cycle: doc 40.]** The closed-form pass verified the
continuum limit exactly (R(1/2,2,0) = 4/3 − log 3 = 0.23472, matching the
certified discrete limit) and REFUTED the exact-3/4 reading — the 3/4 was the
uniform-F″-bound artifact; with exact kernels every pair is net-loss and the
reversal is the full integral 8ξ²/(4−ξ²)² (c = 2). See doc 40 for Theorem B⁗.
