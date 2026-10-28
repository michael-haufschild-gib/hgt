# The Gevrey window: RH-strength at overlap ratio (log log N)^s

- **ID:** ssha-gevrey
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** SSHA README open topic 2 / To build; parent card spacing-scale-harmonic-analysis-2026-10-27
- **Statement:** For a smooth profile φ in [−1,1], ∫φ = 1, with ∫|φ^{(q)}| ≤ A B^q (q!)^s (s ≥ 0), and dilations κ_N → ∞ with (N/κ_N)/(log log κ_N)^s → ∞: RH iff Weil's form is eventually nonnegative on the atomic families of width 1/κ_N. An explicit Gevrey-2 profile exists, so overlap ratio ≫ (log log N)² suffices.

## Goal
Narrow the open window of SH19 ((log N)^ε) to (log log N)^s.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  paper proof below
- [x] 2 → 3  Lean: `TheGevreyWindow.lean`, `TheGevreyProfile.lean` (`riemannHypothesis_iff_atomicFamilies_nonneg_of_gevrey`, `riemannHypothesis_iff_gevreyProfile_nonneg_loglog`); axioms propext, Classical.choice, Quot.sound

## Paper proof
1. Tower, refined: if ‖H^{(j)}‖₁ ≤ C j!^s X^j for all j, then ‖T_p^{(j)}‖₁ ≤ C (j+p)!^s X^j Π_{i≤p}(X+i)
   (induction on p: T_{p+1}^{(j)} = T_p^{(j+1)} − (p+1) T_p^{(j)}).
2. Leibniz, Gevrey: |F^{(l)}| ≤ M b^l l!^s, ‖ψ^{(q)}‖₁ ≤ A B'^q q!^s ⇒ ‖(F(·−c)ψ(a−·))^{(i)}‖₁ ≤ MA i!^s (b+B')^i
   (l!(i−l)! ≤ i!, binomial theorem). For ψ = φ_k, B' = Bk.
3. EM: |S − F∗φ_k| ≤ (|B_p|/p!) n₀^{−p} MA p!^s Π_{i≤p}(X+i) ≤ MA (p^s (X+p)/n₀)^p, X = b + Bk, using
   |B_{2m}| ≤ (2m)! (|B_{2m}| = 2(2m)!ζ(2m)/(2π)^{2m}).
4. Order p_n = 2⌈log log k⌉ + 2: ρ_n = p^s(b + Bk + p)/n₀ → 0 under the growth hypothesis (k/n₀ = B/K, p^s/K → 0,
   p^{s+1}/n₀ → 0), so eventually ρ ≤ e^{−1} and the error ≤ MA e^{−p} ≤ MA/(log k)²; log k · error² → 0.
   Lipschitz part: order-2 EM as in SH19 (bounded LD/k).
5. Gevrey test: mollify the C² negative test with φ_m (fixed m): F^{(l)} = g ∗ (φ_m)^{(l)}, |F^{(l)}| ≤ M_g A (Bm)^l l!^s.
6. Explicit profile: E = expNegInvGlue, E^{(n)}(x) = P_n(1/x)E(x), P_{n+1} = X²(P_n − P_n′);
   W(P) = Σ|c_j| j! bounds sup|P(1/x)E(x)| (t^j e^{−t} ≤ j!); W(P_{n+1}) ≤ 2(2n+1)² W(P_n) ⇒ |E^{(n)}| ≤ 8^n n!².
   φ_G = c E(1+x)E(1−x): Leibniz ⇒ |φ_G^{(q)}| ≤ c 16^q q!², ∫|φ_G^{(q)}| ≤ 2c 16^q q!².

## Log
- 2026-10-28 — created.
