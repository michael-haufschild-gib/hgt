# Denjoy–Carleman profiles: the window (log log N)^{1+ε}

- **ID:** ssha-dc
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper) → Lean
- **Source:** SSHA README "To build"; card 3-formalized/ssha-gevrey-window-2026-10-28
- **Statement:** For odd r ≥ 1, E_r(x) = expNegInvGlue(x^r) satisfies |E_r^{(n)}| ≤ K_r^n (n!)^{1+1/r}; the profile c E_r(1+x) E_r(1−x) is Gevrey of class 1 + 1/r. Hence for every α > 1 there is an explicit profile with: RH iff Weil's form is eventually nonnegative on its atomic families of width (log log N)^α/N.

## Gates
- [x] 0 → 1  in-progress
- [ ] 1 → 2  paper proof below
- [ ] 2 → 3  Lean

## Paper proof
1. E_r is smooth (composition), vanishes on (−∞, 0] (r odd), so all its derivatives vanish there.
2. On (0, ∞), E_r = exp(−(1/x)^r) and E_r^{(n)}(x) = Q_n(1/x) exp(−(1/x)^r), Q_0 = 1,
   Q_{n+1} = r X^{r+1} Q_n − X² Q_n′, deg Q_n ≤ n(r+1).
3. t^j e^{−t^r} ≤ (j!)^{1/r}: (t^j e^{−t^r})^r ≤ (t^r)^j e^{−t^r} ≤ j!.
   With W_D(Q) = Σ_{j<D} |c_j| (j!)^{1/r}: |Q(t)| e^{−t^r} ≤ W_D(Q).
4. (i+m)! ≤ (i+m)^m i! gives w_{i+r+1} ≤ (i+r+1)^{1+1/r} w_i and w_{i+1} = (i+1)^{1/r} w_i, so
   W_{D+r+1}(Q′) ≤ (r+1)(D+r)^{1+1/r} W_D(Q); with D_n = n(r+1)+1, D_n + r = (n+1)(r+1):
   W(Q_n) ≤ ((r+1)^{2+1/r})^n (n!)^{1+1/r}.
5. Leibniz: |(E_r(1+·)E_r(1−·))^{(q)}| ≤ (2K)^q (q!)^s; ‖φ^{(q)}‖₁ ≤ 2c (2K)^q (q!)^s.
6. Apply `riemannHypothesis_iff_atomicFamilies_nonneg_loglog` with s = 1 + 1/r < α; for α > 1 take
   r = 2⌈1/(α−1)⌉ + 1.

## Log
- 2026-10-28 — created.
