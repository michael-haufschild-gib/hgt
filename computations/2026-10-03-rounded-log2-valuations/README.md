# Rounded log 2: p-adic valuations of window numerators (2026-10-03)

**Object.** x_S = Σ_{k≥1} 1/(s(k) 2^k), s(k) = largest S-smooth integer ≤ k (S a finite set of odd
primes) — log 2 = Σ 1/(k 2^k) with denominators rounded down to S-smooth numbers; x_S → log 2 as S
grows. On a window where Q = Π_{p∈S} p^{⌊log_p k⌋} and σ = s(k) are constant, the state numerator
satisfies R_{k+1} = 2R_k + Q/σ (mod Q), so U = R + Q/σ evolves as U·2^i: the digits follow an orbit
of 2 modulo Q/gcd(U, Q). Question (needed to state a Korobov-type normality theorem for x_S): how
large is gcd(U_w, Q_w)?

**Computation.** Exact integer arithmetic over all windows (closed-form jumps), k ≤ 10^15 for
|S| = 1, 2 and k ≤ 10^12 for |S| = 3 (`valuations.py`, `eff_modulus.py`, `residues.py`; pod, < 1 min).

**Outcome.**
- S = {3}: U coprime to Q in every window (U ≡ 2 mod 3 at window start — proved by hand).
- S ⊆ {5, 7, 11}: v_p(U) ≤ 1 in every window; effective modulus Q' = Q/gcd ≥ Q^{0.75} everywhere.
- 3 ∈ S: U ≡ 0 (mod 3) in every window whose σ does not carry the full power 3^{v_3(Q)}, and
  often U ≡ 0 mod 3^{v_3(Q)} (3-adic part pinned at the affine fixed point −Q/σ); Q' < Q^{0.75}
  on 78% of positions for S = {3,5}, but Q' ≥ Q^{1/2} always.

**Explanation (proved by hand).** All S-smooth numbers are odd, so every completed run
[s₁, s₂) of a constant rounded denominator has even length, and its contribution to R mod 3 is a
multiple of 2^{s₂−s₁} − 1 ≡ 0 (mod 3). Only the current run contributes, and only when σ carries the
full 3-power.

**Consequence.** Normality of x_S via orbit sums needs a lower bound on Q'; for 3 ∉ S the data
suggest Q' = Q up to bounded factors, for 3 ∈ S the 3-adic forcing is switched off on most windows.
Not pursued further (toy family; π's BBP moduli change at every digit).
