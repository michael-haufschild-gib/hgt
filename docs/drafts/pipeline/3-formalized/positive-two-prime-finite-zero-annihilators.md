# Positive two-prime annihilators of finite zero sets

- **ID:** positive-two-prime-finite-zero-annihilators
- **Stage:** 3-formalized
- **Type:** THEOREM
- **Statement:** Every finite set of nontrivial zeta zeros, with arbitrary prescribed finite multiplicities, is annihilated by a finite Dirichlet polynomial with nonnegative real coefficients, constant coefficient `1`, and support on `2^a 3^b`. Such a polynomial can be uniformly arbitrarily close to `1` on `Re s ≥ 1`.

## Mathematical point

Strengthens Cycle 17 of the supplied conjecture ledger: positivity of a finite deflating weight, even with arbitrarily small uniform error from `1` on `Re s ≥ 1`, does not exclude any finite exceptional layer. The coefficients are real, not asserted integral.

## Paper proof

Every actual xi zero `ρ=β+iγ` has `β<1` and `γ≠0`, by strip containment and real-axis nonvanishing. If both phases `exp(−iγ log 2)` and `exp(−iγ log 3)` were `1`, the continuous character `x↦exp(−iγx)` would have periods `log 2` and `log 3`. Their irrational ratio forces the character to be constant, contradicting its value `−1` at `π/γ`.

Let `w≠1` have modulus one. Its powers have negative real part at arbitrarily large exponents. Otherwise, for every sufficiently large `k`, both `Re(w^k)` and `Re(w^(2k))` are nonnegative. The identities `x²+y²=1` and `Re((x+iy)²)=x²−y²` then give `Re(w^k)≥1/2`. A block of `K` consecutive such powers has real part at least `K/2`, whereas its geometric-sum modulus is at most `2/|w−1|`, a contradiction.

Choose `p∈{2,3}` with nontrivial phase `w=exp(−iγ log p)`, and any large `k≥1` with `Re(w^k)<0`. Put `r=p^β`. Then

`Pρ(s)=1−2 Re(w^k) r^k p^(−ks)+r^(2k) p^(−2ks)`

has strictly positive displayed coefficients and constant coefficient `1`. At `s=ρ`, it is `1−2 Re(w^k)w^k+w^(2k)=0`. For `Re s≥1`, setting `q=p^(β−1)<1` gives

`|Pρ(s)−1|≤2q^k+q^(2k)→0`.

Finite products retain coefficient positivity and constant coefficient `1`. For the induction step, choose the old product within `ε/2` of `1`, and the new factor within `ε/(2+ε)` of `1`. Then `|PQ−1|≤|P−1||Q|+|Q−1|<ε`. Thus the finite product annihilates the prescribed set and remains uniformly within any positive `ε` of `1` on the closed right half-plane.

For prescribed orders `mρ`, choose `M=1+maxρ mρ`. Continuity of `z↦z^M` at `1` supplies `δ>0` such that `|z−1|<δ` implies `|z^M−1|<ε`. Construct the preceding annihilator `Q` with accuracy `δ`, and take `P=Q^M`. These Dirichlet polynomials are entire, so each root of `Q` has analytic order at least one and its order in `P` is at least `M≥mρ`. Powers retain coefficient positivity and constant coefficient `1`.

The formal representation is a polynomial in two variables over `ℝ≥0`, evaluated at `exp(−s log 2)` and `exp(−s log 3)`. Coefficient positivity and finite support are intrinsic. The actual-zero capstone discharges strip containment and real-axis nonvanishing from the corpus.

## Lean

Module: `GaloisForLFunctions/ArithmeticPositiveDuality/PositiveTwoPrimeAnnihilators.lean`.
Namespace: `GaloisForLFunctions.ArithmeticPositiveDuality.PositiveAnnihilator`.

- `exists_large_pow_re_neg`: arbitrarily late negative-real powers of a nontrivial unit phase.
- `two_three_phase_ne_one`: simultaneous trivial phases at 2 and 3 force zero frequency.
- `exists_single_annihilator`, `exists_finite_annihilator`: construction for arbitrary finite nonreal point sets left of `Re s = 1`.
- `exists_xi_zero_annihilator`: unconditional specialization to every finite set of actual xi zeros.
- `differentiable_dirichletEval`: the Dirichlet evaluation is entire.
- `exists_xi_zero_annihilator_with_multiplicities`: arbitrary prescribed finite zero orders, with the same positivity, normalization, support, and uniform accuracy.

Final direct Lean check passed without warnings. The multiplicity capstone's transitive axioms are exactly `propext`, `Classical.choice`, `Quot.sound`. No AAL decision is claimed.
