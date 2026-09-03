# Archimedean obstructions to integrality anchors for the Riemann zeta function

## Abstract

Every known proof that locates the zeros of an L-function on a line rests on a discrete invariant
squeezed below one: Weil–Deligne (eigenvalues of Frobenius are algebraic integers, amplified by
tensor powers) and Ferrero–Washington (a valuation refuted by one equidistributed instance). We
prove that neither template transfers to the Riemann zeta function. In the Arakelov coordinate
`w(ρ) = 1 − 1/ρ`, in which the critical line is the unit circle, Weil–Deligne integrality of the
zeros is incompatible with the Riemann Hypothesis itself (Theorem 3); in the unnormalised
coordinate `p^ρ` it fails at three primes (Theorem 4, by the six exponentials theorem, which we
formalise). The negation of RH never produces a universal arithmetic statement: the paired Li
coefficients are positive for arbitrarily large `n` whenever RH fails and are never eventually
negative (Theorem 6), so no single instance can refute an off-line zero. Two further rigidity
results support the classification: every twin factorization of ξ is a square root dressed by a
unit (Theorem 1), and ξ has critical-line zeros of odd order above every height, so no structure
doubling all multiplicities exists (Theorem 2). All theorems are certified in Lean 4 without
additional axioms.

## 1. Setting and notation

`ξ(s) = ½ s(s−1) π^{−s/2} Γ(s/2) ζ(s)` is entire, real on the real axis, and satisfies
`ξ(1−s) = ξ(s)`. Its zeros lie in the open strip `0 < Re s < 1`, none is real, and they are
symmetric under `s ↦ 1 − s` and under conjugation. For a zero `ρ` write `m_ρ` for its
multiplicity and `w(ρ) = 1 − 1/ρ`; then `|w(ρ)| = 1 ⟺ Re ρ = ½`, `|w(ρ)| < 1 ⟺ Re ρ > ½`, the
map `ρ ↦ w(ρ)` is injective, and `ρ ↦ 1 − ρ` sends `w ↦ w⁻¹`. The paired Li coefficients are
`2λ_n = Σ_ρ m_ρ (2 − w(ρ)^n − w(ρ)^{−n})`, an absolutely convergent sum, and RH is equivalent to
`λ_n ≥ 0` for all `n` (Li). Hardy's theorem gives infinitely many zeros on the line. `Ξ(t)`
denotes `Re ξ(½ + it)`, which equals `ξ(½ + it)`.

## 2. Twin rigidity

**Theorem 1.** Let `a, d` be analytic on `Re s > ½` with `a·d = ξ` there and equal vanishing
orders at every point of the half-plane. Then there are an analytic `g` with `g² = ξ` on the
half-plane and an analytic nonvanishing `v` with `a = g v` and `d v = g`. Conversely `(g v, g/v)`
is such a factorization for every such `g, v`.

*Proof.* Equal orders make `q = a/d` extend to an analytic nonvanishing function on the
half-plane: the raw quotient has meromorphic order zero at every point, and its meromorphic
normal form is analytic and nonvanishing, with `a = q d`. The half-plane is convex, hence simply
connected, so `q` has an analytic square root `v`, nonvanishing since `q` is. Put `g = d v`: then
`g² = d² q = d a = ξ`, `a = q d = v² d = g v`, and `d v = g`. For the converse, `(g v)(g/v) = ξ`
and the orders of `g v` and `g/v` both equal the order of `g` because `v` and `v⁻¹` have order
zero. ∎

The set of twin factorizations is therefore empty or a torsor under the analytic units of the
half-plane over the diagonal twin `(g, g)`; non-diagonal twins carry no information beyond the
existence of a square root, which is the base rung of the multiplicity ladder
(`RHLadder 1 ⟺` every off-line order is even).

Lean: `RHTower.twin_eq_sqrt_mul_unit`, `twinFactorization_of_sqrt_mul_unit`,
`twinFactorization_iff_exists_sqrt`.

## 3. The global parity wall

**Theorem 2.** (a) For every `T` there are `τ₁ < τ₂` above `T` with `Ξ(τ₁)Ξ(τ₂) < 0`. (b) For
every `T` there is a critical-line zero above `T` of odd order. (c) Not every vanishing order of
ξ is even. (d) Let `f` be analytic at `z` with finite order there, `u` analytic with `u(z) ≠ 0`,
and `e ∈ ℕ`. The order of `f^e u` at `z` is `e` times the order of `f`; if `e` is even it is even;
if `e` is odd its parity is that of the order of `f`. In particular, for `ξ^e u` with `u` entire
and nonvanishing, either `e` is even and every order is even, or `e` is odd and there is a zero
of odd order.

*Proof.* (a) Hardy's tail argument shows that a one-signed tail of the density
`−2 Ξ(4πw)/((4πw)² + ¼)` is impossible, in the weak form `≥ 0` or `≤ 0` beyond some height;
hence `Ξ` takes strictly negative and strictly positive values above every height, and the two
points can be ordered. (b) On a critical-line segment with nonvanishing endpoints, the product of
the endpoint signs of `Ξ` is negative exactly when the total enclosed on-line order is odd; an odd
total forces one summand to be odd. (c) follows from (b). (d) is the additivity of orders under
products together with order zero for a nonvanishing factor. ∎

Consequence: any symmetry class whose induced pairing doubles every multiplicity of ξ is
excluded, and any determinant presenting the divisor of ζ through `e` copies (cusp counts,
Fricke pairs, Weil-representation components, mirror pairs) carries its parity for free when `e`
is even and violates a global doubling when `e` is odd. The theta-multiplier transfer operator on
`Γ₀(4)` has exactly two singular cusps, Fricke-paired, hence `e = 2`.

Lean: `exists_Xi_sign_flip_gt`, `exists_odd_order_line_zero_gt`, `not_forall_even_order_xi`,
`xi_copies_parity_dichotomy`, `det_involution_symmetric`.

## 4. The Frobenius torsion law

Say the Arakelov coordinates are *integral* if every `w(ρ)` is an algebraic integer, *faithful*
if every Galois conjugate of a `w(ρ)` is a `w(ρ')` for a zero `ρ'`, *unitary* if every `|w(ρ)| = 1`,
and *contractive* if every conjugate of every `w(ρ)` lies in the closed unit disc.

**Theorem 3.** (a) Integral, faithful and unitary coordinates cannot coexist. (b) Integral and
faithful coordinates refute RH. (c) Integral, contractive and faithful coordinates are
contradictory. (d) If `p ≥ 2` is an integer, `ρ` is nonreal and `p^ρ` is algebraic, then `ρ` and
`w(ρ)` are transcendental.

*Proof.* (a) Under faithfulness and unitarity every conjugate of `w = w(ρ)` has modulus one, so
by Kronecker's theorem `w` is a root of unity, of some order `m(ρ) ≥ 1`. Distinct zeros have
distinct coordinates and `{z : z^m = 1}` is finite, so each order occurs for finitely many zeros;
since there are infinitely many zeros, the set of orders is infinite. Fix an order `m ≥ 8`
occurring for a zero `ρ`. There is a totative `k` of `m` with `m ≤ 4k ≤ 3m`: take `k = (m−1)/2`,
`m/2 − 1`, or `m/2 − 2` according as `m` is odd, `≡ 0`, or `≡ 2 (mod 4)`; in each case a common
prime divisor of `k` and `m` would divide `m − 2k ∈ {1, 2, 4}` while `k` is odd. The number
`z = exp(2πik/m)` is a primitive `m`-th root of unity, hence a root of the `m`-th cyclotomic
polynomial, which is the minimal polynomial of `w` over ℚ; by faithfulness `z = w(ρ')` for a zero
`ρ'`, and `ρ' = 1/(1 − z)`. Since `π/2 ≤ 2πk/m ≤ 3π/2`, `cos(2πk/m) ≤ 0` and `|1 − z|² =
2 − 2cos(2πk/m) ≥ 2`, so `|ρ'| ≤ 1`. Distinct orders give distinct `z` and distinct `ρ'`, so the
closed unit disc contains infinitely many zeros of ξ, which accumulate; ξ is entire and not
identically zero, a contradiction. (b) RH puts every coordinate on the unit circle, so (a)
applies. (c) Integrality and contractivity imply RH by the norm argument (the product of the
conjugates of a nonzero algebraic integer has modulus at least one, contractivity bounds it by
`|w|`, so `|w| = 1`); then (b). (d) If `ρ` were algebraic it would be irrational, being nonreal,
and Gelfond–Schneider would make `p^ρ` transcendental; algebraicity of `w(ρ)` is equivalent to
that of `ρ`. ∎

Reading. Over `𝔽_q` the Frobenius eigenvalues have modulus `q^{1/2} ≠ 1`, and Kronecker's
theorem never applies; over ξ the scale is `1`, so any Frobenius that is both integral and
unitary has finite order on each mode, and the zeros of ξ are not torsion points in the Arakelov
coordinate.

Lean: `not_xiArakelovIntegral_faithful_unitary`,
`not_riemannHypothesis_of_xiArakelovIntegral_faithful`,
`not_xiArakelovIntegral_contractive_faithful`, `not_isAlgebraic_arakelovW_of_nat_cpow_isAlgebraic`.

## 5. Per-prime integrality and the six exponentials theorem

**Theorem 4.** Let `x₀, x₁` and `y₀, y₁, y₂` be complex numbers, each family linearly
independent over ℚ. Then one of the six numbers `exp(x_i y_j)` is transcendental. Consequently,
for nonreal `ρ` and distinct primes `p, q, r`, not all of `p^ρ, q^ρ, r^ρ` are algebraic.

*Proof.* Suppose all six algebraic; let `K` be the number field they generate, `d = [K:ℚ]`, `c`
a nonzero integer clearing their denominators, `H` a bound for the houses of the scaled numbers,
`X = |x₀| + |x₁|`, `Y = |y₀| + |y₁| + |y₂|`. For `a, b ≤ L` put `λ_{ab} = (a+1)x₀ + (b+1)x₁`,
pairwise distinct by independence, and for `m ∈ [1, M]³` put `s_m = Σ (m_j + 1) y_j`, pairwise
distinct likewise. Then `exp(λ_{ab} s_m) = ∏_{i,j} exp(x_i y_j)^{e_i n_j}` with exponents
`e = (a+1, b+1)`, `n = (m_j + 1)`, and `c^{6LM} exp(λ_{ab} s_m)` is an algebraic integer of house
at most `H^{6LM}`. With `M₀ = N²`, `L = 2dN³` (so `2M₀³ ≤ L²`), Siegel's lemma over `K` gives
integral coefficients `ξ_{ab}`, not all zero, with `F(s_m) = 0` for all `m` of level `M₀`, where
`F(z) = Σ ξ_{ab} exp(λ_{ab} z)`, and house bound `B ≤ 2c₁² L² H^{6LM₀}`. `F` is not identically
zero (an exponential polynomial with distinct frequencies vanishes identically only if its
coefficients do) and `|F(z)| ≤ L² B exp(LX|z|)`.

Induction on `M ≥ M₀`: suppose `F` vanishes at all samples of level `M` and let `|z| ≤ (M+1)Y`.
The multipoint Schwarz lemma on the disc of radius `R = 4(M+1)Y`, with the `M³` zeros of level
`M`, gives `|F(z)| ≤ (2/3)^{M³} L² B exp(4LXY(M+1))`. If `z = s_m` is a sample of level `M+1`
and `F(z) ≠ 0`, then `c^{6L(M+1)} F(z)` is a nonzero algebraic integer of house at most
`L² H^{6L(M+1)} B`, and Liouville's inequality gives `|F(z)| ≥ (H^{6L(M+1)} (L² H^{6L(M+1)}
B)^{d−1})^{−1}`. The two bounds are incompatible once `M³ log(3/2) > K₁ + K₂ N³ M`, where
`K₁, K₂` depend only on `d, c₁, H, X, Y`; this holds for all `M ≥ N²` when `N` exceeds an explicit
constant, since `M³ ≥ N · N³M`. Hence `F` vanishes at every level. For arbitrary `z`, apply the
Schwarz bound at level `M` with `(M+1)Y ≥ |z|` and let `M → ∞`: `F(z) = 0`. This contradicts
nonvanishing. For the corollary take `x = (1, ρ)` and `y = (log p, log q, log r)`: `1, ρ` are
independent because `ρ` is nonreal, the logarithms because distinct primes are multiplicatively
independent, and `exp(1 · log p) = p` is algebraic. ∎

Lean: `SixExponentials.six_exponentials`, `SixExponentials.not_all_three_prime_cpow_isAlgebraic`
(six modules, about 1300 lines, reusing the corpus's Siegel lemma with explicit constant,
multipoint Schwarz lemma, Liouville inequality and Baker's theorem).

## 6. The off-line indicator

**Theorem 5.** The escape multiplicity `I(q)` of the corpus's direct sub-unit anchor satisfies
`I(q) = 0` if `Re q = ½` and `I(q) = 1` otherwise, for every zero copy `q`. Hence the anchor's
sub-unit inequality `B < (115/108) I(q)` holds exactly when `q` is off the line, and `I ≡ 0` is
equivalent to RH.

*Proof.* `I(q) = 0` iff the rank-two boundary flux vanishes iff the centered rate vanishes iff
`Re q = ½`; the budget `B` is nonnegative and below `115/108`. ∎

Lean: `thetaKakutaniEscapeMultiplicity_eq_ite`, `budget_lt_quantum_mul_escapeMultiplicity_iff`,
`forall_thetaKakutaniEscapeMultiplicity_eq_zero_iff_riemannHypothesis`.

## 7. Li sign oscillation and the absence of archimedean universality

**Theorem 6.** (a) If RH fails then for every `N` there is `n ≥ N` with `λ_n > 0`. (b)
Unconditionally, there is no `N` with `λ_n < 0` for all `n ≥ N`. (c) Abstract form: let
`(v_i)` be a family of nonreal complex numbers with `1 ≤ |v_i| ≤ M`, weights `m_i ≥ 1`, and
`Σ m_i |v_i − 1|² < ∞`; if some `|v_{i₀}| > 1` then `Σ_i m_i Re(2 − v_i^n − v_i^{−n})` is
positive for arbitrarily large `n`.

*Proof.* (c) Only finitely many `v_i` exceed `q = (1 + |v_{i₀}|)/2 > 1`; let `R > q` be the
largest modulus among them and `D` the set attaining it, `E` the others exceeding `q`. Write
`v_i = |v_i| u_i` with `|u_i| = 1`; the `u_i` are nonreal, so `u_i ≠ 1`. *Mean value on the
torus:* by simultaneous recurrence choose `n₀ ≥ 2` with `|u_i^{n₀} − 1| < ε` for all `i ∈ D`, with
`ε` below every `|u_i − 1|` and below `A/(2(A+B))` where `A = Σ_D m_i`, `B = Σ_D m_i/|u_i − 1|`.
Then `Σ_{k=1}^{n₀} Σ_D m_i Re(u_i^k) = Re Σ_D m_i u_i(u_i^{n₀} − 1)/(u_i − 1) < εB`, while the
`k = n₀` term alone is at least `A(1 − ε)`; so some `k₀ ∈ [1, n₀)` has
`T(k₀) = Σ_D m_i Re(u_i^{k₀}) < 0`. *Positivity:* put `ε' = −T(k₀)/(2A)` and choose, by
recurrence at large exponents, `n ≥ N` with `|u_i^n − 1| < ε'` for all `i` in `D ∪ E`; set
`n' = n + k₀`. For `i ∈ D`, `Re(v_i^{n'}) = R^{n'} Re(u_i^n u_i^{k₀}) ≤ R^{n'}(Re(u_i^{k₀}) + ε')`,
so the `D`-part of the sum is at least `R^{n'} · (−T(k₀)/2)`, using `Re(2 − v^{n'} − v^{−n'}) ≥
−Re(v^{n'})`. The `E`-part is at least `−Σ_E m_i |v_i|^{n'}` with all `|v_i| < R`, and the tail
below `q` is at least `−n'^2 q^{n'} Σ m_i|v_i − 1|²`. Dividing by `R^{n'}`, the negative parts
tend to zero, so the sum is positive for `n` large. (a) Apply (c) to the representatives of
modulus at least one of `{w(ρ), w(ρ)⁻¹}` with multiplicities `m_ρ`; the paired sum is `2λ_n`,
the representatives are nonreal because no zero is real, and an off-line zero gives a
representative of modulus above one. (b) Under RH all `λ_n ≥ 0`; otherwise (a). ∎

Consequence (no archimedean universality). The negation of RH implies only statements holding
infinitely often or with positive density, never for all `n`: the dominant off-line contribution
to every real arithmetic datum is a mean-zero almost-periodic oscillation. A Ferrero–Washington
argument needs a universal consequence refuted by one instance; none exists here.

Lean: `exists_re_sum_pow_neg`, `exists_ge_re_tsum_liTerm_pos`,
`exists_ge_re_xiLiPaired_pos_of_not_riemannHypothesis`, `not_eventually_re_xiLiPaired_neg`.

## 8. The classification

Every producer shape proposed for RH in the corpus or the literature is one of: (i) a fixed
functional of the zero measure (pair-even, and paying one `log t` of archimedean crowd per zero);
(ii) convergence or continuation of an arithmetic object inside the strip (identical to the
conclusion: Möbius convergence at one point is the zero-free half-plane to its right); (iii) a
symmetry relating the fibre at `s` to the fibre at `σ(s)` (blind at free orbits, because doubling
any block is a free symplectic realisation); (iv) a two-factor presentation of ξ (Theorem 1).
What survives is a discrete invariant squeezed below one, amplified (Weil–Deligne) or direct
(Ferrero–Washington). Theorems 3–4 close the first in both coordinates in which a Frobenius
eigenvalue can be normalised; Theorems 5–6 close the second: the only integer in the corpus's
direct anchor is the off-line indicator, and the negation of RH admits no universal consequence.
A producer would have to supply a one-signed off-line signal without knowledge of the zero's
frequency; no functional of ζ's values does.

## 9. Lean certificate

All theorems are formalised in Lean 4 over Mathlib in the modules named above, wired into the
`GaloisForLFunctions.RHTower` umbrella, with `#print axioms` returning only
`propext, Classical.choice, Quot.sound`, no `sorry`, and no hypotheses beyond those displayed.
