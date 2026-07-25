# Monodromy Integrality and Selberg's normality conjecture

**Draft preprint.** Status: theorems complete and dependency-closed as stated; the central
conjecture (MI) is open.

---

## Abstract

Let `S` be the Selberg class. For `F,G ∈ S` write `R_{F,G}(w) = Σ_n a_F(n) conj(a_G(n)) n^{−w}`,
absolutely convergent for `Re w > 1` by the Ramanujan axiom. We isolate a single hypothesis —
that `R_{F,G}` is **meromorphic** (single-valued) near `w = 1` — and show that it already implies
Selberg's normality conjecture (Conjecture A), including the integrality of `n_F`, and that it
determines the full complex Selberg pairing, which Conjecture A alone cannot reach. We show that
Conjecture A is not a consequence of the Dirichlet-series, Euler-product and Ramanujan axioms alone.
Finally we prove a *Cusp–Spectrum Radius Law*: the shift-lattice expansion of the degree-`d` theta
function of `F` at any base point has radius of convergence exactly the distance from that point to
the rest of the Kaczorowski–Perelli standard-twist spectrum; at the cusp this reads `d q_F^{−1/d}`.

## 1. The hypothesis

**(MI)** For all `F,G ∈ S` there is an open `Ω ⊇ {Re w ≥ 1}` and a meromorphic function on `Ω`
agreeing with `R_{F,G}` on `{Re w > 1}`, holomorphic and non-vanishing on `{Re w = 1}\{1}`.

MI is strictly weaker than the received formulations of the missing ingredient — "`S` is closed
under Rankin–Selberg convolution", "`S` is automorphic" — both of which demand of `R_{F,G}` a
functional equation, an Euler product of the correct degree, entirety, and a spectral model. MI
demands **only single-valuedness**.

**Refinement (MI⁺⁺).** For `F,G` of equal degree `d` and conductor, `R_{F,G}` is meromorphic on
`{Re w > 1/2}`, with poles there contained in `{1 − j/d : j ∈ Z_{≥0}}`, all of integer order.
(The half-plane is sharp: for a newform `f`, `R_{F,F} = ζ(w)L(w,sym²f)/ζ(2w)` has poles at `ρ/2`
for every zeta zero `ρ`, all with `Re < 1/2`.)

## 2. Theorems

**Theorem 1.** *(MI ⟹ Conjecture A.)* Let `F ∈ S` satisfy MI for the pair `(F,F)`. Then there is an
integer `n_F ≥ 0` with `Σ_{p≤x}|a_F(p)|²/p = n_F log log x + C_F + o(1)`, and
`n_F = −ord_{w=1}R_{F,F}`, with `n_F ≥ 1` iff the abscissa of `R_{F,F}` equals 1.

*Proof.* `R_{F,F}` has non-negative coefficients, so by Landau its abscissa is a singularity; MI
turns it into a pole, whence `n_F ∈ Z_{≥0}`. Writing `log R_{F,F}(w) = Σ_p|a_F(p)|²p^{−w} + E(w)`
with `E` holomorphic on `Re w > 1/2` (Euler product + Ramanujan), MI gives
`P(w) := Σ_p |a_F(p)|² p^{−w} = n_F log(1/(w−1)) + G(w)` with `G` holomorphic near `{Re w ≥ 1}`.
Then `−P'(w) = Σ_p |a_F(p)|²(log p)p^{−w}` has **non-negative** coefficients and a simple pole of
residue `n_F` at `w=1`, holomorphic on the rest of the closed line; Wiener–Ikehara gives
`Σ_{p≤x}|a_F(p)|² log p = n_F x + o(x)`, and partial summation finishes. ∎

**Theorem 2.** *(MI ⟹ integrality of the full complex pairing.)* Under MI for `(F,G)`,
`Σ_p a_F(p)conj(a_G(p))p^{−w} = κ_{F,G} log(1/(w−1)) + O(1)` as `w → 1+`, with
`κ_{F,G} = −ord_{w=1}R_{F,G} ∈ Z`; and `|κ_{F,G}|² ≤ n_F n_G`.

*Remark.* Conjecture A by itself gives only `Re B(F,G) ∈ (1/2)Z`, via `a_{FG}(p)=a_F(p)+a_G(p)`,
and says nothing about `Im B(F,G)`. MI removes the imaginary part outright, making the Selberg
pairing an **integral** positive-semidefinite Hermitian form on the monoid `S`.

**Corollary 3.** Under MI for all pairs, Selberg's orthogonality conjecture follows from exactly two
further statements: **(P1)** `n_F = 1` for every primitive `F`; **(P2)** if
`Σ_p|a_F(p) − a_G(p)|²/p = O(1)` then `F = G`. ((P2) strengthens the Murty–Murty /
Soundararajan / Farmer strong-multiplicity-one line, which assumes `a_F(p)=a_G(p)` off a thin set.)

**Theorem 4.** *(Axiom necessity.)* `F(s) = exp(Σ_p (log p)^{10} p^{−s})` satisfies Selberg axioms
(1) (Dirichlet series, `a_F(1)=1`, absolute convergence for `σ>1`), (4) (Euler product with
`b_F(p) = (log p)^{10} ≪_θ p^θ` for every `θ>0`, `b_F(p^k)=0` for `k ≥ 2`) and (5) (Ramanujan), and
satisfies `Σ_{p≤x}|a_F(p)|²/p ≍ (log x)^{20}`. Hence Conjecture A is **not** a consequence of axioms
(1),(4),(5): every proof must use the analytic continuation or the functional equation.

**Theorem 5 (Cusp–Spectrum Radius Law).** For `F ∈ S^♯` of degree `d`, conductor `q`, with standard
twists `F_α` and `Δ(α₀) = dist(α₀, Spec(F)\{α₀})`:
```
limsup_{k→∞} | F_{α₀}(s − k/d)/k! |^{1/k} = 1/(2π Δ(α₀))      (s off {s*_ℓ + k/d}).
```
At the cusp, `Δ(0) = min Spec(F) = d q^{−1/d}`, so the left side equals `q^{1/d}/(2πd)`; the left
side is computed from the archimedean data alone (uniform Stirling on the functional equation), the
right side from `a_F(1)=1` and the first prime-side singularity — a local–global identity.
Verified exactly on `ζ`, `L(·,χ)`, level-1 holomorphic newforms and level-1 Maass forms.

## 3. Machine-checked components

Lean 4 / Mathlib, all unconditional, `#print axioms` = `[propext, Classical.choice, Quot.sound]`:
- `RHTower.selberg_pairing_prime_sq` : `a_F(p)conj(a_G(p)) = a_{F·conj G}(p²) − a_F(p²) − conj(a_G(p²))`
- `RHTower.selberg_energy_polarization`, `RHTower.selberg_pairing_cauchy_schwarz`,
  `RHTower.int_eq_zero_or_one_or_neg_one_of_sq_le_one` — the algebraic bridge of Corollary 3
- `HTGeometry.genPoly_meanValue` — exact mean value of a generalized Dirichlet polynomial with
  arbitrary real frequencies
- `HTGeometry.residue_jump_bound`, `HTGeometry.residue_jump_of_integral_eq_zero` — the residue-jump
  obstruction used in Theorem 5

## 4. Obstructions (why MI is the right weakening)

1. *Degree multiplicativity.* Any construction of `R_{F,G}` separately linear in `F` and in `G`
   transports archimedean invariants additively, while the target has degree `d_F d_G`; so no such
   construction yields a functional equation. Meromorphy is the most one can ask.
2. *Linear-moment closure.* The axioms deliver exactly `Σ_p a_H(p)p^{−w} = log H(w) + O(1)` — the
   linear prime moments. Conjecture A asks for a quadratic moment, which lies in the square of that
   space.
3. *Truncated spectral data.* The spectral-spike sum of the standard twist **is** a partial sum of
   `R_{F,G}`; its limit is exactly what the continuation encodes. Such constructions give identities,
   not continuations.
4. *Frequency non-isolation.* In `Φ_F(s,z)·\bar G(s',z)` the diagonal is the frequency class
   `2Λ_d`, but off-diagonal frequencies approach it at distance `≍ h²k^{1/d−2}`; the diagonal is
   never spectrally isolated, so no smooth Fourier cutoff extracts it.

## 5. Open

MI itself; (P1); (P2). Under MI, Conjecture A and (by Kaczorowski–Perelli) the generalized prime
number theorem for `S` follow.

## 6. Later additions (cycles 29–47)

**Theorem 6 (explicit Rankin–Selberg object).** For `F ∈ S` set
`𝔏_F(w) := Σ_p Σ_{k≥1} k |b_F(p^k)|² p^{−kw}` and `ℛ_F := exp(𝔏_F)`. Then `𝔏_F` and `ℛ_F` have
non-negative coefficients; `𝔏_F(w) = Σ_p|a_F(p)|²p^{−w} + (holomorphic on Re w > max(1/2,θ))`;
`σ_a(ℛ_F) ≤ 1`; `ℛ_F` differs from `R_{F,F}` by a factor holomorphic and non-vanishing on
`Re w > 1/2 + θ`; and `ℛ_F = L(w, π × \tildeπ)` when `F` is automorphic with a polynomial Euler
product. The identity behind it is `Σ_i α_i^k = k·b_F(p^k)`, so the object is written from the
Euler-product axiom alone. Consequently **MI ⟺ `ℛ_F` is meromorphic at `w=1`**, and the Mertens
`3–4–1` inequality holds unconditionally for `ℛ_F`.

**Theorem 7 (log-coefficient transfer; machine-checked).** If `A 0 = 1`,
`n·A_n = Σ_{j<n}(n−j)·B_{n−j}·A_j` and `‖A_n‖ ≤ C R^n` with `C,R ≥ 1`, then `‖B_n‖ ≤ (4CR)^n`.
Applied with `A_k = a_F(p^k)`, `B_k = k b_F(p^k)`, `R = p^ε` this gives `|b_F(p^k)| ≪ (4C_ε)^k p^{kε}`
from Ramanujan alone — the bound that puts the `k ≥ 2` part of every quadratic prime sum to the right
of `1/2`. Lean: `HTGeometry.log_coeff_bound`.

**Theorem 8 (linear integrality).** (a) If `a_F(p) = m + O(p^{−δ})` then `m ∈ Z`, via
single-valuedness of `ζ(s)^m = F(s)e^{−D(s)}` near `s=1`. (b) If `Σ_{p≤x}(a_F(p)−m)/p = O(1)` then
`m = m_F`, the pole order, hence `m ∈ Z_{≥0}`. Both are proved by applying Selberg's axiom (2) to `F`
itself; Conjecture A is the same statement one level up, where the object needing axiom (2) is
`R_{F,F}` — which is exactly MI.

**Theorem 9 (RH does not suffice).** RH for `F` makes `log F` single-valued on `C` minus the critical
line and makes Carlson's theorem available for `σ > 1/2`, but the resulting identity holds only where
`𝔏'_F` already converges; RH places every zero on `σ = 1/2`, i.e. exactly on the boundary that must be
crossed. Hence `RH(F) ⇏ MI ⇏` no zero-location hypothesis can replace MI.

**Remark (Estermann/Kurokawa lens).** `R_{F,F} = ∏_p R_p(p^{−w})` is an Euler product, and such
products do not generically continue past their abscissa: for fixed `P`, `∏_p P(p^{−s})` continues
iff `P` is a product of cyclotomics. So MI is not a missing estimate but the assertion that the
Rankin–Selberg local factors are of `L`-function type — the functoriality structure.

**Narrowing of counterexamples.** Any `F` violating Conjecture A must have prime coefficients of
constant modulus with genuinely oscillating phase, in degree `≥ 2` with `q_F > 1` or degree `≥ 3`
(degree 1 and degree 2/conductor 1 are classified; `a_F(p) = c + O(p^{−δ})` forces `c ∈ Z`;
`a_F(p) = c p^{−iθ}` forces `c = 0`).

## 7. Later additions (cycles 52–67)

**Theorem 10 (Energy Gap, partial).** For `F ∈ S` and `θ ∈ R`, with `ν = |ord_{s=1+iθ}F|`,
`n_F ≥ ν²`. Hence `n_F ≥ 1` whenever `F` has a pole at `s=1` or a zero anywhere on `Re s = 1`; the
**Energy Gap conjecture** (`n_F = 0` or `n_F ≥ 1`) therefore holds for every `F ∈ S` except those
entire and non-vanishing on the whole line `Re s = 1`. Proof: `|Σ_p a_F(p)p^{−σ−iθ}| = ν log(1/(σ−1))
+ O(1)` from meromorphy, against weighted Cauchy–Schwarz. (Lean: `weighted_cauchy_schwarz`.)

**Theorem 11 (`n_F` is not archimedean).** `n_F` is not a function of `(d_F,q_F,γ_F)`: for `χ₁≠χ₂`
primitive even mod `q`, `F = L(·,χ₁)L(·,χ₂)` and `G = L(·,χ₁)²` share degree, conductor and gamma
factor, but `n_F = 2`, `n_G = 4`. Hence the functional equation alone cannot compute the prime
energy — the rigorous form of the fact that over `Q` the functional equation is archimedean, whereas
over `F_q` it *is* the local Frobenius data.

**Theorem 12 (meromorphic parent).** `G(s) := (F'/F)(s)·(\bar F'/\bar F)(s)` is meromorphic on `C`
and has `c(p²) = |a_F(p)|² log²p`. It is the **only** meromorphic function built from `F` carrying
conjugated quadratic coefficient data: `F(s±a)`, `F(as)`, `F'`, `F''`, products and quotients are
linear in `a_F(p)`; `F·log F` is quadratic but multivalued; `(F'/F)²` is meromorphic but
unconjugated.

**Theorem 13 (contour extractor).** For `Re w > 2`, `1 < c < Re w − 1`,
`𝔐_F(w) = lim_T (π/T)(2πi)^{−1}∫_{c−iT}^{c+iT}(F'/F)(s)(\bar F'/\bar F)(w−s)ds`, and each finite-`T`
integral is holomorphic in `w` off an explicit union of segments. With a smoothed weight and
**Baker's theorem on linear forms in two logarithms**, the off-diagonal is *effectively* removable:
`|k log q − j log p| ≫ (log X)^{−C}` for `d,e ≤ X`, so `𝔐_F(w) = δ·J(w;φ_δ) + O(X^{−(c−1)})` with
`δ = (log X)^{−C}`. (Lean: `exists_gap_of_injOn`, `diagonal_isolation`.)

**Theorem 14 (conservation law).** In the extractor the two arguments satisfy
`Re s + Re(w−s) = Re w`, invariant under contour deformation. So for `Re w < 2` at least one argument
lies left of `Re = 1`, and for `Re w` near `1` both lie near `1/2`: the pinching by the poles of
`F'/F` and `\bar F'/\bar F` in the critical strip **cannot** be evaded by any deformation.

**Structure theorem (cycle 67).** In the Hadamard expansion of `F'/F` the archimedean term
`−(d/2)log|t|` and the zero term `Σ_γ δ/(δ²+(t−γ)²) ≈ (d/2)log|t|` cancel exactly. Hence
`Re (F'/F)(σ+it)` is the fluctuation of the zero-counting measure smoothed at scale `δ = σ−1/2`, and
`n_F` governs its variance. Scale matching forces `δ ≍ 1/log T`, the mean zero spacing.

**Consolidated open core.** All formulations of MI produced here — meromorphy of `R_{F,F}`, `ℛ_F`,
`𝔏'_F`, `𝔐_F`; the contour extractor; the autocorrelation of `F'/F` — reduce to the variance of the
`δ`-smoothed zero-counting fluctuation at `δ ≍ 1/log T`, i.e. to Montgomery-type pair correlation.

**Theorem 16 (Real Gram expansion; the energy functional is blind to imaginary Gram entries).**
Let `⟪v,w⟫ = Σ_p v_p \bar w_p / p` and `E(v) = Re⟪v,v⟫`. For all `a,b,c,d ∈ Z`,
```
E(a v + b w + c \bar v + d \bar w)
  = (a²+c²)E(v) + (b²+d²)E(w) + 2ac Re⟪v,\bar v⟫ + 2bd Re⟪w,\bar w⟫
    + 2(ab+cd) Re⟪v,w⟫ + 2(ad+bc) Re⟪v,\bar w⟫ .
```
Since on prime coefficients multiplication in `S` is addition and conjugation is coefficientwise
conjugation, the vectors of the monoid generated by `F, G, \bar F, \bar G` form exactly the
conjugate-closed integral span of `v_F, v_G`. Hence **no combination of prime energies `n_H` over
that monoid determines `Im Σ_p a_F(p)\overline{a_G(p)}/p`**: the full strength of Selberg's
orthogonality conjecture for a pair cannot be obtained from monoid structure plus the energy
functional, only from the analytic axioms. (Lean: `intComb_sq_re`, `wEnergy_intComb`,
`wEnergy_intComb_congr`.)

**Theorem 17 (logarithmic Sato–Tate ⟹ MI).** If the Satake data of `F` is equidistributed in
*logarithmic* density against Haar measure on a compact group `K` with `a_F(p) = χ_ρ(θ_p)`, then
`n_F = ⟨χ_ρ,χ_ρ⟩ = Σ_i m_i² ∈ Z_{≥0}`. The hypothesis requires only `Σ_p χ_λ(θ_p)/p = O(1)` for
each non-trivial irreducible `λ` — strictly weaker than automorphy, and strictly weaker than natural
Sato–Tate.

**Critical scale, second derivation.** Splitting the second moment of `F` by the approximate
functional equation gives a diagonal term `T·R_F(w)` and a dual term of order
`T^{1+d(1−w)/2}(log T)^{n_F−1}/(w−1)`. At `w = 1+2δ` with `δ = c/log T` both are `≍ T(log T)^{n_F}`.
This reproduces the scale `δ ≍ 1/log T` of the structure theorem by an independent route. The dual
term is a divergent partial sum, not `R_F(2−w)`, so no reflection phase `e^{iπn_F}` arises: the
`w ↦ 2−w` route to integrality is closed.

**Theorem 19 (the Selberg symplectic form).** With `c_{F,G}` the logarithmic prime density of
`a_F(p)\overline{a_G(p)}` and `ω(F,G) := Im c_{F,G}`: `ω` is `Z`-bilinear on the multiplicative
monoid of `S`, alternating, satisfies `ω(\bar F,\bar G) = −ω(F,G)` — so conjugation acts by `−1` on
`ω` and by `+1` on every energy — and vanishes on pairs of self-dual elements. Consequently
Selberg's Conjecture B splits as (symmetric part `= δ_{F,G}`) ∧ (`ω ≡ 0`), and by Theorem 16 the
second half is unreachable from the first by any energy identity. (Lean: `wIP_swap`, `wOmega_swap`,
`wOmega_self`, `wOmega_conj`, `wOmega_eq_zero_of_real`.)

**Theorem 21–22 (the zero energy).** Define `E_F := d_F·lim_T (Σ_ρ m_ρ²)/N_F(T)`, the
multiplicity-weighted zero energy. Under RH for `F` this is `d_F` times the large-`α` limit of
Montgomery's pair-correlation function. Unconditionally `Σ_ρ m_ρ² ≥ N_F(T)`, so `E_F ≥ d_F`, with
equality **iff all zeros of `F` are simple** (Lean: `sum_le_sum_sq`, `sum_sq_eq_sum_iff`,
`sum_sq_div_sum_ge_one`). For the primitive factorisation `F = ∏F_i^{e_i}`, `E_F = Σ_i e_i² d_i`,
whereas `n_F = Σ_i e_i²`: the zero energy and the prime energy are different invariants, agreeing
only when every primitive factor has degree one. Consequently the fine-scale end of the pair
correlation is blind to the factorisation, and the prime energy `n_F` is visible only in the
bounded-`α` (Montgomery) regime.

**Theorem 23–24 (complex-shift regularisation).** For `F,G ∈ S` of degree `d ≥ 1`, `b > 0`, `σ ∈ R`,
```
lim_{A→∞}(1/2A)∫_{−A}^{A} Φ_F(σ,a−ib)\overline{Φ_G(σ,a−ib)} da
   = Σ_n a_F(n)\overline{a_G(n)} e^{−4πb n^{1/d}} n^{−2σ} = R_b^{F,G}(2σ),
```
where `Φ_F(s,α)=Σ_n a_F(n)e(−αn^{1/d})n^{−s}` is entire in `s` for `Im α < 0`. `R_b` is entire in `w`
and is the Mellin–Barnes smoothing of the Rankin–Selberg series. Consequently
```
n_F = lim_{b→0+} log[ lim_{A→∞}(1/2A)∫_{−A}^{A}|Φ_F(1/2,a−ib)|² da ] / log log(1/b) :
```
`n_F` is the logarithmic divergence rate of the regularised `L²`-mean of the standard twist of `F`
**on the critical line**. This supplies the regularisation scheme that the naive real-`α` pairing
lacks (the real-`α` integral diverges exactly on `Spec(F)`). Formalised in finite form:
`genPoly_meanValue`, `oscInt_norm_le` (`‖oscInt δ T U‖ ≤ 2/|δ|`, uniform in the interval length),
`genPoly_meanValue_error`.
