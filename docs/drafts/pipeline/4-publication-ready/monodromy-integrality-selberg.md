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
integral is holomorphic in `w` off an explicit union of segments. With a smoothed weight the
off-diagonal is *effectively* removable, the separation being elementary: for distinct positive
integers `d,e ≤ X`,
```
|log d − log e| ≥ 1/max(d,e) ≥ 1/X ,
```
since `log(d/e) ≥ 1 − e/d ≥ 1/d` for `e < d`. Hence `𝔐_F(w) = δ·J(w;φ_δ) + O(X^{−(c−1)})` with
`δ = 1/X`. (Lean: `inv_max_le_abs_log_sub_log`, `monomial_log_separation`, `exists_gap_of_injOn`,
`diagonal_isolation`.)

*Sharpness, and a correction.* An earlier draft asserted the stronger separation
`|k log q − j log p| ≫ (log X)^{−C}` "by Baker's theorem on linear forms in two logarithms". That is
**false** in the range that matters: for distinct primes `p,q ≤ X` with `q = p+2` one has
`|log p − log q| ≍ 1/X`. A `(log X)^{−C}` gap does hold for perfect powers with both exponents `≥ 2`
(Tijdeman), but the dominant terms here have `j = k = 1`. The elementary bound `1/X` is the correct
and sharp input; no transcendence theory is used anywhere in this paper.

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

**Theorem 27 (zero density of the standard twist).** For `b > 0`, `a ↦ Φ_F(1/2, a−ib)` is analytic
almost periodic on the strip, so Jessen's function
`φ(b) = lim_A (1/2A)∫_{−A}^{A}log|Φ_F(1/2,a−ib)|da` exists and is convex, and by Jessen–Tornehave the
zero density per unit horizontal length between depths is `(φ'(b₂)−φ'(b₁))/2π`. With
`φ(b) ≤ (1/2)log M_F(b) = (n_F/2)loglog(1/b)+O(1)` (Jensen + Theorem 24) and `φ(b) ≥ −2πb`
(convexity plus `φ(b)+2πb → 0`), convexity yields
`𝒩_F(b) ≤ (n_F·loglog(2/b) + O(1))/(2πb)`. Unconditional, every degree `d ≥ 1`. (Lean:
`neg_deriv_le_of_convexOn`, `jessen_zero_density_le`.)

**The sharpening is false.** The conjecture `φ(b) = (n_F/2)loglog(1/b)+O(1)` fails already for
`F = ζ`: there `Φ_ζ(1/2,α) = Li_{1/2}(e(−α))` blows up only near `z = 1`, so `φ(b) = O(1)` while
`(1/2)log M(b) ~ (1/2)loglog(1/b)`. Hence **`n_F` is a concentration exponent, not a size exponent**:
every functional insensitive to sets of density zero — geometric means, Jessen functions, Nevanlinna
characteristics — is blind to it. The same phenomenon explains uniformly why prime energies are blind
to `Im c_{F,G}` and why fine-scale pair correlation is blind to the factorisation.

**Theorem 28 (exact regularised spectral form).** With `α_n = dq^{−1/d}n^{1/d}`, `β = 4πq^{1/d}/d`
and `ρ_0^F` the leading K–P residue,
```
M_F(b) = (Cd/q^{1/d}) Σ_{n≥1} |ρ_0^F(α_n)|² α_n^{−1} e^{−βbα_n} ,
n_F = lim_{b→0+} log[ Σ_{α∈Spec(F)} |ρ_0^F(α)|² α^{−1} e^{−βbα} ] / log log(1/b).
```
This is the regularisation of the `α`-pairing across the spectrum lattice that a domination argument
cannot supply: the damping `e^{−βbα}` is produced canonically by the complex shift, the weight
`α^{−1}` is forced, the sum runs over a discrete set, and every ingredient is a residue.

**Theorem 29–30 (dilation correlation of standard twists).** For `F,G ∈ S` of degree `d`, coprime
`r,s`, `λ = (r/s)^{1/d}` and depths `b`, `λb`,
```
lim_{A→∞}(1/2A)∫_{−A}^{A}Φ_F(1/2,a−ib)\overline{Φ_G(1/2,λa−iλb)} da
      = (rs)^{−1/2} Σ_{t≥1} a_F(rt)\overline{a_G(st)} e^{−4πb(rt)^{1/d}} t^{−1} ,
```
and the correlation vanishes identically unless `λ^d ∈ Q`. At `r=s=1` this gives
`ω(F,G) = lim_{b→0} Im[correlation]/loglog(1/b)`: the alternating form `ω`, provably invisible to
every prime-energy identity (Theorem 16), **is** visible as the imaginary part of the Bohr
correlation of the two standard twists. (Lean: `genPoly_mul_conj_bilinear`,
`genPoly_meanValue_bilinear`, `oscInt_norm_le`.)

**Theorem 31 (the degree barrier, quantified).** The Bohr spectrum of `|Φ_F(1/2,·−ib)|²` is
`{2π(n^{1/d}−m^{1/d})}`, which accumulates at `0` iff `d ≥ 2`. Isolating the diagonal requires
averaging length
```
A  ≫_F  b^{−(d−1)} (log(1/b))^{2−n_F+δ} .
```
For `d = 1` any `A → ∞` suffices uniformly. So the degree barrier of the Selberg class is, on the
twist side, exactly the growth of the required Bohr averaging length.

**Theorem 32 (twist-exponent trade-off).** In the family `F_κ(s,α)=Σ a_F(n)e(−αn^κ)n^{−s}` the
frequency gaps are `≍ κn^{κ−1}`, so the Bohr diagonal is isolated iff `κ ≥ 1`; the Selberg axioms
supply analytic continuation only for `κ ≤ 1/d` (Kaczorowski–Perelli). The two ranges meet **iff
`d = 1`**. Automorphy supplies continuation at `κ = 1` (modularity of the additive twist), so the gap
between the Selberg class and automorphy is exactly the twist-exponent interval `[1/d, 1]`, of length
`1 − 1/d` — matching the exponent `d − 1` of Theorem 31 by an independent computation.

**Theorem 38 (independence of the functional equation; unconditional).** For non-principal `χ` and
real `c > 0`, `F_c = L(s,χ)^c` satisfies Selberg's axioms (1), (4), (5), is holomorphic and
non-vanishing on a neighbourhood of `Re s ≥ 1`, has every linear density zero, and has `n_{F_c} = c²`.
Hence integrality comes neither from the Euler product, nor from Ramanujan, nor from edge behaviour;
it must come from axiom (3) together with continuation across the critical strip.

**Theorem 39 (additive versus quadratic).** Every integer the axioms attach to `F` (`r_F`, `m_F`,
`d_F`) is additive under multiplication, hence a linear form in the primitive exponents, while
`n_F = Σe_i²` is quadratic; `L(·,χ₁)L(·,χ₂)` and `L(·,χ₁)²` share `r, d, q, γ, m` but have `n = 2, 4`.
So `n_F ∈ Z` is not a formal consequence of the axiomatic integers: a proof must manufacture a new
integer. (Lean: `additive_not_determine_energy`, `energy_ne_of_same_total`.)

**Theorem 40 (fractional-power obstruction).** If `F = ∏G_i^{c_i}` is single-valued and meromorphic
then `Σ_i c_i·ord_ρ(G_i) ∈ Z` for all `ρ`; with disjoint zero sets, one simple zero or two zeros of
coprime orders forces `c_i ∈ Z`. (Lean: `exponent_int_of_coprime_orders`.)

**Theorem 43 / Corollary 44 (ratio functional equation).** For `F,G ∈ S` with identical gamma
factors, `W = Λ_F/Λ_G` satisfies `W(s) = (ω_F/ω_G)\overline{W(1−\bar s)}`, has divisor
`div F − div G`, and `F/G` has an Euler product, hence no zeros or poles outside the critical strip.
If `F` and `G` share all zeros then `F = G`.

**Theorem 46 (reduction of quantitative strong multiplicity one).** For `F,G ∈ S` with identical
gamma factors, assume (a) a Selberg-type zero-density estimate and (b) that distinct elements of `S`
cannot have zeros paired at distance `o(1/log T)`. Then
`Σ_{p≤x}|a_F(p)−a_G(p)|²/p = O(1) ⟹ F = G`. Both hypotheses are one-cusp, zero-side statements —
neither is Rankin–Selberg nor automorphy.

**Theorem 47 (pairing from bounded counting difference).** For `F,G ∈ S` with identical gamma
factors and conductors, assume a Selberg-type zero-density estimate. If
`Σ_{p≤x}|a_F(p)−a_G(p)|²/p = O(1)` then `Var(S_F − S_G) = O(1)`, hence `N_F − N_G` — an
**integer-valued** step function — is bounded, hence the zeros interleave and
`|γ_n^F − γ_n^G| ≪ 1/log T`. (Lean: `le_shift_of_count_le`, `abs_shift_of_count_le`.) This is the
only place in the programme where integrality is *used* rather than sought.

**Theorem 49 / Corollary 50 (zero energy = zero rigidity).** For `F ∈ S`, `n_F = 0` is equivalent to
`Var(S_F) = O(1)`, to `N_F − M_F` being bounded, and to the zeros of `F` forming a perfect
log-lattice. Hence the `n_F = 0` case of the Energy Gap conjecture is **equivalent** to: a
non-trivial element of `S` cannot have perfectly rigid zeros — a statement containing no prime sums.

**Recorded negative results (with witnesses).** (i) No argument confined to a neighbourhood of
`Re s ≥ 1` can establish any part of Conjecture A: `L(·,χ)^c` satisfies axioms (1),(4),(5), is
holomorphic and non-vanishing there, has all linear densities zero, and has `n = c²`. (ii) The
`ℓ²`-to-zero-free-half-plane step fails by two independent routes (Cauchy–Schwarz on the abscissa;
the `ℋ²` theory of Hedenmalm–Lindqvist–Seip). (iii) The collision function `Λ_F − Λ_G` operates at
density `T` (Bombieri–Perelli regime) and cannot supply a statement at density `T log T`.
(iv) No `L²` accounting of the sawtooth harmonics of a rigid zero set against the prime frequencies
yields a contradiction: the sawtooth's total mass is a bounded constant.

## 8. Integrality on the critical line (cycles 101–110)

**Theorem 52.** For every `F ∈ S`, `log F(s) − Σ_p a_F(p)p^{−s}` is holomorphic on `Re s > 1/2`.
*Proof.* Ramanujan gives `|a_F(p^k)| ≤ C_ε p^{kε}`; the transfer bound
(`log_coeff_bound`, Lean) yields `|b_F(p^k)| ≤ (4C_ε)^k p^{kε}`; the geometric tail bound
(`tail_geometric_bound`, Lean) gives a per-prime tail `O(p^{2(ε−σ)})`, and `Σ_p p^{2(ε−σ)}` converges
for `σ > 1/2 + ε`. ∎ In particular axiom (4)'s exponent `θ` is subsumed by axiom (5): every `F ∈ S`
has effective `θ = 0`, and the Euler product reaches the critical line.

**Theorem 53.** For every `F ∈ S` and fixed `σ > 1/2`, `∫_0^T|log F(σ+it)|²dt ≪_σ T log²T`
(unconditional). Carlson's *size* hypothesis therefore holds for `log F` on every line right of the
critical line — unlike for `F'/F`, whose singularity `1/(s−ρ)` is not locally square-integrable. The
obstruction to applying Carlson is regularity (the branch points at zeros), not size.

**Theorem 57.** Let `F, G ∈ S` with `a_F(p) = a_G(p)` for all primes `p`, and `Δ(p) := a_F(p²) −
a_G(p²)`. If `c := lim (loglog x)^{−1}Σ_{p≤x}Δ(p)/p` exists then
```
c = − ord_{s=1/2}(F/G) ∈ Z .
```
*Proof.* The `k=1` terms cancel and `b(p²) = a(p²) − a(p)²/2`, so
`log(F/G)(s) = Σ_pΔ(p)p^{−2s} + H(s)` with `H` holomorphic on `Re s > 1/3` by the transfer bound.
Partial summation gives `Σ_pΔ(p)p^{−w} = −c·log(w−1) + O(1)` as `w → 1^+`; meromorphy of `F/G` at
`s = 1/2` gives `log(F/G)(s) = m·log(s−1/2)+O(1)` with `m ∈ Z`. Compare at `w = 2s → 1`. ∎

**Corollary 58.** For every `τ`, `c_τ = −ord_{s=1/2+iτ}(F/G) ∈ Z`: the divisor of `F/G` on the
critical line is read off the prime-square densities, with multiplicity.

**Corollary 59.** With `a_F(p) = a_G(p)` for all `p`: if `c_τ = 0` for every `τ` then `F/G` is entire,
hence a Dirichlet polynomial with an Euler product and `a(p)=0`, hence `F = G`.

**Theorem 60.** From `selberg_pairing_prime_sq` (Lean), `|a_F(p)|² = a_{F\bar F}(p²) − 2Re a_F(p²)`,
so with `δ₂(H) := lim (loglog x)^{−1}Σ_{p≤x}a_H(p²)/p`,
```
n_F = δ₂(F\bar F) − 2 Re δ₂(F) .
```
Hence integrality of the prime-square densities of elements of `S` implies Conjecture A. This
replaces the degree-`d²` Rankin–Selberg construction by two logarithmic densities of objects already
in `S` (of degrees `2d` and `d`).

**Theorem 61.** `Σ_p a_H(p)p^{−1/2−iτ}` converges only if `n_H = 0`. Hence the single-function
analogue of Theorem 57 at the critical line is self-referentially blocked: it would compute `n_H` from
data whose convergence requires `n_H = 0`. **`n_F` is the separation constant between the linear and
the quadratic prime data of `F` at the critical line.**

**Theorem 62 (multi-point Energy Gap).** For `F ∈ S`, `Σ_{θ∈R}(ord_{s=1+iθ}F)² ≤ n_F`. The family
`e_θ(p) = p^{iθ}` is orthonormal for the logarithmic prime form because `Σ_p p^{−1−iθ}` is bounded for
`θ ≠ 0`; Bessel's inequality for a positive semi-definite form (Lean: `bessel_of_orthonormal`) gives
the result. Theorem 10 is the single-term case.

**Theorem 63 (critical-line divisor energy).** For `F,G ∈ S` with identical gamma factors and
conductors and `a_F(p) = a_G(p)` for all `p`, with `Δ(p) = a_F(p²) − a_G(p²)` and
`E = lim (loglog x)^{−1}Σ_{p≤x}|Δ(p)|²/p`,
```
Σ_{τ∈R} ( ord_{s=1/2+iτ}(F/G) )² ≤ E ,
```
so the divisor of `F/G` on the critical line has at most `E` points.

**Theorem 64 (strong multiplicity one under Bounded Satake).** If in addition `E < ∞` — in particular
under Bounded Satake — then `F/G` has finitely many zeros and poles (none off the line, by
Theorem 55), hence is a rational function times `e^{as+b}`; being a Dirichlet series it is constant,
so `F = G`. Bounded Satake is strictly weaker than automorphy and than the polynomial Euler product
conjecture, and no Rankin–Selberg convolution is used.

## 9. Rigid zeros (cycles 121–125)

**Theorem 69 (rigid-zero Poisson identity).** If `F ∈ S` has zeros exactly at `γ_n = M_F^{−1}(n)`,
`M_F` the Riemann–von Mangoldt main term with `M_F' = ν`, then substituting `u = M_F(t)` and applying
Poisson summation, `Σ_ρ φ(γ_ρ) = Σ_{k∈Z} ĝ(k)` with `ĝ(k) = ∫φ(t)ν(t)e^{−2πikM_F(t)}dt`, whose
`k = 0` term is exactly the archimedean term of the explicit formula. Hence
```
Σ_{k≠0} ∫φ(t)ν(t)e^{−2πikM_F(t)}dt = −𝒫[φ] ,
```
`𝒫[φ]` the prime side. The archimedean parts cancel identically because `ν = M_F'`.

**Theorem 70 (perfect rigidity forces triviality; unconditional).** Let `F ∈ S` be entire with exactly
rigid zeros. Then `F = 1`.
*Proof.* Take `φ(t) = ψ((t−t_0)/P)e^{it\log p}`, `P = p^{1+η}`. The `k`-th phase derivative is
`\log p − k(d\log(t/2π)+2πc)`, so for `p < t_0^d` no `k ≠ 0` is stationary and repeated integration by
parts gives `Σ_{k≠0}|ĝ(k)| ≪_A P^{1−A}(\log t_0)^{1−A}`. On the prime side `φ̂` concentrates on
`|n − p| ≲ p/P < 1`, isolating `n = p` with tail `≪_A p^{1/2}p^{−Aη}`, so
`𝒫[φ] ≍ |a_F(p)|p^{1/2+η}\log p`. Letting `t_0 → ∞` at fixed `p` forces `a_F(p) = 0`; iterating at
prime powers gives `F = 1`. ∎

This settles the question of whether an entire order-1 function with a Selberg functional equation can
have a perfect log-lattice of zeros and an Euler product: **it cannot, unless trivial.** Equivalently
(Theorem 49) it settles the exactly-rigid case of the Energy Gap.

**Sharpness.** The hypothesis cannot be weakened to `S_F` bounded. For a general zero set the
identities `Σ_γφ(γ) = ∫φν − ∫φ'S_F` and `∫φ'S_F = 𝒫[φ]` show that the displacement correction *is*
`−𝒫[φ]`, so any "rigid model plus displacement" decomposition cancels identically and yields no
arithmetic information. Exact rigidity is exactly the hypothesis under which `∫φ'S_F` admits an
evaluation external to the explicit formula.

## 10. The zero-counting fluctuation (cycles 127–133)

Throughout, `S_F = N_F − M_F` with `M_F` the Riemann–von Mangoldt main term, and
`𝒫[φ] = ∫φ'(t)S_F(t)dt` is the Weil explicit formula written as a pairing (an identity).

**Theorem 75 (unconditional).** If `F ∈ S` is entire with `|S_F| ≤ K` then `Σ_{p≤x}|a_F(p)|²/p ≤ CK²`
for all `x`; in particular `n_F = 0`. *Proof:* test `𝒫[φ] = ∫φ'S_F` against the amplifier
`φ'(t) = Σ_{p≤x}\overline{a_F(p)}p^{−1/2}ψ((t−t_0)/P)e^{it\log p}` with `P ≫ x`; the arithmetic side is
`(P/2π)E_x`, the analytic side `≤ K‖φ'‖_1 ≤ K√(2P)‖φ'‖_2` with `‖φ'‖_2² ≍ PE_x` by
Montgomery–Vaughan; the powers of `P` cancel. (Lean: `energy_le_of_amplifier`.)

**Theorem 76 (unconditional).** The same amplifier with Cauchy–Schwarz in `L²` gives
`(1/P)∫_{t_0}^{t_0+P}|S_F|² ≫ n_F\log\log P`: positive prime energy forces unbounded fluctuation, with
no zero-density estimate, no Selberg CLT and no RH.

**Theorem 77 (unconditional).** If `n_F = 0` then `Σ_n|Λ_F(n)|²/(n\log²n) < ∞`, so the expansion
`𝒮 = −(1/π)Σ_nΛ_F(n)n^{−1/2}\sin(t\log n)/\log n` converges in `B²`; since `S_F` and `𝒮` both satisfy
`∫φ'· = 𝒫[φ]`, they differ by a constant. Hence `S_F` is Besicovitch almost periodic with
`‖S_F − c‖²_{B²} = (1/2π²)Σ_n|Λ_F(n)|²/(n\log²n)` and bounded mean square uniformly in `t_0`.

**Theorem 78.** With the amplifier built from a second element `G`,
`Σ_{p≤x}a_F(p)\overline{a_G(p)}/p = (2πi/P)∫φ'_G S_F + o(1)`: the full complex Selberg pairing —
including the alternating form `ω`, invisible to all prime energies by Theorem 16 — is a pairing of
the **zeros of `F`** against the **primes of `G`**.

**Theorem 79 (unconditional).** For non-constant `F ∈ S` and any `c`,
`\liminf (1/T)∫_0^T|S_F − c|² ≥ 1/12`. *Proof:* `N_F` is integer-valued, so
`|S_F − c| ≥ \mathrm{dist}(M_F+c, Z)`; `d_F ≥ 1` gives `M_F'' ≠ 0`, so `\{M_F+c\}` equidistributes and
the mean of `\mathrm{dist}²` tends to `1/12`.

**Corollary 80.** `n_F = 0 ⟹ Σ_p|a_F(p)|²/p ≥ π²/6 − O(1) > 1`: the convergent prime energy cannot be
small.

**Corollary 81.** Equality in Theorem 79 holds iff `N_F = \mathrm{round}(M_F+c)`, i.e. iff the zeros are
exactly rigid; with Theorem 70 this gives strict inequality for every non-constant `F ∈ S`. The bound
`1/12` is attained exactly by the rigid configuration, which Theorem 70 shows is trivial.

## 11. The characteristic-function method (cycles 139–142)

Write `M\{g\} = \lim_T (1/T)∫_0^T g`. Integrality of the zero-counting function gives, for `F ∈ S`,
`e^{2πikS_F(t)} = e^{−2πikM_F(t)}(1+o(1))`, an identity, not an estimate.

**Theorem 84 (unconditional).** No non-constant `F ∈ S` has `Σ_p|a_F(p)|²/p < ∞`.
*(The hypothesis is convergence of the prime energy, which is strictly stronger than `n_F = 0`, i.e.
`Σ_{p≤x}|a_F(p)|²/p = o(\log\log x)`. The density-zero case is **not** covered; see Scope.)*
*Proof.* (A) `d_F ≥ 1` gives `M_F' = ν → ∞` monotonically, so van der Corput's first-derivative test
yields `M\{e^{2πikS_F}\} = 0`. (B) If `n_F = 0` then by Theorem 77 `S_F = c + 𝒮` with `𝒮 ∈ B²`;
truncating (`|M\{e^{2πik𝒮}\} − M\{e^{2πik𝒮_N}\}| ≤ 2πk‖𝒮−𝒮_N‖_{B²}`) and applying Weyl equidistribution
to the `Q`-independent frequencies `\log p` gives `M\{e^{2πik𝒮}\} = ∏_p I_p` with
`I_p = (1/2π)∫_0^{2π}\exp(2πikΣ_j A_{p^j}\sin(jθ+φ_{p^j}))dθ`. Since `1 − |I_p| = O(k²Σ_jA_{p^j}²)` and
`ΣA_n² < ∞`, the product converges; `A_p → 0` makes all but finitely many `I_p ≈ J_0(2πkA_p) ≠ 0`, and
the finitely many exceptions are real-analytic in `k` with value `1` at `k = 0`, so some integer
`k ≠ 0` makes the product non-zero. Contradiction. ∎
*Sharpness.* For `n_F > 0`, `ΣA_n² = ∞` makes the product vanish, matching (A) — no contradiction. The
check against `ζ` (where `Σ_p 1/p = ∞`) confirms the method does not overreach.

**Theorem 85 (quantitative strong multiplicity one; unconditional).** If `F, G ∈ S` have identical
gamma factors and conductors and `Σ_{p≤x}|a_F(p) − a_G(p)|²/p = O(1)`, then `F = G`.
*Proof.* `M_F = M_G` gives `S_F − S_G = N_F − N_G ∈ Z` pointwise, so `M\{e^{2πik(S_F−S_G)}\} = 1`. The
hypothesis puts the difference expansion in `B²`, so the same Weyl argument evaluates it as
`e^{2πikΔc}∏_p I_p`. Then `|∏_p I_p| = 1` with `|I_p| ≤ 1` forces every `|I_p| = 1` (Lean:
`norm_eq_one_of_prod_norm_eq_one`), which happens only when each local trigonometric polynomial is
constant, i.e. all coefficient differences vanish. ∎ Pole orders must agree under the hypothesis, so
entireness is not needed.

**Scope.** The geometric side of the method takes only the values `0` (single `F`, chirp `M_F`) and
`1` (pair with equal archimedean data, chirp cancels). It therefore decides exactly whether a prime
energy **converges**, settling `Σ_p|a_F(p)|²/p < ∞ ⟹ F = 1` and the corresponding statement for
`F/G`, and cannot produce a general integer — so it does not reach `n_F ∈ Z`. Two regimes are left
untouched and must not be conflated with the above: divergence with density zero
(`Σ_{p≤x}|a_F(p)|²/p → ∞` but `= o(\log\log x)`), and `0 < n_F < 1`. Every quantitative statement in
the divergent regime requires an upper bound for `(1/T)∫_0^T|S_F − 𝒮_N|²dt`, which is a zero-density
hypothesis and is not proved here.

**Theorem 89 (unconditional; the general form of Theorems 84, 85, 87).** Let `H = ∏_i F_i^{α_i}` be a
non-trivial element of the group completion of `S` (`F_i ∈ S`, `α_i ∈ Z`), with
`a_H(p) := Σ_i α_i a_{F_i}(p)`. Then `Σ_{p≤x}|a_H(p)|²/p → ∞`.
*(Divergence, not density: the case `Σ_{p≤x}|a_H(p)|²/p → ∞` with `= o(\log\log x)` is left open.)*

*Proof.* Put `X = Σ_iα_iS_{F_i} = (Σα_iN_{F_i}) − Φ(t)`, `Φ := Σα_iM_{F_i}`, the first bracket
integer-valued, so `e^{2πikX} = e^{−2πikΦ}(1+o(1))` for `k ∈ Z`. Stirling on
`γ(s) = Q^s∏_jΓ(λ_js+μ_j)` gives the **complete** asymptotic
```
Φ(t) = A\,t\log t + B\,t + C\log t + D + O(1/t),
A = \frac{Σα_id_i}{2π},\qquad C = \frac{1}{2π}Σ_iα_iθ_{F_i},\qquad θ_F := \mathrm{Im}\,ξ_F,\ \ ξ_F = 2Σ_j(μ_j−\tfrac12),
```
`B` being the conductor coefficient and `θ_F` the Kaczorowski–Perelli shift invariant. There are
**four** regimes:
```
A ≠ 0                 chirp          |M_T\{e^{2πikX}\}| → 0                       (van der Corput)
A = 0 ≠ B             pure tone      |M_T\{e^{2πikX}\}| → 0
A = B = 0, C ≠ 0      logarithmic    |M_T\{e^{2πikX}\}| → (1+4π²k²C²)^{−1/2} ∈ (0,1)
A = B = C = 0         constant       |M_T\{e^{2πikX}\}| → 1
```
the third from `T^{−1}∫_0^Te^{−2πik(C\log t+D)}dt = e^{−2πikD}T^{−2πikC}/(1−2πikC)`. It is non-empty:
`H = L(s+iθ_1,χ)/L(s+iθ_2,χ)` has `A = B = 0` and `C = (θ_1−θ_2)/2π ≠ 0`.

In every regime, boundedness of `Σ_{p≤x}|a_H(p)|²/p` puts the associated expansion in `B²`, and Weyl
equidistribution of the `Q`-independent frequencies `\log p` evaluates
`|M\{e^{2πikX}\}| = ∏_p|I_p(k)|` with `Σ_p(1−|I_p|) < ∞`. In regimes 1 and 2 the product is non-zero
for a suitable integer `k` while the geometric side is `0` — a contradiction. In regime 4,
`|∏_pI_p| = 1` with `|I_p| ≤ 1` forces every `|I_p| = 1` (`norm_eq_one_of_prod_norm_eq_one`), hence
every local trigonometric polynomial constant, hence `H = 1`. In regime 3 the identity
`∏_p|I_p(k)| = (1+4π²k²C²)^{−1/2}` must hold for **every** integer `k ≠ 0`; but
`√(1+4π²k²C²) ≤ 1+2π|C|k < 1+k²E ≤ \exp(k²E)` once `kE > 2π|C|`, so the polynomial profile on the
right cannot match the Gaussian profile `≈ e^{−k²E}` on the left unless `E = 0`, and then the left
side is `1` while the right side is `< 1` unless `C = 0`. Hence `C = 0`, every `a_H(p) = 0`, and
`H = 1`. (Lean: `HTGeometry.sqrt_lt_exp_of_energy_pos`, `HTGeometry.inv_sqrt_lt_one_of_ne_zero`.) ∎

**Corollary.** The additive map `H ↦ (a_H(p))_p` from the group completion of `S` has trivial kernel in
the strongest sense: no non-trivial element has prime coefficients square-summable against `1/p`.
Consequences: the `n = 0` stratum is empty throughout the group completion; quantitative strong
multiplicity one (Theorem 85) is the case `H = F/G`; and `\mathrm{Re}\,c_{F,G} < (n_F+n_G)/2` strictly
for distinct `F, G` sharing archimedean data (Theorem 86).

---

## 12. The amplifier: unconditional lower bounds for the zero-counting fluctuation

Throughout this section `F ∈ S` is entire and `E_x := Σ_{p≤x}|a_F(p)|²/p`.

**Admissibility.** In the Selberg class only **band-limited** test functions may be used in the Weil
explicit formula `∫φ'S_F = 𝒫[φ]`. If `φ ∈ C_c^∞(R)` then `\hatφ` decays only polynomially and the
prime side `Σ_nΛ_F(n)n^{−1/2}\hatφ(\log n) ≍ Σ_p p^{−1/2+ε}(\log p)^{1−A}` diverges. All amplifiers
below therefore take `\hatψ` compactly supported.

**Theorem 90 (exact amplifier).** Let `\hatψ` be supported in `[−1,1]`, `x ≥ 2`, `P > 2x`, `t_0 ∈ R`,
and `φ'(t) = Σ_{p≤x}\overline{a_F(p)}p^{−1/2}ψ((t−t_0)/P)e^{it\log p}`. Then

1. `\hatφ` is supported in `⋃_{p≤x}[\log p−1/P,\log p+1/P]`, a compact set with `0 ∉ \mathrm{supp}`;
2. the prime side is **exactly** the diagonal `n = p ≤ x`, because distinct positive integers satisfy
   `|\log n − \log m| ≥ 1/\max(n,m)` and `n > P ≫ x ≥ p` forces `\log n − \log p ≫ 1/P`; prime powers
   are excluded outright rather than estimated;
3. the archimedean main term vanishes (it carries `\hatφ(0)`);
4. `‖φ'‖_2² = P‖ψ‖_2²E_x` **exactly**, since the off-diagonal at `(p,p')` carries
   `\widehat{ψ²} = \hatψ*\hatψ` supported in `[−2,2]` and `|\log p − \log p'| ≥ 1/x > 2/P`.

(Lean: `HTGeometry.inv_max_le_abs_log_sub_log`, `HTGeometry.monomial_log_separation`.)

**Theorem 91 (unconditional).** `(1/P)∫|S_F(t)|²|ψ((t−t_0)/P)|²dt ≫_ψ E_x` for `P > 2x`; hence
`(1/T)∫_0^T|S_F|²dt ≫ E(T/2)`.

**Theorem 92 (unconditional).** Adding the rounding floor: `S_F − 𝒮_x = N_F − (M_F+𝒮_x)` with
`N_F ∈ Z`, so `|S_F−𝒮_x| ≥ \|M_F+𝒮_x\|`, and the chirp `M_F` (with `M_F'' ≠ 0`) makes `M_F+𝒮_x`
equidistribute mod `1`. Since the resolved band is exactly orthogonal to the residual (Theorem 90),
```
\frac1T∫_0^T|S_F(t)|²dt \;≥\; \frac{1}{4π²}Σ_{p≤x}\frac{|a_F(p)|²}{p} \;+\; \frac1{12} \;−\; o(1)
\qquad (x < T/2).
```
For `ζ`, Selberg's `(1/T)∫_0^TS² ∼ (1/2π²)\log\log T` shows the main term is sharp up to a factor `2`:
**the amplifier recovers half of Selberg's asymptotic for the whole Selberg class with no zero-density
input.**

**Theorem 93 (unconditional).** For every non-constant `F ∈ S`,
`\liminf_T (1/T)∫_0^T|S_F(t)|²dt = ∞`; in particular `S_F` is unbounded and `S_F ∉ B²`.
*Proof.* The Fourier–Bohr coefficients of `S_F` are exactly `\widehat{S_F}(\log n) =
−Λ_F(n)/(2πn^{1/2}\log n)` (phase suppressed) and vanish off `\{±\log n\}`; Bessel for Fourier–Bohr
coefficients (`\liminf_T(1/T)∫_0^T|f|² ≥ Σ_j|\hat f(λ_j)|²`, from expanding
`(1/T)∫|f−Σ\hat f(λ_j)e^{iλ_jt}|² ≥ 0` and `(1/T)∫e^{i(λ_j−λ_l)t} → δ_{jl}`) gives
`\liminf ≥ (1/4π²)E_N + O(1)` for every `N`; and `E_N → ∞` by Theorem 89. ∎
(Lean: `HTGeometry.oscInt_norm_le`, `HTGeometry.oscInt_gram_bound`,
`HTGeometry.bessel_of_almost_orthogonal`.)

For `ζ` the unboundedness of `S(t)` is classical (Selberg, via his zero-density theorem); here the
amplifier replaces that input, and the argument applies to every element of the class.

## 13. The mod-1 law, and the exact ceiling of the method

**Theorem 94 (complete mod-1 classification; unconditional).** With `A, B, C` as in the proof of
Theorem 89, the law of `X = Σα_iS_{F_i}` mod `1` for `t` uniform on `[0,T]` converges to: the uniform
law if `A ≠ 0` or `A = 0 ≠ B`; the rotates of `f_C(v) = e^{v/C}/(C(e^{1/C}−1))` if `A = B = 0 ≠ C`; a
point mass if `A = B = C = 0`. In particular `S_F` is uniform mod `1` for every non-constant `F ∈ S`,
while `S_{P_1}−S_{P_2}` for `P_j = L(s+iθ_j,χ)` is **exponentially (Benford-)distributed** mod `1`.
*Certificate.* `\int_0^1f_C(v)e^{−2πikv}dv = (1−2πikC)^{−1}`, matching the direct evaluation of
`T^{−1}∫_0^Te^{−2πikC\log t}dt`. (Lean: `HTGeometry.fourierCoeff_expDensity`.)

**Theorem 95 (the ceiling).** The total unconditional content of `e^{2πikS_F} = e^{−2πikM_F}` is:
*`S_F` is equidistributed mod `1` with discrepancy `O_F(1/T)`.* Every unconditional theorem of §11 and
Theorem 94 follows from this; and no statement about the *unwrapped* law of `S_F` — in particular no
value or rate for `n_F` — does. Consequently the method decides exactly whether a prime energy
converges, and the optimal dual frequency for a rate, `k ≍ E^{−1/2} < 1`, is inadmissible because
`e^{2πikN_F} = 1` requires `k ∈ Z`.

**Corollary 96.** With the Selberg-CLT variance `σ² = (n_F/2π²)\log\log T`, a Gaussian would give
`|Ψ_T(1)| = (\log T)^{−n_F}`, whereas in fact `|Ψ_T(1)| = O(1/T)`: the law of `S_F` is uniform mod `1`
to a precision exceeding the Gaussian prediction by a factor `T(\log T)^{−n_F}`. The excess is purely
archimedean, so the Gaussian model — accurate for the unwrapped law — is badly wrong at the mod-1
scale.

## 14. Low degree

**Theorem 97 (unconditional).** If every primitive factor of `F ∈ S` has degree `1`, say
`F = ∏_iP_i^{m_i}` with the `P_i` distinct, then Selberg's Conjecture B holds for every pair
`(P_i,P_j)` and `n_F = Σ_im_i² ∈ Z_{≥1}`.
*Proof.* Degree-`1` elements of `S` are `ζ` and `L(s+iθ,χ)` (Kaczorowski–Perelli), and
`Σ_pa_{P_1}(p)\overline{a_{P_2}(p)}p^{−w} = \log L(w+i(θ_1−θ_2),χ_1\barχ_2)+O(1)` is bounded at `w=1`
unless `P_1 = P_2`, by non-vanishing of `L` on the `1`-line. ∎

**Corollary 98.** Since no element of `S^♯` has degree in `(0,1)∪(1,2)` and degree-`0` elements are
`≡1`, **Conjecture A holds unconditionally for every `F ∈ S` with `d_F ≤ 2` except possibly primitive
elements of degree exactly `2`, for which it asserts precisely `n_F = 1`.**

**Remark (what is still open below Conjecture A).** No unconditional bound
`\limsup_x E_x/\log\log x < ∞` is known: even *finiteness* of `n_F` is open. The best available is
`E_x ≪ \log²x`. A bound `Σ_{n≤x}|a_F(n)|² ≪ x(\log x)^{C}` would give `n_F ≤ C+1` and is equivalent,
via the approximate functional equation, to `∫_0^T|F(1/2+it)|²dt ≪ T(\log T)^{C}` — the Rankin–Selberg
problem.

## 15. Corrections to earlier drafts

Recorded for the reader of previous versions.

1. The separation used in Theorem 13 was stated as `|k\log q − j\log p| ≫ (\log X)^{−C}` "by Baker's
   theorem". That is false where it is used (twin primes `p,q = p+2 ≤ X` give `≍ 1/X`); a
   `(\log X)^{−C}` gap holds only for perfect powers with both exponents `≥ 2`. The correct and sharp
   input is elementary, `|\log d − \log e| ≥ 1/\max(d,e)`, so the smoothing parameter is `δ = 1/X`.
   **No transcendence theory is used anywhere in this paper.**
2. Theorems 84 and 89 were stated with "equivalently `n_F = 0 ⟹ F = 1`". Convergence of
   `Σ_p|a_F(p)|²/p` is strictly stronger than `n_F = 0`; the density-zero case is not covered.
3. The proof of Theorem 89 listed three archimedean regimes. The expansion of the archimedean phase
   was one term short: the term `C\log t`, with `C` proportional to the shift invariant `θ_F`, gives a
   **fourth** regime, realised by `L(s+iθ_1,χ)/L(s+iθ_2,χ)`. The corrected proof appears above; the
   statement is unaffected.
4. The amplifier of §12 was previously taken compactly supported in `t`, which is inadmissible
   (divergent prime side). The band-limited form is used here and makes the amplifier exact.

---

## 16. The sharpest reduction: Conjecture A from one linear density

Write `δ_1(g) := \lim_x(\log\log x)^{−1}Σ_{p≤x}g(p)/p`, the logarithmic density at the scale `p^{−1}`.
One instance is unconditional (Theorem 52 plus a Tauberian step):
```
δ_1\big(p ↦ a_G(p)\big) = −\,\mathrm{ord}_{s=1}G ∈ Z        for every G ∈ S^♯ .
```

**Theorem 99.** For arithmetic functions with `a(1) = 1` and `p` prime,
`a_{FG}(p²) = a_G(p²) + a_F(p)a_G(p) + a_F(p²)`; hence
```
|a_F(p)|² = a_{F\bar F}(p²) − a_F(p²) − \overline{a_F(p²)} .
```
(Lean: `RHTower.selberg_pairing_prime_sq`.) A degree-free cross-check from Newton's identities,
`p_1² = 2h_2 − p_2` with `h_2(α(p)) = a_F(p²)` and `p_2(α(p)) = 2b_F(p²)`, gives
`a_F(p)² = 2a_F(p²) − 2b_F(p²)` (Lean: `HTGeometry.newton_sq_identity`; checked on `ζ`:
`2·1 − 2·½ = 1`, and on a `GL_2` newform: `2(a²−1) − (a²−2) = a²`).

**(PSD₂).** *For every `G ∈ S`, `δ_1\big(p↦a_G(p²)\big) ∈ Z`.*

**Theorem 100.** **(PSD₂) ⟹ Selberg's Conjecture A**, via
`n_F = δ_1(a_{F\bar F}(·²)) − 2\,\mathrm{Re}\,δ_1(a_F(·²))`.

Since `a_G(p²) = h_2(α(p))` is the character of `\mathrm{Sym}²` on the Satake class,
`Σ_pa_G(p²)p^{−s}` differs from `\log L(s,\mathrm{Sym}²G)` by a function holomorphic on
`\mathrm{Re}\,s > 1/2`, so

> **(PSD₂) ⟺ `S` is closed under `\mathrm{Sym}²` in the monodromy-only sense of MI.**

This is strictly weaker than MI as stated in §1: MI asks meromorphy of the **bilinear** `R_{F,G}` for
all pairs (degree `d²`); (PSD₂) asks only for the **unary** operation `\mathrm{Sym}²`
(degree `d(d+1)/2`) applied to each element separately. The quadratic-versus-additive obstruction of
Theorem 4 is bypassed: the quadratic datum `a_F(p)\overline{a_F(p)}` is absorbed into the *linear*
coefficient `a_{F\bar F}(p²)` of the auxiliary element `F\bar F ∈ S`.

**Sanity checks.** `F = ζ`: `a_{ζ²}(p²) = 3`, `a_ζ(p²) = 1`, so `n_ζ = 3 − 2 = 1` ✔. `GL_2` newform
of trivial nebentypus: `a_F(p²) = a_{\mathrm{sym}²}(p)` with `Σ_pa_{\mathrm{sym}²}(p)p^{−s}` regular
at `s = 1`, so `δ_1(a_F(·²)) = 0`, and `δ_1(a_{F\bar F}(·²)) = n_F` ✔.

**Low degree.** Combined with §14: **Conjecture A holds unconditionally for every `F ∈ S` with
`d_F ≤ 2` except possibly primitive elements of degree exactly `2`, where it is the single statement
`δ_1(a_F(·²)) = 1 − δ_1(\det)`.**

## 17. Sharpness of the standard twist in the `α`-aspect

A by-product of the two-variable analysis of §16's obstruction.

**Corollary 101.** Let `G ∈ S` have degree `2` and `δ_1(a_G(·²)) ≠ 0` (e.g. `G = ζ²`, where the
density is `3`). Then **no** bound `Φ_G(s,α) ≪_s α^{−1/2−δ}` with `δ > 0` holds uniformly for
`α ∈ \mathrm{Spec}(G)` and `s` in a punctured neighbourhood of `s^*_0 = 3/4`.
*Proof sketch.* Such a bound would make `Σ_p p^{−w}Φ_G(s,α_p)` converge at `w = 1/2`, hence make
`Σ_p\overline{a_G(p²)}p^{−s'}` holomorphic at `s' = 1` and `δ_1(a_G(·²)) = 0`. ∎

So the decay exponent `−1/2 = 2(s^*_0 − 1)` is sharp and is saturated by the residues
`ρ_0(α_{p²}) ∝ \overline{a_G(p²)}p^{−1/2}` themselves.

## 18. Scope: what the axioms cannot do

The obstruction to (PSD₂), stated at maximum resolution. `\log G` supplies
`Σ_pΣ_j b_G(p^j)p^{−js}`: the `j`-th character datum at weight `p^{−js}`, singular at `s = 1/j`.
Conjecture A needs the same data at weight `p^{−s}`, singular at `s = 1`. Only `j = 1` has the two
scales agreeing — which is exactly why the linear densities are integers and nothing else is. The
rescaling `G(s) ↦ G(s/j)` is harmless; what fails is the **sieve**, the extraction of one `j`-graded
piece, and it fails in four independent ways: (i) no fixed combination `Σ_mc_m\log G(ms)` isolates a
single `j`, since the `p^{−js}`-coefficient is the `G`-independent mixture `Σ_{m|j}c_mb_G(p^{j/m})`;
(ii) the per-prime even-part extraction does not globalise, an average of products not being a product
of averages; (iii) squares are not a union of congruence classes, so no character detects them; (iv)
argument rescaling `G(s/2)` places the wrong coefficients at the wanted frequencies. Sieve and
rescale together are exactly the operation `F ⊗ \bar F`, and their absence is Langlands functoriality.

---

## 19. The square-index series and the standard twist

Throughout this section `G ∈ S` has degree `2` and conductor `q`; `Φ_G(s,z) = Σ_m a_G(m)e(z\sqrt m)m^{−s}`
is the Kaczorowski–Perelli twist, holomorphic for `z ∈ H` and with the standard twist as boundary value.

**Theorem 102 (damped twist; unconditional).** For every `y > 0` and every `s ∈ C`,
`Φ_G(s,−α+iy) = Σ_m a_G(m)e(−α\sqrt m)e^{−2πy\sqrt m}m^{−s}` converges absolutely, and for every
integer `n ≥ 1`
```
\lim_{A→∞}\frac1A∫_0^A Φ_G(s,−α+iy)\,e(αn)\,dα \;=\; a_G(n²)\,e^{−2πyn}\,n^{−2s} .
```
*Proof.* The damping beats every polynomial, so the series may be integrated term by term, and
`\frac1A∫_0^Ae(α(n−\sqrt m))dα → [m = n²]`. ∎

**Theorem 103 (integer sampling; unconditional).** For every `y > 0`,
```
Σ_{n≥1} a_G(n²)\,e^{−2πyn}\,n^{−1} \;=\; \lim_{A→∞}\frac1A Σ_{k≤A}Φ_G\big(\tfrac12,−k+iy\big) ,
```
by Weyl equidistribution of `(k\sqrt m)_k` for non-square `m`. Moreover the contribution of the spectral
singularities to the right-hand average is `O\big((Ay)^{−1/2}\big) → 0`: the quantity is carried entirely
by the regular part of the twist at integer arguments.

**Corollary 104.** `(PSD₂)` for `G` — hence, by §16, Conjecture A for every `F ∈ S` with `d_F ≤ 2` — is
equivalent to
```
Σ_{n≥1} a_G(n²)\,e^{−2πyn}\,n^{−1} \;=\; κ\,\log(1/y) + O(1) \qquad (y → 0^+),\quad κ ∈ Z ,
```
the Abel-regularised form of the prime-square density (equivalent to the logarithmic form by
Hardy–Littlewood, the coefficients being `≪ n^{ε−1}`).

**Remark (why degree 1 is different).** For `d = 1` the twist `Σ_mχ(m)e(αm)m^{−s}` is *periodic* in `α`,
its Bohr means are ordinary Fourier coefficients `∫_0^1`, and `y → 0` commutes with integration over a
compact interval by dominated convergence. Directly, `D_G(s) = Σ_nχ(n)²n^{−s} = L(s,χ²)`, so `(PSD₂)`
holds. For `d ≥ 2` the frequencies `\sqrt m` are irrational, the twist is only almost periodic, the
averaging interval is infinite, and dominated convergence is unavailable. Equivalently: detecting
squares requires an additive twist at exponent `1`, while the Selberg axioms resonate only at exponent
`1/d`; the two coincide exactly when `d = 1`.

**Remark (what is *not* an obstruction).** Three quantities that might be expected to obstruct the
above are bounded: the spectral singularity exponent is `d(\tfrac12 − s^*_0) = −\tfrac12` for **every**
degree, hence locally integrable; the absolute Bohr mean of the singular part is `O(A^{ε})`; and the
off-diagonal in Theorem 102 is `O(A^{ε−1})`. The local expansion C7.1 is *not* uniform over the
spectrum — its radius of validity is the spectral gap `≍ 1/α` — but Theorem 103 avoids any use of
uniformity by taking `A → ∞` before `y → 0`.

---

## 20. Bounded Satake parameters and the energy bound `n_F ≤ d_F²`

**Theorem 105.** Let `F ∈ S` have a polynomial Euler product of local degree `∂_p ≤ d` with Satake
parameters `|α_j(p)| ≤ 1`. Then `|a_F(p)| ≤ d` for every `p`, hence
```
\limsup_{x→∞}\ \frac{1}{\log\log x}Σ_{p ≤ x}\frac{|a_F(p)|²}{p} \;≤\; d^{\,2} .
```
Equality in the density forces `α_1(p) = \cdots = α_d(p)` of modulus `1` for almost all `p`, i.e.
`F = P^{d}` with `\deg P = 1`; so for `F` primitive of degree `d ≥ 2` the inequality is strict.
(Lean: `HTGeometry.norm_sum_le_card`, `HTGeometry.norm_eq_one_of_norm_sum_eq_card`,
`HTGeometry.weighted_sq_le`.)

**Corollary 106.** For `F ∈ S` of degree `2` and conductor `1`, the hypotheses of Theorem 105 hold
**unconditionally**: Kaczorowski–Perelli (*Twists, Euler products and a converse theorem for
`L`-functions of degree 2 in the Selberg class*, arXiv:1207.2312, Theorem 1 and its Corollary) prove
that the local factors have the form `∏_{j≤∂_p}(1−α_j(p)p^{−s})^{−1}` with `|α_j(p)| ≤ 1` and
`∂_p ≤ 2`. Hence `n_F ≤ 4`, and `n_F < 4` for `F` primitive. **In particular `n_F` is finite** — a
question left open in general by §18.

**Remark (scope).** The polynomial-Euler-product and bounded-Satake hypotheses, which are assumptions
throughout §§1–19, are therefore theorems in `S_2` with conductor `1`. In that subclass one also has,
from the same paper: the sharp transformation formula for **linear** twists,
`α ↦ −1/(q_Fα)` (Theorem 2); meromorphy on `C` of every linear twist at a rational, holomorphic for
`σ < 1` (Theorem 3); and the converse theorem that `ζ(s)²` is the only element with a pole at `s = 1`
(Theorem 4), so every other element of the subclass is entire.

**Consequence for §16.** With `∂_p ≤ 2` and `|α_j| ≤ 1` available, Theorem 99's hypotheses reduce to
self-duality together with the assumption that the local determinant `α_1(p)α_2(p)` is the value of a
Dirichlet character; and in the unitary case
```
n_F = 2 + 2\,\mathrm{Re}\,δ_1\big(p ↦ α_1(p)\overline{α_2(p)}\big) ,
```
so Conjecture A for such `F` is exactly `δ_1(α_1\barα_2) ∈ \tfrac12Z`, with `(P1)` the assertion
`\mathrm{Re}\,δ_1(α_1\barα_2) = −\tfrac12`. The outer bounds `0 ≤ n_F ≤ 4` are unconditional.

---

## 21. [WITHDRAWN]

An earlier version of this section derived Wilton's bound for `F ∈ S_2` with `q_F = 1` from
Kaczorowski–Perelli's transformation formula for linear twists, on the reading that the error term of
their Theorem 2 satisfies `H_K ≪ (A/K)^{K}` and is therefore negligible for large `K`. The arXiv source
of that paper gives `H_K(s,α) ≪ (AK)^{K}`, which grows with `K`; the formula transports holomorphy on
an expanding region (which is how the authors use it), not size. The argument of this section is
therefore withdrawn. Sections 16–20 are unaffected.

## 23. The duality operator in degree two, and self-referential twist identities at conductor 2 and 3

Kaczorowski–Perelli's transformation formula for nonlinear twists applies to
`F(s;f) = Σ a_F(n)n^{−s}e(−f(n,α))` whenever the leading exponent `κ_0` of `f` exceeds `1/d`:
```
F(s;f) = Σ_{j=0}^{J} W_j(s) F̄(s^* + η_j; f^*) + G(s;f),   G holomorphic for σ > −K,
s^* = (s + dκ_0/2 − 1 + i d θ_F κ_0)/(dκ_0 − 1),   f^* = T^♭(f),
T(f)(ξ,α) = (4π²i)^{−1} ∮_C Φ Φ_zz/Φ_z dz,   Φ(z,ξ,α) = z^{1/d} − 2π f(qz/ξ,α),  q = q_F(2πd)^{−d},
```
with `T² = id` and `T(f) := −T(−f)` when the leading coefficient of `f` is negative. The shift
`S(f) = f + P(ξ)`, `P ∈ Z[ξ]`, acts trivially on twists but not on `T`.

### 23.1 Closed form of `T` in degree two

**Lemma 23.1.** Let `d = 2`, `q_F = Q`, and `f(ξ,α) = cξ + γξ^{1/2}` with `c ≠ 0`. Then
```
T(f)(ξ,α) = [ ξ − sgn(c)·γ√Q ξ^{1/2} + γ²Q/4 ] / (cQ),   i.e.
c ↦ 1/(cQ),        γ ↦ −γ/(|c|√Q),
```
plus an additive constant `γ²/(4c)` in the phase.

*Proof.* Assume first `c > 0`. With `u = z^{1/2}` one has `Φ = a u − b u²`,
`a = 1 − 2πγ√q ξ^{−1/2}`, `b = 2πcqξ^{−1}`, hence `Φ_z = (a−2bu)/(2u)` and `Φ_{zz} = −a/(4u³)`, so
`ΦΦ_{zz}/Φ_z = −a(a−bu)/(2u(a−2bu))`. Since `dz = 2u du`, the contour integral equals
`∮ −a(a−bu)/(a−2bu) du = 2πi·a²/(4b)`, giving `T(f) = a²/(8πb)`. Substituting and using
`16π²q = q_F = Q`, `4π√q = √Q` yields the display. For `c < 0` apply this to `−f` and negate. ∎

Two checks. `T² = id`: `c ↦ 1/(cQ) ↦ c` and `γ ↦ −γ/(|c|√Q) ↦ γ`. And at `Q = 1`, `c = 1` the operator
fixes `c` and sends `γ ↦ −γ`, i.e. the dual of the standard twist is the standard twist at `−α`. **That
is exactly the coincidence which makes the conductor-one theory work**, exhibited here as the statement
that `c = 1` is a fixed point of `c ↦ 1/(cQ)` precisely when `Q = 1`.

### 23.2 Loops

Since `F(s; cξ + γξ^{1/2}) = F(s,γ)` exactly when `c ∈ Z ∖ {0}`, define a **loop** to be a chain
`c_0 = 1 → c_1 → ⋯ → c_r ∈ Z` with `c_{i+1} = 1/(Q(c_i + m_i))`, `m_i ∈ Z`, and call it **proper** when
`m_i ≠ 0` for `1 ≤ i ≤ r−1` (otherwise two consecutive dualities cancel). Its **weight** is the factor
by which `γ` returns; writing `γ_i = t_iα/(√Q)^i` the track is `t ↦ −t/|c|` and the weight is
`t_r/Q^{r/2}` for even `r`.

**Theorem 134.** The chains
```
Q = 2:   1 →(0)→ 1/2 →(−1)→ −1,                    t : 1, −1, 2,          weight 2/2 = 1;
Q = 3:   1 →(0)→ 1/3 →(−1)→ −1/2 →(1)→ 2/3 →(−1)→ −1,  t : 1, −1, 3/2, −3, 9,  weight 9/9 = 1
```
are proper loops of even length and weight `1`. At `Q = 4` there is no proper loop of length `2` or `4`:
length `2` needs `|1+4m_1| = 1` with `m_1 ≠ 0`, and length `4` forces `|B_2| = 1` and then `m_2 = 0`.

### 23.3 The identity

**Theorem 135.** Let `F ∈ S^♯` have degree 2 and conductor `Q ∈ {2,3}`, and let `α ∈ Spec(F)`. Then for
every integer `M ≥ 0`
```
F(s,α) = Σ_{m=0}^{M} W_m^{(Q)}(s,α) F(s + η_m, α) + H_M(s,α),
```
where `W_0^{(Q)} ≡ 1`, the shifts `0 = η_0 < η_1 < ⋯` and the coefficients of the polynomials
`W_m^{(Q)}` depend only on `Q` (and are linear in the structural invariants `d_F(ℓ)`), and `H_M(s,α)` is
holomorphic for `σ > −(M−1)/2`.

*Proof.* Compose the transformation formula along the loop of Theorem 134. Both endpoints have integer
linear coefficient, so both ends are the standard twist; the intermediate shifts act trivially on
twists; the length is even, so the composite maps `F` to `F` and the accumulated shift
`2iθ_F − 2iθ_F + ⋯` vanishes (conjugation reverses the internal shift); and the weight is `1`, so the
twist parameter returns to `α`. The `W_j` of the transformation formula are `e^{a_js}P_j(s)` with
`deg P_j ≪ j`, a shape stable under composition along a fixed finite chain. ∎

**Corollary 136.** Since the `m = 0` term cancels the left-hand side,
`Σ_{m≥1}W_m^{(Q)}(s,α)F(s+η_m,α)` is holomorphic for `σ > −(M−1)/2`; requiring its residue to vanish at
each pole `s_M` of the standard twist gives, for every `α ∈ Spec(F)` and hence identically in `α`, a
universal family of quadratic relations among the structural invariants `d_F(ℓ)`. Consequently all
`d_F(ℓ)` are determined by `d_F(1) = χ_F − 1/8`, and `χ_F` determines `(ω/ω_F)h_F(s)`.

This is the conductor-2 and conductor-3 analogue of the first step of the conductor-1 classification.
What remains, for the classification itself, is the non-degeneracy of the leading coefficient of the
resulting quadratic form, and then the virtual-`γ`-factor and period-function steps for the groups
`Γ_0(2)^+ ≅ G(√2)` and `Γ_0(3)^+ ≅ G(√3)`.

### 23.4 Formalisation

`formal/GaloisForLFunctions/HTGeometry/DualityLoopWeights.lean`: `cStep`, `tStep`, `cStep_cStep`,
`tStep_tStep` (both involutions), `dualityLoop_two`, `dualityLoop_three` (the two loops, with their
weights), `no_proper_length_two_loop_four`, `proper_length_two_loop_two`, `cStep_four_fixed`.
