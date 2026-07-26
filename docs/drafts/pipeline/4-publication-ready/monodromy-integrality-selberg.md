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

**Theorem 84 (unconditional).** No non-constant `F ∈ S` has `Σ_p|a_F(p)|²/p < ∞`; equivalently
`n_F = 0 ⟹ F = 1`.
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
energy vanishes, settling `n_F = 0 ⟹ F = 1` and `n_{F/G} = 0 ⟹ F = G`, and cannot produce a general
integer — so it does not reach `n_F ∈ Z`.
