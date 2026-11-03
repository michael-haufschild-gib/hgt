# The Window Tower of Spec ℤ (WTZ)

Namespace `GaloisForLFunctions.WindowTowerOfSpecZ`; umbrella `WindowTowerOfSpecZ.lean`; 40 modules.
Every theorem is unconditional; none assumes or proves RH.

## 1. Motivation

Weil's criterion has become a statement about **windows**: RH holds iff Weil's form `Q` is
nonnegative on every test supported in `[−A, 0]`, for every length `A`. One window is a finite
problem: it reads only the prime powers `n ≤ e^A`, its negative index is finite, and its form is
archimedean jumps, one fold per active prime power, a canonical class and a pole plane (CWS). RH is
not a property of one window. It is **uniformity in `A`**: a law valid along the whole tower
`A ↦ W_A` as the length grows and the integers enter one at a time.

Three proved laws fix the shape of what is missing (CWS, ACS, LST): the window `h¹` has no
finite-dimensional realization; its effective rank grows like `2e^A`; counts pay everything except
the primitive part `½Q`. Over `𝔽_q` this situation is resolved by towers of growing rank with
control theorems (base change along `𝔽_{q^m}`, Iwasawa theory), not by one variety. WTZ is the
theory of the window tower of `Spec ℤ` as such: the algebra acting on a window, the transitions
between windows and their control, the Tate pieces and the one non-Tate piece, the lattice carrying
the sections, the growth law in `A`, and the place where selection has to happen.

## 2. Objects

| Object | Lean | Meaning |
|---|---|---|
| Window module | `windowSupported A` | real functions vanishing off `[−A, 0]`; `F_A ⊆ F_B` for `A ≤ B` |
| Window shift | `windowShift t` | `(T_t H)(u) = 1_{u≤0} H(u − t)`: the fold by `t`, cut at the right end |
| Window representation | `windowRep A`, `windowRepFun` | `ρ_A(f)H = Σ_{n≤e^A} f(n)n^{−1/2}T_{log n}H`, a ring map from arithmetic functions to `End(F_A)` |
| Truncation ideal, window algebra | `truncIdeal N` | `I_N = {f : f = 0 on [1,N]}`; window algebra `D_N = 𝒜/I_N`, `N = ⌊e^A⌋` |
| Basis functions | `single n c` | `c·δ_n`, the fold `T_n` as an element of the algebra |
| Position, Tate twist, Tate flow | `positionOp`, `tateTwist c`, `tateTwistHom c` | `(MH)(u) = uH(u)`; `f ↦ f·n^{−c}`, a ring automorphism, implemented by `e^{cu}` |
| Window zeta, Möbius, von Mangoldt operators | `windowRep A ζ`, `windowRep A μ`, `windowRep A Λ` | `Z = Σ T_n`, its inverse, its logarithmic derivative |
| Euler datum, Tate family | `tateFamily F G k` | `F * G = 1`; `J^F_k = twist_{−k}(F) * G` |
| Jordan family | `jordanFun k` (ADT `jordanTotient`) | `J_k = J^ζ_k`, `J_k(m) = Σ_{d∣m}μ(m/d)d^k = #primitive vectors of (ℤ/m)^k` |
| Tate function | `tateFunction A H k` | `τ_H(k) = ⟨ρ_A(J_k)H, H⟩`, an exponential polynomial in the dimension `k` |
| Flip datum, shifted datum | `flipDatum p`, `shiftedDatum ε` | `ζ(s)(1 − p^{−s})²`; `ζ(s)ζ(s − ε)` |
| Atoms, atomic embedding | `atom N φ m`, `atomicEmbedding N φ g`, `IsAtomProfile` | `b_m(u) = φ(u + log N − log m)` at `log(m/N)`; `ι(g) = Σ_{m≤N} g(m)m^{−1/2}b_m` |
| Window bundle | `windowBundleH0 N`, `windowBundleDualH0 N` | `ℰ_N = ⊕_{m ≤ N} 𝒪(½ log m)`, `h⁰(ℰ_N, d) = Σ_{m≤N} h⁰_ℤ(d + ½ log m)` |
| Centred pole plane | `centredCosh A`, `centredSinh A` | `2cosh((u + A/2)/2)`, `2sinh((u + A/2)/2)` |
| Sharp window floor | `sharpWindowFloor A` | `deg K_A + 2 sinh(A/2) − A` |
| Exponentially weighted floor | `exponentialWeilFloor p` | `|Ω(0)| + 2ΣΛ(n)n^{−(p+1)/2} + 1/(p+1) + 1/(p−1)`; finite for `p > 1`, independent of aperture |
| Dilation, Adams lift | `dilate r`, RHTower `mPart e` | `(D_rH)(u) = H(u/r)`; `ψ^e f(n^e) = f(n)`, zero off `e`-th powers |
| Twist, character Euler datum | `twist c`, `twistHom`, `charZeta c`, `charMoebius c` | `f ↦ f·c` for completely multiplicative `c`; `(χζ, χμ)`, the Euler datum of `L(s, χ)` |
| Stage datum | `stageForm N` | Weil's form of the weight truncated at `N`: `M_N + ½⟨c,·⟩² − ½⟨s,·⟩²` |
| Collars, exit tail | `collarWeight A ε`, RHTower `archLevyAntideriv` | `1_{[−ε,0]} + 1_{[−A,−A+ε]}`; `Ω(ε) = ∫_ε^∞ ω`, the Gamma factor's exit tail |
| Factored indicator, Euler factor | `factoredIndicator s`, `eulerInverse p`, `primesUpTo N` | `e_s` = indicator of the integers with prime factors in `s`; `e_{{p}} = (1 − δ_p)^{−1}` |
| Exit potential, end profile, window potential | `exitPotential A`, `endProfile`, `windowPotential A` | `e_A(u) = Ω(−u) + Ω(A+u)`; `φ(t) = Ω(t) − ψ_{1/2}(e^t)`; `V_A = Ω_Γ + e_A − k_A` |
| Adjoint shift | `adjointShift A t` | `(T_t^*H)(u) = 1_{u≥−A}H(u + t)`, the shift toward the left end |
| Stage of a function | `VanishesBelow a f` | `f(n) = 0` for `n < a`: the fold starts acting at stage `a` |
| `Ω`-filtration, almost primes | `omegaVanishing k`, `omegaAtLeast k N`, `almostPrimesUpTo k N` | `f = 0` where `Ω(n) < k`; the `n ≤ N` with `Ω(n) ≥ k`, `= k` |
| Degree derivation, prime-power logarithm, truncated exponential | `degD`, `primePowerLog`, `expTrunc L g` | `Df = f·log`; `ℓ = Λ/log`; `Σ_{j≤L} g^j/j!` |
| Tate exponent | `tateExponent k` | `g_k = ℓ(n^k − 1)`, `g_k(p^a) = #(𝔸^k∖0)(𝔽_{p^a})/a`; `J_k ≡ exp g_k` |
| Generalized von Mangoldt functions, jets | `genVonMangoldt j`, `logPow j`, `tateJet j n k` | `Λ_j = log^j * μ`; `k ↦ Σ_{d∣n}μ(n/d)(log d)^j d^k` |
| Tate count of the modulus | `absTateCount A H k` | `Σ_{n≤e^A} J_k(n)n^{−1/2}∫|H(u)||H(u + log n)|` |
| Weighted norm | `weightNorm N f` | `W_N(f) = Σ_{n≤N} f(n)/√n`, submultiplicative on nonnegative functions |
| Prime indicator, prime part of `Λ`, plethystic logarithm | `primeIndicator`, `primeLog`, `plethLog L f` | `P`, `P_log = Λ·1_{primes}`, `Σ_{a≤L} ψ^a(f)/a` |
| Rational lattice | `ratLattice S x φ y` | `Σ_{r∈S} y_r φ(· − x − log r)`: amplitudes on a finite configuration of positive rationals |
| Picone jump weight | `piconeWeight A h y u` | `2 − (G(u + y) + G(u − y))/h(u)` on the window: the jump `y` seen from a ground state `h` |
| Window gate, path weight | `windowGate A h`, `pathWeight A t`, `innerRegions A` | `h` restricted to the window; the Perron weight of the second-stage path (`t` on `[−A, −log 3] ∪ [log 3 − A, 0]`) |

From CWS: `IsWindowTest`, `windowLevel = ⌊e^A⌋`, `foldEnergy`, `canonicalDensity`, `halfChebyshev`,
`canonicalDegree`, `windowIndex`, `windowGenus`, `exists_flip_twin_of_window`.

## 3. Language

- **Tower**: `A ↦ (F_A, ρ_A, Q|_{W_A})`; **level** `N = ⌊e^A⌋`; **stage** `n`: `log n ≤ A < log(n+1)`.
- **Transition**: the truncation `D_{N+1} → D_N` on algebras, the inclusion `F_A ⊆ F_B` on modules.
- **Small extension**: a surjection of local algebras whose kernel is killed by the maximal ideal
  `m = I_1 = {f : f(1) = 0}`. **Socle element**: an element killed by `m`.
- **Loewy length**: the least `k` with `m^k = 0`. **Cotangent space**: `m/(m² + I_N)`.
- **Tate flow**: the one-parameter group of twists `f ↦ f·n^{−c}`; its generator is the degree
  derivation `f ↦ f·log`, i.e. the commutator with the position.
- **Tate piece**: a value of a Tate family at a positive integer dimension. **Non-Tate piece**: the
  derivative at dimension `0`. **Tate positive**: all Tate pieces are `≥ 0`.
- **Atomic lattice**: the integers `m ≤ e^A`, embedded as atoms.
- **Orbit graph**: a finite set of window points `x + Σ a_p log p` joined by the folds that map one to
  another; arithmetic window forms decompose over orbit graphs. **Horizon**: the largest dimension `k`
  with `ρ_A(J_k) ≥ 0`.
- **Picone weight**: a positive function `h` on the window; AM–GM against `h` bounds each fold by the
  `h`-ratios of the points it links (a ground-state transform for the arithmetic jumps).
- **Soft**: true for data with off-line zeros (shifted products, flip twins, Epstein lattices).
  **Selective**: fails on such data.

## 4. Mechanisms

**A. The window algebra.** Compressions of translations by nonnegative amounts to an interval
compose exactly and vanish past its length: `T_sT_t = T_{s+t}`, `T_t = 0` on `F_A` for `t > A`. So
the Hecke shifts `n^{−1/2}T_{log n}` turn Dirichlet convolution into composition, and `ρ_A` is a ring
homomorphism whose kernel is exactly `I_{⌊e^A⌋}`: **the window algebra is the Dirichlet ring
truncated at the level**. The degree derivation is the commutator with the position,
`Mρ_A(f) − ρ_A(f)M = ρ_A(f·log)`; Tate twists are conjugations by `e^{cu}`. Hence
`ρ_A(Λ) = [M, Z]Z^{−1}`, `Z = ρ_A(ζ)`, equivalently `Z M Z^{−1} = M − ρ_A(Λ)` (the window zeta
operator conjugates the position into position minus von Mangoldt), and

`Q(H) = Ω(0)‖H‖² + J_∞(H) − 2⟨ρ_A(Λ)H, H⟩ + ½⟨c,H⟩² − ½⟨s,H⟩²`.

**B. The tower and its control.** The modules nest equivariantly (`ρ_B = ρ_A` on `F_A`). The
algebras form an inverse system of local Artinian rings with limit the full Dirichlet ring. Each
transition is a small extension with one-dimensional kernel spanned by the new fold `δ_{N+1}`
(`I_M·m ⊆ I_{2M+1}`); on windows shorter than `log 2n` the new fold `T_n` composes to zero with every
element of `m`. The maximal ideal satisfies `m^k ⊆ I_{2^k−1}`, sharply: any `k` folds compose to zero
on windows shorter than `k log 2`, and `T₂^{k−1}` survives on longer ones. The cotangent space has the
primes `≤ e^A` as a basis: the primes generate every window algebra; prime powers and composites
are products. More precisely the `m`-adic filtration is the filtration by the number of prime
factors: `m^k + I_N` is the set of functions vanishing on the `n ≤ N` with `Ω(n) < k`, and `gr_k` has
the `k`-almost primes `≤ N` as a basis. **The Hilbert function of the window algebra is Landau's
count** `π_k(N) = #{n ≤ N : Ω(n) = k}`; embedding dimension `π(N)`, Loewy length `⌊log₂ N⌋ + 1`. The
socle (the part killed by `m`) is spanned by the `δ_n` with `N/2 < n ≤ N`, so the type of `D_N` is
`⌈N/2⌉` and **the window algebra is Gorenstein exactly when `N ≤ 2`**, i.e. on windows shorter than
`log 3`: the perfect pairing `(f, g) ↦ (f * g)(N)` exists only before the second prime.

The first index where a function is nonzero is a multiplicative valuation: the stages multiply and
the leading coefficients multiply. A product of folds acts exactly from the product of their stages
on, and a fold starting at `n₀ ≥ 2` has nilpotency index `⌊log N/log n₀⌋ + 1`. Every window operator
is `f(1)` plus a nilpotent: **Wiener's lemma for the window algebra** — `ρ_A(f)` is invertible iff
`f(1) ≠ 0`, with inverse the truncated geometric series — and the spectrum of `ρ_A(f)` is the single
point `f(1)`. All spectral information of the arithmetic sits in Weil's form, not in the operators.

**C. Tate pieces and the non-Tate piece.** For an Euler datum `(F, G)` the Tate family
`J^F_k = twist_{−k}(F) * G` is a cocycle of the Tate flow, `J^F_{k+l} = twist_{−k}(J^F_l) * J^F_k`,
with `J^F_0 = 1`. For `ζ` it is Jordan's totient; on a window it is the group commutator
`ρ_A(J_k) = e^{kM}Ze^{−kM}Z^{−1}`. Its values at `k = β + 1` are the point counts
`φ(m)#ℙ^β(ℤ/m)` (the Tate pieces of the degeneration, AHD), its value at `k = 0` is `1`, and its
derivative at `k = 0` is `Λ`. With the Tate function `τ_H(k) = ⟨ρ_A(J_k)H, H⟩`:

`Q(H) = Ω(0)τ_H(0) − 2τ_H′(0) + J_∞(H) + ½⟨c,H⟩² − ½⟨s,H⟩²`.

Weil's window form is the first-order jet at dimension zero of a function whose values at the
positive integers are counts. Along the powers of a prime the Tate pieces form a Hensel tower,
`J_k(p^{a+1}) = p^kJ_k(p^a)` (`p^k` is the fibre of reduction `(ℤ/p^{a+1})^k → (ℤ/p^a)^k`), while the
non-Tate piece `log p` is the same at every stage. At the first prime `τ_H(k) = ‖H‖² + (2^k − 1)2^{−1/2}∫H(u)H(u + log 2)`:
the signed fold count of `T₂` is the coefficient of `#ℙ^{k−1}(𝔽₂)`.

Because `τ_H` has only the frequencies `log d`, `d ≤ e^A`, its derivative at `0` is a fixed
combination of its values at `0, …, N − 1`: if `P = Σ p_j x^j` interpolates `log` at `1, …, N`, then
`Λ(n) = Σ_j p_j J_j(n)` for `n ≤ N` and

`Q(H) = Ω(0)‖H‖² + J_∞(H) + pole − 2Σ_j p_j τ_H(j)`:

Weil's window form is an explicit **signed count** — a combination of projective point counts over
the residue rings `ℤ/m`, `m ≤ e^A`, in dimensions `< e^A`, with the interpolation coefficients of `log`
as signs.

The Tate family lies above its tangent at dimension zero: `J_k` is multiplicative and nonnegative
for every real `k ≥ 0`, and `J_k(n) ≥ [n = 1] + kΛ(n)` (at a prime power `p^k − 1 ≥ k log p`). On tests
with nonnegative autocorrelations (e.g. `H ≥ 0`) this gives `τ_H(k) ≥ ‖H‖² + k⟨ρ_A(Λ)H, H⟩`, hence
`Q(H) ≥ Ω(0)‖H‖² + J_∞(H) + pole − (2/k)(τ_H(k) − ‖H‖²)` for every `k > 0`: on nonnegative tests
Weil's arithmetic term is dominated by the projective point counts in every positive dimension,
with equality in the limit `k → 0`. Replacing the autocorrelations of `H` by those of `|H|` only raises
the arithmetic term, so every test is dominated by the Tate counts of its modulus.

**The exponential form.** The degree derivation `D f = f·log` determines a function from its
logarithmic derivative on every window (`X(n) log n = Σ_{d∣n, d>1} c(d)X(n/d)`). With the prime-power
logarithm `ℓ = Λ/log` (`ℓ(p^a) = 1/a`), `ζ ≡ exp ℓ` on every window: the window zeta operator is the
exponential of `log Z = ρ_A(ℓ)`, and **Weil's arithmetic operator is the commutator of the position with
`log Z`**, `ρ_A(Λ) = [M, log Z]`. The Tate family is `J_k ≡ exp g_k`, `g_k(p^a) = (p^{ak} − 1)/a =
#(𝔸^k∖0)(𝔽_{p^a})/a`: the Hasse–Weil formula `Z(X, T) = exp Σ #X(𝔽_{p^a})T^a/a` for the punctured
affine spaces `X = 𝔸^k∖0` over `ℤ`, realized in the window algebra; `Σ J_k(n)n^{−s} = ζ(s − k)/ζ(s)`
is their zeta function. For `k ≥ 0` the exponent is nonnegative and `J_k ≥ [n = 1] + g_k ≥ [n = 1] + kΛ`:
the tangent principle is the first two terms of an exponential of point counts. The jets of the family
at dimension zero are the generalized von Mangoldt functions `Λ_j = log^j * μ` (Bombieri):
`J_k = Σ_j k^jΛ_j/j!`, `Λ_{j+1} = Λ_j log + Λ * Λ_j`, `Λ_j ≥ 0`, and `Λ_j` vanishes on the integers with
more than `j` distinct primes. Weil's arithmetic term is the first Taylor coefficient of the Tate
function at dimension zero, Selberg's `Λ₂ = Λ log + Λ * Λ` the second.

**The λ-ring form and the tower recursion.** The Adams operations of the Dirichlet ring are the power
dilations `ψ^a` (`ψ^a f(m^a) = f(m)`). On every window `ℓ ≡ Σ_a ψ^a(P)/a` with `P` the prime indicator, so
`ζ ≡ exp Σ_a ψ^a(P)/a`: the window zeta operator is the plethystic exponential of the prime folds. Likewise
`Λ ≡ Σ_a ψ^a(P_log)`, and because `ψ^a` intertwines the window of length `A/a` with the window of length
`A` through the dilation `D_a` and the Tate twist `(a − 1)/2`,

`ρ_A(Λ) = Σ_{a ≥ 1} D_a ρ_{A/a}(P_log n^{−(a−1)/2}) D_a^{−1}`:

Weil's arithmetic operator on a window is its prime operator plus the dilated, twisted prime operators
of the shorter windows `A/2, A/3, …` of the tower. The prime powers of a window are the primes of the
windows below it; they cannot be dropped (numerically the prime-only form is negative from `log 4` on).

How far from dimension zero the Tate operators stay positive is measured by the weighted norm
`W_N(f) = Σ_{n≤N} f(n)/√n`, which is submultiplicative on nonnegative functions: `W_N(J_k) ≤
exp(kN^kψ_{1/2}(N))`, so `τ_H(k) ≥ (2 − W_N(J_k))‖H‖²` and `ρ_A(J_k)` is positive as soon as
`kN^kψ_{1/2}(N) ≤ log 2`. Conversely no positive dimension is uniform: the star `{1} ∪ {p ≤ M}` of the
rational lattice with amplitudes `1, −J_k(p)/(2√p)` gives `τ_H(k) = (1 − Σ_{p≤M}J_k(p)²/(4p))‖φ‖²`, which
is negative for long windows because `Σ 1/p` diverges. The horizon shrinks to dimension zero
(numerically at the canonical rate, `k*(A) ≈ 1.66e^{−A/2}`): only the tangent at `k = 0` is uniform along
the tower.
At the first stage the horizon is exact: for `log 2 < A < log 3`, `ρ_A(J_k)` is positive iff
`2^k ≤ 1 + 2√2`, `k* = log₂(1 + 2√2) = 1.9368`; the fold by `log 2 > A/2` couples two disjoint collars,
and a bump minus its translate is extremal. At the second stage the horizon is exactly the threshold
`1.19967` of the weighted path `x + log(3/2) — x + log 3 — x — x + log 2` of
folds `2, 3, 2`: arithmetic window forms decompose over finite orbit graphs of the folds, and atoms
realize only the star graphs (atomic horizon `1.2639` at `N = 3`, `≈ 1.56/log N` in general). The
lower bound is proved by a **path Picone inequality**: weighting the window by the Perron vector of the
path (`1/α` on `[−A, −log 3] ∪ [log 3 − A, 0]`, `1` elsewhere), every point is balanced as soon as
`α² + β ≤ 1`, so `2α|c₂| + 2β|c₃| ≤ ‖H‖²`. The same weight gives the sharp arithmetic bound of the
second stage, `|⟨ρ_A(Λ)H, H⟩| ≤ 0.4505‖H‖²`, against `1.124‖H‖²` from the pointwise canonical density:
graph payments are nonlocal and beat pointwise ones already at the second prime. Four bumps on the path
with amplitudes `(α, −1, 1, −α)` give the value `2(1 − α² − β)‖φ‖²`, so the bound is sharp: on the
second stage `‖H‖² + 2αc₂ + 2βc₃ ≥ 0` for all tests iff `α² + β ≤ 1`, and `ρ_A(J_k) ≥ 0` iff
`((2^k − 1)/(2√2))² + (3^k − 1)/(2√3) ≤ 1`. Inside later stages the horizon keeps stepping down as longer
orbit graphs fit (numerically `1.050 → 1.016` across the third stage): the critical lengths of the tower
are combinations of logarithms, not only the `log n`. The orbit graphs are the finite configurations of
positive rationals: a window point `x` sees `x + log r` for the rationals `r` reached from `1` by
multiplying and dividing by `n ≤ e^A` inside `[1, e^A)`, and the folds act as the Hecke operator of
`ℤ[ℚ_{>0}^×]` truncated to the window. Numerically the horizon is the threshold of this rational Hecke
graph to three to five digits on every stage computed (`1.0457` at `A = 1.5`, `1.0157` at `1.6`,
`0.5829` at `2.3`); the third-stage steps sit at the logarithms of the rationals that enter
(`log(9/2)`, …). One half of this is a theorem for every window: any finite configuration of spread
`< A` is realized by disjoint bumps whose translates by `log n` meet exactly along `s = nr`, so every
arithmetic window form takes the value of the Hecke graph form of the configuration (the rational lattice;
a negative graph form is a negative window form). The atomic lattice is the configuration of the
integers; its graphs are stars, and they do not see the horizon beyond the first stage.
The other half is the **Barta criterion of a window**: a measurable weight `1 ≤ h ≤ C` that balances the
folds at every point of the window, `Σ_n a_n(h(u + log n) + h(u − log n)) ≤ h(u)` (with `h = 0` off the
window), bounds `Σ_n 2a_n|∫H(u)H(u + log n)|` by `‖H‖²`. The constant weight gives the pointwise canonical
density, the path weight gives the second stage; whether a balanced weight exists exactly when every
rational Hecke graph of the window has spectral radius `≤ 1` is open.

**D. The atomic lattice.** Atoms of width `< log((N+1)/N)` at the points `log(m/N)`, `m ≤ N`, are
moved by the window shifts as the integers are multiplied: `T_{log n}b_m = b_{nm}` (`0` past the
level). The atomic embedding `ι` intertwines `ρ_A` with multiplication in `D_N`: the integers of
the window are a free module of rank one over the window algebra. With `⟨ι g, ι h⟩ = ‖φ‖²Σ g(k)h(k)/k`,
Weil's arithmetic term on the lattice is multiplication by `Λ`, `−2‖φ‖²Σ_k (Λ*g)(k)g(k)/k`, and the pole
plane reads the window Dirichlet polynomial `Σ g(m)m^{−s}` at `s = 0` and `s = 1`. The atoms are
mutually orthogonal with `‖b_m/√m‖² = 1/m`, so the lattice is the Arakelov bundle
`ℰ_N = ⊕_{m ≤ e^A} 𝒪(½ log m)` with the theta metric of `Spec ℤ`: Riemann–Roch
`h⁰(ℰ_N, d) − h⁰(ℰ_N^∨, −d) = Nd + ½ log N!` by Poisson summation on each summand, degree `½ log N!`
and slope at most `½ log N ≤ A/2`.

On the lattice the arithmetic term is exponentially smaller than on general tests: splitting each
term `Λ(d)g(m)g(dm)/(dm)` by AM–GM, the first halves sum to the Mertens sum and the second to
`Σ_{d∣k}Λ(d) = log k`, so `|⟨ρ_A(Λ)ιg, ιg⟩| ≤ ½(Σ_{d≤N}Λ(d)/d + log N)‖ιg‖² ≈ A‖ιg‖²`, against the
canonical degree `ψ_{1/2}(e^A) ≈ 2e^{A/2}` on wide tests. The canonical class is invisible to the
integers of the window; window negativity lives on wide tests, where the folds overlap.

**E. The pole plane and the floor.** The pole term `2Ĥ(0)Ĥ(1)` is translation invariant; centred at
the window it is `½⟨c_A,H⟩² − ½⟨s_A,H⟩²` with `‖s_A‖² = 4 sinh(A/2) − 2A`. Its exact capacity
`2 sinh(A/2) − A` replaces the cruder `2A sinh²(A/2)`, giving the sharp floor
`Q ≥ −(deg K_A + 2 sinh(A/2) − A)‖H‖²` and, with `ψ_{1/2}(x) ≤ 2√x log x`, the explicit bound
`≤ −Ω(0) + (4A + 1)e^{A/2}`: window negativity grows at most like `Ae^{A/2}` (the trivial strip).

**F. Symmetries of the tower.** Dilation by `e` maps the window of length `A` onto the window of
length `eA` and intertwines the window representation with the Adams lift `ψ^e`, up to the Tate
twist `(e − 1)/2`: `ρ_{eA}(ψ^e f)D_e = D_eρ_A(f n^{−(e−1)/2})`. The tower is self-similar on `e`-th
powers; Weil's form is not, because the longer window also sees the integers that are not `e`-th
powers and the Gamma factor is not dilation invariant. Over a curve the corresponding base change
`𝔽_q ⇝ 𝔽_{q^e}` is an exact symmetry. The window involution `σ_A` conjugates every shift into its
adjoint, so Serre duality is the Rosati involution of the window algebra, and Weil's arithmetic term
is the Rosati symmetrization of `ρ_A(Λ)`.

**G. Twists.** Pointwise multiplication by a completely multiplicative function is a ring
endomorphism of the Dirichlet ring. The Tate flow (`n^{−s}`) and the character twists (`χ`) are two
families of such twists; they commute, and a twist carries the whole Tate structure: the Tate family
of `L(s, χ)` is `χ·J_k`, its Tate pieces are the character-weighted point counts
`χ(m)φ(m)#ℙ^β(ℤ/m)`, and its non-Tate piece is `χΛ`.

**H. Crossing a stage.** The stage datum `Q_N` (Weil's form of the weight truncated at `N`) changes
across the stage `N + 1` by one autocorrelation, so on a window of level `N + 1`

`Q(H) = Q_N(H) + w_{N+1}(fold energy of T_{N+1} − ∫m_ℓH²)`, `ℓ = log(N+1)`:

crossing a stage adds exactly one fold, whose only cost is its end mass on the two **collars** of width
`ε = A − log(N+1)`. Composite stages are free. Every archimedean jump longer than `ε` carries the
collars out of the window, so `Ω(ε)∫_{collars}H² ≤ J_∞(H)`. On every stage `ε < log(3/2)` and
`Ω(ε) ≥ log 3 > 2/e ≥ Λ(n)/√n`: **the exit charge of its collars pays every new fold, uniformly along
the tower**, and `Q(H) ≥ Q_N(H) − Ω(ε)∫_{collars}H²` with the reduced archimedean energy still
nonnegative. This does not make the reduced stage datum nonnegative: a C² test of length `21/20`
has `Q₁(H)<0<Q(H)` (`exists_first_stage_negative_frozen_positive_complete`). The prime-2 fold
repairs its negative frozen direction; discarding its positive energy makes the collar loan false.

**I. The Euler factorization.** The indicators `e_s` of `s`-factored integers are multiplicative and
`e_{{p}} * e_s = e_{insert p s}`, so `∏_{p ≤ N} e_{{p}}` agrees with `ζ` on `[1, N]` and each `e_{{p}}`
is inverted by `1 − δ_p`. On a window of level `N` the window zeta operator is the finite product of
its commuting unipotent Euler factors `(1 − p^{−1/2}T_{log p})^{−1}`, `p ≤ e^A`: the factorization of the
window symbol survives the truncation.

**J. The end profile.** A point `u` of the window leaves through the right end under every jump
longer than `−u` and is entered from beyond the left end under every jump longer than `A + u`.
Exchanging the jump and point integrals gives the exit-charge inequality `∫ e_A H² ≤ J_∞(H)`,
`e_A(u) = Ω(−u) + Ω(A + u)`; dropping the nonnegative interior jumps and folds,

`Q(H) ≥ ∫ V_A H² + pole`, `V_A(u) = Ω_Γ + φ(−u) + φ(A + u)`, `φ(t) = Ω(t) − ψ_{1/2}(e^t)`:

one universal end profile, the Gamma factor's exit tail minus the half-weighted Chebyshev count, as
a function of the distances to the two ends, for every window of the tower. The end profile is the constant case of a
**ground-state transform**: for a positive weight `h` and its window gate `G = h·1_{[−A,0]}`, the Picone
jump weight `a_h(y, u) = 2 − (G(u + y) + G(u − y))/h(u)` satisfies `∫a_h(y,·)H² ≤ ∫(H − H(·+y))²` for every
jump, so a balanced weight (`a_h ≥ 0`) bounds the Lévy energy below by `∫(∫_0^∞ω a_h)H²`, and together
with the fold Barta bound `Q ≥ (Ω_Γ − κ)‖H‖² + ∫V H² + pole` — the Allegretto–Piepenbrink form of the
window capacity problem, with interior jumps charged and not only exits. Where `V_A` pays the
pole capacity `2 sinh(A/2) − A` pointwise, the window is positive. On prime-free windows the
minimum is at the centre (`Ω` is midpoint convex), and `Ω_Γ + 2Ω(1/14) > 2 sinh(1/14) − 1/7`:
**every window of length `≤ 1/7` is positive by its exit charge**, without any estimate of Weil's
form (the exact pointwise limit is `≈ 0.174`). Beyond, `φ` turns negative like `−2e^{t/2}` and the
interior jumps must pay.

**K. Selection.** Tate pieces at a prime have the sign of the weight: `J^F_k(p) = F(p)(p^k − 1)` and
`λ_F(p) = F(p) log p`. A flip twin has a negative Tate piece at its prime from the stage where the
flip becomes visible. The shifted datum `ζ(s)ζ(s − ε)`, with zeros `ρ + ε` off the line, is Tate
positive in every positive dimension. Near dimension zero, Tate positivity at the primes is exactly
the sign of the weight. Counts at integer dimensions do not select. More generally, a datum whose
logarithm `g` (`DF = (Dg)F`) is nonnegative is Tate positive in every real dimension `k ≥ 0` at every
integer, `J^F_k ≥ [n = 1] + g(n)(n^k − 1)`; `ζ(s)ζ(s − ε)` has the nonnegative logarithm `ℓ(1 + n^ε)`,
flip twins have `ℓ_F(p) = −1`, and the quadratic `L(s, χ)` has `χℓ`, negative at the inert primes. The
sign of the logarithm separates neither the fakes from `ζ` nor `ζ` from other `L`-functions.

## 5. Questions the programme answers

| Question (obstacles §2.7) | Answer |
|---|---|
| What are the restriction maps `W_A → W_{A'}` and their control theorem? | Algebraically and analytically controlled. Analytic control: crossing a stage adds one fold paid by its end mass (`weilQuad_eq_stageForm_add_fold`, `weilQuad_nonneg_of_endCoercive`), composite stages are free (`weilQuad_eq_stageForm_of_not_primePow`), and the collar exit charge pays every new fold uniformly (`levyJump_ge_collar`, `primeJumpWeight_le_archLevyAntideriv`, `weilQuad_ge_reducedStageForm`). Algebraic control: equivalently, equivariant inclusions of window modules over the truncations `D_{⌊e^{A'}⌋} → D_{⌊e^A⌋}` (`windowRepFun_of_le`, `ker_windowRep`). Each stage is a small extension with kernel the new fold (`sub_single_mem_truncIdeal_succ`, `mul_mem_truncIdeal`); the new fold is a socle element until stage `2n` (`windowRep_single_mul_eq_zero`); Loewy length `⌊log₂ N⌋ + 1` (`windowRep_kills_pow_iff`); cotangent space = primes (`mem_sq_sup_truncIdeal_iff`, `single_prime_not_mem`); Hilbert function = almost-prime counts (`mem_pow_sup_truncIdeal_iff`, `sub_restrictTo_almostPrime_mem`, `restrictTo_almostPrime_mem_iff`); socle `(N/2, N]`, Gorenstein iff `N ≤ 2` (`mul_mem_truncIdeal_forall_iff`, `socle_principal_iff`); local with one-point spectra (`isUnit_windowRep_iff`, `isUnit_windowRep_sub_iff`); inverse limit = Dirichlet ring (`existsUnique_limit`, `iInf_truncIdeal`). |
| What is the count attached to a fold `T_n`; what does `sym₂` count? | `T_n` is `δ_n`; in the Tate function its coefficient is `J_k(n)n^{−1/2}`, a count of primitive vectors of `(ℤ/n)^k` (`tateFunction_eq`, `jordanTotient_eq_card_primVec`). At the first prime the signed fold count `anti₂ − sym₂` is the coefficient of `#ℙ^{k−1}(𝔽₂) = 2^k − 1` (`tateFunction_firstPrime`). It enters Weil's form only through the derivative at `k = 0` (`weilQuad_eq_tateJet`): no integer dimension makes it a count. Equivalently, Weil's window form is a signed combination of the counts `φ(m)#ℙ^{j−1}(ℤ/m)`, `j < e^A`, with the coefficients of the polynomial interpolating `log` at `1, …, ⌊e^A⌋` (`sum_coeff_mul_jordanTotient`, `weilQuad_eq_signedCount`): the window `h¹` is a signed count, and its sign is the sign of that interpolation against the archimedean data. Geometrically the folds act on orbit graphs of window points: at the first stage `T₂` is a perfect matching of the two disjoint collars (`|c₂| ≤ ‖H‖²/2`, sharp: `abs_autocorr_le_half`, `tateFunction_nonneg_iff_firstStage`), at the second stage `T₂, T₃` form the weighted path `P₄` (`secondStage_nonneg_iff`). On the indicator of a finite configuration `S ⊂ ℚ_{>0}` the folds are literally counts: `∫H(u)H(u + log n) = ‖φ‖²·#{r ∈ S : nr ∈ S}`, the number of multiplicative `n`-pairs inside `S` (this is what `sym_n` counts), and the fold energy is `‖φ‖²` times the number of `n`-edges cut by `S` (`integral_ratLattice_one_eq_card`, `foldEnergy_ratLattice_eq_card`); Weil's arithmetic term is the `Λ(n)n^{−1/2}`-weighted count of multiplicative pairs. |
| Is there a scheme over `ℤ` whose `ℤ/m`-points give the twisted counts and whose "conductor-one" part is the window form? | The punctured affine spaces `𝔸^k∖0` (primitive vectors), with the dimension as parameter; the Tate operator is the exponential of their Frobenius point counts, the window form of their Hasse–Weil zeta function (`expTrunc_sub_jordan_mem`, `tateExponent_prime_pow`): `J_k(m) = φ(m)#ℙ^{k−1}(ℤ/m)` are the Tate pieces (`jordanTotient_eq_card_projPoints`); `∂_kJ_k(m)|₀ = Λ(m)` (`hasDerivAt_jordanTotient_zero`) makes Weil's arithmetic window term the derivative at dimension zero (`hasDerivAt_tateFunction`). |
| What lattice of rank `≈ 2e^A` carries the sections; with what metric? | For the arithmetic of the window, the rational lattice: finite configurations of `ℚ_{>0}^×` inside the window, on which the folds are the Hecke operators of `ℤ[ℚ_{>0}^×]` (`exists_rationalLattice`, `exists_windowTest_eq_heckeForm`; numerically it carries the exact Tate horizons). The atomic lattice (on it the arithmetic term is bounded by the Mertens sum, `abs_sum_vonMangoldt_mul_le`, `abs_integral_windowRep_vonMangoldt_atomic_le`): the integers `m ≤ e^A`, a free rank-one module over the window algebra (`windowRepFun_atomicEmbedding`), of rank `⌊e^A⌋`; the window genus `≥ (2 − η)e^A` (CWS) is twice this rank to main order. Metric `‖φ‖²Σ g(k)h(k)/k` (`integral_atomicEmbedding_mul`); arithmetic term = multiplication by `Λ` (`integral_windowRep_atomicEmbedding`); pole = values at `s = 0, 1` (`poleA_atomicEmbedding`, `poleB_atomicEmbedding`); the Gamma factor enters as the Gaussian (theta) metric on each atom and as the Lévy kernel between atoms. As an Arakelov bundle it is `⊕_{m≤e^A} 𝒪(½ log m)` with `h⁰ − h⁰∨ = Nd + ½ log N!` and slope `≤ A/2` (`integral_atomicEmbedding_single`, `windowBundleH0_riemannRoch`, `windowBundle_slope_le`). |
| What growth law does the tower obey? | Negativity `≤ (deg K_A + 2 sinh(A/2) − A)‖H‖² ≤ (−Ω(0) + (4A+1)e^{A/2})‖H‖²` (`weilQuad_ge_neg_sharpWindowFloor`, `sharpWindowFloor_le`). Its exponent lies between the zero width and `½`, with RH iff it is `0` (ACCE `UnconditionalEqualityOfPolarAndFullGroundEnergyRates`, SRT `NegativityRateEqualsMaximalDepth`). The arithmetic part of the floor is sharp at the graph canonical degree: balanced weights bound it (`sum_two_mul_abs_autocorr_le`, exact at the second stage, `abs_arith_secondStage_le`), configurations attain it (`exists_windowTest_eq_heckeForm`); numerically it is `≈ 0.3–0.4 ψ_{1/2}(e^A)`: the constant of the floor improves, its exponent does not. The Tate horizon shrinks along the tower (`exists_tateFunction_neg`, numerically `≈ 1.66e^{−A/2}`). |
| Do the Tate pieces reproduce the degeneration on twisted windows (criterion 6)? | Yes for character twists: twists commute with the Tate flow and carry Tate families (`twist_tateTwist_comm`, `tateFamily_twist`); the Tate pieces of `L(s, χ)` are `χ(m)φ(m)#ℙ^β(ℤ/m)` (`tateFamily_charTwist_succ`) and its non-Tate piece is `χΛ` (`hasDerivAt_tateFamily_charTwist`), the dimension `β` entering as the dimension of projective space. |
| Is there a Frobenius / base change for the tower; what is Serre duality on it? | Adams lifts are dilations `A ↦ eA` up to a Tate twist (`windowRepFun_mPart_dilate`, `windowShift_dilate`); Serre duality `σ_A` is the Rosati involution (`windowInvolution_windowShift`, `integral_windowRepFun_mul_eq`). |
| Which axiom fails for the fakes? | Flip twins fail Tate positivity at their prime (`flipDatum_tateFamily_prime_neg`); shifted products `ζ(s)ζ(s−ε)` satisfy it (`shiftedDatum_tateFamily_nonneg`); every algebraic structure of the tower holds for every Euler datum. Selection is the sign of the derivative at dimension zero against the archimedean data, along the whole tower — Weil's form itself. A nonnegative logarithm gives Tate positivity in every real dimension (`tateFamily_ge_of_log_nonneg`, `shiftedDatum_tateFamily_ge`) and so cannot select. Numerically the tower is rigid: changing a single weight `Λ(n)` breaks positivity within `≈ 0.4` of `log n`, and removing the Adams components `ψ^a(P_log)` creates negative directions at the frequencies `γ/a` (§7.8). |

## 6. Tools

**Developed.**
- Window shifts and the window representation of the Dirichlet ring; nesting along the tower.
- Truncation ideals, basis functions `δ_n`, small-extension, socle and Loewy calculus; cotangent
  spaces; inverse limits of compatible window classes.
- The Tate flow: twist automorphisms, the degree derivation as a commutator, Tate families of Euler
  data as cocycles, Tate operators as group commutators; Tate pieces at primes.
- The Jordan family as an analytic family in the dimension; Tate functions of window tests.
- Atoms and the atomic embedding; orthogonality, regular representation, pole moments of atomic tests.
- Arakelov `h⁰` of the growing-rank window bundle `⊕_{m≤e^A} 𝒪(½ log m)`: Poisson Riemann–Roch,
  degree `½ log ⌊e^A⌋!`, slope `≤ A/2`.
- Centred pole plane; exact capacity by Cauchy–Schwarz; sharp floor and pencil; `ψ_{1/2}` bound by
  telescoping `Σ n^{−1/2} ≤ 2√N`.
- Dilations of windows and Adams lifts; adjoint shifts and the Rosati involution.
- Completely multiplicative twists of Euler data; character-weighted Tate pieces.
- Lagrange interpolation of `log` on the integers of a window; signed-count form of Weil's window form.
- Stage data and the transfer across a stage (a one-step Schur/capacity criterion along the socle).
- Collar exit charges of the Gamma factor (a Hardy-type inequality for the archimedean jumps on the
  collars of a window) and the uniform margin `Ω(log(3/2)) ≥ log 3 > 2/e ≥ Λ(n)/√n`.
- Multiplicativity calculus of factored indicators; the exact window Euler product (the
  factorization of the window symbol into unipotent local factors).
- The stage valuation (multiplicative leading terms), Wiener's lemma by truncated geometric series,
  the `Ω`-filtration and its associated graded algebra, the socle calculus.
- The tangent principle for the Jordan family (convexity of `p^k` at `0`), multiplicativity of `J_k`
  in real dimension.
- AM–GM against the divisor structure (`Σ_{d∣k}Λ(d) = log k`) for the atomic arithmetic form.
- Picone inequalities on orbit graphs of the folds (ground-state AM–GM with piecewise-constant
  Perron weights), the first instance of the graph Schur-complement tool at the second prime.
- Adams operations (power dilations) as λ-ring structure: plethystic logarithms and exponentials,
  the tower recursion linking the windows `A` and `A/a`.
- The degree derivation as an ODE on the window algebra: uniqueness from the logarithmic derivative,
  truncated exponentials, exponential forms of `ζ` and of the Tate family; jet towers of finite
  exponential sums and their exponential generating functions.

**Used from the corpus.** CWS (window tests, folds, canonical class, floor, index, genus, flip twins);
AHD/ADT (`jordanTotient`, `natCard_projPoints_mul_totient`, `natCard_primVec_eq_jordanTotient`); RHTower
`WeilMarkovPoleCapacity` (Markov form, `levyJump`, pole pairings); SpacingScaleHarmonicAnalysis
(`weilQuad`, Cauchy–Schwarz); RHTower `mPart` (power dilation); mathlib `ArithmeticFunction`. The coefficientwise Jordan derivative is
the window form of RHTower `hasDerivAt_suzukiShiftedCoefficient`.

- The exit-charge (Hardy-type) inequality for the Gamma factor on a window, by exchanging jump and
  point integrals; the end-profile potential and pointwise payment; elementary bounds on `Ω`
  (closed form, `arctan(1/√3) = π/6`, `arctan x ≥ π/4 − (1 − x)/2`, `log 95 ≥ 22/5`, `log 55 ≥ 4`).

**To develop.** Balanced weights for the ground-state transform beyond the archimedean critical length
(where the pole must enter), i.e. the Poincaré inequality for the interior jumps against the end-profile
potential where `V_A` is negative, uniformly in `A`; the higher critical lengths of the window index
(the first is SRT's contact aperture); Picone weights for the orbit graphs of every stage (the
general graph Schur complement, beyond the second stage) and their coupling to the archimedean jumps
and the pole; the rigidity of the fold weights through the explicit formula with zeros.

## 7. Open research topics

1. **The derivative at dimension zero.** `τ_H` is an exponential polynomial in `k` whose values at the
   positive integers are counts and whose value at `0` is `‖H‖²`. RH is the statement that
   `Ω(0)τ_H(0) − 2τ_H′(0) + J_∞(H) + pole ≥ 0` on every window. Of the positivity of the family
   `k ↦ ρ_A(J_k)` (commutators of `Z` with the Tate flow), what survives differentiation at `0` at
   the primes is exactly the sign of the weight (`tateFamily_prime_nonneg_iff`) — the Markov
   property, soft. In every fixed positive dimension the Tate operators eventually fail
   (`exists_tateFunction_neg`), while they are positive below a horizon that shrinks to `0`; at the
   first two stages the horizon is exact (`tateFunction_nonneg_iff_firstStage`,
   `tateFunction_nonneg_iff_secondStage`) and is the threshold of a rational Hecke graph. Open: a
   positivity of the whole family, coupled to the archimedean data, that survives the derivative.
2. **Positivity across a small extension.** The exact transfer is
   `Q=Q_N+w(fold energy−collar mass)`. The sufficient nonnegative collar loan fails already at
   the first stage, even on a strictly positive complete C² test of length `21/20`
   (`exists_first_stage_positive_exit_loan_failure`). Numerically the same happens at every stage
   `n ≤ 16`: the frozen datum (fold `n` dropped) is negative at `log n + 0.2` (minima `−0.14` …
   `−0.57`). Open: pay the signed fold jointly with the frozen datum, uniformly along the tower.
3. **Analytic control by stages.** Each stage adds one signed collar correlation. The window index is
   nondecreasing; its first critical length is twice SRT's contact aperture (`zetaContactAperture`,
   `≥ 0.362` off RH), and CWS bounds the index by one below `log 2 + 1/50`. Open: the higher critical
   lengths `A_k = inf{A : ι(A) ≥ k}`, and AOT's spectral jumps resolved by stages.
4. **Window capacity.** The pointwise part is done: `Q ≥ ∫V_A H² + pole` with the universal end
   profile, and short windows (`≤ 1/7`) are positive by it. Open: a Poincaré inequality for the
   interior jumps on the region where `V_A < 0`, uniform in `A` (RH; shared with CWS §7). Numerically
   the archimedean form `Ω_Γ‖H‖² + J_∞(H)` alone has negative index `0` below `A₁ ≈ 0.218`, `1` up to
   `A₂ ≈ 0.763`, and in general its critical lengths are `A_k ≈ k/2 − 0.24` (gaps `→ π/ξ₀`): a Weyl law
   `ι_Γ(A) ≈ 2A` for the Gamma symbol `Re ψ(¼ + iξ/2) − log π`, which vanishes at `ξ₀ = 6.2898 ≈ 2π`
   (the `2π` of the Riemann–von Mangoldt formula). So no potential bound for `J_∞` (exit potential, ground-state weights) passes `A₁`: beyond
   it the pole is indispensable. The second archimedean direction is odd under `σ_A` and appears
   just after the first prime `log 2`.
5. **The exponent.** Close the gap between the zero width and the negativity exponent without
   no-clustering hypotheses.
6. **The Perron state of the pole-free form.** Weil's form without the pole is a Schrödinger form with
   nonpositive off-diagonal kernel (Lévy jumps and prime folds), so its ground state is positive.
   Numerically its ground energy is about minus the canonical degree, the rest of its spectrum
   accumulates at `0` from above, and the pole lifts exactly the Perron state. RH implies that the
   pole-free form has at most one negative square on every window (the pole has one positive
   direction). Open: the Perron state and the gap as laws in `A`.
7. **Signed repair at the first prime.** The odd unit cubic has frozen archimedean energy
   `<−29‖f‖²/2100` and complete energy `>‖f‖²/100`. Its negative correlation at `log2` supplies
   the positive prime contribution. Both strict signs survive mollification inside a window
   of length `21/20`. For every odd C² test supported in `[-1/2,1/2]`, the frozen form satisfies
   `Q₁(F)+20M(F)²≥‖F‖²/125`, where `M(F)=∫F(x)x(1−16x²/5)dx`; its restriction to `M=0`
   is coercive. The complete form satisfies `Q(F)≥‖F‖²/100` when `∫xF=∫x³F=0`;
   the signed prime-2 term and sinh pole are included. Open: pay the two low moments and their
   cross terms, then extend to every first-stage test.
8. **Rigidity of the fold weights.** Numerically, replacing one weight `Λ(n)` by `λΛ(n)` keeps the
   window positive only for `λ` in an interval that collapses onto `1` within about half a unit of
   length after `log n` (for `n = 2`: `[0.61, 1.62]` at `+0.10`, `[0.964, 1.092]` at `+0.25`,
   `[0.98, 1.012]` at `+0.40`); dropping all prime powers breaks positivity from `log 4` on. The
   mechanism is the zero-free band: Weil's spectral measure vanishes on `|ξ| < γ₁ = 14.13`, and a
   single-fold change adds `2(λ − 1)Λ(n)n^{−1/2}cos(ξ log n)`, negative somewhere inside the band, which
   a window resolves once it is long enough. Open: the rigidity theorem as a law along the tower
   (unconditional, since no zero lies below height `14`), and the rate at which the interval
   collapses; numerically it tightens at `A − log n ≈ π/γ₁ = 0.22` for every `n`, the length at which a
   window resolves the zero-free band.
   The tower recursion has a spectral fingerprint: removing the Adams component `ψ^a(P_log)` (the
   `a`-th prime powers) produces negative directions exactly at the frequencies `γ/a` — `7.07 = γ₁/2`
   when the squares are dropped, `4.71 = γ₁/3` when the cubes are — because `Σ_p log p·p^{−as}` carries the
   singularities of `ζ′/ζ(as)` at `ρ/a`, off the line. The `a`-th Adams operation transports the zeros
   to `ρ/a`; only the full sum over `a` puts them back on the line.

## 8. Pillar theorems

| Theorem | Lean |
|---|---|
| Window shifts compose and die past the length | `windowShift_add`, `windowShift_eq_zero`, `windowShift_zero` |
| The window representation is a ring map; its kernel is the truncation | `windowRep`, `windowRepFun_mul`, `windowRep_eq_zero_iff`, `ker_windowRep` |
| Nesting along the tower | `windowRepFun_of_le` |
| Degree derivation = commutator with the position; Tate twists = conjugations | `position_comm_windowRep`, `windowRepFun_twist`, `tateTwistHom`, `tateTwist_tateTwist` |
| Von Mangoldt operator = logarithmic derivative of the window zeta operator | `windowRep_vonMangoldt_mul_zeta`, `windowRep_vonMangoldt_eq`, `windowRep_moebius_mul_zeta` |
| Weil's window form in the window algebra | `weilQuad_eq_windowRep` |
| One new fold per stage; socle law; small extensions | `sub_single_mem_truncIdeal_succ`, `mul_mem_truncIdeal`, `mul_mem_truncIdeal_succ`, `windowRep_single_mul_eq_zero` |
| Sharp Loewy length | `pow_truncIdeal_one_le`, `single_two_pow`, `windowRep_kills_pow_iff` |
| Cotangent space = primes | `mem_sq_sup_truncIdeal_iff`, `single_prime_not_mem` |
| Inverse limit = Dirichlet ring | `iInf_truncIdeal`, `existsUnique_limit` |
| Jordan family: `J_0 = 1`, `∂J|₀ = Λ`, Tate pieces = point counts | `jordanFun_zero`, `jordanFun_eq`, `hasDerivAt_jordanTotient_zero`, `jordanTotient_eq_card_projPoints`, `jordanTotient_eq_card_primVec`, `windowRepFun_jordan_nonneg` |
| Weil's form = 1-jet of the Tate function at dimension zero | `tateFunction_zero`, `hasDerivAt_tateFunction`, `tateFunction_succ`, `tateFunction_firstPrime`, `weilQuad_eq_tateJet` |
| The exit-charge inequality; the end profile; pointwise payment | `integral_exitWeight_mul_le`, `lintegral_exitPotential_le`, `integral_exitPotential_mul_le`, `exitPotential_sub_canonicalDensity`, `weilQuad_ge_endProfile`, `weilQuad_ge_windowPotential`, `weilQuad_nonneg_of_potential` |
| Short windows are positive by their exit charge | `two_mul_archLevyAntideriv_half_le_exitPotential`, `weilQuad_nonneg_of_primeFree_centre`, `archLevyAntideriv_one_div_24_ge`, `weilQuad_nonneg_of_le_one_twelfth` |
| Transfer across a stage; composite stages free | `markovForm_succ`, `weilQuad_eq_stageForm_add_fold`, `weilQuad_ge_stageForm_sub_endMass`, `weilQuad_nonneg_of_endCoercive`, `weilQuad_eq_stageForm_of_not_primePow` |
| First fold repairs a negative frozen direction; nonnegative collar loan fails | `cubicWindow_weilQuad_pos`, `exists_first_stage_negative_frozen_positive_complete`, `exists_first_stage_positive_exit_loan_failure` |
| One cubic moment pays the frozen odd form on the unit window; its kernel is coercive | `stageForm_one_cubicMoment_lower`, `stageForm_one_add_cubicMoment_ge`, `stageForm_one_coercive_of_cubicMoment_zero` |
| Complete odd unit-window coercivity after first and third moments vanish | `stageForm_two_ge_of_odd_two_moments_zero`, `weilQuad_ge_of_odd_two_moments_zero` |
| Gamma comparison retains its lag costs; the exact second moment gives a position square and improves the uniform loss to `7/192` | `unit_odd_gamma_lag_moments_lower`, `unit_odd_gamma_position_lower`, `unit_odd_gamma_jump_second_moment_lower` |
| The exit charge pays every new fold | `collar_le_jump`, `levyJump_ge_collar`, `primeJumpWeight_le`, `log_three_le_archLevyAntideriv`, `primeJumpWeight_le_archLevyAntideriv`, `weilQuad_ge_reducedStageForm` |
| The window Euler product | `isMultiplicative_factoredIndicator`, `factoredIndicator_mul_insert`, `prod_factoredIndicator`, `eulerFactor_mul_inverse`, `windowRep_zeta_eq_prod`, `windowRep_eulerFactor_mul_inverse` |
| Weil's window form is a signed count | `exists_log_interpolant`, `sum_coeff_mul_jordanTotient`, `integral_windowRep_vonMangoldt_eq_signedCount`, `weilQuad_eq_signedCount` |
| Tate cocycle, commutator and conjugation forms | `tateFamily_add`, `tateFamily_zeta`, `windowRepFun_jordan_eq_commutator`, `windowRep_zeta_conj_position` |
| Hensel tower of Tate pieces | `jordanTotient_prime_pow_succ`, `hasDerivAt_jordanTotient_prime_pow` |
| Tate pieces at primes; flip twins; softness | `tateFamily_prime`, `logDeriv_prime`, `tateFamily_prime_mul_log`, `flipDatum_tateFamily_prime_neg`, `shiftedDatum_tateFamily_nonneg` |
| Atomic lattice = regular representation | `windowShift_atom_of_le`, `windowShift_atom_of_lt`, `windowRepFun_atomicEmbedding`, `integral_atomicEmbedding_mul`, `integral_windowRep_atomicEmbedding`, `poleA_atomicEmbedding`, `poleB_atomicEmbedding` |
| Twists: ring endomorphisms commuting with the Tate flow; twisted Tate pieces | `twistHom`, `twist_tateTwist_comm`, `tateFamily_twist`, `charZeta_mul_charMoebius`, `tateFamily_charTwist`, `tateFamily_charTwist_succ`, `hasDerivAt_tateFamily_charTwist` |
| What survives the derivative at dimension zero: the Markov sign | `tateFamily_prime_nonneg_iff` |
| A nonnegative logarithm gives Tate positivity in every real dimension; the shifted datum has one | `degD_inverse`, `degD_tateFamily`, `expTrunc_sub_tateFamily_mem`, `tateFamily_ge_of_log_nonneg`, `degD_shiftedDatum`, `shiftedDatum_tateFamily_ge` |
| Adams lifts = dilations; Serre duality = Rosati involution | `windowShift_dilate`, `windowRepFun_mPart_dilate`, `windowInvolution_windowShift`, `integral_windowShift_mul_eq`, `integral_windowRepFun_mul_eq` |
| The Arakelov bundle of a window | `integral_atomicEmbedding_single`, `arithH0_add_half_log`, `windowBundleH0_riemannRoch`, `windowBundle_slope_le` |
| Exact pole capacity; sharp floor and pencil; exponent `½` | `pole_eq_centred`, `integral_centredSinh_sq`, `centredSinhPairing_sq_le`, `pole_ge`, `weilQuad_ge_neg_sharpWindowFloor`, `pencil_nonneg_sharp`, `halfChebyshev_le`, `sharpWindowFloor_le` |
| Aperture-independent floor `Q(H) ≥ −C(p)∫e^{−pu}H²`, `p > 1`; one positive weighted pencil on every window | `abs_correlation_le_exponentialMass`, `laplaceMoment_sq_le_exponentialMass`, `weilQuad_ge_neg_exponentialMass`, `weighted_pencil_ge` |
| Windows of length `≤ 1/7` are positive by their exit charge | `archLevyAntideriv_one_div_14_ge`, `weilQuad_nonneg_of_le_one_seventh` |
| Stage valuation; exact nilpotency; Wiener's lemma; one-point spectrum | `mul_vanishesBelow`, `pow_vanishesBelow`, `windowRep_mul_eq_zero_iff`, `windowRep_pow_eq_zero_iff`, `isUnit_windowRep_iff`, `isUnit_windowRep_sub_iff` |
| Hilbert function = almost-prime counts; socle; Gorenstein iff `N ≤ 2` | `pow_truncIdeal_one_le_omegaVanishing`, `single_mem_pow_truncIdeal_one`, `mem_pow_sup_truncIdeal_iff`, `sub_restrictTo_almostPrime_mem`, `restrictTo_almostPrime_mem_iff`, `mul_mem_truncIdeal_forall_iff`, `socle_principal_iff` |
| The tangent principle of the Tate family | `isMultiplicative_jordanFun`, `jordanTotient_nonneg`, `jordanTotient_ge_tangent`, `tateFunction_ge_tangent`, `weilQuad_ge_of_nonneg_tangent` |
| The atomic lattice sees only the Mertens sum | `abs_term_le`, `abs_sum_vonMangoldt_mul_le`, `abs_integral_windowRep_vonMangoldt_atomic_le` |
| Every test is dominated by the Tate counts of its modulus | `absTateCount`, `weilQuad_ge_absTateCount` |
| `ζ = exp ℓ` on windows; `ρ_A(Λ) = [M, log Z]`; `J_k = exp g_k` (Hasse–Weil of `𝔸^k∖0`) | `mem_truncIdeal_of_degD`, `degD_expTrunc`, `expTrunc_sub_mem`, `expTrunc_sub_zeta_mem`, `windowRep_zeta_eq_exp`, `windowRep_vonMangoldt_eq_comm_log`, `tateExponent_prime_pow`, `degD_jordanFun`, `expTrunc_sub_jordan_mem`, `jordanTotient_ge_exp_tangent`, `jordanTotient_prime_pow_ge` |
| The Tate positivity horizon: submultiplicative weighted norm, positivity for `kN^kψ_{1/2}(N) ≤ log 2` | `weightNorm_mul_le`, `weightNorm_expTrunc_le`, `weightNorm_tateExponent_le`, `weightNorm_jordan_le`, `abs_autocorr_le`, `tateFunction_ge_two_sub`, `tateFunction_nonneg_of_le_log_two` |
| `ζ` is the plethystic exponential of the primes; the tower recursion of `ρ_A(Λ)` | `prime_pow_eq_prime_pow`, `mPart_apply_prime_pow`, `primePowerLog_sub_plethLog_mem`, `vonMangoldt_sub_sum_mPart_mem`, `expTrunc_sub_mem_of_sub_mem`, `expTrunc_plethLog_sub_zeta_mem`, `windowRepFun_congr`, `windowRepFun_vonMangoldt_eq_sum_dilate` |
| The exact Tate horizon at the first prime, `2^k ≤ 1 + 2√2` | `windowLevel_eq_two`, `tateFunction_firstStage`, `abs_autocorr_le_half`, `tateFunction_nonneg_firstStage`, `exists_tateFunction_neg_firstStage`, `tateFunction_nonneg_iff_firstStage` |
| The second stage is a weighted path: path Picone inequality, Tate positivity and the sharp arithmetic bound | `two_abs_mul_le_ratio`, `two_abs_autocorr_le`, `path_balance`, `two_mul_abs_autocorr_add_le`, `tateFunction_nonneg_secondStage`, `abs_arith_secondStage_le` |
| No uniform Tate positivity: the star of the primes breaks every positive dimension | `primesTo`, `starConfig`, `star_coincidence`, `exists_tateFunction_neg_of_primeSum`, `exists_tateFunction_neg` |
| The second-stage path is attained: exact form and exact Tate horizon | `bump_mul_eq_zero`, `exists_neg_secondStage`, `secondStage_nonneg_iff`, `tateFunction_secondStage`, `tateFunction_nonneg_iff_secondStage` |
| The ground-state transform: Picone for the Lévy jumps; ground-state criterion for Weil's form | `piconeWeight`, `measurable_piconeWeight`, `integral_piconeWeight_mul_le`, `integral_mul_le_levyJump_of_picone`, `weilQuad_ge_groundState` |
| The Barta criterion of a window: balanced weights bound all folds | `sum_two_mul_abs_autocorr_le`, `arith_form_nonneg_of_balanced` |
| The folds count multiplicative pairs on configurations | `sum_sum_ite_eq_card`, `integral_ratLattice_one_eq_card`, `foldEnergy_ratLattice_eq_card` |
| The rational lattice: finite configurations of `ℚ_{>0}^×` in a window; arithmetic window forms = Hecke graph forms | `ratLattice`, `exists_pos_le_of_finset`, `log_sub_ne_zero`, `exists_rationalLattice`, `exists_windowTest_eq_heckeForm` |
| Jets of the Tate family = generalized von Mangoldt functions | `hasDerivAt_tateJet`, `tateJet_zero`, `tateJet_zero_dim`, `hasSum_tateJet`, `genVonMangoldt_succ`, `genVonMangoldt_two`, `genVonMangoldt_nonneg`, `genVonMangoldt_eq_zero_of_lt` |

## 9. Traps

| Trap | Truth |
|---|---|
| Positivity of short windows needs an estimate of Weil's form | Up to length `1/7` the exit charge alone pays it, pointwise |
| A better potential for the jumps reaches the first prime | No bound of `J_∞` by a potential passes `A₁ ≈ 0.215`, where `Ω_Γ + J_∞` itself turns negative (numerics); the pole must enter |
| The window operators carry spectral information | Each `ρ_A(f)` is `f(1)` plus a nilpotent (Wiener's lemma); the spectrum is in Weil's form, not in the algebra |
| The atomic lattice sees the canonical class | On atoms the arithmetic term is bounded by the Mertens sum `≈ A`, not by `ψ_{1/2}(e^A) ≈ 2e^{A/2}` |
| Tate operators are positive in small positive dimension | In every fixed `k > 0` they fail on long windows (`exists_tateFunction_neg`); `ρ_A(J_k)` is positive below a horizon `≍ e^{−A/2}` (proved lower bound `log 2/(N^kψ_{1/2}(N))`, numerics `1.66e^{−A/2}`), which shrinks to `0` along the tower; only the tangent at `0` is uniform |
| Weil's window form is reflection positive along `σ_A` | Numerically not in either sign: the Lévy cross kernel `ω(x + y)` is completely monotone, so the archimedean cross form is reflection negative, and the folds make it indefinite; Mechanism D needs another reflection |
| Configurations of integers (atoms) see the arithmetic of a window | They see only stars; the extremal configurations are rational (`{1, 3/2, 2, 3}` at the second stage), and the window arithmetic is the Hecke operator of `ℤ[ℚ_{>0}^×]` |
| The Tate function is log-convex at dimension zero | On wide tests `T₁² ≈ 4N ≫ T₀T₂ ≈ 4√N log N`: Weil's term is not controlled by Selberg's jet through Cauchy–Schwarz |
| The window algebra is the semilocal algebra of the Euler factors at `p ≤ e^A` | It is the Dirichlet ring truncated at `n ≤ e^A`; composites are products, truncation is by size |
| The tower is a direct limit of finite objects carrying `h¹` | The algebras are finite-dimensional; the modules are not, and no window has a finite-dimensional realization (CWS) |
| A new prime power is a large perturbation of the window | Algebraically it is a socle element; it composes to zero with every fold until stage `2n` |
| Weil's arithmetic term is a count | It is the derivative at dimension zero of counts, i.e. a signed combination of counts with interpolation signs; at every positive integer dimension the family is a count, and that positivity is soft |
| Counting coefficients select `ζ` | `ζ(s)ζ(s − ε)` is Tate positive with zeros off the line |
| The pole plane costs `Ae^A` on a window | Its exact capacity is `2 sinh(A/2) − A`, exponent `½` |
| Atoms diagonalize Weil's form | They diagonalize the norm and turn the arithmetic into multiplication by `Λ`; the Lévy kernel couples all atoms |

## 10. Place in the research and relation to other programmes

| Programme | Relation |
|---|---|
| `CohomologyOfWindowsOfSpecZ` (CWS) | one window at a time: datum, folds, canonical class, floor, index, genus, Tate law, selection. WTZ is its tower: algebra, transitions, control, Tate pieces, lattice, growth |
| `ArithmeticHodgeTheoryOfDegenerations`, `ArithmeticDegenerationTheory` | Jordan totient and the projective-space count law; WTZ puts the Tate pieces and Weil's form on one family and differentiates it |
| `ArithmeticContinuationAndCriticalEnergy`, `SquareRootThreshold` | ground-energy rates, the two-bump negativity rate, the contact aperture (first critical length); WTZ supplies the explicit floor whose exponent they are |
| RHTower Lévy collars (`WeilLevyBoundaryEscapeCollarPotential`, `WeilLevyCoshPlasticCrossover`) | boundary escape decomposition and the exit tail `Ω = archLevyAntideriv`; WTZ localizes the escape to the collars of each new fold |
| `LatticeSectionTheory`, `ArithmeticOrientationTheory` | Künneth Riemann–Roch, exterior jumps, the archimedean killing potential `archWindowKilling`, aperture transport and the spectral jumps of the ground energy (`TransportInApertureAndTheCeilingLyapunovIdentity`): the analytic control of the tower, beside WTZ's algebraic control |
| `ArithmeticCastelnuovoSeveri`, `ArithmeticOrientationGeometry` | Hecke action, scaling surface, orbit rates, curve towers as base changes; the window algebra is the Hecke action compressed to a window, Adams lifts its base change |
| HTGeometry / RHTower power dilation | `mPart`, `powerDilationRingHom`: the Adams lifts used for the tower's self-similarity |
| RHTower Suzuki / shifted Euler coefficients | the coefficientwise derivative `∂_ω c_ω(n)|₀ = 2Λ(n)` |

WTZ sits between the degeneration (which isolates `H¹` as the one non-Tate piece) and any producer
of positivity: it states exactly what a producer must act on — a module over a finite local algebra
at every length, compatible along small extensions — and exactly where counts stop: at the
derivative in the dimension.

## 11. Success criteria and criteria for contributions

The programme succeeds when the questions of §5 have theorems as answers (done) and when positivity
of the window `h¹` is produced, or its carriers classified, uniformly along the tower through one of:
a positivity of the Tate family that survives the derivative at `k = 0`; a transfer of positivity
across each small extension; a Poincaré inequality for the censored jump process at every length.

A contribution must:
1. be a law along the tower (in `A`, in the level `N`, or across a stage), or a statement on one
   window that the tower structure turns into such a law;
2. say which part of the window it controls: the algebra (arithmetic), the archimedean jumps, the
   pole plane, the atomic lattice;
3. say what it does on fakes (flip twins, shifted products, Epstein data, golden curve);
4. be an identity or a structural inequality, not an estimate losing a factor growing with `A`;
5. be unconditional; equivalences with RH are labelled as such.

## 12. Big picture

A window of length `A` is a module over a finite local algebra, the Dirichlet ring truncated at
`e^A`; the tower is a chain of small extensions, one new fold per integer, generated by the primes,
with the Dirichlet ring as limit, self-similar under dilation through the Adams lifts and with Serre
duality as its Rosati involution. The integers of the window, as atoms, are the regular
representation of that algebra. The Tate flow acts on it by automorphisms; the commutators of the
window zeta operator with the flow are the Jordan counts, the point counts of punctured affine space
over residue rings that the degeneration produces as Tate pieces. Weil's window form is the
derivative of this family at dimension zero, plus the Gamma factor and the pole plane, whose exact
capacity bounds window negativity by `Ae^{A/2}`. Counts in positive dimension are positive for `ζ`
and for fakes alike; what remains is a positivity that survives the derivative at dimension zero,
uniformly along the tower.
