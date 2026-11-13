# Artin's Euler factors under induction

- **ID:** agz-artin-induction
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** docs/reports/review-1211/obstacles-summary.md §2.14 question 4 (A154)
- **Statement:** For `H ≤ G = Gal(L/K)`, `M = L^H` and a representation `ρ` of `H`, the local
  Euler factor of `Ind_H^G ρ` at a prime `p` of `K` is the product over the primes `q | p` of
  `M` of the local factors of `ρ` at `q` in the variable `T^{f(q|p)}`; hence
  `L(s, Ind ρ, L/K) = L(s, ρ, L/M)` for `Re s > 1`.

## Goal
First half of A154. With `brauer_induction` every Artin `L`-function becomes a product of
integer powers of Artin `L`-functions of linear characters over intermediate fields. What then
remains of A154 is the reciprocity law for a linear character (class field theory), which is not
attempted here.

## Gates
- [x] I1 group theory: the Frobenius traces of an induced function; the residue degree as an index
- [x] I2 linear algebra: the Frobenius trace of a character is the trace on the inertia
  invariants; a polynomial with constant term `1` is determined by its power sums; the local
  Euler polynomial of an induced representation
- [x] I3 arithmetic: primes of the intermediate field, residue degrees, Frobenius elements; the
  Euler products for `Re s > 1`

## Approach

Notation: `G` finite, `I ≤ G`, `φ` in the normalizer of `I`, `χ : G → ℂ`,
`S(χ; I, g) = Σ_{τ∈I} χ(gτ)` (sum over the coset `gI`),
`a_m(χ; I, φ) = S(χ; I, φ^m)/|I|`. For a representation `V` with character `χ`,
`a_m = tr(φ^m | V^I)` and `det(1 − Tφ | V^I)^{-1} = exp(Σ_m a_m T^m/m)`.

**I1.** Let `H ≤ G`, `ψ : H → ℂ`, `ψ°` its extension by zero.
(a) `A = {m : φ^m I ∩ H ≠ ∅}` contains `0`, is closed under addition, and `m + n, n ∈ A` give
`m ∈ A`: `(φ^mτ)(φ^nτ') = φ^{m+n}(φ^{−n}τφ^n)τ'` and
`(φ^{m+n}τ)(φ^nτ')^{−1} = φ^m(φ^n ττ'^{−1} φ^{−n})`. It contains `ord φ > 0`. So `A = fℕ`,
`f = min(A ∖ 0)` (division with remainder).
(b) Let `φ' ∈ H`, `φ' = φ^fτ₀`, `τ₀ ∈ I`. Then `φ'^k = φ^{fk}τ_k` with `τ_k ∈ I` (induction, `φ^f`
normalizes `I`), so `φ^{fk}I = φ'^kI` and `S(ψ°; I, φ^{fk}) = S(ψ°; I, φ'^k)`. Since `φ' ∈ H`,
`φ'^kτ ∈ H` iff `τ ∈ H`: `S(ψ°; I, φ'^k) = S(ψ; H ∩ I, φ'^k)`, the coset sum in `H`.
(c) If `f ∤ m` no element of `φ^mI` lies in `H`: `S(ψ°; I, φ^m) = 0`.
(d) `(Ind ψ)(g) = |H|^{-1} Σ_x ψ°(xgx^{-1})`, so
`S(Ind ψ; I, g) = |H|^{-1} Σ_{x∈G} S(ψ°; xIx^{-1}, xgx^{-1})`. With (b), (c) for the pair
`(xIx^{-1}, xφx^{-1})`: residue degree `f_x`, Frobenius `φ_x ∈ H`, inertia `I_x = H ∩ xIx^{-1}`,

  `S(Ind ψ; I, φ^m) = |H|^{-1} Σ_{x∈G, f_x | m} S(ψ; I_x, φ_x^{m/f_x})`.

The summand is constant on the double cosets `HxD`, `D = ⟨φ⟩I`, which have `|H||D|/|H ∩ xDx^{-1}|`
elements, and `[D:I] = f_x [H ∩ xDx^{-1} : I_x]`; so
`a_m(Ind ψ; I, φ) = Σ_{HxD, f_x | m} f_x a_{m/f_x}(ψ; I_x, φ_x)`, which is
`Π_x det(1 − T^{f_x}φ_x | W^{I_x})` for the Euler polynomials. ∎

(e) Index. Let `D = ⋃_m φ^mI` and `n` the least positive exponent with `φ^n ∈ I`. The cosets of
`I` in `D` are `φ^mI`, `m < n` (distinct: `φ^{m'−m} ∈ I` gives `n | m' − m`). By (b), (c) with
`ψ = 1`, `|H ∩ φ^mI| = |H ∩ I|` if `f | m` and `0` otherwise, and `f | n`. So
`|H ∩ D| = (n/f)|H ∩ I|`, and `|D| = n|I|`. ∎

Lean (I1): `formal/GaloisForLFunctions/RHTower/Artin/ArtinFrobeniusTracesOfAnInducedFunction.lean`
(`cosetSum`, `frobeniusTrace`, `cosetSum_mul_mem`, `exists_pow_mul_mem`, `CosetMeets`,
`residueDegree`, `cosetMeets_iff_dvd`, `residueDegree_eq_of_dvd`, `cosetSum_extendByZero_coe`,
`cosetSum_extendByZero_pow`, `cosetSum_extendByZero`, `conj_mem_normalizer_map_conj`,
`sum_conj_eq_cosetSum`, `cosetSum_inducedFunction`, `residueDegreeAt`, `frobeniusAt`,
`cosetSum_inducedFunction_pow`, `frobeniusTrace_inducedFunction`, `cosetSum_one_eq_sum_range`,
`card_subgroupOf_mul_residueDegree`, `card_eq_card_mul_residueDegree`).

**I2.** Power traces. For `P ∈ ℂ[X]` say `a` are power traces of `P` if
`P · Σ_{m≥0} a_m X^m = a_0 P − X P'` in `ℂ[[X]]` (for `P(0) = 1`: `−XP'/P = Σ_{m≥1} a_m X^m`).
(a) `1 − tX` has `a_m = t^m`: `(1 − tX) Σ t^m X^m = 1`. Products add power traces (Leibniz).
`P(X^f)` has `b_m = f a_{m/f}` for `f | m`, `0` otherwise: `Σ b_m X^m = f (Σ a_m X^m)(X^f)` and
`X (P(X^f))' = f X^f P'(X^f)`.
(b) Newton. Coefficient `n+1`: `(n+1) p_{n+1} = −Σ_{i+j=n} p_i a_{j+1}`. So `a` and `p_0`
determine `P`; and `P` with `p_0 = 1` determines `a_m`, `m ≥ 1` (`ℂ[[X]]` is a domain).
(c) `det(1 − XA)` has `a_m = tr A^m`: triangulate, `det(1 − XA) = Π(1 − t_iX)`,
`tr A^m = Σ t_i^m`, and (a).
(d) For `I ⊴ Γ` the mean `e = |I|^{-1} Σ_{τ∈I} ρ(τ)` is a projection onto `V^I`, so
`tr(g | V^I) = tr(ρ(g) e) = |I|^{-1} Σ_τ χ(gτ)`. Hence `det(1 − Xφ | V^I)` has the power traces
`a_m(χ; I, φ)` and is the only polynomial with constant term `1` that has them.
(e) Weights. For `x ∈ G`: `D_x = H ∩ xDx^{-1}`. By I1(e) for the conjugate pair,
`|D_x| f_x = |I_x| n` and `|D| = n|I|`, so `|D_x| f_x |I| = |I_x| |D|` and
`a_m(Ind ψ; I, φ) = (|H||D|)^{-1} Σ_{x, f_x | m} |D_x| f_x a_{m/f_x}(ψ; I_x, φ_x)`.
(f) Double cosets. For `x = h_0 y d_0`: `u ↦ h = u^{-1}h_0` maps `D_x` onto
`{h ∈ H : y^{-1}h^{-1}x ∈ D}`, and no such `h` exists off `HyD`. So
`Σ_{x∈HyD} |D_x| = Σ_{h∈H} #{x : y^{-1}h^{-1}x ∈ D} = |H||D|`.
(g) Artin's formula. Let `π : G → Q` be onto with fibres the double cosets `HyD`, `f_x = f_{π x}`,
and `R_q` (`R_q(0) = 1`) with the power traces `a_m(ψ; I_x, φ_x)` for `π x = q`. By (a) the
product `Π_q R_q(X^{f_q})` has the power traces `Σ_q [f_q | m] f_q a_{m/f_q}(R_q)`; by (e), (f)
and (b) these are `a_m(Ind ψ; I, φ)` for `m ≥ 1`. By (b), `P = Π_q R_q(X^{f_q})` for every `P`
with `P(0) = 1` and these power traces, in particular `det(1 − Xφ | V^I)` when `χ_V = Ind ψ`. ∎

Lean (I2): `formal/GaloisForLFunctions/RHTower/Artin/ArtinLocalEulerPolynomialFromFrobeniusTraces.lean`
(`HasPowerTraces`, `hasPowerTraces_one_sub_C_mul_X`, `HasPowerTraces.mul`, `.congr`, `.expand`,
`.coeff_succ`, `.eq_of_coeff_zero`, `.traces_eq`, `hasPowerTraces_prod`,
`exists_multiset_charpoly_reverse_eq`, `hasPowerTraces_charpoly_reverse`, `subgroupMean`,
`trace_toInvariants`, `trace_toInvariants_pow`, `hasPowerTraces_localEulerPolynomial`,
`hasPowerTraces_localEulerPolynomial_restrict`) and
`formal/GaloisForLFunctions/RHTower/Artin/ArtinLocalEulerPolynomialOfAnInducedCharacter.lean`
(`mem_map_conj_iff_exists_pow_mul`, `card_decomposition_mul_residueDegreeAt`,
`frobeniusTrace_frobenius_eq`, `frobeniusTrace_inducedFunction_weighted`,
`sum_card_decomposition_doubleCoset`, `eulerPolynomial_induced_eq_prod`,
`localEulerPolynomial_induced_eq_prod`).

**I3.** Rings `A ⊂ B ⊂ C`, `G` finite acting on `C` with `C^G = A`, `H ≤ G` with `C^H = B`,
`Q` a prime of `C` with finite residue field, `p = Q ∩ A`, `D = G_Q`, `I = I_Q`, `φ` a Frobenius
element at `Q` (`φc ≡ c^{|A/p|} mod Q`).
(a) `D = ⋃_m φ^m I`: the kernel of `D → Aut(C/Q | A/p)` is `I`, the image of `φ` is
`x ↦ x^{|A/p|}`, and this generates the Galois group of the finite field `C/Q` over `A/p`.
(b) Fibres. `xQ ∩ B = yQ ∩ B` iff `x ∈ HyD` (`H` is transitive on the primes of `C` above a
prime of `B`).
(c) Residue degree. For `w = Q ∩ B`: `|D| = |I| f(Q|p)` and `|D ∩ H| = |I ∩ H| f(Q|w)`; by I1(e)
`|D ∩ H| f = |I ∩ H| n` with `n = [D : I] = f(Q|p)`. So `f = f(Q|p)/f(Q|w) = f(w|p)`.
(d) Frobenius of `H`. `φ_H c ≡ c^{|B/w|}`, `|B/w| = |A/p|^{f(w|p)}` and `φ^f c ≡ c^{|A/p|^f}`, so
`φ^{−f}φ_H ∈ I`.
(e) Local formula. The pair `(xIx^{-1}, xφx^{-1})` is the inertia group and a Frobenius element
at `xQ`. By (a)–(d) and I2(g) for `π(x) = xQ ∩ B`:
`det(1 − Xφ | V^I) = Π_{w | p} det(1 − X^{f(w|p)} φ_{Q_w} | W^{I_{Q_w} ∩ H})`.
(f) Number fields `K ⊂ M ⊂ L`, rings of integers. The primes of `M` above `v` are the
`xQ ∩ 𝓞_M` (a prime of `M` lies below a prime of `L`; `G` is transitive above `v`), and
`N(w) = N(v)^{f(w|v)}`. So `P_v(ρ; N(v)^{-s})^{-1} = Π_{w|v} P_w(σ; N(w)^{-s})^{-1}`. For
`Re s > 1` the product over the primes of `M` converges absolutely; regrouping along the fibres
of `w ↦ w ∩ K` gives `L(s, ρ, L/K) = L(s, σ, L/M)`. ∎

Lean (I3): `formal/GaloisForLFunctions/RHTower/Artin/ArtinLocalEulerFactorOfAnInducedRepresentation.lean`
(`mk_pow_smul_eq_pow`, `exists_pow_inv_mul_mem_inertia`, `mem_stabilizer_iff_exists_pow_mul`,
`hasPowerTraces_frobeniusInertiaEulerPolynomial`, `under_smul_eq_iff`,
`residueDegree_inertia_eq_inertiaDeg`, `frobenius_subgroup_eq_pow_mul`,
`frobeniusInertiaEulerPolynomial_induced_eq_prod`) and
`formal/GaloisForLFunctions/RHTower/Artin/ArtinEulerProductOfAnInducedRepresentation.lean`
(`isGaloisGroup_subgroup_ringOfIntegers`, `absNorm_eq_absNorm_under_pow_inertiaDeg`,
`finitePlacesAbove`, `exists_smul_under_eq_asIdeal`,
`numberFieldFinitePlaceLocalEulerPolynomial_induced`,
`numberFieldFinitePlaceArtinEulerReciprocal_induced`,
`numberFieldFinitePlaceArtinEulerReciprocalProduct_induced`).

## Log
- 2026-11-13 — created; I1–I3 proved and formalized
