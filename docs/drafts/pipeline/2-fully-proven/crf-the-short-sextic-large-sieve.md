# Unrestricted fifth-power conjugation and the smooth short sextic large sieve over ℤ[ω]

- **ID:** crf-the-short-sextic-large-sieve
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** `docs/reports/review-1911/todo.md` #12 · `formal/GaloisForLFunctions/CoherenceTheoryOfReciprocityFamilies/`
- **Statement:** For every finite set `s` of primary primes `π ∤ 6` in `O = ℤ[ω]` and **every** `x ∈ O` (coprime or not), `\overline{χ_{∏_s π}(x)} = χ_{∏_s π}(x)^5` and `‖χ_{∏_s π}(x)‖ ≤ 1`; for any real-valued Schwartz weight `f`, `sexticGramEntry f B u₁ u₂` is Hermitian (`\overline{G(u₁, u₂)} = G(u₂, u₁)`), and when `f ≥ 0` any finite family `(s_i)_{i ∈ F}` with coefficients `c_i ∈ ℂ` satisfies the smooth Schur sextic large-sieve inequality `∑_{n ∈ ℤ²} f(Bn) ‖∑_{i ∈ F} c_i χ_{u_i}(n)‖^2 ≤ ∑_{i ∈ F} ‖c_i‖^2 (∑_{n ∈ ℤ²} f(Bn) + ∑_{j ∈ F \setminus \{i\}} ‖G(u_i, u_j)‖)`, where each off-diagonal `‖G(u_i, u_j)‖` is governed by `norm_gramEntry_le`.

## Goal
Extend `\overline{χ_c(x)} = χ_c(x)^5` from coprime residues to all `x ∈ ℤ[ω]` (bridging Hermitian `L²` squares directly to `sexticSymbol · · ^ 5` Gram entries without coprimality sieving) and prove the unconditional smooth Schur large-sieve inequality for sextic character families over `ℤ[ω]`.

## Gates
- [x] 0 → 1  in-progress: exact interfaces in `TheShortSexticGramIsDiagonal.lean` and `TheReflectedGramIsTwistedByTheRowRootNumbers.lean` verified
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [ ] 2 → 3  formalized: Lean module `TheShortSexticLargeSieve.lean`, `lake --old env lean` green, standard axioms only

## Paper Proof (`[PROVED HERE]`)

1. **Unrestricted fifth-power conjugation and unit-disk bound (`conj_sexticSymbol_prod_eq_pow_five`, `norm_sexticSymbol_prod_le_one`).**
   - At a single primary prime `π ∤ 6` (`(π)` maximal, `λ ∉ (π)`, `2 ∉ (π)`, `λ^2 ∣ π - 1`) and any `x ∈ O`: if `IsCoprime x π`, `conj_sexticSymbol_eq_pow_five` and `norm_sexticSymbol_eq_one` give `\overline{χ_π(x)} = χ_π(x)^5` and `‖χ_π(x)‖ = 1`. If `¬ IsCoprime x π`, then `x ∈ (π)` (since `O / (π)` is a field, any nonzero class has an inverse `x y ≡ 1 (mod π)`), so `sexticSymbol_prime` evaluates `complexSexticChar` at `0`, giving `χ_π(x) = 0`, where `\overline{0} = 0 = 0^5` and `‖0‖ = 0 ≤ 1`.
   - Multiplicativity in the denominator (`sexticSymbol_one_denominator`, `sexticSymbol_mul_denominator`) extends both relations to `∏_{π ∈ s} π` for every `x ∈ O`.

2. **Hermitian symmetry of `sexticGramEntry` (`conj_sexticGramEntry`, `norm_sexticGramEntry_symm`).**
   - For real-valued `f`, `\overline{f(Bn)} = f(Bn)` and `\overline{χ_{u₁}(x) χ_{u₂}(x)^5} = \overline{χ_{u₁}(x)} \cdot \overline{\overline{χ_{u₂}(x)}} = χ_{u₁}(x)^5 χ_{u₂}(x)`. Commuting continuous conjugation `Complex.conjCLE` with `tsum` yields `\overline{G(u₁, u₂)} = G(u₂, u₁)` and `‖G(u₁, u₂)‖ = ‖G(u₂, u₁)‖`.

3. **Smooth Schur sextic large sieve (`short_sextic_large_sieve_rowwise`, `short_sextic_large_sieve`).**
   - Pointwise at `x_n = n_0 + n_1 ω` with `w_n = Re f(Bn) ≥ 0`:
     $$w_n \Bigl\|\sum_{i \in F} c_i \chi_{u_i}(x_n)\Bigr\|^2 = w_n \sum_{i \in F} \|c_i\|^2 \|\chi_{u_i}(x_n)\|^2 + \sum_{i \in F} \sum_{j \in F \setminus \{i\}} \operatorname{Re}\!\bigl(c_i \overline{c_j} \, \chi_{u_i}(x_n) \chi_{u_j}(x_n)^5 f(Bn)\bigr).$$
   - Using `‖χ_{u_i}(x_n)‖^2 ≤ 1`, commuting `tsum` with finite sums and `Complex.reCLM`, bounding `Re(c_i \overline{c_j} G(u_i, u_j)) ≤ ‖c_i‖ ‖c_j‖ ‖G(u_i, u_j)‖ ≤ \frac{1}{2}(‖c_i‖^2 + ‖c_j‖^2) ‖G(u_i, u_j)‖`, and symmetrizing via `‖G(u_i, u_j)‖ = ‖G(u_j, u_i)‖` yields the row-wise and uniform large-sieve bounds.

## Log
- 2026-11-20 — complete paper proof recorded in `2-fully-proven`.
