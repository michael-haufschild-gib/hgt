# RH for odd-degree hyperelliptic curves over every finite field of odd characteristic

- **ID:** aet-rh-odd-hyperelliptic-general
- **Stage:** 1-in-progress
- **Type:** THEOREM (paper)
- **Source:** card `3-formalized/rh-split-hyperelliptic-by-counting.md` (split case over `𝔽_p`)
- **Statement:** `F` finite, `q = |F|` odd, `f ∈ F[X]` squarefree of odd degree `m`. The `m − 1`
  reciprocal roots `ω_i` of the L-function of `w(P) = χ(Res(P, f))` satisfy `|ω_i| = √q`, and
  `Σ_{x∈E} χ_E(f(x)) = −Σ ω_i^n` for every extension `E/F` of degree `n`.

## Approach (paper proof)
1. *Norms, any `f`.* For `x ∈ E`, `P = minpoly x` (degree `d`): `N_{E/F}(f(x)) = Res(P, f)^{n/d}`.
   `N_{E/F} = N_{F(x)/F} ∘ N_{E/F(x)}` (`norm_norm`); over an algebraic closure `Ω`,
   `N_{F(x)/F}(f(x)) = Π_{σ : F(x) → Ω} f(σx) = Π_{β ∈ P.aroots Ω} f(β)` (`norm_eq_prod_embeddings`,
   `liftEquiv'`, `P` separable) `= Res(P_Ω, f_Ω)` (`resultant_eq_prod_eval`, `P` monic split)
   `= Res(P, f)` (`resultant_map_map`, injectivity). Hence `Σ_E χ_E(f) = c_n(w)`.
2. *Rationality, odd `m`.* For `k ≥ m`: `h = f₀Q + r` (`f₀ = f/lc`), `Res(f, h)` depends on `r`
   only; `r ↦ c r` (`c` a nonsquare) multiplies `Res(f, r)` by `c^m`, `χ(c^m) = −1`: `s_k = 0`.
3. *Newton* (as in the split case): `c_n = −Σ ω_i^n`, `#ω = m − 1`.
4. *Split case over any finite field* `L` (odd char): as the `𝔽_p` card with `GaloisField` replaced
   by `FiniteField.Extension L p (2k)`, `|E| = (|L|^k)²`.
5. *Descent.* `L` = splitting field of `f`, `r = [L : F]`. For `E = Extension L p n`,
   `[E : F] = rn` and `Σ_E χ_E(f)` is the same sum for `F` and for `L`: so
   `Σ_i (ω_i^r)^n = Σ_j ω'^n_j` for all `n ≥ 1`, both of size `m − 1`; power sums determine the
   multiset (`multiset_eq_of_powerSum_eq_le`): `{ω_i^r} = {ω'_j}`, `|ω'_j| = |L|^{1/2} = q^{r/2}`,
   so `|ω_i| = √q`.

## Lean plan
- `RHTower/HyperellipticLFunction.lean`: step 1 without `hsplit`.
- `RHTower/HyperellipticDegreeSums.lean`: step 2 (`degSumW_eq_zero_of_odd`).
- `RHTower/HyperellipticRiemannHypothesis.lean`: steps 3–4 over any finite `F`.
- `RHTower/HyperellipticDescent.lean`: step 5; Hasse–Weil for all extensions.
- `ArithmeticEffectivityTheory/TheHyperellipticCalibration.lean`: datum over any `F`, any odd `f`.

## Log
- 2026-10-27 — created.
