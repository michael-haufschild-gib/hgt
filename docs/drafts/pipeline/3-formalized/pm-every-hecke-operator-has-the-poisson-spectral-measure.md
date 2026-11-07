# PM — the whole Hecke algebra has the Poisson spectral measure on a resonant state

- **ID:** pm-all-n-hecke-moments (review-0711 A25)
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Statement:** For the classical Hecke operator `T_n F(x,y) = n^{-1/2} Σ_{ad=n} Σ_{b<d} F((ax+b)/d, ay/d)`, a resonant state `t_Y = Λ^Y E_u` (`Λ(1+2u)=0`, `Re u<0`) and `Y ≥ n, m`:
  `⟨T_n t_Y, T_m t_Y⟩ = ‖t_Y‖² ∫ P_{−Re u}(t−Im u) W_{it}(n) W_{it}(m) dt = ‖t_Y‖² Σ_{d∣(n,m)} μ_{nm/d²}(u)`, and `⟨T_n t_Y, t_Y⟩ = μ_n(u)‖t_Y‖²` for every `n`.

## Proof
1. **Hecke recursion on periodic functions.** For `F` `1`-periodic in `x`, `T_pT_n = T_{pn} + 1_{p∣n}T_{n/p}`. The branch `F(px,py)` gives the representatives `(pa,d)`. The residue branch is `Σ_{b<p}Σ_{c<d} F((ax+ab+pc)/(pd), ay/(pd))`. If `p∤a`, `(b,c) ↦ ab+pc mod pd` is injective (reduce mod `p`, cancel `a`; then cancel `p`), hence a complete residue system, and periodicity gives the representative `(a,pd)`. If `a=pa₁`, the argument is `(a₁x+a₁b+c)/d`; a period sum is translation invariant, so this is `p` copies of the `(a₁,d)` orbit. The representatives of `pn` split as `p∣A` or `p∤A, p∣D`; the extra `p` copies carry the normalization `p/√(pn) = 1/√(n/p)`.
2. **Eigen-equation.** Strong induction on `n = p·m`, `p = minFac n`: `T_nE = T_p(W(m)E) − 1_{p∣m}W(m/p)E = (W(p)W(m) − 1_{p∣m}W(m/p))E = W(pm)E` by `whittakerCoeff_hecke`.
3. **Truncation.** At `Λ(1+2u)=0` the constant term is `B y^{½−u}`. A representative sends `1_{y>Y}` to `1_{y>Yd/a}` and `n^{-1/2}d(ay/d)^{½−u} = (d/a)^u y^{½−u}`. With step 2, `T_n t_Y = Σ_{ad=n}(d/a)^u t_{Yd/a}`, a sum of translations by `log(d/a)` of the stationary family `S(x) = e^{ux}t_{Ye^x}`.
4. **Gram.** `⟨S(x),S(x′)⟩ = ‖t_Y‖² e^{−σ|x−x′|+it₀(x−x′)}` is the Fourier transform of the Poisson kernel; `Σ_{ad=n}(d/a)^{it} = W_{it}(n)` and `W` is even in the parameter. The product law `W(n)W(m)=Σ_{d∣(n,m)}W(nm/d²)` gives the last form.

## Lean
`formal/GaloisForLFunctions/RenormalizedIntersectionTheory/ResonantStates/`:
- `EveryHeckeOperatorIsDiagonalOnEisenstein.lean`: `heckeN`, `heckeN_prime`, `sum_crt`, `heckeOp_heckeN`, `heckeN_cuspLeg`.
- `TheHeckeAlgebraHasThePoissonSpectralMeasure.lean`: `heckeN_truncatedLeg`, `integral_heckeN_mul_conj_heckeN`, `integral_heckeN_mul_conj_eq_resonantHeckeMoment`, `integral_heckeN_mul_conj_heckeN_eq_sum_gcd`.

Both checked with `lake --old env lean`; no hypotheses beyond the resonance data of the state.

## Scope
This removes the squarefree restriction of `integral_heckeWord_mul_conj_eq_resonantHeckeMoment`. It is a statement about one resonant state; it gives no sign for the PM obstacles B68–B71.
