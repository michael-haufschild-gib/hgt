# The native half-plane: tasks A118a–d

- **ID:** native-half-plane-a118
- **Stage:** 1-in-progress
- **Type:** THEOREM (Lean), in parts
- **Source:** docs/reports/review-1111/obstacles-summary.md §2.1 "The native half-plane (given `[X]`)"
- **Statement:** make the two-estimate route to `Θ ≤ 7/8` native: corrections `H_η` (A118b),
  comparison with cube indices (A118a), uniform saving (A118c), direct bound (A118d).

## Goal
Each task closed by an unconditional Lean theorem in the native graph, built from corpus blocks.
The external source `[X]` (text `logs/review-2410-current-audit/quasi-rh-seven-eighths.txt`) is a
mathematical guide only; no external code enters the corpus.

## Frame defect (found 2026-11-11)
The family step of `FamilyContinuationTheory` runs on `heckePoleCleared = (s−1)L(s,η)`. For a
nonprincipal `η` this has the value `0` at `s = 1` (`heckeThetaPoleCoefficient = 0`). Hence
for `β < 1` the zero-free premise of `hstep` is false, and at `β = 1` the required estimates
would continue `exp·H/((s−1)L)` across its pole at `1`: the premise of
`zetaZeroAbscissa_le_of_two_estimates`, `heckeHalfPlane_of_family_corrected_signal`,
`heckeHalfPlane_of_family_height_estimates`, `heckeHalfPlane_of_family_common_signal`,
`heckeLFunction_ne_zero_of_family_common_signal_all` is unsatisfiable as soon as `K` has a
nonprincipal ray class character. Fix: kernel `exp((s−c)²) H(s)/L(s,η)` (the source's form),
zero-free premise on `L` off `1`, and the family step with `E ≠ 0` required only at zeros of
`L` (principal character: `L_native = (s−1)L`, `E = exp·H·(s−1)`).

## Status
| Task | Content | Lean |
|---|---|---|
| frame | family step on the zeros of `L`; kernels `exp·H/L` | `FamilyContinuationTheory/TheFamilyStepReadsTheZerosOfTheLFunctions`: `heckeHalfPlane_of_family_reciprocal_signal`, `…_reciprocal_height_estimates`, `zetaZeroAbscissa_le_of_two_reciprocal_estimates`, `heckePoleCleared_one_of_ne_one` |
| A118b | `H_η = ∏_{P∉S} h_P` at `w = 1, z = 1/6`; `h = (1−q²)(1 − q(R−D)/(1−D))/(1−R)`, `q = N(P)⁻¹`, `D = η(P)N(P)^{−s}`, `R = A_P N(P)^{3−6s}`, `‖A_P‖, ‖η(P)‖ ≤ 1`; converges on `Re s > 2/3` | `FamilyContinuationTheory/TheCorrectionOfThePrincipalRowIsAConvergentEulerProduct`: `norm_principalLocalFactor_sub_one_le` (`‖h−1‖ ≤ 14 N^{−e}`, `e = min(6σ−3,1+σ,2)`), `exists_principalCorrection_cutoff` (`‖H−1‖ ≤ ½` on `Re s > σ`, any `σ > 2/3`), `exists_fullPrincipalCorrection_cutoff`, endpoint `exists_cutoff_zetaZeroAbscissa_le_of_two_estimates` (only premise: the two estimates). Phases arbitrary of modulus `≤ 1`; the actual phase `A_P = conj(α(π))⁶η(P)⁶` enters with A118a |
| A118a | Poisson in `m`, scalar Euler identity (source Lemma 7.1), principal row = signal | arithmetic: layer Gauss sums, local Poisson values, reciprocity, multiplicativity (`correctedCoeff_mul`), prime Gauss identities (`ThePrimeGaussIdentitiesFixTheLocalPhases`), explicit prime-power values (`ThePoissonCoefficientOfAPrimePowerIsExplicit`), **complete local identity** `hasSum_localTerm` and absolute convergence `hasSum_norm_localTerm` (`TheLocalFactorOfThePoissonSeriesIsExplicit`: all `j < 6`, unit twist `ρ`, `X, Y, V` free with `‖V‖, ‖ρY‖, ‖R‖ < 1`); general Euler product `hasProd_tsum_eulerTerm` (`TheSeriesOfAMultiplicativeFunctionIsItsEulerProduct`: exponent vectors `ι →₀ V`, summable excess masses). Open: global identity (7.13) (principal row: `H_v` at `(1, 1/6)` = `principalLocalFactor`; rows `u ≠ 1` need `a ↦ χ_a(u)` as a ray class character, source Lemma 4.1, via composite reciprocity and unit supplements), Poisson identity (7.5), contour comparison |
| A118c | uniform saving | open |
| A118d | reflection of the theta row, quadratic/sextic large sieves, detector | open |

## Arithmetic of A118a (source §4.2, §7.2), native order
1. layer Gauss sums mod `π^t` — done; 2. local Poisson coefficient (7.8) — done;
3. quadratic reciprocity `η_p(q)η_q(p)Γ(p)Γ(q) = Γ(pq)` — done (`TheQuadraticSymbolsOfTheEisensteinIntegersAreReciprocal`);
4. sextic reciprocity at primes `χ_q(p)Γ(p)Γ(q) = Γ(pq)χ_p(q)` — done (`TheSexticSymbolsAreReciprocalUpToTheQuadraticPhase`);
5. `r(a,b) = Γ(ab)/(Γ(a)Γ(b))` a ±1 bicharacter on odd classes, `Γ(cd²) = Γ(c)`, `Γ⁴ = 1` — done (`TheQuadraticPhaseIsABicharacterModuloFour`, finite identities by kernel `decide` over coordinates mod 4); open: `r(p,p) = χ_p(−1)`;
6. composite sextic symbols, composite reciprocity `χ_b(a) = r(a,b)χ_a(b)` — done (`TheCompositeSexticSymbolsAreReciprocal`: `quadSymbol`, `sexticSymbol`, `quadSymbol_reciprocity`, `sexticSymbol_reciprocity`); binary Poisson CRT — done (`ThePoissonCoefficientSplitsOverCoprimeModuli`);
7. composite `γ_j(c)` (squarefree) and CRT `γ_j(ab) = χ_a(b)^jχ_b(a)^jγ_j(a)γ_j(b)`; sextic Gauss sums `g_c` (any `c`): CRT and unit twist — done (`TheSexticGaussSumsAreTwistedMultiplicative`);
8. prime identities — done (`ThePrimeGaussIdentitiesFixTheLocalPhases`: `G₁G₅ = εQ`, `Γ² = η(−1)`, `r(π,π) = ε`, `c₄G₁G₂ = −πG₃`; `TheLocalFactorOfThePoissonSeriesIsExplicit`: `G₂G₄ = Q`, `G₃ = NΓ`, `c₄³ = 1`);
9. `G(c) = χ_c(4)Γ(c)`: `G(vw) = G(v)G(w)r(v,w)` — done; `γ₂` CRT — done; pair phases cancel (`pairPhase_eq_one`: cube indices drop out, `χ⁶ = 1`) and `correctedCoeff_mul` (`K = R(A,s)γ₂(c)G(A)F(s,A;H)` multiplicative) — done (`TheThetaCoefficientCancelsThePairPhases`); open: `G(p³) = γ₃(p)`, prime identities (8) for the local values;
10. CRT of the Fourier transform of `m ↦ χ_A(m)g_s(−m)`: `poissonCoeff_mul_reciprocity` — done (`ThePoissonCoefficientIsMultiplicativeUpToReciprocity`); open: `ξ`, `b*` at `S`, unit factors at each prime (7.9);
11. local series (table 7.16) = closed form (7.11) — done (`hasSum_localTerm`; families geometric in `R` by `localTerm_shift`); open: global `F_{η,u} = ζ^S(6z)L^S(w)/L^S(x)·H_{η,u}`.
Analytic after: Poisson on `O` with annular weight, contour moves, principal row = signal (Lemma 10.5).

## Multiplicativity of the Poisson coefficient (paper proof, native normalization)
`F(s,A;H) = Σ_{m mod sA} χ_A(m) g_s(−m) ψ_{sA}(Hm)`, `g_s(h) = Σ_{d mod s} χ_s(d)ψ_s(hd)`, all indices
good primary. For coprime splits `s = s₁s₂`, `A = A₁A₂`, `(s₁A₁, s₂A₂) = 1`, `Mᵢ = sᵢAᵢ`:
- Gauss CRT (`d = s₂d₁ + s₁d₂`): `g_{s₁s₂} = χ_{s₁}(s₂)χ_{s₂}(s₁) g_{s₁} g_{s₂}`; twist `g_s(−ux) = χ̄_s(u) g_s(−x)`.
- Poisson CRT (`ThePoissonCoefficientSplitsOverCoprimeModuli`):
  `F(s,A;H) = R(A₁,s₂)R(A₂,s₁)·R(A₁,A₂)χ_{A₁}(A₂)²·F(s₁,A₁;H)F(s₂,A₂;H)` after sextic reciprocity
  `χ_b(a) = R(a,b)χ_a(b)`; the `s`–`s` phases cancel exactly.
- With the probe's `R(A,s)` (bicharacter): `R(A,s)F(s,A;H)` has only the `A`–`A` phase `R(A₁,A₂)χ_{c₁}(c₂)²`
  (`A = cn³`). The theta factor `γ₂(c)G(A)` contributes `χ_{c₁}(c₂)⁴R(A₁,A₂)`; total `χ_{c₁}(c₂)⁶ = 1`.
So `K = R(A,s)γ₂(c)α(A)G(A)η(A)·F(s,A;H)` is multiplicative in `(s, A)`; the dependence on the unit part
of `H` at each prime is the local twist of `localPoisson`.

## Local factor at `u = 1` (paper proof, native definitions)
Source conventions (read the PDF, the text extraction drops overlines): `G(c) = conj(χ_c(4))Γ(c)`,
`γ₁γ₂ = conj(χ(4))γ₃γ₂³` (= MMD `gauss_sextic_relation`); probe coefficient
`γ₂(c)·conj(α(A)G(A))·η(A)Ξ(A)⁻¹R(A,s)`, `a_p = conj(α(p))³η(p)³`, `D = η(p)·conj(χ_p(u))Q^{−x}`.
Native local coefficient at a good prime `π` (`H = π^{6m}`, weights `Q^{−(x+½)e₀−(1+3x)l−(1+w)k−6zm}`,
`t = e₀+3l`): `conj(α)^tη^t·r(π,π)^{tk}·γ₂(π)^{e₀}·G(π^t)⁻¹·F(π^k,π^t;π^{6m})`, `F = Q^k C_p`.
Rows: `(0,0)`: `1/(1−V) + W/(1−W)`; `(0,2r+2,k=0)`: `R^{r+1}(1−q)V^{m−r−1}` (`G(π^{6r+6}) = 1`);
`(0,2r+2,k=1,m=r+1)`: `WR^{r+1}` (`G₁G₋₁ = ωQ`, `r(π,π)^{even} = 1`);
`(1,2r,k=0,m=r)`: `−ηQ^{−x}R^r` (`G(π^{6r+1}) = G(π)`, `γ₁γ₂ = −αG(π)`);
`(1,2r,k=1,m≥r+1)`: `−η(Q−1)Q^{−x−w}R^rV^{m−r}` (`r(π,π) = χ(−1)`); odd `l` rows vanish at `j = 0`.
Sum = source (7.11) at `j = 0`; with `(1−V)(1−W)/(1−D)` it is `principalLocalFactor` at `w = 1, z = 1/6`.

## Log
- 2026-11-11 — created; frame defect found; closed form of the principal local factor checked
  against the source (Lemma 7.1 at `u = 1`) and the external `continuedCorrection`.
