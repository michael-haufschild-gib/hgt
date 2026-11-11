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
| A118a | Poisson in `m`, scalar Euler identity (source Lemma 7.1), principal row = signal | local layer: `TheGaussSumOfAPrimePowerLivesOnOneLayer` (`layerGauss_eq_zero`, `layerGauss_eq`, `layerGauss_one`: lifted Gauss sums mod `π^t`), `ThePoissonCoefficientOfAPrimePowerIsOneGaussSum` (`localPoisson_*`: source (7.8), `P = Q^{t+k} C_p`). Open: global CRT factorization with pair phases, local series = closed form, Poisson identity, contour comparison |
| A118c | uniform saving | open |
| A118d | reflection of the theta row, quadratic/sextic large sieves, detector | open |

## Arithmetic of A118a (source §4.2, §7.2), native order
1. layer Gauss sums mod `π^t` — done; 2. local Poisson coefficient (7.8) — done;
3. quadratic reciprocity `η_p(q)η_q(p)Γ(p)Γ(q) = Γ(pq)` — done (`TheQuadraticSymbolsOfTheEisensteinIntegersAreReciprocal`);
4. sextic reciprocity at primes `χ_q(p)Γ(p)Γ(q) = Γ(pq)χ_p(q)` — done (`TheSexticSymbolsAreReciprocalUpToTheQuadraticPhase`);
5. `r(a,b) = Γ(ab)/(Γ(a)Γ(b))` a ±1 bicharacter on odd classes, `Γ(cd²) = Γ(c)`, `Γ⁴ = 1` — done (`TheQuadraticPhaseIsABicharacterModuloFour`, finite identities by kernel `decide` over coordinates mod 4); open: `r(p,p) = χ_p(−1)`;
6. composite sextic symbols, composite reciprocity `χ_b(a) = r(a,b)χ_a(b)` — done (`TheCompositeSexticSymbolsAreReciprocal`: `quadSymbol`, `sexticSymbol`, `quadSymbol_reciprocity`, `sexticSymbol_reciprocity`); binary Poisson CRT — done (`ThePoissonCoefficientSplitsOverCoprimeModuli`);
7. composite `γ_j(c)` (squarefree) and CRT `γ_j(ab) = χ_a(b)^jχ_b(a)^jγ_j(a)γ_j(b)`;
8. prime identities `γ₂³ = −α`, `γ₁γ₂ = χ(4)γ₃γ₂³` (MMD Hasse–Davenport), (4.7);
9. `G(c) = χ_c(4)Γ(c)`: `G(vw) = G(v)G(w)r(v,w)`, `G(p³) = γ₃(p)`;
10. CRT of the Fourier transform of `m ↦ ξ(m)χ_A(m)g_{χ_s}(s,−m)` with unit factors (7.9);
11. local series (table 7.16) = closed form (7.11); global `F_{η,u} = ζ^S(6z)L^S(w)/L^S(x)·H_{η,u}`.
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

## Log
- 2026-11-11 — created; frame defect found; closed form of the principal local factor checked
  against the source (Lemma 7.1 at `u = 1`) and the external `continuedCorrection`.
