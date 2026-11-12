# Spectral Theory of the Cubic Cover (STCC)

Namespace `GaloisForLFunctions.SpectralTheoryOfTheCubicCover`; umbrella
`SpectralTheoryOfTheCubicCover.lean`. Source: the long columns of the floor bin in
`CoherenceTheoryOfReciprocityFamilies` (CRF, question Q1 = B175).

## 1. Why this field

The cubic-theta probe reads the zeros of `ζ` through a family of rows `u ∈ ℤ[ω]`. CRF reduced the
binding part of its floor bin (B175) to one first moment: the root number of row `u` is
`G(u) γ₂(u)²`, a phase of bounded conductor times the square of the cubic theta coefficient
(`rowRootNumber_eq_thetaPhase_mul_sq`), and the long columns are first moments of these squares over
the rows. Whether they carry a main term of size `U^{2/3}` — and what it is — is a question about the
square of the cubic theta function `θ` on the cubic metaplectic cover of `SL₂` over `ℚ(ζ₃)`.

The tool for squares of automorphic forms is the Rankin–Selberg method: unfold `θ²` against an
Eisenstein series and read the Dirichlet series `Σ_ν T(ν)² N(ν)^{−w}` of the squared Fourier
coefficients from the analytic behaviour of the Eisenstein series. On the cubic cover this needs
three things the corpus does not have together: an unfolding identity on hyperbolic three-space, a
continuation of the cubic Eisenstein series as a function, and a renormalization for `θ²`, which is
not square integrable. MMD has built the spectral side — the quotient, its self-adjoint Laplacian,
a Fredholm pencil below the continuous spectrum, the meromorphic resolvent at `8/9`, the matching of
the Eisenstein series with "seed + resolvent correction", the nonzero residue `θ` and its Fourier
coefficients. STCC builds the Rankin–Selberg layer on top.

## 2. Objects

| Object | Meaning |
|---|---|
| `Γ`, `κ` | the principal level-three group `levelThree ⊂ SL₂(ℤ[ω])` and the cubic Kubota character `κ = complexCharacter` |
| `Γ∞`, `P` | the cusp stabilizer (translations by `3ℤ[ω]`) and a period parallelogram of `3ℤ[ω]` |
| `ℍ³`, `μ`, `v` | hyperbolic three-space, the invariant volume `dx dy dv/v³`, the height |
| multiplier `j` | `F(Mw) = κ(M)^j F(w)`; products add multipliers modulo three |
| `E(w, s)` | the cubic Eisenstein series `Σ_{Γ∞\Γ} κ(M)^{−1} v(Mw)^s`, multiplier `1`, `Re s > 2` |
| `E(w ∣ ψ)` | the incomplete Eisenstein series `Σ_{Γ∞\Γ} κ(M)^{−1} ψ(v(Mw))` for a height profile `ψ` |
| `θ` | the residue of `E` at `s = 4/3`: multiplier `1`, eigenvalue `8/9`, constant term `c v^{2/3}`, Fourier coefficients `T(ν)` |
| constant term | `a₀(F; v) = |P|^{−1} ∫_P F(z + jv) dz` |
| `E_{κ²}`, `E*` | the Eisenstein series of multiplier `2` (the conjugate of `E`), its residue `\overline{θ}` at `4/3`, its constant Laurent coefficient `E*` there |
| `R(F, s)` | the renormalized Rankin–Selberg integral of a function of moderate growth |
| `D(w)`, `S(w)` | `Σ_ν T(ν)² N(ν)^{−w}` and its squarefree part |

## 3. Language

- **Unfolding**: the integral of `F · E(·∣ψ)` over `Γ\ℍ³` is the integral of `F · ψ(v)` over `Γ∞\ℍ³`,
  i.e. the Mellin pairing of `ψ` with the constant term of `F`.
- **Multiplier bookkeeping**: `θ²` has multiplier `κ²`; it pairs with an Eisenstein series of
  multiplier `κ` (`κ³ = 1`), and it is renormalized by one of multiplier `κ²`.
- **Growth exponent**: the power `v^α` of the constant term at a cusp; `θ²` has `α = 4/3`.
- **Coinciding pole**: a growth exponent equal to a pole of the renormalizing Eisenstein series; it
  produces `v^{2/3} log v` in the renormalized constant term.

## 4. Mechanisms

1. *Unfolding on the cubic cover.* A strict fundamental domain for `Γ` and one for `Γ∞`
   (`hyperbolicFundamentalSet_unique`), the invariant volume, and the coset sum of `E(·∣ψ)`.
2. *Continuation by seed and resolvent* (MMD). `E(s) = seed(s) − R(s(2 − s)) defect(s)`, the defect
   compactly supported and entire in `s`; the resolvent exists off the spectrum and is meromorphic at
   `8/9`.
3. *Renormalization.* `θ² − c² E*` has constant term `c² r v^{2/3} log v − c² φ₀ v^{2/3}` plus rapid
   decay, with `r` the residue of the scattering coefficient; it is square integrable.
4. *The double pole.* The Mellin transform of `v^{2/3} log v` has a double pole at `s = 4/3`; so
   `D(w)` has a double pole at `w = 2/3` with leading coefficient `∝ c² r ∝ c³`.
5. *Cube frequencies.* `D(w) = \overline{C}² ζ_K(3w − 1) S(w)` on unramified indices; a double pole of `D`
   is a simple pole of `S`: the squarefree part is coherent at `2/3`.

## 5. Pillar theorems

**From MMD.**

| Theorem | Lean |
|---|---|
| strict fundamental domains for every subgroup of level three; invariant volume | `hyperbolicFundamentalSet_unique`, `hyperbolicFundamentalSet_isFundamentalDomain`, `hyperbolicVolume_invariant` |
| the Eisenstein series as a sum of cusp-height powers; automorphy | `hyperbolicEisenstein_eq_height_series`, `cosetHeight_cosetOf`, `hyperbolicEisenstein_automorphy` |
| the self-adjoint quotient Laplacian; the Fredholm pencil on `0 ≤ λ < 1`; the meromorphic resolvent at `8/9` | `TheCubicVariationalLaplacian`, `TheCubicSpectralPencilIsFredholm`, `kernelSpectralResolvent_meromorphicAt` |
| the Eisenstein remainder equals the resolvent correction (`Re s > 4`, `Im s > 0`) | `TheCubicInitialResolventMatching` |
| the residue `θ` is nonzero, has eigenvalue `8/9` and transforms by `κ` | `TheCubicResidueIsNonzero`, `TheCubicResidualCharacter` |
| the Fourier coefficients of `θ` on squarefree times cube indices | `normalized_sourceFourier_squarefree_cube`, `sourceFourier_squarefree_cube_support_iff` |

**Of this programme.**

| Theorem | Lean | Answers |
|---|---|---|
| unfolding: for `F` of multiplier `κ⁻¹` and any strict fundamental set `D_∞` of `Γ∞`, `∫_{D_Γ} F · E(·∣ψ) = ∫_{D_∞} F · ψ(v)`, with absolute convergence; the complete series `ψ(t) = t^s` | `integral_mul_incompleteEisenstein`, `lintegral_norm_mul_incompleteEisenstein`, `integral_mul_hyperbolicEisenstein`, `cuspSelect` | SQ1 |
| `Γ∞` is the period lattice `3ℤ[ω]`; the period strip is a strict fundamental set; in coordinates `dμ = v^{−3} dv dz` | `translationOf_injective`, `translationOf_surjective`, `cuspStrip_unique`, `cuspStrip_coordinates` | SQ1 |
| the incomplete Eisenstein series reads the constant term: `∫_{D_Γ} F · E(·∣ψ) = ∫_0^∞ ψ(v) (∫_P F(z + jv) dz) v^{−3} dv`; for `ψ = t^s` the Mellin transform of the constant term | `integral_mul_incompleteEisenstein_eq_constantTerm`, `integral_mul_hyperbolicEisenstein_eq_constantTerm` | SQ1, SQ3 |
| the scattering coefficient continues across `4/3`: `(s − 4/3)φ(s)` is holomorphic on `Re s > 1` with value `r ≠ 0` at `4/3`; `Res ζ_K = L(1, χ₋₃)` | `sub_mul_scatteringCoefficient`, `clearedScattering_differentiableOn`, `clearedScattering_four_thirds`, `dedekindZeta_residue_eq` | SQ2, SQ4 |
| the constant term of `E` continues across `4/3` with residue `3πr v^{2/3}`; its constant Laurent coefficient is `v^{4/3} + v^{2/3}(g'(4/3) − 3πr log v)` | `sub_mul_constantTerm`, `clearedConstantTerm_four_thirds`, `hasDerivAt_clearedConstantTerm` | SQ2, SQ4 |
| `θ²` has multiplier `κ⁻¹`; its constant term is `|P|(c² v^{4/3} + Σ_h a(v, h) a(v, −h))`, `c = 3πr`, `a(v, h)a(v, −h) = T(h)T(−h)v²K_{1/3}(4π|ξ_h|v)²`; Rankin–Selberg: `∫_{D_Γ} θ² E(·∣ψ) = |P| ∫_0^∞ ψ(v)(c²v^{4/3} + Σ_h a(v,h)a(v,−h)) v^{−3} dv`, unconditional for continuous `ψ` of compact support in `(0, ∞)` | `thetaSq_automorphy`, `integral_thetaSq_periodDomain`, `thetaAmplitude_mul_neg`, `integral_thetaSq_mul_incompleteEisenstein_of_compact` | SQ3 |

## 6. Questions

| # | Question |
|---|---|
| SQ1 | Unfolding: is `∫_{Γ\ℍ³} F · E(·∣ψ) = ∫_{Γ∞\ℍ³} F · ψ(v)` for every `F` of multiplier `κ^{−1}` with the right integrability? |
| SQ2 | Is `E(w, s)` meromorphic on `Re s > 1` as a function on `ℍ³`, with the single pole `4/3`, and of polynomial growth on vertical lines? |
| SQ3 | The constant term of `θ²`: `c² v^{4/3} + Σ_ν T(ν)T(−ν) W_ν(v)²`, `T(−ν) = T(ν)` |
| SQ4 | The renormalized `R(θ², s)`: continuation past `4/3`, the double pole, its leading coefficient |
| SQ5 | The main term of `Σ_{N(ν) ≤ X} T(ν)² ω(N(ν)/X)` and of the squarefree part `S` |
| SQ6 | The other cusps of `Γ` where `θ` has a constant term |
| SQ7 | The twisted versions read by the long columns: `θ · θ_n` for the column index `n` |

## 7. Traps

| Trap | Truth |
|---|---|
| `⟨θ², E(·, s)⟩` converges for `Re s` large | `θ²` grows like `v^{4/3}` and `E` like `v^s`: it converges for no `s`; unfolding needs incomplete series or renormalization |
| `θ²` pairs with `θ̄` | `θ²` has multiplier `κ²`; the residual eigenfunction of multiplier `κ²` is `\overline{θ}`, and the pairing partner of `θ²` is `E` of multiplier `κ` |
| A growth exponent gives a simple pole | when it coincides with a pole of the renormalizing series it gives a logarithm and a double pole |
| A pole of `D` at `2/3` shows the squarefree part is coherent | the cube frequencies alone give a simple pole; the squarefree part needs the double pole |
| The resolvent continuation covers the real segment `1 < s < 2` | off the real axis self-adjointness suffices; on the segment it needs the Fredholm pencil |

## 8. Tools this programme develops

Unfolding for incomplete and complete cubic Eisenstein series; constant terms on the cusp strip;
the Rankin–Selberg integral of products of automorphic functions with multipliers; renormalization
with coinciding poles; Mellin and contour transfer from the renormalized integral to Dirichlet series
of Fourier coefficients.

## 9. Position in the corpus

| Programme | Relation |
|---|---|
| MetaplecticMobiusDescent | the quotient, its Laplacian, resolvent, Eisenstein series, residue and theta coefficients |
| CoherenceTheoryOfReciprocityFamilies | the consumer: the long columns of the floor bin are first moments of `γ₂²` |
| RHTower (half-weight Rankin–Selberg, Selberg unfoldings) | the same method on `ℍ²` for `SL₂(ℤ)`-type groups |

## 10. Success criteria

1. SQ1 in Lean for incomplete and complete Eisenstein series.
2. The Eisenstein series continued as a function to `Re s > 1` near `4/3`, with growth control.
3. The double pole of `R(θ², s)` at `4/3` with its leading coefficient, unconditionally.
4. A main term for the smoothed first moment of the squarefree squares, and the consequence for
   CRF's Q1.

## 11. What a contribution must be

- It is a theorem about the actual cubic cover (MMD's objects), not a model.
- It proves an analytic identity or estimate that the next step uses.
- It keeps the multiplier bookkeeping explicit.
- It is unconditional; integrability conditions on the functions it treats are part of the statement.

## 12. Open research topics

1. The constant terms of `θ` at all cusps of `Γ` and the scattering matrix at `4/3`.
2. The triple product `∫ θ³` and the next Laurent coefficient of `R(θ², s)`.
3. The products `θ(z) θ(nz)` and their constant terms (the column twists of CRF).
4. Uniformity in the column index (the remainder of the long columns).
