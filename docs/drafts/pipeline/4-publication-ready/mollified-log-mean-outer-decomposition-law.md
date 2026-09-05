# The mollified log-mean of zeta: outer decomposition law, torus Jensen mass, and the Gaussian head

- **ID:** `mollified-log-mean-outer-decomposition-law`
- **Stage:** 4-publication-ready
- **Type:** theorem + reformulation of an open problem
- **Knowledge label:** `[NEW THEOREM] [NEW LEAN FORMALISATION] [FORMALISED] [OPEN CORE ISOLATED]`
- **Source boundary:** Conrey's mollified second moment `1 + 1/θ` (literature) is used only as a
  numerical calibration and in the corpus's earlier `(L)` ceiling; the CFZ ratios recipe is used
  only for the conjectural constant `c₄(θ)`. Every statement below marked Lean is unconditional.

## Closed claim

Let `Ψ_M(s) = ∑_{h≤M} μ(h) (log(M/h)/log M) h^{-s}` and, for a function `F` on the critical line,
`ℓ_F(T) := (1/T)∫_T^{2T} log|F(1/2+it)| dt`. Let `(L)` be the statement `ℓ_ζ(T) → 0`, which by
Littlewood's lemma is `∑_{β>1/2, γ≤T}(β − 1/2) = o(T)` (Selberg's density gives only `O(T)`).

1. **Decomposition (Lean).** `ℓ_{ζΨ} = ℓ_ζ + ℓ_Ψ` on every segment of the line (finitely many zeros
   on the segment), for every unit-head Dirichlet polynomial `Ψ`.
2. **Floors (Lean).** `−(C + K log T) ≤ T·ℓ_ζ(T)` at every height `T ≥ 20` (admissible heights are
   dense, both sides continuous); `−(C + K log Mb) ≤ ∫_{T₁}^{T₂} log|Ψ(1/2+it)| dt` uniformly in the
   heights for every bounded unit-head `Ψ`. Hence `ℓ_ζ ≤ ℓ_{ζΨ} + o(1)`: an outer law
   `ℓ_{ζΨ}(T) → 0` for any such mollifier implies `(L)`.
3. **Two-sided window torus law (Lean).** For every real bounded unit-head Dirichlet polynomial with
   line coefficients `a_n = Re(b_n)/√n` and truncated Steinhaus Jensen mass
   `J(ε) = ½ E_χ log max(|∑ a_n χ(n)|², ε²)`: for all `ε ∈ (0,1)`, `η > 0`, eventually
   `J(ε) − η − D/log(1/ε) ≤ ℓ_Ψ(T) ≤ J(ε) + η`. Upper side: continuous Bohr transfer (Weierstrass
   on the corpus even-moment tower). Lower side: the small-values estimate
   `∫_{T₁}^{T₂} max(log ε − log|Ψ|, 0) ≤ (C₁(T₂−T₁) + C₂(1+|T₁|+|T₂|))/log(1/ε)`, from the
   interior lower bound `log|Ψ(w)| ≥ −C + ∑ m_a log|(w−c₀)−a|` (zero-free cofactor factorization
   and minimum modulus on the ball of radius 9 about `8+it`) and a linear strip zero count.
4. **Equivalence (Lean).** For every fixed `M > 1`:
   `(L) ⟺ ∀ε∈(0,1) ∀η>0: eventually ℓ_{ζΨ_M}(T) ≤ J_M(ε) + η`, and under `(L)` the mollified
   log-mean is squeezed between `J_M(ε) − D_M/log(1/ε) − η` and `J_M(ε) + η`.
   *Scope of the claim:* for fixed `M` this is (1) together with (3); it does not bear on `(L)` beyond
   isolating the residue. The `(L)`-productive regime is `M = T^θ`, where the needed statement is
   the torus law uniformly in `M`; the small-values constants are already `(log M)^4`-uniform, the
   Weierstrass-based transfer is not.
5. **The torus constant (computation, not Lean).** For the linear mollifier `J_M ≈ 0`
   (`≤ 0.005` at `M ≤ 10⁴`, `−0.002 ± 0.012` at `M = 3·10⁵`); for the sharp Möbius sum
   `J_M = 0.34, 0.43, 0.50` at `M = 10², 10³, 10⁴` (`≍ log log M`). Smoothing is what makes the
   mollifier nearly outer; `J_M → 0` is not proven.
6. **Gaussian head (Lean).** With `H_M = −(1/log M)(ζ'/ζ)_{≤M}`, the head of `ζΨ_M − 1`:
   `E|H_M|² → 1/2` and, for `M = T^θ`, `θ < 1/2`, `E|H_M|⁴ → 1/2 = 2(1/2)²`; the full deviation is
   not Gaussian (`c₄(θ) = 1 + 8/(3θ) + 2/θ² + 2/(3θ³)` by the ratios recipe, validated on the
   Lean head moments; `E log|ζΨ|² ≈ 0` numerically against the Gaussian `E₁` prediction).

The manuscript does not assert `(L)`, `J_M → 0`, or any uniform-in-`M` torus law.

## Gates

- [x] 0 → 1: the outer law identified as the `(L)` residue; the mollifier's zeros as the second term
- [x] 1 → 2: paper proofs of the decomposition, floors, torus laws, small-values estimate, equivalence
- [x] 2 → 3: unconditional Lean theorems, targeted builds, axiom audits
- [x] 3 → 4: scope statement (fixed `M`) and open cores recorded (STATUS CANNOT-296/297/298,
      MUST-207/208/209/210/211)

## Anti-theatre closure

- The torus constant is not defined as the flow limit; it is the Steinhaus expectation of an explicit
  polynomial, computed independently, and the flow means are proven to converge to its truncations.
- The small-values estimate uses actual zeros (factorization with multiplicities, strip count), not a
  Cartan-type black box; the `(log 1/x)² ≤ 16x^{-1/2}` majorant gives an explicit `64` per zero.
- The fixed-`M` equivalence is labelled as a decomposition plus a Dirichlet-polynomial law; it is not
  presented as progress on `(L)`.
- Numerics are used only to refute the Gaussian full law and to estimate `J_M`; no theorem depends
  on them.

## Formal sources

- `formal/GaloisForLFunctions/RHTower/MollifiedDeviationHeadVariance.lean`
- `formal/GaloisForLFunctions/RHTower/MollifiedDeviationHeadFourthMoment.lean`
- `formal/GaloisForLFunctions/RHTower/ComplexGaussianLogMeanExponentialIntegral.lean`
- `formal/GaloisForLFunctions/RHTower/MollifierLineLogMeanFloor.lean`
- `formal/GaloisForLFunctions/RHTower/DirichletPolynomialTorusLogUpperLaw.lean`
- `formal/GaloisForLFunctions/RHTower/OuterDecompositionLawMollifiedProduct.lean`
- `formal/GaloisForLFunctions/RHTower/DirichletPolynomialLineSmallValues.lean`
- `formal/GaloisForLFunctions/RHTower/OuterLawMollifiedProductEquivalence.lean`
- `formal/GaloisForLFunctions/RHTower/DirichletPolynomialWindowTorusLaw.lean`

Principal capstones:

- `RHTower.exists_head_fourthMoment_close`, `RHTower.tendsto_headFourthEnergy`
- `RHTower.integral_log_norm_zeta_mul_edPoly_line`
- `RHTower.exists_zetaLine_logMean_le_mollifiedProduct_logMean`
- `RHTower.exists_line_smallValues_bound`, `RHTower.exists_interior_log_lower_bound`
- `RHTower.exists_window_logMean_torus_twoSided`
- `RHTower.exists_zetaLine_logMean_floor_all_heights`
- `RHTower.zetaLine_logMean_le_iff_mollifiedProduct_logMean_le`
- `RHTower.exists_mollifiedProduct_logMean_squeeze_of_L`

All are wired into `GaloisForLFunctions.RHTower`. Computations:
`2-fully-proven/computations/mollified-fourth-moment-recipe/`.

## Verification

- Direct `lake env lean` checks passed for every module.
- Targeted module builds passed (`lake build` per module).
- Axiom audits report only `propext`, `Classical.choice`, `Quot.sound`.
- The formal lint gate passes for these modules; at the time of writing it reports an unrelated
  unwired module under `HTGeometry/DispersivePDE` owned by a concurrent session.
