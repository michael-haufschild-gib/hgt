# Möbius Hilbert form criterion

- **ID:** `MC-HILBERT-SO1`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** MC conjecture loop (`1-in-progress/mc-conjecture-loop-2026-09-28.md`), cycle 51. It sharpens
  `3-formalized/mobius-gamma-hankel-sub-orthogonality.md`.
- **Statement:** If `Σ_{m,n≤N} μ(m)μ(n)/(m+n) = O_ε(N^ε)` for every `ε>0`, then RH. In particular
  **Hilbert sub-orthogonality** `Σ_{1≤m≠n≤N} μ(m)μ(n)/(m+n) ≤ 0 ∀N` implies RH.

## Goal
Move the MC sharp producer target from the two-parameter Γ–Hankel band `r ∈ (1, 2σ₀)` to the single
boundary exponent `r = 1`, i.e. the Hilbert matrix `[1/(m+n)]`. The target is now one explicit sequence
of finite inequalities indexed by `N` alone. Via Plancherel with `|Γ(½+iτ)|² = π sech(πτ)`, it is a
critical-line statement: `∫ sech(πτ)\|Σ_{n≤N}μ(n)n^{−½−iτ}\|²dτ ≤ Σ_{n≤N}μ(n)²/n`.

## Gates
- [x] 0 → 1  in-progress
- [x] 1 → 2  fully-proven (paper proof below)
- [x] 2 → 3  formalized: `RHTower.riemannHypothesis_of_mobiusHilbertFormSubpower`,
  `RHTower.riemannHypothesis_of_mobiusHilbertSubOrthogonal` in `RHTower/MobiusHilbertFormCriterion.lean`.
  Axioms: propext, Classical.choice, Quot.sound.
- [ ] 3 → 4  not planned (MC terminus, no manuscripts)

## Paper proof
Let `F_N(x)=Σ_{n≤N}μ(n)e^{−nx}`, so `E_N(r)=Γ(r)Σ_{m,n≤N}μ(m)μ(n)(m+n)^{−r}=∫_0^∞x^{r−1}F_N²`.
1. **Geometric tail.** For `M≤N`, `x>0`: `\|F_N(x)−F_M(x)\| ≤ e^{−(M+1)x}/(1−e^{−x})`.
2. **Tail energy.** Assume `E_N(1)≤C(N+1)^ε ∀N`. For `0<y≤1` put `M=⌈y^{−2}⌉`.
   - If `N≤M`: `∫_y^∞F_N² ≤ E_N(1) ≤ C·3^εy^{−2ε}`.
   - If `N>M`: `F_N² ≤ 2F_M² + 2(4/y²)e^{−2(M+1)x}` on `(y,∞)`, since `1−e^{−x} ≥ y/2`. The exponential
     part integrates to `≤ (2/y²)e^{−2/y} ≤ 1`.
   - Hence `∫_y^∞F_N² ≤ (2C3^ε+2)y^{−2ε}`, uniformly in `N`.
3. **Dyadic summation.** With `ε=(r−1)/4`, on `(u,2u]`: `x^{r−1} ≤ (2u)^{r−1}`, so each piece is
   `≤ K2^{r−1}u^{r−1−2ε}`. Along `u=2^{−j}` the pieces sum to `≤ K2^{r−1}ρ/(1−ρ)`, `ρ=2^{−(r−1−2ε)}`.
   The piece `(0,2^{−J}]` is `≤ 2^{−J(r−1)}E_N(1) ≤ 1` for large `J`. The piece `(1,∞)` is
   `≤ 4·2^{−r}Γ(r)`, since `\|F_N\| ≤ 2e^{−x}`. So `sup_N E_N(r) < ∞` for every `r>1`.
4. Fatou and Plancherel give finite Laplace energy on every line `σ>½`, so `Γ(s)/ζ(s)` is analytic on
   `Re s>½` and RH holds (corpus `mobiusLaplaceCofinalStrictRightEnergyFinite_implies_riemannHypothesis`).
5. **Sub-orthogonal corollary.** The diagonal `Σμ(n)²/(2n) ≤ (1+log N)/2 ≤ ((1+1/ε)/2)(N+1)^ε`.

## Why it matters for MC
- One exponent suffices. Growth may even be subpolynomial rather than bounded.
- SO₁ is plausible with a large margin. Under RH, `E_N(1) ≈ c_Z log N + M(N)²/N + O(1)`, where
  `c_Z = Σ\|Γ(ρ)/ζ'(ρ)\|² ~ 10⁻¹⁹`, while the diagonal is `≈ (3/π²)log N`. Failure would need
  `\|M(N)\| ≳ √(0.3N log N)`.
- Converse **formalized**: `RHTower/MobiusHilbertFormEquivalence.lean`,
  `mobiusHilbertFormSubpower_iff_riemannHypothesis`. It combines corpus Littlewood and uniform Abel–Laplace bounds
  `\|F_N\| ≤ Kx^{−½−δ}` with the trivial bound `\|F_N\| ≤ N`, via the geometric mean `F_N² ≤ (N²)^a(K²x^{−1−2δ})^{1−a}`.

## Literature relation (honest)
- The subpower criterion is the Hilbert-matrix form of the classical mean-square Mertens criterion
  (Titchmarsh §14: `∫_1^X M(x)²x^{−2}dx ≪ X^ε ⇔ RH`, and `≪ log X` ⇒ RH with simple zeros).
  `E_N(1)=∫_0^∞F_N²` and Laplace–Plancherel relate it to `∫M(x)²x^{−2}dx`.
- New here: the exact sign form (SO₁, with the log-size diagonal as the explicit ceiling), the
  one-exponent reduction of the corpus Γ–Hankel band, and the Lean proof.
- SO₁'s content is a quantitative Titchmarsh condition: log-mean of `M(x)²/x²` below ≈ `3/π²`.

## Boundary integrality refinement (cycle 57)
`RHTower/MobiusHilbertDivisorBoundary.lean`:
- `mobiusHilbertDivisorSection_le`: Σ_{m\|n,m<n≤N}μ(m)μ(n)/(m+n) ≤ 3/2 − ½Σ_{n≤N}μ²/n.
- `finiteMobiusGammaHankelEnergy_one_le_nonComparableExcess`: E_N ≤ (NonComp − D) + 3.
- `neg_three_le_nonComparableExcess`: NonComp − D ≥ −3.
- `riemannHypothesis_of_nonComparableExcess_subpower`: NonComp − D = O(N^ε) ⇒ RH.
- Heuristic under RH: NonComp ≈ 0.55 log N vs D ≈ 0.30 log N. The divisor section is ≈ −0.85 log N,
  more negative than the proven ceiling −2D.

## Log
- 2026-09-28: proved and formalized in one session (MC loop cycle 51).

## Scale boundary (unboundedness and log-scale strength)
- `MobiusHilbertFormEquivalence.not_exists_forall_finiteMobiusGammaHankelEnergy_one_le`: the
  Möbius Hilbert form is unbounded (unconditional). A bound gives L² log-Mellin energy on
  Re s=½ (Fatou), which excludes critical zeros; Hardy supplies one.
- `MobiusHilbertLogarithmicMertensBound.shiftedMertensReal_sq_le_of_hilbert_log_le`:
  if E_N ≤ C(1+log N) for every N, then M(N)² ≤ (16C+1)N(1+log N) for every N. The proof uses
  the Abel form F_N(x)=M(N)q^N+(1−q)Σ_{k<N}M(k)q^k on (0,1/(4N)] and strong induction.
- `shiftedMertensReal_sq_le_of_mobiusHilbertSubOrthogonal`: SO₁ ⇒ |M(N)| ≤ 3√(N(1+log N)).
- Consequence: the exact MC target is "unbounded but O(N^ε)". The log-scale target (and SO₁)
  implies a pointwise weak Mertens bound not known to follow from RH. The finite form carries the
  endpoint term M(N)²/N, unlike Ng's integrated mean square.
- `MobiusHilbertLogarithmicOmega.exists_pos_forall_exists_hilbert_gt_log`: for some c > 0, E_N > c log(N+1) + C
  infinitely often, for every C (unconditional). The mechanism is the log tail, then layer-cake integration by
  parts (E_N(1+2r) ≤ 2c/r + O(1)), then Fatou + Plancherel, set against the Hardy-zero window floor 2c₀²/r.
- So the exact target band is Ω(log N) (unconditional) to O(N^ε) (⇔ RH). O(log N) itself forces weak Mertens.
- Exponent law (`MobiusHilbertExponentLaw.forall_exists_hilbert_le_rpow_iff`): for a ≥ 0,
  E_N = O(N^{a+ε}) ∀ε ⇔ Θ ≤ (1+a)/2, with Θ = zetaZeroAbscissa. The growth exponent of the Möbius Hilbert
  form is exactly 2Θ − 1. Power savings in E_N are equivalent to zero-free strips. Both directions are
  unconditional: Littlewood at Θ in one direction, and a sharp tail + layer cake + closed-half-plane criterion in
  the other.

## All-N logarithmic floor and divergence threshold (2026-09-29)

- **Every-N floor [Lean: `RHTower.exists_forall_mul_log_le_finiteMobiusGammaHankelEnergy_one`].** There are `c>0` and `N₀` with `E_N ≥ c log N` for all `N ≥ N₀`. This is the sharp order: under RH and simple zeros `E_N ≍ log N`.
  - Plancherel gives `2πE_N = ∫|Γ(½+iu)M_N(½+iu)|²du` (`integral_norm_sq_gamma_mul_edPoly_mobCoeff_line`).
  - At a Hardy zero `½+iγ`, `e^{−(u−γ)²}|ζ|² ≤ B(u−γ)²|Γ|²` on the whole line.
  - With `κ_L = sinc(L(u−γ))⁴e^{−(u−γ)²}`, `L²κ_L|ζ|² ≤ B|Γ|²`.
  - On the line `z(z−1) = −(¼+u²)` and `(z+3)(z−4) = −(49/4+u²)`, so `P_N = z²·mobField_N/((z+3)(z−4)) = a(u)(ζM_N−1)` with `a ∈ [1/49,1]`. Then `|ζM_N|² ≥ a + 2Re P_N`: only the linear term in `ζM_N−1` enters.
  - The holomorphic window `sinc(−iL(z−ρ₀))⁴exp((z−ρ₀)²)` costs `e^{10L}` at `Re z = 3`, where `|P_N| ≤ 20/N`. With `L = log N/20` the cross term is `O(√N/N)`, and the main term is `∫κ_L a ≥ m₀/L`.
  - Hence `2πE_N ≥ (L²/B)(m₀/L − O(L e^{−log N/2}))`.
  - Gaussian windows cost `e^{c/w²}` and stop at `√log N` (the old cycle-67 obstruction). The band-limited window removes it.
- **Divergence [Lean: `RHTower.tendsto_finiteMobiusGammaHankelEnergy_atTop`, `…_of_riemannZeta_eq_zero`].** A bound for infinitely many `N` already makes `Γ/ζ` square integrable on `Re s = r/2` (Fatou along a subsequence), so any zero with `Re ρ ≥ r/2` forces `E_N(r) → ∞`.
- **Threshold [Lean: `RHTower.bddAbove_range_finiteMobiusGammaHankelEnergy_iff`].** For `r ≠ 2Θ`, `E_N(r)` is bounded iff `r > 2Θ`. The bounded side uses Littlewood `|M(n)| ≪ n^{Θ+ε}`, which gives `|F_N(x)| ≪ x^{−b}` uniformly on `(0,1]`.
