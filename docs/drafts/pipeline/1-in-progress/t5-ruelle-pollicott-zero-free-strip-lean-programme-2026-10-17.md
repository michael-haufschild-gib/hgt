# T5 Lean programme: Ruelle zeta functions of Hölder suspensions over mixing SFTs are zero-free near Re s = 1

- **ID:** t5-ruelle-pollicott-zero-free-strip-lean-programme-2026-10-17
- **Stage:** 1-in-progress (formalization programme for card 4 item T5)
- **Type:** THEOREM (paper proof below) / Lean programme
- **Source:** `2-fully-proven/route TT/route-tt-structural-theorems-2026-10-14.md`, T5

## Statement (Lean target)
Data: alphabet `Fin k`, aperiodic 0-1 matrix `A` (`A^M > 0`), shift space `X`, `0 < θ < 1`, roof
`r : X → ℝ`, `r > 0`, `|r x − r y| ≤ C θ^{n(x,y)}` (`n(x,y)` = first disagreement).
`Z_n(s) = Σ_{σ^n x = x} e^{−s r^n(x)}`, `ζ_R(s) = exp Σ_{n≥1} Z_n(s)/n`.
Hypothesis (entropy ≤ 1): `Σ_n Z_n(σ)/n < ∞` for every real `σ > 1`.
**T5-core.** `∃ ε > 0`, `∃ E` holomorphic on `{Re s > 1 − ε}` with `E(s) ζ_R(s) = 1` on `Re s > 1`.
**T5.** If moreover `riemannZeta = ζ_R` on `Re s > 1`, then `riemannZeta s ≠ 0` for `Re s > 1 − ε`, `s ≠ 1`.
(Also: `ζ_R = Π_{primitive orbits γ}(1 − e^{−sℓ_γ})^{−1}`.)

## Paper proof
Notation: `g_s = e^{−s r}`; `r_m(x) = r(π_m x)`, `π_m x` = the first `m` symbols of `x` followed by a
fixed admissible continuation; `|r − r_m| ≤ Cθ^m`, `r_m` has the same Hölder constant;
`S_n(σ) = Σ_{|w|=n} sup_{[w]} e^{−σ r^n}`.

1. **Partition sums.** Closing each admissible `w` (length `n`) by a fixed connecting word of length `M`
   gives an injection into closed words of length `n + M`, with bounded distortion `D = C/(1 − θ)`:
   `S_n(σ) ≤ e^{|σ|(D + M‖r‖)} Z_{n+M}(σ)`. From the hypothesis `Z_n(1+δ) ≤ C_δ n`, and
   `Z_n(σ) ≤ Z_n(σ') e^{n(σ'−σ)‖r‖}` for `σ ≤ σ'`. Hence for `σ ≥ 1 − ε`: `S_n(σ) ≤ C n e^{nκ}`,
   `κ = (ε + δ)‖r‖`. For `σ > 1`: `Z_n(σ) ≤ C n e^{−n(σ−σ')r_min}` (exponential decay).
2. **Space.** `B = F_{θ'}`, `θ < θ' < 1`: bounded `f : X → ℂ` with `|f|_{θ'} = sup |f x − f y|/θ'^{n(x,y)}`,
   `‖f‖ = ‖f‖_∞ + |f|_{θ'}`; Banach.
3. **Operators.** `T_m f(x) = Σ_{a: A a x₀ = 1} g_{s,m}(ax) f(ax)` (`m ≤ ∞`, `g_{s,m} = e^{−s r_m}`).
   (LY) `‖T_m^n f‖_∞ ≤ S_n‖f‖_∞`, `|T_m^n f|_{θ'} ≤ S_n(C₁‖f‖_∞ + θ'^n |f|_{θ'})`, uniform in `m`.
   (Pert) `‖T_m − T_{m'}‖ ≤ C₃ (θ/θ')^{min(m,m')}` (case split on the level of disagreement).
   (FR+S) `E_N f = Σ_{|w|=N} f(π_N w) χ_{[w]}`: `‖E_N‖ ≤ 1`, rank `≤ k^N`, `‖(1 − E_N)f‖_∞ ≤ θ'^N|f|_{θ'}`;
   `T^N = T^N E_N + T^N(1 − E_N)` with `‖T^N(1 − E_N)‖ ≤ C₄ S_N θ'^N ≤ C (Nη)^N`-type, `η = θ'e^κ < 1`.
4. **Riesz calculus** (Banach algebra of operators). For a circle `Γ_ρ` in the resolvent set:
   `P_in = (2πi)⁻¹∮_{Γ_ρ} R(z) dz`, `P_out = 1 − P_in`, `T^n P_in = (2πi)⁻¹∮ zⁿR(z)dz` (so
   `‖TⁿP_in‖ ≤ ρ^{n+1} Λ`), `G_n = −(2πi)⁻¹∮ z^{−n}R(z)dz` with `TⁿG_n = P_out`, `‖G_n‖ ≤ ρ^{1−n}Λ`.
   `P_in² = P_in` (resolvent identity, two circles), `TP = PT`.
   **Finite rank:** if `T^N = F + S`, rank `F ≤ r`, `‖G_N‖‖S‖ < 1`, then `ranP_out ∩ ker F = 0`, so
   `dim ranP_out ≤ r`.
   **Perturbation:** `‖R_T(z)‖ ≤ Λ` on Γ and `‖T − T'‖Λ ≤ ½` ⇒ `‖R_{T'}‖ ≤ 2Λ`,
   `‖TⁿP_out(T) − T'ⁿP_out(T')‖ ≤ C R'ⁿ ‖T − T'‖`.
   **Traces:** finite-rank `X` on `B` has `tr X = tr(X|_W)`, `W ⊇ ranX` invariant; `|tr X| ≤ dim W ‖X‖`
   (trace = sum of eigenvalues, each `≤ ‖X‖`).
5. **Level spaces.** `V_m` = functions depending on the first `m` symbols (dim `≤ k^m`), `T_m V_m ⊆ V_{m−1}`;
   `Z_n^{(m)} := Σ_{Fix σⁿ} e^{−s r_mⁿ} = tr(T_mⁿ|_{V_m})` (closed paths in the level-`m` graph);
   `ran P_out(T_m) ⊆ V_m` (`P_out f = G_n T_mⁿ f` and `T_mⁿ f → V_{m−1}` at rate `S_nθ'ⁿ`);
   `V_m = ranP_out ⊕ (V_m ∩ ranP_in)`, so `|Z_n^{(m)} − tr(T_mⁿP_out)| ≤ k^m ρ^{n+1} Λ`.
6. **Main estimate.** `m' = ⌈αn⌉`: `|Z_n − Z_n^{(m')}| ≤ n C θ^{m'} e^{nκ}`;
   `|tr(T_{m'}ⁿP_out) − tr(T_∞ⁿP_out)| ≤ 2k^N C R'ⁿ (θ/θ')^{m'}`. Choosing `α` then `ε, δ` small:
   `|Z_n − tr(T_∞ⁿ P_out)| ≤ C n ρ''ⁿ`, `ρ'' < 1`.
7. **Continuation.** `E(s) := det(1 − T_s|_{ranP_out}) · exp(−Σ_n (Z_n(s) − tr(T_sⁿP_out))/n)`;
   independent of the admissible radius (eigenvalues between two radii `< 1` contribute
   `Π(1−λ) = exp(−Σλⁿ/n)`); holomorphic locally (resolvent holomorphic in `s`); for `Re s > 1` all
   eigenvalues have modulus `< 1`, so `E = exp(−Σ Z_n/n) = 1/ζ_R`.
8. **Corollary.** `riemannZeta · E = 1` on `Re s > 1`, hence on the connected set
   `{Re s > 1 − ε} ∖ {1}`; so `riemannZeta ≠ 0` there.

## Modules (planned)
1. `HTGeometry/SymbolicShiftSpace` — shift space, words, cylinders, periodic points ↔ closed words,
   continuations, closing lemma.
2. `HTGeometry/SymbolicHolderSpace` — the Banach space `F_θ'`.
3. `HTGeometry/SymbolicTransferOperator` — `T_m`, LY, perturbation, `E_N`, partition sums.
4. `HTGeometry/RieszProjectionBanach` — resolvent calculus, projections, finite rank, perturbation, traces.
5. `HTGeometry/SymbolicZetaTraceAsymptotics` — level spaces, trace identity, main estimate.
6. `RHTower/RuellePollicottZeroFreeStrip` — continuation, Euler product, ζ corollary.

## Log
- 2026-10-17 — paper proof written (steps 1–8); module 1 started.
- 2026-10-17 — Lean modules compiled (standard axioms pending final audit), reusing the corpus Riesz
  projection layer (`RieszProjection`, `ResolventPerturbation`):
  `HTGeometry/FiniteRankTraceDeterminant` (finite-rank trace/det, `det(1−f)=exp(−Σtr fⁿ/n)`,
  multiplicativity, `|tr| ≤ dim·‖X‖`, similarity invariance);
  `HTGeometry/RieszProjectionPowerCalculus` (`aⁿP` moments, outer inverse `G_n`, nested projections,
  idempotence from a circle, finite rank of `1−P` from `Tⁿ=F+S`, range of `1−P` in absorbing closed
  subspaces); `HTGeometry/QuasiCompactSpectralCircle` (finite-rank Fredholm determinant ⇒ a circle
  in the resolvent set between any two radii above `‖S‖^{1/N}`);
  `HTGeometry/HolomorphicRieszFamily` (holomorphic Riesz projections, Kato transformation,
  holomorphic outer trace/det); `HTGeometry/SymbolicShiftSpace` (words, periodic points, Birkhoff
  sums, distortion, closing lemma, compactness, `periodicOrbitSum` bridge);
  `HTGeometry/SymbolicHolderSpace` (Banach space `F_ϑ`, `ofLinear` operator builder).
  Next: transfer operators (n-th power formula, Lasota–Yorke, perturbation, `E_N`, level spaces,
  trace identity), main estimate, continuation, corollary.
