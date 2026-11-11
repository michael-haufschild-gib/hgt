# The tangent data of Möbius and Liouville in world I

- **ID:** A137
- **Stage:** 3-formalized
- **Lean:** `FloorFreeArithmetic/TheTangentDataOfMobiusAndLiouvilleInWorldOne.lean`

## Statement

Kernel `K(s) = e^{(s−c)²}A(s)/((s−1)ζ(s))`; `A = s − 1` (Möbius), `A = (s−1)ζ(2s)` (Liouville).

1. **Möbius window sum.** `signal K_μ 2 Z = Σ_n μ(n) e^{c(log Z − log n) − (log Z − log n)²/4}/(2√π)`.
2. **Explicit formula above a level.** If the zeros right of `σ' < σ` are finitely many and none
   is on `Re s = σ`: `signal K 2 Z = Σ_{ρ: Re ρ > σ} Res_ρ(Z^s K) + O(Z^σ)`.
3. **Residues.** At a zero of order `m`, with `(s−1)ζ(s) = (s−ρ)^m g(s)` and `H = e^{(s−c)²}A/g`:
   `Res_ρ(Z^s K) = Z^ρ Σ_{j<m} (log Z)^j/j! · H^{(m−1−j)}(ρ)/(m−1−j)!`.
4. **World I** (`Θ∞ < Θ`): `e^{−Θu}(signal(e^u) − Σ_{Re ρ = Θ} Res_ρ) → 0` for μ and λ. The data of
   μ and λ have the same support (top zeros) and degrees `m − 1`; leading numerators differ by
   the unit `ζ(2ρ)`.

## Proof

World I gives `σ' < σ < Θ` with finitely many zeros right of `σ'` (the zeros right of `Θ∞`
are first components of finitely many divisor copies) and none on `Re s = σ` (finitely many
real parts to avoid). Right of `σ'` and above the heights of that finite set, `|ζ|` has the
subpolynomial lower bound of `InvZetaAbscissaSubpolynomial`; with `|s − 1| ≥ |t|` and the
Gaussian, the integrand is `O(1/(1+t²))` on both lines and the horizontal sides vanish. The
finite-pole contour shift gives (2). The residue formula clears the pole with `t^{m+1}` and takes
the Cauchy product of the Taylor series of `e^{L(ρ+t)}` and `H(ρ+t)`. Residues below the top line
are `e^{(Re ρ − Θ)u}` times polynomials in `u` after normalization; the `σ`-line term is
`O(e^{(σ−Θ)u})`. (1) is `1/ζ = Σ μ(n)n^{−s}`, Fubini, and the complex Gaussian integral.

Axioms of the headline theorems: `propext`, `Classical.choice`, `Quot.sound`.

## Open

No bound on the top coefficients `H(ρ)` (equivalently on the leading Taylor coefficient of `ζ` at
a top zero) is derived: the §2.10 question whether exact Type I sums constrain it.
