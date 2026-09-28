# Möbius divisor-section sign law (all monotone Hankel kernels)

- **ID:** `MC-DIVISOR-SIGN-LAW`
- **Stage:** 3-formalized
- **Route:** MC / Route E receiver (Γ–Hankel Möbius covariance)
- **Lean:** `GaloisForLFunctions.RHTower.MobiusDivisorSectionSignLaw`, `GaloisForLFunctions.RHTower.MobiusDivisorMonotoneSignLaw` (axioms: propext, Classical.choice, Quot.sound)

## Statement
For `N, K ∈ ℕ` put `C_N(K) = Σ_{n≤N} Σ_{m|n, m<n, m+n≤K} μ(m)μ(n)` and `N' = min(N, K−1)`. Then

`C_N(K) ≤ −#{squarefree n : N'/2 < n ≤ N'} ≤ 0` (`divisorPairCountBelow_le`, `divisorPairCountBelow_nonpos`).

Abel summation gives, for every nonincreasing `w ≥ 0`, `Σ_{m|n, m<n≤N} μ(m)μ(n) w(m+n) ≤ 0` (`sum_divisorPairs_antitone_weight_nonpos`). Special cases:
- the divisor section of the Γ–Hankel covariance at every `r > 0` (`gammaHankel_divisorSection_nonpos`);
- `Σ_{n≤N} μ(n)qⁿ Σ_{m|n,m<n} μ(m)q^m ≤ 0` for `0 ≤ q ≤ 1` (`sum_divisorPairs_pow_nonpos`).

At `r = 1` (first module) the sharper row law holds: `row(n) = A_n/n` with `A_n ≤ −φ(n)/n`, so the integer-dilation section is at most `Σμ²/n − 2Σμ²φ(n)/n²` (`integerDilationGammaSection_le`).

## Proof mechanism
- **Full rows** (`2n ≤ K`) equal `−μ(n)²`.
- **Partial rows** (squarefree `n`, `2n > K`): the complement `e = n/m` turns them into `−Σ_{e|n, n/e+n>K} μ(e)`.
  - The `e = 1` term is `−1`.
  - The `e ≥ 2` terms map injectively to the squarefree cofactors `j = n/e ≤ N'/2`. Injectivity holds because `m + n = j(e+1)` is the next multiple of `j` after `n = je`, so two admissible `e < e'` would give `j(e+1) ≤ je' ≤ N' < K < j(e+1)`.
- The anti-diagonal (Hankel) geometry is therefore essential.

## Scope and limits
- The law extends the edge-pair sections of `RouteEAllQuotientPowerEdgeDominance` to all divisor-comparable pairs, at all exponents.
- **Integer-gap law.** It fails for real-normed Beurling systems. With `k ≥ 4` primes of norm `1+ε` and `K = 2+2.5ε`, `C = −k + C(k,2) > 0`.
- **Forced positivity** (paper, `N → ∞`, `r ↓ 1`). The counting drift gives `Div_r ≲ −0.608/(r−1) ≈ −2D_r`. Since `E_r ≥ 0`, the non-comparable section satisfies `NC_r ≥ −D_r − Div_r ≳ +D_r`. Sub-orthogonality then pins `NC_r ∈ [|Div_r| − D_r, |Div_r|]`.
- **No sign law for other lines.** The fixed-ratio lines `a ≥ 2` of the coprime matrix reduce to restricted Mertens sums, so they carry no sign law.

## Novelty
Corpus search (`research "divisor pairs Mobius antitone weight sign nonpositive"`) found no prior result. The corpus had only edge pairs (`RouteEAllQuotientPowerEdgeDominance`) and the absolute bound `|integerDilationGammaSection| ≤ 6(1+log X)`.
