# Weil positivity forces the functional equation at the critical zeros

**Status:** formalized (Lean, unconditional, standard axioms).
**Modules:**
- `formal/GaloisForLFunctions/RHTower/WeilDilationCriticalLineShift.lean`
- `formal/GaloisForLFunctions/RHTower/WeilDilationResidueRealness.lean`

## Statements
- `dilated_prime_side_line`: `Σ_n (Σ_{m∈S, m|n} b(m)Λ(n/m)) n^{−½} k(log n) = (1/2π)∫ B(c+it)H_k(c+it)(−ζ'/ζ)(c+it)dt`.
- `integral_dilationShiftIntegrand_eq`: the analytic integrand `B ξ³ ξ̄³ H_k (−ζ'/ζ)` (with its removable singularities filled) has equal integrals on `Re s = c` and `Re s = ½`.
- `dilation_tangent_criterion`: Weil positivity of `Λ + w` ⇒ `Re V(t) ≤ 0` for all `t`.
- `dilationPoly_im_eq_zero_of_weilPositive`: Weil positivity ⇒ `Im B(½+iγ) = 0` at every critical zero.
- `single_dilation_critical_ordinates`: `Λ(n) + cΛ(n/m)` Weil-positive, `c ≠ 0` ⇒ `γ log m ∈ πℤ` for every critical ordinate `γ`.

## Proof
1. One-sided prime sums of translates (Zeta23 `prime_side_line`) give the dilated sum as a line integral.
2. `ξ ζ'/ζ = ξ' − ξ(1/s + 1/(s−1) + Γℝ'/Γℝ)`.
   - Riemann's kernel transform vanishes at every zero, so `B ξ³ ξ̄³ H (−ζ'/ζ)` is analytic on `Re s > 0`. The pole at 1 is removed by `dslope`, because the polar-free bump vanishes at `−i/2`.
   - Strip bounds: `ξ` is bounded by its kernel integral, `ξ'` by Cauchy estimates, the digamma grows logarithmically, and `H` decays.
   - This justifies the vertical shift.
3. Spread radical tests `twistTest 0 τ₀ (log S) S`:
   - energy `= 2π Re W_ζ − 2Re∫V|q̂_S|² − 2Re Err`;
   - `W_ζ = O(S¹⁰e^{−S})`;
   - `Err = O(S⁷e^{−S})`, from the tail mass `E₀S⁶e^{−S²}` of Riemann's kernel against tilted Plancherel;
   - `(1/S)∫V|q̂_S|² → V(τ₀)∫|κ̂|⁴`.
4. Near a critical zero of order `m`, `(t−γ)Re[B(−ζ'/ζ)] → −m Im B(ρ)`. The weight `|ξ|⁶|ĥ|²` is positive off isolated points, so a nonzero `Im B(ρ)` gives a violation.

## Open (paper only)
The density step to `b = 0`. `Im B(½+iγ)` is an exponential sum of type `log M` with `O(T)` real zeros, while Selberg gives `≫ T log T` critical zeros. Alternatively, off-line division tests force `1 + B(ρ) = 0` at off-line zeros, and Riemann–von Mangoldt applies to `B(s) − B(1−s)`.
