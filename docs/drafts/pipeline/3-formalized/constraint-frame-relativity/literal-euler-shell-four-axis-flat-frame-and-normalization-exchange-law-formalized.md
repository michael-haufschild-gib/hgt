# Literal Euler-shell four-axis flat frame and normalization-exchange law — formalized

- **ID:** `cfr-euler-shell-four-axis-flat-frame-formalized`
- **Stage:** 3-formalized
- **Paper proof:** `literal-euler-shell-four-axis-flat-frame-and-normalization-exchange-law.md` (same directory)
- **Status:** `[LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`

## Lean modules

| Module | Path |
|---|---|
| `GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.EulerShellFourAxis` | new |

Reused without duplication:

| Module | Supplies |
|---|---|
| `…ConstraintFrameRelativity.RamificationBooleanSupport` | `unitalShellIndicator`, `logCoeffOperator`, `unitalShellIndicator_pow_self_eq_one_iff` |
| `…ConstraintFrameRelativity.FiniteTiltResponse` | `wexp`, `wcov`, `wexp_add/sub/const_mul/const` |
| `…ConstraintFrameRelativity.PhaseHistoryDilation` | `shellFlow`, `exists_large_return` (Kronecker recurrence) |

Wired into `GaloisForLFunctions.HTGeometry`.

## Formal theorem chain

All declarations live in namespace `HTGeometry.ConstraintFrameRelativity`.

Section 1 — clock recovery from the logarithmic prolongation, card `(1)`–`(5)`:

1. `logCoeffOperator_iterate` — `L^k f (n) = (-log n)^k f(n)` for the operator `(Lf)(n) = -(log n)f(n)`
   of card `(2)`, by induction on `k`.
2. `shell_clock_recovery` — card `(4)`: `(L^k a_m)(p^m) = (-m log p)^k` for every prime `p` and
   every `k`, using `a_m(p^m) = 1` (the marked shell indicator is unital exactly at squarefree
   radicals) and `log(p^m) = m log p`.
3. `prime_clock_eq` — card `(5)`: `-(1/m)(L a_m)(p^m) = log p`, the source recovery of the prime
   clock.

Section 2 — the diagonal four-axis frame, card `(6)`–`(10)`:

4. `clockGen`, `phaseFlow`, `reesFrame` — the three coordinate-diagonal operators `Λ_F`, `U_F(t)`,
   `R_F` of card `(6)`, `(8)` on `H_F = ℂ^F`.
5. `diagonal_commute` — card `(10)`: `[Λ_F, R_F] = [U_F(t), R_F] = [U_F(t), Λ_F] = 0`, i.e. the
   prime-skeleton connection is flat. All three commutators are proved simultaneously by
   coordinatewise commutativity of ℂ.
6. `restriction_natural` — card item 2.1(1)–(2): strict aperture naturality. Along any aperture
   inclusion `ι : E → F` each of the three operators restricts to the diagonal operator of the
   restricted data, with the restriction identities holding definitionally (`rfl`), which is the
   strict form of "restrictions compose strictly".
7. `hasDerivAt_phaseFlow` — card `(9)`: `d/dt U_F(t) = -i Λ_F U_F(t)` coordinatewise, as an exact
   `HasDerivAt` statement at every real time.

Section 3 — the Gamma–Rees weight collapses cofinally, card `(7)`, `(12)`:

8. `reesWeight` — the literal weight `ℓ_p = 4p³(log p)²/((p+1)²(p-1)(2p-1))` of card `(7)`.
9. `tendsto_reesRational` — the exact leading behaviour of the rational factor:
   `4p⁴/((p+1)²(p-1)(2p-1)) → 2`, proved by dividing through by `p⁴` and taking the four
   elementary limits of `p⁻¹ → 0`. This is the content of `ℓ_p ~ 2(log p)²/p`.
10. `tendsto_reesWeight` — card `(12)`, first half: `ℓ_p → 0`, from step 9 combined with
    `Real.tendsto_pow_log_div_mul_add_atTop` (`(log p)²/p → 0`).
11. `reesWeight_pos` — `ℓ_p > 0` for `p ≥ 2`.
12. `reesWeight_inv_unbounded` — card `(12)`, second half: `sup_F ‖R_F⁻¹‖ = ∞`, in the explicit
    cofinal form `∀ M, ∃ p ≥ 2, ℓ_p⁻¹ > M`.

Section 4 — recurrent phase orbit with an unbounded lift, card `(11)`:

13. `clockHistory` — the lifted clock history `h(t) = -t log p` of card `(11)`.
14. `tendsto_abs_clockHistory` — `|h(t)| → ∞`: the lift is unbounded although the phase orbit is a
    bounded torus orbit.
15. Recurrence is supplied by `exists_large_return` of `PhaseHistoryDilation` (Kronecker density
    for the ℚ-linearly-independent prime logarithms), reused rather than rebuilt.

Section 5 — the coefficient-stream space `X_σ`, card `(17)`:

16. `phaseChar`, `phaseTerm`, `phaseTermDeriv`, `phaseSum`, `totalMass` — the Dirichlet term
    `c_n n^{-σ-it}` split as mass times phase, its formal `k`-th time derivative, the series, and
    `Z_c = ∑ c_n n^{-σ}`.
17. `MomentStream c σ` — membership in `X_σ`: `∑ |c_n| n^{-σ}(1 + log n)^k < ∞` for every `k`,
    exactly card `(17)`.
18. `norm_phaseChar`, `norm_phaseTermDeriv`, `norm_phaseTermDeriv_le` — the exact term norm
    `(log n)^k |c_n| n^{-σ}` and its domination by the `k`-th moment summand.
19. `summable_phaseTermDeriv`, `summable_mass`, `summable_phaseTerm` — every moment series
    converges absolutely.
20. `momentStream_of_finite_support` — the space is inhabited: every finitely supported stream
    lies in `X_σ` for every `σ`.

Section 6 — Theorem 4.1, card `(19)`–`(21)`:

21. `hasDerivAt_phaseTermDeriv` — each Dirichlet term is differentiable in time with derivative the
    next term.
22. `hasDerivAt_phaseSum` — card `(21)`: termwise time differentiation of every order,
    `d/dt (∑ term_k) = ∑ term_{k+1}`, proved from `hasDerivAt_tsum_of_isPreconnected` with the
    `(k+1)`-st moment as the summable dominating bound. This is the exact statement that source
    intervention commutes with every time derivative.
23. `streamExp`, `normalizedObservation` — the normalised expectation `E_{P_c}` and `C_c(t)` of
    card `(18)`.
24. `totalMass_add`, `phaseSum_add` — affinity of both numerator and denominator in the
    intervention parameter.
25. `hasDerivAt_affine_div_complex` — the affine Möbius derivative with complex numerator and real
    denominator, proved via `HasDerivAt.inv` and the product rule.
26. `hasDerivAt_normalizedObservation_stream` — the **boxed** card `(19)`:
    `D C_c[h](t) = Z_c⁻¹(∑ h_n n^{-σ-it} - H₀(h) C_c(t))`, as a `HasDerivAt` at `e = 0` of
    `e ↦ C_{c + e h}(t)`.
27. `exchange_bilinear` — the **boxed** card `(20)`: with `h_n = c_n r_n` the exchange derivative is
    the bilinear covariance `E_{P_c}[r e^{-itx}] - E_{P_c}[r] E_{P_c}[e^{-itx}]`. Proved with no
    hypotheses at all, the two sides being equal termwise.
28. `hasDerivAt_affine_div_gen`, `hasDerivAt_normalizedObservation` — the same exchange law in the
    scalar model, isolating the mechanism "normalisation subtracts the radial component of the
    coefficient change before phase observation".
29. `exchange_covariance` — the finite-weight form: against a normalised weight the exchange defect
    equals the fully centred second moment `E[(r - Er)(f - Ef)]`.

Section 7 — the normalisation wall, card `(22)`:

30. `normalization_wall` — `m ≥ 12` and `σ > 1` force `m σ ≠ 1`, so the positive GNS fibre and the
    physical half-density prime fibre are not bounded gauges of one Hilbert space.

Capstones:

31. `four_axis_frame` — Theorem 2.1 in one statement: clock recovery for all `k`, the three
    vanishing commutators, the flow ODE, arbitrarily late `ε`-returns of the phase orbit,
    unboundedness of the lift, and the cofinal collapse of the Rees inverse.
32. `normalization_exchange` — Theorem 4.1 in one statement: termwise time differentiation of every
    order, the exchange derivative `(19)`, and its covariance form `(20)`.

## Verification

```
lake build GaloisForLFunctions.HTGeometry.ConstraintFrameRelativity.EulerShellFourAxis
```

builds clean, no warnings.

```
#print axioms four_axis_frame
#print axioms normalization_exchange
#print axioms normalization_wall
#print axioms tendsto_reesWeight
```

all report `[propext, Classical.choice, Quot.sound]` — no `sorry`, no project axiom.

## Scope

The Lean development is the paper theorem: no premise of the module encodes an unproven analytic
input. `MomentStream c σ` is the definition of membership in the Fréchet space `X_σ` of card `(17)`,
not an assumption about an unknown object, and `momentStream_of_finite_support` exhibits inhabitants.

Card items deliberately not formalized, because they are not theorems of this card:

- the identification `S_m = ζ H_m` and the hypertranscendence of `H_m` (card §3) are the content of
  `RHTower.HighExponentShellHypertranscendence`, cited by the paper card and not re-proved here;
- the open gates of §6 (cross-organ comparison, withheld-organ prediction) remain open by the
  card's own statement.
