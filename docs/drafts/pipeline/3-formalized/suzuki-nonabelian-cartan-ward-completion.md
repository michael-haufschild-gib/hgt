# Suzuki nonabelian Cartan–Ward completion

- **ID:** SUZUKI-NONABELIAN-CARTAN-WARD-COMPLETION
- **Stage:** 3-formalized
- **Type:** THEOREM (paper + Lean)
- **Source:** source-first synthesis of Suzuki unit-Riesz wall light amplitudes with the rank-two wild Stokes fission moment map
- **Statement:** The reporter-weighted negative-light walls admit canonical opposite-root `SL₂` Stokes pairs whose third-order-renormalized Cartan logarithm differs from Suzuki's completed prime–Gamma Green observable by a uniformly bounded positive remainder.

## Goal

Replace additive positive-minus-negative wall incidence, which is blind to center reserve, by a
literal nonabelian Stokes moment map.  At every prime-power wall the opposite-root product has
Cartan coordinate `1 + x`, where `x` is exactly reporter-weighted negative-light energy.  Prove
that its forced quadratic counterterm leaves a uniformly bounded cubic remainder, then identify
the Gamma-completed Cartan observable with Suzuki Green up to that remainder.  This supplies an
actual irregular-RH carrier for the live center-reserve debt; it does not assume a Xi divisor or
claim the remaining cofinal Cartan bound.

## Gates

- [x] 0 → 1  in-progress: well-posed, source-pure, attack idea, Door passport sketch
- [x] 1 → 2  fully-proven: complete paper proof, `[PROVED HERE]`, no open dependency
- [x] 2 → 3  formalized: targeted module check green; new declarations' axioms checked
- [ ] 3 → 4  publication-ready: standalone paper (theorem + proof + Lean certificate + Door-2)

## Source definitions

For integer aperture `A ≥ 2`, let

`P_A = {(p,e) : p prime, e ≥ 0, n(p,e)=p^(e+1) ≤ A}`.

At spectral center define

`x_A(p,e) = r_A(n(p,e)) · |ell_-(0;p,e)|²`,

where `r_A(n) = exp((log n-log A)/2)-exp(log n-log A)` is Suzuki's unit-Riesz
reporter and `ell_-` is the forced negative-light wall amplitude.  Let

`U(a)=[[1,a],[0,1]]`, `L(a*)=[[1,0],[a*,1]]`,

with `a_A(p,e)=sqrt(r_A(n(p,e))) ell_-(0;p,e)`.  The rank-two fission cell is
`U(a_A)L(a_A*)`; its Cartan coordinate is `1+x_A`.  Different prime powers occupy independent
rank-two blocks.  Thus the finite global carrier is the block-diagonal direct sum, not a product
of all cells inside one shared `SL₂`; its positive Levi determinant is the product of the cell
Cartan coordinates.

Set

`K_A = sum_(P_A) log(1+x_A)`,

`Q_A = sum_(P_A) x_A^2`, and

`R_A = K_A - sum_(P_A) x_A + Q_A/2`.

## Theorem package `[PROVED HERE]`

1. **Exact Stokes occurrence.**  Each fission cell has determinant one and upper-left Cartan
   coordinate `1+x_A(p,e)`.
2. **Uniform nonlinear remainder.**  `0 ≤ R_A ≤ 9/exp(3)` for every `A ≥ 2`.
3. **Completed Cartan–Ward identity.**

   `2 K_A + Q_A - suzukiUnitRieszRegularWardMass(log A)`

   `= unitRieszSuzukiGreen(log A) + 2 R_A`.

4. **Frontier transfer.**  Any one-sided or two-sided cofinal bound strong enough for Suzuki
   Green survives replacement by the completed Cartan observable, because `2R_A` is nonnegative
   and uniformly bounded.

## Proof `[PROVED HERE]`

Fix `A ≥ 2` and `(p,e) in P_A`; write `n=p^(e+1)`.  Suzuki's reporter is

`r_A(n)=exp((log n-log A)/2)-exp(log n-log A)`

`=sqrt(n/A)-n/A = sqrt(n/A)(1-sqrt(n/A))`.

Since `0 < n/A ≤ 1`, consequently `r_A(n) ≥ 0`.  Suzuki's exact center light split gives

`|ell_-(0;p,e)|²=(log p)/(2 sqrt(n))`.

Therefore

`x_A(p,e)=r_A(n)|ell_-(0;p,e)|²`

`=(log p)/(2 sqrt(A)) (1-sqrt(n/A))`.                                           `(1)`

In particular

`0 ≤ x_A(p,e) ≤ log(A)/(2 sqrt(A))`,                                           `(2)`

because `p ≤ n ≤ A`.

Put `a=sqrt(r_A(n)) ell_-(0;p,e)`.  Direct multiplication gives

`U(a)L(a*)=[[1+aa*,a],[a*,1]]`.

Here `aa*=|a|²=r_A(n)|ell_-|²=x_A(p,e)`, and the determinant is
`(1+x_A)-x_A=1`.  Gauss decomposition therefore has positive Levi coordinate `1+x_A`.
Taking direct sums over `P_A` proves exact Stokes occurrence and makes the positive Levi
determinant `prod_(P_A)(1+x_A)`; its real logarithm is `K_A`.

For `u ≥ 0`, set `phi(u)=log(1+u)-u+u²/2`.  Then

`phi(0)=0`, `phi'(u)=u²/(1+u)`, and `0 ≤ phi'(u) ≤ u²`.

Integration from `0` to `u` yields

`0 ≤ phi(u) ≤ u³/3`.                                                           `(3)`

Unique factorization makes `(p,e) ↦ p^(e+1)` injective, with image in
`{2,...,A}`; hence `card(P_A) ≤ A`.  Summing (3) and using (2),

`0 ≤ R_A ≤ (1/3) card(P_A) (log A/(2sqrt A))³`

`≤ log(A)³/(24 sqrt(A))`.                                                       `(4)`

For real `y ≥ 1`, differentiation of `log(y)³/sqrt(y)` gives the sign of
`log(y)²(6-log(y))`; its maximum is attained at `y=exp(6)` and equals
`216/exp(3)`.  Equation (4) proves

`0 ≤ R_A ≤ 9/exp(3)`.                                                          `(5)`

By definition of `R_A`,

`2K_A+Q_A = 2 sum_(P_A) x_A + 2R_A`.                                           `(6)`

The corpus-proved exact center split identifies `sum x_A` with one half of Suzuki's finite
prime outgoing charge.  Thus the first term on the right of (6) is that full charge.  Subtract
the regular-screw mass and invoke Suzuki's atomic–continuous identity to obtain

`2K_A+Q_A-RegularWardMass(log A)=unitRieszSuzukiGreen(log A)+2R_A`.              `(7)`

Finally (5) gives `0 ≤ 2R_A ≤ 18/exp(3)`.  Adding such a perturbation preserves upper bounds
after increasing the bound by `18/exp(3)`, preserves lower bounds in the forward direction,
and its subtraction preserves lower bounds after decreasing them by that constant.  Hence all
one-sided and two-sided cofinal boundedness statements transfer between the two observables.
This proves the package.

## Approach

- Use center light split `|ell_-|² = (log p)/(2 sqrt(n))` and the exact reporter to obtain
  `x_A(p,e) = (log p)/(2 sqrt(A)) · (1-sqrt(n/A))`.
- Hence `0 ≤ x_A(p,e) ≤ log(A)/(2 sqrt(A))`.
- Prime-power uniqueness injects `P_A` into `{2,...,A}`, so `card(P_A) ≤ A`.
- For `phi(x)=log(1+x)-x+x²/2`, `phi'(x)=x²/(1+x)`, giving
  `0 ≤ phi(x) ≤ x³/3` for `x ≥ 0`.
- Therefore `R_A ≤ log(A)^3/(24 sqrt(A)) ≤ 9/exp(3)`; the last bound is the exact maximum
  of `log(x)^3/sqrt(x)` on `[1,infinity)` at `x=exp(6)`.
- At center, the existing exact light split gives `sum x_A = primeOutgoingCharge(A)/2`.
  Substitute into Suzuki's atomic–continuous identity.

## Lean certificate

- Module: `GaloisForLFunctions.RHTower.Suzuki.SuzukiNonabelianCartanWardCompletion`.
- Literal rank-two carrier: `det_suzukiRankTwoStokesFissionCell`,
  `suzukiRankTwoStokesFissionCell_zero_zero`,
  `suzukiCenterStokesCartanCell_primePower_eq_negativeLight`, and
  `suzukiRankTwoStokesFissionCell_source_zero_zero`.
- Uniform nonlinear control: `suzukiStokesCartanCubicRemainderMass_nonneg`,
  `suzukiStokesCartanCubicRemainderMass_le_log_cube_div_sqrt`, and
  `exists_uniform_bound_suzukiStokesCartanCubicRemainderMass`.
- Completed identity: `suzukiCompletedStokesCartanWardObservable_eq_green_add_remainder`.
- Verification: direct targeted Lean check passed.  `#print axioms` on all new theorems reported
  only `propext`, `Classical.choice`, and `Quot.sound`.  No project-wide build or lint was run.

## Door passport sketch

- **Door 0 (source purity):** only prime powers, von Mangoldt wall amplitude, unit-Riesz reporter,
  negative-light FE split, and regular-screw Gamma continuum occur.
- **Door 1 (non-circularity):** no zero enumeration, RH premise, fitted coefficient, or
  source-dependent choice.  Remaining global statement is explicitly a cofinal Cartan bound.
- **Door 2 (novelty):** corpus search found light Gram, projective Fock holonomy, determinant
  regularization, and abstract fission separately, but no arithmetic rank-two Stokes Cartan law
  or this bounded completion.  Primary-literature search found finite-dimensional fission moment
  maps (Boalch), wild harmonic metrics (Biquard–Boalch), and Fredholm tau functions (Bertola), but
  no cofinal prime/Gamma Stokes construction or Suzuki reporter specialization.  Search result is
  evidence of no located duplicate, not a claim of exhaustive priority.
- **Door 3 (risk):** falsified if exact center cell is not `x_A`, if cubic remainder is not
  uniformly bounded, or if Gamma completion fails to recover Suzuki Green.

## Literature audit

- P. Boalch, *Geometry and braiding of Stokes data; Fission and wild character varieties*,
  Ann. of Math. 179 (2014), arXiv:1111.6228: finite-dimensional group-valued moment map and the
  rank-two `1+ab` fission coordinate.
- O. Biquard and P. Boalch, *Wild non-abelian Hodge theory on curves*, Compos. Math. 140 (2004),
  arXiv:math/0111098: finite-rank meromorphic connections with fixed polar data.
- M. Bertola, *The Malgrange Form and Fredholm Determinants*, SIGMA 13 (2017), arXiv:1703.00046:
  Fredholm realization of analytic matrix Riemann–Hilbert tau functions.
- M. Planat, 2026 Preprints.org manuscript 202604.0442: unrelated fixed Painlevé-III bridge;
  manuscript itself reports its direct Xi bridge fails by zero-counting asymptotics.

## Log

- 2026-08-25 — created in 1-in-progress after additive incidence and projective Fock variants were
  rejected as existing corpus bridges; exact center Cartan calculation survived first hostile audit.
- 2026-08-25 — corrected global carrier to a block-diagonal direct sum after shared-plane fusion
  failed hostile audit; completed paper proof and advanced to 2-fully-proven.
- 2026-08-25 — formalized rank-two cells, source occurrence, uniform cubic control, and completed
  Cartan–Ward identity; targeted Lean and axiom checks passed; advanced to 3-formalized.
