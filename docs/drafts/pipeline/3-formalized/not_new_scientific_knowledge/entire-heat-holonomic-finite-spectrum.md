# Entire-Heat Holonomic Anchors Have Finite Spectrum

- **ID:** entire-heat-holonomic-finite-spectrum
- **Stage:** 2-fully-proven / not new scientific knowledge
- **Type:** THEOREM (paper) / BRIDGE / ROUTE NO-GO
- **Scientific status:** `[BRIDGE]` — a direct comparison of P-recursive tail propagation with super-Gaussian heat decay
- **Statement:** A jointly entire one-sided periodic heat orbit with a D-finite multiplicative anchor has only finitely many nonzero Fourier modes.

## Goal

Separate the genuinely nonlinear DA escape from the linear differential-equation stratum without using coefficient arithmetic. The result concerns holonomicity of the ordinary generating function in the multiplicative Fourier coordinate.

## Gates

- [x] Exact one-sided periodic heat class fixed.
- [x] Complete unconditional paper proof.
- [x] Arbitrary complex Fourier coefficients allowed.
- [x] Arbitrary homogeneous linear differential order allowed.
- [x] Parent-theory gate: **FAILS scientific novelty.** The proof is an elementary use of the classical D-finite/P-recursive equivalence.
- [x] Formalization: complete. The whole analytic and recurrence theorem is proved unconditionally in Lean; see the section below.

## Theorem `[PROVED HERE] [BRIDGE]`

Let `(a_n)_(n>=0)` be complex numbers and suppose

`u(t,z) = sum_(n>=0) a_n exp(-4 pi^2 n^2 t) exp(2 pi i n z)`

converges locally uniformly on `C^2`. Define

`h(w)=sum_(n>=0) a_n w^n`.

If `h` is D-finite over `C(w)`, then `a_n=0` for all sufficiently large `n`. Consequently `h` is a polynomial and `u` is a finite exponential polynomial in the spatial variable.

Equivalently, every infinite-spectrum anchor in this entire-complex-time class is non-holonomic.

## Proof

### 1. Entire backward time forces super-Gaussian decay

For every `A>0`, evaluate at `t_A=-A/(4 pi^2)`. The power series

`h_A(w)=sum_(n>=0) a_n exp(A n^2)w^n`

is entire. Cauchy's estimate on the unit circle gives a constant `M_A>0` with

`|a_n| <= M_A exp(-A n^2)`                                                     `(1)`

for every `n`.

### 2. A nonzero P-recursive tail propagates a factorial-scale subsequence

Since `h` is D-finite, `(a_n)` is P-recursive. After discarding finitely many indices and translating the least shift to zero, there are polynomials `q_0,...,q_r in C[n]`, with `q_0 q_r` nonzero, such that

`sum_(j=0)^r q_j(n)a_(n+j)=0`                                                  `(2)`

for every sufficiently large integer `n`.

If `r=0`, equation (2) already makes `a_n=0` eventually. Assume `r>=1`.

There are constants `C,d>0` and `N` such that `q_0(n)!=0` and

`|q_j(n)/q_0(n)| <= C n^d`

for `n>=N` and every `j`. Hence (2) gives

`|a_n| <= Cr n^d max_(1<=j<=r)|a_(n+j)|`.                                    `(3)`

Suppose some `a_(n_0)!=0` with `n_0>=N`. Iteratively choose

`n_(k+1) in {n_k+1,...,n_k+r}`

so that (3) yields

`|a_(n_(k+1))| >= |a_(n_k)|/(Cr n_k^d)`.

Because `n_0+k<=n_k<=n_0+rk`, iteration gives a constant `D>0` such that along this infinite path

`|a_(n_k)| >= exp(-D n_k log n_k)`                                             `(4)`

for all sufficiently large `k`.

### 3. The two scales contradict

Take `A=1` in (1). Along the path from (4),

`exp(-D n_k log n_k) <= M_1 exp(-n_k^2)`,

which is impossible as `k->infinity`. Therefore no coefficient `a_n` with sufficiently large `n` is nonzero. Thus `h` is a polynomial and the heat orbit has finite spectrum. `square`

## Exact route consequence

The theorem rules out every implementation with all three features:

1. a one-sided integer-frequency heat deformation that is entire for all complex time;
2. an infinite spectral source;
3. a proposed holonomic multiplicative anchor, of any linear differential order.

The obstruction is coefficient-free. Passing to transcendental or Liouville amplitudes does not rescue a D-finite anchor.

This does not rule out the actual de Bruijn-Newman deformation, which uses a continuous kernel and a zero-reality phase rather than holonomicity of a one-sided lattice generating function. It also does not rule out genuinely nonlinear DA anchors.

## Parent audit

1. The equivalence between D-finite power series and P-recursive coefficient sequences is classical.
2. Classical Newton-polygon theory also implies that a transcendental entire solution of a linear differential equation with polynomial coefficients has positive ordinary order. The recurrence proof above is more direct for the stronger super-Gaussian hypothesis.
3. Exact searches did not locate the heat-orbit wording. The argument nevertheless fails the routine-parent gate because (3)-(4) are the standard finite-width recurrence propagation estimate.

## Successor residue

The remaining class consists of genuinely nonlinear DA series of minimal differential order at least three with arbitrary complex coefficients. The conjectural arbitrary-order obstruction is recorded in `1-in-progress/supergaussian-da-coefficient-floor.md`.


## Lean formalization — 2026-08-17

Module: `formal/GaloisForLFunctions/HTGeometry/EntireHeatHolonomicFiniteSpectrum.lean`
(namespace `GaloisForLFunctions.EntireHeatHolonomic`, wired into the
`GaloisForLFunctions.HTGeometry` umbrella).  Nothing is imported as a classical black box: the
D-finite ⟹ P-recursive step, which the card's proof cites as classical, is *proved* here.

| Proof step | Lean name |
|---|---|
| **1.** entire backward time ⟹ `‖a_n‖ ≤ M_A e^{-A n²}` for every `A > 0` | `exists_superGaussian_bound` |
| coefficients of an iterated formal derivative, `[w^n] h^{(i)} = (n+1)⋯(n+i)·a_{n+i}` | `coeff_iterate_derivativeFun` |
| coefficient of a polynomial multiple, `[w^{M+K}](p·G) = Σ_{k≤K} p_k [w^{M+K−k}]G` | `coeff_polynomial_mul` |
| **2.** D-finite ⟹ P-recursive: the induced recurrence `Σ_{j≤K+m} q_j(M) a_{M+j} = 0`, valid for **every** `M ≥ 0` | `recurCoeff`, `recurrence_of_dFinite` |
| the `i`-th contribution to `q_j` is monic of degree exactly `i` | `shiftFactor`, `shiftFactor_monic`, `shiftFactor_natDegree`, `coeff_shiftFactor_self` |
| hence distinct differential orders cannot cancel: some `q_j ≠ 0` | `recurCoeff_ne_zero`, `exists_recurCoeff_ne_zero` |
| "after discarding finitely many indices and translating the least shift to zero, `q_0 ≠ 0`" | `exists_lowest_shift` |
| polynomial bounds used by the propagation estimate `(3)` | `norm_polyEval_le`, `exists_lower_bound_polyEval` |
| **2.–3.** a nonzero tail propagates along a finite-width path and contradicts super-Gaussian decay | `eventually_eq_zero_of_recurrence_of_superGaussian` |
| **the theorem**: `a_n = 0` for all large `n` | `entireHeat_dFinite_finite_spectrum` |
| "Thus `h` is a polynomial" | `exists_polynomial_of_eventually_zero`, `entireHeat_dFinite_isPolynomial` |

Three points where the Lean statement is deliberately different from the card's wording, all in
the direction of a **stronger** theorem or a **more elementary** proof.

* **The heat hypothesis is weaker.**  The card assumes `u(t,z)` converges *locally uniformly* on
  `ℂ²`; the Lean hypothesis is only that the defining series converges (`Summable`) at every point
  of `ℂ²`, which locally uniform convergence implies.  Step 1 then needs no Cauchy estimate at all:
  at `t = -A/(4π²)`, `z = 0` the terms are `a_n e^{An²}`, and a convergent series has bounded
  terms.
* **The recurrence holds from index `0`.**  The card's step 2 says "for every sufficiently large
  integer `n`" after "discarding finitely many indices".  The explicit coefficient extraction used
  here (`recurrence_of_dFinite`) is valid for **every** `M ≥ 0` once the shift `K` is taken to
  dominate all `deg p_i`; the only discarding still needed is of the *vanishing lowest shifts*,
  which is `exists_lowest_shift`.
* **The propagation estimate is coarser but sufficient.**  Where the card uses
  `|q_j(n)/q_0(n)| ≤ C n^d` and reaches the factorial-scale lower bound `exp(-D n log n)`, the Lean
  proof uses the crude `‖q_j(n)/q_0(n)‖ ≤ E e^{Dn}` and reaches `exp(-D r k²)`.  This is legitimate
  precisely because the decay hypothesis holds for *every* `A > 0`: `A := D·r + 2` is chosen after
  `D` and the recurrence width `r`, and the contradiction becomes the purely quadratic comparison
  `exp(k(log E + D n₀) − 2k²) → 0`.  No `n log n` scale, and no square roots, are needed.

**Not formalized (and not an obligation of this card).**  The "Exact route consequence" and
"Parent audit" sections are commentary on what the theorem rules out (de Bruijn–Newman, nonlinear
DA anchors) and on its classification as `[BRIDGE]`; the Newton-polygon remark is explicitly
flagged there as an alternative route not taken.  The `1-in-progress` successor
`supergaussian-da-coefficient-floor.md` is the open conjecture, not a claim of this card.

Verification: `lake build GaloisForLFunctions.HTGeometry.EntireHeatHolonomicFiniteSpectrum` — PASS;
`#print axioms` on all 14 named results reports only `[propext, Classical.choice, Quot.sound]`.

## Log

- 2026-07-11 — Proved the coefficient-free all-linear-order finite-spectrum theorem and classified it `[BRIDGE]`.
- 2026-08-17 — formalized in Lean, including an unconditional proof of the classical
  D-finite ⟹ P-recursive step; card moved to stage 3.
