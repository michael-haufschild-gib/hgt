# Algebraic Entire-Heat DA Fibers Have Finite Spectrum

- **ID:** arithmetic-entire-heat-da-finite-spectrum
- **Stage:** 3-formalized / not new scientific knowledge
- **Type:** THEOREM (paper) / BRIDGE / ROUTE NO-GO
- **Scientific status:** `[BRIDGE]` — an exact finite-spectrum consequence of classical Pólya-Popken coefficient arithmetic and Fourier diagonalization of the heat equation
- **Statement:** A jointly entire one-sided periodic heat orbit with algebraic Fourier coefficients cannot have a DA spatial fiber unless only finitely many Fourier coefficients are nonzero.

## Goal

Test whether differential algebraicity can emerge as a genuine phase inside a complex-entire arithmetic heat flow. The theorem concerns periodic heat solutions in general. Its downstream target is only a discrete arithmetic surrogate of a de Bruijn-Newman deformation, not the actual continuous Fourier kernel.

## Gates

- [x] Exact one-sided periodic heat class fixed.
- [x] Complete unconditional paper proof.
- [x] Arithmetic coefficient theorem identified: Popken's lower bound for nonzero algebraic Taylor coefficients, with Mahler normalization reducing an ADE of an algebraic-coefficient series to algebraic constants.
- [x] Adjacent DA heat-ansatz literature checked.
- [x] Parent-theory gate: **FAILS scientific novelty.** The proof is a short comparison of two known asymptotic scales.
- [x] Formalization: complete and unconditional in Lean 4, theorem and arithmetic parent both.

## Theorem `[PROVED HERE] [BRIDGE]`

Let `(a_n)_(n>=0)` be algebraic numbers and suppose

`u(t,z) = sum_(n>=0) a_n exp(-4 pi^2 n^2 t) exp(2 pi i n z)`

converges locally uniformly on `C^2`. Then `u` is jointly entire, `1`-periodic in `z`, and satisfies

`partial_t u = partial_z^2 u`.

If the spatial fiber `z |-> u(0,z)` is differentially algebraic over `C(z)`, then `a_n=0` for all sufficiently large `n`. Consequently `u` is a finite exponential polynomial in `z`, and every spatial fiber `u_t` is D-finite and DA.

Equivalently, if infinitely many `a_n` are nonzero, then the whole jointly entire arithmetic heat orbit has an HT anchor at `t=0`.

## Proof

### 1. Entire backward time forces super-Gaussian Fourier decay

For `A>0`, set

`t_A = -A/(4 pi^2)`.

The fiber at `t_A` is

`u(t_A,z) = sum_(n>=0) a_n exp(A n^2) exp(2 pi i n z)`.

Put `w=exp(2 pi i z)`. The one-sided series defines an entire function

`h_A(w)=sum_(n>=0) a_n exp(A n^2) w^n`.

Indeed, the local uniform convergence of the displayed heat series for every `z in C` gives convergence for every `w in C^x`, while the power series is regular at `w=0`.

By Cauchy's coefficient estimate on `|w|=1`,

`|a_n| exp(A n^2) <= M_A`,

where `M_A=max_(|w|=1)|h_A(w)|`. Hence

`|a_n| <= M_A exp(-A n^2)`                                                    `(1)`

for every `n`. Since `A` is arbitrary, the nonzero Fourier coefficients decay faster than every fixed Gaussian.

### 2. A DA spatial fiber gives a DA ordinary generating function

Put

`h(w)=h_0(w)=sum_(n>=0) a_n w^n`.

On any simply connected logarithm chart in `C^x`,

`h(w)=u(0, Log(w)/(2 pi i))`.

The local logarithm is DA over `C(w)`, because its derivative is `1/w`. Differentially algebraic functions are closed under composition. Therefore the hypothesis that `u(0,.)` is DA over `C(z)` implies that `h` is DA over `C(w)`.

Mahler's normalization theorem implies that an algebraic-coefficient DA series satisfies an ADE with algebraic coefficients. Popken's theorem therefore applies: there are constants `alpha,beta>0` such that, for every `n>=1`, either `a_n=0` or

`|a_n| >= alpha n^(-beta n log n)`

at the fixed embedding of the algebraic numbers into `C`. Equivalently, after enlarging a constant `C>0`, every sufficiently large nonzero coefficient satisfies

`|a_n| >= exp(-C n (log n)^2)`.                                                `(2)`

The arithmetic content behind this estimate is Pólya-Popken denominator control together with Maillet's upper bound for the Galois conjugates and the nonzero algebraic norm.

### 3. The two scales are incompatible

Take `A=1` in `(1)`. If there were arbitrarily large indices with `a_n!=0`, then `(1)` and `(2)` would give

`exp(-C n (log n)^2) <= M_1 exp(-n^2)`.

After logarithms this would require

`n^2 <= C n (log n)^2 + log M_1`,

which is false for all sufficiently large `n`. Therefore `a_n=0` eventually.

The remaining Fourier sum is finite. Each spatial fiber is consequently annihilated by a constant-coefficient linear differential operator

`product_(n : a_n!=0) (D_z-2 pi i n)`.

Thus every fiber is D-finite and DA. `square`

## Backward-time barrier corollary

Let `h(w)=sum a_n w^n in Qbar[[w]]` be a nonpolynomial DA entire function and form its formal periodic heat evolution

`sum a_n exp(-4 pi^2 n^2 t) exp(2 pi i n z)`.

This evolution cannot extend to an entire function on all of `C^2`. It must encounter a finite backward-complex-time barrier. Classical theta functions illustrate the correct boundary behavior: their Gaussian coefficient scale supports heat evolution only in a half-plane or strip, not for every complex time.

## Exact route consequence

This theorem rules out the following de Bruijn-Newman implementation:

1. replace the actual continuous Fourier kernel by a one-sided integer-frequency heat series with algebraic amplitudes;
2. require the deformation to be entire for every complex time;
3. use the appearance of a DA spatial fiber as the arithmetic transition.

If such a DA fiber occurs at the algebraic-coefficient anchor, the model collapses to finite spectrum and all of its fibers are DA. It therefore cannot carry a zeta-like infinite spectral source or a nontrivial DA/HT transition.

The actual de Bruijn-Newman deformation has a continuous, highly structured kernel rather than rational one-sided lattice amplitudes. Its zero-reality phase and the Newman constant remain outside this theorem. The result excludes the stated arithmetic lattice surrogate, not the original route.

## Parent and literature audit

1. **Pólya-Popken coefficient bound.** For a DA power series whose Taylor coefficients are algebraic, Popken proved that each coefficient is either zero or has size at least `alpha n^(-beta n log n)` at the fixed complex embedding. Krattenthaler and Rivoal explain that this follows by combining Pólya-Popken denominator control, Maillet bounds for all Galois conjugates, and the algebraic norm; see C. Krattenthaler and T. Rivoal, *Arithmetic properties of the Taylor coefficients of differentially algebraic power series*, arXiv:2502.09259.
2. **Mahler normalization.** K. Mahler, *A remark on algebraic differential equations*, Rend. Accad. Naz. Lincei 50 (1971), 402-412, shows that an algebraic-coefficient DA series may be taken to satisfy an ADE with algebraic coefficients.
3. **Arithmetic ADE coefficients.** V. Laohakosol, K. Kongsakorn, and P. Ubolsri, *Coefficients of differentially algebraic series*, J. Austral. Math. Soc. 48 (1990), 402-412, surveys and extends the Hurwitz-Pólya-Popken denominator theory.
4. **DA heat solutions.** V. Buchstaber and E. Netay, *Differential-algebraic solutions of the heat equation*, arXiv:1405.0926, constructs finite DA ansatz classes and connects theta/sigma heat solutions to nonlinear ODEs. It does not state the algebraic-Fourier, entire-complex-time finite-spectrum obstruction above.
5. Exact searches for DA periodic heat fibers, algebraic Fourier heat orbits, and Pólya-Popken heat applications did not locate this wording. The proof nevertheless fails the routine-parent gate: after the two estimates are written down, the contradiction is immediate.

## Failed unrestricted strengthening

`[CONJECTURE KILLED]` It is false that every transcendental entire DA function has positive ordinary order. Valiron constructed a third-order algebraic differential equation with a transcendental entire solution of order zero. Therefore ordinary growth alone cannot prove an unrestricted heat-fiber rigidity theorem. The algebraicity of the Taylor coefficients is essential to the proved statement.

Primary correction: G. Valiron, *Sur les fonctions entieres d'ordre nul et les equations differentielles*, Bull. Soc. Math. France 53 (1925), 34-42; see also Sh. Strelitz, *Three Theorems on the Growth of Entire Transcendental Solutions of Algebraic Differential Equations*, Canad. J. Math. 35 (1983), 1110-1128.

## Successor residue

The live non-arithmetic question is whether every nonpolynomial DA entire series must have infinitely many coefficients above some Gaussian scale. An affirmative answer would remove algebraicity entirely. Popken supplies the needed floor for algebraic coefficients, but arbitrary complex specializations have no available Diophantine lower bound; Valiron-type order-zero DA functions also prevent an ordinary-growth substitute.

## Log

- 2026-07-11 — Proved the arithmetic finite-spectrum theorem, killed the unrestricted order-zero argument with Valiron's example, checked DA heat-ansatz literature, and classified the result `[BRIDGE]` under the routine-parent gate.
- 2026-07-11 — Strengthened the coefficient class from rational numbers to all algebraic numbers using Popken's algebraic-coefficient lower bound and Mahler normalization. The strengthening remains `[BRIDGE]`.

## Lean formalization (2026-08-30)

Complete and unconditional; every declaration below depends only on `propext`, `Classical.choice`
and `Quot.sound`.

| Statement | Lean name | Module (`formal/GaloisForLFunctions/HTGeometry/`) |
|---|---|---|
| Card theorem | `arithmetic_heat_finite_spectrum` | `ArithmeticHeatFiniteSpectrum.lean` |
| Super-Gaussian decay `(1)` | `exists_gaussian_bound` | `ArithmeticHeatFiniteSpectrum.lean` |
| Entire generating function | `radius_eq_top_of_gaussian` | `ArithmeticHeatFiniteSpectrum.lean` |
| Logarithm chart is DA and faithful | `differentiallyAlgebraicOn_logChart`, `substitutionFaithful_logChart` | `ArithmeticHeatFiniteSpectrum.lean` |
| Popken's floor `(2)` | `exists_popken_floor_of_formalRelation` | `ArithmeticTaylorCoefficientFloor.lean` |
| Popken's bound from an integral Euler equation | `exists_popken_lower_bound` | `PopkenCoefficientLowerBound.lean` |
| Denominators of the inverse indicial values | `exists_indicial_denominator` | `PopkenCoefficientLowerBound.lean` |
| **Pólya–Popken denominator control** | `exists_mahlerDen_of_nondegenerate_eulerADE` | `PolyaPopkenDenominator.lean` |
| Mahler weight and its size | `mahlerScale`, `mahlerScale_mul_dvd`, `mahlerScale_succ_dvd`, `log_mahlerScale_le` | `MahlerDenominatorScale.lean` |
| Graded denominator calculus | `MahlerDen`, `exists_taylorDefect_const` | `MahlerDenominatorSeries.lean` |
| Denominators of algebraic numbers; norm of the inverse | `DenBy`, `exists_denBy`, `exists_norm_denominator` | `AlgebraicDenominator.lean` |
| Maillet for every conjugate | `exists_uniform_conjugate_gevrey`, `isFormalEulerADESolution_conj` | `EulerADEConjugate.lean` |
| Integral Euler normalization | `exists_integer_euler_ade` | `IntegerEulerADE.lean` |

Route notes.

* The hypothesis is the pointwise convergence of the heat series at every complex time and place,
  which is weaker than the local uniform convergence assumed on paper, so the Lean statement is
  slightly stronger than the card's.
* Step 2 is carried out with the corpus's composition-closure theorem
  `RGTowerCoherence.differentiallyAlgebraicOn_comp` on the disc `|w - 1| < 1/2`, where the
  principal logarithm chart `g(w) = log w / 2πi` is analytic, differentially algebraic
  (`2πi w g'(w) = 1`) and faithful; the relation obtained there extends to the plane by the
  identity theorem and passes to the Taylor series through `TaylorFormalBridge.taylorPS_jetFun`.
* The arithmetic parent — Pólya–Popken denominator control — was missing from the corpus and is
  built here in Mahler's own form: the weight `Δ_q = C^q ∏_{j ≤ q} A_j^{⌊q/j⌋}`, whose floor
  exponents are superadditive (`⌊i/j⌋ + ⌊i'/j⌋ ≤ ⌊(i+i')/j⌋`), is a denominator for the `q`-th
  coefficient, where `A_j` is the absolute norm of the `j`-th indicial value.  Superadditivity is
  exactly what the convolution in the nonlinear part of the coefficient recursion needs, and
  `∑_{j ≤ q} q/j ≤ q(1 + log q)` gives `log Δ_q = O(q (log q)^2)`, Popken's exponent.
* Maillet's bound for the Galois conjugates uses the naturality of the Euler jet evaluation under a
  ring homomorphism: after Mahler's integer normalization the equation is defined over `ℤ`, so each
  embedding of the coefficient field carries the solution to another solution of the same equation.
