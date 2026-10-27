# Finite theta-source readings of the collided metric

- **ID:** CDG-FINITE-THETA-READINGS
- **Stage:** 3-formalized
- **Type:** Unconditional theorem; contribution status unaccepted.
- **Source:** Conjugate-Diagonal Geometry question 2.
- **Status:** Paper proof and exact Lean endpoints complete; novelty/significance gate open.
- **Count:** Unaccepted. All leaves form one candidate, together with the growing-aperture strengthening.

## Exact construction

Let `k=thetaCuspFullSource` and let `g_N` be the even reflection of the
literal half-line prefix through integer N. The finite carrier uses a
nonempty prefix:

```
A_N(s) = integral g_(N+1)(x) exp((1/2-s)x) dx,
B_N(s) = integral x g_(N+1)(x) exp((1/2-s)x) dx.
```

Every carrier field is proved for this actual source. In particular `A_N`
is entire, `A_N'=-B_N`, and the source is positive, continuous, even, and
has every exponential moment. Its possible physical cusp at zero is
compatible with these facts; smoothness at the cusp is not assumed.
The unscreened finite-prime source is a different construction.

Use the fixed smooth cutoff `chi_n`, equal to one on the disc of radius
`n+1` and supported in the disc of radius `n+2`. Set

```
M_n = 1 + ||D_1 chi_n||_infinity + ||D_i chi_n||_infinity
          + ||Delta chi_n||_infinity,
K_n = exp((n+1)^4) M_n,
eta_n = exp(-K_n),
N_n = ceil(K_n) + n + 10.
```

The prefix index, regulator and smooth cutoff are independent of the test,
moment order, motions, and zero divisor. The derivative suprema are
mathematical constants; no numerical implementation or computable
convergence modulus is asserted.

For `k_L(delta)=2cosh(2L delta)-2`, define the positive finite-source reading

```
Q_n(f,L,j) = pi^-1 integral chi_n(s) |F_f(s)|^2 k_L(Re(s)-1/2)^j
                 eta_n |B_(N_n)(s)|^2 / (|A_(N_n)(s)|^2+eta_n)^2 ds.
```

Here `F_f` is the centred transform of a compact C² test. Only finitely many
integer theta atoms enter each amplitude, although physical and spectral
integrals remain genuine integrals.

## Checked full-trace theorem

For every compact C² test f and natural j there are nonnegative B,D such
that, for every n>=1 and real L,tau satisfying

```
|tau| <= n/2,     j|L| <= 2log(n+1),
```

one has

```
|Q_n(twist_tau f,L,j)
  - sum_rho m_rho |F_f(rho-i tau)|^2 k_L(Re(rho)-1/2)^j|
 <= B exp(-n^4+56n^2+62) + D (16/n)(C_xi+log(n+4)).
```

Consequently these readings converge uniformly throughout the joint
window to the full multiplicity-weighted trace. Order zero gives the
collided form; order one gives the symmetric Hecke defect. Neither simple
zeros nor an admitted zero-free contour is required.

The stronger quantifier order, uniform over normalized tests in growing
physical apertures and over all orders after division by `4^j`, is tracked
in `logarithmic-aperture-finite-theta-metric.md`. It is part of the same
candidate, not a separate contribution.

## Dependency-closed paper proof

1. **Relative integer tail.** The actual first-atom domination gives
   `0<=thetaCuspSourceTerm(x,m)<=2m^4 exp(-pi(m^2-1)) thetaCuspSourceTerm(x,1)`
   for x>=0,m>=1. With the finite constant
   `C_tail=2exp(pi) sum_m m^4 exp(-(pi-1)m^2)`, extracting `exp(-N^2)`
   from the omitted atoms and using exact evenness gives
   `0<=k(x)-g_N(x)<=C_tail exp(-N^2) k(x)` globally.
2. **Entire finite amplitudes.** The nonempty reflected prefix is bounded
   by the full positive source. Its continuity, evenness, strict positivity,
   and all exponential moments therefore satisfy the existing bilateral
   transform theorem. This proves entireness and the exact first-moment
   derivative without any derivative-tail premise.
3. **Disc bounds.** The actual source envelope is
   `k(x)<=U exp((|M|+5)^2/24) exp(-M|x|)`, with fixed U>0.
   Put `J=integral exp(-|x|) dx` and
   `H_R=U J exp((R+15/2)^2/24)`. Choosing M=R+5/2 gives, on |s|<=R,
   `|A_N(s)|,|xi(s)|<=H_R` and
   `|A_N(s)-xi(s)|<=C_tail H_R exp(-(N+1)^2)`.
4. **Potential stability.** For eta>0 and complex a,b,
   `|0.5log(|a|^2+eta)-0.5log(|b|^2+eta)|
    <=(|a|+|b|)|a-b|/(2eta)`.
   The logarithm estimate follows from integrating its derivative above
   eta; the norm-square difference is bounded by the reverse triangle
   inequality. Let `C0=C_tail(UJ)^2`.
5. **Prescribed coupling.** For R=n+2, the cutoff satisfies
   `N_n^2>=K_n^2+(n+10)^2`, while
   `(R+15/2)^2/12<=(n+10)^2` and `M_n<=K_n<=exp(K_n)`.
   Since `K_n>=exp((n+1)^4)` and `(n+1)^4>=16` for n>=1,
   `2K_n-K_n^2<=-(n+1)^4`. Thus the finite-minus-full potential V_n obeys
   `M_n |V_n(s)|<=C0 exp(-(n+1)^4)` on the entire cutoff disc.
6. **Compact-current transfer.** The finite potential has Laplacian twice
   `eta |B_N|^2/(|A_N|^2+eta)^2`. Compact Green testing therefore gives
   `|finiteReading(phi)-explicitReading(phi)|
    <=(2pi)^-1 B C0 pi(n+2)^2 exp(-(n+1)^4)`
   whenever `|Delta(chi_n phi)|<=M_n B`. The exact derivative identity in
   step 2 identifies the literal first moment in this curvature.
7. **Moving local error.** For the depth test, the proved C² bound has
   `B=4^(j+1) A_f^2 exp(E)` with
   `E=2((n+3+|tau|)^2+j|L|(n+7/2))` and a proved Gaussian transform
   constant A_f. The joint window and the disc area give finite-source
   error at most
   `(2pi)^-1 4^(j+1) A_f^2 (4pi C0) exp(-n^4+56n^2+62)`.
8. **Full actual divisor.** The checked prescribed-xi regulator theorem
   has the same local envelope, and the omitted moving trace is bounded
   by a fixed multiple of `sourceReferenceTail(n)`. The latter is at most
   `(16/n) Re(xi'/xi)(1+n)`, hence at most
   `(16/n)(C_xi+log(n+4))`, by proved arithmetic right-half-plane bounds.
   Two triangle inequalities yield the stated full-trace certificate and
   its uniform limit. All multiplicities are retained.

## Lean status

Checked main leaves and endpoint axiom closures:

- `ThetaCuspIntegerRelativeTail`: `reflectedFiniteThetaSource_relative_tail`.
- `ThetaCuspReflectedFiniteSource`: `hasDerivAt_finiteThetaAmplitude`.
- `ThetaCuspFiniteAmplitudeBounds`: finite amplitude error on complex discs.
- `HTGeometry/RegularizedLogStability`: `half_log_normSq_stability`.
- `FiniteThetaRegulatorScale`: `finiteTheta_potential_envelope_le`.
- `FiniteThetaSourceCurvature`: `sourceControl_mul_finiteThetaPotential_error_le`,
  `twice_integral_finiteThetaSourceCurvature`.
- `FiniteThetaReadingError`: `finiteThetaSourceReading_error_le_window`.
- `ExplicitThetaErrorCertificate`: the actual full-source logarithmic error
  certificate, including its dependency olean.

Every listed endpoint has only `propext`, `Classical.choice`, `Quot.sound`
in its transitive axiom closure. Finished leaves are wired into their
owning umbrellas; no umbrella is compiled. `FiniteThetaMetric` passes scratch and main leaf checks (90209, 49941),
including `finiteThetaSource_uniform_moving_moments`,
`exists_finiteThetaSource_logarithmic_error_bound`,
`finiteThetaSource_uniform_moving_collided`, and
`finiteThetaSource_uniform_moving_heckeDefect`, each with the same standard
transitive axiom closure.
No numerical computations, added analytic premises, or raised proof limits.

## Novelty and significance audit

Established ingredients are excluded from any contribution count:

- Haglund, [finite Xi approximants](https://arxiv.org/pdf/0910.5228) (2009),
  equations (2),(3),(12)–(14), already uses the same finite half-line theta
  transforms up to normalization and coordinates, their entireness and
  compact-local approximation.
- Andersson, [Poincaré–Lelong Type Formulas and Segre Numbers](https://d-nb.info/1355764351/34),
  J. Geom. Anal. 35:25 (2025), §5.6, contains the regularized-current
  mechanism whose scalar density is proportional to
  `eta |A'|^2/(|A|^2+eta)^2`.
- Van Hemert, [Exact Zero Detection and Compact Arithmetic Realizations for
  the Riemann Xi Function](https://raw.githubusercontent.com/LeonardSEO/riemann-xi-zero-detection/main/paper/paper.tex)
  (11 October 2026), treats reflected finite heads, seam obstructions and
  Gaussian absolute tails. Those constructions are not novelty claims.
- Corpus `XiCTaylorThetaTailFiniteCoefficientGate` uses error-selected
  Taylor schedules and separate oriented-current gates.
  `HedenmalmCoefficientFaithfulExteriorSourceContour` interpolates at actual
  zeros and uses admitted contours. `XiThetaArithmeticTraceZeroHankelApproximants`
  has positive finite Gauss stages without Xi divisor fidelity.
  `XiCTaylorThetaTailFiniteArithmeticCofinalSelection` has a pointwise
  Hermitian density defect at an admitted affine endpoint.
- `XiCompactPolarWeilRealization` already proves faithful compact-source
  evaluation and full spectral completion. Generic rank or faithfulness
  corollaries are therefore not additional contributions.

The exact remaining candidate is the full arithmetic collided metric with
one prescribed finite prefix/regulator, quantitative moving-window control,
and the growing-test-family quantifier order. A failed search for an exact
counterpart is not evidence by itself of novelty. Acceptance requires the
combined theorem and an affirmative significance judgment, not a count of
its helper lemmas.

## Calibration and limitations

This is positive conjugate-diagonal geometry. It carries no successor
charge, no odd-detector sign, and no bound `Delta<=D`. Planted off-line
packets contribute positive mass. The mechanism also applies to other
entire sources with the required proved approximation bounds, so positivity
alone does not select the zeta fibre. No simplicity, critical-line location,
zero-spacing estimate, or RH theorem follows from the construction.
