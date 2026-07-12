# One rectangular two-edge window is a complete Weil detector

- **ID:** `explicit-rectangular-two-edge-weil-completeness`
- **Stage:** 1-in-progress
- **Type:** `[THEOREM]` / COFINAL CCM BOUNDARY COMPLETENESS AND POLE TOMOGRAPHY
- **Scientific status:** `[THEOREM] [NOVELTY AUDIT PASSED 2026-07-12] [PUBLICATION AUDIT IN PROGRESS]`
- **Statement:** For every fixed width `L>0`, the single translated rectangular two-edge family
  detects every possible off-critical Xi divisor.  If RH is false, its multiplicity-exact Weil
  values are unbounded below as the aperture tends to infinity.  Equivalently, RH is characterized
  by nonnegativity on this one explicit cofinal family.

## Candidate theorem

Fix `L>0`.  For `a>L`, let

```text
phi_(a,L)(x)=1_[a-L,a](x)+1_[-a,-a+L](x).                    (1)
```

Its bilateral centered Laplace transform is

```text
A_L(w)=(1-exp(-Lw))/w,
F_(a,L)(w)=exp(aw)A_L(w)+exp(-aw)A_L(-w).                    (2)
```

The removable value is `A_L(0)=L`.  For every `w` with `Re w>0`,

```text
A_L(w) != 0,                                                 (3)
```

because `exp(-Lw)=1` would force `Re w=0`.

Let `Q_Xi(F)` be the multiplicity-exact centered Xi-Weil polarization.  The proposed theorem is

```text
RH
 <-> Q_Xi(F_(a,L))>=0 for every a>L
 <-> inf_(a>L) Q_Xi(F_(a,L))> -infinity.                     (4)
```

More sharply, if RH is false then

```text
liminf_(a->infinity) Q_Xi(F_(a,L))=-infinity.                (5)
```

The proposed theorem is stronger on the aperture coordinate.  It should suffice
to test the single logarithmic sequence

```text
a_n=(1/2)log n,  n>exp(2L).                                 (5a)
```

Thus false RH should force `liminf_n Q_Xi(F_(a_n,L))=-infinity`.

## Why the rectangle removes the genericity layer

For a smooth compact profile `f`, the earlier two-edge theorem needed a residual choice satisfying
`A_f(w)!=0` at every off-line zero.  The rectangle has the exact transform `(2)`, and `(3)` holds
simultaneously for the entire open right half-plane.  No Baire category argument, profile
selection, or zero-dependent parameter remains.

For `Re w>0`, one also has

```text
A_L(-w)=exp(Lw)A_L(w),
F_(a,L)(w)^2
 =A_L(w)^2[exp(2aw)+2exp(Lw)+exp(-2(a-L)w)].                 (6)
```

The middle term is independent of `a`; the last is uniformly bounded for `a>=L`.  Since
`A_L(delta+i gamma)=O_L(1/|gamma|)` uniformly for `0<=delta<=1/2`, analytic multiplicity counting
makes both terms absolutely summable over the Xi divisor.  The on-line contribution is uniformly
bounded for the same reason.

Thus the only unbounded candidate is

```text
S_L(a)=4 Re sum_(w in Z_+) m_w A_L(w)^2 exp(2aw),            (7)
```

where `Z_+` contains one representative `w=delta+i gamma`, `delta>0`, from each off-line
FE--Schwarz quartet.

## Logarithmically sampled Landau globalization

Put

```text
delta_*=sup_(w in Z_+) Re w.                                 (8)
```

Under false RH, `0<delta_*<=1/2`.  At the sampled apertures `(5a)`, the growing term becomes the
ordinary generalized Dirichlet coefficient

```text
S_L(n)=2 sum_(w in Z_right) m_w A_L(w)^2 n^w,               (9)
```

where `Z_right` includes every multiplicity copy with `Re w>0`, hence is closed under conjugation
and makes `S_L(n)` real.  If `S_L(n)` were bounded below, choose `C` so that its tail plus `C` is
nonnegative.  Its ordinary Dirichlet series has, initially for `Re s>1+delta_*`, the continuation

```text
sum_(n>=N) [S_L(n)+C]n^(-s)
 =2 sum_(w in Z_right) m_w A_L(w)^2
    [zeta(s-w)-sum_(n<N)n^(w-s)]
  +C[zeta(s)-sum_(n<N)n^(-s)].                              (9a)
```

Every shifted pole `s=1+w` is genuine by `(3)`, so the abscissa is exactly `1+delta_*`.  The Xi
divisor has a uniform positive ordinate gap from the real strip segment; that gap is now proved in
Lean.  The zero-density estimate `N_Xi(R)=O(R log R)` now yields the multiplicity-exact
reciprocal-`3/2` law.  A square-root vertical zeta bound then proves that `(9a)` is locally normally
convergent and holomorphic on an explicit ball centred at the real point `1+delta_*`.

The required Landau theorem has also been sharpened.  Its Taylor centre may be placed an arbitrary
positive distance `h` to the right of a convergence point; there is no fixed unit aperture.  Hence
an eventual lower bound for `S_L(n)` produces a nonnegative tail series that converges at a real
point strictly left of `1+delta_*`.  The ordinary L-series of this tail is proved to equal `(9a)`
plus the constant-zeta term and a finite Dirichlet polynomial on `Re s>1+delta_*`.

The pole core is now closed.  Multiplication by `xi(s-1/2)` cancels every shifted-zeta pole, but at
a zero of multiplicity `m` the equal-support fiber retains exact order `m-1`; all off-support terms
have order at least `m`.  Local normal convergence preserves the latter order floor through the
infinite tail.  Landau continuation would make the complete cancelled carrier divisible by order
`m`, contradicting its exact order `m-1`.  Therefore false RH forces the sampled dominant
coefficients below every real level cofinally.  The FE fold identifies those coefficients with the
full dominant sum, and the aperture-uniform remainder gives `(5)` and `(5a)`.

## Positive CCM law

The cofinal detector requires no expanding profile class.  Its complete noncompact resource is the
single aperture coordinate:

```text
one fixed boundary window + cofinal translation + exact Xi divisor.             (10)
```

Accordingly, a successful CCM source construction need only prove nonnegativity on this explicit
one-parameter boundary section.  It must still transport the completed Euler--Gamma incidence to
the actual Xi divisor; finite-cutoff positivity alone does not supply that transport.

The positive dual of the completed no-go is stronger: for every `L>0`, RH is equivalent to this
single logarithmically sampled family being merely bounded below.  Thus any source theorem giving
one finite cofinal lower bound—not necessarily positivity—closes RH.

## Attacks

1. **Indicator regularity.**  The rectangle is not smooth.  The theorem must be stated directly
   on the multiplicity-exact divisor polarization, or the admissible Weil class must be shown to
   contain the indicator by completion.  No distributional explicit-formula claim is allowed
   without that closure theorem.
2. **Abscissa attack — closed.**  Scale-local Landau convergence is converted into an analytic
   shifted-zeta continuation and identified with the normally convergent Xi-cancelled carrier on a
   connected half-plane.  The exact order mismatch at an actual shifted pole gives the contradiction.
3. **Real-boundary attack — closed.**  Holomorphy at `1+delta_*` is proved from the actual Xi
   divisor, its unconditional zero count, and a qualitative uniform ordinate gap, not from an
   asserted numerical first-zero height.
4. **Cancellation attack — closed.**  The equal-support fiber is finite and consists of identical
   nonzero weighted terms; every other support is divisible by one additional local factor.
5. **Multiplicity attack — closed.**  The proof computes exact analytic order `m-1` and never uses
   simplicity.
6. **Parent-theory attack.**  Landau oscillation and Weil positivity are classical.  Candidate
   novelty is the one-window restriction and its exact nonvanishing mechanism, not either parent.
   Suzuki's 2025 Corollary 4.3 already gives an RH-equivalent one-parameter tail equality for a
   screw line, so "one parameter" alone is not novel.  The comparison must isolate the stronger
   claim here: one fixed-width translated rectangular Weil profile, positivity rather than a
   constructed norm equality, and forced divergence to `-infinity` under false RH.
7. **Formal gate.**  The standalone paper may claim `(4)`--`(5)` only after the complete Landau,
   divisor-series, and bounded-remainder proof is formalized unconditionally on the actual Xi
   divisor.

## Lean program

1. **Complete.** `CCMRectangularTwoEdge.lean` defines `A_L` and `F_(a,L)` and proves `(2)`, `(3)`,
   and `(6)`, together with evenness and exact compatibility with `xiWeilSharp`.
2. **Complete.** The same module proves square summability of `F_(a,L)` on the actual
   multiplicity-exact `XiZeroCopy` divisor by an explicit reciprocal-square majorant.
3. **Complete.**  The FE--Schwarz orbit contributes exactly four times the real part of one squared
   rectangular value on `XiZeroCopy`.  The growing edge is selected by the sign of the transverse
   coordinate, and the full multiplicity-exact polarization differs from its dominant-edge sum by
   an explicitly bounded remainder, uniformly for every aperture `a>=L`.
4. **Boundary continuation complete.**  The right-half coefficient series is absolutely summable,
   every coefficient is nonzero for `L>0`, logarithmic sampling gives the exact monomial `n^w`, and
   the shifted-zeta series is locally normally convergent and holomorphic on a positive-radius ball
   centred at `1+delta_*`.  The proof uses the formal reciprocal-`3/2` Xi-divisor law and the formal
   square-root vertical zeta bound.
5. **Scale-local Landau transfer complete.**  The arbitrary-shift Landau theorem, real coefficient
   construction, `O(n^delta_*)` growth bound, right-half L-series identity, finite-prefix correction,
   and forced convergence strictly left of `1+delta_*` are formalized unconditionally.
6. **Complete.** `CCMShiftedXiPoleJet.lean`, `CCMShiftedXiGlobalOrder.lean`,
   `CCMShiftedXiLandauContinuation.lean`, and `CCMShiftedXiLandauPoleContradiction.lean` prove the
   noncancelling arbitrary-multiplicity pole-jet contradiction.
7. **Complete.** `CCMRectangularDominantFold.lean` identifies the full dominant sum with the
   right-half real coefficient at logarithmic aperture.
8. **Complete.** `CCMRectangularWeilCompleteness.lean` combines the fold with the uniform remainder,
   proves `(5a)`, and proves RH equivalent to either nonnegativity or boundedness below of this one
   fixed-width sampled family.

9. **Complete screw-coordinate form.** `CCMRectangularScrewCurvature.lean` defines the
   multiplicity-exact real Xi screw profile

   ```text
   Psi_Xi(t)=sum_q [cosh(t(rho_q-1/2))-1]/(rho_q-1/2)^2
   ```

   by an absolutely convergent reciprocal-square series and proves the exact identity

   ```text
   Q_L(a)=2[Psi_Xi(2a)+Psi_Xi(2a-2L)-2Psi_Xi(2a-L)+2Psi_Xi(L)].
   ```

   Consequently false RH forces this fixed-width discrete curvature below every real level
   cofinally on `t=log n`, and RH is equivalent to either its nonnegativity or its eventual lower
   boundedness on that one arithmetic mesh.

10. **Complete transverse-growth law.** `CCMRectangularTransverseGrowth.lean` proves that if the
    right Xi divisor is nonempty and

    ```text
    delta_*=sup_Re(rho)>1/2 (Re(rho)-1/2),
    ```

    then the single fixed-width sampled sequence has sharp power exponent `delta_*`:

    ```text
    |Q_L(log n/2)| <= C_L n^(delta_*)
    ```

    at every admissible sample, while for every `0<=alpha<delta_*`, every `C>=0`, and every
    starting index, a later sample satisfies

    ```text
    |Q_L(log n/2)| > C n^alpha.
    ```

    Under RH the same family is uniformly bounded.  Hence RH is equivalent to boundedness of the
    norm of this one sampled family, and, when RH is false, the family recovers the exact supremal
    horizontal displacement rather than merely detecting its existence.

11. **Complete observable pole-support tomography.**
    `CCMRectangularPoleTomography.lean` constructs the canonical meromorphic continuation

    ```text
    C_L(s)=Xi-cancelled rectangular series / xi(s-1/2).
    ```

    In `Re(s)>1`, every shifted right-divisor coordinate `s=1+(rho-1/2)` is a simple pole of
    `C_L`, and there are no other poles there.  The order is always `-1`, including when `rho` is
    multiple: the numerator has exact order `m-1` and the denominator exact order `m`.

    `CCMRectangularObservablePoleTomography.lean` then removes the dependence on the isolated
    dominant component.  After deleting any finite prefix beyond which `L<=log(n)/2`, the actual
    logarithmically sampled Weil sequence differs from the right-divisor carrier by a uniformly
    bounded sequence.  The correction L-series is analytic throughout `Re(s)>1`.  Therefore the
    actual tail L-series has a canonical continuation whose simple-pole support in `Re(s)>1` is
    exactly

    ```text
    {1+(rho-1/2) : xi(rho)=0, Re(rho)>1/2}.
    ```

    Thus one fixed-width scalar Weil sequence recovers the complete off-critical support, while
    its sharp power exponent recovers the maximal horizontal displacement.

## Primary-literature novelty audit

The exact theorem surface was compared with Connes--Consani's scaling-Hamiltonian, zeta-cycle,
and archimedean Weil-positivity papers; Suzuki's 2025 Hilbert-space/screw-line criterion; Suzuki's
2022 screw-function RH criteria; and Suzuki's June 2026 unified screw-function treatment of the
Yoshida, Bombieri, Connes, and Connes--Consani--Moscovici forms.  Those works supply the parent
Weil/screw/operator frameworks and one-parameter criteria.  No located result gives the conjunction
proved here: an arbitrary fixed positive rectangle width, the arithmetic mesh `t=log n`, eventual
lower boundedness and norm boundedness as exact RH criteria, cofinal negative divergence under
false RH, sharp transverse power exponent, and exact simple-pole support tomography from the
observable tail L-series.  The novelty claim is restricted to that conjunction; Landau's theorem,
Weil positivity, shifted-zeta continuation, and screw functions remain acknowledged parent theory.

## Gates

- [x] candidate explicit profile and nonvanishing mechanism isolated
- [x] exact transform and leading/remainder decomposition proved on paper
- [x] scalar transform, symmetry, strip bound, and Xi-divisor square summability formalized in Lean
- [x] exact dominant-edge decomposition and global aperture-uniform remainder bound formalized
- [x] reciprocal-`3/2` Xi-divisor summability and square-root vertical zeta bound formalized
- [x] local normal continuation at the actual transverse boundary formalized
- [x] scale-local Landau transfer and forced left-boundary convergence formalized
- [x] arbitrary-multiplicity global pole-jet contradiction formalized
- [x] dominant fold and uniform-remainder restoration formalized
- [x] exact RH equivalence, cofinal divergence, and bounded-below criterion formalized
- [x] exact screw-function discrete-curvature identity and logarithmic-mesh criterion formalized
- [x] sharp transverse power exponent and norm-boundedness criterion formalized
- [x] complete paper proof audited at the divisor-polarization and abscissa boundaries
- [x] unconditional Lean formalization of every promoted divisor-side claim
- [x] primary-literature novelty audit
- [ ] independent proof audit
- [ ] standalone paper score at least 90/100
