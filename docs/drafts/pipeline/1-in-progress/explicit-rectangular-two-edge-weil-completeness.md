# One rectangular two-edge window is a complete Weil detector

- **ID:** `explicit-rectangular-two-edge-weil-completeness`
- **Stage:** 1-in-progress
- **Type:** `[CONJECTURE]` / COFINAL CCM BOUNDARY COMPLETENESS
- **Scientific status:** `[CONJECTURE] [NOVELTY UNVERIFIED] [TARGET SIGNIFICANCE 90/100]`
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
Lean.  Together with the `O(|gamma|^-2)` amplitude, zero counting, and a vertical-strip polynomial
bound for zeta, it should make `(9a)` locally normal and holomorphic near the real point
`1+delta_*`.

The already formalized nonnegative-Dirichlet-series Landau theorem then rules out the assumed lower
bound.  Restoring the uniformly bounded middle, decaying, and on-line terms yields `(5)` and the
stronger sampled assertion `(5a)`.  This reduction removes the need to formalize a separate
continuous-Laplace Landau theorem.

## Positive CCM law

The cofinal detector requires no expanding profile class.  Its complete noncompact resource is the
single aperture coordinate:

```text
one fixed boundary window + cofinal translation + exact Xi divisor.             (10)
```

Accordingly, a successful CCM source construction need only prove nonnegativity on this explicit
one-parameter boundary section.  It must still transport the completed Euler--Gamma incidence to
the actual Xi divisor; finite-cutoff positivity alone does not supply that transport.

## Attacks

1. **Indicator regularity.**  The rectangle is not smooth.  The theorem must be stated directly
   on the multiplicity-exact divisor polarization, or the admissible Weil class must be shown to
   contain the indicator by completion.  No distributional explicit-formula claim is allowed
   without that closure theorem.
2. **Abscissa attack.**  Conditional Laplace convergence left of `2delta_*` must imply
   holomorphy on the corresponding half-plane.  This is a real theorem, not a formal consequence
   of the meromorphic series.
3. **Real-boundary attack.**  Holomorphy at `2delta_*` must be proved from the actual Xi entire
   function, not from an asserted first-zero height.
4. **Cancellation attack.**  Opposite poles in `(9)` are distinct because off-line zeros have
   nonzero height.  The nonzero coefficients `(3)` prevent residue cancellation at each pole.
5. **Multiplicity attack.**  Every divisor copy must enter `(7)` with analytic multiplicity; no
   simple-zero assumption is permitted.
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
4. **Safe half-plane complete.**  The right-half coefficient series is absolutely summable, every
   coefficient is nonzero for `L>0`, logarithmic sampling gives the exact monomial `n^w`, and the
   shifted-zeta series converges absolutely on `Re s>=3/2+eps`.  Local normal continuation to the
   Landau boundary remains open and uses the now-formal uniform Xi ordinate gap.
5. Specialize the existing formal nonnegative-Dirichlet-series Landau theorem to `(9a)`.
6. Identify the exact abscissa and specialize the theorem to the actual Xi divisor.
7. Prove `(4)`--`(5a)` without a simplicity, RH, or source-positivity hypothesis.

## Gates

- [x] candidate explicit profile and nonvanishing mechanism isolated
- [x] exact transform and leading/remainder decomposition proved on paper
- [x] scalar transform, symmetry, strip bound, and Xi-divisor square summability formalized in Lean
- [x] exact dominant-edge decomposition and global aperture-uniform remainder bound formalized
- [ ] complete paper proof audited at indicator-class and abscissa boundaries
- [ ] unconditional Lean formalization of every promoted claim
- [ ] primary-literature novelty audit
- [ ] independent proof audit
- [ ] standalone paper score at least 90/100
