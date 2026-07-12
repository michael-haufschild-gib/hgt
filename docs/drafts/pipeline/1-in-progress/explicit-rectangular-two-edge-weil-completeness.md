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

## Landau globalization program

Put

```text
delta_*=sup_(w in Z_+) Re w.                                 (8)
```

Under false RH, `0<delta_*<=1/2`.  For `Re s>2delta_*`, termwise Laplace transformation gives

```text
L S_L(s)
 =2 sum_(w in Z_+) m_w
   [A_L(w)^2/(s-2w)+conj(A_L(w)^2)/(s-2conj(w))].            (9)
```

The `O(|gamma|^-2)` coefficient bound and the Xi zero-counting bound give locally normal
convergence away from the displayed poles.  Every pole is genuine by `(3)`.  Hence the Laplace
abscissa is exactly `2delta_*`: a smaller abscissa would make the Laplace transform holomorphic at
some genuine pole with larger real part.

The meromorphic continuation `(9)` is holomorphic near the real point `2delta_*`.  A pole there
would be a real nontrivial zeta zero, while nonreal poles cannot accumulate at a finite point.
Landau's oscillation theorem therefore rules out a lower bound for `S_L` on any tail and yields
`(5)` after restoring the uniformly bounded terms.

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
7. **Formal gate.**  The standalone paper may claim `(4)`--`(5)` only after the complete Landau,
   divisor-series, and bounded-remainder proof is formalized unconditionally on the actual Xi
   divisor.

## Lean program

1. Define `A_L` and `F_(a,L)` and prove `(2)`, `(3)`, and `(6)`.
2. Prove square summability of `F_(a,L)` on `XiZeroCopy` from the existing inverse-square divisor
   summability.
3. Formalize the off-line quartet decomposition and the bounded remainder.
4. Build the weighted resolvent series `(9)` and prove local normal convergence off its poles.
5. Formalize the continuous-Laplace Landau boundary-singularity theorem.
6. Identify the exact abscissa and specialize the theorem to the actual Xi divisor.
7. Prove `(4)`--`(5)` without a simplicity, RH, or source-positivity hypothesis.

## Gates

- [x] candidate explicit profile and nonvanishing mechanism isolated
- [x] exact transform and leading/remainder decomposition proved on paper
- [ ] complete paper proof audited at indicator-class and abscissa boundaries
- [ ] unconditional Lean formalization of every promoted claim
- [ ] primary-literature novelty audit
- [ ] independent proof audit
- [ ] standalone paper score at least 90/100

