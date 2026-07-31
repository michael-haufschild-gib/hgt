# Canonical cyclic trace law for faithful Sonin principal shells

- **ID:** `sonin-principal-shell-cyclic-trace`
- **Stage:** 2-fully-proven
- **Type:** THEOREM / source-specific principal finite-part descent
- **Scientific status:** `[CORPUS-NEW] [EXTERNAL NOVELTY PROVISIONAL] [NOT RH]`
- **Parents:** `CCMSoninFiniteWordNormalForm.lean`,
  `CCMSoninFiniteWordFaithfulness.lean`, `SoninLogShellCocycle.lean`,
  `SoninSemilocalRelativeTrace.lean`

## Theorem

Fix aperture `a>0`. A live canonical Sonin normal state is a window

```text
d=(C,F,x),   a <= F < C,   x>0,   a <= xF.
```

Define

```text
tau_a(0)=0,
tau_a(d)=1_(x=1) [log C-log F].                           (1)
```

For the exact tropical state product already proved to represent multiplication of the genuine
Sonin principal operators modulo compacts,

```text
tau_a(s*t)=tau_a(t*s)                                    (2)
```

for all zero/live states. The value is invariant under compact congruence of represented
operators. Its finite-support bilinear extension is cyclic.

For a genuine CCM Gram factor with source `r>1` and target `q>1`,

```text
tau_a(Gram(r,q)) = if r=q then log r else 0.              (3)
```

In particular, for `r=p^m`, the trace is `m log p`, independently of aperture. Multiplication by
the Euler-logarithm coefficient `p^(-m/2)/m` yields

```text
log(p) p^(-m/2),                                         (4)
```

the exact unsquared nonarchimedean Connes/Weil orbital coefficient.

## Proof

If the product displacement is not one, both sides of `(2)` vanish. Suppose the first scale is
`x`, the second is `y`, and `xy=1`. The exact normal-state composition formulas give

```text
C_(t*s)=x C_(s*t),
F_(t*s)=x F_(s*t).                                       (5)
```

The floor formula includes the Sonin base-cutoff normalization. Under `xy=1`, both input domain
conditions force the raw overlap floor above `a`, so this normalization is inert. Positive
dilation preserves strict overlap; therefore the two products are simultaneously live or zero.
When live, `(5)` and `log(xz)=log x+log z` give equal logarithmic widths. This proves `(2)`.

Faithful zero/live normal-form classification says two state operators are compact-congruent iff
their states agree, proving Calkin invariance. Summing `(2)` coefficientwise proves cyclicity of
the finite-support pairing.

For `Gram(r,q)`, exact normal data have displacement `r^(-1)q`. This equals one iff `r=q`.
On the diagonal the floor is `a`, the ceiling is `ra`, and `(1)` is
`log(ra)-log a=log r`, proving `(3)` and `(4)`.

## Theorem G: cyclic extension across the exact principal-relative ideal

Let `I_a` be the concrete Sonin principal-relative ideal (exact projection corrections and finite
physical/Fourier time-band blocks; every member is Schatten-1).  Call

```text
T = s.operator + K,    s a canonical window state,   K in I_a          (5G)
```

a *principal-relative operator*.  Define

```text
tilde_tau(T) = tau_a(s) + Tr(K).                                        (6)
```

Then, unconditionally for every aperture `a>0`:

1. **Directness.**  The presentation `(5G)` is unique, so `(6)` depends only on `T`.
2. **Restriction.**  `tilde_tau` is `tau_a` on principal shells and the ordinary trace on `I_a`.
3. **Closure.**  Principal-relative operators are closed under the genuine operator product; the
   exact residual
   ```text
   R(s,t) = s.operator * t.operator - (s*t).operator                    (7)
   ```
   lies in `I_a`, so `s.operator * t.operator =_r (s*t).operator` — a relative-ideal congruence,
   not merely a compact congruence.
4. **Cyclicity.**  `tilde_tau(TT') = tilde_tau(T'T)`, and its finite-support bilinear extension is
   symmetric.
5. **Single-corner anomaly formula.**  For a genuine CCM Gram factor `g=(r,q)` at aperture `a`,
   ```text
   tilde_tau(Gram_a(r,q)) = (if r=q then log r else 0) + Tr(Gram_a(r,q) - W_a(g)),  (8)
   ```
   where `W_a(g)` is the canonical live window of `g`.

### Proof

*Directness.*  Every member of `I_a` is compact, so two presentations of the same operator have
compact-congruent principal parts.  Faithfulness of the zero/live normal form forces the states to
be equal, and cancellation then forces the relative parts to be equal.

*Closure and the exact residual.*  The physical and the Fourier branch each multiply **exactly**:
same-polarization products are again window translations with the composed ceiling, floor, and
displacement, and the trailing central complement normalizes exactly.  Hence

```text
R(s,t) = P_s F_t + F_s P_t,                                             (9)
```

the sum of the two cross-polarization products, with no error term.  Each cross product carries a
physical band on one side and a Fourier band on the other; moving the dilation across turns it into
a finite time-band block times a bounded factor, so both summands lie in `I_a`.

*Cyclicity.*  Only one new input is needed, namely

```text
Tr(P F) = Tr(F P)                                                       (10)
```

for a physical window `P` and a Fourier window `F`.  Neither factor is compact, so bounded
cyclicity does not apply directly.  Let `G` and `H` be the physical band of `P` and the Fourier
band of `F`; they are idempotent and act as left units, `GP=P`, `HF=F`.  Put

```text
alpha = P H,    beta = F G.                                             (11)
```

Both lie in `I_a`, hence are Schatten-1 and therefore Hilbert--Schmidt, and

```text
alpha beta = P F G,     beta alpha = F P H.                             (12)
```

Since `PF` and `FP` are trace class and `GP=P`, `HF=F`, bounded cyclicity gives
`Tr(alpha beta)=Tr(PF)` and `Tr(beta alpha)=Tr(FP)`, while Hilbert--Schmidt cyclicity gives
`Tr(alpha beta)=Tr(beta alpha)`.  This proves `(10)`.  Applying `(10)` to both summands of `(9)`
gives `Tr R(s,t) = Tr R(t,s)`.  Expanding `TT'` and `T'T` leaves only that residual pair, three
bounded/trace-class commutations, and the already-proved state cyclicity `(2)`, so `(6)` is
cyclic.  Summing coefficientwise gives the finite-support bilinear statement.

*Single-corner formula.*  The quadratic Gram corner is relative-ideal congruent to its mixed shell
translation, which is exactly the canonical live window of `g` after normalization; `(3)` then
evaluates the principal term.

No zero location, asymptotic estimate, numerical experiment, or RH premise is used.  The
Hilbert--Schmidt pair `(11)` is the whole mechanism: the two orders of a noncompact cross product
are recovered from one Hilbert--Schmidt product taken in the two orders.

## Theorem H: one-sided aperture flag law for the extended trace

Fix a strict crossing flag

```text
0 < a < b < c < r*a,   r > 1.                                          (13)
```

Each aperture defect `Delta(u,v;r)` is a principal-relative operator whose principal part is the
scale-one lost shell `S(r*u, r*v)`.  Because `c <= r*a <= r*b`, **all three** defects of the flag
are presented at the single base aperture `c`, so one extended trace reads all of them.  Then

```text
tilde_tau(Delta(a,c;r))
  = tilde_tau(Delta(a,b;r)) + tilde_tau(Delta(b,c;r)) + Tr Kappa(a,b,c;r),  (14)
```

and, using the already-proved curvature energy law,

```text
Re tilde_tau(Delta(a,c;r))
  = Re tilde_tau(Delta(a,b;r)) + Re tilde_tau(Delta(b,c;r))
      - ||Z(a,b,c;r)||_HS^2,                                            (15)
```

where `Z` is the coupling between the two successive lost layers.  Hence

```text
Re tilde_tau(Delta(a,c;r))
  <= Re tilde_tau(Delta(a,b;r)) + Re tilde_tau(Delta(b,c;r)),            (16)
```

with equality exactly when `Kappa(a,b,c;r)=0`.  Moreover each of the three values is **real**:

```text
Im tilde_tau(Delta(u,v;r)) = 0,                                         (17)
```

so `(15)` and `(16)` are statements about the values themselves, not merely about real parts.

### Proof

The logarithmic weights are `log c - log a`, `log b - log a`, `log c - log b`, an exact
coboundary, so the principal parts of `(14)` cancel identically.  The shell residuals telescope
because `S(r*a,r*c) = S(r*a,r*b) + S(r*b,r*c)` holds as an operator identity, leaving exactly
`Kappa`.  All three residuals and `Kappa` are Schatten-1, so ordinary trace is additive on them.
Equation `(15)` is `(14)` plus the curvature energy law, and `(16)` is nonnegativity of a squared
Hilbert--Schmidt norm.  For `(17)`: the logarithmic weight is real, the defect is the Gram square
`X*X` of the lost-layer transition and the shell is a sum of orthogonal projections, so the
Schatten-1 residual is self-adjoint; and the diagonal sum defining the ordinary trace sends the
adjoint to the conjugate termwise, so a self-adjoint trace-class operator has real trace.

The content of `(16)` is that the completed finite part, **before** any archimedean term, is
already one-sided along aperture flags — but in the *subadditive* direction.  A uniform lower floor
therefore cannot be produced by aperture refinement alone: refining a flag can only decrease the
real extended trace, by exactly the successive-layer coupling energy.  Any surviving weld must
obtain its lower bound from the archimedean conductor, not from the aperture tower.

## Theorem J: the Burnol conductor as a concrete operator

The Burnol layer in the corpus is stated for an abstract bounded position channel `M` subject to
`[M, A_a] = 0`, and the only previously available way to satisfy that premise was to replace `M` by
its Lüders block at one fixed cutoff.  That is aperture-local: the Lüders block is built from the
very cutoff it commutes with, so a different aperture needs a different channel.

Physical cutoffs commute with each other, so every finite real combination of them commutes with
the whole cutoff family at once.  Take the combination whose value on the layer between `rᵏa` and
`rᵏ⁺¹a` is `log(rᵏa)`:

```text
M(a,r,n) = sum_(k<n) log(r^k a) . (A_(r^(k+1) a) - A_(r^k a)).            (18)
```

Then, unconditionally:

1. `M(a,r,n)` is bounded and self-adjoint, and `[M(a,r,n), A_c] = 0` for **every** `c`;
2. `M(a,r,n)` multiplies the shell unit vector of the `k`-th layer by exactly `log(rᵏa)`, so it is
   a genuine step logarithm of the position, and it is not the zero operator whenever
   `log a != 0`;
3. its conductor `H = M + JMJ`, with `J` the cosine-Fourier involution, is therefore a concrete
   operator, and the Burnol cancellation identity
   ```text
   [M, R_c] = J [H, A_c] J                                                (19)
   ```
   together with the pointed and finite-rank Burnol Ward reflection laws hold for it at **every**
   aperture `c` with the single fixed channel `(18)`.

### Proof

Two physical cutoffs multiply to the cutoff at the smaller radius in either order, so they commute
and `(18)` commutes with every `A_c`; real coefficients and self-adjoint cutoffs give
self-adjointness.  A shell unit vector of the `k`-th layer is fixed by every cutoff above the layer
and annihilated by every cutoff below it, so in `(18)` every term with `j<k` and every term with
`j>k` kills it and the `j=k` term returns it scaled by `log(rᵏa)`; a unit vector is nonzero, so a
nonzero scalar forces `M != 0`.  Equation `(19)` and the Ward laws are the corpus's abstract
identities with the premise now discharged by an actual operator.

This makes the Burnol interface inhabited rather than merely consistent.  It does not yet compute
the archimedean finite part, and it does not prove that the conductor cancels a divergence: `(18)`
is a bounded truncation, and the unbounded logarithmic multiplier and its commutator bounds are
still missing.

## Theorem K: the dilation commutator is exactly `log r`

A position channel is a *logarithm* only if conjugation by the dilation shifts it by a constant.
For the step channel `(18)` this holds exactly on the finite tower.  Write `U` for the normalized
dilation by `r⁻¹` and `A_s` for the physical cutoff at radius `s`.  Since `U A_s = A_(r s) U`, the
dilation carries each layer of the tower to the next, so

```text
U . M(a,r,n) = Mshift(a,r,n) . U,
Mshift(a,r,n) = sum_(k<n) log(r^k a) . (A_(r^(k+2) a) - A_(r^(k+1) a)).   (20)
```

Peeling the first term of `M(a,r,n+1)`, using `log(r^(k+1)a) = log(r^k a) + log r`, and
telescoping the resulting band sum gives

```text
Mshift(a,r,n)
  = M(a,r,n+1) - log a . (A_(r a) - A_a) - log r . (A_(r^(n+1) a) - A_(r a)),  (21)
```

hence the exact relation

```text
U . M(a,r,n)
  = ( M(a,r,n+1) - log a . (A_(ra) - A_a)
        - log r . (A_(r^(n+1) a) - A_(ra)) ) . U.                          (22)
```

Only two terms survive, one at each end of the finite tower.  Between them, on the interior band,
dilation conjugation subtracts exactly the scalar `log r`.  At base aperture `a=1` the lower edge
term vanishes identically and `(22)` reads

```text
U . M(1,r,n)
  = ( M(1,r,n+1) - log r . (A_(r^(n+1)) - A_r) ) . U.                      (23)
```

This is the archimedean generator relation `[log t, dilation] = log r . dilation` in exact finite
form: the constant produced by one dilation step is `log r`, independently of the layer, of the
aperture, and of the truncation length.  It identifies the conductor channel as a genuine
logarithm of position rather than an operator that merely takes logarithmic values.

## Theorem L: the truncations approximate the genuine logarithm

The step conductor `(18)` is multiplication by a step symbol; the genuine logarithm of position,
cut to the same tower band, is multiplication by `log|t|`.  Every point of the band lies in exactly
one layer, and on the layer between `rᵏa` and `rᵏ⁺¹a`

```text
0 <= log|t| - log(r^k a) <= log r,                                       (24)
```

so the two symbols differ by a bounded symbol with bound `log r`.  An operator acting almost
everywhere as multiplication by a symbol bounded by `K` has operator norm at most `K`, hence

```text
|| M(a,r,n) - Log_band(a,r,n) || <= log r,                               (25)
```

uniformly in the truncation length `n` and the base aperture `a`.  Refining the tower therefore
drives the step conductor to the genuine logarithm of position in operator norm; the truncations
are not merely logarithm-valued, they converge to the logarithm.

### Proof

Multiplication by a measurable symbol bounded by `C` is a continuous operator on `L^p` of norm at
most `C` — the pointwise estimate `||phi(x) f(x)|| <= C ||f(x)||` read through the `L^p` seminorm.
An even symbol commutes with the reflection, so the multiplier preserves the even carrier.  The
step channel is a finite combination of physical cutoffs, so it acts almost everywhere as
multiplication by the corresponding step symbol; evaluating that symbol on a layer collapses the
sum to the single surviving index.  The band logarithm is bounded on the band by
`|log a| + |log(r^n a)|`, and `(24)` is monotonicity of the logarithm on the layer.  Combining the
two symbol formulas gives `(25)`.

## Theorem N: the archimedean defect is not trace class

The scalar that dilation extracts from the conductor in `(22)` sits on the interior band
`A_(r^(n+1) a) - A_(r a)`.  For `n >= 1` that band is a nondegenerate shell projection, hence
noncompact, and `log r > 0`, so

```text
log r . (A_(r^(n+1) a) - A_(r a))  is noncompact, hence not Schatten-1.    (26)
```

Therefore the archimedean scalar is carried on an infinite-rank band.  It cannot be read by the
ordinary operator trace, and no trace-class counterterm can absorb it: the Burnol completion must
use the aperture-regularized reading supplied by the extended trace `(6)`, not an ordinary trace.

Together with Theorem H this pins the shape of the remaining problem from both sides.  The
aperture tower is subadditive, so the floor is not archimedean-free; and the archimedean defect is
not trace class, so the floor is not obtainable by adding a trace-class counterterm either.  What
survives is exactly the regularized pairing of the extended trace against the conductor.

## Theorem O: stationarity on the core of the logarithm

Let `f` be supported in the `m`-th tower band.  For `n >= m` the two band symbols agree on that
band, so

```text
Log_band(a,r,n) f = Log_band(a,r,m) f      for all n >= m.                (27)
```

The truncations are therefore *eventually constant* on every band-supported vector, not merely
convergent: they define one operator on the union of the band-supported subspaces, which is the
natural core of the logarithm of position.  The shell units of the tower lie in that core, so it
is not the zero subspace.

### Proof

Both symbols equal `log|t|` at every point of the smaller band, and `f` vanishes almost everywhere
off it, so the two products agree almost everywhere.  A shell unit of layer `k` is the normalized
indicator of a cell strictly inside `(r^k a, r^(k+1) a)`, hence inside the `m`-th band whenever
`k+1 <= m`.

What `(27)` does **not** give is the unbounded operator on the whole carrier: that needs density of
the core in the even carrier, an `L²` exhaustion argument which is not carried out here.

## Theorem P: the band-supported core is dense

Let `B_N = { t : 1/(N+1) < |t| <= N+1 }`.  These bands exhaust the punctured line, so

```text
(for all N, 1_(B_N) h = 0)  =>  h = 0,                                   (28)
```

because a nonzero point lies in some band and the origin is null.  Each `1_(B_N)` is an orthogonal
projection, so for any `h` the truncation `1_(B_N) h` is itself band supported, and

```text
<1_(B_N) h, 1_(B_N) h> = <1_(B_N) h, h>.                                 (29)
```

Hence a vector orthogonal to every band-supported vector has every truncation of norm zero, so by
`(28)` it vanishes:

```text
h orthogonal to the band-supported core  =>  h = 0,                      (30)
```

that is, the core is dense.  With Theorem O the truncated logarithms are stationary on that core,
so the logarithm of position is defined, unambiguously, on a dense domain: the unbounded
multiplier exists as the common value of the truncations.

### Proof

`(28)` is countable choice of a band per nonzero point plus nullity of the origin.  `(29)` is
idempotence and symmetry of the cutoff.  No integral estimate and no dominated convergence is
used: the orthogonal-projection identity replaces the exhaustion estimate entirely.

## Theorem Q: refinement loses exactly the accumulated coupling

Theorem H splits one aperture step into two.  Iterating it along a strictly increasing chain
`x_0 < x_1 < ... < x_m` inside a single crossing chamber `x_m < r x_0` gives, writing
`rho(u,v) = Tr(Delta(u,v;r) - S(r u, r v))`,

```text
rho(x_0, x_m) = sum_(i<m) rho(x_i, x_(i+1))
                  + sum_(1 <= j < m) Tr Kappa(x_0, x_j, x_(j+1)),         (31)
```

and hence, on real parts,

```text
Re rho(x_0, x_m) = sum_(i<m) Re rho(x_i, x_(i+1))
                     - sum_(1 <= j < m) ||Z(x_0, x_j, x_(j+1))||_HS^2.    (32)
```

The loss accumulates term by term, with no cancellation and no cross terms, so

```text
Re rho(x_0, x_m) <= sum_(i<m) Re rho(x_i, x_(i+1)).                       (33)
```

This upgrades the one-step no-go of Theorem H to a quantitative statement: refining an aperture
step into `m` pieces costs exactly the sum of the `m-1` successive lost-layer coupling energies.
Since every term is nonnegative, no refinement schedule can raise the value, so none can produce a
floor that the unrefined step does not already have.

**Sharpness is open.**  Equality in `(33)` holds exactly when every coupling of the chain vanishes:

```text
Re rho(x_0,x_m) = sum_i Re rho(x_i,x_(i+1))
  <->  Z(x_0, x_j, x_(j+1)) = 0 for every 1 <= j < m.                     (34)
```

Whether `Z` is ever nonzero in a crossing chamber is **not proved here**, and the two obvious
witness families provably fail.

*Outer family.*  The corpus's noncompactness witness for the pair `(a,b)` is supported in the
annulus `(r a, r d)`, which lies outside `[-c,c]`, so it is asymptotically fixed by `Q_c` and
`Z f_n = Y f_n - Y Q_c f_n -> 0`.  It carries no information about `Z`.

*Inner family.*  Shells supported in `(b,c)` are annihilated exactly by `Q_c`, so they do sit in
the range of `Q_b - Q_c`.  Both this and its Fourier dual are immediate from the corpus's exact
orthogonality identities `Q_c A_c = 0` and `Q_c R_c = 0`.  But the dilation moves that annulus to `(r b, r c)` or `(b/r, c/r)`, and inside the
crossing chamber `c < r a` neither image meets `(a,b)`: the first has `r b > b`, and the second has
`c/r < a`.  So `(Q_a - Q_b) D_r` sees nothing of it either, at the level of physical support.

Both failures are geometric: in the crossing chamber the dilation simply does not carry the `(b,c)`
annulus into the `(a,b)` annulus.  Any witness must therefore exploit the **Fourier tails** of the
Sonin projections rather than physical support, and any proof that `Z = 0` must control exactly
those tails.  That is the precise shape of the remaining question.

The dual annihilation law supplies the first handle on that side: vectors *band-limited* to
`[-c,c]` are also killed exactly by `Q_c`, so the range of `Q_b - Q_c` contains a second, purely
spectral family whose physical support is unconstrained.  Whether the dilation moves that family
into the `(a,b)` layer is the next thing to test.

**Method to use.**  Do not look for a witness vector.  The corpus already contains a working proof
of exactly this kind of nonvanishing, for the bilateral aperture holonomy
(`evenSoninBilateralApertureHolonomy_ne_zero`), and its shape is:

1. assume the operator vanishes;
2. turn that into a *commutation* of the Sonin projection with a dilation;
3. a commuting projection has zero dilation cross-boundary;
4. contradict `evenCentralSoninDilationCorner_not_isCompactOperator`, since `0` is compact.

Step 2 is the whole problem for `Z`: the holonomy is a one-aperture object and gives `Q` commuting
with the dilation by `r²` directly, whereas `Z = 0` is a three-aperture statement
`Q_a D_r Q_b - Q_a D_r Q_c - Q_b D_r Q_b + Q_b D_r Q_c = 0` with no evident commutator form.
Finding a specialization of the chamber in which it collapses to a commutation is the concrete
next task, and it is elementary algebra, not analysis.

Note also that `Z` commutes with the cosine Fourier involution
(`evenFourierTransform_evenSoninApertureSuccessiveLayerTransition`), so any such argument may
assume Fourier evenness throughout.

**Restatement now available.**  The coupling question is equivalent to a support question about
the defect itself:

```text
Z(a,b,c;r) = 0   <->   Delta(a,b;r) . (1 - Q_c) = 0,                      (35)
```

that is, the coupling vanishes exactly when the aperture defect between `a` and `b` is annihilated
by the complement of the carrier at `c` — exactly when the defect is *carried* by the outer
aperture.  Both directions are immediate from `Delta = Y* Y` and `Z = Y (1 - Q_c)`: forward by
associativity, backward because `Z* Z = (1-Q_c) Delta (1-Q_c)`.

This is the form to attack.  It is an identity between two explicitly constructed operators with no
compact error and no limit, so the question "is the coupling nonzero?" has become "does the
`a`-to-`b` defect see anything outside the `c`-carrier?".  Since the defect is relative-ideal equal
to the shell `S(r a, r b)` and `c < r a`, the defect is supported outside the `c`-window *modulo
the ideal*; whether that survives exactly is precisely what `(35)` asks.

**Sharpest form.**  The defect is a Gram square `Delta = Y* Y` with `Y = (Q_a - Q_b) D_r Q_b`, so it
absorbs the inner projection on both sides:

```text
Q_b Delta(a,b;r) = Delta(a,b;r) = Delta(a,b;r) Q_b.                       (36)
```

The defect therefore always lives on the carrier at `b`.  Combining with `(35)`:

```text
Z(a,b,c;r) = 0   <->   Delta(a,b;r) Q_c = Delta(a,b;r).                   (37)
```

So the whole question is a *carrier* question about one explicit positive operator: the defect
always lives on `K_b`; does it in fact already live on the smaller `K_c`?  Nothing analytic remains
in the statement — `(37)` is an equality of two products of explicitly defined projections and
dilations.  Writing the defect in its closed form
(`evenCentralSoninQuadraticCorner_restrictionDefect`), `(37)` reads

```text
Q_b D_r (Q_a - Q_b) D_r (Q_b - Q_c) = 0.                                  (38)
```

**Algebra is exhausted here.**  `(38)` is `Q_b D_r Z = 0`, so the reduction has closed a loop: every
further rearrangement returns an equivalent of `Z = 0` itself.  Settling it needs one of two things
that are not algebraic, and neither is in the corpus:

- a vector in `K_b (-) K_c` whose `D_r`-image has nonzero component in `K_a (-) K_b` — an explicit
  construction, since the physical-support families provably fail; or
- a structural theorem on how the Sonin projections at two apertures interact under dilation,
  strong enough to force the triple product to vanish.

Repeated algebraic restatement past this point produces equivalents, not progress.

**Witness criterion, and the exact obstruction to using it.**  On a vector `w` supported inside
`[-c,c]` the projection at `c` vanishes exactly, so

```text
Z w = Y w,        Y = (Q_a - Q_b) D_r Q_b,                                (39)
```

and hence `Z != 0` as soon as `Y` fails to annihilate some inner-band vector.  This moves the
search onto `Y`, which the corpus already proves noncompact — so `Y != 0` outright.  What is *not*
known is whether `Y` is nonzero **on the inner band** specifically.

Tracing the natural candidates shows why that is hard, and names the missing tool.  For `w` a shell
in the annulus `(b,c)`, `Y w = (Q_a - Q_b) D_r Q_b w`.  If `Q_b w` were still supported in `(b,c)`
the dilation would send it to `(r b, r c)` or `(b/r, c/r)`, and in the crossing chamber `c < r a`
neither meets `(a,b)`, so `Y w` would vanish.  But `Q_b w` is a Sonin vector: it is supported
outside `[-b,b]` with no upper support bound, so the argument does not apply and the value is
undetermined.

The missing lemma is therefore precise: **support control for `Q_b` applied to an annulus-supported
vector** — how far outside `(b,c)` the Sonin projection spreads it.

That spreading can now be isolated exactly.  The defining identity of the projection correction
gives `Q_b = 1 - A_b - R_b + C_b`, so on a vector killed by the physical cutoff,

```text
Q_b w = (1 - R_b) w + C_b w,        C_b Schatten-1,                       (40)
```

and therefore, for `w` in the annulus between the two apertures,

```text
Z w = (Q_a - Q_b) D_r [ (1 - R_b) w + C_b w ].                            (41)
```

So the entire obstruction is the **Fourier band-pass** `1 - R_b`: it is the only term that spreads
the support, and everything else is trace class.  The remaining question is quantitative and
classical — how much of `(1 - R_b) w`, for `w` supported in `(b,c)`, the dilation carries into the
`(a,b)` layer.  That is a time-band estimate of the kind the prolate literature supplies.

**Half of it is unnecessary.**  The dilation sum has two branches, and the forward one contributes
nothing.  A vector supported in `[-c,c]` is carried by `U_r` into `[-c/r, c/r]`, and `c <= r a`
makes that a subset of `[-a,a]`, where both Sonin projections annihilate exactly.  Hence

```text
(Q_a - Q_b) U_r w = 0,     so   (Q_a - Q_b) D_r w = (Q_a - Q_b) U_r^{-1} w  (42)
```

for every inner-band `w` in the chamber.  Only the inverse branch survives.

**The dual holds for the band-limited piece.**  Dilation acts inversely on frequency, so the
inverse branch *contracts* a Fourier band: `U_{r^-1}` carries band `[-b,b]` to `[-b/r, b/r]`, and
`b <= r a` puts that inside `[-a,a]`, where both projections annihilate band-limited vectors.  Hence

```text
(Q_a - Q_b) U_r^{-1} v = 0   whenever  R_b v = v,                         (43)
```

so on the band-limited piece only the *forward* branch survives.  Applying `(42)` to `w` and `(43)`
to `R_b w` in the split `(41)` leaves

```text
Z w = (Q_a - Q_b) U_r^{-1} w  -  (Q_a - Q_b) U_r R_b w
        + (Q_a - Q_b) D_r C_b w,                                          (44)
```

with a single, and opposite, dilation branch on each of the two principal terms.  The estimate now
has to compare an expanding dilation of the vector against a contracting-then-expanding dilation of
its Fourier band, plus a trace-class remainder.

`(44)` is proved, not merely assembled by hand
(`evenSoninApertureSuccessiveLayerTransition_apply_annulus_branches`).  It specialises to a
remainder-free identity on vectors killed by the exact projection correction — but **that
specialisation may be vacuous**: `C_b` is a nonzero Schatten-1 operator and nothing here shows its
kernel meets the annulus, so it must not be used as a witness family until inhabitedness is proved.

The usable form is quantitative instead, and needs no hypothesis beyond the annulus.  The aperture
layer is a self-adjoint idempotent, hence a contraction, and the dilation sum has norm at most two,
so the remainder in `(44)` is controlled outright:

```text
|| Z w - [ (Q_a - Q_b) U_r^{-1} w - (Q_a - Q_b) U_r R_b w ] ||
   <= 2 || C_b w ||.                                                      (45)
```

So the two opposite branches approximate the coupling on the whole annulus family, with error the
size of the correction.  A witness now needs only that the branch difference exceed `2||C_b w||`
for some annulus vector — a comparison between two explicit dilations and one Schatten-1 norm.

**The second branch is trace-class-small.**  On an inner-band vector the forward dilation and the
Fourier cutoff exchange places, and the physical cutoff at the inner aperture may be inserted for
free because `U_r` already carries the vector inside `[-a,a]`.  What is left is a finite time-band
block:

```text
U_r R_b w = ( R_{r b} A_a ) (U_r w),      R_{r b} A_a  Schatten-1,        (46)
```

so the second branch obeys `|| (Q_a - Q_b) U_r R_b w || <= || R_{r b} A_a || . || w ||` with a
*fixed* trace-class constant, uniformly in `w`.

The witness question is therefore concentrated entirely in the **first** branch: it suffices to
find an annulus vector with

```text
|| (Q_a - Q_b) U_r^{-1} w ||  >  || R_{r b} A_a || . || w ||  +  2 || C_b w ||,   (47)
```

both subtracted quantities being fixed trace-class quantities.  Everything else has been
eliminated.

**But the first branch is bounded by a deep-carrier distance.**  Both projections of the layer
absorb the projection at any larger aperture, so the layer annihilates every deeper carrier and

```text
|| (Q_a - Q_b) v ||  <=  || v - Q_s v ||     for every  a <= b <= s.       (48)
```

Applying this with `v = U_r^{-1} w` and any `s` between `b` and the inner radius of the expanded
support: **a family that is asymptotically inside a deeper Sonin carrier is asymptotically
invisible to the layer, whatever its support.**  This is the uniform reason every natural test
family has failed, and it cuts both ways — it also says a witness must be a family that stays a
definite distance from *every* deeper carrier, which no shell family does.

The two horns are therefore explicit.  Either such a family exists, or `Z = 0` in the crossing
chamber and the aperture defect is exactly additive.  `(48)` is the tool for the second horn.

**Outer compression form.**  The operator version of `(48)` is that the layer absorbs the
complement of any deeper carrier, and dually the outer layer absorbs it on the left.  Together:

```text
Z = (Q_a - Q_b)(1 - Q_c) . D_r . (1 - Q_c)(Q_b - Q_c),                     (49)
```

so the coupling never sees the dilation on the outer carrier at all — only the part of `D_r`
acting outside `K_c` contributes, on both sides.  This is the sharpest structural form: the
question is whether the dilation, compressed to the complement of the deepest carrier in the
chamber, still connects the two layers.

**The layer itself is elementary modulo the ideal.**  The complement of a Sonin projection is the
sum of its two forbidden cutoffs up to the exact correction, and each cutoff annihilates its own
projection, so

```text
Q_b - Q_c  =  (A_c + R_c) Q_b  -  C_c (Q_b - Q_c),      C_c Schatten-1,    (50)
```

that is, **the aperture layer is the outer window in both polarizations, restricted to the inner
carrier, modulo trace class**.  The layer's range was defined by an orthogonality condition; `(50)`
replaces it by explicit cutoffs, which is what any support or band computation needs.

**And the layer is simply a shell.**  Substituting the formal complement `1 - A_a - R_a` for the
inner projection in `(50)` leaves only elementary cutoffs.  The like-polarization products collapse
by the minimum law and the two mixed products are finite time-band blocks, so

```text
Q_a - Q_b  =_r  S(a,b)  =  (A_b - A_a) + (R_b - R_a).                      (51)
```

The aperture layer *is* the two-polarization shell, modulo the ideal.  This is the layer analogue
of the corpus's Theorem E for the defect, and it makes the coupling elementary: modulo the ideal,

```text
Z  =_r  S(a,b) . D_r . S(b,c),                                             (52)
```

a product of two explicit shells with a dilation between them.  `(52)` is proved, not assembled by
hand (`evenSoninApertureSuccessiveLayerTransition_principalRelativeEq_shellProduct`).

Expanding it gives eight terms.  The four mixed-polarization ones are finite time-band blocks,
hence in the ideal.  The four like-polarization ones vanish **exactly**: by the intertwining
`U_x A_C = A_{x^-1 C} U_x` each pairs the annulus `(a,b]` against `(b/r, c/r]` or `(r b, r c]`, and
in the chamber `c < r a` the first lies entirely below `a` while the second lies entirely above `b`,
so the disjoint-shell laws apply.  The Fourier duals of those laws are supplied here; the physical
ones were already in the corpus.

The expansion is now carried out in Lean, and it gives

```text
Z  in  I_a,                                                                (53)
```

the coupling lies in the concrete relative ideal — a strengthening of its Hilbert--Schmidt
property.  Note carefully what this is not: `Z in I_a` does **not** give `Z = 0`.  The whole
remaining gap between the two is the gap that has been open since the sharpness question was first
isolated.

### Proof

Induction on the chain length from the three-point law, with the chamber hypothesis inherited
because the chain is increasing.  The bookkeeping is done on the residual traces alone, so no
principal-relative presentation appears; the logarithmic weights cancel as a coboundary along the
chain in any case.  `(32)` is `(31)` plus the curvature energy law at each refinement, and `(33)`
is nonnegativity of a sum of squared Hilbert--Schmidt norms.

## Frontier effect

Closed:

- cyclicity of canonical principal Sonin shell value;
- aperture-independent diagonal orbital response;
- finite-place identification with exact von-Mangoldt flux;
- ambiguity from compact-congruent normal representatives;
- extension of the trace across the exact principal-relative ideal, with ordinary trace on its
  trace-class part, unique presentation, and full cyclicity for the genuine operator product.

Still open:

- attach Burnol archimedean conductor finite part;
- prove completed one-sided lower floor and RH.

Newly ruled out: obtaining the lower floor from the aperture tower.  By `(16)` the real extended
trace is subadditive along every strict aperture flag, with defect exactly minus the successive
lost-layer coupling energy, so refinement can only push it down.  The floor, if it exists, is an
archimedean statement.

Settled negatively elsewhere: aperture-restriction compatibility of the relative extension fails at
every strict aperture pair (`sonin-aperture-area-rigidity-and-restriction-defect`, Theorem D), so
the surviving route must carry the aperture cocycle rather than assume invariance.

## Novelty audit

Internal corpus search found the crossed-product trace law and faithful tropical normal form, but
no theorem connecting them; this theorem is corpus-new. Targeted inspection of the primary
Connes--Consani--Moscovici semilocal prolate paper found the Sonin Hilbertian isomorphism and
semilocal operator program, not the tropical normal-state trace `(1)`--`(3)`. External novelty is
provisional pending expert/literature review.

## Gates

- [x] dependency-closed paper proof
- [x] zero and nonidentity-displacement cases
- [x] exact reciprocal-scale overlap covariance
- [x] live/zero equivalence under cyclic swap
- [x] Calkin invariance from faithful normal form
- [x] finite-support cyclic pairing
- [x] exact CCM diagonalization
- [x] exact prime-power flux coefficient
- [x] relative-ideal trace extension
- [x] unconditional Lean formalization of `(1)`--`(4)` and Theorem G
- [x] one-sided aperture flag law for the extended trace (Theorem H)
- [x] reality of the aperture finite part
- [x] proof that the aperture tower alone cannot supply the lower floor
- [x] concrete Burnol conductor: a nonzero self-adjoint channel commuting with the whole cutoff
      family, discharging the abstract position hypothesis at every aperture at once (Theorem J)
- [x] exact dilation commutator of the conductor channel: `log r` on the interior band, with the
      two finite-tower edge terms computed exactly (Theorem K)
- [x] genuine logarithm of position on the tower band, and operator-norm convergence of the
      truncations to it at rate `log r` (Theorem L)
- [x] archimedean defect proved noncompact, hence not absorbable by any trace-class counterterm
      (Theorem N)
- [x] the truncations are stationary on the band-supported core, which is nonempty (Theorem O)
- [x] density of the band-supported core, hence the logarithm of position on a dense domain
      (Theorem P)
- [x] quantitative refinement loss along an arbitrary chain (Theorem Q)
- [ ] Burnol completion and completed lower floor

## Lean

| Statement | Declaration |
|---|---|
| `(2)` state cyclicity | `soninWindowStateCyclicLogTrace_compose_comm` |
| `(3)` Gram diagonalization | `soninGramFactorPrincipalCyclicTrace_eq_ite` |
| `(4)` prime-power flux | `soninPrimePowerPrincipalCyclicTraceDensity_eq_fluxCoefficient` |
| `(7)` relative-ideal closure | `soninWindowState_operator_mul_principalRelativeEq` (pre-existing) |
| `(9)` exact cross residual | `soninWindowStateResidual_live_eq_cross` |
| `(10)` cross-trace symmetry | `opTrace_physicalWindow_mul_fourierWindow_comm` |
| residual trace symmetry | `opTrace_soninWindowStateResidual_comm` |
| G.1 directness | `SoninPrincipalRelativeOperator.toOperator_injective` |
| G.2 restriction | `SoninPrincipalRelativeOperator.extendedTrace_ofState` / `..._ofRelative` |
| G.3 product realization | `SoninPrincipalRelativeOperator.toOperator_compose` |
| G.4 cyclicity | `SoninPrincipalRelativeOperator.extendedTrace_compose_comm` |
| G.4 bilinear cyclicity | `soninPrincipalRelativePairTrace_comm` |
| `(8)` single-corner anomaly | `SoninPrincipalRelativeOperator.extendedTrace_ofGramFactor` |
| aperture defect as presentation | `soninApertureRestrictionDefectPresentation` |
| aperture defect value | `extendedTrace_soninApertureRestrictionDefectPresentation` |
| `(14)` flag law | `extendedTrace_soninApertureRestrictionDefect_flag` |
| `(15)` exact scalar defect | `re_extendedTrace_soninApertureRestrictionDefect_flag` |
| `(16)` one-sided law | `re_extendedTrace_soninApertureRestrictionDefect_flag_le` |
| equality case | `re_extendedTrace_soninApertureRestrictionDefect_flag_eq_iff` |
| trace conjugation law | `ContinuousLinearMap.opTrace_adjoint` |
| real trace of a self-adjoint operator | `ContinuousLinearMap.im_opTrace_eq_zero_of_adjoint_eq` |
| `(17)` reality | `im_extendedTrace_soninApertureRestrictionDefectPresentation` |
| `(18)` concrete channel | `evenLogShellChannel` |
| J.1 universal commutation | `ccmCommutator_evenLogShellChannel_evenIndicatorCutoff` |
| J.1 self-adjointness | `adjoint_evenLogShellChannel` |
| J.2 logarithmic eigen-action | `evenLogShellChannel_apply_logShellUnit` |
| J.2 nonvacuity | `evenLogShellChannel_ne_zero` |
| J.3 conductor | `soninBurnolLogShellConductor` |
| `(19)` concrete cancellation | `ccmCommutator_evenLogShellChannel_evenFourierCutoff` |
| J.3 pointed Ward law | `pointedCutoffWardTrace_evenLogShellChannel_eq_burnolConductor` |
| J.3 finite-packet Ward law | `finiteRankCutoffWardTrace_evenLogShellChannel_eq_burnolConductor` |
| `(20)` dilation intertwining | `evenDilationCLM_mul_evenLogShellChannel` |
| `(21)` edge decomposition | `shiftedLogShellChannel_eq_sub_edges` |
| `(22)` Weyl relation | `evenDilationCLM_mul_evenLogShellChannel_eq_shift` |
| `(23)` unit-base form | `evenDilationCLM_mul_evenLogShellChannel_one` |
| bounded multiplier on `Lᵖ` | `MeasureTheory.lpBoundedMulCLM`, `norm_lpBoundedMulCLM_le` |
| symbol-bound norm law | `MeasureTheory.norm_le_of_ae_mul`, `norm_le_of_evenCoeFn_mul` |
| even-carrier multiplier | `evenBoundedMul` |
| channel as a multiplier | `evenLogShellChannel_coeFn` |
| `(24)` pointwise error | `norm_soninStepLogSymbol_sub_soninBandLogSymbol_le` |
| `(25)` operator error | `norm_evenLogShellChannel_sub_soninBandLogMultiplier_le` |
| `(26)` defect noncompact | `not_isCompactOperator_conductorDilationDefect` |
| `(26)` defect not Schatten-1 | `not_memSchattenClass_one_conductorDilationDefect` |
| `(27)` stationarity on the core | `soninBandLogMultiplier_eq_of_bandSupported` |
| core is nonempty | `soninBandSupported_logShellUnit` |
| `(28)` band exhaustion | `eq_zero_of_forall_bandTruncation_eq_zero` |
| `(30)` density of the core | `eq_zero_of_inner_bandSupported_eq_zero` |
| `(31)` chain flag law | `soninApertureResidualTrace_chain` |
| `(32)` accumulated loss | `re_soninApertureResidualTrace_chain` |
| `(33)` chain subadditivity | `re_soninApertureResidualTrace_chain_le` |
| chain equality characterization | `re_soninApertureResidualTrace_chain_eq_iff` |
| exact physical-band annihilation | `evenCentralSoninProjection_eq_zero_of_indicatorCutoff_eq_self` |
| exact Fourier-band annihilation | `evenCentralSoninProjection_eq_zero_of_fourierCutoff_eq_self` |
| `(35)` support restatement | `evenSoninApertureSuccessiveLayerTransition_eq_zero_iff_defect_mul_complement` |
| `(36)` defect carried by `Q_b` | `evenSoninApertureRestrictionDefect_mul_evenCentralSoninProjection` |
| `(37)` carrier form | `evenSoninApertureSuccessiveLayerTransition_eq_zero_iff_defect_mul_outer` |
| `(39)` inner-band agreement | `evenSoninApertureSuccessiveLayerTransition_apply_of_indicatorCutoff_eq_self` |
| witness criterion | `evenSoninApertureSuccessiveLayerTransition_ne_zero_of_lostTransition_apply_ne_zero` |
| `(40)` outer-band split | `evenCentralSoninProjection_apply_of_indicatorCutoff_eq_zero` |
| `(41)` reduced coupling | `evenSoninApertureSuccessiveLayerTransition_apply_annulus` |
| `(42)` forward branch vanishes | `evenSoninApertureLayer_evenDilationCLM_apply_eq_zero` |
| `(42)` inverse branch only | `evenSoninApertureLayer_evenDilationSum_apply_eq_inverse` |
| `(43)` inverse branch vanishes | `evenSoninApertureLayer_evenDilationCLM_inv_apply_eq_zero` |
| `(43)` forward branch only | `evenSoninApertureLayer_evenDilationSum_apply_eq_forward` |
| `(44)` branch normal form | `evenSoninApertureSuccessiveLayerTransition_apply_annulus_branches` |
| remainder-free case (possibly vacuous) | `..._apply_annulus_branches_of_correction_eq_zero` |
| `(45)` two-branch estimate | `norm_evenSoninApertureSuccessiveLayerTransition_sub_branches_le` |
| layer is a contraction | `norm_evenSoninApertureLayer_apply_le` |
| `(46)` second branch is a time band | `evenSoninApertureLayer_secondBranch_eq_timeBand` |
| `(46)` block is Schatten-1 | `memSchattenClass_one_secondBranch_timeBand` |
| `(47)` second-branch bound | `norm_evenSoninApertureLayer_secondBranch_le` |
| layer kills deeper carriers | `evenSoninApertureLayer_mul_evenCentralSoninProjection_eq_zero` |
| `(48)` deep-carrier bound | `norm_evenSoninApertureLayer_apply_le_dist_deepCarrier` |
| `(48)` asymptotic form | `tendsto_norm_evenSoninApertureLayer_apply_of_tendsto_deepCarrier` |
| `(49)` outer compression | `evenSoninApertureSuccessiveLayerTransition_eq_outerCompression` |
| `(49)` bound | `norm_evenSoninApertureSuccessiveLayerTransition_apply_le_outerCompression` |
| `(50)` layer window normal form | `evenSoninApertureLayer_eq_window_sub_correction` |
| `(50)` modulo the ideal | `evenSoninApertureLayer_principalRelativeEq_window` |
| `(51)` layer is a shell | `evenSoninApertureLayer_principalRelativeEq_twoPolarizationShell` |
| projection is its complement | `evenCentralSoninProjection_principalRelativeEq_formalComplement` |
| `(52)` shell product form | `evenSoninApertureSuccessiveLayerTransition_principalRelativeEq_shellProduct` |
| Fourier disjoint shells | `evenFourierShell_mul_eq_zero_of_left_ceiling_le_right_floor` |
| like-polarization vanishing | `indicatorShell_forward_vanishing`, `fourierShell_inverse_vanishing` |
| shell product in the ideal | `evenTwoPolarizationShell_mul_evenDilationSum_mul_shell_mem_ideal` |
| `(53)` coupling in the ideal | `evenSoninApertureSuccessiveLayerTransition_mem_principalRelativeIdeal` |

Files: `formal/GaloisForLFunctions/RHTower/SoninPrincipalShellCyclicTrace.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPrincipalRelativeCyclicExtension.lean`,
`formal/GaloisForLFunctions/RHTower/SoninApertureExtendedTraceFlagLaw.lean`,
`formal/GaloisForLFunctions/HTGeometry/OperatorTraceAdjoint.lean`,
`formal/GaloisForLFunctions/RHTower/SoninBurnolLogShellChannel.lean`,
`formal/GaloisForLFunctions/RHTower/SoninBurnolLogShellWeyl.lean`,
`formal/GaloisForLFunctions/HTGeometry/LpBoundedMultiplier.lean`,
`formal/GaloisForLFunctions/RHTower/EvenBoundedMultiplier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninBurnolLogBandComparison.lean`,
`formal/GaloisForLFunctions/RHTower/SoninBandSupportedDense.lean`,
`formal/GaloisForLFunctions/RHTower/SoninApertureFlagChain.lean`,
`formal/GaloisForLFunctions/RHTower/SoninInnerBandAnnihilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninApertureDefectSupport.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCouplingInnerBandCriterion.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOuterBandProjectionSplit.lean`,
`formal/GaloisForLFunctions/RHTower/SoninForwardBranchVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninInverseBranchVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCouplingBranchNormalForm.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCouplingBranchEstimate.lean`,
`formal/GaloisForLFunctions/RHTower/SoninSecondBranchTimeBand.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLayerDeepCarrierBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCouplingOuterCompression.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLayerWindowNormalForm.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLayerShellCongruence.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCouplingShellProduct.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellProductIdeal.lean`.
All declarations depend only on `propext`, `Classical.choice`, `Quot.sound`.

Novelty split for Theorem G: `(7)` was already in the corpus
(`SoninApertureRestrictionDefect.lean`) and is reused, not reproved.  New here are the exact
cross-polarization identity `(9)`, the cross-trace symmetry `(10)` and its Hilbert--Schmidt band
mechanism `(11)`--`(12)`, the directness/uniqueness of the presentation, the glued functional, its
cyclicity, and the single-corner formula `(8)`.

## Log

- 2026-07-31 — eight-term expansion completed: the four like-polarization terms vanish exactly by
  chamber disjointness, the four mixed ones are time-band blocks, so the shell product and hence the
  coupling lie in the relative ideal.  This is a strengthening of Hilbert--Schmidt, not a proof that
  the coupling vanishes; the gap between ideal membership and zero is what remains open.
- 2026-07-31 — shell product form of the coupling proved in Lean, closing the gap between the
  card's hand computation and the corpus, and the Fourier duals of the disjoint-shell vanishing laws
  added.  What remains of this line is the eight-term expansion itself.
- 2026-07-31 — layer-shell congruence: the aperture layer is the two-polarization shell modulo the
  ideal, the layer analogue of Theorem E for the defect.  The coupling therefore reduces modulo the
  ideal to a product of two explicit shells around a dilation, whose terms are annulus-disjoint in
  the chamber — so the coupling lies in the relative ideal.  Still short of Z = 0.
- 2026-07-31 — layer window normal form: the aperture layer is the outer window in both
  polarizations restricted to the inner carrier, modulo Schatten-1.  This trades the layer's
  orthogonality definition for explicit cutoffs, which is the form support and band computations
  can actually use.
- 2026-07-31 — outer compression form: the coupling is the dilation compressed on both sides by the
  complement of the outer carrier, so it never sees the dilation on K_c at all.  This is the
  operator version of the deep-carrier bound and the sharpest structural form of the question.
- 2026-07-31 — deep-carrier bound proved, giving the uniform reason every test family has failed:
  the layer annihilates every deeper carrier, so it sees a vector only through its distance to one.
  Any family asymptotically inside a deeper carrier is asymptotically invisible.  The two horns are
  now explicit — either a family staying a definite distance from every deeper carrier exists, or
  the coupling vanishes and the aperture defect is exactly additive.
- 2026-07-31 — second branch shown trace-class-small: on an inner-band vector it factors through
  the fixed time-band block R_(rb) A_a, which is Schatten-1, so it is bounded by a fixed constant
  times the vector norm.  The witness question is now concentrated entirely in the first branch,
  against two fixed trace-class quantities.
- 2026-07-31 — correction-free specialisation flagged as possibly vacuous and replaced by a
  quantitative estimate: the layer is a contraction and the dilation sum has norm two, so the
  two-branch difference approximates the coupling on every annulus vector with error at most twice
  the correction norm.  A witness now needs one explicit comparison, with no hypothesis whose
  inhabitedness is unknown.
- 2026-07-31 — branch normal form proved in Lean, closing the gap between the card's assembled
  equation and the formal corpus.  On a correction-free annulus vector the coupling is exactly the
  difference of the two opposite dilation branches, so a witness search can be restricted to those
  vectors and reduces to a single comparison.
- 2026-07-31 — dual branch elimination.  On the band-limited piece the inverse dilation contracts
  the Fourier band inside the inner aperture, where both projections annihilate, so only the forward
  branch survives there.  With the inner-band statement this leaves one dilation branch on each of
  the two principal terms of the coupling, and they are opposite branches.
- 2026-07-31 — forward branch eliminated.  In the chamber the contracting dilation pushes the outer
  window inside the inner aperture, where both Sonin projections annihilate exactly, so the aperture
  layer kills that branch outright.  The coupling on the inner band sees only the expanding
  dilation, halving what the remaining time-band estimate must cover.
- 2026-07-31 — the support spreading isolated.  On a vector outside the physical window the Sonin
  projection is the Fourier band-pass plus a trace-class correction, so the coupling on an annulus
  vector is the aperture layer applied to the dilated band-pass, up to trace class.  The whole
  obstruction is now the single classical operator 1 - R_b, and the remaining input is a time-band
  estimate rather than anything specific to the Sonin construction.
- 2026-07-31 — witness criterion proved and the missing analytic tool named.  On the inner band the
  coupling equals the lost transition, so a nonzero value of the lost transition there settles it;
  tracing the annulus candidates shows the obstruction is that the Sonin projection of an
  annulus-supported vector has no upper support bound.  Support control for Q_b on annulus vectors
  is the one input a resolution needs, either way.
- 2026-07-31 — algebra exhausted on the coupling.  The closed form of the defect turns the carrier
  condition into Q_b D_r Z = 0, which is equivalent to Z = 0 again: the reduction has closed a loop.
  Further rearrangement yields equivalents, not progress; what is needed is an explicit witness or a
  structural theorem on two-aperture projections under dilation.
- 2026-07-31 — sharpest form reached.  The defect is a Gram square ending on Q_b, so it absorbs the
  inner projection on both sides and always lives on the carrier at b.  The coupling then vanishes
  exactly when it already lives on the smaller carrier at c: a carrier question about one explicit
  positive operator, with nothing analytic left in the statement.
- 2026-07-31 — coupling question restated as a support question: the coupling vanishes exactly when
  the aperture defect is annihilated by the complement of the outer carrier.  No compact error and
  no limit remains in the statement, and the modulo-ideal picture (defect = shell above r a, with
  c < r a) says the answer is yes modulo the ideal — so the whole question is whether that survives
  exactly.
- 2026-07-31 — full-tree verification: both area umbrellas build (`RHTower` 14191 jobs,
  `HTGeometry` 12086 jobs) and `formal_tools.py lint` passes, so this session's modules integrate
  cleanly.  Also found the corpus's own nonvanishing technique (vanishing -> commutation -> zero
  cross-boundary -> contradiction with a noncompact corner) and recorded it as the method for the
  coupling question, replacing the vaguer "needs a Fourier-tail estimate" note.
- 2026-07-31 — dual annihilation added and a self-duplication corrected: the physical-band
  annihilation is one line from the corpus's `Q_c A_c = 0`, which the previous session's thirty-line
  proof had not used.  The Fourier dual then comes free from `Q_c R_c = 0` and opens the spectral
  side of the witness search.
- 2026-07-31 — both obvious witness families for the coupling ruled out, and the exact tool for the
  inner one formalized: shells inside the window are annihilated exactly, not asymptotically, by the
  Sonin projection.  In the crossing chamber the dilation does not carry the (b,c) annulus into the
  (a,b) annulus, so any witness must live in the Fourier tails of the projections.
- 2026-07-31 — sharpness isolated.  Equality in the chain law holds exactly when every coupling of
  the chain vanishes.  Whether any coupling is nonzero is open: the corpus's noncompactness witness
  is built for the wrong pair and lives in `ran Q_b` with no control of `Q_c`.  Recorded so the
  chain no-go is not read as asserting a positive loss.
- 2026-07-31 — one-step no-go upgraded to a chain law: refining an aperture step into m pieces
  loses exactly the sum of the m-1 successive coupling energies, with no cancellation.  A floor
  from refinement would have to survive an unbounded accumulation of nonnegative losses.
- 2026-07-31 — density closed, and the analytic detour avoided.  The `L²` exhaustion estimate was
  unnecessary: each band truncation is an orthogonal projection, so orthogonality to the core makes
  every truncation have zero norm, and band exhaustion of the punctured line finishes it.  With
  stationarity this puts the logarithm of position on a dense domain.
- 2026-07-31 — stationarity on the core proved: beyond the supporting band the truncations stop
  changing, so they define one operator on the band-supported core, and the shell units lie in it.
  Density of that core is the one analytic step still missing for the unbounded multiplier.
- 2026-07-31 — archimedean defect proved noncompact.  The scalar log r that dilation extracts sits
  on a nondegenerate shell band, so it is not Schatten-1 and no trace-class counterterm can absorb
  it.  With Theorem H this closes both escape routes: the floor is neither aperture-free nor
  trace-class-repairable, leaving only the regularized extended-trace pairing.
- 2026-07-31 — approximation closed.  Built the missing bounded-multiplier operator on L^p and its
  even-carrier restriction, identified the step conductor as multiplication by a step symbol, and
  proved the operator distance to the genuine band logarithm is at most log r, uniformly in the
  truncation length and the aperture.
- 2026-07-31 — dilation commutator computed exactly.  The step conductor satisfies the archimedean
  generator relation on the tower: conjugating by the dilation subtracts the constant log r on the
  interior band, with only two edge terms, both explicit.  The channel is a genuine logarithm of
  position, not merely an operator with logarithmic values.
- 2026-07-31 — Burnol conductor made concrete.  Audit finding: the whole Burnol layer was an
  uninhabited Prop interface, satisfiable only aperture-locally through Lüders pinching.  A step
  logarithm built from the shell cutoffs commutes with the entire cutoff family, is self-adjoint,
  acts on the k-th layer by log(r^k a), and is nonzero; every abstract Burnol identity now has a
  nontrivial instance with one fixed channel.
- 2026-07-31 — one-sided aperture flag law proved and formalized.  All three defects of a strict
  flag are presented at one base aperture, the logarithmic weights cancel as a coboundary, and the
  whole scalar defect is minus the successive-layer coupling energy.  Consequence: the aperture
  tower is subadditive, so it cannot supply the completed lower floor; that debt is archimedean.
- 2026-07-31 — relative-ideal trace extension closed and formalized.  New mechanism: a physical
  window and a Fourier window, each cut down to its own band, form a Hilbert--Schmidt pair whose
  two products recover the two orders of the noncompact cross product, giving `Tr(PF)=Tr(FP)`.
  This upgrades the previous compact congruence to an exact relative-ideal congruence and makes the
  glued functional a genuine cyclic trace.

