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

**Sharpness, now settled.**  Equality in `(33)` holds exactly when every coupling of the chain
vanishes:

```text
Re rho(x_0,x_m) = sum_i Re rho(x_i,x_(i+1))
  <->  Z(x_0, x_j, x_(j+1)) = 0 for every 1 <= j < m.                     (34)
```

`Z` **is** nonzero in a crossing chamber: the sibling card
`cofinal-essential-phase-sonin-coupling-nonannihilation.md` constructs a frequency-locked annular
Meyer wavepacket family on which `|| Z_r w_r - U_{1/r} w_r || -> 0`, so `Z_r != 0` for all large
`r` (`exists_scale_soninApertureCoupling_ne_zero`), and the inequality `(33)` is therefore strict
at an actual flag and scale (`exists_strict_soninApertureResidualTrace_chain`, with the explicit
gap `1/4` in `exists_soninApertureResidualTrace_chain_gap`).  The two obvious witness families
below still provably fail — the witness has to be the escaping wavepacket, not a support-supported
shell — and that is why the construction is on the sibling card rather than here.

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
further rearrangement returns an equivalent of `Z = 0` itself.  Settling it needed one of two things
that are not algebraic:

- a vector in `K_b (-) K_c` whose `D_r`-image has nonzero component in `K_a (-) K_b` — an explicit
  construction, since the physical-support families provably fail; or
- a structural theorem on how the Sonin projections at two apertures interact under dilation,
  strong enough to force the triple product to vanish.

Repeated algebraic restatement past this point produces equivalents, not progress.

**Answered by the first route.**  The escaping wavepacket of the sibling card is exactly such a
vector family, and it is not of physical-support type — it escapes to infinity in position while
its rescaled frequency stays locked.  So `(38)` is *false* in the crossing chamber:
`exists_scale_soninApertureTripleProduct_ne_zero` gives an actual dilation scale at which
`Q_b D_r (Q_a - Q_b) D_r (Q_b - Q_c) != 0`, and hence
`exists_scale_evenSoninApertureRestrictionDefect_mul_outer_ne` shows the defect, which by `(36)`
always lives on `K_b`, does **not** live on the smaller `K_c`.  The carrier question of `(37)` is
therefore settled in the negative.

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

**What actually carries the coupling.**  The like-polarization terms vanish *identically*, not just
modulo the ideal, so the shell product is not merely congruent to the mixed terms — it equals their
sum exactly:

```text
S(a,b) D_r S(b,c)
  = (A_b - A_a) U_r (R_c - R_b)  +  (A_b - A_a) U_r^{-1} (R_c - R_b)
  + (R_b - R_a) U_r (A_c - A_b)  +  (R_b - R_a) U_r^{-1} (A_c - A_b).      (55)
```

So `Z` is congruent to a sum of exactly four finite time-band blocks, each a physical band composed
with a Fourier band across a dilation, and the vanishing question is precisely **whether those four
blocks cancel**.

This is evidence against vanishing rather than for it, and the individual nonvanishing is now
proved rather than argued.  The corpus computes the squared Hilbert--Schmidt norm of a finite time
band as the exact rectangle area, so for a nondegenerate rectangle

```text
|| timeBand(a,b;c,d) ||_HS^2 = (b-a)(d-c) > 0,   hence  timeBand != 0.     (56)
```

Each of the four blocks in `(55)` is therefore individually nonzero, and the energy is strictly
monotone in the rectangle, so the four have genuinely different sizes.  Theorem S below settles the
cancellation question outright.

## Theorem S: the four mixed blocks do not cancel

Group the four blocks of `(55)` by the polarization of their *range*:

```text
M_phys = (A_b - A_a) D_r (R_c - R_b),      M_four = (R_b - R_a) D_r (A_c - A_b).
```

`M_phys` absorbs `A_b` on the left and `M_four` absorbs `R_b` on the left, so their values at a
common vector lie in the physical band `(a,b]` and the Fourier band `(a,b]` respectively.  A vector
in both bands is zero — the qualitative uncertainty principle — hence

```text
M_phys + M_four = 0   <=>   M_phys = 0  and  M_four = 0.                   (57)
```

The two polarizations therefore *cannot* cancel each other; they can only vanish separately.  And
the physical one does not vanish:

```text
M_phys != 0   and   M_four != 0     whenever 0 < a < b < c and r > 1.      (58)
```

Consequently

```text
M_phys + M_four != 0,                                                      (59)
```

so the four-block expansion of `(55)` is a nonzero operator: the blocks do not cancel.

The Fourier half is the same argument with the polarizations exchanged; it is recorded because it
shows the two halves are *both* live, not merely their sum.

### Proof of `(58)`

Suppose `M_phys = 0`.  Fix `w` and put `v = (R_c - R_b) w`, `y = D_r v`.

*Step 1 — `y` is band-limited at `r c`.*  Conjugating the Fourier cutoff through the two dilations
gives `R_{rc} U_r = U_r R_c` and `R_{rc} U_{r^{-1}} = U_{r^{-1}} R_{r^2 c}`, and both `R_c` and
`R_{r^2 c}` fix `R_c`, so `R_{rc} D_r R_c = D_r R_c`.  Since `R_c v = v`, `R_{rc} y = y`.

*Step 2 — `y = 0`.*  By hypothesis `(A_b - A_a) y = 0`, i.e. `y` vanishes a.e. on the shell
`(a,b)`.  On the even subspace the Fourier transform is an *involution* (it squares to reflection,
and reflection is the identity there), so `y` is itself the Fourier transform of a boundedly
supported vector.  The one-interval uncertainty theorem — a boundedly supported `L^2` function whose
Fourier transform vanishes on a nondegenerate open interval is zero — then gives `y = 0`.  Note the
sharpness: only one interval of vanishing is used, not a whole complementary band.

*Step 3 — `v = 0`.*  So `D_r v = 0`, i.e. `U_r v = -U_{r^{-1}} v`, i.e. `U_{r^{-2}} v = -v`.  The
same Fourier covariance now shrinks the band: from `R_t v = v` it follows that
`R_{t r^{-2}} v = R_{t r^{-2}} (-U_{r^{-2}} v) = -U_{r^{-2}} R_t v = -U_{r^{-2}} v = v`.  Iterating
from `t = c`, the vector `v` is band-limited at `c r^{-2n}` for every `n`; choose `n` with
`c r^{-2n} <= b`.  But `R_b v = 0`, and `R_b R_{c r^{-2n}} = R_{c r^{-2n}}`, so `v = 0`.  No limit
argument is needed — one aperture below `b` suffices.

*Step 4 — contradiction.*  Hence `R_c - R_b = 0`.  But a nondegenerate Fourier annulus is nonzero:
the Fourier transform of a symmetric physical shell vector is a unit vector on which `R_c - R_b`
acts as the identity, because the Fourier transform preserves evenness and squares to the identity
there.  Contradiction.

For `M_four` the four steps read the same with `A` and `R` exchanged, and two simplifications: the
image is *compactly supported* rather than band-limited, so the one-interval uncertainty theorem
applies to it directly with no involution step, and the band-shrinking iteration is run with the
expanding dilation `U_{r^2}` instead of the contracting one.  Step 4 is then the physical annulus,
where the shell vector is the witness with no Fourier transform taken.

### What `(59)` does and does not settle

It closes the cancellation question that `(55)` opened: **the blocks do not cancel**.  It does not
give `Z != 0`, and — this is the point worth recording — it *cannot*.  From `(55)` one gets

```text
in the crossing chamber 0 < a < b < c <= r a:
  Z = 0   =>   M_phys + M_four  in  I_a,                                   (60)
```

but the hypothesis of the contrapositive is unsatisfiable: `M_phys + M_four` is exactly the shell
product `S(a,b) D_r S(b,c)`, and that product was already proved to lie in `I_a` — it is how `(53)`
was obtained in the first place.  So `(60)` is a true statement with a vacuous useful direction.
Every object the congruence route produces lies in the ideal, on both sides, and the ideal is
exactly what the congruence forgets.  **The congruence route cannot decide `Z = 0` at all.**

The durable content of Theorem S is therefore not `(60)` but `(58)`: the two polarized blocks are
individually nonzero, together with the uncertainty machinery that proves it — qualitative
uncertainty on the even subspace, the Fourier involution there, one-interval vanishing, and
injectivity of the dilation sum on both a Fourier and a physical annulus.  Those apply to any
operator, not only to congruence classes.

## The open core, stated exactly

Both aperture layers are self-adjoint, so the coupling is zero exactly when the dilation sum carries
one layer into the orthogonal complement of the other:

```text
Z = 0   <=>   < (Q_a - Q_b) u ,  D_r (Q_b - Q_c) v >  =  0   for all u, v.  (61)
```

`(61)` has no algebra left in it: `K_a ⊖ K_b` and `K_b ⊖ K_c` are two nonzero Sonin layers, and the
question is whether the dilation group moves one into the orthogonal complement of the other.  That
would be a rigidity with no evident source, since the layers are not dilation-invariant and the
dilation sum is injective on the bands that surround them.  It remains open, but this is the
statement to attack, and it is the first form of the question that mentions neither the relative
ideal nor any approximation.

**One Sonin space carries the whole question.**  The dilation sum does not preserve the aperture
tower but it does not leave it either — it only loses a factor `r` of aperture:

```text
D_r K_a  subset  K_{a/r},   equivalently   Q_{a/r} D_r Q_a = D_r Q_a.      (62)
```

In the crossing chamber `b/r < a`, so both layers already live inside `K_{b/r}`, and `(62)` says the
dilated inner layer does too.  The coupling is therefore exactly the *compression* of the dilation
sum to that single Sonin space, cut between two of its orthogonal sublayers:

```text
Z = (Q_a - Q_b) . C . (Q_b - Q_c),   C = Q_{b/r} D_r Q_{b/r}  self-adjoint. (63)
```

So the coupling never sees the dilation sum itself, only its Sonin compression `C`, and `Z = 0` says
`C` has no matrix element between `K_a ⊖ K_b` and `K_b ⊖ K_c` — a block-diagonality of `C` against
the aperture tower.  That block-diagonality is now *disproved*:
`exists_scale_soninCompressedDilation_layer_block_ne_zero` exhibits a scale at which the block is
nonzero, so the compressed dilation cannot be brought to block-diagonal form by the tower.

**`(61)` is now answered in Lean, in the negative.**
`exists_scale_soninApertureLayers_not_orthogonal` exhibits, at an actual dilation scale, layer
vectors `u` and `v` with `< (Q_a - Q_b) u , D_r (Q_b - Q_c) v >` nonzero.  So the dilation group
does not carry one Sonin layer into the orthogonal complement of the other, and the rigidity that
`(61)` would have required does not hold.

**Already answered on paper, at large scale.**  The sibling card
`cofinal-essential-phase-sonin-coupling-nonannihilation.md` proves unconditionally that for every
fixed strict flag `0 < a < q < b < c` there is a cofinal family of frequency-locked annular Meyer
wavepackets `w_r` with `|| Z_r w_r - U_{1/r} w_r || -> 0`, hence `|| Z_r || -> 1` and `Z_r != 0` for
all large `r`.  So `(61)` fails — the layers are *not* dilation-orthogonal — and the successive-layer
curvature is strictly negative, not merely nonpositive.  What remains here is only the Lean
certificate of that construction, which is being built on that card; do not re-attack `(61)` as if
it were open.

**A trap recorded, because it looks like a proof.**  The tower is *not* dilation covariant.  One is
tempted to write `U_r Q_s U_r^{-1} = Q_{s/r}` and then compute `(Q_a - Q_b)(Q_{b/r} - Q_{c/r}) = 0`
and `(Q_a - Q_b)(Q_{rb} - Q_{rc}) = 0` from nesting alone, concluding `Z = 0` outright.  The
covariance is false: dilation scales the physical constraint by `r` and the Fourier constraint by
`1/r`, so `U_r K_s` is the *asymmetric* Sonin space with physical aperture `s/r` and Fourier aperture
`rs`, and only the inclusion `U_r K_s subset K_{s/r}` survives.  `(62)` is the correct residue, and
it is an inclusion, not an identity of projections.

### Proof

Induction on the chain length from the three-point law, with the chamber hypothesis inherited
because the chain is increasing.  The bookkeeping is done on the residual traces alone, so no
principal-relative presentation appears; the logarithmic weights cancel as a coboundary along the
chain in any case.  `(32)` is `(31)` plus the curvature energy law at each refinement, and `(33)`
is nonnegativity of a sum of squared Hilbert--Schmidt norms.

## Theorem R: the aperture layer read by the extended trace

The layer–shell congruence `(51)` makes the aperture layer itself a principal-relative operator:
principal part the scale-one shell `S(a,b)`, remainder Schatten-1.  The extended trace therefore
reads the layer directly and

```text
tilde_tau(Q_a - Q_b) = (log b - log a) + Tr(Q_a - Q_b - S(a,b)).           (54)
```

Until now only the aperture *defect* had such a reading.  The layer is the more primitive object —
the defect is built from it — and `(54)` shows it carries the same principal cocycle `log(b/a)`,
independently of any prime scale.  The cocycle is thus a property of the aperture pair alone, not
of the source data it acts on.

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

## State of the completion gate

The last gate is `Burnol completion and completed lower floor`.  What is proved, and what it now
rests on:

**Proved (unconditional).**

1. The completed packet channel has a lower floor **iff** the excess of the coupling energy over the
   per-scale contribution is summable — `bddBelow_soninCompletedPacketValueVar_iff`.
2. Any completion with a floor must track the energy asymptotically
   (`tendsto_min_sub_hsNormSq_of_bddBelow`), diverge along the scales
   (`tendsto_atTop_of_bddBelow_soninCompletedPacketValueVar`), and blow up **on the source packets
   themselves** (`tendsto_norm_apply_soninClockPacket_atTop_of_bddBelow`).
3. The coupling energy diverges — `tendsto_hsNormSq_soninApertureCoupling_atTop`.
4. Excluded, therefore: every contribution bounded above
   (`not_bddBelow_soninCompletedPacketValueVar_of_bddAbove`), every prime-independent scalar
   including the corpus's Burnol counterterm `log(b/a)`
   (`..._burnolCounterterm`, `..._const`), every fixed bounded operator
   (`..._fixedChannel`), and the position-side conductor channel under **any** height schedule
   (`..._logShellChannelFamily`), because the packets' support is fixed and on a fixed annulus the
   channel is bounded independently of the height (`exists_bound_norm_evenLogShellChannel_of_annulus`).
5. The **frequency-side** channel blows up on the packets along an explicit carrier and height
   schedule (`exists_schedule_tendsto_norm_evenFourierLogShellChannel_atTop`), because the packets'
   frequency runs even though their support does not — but it is *also* excluded now
   (`not_bddBelow_soninCompletedPacketValueVar_fourierLogShellChannelFamily`), at every height
   schedule, because on the packets it grows only logarithmically in the scale.
6. Its size is capped: `norm_evenFourierLogShellChannel_apply_le` bounds the contribution by the
   largest layer logarithm, i.e. by `log` of the outer tower radius.
7. A shortfall of any fixed amount kills the floor —
   `not_bddBelow_soninCompletedPacketValueVar_of_shortfall`.

**The rate, now reduced to one one-variable estimate.**  Cut the aperture window `(b,c)` into `N`
sub-annuli, so each has half-width `delta = (c-b)/(2N)`, and carry them on the clock's frequency
`kappa = r q`.  Every band quantity of such a packet depends on the annulus only through `delta*t`
and `delta*kappa` (`norm_sq_evenFourierCutoff_soninScaledPacketEven_fraction`), and the band radii
that the two-branch estimate uses are the *fixed* apertures of the flag.  So all `N` band conditions
are the single condition `delta*kappa = (c-b) r q / (2N)` large — that is, `r` at least a constant
times `N`.  A threshold linear in `N` gives `N` of order `r` usable packets at scale `r`, hence
`hsNormSq Z_r` of order `r`, which beats the logarithmic cap of 6 decisively.  What is still needed
is the reference packet's spectral tail as a function of `delta*kappa` alone: a single one-variable
decay estimate, no longer one per annulus.

**The rescaled packet family, as built.**  Everything the `N`-packet argument reads is now expressed
through the fixed reference profile at the rescaled argument, with no annulus-dependent constant
left:

- profile, mean, packet, `L²` class, even-carrier membership, energy, both support cutoffs
  (`SoninScaledAnnulusProfile`, `SoninScaledProfileMass`, `SoninScaledPacket`,
  `SoninScaledPacketScaling`, `SoninScaledPacketL2`, `SoninScaledPacketSupport`);
- spectrum, density, band masses, the bridge to `fourierUnitary`, and the scale-free band fraction
  (`SoninScaledPacketFourier`, `SoninScaledPacketDensity`, `SoninScaledPacketFourierL2`,
  `SoninScaledPacketBandMass`);
- the lobe split, centre freedom, rapid decay of the reference, and the mean as a reference tail
  (`SoninOneSidedPacket`, `SoninLobeBumpFourier`, `SoninReferenceProfileDecay`,
  `SoninScaledBumpTail`, `SoninScaledMeanBound`);
- three real-line Fourier rules missing from mathlib — dilation, additivity, translation
  (`HTGeometry/FourierIntegralDilation`).

The packet's own spectral tail is now proved, and in the uniform form the band estimate needs:
`norm_fourier_soninScaledPacket_le_tailSup` bounds the packet's spectrum at *every* frequency in a
band of radius `t < w` by `2 delta` times the reference majorant at the gap `delta*(w - t)`, plus
the mean times the global majorant.  Both factors are governed by `tendsto_soninRefTailSup_atTop`
and `abs_soninScaledPacketMean_le`, so both are small once `delta*(w - t)` and `delta*w` are large.
Both sides of the comparison are now combined into a single uniform statement.  The band energy is at most `2t` times the square of
the uniform bound (`norm_sq_evenFourierCutoff_soninScaledPacketEven_le_uniform`), and the total
energy is at least `delta` times the reference square's mass, minus reference-square tails
(`norm_sq_soninScaledPacketEven_ge`).  Since the band bound carries a factor `delta^2` and the floor
carries `delta`, the captured *fraction* is at most a constant times `t * delta`, and
`exists_uniform_soninScaledPacket_band_escape` turns this into two annulus-free constants: whenever
`delta*|w| >= u0` and `t*delta <= rho`, the packet keeps more than half its energy outside the band.

This is the form the counting argument needs, and it is worth being precise about why.  With `N`
annuli of half-width `delta = (c-b)/(2N)` in the shell and carrier `w = r q`, the product
`delta*w = (c-b) q r / (2N)` is a *constant* if `N` grows like `r` — so the tails do not vanish and
the threshold `u0` is not met automatically.  The fix is to take `N` about `r/K` for a fixed large
`K`: then `delta*w` is about `K (c-b) q / 2`, which clears `u0` once `K` is large, while
`t*delta` (with `t = b` fixed) is about `2 b K / r`, which clears `rho` for large `r`.  The count is
still linear in `r`, so the energy still beats the logarithmic cap.

The other two error terms of the two-branch estimate are now accounted for, and the accounting
turned out not to need a rate at all.

Tracing `tendsto_norm_soninApertureCoupling_soninPacketEven_sub_subAnnulus`, the error is
`2||Corr_b w|| + ||L v - v|| + ||R_b w||`, and unfolding the middle term through
`tendsto_norm_evenSoninApertureLayer_soninDilatedPacket_sub` shows every contribution is one of
three kinds: (i) the *physical* shell on the dilated packet, which is **exactly zero** once
`r b >= b0` — a support condition, uniform over the annuli since every annulus starts at or above
`b`; (ii) *band* terms, for the packet and for its dilate, which the band-escape estimate covers;
(iii) *projection corrections*, which are elements of the principal-relative ideal.

For (iii) the corpus already proves the decisive fact: every ideal element is Schatten-1
(`IsSoninPrincipalRelativeIdeal.memSchattenClass_one`), hence Hilbert--Schmidt.  A Hilbert--Schmidt
operator has a *fixed finite* energy, so by mode counting it can exceed a threshold `ε` on at most
`hsNormSq/ε^2` members of any orthonormal family — a bound that does not grow with the family.  The
packets on disjoint annuli are orthogonal, so however many the schedule supplies, the corrections
spoil only boundedly many.  No rate for a compact operator is needed, and none is available.

The assembly itself is now proved in annulus-free form.  `card_sub_le_hsNormSq_of_ideal_errors`
takes exactly the shape of the two-branch estimate — a unit target, finitely many relative-ideal
errors, a fixed slack — and returns `(N - ∑ₖ hsNormSq Tₖ/ε²)(1 - η)²` as a lower bound on the
coupling's Hilbert--Schmidt energy.  Both discounts are constants: the first because each ideal
error has fixed finite energy, the second because `η` is chosen once from `ε` and the slack.  So the
bound is `N` minus a constant, times a constant.

One band in the budget is *not* covered by the crude escape threshold, and finding it forced a
sharper estimate.  Unfolding the layer defect on the dilated packet leaves the term `||R_{a0} v||`,
and since dilation conjugates a frequency cutoff into another one, this is the cutoff at radius
`r a0` applied to the packet itself.  Its product with the half-width is about `K a0 (c-b)/2` — a
*constant that grows with* `K`, so the hypothesis `t delta <= rho` of the escape theorem is exactly
backwards for it.  What saves the term is that its gap to the carrier, `delta r (q - a0)`, is about
`K (c-b)(q-a0)/2`, which grows with `K` too, and the tail decays faster than any power.
`norm_sq_evenFourierCutoff_le_fraction_mul_norm_sq` states the fraction rather than a threshold, so
this trade is expressible: the fraction is `16 t delta A^2 / I`, linear in the band and quadratic in
the tail at the gap.

The family itself is now built: `orthonormal_soninScaledPacketEven` takes any ordered index type,
half-widths, centres with pairwise gaps, and *arbitrary* carriers, and returns an orthonormal family
of normalized rescaled packets.  Only the supports enter the orthogonality, so the carriers need no
relation to each other — which matters, since the schedule gives all annuli the same carrier `r q`
and a proof that leaned on distinct carriers would not apply.

The cut is now built, and with it the supply side of the count is complete:
`orthonormal_soninShellCutPacket` produces `N` orthonormal packets at a single common carrier from
exactly two scalar conditions, both on the product `δ|w| = (c-b)|w|/(2N)`, and both met once that
product clears the thresholds of the two vanishing theorems.  Note the separation holds with
*equality* for consecutive pieces — the annuli abut — which the orthogonality tolerates because the
overlap is a single point.

The demand side now has its estimate.  `norm_soninApertureCoupling_sub_dilate_le` was extracted
from the interior of the corpus's limit proof, where it sat inline and entangled with the
fixed-profile packets; stated for an arbitrary vector with the two support properties, it applies
verbatim to the shell-cut packets, which is
`norm_soninApertureCoupling_soninShellCutPacket_sub_dilate_le`.  The estimate needs no smallness at
all — carrier, half-width and scale are free — because it is purely structural; smallness is only
needed later, to make the three errors small.

Matching the three errors to the survivor count needs one estimate the corpus did not have, and
tracing the layer defect through the dilation says exactly which.  Writing the layer as shell plus
correction difference, the defect on the dilate is `(A_b - A_a)v` — *exactly zero*, since the
inverse dilate is supported above both cutoffs once `r b` exceeds them — plus
`(R_b - R_a)v - v`, plus two projection corrections.  The corrections are ideal errors precomposed
with the dilation, which the ideal absorbs by right multiplication, so the survivor count takes
them.  The band part splits into `‖R_{a} v‖`, which is the cutoff at radius `r a` on the packet and
is covered by the band fraction, and `‖v - R_{b} v‖`, which is the packet's mass *above* radius
`r b` — above its carrier, not below.

That high-side tail is over an unbounded region, so a supremum bound cannot control it; it needs a
majorant integrable at infinity.  `exists_soninRefTailSup_le_div` supplies the majorant — at every
order `N`, the majorant outside radius `u` is at most `C_N / u^N` — and
`setIntegral_le_of_le_powerTail` now integrates it: any nonnegative function dominated by
`K|ξ|^{-p}` with `p > 1` has mass at most `2K t^{1-p}/(p-1)` outside the band of radius `t`.

Both halves of that step are now in place.  The discarded energy is identified as the density
integrated over the complement of the band, and above twice the carrier the density is at most
`16 δ² S(δ|ξ|/2)²`, since each of the three tail arguments then exceeds half the frequency.

That arithmetic is done, and with it **every error term of the aperture reduction is now bounded**.
The high-side tail — the last one, and the only one on an unbounded region — is at most
`2 K δ^{2-2N} t^{1-2N}/(2N-1)` at every order `N >= 1`.

The error budget therefore stands complete:

- the physical shell on the dilate: exactly zero, by support;
- the projection corrections: Schatten-1, so bounded spoilage of the mode count;
- the packet's own band content and `‖R_a v‖`: the band fraction;
- `‖v - R_b v‖`: the high-side power tail, above.

The budget is now a single theorem, `norm_soninApertureCoupling_sub_dilate_le_budget`, in the exact
shape the survivor count consumes: two relative-ideal errors applied to the vector itself, plus three
terms the spectral estimates bound.  The step that makes this possible is small but essential — the
correction difference naturally acts on the *dilate*, and the mode count can only see operators
applied to the family's own members, so it is rewritten as
`(Corr_a - Corr_b) * D` applied to the vector, which stays in the ideal because the ideal is closed
under right multiplication.

The general assembly is now one theorem.  `card_sub_le_hsNormSq_soninApertureCoupling` takes an
orthonormal family in the shell with band terms below `β` and returns
`(N - discount)(1 - eta)^2 <= hsNormSq Z`, with the discount the fixed energies of three ideal errors
over `eta^2`.  Two facts made it close: the coupling is *itself* a relative-ideal element, so it is
Hilbert--Schmidt and the mode count applies to it, and the dilates are unit vectors because dilation
is unitary, so they serve as the near-isometry targets with no further work.  The correction is
listed twice in a three-element family, which is how the budget's factor of two enters a sum of
equally weighted terms.

Instantiated at the cut, the bound now reads
`(N - discount)(1 - eta)^2 <= hsNormSq Z` with `N` the number of annuli — the only quantity on the
right that grows.  Everything subtracted from it is fixed once the schedule's constants are chosen.

The normalization step is now done in the form that makes it reusable: the three band terms are
values of *fixed operators* on the vector — the shell composed with the dilation, a band's complement
composed with the dilation, and a band — so writing them as one functional
`soninCouplingBandTotal` makes the whole budget divide by the packet norm at once, rather than term
by term.  `soninCouplingBandTotal_soninShellCutUnit_le` then trades a bound `P` on the packets'
totals and a lower bound `L` on their norms for the family bound `P/L`.

`L` is supplied: `sqrt(delta I / 2)`, from the energy floor by square roots.  The physical term is
also settled, and better than expected — it vanishes for *every* scale above one, with no condition
on the schedule at all, because the cut's annuli start at `b` and the inverse dilate is annihilated
by any physical cutoff below `r` times the inner radius.

The frequency-side transport was already in the corpus
(`norm_evenFourierCutoff_evenDilationCLM_inv` and its complement form in
`SoninFourierCutoffDilation`), so the dilate's two band terms are literally the packet's band content
at radius `r a` and the packet's spectral mass above radius `r b`.

`soninCouplingBandTotal_soninShellCutPacket_eq` now states `P` exactly: the band budget of a cut
packet is three band quantities *of the packet itself*, at radii `r b` (from above), `r a`, and `b`.
Nothing in it refers to the dilate or to the aperture layer any more.

The interface to those estimates is now built:
`soninCouplingBandTotal_soninShellCutPacket_le_of_sq_bounds` takes the three *squared* bounds and
returns the budget as the sum of their square roots, which is the right shape because the budget is a
sum of norms while every spectral estimate bounds a square.

The third of the three is now supplied in the cut's own terms.  Two hypotheses had to be discharged
and both came out of conditions already imposed: the mean below one follows from the *same* reference
tail condition that the orthonormality and the energy floor need, so it costs nothing new; and
`2 w <= r b` with `w = r q` reduces to `2 q <= b`, a condition on the carrier ratio alone, with the
scale cancelling.  So `q` must be chosen in `(a, b/2]`, not merely in `(a, b)` — which also forces
`a < b/2`, shrinking the inner aperture if necessary.  That is free, since `a` is ours to choose.

Both remaining bounds are now supplied, so `P` is complete:
`exists_soninCouplingBandTotal_soninShellCutPacket_le` gives every packet of a shell cut an explicit
band budget.  The whole estimate rests on exactly three conditions on the schedule — the carrier
ratio `q` in `(a, b/2]`, the scale large enough that `b < r q`, and the reference tail small at
`delta * r q`.

`P` and `L` are now joined: `card_sub_le_hsNormSq_soninApertureCoupling_shellCut_of_bounds` takes a
bound on the packets' band budgets, a floor for their norms, and returns
`(N - discount)(1 - eta)^2 <= hsNormSq Z` with slack `P/L`.  Every input to the energy bound is
therefore an explicit quantity of the schedule.

With the floor named, the energy bound takes the band budget as its only quantitative input and the
slack is `P / sqrt(delta I / 2)`.

The last step is arithmetic, and the orders repay a careful reading, because the three parts of `P`
do *not* all shrink for the same reason:

- the band term at `b` is `O(delta)`, so over the floor it is `O(sqrt(delta)) = O(1/sqrt(N))` — it
  vanishes as the cut refines;
- the band term at `r a` is `O(delta sqrt(r a))`, so over the floor it is `O(sqrt(delta r))`, and
  since `delta r` is about the schedule constant `K`, this does *not* vanish with `N` at all.  What
  kills it is the tail factor `S(delta r (q - a))`, of size `S(K(q-a))`, together with the polynomial
  rate: `sqrt(K) S(K(q-a)) = O(1/(sqrt(K)(q-a)))`.  So this term is controlled by `K`, not by `N`;
- the high-side term is *not* refinement-controlled, contrary to what the order count above
  suggested: writing the radicand exactly (`soninShellCutHighSlack_radicand_eq`) shows the
  half-width and the radius enter to the same negative order and therefore combine, giving
  `(delta t)^{1 - 2N_0}` up to a constant.  With `t = r b` the product is `delta r b`, about
  `kappa b`, a constant of the schedule.  So this term too is governed by `kappa` — large `kappa`
  or large order both shrink it — and refining the cut does nothing for it.

So the schedule must fix `K` first, large enough for the middle term, and only then let `N` grow.
That is the same conclusion the earlier `delta w` analysis reached, now visible in the estimate
itself.

`exists_card_sub_le_hsNormSq_soninApertureCoupling_shellCut` states the energy bound with every input
explicit: no `P`, no `L`, no family — only the shell `(a,b,c)`, the number of annuli `N`, the scale
`r`, the carrier ratio `q`, the decay order, the mode threshold and the shortfall.

Checking that bound against the schedule exposed a defect in the version that discards the mean, and
it matters.  Over the floor, a band term at radius `t` contributes about
`sqrt(delta t) (S(delta(w-t)) + S(0))`.  At `t = b` that is fine, since `delta -> 0` with `b` fixed.
At `t = r a` it is *not*: `delta * r a` is about `kappa a` with `kappa = delta r` the schedule
constant, so `sqrt(delta t)` does not shrink, and the term `S(0)` — the global majorant — is a
constant.  Discarding the mean therefore leaves a quantity bounded away from zero.

`norm_sq_evenFourierCutoff_soninShellCutPacket_le_sharp` repairs this by keeping the mean's own
estimate: the mean is a tail at the carrier, the carrier is further from the origin than the gap, so
by antitonicity the entire bound collapses to *one* tail at the gap times `(1 + 2 S(0)/J_0)`.  Then
the `r a` term is `sqrt(kappa a) S(kappa(q-a))`, which the polynomial decay rate drives to zero as
`kappa` grows.  This is the estimate the schedule needs; the mean-free one is retained but is only
adequate at fixed radii.

The budget and the energy bound are rebuilt on it:
`exists_card_sub_le_hsNormSq_soninApertureCoupling_shellCut_sharp` has the same shape as before but
with every band term carrying a tail at its own gap.  Now that no term is bounded below by a constant
of the reference profile, a schedule can be chosen.  Concretely the three slack terms are, in order
of what controls them: `sqrt(delta b) S(delta(rq - b))` — refinement; `sqrt(kappa a) S(kappa(q-a))` —
the schedule constant `kappa = delta r`, through the polynomial rate; and
`delta^{1-N_0}(rb)^{(1-2N_0)/2}` — refinement at every order.

All three are now *exact*, not asymptotic.  A band term of the slack is
`4 (1 + 2 S(0)/J_0) S(delta (w - t)) sqrt(t delta / I)`
(`sqrt_soninShellCutSharpBandBoundAt_div_floor`), so the two quantities that decide it — the tail at
the gap, and the product of band radius with half-width — are visible in the statement rather than
inferred from orders.  The high-side term is
`sqrt(4 K delta t^{1 - 2N_0} / (delta^{2N_0} (2N_0 - 1) I))`
(`sqrt_soninShellCutHighBoundAt_div_floor`), with the half-width cancelled once against the floor.

The slack condition `3 eps + (sum of the three) <= eta` is therefore an inequality between named
elementary expressions in the schedule, and choosing a schedule means choosing `kappa` and `N` to
satisfy it.

The one place analysis still enters is the middle term, which must be driven down by the schedule
constant rather than by refinement.  That is now settled in both halves.  The vanishing:
`tendsto_sqrt_mul_soninRefTailSup_atTop` says the majorant absorbs a root, since an extra order of
decay covers the weight, with `tendsto_pow_mul_soninRefTailSup_atTop` doing the same for any power.
And the identification: `sqrt_soninShellCutSharpBandBoundAt_div_floor_middle` shows the middle term
*is* that shape — pulling the half-width inside the root turns it into a constant of the shell times
`sqrt(kappa u) S(u)`, at the gap `u = delta r (q - a)`, with `kappa = a/((q-a) I)`.

So the middle term vanishes as the gap grows, and the gap grows with the schedule constant at every
scale.

The outer term is the complementary case and is now settled the same way.  At the fixed radius `b`
the majorant need not be small at all: after the half-width moves inside the root the term is
`S(delta(rq - b)) sqrt(delta b / I)`, and the root carries the whole decay, because
`tendsto_soninShellCutWidth_atTop` — the half-width of a cut into `N` equal annuli vanishes as `N`
grows.  Two terms, two mechanisms: one needs a large gap, the other a fine cut, and neither can
substitute for the other.  The high-side term joins the first group, not the second — see the
correction below.

All three slack terms now have both a closed form and a vanishing theorem, and they sort into two
groups by what drives them:

| term | closed form | driven by |
|---|---|---|
| band at `b` | `S(delta(rq-b)) sqrt(delta b / I)` times a constant | refinement, `N -> infinity` |
| band at `r a` | shell constant times `sqrt(kappa u) S(u)`, `u` the gap | the schedule constant |
| high side | `sqrt(C (delta t)^{1-2N_0})` | the schedule constant |

So the schedule is: fix the carrier ratio `q` in `(a, b/2]`, choose the constant `kappa = delta r`
large enough that the two `kappa`-driven terms fall below their share of `eta - 3 eps`, then let `N`
grow — which drives the third term and supplies the count.

That schedule is now realised exactly rather than approximately.  Taking `r = 2 N kappa/(c-b)` gives
`delta r = kappa` on the nose (`soninShellCutWidth_mul_scale`), so the gap is `kappa(q-a)` and the
high-side product is `kappa b`, both *constants in* `N`; the two `kappa`-driven slack terms are
therefore literally independent of the cut's size, and only the outer term still moves with `N`.
The scale grows linearly in `N`, so the coupling's own largeness conditions — scale above one,
carrier past the outer radius, `c <= r a` — all hold once the cut is fine enough.

Substituting it into the three closed forms makes the separation visible in the statements
themselves: the middle term is
`4 C sqrt(a kappa /I) sqrt(...) S(kappa(q-a))` and the high-side term
`sqrt(4K/((2N_0-1) I) (kappa b)^{1-2N_0})`, *neither mentioning* `N`, while the outer term keeps its
factor `sqrt(delta b / I)`, which vanishes with the cut.  The slack condition is therefore two fixed
numbers in `kappa` plus one quantity tending to zero in `N` — which is exactly a statement of the
form "choose `kappa`, then choose `N`".

The first choice is now made: `exists_kappa_slack_le` gives, for any positive target, a product
beyond which the two surviving terms sum below it.  Both vanish for their own reason — the middle by
the weighted majorant, the high-side by the negative exponent — and the statement is free of the cut,
so the `kappa` it produces can be fixed before any `N` is named.

The second choice is now available too.  `eventually_outerSlack_le` says the outer term is below any
positive target once the cut is fine enough, and the step that makes it independent of the carrier is
`outerSlack_le_global`: past the outer radius the majorant at the gap is below the *global* majorant,
so the carrier drops out of the bound entirely and only the vanishing root remains.

Both constants of the schedule are therefore choosable, in the right order and each by its own
mechanism.

The coupling's own hypotheses are now checked against the schedule as well, and they split the same
way.  The largeness conditions — scale above one, `b < r q`, `c <= r a`, and the cut nonempty — are
each a linearly growing quantity passing a fixed threshold, so all hold from some cut onwards
(`eventually_soninShellCutScale_conditions`).  The two tail conditions do *not* depend on the cut at
all: under the tied scale they are conditions on `kappa q` alone
(`soninShellCut_tail_conditions_of_product`), so they belong with the first choice, not the second.

Every hypothesis of the energy bound is therefore discharged by one of the two choices, and the
assembly is a matter of instantiating them.

The first choice is now made in one step: `exists_kappa_full` produces a single `kappa` satisfying
all four of its obligations at once — both tail conditions and both cut-independent slack terms.
All four improve as the product grows, so the four eventualities intersect, and the statement
mentions no cut.

The mirror statement is now proved as well: `exists_soninShellCut_second_choice` gives one `N`
satisfying the outer slack bound and the four largeness conditions together, *and* exceeding any
prescribed threshold.  That last clause is the one that matters for the conclusion — it is what makes
the count unbounded rather than merely positive.

Both choices are therefore available as clean existence statements, in the forced order.

`totalSlack_scale_eq` closes the algebra between them and the energy bound's hypothesis: the
hypothesis divides a *sum* of three roots by the floor, division distributes, and each quotient is
one of the three closed forms already computed.  So the hypothesis reads, literally, as
"first-choice quantity plus first-choice quantity plus second-choice quantity, below the threshold".

That instantiation is now done.  `exists_schedule_card_sub_le_hsNormSq_soninApertureCoupling` is the
capstone of the line: for every shortfall `eta` in `(0,1]` and every threshold `M` there are a
product `kappa` and a cut with `N >= M` annuli such that

  `(N - (sum of three ideal energies)/(eta/6)^2) (1 - eta)^2 <= hsNormSq Z`.

The shortfall is spent as `eps = eta/6` for the mode threshold and `eta/6` for each of the two
choices, leaving `5 eta/6 <= eta`.  That "everything subtracted from `N` is a constant" needed checking, because one of the three ideal
errors is a correction difference *precomposed with the dilation*, and the dilation moves with the
scale.  It is a constant: `hsNormSq_comp_evenDilationCLM` shows right composition by a dilation
preserves Hilbert--Schmidt energy — passing to adjoints turns it into left composition by the
inverse dilation, which is an isometry — so the discount is
`(2 hsNormSq(Corr_b) + hsNormSq(Corr_a - Corr_b))/(eta/6)^2`, depending on the aperture and the
shortfall but not on the schedule.

Since `M` is arbitrary and the discount is fixed, **the coupling's Hilbert--Schmidt energy is
unbounded along the schedule, with the count growing without limit**.  That conclusion is now a
theorem rather than a reading: `exists_hsNormSq_soninApertureCoupling_ge` fixes the shortfall at a
half, so the bound reads `(N - 144 Dis)/4` with `Dis` the aperture's own constant, and demands the
cut past `ceil(4B + 144 Dis)` — giving `B <= hsNormSq Z` for any prescribed `B`.

**Unboundedness by itself is not new.**  `tendsto_hsNormSq_soninApertureCoupling_atTop`, already in
the corpus, gives the coupling energy tending to infinity along any clock past the crossing
threshold; the statement above is weaker in form and adds nothing on its own.  What this line adds
is the *rate*.  `exists_linear_hsNormSq_soninApertureCoupling` states it: one product `kappa` serves
every threshold, the count is the fixed multiple `(c-b)/(2 kappa)` of the scale, and hence

  `hsNormSq Z_r >= (c-b)/(8 kappa) * r - 36 Dis`,

a positive slope in the scale rather than mere divergence.  That is the form a comparison with a
sublinear cap can use, and it is what the older argument — which picks a fresh annulus family for
each target and concludes only "eventually" — does not provide.

Reading the rate test (`not_bddBelow_soninCompletedPacketValueVar_of_shortfall`) showed what shape
the conclusion has to take: it wants a *sequence* of scales with a global `1 < p i` and
`c < p i * a`, and an eventual shortfall against the coupling energy.  So the schedule statement is
now the eventual one — one product, and *every* fine enough cut — rather than a threshold-indexed
existence.  Reindexing `p i := scale (N_0 + i)` past the point where the conditions hold then gives
the test its sequence, and `exists_scale_sequence_of_schedule` now does exactly that: one product,
one starting cut, and thereafter a scale for each index, each exceeding one and reaching the aperture
*strictly* — the strict form being what the test asks for, one notch stronger than the energy bound
itself needs.  Along the sequence the energy is at least `(Nstart + i)/4 - 36 Dis`.

The comparison itself is now available in general form:
`eventually_log_add_le_linear` says that for every positive slope `s` and all constants `C`, `δ`,
eventually `log x + δ <= s x - C`.  The proof is two steps — `log x <= 2 sqrt x`, since halving the
logarithm puts it under the square root's own bound `log y <= y - 1`; and a square root is eventually
under any positive multiple of the argument.

Applied along the sequence this closes the comparison.
`not_bddBelow_soninCompletedPacketValueVar_of_log_cap` states it: for *any* function `f` with
`f r <= log r` for `r > 1` — that is, any completion whose per-scale contribution obeys the
logarithmic cap — the schedule's own sequence of scales witnesses that the packet channel has no
floor.

The statement takes the cap as a hypothesis on an arbitrary `f` rather than naming a particular
completion, so it applies to every completion the cap covers, and it names no packet, cut or slack —
only the aperture, the cap and the conclusion.

**What this adds over the corpus, precisely.**  The log-shell channel itself was *already* closed, by
`not_bddBelow_soninCompletedPacketValueVar_logShellChannelFamily`, and by a cheaper route: the
packets sit inside the fixed outer radius, so the annulus bound caps that channel's contribution by a
*constant*, and constant-versus-unbounded needs no rate.  The linear rate is not needed there.  What
it buys is the class of completions whose contribution *grows*: `..._of_sublinear` closes every
completion with `f(r)/r -> 0`, growing or not, bounded or not.  Between "bounded above" and
"sublinear" lies everything the earlier qualitative argument could not touch.

Read the other way, this sharpens the open gate itself.  `not_sublinear_of_forall_bddBelow` says a
completion surviving at every schedule must have `f(r)/r` *not* tending to zero — it must grow at
least linearly in the scale along some sequence.  The remaining question is therefore no longer "is
there a completion?" but the much more specific "is there an *admissible* one growing at least
linearly?", and admissibility is where the corpus already has leverage: an ideal element, or any
uniformly bounded family, contributes `O(1)` on packets of bounded norm and so is excluded outright.

That exclusion is now formal on the schedule's own scales rather than borrowed from the crossing
clock: a bounded contribution divides by the scale to zero, so
`not_bddBelow_soninCompletedPacketValueVar_of_bounded` follows from the sublinear theorem, and
`re_inner_self_le_opNorm_mul_sq` supplies the bound for a uniformly bounded operator family — the
pairing is at most the operator norm times the squared packet norm.  That inequality had been proved
inline inside the log-shell closure; it is now a lemma.

One further step was needed to make that usable, and it is a matter of *shape* rather than strength.
A completion built from an operator family produces a contribution indexed by the schedule's steps,
not a function of the scale, so the failure had to be restated for a bare sequence:
`not_bddBelow_soninCompletedPacketValueVar_of_bddAbove_seq` closes every contribution sequence
bounded above, and uses only that the energy diverges — the linear rate is not needed for it.  The
packets' own size is bounded as it must be for the pairing bound to bite:
`norm_sq_soninScaledPacketEven_le` gives `‖psi‖^2 <= 8 delta I`, since with the mean below one the
packet is pointwise at most twice the profile.

With those in place the exclusion can be stated at the level of operators rather than numbers:
`not_bddBelow_soninCompletedPacketValueVar_of_bounded_family` closes every completion assembled from
a uniformly bounded family of operators paired against vectors of bounded norm.  That is the form in
which a candidate completion is actually presented, so it is the form worth citing.

The exclusion is not confined to the sublinear class, and the rate says by how much.  Half the
energy's own slope is a *threshold*: `exists_slope_not_bddBelow_soninCompletedPacketValueVar`
produces a single positive `s` and a single schedule that together defeat every completion whose
contribution stays below `s r` at large scales, whatever its growth.  The proof spends the energy in
two halves — one half absorbs the contribution, the other outruns the fixed constant `36 Dis` plus
the shortfall — so no comparison with `o(r)` is involved.  Sublinear completions are the special
case where the cap holds for every `s`.

Read as a necessary condition this is strictly sharper than `not_sublinear_of_forall_bddBelow`:
`frequently_slope_lt_of_forall_bddBelow` says a completion restoring the floor at every schedule must
satisfy `s r < f r` for arbitrarily large `r`, with `s` fixed in advance by the aperture — not merely
fail to be `o(r)`.  A completion is therefore pinned between two named quantities: it must beat a
definite slope infinitely often, and it must do so while remaining admissible, which the pairing
bound forbids for anything of bounded operator norm.

**The one live candidate, and what a tall tower can actually buy.**  Item 5 above leaves exactly one
channel unexcluded: the frequency-side one, which unlike the position-side channel does blow up on
the packets, because their frequency runs with the scale even though their support does not.  Its
freedom is the *height* schedule — a completion may take the tower as tall as it likes at each step —
and the crude bound `norm_evenFourierLogShellChannel_apply_le` grows with that height, since it takes
the largest layer logarithm below it.

That freedom is now shown to be illusory against a vector with a rapidly decaying spectrum, and the
argument is structural rather than analytic.  The exact energy identity is a sum over shells, so it
splits at any index: `norm_sq_evenLogShellChannel_apply_le_split` bounds the shells below the cut by
the largest layer logarithm there times the vector's own mass — the layers being orthogonal with
total mass at most `‖u‖^2`, which is `sum_norm_sq_evenIndicatorLayer_le` — and leaves the shells above
the cut as their own weighted sum.  Everything the height can add sits in that second sum.

The second sum is then bounded by a quantity independent of the height.  Three facts do it.  A shell
above a radius sees only what the vector leaves above that radius
(`norm_evenIndicatorLayer_apply_le_high`, from the shell's annihilation of the inner cutoff), so a
power decay of the mass outside a ball gives a power decay of every outer shell's mass.  A tower's
radii are geometric in the index, so `logShellRadius_pow` turns that power into a geometric sequence.
And a logarithm squared is below four times its argument (`sq_log_le_four_mul`, from `log t <= 2 sqrt
t`), so *one order of the decay pays for the entire logarithmic weight* — no comparison of growth
orders is needed, and the polynomial-times-geometric sum never has to be estimated.  What is left is
a bare geometric tail, and `sum_Ico_geom_le` closes it.

The conclusion is `norm_evenFourierLogShellChannel_apply_le_of_highTail`: for a vector whose spectral
mass outside every radius past the cut decays like an inverse power, the channel's norm is at most
`sqrt(M^2 ‖w‖^2 + 4 C a^{-p} (r^p)^{-K} (1 - (r^p)^{-1})^{-1})` — **with no reference to the tower's
height at all**, only to the cut index `K` and the bound `M` on the layer logarithms below it.
`re_inner_evenFourierLogShellChannel_le` states the number a completion built from it actually
contributes.

So a tall tower buys nothing: the contribution is the logarithm at the cut and no more.

The packet's own spectral tail is what makes that hypothesis true of the packets, and the corpus
already had it — `exists_norm_sq_sub_evenFourierCutoff_soninScaledPacketEven_le`, built for the
shell-cut budget's high side, says exactly that above twice the carrier the mass outside a ball is a
power tail at every order.  It needed only to be read with a natural exponent
(`..._le_div`, at order `2N-1`) and transported across the transform
(`norm_sub_evenIndicatorCutoff_evenFourierTransform`, since the physical cutoff's defect after the
transform is the frequency cutoff's defect before it).  So
`exists_norm_evenFourierLogShellChannel_soninScaledPacketEven_le` holds: on a rescaled packet with
the cut past twice the carrier, the channel is bounded with the height nowhere in the statement.

Written out, that bound's outer term carries the half-width to the power `-(2N-2)` and the cut radius
to the same power, so they combine — `soninChannelOuterTerm_eq` — and the whole term is a shell
constant over `(delta * cut radius)^(2N-2)`.  This is the third time this line has met the same
phenomenon, and it is worth naming: *every* quantity of a rescaled packet that looks like it depends
separately on the refinement and on the scale in fact depends on their product alone.  Here it means
the outer term is fixed under the tied scale, since `delta` times anything proportional to the
carrier is a fixed multiple of the schedule constant.

The choice of cut index is now made, and it is forced.  The tower's radii are geometric, so the least
index whose radius reaches a target overshoots by at most one factor of the ratio
(`exists_soninChannelCutIndex`); taking the cut there brackets the cut radius between twice the
carrier and `max(a0, 2 r0 w)`.  Both halves of the bound want exactly that bracket — the upper end
bounds the layer logarithms below the cut (`abs_log_logShellRadius_le_max`, since the radii increase
and the logarithm is monotone, so every interior logarithm lies between the base's and the cut's),
and the lower end bounds the half-width times the cut radius from below.

`exists_norm_evenFourierLogShellChannel_soninScaledPacketEven_le_carrier` is the result: the channel's
norm on a rescaled packet is at most

  `sqrt( max(|log a0|, |log max(a0, 2 r0 w)|)^2 ‖psi‖^2 + shell constant / (2 delta w)^(2N-2) )`,

with **no cut index and no tower height** — only the packet's carrier and half-width and the tower's
base and ratio.

**Item 5 is now closed.**  Two steps finish it.  First, the sublinear failure is restated in the form
the estimate actually produces: a *dominated* one.  Isolating the schedule's eventual shortfall
(`exists_schedule_eventually_sublinear_add_le_hsNormSq`) shows the argument never used equality with
the cap, only domination, so `..._of_sublinear_dominated` holds; and at the operator level
`..._of_sublinear_channel` closes every family whose *images* on vectors of bounded norm grow more
slowly than the scale.  That is strictly wider than the bounded-family exclusion — the operator norms
may grow without limit.

Second, the bound above is checked to be sublinear.  Along a schedule whose carriers stay proportional
to the scale and whose half-width times carrier stays bounded below, the constant term is genuinely
constant and the logarithmic term is `O(log scale)`: `tendsto_log_max_div_atTop` handles the maximum
with a fixed base, and `tendsto_sqrt_sq_mul_add_div_atTop` carries it through the square root, since
the root of a sum is below the sum of the roots.

`not_bddBelow_soninCompletedPacketValueVar_fourierLogShellChannelFamily` is the conclusion: **no
completion built from the frequency-side channel restores the floor, at any height schedule.**  The
hypotheses are exactly the three the schedule supplies — carriers proportional to the scale,
half-width times carrier bounded below, packet norms bounded — and the heights are arbitrary.

With that, every channel the corpus knows is excluded: prime-independent scalars, the Burnol
counterterm, any fixed bounded operator, any uniformly bounded family, the position-side conductor at
any height, and now the frequency-side conductor at any height.  Together with the threshold theorem,
a completion that could still work must grow at least a definite positive multiple of the scale
infinitely often — and none of the corpus's channels does.

**The requirement, stated in the ideal's own norm.**  The channel-by-channel exclusions leave open
what a working completion would have to look like, and the answer is now quantitative rather than
qualitative.  A Hilbert--Schmidt operator's image is bounded by its Hilbert--Schmidt norm
(`norm_apply_le_hsNorm_mul`), so on vectors of norm at most one the contribution is at most that norm.
Hence `not_bddBelow_soninCompletedPacketValueVar_of_sublinear_hsNorm`: a completion whose channels'
Hilbert--Schmidt energies grow more slowly than the scale fails, however they are built.

Sharpening that from sublinear to a definite slope gives the size requirement:
`frequently_slope_lt_hsNorm_of_bddBelow` says a completion restoring the floor must satisfy
`s * scale < hsNorm(channel)` at arbitrarily late steps, with `s` half the energy slope and fixed in
advance by the aperture.  Since every element of the principal-relative ideal is Schatten-1 and
therefore Hilbert--Schmidt (`IsSoninPrincipalRelativeIdeal.memSchattenClass_one`), this is exactly the
size an ideal-valued completion would have to reach.

The gate is therefore no longer a search for a construction but a statement about magnitudes: the
coupling's own energy is `hsNormSq Z_r >= slope * r`, so its Hilbert--Schmidt norm grows like the
square root of the scale, while a completion correcting it must have Hilbert--Schmidt norm growing
like the scale itself.  Whether the ideal contains such a sequence is what remains open; nothing
above rules it out, and nothing in the corpus exhibits one.

**The obvious way to build one does not work.**  Faced with a size requirement that grows, the natural
move is to let the channel move with the scale — carry one fixed conductor along the tower by the
dilation that takes one layer to the next.  That cannot help, and for a reason with no analysis in it:
dilation is an isometry, so the transported channel's image is no larger than the original's
(`norm_transported_apply_le` covers transport by any contractions on either side), and the
contribution stays bounded.  `..._of_dilation_transported` is the statement for the dilations
themselves.

So the growth the size requirement demands cannot come from *moving* a fixed operator; it has to come
from a genuinely unbounded sequence of distinct operators.  That narrows the open question further:
not "is there an admissible completion?" but "does the principal-relative ideal contain a sequence of
elements whose Hilbert--Schmidt norms grow at least linearly in the scale, and which cancels the
coupling on the packets?".

What remains on this line is the comparison against the logarithmic cap: the cap bounds the
completed contribution by `log` of the outer radius, while the schedule's scale grows linearly in
`N`, so the energy `N - const` outruns `log r` and the shortfall test applies.  With `N` about `r/K` this gives coupling
energy of order `r`, against the `log r` cap, closing the shortfall test.  Then feed that through the two-branch estimate to get `N` of
order `r` packets at scale `r`.

**Open.**  By 6 and 7 the gate is one rate comparison: does `hsNormSq Z_r` exceed
`log(outer radius)` by a fixed amount at all large scales?  The divergence in 3 carries no rate — it
gives `hsNormSq Z_r > N - 1` for each `N` eventually, each `N` with its own threshold.  A rate needs
an orthonormal family whose size grows with the scale and which the coupling does not contract.  The
shell-cell family cannot serve: its vectors are nonnegative indicators, so their spectrum sits at the
origin, exactly where the layer term forbids it.  The family must be modulated — packets on disjoint
sub-annuli — and the missing input is the quantitative dependence of a Meyer profile's spectral tail
on the width of its annulus.  First step taken: `soninScaledAnnulusBump` is a *rescaled fixed*
profile, with `soninScaledAnnulusBump_scaling` an exact identity, so its transform at half-width
`delta` is `delta` times the reference transform at `delta` times the frequency.  The corpus's
`soninAnnulusBump` cannot do this — its `ContDiffBump` radii depend on the annulus and mathlib's bump
family is abstract, so two widths have unrelated profiles.

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
- [x] proof that the aperture tower alone cannot supply the lower floor — now quantitative:
      `not_exists_lower_bound_soninAperturePacketCurvature_re_opTrace` in
      `SoninNoAperturePacketFloor.lean` shows the unit-weight source-packet curvature trace admits
      *no* lower bound at all.  Subadditivity alone left a floor possible; unboundedness does not.
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
| `(1)` the canonical logarithmic weight of a live window, and the zero/live state trace | `soninLiveWindowCyclicLogWeight`, `soninWindowStateCyclicLogTrace` |
| `(2)` state cyclicity (its floor/ceiling swap step `(5)` is internal to the proof) | `soninWindowStateCyclicLogTrace_compose_comm`, `soninWindowStateCyclicLogTrace_rotate_three` |
| `(6)` the extended trace of a principal-relative operator | `SoninPrincipalRelativeOperator.extendedTrace` |
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
| **G.1--G.2 as a characterization**: the presented operators, and the extended trace as the *unique* gluing of the two normalizations on them | `soninPrincipalRelativeCarrier`, `add_relative_mem_soninPrincipalRelativeCarrier`, `eq_extendedTrace_of_normalizations`, `eq_of_normalizations`, `soninExtendedTraceOn`, `soninExtendedTraceOn_state`, `soninExtendedTraceOn_add_relative`, `existsUnique_soninExtendedTraceOn` |
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
| `(38)` explicit carrier equation, in projections and dilations only | `evenSoninApertureRestrictionDefect_eq_compression`, `evenSoninApertureSuccessiveLayerTransition_eq_zero_iff_tripleProduct` |
| **`(38)` is false**: at an actual scale the triple product is nonzero, so the defect escapes the smaller carrier | `exists_scale_soninApertureTripleProduct_ne_zero`, `exists_scale_evenSoninApertureRestrictionDefect_mul_outer_ne` |
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
| `(54)` layer presentation | `soninApertureLayerPresentation` |
| `(54)` layer extended trace | `extendedTrace_soninApertureLayerPresentation` |
| `(55)` exact mixed-term form | `evenTwoPolarizationShell_mul_evenDilationSum_mul_shell_eq_mixed` |
| `(55)` coupling form | `evenSoninApertureSuccessiveLayerTransition_principalRelativeEq_mixed` |
| `(56)` time band nonzero | `fullTimeBandFourier_ne_zero` |
| `(56)` positive energy | `hsNormSq_fullTimeBandFourier_pos` |
| Fourier squares to reflection | `l2_fourier_fourier` |
| even uncertainty | `eq_zero_of_evenIndicatorCutoff_eq_self_of_evenFourierCutoff_eq_self` |
| band-limited shell vanishing | `eq_zero_of_evenFourierCutoff_eq_self_of_shell_apply_eq_zero` |
| annulus injectivity of `D_r` | `eq_zero_of_evenDilationSum_apply_eq_zero_of_fourierAnnulus` |
| Fourier annulus nonzero | `evenFourierCutoff_sub_ne_zero` |
| `(57)` polarization split | `soninMixedPhysicalBlock_add_soninMixedFourierBlock_eq_zero_iff` |
| `(58)` physical block nonzero | `soninMixedPhysicalBlock_ne_zero` |
| `(58)` Fourier block nonzero | `soninMixedFourierBlock_ne_zero` |
| `(58)` both halves | `soninMixedBlocks_ne_zero` |
| compact support vs Fourier shell | `eq_zero_of_evenIndicatorCutoff_eq_self_of_fourierShell_apply_eq_zero` |
| annulus injectivity, physical | `eq_zero_of_evenDilationSum_apply_eq_zero_of_physicalAnnulus` |
| physical annulus nonzero | `evenIndicatorCutoff_sub_ne_zero` |
| `(59)` blocks do not cancel | `soninApertureCouplingMixedTerms_ne_zero` |
| `(60)` ideal criterion (vacuous) | `evenSoninApertureSuccessiveLayerTransition_ne_zero_of_polarizedBlocks_notMem_ideal` |
| `(61)` orthogonality criterion | `evenSoninApertureSuccessiveLayerTransition_eq_zero_iff_layers_orthogonal` |
| strict flag law | `exists_strict_soninApertureResidualTrace_chain` |
| strict flag law with an explicit gap | `exists_soninApertureResidualTrace_chain_gap` |
| `(61)` on the projections | `evenSoninApertureSuccessiveLayerTransition_eq_zero_iff_projection_orthogonal` |
| `(61)` answered: the layers are **not** dilation-orthogonal | `exists_scale_soninApertureLayers_not_orthogonal` |
| `(62)` tower absorption | `evenCentralSoninProjection_mul_evenDilationSum_mul_evenCentralSoninProjection` |
| `(62)` on a whole layer | `evenCentralSoninProjection_mul_evenDilationSum_mul_evenSoninApertureLayer` |
| `(63)` compressed dilation | `evenSoninCompressedDilation` |
| `(63)` self-adjoint | `adjoint_evenSoninCompressedDilation` |
| `(63)` compression form | `evenSoninApertureSuccessiveLayerTransition_eq_compression` |
| `(63)` as a vanishing test | `evenSoninApertureSuccessiveLayerTransition_eq_zero_iff_compression_orthogonal` |
| `(63)` answered: the compressed dilation has a nonzero off-diagonal block | `exists_scale_soninCompressedDilation_layer_block_ne_zero` |
| worked instance at the flag `1 < 3/2 < 2 < 3`, so the hypothesis class is visibly inhabited | `soninApertureCoupling_ne_zero_instance`, `evenSoninApertureRestrictionDefect_ne_add_instance`, `not_exists_lower_bound_instance` |
| energy strictly monotone | `hsNormSq_fullTimeBandFourier_lt_of_lt` |
| **what a completion must do**: no counterterm bounded above on the packet family restores a floor, so a completion with a floor is unbounded above along it | `not_exists_lower_bound_soninAperturePacketCurvature_add_bounded`, `not_bddAbove_of_lower_bound_completion`, `exists_packet_le_completion_of_lower_bound` |
| **the threshold for an extensive completion**: per-scale form, floor when the contribution dominates the energies, no floor below `1/4`, and the `log(b/a)` counterterm failing on a short flag | `soninCompletedPacketValue`, `soninCompletedPacketValue_eq_sum`, `soninCompletedPacketValue_nonneg`, `not_exists_lower_bound_soninCompletedPacketValue`, `log_six_fifths_lt_quarter`, `not_exists_lower_bound_soninCompletedPacketValue_logCounterterm` |
| **the exact criterion for any completion**: finite sums are bounded below iff the negative part is summable, hence the floor exists iff the energy excess is summable, and a working completion tracks the energy | `bddBelow_finsetSum_iff_summable_min_zero`, `soninCompletedPacketValueVar`, `soninCompletedPacketValueVar_eq_sum`, `bddBelow_soninCompletedPacketValueVar_iff`, `tendsto_min_sub_hsNormSq_of_bddBelow` |
| Hilbert--Schmidt energy dominates a whole finite orthonormal family, hence its cardinality when the operator is nonexpanding-free on it | `sum_norm_sq_apply_le_hsNormSq`, `card_le_hsNormSq_of_norm_apply_eq_one` |
| growing coupling energy defeats every completion bounded above | `not_bddBelow_of_tendsto_hsNormSq_atTop` |
| the transition limit and the norm limit for a packet on **any sub-annulus** of the aperture window, flag and packet annulus now independent | `tendsto_norm_soninApertureCoupling_soninPacketEven_sub_subAnnulus`, `tendsto_norm_soninApertureCoupling_apply_soninPacketEven_subAnnulus` |
| packets on disjoint annuli are exactly orthogonal | `inner_soninPacketEven_eq_zero_of_disjoint` |
| **`N` disjoint annuli force coupling energy above `N - 1`**, the uniform subdivision that supplies them, and hence **the coupling energy tends to infinity** | `eventually_sub_one_le_hsNormSq_of_disjointAnnuli`, `soninUniformAnnulusFloor`, `exists_disjoint_annulus_family`, `tendsto_hsNormSq_soninApertureCoupling_atTop` |
| **no completion bounded above restores the floor**, at any strict flag | `not_bddBelow_soninCompletedPacketValueVar_of_bddAbove` |
| the packet's two lobes: profile and packet split as a lobe plus its reflection, the **reflection rule** `𝓕(f∘neg)(ξ) = 𝓕f(-ξ)`, the lobe's integrability, and hence the packet's transform and its magnitude in terms of one lobe at `±ξ` | `soninOneSidedBump`, `soninScaledAnnulusBump_eq_oneSided_add`, `soninOneSidedPacket`, `soninScaledPacket_eq_oneSided_add`, `fourier_comp_neg`, `integrable_soninOneSidedPacket`, `fourier_soninScaledPacket_eq_oneSided`, `norm_fourier_soninScaledPacket_le_oneSided` |
| **band energy at the operator level**: the Fourier cutoff's energy is the density over the band, scales by `δ` at radius `δt`, so the captured *fraction* is the same for every annulus | `norm_sq_evenFourierCutoff_soninScaledPacketEven`, `norm_sq_evenFourierCutoff_soninScaledPacketEven_eq_density`, `norm_sq_evenFourierCutoff_soninScaledPacketEven_scaling`, `norm_sq_evenFourierCutoff_soninScaledPacketEven_fraction` |
| the bridge to the carrier: the rescaled packet is integrable, its `L²` transform is the classical one, and the density computes that transform's modulus | `integrable_soninScaledPacket`, `fourierUnitary_soninScaledPacketL2_coeFn`, `soninScaledPacketSpectralDensity_eq_norm_sq` |
| the rescaled packet's spectral **density** and **band mass**: density scales by `δ²` at rescaled argument, band mass of radius `t` is `δ` times the reference band mass of radius `δt` | `soninScaledPacketSpectralDensity`, `soninScaledPacketSpectralDensity_scaling`, `indicator_soninScaledPacketSpectralDensity_scaling`, `integral_indicator_soninScaledPacketSpectralDensity_scaling` |
| the rescaled packet's **spectrum**: the transform is the reference transform at `δξ` scaled by `δ`, so a band of radius `t` for the family is a band of radius `δt` for the reference | `fourier_soninScaledPacket_scaling`, `norm_fourier_soninScaledPacket_scaling`, `norm_fourier_soninScaledPacket_of_abs_le` |
| **real-line Fourier rules absent from mathlib**: dilation, additivity, translation, homogeneity, modulation, and the **cosine modulation rule** `𝓕(f·cos(2πw₀·))(ξ) = ½𝓕f(ξ-w₀) + ½𝓕f(ξ+w₀)` | `GaloisForLFunctions.HTGeometry.fourierIntegral_comp_div`, `..._add`, `..._comp_add_right`, `..._const_mul`, `..._exp_mul`, `integrable_exp_mul`, `fourierIntegral_mul_cos` |
| **the packet mean is a reference tail**: the profile's mass is exactly `2δ` times the reference mass (centre free), so the half-width cancels and the mean is bounded by reference tails at `±δw` alone | `integrable_soninUnitBumpData`, `integral_soninUnitBumpData_pos`, `integral_soninOneSidedBump`, `integral_soninScaledAnnulusBump_eq`, `abs_soninScaledPacketMean_le` |
| the profile's spectrum and its **cosine mass** bounded by reference tails at `±δw` — the numerator of the packet mean | `integrable_soninOneSidedBump`, `fourier_soninScaledAnnulusBump_eq_oneSided`, `norm_fourier_soninScaledAnnulusBump_le`, `abs_integral_soninScaledAnnulusBump_mul_cos_le` |
| **the packet's spectral tail**: the packet is the profile times a cosine minus the profile times its mean, so its transform is two shifted profile transforms and a multiple of one — three reference tails | `soninScaledBumpTailBound`, `integrable_soninScaledAnnulusBumpC`, `norm_fourier_soninScaledPacket_le` |
| **a uniform tail majorant**: the supremum of the reference transform outside a symmetric band is finite (bounded by the profile's mass) and vanishes as the band grows (rapid decay in both directions) | `soninRefTailSup`, `norm_fourier_soninUnitBumpC_le`, `bddAbove_fourierTail`, `norm_fourier_soninUnitBumpC_le_tailSup`, `soninRefTailSup_nonneg`, `soninRefTailSup_le`, `tendsto_soninRefTailSup_atTop` |
| **uniform in-band bound**: below the carrier, every in-band frequency is separated from both shifted spectra by the gap, so the whole in-band spectrum is bounded by the majorant at the gap plus the mean times the global majorant | `soninScaledBumpTailBound_le`, `norm_fourier_soninScaledPacket_le_tailSup` |
| **band energy below the carrier**: the band energy is the density integrated over the band, and the uniform bound majorizes the density throughout, so the energy is at most the band's length times the squared bound | `integrable_soninScaledPacketSpectralDensity`, `centralBand_eq_Icc`, `measurableSet_centralBand`, `volume_centralBand_toReal`, `norm_sq_evenFourierCutoff_soninScaledPacketEven_le_uniform` |
| the tail supremum as **general infrastructure**, with the translated-dilate transform rule: any profile's tail majorant is finite (bounded by its mass), and vanishes as the band grows exactly when the profile is smooth with compact support | `GaloisForLFunctions.HTGeometry.fourierTailSup`, `..._nonneg`, `..._le`, `le_fourierTailSup`, `bddAbove_fourierTail`, `norm_fourierIntegral_le_mass`, `fourierIntegral_comp_div_sub`, `norm_fourierIntegral_comp_div_sub`, `tendsto_fourierTailSup_atTop` |
| **the squared profile**: below the annulus radius the lobes are disjoint, so the squared profile is two translated dilates of the reference square, whose mass is positive and centre free | `soninUnitBumpSq`, `soninUnitBumpSqC`, `contDiff_soninUnitBumpSqC`, `hasCompactSupport_soninUnitBumpSqC`, `integral_soninUnitBumpSq_pos`, `soninOneSidedBump_mul_neg_eq_zero`, `soninScaledAnnulusBump_sq`, `integral_soninOneSidedBump_sq`, `integral_soninScaledAnnulusBump_sq_eq` |
| **the squared profile's oscillation bound**: its cosine mass against frequency `w` is at most four half-widths times the reference-square majorant at `δ\|w\|` | `norm_fourier_soninOneSidedBump_sq`, `fourier_soninScaledAnnulusBump_sq_eq_oneSided`, `norm_fourier_soninScaledAnnulusBump_sq_le`, `soninRefSqTailSup`, `tendsto_soninRefSqTailSup_atTop`, `abs_integral_soninScaledAnnulusBump_sq_mul_cos_le`, `abs_integral_soninScaledAnnulusBump_sq_mul_cos_le_tailSup` |
| **the packet's energy floor**: squaring turns the carrier into a constant plus a doubled carrier, so the energy is half the squared profile's mass plus two oscillatory corrections and a nonnegative mean term — hence at least `δ` times a positive constant, minus reference-square tails | `norm_sq_soninScaledPacketEven_eq_expansion`, `norm_sq_soninScaledPacketEven_ge` |
| **uniform band escape**: two constants, naming no annulus, force every packet of the family to keep more than half its energy outside the band — the carrier far from the origin on the scale of the half-width, and the product of band radius and half-width small | `soninRefTailSup_le_mass`, `abs_soninScaledPacketMean_le_tailSup`, `exists_uniform_soninScaledPacket_band_escape` |
| **bounded spoilage**: a Hilbert--Schmidt operator exceeds a threshold `ε` on at most `hsNormSq/ε²` members of *any* finite orthonormal family, so all but boundedly many survive — and simultaneously for finitely many such operators | `card_filter_le_hsNormSq`, `card_le_card_filter_lt_add_hsNormSq` |
| the ideal errors of the aperture reduction are Schatten-1, hence Hilbert--Schmidt, hence spoil only boundedly many packets however many are supplied | `isHilbertSchmidt_of_isSoninPrincipalRelativeIdeal`, `isHilbertSchmidt_evenSoninProjectionCorrection`, `card_filter_le_hsNormSq_of_isSoninPrincipalRelativeIdeal`, `card_le_card_filter_lt_of_isSoninPrincipalRelativeIdeal`, `card_le_card_filter_forall_lt_of_isSoninPrincipalRelativeIdeal` |
| **energy from nearly preserved modes**: an operator carrying each of `N` orthonormal vectors to within `η` of *some* unit vector has energy at least `N (1-η)²`, with no relation required between the targets | `sum_finset_norm_sq_apply_le_hsNormSq`, `card_mul_sq_le_hsNormSq_of_le_norm_apply`, `card_mul_sq_le_hsNormSq_of_near_unit` |
| **survivor energy**: an operator estimated on an orthonormal family by a unit target up to finitely many relative-ideal errors and a fixed slack has energy at least `(N - ∑ₖ hsNormSq Tₖ/ε²)(1-η)²` — both discounts independent of `N` | `card_sub_le_hsNormSq_of_ideal_errors`, `card_sub_le_hsNormSq_of_one_ideal_error` |
| **the band fraction**, not merely a threshold: the share of a packet's energy inside a band of radius `t` below its carrier is at most `16 t δ A² / I`, with `A` the tail bound at the gap — so a *wide* band is harmless provided its gap to the carrier is large | `soninRefTailSup_antitone`, `norm_sq_soninScaledPacketEven_ge_half`, `norm_sq_evenFourierCutoff_le_fraction_mul_norm_sq` |
| **the orthonormal family**: separated annuli give packets vanishing on each other's supports, hence orthogonal for *arbitrary unrelated carriers*; the energy floor makes each nonzero, so normalizing gives an orthonormal family as large as the shell can be cut | `orthonormal_normalize`, `inner_soninScaledPacketEven_eq_zero_of_disjoint`, `soninScaledPacketEven_ne_zero`, `orthonormal_soninScaledPacketEven` |
| **the shell cut**: `[b,c]` divided into `N` equal abutting annuli — centres in arithmetic progression, common half-width `(c-b)/(2N)`, separation with equality, every annulus inside the shell, half-width below the inner radius; `N` orthonormal packets at one common carrier from two scalar conditions on `δ|w|` | `soninShellCutWidth`, `soninShellCutCentre`, `soninShellCut_sep`, `soninShellCut_le`, `soninShellCutWidth_lt_centre`, `abs_soninScaledPacketMean_le_one`, `orthonormal_soninShellCutPacket` |
| **distance to the dilate**, for *any* vector vanishing inside the inner aperture and fixed by the outer one: twice the projection correction, the layer defect on the dilate, and the vector's own band content — and every shell-cut packet satisfies the two support facts | `norm_soninApertureCoupling_sub_dilate_le`, `norm_soninApertureCoupling_soninShellCutPacket_sub_dilate_le` |
| **an explicit decay rate at every order** for both majorants: the Schwartz seminorms give one constant bounding `\|v\|^N ‖𝓕 f v‖` at *every* frequency, so the majorant outside radius `u` is at most `C_N / u^N` | `exists_pow_mul_norm_fourierIntegral_le`, `norm_fourierIntegral_le_div_of_pow_bound`, `exists_pow_mul_norm_fourier_soninUnitBumpC_le`, `exists_pow_mul_norm_fourier_soninUnitBumpSqC_le`, `exists_soninRefTailSup_le_div`, `exists_soninRefSqTailSup_le_div` |
| **mass outside a band**: a power tail `K\|ξ\|^{-p}` with `p > 1` integrates over the outside of a symmetric band to `2K t^{1-p}/(p-1)`, so any nonnegative function it dominates has that much mass at most — the estimate a supremum bound cannot give on an unbounded region | `centralTail_eq_union`, `integrableOn_powerTail_Ioi`, `integrableOn_powerTail_Iic`, `integrableOn_powerTail`, `integral_powerTail_Ioi`, `integral_powerTail`, `setIntegral_le_of_le_powerTail` |
| **the discarded energy** is the density integrated over the band's *complement*, and above twice the carrier that density is at most `16 δ² S(δ\|ξ\|/2)²` — all three tail arguments then exceed half the frequency | `measurableSet_strictCentralTail`, `norm_sq_sub_evenFourierCutoff_soninScaledPacketEven_eq_density`, `soninScaledPacketSpectralDensity_le_tailSup` |
| **the energy above a band**: substituting the polynomial rate turns that density into a genuine power tail of order `2N`, integrable at every positive order, so the packet keeps at most `2K δ^{2-2N} t^{1-2N}/(2N-1)` above a band at twice its carrier | `exists_soninScaledPacketSpectralDensity_le_powerTail`, `exists_norm_sq_sub_evenFourierCutoff_soninScaledPacketEven_le` |
| **the full error budget in five named terms**, with the correction difference written as an ideal operator applied to the vector itself — the ideal absorbs the dilation by right multiplication, which is what lets the mode count see it | `norm_evenSoninApertureLayer_sub_le`, `isSoninPrincipalRelativeIdeal_correctionDiff_comp_dilation`, `norm_soninApertureCoupling_sub_dilate_le_budget` |
| **coupling energy from a shell family**: an orthonormal family vanishing inside the inner aperture and fixed by the outer one, with band terms below `β`, forces `hsNormSq Z >= (N - discount)(1-η)²` — the coupling is itself an ideal element, hence Hilbert--Schmidt, and its dilates are unit vectors | `soninCouplingIdealErrors`, `isSoninPrincipalRelativeIdeal_soninCouplingIdealErrors`, `card_sub_le_hsNormSq_soninApertureCoupling` |
| **the same with the cut's packets**: normalizing changes nothing the estimate sees, since the cutoffs are linear, so the bound reads with the number of annuli `N` in place of the family's cardinality | `soninShellCutUnit`, `orthonormal_soninShellCutUnit`, `evenIndicatorCutoff_soninShellCutUnit_eq_zero`, `evenIndicatorCutoff_soninShellCutUnit_eq_self`, `card_sub_le_hsNormSq_soninApertureCoupling_shellCut` |
| **the band budget under normalization**: the three band terms are values of *fixed operators* — shell∘dilation, band-complement∘dilation, band — so each divides by the packet norm, hence so does their total; a bound on the packets' totals over a lower bound for their norms bounds the family's | `norm_apply_normalize`, `soninCouplingBandTotal`, `soninCouplingBandTotal_eq`, `soninCouplingBandTotal_normalize`, `soninCouplingBandTotal_soninShellCutUnit_le` |
| **the dilate adds nothing new**: its physical term vanishes outright for a cut packet (both aperture radii sit below `r` times the annulus's inner radius), and the packet's norm floor comes from the energy floor by square roots | `evenIndicatorCutoff_evenDilationCLM_inv_soninScaledPacketEven_eq_zero`, `evenIndicatorCutoff_sub_evenDilationCLM_inv_soninShellCutUnit_eq_zero`, `sqrt_le_norm_soninShellCutPacket` |
| **the band budget in three radii of one vector**: mass above `r b`, content in the band of radius `r a`, content in the band of radius `b` — the physical term discarded, the dilate's terms transported back | `soninCouplingBandTotal_eq_packetTerms`, `evenIndicatorCutoff_sub_evenDilationCLM_inv_soninShellCutPacket_eq_zero`, `soninCouplingBandTotal_soninShellCutPacket_eq` |
| **squared estimates enter through their roots**: the budget is a sum of norms while the spectral estimates bound squares, so three squared bounds give the budget as the sum of their square roots — for the cut packets the physical term is supplied by the geometry | `norm_le_sqrt_of_sq_le`, `soninCouplingBandTotal_le_of_sq_bounds`, `soninCouplingBandTotal_soninShellCutPacket_le_of_sq_bounds` |
| **the third squared bound, in the cut's own terms**: the mean hypothesis discharged by the same tail condition the orthonormality and the floor already need, and the carrier ratio `q <= b/2` putting the band at `r b` above twice the carrier | `exists_norm_sq_sub_evenFourierCutoff_le_of_tail`, `exists_norm_sq_sub_evenFourierCutoff_soninShellCutPacket_le` |
| **`P` complete**: all three squared bounds supplied and fed through the roots, so every packet of a shell cut has an explicit band budget under three schedule conditions — carrier ratio in `(a, b/2]`, scale large enough that `b < r q`, reference tail small at `δ·rq` | `norm_sq_evenFourierCutoff_soninShellCutPacket_le`, `exists_soninCouplingBandTotal_soninShellCutPacket_le` |
| **energy from `P` and `L`**: a bound on the packets' band budgets and a floor for their norms supply the family hypothesis with slack `P/L`, giving `(N - discount)(1-η)² <= hsNormSq Z` | `card_sub_le_hsNormSq_soninApertureCoupling_shellCut_of_bounds` |
| **the floor named**: `L = sqrt(δ I / 2)` is the cut's own quantity, so the energy bound needs only the band budget as input, with slack `P / sqrt(δ I / 2)` | `soninShellCutNormFloor`, `soninShellCutNormFloor_pos`, `card_sub_le_hsNormSq_soninApertureCoupling_shellCut_of_bandBound` |
| **the band bound freed of the annulus** (mean replaced by one, legitimate under the same tail condition), and with it the band budget of *every* packet of a cut below one expression | `soninShellCutBandBoundAt`, `soninShellCutHighBoundAt`, `norm_sq_evenFourierCutoff_soninShellCutPacket_le_uniform`, `exists_soninCouplingBandTotal_soninShellCutPacket_le_uniform` |
| **the energy bound with every input explicit**: only the schedule enters — shell, number of annuli, scale, carrier ratio, decay order, threshold, shortfall | `exists_card_sub_le_hsNormSq_soninApertureCoupling_shellCut` |
| **the band bound with the mean kept**, which the growing band needs: the mean is itself a tail at the carrier, and the carrier is further out than the gap, so the whole bound is *one* tail at the gap times a profile constant | `soninShellCutSharpBandBoundAt`, `norm_sq_evenFourierCutoff_soninShellCutPacket_le_sharp` |
| **the budget and the energy bound rebuilt on the sharp estimate**: same shape, different content — every band term now carries a tail at its own gap, so no term is bounded below by a profile constant | `exists_soninCouplingBandTotal_soninShellCutPacket_le_sharp`, `exists_card_sub_le_hsNormSq_soninApertureCoupling_shellCut_sharp` |
| **the band slack in closed form**: root of band over root of floor collapses to `2 X sqrt(t/(δ I))`, so a band term of the slack is the tail at its gap times the root of `t δ / I` — the two quantities that decide it, named | `sqrt_band_div_sqrt_floor`, `sqrt_soninShellCutSharpBandBoundAt_div_floor` |
| **the high-side slack in closed form**: one root, the half-width cancelled once against the floor — `sqrt(4 K δ t^{1-2N_0} / (δ^{2N_0} (2N_0 - 1) I))` | `soninShellCutHighBoundAt_nonneg`, `sqrt_soninShellCutHighBoundAt_div_floor` |
| **the majorant beats every weight**: one extra order of decay absorbs a power or a root, so `u^n S(u) -> 0` and `sqrt(u) S(u) -> 0` — the vanishing the middle slack term needs | `tendsto_pow_mul_soninRefTailSup_atTop`, `tendsto_sqrt_mul_soninRefTailSup_atTop` |
| **the middle slack term identified**: pulling the half-width inside the root makes it a shell constant times `sqrt(kappa u) S(u)` at the gap `u = δ r (q - a)` — exactly the shape the weighted vanishing covers | `mul_sqrt_div_eq_sqrt_mul_div`, `tendsto_sqrt_const_mul_soninRefTailSup_atTop`, `sqrt_soninShellCutSharpBandBoundAt_div_floor_middle` |
| **the outer slack term and the refining cut**: at the fixed radius `b` the root carries the whole decay, and the half-width of a cut into `N` annuli vanishes as `N` grows | `tendsto_soninShellCutWidth_atTop`, `sqrt_soninShellCutSharpBandBoundAt_div_floor_outer`, `tendsto_sqrt_soninShellCutWidth_mul_atTop` |
| **the high-side slack depends on one product only**: half-width and radius enter to the same negative order, so the radicand is a constant times `(δ t)^{1-2N_0}` — governed by the product, hence by the schedule constant, not by refinement | `soninShellCutHighSlack_radicand_eq`, `sqrt_soninShellCutHighBoundAt_div_floor_product` |
| **the high-side slack vanishes** in that product, the exponent being negative from the first order on — completing a vanishing theorem for each of the three terms | `tendsto_rpow_one_sub_two_mul_atTop`, `tendsto_sqrt_const_mul_rpow_atTop` |
| **the scale that fixes the product**: tying `r` to `N` by `r = 2 N kappa/(c-b)` makes `δ r = kappa` *exactly*, so the gap is `kappa(q-a)` and the high-side product is `kappa b`, both constant in `N`; and the scale grows linearly with `N` | `soninShellCutScale`, `soninShellCutWidth_mul_scale`, `soninShellCutScale_pos`, `tendsto_soninShellCutScale_atTop`, `soninShellCutWidth_mul_gap`, `soninShellCutWidth_mul_outer` |
| **the three slack terms under that scale**: the middle and high-side ones become expressions in `kappa` alone, with `N` absent from the statement; the outer one keeps its vanishing root | `sqrt_soninShellCutSharpBandBoundAt_div_floor_middle_scale`, `sqrt_soninShellCutHighBoundAt_div_floor_scale`, `sqrt_soninShellCutSharpBandBoundAt_div_floor_outer_scale` |
| **the first constant is choosable**: both surviving terms vanish as the prescribed product grows, so beyond some product their weighted sum is below any target — fixed independently of the cut | `tendsto_middleSlackConst_atTop`, `tendsto_highSlackConst_atTop`, `exists_kappa_slack_le` |
| **the second constant is choosable**: past the outer radius the carrier drops out of the outer term's bound (majorant below the global one), leaving a fixed multiple of a root that vanishes with the cut | `soninRefTailSup_le_global`, `outerSlack_le_global`, `eventually_outerSlack_le` |
| **the coupling's largeness conditions are eventual in the cut**, and its two tail conditions are conditions on the prescribed product alone — the tied scale holds that product fixed | `eventually_soninShellCutScale_conditions`, `soninShellCut_tail_conditions_of_product` |
| **one product serves all four first-choice obligations**: the two tail conditions and the two cut-independent slack terms all improve with the product, so a single `kappa` satisfies them together | `exists_kappa_full` |
| **one cut serves all five second-choice obligations**, and can be taken as fine as desired — which is what supplies the count | `eventually_soninShellCut_second_choice`, `exists_soninShellCut_second_choice` |
| **the total slack is the sum of the three quotients**, two in the prescribed product and one in the cut — no algebra left between the hypothesis and the two choices | `sum_div_three`, `totalSlack_scale_eq` |
| **a schedule exists at every size**: for any shortfall and any threshold there are a product and a cut past that threshold realising the energy bound — `(N - discount)(1-η)² <= hsNormSq Z` with `N` unbounded | `exists_schedule_card_sub_le_hsNormSq_soninApertureCoupling` |
| **the discount is scale free**: right composition by a dilation preserves Hilbert--Schmidt energy (adjoints turn it into left composition by the inverse), so the three ideal errors sum to `2 hsNormSq(Corr_b) + hsNormSq(Corr_a - Corr_b)`, a constant of the aperture | `hsNormSq_comp_evenDilationCLM`, `hsNormSq_soninCouplingIdealErrors_two`, `sum_hsNormSq_soninCouplingIdealErrors` |
| **the coupling's energy exceeds every level**: at a fixed aperture window and carrier ratio, some schedule drives `hsNormSq Z` past any prescribed bound | `exists_hsNormSq_soninApertureCoupling_ge` |
| **the energy is linear in the scale**: one product serves every threshold, and the count is a fixed multiple of the scale, so `hsNormSq Z >= (c-b)/(8 kappa) * r - 36 Dis` — a positive slope, not merely divergence | `soninShellCutScale_mul_slope`, `exists_linear_hsNormSq_soninApertureCoupling` |
| the schedule statement strengthened to the **eventual** form — one product, and *every* fine enough cut works — which is the shape the rate test consumes | `exists_schedule_card_sub_le_hsNormSq_soninApertureCoupling` (restated) |
| **the schedule as a sequence**: shifting the index past the point where the conditions start holding gives scales `p i` with uniform admissibility (`1 < p i`, `c < p i a`) and energy growing with `i` — the rate test's input shape | `eventually_soninShellCutScale_gt`, `exists_scale_sequence_of_schedule` |
| **a logarithm falls short of every positive slope**: `log x <= 2 sqrt x` (halving puts it under the root's own bound), and a root is eventually under any positive multiple — so `log x + δ <= s x - C` eventually, for every `s > 0` | `log_le_two_mul_sqrt`, `eventually_log_add_le_linear` |
| **no logarithmically capped completion restores the floor**: along the schedule's scales the capped contribution trails the coupling energy by a fixed amount, which is the rate test's hypothesis | `not_bddBelow_soninCompletedPacketValueVar_of_log_cap` |
| **no *sublinear* completion restores the floor** — the widest class the linear rate reaches: the contribution may grow, and grow without bound, provided it grows more slowly than the scale | `eventually_sublinear_add_le_linear`, `not_bddBelow_soninCompletedPacketValueVar_of_sublinear` |
| **what a completion would have to do**: one that restores the floor at every schedule cannot have its contribution divide by the scale to zero — it must grow at least linearly along some sequence of scales | `not_sublinear_of_forall_bddBelow` |
| **the bounded case sits inside the sublinear one** on the schedule's scales, and a uniformly bounded operator family contributes at most `‖C‖` times the squared packet norm | `tendsto_div_atTop_nhds_zero_of_bounded`, `re_inner_self_le_opNorm_mul_sq`, `not_bddBelow_soninCompletedPacketValueVar_of_bounded` |
| **the failure for a bounded contribution *sequence*** — the form an operator family supplies — using only divergence of the energy; with the packets' own size bounded, `‖ψ‖² <= 8 δ I` | `integrable_soninScaledPacket_sq`, `norm_sq_soninScaledPacketEven_le`, `not_bddBelow_soninCompletedPacketValueVar_of_bddAbove_seq` |
| **no completion from a uniformly bounded operator family restores the floor** — the operator-level form of the exclusion | `re_inner_family_le`, `not_bddBelow_soninCompletedPacketValueVar_of_bounded_family` |
| **a definite positive slope below which every completion fails**, and the sharpened necessary condition: a surviving completion must exceed that slope infinitely often | `exists_slope_not_bddBelow_soninCompletedPacketValueVar`, `frequently_slope_lt_of_forall_bddBelow` |
| **the step multiplier splits at any shell index**: Bessel below the cut, the outer shells' own weighted mass above it | `sum_norm_sq_evenIndicatorLayer_le`, `sum_range_logShellRadius_weight_le`, `norm_sq_evenLogShellChannel_apply_le_split`, `norm_evenLogShellChannel_apply_le_of_tail`, `norm_evenFourierLogShellChannel_apply_le_of_tail` |
| **a logarithmic weight against a geometric tail**: partial geometric sums, and `(log t)^2 <= 4t` | `geom_sum_range_le`, `sum_Ico_geom_le`, `sq_log_le_four_mul`, `sq_abs_log_le_four_mul` |
| **the outer shells against a power tail** — a shell sees only the mass above its inner radius, and the weighted outer sum is one geometric term | `norm_evenIndicatorLayer_apply_le_high`, `logShellRadius_pow`, `sum_Ico_logShellRadius_weight_le` |
| **the channel on a vector with a power tail is bounded uniformly in the tower height**, in position and in frequency, with the pairing bound it supplies | `norm_evenLogShellChannel_apply_le_of_powerTail`, `norm_sq_evenIndicatorLayer_le_of_highTail`, `norm_evenLogShellChannel_apply_le_of_highTail`, `norm_evenFourierLogShellChannel_apply_le_of_highTail`, `re_inner_evenFourierLogShellChannel_le` |
| **the rescaled packet meets that hypothesis**, so the frequency-side channel on a packet is bounded uniformly in the tower height | `norm_sub_evenIndicatorCutoff_evenFourierTransform`, `exists_norm_sq_sub_evenFourierCutoff_soninScaledPacketEven_le_div`, `exists_norm_evenFourierLogShellChannel_soninScaledPacketEven_le` |
| **the outer term is a shell constant over `(delta * cut radius)^(2N-2)`** — half-width and radius enter to the same negative order and combine | `soninChannelOuterTerm_eq`, `exists_norm_evenFourierLogShellChannel_soninScaledPacketEven_le_combined` |
| **the cut index chosen at the carrier**, giving the channel bound in the packet's own data — no cut index, no tower height | `exists_soninChannelCutIndex`, `abs_log_logShellRadius_le_max`, `exists_norm_evenFourierLogShellChannel_soninScaledPacketEven_le_carrier` |
| **a channel family of sublinear size is excluded** — the dominated form of the sublinear failure, and its operator-level reading | `exists_schedule_eventually_sublinear_add_le_hsNormSq`, `not_bddBelow_soninCompletedPacketValueVar_of_sublinear_dominated`, `not_bddBelow_soninCompletedPacketValueVar_of_sublinear_channel` |
| **logarithms of a growing maximum are sublinear**, and stay so through a square root against a fixed quadratic | `tendsto_log_div_atTop`, `tendsto_log_max_div_atTop`, `tendsto_max_abs_log_div_atTop`, `tendsto_sqrt_sq_mul_add_div_atTop` |
| **the frequency-side channel is closed as a completion**, at every height schedule | `not_bddBelow_soninCompletedPacketValueVar_fourierLogShellChannelFamily` |
| **how large a completion's channels must be**: sublinear Hilbert--Schmidt energies fail, and a surviving completion's Hilbert--Schmidt norm exceeds a definite multiple of the scale infinitely often | `norm_apply_le_hsNorm_mul`, `not_bddBelow_soninCompletedPacketValueVar_of_sublinear_hsNorm`, `exists_slope_schedule_eventually_add_le_hsNormSq`, `not_bddBelow_soninCompletedPacketValueVar_of_slope_hsNorm`, `frequently_slope_lt_hsNorm_of_bddBelow` |
| **transporting a fixed channel along the tower buys nothing** — by any contractions, in particular by the dilations | `norm_transported_apply_le`, `not_bddBelow_soninCompletedPacketValueVar_of_transported_channel`, `not_bddBelow_soninCompletedPacketValueVar_of_dilation_transported` |
| **rapid decay of the reference profile**, and hence of every lobe in the rescaled variable `δξ` | `contDiff_soninUnitBumpC`, `hasCompactSupport_soninUnitBumpC`, `tendsto_pow_mul_norm_fourier_soninUnitBumpC_atTop`, `tendsto_pow_mul_norm_fourier_soninOneSidedBump` |
| **the lobe profile's transform is centre free**: a phase times `δ` times the reference transform at `δξ`, so its magnitude is `δ‖𝓕φ_ref(δξ)‖` | `soninUnitBumpC`, `soninOneSidedBump_eq_comp`, `fourier_soninOneSidedBump`, `norm_fourier_soninOneSidedBump` |
| the two hypotheses the two-branch estimate consumes, for the rescaled family: a cutoff at or below `m-δ` annihilates it, one at or above `m+δ` fixes it | `soninScaledPacket_eq_zero_of_abs_le`, `soninScaledPacket_eq_zero_of_le_abs`, `evenIndicatorCutoff_soninScaledPacketEven_eq_zero`, `evenIndicatorCutoff_soninScaledPacketEven_eq_self` |
| the rescaled packet as a vector of the even Sonin carrier, with its squared norm and the energy scaling | `memLp_soninScaledPacket`, `soninScaledPacketL2`, `soninScaledPacketL2_mem_evenSubspace`, `soninScaledPacketEven`, `norm_sq_soninScaledPacketEven`, `norm_sq_soninScaledPacketEven_scaling` |
| **the packet is a rescaling**: profile and mean both scale, so the packet at half-width `δ` and frequency `κ` is the reference packet at `δκ` precomposed with the dilation; hence evenness, support, continuity, compact support, and energy scaling | `soninScaledPacket_scaling`, `soninScaledPacket_even`, `soninScaledPacket_support_subset`, `continuous_soninScaledPacket`, `hasCompactSupport_soninScaledPacket`, `integral_soninScaledPacket_sq_scaling` |
| the modulated packet on the rescaled profile: cosine-weighted mass scaling, the mean depending **only on the product of width and frequency**, and the second Meyer condition | `integrable_soninScaledAnnulusBump_mul_cos`, `integral_soninScaledAnnulusBump_mul_cos_scaling`, `soninScaledPacketMean`, `soninScaledPacketMean_scaling`, `soninScaledPacket`, `integral_soninScaledPacket` |
| the rescaled profile's mass: compact support, integrability, mass **exactly proportional to the half-width**, and positivity | `hasCompactSupport_soninScaledAnnulusBump`, `integrable_soninScaledAnnulusBump`, `integral_soninScaledAnnulusBump_scaling`, `integral_soninScaledAnnulusBump_pos` |
| an annulus profile that is **one fixed profile rescaled**, with the exact scaling law, support, evenness, smoothness and a lower bound at the centre | `soninUnitBumpData`, `soninScaledAnnulusBump`, `soninScaledAnnulusBump_scaling`, `soninScaledAnnulusBump_support_subset`, `one_le_soninScaledAnnulusBump_center`, `contDiff_soninScaledAnnulusBump` |
| the shell cells' geometry: exact width `(b-a)/((n+2)(n+3))`, shrinking like `1/n²`, accumulating at the inner radius | `shellRight_sub_shellLeft`, `shellRight_sub_shellLeft_le`, `tendsto_shellLeft_atTop` |
| the dilated shell mode's support, **exactly**: apertures below the dilated inner radius annihilate it, apertures above the dilated outer radius fix it, and its norm is unchanged | `evenIndicatorCutoff_evenDilationCLM_inv_evenShellVectorEven_eq_zero`, `evenIndicatorCutoff_evenDilationCLM_inv_evenShellVectorEven_eq_self`, `norm_evenDilationCLM_inv_evenShellVectorEven` |
| **band escape for shell modes**: a high mode's mass inside any fixed frequency band vanishes, because the physical-then-Fourier block on the shell is a finite rectangle | `tendsto_norm_evenFourierCutoff_evenShellVectorEven`, `tendsto_norm_sub_evenFourierCutoff_evenShellVectorEven` |
| compact operators die on any orthonormal sequence (Bessel + Fréchet--Riesz), hence on the shell modes — the exact projection correction included | `tendsto_inner_orthonormal_atTop_zero`, `tendsto_apply_orthonormal_atTop_zero`, `tendsto_norm_compactOperator_apply_orthonormal`, `tendsto_norm_compactOperator_apply_evenShellVectorEven`, `tendsto_norm_evenSoninProjectionCorrection_apply_evenShellVectorEven` |
| **mode counting**: a fixed shell carries an orthonormal family indexed by mode number, so the energy dominates the count of modes an operator does not contract | `sum_norm_sq_evenShellVectorEven_apply_le_hsNormSq`, `card_le_hsNormSq_of_evenShellVectorEven` |
| **rate test**: a completion whose contribution eventually falls short of the coupling energy by a fixed amount cannot restore the floor | `not_bddBelow_soninCompletedPacketValueVar_of_shortfall`, `not_bddBelow_soninCompletedPacketValueVar_of_shortfall_clock` |
| the matching **upper** bound: a shell projection is a contraction, so the channel norm never exceeds the largest layer logarithm below the height — in position and in frequency | `norm_evenIndicatorLayer_apply_le`, `norm_evenLogShellChannel_apply_le`, `norm_evenFourierLogShellChannel_apply_le` |
| an **explicit** carrier and height schedule realising the blow-up: carrier at height `2i`, tower bracketed between heights `i` and `3i` | `tendsto_logShellRadius_atTop`, `exists_schedule_tendsto_norm_evenFourierLogShellChannel_atTop` |
| **frequency-side blow-up**: along a bracketing height schedule the reflected channel sends the packets to vectors of unbounded norm | `tendsto_norm_evenFourierLogShellChannel_soninPacketEven_atTop` |
| the packet's frequency mass between a slow band and a fast band stays above a fixed positive level | `exists_pos_eventually_le_fourier_band_gap` |
| the tower channel reflected into the **frequency** variable, its energy read through the isometry, and the two-radius lower bound transported to frequency-band masses | `evenFourierLogShellChannel`, `norm_evenFourierLogShellChannel_apply`, `norm_evenIndicatorCutoff_evenFourierTransform`, `norm_evenIndicatorLayer_evenFourierTransform`, `sq_le_norm_sq_evenFourierLogShellChannel_apply` |
| **exact energy of a step multiplier**: finite Pythagoras, the layer decomposition, and the resulting two-sided bounds — a lower bound by the smallest layer logarithm, and a **hypothesis-free** version reading the mass between two radii | `norm_sum_sq_of_pairwise_inner_eq_zero`, `inner_layer_apply_eq_zero_of_ne`, `norm_sq_evenLogShellChannel_apply`, `le_norm_evenLogShellChannel_apply`, `sq_le_norm_sq_evenLogShellChannel_apply` |
| the tower's layers are orthogonal projections: disjoint shells annihilate, their images pair to zero, and the partial sums telescope | `evenIndicatorLayer`, `adjoint_evenIndicatorLayer`, `evenIndicatorLayer_mul_of_le`, `evenIndicatorLayer_mul_of_le'`, `inner_evenIndicatorLayer_apply_eq_zero`, `sum_evenIndicatorLayer`, `evenIndicatorLayer_mul_self` |
| **the general necessary condition**: a completion with a floor must send the source packets to vectors of unbounded norm | `soninClockPacket`, `soninChannelFamilyContribution`, `norm_soninBumpL2_pos`, `tendsto_norm_apply_soninClockPacket_atTop_of_bddBelow` |
| on a fixed annulus the channel is bounded independently of the tower height, so **no height schedule** makes the log-shell channel restore the floor | `evenLogShellChannel_layer_apply_eq_zero`, `exists_bound_norm_evenLogShellChannel_of_annulus`, `not_bddBelow_soninCompletedPacketValueVar_logShellChannelFamily` |
| the channel norm dominates every layer logarithm below the height, so the channel norms **diverge** with the tower — the surviving completion class is inhabited | `log_logShellRadius`, `le_norm_evenLogShellChannel`, `tendsto_norm_evenLogShellChannel_atTop`, `exists_norm_atTop_channel_family` |
| pairing against any **fixed bounded operator** is bounded above, hence no floor; the concrete conductor channel at fixed aperture and height is such an operator | `soninFixedChannelContribution`, `soninFixedChannelContribution_le`, `not_bddBelow_soninCompletedPacketValueVar_fixedChannel`, `not_bddBelow_soninCompletedPacketValueVar_logShellConductor` |
| the scalar Burnol counterterm, and every prime-independent scalar, leaves the channel unbounded below; a working completion must diverge along the scales | `not_bddBelow_soninCompletedPacketValueVar_burnolCounterterm`, `not_bddBelow_soninCompletedPacketValueVar_const`, `tendsto_atTop_of_bddBelow_soninCompletedPacketValueVar` |
| the new statements at the worked flag `1 < 3/2 < 2 < 3` | `soninApertureTripleProduct_ne_zero_instance`, `evenSoninApertureRestrictionDefect_mul_outer_ne_instance`, `not_exists_lower_bound_bounded_instance` |

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
`formal/GaloisForLFunctions/RHTower/SoninShellProductIdeal.lean`,
`formal/GaloisForLFunctions/RHTower/SoninApertureLayerExtendedTrace.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellProductMixedTerms.lean`,
`formal/GaloisForLFunctions/RHTower/SoninTimeBandNonvanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninMixedBlockPolarizationSplit.lean`,
`formal/GaloisForLFunctions/RHTower/SoninBandLimitedShellVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDilationSumFourierInjective.lean`,
`formal/GaloisForLFunctions/RHTower/SoninMixedPhysicalBlockNonvanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninMixedFourierBlockNonvanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCouplingLayerOrthogonality.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCouplingSoninCompression.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDefectCarrierEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninExtendedTraceUniqueness.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionUnboundedRequirement.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionEnergyThreshold.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionSummabilityCriterion.lean`,
`formal/GaloisForLFunctions/RHTower/SoninSubAnnulusCouplingLimit.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketDisjointOrthogonality.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCouplingEnergyGrowth.lean`,
`formal/GaloisForLFunctions/RHTower/SoninBurnolCompletionNoFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFixedChannelNoFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLogShellChannelGrowth.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelAnnulusBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionBlowUpRequirement.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellLayerProjections.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelNormIdentity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketBandGapFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUp.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUpInstance.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelUpperBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionRateTest.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeCounting.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOrthonormalCompactVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeBandEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDilatedShellModeSupport.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellCellGeometry.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledAnnulusProfile.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
All declarations depend only on `propext`, `Classical.choice`, `Quot.sound`.

Novelty split for Theorem G: `(7)` was already in the corpus
(`SoninApertureRestrictionDefect.lean`) and is reused, not reproved.  New here are the exact
cross-polarization identity `(9)`, the cross-trace symmetry `(10)` and its Hilbert--Schmidt band
mechanism `(11)`--`(12)`, the directness/uniqueness of the presentation, the glued functional, its
cyclicity, and the single-corner formula `(8)`.

## Log

- 2026-08-01 — the first construction one would try against the size requirement is ruled out, and
  cheaply: carrying a fixed conductor along the tower by the dilations cannot grow it, because
  dilation is an isometry.  Stated for transport by arbitrary contractions, so it covers every
  conjugation scheme at once.  The value is negative but sharp — the required growth cannot come from
  moving one operator, only from a genuinely unbounded sequence of distinct ones.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninTransportedChannelClosed.lean`.
- 2026-08-01 — the gate is converted from a search into a size requirement.  Bounding an operator's
  image by its Hilbert--Schmidt norm turns the slope threshold into a statement about the ideal's own
  norm: a surviving completion's channels must have Hilbert--Schmidt norm exceeding a fixed multiple
  of the scale infinitely often.  Worth recording because it makes the remaining question checkable
  against a magnitude rather than against a construction — and because the comparison is stark, the
  coupling's Hilbert--Schmidt norm growing like the square root of the scale while its corrector's
  must grow like the scale.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninHilbertSchmidtCompletionFloor.lean`.
- 2026-08-01 — **the frequency-side channel is closed**, and with it every channel the corpus has.
  Two steps: the sublinear failure only ever used *domination* by a sublinear cap, not equality, so
  restating it that way makes it consume an estimate rather than a definition — and at the operator
  level it closes every family whose images grow more slowly than the scale, operator norms
  unbounded or not.  Then the packet bound is checked sublinear: constant term constant, logarithmic
  term `O(log scale)`, both surviving the square root.  The remaining question is unchanged in form
  but now has no candidate: a surviving completion must beat a definite slope infinitely often, and
  no channel in the corpus grows that fast.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninSublinearChannelFamily.lean`,
  `formal/GaloisForLFunctions/HTGeometry/LogMaxSublinear.lean`,
  `formal/GaloisForLFunctions/RHTower/SoninFourierChannelFamilyClosed.lean`.
- 2026-08-01 — the cut index is chosen, and the frequency-side channel's bound on a packet is now
  stated in the packet's own data alone.  Both halves of the bound turn out to want the same bracket
  on the cut radius — the upper end for the layer logarithms, the lower end for the half-width
  product — and the least index past twice the carrier supplies both at once, because a geometric
  tower overshoots by at most one ratio.  The bound reads `O(log carrier)` plus a constant in the
  half-width-times-carrier product, which along the schedule is `O(log scale)` plus a constant.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninChannelCutIndex.lean`.
- 2026-08-01 — the height-uniform bound is instantiated on the packets, and the input it needed turned
  out to be already in the corpus: the packet's spectral power tail, built for the shell-cut budget's
  high side, is exactly the hypothesis, needing only a natural exponent and transport across the
  transform.  Writing the resulting outer term out exposes the same combination this line has now met
  three times — half-width and radius entering to the same negative order, so that only their product
  matters.  Recording it as a pattern rather than an accident: a rescaled packet has no quantity that
  depends on refinement and scale separately.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninPacketChannelHeightBound.lean`,
  `formal/GaloisForLFunctions/RHTower/SoninPacketChannelCombinedForm.lean`.
- 2026-08-01 — the last unexcluded channel's freedom is measured, and it is smaller than it looked.
  A completion using the frequency-side channel may choose the tower's height at each step, and the
  crude bound grows with it; but against a vector with a rapidly decaying spectrum the height is
  irrelevant.  The mechanism is worth recording because it avoids the estimate one expects to need:
  the shells above the cut carry a weight growing linearly in the index and a mass decaying
  geometrically in it, and rather than sum polynomial-times-geometric, `(log t)^2 <= 4t` lets one
  order of the decay absorb the whole weight, leaving a bare geometric tail.  The bound that comes
  out mentions only the cut index.
  Lean: `formal/GaloisForLFunctions/HTGeometry/LogWeightedGeometricSum.lean`,
  `formal/GaloisForLFunctions/RHTower/SoninChannelHeightSplit.lean`,
  `formal/GaloisForLFunctions/RHTower/SoninShellTailWeightedSum.lean`,
  `formal/GaloisForLFunctions/RHTower/SoninChannelHeightUniform.lean`.
- 2026-08-01 — the sublinear exclusion is replaced by a *threshold* one: there is a definite positive
  slope, half the energy's own, below which every completion fails, and correspondingly a surviving
  completion must exceed that slope infinitely often.  The strengthening is free — the energy is
  spent in two halves instead of compared against a vanishing quotient — and it converts the open
  gate from a qualitative growth condition into an inequality against a named constant of the
  aperture.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninLinearThresholdCompletionFails.lean`.
- 2026-08-01 — the exclusion is lifted to the operator level: any completion built from a uniformly
  bounded operator family, paired against vectors of bounded norm, fails.  Nothing new is proved —
  it is the pairing bound and the bounded-sequence failure composed — but it is the form a candidate
  completion is actually presented in, and it removes the step where a reader has to check that the
  numbers coming out of an operator family are bounded.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninBoundedFamilyCompletionFails.lean`.
- 2026-08-01 — the failure is restated for a bare contribution *sequence*, which is the shape an
  operator family actually produces — a function of the schedule's step, not of the scale.  Worth
  noting the proof needs only divergence of the energy, not the linear rate, so the bounded-sequence
  case is genuinely cheaper than the sublinear one and should be cited directly rather than through
  it.  Also proved the matching upper bound on the packets, `‖psi‖^2 <= 8 delta I`, without which the
  pairing bound has nothing to bite on.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninBoundedSequenceCompletionFails.lean`.
- 2026-08-01 — the bounded case is placed inside the sublinear one, so the schedule now covers it
  without borrowing the crossing-clock argument.  Two small things came out of it: a bounded function
  divides by its argument to zero (stated once, rather than re-derived), and the pairing bound
  `re <inner> <= ‖C‖ ‖w‖²`, which had been living inline inside the log-shell closure proof and is
  now a named lemma.  Neither is deep; both were being re-proved implicitly.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninBoundedCompletionFails.lean`.
- 2026-08-01 — the sublinear result is turned round into a statement about the gate: any completion
  that restores the floor at every schedule must grow at least linearly in the scale.  Formally it is
  the contrapositive and costs three lines, but it is the more useful direction to have written down
  — it converts the open question from an existence question about completions into a growth
  condition that a candidate must satisfy, and a growth condition can be checked against the
  admissibility the corpus already imposes.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninCompletionMustGrowLinearly.lean`.
- 2026-08-01 — checking the corpus for the cap found that the log-shell channel completion is
  *already closed*, and by a cheaper argument than mine: its contribution is bounded by a **constant**
  (the packets live inside the fixed outer radius, so the annulus bound applies uniformly), and a
  constant is beaten by qualitative unboundedness alone.  So the linear rate is not what closes the
  Burnol channel.  What it does close is the class of completions that *grow*, which is where the
  qualitative argument has nothing to say — and the natural boundary is not the logarithm but
  sublinearity, so I proved that instead: any `f` with `f(r)/r -> 0` fails.  The logarithm is one
  case of it.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninSublinearCompletionFails.lean`,
  `formal/GaloisForLFunctions/HTGeometry/LogBelowLinear.lean` (extended).
- 2026-08-01 — **the comparison closes.**  Any completion whose contribution at each scale is at most
  the logarithm of that scale fails to give the packet channel a floor, witnessed by the schedule's
  own sequence.  Stating the cap as a hypothesis on an arbitrary function was the right move: it
  keeps the theorem independent of how any particular completion is built, which is what the rate
  test was designed for.  The proof is the three results of the last four entries meeting — linear
  energy, logarithm below every slope, and the sequence — with nothing new needed.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninLogCappedCompletionFails.lean`.
- 2026-08-01 — the log-versus-linear comparison is proved in general, which keeps it out of the
  aperture-specific chain: for every positive slope, a logarithm plus a constant is eventually below
  it.  The two-step route through `log x <= 2 sqrt x` is worth preferring to a direct limit argument
  because it is elementary and quantitative — the threshold is `max(16/s^2, 2(C+δ)/s)`, explicitly.
  Lean: `formal/GaloisForLFunctions/HTGeometry/LogBelowLinear.lean`.
- 2026-08-01 — the schedule is turned into a sequence, which is the form the rate test needs.  One
  detail worth recording: the test asks for `c < p i * a` strictly, while the energy bound only ever
  needed `c <= r a`, so the strict version had to be produced separately — from the same divergence
  of the scale, but as its own eventual statement rather than by weakening.  Cheaper than editing the
  conditions lemma and rebuilding its dependents.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninScheduleSequence.lean`.
- 2026-08-01 — the schedule statement is strengthened from "for every threshold there is a cut" to
  "every fine enough cut works", which is not a cosmetic change: the rate test consumes a *sequence*
  of scales with uniform conditions, and a threshold-indexed existence does not produce one without
  choice-and-recursion.  The eventual form does, by reindexing past the point where the conditions
  start holding.  The proof needed only `filter_upwards` in place of `.exists`, since the second
  choice was already eventual — the weaker form had been throwing information away.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellCutScheduleExists.lean` (restated).
- 2026-08-01 — checking the corpus before going further found that *unboundedness of the coupling
  energy was already proved* (`tendsto_hsNormSq_soninApertureCoupling_atTop`), so the previous
  entry's theorem restates known content in a weaker form.  The novelty of this line is the rate, and
  the rate needed one change to be expressible: the schedule's product had to be hoisted outside the
  threshold quantifier, which it can be, since none of its four obligations mentions the cut.  With
  `kappa` fixed once, the count is a *fixed* multiple of the scale and the bound becomes linear in
  the scale — the form a sublinear cap can be compared against.  Corrected framing recorded in the
  ledger.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninCouplingEnergyLinear.lean`.
- 2026-08-01 — the unboundedness is stated and proved as its own theorem, with the shortfall fixed at
  a half so the bound becomes `(N - 144 Dis)/4` and the threshold `ceil(4B + 144 Dis)` does the rest.
  Nothing new is used; the value is in having the conclusion in a form that later work can cite
  without re-deriving the schedule.  This is the first statement of the line whose conclusion
  mentions neither packets nor cuts nor slack — only the coupling and a bound.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninCouplingEnergyUnbounded.lean`.
- 2026-08-01 — the discount is verified scale free, which the unboundedness claim silently assumed.
  One of the three ideal errors carries the dilation, so its energy could have grown with the scale
  and eaten the count; it does not, because right composition by a unitary preserves
  Hilbert--Schmidt energy.  The corpus had only the *left* version of that
  (`hsNormSq_comp_left_eq_of_norm_map`) plus a one-sided bound on the right, so the equality had to
  be routed through adjoints — right composition by `D` is left composition by `D†` after adjoining,
  and `D† = D_{1/r}` is again an isometry.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninIdealErrorEnergyConstant.lean`.
- 2026-08-01 — **the schedule exists.**  Instantiating the two choices against the energy bound gives,
  for every shortfall and every threshold, a product and a cut past that threshold with
  `(N - const)(1 - eta)^2 <= hsNormSq Z`.  The assembly went through unchanged on the first attempt,
  which is the payoff of the last dozen entries: every hypothesis had already been sorted to one of
  the two choices, the algebra between them had been closed, and the closed forms matched the
  theorem's arguments syntactically.  The count is unbounded because the second choice admits an
  arbitrary threshold and everything subtracted from it is a constant of the aperture and the
  shortfall.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellCutScheduleExists.lean`.
- 2026-08-01 — the algebra between the two choices and the energy bound's hypothesis is closed.  The
  hypothesis divides a sum by the floor, so the three closed forms only apply after distributing the
  division — a one-line fact, but it is the join between the analytic work and the schedule, and
  without it the two existence statements do not meet the theorem they are meant to feed.  The
  hypothesis now reads as two first-choice quantities plus one second-choice quantity below the
  threshold.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellCutTotalSlack.lean`.
- 2026-08-01 — the second choice is packaged to match, with one clause added that the first did not
  need: the cut may be demanded finer than any prescribed threshold.  That is the clause the final
  conclusion rests on — the energy bound gives `N` minus a constant, so an `N` that is merely
  admissible proves nothing, while an `N` that can be pushed past any threshold makes the energy
  unbounded.  Both choices now exist as statements of the same shape, in the forced order.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellCutSecondChoice.lean`.
- 2026-08-01 — the first choice is packaged as a single existence: one `kappa` meeting all four of
  its obligations.  Worth noting that the four are of two different kinds — two are conditions on
  the packets (mean below one, energy floor) and two are conditions on the coupling's error — and
  they only combine because *all four improve in the same variable*.  That is not automatic; it is
  the consequence of the tied scale having made the two slack terms functions of the product alone.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellCutKappaFull.lean`.
- 2026-08-01 — the coupling's own hypotheses are sorted against the schedule, and the sorting is
  clean: the four largeness conditions are eventual in the cut, while the two tail conditions turn
  out not to involve the cut at all — under the tied scale they are conditions on `kappa q`, so they
  are discharged by the *first* choice rather than the second.  That was not obvious in advance and
  it matters for the assembly: the tail conditions must be imposed when `kappa` is picked, not left
  to be arranged later by refining.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellCutScaleConditions.lean`.
- 2026-08-01 — the second constant is choosable, and the step that makes it work is worth naming:
  past the outer radius the outer term's majorant is below the *global* majorant, so the carrier —
  which grows with the cut under the tied scale — drops out of the bound altogether.  Without that
  the outer term would still depend on `N` through two competing factors; with it, only the
  vanishing root is left.  Both schedule constants are now choosable, each by its own mechanism and
  in the forced order.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellCutCutChoice.lean`.
- 2026-08-01 — the first of the schedule's two constants is chosen.  The statement worth having is
  not that each term vanishes but that their *sum* is below a target beyond some product, with the
  cut nowhere in the statement — that is what licenses fixing `kappa` first and leaves `N` genuinely
  free afterwards.  The two terms vanish for unrelated reasons, so the proof is a sum of two limits
  rather than one estimate; keeping them separate until the last step is what made it short.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellCutKappaChoice.lean`.
- 2026-08-01 — the slack terms are rewritten under the scale, and the separation the last several
  entries argued for is now visible in the statements: two of the three no longer mention the number
  of annuli at all.  That is the point of tying the scale to the cut — not that it makes the
  estimates smaller, but that it removes one variable from two of the three terms, leaving a
  condition of the shape "two constants in `kappa`, plus something vanishing in `N`".
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellCutScheduledSlack.lean`.
- 2026-08-01 — the schedule is realised exactly.  Tying the scale to the cut by
  `r = 2 N kappa/(c-b)` makes `delta r = kappa` an identity, not an asymptotic, and that single
  choice collapses the analysis: the gap and the high-side product become constants in `N`, so the
  two schedule-driven slack terms stop depending on the cut altogether and the quantifier order
  `kappa` then `N` is realised by construction rather than argued.  Small Lean trap worth noting —
  rewriting backwards with the product identity substitutes `kappa` inside the scale as well, since
  the scale mentions it; the fix is to reassociate first and rewrite forwards.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellCutScale.lean`.
- 2026-08-01 — the third vanishing is proved, so every slack term now has one.  Nothing subtle in it:
  the exponent `1 - 2 N_0` is negative from the first order, so the negative power vanishes and the
  root follows by continuity.  With all three in hand the classification is complete and stable —
  two terms driven by the schedule constant, one by refinement — which is what makes the order of
  quantification forced rather than chosen.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellCutHighSlackVanishing.lean`.
- 2026-08-01 — writing the high-side radicand exactly corrected an order count made three entries
  ago.  I had estimated that term as `O(N^{-1/2})`, refinement-controlled at every order; the exact
  form shows it is `(delta t)^{1-2N_0}` up to a constant, so half-width and radius enter only through
  their product, and with `t = r b` that product is about `kappa b` — constant under refinement.  The
  slip was dropping the floor's own factor of `delta` when dividing.  Corrected reading: *two* of the
  three slack terms are governed by the schedule constant and only the outer one by refinement, so
  `kappa` must be chosen large before `N` grows, and `N` is then free.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellCutHighSlackProduct.lean`.
- 2026-08-01 — the outer slack term is identified and its vanishing supplied, completing the pair.
  It is the exact complement of the middle one: there the majorant does the work and the root is
  harmless, here the root does the work and the majorant need not be small.  The mechanism is the
  trivial-looking `tendsto_soninShellCutWidth_atTop`, which is worth stating separately because it is
  the only place refinement enters the slack at all.  With both proved, the two constants of the
  schedule are decoupled — the gap constant handles one term, the cut size the other.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellCutOuterSlack.lean`.
- 2026-08-01 — the middle slack term is identified with the shape its vanishing theorem covers, which
  closes the gap between the closed forms and the limits.  The step that does the work is small:
  moving the half-width inside the root, after which the band radius and the gap differ only by the
  ratio `a/(q-a)` of the shell's radii, so the whole term is a shell constant times
  `sqrt(kappa u) S(u)`.  Every slack term now has both a closed form and a vanishing theorem, and the
  schedule is a matter of choosing constants against them.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellCutMiddleSlack.lean`.
- 2026-08-01 — the weighted vanishing of the majorant is proved, which is the last analytic input the
  schedule needs: the middle slack term is a majorant times a *root* of its own argument, and only
  the schedule constant can shrink it.  Both proofs work by spending one extra order of the
  polynomial rate on the weight — a power `n` is covered by order `n+1`, a root by order `2` — so
  nothing beyond the rate already established is used.  Worth noting the failed first attempt: the
  natural route through `sqrt` tending to infinity needs a lemma this toolchain does not have under
  that name, and taking one more order instead avoids the question entirely.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninRefTailWeightedVanishing.lean`.
- 2026-08-01 — the high-side slack joins the band slack in closed form, so the schedule's slack
  condition is now an inequality between named elementary expressions with no hidden constants.  The
  high-side quotient behaves differently from the band ones: there the half-width cancels *once*
  against the floor rather than collapsing with a band length, leaving `delta^{1-2N_0}` against the
  radius to the negative order.  That asymmetry is the reason the high-side term improves with
  refinement at every order while the band at `r a` does not improve with refinement at all.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellCutHighSlackClosedForm.lean`.
- 2026-08-01 — the band slack is put in closed form, which turns the order-of-magnitude reading of
  the last few entries into an identity.  The quotient of the band root by the floor root collapses
  because both are roots and the half-width appears to the first power in each: what survives is
  `2 X sqrt(t/(delta I))`, and with `X` the sharp band bound this is the tail at the gap times
  `sqrt(t delta / I)`.  The two governing quantities are now named in the statement, so choosing the
  schedule is a matter of making a tail small and a product small, with nothing hidden in constants.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellCutSlackClosedForm.lean`.
- 2026-08-01 — the budget and the energy bound are rebuilt on the sharp estimate, so the whole chain
  from shell cut to Hilbert--Schmidt energy now runs on bounds that vanish in the schedule.  The two
  rebuilt theorems are line-for-line the previous ones with the band bound swapped, which is the
  payoff of having stated the intermediate interfaces in terms of *a* squared bound rather than a
  particular one — the correction cost two theorems, not the arc.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellCutSharpSchedule.lean`.
- 2026-08-01 — checking the assembled bound against the intended schedule found that discarding the
  packet mean is too lossy, and the loss is not a constant factor but the whole estimate.  At a band
  whose radius grows with the scale, the band's length cancels the half-width, and the term left
  behind is the *global* majorant `S(0)`, which does not shrink; so the `r a` term stayed bounded
  away from zero.  Keeping the mean's own bound fixes it, because the mean is a tail at the carrier
  and the carrier is further out than the gap — antitonicity then collapses the whole expression to
  one tail at the gap.  The lesson generalises: in this construction every appearance of the global
  majorant must be paired with a factor that vanishes, or the estimate silently stops being an
  estimate.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellCutSharpBandBound.lean`.
- 2026-08-01 — the energy bound is now closed in the sense that matters for the next step: every
  input is a quantity of the schedule, with no auxiliary parameter left to supply.  Freeing the band
  bound of the annulus needed only that the mean is below one, which the tail condition already
  gives — so the same single condition now discharges orthonormality, the energy floor, the mean
  bound, the high-side tail *and* the band bound's uniformity.  What is left is no longer
  construction but choice: exhibit `N(r)` linear in `r` satisfying the slack condition, and compare
  against the logarithmic cap.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellCutUniformBandBound.lean`,
  `formal/GaloisForLFunctions/RHTower/SoninShellCutEnergySchedule.lean`.
- 2026-08-01 — the norm floor is named as the cut's own quantity, and writing the slack explicitly
  made the three parts of the budget comparable for the first time.  They shrink for three different
  reasons: the band term at `b` by refinement, the band term at `r a` *not* by refinement at all but
  by the schedule constant through the tail's polynomial rate, and the high-side term by refinement
  at every order, the order cancelling out of the exponent.  Only the middle one constrains the order
  of quantification, and it is what forces `K` to be fixed before `N` grows.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellCutEnergyExplicitFloor.lean`.
- 2026-08-01 — `P` and `L` are joined, so the energy bound's every input is now an explicit quantity
  of the schedule.  The join itself is where the two halves of the last several rounds meet: the
  family hypothesis wants the budget of the *normalized* packets, the estimates give the budget of the
  packets, and the division between them is exactly the norm floor.  Nothing about the aperture, the
  layer or the ideal appears in the statement any more — only `N`, `P`, `L`, the threshold and the
  shortfall.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellCutEnergyFromBounds.lean`.
- 2026-08-01 — `P` is complete: every packet of a shell cut now has an explicit band budget, resting
  on three schedule conditions and nothing else.  Worth noting how few they are — the carrier ratio
  bound, one scale condition, and one tail condition, with the tail condition doing quadruple duty
  (orthonormality, energy floor, mean bound, high-side tail).  A Lean detail that cost a cycle: named
  hypothesis binders inside a `forall` whose types do not mention them are flagged unused by the
  warning-strict gate, even when the proof body uses the corresponding introduced variables; they
  have to be written as bare arrows instead.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellCutBandTotalBound.lean`.
- 2026-08-01 — the high-side bound is restated in the cut's terms, and the two hypotheses it needed
  both turned out to be already paid for.  The mean-below-one assumption is implied by the reference
  tail condition that orthonormality and the energy floor separately require, so a single condition
  on `delta * carrier` now serves three purposes.  And the "above twice the carrier" requirement,
  which looked like it might couple the scale to the geometry, reduces to `2 q <= b` — the scale
  cancels on both sides, so it is a constraint on the carrier ratio alone and holds at every scale at
  once.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellCutHighTail.lean`.
- 2026-08-01 — the squared-to-norm interface is built, and writing it surfaced a constraint on the
  schedule that the qualitative account had hidden.  The high-side tail estimate applies only above
  *twice* the carrier, so the term `‖psi - R_{r b} psi‖` needs `2 r q <= r b`, that is `2 q <= b`.
  The carrier ratio `q` therefore has to be taken in `(a, b/2]` rather than anywhere in `(a, b)`,
  which in turn forces `a < b/2`.  Both are free choices, but the earlier ledger entries said only
  "`a < q < b`", which is not enough.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellCutBandBound.lean`.
- 2026-08-01 — the band budget is now stated in the packet's own terms: three band quantities of one
  vector, at radii `r b`, `r a` and `b`.  Every reference to the dilate and to the layer has been
  eliminated — the physical term by exact vanishing, the two dilate band terms by the corpus's
  frequency transport.  This is the point where the aperture geometry stops mattering and only the
  packet's spectrum does; the remaining work is arithmetic on three numbers with known estimates.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellCutBandPacketTerms.lean`.
- 2026-08-01 — the dilate's contributions are settled, and two of the three came for free.  The
  physical term vanishes for *every* scale above one — no schedule condition — because the cut's
  annuli start at `b` and an inverse dilate dies under any physical cutoff below `r` times its inner
  radius.  And the frequency-side transport turned out to be already in the corpus: I wrote
  `norm_evenFourierCutoff_evenDilationCLM_inv` and its complement form and the build rejected both as
  already declared, in `SoninFourierCutoffDilation`.  Worth recording as a process note — the
  duplicate was caught by the compiler, not by the pre-write search, because I searched for the
  mathematical content under the packet's name rather than under the cutoff's.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninDilatedBandTransport.lean`.
- 2026-08-01 — the band budget is transported to the normalized packets.  Making the three terms one
  functional was the right move: each is a *fixed operator* applied to the vector, so the total
  divides by the norm in a single step instead of three, and the resulting lemma takes a bound on the
  packets and a lower bound on their norms and returns the family bound.  Two toolchain frictions
  worth recording: `ContinuousLinearMap.mul_apply` and `.one_apply` are both deprecated here in
  favour of `mul_apply_eq_comp` and `one_apply_eq_self`, and the general normalization lemma stated
  over `RCLike` will not `rw` into a complex-carrier goal — the coercions differ syntactically — so
  it has to be re-exposed at `ℂ` by `exact`, which unfolds them.
  Lean: `formal/GaloisForLFunctions/HTGeometry/NormalizeApply.lean`,
  `formal/GaloisForLFunctions/RHTower/SoninShellCutBandTotal.lean`.
- 2026-08-01 — the cut is plugged into the assembly, and the plumbing was free: the cutoffs are
  linear, so a normalized packet vanishes under the inner cutoff and is fixed by the outer one for
  exactly the same reason the packet does, with `map_smul` doing all the work.  The bound now reads
  with `N`, the number of annuli, and every other quantity in it is fixed by the schedule.  What is
  left is not a new mechanism but a normalization: the four band estimates are stated for the packets
  and are needed for the unit vectors, so each must be divided by the packet norm — which is exactly
  what the energy floor bounds from below.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellCutCouplingEnergy.lean`.
- 2026-08-01 — the general assembly closes: family in, energy bound out.  Two things had to be true
  and both already were.  The coupling is a relative-ideal element
  (`evenSoninApertureSuccessiveLayerTransition_mem_principalRelativeIdeal`), hence Hilbert--Schmidt
  — without that the mode count could not be applied to the very operator being bounded.  And the
  dilates are unit vectors, so the near-isometry targets need no construction at all.  A small
  encoding point worth keeping: the budget carries a factor two on the projection correction, and
  the survivor count sums equally weighted terms, so the correction is listed *twice* in a
  three-element family rather than given a coefficient.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninCouplingEnergyFromFamily.lean`.
- 2026-08-01 — the five error terms are collected into one theorem, and doing so exposed a mismatch
  that would have blocked the assembly.  The correction difference in the layer defect acts on the
  *dilate* of the packet, but `card_sub_le_hsNormSq_of_ideal_errors` can only count operators applied
  to the orthonormal family's own members.  The fix is that the relative ideal is closed under right
  multiplication, so `(Corr_a - Corr_b) * D` is itself an ideal element and the term becomes an ideal
  error on the packet.  Without that closure property the budget would have needed a second, separate
  counting argument for the dilated family.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninCouplingErrorBudget.lean`.
- 2026-08-01 — the high-side tail is bounded, completing the error budget: every term of the
  aperture reduction now has an estimate, and they are controlled by four different mechanisms —
  exact support vanishing, Schatten-1 mode counting, band measure, and decay.  The Lean cost of this
  step was almost entirely bookkeeping between the two exponent notations: the majorant rate is
  stated with a natural power, the tail integral needs a real one, and the bridge is
  `Real.rpow_natCast` after pushing the cast through `2 * N`.  A second recurring trap: `Set.indicator`
  rewrites need the membership as a set membership, never as the raw inequality that defines the set.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninScaledPacketHighTailBound.lean`.
- 2026-08-01 — the discarded energy now has both an identity and a pointwise bound.  The identity is
  the mirror of the band one, but the boundary matters: the complement of the *closed* band is open,
  and stating it with the strict inequality `t < |eta|` makes the pointwise identification exact
  rather than almost-everywhere, since at `|xi| = t` the discarded part is zero while a closed-set
  indicator would not be.  The pointwise bound is where the factor two in "twice the carrier" earns
  its place: it is exactly what makes all three tail arguments — at the two shifted frequencies and
  at the frequency itself — exceed half the frequency simultaneously, so one majorant value covers
  the whole expression.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninScaledPacketHighTail.lean`.
- 2026-08-01 — the power tail is integrated, so the high-side estimate now has both halves.  Two
  things about the Lean were not obvious in advance.  The left ray is not free: mathlib's improper
  integral lemmas are stated for `Ioi` only, so integrability on `Iic (-t)` has to be transported
  across the reflection, which
  `MeasurePreserving.integrableOn_comp_preimage` does once the preimage is identified.  And the
  natural-looking hypothesis `0 <= K` is not needed anywhere — if `K` were negative the domination
  hypothesis would already be the stronger statement — so it was dropped rather than carried.
  Lean: `formal/GaloisForLFunctions/HTGeometry/PowerTailIntegral.lean`.
- 2026-08-01 — tracing the layer defect through the dilation identified the one estimate still
  missing, and it is not the one the ledger predicted.  Two of the three pieces are already covered
  — the physical shell term vanishes exactly, the corrections are ideal errors precomposed with the
  dilation — and of the two band pieces, `‖R_a v‖` is the cutoff at radius `r a` on the packet, which
  the band fraction handles.  The piece with no existing tool is `‖v - R_b v‖`: the packet's spectral
  mass *above* radius `r b`, hence over an unbounded region, where a supremum bound is worthless.
  What that needs is a majorant integrable at infinity, and the Schwartz seminorms give it directly:
  one constant per order bounding `|v|^N ‖𝓕 f v‖` at every frequency, hence `C_N / u^N` for the
  majorant outside radius `u`.  Both majorants now have an explicit rate at every order, replacing
  the qualitative vanishing used so far.
  Lean: `formal/GaloisForLFunctions/HTGeometry/FourierPowerBound.lean`,
  `formal/GaloisForLFunctions/RHTower/SoninRefTailPolynomialDecay.lean`.
- 2026-08-01 — the coupling's distance to the dilate is now a standalone theorem rather than a step
  buried inside a limit proof.  The corpus proved it inline, for the fixed-profile packets only, in
  the middle of `tendsto_norm_soninApertureCoupling_soninPacketEven_sub_subAnnulus`; but the argument
  never uses the packet, only that the vector vanishes inside the inner aperture and is fixed by the
  outer one.  Extracted with those as hypotheses it applies to the rescaled shell-cut packets
  unchanged, and is one theorem rather than a duplicated block.  Worth noting the estimate is free of
  every smallness assumption — carrier, half-width and scale are unconstrained — because it is
  structural; the analysis enters only afterwards, in bounding the three error terms.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninCouplingDilateDistance.lean`.
- 2026-08-01 — the shell cut is built, completing the supply side of the counting argument.  The
  corpus's `exists_disjoint_annulus_family` produces annuli by endpoints for the fixed-profile
  family; the rescaled family is parameterised by centre and half-width instead, so the cut is given
  explicitly — centres `b + (2i+1)δ` with `δ = (c-b)/(2N)` — and its five needed properties proved
  directly.  Consecutive pieces abut, so the separation inequality holds with equality; that is
  admissible because the shared endpoint is a null set for the pairing.  The two conditions the
  packets need collapse to conditions on the single product `δ|w|`, which is what makes one carrier
  serve all `N` annuli.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellCut.lean`.
- 2026-08-01 — the orthonormal family is constructed for the rescaled packets.  The corpus had
  disjoint-annulus orthogonality only for the *fixed-profile* family, and that proof does not
  transfer by instantiation because the two packet constructions are different objects; but its
  mechanism does, since both vanish outside their annuli.  Two facts had to be added around it: the
  energy floor makes each packet nonzero (needed to divide by the norm), and a general
  `orthonormal_normalize` turning a nonzero pairwise-orthogonal family into an orthonormal one,
  which mathlib does not provide.  Worth recording that orthogonality here uses *only* the supports:
  the carriers are unrelated, and in the intended schedule they are in fact all equal to `r q`, so
  any argument that separated them would have been useless.
  Lean: `formal/GaloisForLFunctions/HTGeometry/OrthonormalNormalize.lean`,
  `formal/GaloisForLFunctions/RHTower/SoninScaledPacketOrthogonality.lean`.
- 2026-08-01 — checking the error budget against the escape threshold found a term the threshold
  cannot take.  The layer defect on the dilated packet contributes `||R_{a0} v||`, which is the
  frequency cutoff at radius `r a0` on the packet, because dilation conjugates cutoffs; its
  band-times-width product *grows* with the schedule constant `K` instead of shrinking.  The term is
  still negligible, but for a different reason: its gap to the carrier grows with `K` as well, and
  the reference tail beats every power.  Recording that required replacing the yes/no threshold by
  the fraction itself, `16 t delta A^2 / I` with `A` the tail bound at the gap.  General lesson for
  this construction: band radius and band gap are independent knobs, and only the gap is governed by
  decay.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandFraction.lean`.
- 2026-08-01 — the counting core is proved, in a form that mentions no annulus, no aperture and no
  packet.  `card_mul_sq_le_hsNormSq_of_near_unit` is the honest statement of what the two-branch
  estimate buys: carrying `N` orthonormal vectors to within `η` of unit targets — *any* unit targets,
  unrelated to each other — costs `N (1-η)²` of Hilbert--Schmidt energy.  Composing it with the
  bounded-spoilage count gives `card_sub_le_hsNormSq_of_ideal_errors`, whose hypothesis is literally
  the shape the aperture estimate produces.  Both discounts to `N` are constants, so the conclusion
  is linear in the number of modes supplied.
  Lean: `formal/GaloisForLFunctions/HTGeometry/HilbertSchmidtNearIsometryCount.lean`,
  `formal/GaloisForLFunctions/RHTower/SoninSurvivorEnergyCount.lean`.
- 2026-08-01 — the correction terms are handled, and the route through them is not the one the plan
  assumed.  The corpus kills them with compactness
  (`IsCompactOperator.norm_apply_tendsto_zero_of_bounded_weakly_null`), which gives no rate and so
  cannot be made uniform over a family of annuli that changes with the scale.  The way out is that
  the ideal errors are not merely compact but Schatten-1, which the corpus already proves — hence
  Hilbert--Schmidt, hence of *fixed finite energy*.  Mode counting then replaces the rate entirely:
  `card_filter_le_hsNormSq` says a Hilbert--Schmidt operator exceeds `ε` on at most `hsNormSq/ε^2`
  members of any orthonormal family, a bound independent of the family's size, so a growing family
  of orthogonal packets loses only boundedly many to a fixed error.  This also removes the need for
  any absolute-continuity or weak-nullity argument about shrinking supports.
  Lean: `formal/GaloisForLFunctions/HTGeometry/HilbertSchmidtBadModeCount.lean`,
  `formal/GaloisForLFunctions/RHTower/SoninIdealBadModeCount.lean`.
- 2026-08-01 — the two halves are combined, and the combination exposed the real constraint on the
  schedule.  `exists_uniform_soninScaledPacket_band_escape` produces two constants that mention no
  annulus: a carrier threshold `u0` and a shortness threshold `rho`.  Producing them needs the mean
  bounded by one (from the reference majorant, `abs_soninScaledPacketMean_le_tailSup`) and the
  reference-square tail below a twentieth of the reference square's mass; both come from the two
  vanishing theorems already proved.  The lesson is in the arithmetic: `delta*w` is *constant* if the
  number of annuli grows like the scale, so the naive schedule never clears `u0`.  Taking about `r/K`
  annuli for a fixed large `K` clears it while keeping the count linear in `r` — still far above the
  logarithmic cap.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandEscape.lean`.
- 2026-08-01 — the two halves of the energy comparison are now both proved, and the tail-supremum
  construction was generalized so the second half could reuse the first.  The band half is short:
  integrate the uniform in-band bound over the band.  The energy half needed a new object.  Squaring
  the packet produces integrals against the *squared* profile, and the corpus's estimates were all
  hard-wired to the profile itself.  What makes the repetition unnecessary is a geometric fact: once
  the half-width drops below the annulus radius the two lobes are disjoint, so the squared profile is
  again two translated dilates of a single fixed reference — the square of the reference bump, which
  is again smooth, compactly supported and of positive mass.  With `fourierTailSup` and
  `norm_fourierIntegral_comp_div_sub` stated for an arbitrary profile, the whole chain then applies
  to the square verbatim, and `cos^2 = (1 + cos 2x)/2` turns the packet's energy into the squared
  profile's mass plus two of its cosine masses.  Energy floor: `delta` times a positive constant,
  minus tails that vanish with `delta*w`.
  Lean: `formal/GaloisForLFunctions/HTGeometry/FourierTailSup.lean`,
  `formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandEnergy.lean`,
  `formal/GaloisForLFunctions/RHTower/SoninScaledProfileSquare.lean`,
  `formal/GaloisForLFunctions/RHTower/SoninScaledProfileSquareTail.lean`,
  `formal/GaloisForLFunctions/RHTower/SoninScaledPacketEnergyLower.lean`.
- 2026-08-01 — the packet's spectral tail is proved, and then upgraded to the uniform form the band
  estimate actually needs.  The pointwise bound (`norm_fourier_soninScaledPacket_le`) is a direct
  assembly: cosine modulation splits the packet's transform into two shifted profile transforms, the
  mean term is a scalar multiple of a third, and each is a reference tail.  But a band estimate needs
  one number controlling all in-band frequencies at once, and rapid decay is a statement about a
  single frequency going to infinity.  The fix is `soninRefTailSup`, the supremum of the reference
  transform outside a symmetric band: finite because the transform is bounded by the profile's mass,
  vanishing as the band grows because the profile decays in *both* directions — the corpus already
  had both one-sided decay statements, which is what makes the two-sided supremum reachable.  With
  it, `norm_fourier_soninScaledPacket_le_tailSup` holds uniformly on `|xi| <= t` whenever `t < w`.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninScaledPacketTail.lean`,
  `formal/GaloisForLFunctions/RHTower/SoninReferenceTailSup.lean`.
- 2026-08-01 — the cosine modulation rule is built, completing the real-line Fourier toolkit this
  construction needed: dilation, additivity, translation, homogeneity, character modulation, and now
  `F(f cos(2 pi w0 x))(xi) = (F f(xi - w0) + F f(xi + w0))/2`.  Mathlib has all of these only in the
  abstract bilinear form whose head symbol differs from `Real.fourierIntegral`, so each had to be
  proved by substitution in the defining integral.  With this the packet's spectral tail is a
  three-line assembly from parts already proved.
  Lean: `formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`.
- 2026-08-01 — the mean itself is now bounded by reference tails, with the half-width gone.  Both
  lobes carry equal mass, so the profile's total mass is exactly `2 delta` times the reference mass —
  centre free — and dividing the cosine bound by it cancels `delta`.  So
  `|mean(m, delta, 2 pi w)|` is at most a fixed multiple of reference tail values at `±delta*w`,
  uniformly over the annuli: the mean is small as soon as `delta*w` is large, which is the same
  single condition the band estimates turn on.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — the packet mean's numerator is now a reference tail.  The profile's transform is one
  lobe's at both signs, each equal to `delta` times the reference transform at `±delta*xi`; and the
  corpus's cosine-integral identity turns the cosine-weighted mass into the average of the transform
  at `±w`.  So `|int bump * cos(2 pi w x)|` is bounded by `delta` times reference tail values at
  `±delta*w`, which decay faster than any polynomial in `delta*w`.  Since the denominator of the mean
  is exactly `delta` times the reference mass, the mean itself is governed by the same tail.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — the one function is bounded.  The reference profile is smooth with compact support, so
  the corpus's rapid-decay lemma applies to it directly, and via centre freedom every lobe inherits
  the same decay in the rescaled variable: along any family with `delta_i * xi_i -> infinity`, the
  lobe's transform beats every polynomial rate in that product.  This is the tail estimate the rate
  argument asked for, in the single variable `delta*kappa` — the quantity the `N`-packet threshold
  turns on.  What is left is bookkeeping: feed it through the mean, the band masses and the
  two-branch estimate to get `N` of order `r` packets at scale `r`.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — centre freedom proved.  A lobe of the profile is the reference bump dilated by the
  half-width and translated to the lobe's centre; translation contributes only a unimodular phase,
  so `||F(lobe profile)(xi)|| = delta * ||F(reference)(delta*xi)||`, with the centre gone.  This
  needed a third missing real-line rule, `fourierIntegral_comp_add_right`, proved like the others by
  substitution.  Every spectral quantity of the family is now the *fixed* reference profile's,
  evaluated at `delta*xi` — the tail estimate has exactly one function to bound.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — the lobe decomposition is complete on the spectral side:
  `F(packet)(xi) = F(lobe)(xi) + F(lobe)(-xi)`, hence
  `||F(packet)(xi)|| <= ||F(lobe)(xi)|| + ||F(lobe)(-xi)||`.  The interference between the two lobes,
  which is the only place the annulus *centre* enters, is now confined to the sum: a tail bound for
  the single lobe transfers to the packet with a factor two and no centre dependence.  The remaining
  analytic input is that lobe tail as a function of `delta*kappa`.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — supplied the additivity rule the lobe decomposition needs.  Mathlib has additivity of
  the Fourier integral only in the abstract bilinear form with continuity side conditions; the
  real-line specialisation is now `fourierIntegral_add`, proved from `fourier_real_eq` and the
  convergence criterion (with one wrinkle: the criterion is stated with `inner R v xi`, which needs
  `Real.inner_apply` to match the `v * xi` of the integral formula).  With this and
  `fourier_comp_neg` the packet's transform can be assembled from one lobe's at `±xi`.
  Lean: `formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`.
- 2026-08-01 — split the packet into its two lobes, which is where the remaining centre dependence
  sits.  Profile and packet are each a lobe plus its reflection, and the reflection rule
  `F(f o neg)(xi) = F f (-xi)` follows from mathlib's inverse-transform identities.  A lobe is a
  single translate of the reference bump, so its spectral magnitude carries no interference term —
  the tail estimate should be run on the lobe, not the packet.  Assembling the packet's transform as
  the sum of the lobe's at `±xi` needs additivity of the Fourier integral on the real line, which
  mathlib provides only in the abstract bilinear form (`VectorFourier.fourierIntegral_add`, with
  continuity side conditions); specialising it is the next step.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — the scaling work pays off as a *linear* threshold.  With all band quantities depending
  on the annulus only through `delta*t` and `delta*kappa`, cutting `(b,c)` into `N` annuli of
  half-width `(c-b)/(2N)` and carrying them at frequency `r q` turns the `N` band conditions into the
  single condition `(c-b) r q / (2N)` large, i.e. `r` at least a constant times `N`.  So `N` of order
  `r` packets are usable at scale `r`, giving `hsNormSq Z_r` of order `r` against a logarithmic
  contribution cap.  Earlier I worried that exact self-similarity would force the annuli to be
  geometrically spread and so bounded in number inside a fixed window; that worry was misplaced —
  the argument needs uniform *dependence* on `delta*kappa`, not a single fixed reference annulus.
  The one remaining input is the reference spectral tail as a function of `delta*kappa`.
- 2026-08-01 — the scale-free band fraction is now a statement about the Sonin Fourier cutoff itself:
  `||R_t w||^2 = delta * ||R_{delta t} w_ref||^2`, and since the total energy carries the same factor,
  `norm_sq_evenFourierCutoff_soninScaledPacketEven_fraction` says the captured fraction is identical
  for every annulus of the family.  This is the operator-level form of the property the `N`-packet
  threshold needs: hold `delta*kappa` fixed and every packet of the family loses and keeps exactly
  the same proportion of its energy to any proportionally scaled band.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — the classical scaling identities are now attached to the carrier's own Fourier
  transform: the rescaled packet is integrable, so its `L²` transform agrees a.e. with the classical
  integral, and its spectral density is the modulus squared of that transform.  Everything proved
  about the family's spectrum by substitution therefore applies to `evenFourierCutoff` band masses,
  which is what the two-branch estimate reads.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — band masses now scale like the total mass, so band *fractions* are scale free.  The
  density picks up `delta^2` with its argument rescaled, and the substitution in the band integral
  gives back one factor of `delta`, so the mass inside radius `t` is `delta` times the reference mass
  inside `delta*t` — exactly how the total energy scales.  The fraction of spectral mass in a band is
  therefore a function of `delta*t` and `delta*kappa` alone, identical for every annulus of the
  family.  That is the statement the `N`-packet threshold needed: hold `delta*kappa` fixed and one
  band estimate serves all `N`.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — the spectrum of the whole family is now one spectrum.  Applying the dilation rule to
  the packet scaling gives
  `F(packet m delta kappa)(xi) = delta * F(packet (m/delta) 1 (delta*kappa))(delta*xi)`, so a
  frequency band of radius `t` for the family is a band of radius `delta*t` for the reference.  Every
  band mass, tail and density for a narrow annulus at a high carrier is therefore the reference
  quantity at a rescaled radius — the per-annulus constants that made the `N`-packet threshold
  `N`-dependent are gone from the spectral side as well as the spatial one.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — the spectral side of the scaling now has its tool.  Mathlib carries the translation and
  isometry rules for the Fourier integral but no dilation rule, so
  `fourierIntegral_comp_div` is proved here by substituting the dilation in the defining integral:
  the transform of `x -> f(x/delta)` at `xi` is `delta` times the transform of `f` at `delta*xi`.
  Applied to the rescaled packet this turns its whole spectral profile — density, band masses, tails
  — into the reference profile read at `delta*xi`, which is the last step needed before the band
  limits can be stated once for the entire family instead of once per annulus.
  Lean: `formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — the rescaled family now satisfies the two support hypotheses of the two-branch
  estimate: a physical cutoff at or below `m - delta` annihilates it, one at or above `m + delta`
  fixes it.  The outer statement needs `0 <= m` — without it a packet centred at a negative `m` has
  its two lobes on the wrong sides and the cutoff argument fails, which the proof search found
  before I did.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — the rescaled family now lives in the even Sonin carrier:
  `soninScaledPacketEven`, with squared norm the integral of the square and, by the scaling law,
  `delta` times the reference energy at `delta*kappa`.  The coupling estimates can therefore be run
  against this family with the constants uniform in the annulus, which is what the earlier
  sub-annulus family could not offer.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — the packet itself is now an exact rescaling:
  `soninScaledPacket m delta kappa x = soninScaledPacket (m/delta) 1 (delta*kappa) (x/delta)`.
  Every integral attached to it therefore reduces to a reference one — the energy is `delta` times
  the reference energy at `delta*kappa` — so the per-annulus constants that made the `N`-packet
  threshold `N`-dependent are all instances of a single reference constant evaluated at the rescaled
  frequency.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — the width and the frequency now enter only through their product.  The same dilation
  substitution scales the cosine-weighted mass, so the two factors of the half-width cancel in the
  mean: `soninScaledPacketMean m delta kappa = soninScaledPacketMean (m/delta) 1 (delta*kappa)`.  The
  modulated packet on the rescaled profile is defined and satisfies the second Meyer condition
  (`integral_soninScaledPacket = 0`).  So a narrower annulus at a proportionally higher carrier is
  *the same packet rescaled* — which is what will let one threshold serve a growing family, instead
  of a fresh threshold per annulus.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — first quantitative consequence of the rescaled profile: its total mass is exactly the
  half-width times the reference mass (`integral_soninScaledAnnulusBump_scaling`, by substituting the
  dilation), and it is positive.  That is the normalisation a mean-zero modulation divides by, so the
  width now enters the packet's mean explicitly rather than being hidden in an abstract bump.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — started the missing estimate at its root.  Width dependence cannot be extracted from
  the corpus's annulus bump: its `ContDiffBump` radii depend on the annulus, and mathlib's bump family
  is abstract, so the profiles of two different widths are unrelated — no scaling law exists to
  prove.  `SoninScaledAnnulusProfile.lean` therefore builds the profile as one fixed reference bump
  precomposed with a dilation, and proves the scaling law as an identity, along with evenness,
  smoothness, the support in the two intervals of half-width `delta` around `±m`, and a lower bound
  at the centre.  That identity is what will carry the width through a Fourier estimate.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninScaledAnnulusProfile.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — **the cell family cannot serve, and the reason is the second Meyer condition.**  The
  layer term needs the dilated test vector to have *no* mass below the inner aperture:
  `Q_a v = v` requires `R_a v = 0`.  A cell vector is a nonnegative indicator, so its Fourier
  transform at zero is its integral, which is positive by `evenShellCell_measureReal_pos` — its
  spectrum is concentrated *at* low frequency, and `R_a v` is bounded away from zero however the
  cell shrinks.  The wavepacket escapes this precisely because it is modulated and mean zero
  (`integral_soninPacket = 0`); that condition, which looked like a normalisation, is what puts its
  spectrum at the carrier and away from the origin.  So the orthonormal family for a rate must be
  modulated, i.e. packets on disjoint sub-annuli — the family already used in
  `eventually_sub_one_le_hsNormSq_of_disjointAnnuli` — and the rate problem is the original one: a
  narrower annulus has a wider spectral tail, so each extra packet needs a larger scale.  The mode
  detour is closed; the quantitative bump estimate is the real obstacle.
- 2026-08-01 — **correction to the mode plan.**  `evenShellVectorEven` is not a family of oscillating
  modes: it is the normalized indicator of the `n`-th *cell* of a partition of the shell, orthonormal
  because the cells are disjoint.  The cells accumulate at the inner radius with exact width
  `(b-a)/((n+2)(n+3))`, so the `n`-th one has frequency scale of order `n²`, not `n`.  The count that
  matters — how many cells have dilated frequency inside the aperture pair at scale `r` — is
  therefore of order `sqrt(r)`, not `r`, since the condition is `n²/r` in `(a,b)`.  That is still far
  above the logarithmic cap on the frequency channel, so the route survives, but the earlier note
  claiming a linear count assumed an oscillatory family and was wrong.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellCellGeometry.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledAnnulusProfile.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — the geometric half of the layer term, exactly.  The cutoff/dilation intertwining is an
  identity, so the inverse dilate of a shell mode sits in the dilated shell with no error: apertures
  below `r*s` annihilate it, apertures above `r*u` fix it, and its norm is unchanged.  For the
  wavepacket the same statements hold only through its compactly supported profile; for modes they
  are immediate.  What is left of the layer term is the *Fourier* half — the dilated mode's
  frequency, which is the mode number divided by the scale, has to sit inside the aperture pair, and
  that is where the modes' sharp profile makes the estimate weaker than the packet's.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninDilatedShellModeSupport.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellCellGeometry.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledAnnulusProfile.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — the band term came free as well.  A shell mode is fixed by the physical cutoff at the
  shell's outer radius, so a frequency cutoff reaches it only through the physical-then-Fourier
  block — which is one of the relative ideal's own generators, a finite time--frequency rectangle,
  hence compact.  Compact operators die on orthonormal sequences, so the mode's mass in any fixed
  band vanishes with the mode number, with no new analysis.  Two of the three error terms of a mode
  estimate are now discharged; the layer defect on the *dilated* mode is the one that remains.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellModeBandEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDilatedShellModeSupport.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellCellGeometry.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledAnnulusProfile.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — first input of the mode estimate discharged.  The two-branch estimate carries three
  error terms; the compact one is now free for *any* orthonormal sequence, by Bessel plus
  Fréchet--Riesz plus the corpus's compact/weakly-null lemma, so on the shell modes the exact
  projection correction vanishes with no further work.  What the mode estimate still needs is the
  band term: the Fourier mass of a high shell mode below a fixed radius, which is the analogue for
  modes of the packet's low-band escape and is not in the corpus.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninOrthonormalCompactVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeBandEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDilatedShellModeSupport.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellCellGeometry.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledAnnulusProfile.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — built the instrument a rate needs.  The energy lower bound so far came from cutting
  the window into `N` annuli, which forces a fresh scale threshold for each `N` and so yields no
  speed.  A fixed shell already carries an orthonormal family indexed by the *mode number*
  (`evenShellVectorEven`), so `card_le_hsNormSq_of_evenShellVectorEven` bounds the energy below by
  the number of modes the coupling does not contract — a count that can grow with the scale inside
  one fixed geometry.  Turning that into a rate needs a quantitative version of the two-branch
  estimate on shell modes, which is the analytic step still missing.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellModeCounting.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOrthonormalCompactVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeBandEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDilatedShellModeSupport.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellCellGeometry.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledAnnulusProfile.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — the comparison itself is now a corpus theorem rather than a remark: a completion whose
  per-scale contribution eventually falls short of the coupling energy by any fixed positive amount
  leaves the channel unbounded below, whatever the completion is built from.  With the logarithmic
  upper bound on the frequency channel, the whole gate reduces to one question with two named
  quantities: does `hsNormSq Z_r` exceed `log(outer radius)` by a fixed amount at all large scales?
  A growth *rate* for the coupling energy is the missing input — the divergence proof supplies none.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninCompletionRateTest.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeCounting.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOrthonormalCompactVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeBandEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDilatedShellModeSupport.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellCellGeometry.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledAnnulusProfile.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — the frequency-side contribution is now pinned from both sides: the same orthogonal
  decomposition that gives the lower bound gives `||channel_n u|| <= (largest layer logarithm) ||u||`,
  since the layer masses total at most the vector's.  So the completion this channel can supply
  grows *at most* like the logarithm of the outer tower radius.  The gate is therefore a rate
  comparison: the floor needs the contribution to track the coupling energy with summable excess,
  and the contribution is logarithmic in the radius.  What is still missing is a *rate* for the
  coupling energy — the divergence proof gives `hsNormSq Z_r > N - 1` for each `N` eventually, with
  no speed, so the two sides cannot yet be compared.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninChannelUpperBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionRateTest.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeCounting.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOrthonormalCompactVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeBandEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDilatedShellModeSupport.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellCellGeometry.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledAnnulusProfile.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — the schedule is no longer a hypothesis.  Reading the carrier along the tower itself —
  carrier at height `2i`, inner radius at height `i`, outer at height `3i` — makes the bracketing
  automatic: geometric growth separates all three by `a(r^i - 1)`, and the inner radius climbs.  So
  `exists_schedule_tendsto_norm_evenFourierLogShellChannel_atTop` exhibits an actual carrier and
  height schedule with `||T_i w_i|| -> infinity`, unconditionally.  The awkward direction — picking
  integer heights to bracket a *given* carrier — was avoidable because the packet family is
  parameterised by an arbitrary carrier sequence.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUpInstance.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelUpperBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionRateTest.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeCounting.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOrthonormalCompactVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeBandEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDilatedShellModeSupport.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellCellGeometry.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledAnnulusProfile.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — **the blow-up condition is met on the frequency side.**  Along a height schedule whose
  inner tower radius is outrun by the carrier, whose outer radius outruns it, and whose inner radius
  climbs the tower, the reflected channel satisfies `||T_i w_i|| -> infinity` on the source packets.
  That is exactly the necessary condition
  (`tendsto_norm_apply_soninClockPacket_atTop_of_bddBelow`) that the scalar counterterm, every
  bounded contribution, every fixed operator, and the position-side tower under any height schedule
  all failed.  The schedule is still a hypothesis — the arithmetic realising it, and whether the
  resulting contribution beats the coupling energy with summable excess, are the next questions —
  but the frequency side is no longer excluded, and it is the only side that is not.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUp.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUpInstance.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelUpperBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionRateTest.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeCounting.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOrthonormalCompactVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeBandEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDilatedShellModeSupport.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellCellGeometry.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledAnnulusProfile.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — the mass the frequency-side bound consumes is now known not to erode: between a band
  the carrier outruns and a band that outruns the carrier, the packet holds frequency energy above a
  fixed positive level, uniformly along the clock.  Both corpus band limits in gap form feed this
  directly, and the packet norm limit supplies the level.  Multiplying by the layer logarithm — which
  diverges once the inner radius is taken to infinity — is the remaining step.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninPacketBandGapFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUp.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUpInstance.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelUpperBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionRateTest.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeCounting.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOrthonormalCompactVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeBandEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDilatedShellModeSupport.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellCellGeometry.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledAnnulusProfile.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — the estimate moved to the frequency side, which is where the packets actually travel.
  Reflecting the tower channel through the Fourier involution turns it into a step multiplier in
  frequency; the reflection is isometric, so the energy is the position channel's energy on the
  transformed vector and the layer masses become frequency-band masses.  The two-radius lower bound
  therefore transports verbatim.  The packets' support is fixed — that is what closed the position
  channel — but their frequency runs to infinity, so on this side the corpus's own band limits feed
  the bound.  What remains is to choose the inner and outer radii as functions of the clock and let
  the two band limits run.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninFourierChannelBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketBandGapFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUp.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUpInstance.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelUpperBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionRateTest.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeCounting.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOrthonormalCompactVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeBandEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDilatedShellModeSupport.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellCellGeometry.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledAnnulusProfile.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — the lower bound restated without support hypotheses, which is the form the Fourier
  side needs: `L^2 (||layer(rho_0, rho_n) u||^2 - ||layer(rho_0, rho_m) u||^2) <= ||channel_n u||^2`.
  A packet's Fourier transform never vanishes exactly on a band, so the earlier version — which
  assumed no mass below the inner radius — could not be applied to it; this one asks only how much
  mass sits between two radii, which the corpus's band limits do control.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninChannelNormIdentity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketBandGapFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUp.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUpInstance.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelUpperBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionRateTest.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeCounting.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOrthonormalCompactVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeBandEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDilatedShellModeSupport.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellCellGeometry.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledAnnulusProfile.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — the step multiplier now has an exact energy, not just an upper bound:
  `||channel u||^2 = sum over layers of (layer logarithm)^2 times (layer mass)^2`, from finite
  Pythagoras on the orthogonal layer decomposition.  The lower bound follows —
  `le_norm_evenLogShellChannel_apply`: on a vector living between two tower radii the channel is at
  least the smallest layer logarithm in that range, times the norm.  Finite Pythagoras for a
  pairwise-orthogonal `Finset` family is not in mathlib in this form (only the
  `OrthogonalFamily`-of-subspaces version) and is now corpus-owned.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninChannelNormIdentity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketBandGapFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUp.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUpInstance.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelUpperBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionRateTest.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeCounting.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOrthonormalCompactVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeBandEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDilatedShellModeSupport.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellCellGeometry.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledAnnulusProfile.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — built the orthogonal decomposition the tower estimates were doing by hand: the
  difference of two nested cutoffs is the shell projection between them, disjoint shells annihilate
  in both orders, their images are orthogonal, and the layers of a tower telescope to the difference
  of the extreme cutoffs.  This is what a *lower* bound on a step multiplier needs — the upper
  bounds so far went through the triangle inequality, which cannot see cancellation, and the next
  question (whether a Fourier-side channel blows up on the packets, whose frequency does run to
  infinity even though their support does not) is a lower-bound question.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninShellLayerProjections.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelNormIdentity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketBandGapFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUp.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUpInstance.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelUpperBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionRateTest.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeCounting.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOrthonormalCompactVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeBandEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDilatedShellModeSupport.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellCellGeometry.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledAnnulusProfile.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — the constraint stated once, for completions of arbitrary shape: the contribution at a
  scale is at most the packet norm times the norm of the operator *applied to that packet*, and the
  packet norms are uniformly bounded, so a completion restoring the floor must satisfy
  `||T_i w_i|| -> infinity`.  Being large somewhere is not enough — the operators must be large
  exactly where the source packets live.  Each earlier no-go is an instance: constants, bounded
  contributions, fixed operators, and the log-shell tower under any height schedule all keep
  `||T_i w_i||` bounded.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninCompletionBlowUpRequirement.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellLayerProjections.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelNormIdentity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketBandGapFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUp.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUpInstance.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelUpperBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionRateTest.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeCounting.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOrthonormalCompactVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeBandEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDilatedShellModeSupport.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellCellGeometry.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledAnnulusProfile.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — and the inhabitant does not in fact help.  The channel norms diverge only because the
  tower reaches far out in position; the source packets never leave a fixed annulus, and on that
  annulus all but finitely many layers cancel between their two cutoffs, so the channel's pairing
  with the packets is bounded independently of the height.  Hence no schedule of tower heights
  restores the floor.  The surviving class is now narrower still: a completion must grow *on the
  fixed annulus where the packets live*, which the logarithm of position cannot do.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninChannelAnnulusBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionBlowUpRequirement.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellLayerProjections.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelNormIdentity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketBandGapFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUp.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUpInstance.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelUpperBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionRateTest.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeCounting.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOrthonormalCompactVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeBandEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDilatedShellModeSupport.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellCellGeometry.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledAnnulusProfile.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — checked that the elimination has not emptied the space.  The channel acts on the
  `k`-th layer unit by `log(r^k a)`, so its norm is at least that for every layer below the tower
  height, and the norms therefore diverge with the height.  So the one surviving class — channel
  families whose norms grow with the scale — contains the corpus's own conductor tower, and the no-go
  chain constrains the weld without refuting it.  A no-go over an empty class would have asserted
  nothing; this one does not.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninLogShellChannelGrowth.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelAnnulusBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionBlowUpRequirement.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellLayerProjections.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelNormIdentity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketBandGapFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUp.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUpInstance.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelUpperBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionRateTest.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeCounting.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOrthonormalCompactVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeBandEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDilatedShellModeSupport.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellCellGeometry.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledAnnulusProfile.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — extended from scalars to operators: pairing the source packets against any *fixed*
  bounded operator is bounded above, because the packet energy is uniform in the frequency, so no
  fixed channel restores the floor — the concrete Burnol conductor at one aperture and one tower
  height included.  The surviving completion must be a channel family whose norms diverge with the
  scale.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninFixedChannelNoFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLogShellChannelGrowth.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelAnnulusBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionBlowUpRequirement.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellLayerProjections.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelNormIdentity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketBandGapFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUp.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUpInstance.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelUpperBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionRateTest.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeCounting.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOrthonormalCompactVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeBandEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDilatedShellModeSupport.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellCellGeometry.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledAnnulusProfile.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — applied to the actual Burnol term: it is `log(b/a)`, one constant per scale, so the
  completed channel is unbounded below at every strict flag.  Any completion that restores the
  floor must tend to infinity along the scales.  The scalar-counterterm form of the weld is closed;
  the regularized pairing is what remains.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninBurnolCompletionNoFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFixedChannelNoFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLogShellChannelGrowth.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelAnnulusBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionBlowUpRequirement.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellLayerProjections.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelNormIdentity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketBandGapFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUp.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUpInstance.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelUpperBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionRateTest.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeCounting.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOrthonormalCompactVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeBandEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDilatedShellModeSupport.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellCellGeometry.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledAnnulusProfile.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — **the coupling energy is unbounded, and that closes the bounded completion class.**
  Cutting the aperture window into `N` disjoint annuli gives `N` exactly orthogonal packets; the
  coupling carries each to its own dilate without losing norm, so after normalisation the coupling
  asymptotically preserves an `N`-element orthonormal family and Hilbert--Schmidt domination gives
  `hsNormSq Z_r > N - 1` at every large scale.  Letting `N` grow,
  `tendsto_hsNormSq_soninApertureCoupling_atTop`: the energy tends to infinity along every clock
  past the crossing threshold.  Through the summability criterion this yields
  `not_bddBelow_soninCompletedPacketValueVar_of_bddAbove` — **no completion bounded above on the
  scales restores the floor, at any strict flag**, not merely on the short flags where the
  aperture logarithm was already below the `1/4` threshold.  A working completion must grow with
  the scale at least as fast as the coupling energy.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninCouplingEnergyGrowth.lean`,
`formal/GaloisForLFunctions/RHTower/SoninBurnolCompletionNoFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFixedChannelNoFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLogShellChannelGrowth.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelAnnulusBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionBlowUpRequirement.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellLayerProjections.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelNormIdentity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketBandGapFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUp.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUpInstance.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelUpperBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionRateTest.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeCounting.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOrthonormalCompactVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeBandEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDilatedShellModeSupport.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellCellGeometry.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledAnnulusProfile.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — both ingredients of the growth argument are now in place.  The transition chain never
  used the packet annulus as such, only two support facts — vanishing inside the inner aperture and
  support inside the outer one — so it restates verbatim for a packet on any sub-annulus of `(b,c)`;
  and packets on disjoint annuli are *exactly* orthogonal, since their supports are disjoint
  pointwise, with no frequency separation or limit needed.  So a subdivision of `(b,c)` into `N`
  sub-annuli gives `N` orthogonal packets, each carried by the coupling to its own dilate at one
  common scale.  What remains is to normalise them and let the `N` limits run simultaneously, which
  with `card_le_hsNormSq_of_norm_apply_eq_one` gives `hsNormSq Z_r >= N` for large `r`.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninSubAnnulusCouplingLimit.lean`,
  `formal/GaloisForLFunctions/RHTower/SoninPacketDisjointOrthogonality.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCouplingEnergyGrowth.lean`,
`formal/GaloisForLFunctions/RHTower/SoninBurnolCompletionNoFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFixedChannelNoFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLogShellChannelGrowth.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelAnnulusBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionBlowUpRequirement.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellLayerProjections.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelNormIdentity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketBandGapFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUp.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUpInstance.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelUpperBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionRateTest.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeCounting.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOrthonormalCompactVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeBandEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDilatedShellModeSupport.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellCellGeometry.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledAnnulusProfile.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — set up the growth question, which is what the summability criterion now turns on.
  `sum_norm_sq_apply_le_hsNormSq` generalises the corpus's one-vector domination to a finite
  orthonormal family, so `N` orthonormal vectors that the coupling does not contract force
  `hsNormSq Z >= N`; and `not_bddBelow_of_tendsto_hsNormSq_atTop` says that if the coupling energy
  grows without bound then no completion bounded above can restore the floor.  What is needed next
  is `N` mutually orthogonal wavepackets that the coupling preserves at one scale — disjoint
  sub-annuli of `(b,c)` are the natural candidates, and that requires the packet chain restated for
  a packet supported in a sub-annulus rather than for the one built on `(b,c)` itself.
  Lean: `formal/GaloisForLFunctions/HTGeometry/HilbertSchmidtDominatesPointwise.lean`,
  `formal/GaloisForLFunctions/RHTower/SoninCompletionSummabilityCriterion.lean`,
`formal/GaloisForLFunctions/RHTower/SoninSubAnnulusCouplingLimit.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketDisjointOrthogonality.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCouplingEnergyGrowth.lean`,
`formal/GaloisForLFunctions/RHTower/SoninBurnolCompletionNoFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFixedChannelNoFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLogShellChannelGrowth.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelAnnulusBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionBlowUpRequirement.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellLayerProjections.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelNormIdentity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketBandGapFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUp.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUpInstance.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelUpperBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionRateTest.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeCounting.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOrthonormalCompactVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeBandEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDilatedShellModeSupport.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellCellGeometry.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledAnnulusProfile.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — the last gate is now an exact summability criterion, for completions of arbitrary
  shape: the completed packet channel is bounded below **iff** the sequence
  `min(contribution - coupling energy, 0)` is summable.  Consequently any completion that restores
  the floor must track the coupling energy asymptotically along the scales.  The underlying
  sequence lemma — finite sums bounded below iff the negative part is summable — is not in mathlib
  and is now corpus-owned.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninCompletionSummabilityCriterion.lean`,
`formal/GaloisForLFunctions/RHTower/SoninSubAnnulusCouplingLimit.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketDisjointOrthogonality.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCouplingEnergyGrowth.lean`,
`formal/GaloisForLFunctions/RHTower/SoninBurnolCompletionNoFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFixedChannelNoFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLogShellChannelGrowth.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelAnnulusBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionBlowUpRequirement.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellLayerProjections.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelNormIdentity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketBandGapFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUp.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUpInstance.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelUpperBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionRateTest.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeCounting.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOrthonormalCompactVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeBandEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDilatedShellModeSupport.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellCellGeometry.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledAnnulusProfile.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — the last gate, for extensive completions, is now a single inequality: contribution
  per scale versus coupling energy per scale.  Above every scale's energy the completed channel is
  bounded below by zero; below the uniform floor `1/4` it is unbounded below.  The aperture
  logarithm sits below the threshold on short flags (`log(6/5) < 1/4`, from `5/4 <= exp(1/4)`), so
  the natural extensive candidate is ruled out at an explicit flag.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninCompletionEnergyThreshold.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionSummabilityCriterion.lean`,
`formal/GaloisForLFunctions/RHTower/SoninSubAnnulusCouplingLimit.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketDisjointOrthogonality.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCouplingEnergyGrowth.lean`,
`formal/GaloisForLFunctions/RHTower/SoninBurnolCompletionNoFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFixedChannelNoFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLogShellChannelGrowth.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelAnnulusBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionBlowUpRequirement.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellLayerProjections.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelNormIdentity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketBandGapFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUp.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUpInstance.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelUpperBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionRateTest.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeCounting.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOrthonormalCompactVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeBandEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDilatedShellModeSupport.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellCellGeometry.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledAnnulusProfile.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — the last gate is now a property of the archimedean side alone.  Since the packet
  channel is unbounded below, any counterterm bounded above on the packet family — packet-dependent
  or not — leaves it unbounded below, so a completion with a lower floor must be unbounded above
  along that family and must exceed every level at some packet.  Also guarded the session's new
  statements at the worked flag `1 < 3/2 < 2 < 3`, so none of them is a no-go over an empty class.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninCompletionUnboundedRequirement.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionEnergyThreshold.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionSummabilityCriterion.lean`,
`formal/GaloisForLFunctions/RHTower/SoninSubAnnulusCouplingLimit.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketDisjointOrthogonality.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCouplingEnergyGrowth.lean`,
`formal/GaloisForLFunctions/RHTower/SoninBurnolCompletionNoFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFixedChannelNoFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLogShellChannelGrowth.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelAnnulusBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionBlowUpRequirement.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellLayerProjections.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelNormIdentity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketBandGapFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUp.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUpInstance.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelUpperBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionRateTest.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeCounting.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOrthonormalCompactVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeBandEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDilatedShellModeSupport.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellCellGeometry.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledAnnulusProfile.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — Theorem G items 1--2 upgraded from *properties* of the glued functional to a
  *characterization* of it.  Directness said the presentation is unique and the restrictions said
  what the value is on each part, but nothing said the extended trace is the only assignment with
  those restrictions.  `existsUnique_soninExtendedTraceOn` now says exactly that, on the set of
  presented operators, and `eq_extendedTrace_of_normalizations` gives the same statement for a
  functional defined on the whole algebra.  The hypotheses are the weakest that can work: read a
  canonical normal state by its logarithmic weight, and absorb one exact correction by the ordinary
  trace.  Note the presented operators are *not* a subspace — window states do not add — so this is
  a gluing statement, not a linear-functional statement, unlike the finite-part analogue on
  `sonin-principal-relative-trace-splitting`.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninExtendedTraceUniqueness.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionUnboundedRequirement.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionEnergyThreshold.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionSummabilityCriterion.lean`,
`formal/GaloisForLFunctions/RHTower/SoninSubAnnulusCouplingLimit.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketDisjointOrthogonality.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCouplingEnergyGrowth.lean`,
`formal/GaloisForLFunctions/RHTower/SoninBurnolCompletionNoFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFixedChannelNoFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLogShellChannelGrowth.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelAnnulusBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionBlowUpRequirement.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellLayerProjections.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelNormIdentity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketBandGapFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUp.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUpInstance.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelUpperBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionRateTest.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeCounting.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOrthonormalCompactVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeBandEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDilatedShellModeSupport.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellCellGeometry.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledAnnulusProfile.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — `(38)`, the card's own terminus, is now a theorem *and* is false.  The explicit
  carrier equation `Q_b D_r (Q_a - Q_b) D_r (Q_b - Q_c) = 0` had never been stated in Lean — only
  its predecessors `(35)`--`(37)` had — so it is now `..._eq_zero_iff_tripleProduct`, derived from
  the compression form of the defect and the nesting absorption `Q_b(1 - Q_c) = Q_b - Q_c`.  With
  the escaping wavepacket it fails at an actual scale, so the defect, always carried by `K_b` by
  `(36)`, is *not* carried by `K_c`.  The "algebra is exhausted" paragraph is answered by its own
  first route: the required vector family exists and is not of physical-support type.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninDefectCarrierEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninExtendedTraceUniqueness.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionUnboundedRequirement.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionEnergyThreshold.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionSummabilityCriterion.lean`,
`formal/GaloisForLFunctions/RHTower/SoninSubAnnulusCouplingLimit.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketDisjointOrthogonality.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCouplingEnergyGrowth.lean`,
`formal/GaloisForLFunctions/RHTower/SoninBurnolCompletionNoFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFixedChannelNoFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLogShellChannelGrowth.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelAnnulusBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionBlowUpRequirement.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellLayerProjections.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelNormIdentity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninPacketBandGapFloor.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUp.lean`,
`formal/GaloisForLFunctions/RHTower/SoninFourierChannelBlowUpInstance.lean`,
`formal/GaloisForLFunctions/RHTower/SoninChannelUpperBound.lean`,
`formal/GaloisForLFunctions/RHTower/SoninCompletionRateTest.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeCounting.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOrthonormalCompactVanishing.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellModeBandEscape.lean`,
`formal/GaloisForLFunctions/RHTower/SoninDilatedShellModeSupport.lean`,
`formal/GaloisForLFunctions/RHTower/SoninShellCellGeometry.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledAnnulusProfile.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledProfileMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketScaling.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketSupport.lean`,
`formal/GaloisForLFunctions/HTGeometry/FourierIntegralDilation.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketDensity.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketFourierL2.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledPacketBandMass.lean`,
`formal/GaloisForLFunctions/RHTower/SoninOneSidedPacket.lean`,
`formal/GaloisForLFunctions/RHTower/SoninLobeBumpFourier.lean`,
`formal/GaloisForLFunctions/RHTower/SoninReferenceProfileDecay.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledBumpTail.lean`,
`formal/GaloisForLFunctions/RHTower/SoninScaledMeanBound.lean`.
- 2026-08-01 — added a worked numerical instance of the whole chain at `1 < 3/2 < 2 < 3`.  Every
  no-go here is stated over a hypothesis class, and a no-go over an empty class asserts nothing;
  the instance module makes non-vacuity checkable at a glance rather than by inspection.
- 2026-08-01 — the strict flag law now comes with an explicit gap: at a suitable clock scale
  refining costs at least `1/4`, since the coupling energy has a uniform floor there.  Strictness
  alone left the loss possibly infinitesimal.
- 2026-08-01 — **the chain law is strictly subadditive.**  The sharpness criterion recorded earlier
  ("equality holds exactly when every coupling of the chain vanishes") is now settled in the
  negative direction: the sibling nonannihilation card supplies an actual flag and scale with a
  nonzero coupling, so `exists_strict_soninApertureResidualTrace_chain` gives a strict `<` in the
  flag law.  Refinement genuinely destroys residual trace; it does not merely redistribute it.
  Lean: `formal/GaloisForLFunctions/RHTower/SoninFlagChainStrict.lean`.
- 2026-08-01 — compression form `(63)`: the coupling is the Sonin-compressed dilation cut between
  two layers of one Sonin space, via the tower absorption `(62)`.  Recorded the dilation-covariance
  trap that would otherwise "prove" `Z = 0`: `U_r K_s` is asymmetric, so only an inclusion holds.
- 2026-08-01 — correction to the previous entry: `(60)` is vacuous.  `M_phys + M_four` is the shell
  product, which is already known to lie in `I_a`, so no congruence-level statement can separate
  `Z` from zero.  Replaced by `(61)`, the exact orthogonality criterion on the two Sonin layers —
  the first formulation of the coupling question free of the ideal and of any approximation.
- 2026-07-31 — both polarized halves proved nonzero, not just their sum; the Fourier half needs no
  involution step because its image is compactly supported outright.
- 2026-07-31 — Theorem S: the four mixed blocks do **not** cancel.  Range polarization plus the
  qualitative uncertainty principle splits the sum `(57)`, and the physical half is nonzero `(58)`
  by band-limitedness plus one-interval uncertainty plus a band-shrinking iteration that makes the
  dilation sum injective on a Fourier annulus.  Consequence `(60)`: `Z = 0` would force the four
  named time-band blocks into the relative ideal, so the coupling problem is now a single explicit
  ideal-membership question with no Sonin projection left in it.

- 2026-07-31 — time-band nonvanishing proved from the corpus's rectangle-area formula, so the four
  blocks carrying the coupling are individually nonzero and of strictly different sizes.  This is
  the input a non-cancellation argument needs; it does not by itself exclude cancellation.
- 2026-07-31 — exact mixed-term form: the like-polarization terms vanish identically, so the shell
  product equals the sum of exactly four time-band blocks and the vanishing question is whether
  those four cancel.  Each is individually nonzero by analyticity of band-limited functions, which
  is evidence against vanishing without deciding it.
- 2026-07-31 — the aperture layer itself given an extended-trace reading, with principal value the
  aperture cocycle.  Previously only the defect had one; the layer is more primitive and carries the
  same cocycle independently of any prime scale, so the cocycle belongs to the aperture pair rather
  than to the source data.
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

