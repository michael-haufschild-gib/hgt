# Sonin residual Hilbert--Schmidt escape and moment-curve properness

- **ID:** `sonin-residual-hs-escape-and-moment-curve-properness`
- **Stage:** 1-in-progress
- **Type:** `[SOURCE THEOREM] [CLUSTER-SET CLASSIFICATION] [NOVELTY UNVERIFIED]`
- **Parent:** `sonin-prime-arch-finite-moment-transfer.md`
- **RH status:** not an RH proof; collapses the live finite-block closure core to an exact
  fixed-aperture identity, conditional only on the continuity package isolated below.

## Frontier statement

Let

```text
P_a = physical cutoff on [-a,a],
F_a = Fourier-conjugate cutoff on [-a,a],
Q_a = projection onto K_a = ker(P_a) intersect ker(F_a),
Q0_a = 1-P_a-F_a,
C_a = Q_a-Q0_a,
D_p = U_p+U_p^(-1),
R_(a,p) = (1-Q_a)D_pQ_a-(1-Q0_a)D_pQ0_a.
```

The repository's weighted all-prime residual is the block direct sum of nonzero scalar multiples
of the `R_(a,p^m)` with `m>=2`.  Its positive energy is `T_a=K_a^*K_a`, and

```text
S_r(a)=Tr(T_a^(r+1)).
```

The proposed source theorem has four parts.

1. For every fixed `p>1`, `a |-> R_(a,p)` is continuous in Hilbert--Schmidt norm on
   `(0,infinity)`.
2. `||R_(a,p)||_HS^2 -> infinity` as `a->infinity`.
3. The all-prime zeroth moment satisfies

   ```text
   S_0(a) -> 0        as a->0+,
   S_0(a) -> infinity as a->infinity.
   ```

   Every `a |-> S_r(a)` is continuous on `(0,infinity)`.
4. Consequently any finite limit of Sonin moment blocks with positive zeroth coordinate is an
   actual finite-aperture value.  In particular,

   ```text
   SoninPrimeArchFiniteMomentClosure
     iff
   exists a>0, forall r,
     soninAllPrimeEnergyMoment a r = normalizedPrimeArchMoment r.
   ```

The reverse implication in part 4 is immediate.  The forward implication uses the already
formalized cofinal-section theorem to obtain one aperture sequence converging in every moment.
Parts 1--3 trap that sequence in a compact aperture interval; a convergent subsequence and
continuity give one exact aperture matching all orders.

## Existing inputs

The following are already proved in the corpus.

1. `||C_a||_HS^2=8a^2`.
2. Each `R_(a,p)` is Hilbert--Schmidt and nonzero for `a>0`.
3. Every logarithmic prime-power weight is nonzero and their squared norms are summable.
4. The all-prime block direct sum is Hilbert--Schmidt.
5. `S_0(a)=||K_a||_HS^2`, and the all-prime area estimate gives

   ```text
   S_0(a) <= 128 a^2 sum_(p,k)|w_(p,k)|^2.
   ```

6. `normalizedPrimeArchMoment 0>0`.
7. Finite-block closure is equivalent to one positive aperture sequence converging in every
   moment coordinate.

External input: Burnol, *Two complete and minimal systems associated with the zeros of the
Riemann zeta function*, J. Théorie des Nombres de Bordeaux 16 (2004), Proposition
`denselemma`, proves

```text
closure(union_(b>a) K_b)=K_a.
```

Burnol's proof identifies `K_a^perp=A_a+B_a`, uses closedness of this sum and
`intersection_(b>a)(A_b+B_b)=A_a+B_a`.  This is exactly the one-sided density needed below.

## Paper proof

### 1. Strong continuity of the Sonin projections

The family `K_a` is decreasing.

- If `a_n` increases to `a`, then `intersection_n K_(a_n)=K_a`, since the increasing physical
  and Fourier intervals exhaust `[-a,a]` up to null endpoints.  Monotone convergence of
  orthogonal projections gives `Q_(a_n)->Q_a` strongly.
- If `a_n` decreases to `a`, Burnol's density theorem gives
  `closure(union_n K_(a_n))=K_a`.  The other monotone-projection theorem again gives strong
  convergence.

Every scalar sequence converging to `a` has monotone subsequences on either side.  Hence
`Q_b->Q_a` strongly as `b->a`.  The cutoff projections `P_b,F_b` are strongly continuous by
absolute continuity of the `L2` integral, so `Q0_b` and `C_b` are strongly continuous.

### 2. Hilbert--Schmidt continuity of the correction

Regard Hilbert--Schmidt operators as a Hilbert space.  On a compact positive aperture interval,
the exact identity

```text
||C_b||_HS^2=8b^2
```

gives a uniform Hilbert--Schmidt bound.  Strong operator convergence of `C_b` gives convergence
of all matrix coefficients.  Finite-rank operators are dense in the Hilbert--Schmidt class, so
the uniform bound upgrades matrix-coefficient convergence to weak Hilbert--Schmidt convergence.
As `b->a`, the displayed exact identity also gives
`||C_b||_HS->||C_a||_HS`.  Weak convergence plus convergence of Hilbert-space norms gives

```text
||C_b-C_a||_HS -> 0.
```

### 3. Hilbert--Schmidt continuity of one residual

Use the corpus factorization

```text
R_(a,p)=(1-Q_a)D_p C_a-C_a D_p Q0_a.                  (1)
```

If bounded operators `A_n` and their adjoints converge strongly to `A` and `A^*`, then
left and right multiplication by `A_n` converge on every fixed Hilbert--Schmidt operator in
Hilbert--Schmidt norm.  Apply this standard finite-rank approximation lemma to `(1)`, using
strong continuity and self-adjointness of `Q_a,Q0_a,D_p`, plus Hilbert--Schmidt continuity of
`C_a`.  This proves part 1.

### 4. Large-aperture strong limit

As `a->infinity`, `P_a->1` strongly by monotone convergence of the physical cutoffs, and
`F_a->1` strongly by Fourier conjugacy.  Since `Q_a<=1-P_a`,

```text
Q_a -> 0 strongly,
Q0_a=1-P_a-F_a -> -1 strongly,
C_a=Q_a-Q0_a -> 1 strongly.
```

Substitution in `(1)` gives the exact strong limit

```text
R_(a,p) -> D_p-(-D_p)=2D_p.                            (2)
```

The factor `2` is essential: the true Sonin corner tends strongly to zero, while the formal
complement corner tends to `-2D_p`.

### 5. Hilbert--Schmidt escape

`D_p=U_p+U_p^(-1)` is not Hilbert--Schmidt.  Under logarithmic coordinates, `U_p` is translation
by `log p`.  Choose an infinite orthonormal family of compactly supported translates whose two
`D_p` images remain separated; their image norms are bounded below by one fixed positive
constant.  Hence the Hilbert--Schmidt sum for `D_p` diverges.

Fix `M>0`.  Since `2D_p` is not Hilbert--Schmidt, choose a finite orthonormal family
`e_1,...,e_N` with

```text
sum_i ||2D_p e_i||^2 > 2M.
```

The strong convergence `(2)` makes the corresponding finite sum for `R_(a,p)` exceed `M` for all
large `a`.  Bessel's lower bound for Hilbert--Schmidt norm then gives

```text
||R_(a,p)||_HS^2 >= sum_i ||R_(a,p)e_i||^2 > M.
```

Therefore `||R_(a,p)||_HS^2->infinity`.

### 6. All-prime endpoint coercivity

Fix one retained prime-power block, for example `(2,0)`.  Its logarithmic weight is nonzero.
The all-prime block Hilbert--Schmidt energy dominates this one weighted block, so part 2 gives

```text
S_0(a)=||K_a||_HS^2 -> infinity.
```

At the other endpoint the corpus area bound gives `S_0(a)->0`.

### 7. Continuity of every moment

Each weighted local block is Hilbert--Schmidt continuous.  On a compact aperture interval, the
existing square-summable uniform local bound controls the all-prime tail independently of
aperture.  Finite-block continuity plus uniform tail control gives Hilbert--Schmidt continuity of
`K_a`.

Thus `T_a=K_a^*K_a` is continuous in trace norm.  The local operator-norm ceiling on `K_a` gives
uniform bounds for powers, and the telescoping identity for `T_b^(r+1)-T_a^(r+1)` gives trace-norm
continuity.  Taking traces proves continuity of `S_r`.

### 8. Proper positive-mass cluster classification

Let `a_j>0` and suppose `S_r(a_j)->m_r` for every `r`, with `m_0>0`.  Small-aperture collapse
excludes subsequences tending to zero.  Large-aperture escape excludes unbounded subsequences.
Hence `a_j` is eventually contained in some compact interval `[epsilon,A]`.  A subsequence tends
to `a_*` in that interval, and continuity gives `S_r(a_*)=m_r` for every `r`.

Apply this to the single cofinal aperture sequence already extracted from
`SoninPrimeArchFiniteMomentClosure`, using `normalizedPrimeArchMoment_zero_pos`.

## Hostile audit

1. **Wrong endpoint sign:** direct evaluation of the two corners gives
   `crossBoundary(Q_a,D_p)->0` and `crossBoundary(Q0_a,D_p)->-2D_p`; their difference is
   `2D_p`, not `0` or `D_p`.
2. **Strong limit does not normally force Hilbert--Schmidt norms to diverge:** it does here
   because the limit is non-Hilbert--Schmidt and finite orthonormal lower sums converge
   termwise.  No compactness principle is being used backwards.
3. **A single escaping block suffices:** the all-prime construction is an orthogonal block direct
   sum, so no cancellation can erase one block's Hilbert--Schmidt energy.
4. **Continuity is load-bearing:** strong continuity alone permits trace mass to escape.  The
   exact `8a^2` correction norm is what upgrades the correction to Hilbert--Schmidt continuity.
5. **Right-continuity is not guessed:** it uses Burnol's published density theorem for the
   decreasing Sonine filtration.
6. **No Xi divisor or RH-equivalent measure:** all endpoint and continuity inputs are properties
   of the explicit Sonin/cutoff source.  The target enters only through the positive finite number
   `normalizedPrimeArchMoment 0`.
7. **Scientific boundary:** this does not prove the exact fixed-aperture identity.  It proves that
   no cofinal or boundary schedule can provide it.  Future work must either find one actual
   aperture matching all prime--Gamma moments or retire this block-diagonal closure route.

## Novelty audit

Corpus searches found:

- small-aperture collapse and area bounds;
- exact correction energy `8a^2`;
- finite-aperture residual Hilbert--Schmidt/nonzero theorems;
- the conditional finite-block cluster-to-RH consumer.

They did not find large-aperture strong convergence of the principal-subtracted residual,
Hilbert--Schmidt escape, properness of `S_0`, continuity of the all-prime trace moments, or the
fixed-aperture classification.

Primary-literature searches found Burnol's density theorem and the Connes--Consani Sonin/prolate
trace programme, but no theorem for this logarithmically weighted principal-subtracted
prime-power residual or its trace-moment curve.  External novelty remains provisional until a
broader operator-theory and Sonine/prolate audit is complete.

## Gates

- [x] corpus and failed-route search
- [x] exact source objects and endpoint sign isolated
- [x] paper proof decomposed into named analytic lemmas
- [x] Burnol density input located in primary literature
- [ ] independently hostile-audit every continuity step
- [ ] complete broad literature collision audit
- [ ] promote to 2-fully-proven
- [ ] formalize source theorem and fixed-aperture classification in Lean
- [ ] decide exact fixed-aperture identity or retire block-diagonal Sonin cluster route
