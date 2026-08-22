# The Mertens conormal extends through a graded logarithmic differential corona

- **ID:** `mertens-logarithmic-corona-differential-tower`
- **Stage:** 2-fully-proven/not_new_scientific_knowledge
- **Type:** THEOREM (paper) / SOURCE-OPERATOR EXTENSION / GRADED CORONA / RH BRIDGE
- **Scientific status:** `[PROVED HERE] [FORMALIZED] [BRIDGE]
  [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parents:**
  - `mertens-corona-shift-conormal.md`
  - `logarithmic-marcinkiewicz-prime-tail-boundary.md`
  - `../../1-in-progress/hypertranscendental-mackey-corona-field.md`
  - `../../1-in-progress/calibrated-gamma-mertens-zero-orbit-comparison-rh.md`
- **Statement:** The degree-zero Mertens conormal cannot carry multiplication by `log p` on one
  fixed Marcinkiewicz space.  Its exact positive replacement is a graded source module.  The
  degree-`k` class is represented by `p |-> (log p)^k`, the logarithmic clock raises degree, and
  every positive Euler translation vanishes in every corona grade.  The time-one Gamma--Meixner
  transform identifies this module with the complete differentiated polar tower at the source
  boundary.

## 1. Graded prime-tail spaces

For `k>=0`, define

```text
||b||_(M,k)
 = sup_(X>=2) 1/(log X)^(k+1)
     sum_(p<=X) (log p)/p |b_p|.                         (1)
```

Let `M_k` be the corresponding weighted Marcinkiewicz space and `M_(k,0)` the closure of finite
support.  Equivalently,

```text
b in M_(k,0)
 iff lim_(Y->infinity) sup_(X>Y) 1/(log X)^(k+1)
       sum_(Y<p<=X) (log p)/p |b_p| = 0.                 (2)
```

The equivalence is immediate: the displayed supremum is the norm of the tail after deleting the
coordinates `p<=Y`.  The usual coordinatewise-Cauchy/Fatou argument also shows that every `M_k`
is complete.

Put

```text
u_k(p)=(log p)^k,
E_k=C u_k+M_(k,0).                                       (3)
```

### Theorem 1: exact corona normalization `[PROVED]`

Prime-number-theorem partial summation gives, for every fixed `k>=0`,

```text
A_k(X):=sum_(p<=X) (log p)^(k+1)/p
       =(log X)^(k+1)/(k+1)+C_k+o(1).                   (4)
```

For `k=0` this is Mertens' first theorem.  For general `k`, write

```text
A_k(X)=integral_(2-)^X (log t)^k/t d theta(t),
theta(X)=sum_(p<=X) log p.                               (5)
```

The classical zero-free-region estimate

```text
theta(X)=X+O(X exp(-a sqrt(log X)))                      (6)
```

makes the error integral convergent after `v=log t`; the main integral is exactly the leading
term in `(4)`.

Equations `(2)` and `(4)` imply

```text
u_k in M_k\M_(k,0),
||[u_k]||_(M_k/M_(k,0))=1/(k+1).                        (7)
```

For the upper bound in `(7)`, delete the primes through `Y`; `(4)` uniformly bounds every later
tail by `1/(k+1)+o_Y(1)`.  For the lower bound, every element of `M_(k,0)` has normalized absolute
prefix mass tending to zero, whereas the normalized mass of `u_k` tends to `1/(k+1)`.

Every element of `E_k` therefore has a unique decomposition

```text
x=c u_k+b,       b in M_(k,0).                           (8)
```

Define

```text
q_k(c u_k+b)=c.                                          (9)
```

Then `q_k` is continuous and has exact norm

```text
||q_k||=k+1,                                             (10)
```

because the distance of `c u_k` from `M_(k,0)` is `|c|/(k+1)`.

## 2. Exact logarithmic-clock law

Let

```text
(L b)_p=(log p)b_p.                                      (11)
```

For `p<=X`, `log p<=log X`, so

```text
sum_(p<=X) (log p)/p |(L b)_p|
 <=log X sum_(p<=X) (log p)/p |b_p|.                    (12)
```

Consequently

```text
L:M_k -> M_(k+1),       ||L||<=1.                       (13)
```

It preserves finite support and hence sends `M_(k,0)` continuously into `M_(k+1,0)`.  Since

```text
L u_k=u_(k+1),                                           (14)
```

it restricts to `L:E_k->E_(k+1)` and induces the exact conormal law

```text
q_(k+1)L=q_k.                                            (15)
```

Thus the failure of `L one` to lie in `M_0` is not an unstructured unboundedness defect.  It is
exact degree raising in a canonical scale selected by the higher Mertens asymptotics `(4)`.

## 3. Every positive Euler translation dies in every grade

For `h>0`, put

```text
(S_h b)_p=p^(-h)b_p.                                     (16)
```

Let `K=||b||_(M,k)`.  On the dyadic block `2^j<p<=2^(j+1)`,

```text
sum (log p)/p |b_p|p^(-h)
 <=K ((j+1)log 2)^(k+1) 2^(-jh).                        (17)
```

The right side is summable in `j`.  Hence

```text
sum_p (log p)/p |(S_h b)_p|<infinity,                   (18)
```

continuously in `b`.  Weighted absolute summability implies membership in `M_(k,0)`, by deleting
a finite head and bounding the remaining `M_k` norm by its weighted `l^1` tail divided by
`(log 2)^(k+1)`.  Therefore

```text
S_h:M_k -> M_(k,0),
q_k S_h=0.                                               (19)
```

Moreover `L S_h=S_h L`.  Hence, for every `r>=0`,

```text
L^r S_h(E_k) subset M_(k+r,0),
q_(k+r)L^r S_h=0.                                       (20)
```

Equation `(20)` is a complete finite differential-translation no-go: no finite number of
prime-log derivatives applied before or after a positive horizontal shift can promote a shifted
right-half character into the nonzero source corona.

## 4. The positive source-operator module

Form the graded quotient line

```text
Q_k=E_k/M_(k,0)=C[u_k]
```

and the algebraic direct sum `Q_gr=direct_sum_(k>=0) Q_k`.  Equations `(14)`--`(20)` give

```text
Q_gr=C[L][u_0],
L^k[u_0]=[u_k],
S_h Q_gr=0                    for every h>0.              (21)
```

Thus the source boundary is cyclic over the logarithmic differential algebra, with one
one-dimensional symbol in every degree.  The positive translation ideal acts by zero.  More
generally, for every finite operator stencil

```text
A=sum_(r,h) a_(r,h)L^r S_h,       h>=0,                  (22)
```

its action on `Q_gr` is precisely its `h=0` part.  The quotient is the augmentation module which
retains the boundary differential jet and discards every strictly translated source.

This is the first nontrivial part of the requested completed Euler--Gamma source-operator
extension: it handles the complete finite algebra generated by horizontal Euler translations and
the logarithmic clock.  It does not yet include reflected analytic continuation or the global
Gamma framing.

## 5. Time-one Gamma--Meixner polar realization

The exact time-one weight is

```text
w_1(p)=cosh(2log p)^(-1/2)
      =sqrt(2)p^(-1)(1+p^(-4))^(-1/2).                  (23)
```

For `Re(s)>0`, define

```text
F_k(s)=sum_p w_1(p)(log p)^(k+1)p^(-s).                 (24)
```

Let `P(s)=sum_p p^(-s)` be the prime zeta function.  The difference between `(24)` and

```text
sqrt(2)(-1)^(k+1)P^((k+1))(1+s)                         (25)
```

is holomorphic on `Re(s)>-4`, because the correction in `(23)` is `O(p^(-5))`.  On a branch near
`s=0`, Moebius inversion of `P` gives

```text
P(1+s)=-log s+H(s),                                     (26)
```

where `H` is holomorphic for `|s|<1/2`.  Differentiating `(26)` `k+1` times yields the exact
principal part

```text
F_k(s)=sqrt(2) k!/s^(k+1)+G_k(s),                        (27)
```

with `G_k` holomorphic for `|s|<1/2`.  There are no lower polar orders.

The transform intertwines the source operators exactly:

```text
F_(L b)(s)=-d/ds F_b(s),
F_(S_h b)(s)=F_b(s+h).                                   (28)
```

Consequently `(21)` maps to the full differentiated Mertens polar tower, and the degree-`k`
conormal maps to the principal part `sqrt(2)k!/s^(k+1)`.  Under local reflection `s |-> -s`, this
principal symbol has parity

```text
s^(-(k+1)) |-> (-1)^(k+1)s^(-(k+1)).                    (29)
```

Equation `(29)` is a genuine reflected symbol on the polar quotient.  It is not yet an involution
on the completed Euler coefficient module.

## 6. Collision with the actual completed-Xi source

The Lean-formalized even-shift identity for `xi'/xi` exposes the coefficient filter

```text
Lambda(n)(1-n^(-2)).                                    (30)
```

On the degree-one prime face, `(30)` is exactly the source defect `I-S_2`.  Equations `(19)` and
`(21)` give

```text
q_k(I-S_2)=q_k                                           (31)
```

in every logarithmic grade.  Thus the rationally renormalized completed-Xi `+2` defect and the
Gamma unit-translation conormal have the same augmentation law at the source boundary.  This is
an exact pre-divisor common boundary symbol, not a fitted zero-space identification.

The all-prime-power correction does not alter the corona class: the existing critical all-grade
Euler-ray theorem proves that every grade `m>=2` lies in the vanishing-tail layer.  Hence `(31)` is
the complete critical Euler source symbol of the formalized Xi shift exposure, not merely a
degree-one truncation artifact.

## 7. No-go and nontrivial positive successor

### One-space no-go

`L one=(log p)` is outside the original `M_log`.  Therefore the rank-one coefficient conormal
cannot be a module over the logarithmic clock in one Banach space.

**Positive successor:** the canonical graded spaces `(1)` make `L` a contraction between adjacent
grades and produce the cyclic module `(21)`.

### Finite differential repair no-go

Equation `(20)` proves that no finite prime-log differential repair makes a positive shift visible
in the corona.

**Positive successor:** the complete boundary differential jet survives and is identified with
the Gamma polar tower by `(27)`--`(28)`.

### Raw common-cocycle no-go

Sharing the augmentation law `(31)` does not make the Euler and Gamma analytic cocycles equal.
The completed logarithmic derivative has a hypertranscendental translation defect, while the
digamma cocycle is rational.  Treating `(31)` as equality of analytic fibres would be false.

**Positive successor:** `(31)` gives an exact common *boundary symbol*.  The remaining comparison
must lift that symbol through a singular, reflected completion; it cannot be a finite
differential-translation stencil.

## 8. RH consequence and exact remaining core

This theorem closes the finite Euler differential-algebra part of the source-operator-extension
gate in `calibrated-gamma-mertens-zero-orbit-comparison-rh.md`.  It does not close the gate itself.

The remaining object must be a reflected singular completion `Lambda_zeta` satisfying all of:

1. its associated graded module is `(21)`;
2. its polar symbol is `(27)` and its Gamma transgression is the existing factorial rank-one
   boundary current;
3. it contains the formalized completed-Xi shift defect with augmentation law `(31)`;
4. it preserves the two affine support locations `-rho` and `conjugate(rho)-1` under the
   zero-orbit comparison;
5. it is defined before a zero is inserted.

Because all finite differential-translation repairs die by `(20)`, the smallest live candidate is
a boundary-supported hyperfunction or local-cohomology completion in the horizontal translation
parameter, paired with the Gamma analytic framing.  Constructing that object and proving its
zero-orbit affine-support faithfulness remains `[OPEN CORE]`.

## 9. Parent-theory and novelty verdict

- Weighted Marcinkiewicz/Cesaro quotients and their order-continuous ideals are established Banach
  lattice theory.
- Equation `(4)` is classical prime-number-theorem partial summation.
- The expansion `(26)` and its higher coefficients are explicitly studied in Artur Kawalec,
  *On the series expansion of the prime zeta function about s=1 and its coefficients*, 2026,
  `https://arxiv.org/abs/2603.21535`.
- A point-supported distribution being a finite sum of delta derivatives is classical
  distribution theory; this is the parent model for the boundary-jet interpretation of `(21)`.

The exact graded prime-source package is useful project architecture, but it is mechanically
assembled from these parents.  It is therefore `[BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`.  The
candidate-new and RH-significant content begins only with the reflected singular completion and
its source-defined affine-support-faithful Gamma comparison.

## Lean status (2026-08-22)

`formal/GaloisForLFunctions/RHTower/MertensGradedCoronaTower.lean`, wired into
`GaloisForLFunctions.RHTower`, `lake build`-green:

- `gradedMarcinkiewiczQuotient`, `MemGradedMarcinkiewiczLayer`, `MemGradedVanishingTailLayer`,
  `gradeSource`, `logClock` — equations `(1)`--`(3)`, `(11)`, with
  `memGradedMarcinkiewiczLayer_zero` / `memGradedVanishingTailLayer_zero` identifying the grade-0
  spaces with the corpus `M_log`, `M_0`.
- `primeLogMass_gradeSource`, `tendsto_gradedMarcinkiewiczQuotient_gradeSource`,
  `memGradedMarcinkiewiczLayer_gradeSource`,
  `tendsto_gradedMarcinkiewiczQuotient_gradeSource_tail`,
  `not_memGradedVanishingTailLayer_gradeSource` — equations `(4)`, `(7)`, from the corpus higher
  Mertens theorem `RHTower.tendsto_primeLogPowSum_sub`.
- `gradedPrimeMean`, `abs_gradedPrimeMean_le`,
  `tendsto_gradedPrimeMean_zero_of_gradedVanishingTail`,
  `tendsto_gradedPrimeMean_gradeSource`,
  `tendsto_gradedPrimeMean_of_gradedVanishingTail` — equations `(8)`--`(10)`.
- `gradedMarcinkiewiczQuotient_logClock_le`, `memGradedMarcinkiewiczLayer_logClock`,
  `memGradedVanishingTailLayer_logClock`, `logClock_gradeSource`,
  `tendsto_gradedPrimeMean_logClock` — equations `(12)`--`(15)`.
- `sum_primeUnitTranslation_graded_block_le`,
  `memCriticalSummableLayer_primeUnitTranslation_graded`,
  `memGradedVanishingTailLayer_primeUnitTranslation`,
  `tendsto_gradedPrimeMean_primeUnitTranslation_zero`,
  `memGradedVanishingTailLayer_logClock_iterate`,
  `tendsto_gradedPrimeMean_logClock_iterate_primeUnitTranslation` — equations `(16)`--`(20)`.
- `logClock_iterate_gradeSource` — equation `(21)`.
- `tendsto_gradedPrimeMean_gradedSourceDefect`, `mertensGradedCoronaTower` — equation `(31)` and
  the packaged tower.

**§5 is now formalized.**  `formal/GaloisForLFunctions/RHTower/PrimeLogPowZetaAbelPole.lean` and
`formal/GaloisForLFunctions/RHTower/MertensGradedCoronaPolarTower.lean`, both wired into
`GaloisForLFunctions.RHTower`, `lake build`-green and axiom-audited to
`[propext, Classical.choice, Quot.sound]`:

- `logPowMajorantConst`, `logAffine_pow_le_majorant`, `log_pow_le_majorant`,
  `integrableOn_rpow_mul_log_pow_Ioi_one`, `integrableOn_rpow_mul_logAffine_pow_Ioi_one`,
  `logPowRpowPrimitive`, `hasDerivAt_logPowRpowPrimitive`, `tendsto_logPowRpowPrimitive`,
  `integral_rpow_mul_log_pow_Ioi_one` — the elementary logarithmic power integral
  `∫_1^∞ t^{-δ-1}(log t)^m dt = m!/δ^{m+1}`, by the recursion `I_m = (m/δ) I_{m-1}`.
- `weightedDirichlet_eq_abel_integral_pow` (in `PrimeLogZetaAbelPole.lean`, with the previous
  logarithmically bounded version now a corollary) — the Abel representation of an arithmetic
  Dirichlet series whose partial sums grow like any fixed power of `log`.
- `gradedMertensError`, `tendsto_gradedMertensError`, `exists_gradedMertensError_bound`,
  `exists_primeLogPowSum_bound`, `summable_primeLogPowWeight_rpow`,
  `integrableOn_rpow_mul_gradedFloor`, `gradedPrimeLogZeta`,
  `gradedPrimeLogZeta_eq_abel_integral`, `gradedAbelIntegral_eq`, `abs_gradedErrorIntegral_le` —
  the graded Abel decomposition against the higher Mertens theorem.
- `tendsto_gradedPrimeLogZeta` — **the graded prime-zeta Abel pole**
  `lim_{δ ↓ 0} δ^{k+1} ∑_p (log p)^{k+1} p^{-1-δ} = k!`.
- `abelWeighted_gradeSource`, `timeOnePrimeLaplace_gradeSource_eq`,
  `summable_timeOneCorrection_primeLogPowWeight`, `abs_gradedTimeOneDefect_le` — equations
  `(23)`--`(24)`, on top of the corpus factorization `RHTower.meixnerShape_factorization`.
- `tendsto_gradedTimeOnePrimeLaplace` — equations `(25)`--`(27)`:
  `lim_{s ↓ 0} s^{k+1} F_k(s) = √2 · k!`, no lower polar orders.
- `hasDerivAt_timeOnePrimeLaplace_gradeSource` and `timeOnePrimeLaplace_gradeSource_shift` —
  equation `(28)`: the logarithmic clock is minus the boundary derivative and a positive Euler
  translation is a shift of `s`.
- `principalPart_reflection` — equation `(29)`, the parity of the principal symbol.

## Gates

- [x] exact graded source spaces constructed
- [x] higher Mertens source classes and quotient norms proved
- [x] logarithmic clock proved to raise degree continuously
- [x] every positive translation proved corona-zero in every grade
- [x] complete finite differential-translation no-go proved
- [x] cyclic graded source-operator module identified
- [x] full time-one differentiated polar tower identified
- [x] actual completed-Xi even-shift augmentation symbol identified
- [x] every no-go given a nontrivial positive successor
- [x] parent-theory and novelty gate run
- [x] §1--§4 and §6 formalized unconditionally in Lean 4 (no wrapper shell: the higher Mertens
  theorem is a corpus theorem)
- [x] §5 formalized: the graded prime-zeta Abel pole `s^{k+1} ∑_p (log p)^{k+1} p^{-1-s} → k!`
- [ ] construct the reflected singular completion
- [ ] identify its full Gamma transgression
- [ ] prove zero-orbit affine-support faithfulness
- [ ] prove RH
