# Wold--Boolean diagonal renormalization mismatch

- **ID:** `wold-boolean-diagonal-renormalization-mismatch`
- **Stage:** 2-fully-proven / not new scientific knowledge
- **Type:** EXACT INFINITY-SCALE NO-GO / POSITIVE SURVIVOR
- **Scientific status:** `[PAPER-PROVED] [PARENT MEASURE THEORY] [NOT RH]`
- **Parents:**
  - `finite-boolean-hochschild-diagonal-cofinal-fracture.md`;
  - `../new_scientific_knowledge/prime-wold-accelerated-type-modular-drift-law.md`;
  - `../../1-in-progress/source-modular-drift-realization-equivalence-law.md`;
  - `../../1-in-progress/polarized-irregular-source-purity-law.md`.

## Statement

The canonical finite Boolean Hochschild diagonal does have a canonical distributional all-prime
limit, but its unique scalar normalization is the Boolean entropy factor
\[
2^{\pi(x)}.
\]
Every scalar Wold/Gamma normalization whose logarithm has any fixed finite power of the reciprocal
Wold boundary volume converges to zero.  In particular, neither a finite-Rees multiplier nor the
first-level essential Gamma gauge \(\exp(C/a_x)\) can renormalize the finite Boolean contractions
into a nonzero all-prime diagonal.

Thus the remaining controlled-totalization problem cannot be solved by multiplying the Boolean
separability diagonal by the Wold first-trace anomaly.  A viable totalization must retain the
Boolean entropy record and the Wold/Gamma modular record as distinct coupled channels.

## 1. Infinite Boolean prime cube

Let
\[
X=\{\pm1\}^{\mathbb P}
\]
with product Haar probability \(\mu\).  For
\[
P_x=\{p:p\le x\},\qquad n_x=|P_x|=\pi(x),
\]
write
\[
D_x(u,v)
=
\mathbf 1_{\{u_p=v_p\ {\rm for\ every}\ p\le x\}}.
\tag{1}
\]
This is the cylinder realization of the finite separability diagonal
\[
D_{P_x}
=2^{-n_x}\sum_{\chi\in\widehat{\{\pm1\}^{P_x}}}
\chi\otimes\overline\chi.
\]
Independence gives
\[
\int_{X\times X}D_x\,d(\mu\otimes\mu)=2^{-n_x}.
\tag{2}
\]

Let
\[
\Delta_\mu(F)=\int_XF(u,u)\,d\mu(u)
\tag{3}
\]
be the diagonal Haar coupling.

## 2. Boolean entropy normalization theorem

`[PAPER-PROVED] [BOOLEAN_DIAGONAL_DISTRIBUTIONAL_LIMIT]`

The probability measures
\[
d\nu_x(u,v)=2^{n_x}D_x(u,v)\,d\mu(u)d\mu(v)
\tag{4}
\]
converge weak-* to \(\Delta_\mu\).

### Proof

Let \(F\) be a continuous cylinder function depending only on a finite prime set \(Q\).  Once
\(Q\subseteq P_x\), the measure in `(4)` is the product Haar law conditioned on equality of the
two \(P_x\)-coordinate packets.  Its \(Q\)-marginal is therefore exactly the diagonal Haar law:
\[
\int_{X\times X}F\,d\nu_x
=
\int_XF(u,u)\,d\mu(u).
\tag{5}
\]
Cylinder functions are uniformly dense in \(C(X\times X)\), while every \(\nu_x\) has mass one.
Equation `(5)` therefore proves weak-* convergence to `(3)`. `QED`

The normalization is forced.  Let \(c_x\ge0\), and suppose
\[
c_xD_x\,\mu\otimes\mu
\overset{*}{\rightharpoonup}\nu
\tag{6}
\]
for a finite measure with nonzero mass.  Testing `(6)` on the constant function one and using
`(2)` gives
\[
c_x2^{-n_x}\longrightarrow\nu(X\times X)>0.
\tag{7}
\]
Hence
\[
c_x
=
\bigl(\nu(X\times X)+o(1)\bigr)2^{n_x}.
\tag{8}
\]
Thus \(2^{\pi(x)}\) is the unique scalar normalization up to a nonzero asymptotic constant.

## 3. Wold/Gamma scalar normalizations vanish

Let
\[
a_x=\prod_{p\le x}(1-p^{-1}).
\tag{9}
\]
Mertens' product theorem and the prime number theorem give
\[
a_x^{-1}=O(\log x),
\qquad
n_x\gg {x\over\log x}.
\tag{10}
\]

`[PAPER-PROVED] [FINITE_WOLD_ORDER_BOOLEAN_DIAGONAL_VANISHING]`

Fix \(K\ge0\).  If \(c_x>0\) satisfies
\[
\log^+c_x=O(a_x^{-K}),
\tag{11}
\]
then
\[
c_xD_x\,\mu\otimes\mu
\overset{*}{\rightharpoonup}0.
\tag{12}
\]

### Proof

Equations `(2)`, `(10)`, and `(11)` give
\[
\log\left(c_x\int D_x\,d(\mu\otimes\mu)\right)
\le
C(\log x)^K-n_x\log2.
\tag{13}
\]
The right side tends to \(-\infty\), because
\[
(\log x)^K=o(x/\log x).
\]
Thus the total masses tend to zero.  Positivity then gives weak-* convergence to the zero
measure. `QED`

This covers:

1. every fixed finite-Rees scalar \(c_x=O(a_x^{-N})\);
2. every fixed first-level essential Gamma gauge
   \[
   c_x=\exp(C/a_x);
   \]
3. every scalar family whose logarithm has one fixed finite Rees order.

The result is stronger than failure of projective-norm convergence.  Even after passing to the
weak-* measure completion, the literal Wold/Gamma scalar record is too small to retain the
Boolean diagonal.

## 4. Accelerated-type location

For
\[
\ell_2(y)=\log(1+\log(1+y)),
\]
Mertens and the prime number theorem give
\[
\boxed{\quad
\lim_{x\to\infty}
a_x\ell_2(2^{n_x})
=e^{-\gamma}.
\quad}
\tag{14}
\]
Indeed,
\[
\ell_2(2^{n_x})
=\log n_x+O(1),
\qquad
\log n_x\sim\log x,
\qquad
a_x\log x\to e^{-\gamma}.
\]

Thus the nonzero distributional Boolean diagonal lives at the saturated accelerated type already
seen in the full Iwahori/Weyl record.  The Wold--Gamma first trace has accelerated type zero.
This is not an accidental mismatch of estimates:
\[
\begin{array}{c|c}
\text{record} & \text{accelerated type}\\ \hline
\text{Wold/Gamma first-trace gauge} & 0\\
\text{nonzero Boolean diagonal measure} & e^{-\gamma}\\
\text{full adelic Iwahori/Weyl joining} & e^{-\gamma}.
\end{array}
\tag{15}
\]

## 5. Consequence for the RH architecture

The proposal
\[
\text{finite Boolean contraction}
\xrightarrow{\text{scalar Wold/Gamma renormalization}}
\text{strict all-prime source diagonal}
\tag{16}
\]
is impossible.  The only nonzero scalar distributional normalization already has the saturated,
nonselective type of the external Weyl joining.

The positive survivor is a two-scale requirement:

```text
Boolean entropy channel:
  retains the full equality/face diagonal and costs 2^(pi(x));

Wold/Gamma modular channel:
  retains vacuum probability, first trace, and centered drift;

viable source totalization:
  couples the channels without scalarizing either one.
```

In particular:

1. replacing the projective tensor completion by measures is insufficient by itself;
2. multiplying the separability diagonal by \(a_x^{-1}\), \(\exp(C/a_x)\), or any fixed
   logarithmic finite-Rees family gives zero;
3. using \(2^{\pi(x)}\) recovers the diagonal coupling but imports the saturated nonselective
   essential height;
4. the missing object must be operator-, correspondence-, or sheaf-valued with a complementary
   Boolean/Iwahori record, while its Wold marginal remains the fixed ordinary-prime modular
   class.

This narrows `XI_CONTROLLED_CUBICAL_HOMOTOPY_BASE_CHANGE`.  The next construction cannot be a
scalar renormalized Hochschild diagonal.  It must identify the Gamma/co-Poisson/Sonin Xi boundary
class inside one genuinely coupled Boolean--Wold totalization and prove that Xi specialization
does not replace the Wold modular marginal by the saturated Boolean/Weyl record.

## 6. Canonical non-scalar survivor: Wold thermofield standard-form vector

There is a canonical way to retain a weighted diagonal without scalar renormalization.  It also
shows exactly what the scalar measure picture forgot.

Let \(P\) be finite, let
\[
\Omega_P=\mathbb N_0^P,
\qquad
\mu_P(\nu)=\prod_{p\in P}(1-p^{-1})p^{-\nu_p},
\tag{17}
\]
and put \(H_P=\ell^2(\Omega_P)\) with counting measure.  In
\(H_P\widehat\otimes_2\overline{H_P}\), define
\[
\Omega_P^{\rm W}
=
\sum_{\nu\in\Omega_P}
\sqrt{\mu_P(\nu)}\,e_\nu\otimes\overline{e_\nu}.
\tag{18}
\]

`[PAPER-PROVED] [WOLD_THERMOFIELD_STANDARD_FORM_VECTOR]`

The vector `(18)` has norm one.  For disjoint finite prime packets,
\[
\Omega_{P\sqcup Q}^{\rm W}
=
\Omega_P^{\rm W}\otimes\Omega_Q^{\rm W}
\tag{19}
\]
under the canonical tensor shuffles.  If \(M_f\) is diagonal multiplication by
\(f\in \ell^\infty(\Omega_P)\), then
\[
(M_f\otimes1)\Omega_P^{\rm W}
=
\left(1\otimes\overline{M_{\bar f}}\right)\Omega_P^{\rm W}.
\tag{20}
\]
Its vector state is the Wold-weighted diagonal coupling:
\[
\left\langle
\Omega_P^{\rm W},
\left(M_f\otimes\overline{M_{\bar g}}\right)\Omega_P^{\rm W}
\right\rangle
=
\sum_{\nu\in\Omega_P}\mu_P(\nu)f(\nu)g(\nu),
\tag{21}
\]
Here the Hilbert inner product is conjugate-linear in the first variable.

### Proof

Equation `(17)` is a probability law, so the squared norm of `(18)` is
\(\sum_\nu\mu_P(\nu)=1\).  Product factorization of \(\mu_P\) gives `(19)` coefficientwise.
Both sides of `(20)` multiply the \(\nu\)-coefficient by \(f(\nu)\).  Expanding the inner
product gives `(21)`. `QED`

The compatible unit vectors `(19)` define a canonical incomplete infinite tensor product
\[
\bigotimes_p
\left(
\ell^2(\mathbb N_0)\widehat\otimes_2
\overline{\ell^2(\mathbb N_0)},
\Omega_{\{p\}}^{\rm W}
\right)
\tag{22}
\]
and a distinguished unit vector \(\Omega_\infty^{\rm W}\).  Thus the Wold-weighted identity
standard-form vector and its diagonal multiplication correspondence have a strict all-prime
Hilbert realization.  No factor
\(2^{\pi(x)}\), \(a_x^{-1}\), or \(\exp(C/a_x)\) appears at vector level.

This statement must not be confused with a Hochschild diagonal.  Equation `(20)` is central only
for the diagonal multiplication algebra.  On the full matrix algebra, `(18)` is a cyclic
purification vector in the standard correspondence, not a separability idempotent and not a
bounded contracting homotopy.  The actual identity bimodule is the correspondence generated by
the left and right actions; the single vector records its Wold state.  Consequently this
construction does not extend the finite Boolean Hochschild contractions through cofinal
completion.

Its scalar diagonal measure is nonuniform.  Relative to
\(\mu_P\otimes\mu_P\), its density is
\[
\sum_{\nu\in\Omega_P}
\mu_P(\nu)^{-1}\mathbf1_{\{\nu\}}\otimes\mathbf1_{\{\nu\}},
\tag{23}
\]
not a scalar multiple of the algebraic Boolean diagonal.  For uniform Boolean weights, `(23)`
reduces to the forced factor \(2^{|P|}D_P\).  Formula `(23)` is the precise non-scalar record
which the failed scalar renormalization omitted.

For a second product law \(\mu_{P,c}\), define the analogous vector
\(\Omega_{P,c}^{\rm W}\).  Its overlap with the critical vector is exactly the finite Hellinger
affinity:
\[
\left\langle\Omega_{P,0}^{\rm W},\Omega_{P,c}^{\rm W}\right\rangle
=
\prod_{p\in P}
\sum_{k\ge0}\sqrt{\mu_{p,0}(k)\mu_{p,c}(k)}.
\tag{24}
\]
Hence the infinite vector belongs to the critical incomplete tensor-product sector exactly when
the Kakutani product is nonzero.  The corpus theorem makes this equivalent to \(c=0\).  Thus
the Hellinger--Rees fracture is literally the sector fracture of the Wold thermofield
correspondence.

This closes one carrier question but not the RH interface:

```text
closed here:
  strict all-prime non-scalar Wold standard-form carrier;

still open:
  lift Gamma/co-Poisson/Sonin continuation into this correspondence and prove
  every Xi top conormal is the source-derived vector/correspondence class,
  rather than a generalized functional in a disjoint sector.
```

The latter statement is exactly where RH strength remains.

## 7. Hostile audit

1. **Not RH.**  No Xi conormal landing or modular-class conservation is proved.
2. **Not a new diagonal theorem.**  Conditional product measures and weak-* convergence to the
   diagonal coupling are parent probability theory.
3. **Not a claim that saturated type is bad.**  Saturated type is necessary to retain the full
   Boolean diagonal distributionally.  It is nonselective only when substituted for the Wold
   modular record.
4. **No arbitrary exhaustion claim.**  The asymptotic comparison uses the canonical ordinary-prime
   exhaustion \(p\le x\).  Sparse packet exhaustions can have different relations between packet
   cardinality and Wold volume.
5. **No positivity producer.**  Positivity is used only to turn vanishing mass into weak-*
   convergence to zero.
6. **No scalar escape.**  Equation `(7)` classifies every positive scalar normalization with a
   nonzero finite measure limit.

## 8. Literature boundary

Finite conditional diagonals, martingale/cylinder convergence, Haar diagonal couplings, canonical
purifications, incomplete infinite tensor products, and uniqueness of scalar normalization by
total mass are standard.  Mertens' theorem and the prime number theorem supply the arithmetic
scale comparison.  No standalone novelty is claimed.

Corpus value is the exact incompatibility between the canonical Boolean Hochschild diagonal and
the literal Wold/Gamma first-trace scale.  It closes scalar essential renormalization as the next
RH construction and forces a genuinely two-record totalization.

## Gates

- [x] finite Boolean diagonal identified as equality-cylinder kernel
- [x] unique nonzero distributional normalization proved
- [x] weak-* diagonal coupling limit proved
- [x] all fixed logarithmic finite-Rees Wold normalizations proved to vanish
- [x] Gamma first-level essential scalar normalization excluded
- [x] accelerated type of Boolean normalization identified
- [x] strict non-scalar Wold thermofield standard-form carrier constructed
- [x] its sector overlap identified with the Hellinger/Kakutani product
- [x] finite labelled Boolean--Sonin history coupling constructed from both reciprocal quotient
  contractions; exact history energy and adjoint-mate fracture proved
- [x] hostile audit and parent-theory status recorded
- [ ] couple the Wold standard-form carrier to the full Boolean Hochschild/Tate totalization
- [ ] attach Gamma/co-Poisson/Sonin comparison
- [ ] prove source-first, multiplicity-faithful Xi conormal landing
- [ ] prove Wold modular marginal conservation
- [ ] RH
- [ ] unconditional Lean formalization after selecting the analytic carrier

## Formalization progress (2026-08-24)

`GaloisForLFunctions.HTGeometry.WoldThermofieldStandardForm` now proves, unconditionally:

- diagonal Hilbert--Schmidt standard-form kernel for every `ℓ²` vector;
- exact Hilbert--Schmidt norm identity;
- bounded left/right diagonal actions, centrality, and exact vector-state formula;
- normalized finite occupation point weights;
- finite occupation thermofield kernel, unit norm, centrality, and exact bounded-observable state;
- canonical disjoint-packet pure-tensor shuffle, including norm, coefficient, kernel, and inner
  product factorization;
- local geometric unit half-densities and exact finite-product Hellinger overlap `(24)`.
- canonical reindexing from finite support to literal `Ω_P = ℕ₀^P`, exact prime probability law
  `(17)`, and literal finite-prime unit/state formulas.
- `GaloisForLFunctions.RHTower.WoldBooleanAcceleratedType` proves the exact PNT logarithmic
  comparison and accelerated limit
  `a_N * ell2 (2 ^ Nat.primeCounting N) -> exp (-EulerGamma)` from `(14)`.
- `GaloisForLFunctions.HTGeometry.FiniteBooleanDiagonalNormalization` proves the finite equality
  cylinder mass `(2)`, exact reporter identity `(5)`, stability after adjoining ignored Boolean
  coordinates, and forced scalar asymptotic `(7)`--`(8)` from total mass.
- `GaloisForLFunctions.HTGeometry.BooleanSoninFullHistory` already supplies the labelled full
  Boolean history contraction, exact distinguished-ray energy, and adjoint-mate fracture.
- `GaloisForLFunctions.HTGeometry.PrimeValuationKakutaniSector` already proves that the twisted and
  critical infinite prime product measures are equivalent exactly at `c = 0`.
- `GaloisForLFunctions.RHTower.WoldBooleanFiniteReesVanishing` proves `(11)`--`(13)` exactly:
  for every eventually positive `c_N` with `log⁺(c_N) = O(a_N⁻ᵋ)` for one fixed `K`,
  `c_N / 2 ^ Nat.primeCounting N → 0`.

Targeted leaf builds pass.  Every new theorem has only `propext`, `Classical.choice`, and
`Quot.sound` in its axiom report.

Card remains Stage 2.  Exact remaining Lean obligations include the infinite
incomplete-tensor-product realization and its vector-sector/Kakutani bridge, cylinder diagonal
weak-* limit for all continuous reporters, and their identification with the card's canonical
Haar diagonal coupling.
