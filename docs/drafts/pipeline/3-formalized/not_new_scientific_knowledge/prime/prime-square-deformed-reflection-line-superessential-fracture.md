# Prime-square deformed reflection-line superessential fracture

- **ID:** `prime-square-deformed-reflection-line-superessential-fracture`
- **Stage:** 3-formalized
- **Type:** EXACT SOURCE-LOCAL THEOREM / NO-GO / POSITIVE SURVIVOR
- **Scientific status:** `[PAPER-PROVED] [FINITE FOURIER PARENT] [NOT RH]`
  `[DIRECT POISSON--WOLD LINE SEWING REFUTED]`
- **Parents:**
  - `prime-square-mobius-fourier-complementary-record-law.md`;
  - `../../1-in-progress/polarized-irregular-source-purity-law.md`;
  - `../../1-in-progress/cofinal-conormal-picard-purity-law.md`.
- **Statement:** The actual prime-square Fourier transform sends a deformed occupation line to its
  reflected line with an exact scalar coefficient whose critical normalization is at least one,
  with equality only at zero radial drift.  Its all-prime product has
  \(\exp(|c|\vartheta(x))\) growth off the critical line, a superessential scale strictly larger
  than the Wold--Gamma first-trace anomaly.  Therefore the missing Poisson--Wold comparison cannot
  be the tensor product of scalar reflected-line compressions.

## 1. Literal deformed occupation line

Fix a prime \(p\).  In the orthonormal valuation-stratum plane
\[
 E_p=\operatorname{span}\{u_p,v_p\}
 \subset\ell^2(\mathbb Z/p^2\mathbb Z)
\]
of `prime-square-mobius-fourier-complementary-record-law.md`, put
\[
 q_{p,c}
 =
 \frac{\sqrt p\,u_p+p^c v_p}{\sqrt{p+p^{2c}}},
 \qquad c\in\mathbb R.                                    \tag{1}
\]
This is the positive two-stratum compression of the deformed valuation natural-cone vector.
Reflection sends \(c\) to \(-c\).

The literal unitary additive Fourier transform satisfies
\[
\begin{aligned}
 {\cal F}_pu_p
 &=\sqrt{\frac{p-1}{p}}\,w_p-\frac1{\sqrt p}v_p,\\
 {\cal F}_pv_p
 &=-\frac1{\sqrt p}u_p+\frac{p-1}{p}v_p
   +\frac{\sqrt{p-1}}p w_p.                              \tag{2}
\end{aligned}
\]

## 2. Exact reflected-line coefficient

`[PROVED HERE]`

Put \(r=p^c\).  Substitution of `(2)` into `(1)` gives
\[
 {\cal F}_pq_{p,c}
 =
 \frac{
  -r p^{-1/2}u_p+
  \left(-1+r\frac{p-1}{p}\right)v_p+
  \sqrt{p-1}\left(1+\frac rp\right)w_p
 }{\sqrt{p+r^2}}.
 \tag{3}
\]
Taking the scalar product with \(q_{p,-c}\) yields
\[
 \boxed{
 \alpha_p(c)
 :=
 \langle q_{p,-c},{\cal F}_pq_{p,c}\rangle
 =
 \frac{\frac{p-1}{p}-(p^c+p^{-c})}
 {\sqrt{(p+p^{2c})(p+p^{-2c})}}.
 }
 \tag{4}
\]
At the critical parameter,
\[
 \alpha_p(0)=-\frac1p,                                    \tag{5}
\]
recovering the transverse eigenvalue of the undeformed Fourier compression.

Normalize by this source-fixed critical coefficient:
\[
 \beta_p(c)
 :=
 \frac{\alpha_p(c)}{\alpha_p(0)}
 =
 \frac{p(p^c+p^{-c})-(p-1)}
 {\sqrt{(p+p^{2c})(p+p^{-2c})}}.
 \tag{6}
\]

## 3. Sharp local criticality law

`[PROVED HERE]`

For \(r>0\), put \(x=r+r^{-1}\ge2\).  The numerator and squared denominator in `(6)` are
\[
 N=p x-(p-1),\qquad
 D^2=(p+r^2)(p+r^{-2}).
\]
Direct expansion gives the exact identity
\[
 \boxed{
 N^2-D^2
 =
 p(p-1)x(x-2).
 }
 \tag{7}
\]
Since \(p>1\), equation `(7)` proves
\[
 \boxed{
 \beta_p(c)\ge1,
 \qquad
 \beta_p(c)=1\Longleftrightarrow c=0.
 }
 \tag{8}
\]
The equality condition uses \(r+r^{-1}=2\Longleftrightarrow r=1\), and
\(p^c=1\Longleftrightarrow c=0\).

Equation `(8)` is a genuine local critical-line reporter.  It is not a proof-producing
contraction: dividing a unitary matrix coefficient by \(-1/p\) destroys contractivity.

## 4. Cofinal type of the scalar compression

Let \(0<|c|<1/2\), \(d=|c|\), and
\[
 B_x(c)=\prod_{p\le x}\beta_p(c),
 \qquad
 \vartheta(x)=\sum_{p\le x}\log p.                        \tag{9}
\]
Because `(6)` is invariant under \(c\mapsto-c\), assume \(c=d>0\).  Then
\[
 \frac{\beta_p(c)}{p^d}\longrightarrow1                  \tag{10}
\]
as \(p\to\infty\): the numerator in `(6)` is asymptotic to \(p^{1+d}\), while
\[
 \sqrt{(p+p^{2d})(p+p^{-2d})}\sim p
\]
because \(2d<1\).  Hence
\[
 \frac{\log\beta_p(c)}{\log p}\longrightarrow d.
 \tag{11}
\]
Weighted Cesàro summation over the primes gives
\[
 \boxed{
 \lim_{x\to\infty}
 \frac{\log B_x(c)}{\vartheta(x)}
 =
 |c|.
 }
 \tag{12}
\]
No prime number theorem is needed for `(12)` beyond
\(\vartheta(x)\to\infty\): apply the pointwise estimate from `(11)` to the positive weights
\(\log p\), with the finitely many initial primes negligible.

Thus the critical-normalized scalar line comparison has exact exponential type
\[
 B_x(c)=\exp\bigl((|c|+o(1))\vartheta(x)\bigr).            \tag{13}
\]

## 5. Two distinct essential scales

The ordinary-prime Wold boundary coordinate is
\[
 a_x=\prod_{p\le x}(1-p^{-1})\asymp(\log x)^{-1}.          \tag{14}
\]
Every fixed finite Rees power has logarithm
\[
 O(\log a_x^{-1})=O(\log\log x).                          \tag{15}
\]
The reflected Wold--Gamma anomaly has logarithm
\[
 \log|\exp(2t/a_x)|
 =
 \frac{2\operatorname{Re}t}{a_x}
 =
 O_t(\log x).                                             \tag{16}
\]
By contrast, the prime-square scalar compression has logarithm
\[
 \log B_x(c)
 =
 (|c|+o(1))\vartheta(x)
 \sim |c|x,                                               \tag{17}
\]
where the final asymptotic is the classical prime number theorem.

Relative to \(a_x\), `(16)` is essential but `(17)` is superessential.  In the rough coordinate
\(a_x^{-1}\asymp\log x\), the two levels are
\[
 \exp(O(a_x^{-1}))
 \quad\hbox{versus}\quad
 \exp\!\bigl(\exp((1+o(1))a_x^{-1})\bigr).                \tag{18}
\]

## 6. No-go and positive survivor

`[NO-GO]` The proposed source metric identity in
`polarized-irregular-source-purity-law.md` cannot be built by:

1. projecting each literal prime-square Fourier clock onto the reflected deformed occupation
   line;
2. dividing by its critical coefficient \(-1/p\); and
3. tensoring those scalar maps over the primes.

The resulting metric transition has the superessential rate `(13)`, whereas the exact
Wold--Gamma determinant torsor has the strictly smaller first-trace rate `(16)`.  Their quotient
is not bi-finite-Rees and cannot be hidden in the proposed moderate remainder.

`[POSITIVE SURVIVOR]` The source contains two successive infinity phenomena:

```text
primewise line compression:
  superessential orthogonality catastrophe exp(|c| theta(x));

full continuation--record correspondence:
  unitary before scalarization and therefore cancels that catastrophe;

Gamma/Wold determinant torsor:
  residual first-trace Stokes anomaly exp(2t/a_x).
```

Consequently the full three-channel prime-square Fourier correspondence, including leakage, must
be assembled before taking the determinant/metric line.  Only after that conservative joining
can the single-exponential Wold--Gamma anomaly be compared with additive Poisson unitarity.

This is a sharper requirement than “retain a complementary record.”  The record must cancel the
entire \(\vartheta(x)\)-scale direction loss while preserving the smaller \(a_x^{-1}\)-scale odd
first trace.  A construction which scalarizes before this cancellation is mathematically
incapable of proving the desired Stokes metric identity.

## 7. Hostile audit

1. **The local inequality is only a reporter.**  No source theorem gives
   \(\beta_p(c)\le1\); assuming such contractivity would force \(c=0\) by `(8)` and merely insert
   the desired conclusion.
2. **Full Fourier unitarity is also insufficient.**  It conserves the complete continuation and
   leakage record for every \(c\).  Conservation alone does not make the reflected line
   saturated.
3. **Finite clocks retain off-line zeros.**  Finite Fourier self-duality cannot select the
   critical line.
4. **The scale mismatch is source-specific.**  It uses the actual \(-1/p\) Fourier compression
   and the ordinary-prime Wold volume.  It is not a generic generalized-prime positivity
   argument.
5. **No RH claim.**  The remaining theorem is a moving, all-prime, source-calibrated
   continuation--record joining followed by strict Xi conormal landing.

## 8. Novelty and Lean status

Equations `(4)`--`(8)` are elementary consequences of the already-known finite Fourier matrix.
Equation `(12)` is an elementary weighted product consequence.  Their conjunction with the
Wold--Gamma scale identifies a new corpus no-go, but no standalone external novelty is claimed.

The algebraic identity `(7)` is suitable for a small unconditional Lean theorem.  A Lean wrapper
which defines only \(N\) and \(D^2\) would be too weak: formalization is justified only if it also
contains the actual reflected-line coefficient derived from the finite Fourier clock.  That
source-linked matrix interface is not yet present in the formal tree, so formalization is
deferred rather than replacing the analytic comparison by scalar algebra.

## Gates

- [x] literal deformed occupation line fixed
- [x] exact reflected Fourier coefficient proved
- [x] critical normalization and equality locus proved
- [x] cofinal product type proved
- [x] Wold--Gamma scale comparison proved
- [x] direct scalar line-sewing route retired
- [x] strongest positive survivor extracted
- [x] formalize only after actual prime-square Fourier carrier interface exists (the interface
  is now in the formal tree; see the stage-3 section below)
- [ ] construct full continuation--record joining at the \(\vartheta(x)\) scale
- [ ] identify residual first-trace metric anomaly on the joined source
- [ ] land every Xi conormal jet strictly
- [ ] RH

## 2026-07-30 successor correction

The phrase “finite-order record” in the previous successor is too restrictive after the
all-orders-flat operator theorem.  The actual reflected Wold irregular sector can be joined only
by an essential or non-operator correspondence.

The growth escape is nevertheless not unlimited.  The ordinary-prime product-Poisson
representations of reflected off-line parameters are disjoint.  Hence no nonzero **closed
source-linear** all-prime joining exists between them, even if its norm is superessential.  Any
closed off-line joining must retune the source algebra action; any untwisted joining must become a
nonclosable or multivalued relation.

The corrected positive successor is therefore:

```text
full continuation--record cancellation of the theta(x)-scale catastrophe
  -> possibly essential closed round-trip graph
  -> fixed ordinary-prime source-linearity
  -> strict Xi conormal landing.
```

The last three clauses force the critical line by
`source-linear-essential-superselection-no-sewing.md`.  No finite-order or finite-Rees bound is
required.

## 2026-08-19 — unconditional Lean formalization (stage 3)

Three modules carry the card, all axiom-clean (`propext, Classical.choice, Quot.sound`):
`formal/GaloisForLFunctions/RHTower/PrimeSquareFourierStrata.lean`,
`formal/GaloisForLFunctions/RHTower/PrimeSquareDeformedReflectionType.lean`,
`formal/GaloisForLFunctions/RHTower/PrimeSquareSuperessentialScale.lean`.

**The literal finite Fourier clock** (the source-linked matrix interface the card asked for)

| Card item | Lean declaration |
|---|---|
| the multiples of `p` in `ℤ/p²`, and the exact subgroup character sum | `primeSquareMultiples`, `card_primeSquareMultiples`, `sum_stdAddChar_primeSquareMultiples` |
| the valuation strata `1_U`, `1_V`, `δ₀` and their sums/products | `unitIndicator`, `valOneVec`, `deltaZero`, `sum_unitIndicator`, `sum_valOneVec`, … |
| eq. (2), the literal additive Fourier action on the strata | `dft_unitIndicator`, `dft_multipleIndicator`, `dft_deltaZero`, `primeSquareFourier_unitIndicator`, `primeSquareFourier_valOneVec` |
| the Fourier compression matrix of the valuation plane | `countInner_unit_fourier_unit`, `countInner_valOne_fourier_unit`, `countInner_unit_fourier_valOne`, `countInner_valOne_fourier_valOne` |
| eq. (1), the deformed occupation line `q_{p,c}` | `deformedOccupationRaw`, `deformedOccupationLine` |
| **eq. (4), the exact reflected-line coefficient `α_p(c)`** | `reflectedLineCoefficient_eq` |
| **eq. (5), `α_p(0) = −1/p`** | `reflectedLineCoefficient_zero` |
| eq. (6), the critical normalization `β_p(c)` | `criticalNormalizedReflection`, `criticalNormalizedReflection_eq` |
| **eq. (7), `N² − D² = p(p−1)x(x−2)`** | `reflection_numerator_sq_sub` |
| **eq. (8), `β_p(c) ≥ 1` with equality exactly at `c = 0`** | `one_le_criticalNormalizedReflection`, `criticalNormalizedReflection_eq_one_iff` |

**The cofinal type and the scale fracture**

| Card item | Lean declaration |
|---|---|
| the `c ↦ −c` symmetry of the normalized coefficient | `criticalNormalizedReflection_neg` |
| the sandwich `p^c/4 ≤ β_p(c) ≤ 3 p^c` | `criticalNormalizedReflection_bounds` |
| **eq. (11), `log β_p(c)/log p → |c|`** | `tendsto_log_criticalNormalizedReflection_div_log` |
| the weighted Cesàro transfer over the primes | `tendsto_weighted_prime_average` |
| **eq. (12), `log B_x(c)/θ(x) → |c|`** | `tendsto_log_prod_criticalNormalizedReflection` |
| **eqs. (13),(17), the linear rate `log B_N(c) ∼ |c| N`** | `tendsto_log_prod_criticalNormalizedReflection_div_natCast` |
| eq. (14), the Wold boundary volume `a_N = ∏_{p<N}(1−1/p)` and its polylogarithmic reciprocal | `primeEulerVolume`, `exists_inv_primeEulerVolume_le` (via Mertens' second theorem `tendsto_primeRecipSum_sub_logLog`) |
| **eqs. (16)–(18), the superessential separation of the two scales** | `tendsto_inv_primeEulerVolume_div_logProd` |

The separation is stated exactly as the card's no-go requires: the exponent scale `1/a_N` of the
Wold–Gamma first-trace anomaly, divided by the exponent `log B_N(c)` of the critically normalized
prime-square line comparison, tends to zero for every nonzero admissible drift.  Hence the
scalarized line comparison cannot be the missing Poisson–Wold morphism.

The remaining unchecked gates in the Gates section above are the open continuation--record
programme of the successor card, not statements of this one: everything this card proves is now
formalized.
