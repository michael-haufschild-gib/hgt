# Balanced-word height bar strict contraction

- **ID:** deninger-balanced-word-height-bar-strict-contraction
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[PROVED HERE] [LEAN-PROVED] [NOT RH]`
- **Label:** DAC_BALANCED_WORD_HEIGHT_BAR_STRICT_CONTRACTION
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/DeningerWordHeight.lean`,
  `DeningerBarWord.lean`, `DeningerBarInsert.lean`, `DeningerBarSlice.lean`,
  `DeningerBarDifferential.lean`, `DeningerBarUnit.lean`, `DeningerBarContraction.lean`,
  `DeningerBarSector.lean`, `DeningerBarFace.lean`, `DeningerBarInsertComm.lean`,
  `DeningerBarFibre.lean`, `DeningerBarSquareZero.lean`, `DeningerBarAlgebra.lean`,
  `DeningerBarPower.lean`
- **Parent:** deninger-arithmetic-calderon-green-intermediate-extension
- **Statement:** The rational prime-log height source has a canonical entire word-height
  completion of its two-term Milnor algebra.  The augmented two-sided bar complex is a nuclear
  Fréchet complex, every face and extra degeneracy is continuous, arithmetic-character sectors
  are closed complemented subcomplexes, and every sector—including total character zero—is
  split strictly exact.  Prime-log Green, Hardy, reflection, and power operators extend as chain
  operators before specialization.

## Frontier addressed

`DAC_PRIME_LOG_HEIGHT_KOTHE_CALDERON_SOURCE` controls one arithmetic character at a time.  It does
not by itself control Sullivan--Milnor words whose nonzero letters cancel to total character zero.
Two natural conjectures fail:

1. weighting a word only by the height of its total character gives weight one to every
   `(m,-m)` and therefore no summability on the balanced sector;
2. controlling every fixed word length separately does not control the number of faces in
   unbounded bar degree.

The survivor is forced by source structure: multiply the heights of the letters and take every
exponential word-length seminorm.  This card proves that this topology makes the canonical bar
incidence strict, including its balanced sector.  It does not identify the bar incidence with the
commutative relative Sullivan conormal; that comparison is the remaining source theorem.

No zeta zero, Xi divisor, RH-equivalent premise, numerical computation, or chosen spectral gap
enters.

## Source algebra and word topology

Let
\[
 \Gamma=\mathbb Z^{(\mathbb P)},\qquad
 H(m)=\prod_p p^{|m_p|},\qquad
 \ell(m)=\sum_p m_p\log p,
\]
and let \(\mathscr K_H^0\) be the nonzero-coefficient prime-log height Köthe space from
`DAC_PRIME_LOG_HEIGHT_KOTHE_CALDERON_SOURCE`.  Form the completed two-term Milnor algebra
\[
 B_H=\mathbb C\mathbf 1\oplus\mathscr K_H^0,
 \qquad
 (\lambda,a)(\mu,b)=(\lambda\mu,\lambda b+\mu a).              \tag{1}
\]
Thus the product of two degree-one Kummer terms is zero.

Put
\[
 I=\{\mathbf1\}\sqcup(\Gamma\setminus\{0\}),
\]
with letter character and height
\[
 \chi(\mathbf1)=0,\quad h(\mathbf1)=1,
 \qquad \chi(m)=m,\quad h(m)=H(m).                             \tag{2}
\]
For a nonempty word \(w=(i_1,\ldots,i_r)\in I^r\), define
\[
 |w|=r,\qquad \chi(w)=\sum_{j=1}^r\chi(i_j),qquad
 h_{\mathrm{word}}(w)=\prod_{j=1}^r h(i_j).                   \tag{3}
\]
Let \(\mathscr W_H\) be the coefficient space on all nonempty words for which
\[
 P_{k,R}(c)=
 \sum_{r\ge1}\ \sum_{w\in I^r}
 R^r h_{\mathrm{word}}(w)^k|c_w|<\infty                       \tag{4}
\]
for every integer \(k\ge0\) and \(R\ge1\).

Word length \(r=n+2\) is the bar degree
\[
 \operatorname{Bar}_n(B_H)=B_H^{\widehat\otimes(n+2)},
 \qquad n\ge0,                                                \tag{5}
\]
and length one is the augmented target \(B_H\).  Formula (4) simultaneously completes all bar
degrees; at each fixed length it is the completed projective \(\ell^1\) tensor topology.

## Theorem

**Theorem [PROVED HERE] [DAC_BALANCED_WORD_HEIGHT_BAR_STRICT_CONTRACTION].**

1. \(B_H\) and \(\mathscr W_H\) are complete nuclear Fréchet spaces.  The multiplication (1) is
   jointly continuous and obeys
   \[
    q_k(xy)\le q_k(x)q_k(y),
    \qquad q_k(\lambda,a)=|\lambda|+p_k(a).                    \tag{6}
   \]

2. Let \(\partial_j\) multiply letters \(j,j+1\), and on a word of length \(r\ge2\) put
   \[
    b=\sum_{j=0}^{r-2}(-1)^j\partial_j.                        \tag{7}
   \]
   The map \(b\) extends continuously to \(\mathscr W_H\), satisfies \(b^2=0\), and
   \[
    P_{k,R}(bc)\le P_{k,2R}(c).                                \tag{8}
   \]
   On length two, \(b\) is the augmentation multiplication \(B_H\widehat\otimes B_H\to B_H\).

3. Prepending the unit,
   \[
    s(i_1,\ldots,i_r)=(\mathbf1,i_1,\ldots,i_r),               \tag{9}
   \]
   extends continuously, with
   \[
    P_{k,R}(sc)=R P_{k,R}(c),
    \qquad bs+sb=1.                                            \tag{10}
   \]
   Consequently the augmented completed bar complex is split strictly exact.  Every boundary
   range is closed, not merely dense.

4. For \(\gamma\in\Gamma\), coordinate restriction
   \[
    Q_\gamma c=\mathbf1_{\{\chi(w)=\gamma\}}c_w               \tag{11}
   \]
   is a continuous projection.  It commutes with \(b\) and \(s\).  Hence every character sector
   is a closed complemented split strictly exact augmented subcomplex.  In particular, the
   total-character-zero bar sector resolves exactly the scalar line
   \((B_H)_0=\mathbb C\mathbf1\); balanced words create no completed bar homology.

5. Total prime-log generator
   \[
    (D_{\mathrm{tot}}c)_w=\ell(\chi(w))c_w                     \tag{12}
   \]
   is a continuous chain operator.  On the complement of the zero-character sector its Green
   inverse, odd Hodge sign, and Hardy projectors are continuous chain operators:
   \[
   \begin{aligned}
    (G_{\mathrm{tot}}c)_w&=|\ell(\chi(w))|^{-1}c_w,\\
    (W_{\mathrm{tot}}c)_w&=i\,\operatorname{sgn}(\ell(\chi(w)))c_w,\\
    (\Pi_\pm^{\mathrm{tot}}c)_w&=
      \mathbf1_{\{\pm\ell(\chi(w))>0\}}c_w.
   \end{aligned}                                               \tag{13}
   \]
   Both \(D_{\mathrm{tot}}\) and \(G_{\mathrm{tot}}\) lose at most one height seminorm; sign and
   projectors decrease every seminorm.

6. Componentwise reflection \(m\mapsto-m\) and positive power \(m\mapsto qm\) extend to
   continuous chain maps.  Reflection sends sector \(\gamma\) to \(-\gamma\), exchanges Hardy
   halves, and anticommutes with \(D_{\mathrm{tot}}\).  For positive integer \(q\), the power map
   sends sector \(\gamma\) to \(q\gamma\) and
   \[
    P_{k,R}(V_qc)=P_{qk,R}(c).                                 \tag{14}
   \]

## Proof

### Nuclearity and multiplication

The letter-height counting sum is finite:
\[
 \Sigma_2:=\sum_{i\in I}h(i)^{-2}
 =1+\sum_{m\ne0}H(m)^{-2}
 \le\zeta(2)^2.                                                \tag{15}
\]
For a seminorm pair \((k,R)\), choose \(S>R\Sigma_2\) and compare it with \((k+2,S)\).  The
Grothendieck--Pietsch ratio sum over all words is
\[
\begin{aligned}
 \sum_{r\ge1}\sum_{w\in I^r}
 \frac{R^r h_{\mathrm{word}}(w)^k}
      {S^r h_{\mathrm{word}}(w)^{k+2}}
 &=\sum_{r\ge1}\left(\frac{R}{S}\Sigma_2\right)^r<\infty.   \tag{16}
\end{aligned}
\]
Thus \(\mathscr W_H\) is nuclear.  Completeness follows by the same coordinatewise argument as
for a Köthe \(\ell^1\) intersection.  The fixed-length subspace gives the completed projective
tensor power because projective \(\ell^1\) weights multiply.

If two nonunit letters meet, their product in (1) is zero.  Every other nonzero product deletes
one unit and preserves the remaining letter.  It therefore preserves total character and never
increases word height.  Inequality (6) follows directly from (1) and the triangle inequality.

### Bar differential and strict contraction

On length \(r\), each of the \(r-1\) faces decreases length by one and does not increase height.
Hence
\[
 P_{k,R}(bc)
 \le\sum_{r\ge2}(r-1)R^{r-1}
    \sum_{w\in I^r}h_{\mathrm{word}}(w)^k|c_w|
 \le P_{k,2R}(c),                                              \tag{17}
\]
because \((r-1)R^{r-1}\le(2R)^r\) for \(R\ge1\).  The simplicial face identities give \(b^2=0\).

Prepending \(\mathbf1\) preserves word height and multiplies the length weight by \(R\), proving
the first part of (10).  In \(bsc\), the first face multiplies the prepended unit with the first
old letter and equals \(c\).  Every later face cancels with the corresponding term of \(sbc\)
because their signs differ.  This proves \(bs+sb=1\), including length one where augmentation of
\(\mathbf1\otimes x\) is \(x\).

If \(bc=0\), then \(c=b(sc)\).  Thus image equals kernel in every degree.  Kernels are closed, and
the continuous map \(s\) is a right inverse on each kernel, proving split strict exactness.

### Character sectors and Hodge operators

Coordinate deletion decreases every seminorm, so (11) is continuous.  Nonzero bar faces preserve
the sum of letter characters, and prepending the unit adds zero.  Therefore \(Q_\gamma\) commutes
with \(b,s\), and the contraction restricts to every sector.  Since no nonunit letter has
character zero, the length-one zero sector is exactly \(\mathbb C\mathbf1\).

For every word,
\[
 H(\chi(w))\le h_{\mathrm{word}}(w).                           \tag{18}
\]
If \(\chi(w)\ne0\), the prime-log height inequality gives
\[
 |\ell(\chi(w))|^{-1}
 \le H(\chi(w))
 \le h_{\mathrm{word}}(w),                                    \tag{19}
\]
while
\[
 |\ell(\chi(w))|
 \le\log H(\chi(w))
 \le h_{\mathrm{word}}(w).                                    \tag{20}
\]
Equations (19)--(20) prove the one-height-step estimates.  Faces and the extra degeneracy preserve
total character, so every operator in (12)--(13) commutes with the bar differential; sign
relations are coefficientwise.  Reflection preserves letter height, and
\(H(qm)=H(m)^q\) proves (14).

## Exact Route-L consequence

Rational total-character-zero incidence is no longer an undifferentiated analytic obstruction.
There is now a concrete source completion on which:

1. nonzero total character is controlled by the prime-log Green/Hodge calculus;
2. balanced total character zero is controlled by a continuous extra-degeneracy contraction;
3. both mechanisms coexist with reflection, positive powers, nuclearity, and closed boundary
   ranges.

The first unresolved theorem is therefore not “find some topology for balanced Milnor words.”  It
is the following strict comparison:

> Construct a character- and word-height-compatible chain equivalence from this entire bar source
> to the actual commutative relative Sullivan--Milnor conormal, then extend it through generic
> algebraic Kummer faces, product-formula/real apex, and the radial Poisson/Meyer seam.

This comparison cannot be inferred merely because both algebraic resolutions augment to the same
two-term algebra: completion can destroy quasi-isomorphisms unless the comparison and its homotopy
are continuous and strict.

Subsequent theorem `DAC_LINEARIZED_MILNOR_FIRST_SULLIVAN_STRICT_PRIMITIVE` constructs the first
commutative side of that comparison: the full completed base Milnor ideal has a canonical
normalized-coproduct primitive in a linearized first Sullivan attachment.  Current open comparison
therefore begins with genuine multiplicative syzygies beyond the first layer, not with the base
Milnor ideal.

## Failed conjectures and positive survivors

### Total-character height alone

**Failure.** Words \((m,-m)\) all have total height \(H(0)=1\).  Their coefficient basis therefore
has no summable nuclear transition under any topology depending only on total character.

**Positive survivor.** Product-of-letter height records cancellation cost and gives (15)--(16).

### Fixed bar degree only

**Failure.** The differential in word length \(r\) has \(r-1\) faces, so no degree-independent
bound follows from a single fixed length weight.

**Positive survivor.** The family of all exponential length weights absorbs face growth by (17)
and remains nuclear by increasing the length parameter in (16).

### Green inversion on balanced words

**Failure.** \(D_{\mathrm{tot}}=0\) on every balanced word, so prime-log division cannot contract
that sector.

**Positive survivor.** The bar extra degeneracy preserves total character and contracts the
balanced sector without division.

## Hostile novelty and circularity audit

- Bar resolutions, extra degeneracies, Köthe nuclearity, and completed projective tensor products
  are parent mathematics.
- Existing work on cyclic homology of nuclear Köthe algebras and on algebra structures of bar
  complexes does not supply this prime-height/word-length/character-sector Deninger source.
- Corpus contains genuine cyclic bars and finite Sullivan--Milnor resolutions, but search found no
  product-of-prime-heights entire bar completion or strict balanced-character contraction.
- New content is source-exact conjunction and frontier reduction, not a claim that bar homological
  algebra itself is new.
- The theorem proves no comparison with the actual pro-Stein Sullivan conormal, no real
  product-formula attachment, no Paugam orientation comparison, and no RH statement.
- Ordinary \(\zeta(2)\) in (15) is only the convergent positive Dirichlet series used for counting;
  it contains no information about nontrivial zeta zeros.

## Lean statements

The alphabet `I = {1} ⊔ (Γ∖{0})` is realised as `Γ = DeningerLattice` itself, with the zero
character as the unit: `h(0) = 1` and `χ(0) = 0`.  Words are `DeningerBarWord = Σ r, Fin (r+1) → Γ`
(nonempty), with `deningerBarLength`, `deningerBarHeight`, `deningerBarChar`.

| Card item | Lean declaration |
|---|---|
| `(2)`--`(4)` the word source | `deningerBarKotheData`, `DeningerBarKothe`, `deningerBarSeminorm`, `deningerBarSeminormR`, `deningerBarSeminormR_summable` |
| `(15)`--`(16)` counting and nuclearity | `deningerHeightInvSum`, `deningerWordPow_tsum`, `deningerBarKotheData_isNuclear`, `deningerBarKothe_isNuclearSpace` |
| clause 1, completeness and density | `deningerBarKothe_exists_limit`, `deningerBarKothe_exists_finite_approx` |
| `(1)`, `(6)` the two-term algebra | `DeningerTwoTerm`, `deningerTwoTermMul`, `deningerTwoTermSeminorm`, `deningerTwoTermSeminorm_mul_le` |
| `(7)` the faces and their fibres | `deningerBarFaceWord`, `deningerBarFaceWord_eq_some_iff`, `deningerBarFibre`, `deningerBarFibreSum_eq_sum`, `deningerBarDiffCoe_eq_sum` |
| `(7)` the differential | `deningerBarDiffCoe`, `deningerBarDiff` |
| `(8)` the doubling estimate | `deningerBarSeminormR_diff_le` |
| `b² = 0` | `deningerInsertUnit_comm`, `deningerBarDouble`, `deningerBarDouble_swap`, `deningerBarDiffCoe_comp_self`, `deningerBarDiff_comp_self` |
| `(9)`, `(10)` the extra degeneracy | `deningerBarUnitCoe`, `deningerBarUnit`, `deningerBarSeminormR_unit`, `deningerBarContraction`, `deningerBarContraction_op` |
| split strict exactness | `deningerBar_exact` |
| `(11)` character sectors | `deningerBarCharMul`, `deningerBarCharMul_diff`, `deningerBarCharMul_unit`, `deningerBarSectorProj`, `deningerBarSectorProj_idem`, `deningerBarSectorProj_diff`, `deningerBarSectorProj_unit`, `deningerBarSector_exact`, `deningerBarSeminorm_sectorProj_le` |
| clause 4, the length-one zero sector | `deningerBarChar_one_eq_zero_iff` |
| `(12)`, `(13)`, `(18)`--`(20)` | `deningerHeight_barChar_le`, `deningerBarTotalGenerator`, `deningerBarTotalGreen`, `deningerBarTotalHodge`, `deningerBarHardyPlus`, `deningerBarHardyMinus`, with `deningerBarTotalGenerator_diff`, `deningerBarTotalGreen_diff`, `deningerBarTotalHodge_diff`, `deningerBarHardyPlus_diff`, `deningerBarHardyMinus_diff`, `deningerBarSeminorm_totalGenerator_le`, `deningerBarSeminorm_totalGreen_le`, `deningerBarSeminorm_totalHodge_le`, `deningerBarSeminorm_hardyPlus_le`, `deningerBarSeminorm_hardyMinus_le` |
| clause 6, reflection | `deningerBarReflect`, `deningerBarSeminorm_reflect`, `deningerBarReflect_diff_op`, `deningerBarReflectWord_char`, `deningerBarReflect_sector`, `deningerBarReflect_hardy`, `deningerBarReflect_totalGenerator` |
| `(14)`, clause 6, powers | `deningerBarPower`, `deningerBarSeminormR_power`, `deningerBarPower_diff`, `deningerBarPowerWord_char`, `deningerBarPowerWord_height` |

Reading conventions, all faithful to the paper statement:

- the fibre of the `j`-th face over a word is the pair of unit insertions at positions `j` and
  `j+1`, which coincide exactly when the merged letter is the unit — this is `(7)` read on
  coefficients, and it is proved to be the honest fibre of the face `deningerBarFaceWord`;
- `b² = 0` is proved by the simplicial pairing `(j,j') ↦ (j'-1, j)` acting on the double fibres,
  which are matched by the commutation of two unit insertions;
- completeness is sequential, which for a countable seminorm family is Fréchet completeness;
- density is stated as approximation of every vector by a truncation of its own coordinate
  expansion, in every seminorm.

## Gates

- [x] 0 → 1 in-progress: balanced-word divergence and face-growth obstruction isolated
- [x] 1 → 2 fully-proven: nuclear word topology, strict contraction, sector decomposition, and
      chain Hodge operators proved without conditional premise
- [x] 2 → 3 formalized: all six numbered clauses proved unconditionally in Lean
- [x] targeted axiom audit: only `propext`, `Classical.choice`, `Quot.sound`
- [x] modules wired into `RHTower.lean`
- [ ] 3 → 4 publication-ready: requires strict Sullivan comparison and independent specialist
      novelty/significance audit

## References

- `deninger-prime-log-height-kothe-calderon-source.md`.
- `../../../3-formalized/not_new_scientific_knowledge/prime-log-height-bound.md`.
- Z. A. Lykova, *Cyclic cohomology of certain nuclear Fréchet and DF algebras*,
  arXiv:0704.1019.
- B. Fresse, *The bar complex of an E-infinity algebra*, arXiv:math/0601085.
- C. Deninger, *Dynamical systems for arithmetic schemes*, arXiv:1807.06400.

## Log

- 2026-08-10 — Formalized the whole theorem unconditionally.  Modelled the alphabet
  `{1} ⊔ (Γ∖{0})` as `Γ` with the zero character as the unit, which makes the fibre of a face
  the pair of unit insertions and the coefficient description of `b` finite and explicit.  Built
  the entire word-height source and its nuclearity, the two-parameter seminorms, the differential
  with the doubling estimate, `b² = 0` by the simplicial pairing on double fibres, the extra
  degeneracy with the exact length-weight identity and `bs + sb = 1`, split strict exactness,
  the character multiplier calculus with the sector projections and the total prime-log
  Green/Hodge/Hardy operators, and reflection and positive powers as chain maps.  Card promoted
  to `3-formalized`.
- 2026-08-08 — Rejected total-character-only and fixed-length completions.  Constructed the entire
  product-letter-height bar source; proved nuclearity, continuous bar faces, continuous
  extra-degeneracy contraction, strict exactness in every arithmetic-character sector, and
  compatibility with prime-log Green/Hodge, reflection, and positive powers.  Narrowed first
  Route-L source theorem to strict comparison with actual Sullivan--Milnor/pro-Stein incidence;
  the subsequent linearized first-Sullivan theorem closes its base-ideal layer.
