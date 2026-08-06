# Prime-sieve Wold--Gamma/BV relative character and atomic cofinal limit

- **ID:** `prime-sieve-wold-gamma-bv-relative-character`
- **Stage:** 3-formalized
- **Type:** SOURCE-COFINAL OPERATOR/CONORMAL THEOREM
- **Scientific status:** `[PAPER PROOF COMPLETE] [CANDIDATE NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY PROVISIONAL] [NOT RH]`
- **Parents:**
  - `../1-in-progress/multiplicative-wold-gamma-anomaly-purity-rh.md`;
  - `not_new_scientific_knowledge/bv-prime-window-polar-coefficient-decimation-law.md`;
  - `../1-in-progress/source-effective-polar-kummer-conormal-purity.md`;
  - `../1-in-progress/source-curved-prime-torus-conormal-temperedness.md`.
- **Statement:** Independent one-prime Wold defects do not form a cofinal character.  Their
  commuting prime-sieve intersection does.  Its regular polarized determinant has absolutely
  summable prime-enlargement increments and converges to the one-dimensional vacuum determinant;
  its singular first-trace density is exactly the BV principal-conormal coefficient, has total
  cofinal variation one, and tends to zero.  The principal conormal therefore survives only in the
  source-normal blow-up of this convergent relative character.

## 1. Commuting arithmetic sieve

Let
\[
 H=\ell^2(\mathbb N_{>0}),\qquad
 Qe_n=n^{-1}e_n,\qquad
 S_pe_n=e_{pn},\qquad
 E_p=I-S_pS_p^*.
\]
For a finite set \(P\) of rational primes put
\[
 M_P=\prod_{p\in P}p,\qquad
 E_P=\prod_{p\in P}E_p,\qquad
 Q_P=E_PQ.                                                     \tag{1}
\]
The projections \(E_p\) commute, and \(E_P\) is the coordinate projection onto
\[
 \{n\geq1:(n,M_P)=1\}.                                        \tag{2}
\]
If \(p\notin P\), there is an orthogonal \(Q_P\)-reducing decomposition
\[
 E_PH=E_{P\cup\{p\}}H\ \widehat\oplus\ S_pE_PH,                \tag{3}
\]
and \(S_p:E_PH\to S_pE_PH\) identifies the second restriction of \(Q_P\) with
\(p^{-1}Q_P\).

Indeed, every integer coprime to \(M_P\) is uniquely either prime to \(p\) or \(p\) times an
integer coprime to \(M_P\).  Also \(QS_p=p^{-1}S_pQ\).  This proves `(1)`--`(3)` without analytic
continuation or divisor data.

## 2. Regular determinant layer

For \(|t|<1\), define
\[
 \Phi_P(t)
 =
 \frac{\det_2(I-tQ_P)}{\det_2(I+tQ_P)}.                         \tag{4}
\]
Since \(Q_P\) is Hilbert--Schmidt, `(4)` is defined and nonzero on the open unit disk.  Orthogonal
determinant multiplicativity in `(3)` gives the exact prime-enlargement law
\[
 \boxed{\quad
 \Phi_{P\cup\{p\}}(t)=\frac{\Phi_P(t)}{\Phi_P(t/p)}.
 \quad}                                                        \tag{5}
\]
This is not the independent one-prime defect
\(\Phi_\varnothing(t)/\Phi_\varnothing(t/p)\) repeated at every prime.  The numerator in `(5)`
changes with the already-sieved packet.

The logarithmic expansion is
\[
 \log\Phi_P(t)
 =
 -2\sum_{j\geq1}
 \frac{t^{2j+1}}{2j+1}
 \zeta(2j+1)
 \prod_{p\in P}(1-p^{-(2j+1)}).                                \tag{6}
\]
For every \(0<r<1\), there is \(C_r<\infty\), independent of \(P\) and \(p\notin P\), such that
\[
 \sup_{|t|\leq r}
 \left|
 \log\Phi_{P\cup\{p\}}(t)-\log\Phi_P(t)
 \right|
 \leq \frac{C_r}{p^3}.                                        \tag{7}
\]
To prove `(7)`, use `(5)` and `(6)` at \(t/p\), together with
\[
 \operatorname{Tr}(Q_P^k)
 \leq\zeta(k)\leq\zeta(3)
 \qquad(k\geq3).
\]
The remaining odd power series is bounded by a constant times \(p^{-3}\).  Hence the increments
in `(7)` are absolutely summable over all primes.

As \(P\) increases through the finite prime sets,
\[
 Q_P\longrightarrow P_{\{1\}}
 \quad\text{in Hilbert--Schmidt norm},                          \tag{8}
\]
because
\[
 \|Q_P-P_{\{1\}}\|_2^2
 =
 \sum_{\substack{n>1\\(n,M_P)=1}}\frac1{n^2}
 \longrightarrow0
\]
by dominated convergence.  Therefore `(4)` converges locally uniformly on \(|t|<1\) to
\[
 \Phi_{\rm vac}(t)
 =
 \frac{\det_2(I-tP_{\{1\}})}{\det_2(I+tP_{\{1\}})}
 =
 e^{2t}\frac{1-t}{1+t}.                                       \tag{9}
\]
Equivalently, the Euler factors in `(6)` cancel \(\zeta(2j+1)\) in the cofinal limit, leaving
the single vacuum eigenvalue.

## 3. Singular first-trace layer

For a cutoff \(N\), put
\[
 T_P(N)
 =
 \operatorname{Tr}_{n\leq N}(Q_P)
 =
 \sum_{\substack{n\leq N\\(n,M_P)=1}}\frac1n.                  \tag{10}
\]
Finite inclusion--exclusion gives
\[
 T_P(N)
 =
 \sum_{d\mid M_P}\frac{\mu(d)}d H_{\lfloor N/d\rfloor}.
\]
Consequently
\[
 T_P(N)=a_P\log N+\kappa_P+o(1),                               \tag{11}
\]
where
\[
 a_P=\prod_{p\in P}(1-p^{-1}),\qquad
 \kappa_P
 =
 a_P\left(
 \gamma+\sum_{p\in P}\frac{\log p}{p-1}
 \right).                                                     \tag{12}
\]
The singular trace density has the exact transition
\[
 a_{P\cup\{p\}}=a_P(1-p^{-1}),\qquad
 a_P-a_{P\cup\{p\}}=\frac{a_P}{p}.                            \tag{13}
\]

For any enumeration \(p_1,p_2,\ldots\) of all primes, let
\(P_n=\{p_1,\ldots,p_n\}\).  Euler's divergence of
\(\sum_p1/p\) gives \(a_{P_n}\to0\), and `(13)` telescopes:
\[
 \boxed{\quad
 \sum_{n\geq1}\frac{a_{P_{n-1}}}{p_n}=1.
 \quad}                                                        \tag{14}
\]
Thus the singular density has finite total cofinal variation, even though the independent
one-prime densities \(1-p^{-1}\) are not summable.

The finite part \(\kappa_P\) is retained in `(11)` but is not used to manufacture convergence.
The regular/singular relative character is the pair consisting of the \(\det_2\) layer and the
coefficient \(a_P\) of the trace term removed by \(\det_2\).

## 4. Exact BV principal-conormal reading

Let \(W\) be a compactly supported BV window.  For every scale \(a>0\), put
\[
 W_a(x)=W(ax)
\]
and let \(p_a\) be its canonical prime--polar coefficient sequence.  For every integer \(q\geq2\),
the proof of the BV decimation law gives, without requiring \(\sqrt q\) to be an integer,
\[
 D_qp_a=p_{aq},\qquad
 (D_qb)(N)=b(qN).                                            \tag{15}
\]
Indeed, the prime term is reindexed directly, while
\(M_{W_a}(3/2)=a^{1/2}M_W(3/2)\).

Let \(J\) denote the pole-cancelled BV/co-Poisson principal-normal class before choosing a zero.
The source laws are
\[
 J(D_qp_a)=q^{s-1}J(p_a),\qquad
 J(S_qb)=q^{-s}J(b).                                         \tag{16}
\]
With \(E_q=I-S_qD_q\), equations `(15)`--`(16)` cancel the spectral variable:
\[
 J(E_qp_a)=(1-q^{-1})J(p_a).                               \tag{17}
\]
For distinct primes the decimation, inflation, and off-multiple projections commute.  Induction
therefore gives the finite-prime identity
\[
 \boxed{\quad
 J(E_Pp_a)=a_PJ(p_a).
 \quad}                                                       \tag{18}
\]
At every uncensored divisor fibre, `(18)` is the corresponding identity for the complete
principal Laurent residue, including its multiplicity scalar.  Thus the coefficient \(a_P\) in
the singular trace asymptotic `(11)` is literally the coefficient of the same sieved BV
principal conormal.

## 5. Cofinal relative character and normal-cone fracture

Equations `(5)`, `(13)`, and `(18)` define one finite-packet relative source character:
\[
 \mathfrak C_P
 =
 \bigl(Q_P,\Phi_P,a_PJ(p_a)\bigr).                            \tag{19}
\]
Its regular increments have total variation bounded by
\(\sum_pC_rp^{-3}\); its singular scalar increments have total variation one.  Its endpoint is
\[
 \mathfrak C_\infty
 =
 \bigl(P_{\{1\}},\Phi_{\rm vac},0\bigr)                       \tag{20}
\]
in the coarse Hilbert/determinant/conormal topology.

The zero in `(20)` does not mean that the distinguished conormal was absent.  For every finite
\(P\),
\[
 a_P^{-1}J(E_Pp_a)=J(p_a).                                  \tag{21}
\]
Therefore the source-normal blow-up of `(19)` along \(a_P=0\) retains one constant nonzero
principal-conormal direction while the coarse realization loses it.  This is an exact instance
of the required third-completion fracture:

```text
coarse all-prime limit:
  regular vacuum survives, principal conormal vanishes;

source-normal blow-up:
  regular vacuum and calibrated principal conormal both survive.
```

The blow-up is source-defined: \(E_P\), \(a_P\), and \(J(E_Pp_a)\) exist before a zero or a divisor
fibre is selected.

## 6. Naive differential-character no-go

The one-prime pair
\[
 \left(
 \frac{\Phi_\varnothing(t)}{\Phi_\varnothing(t/p)},
 1-p^{-1}
 \right)
\]
tends to \((\Phi_\varnothing(t),1)\), not to the identity.  Taking its direct product over primes
therefore diverges in both regular and singular channels.  Calling those independent scalar
reporters one differential character does not construct an all-prime source object.

The nested sieve `(19)` is the positive replacement.  Previously adjoined primes change the next
defect: the regular increment becomes \(O(p^{-3})\), while the singular increment becomes
\(a_P/p\) and telescopes.  Higher-prime interaction is therefore load-bearing, not an optional
repackaging of the one-prime Wold law.

There is still no RH conclusion.  Blowing up by \(a_P^{-1}\) is singular.  Differential
cohomology, determinant curvature, and the integral characteristic class do not by themselves
bound the nonunitary flat holonomy of the normalized conormal line.  A Hermitian comparison must
be constructed from the source and proved continuous in the blow-up topology.

## 7. Exact next theorem: contractive polar transgression

Fix \(0<r<1\) and define the source transition size
\[
 \delta_r(P,p)
 =
 \frac{a_P}{p}
 +
 \sup_{|t|\leq r}|\log\Phi_P(t/p)|.                       \tag{22}
\]
Equations `(7)` and `(14)` prove, for every prime exhaustion,
\[
 \sum_n\delta_r(P_{n-1},p_n)<\infty.                     \tag{23}
\]

The RH-bearing comparison is now one quantitative statement, rather than the assertion that a
determinant character exists:

> **[CONJECTURE -- SOURCE-NORMAL CONTRACTIVE POLAR TRANSGRESSION.]**
> The source-calibrated normal blow-up of `(19)` has finite-packet Kummer--Arakelov regulators
> \(h_P\) whose prime transport is the centered principal-conormal transport, and there are
> source constants \(C,r\), independent of \(P\) and \(p\notin P\), such that
> \[
> \|h_{P\cup\{p\}}-h_P\|_{L^1+L^2}
> \leq C\,\delta_r(P,p).                                    \tag{24}
> \]
> The regulator and `(24)` are constructed before divisor specialization and preserve every
> normalized principal-conormal multiplicity jet.

By `(23)`, equation `(24)` makes \((h_P)\) mixed-Cauchy.  At a divisor fibre \(\rho\), exact
prime transport gives
\[
 \langle h_\rho,f_p\rangle
 =
 (\tfrac12-\operatorname{Re}\rho)\log p.
\]
The mixed Kummer coherent-power selector then forces
\(\operatorname{Re}\rho=\tfrac12\).  Hence `(24)` plus the source comparison proves RH.

This consequence also makes `(24)` hostilely testable.  For a coherent off-critical exponent
\(c\neq0\), the unique component-constant finite Kummer regulators have harmonic-size transition
defects and are not mixed-Cauchy, whereas the right side of `(24)` is summable.  Thus an off-line
generalized-prime model can satisfy `(24)` only if it carries the literal nested ordinary-prime
source character and a false contractive comparison; positivity, functional equation, entire
completion, and hypertranscendence alone do not approach it.

## Novelty and literature boundary

Parent ingredients are not claimed as new:

- Wold decompositions for commuting isometries;
- Hilbert--Schmidt regularized determinants and their product laws;
- Eratosthenes inclusion--exclusion and Euler's divergence of reciprocal primes;
- BV coefficient decimation and the co-Poisson principal-normal class.

Targeted searches found tuple-Wold theory, regularized determinant product formulas, Bost--Connes
finite-prime semigroup systems, and classical sieve asymptotics.  They did not locate the exact
conjunction `(5)`, `(14)`, `(18)`, and `(21)`: a coprime Wold sieve whose polarized Gamma
determinant and BV principal conormal form one finite-variation cofinal relative character with an
atomic coarse limit and a nonzero source-normal conormal blow-up.  This is a provisional
noncollision report, not a priority claim.

Closest external parents include:

- Satyabrata Majee and Amit Maji, *Wold decomposition for isometries with equal range*,
  https://arxiv.org/abs/2309.04445;
- Thomas Britz, Alan Carey, Fritz Gesztesy, Roger Nichols, Fedor Sukochev, and Dmitriy Zanin,
  *The product formula for regularized Fredholm determinants*,
  https://arxiv.org/abs/2007.12834;
- Nathan Brownlowe, Nadia Larsen, Ian Putnam, and Iain Raeburn,
  *Subquotients of Hecke \(C^*\)-algebras*,
  https://arxiv.org/abs/math/0309429.

## Gates

- [x] finite commuting prime-sieve operator constructed
- [x] exact nested polarized-determinant transition proved
- [x] absolute cofinal convergence to the vacuum determinant proved
- [x] singular first-trace density and total variation proved
- [x] arbitrary-integer BV scale-decimation extension proved
- [x] multi-prime BV principal-conormal coefficient proved
- [x] coarse-limit/normal-blow-up fracture classified
- [x] naive independent-defect differential character killed
- [x] exact contractive transgression inequality isolated
- [ ] independent specialist novelty audit
- [x] Lean formalization complete for every proved theorem (Sections 1--7); see
  "Formalization status" below
- [ ] source-normal contractive polar transgression `(24)`
- [ ] RH

## Formalization status

Every theorem proved in this card (Sections 1--7) is formalized unconditionally
in Lean 4, with axiom set `propext`, `Classical.choice`, `Quot.sound` throughout.
Conjecture `(24)` is not proved on paper and is not a formalization target.

Section 3, the singular first-trace layer, is `[LEAN-PROVED]` in
`HTGeometry/PrimeSieveDensityTelescope.lean` (axioms: `propext`,
`Classical.choice`, `Quot.sound`):

| Card item | Declaration |
|---|---|
| `a_P = ∏_{p∈P}(1-p^{-1})` | `sieveDensity` |
| `(13)` `a_{P∪{p}} = a_P(1-p^{-1})` | `sieveDensity_insert` |
| `(13)` `a_P - a_{P∪{p}} = a_P/p` | `sieveDensity_sub_insert` |
| telescoping partial sums | `sum_sieveDensity_div_prime` |
| `a_{P_n} → 0` from Euler divergence | `tendsto_sieveDensity_sievePrefix` |
| `(14)` `∑_{n≥1} a_{P_{n-1}}/p_n = 1` | `hasSum_sieveDensity_div_prime`, `tsum_sieveDensity_div_prime` |

The sieved trace identity behind the logarithmic expansion `(6)` is `[LEAN-PROVED]`
in `HTGeometry/PrimeSieveEulerTrace.lean`:

| Card item | Declaration |
|---|---|
| `M_P = ∏_{p∈P} p` and its enlargement | `sievePrimorial`, `sievePrimorial_insert`, `coprime_sievePrimorial` |
| the coprimality class of the enlarged sieve | `coprime_sievePrimorial_insert_iff` |
| the sieved sum `∑_{(n,M_P)=1} f(n)` | `sievedSum` |
| the arithmetic splitting of `(3)`: coprime-to-`p` plus `p` times the class | `sievedSum_insert` |
| finite Euler product of the sieve | `sievedSum_eq_mul_prod` |
| `Tr(Q_P^k) = ζ(k) ∏_{p∈P}(1-p^{-k})` | `sievedSum_rpow_inv` |

`sievedSum_insert` is the exact arithmetic content of the `Q_P`-reducing
decomposition `(3)`: every integer coprime to `M_P` is uniquely either prime to
`p` or `p` times an integer coprime to `M_P`, and on the second class the weight
is scaled by `f(p)`.

Section 3's decimated expansion `(12)` and its affine asymptotic `(11)` are
`[LEAN-PROVED]` in `HTGeometry/PrimeSieveHarmonicInclusionExclusion.lean`:

| Card item | Declaration |
|---|---|
| `T_P(N) = ∑_{n ≤ N, (n,M_P)=1} 1/n` | `sievedHarmonic` |
| `H_N = ∑_{1 ≤ j ≤ N} 1/j` | `sum_Icc_one_div_eq_harmonic` |
| divisors of `gcd` as the filtered divisors | `divisors_gcd_eq_filter` |
| `∑_{d ∣ n} μ(d) = [n = 1]` | `sum_divisors_moebius_real` |
| the multiples of `d` below `N` are `d · Icc 1 ⌊N/d⌋` | `multiples_Icc` |
| `(12)` `T_P(N) = ∑_{d ∣ M_P} μ(d)/d · H_{⌊N/d⌋}` | `sievedHarmonic_eq_sum_divisors` |
| `d ↦ μ(d)/d` multiplicative, and its divisor sum | `moebiusDiv`, `isMultiplicative_moebiusDiv`, `isMultiplicative_moebiusDivSum` |
| `∑_{d ∣ M_P} μ(d)/d = a_P = ∏_{p∈P}(1-1/p)` | `sum_divisors_moebiusDiv_sievePrimorial` |
| `⌊N/d⌋ → ∞` and `⌊N/d⌋/N → 1/d` | `tendsto_natDiv_atTop`, `tendsto_natDiv_div_self` |
| `log ⌊N/d⌋ - log N → -log d` | `tendsto_log_natDiv_sub_log` |
| `H_{⌊N/d⌋} - log N → γ - log d` | `tendsto_harmonic_natDiv_sub_log` |
| `κ_P = ∑_{d ∣ M_P} μ(d)/d · (γ - log d)` | `sieveHarmonicConstant` |
| `(11)` `T_P(N) - a_P log N → κ_P` | `tendsto_sievedHarmonic_sub` |

The leading coefficient of `(11)` is literally the sieve density of `(13)`: the
Möbius divisor sum of the squarefree primorial is the finite Euler product, so
the same `a_P` governs both the density telescope of Section 3 and the
logarithmic growth of the first sieved trace.

Section 2's regular determinant layer is `[LEAN-PROVED]` in
`HTGeometry/PrimeSieveRegularDeterminant.lean`, at the level of
`log Φ_P` (the polarization kills the even traces and the regularized quadratic
term, so `(6)` is the complete content of `(4)`):

| Card item | Declaration |
|---|---|
| `Tr(Q_P^k)` as a sieved sum, natural-power form | `sieveTrace`, `sieveTrace_eq_mul_prod`, `sieveTrace_insert` |
| `0 ≤ Tr(Q_P^k) ≤ ζ(3)` for `k ≥ 3` | `sieveTrace_nonneg`, `sieveTraceBound`, `sieveTrace_le_bound` |
| `(6)` `log Φ_P(t) = -2 ∑_{j≥1} t^{2j+1}/(2j+1) ζ(2j+1) ∏(1-p^{-(2j+1)})` | `sieveLogPhi` |
| convergence of `(6)` on `|t| < 1` | `norm_sieveLogPhi_term_le`, `summable_sieveLogPhi_bound`, `summable_sieveLogPhi_term` |
| `(5)` `Φ_{P∪{p}}(t) = Φ_P(t)/Φ_P(t/p)` | `sieveLogPhi_insert` |
| `sup_{|t|≤r} |log Φ_P(t)| ≤ 2ζ(3)/(1-r²) · r³` | `abs_sieveLogPhi_le` |
| `(7)` increment bound `C_r/p³` | `abs_sieveLogPhi_insert_sub_le` |
| `log Φ_vac(t) = 2t + log(1-t) - log(1+t)` | `vacuumLogPhi` |
| `(9)` `Φ_vac(t) = e^{2t}(1-t)/(1+t)` | `exp_vacuumLogPhi` |
| odd tail of the `artanh` series | `hasSum_vacuumSeries` |
| `Tr(Q_P^k) → 1` cofinally | `tendsto_sieveTrace_sievePrefix` |
| `(9)` cofinal limit `log Φ_P → log Φ_vac` | `tendsto_sieveLogPhi_sievePrefix` |

`sieveLogPhi_insert` is the boxed law `(5)` in logarithmic form: the enlarged
logarithm is the difference of the old logarithm and its own decimation at the
adjoined prime, so the numerator does change with the already-sieved packet.
`tendsto_sieveTrace_sievePrefix` replaces the Euler-product argument by the
direct one: every integer above one has a prime factor, which enters the sieve
at a finite stage, so Tannery's theorem collapses the traces to the single
surviving eigenvalue `n = 1` — this is exactly the Hilbert--Schmidt statement
`(8)` at the level of the power traces.

Section 1's operator layer and the determinant definition `(4)` itself are
`[LEAN-PROVED]` in `HTGeometry/LpDiagonalOperator.lean` (reusable) and
`HTGeometry/PrimeSieveOperator.lean`:

| Card item | Declaration |
|---|---|
| diagonal operators on `ℓ²(ι)`, generic | `HilbertSchmidt.diagKernel`, `isHS_diagKernel`, `diagOp`, `diagOp_apply` |
| composition, difference, powers of diagonals | `diagOp_comp`, `diagOp_sub`, `diagOp_pow` |
| `‖·‖_HS` and the power traces of a diagonal | `hsNormSq_diagOp`, `opTrace_diagOp_comp`, `opTrace_diagOp_pow` |
| `Q e_n = n^{-1} e_n` restricted to `(n,M_P)=1`, i.e. `(1)`+`(2)` | `sieveWeight`, `sieveOperator` |
| `Q_P` is Hilbert--Schmidt | `isHilbertSchmidt_sieveOperator` |
| `Tr(Q_P^k) = ζ(k) ∏(1-p^{-k})` as an operator trace | `opTrace_sieveOperator_pow` |
| the Hilbert--Carleman exponent of `Q_P` | `operatorFredholmExpGerm_sieveOperator` |
| convergence of that germ on `\|t\| < 1` | `summable_expGerm_term`, `sieveTraceBoundTwo`, `sieveTrace_le_boundTwo` |
| even degrees cancel, odd degrees double | `expGermDiff`, `expGermDiff_even`, `expGermDiff_odd` |
| `(4)` `Φ_P(t) = det₂(I-tQ_P)/det₂(I+tQ_P)` | `sievePhi` |
| **`(4)` = `(6)`** | `sievePhi_eq_exp_sieveLogPhi` |
| `P_{\{1\}}`, the vacuum projection | `vacuumWeight`, `vacuumProjection` |
| `‖Q_P - P_{\{1\}}‖₂² = ∑_{n>1,(n,M_P)=1} n^{-2}` | `hsNormSq_sieveOperator_sub_vacuum` |
| `(8)` `Q_P → P_{\{1\}}` in Hilbert--Schmidt norm | `tendsto_hsNormSq_sieveOperator_sub_vacuum` |

`sievePhi_eq_exp_sieveLogPhi` closes the loop between the two presentations of
the sieve character: the determinant quotient of `(4)`, built from the corpus's
coordinate-free Hilbert--Carleman germ, equals the exponential of the odd trace
series `(6)`, so the boxed enlargement law `(5)` and the increment bound `(7)`
are statements about the determinant itself and not only about a chosen
series.

Section 4's coefficient layer is `[LEAN-PROVED]` in
`HTGeometry/CoefficientDecimationSieve.lean`:

| Card item | Declaration |
|---|---|
| `(D_q b)(N) = b(qN)`, `(S_q b)(M) = b(M/q)` on multiples | `decimate`, `inflate` |
| `D_q S_q = 1` | `decimate_inflate` |
| `P_q = S_q D_q` is the projection onto multiples of `q` | `multipleProjection`, `multipleProjection_apply` |
| `E_q = I - S_q D_q` is the projection onto non-multiples | `offMultiple`, `offMultiple_apply` |
| `E_P` as a coordinate projection onto `(M, M_P) = 1` | `sieveOffMultiple`, `sieveOffMultiple_empty` |
| `E_{P∪\{p\}} = E_p ∘ E_P` | `sieveOffMultiple_insert` |
| `D_p` commutes with `E_P` for `p ∉ P` | `decimate_sieveOffMultiple` |
| `J(S_q b) = q^{-s} J(b)` for the Dirichlet functional, exactly | `LSeries_inflate` |
| the multiple-projection Dirichlet series | `LSeries_multipleProjection`, `LSeriesSummable_multipleProjection` |
| the off-multiple Dirichlet split | `LSeries_offMultiple` |
| **`(17)`+`(18)`** `J(E_P p_a) = a_P J(p_a)` | `J_sieveOffMultiple` |

`sieveOffMultiple_inv_eq_sieveWeight` (in `PrimeSieveOperator.lean`) identifies
this coefficient-space `E_P` with the spectral projection carried by the sieved
diagonal of Section 1: the off-multiple sieve of the reciprocal sequence *is*
`sieveWeight P`.  So `(18)` and `(13)` speak about one operator, which is the
content of the card's remark that `a_P` in `(11)` is literally the coefficient of
the same sieved BV principal conormal.

`J_sieveOffMultiple` derives `(18)` from exactly the four source laws the card
lists: the decimation reindexing `(15)`, the decimation character `q^{s-1}` and
the inflation character `q^{-s}` of `(16)`, and additivity of `J`.  The
inflation character is discharged unconditionally here (`LSeries_inflate`), and
the decimation character is the corpus theorem
`RHTower.CompactBVPrimeWindow.continuedSourceResidueValue_argumentDilation`
together with the coefficient decimation
`polarCoefficient_argumentDilation_eq_argumentExpansion_sq_mul`.  That extension is carried out in
`RHTower/BVPrimeWindowSieveResidue.lean`, which closes Section 4 at the actual
Laurent residue:

| Card item | Declaration |
|---|---|
| natural-number argument dilation, total in the index | `natDilate`, `natDilate_eq`, `mellinTransform_natDilate` |
| `(16a)` `J(p_{aq}) = q^{s-1} J(p_a)` | `continuedSourceResidueValue_natDilate` |
| `(15)` `D_q p_a = p_{aq}`, for every integer `q ≥ 1` | `weightedPrimeWindow_decimate`, `polarCoefficient_decimate`, `decimate_polarCoefficient` |
| the continuation of the sieved coefficient sequence | `sievedContinuedSource` |
| that it *is* the continuation | `LSeries_sieveOffMultiple_polarCoefficient` |
| **`(18)`** `J(E_P p_a) = a_P J(p_a)` at the actual residue | `tendsto_sievedContinuedSource_residue` |
| **`(21)`** `a_P^{-1} J(E_P p_a) = J(p_a)` | `tendsto_sievedContinuedSource_residue_normalized` |
| the conormal component of `(20)`: `a_P J(p_a) → 0` cofinally | `tendsto_sievedResidueValue_sievePrefix` |

`polarCoefficient_decimate` is `(15)` in the general form the card states it —
for every integer `q ≥ 1`, with no square condition: the finite prime part is
reindexed directly and the archimedean counterterm rescales by
`M_{W_q}(3/2) = q^{1/2} M_W(3/2)`.  The parent card proved only the square case,
because it moved along the bilateral ladder on both channels at once.

`tendsto_sievedContinuedSource_residue` needs no hypothesis beyond `0 < Re ρ`
and `ρ` being a zero of the pole-filled zeta.  The mechanism is exactly the one
the card describes: the Möbius expansion of `E_P` turns the sieved series into a
finite alternating combination of dilated continued sources, each inflation
contributes `d^{-(ρ+1/2)}` and each dilation `d^{ρ-1/2}`, these cancel to
`d^{-1}` independently of the zero, and `∑_{d ∣ M_P} μ(d)/d` is the Euler
product `a_P`.

Together, `tendsto_sievedContinuedSource_residue_normalized` and
`tendsto_sievedResidueValue_sievePrefix` are the two halves of the fracture
`(20)`--`(21)`: the coarse cofinal limit of the conormal component is zero, while
its source-normal normalization is the constant nonzero direction
`J(p_a)` at every finite stage.

Sections 5, 6 and the provable part of Section 7 are `[LEAN-PROVED]` in
`HTGeometry/PrimeSieveTransitionSize.lean` and, for the packaged character, in
`RHTower/BVPrimeWindowSieveResidue.lean`:

| Card item | Declaration |
|---|---|
| `(19)` `𝔠_P = (Q_P, Φ_P, a_P J(p_a))` | `RHTower.CompactBVPrimeWindow.relativeCharacter` |
| `(20)` `𝔠_P → 𝔠_∞ = (P_{\{1\}}, Φ_vac, 0)` | `RHTower.CompactBVPrimeWindow.tendsto_relativeCharacter` |
| `C_r = 2ζ(3)r³/(1-r²)` | `sieveRegularConstant`, `sieveRegularConstant_nonneg` |
| `sup_{\|t\|≤r} \|log Φ_P(t/p)\| ≤ C_r/p³` | `abs_sieveLogPhi_div_le`, `sSup_abs_sieveLogPhi_le` |
| `(22)` `δ_r(P,p) = a_P/p + sup_{\|t\|≤r} \|log Φ_P(t/p)\|` | `sieveTransitionSize` |
| `δ_r ≥ 0` and `δ_r(P,p) ≤ a_P/p + C_r/p³` | `sieveTransitionSize_nonneg`, `sieveTransitionSize_le` |
| `∑_p p^{-3} < ∞` along any enumeration | `injective_primeIndex`, `tendsto_primeIndex_atTop`, `summable_primeIndex_cube_inv` |
| **`(23)`** `∑_n δ_r(P_{n-1}, p_n) < ∞` | `summable_sieveTransitionSize` |
| `Tr(Q_∅^k) > 0`, hence `log Φ_∅(t) < 0` on `(0,1)` | `sieveTrace_empty_pos`, `sieveLogPhi_empty_neg` |
| the naive defect tends to `log Φ_∅(t)`, not to `0` | `tendsto_naiveRegularDefect` |
| **Section 6** regular channel diverges | `not_summable_naiveRegularDefect` |
| **Section 6** singular channel diverges | `not_summable_naiveSingularDefect` |

`summable_sieveTransitionSize` is `(23)` exactly as the card derives it: the
singular losses are the telescoping family of `(14)`, whose total is one, and the
regular increments are bounded by `C_r p^{-3}`, summable because the primes are
an injective subfamily of the integers.

The Section 6 no-go is proved as a genuine divergence, not merely as a failure of
one argument.  `sieveLogPhi_empty_neg` shows the unsieved logarithm is strictly
negative for `0 < t < 1` — every term of `(6)` at `P = ∅` is positive, and the
`j = 0` term already is — so by `tendsto_naiveRegularDefect` the independent
one-prime defects converge to a nonzero limit and `not_summable_naiveRegularDefect`
follows.  In the singular channel the independent defects are the prime
reciprocals, not summable.  Contrast `(23)`: the nested sieve's transitions are
summable in both channels simultaneously.  Higher-prime interaction is therefore
load-bearing, exactly as the card asserts.

Conjecture `(24)` is not proved on paper and is not a formalization target.

The statement is proved for an arbitrary enumeration `e : ℕ ≃ Nat.Primes`, so it
is the exact cofinal claim of `(14)`: the singular density has total cofinal
variation one along *every* prime exhaustion.

Remaining for this card: Section 1 (the commuting sieve on `ℓ²(ℕ_{>0})`, `(1)`--`(3)`),
Section 2 (the polarized `det₂` layer `(4)`--`(9)`; the corpus already owns the
regularized determinant germ `operatorFredholmDet2Germ` in
`HTGeometry/OperatorFredholmGerm.lean` and the Hilbert--Schmidt trace layer),
Sections 3's asymptotic `(11)`--`(12)`, Section 4 (`(15)`--`(18)`, the BV
principal-conormal coefficient), Section 5 (`(19)`--`(21)`), and Section 6.
Conjecture `(24)` is not proved on paper and is not a formalization target.

## Log

- 2026-07-29 — Replaced the divergent product of independent one-prime Wold defects by the
  commuting coprime sieve.  Proved absolute convergence of its regular determinant increments,
  total-variation convergence of its singular trace/BV coefficient, and the atomic coarse
  limit with nonzero normalized conormal blow-up.  Isolated `(24)` as the exact remaining
  source-to-Kummer estimate.
- 2026-07-29 — Normalization-amplification audit:
  `prime-valuation-conditioning-normalization-amplification-no-go.md` proves that the
  unnormalized loss \(a_P/p\) becomes the nonsummable conditional-state distance \(1/p\) after
  division by \(a_P\), and every finite conditioned state is at total-variation distance one
  from the weak atomic endpoint.  Equation `(24)` remains an RH-bearing cancellation statement,
  but it no longer follows from or is made plausible by `(23)`; deriving normalized strong
  convergence from the telescoping unnormalized character is retired.
