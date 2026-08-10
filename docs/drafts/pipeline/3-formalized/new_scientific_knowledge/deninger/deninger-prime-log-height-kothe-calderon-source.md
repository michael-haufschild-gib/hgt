# Prime-log height Köthe Calderón source

- **ID:** deninger-prime-log-height-kothe-calderon-source
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Scientific status:** `[PROVED HERE] [LEAN-PROVED] [NOT RH]`
- **Label:** DAC_PRIME_LOG_HEIGHT_KOTHE_CALDERON_SOURCE
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/DeningerPrimeLogHeight.lean`,
  `DeningerKotheComplete.lean`,
  `DeningerPrimeLogHeightKothe.lean`,
  `DeningerPrimeLogHeightConvolution.lean`,
  `DeningerPrimeLogHeightGreen.lean`,
  `DeningerPrimeLogHeightForms.lean`,
  `DeningerPrimeLogHeightMellin.lean`,
  `DeningerPrimeLogHeightPower.lean`,
  `DeningerPrimeLogHeightCartan.lean`
- **Parent:** deninger-arithmetic-calderon-green-intermediate-extension
- **Statement:** Rational Kummer character lattice has a canonical nuclear height-Köthe
  completion on which signed prime-log generator, Green inverse, odd Hodge sign, Hardy projectors,
  convolution, reflection, positive powers, and every finite-order centered Mellin jet are
  continuous; its positive Green graph is a closed Lagrangian relation.

## Goal

Route L has a real small-divisor obstruction. On an ordinary Hilbert completion, signed prime-log
frequencies
\[
 \ell(m)=\sum_p m_p\log p
\]
have no positive global gap. Hence inverse Green generator is unbounded and finite positive
Hodge--Koszul contractions need not be equicontinuous. Fixed Sobolev completion cannot repair
this.

Source already carries canonical multiplicative height
\[
 H(m)=\prod_p p^{|m_p|}.
\]
Previously proved prime-log height inequality absorbs inverse small divisor after one height step.
This card proves that taking every height step, rather than one Hilbert norm, produces a concrete
nuclear source carrying full free-unit Calderón/Hodge package.

No zeta zero, divisor-selected vector, RH premise, or numerical computation enters.

## Source and theorem

Let \(\Gamma=\mathbb Z^{(\mathbb P)}\) be finitely supported integer prime-exponent lattice. Put
\[
 H(m)=\prod_p p^{|m_p|},\qquad
 \ell(m)=\sum_p m_p\log p.                                      \tag{1}
\]
Then
\[
 H(m+n)\le H(m)H(n),\quad H(-m)=H(m),\quad
 \ell(m+n)=\ell(m)+\ell(n).                                     \tag{2}
\]
For \(k\in\mathbb N\), define
\[
 p_k(a)=\sum_{m\in\Gamma}H(m)^k|a_m|,\qquad
 \mathscr K_H=\{a:p_k(a)<\infty\text{ for every }k\},
 \quad \mathscr K_H^0=\{a\in\mathscr K_H:a_0=0\}.                \tag{3}
\]

**Theorem [PROVED HERE] [DAC_PRIME_LOG_HEIGHT_KOTHE_CALDERON_SOURCE].**

1. Seminorms \(p_k\) make \(\mathscr K_H\) a complete nuclear Fréchet algebra for
   \[
    (a*b)_r=\sum_{m+n=r}a_mb_n,
    \qquad p_k(a*b)\le p_k(a)p_k(b).                             \tag{4}
   \]
   Finitely supported group algebra is dense. Reflection and star
   \[
    (Ra)_m=a_{-m},\qquad (a^*)_m=\overline{a_{-m}}               \tag{5}
   \]
   are continuous seminorm isometries.

2. Coefficient multiplication
   \[
    (Da)_m=\ell(m)a_m                                            \tag{6}
   \]
   is a continuous derivation. Its kernel is the constant line and its range is exactly
   \(\mathscr K_H^0\). On that range,
   \[
    (D^{-1}a)_m=\ell(m)^{-1}a_m                                 \tag{7}
   \]
   is continuous, with
   \[
    p_k(Da)\le p_{k+1}(a),\qquad
    p_k(D^{-1}a)\le p_{k+1}(a).                                 \tag{8}
   \]
   Thus
   \[
    0\longrightarrow\mathbb C\delta_0
      \longrightarrow\mathscr K_H
      \mathop{\longrightarrow}^{D}\mathscr K_H^0
      \longrightarrow0                                         \tag{9}
   \]
   is split strict exact in the Fréchet category.

3. On \(\mathscr K_H^0\), define
   \[
   \begin{aligned}
    (Aa)_m&=|\ell(m)|a_m,&
    (Ga)_m&=|\ell(m)|^{-1}a_m,\\
    (Wa)_m&=i\,\operatorname{sgn}(\ell(m))a_m,&
    (\Pi_\pm a)_m&=\mathbf 1_{\{\pm\ell(m)>0\}}a_m .
   \end{aligned}                                                 \tag{10}
   \]
   Then \(A\) and \(G=A^{-1}\) are continuous inverse automorphisms, \(W\) is a continuous
   seminorm isometry, and
   \[
    W^2=-1,\quad \Pi_\pm^2=\Pi_\pm,\quad
    \Pi_+\Pi_-=0,\quad \Pi_++\Pi_-=1,\quad
    W=i(\Pi_+-\Pi_-).                                            \tag{11}
   \]
   Ordinary order \(q>1\) versus \(q<1\) on positive rationals therefore produces an exact
   source Hardy orientation before Xi-divisor specialization.

   For \(r\ge0\), coefficientwise Poisson extension
   \[
    (P_ra)_m=e^{-r|\ell(m)|}a_m                                 \tag{11a}
   \]
   is a continuous seminorm contraction, with
   \[
    P_0=1,\qquad P_{r+t}=P_rP_t,\qquad
    \partial_rP_r=-AP_r.                                       \tag{11b}
   \]
   Hence \(A\) is the literal outward Dirichlet-to-Neumann operator of this global free-unit
   Poisson family.

4. Forms
   \[
    \langle a,b\rangle_0=\sum_m a_mb_{-m},\qquad
    \Psi(a,b)=i\sum_m\ell(m)a_mb_{-m}                            \tag{12}
   \]
   are continuous, and \(\Psi\) is alternating. With \(Ca=a^*\),
   \[
    \Psi(a,WCa)
      =\sum_{m\ne0}|\ell(m)|\,|a_m|^2
      =:\mathcal E(a)\ge0,                                      \tag{13}
   \]
   with equality exactly when \(a=0\) in \(\mathscr K_H^0\).

5. On \(\mathscr P_H=\mathscr K_H^0\oplus\mathscr K_H^0\), put
   \[
    \Omega((x,u),(y,v))
      =\langle u,y\rangle_0-\langle v,x\rangle_0.                \tag{14}
   \]
   Then
   \[
    \Lambda_H=\operatorname{Graph}(A)                            \tag{15}
   \]
   is closed and equals its symplectic annihilator inside \(\mathscr P_H\). It is a closed
   Lagrangian test relation with Green form \(\mathcal E\).

6. For positive integer \(q\), power map \(V_q\delta_m=\delta_{qm}\) is continuous and
   \[
   \begin{aligned}
    p_k(V_qa)&=p_{qk}(a),&
    DV_q&=qV_qD,& AV_q&=qV_qA,\\
    WV_q&=V_qW,& \Pi_\pm V_q&=V_q\Pi_\pm .
   \end{aligned}                                                 \tag{16}
   \]
   Reflection obeys
   \[
    DR=-RD,\quad AR=RA,\quad WR=-RW,\quad R\Pi_+=\Pi_-R.          \tag{17}
   \]

7. For every \(s\in\mathbb C\) and \(j\in\mathbb N\),
   \[
    \mathcal M_s^{(j)}(a)
      =
      \sum_m[-\ell(m)]^j
        e^{-(s-\frac12)\ell(m)}a_m                              \tag{18}
   \]
   is a continuous functional and satisfies
   \[
    \mathcal M_s^{(j)}(Ra)
      =(-1)^j\mathcal M_{1-s}^{(j)}(a).                          \tag{19}
   \]
   Completion retains every finite-order centered Mellin conormal jet at every complex
   parameter, not only on critical line.

## Proof

### Arithmetic small divisors and counting

For \(m\ne0\), write
\[
 M(m)=\prod_{m_p>0}p^{m_p},\qquad
 N(m)=\prod_{m_p<0}p^{-m_p}.
\]
They are coprime and
\[
 H(m)=M(m)N(m),\qquad \ell(m)=\log\frac{M(m)}{N(m)}.             \tag{20}
\]
Unique factorization gives \(M(m)\ne N(m)\). Existing prime-log height theorem gives
\[
 H(m)^{-1}\le|\ell(m)|.                                        \tag{21}
\]
Also
\[
 |\ell(m)|\le\sum_p|m_p|\log p=\log H(m)\le H(m).               \tag{22}
\]

Map \(m\mapsto(M(m),N(m))\) injects \(\Gamma\) into ordered positive-integer pairs. Hence, for
every \(\alpha>1\),
\[
 \sum_{m\in\Gamma}H(m)^{-\alpha}
 \le\sum_{M,N\ge1}(MN)^{-\alpha}
 =\zeta(\alpha)^2<\infty.                                      \tag{23}
\]

### Completeness and nuclearity

Each \(p_k\) is a weighted \(\ell^1\) norm. A sequence Cauchy for every \(p_k\) converges in each
weighted Banach space; continuity of coordinates makes these limits one common element of
\(\mathscr K_H\). Finite truncations converge in every seminorm.

For Köthe weights \(W_k(m)=H(m)^k\), choose \(l=k+2\). Equation (23) gives
\[
 \sum_m\frac{W_k(m)}{W_l(m)}
 =\sum_mH(m)^{-2}<\infty.                                      \tag{24}
\]
Grothendieck--Pietsch criterion therefore proves nuclearity. Köthe criterion already exists in
corpus; new use is exact source weight \(H(m)^k\).

### Algebra, Green inverse, and Hodge structure

Equation (2) and Tonelli give
\[
\begin{aligned}
 p_k(a*b)
 &\le\sum_{m,n}H(m+n)^k|a_m||b_n|\\
 &\le\sum_{m,n}H(m)^kH(n)^k|a_m||b_n|
 =p_k(a)p_k(b).
\end{aligned}
\]
Reflection preserves \(H\). Additivity of \(\ell\) proves Leibniz rule for \(D\).

Equations (21)--(22) give coefficientwise
\[
 |\ell(m)|\le H(m),\qquad |\ell(m)|^{-1}\le H(m)
\]
for \(m\ne0\), proving (8) for \(D,A,D^{-1},G\). Only zero of \(\ell\) is \(m=0\), so (9)
follows. Sign multiplier has modulus one and coordinate deletion decreases every seminorm, proving
(11). Since \(0<e^{-r|\ell(m)|}\le1\), each \(P_r\) decreases every \(p_k\); semigroup and
derivative identities in (11b) hold coefficientwise and pass through every seminorm by continuity
of \(A\). Coordinatewise half-line energy is
\[
 \int_0^\infty
   \left(|\partial_r(e^{-r|\ell(m)|}a_m)|^2
     +|\ell(m)e^{-r|\ell(m)|}a_m|^2\right)dr
 =|\ell(m)||a_m|^2.
\]
Tonelli and the bound \(\sum_mH(m)|a_m|^2\le p_1(a)p_0(a)\) recover (13) as total Poisson
Dirichlet energy.

Absolute convergence and continuity of (12) follow from
\[
 |\langle a,b\rangle_0|\le p_0(a)p_0(b),\qquad
 |\Psi(a,b)|\le p_1(a)p_0(b).                                  \tag{25}
\]
Changing \(m\) to \(-m\) proves alternation. At reflected index,
\[
 (WCa)_{-m}
 =-i\,\operatorname{sgn}(\ell(m))\,\overline{a_m},
\]
which proves (13).

Continuity of \(A\) makes graph closed. Symmetry
\[
 \langle Ax,y\rangle_0=\langle x,Ay\rangle_0
\]
makes graph isotropic. If \((y,v)\) annihilates every \((x,Ax)\), then
\(\langle v-Ay,x\rangle_0=0\) for every finitely supported \(x\). Coordinate separation gives
\(v=Ay\), proving maximality.

### Powers and Mellin jets

Since \(H(qm)=H(m)^q\), equation (16) is direct; positive \(q\) preserves sign of \(\ell\).
Equation (17) follows from \(\ell(-m)=-\ell(m)\).

For \(u=s-\frac12\),
\[
 |e^{-u\ell(m)}|
 \le e^{|\operatorname{Re}u|\,|\ell(m)|}
 \le H(m)^{|\operatorname{Re}u|},\qquad
 |\ell(m)|^j\le[\log H(m)]^j\le H(m)^j.                         \tag{26}
\]
Choosing integer \(k\ge|\operatorname{Re}u|+j\) bounds (18) by \(p_k(a)\). Substitution
\(m\mapsto-m\) proves (19).

## Cartan--Koszul consequence

Let \((C^\bullet,d)\) be any complete differential graded module over
\(\mathscr K_H\), graded by \(\Gamma\), whose topology is given by Köthe-graded seminorms
\(q_k(x)=\sum_m H(m)^k q(x_m)\) for a defining family of coefficient seminorms \(q\).
Assume \(d\) and the continuous contraction \(\iota\) preserve the \(\Gamma\)-grading, and let
the continuous operator \(L\) satisfy
\[
 d\iota+\iota d=L,\qquad
 L|_{C^\bullet_m}=\ell(m)\operatorname{id}.                     \tag{27}
\]
On completed nonzero-character part,
\[
 h=L^{-1}\iota                                                   \tag{28}
\]
is continuous by (8) and satisfies \(dh+hd=1\). Thus every nonzero arithmetic-character sector is
strictly contractible without a uniform prime-log gap.

For relative Sullivan--Milnor tower this reduces analytic limit problem to one sharply typed
verification: construct its arithmetic-character grading and Cartan contraction continuously on
this height completion. If verified, only total-character-zero Milnor sector can survive. This
card does not assume that verification and does not claim full Milnor conormal descent.

## Exact Route-L consequence

Theorem closes three pieces of former undifferentiated source obstruction:

1. all-prime rational Kummer character completion is concrete and nuclear;
2. gapless signed prime-log generator has continuous Green inverse after one source-height
   seminorm loss;
3. free analytic Poisson/Calderón graph, positive Hodge sign, and Hardy orientation exist globally
   before divisor specialization and retain every centered Mellin jet.

Therefore absence of uniform Kummer spectral gap is no longer a blocker by itself. At the level of
this theorem alone, the next incidence question is narrower:

> Construct arithmetic-character-graded Cartan action on actual Tate--Milnor/Sullivan conormal,
> then prove its zero-character sector, real apex, and radial Poisson/Meyer seam form a closed
> relation compatible with height-Köthe completion.

Zero-character sector is load-bearing: division by \(D\) there is impossible, and deleting it
would erase product-formula/Arakelov data. This theorem also does not identify ordinary-rational
Hardy split with Paugam upper spectral half.

Subsequent theorem `DAC_BALANCED_WORD_HEIGHT_BAR_STRICT_CONTRACTION` constructs an entire
product-letter-height bar resolution of the rational two-term Milnor target and split-contracts
its balanced sector without dividing by \(D\).  A second subsequent theorem,
`DAC_LINEARIZED_MILNOR_FIRST_SULLIVAN_STRICT_PRIMITIVE`, constructs the commutative first
attachment and a continuous primitive for the full completed base Milnor ideal.  Current first
source theorem is therefore cofinal control of genuine multiplicative syzygies beyond that layer
and comparison with the bar/pro-Stein conormal, followed by generic Kummer, real/product-formula,
and radial Poisson/Meyer attachment.  This does not erase the genuine Arakelov zero mode; it
separates it from spurious balanced-word completion homology.

## Failed conjectures and positive survivors

### Fixed Hilbert or fixed Sobolev completion

**Failure.** Nonzero signed prime-log frequencies approach zero, so \(D^{-1}\) is unbounded when
basis vectors have one fixed normalization.

**Positive survivor.** Inverse is tame on the projective limit: (8) gives a one-step
multiplicative-height estimate.  No optimality of that integer-indexed estimate is asserted.

### Polynomial weights in logarithmic height

**Failure.** Take consecutive integers \(M=N+1\), regarded through their prime-exponent vectors.
Then \(H=MN\), while
\(
 |\log(M/N)|^{-1}=|\log(1+1/N)|^{-1}\ge N
\).
Thus the inverse grows exponentially in \(\log H\) along this family, so no fixed polynomial in
\(\log H\) absorbs every inverse mode.

**Positive survivor.** Polynomial weights in multiplicative height, equivalently exponential
weights in logarithmic height, are sufficient and source-derived.

### One exponential-height Hilbert level

**Failure.** Estimate (8) shifts level \(k\) to \(k+1\), not one level to itself.

**Positive survivor.** Projective intersection of all levels is stable, complete, nuclear, and
retains all Mellin jets.

## Hostile audit

- Prime-log height inequality is existing corpus infrastructure, not new.
- Köthe nuclearity, convolution estimates, graph Lagrangians, and Cartan contraction are parent
  mathematics.
- New content is source-exact conjunction: already-forced prime-log height is tame scale for
  Deninger gapless Kummer generator, yielding global all-prime nuclear Calderón/Hodge source and,
  before the subsequent balanced-word theorem, isolating the next obstruction at total character
  zero plus Poisson/Meyer seam.
- Hardy projectors here live on rational Kummer height source. They do not complement Meyer
  positive Poisson embedding in his nuclear space.
- Mellin-jet continuity proves non-erasure, not positivity of \(M_\zeta\), and not RH.
- Full arithmetic relation still needs actual Sullivan--Milnor Cartan grading, real orientation
  attachment, and strict radial Poisson comparison.

Targeted corpus and arXiv searches found ingredients separately but no use of prime-exponent height
Köthe scale to make Deninger prime-log Green inverse continuous and construct this package. This is
noncollision, not priority claim.

## Lean statements

The source is `deningerHeightKotheData` on the lattice `DeningerLattice = Nat.Primes →₀ ℤ`, with
`deningerHeight` for `H`, `deningerFreq` for `ℓ`, and `deningerHeightSeminorm k` for `p_k`.

| Card item | Lean declaration |
|---|---|
| `(2)` submultiplicativity, evenness, additivity | `deningerHeight_add_le`, `deningerHeight_neg`, `deningerFreq_add`, `deningerFreq_neg` |
| `(20)`--`(21)` height bound | `deningerHeightNat_eq_primeLogHeight`, `deningerHeight_inv_le_abs_freq` |
| `(22)` upper bound | `abs_deningerFreq_le_log_height`, `log_deningerHeight_le_height` |
| `(23)` counting | `deningerHeight_summable_inv_sq` |
| `(3)` the space and its seminorms | `DeningerHeightKothe`, `deningerHeightSeminorm`, `deningerHeightKotheZero` |
| `(1)` completeness | `deningerKothe_exists_limit`, `deningerHeightKothe_exists_limit` |
| `(24)` nuclearity | `deningerHeightKotheData_isNuclear`, `deningerHeightKothe_isNuclearSpace` |
| `(4)` convolution algebra | `deningerHeightConv`, `deningerHeightSeminorm_conv_le`, `deningerHeightConv_comm`, `deningerHeightConv_assoc`, `deningerHeightConv_delta_zero_left` |
| `(1)` density of the group algebra | `deningerKothe_exists_finite_approx`, `deningerHeightKothe_exists_finite_approx` |
| `(5)` reflection and star | `deningerHeightReflect`, `deningerHeightStar`, `deningerHeightSeminorm_reflect`, `deningerHeightSeminorm_star` |
| multiplier calculus | `deningerHeightMul`, `deningerHeightSeminorm_mul_le` |
| `(6)`, `(7)`, `(8)` | `deningerGenerator`, `deningerGreen`, `deningerHeightSeminorm_generator_le`, `deningerHeightSeminorm_green_le` |
| `(9)` split strict exactness | `deningerGenerator_ker_eq_span_delta`, `deningerGenerator_mem_zero`, `deningerGenerator_green`, `deningerGenerator_surjective_onto_zero` |
| `(10)` the four operators | `deningerModulus`, `deningerModulusGreen`, `deningerHodgeSign`, `deningerHardyPlus`, `deningerHardyMinus` |
| `(11)` Hodge/Hardy relations | `deningerHodgeSign_sq`, `deningerHardyPlus_idem`, `deningerHardyMinus_idem`, `deningerHardy_mul_eq_zero`, `deningerHardy_add_eq_id`, `deningerHodgeSign_eq_hardy_sub` |
| `(11a)`, `(11b)` Poisson family | `deningerPoisson`, `deningerHeightSeminorm_poisson_le`, `deningerPoisson_zero`, `deningerPoisson_add`, `deningerPoisson_hasDerivAt` |
| `(12)`, `(25)` the two forms | `deningerPairing`, `deningerPsi`, `deningerPairing_norm_le`, `deningerPsi_norm_le`, `deningerPsi_antisymm` |
| `(13)` Green energy | `deningerEnergy`, `deningerPsi_hodgeStar`, `deningerEnergy_nonneg`, `deningerEnergy_eq_zero_iff` |
| `(14)`, `(15)` Lagrangian graph | `deningerLagrangian_isotropic`, `deningerLagrangian_maximal`, `deningerLagrangian_closed` |
| `(16)` power maps | `deningerPower`, `deningerHeightSeminorm_power`, `deningerPower_generator`, `deningerPower_modulus`, `deningerPower_hodgeSign`, `deningerPower_hardyPlus`, `deningerPower_hardyMinus` |
| `(17)` reflection relations | `deningerReflect_generator`, `deningerReflect_modulus`, `deningerReflect_hodgeSign`, `deningerReflect_hardy` |
| `(18)`, `(19)` Mellin jets | `deningerMellinJet`, `deningerMellinJet_norm_le`, `deningerMellinJet_reflect` |
| `(27)`, `(28)` Cartan contraction | `deningerCartanHomotopy`, `deningerCartanContraction`, `deningerCartanContraction_seminorm_le` |

Reading conventions used by the formalization, all faithful to the paper statement:

- completeness is stated sequentially (`DeningerKotheCauchy` → `DeningerKotheTendsto`), which for a
  countable seminorm family is exactly Fréchet completeness;
- density of the finitely supported group algebra is stated as approximation of every vector by a
  truncation of its own coordinate expansion, in every seminorm;
- `(11b)`'s derivative identity is the coefficientwise one, which is how the paper proof produces
  it;
- closedness of the Lagrangian graph is stated as sequential closedness for the seminorm family;
- `(27)`--`(28)` are stated on an arithmetic-character piece with an abstract differential and
  contraction, which is the exact content of the Cartan argument.

## Gates

- [x] 0 → 1 in-progress: source object, hard obstruction, and falsifiers isolated
- [x] 1 → 2 fully-proven: all displayed claims proved above without RH-equivalent premise
- [x] 2 → 3 formalized: all seven numbered clauses and the Cartan--Koszul consequence proved
      unconditionally in Lean
- [x] targeted axiom audit: only `propext`, `Classical.choice`, `Quot.sound` (50 declarations)
- [x] modules wired into `RHTower.lean`
- [ ] 3 → 4 publication-ready: integrate after independent specialist audit and actual
      Sullivan--Milnor comparison

## References

- Existing corpus theorem:
  ../../../3-formalized/not_new_scientific_knowledge/prime-log-height-bound.md.
- Existing corpus infrastructure: DeningerKotheSpace, DeningerPowerNaturality,
  DeningerRelativeSullivanMilnorLimit, DeningerBoundaryHodgeOperator, and
  DeningerArithmeticPositiveCalderonKoszul.
- Ralf Meyer, A spectral interpretation for the zeros of the Riemann zeta function,
  arXiv:math/0412277.
- Christopher Deninger, Dynamical systems for arithmetic schemes, arXiv:1807.06400.

## Log

- 2026-08-10 — Formalized the whole theorem unconditionally: prime-log height algebra and
  counting, the Köthe source with completeness, nuclearity and dense group algebra, the
  convolution algebra with submultiplicative seminorms, the multiplier calculus giving the Green
  inverse and the whole Hodge/Hardy/Poisson package, the two forms with the Green energy identity
  and its definiteness, the closed Lagrangian graph, the power and reflection relations, every
  centered Mellin jet with its functional equation, and the Cartan contraction. Card promoted to
  `3-formalized`.
- 2026-08-08 — Rejected fixed-Hilbert, logarithmic-Sobolev, and single-height repairs. Constructed
  multiplicative-height Köthe source; proved nuclearity, strict Green inversion, cup--Hodge
  positivity, exact Hardy orientation, Lagrangian graph, source functoriality, and continuity of
  all centered Mellin jets. Localized remaining incidence problem to total-character-zero
  Sullivan--Milnor/real/Poisson seam.
