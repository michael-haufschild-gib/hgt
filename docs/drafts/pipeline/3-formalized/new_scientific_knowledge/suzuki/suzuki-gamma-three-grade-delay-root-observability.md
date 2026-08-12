# Gamma transport first changes Suzuki's prime normal expansion at grade three

- **ID:** `suzuki-gamma-three-grade-delay-root-observability`
- **Stage:** 3 — formalized in Lean 4
- **Type:** SHARP ASYMPTOTIC / ROOT-PORT OBSERVABILITY LAW
- **Scientific status:** `[PROVED HERE] [NEW SCIENTIFIC KNOWLEDGE]`
  `[NOVELTY UNVERIFIED] [NOT RH]`
- **Inputs:** `suzuki-gamma-homogeneous-half-log-scattering-classification.md`,
  `suzuki-prime-normal-binomial-resolvent.md`,
  `suzuki-root-retained-exterior-dilation.md`
- **Route:** Connes/CCM restricted-Weil form through Suzuki completed zero modes

## 1. Result

Let \(X\) be a complex Hilbert space and \(T=T^*\in\mathcal B(X)\).  Let \(F_\Gamma\) be any
tempered homogeneous solution of

```text
(2L I+R-T)F_Gamma'(L)+F_Gamma(L)=0                    (1)
```

with frequency channel vectors \(c_+,c_-\in X\) and half-log trace

```text
beta
 =1/(2 sqrt(pi))
  [exp(i pi/4)c_+ + exp(-i pi/4)c_-].                  (2)
```

Let

```text
P_T(beta)(L)=(L I-T/2)^(-1/2)beta                     (3)
```

be the exact prime-normal binomial solution.  Then the previous
\(O(L^{-1})\) comparison sharpens to

```text
F_Gamma(L)-P_T(beta)(L)=O_X(L^(-7/2)).                 (4)
```

More precisely, the first Gamma correction is

```text
F_Gamma(L)-P_T(beta)(L)
 =C_Gamma(c_+,c_-)L^(-7/2)+O_X(L^(-9/2)),              (5)
```

where

```text
C_Gamma(c_+,c_-)
 =zeta(3) Gamma(7/2)/(6 pi)
   [i exp(i7pi/4)c_+ -i exp(-i7pi/4)c_-].              (6)
```

Consequently the literal Gamma jump does not change prime grades zero, one, or two:

```text
F_Gamma(L)
 =L^(-1/2)beta
  +(1/4)L^(-3/2)T beta
  +(3/32)L^(-5/2)T^2 beta
  +O_X(L^(-7/2)).                                      (7)
```

Now let \(X=\ell^2(\{\mathrm{left},\mathrm{right}\}\times\Gamma_a)\), let \(P\) retain strict
interior vertices, and let the trace be supported on the two exterior roots:

```text
beta=beta_- e_(left,0)+beta_+ e_(right,0).              (8)
```

For Suzuki's Gamma-positive full adjacency

```text
T=sum_(p^j<=exp(2a)) w_(p,j)
   [U_(j e_p)+U_(-j e_p)],
w_(p,j)=(log p)/p^(j/2),                               (9)
```

put

```text
c_a^2=sum_(p^j<exp(2a)) (log p)^2/p^j.                 (10)
```

Then the first strict-interior observation is an exact scaled isometry:

```text
||P T beta||^2
 =c_a^2(|beta_-|^2+|beta_+|^2).                        (11)
```

Hence

```text
lim_(L->infinity) L^(3/2)P F_Gamma(L)
 =(1/4)P T beta,                                       (12)

lim_(L->infinity) L^3||P F_Gamma(L)||^2
 =(c_a^2/16)(|beta_-|^2+|beta_+|^2).                   (13)
```

For every

```text
a>(1/2)log 2,                                           (14)
```

one has \(c_a>0\).  Thus no nonzero endpoint half-log trace is dark at first prime grade in the
oriented root-retained carrier.  Opposite-end spatial resonances cannot cancel `(11)` because the
two root labels are orthogonal one-sided germ coordinates.

## 2. Gamma phase has a cubic zero

The exact Gamma multiplier is

```text
r(eta)
 =2 sum_(n>=1) eta^2/[n(n^2+eta^2)]
 =2 zeta(3)eta^2+O(eta^4).                             (15)
```

Its transport phase relative to the prime equation is

```text
phi(eta)=(1/2)integral_0^eta r(s)ds
         =zeta(3)eta^3/3+O(eta^5).                     (16)
```

Therefore

```text
exp(i phi(eta))
 =1+i zeta(3)eta^3/3+O(eta^5).                         (17)
```

The absence of constant, linear, and quadratic terms in `(17)` is the entire three-grade delay.
It uses the literal Gamma quotient; replacing \(R\) by an arbitrary bounded remainder would lose
the conclusion.

## 3. Complete positive-tail asymptotic

Choose an even cutoff \(\chi\) supported near frequency zero.  On the positive frequency half-line,
the difference between Gamma and prime channel integrands is

```text
chi(eta) eta^(-1/2)exp(-i eta T/2)
 [exp(i phi(eta))-1]c_+

=i zeta(3)/3 chi(eta)eta^(5/2)c_+
 +O_X(eta^(7/2)).                                      (18)
```

On the negative half-line, with \(\eta=-t\),

```text
chi(t)t^(-1/2)exp(i t T/2)
 [exp(-i phi(t))-1]c_-

=-i zeta(3)/3 chi(t)t^(5/2)c_-
 +O_X(t^(7/2)).                                        (19)
```

Abel-damped Fourier--Watson integrals give

```text
integral_0^infinity eta^(5/2)exp(+i eta L)deta
 =Gamma(7/2)exp(i7pi/4)L^(-7/2),

integral_0^infinity eta^(5/2)exp(-i eta L)deta
 =Gamma(7/2)exp(-i7pi/4)L^(-7/2).                      (20)
```

Using the inverse Fourier factor \(1/(2\pi)\), equations `(18)`--`(20)` give `(5)`--`(6)` for
the low-frequency part.  The \(O(\eta^{7/2})\) remainders give \(O(L^{-9/2})\).

The high-frequency part is rapidly decreasing on the positive terminal ray; the earlier
\(O(L^{-1})\) bound was not sharp.  To prove this without discarding the Gamma phase, use a smooth
dyadic partition \(\rho_j\) on \(|\eta|\asymp2^j\).  The exact operator phase derivative is

```text
B_L(eta)=[L+r(eta)/2]I-T/2.                            (21)
```

For \(L>\|T\|/2+1\), it is positive and

```text
||B_L(eta)^(-1)||<=C/(L+j)                             (22)
```

on the \(j\)-th block, because \(r(\eta)=2\log|\eta|+O(1)\).  Its \(m\)-th differentiated inverse
has the corresponding symbol bounds; \(r^{(k)}(\eta)=O_k(|\eta|^{-k})\) for \(k\ge1\).

Apply the commuting integration-by-parts operator

```text
(1/i)B_L(eta)^(-1)d/deta
```

\(N\) times on the block.  A physical \(L\)-derivative of order \(m\) inserts \(\eta^m\).
Every integration gains \(2^{-j}(L+j)^{-1}\), including derivatives falling on the block cutoff.
The block is therefore bounded by

```text
C_(m,N)2^[j(m+1/2-N)](L+j)^(-N).                       (23)
```

Choose \(N>m+1/2\).  Summing `(23)` over \(j\) gives \(O_{m,N}(L^{-N})\).  The negative frequency
tail is identical.  Thus the complete high-frequency Gamma and prime integrals differ by
\(O(L^{-N})\) for every \(N\), and the low-frequency calculation proves `(5)`.

For \(R=0\), the inverse Fourier prime-channel solution solves

```text
(2L I-T)F'+F=0
```

and has trace `(2)`.  Terminal uniqueness of that equation identifies it exactly with `(3)`.
Expanding `(3)` through \(T^2\) and adding `(5)` proves `(7)`. `QED`

## 4. Exact root-port observability

The root vectors in `(8)` are not strict-interior vertices.  For a strict visible prime power
\(p^j<e^{2a}\), the \(+\delta\) step sends

```text
(left,0)  ->(left,j e_p),    location -a+j log p,
(right,0) ->(right,j e_p),   location  a-j log p,       (24)
```

and both locations lie strictly in \((-a,a)\).  The \(-\delta\) steps go farther outside and are
deleted by \(P\).  At equality \(p^j=e^{2a}\), the \(+\delta\) step lands on the opposite endpoint
and is also deleted by strict projection.

Distinct prime powers have distinct valuation vectors.  Moreover the left and right root sectors
are orthogonal even when their physical locations coincide.  Therefore

```text
P T beta
 =sum_(p^j<exp(2a)) w_(p,j)
   [beta_- e_(left,j e_p)+beta_+ e_(right,j e_p)],      (25)
```

an orthogonal sum.  Taking its squared norm proves `(11)`.

Project `(7)`.  Since \(P\beta=0\),

```text
P F_Gamma(L)
 =(1/4)L^(-3/2)P T beta+O_X(L^(-5/2)).                 (26)
```

Equations `(12)`--`(13)` follow from `(11)` and `(26)`.  Finally \(2<e^{2a}\) is equivalent to
`(14)`, and the \(p=2,j=1\) term makes \(c_a>0\). `QED`

## 5. Spatial regularity consequence and exact limit

The observed profile \(L^{-3/2}\) is in unweighted \(H^1(dL)\cap L^2(dL)\), but not in spatial
\(H^1(dr)\).  Indeed \(r=e^{-L}\) gives

```text
integral_0^epsilon
 |d/dr [(-log r)^(-3/2)]|^2 dr

=(9/4)integral_(L_epsilon)^infinity
 exp(L)L^(-5)dL

=infinity.                                             (27)
```

More generally no nonzero inverse-log power has a derivative in a positive exponential
\(L^2\) weight.  Thus, once the literal completed-source normal-family intertwiner is proved,
`(13)` gives a sharp source observable:

```text
nonzero endpoint trace
 -> nonzero first prime descendant
 -> failure of spatial H1 at an oriented interior seam. (28)
```

The theorem does not yet apply `(28)` directly to every completed zero mode: that final arrow
still requires the exact source intertwiner.  It does prove there is no cancellation mechanism
inside the complete prime--Gamma normal carrier that could hide \(\beta\ne0\) through Gamma
transport, word collision, opposite-end resonance, or higher grade.

For \(a\le(1/2)\log2\), the prime observation constant vanishes because no prime seam lies strictly
inside.  This is not a dark state of a nontrivial prime graph; the graph has no strict-interior
prime edge.  Small-aperture corona detection must use the polar--Gamma or direct prolate channel.

## 6. Exact frontier movement

```text
Gamma versus prime asymptotic:
  equality through prime grade two;                     [CLOSED]

first Gamma correction:
  explicit zeta(3) grade-three coefficient;             [CLOSED]

root-port first-prime observation:
  exact scaled isometry for a>(log 2)/2;                 [CLOSED]

normal-carrier nonzero-trace cancellation:
  impossible at first interior grade;                   [CLOSED]

completed zero mode -> normal carrier:
  prove source/cutoff intertwining;                      [OPEN]

trace-zero inverse-log-flat channel:
  prove weighted Gamma-subcritical forcing;             [OPEN]
```

This replaces the earlier qualitative \(O(L^{-1})\) Gamma comparison by a sharp asymptotic and
exposes the first exact corona Gram observable.

## 7. Hostile audit

1. **No \(O(L^{-1})\) contamination.**  The complete high-frequency Gamma phase is controlled
   dyadically to all orders; low frequency alone would not justify `(4)`.
2. **No Gamma deletion.**  Its first nonzero effect is computed explicitly in `(6)`.
3. **No prime truncation.**  Formula `(3)` contains all grades; `(7)` is its justified asymptotic
   truncation.
4. **No spatial resonance cancellation.**  Oriented root labels are orthogonal before scalar
   evaluation.
5. **No false \(H^1\) conversion.**  Equation `(27)` explicitly distinguishes boundary-log
   \(H^1(dL)\) from spatial \(H^1(dr)\).
6. **No source-intertwiner claim.**  The carrier observable is not asserted for a completed mode
   until that mode has been mapped into the exact normal family.
7. **No RH claim.**  Trace-zero source regularity and two-port return injectivity remain open.
8. **No whole-Connes claim.**  Other producer classes remain live.

## 8. Novelty boundary

Watson's lemma, dyadic nonstationary phase, and orthogonality of valuation coordinates are
classical.  Candidate-new source knowledge is the exact conjunction

```text
literal Gamma phase begins at frequency degree 3
 -> Suzuki prime grades 0,1,2 are unchanged
 -> first interior root observation has exact Gram c_a^2
 -> every nonzero root trace is visible at grade 1.      (29)
```

Corpus search found no previous form of `(4)`--`(13)` or `(29)`.  External priority remains
unverified.

## 9. Lean target

`SuzukiRootPortFirstGradeObservability.lean` formalizes the source-arithmetic injectivity core:

```text
suzukiLeftRoot_step_admissible
suzukiRightRoot_step_admissible
suzukiFirstGrade_left_coordinate
suzukiFirstGrade_right_coordinate
suzukiFirstGrade_rootTrace_injective
```

Thus one strictly visible step unconditionally separates both root coefficients in the actual
oriented `lp` carrier.  **The exact finite-step squared norm sum `(11)` is now formal**, in

```text
formal/GaloisForLFunctions/RHTower/SuzukiRootPortObservationGram.lean
  suzukiRootPortObservation                 the compressed transported trace P T beta
  suzukiRootPortObservation_left_coordinate exact left descendant coordinate -w_i beta_-
  suzukiRootPortObservation_right_coordinate  exact right descendant coordinate -w_i beta_+
  suzukiRootPortObservation_norm_sq         (11) for any injective visible alphabet
  suzukiRootPortObservation_primePower_norm_sq  (11) at Suzuki's alphabet, c_a^2 = sum (log p)^2/p^j
  two_visible_of_gt_half_log_two            (14): 2^1 is strictly visible past (log 2)/2
  suzukiRootPort_gram_pos                   c_a^2 > 0 on any alphabet containing 2^1
  suzukiRootPortObservation_ne_zero         no nonzero endpoint trace is dark at first grade
```

All audit to `[propext, Classical.choice, Quot.sound]`.  The analytic asymptotic `(4)` depends on
the Hilbert-valued oscillatory Gamma theorem still absent from Lean and is not introduced as an
axiom; it is a named shared-infrastructure target, not a gate of this card.

## Gates

- [x] prove Gamma phase has exact cubic zero
- [x] prove high-frequency Gamma tail is rapidly decreasing on the positive terminal ray
- [x] compute first Gamma correction at \(L^{-7/2}\)
- [x] prove prime grades zero, one, and two are unchanged
- [x] compute exact root-port observation Gram
- [x] prove first-grade injectivity for \(a>(\log2)/2\)
- [x] prove inverse-log first descendant is not spatial \(H^1\)
- [x] formalize strict-step root-port coordinate injectivity in Lean
- [x] formalize exact finite-step root-port observation Gram in Lean
- [ ] prove completed-source normal-family intertwining
- [ ] close trace-zero weighted source gate
- [ ] RH or whole-program no-go
