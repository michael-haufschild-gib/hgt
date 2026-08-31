# Integrable cocycle descent, Hahn rapidity, and compact-recurrence neutrality law

- **ID:** ULF-TAFM-7
- **Stage:** 3-formalized
- **Status:** `[PAPER-PROVED]`; `[LEAN-CERTIFIED]`; `[BRIDGE]`
- **Lane:** topologically admitted formation mechanics
- **Claim:** continuous descent is unnecessary: an open real formation character vanishes whenever
  it is the translation increment of one integrable potential on a finite invariant observer law
- **Parents:** ULF-TAFM-4 through ULF-TAFM-6, compact recurrence character descent, Haar
  translation invariance, Radon--Nikodym reconstruction

## 1. Field correction

The prime-circle selection interface currently asks the recovered real modular character to extend
continuously through a compact recurrent observer. That is sufficient but unnecessarily rigid. The
source corpus more naturally produces measurable densities, likelihood ratios, finite variation,
and finite information work than continuous real characters on a compact quotient.

The correct primitive is an **integrable translation potential**. Let `L` be an additive formation
group, let `K` be a compact abelian phase quotient with Haar probability `m`, let

`i : L -> K`

be a formation map, and let `chi : L -> R` be an open lifted character. An integrable potential for
`chi` is a function `u in L1(K,m)` satisfying

\[
 u(x+i(\ell))=u(x)+\chi(\ell)
 \quad\text{for }m\text{-almost every }x,
 \tag{ICD.1}
\]

for every `ell in L`.

This is a gauge equation. The compact observer sees `x`; the open history is the additive increment
`chi`. Changing `u` by a translation-invariant integrable function changes the gauge but not the
increment. Nonzero `chi` is holonomy of the lifted history.

## 2. Exact integrable-cocycle conservation law

### Theorem 2.1 -- finite invariant mass kills constant additive holonomy

Let a group `L` act measure-preservingly on a finite measure space `(K,m)`, with
`0 < m(K) < infinity`. Suppose `u in L1(K,m)` and

\[
 u(\ell x)=u(x)+\chi(\ell)
 \quad m\text{-almost everywhere}
 \tag{ICD.2}
\]

for every `ell`, where `chi : L -> R` is additive. Then `chi=0`.

#### Proof

Fix `ell`. Measure preservation and integrability give

\[
 \int_K u\,dm
 =\int_K u(\ell x)\,dm
 =\int_K (u(x)+\chi(\ell))\,dm
 =\int_K u\,dm+\chi(\ell)m(K).
\]

Hence `chi(ell)m(K)=0`. Since `m(K)>0`, `chi(ell)=0`. This holds for every `ell`. QED.

The identity is exact. No continuity, pointwise boundedness, uniform modulus, compactness theorem,
or limiting argument is used after the invariant finite law exists.

### Corollary 2.2 -- compact Haar classification

For a compact abelian group `K` with Haar probability and any formation map `i : L -> K`,

\[
 \boxed{\text{an integrable translation potential for }(i,\chi)\text{ exists}
 \iff \chi=0.}
 \tag{ICD.3}
\]

The forward implication is Theorem 2.1. For `chi=0`, the zero potential works. Notice that density
or injectivity of `i` is unnecessary for the conservation identity; those conditions matter only
when the observer must retain every finite history.

## 3. Hahn/Radon--Nikodym fusion

Let `P,Q` be finite positive measures on `K`, let `lambda=P+Q`, and write

\[
 h=\frac{d(Q-P)}{d\lambda}.
 \tag{ICD.4}
\]

ULF-TAFM-6 proves that `h` is integrable and reconstructs the signed current exactly:

\[
 Q-P=h\lambda,
 \qquad
 |Q-P|=|h|\lambda.
 \tag{ICD.5}
\]

Assume the prior-weighted experiment is phase-normalized so that `lambda` is Haar probability, and
assume its canonical density carries the formation increment

\[
 h(x+i(\ell))=h(x)+\chi(\ell)
 \quad\lambda\text{-almost everywhere}.
 \tag{ICD.6}
\]

### Theorem 3.1 -- integrable Hahn-current neutrality

Under `(ICD.4)`--`(ICD.6)`, `chi=0`.

#### Proof

Radon--Nikodym integrability supplies `h in L1(K,lambda)`. Since `lambda` is Haar, `(ICD.6)` makes
`h` an integrable translation potential. Corollary 2.2 gives `chi=0`. QED.

This is the promised three-organ fusion:

1. positivity supplies finite invariant Haar mass;
2. Hahn/Radon--Nikodym reconstruction supplies an automatic `L1` source potential;
3. compact recurrence supplies the phase quotient on which translations preserve mass;
4. gauge holonomy is the recovered open character and must vanish.

The hypothesis still has real content: exact affine covariance `(ICD.6)` is not automatic from
absolute continuity. The theorem turns the missing producer from uniform continuity of a real
character into one source-native covariance identity for an already integrable density.

## 4. Rapidity interpretation

For equivalent binary laws, posterior contrast lies in `(-1,1)`. Its inverse hyperbolic tangent is
half the log-likelihood ratio:

\[
 r=\operatorname{artanh}(h)
   =\frac12\log\frac{dQ}{dP}.
 \tag{ICD.7}
\]

The bounded contrast is the positive observer quotient; `r` is its open rapidity lift. Exponential
tilts translate `r`, while `tanh` returns to the bounded phase coordinate. Thus the same mechanism
has two exact failure modes off the neutral locus:

- the rapidity lift is not integrable against the invariant compact observer law; or
- it fails the translation-coboundary identity on the completed observer.

This identifies “noncompactness” without treating it as metaphor: nonzero modular holonomy cannot
be represented by finite-information `L1` rapidity on a recurrent finite-mass quotient.

## 5. Fourth-organ prediction: prime-circle modular selection

Let

\[
 L_P=\bigoplus_{p\text{ prime}}\mathbb Z,
 \qquad
 \lambda(c)=\sum_p c_p\log p,
 \qquad
 i_P(c)=[\lambda(c)]\in\mathbb R/\mathbb Z.
\]

The corpus proves that `i_P` is injective and dense. For `t in R`, put

\[
 \chi_t(c)=t\lambda(c).
 \tag{ICD.8}
\]

### Theorem 5.1 -- prime modular `L1` descent classification

There exists `u in L1(R/Z,Haar)` satisfying

\[
 u(x+i_P(c))=u(x)+t\lambda(c)
 \quad\text{almost everywhere for every }c
 \tag{ICD.9}
\]

if and only if `t=0`.

#### Proof

Corollary 2.2 gives existence iff `chi_t=0`. Evaluating at the history supported at prime `2` with
coefficient one gives `t log 2=0`; since `log 2 != 0`, this is equivalent to `t=0`. QED.

For the theta-source recovered conormal current, the corpus identifies

\[
 t_\rho=2\operatorname{Re}\rho-1.
 \tag{ICD.10}
\]

Therefore an integrable prime-circle translation potential exists for a divisor copy `rho` iff
`Re rho=1/2`; existence for every copy is equivalent to RH. Functional-equation reflection sends
`t_rho` to `-t_rho` and a potential `u` to `-u`, so the formation law is information-neutral under
reflection.

## 6. Why this advances the producer

The continuous-descent interface demanded a uniform boundary modulus for an unbounded recovered
log character. The new interface needs only:

1. one finite invariant observer law;
2. one integrable source potential, obtainable from finite variation or finite likelihood work;
3. exact translation covariance before choosing a zero.

This is a strictly weaker regularity demand: an `L1` potential need not be bounded or continuous.
It is also falsifiable. Any candidate source potential with nonzero modular rate must lose
integrability or covariance, and the failure can be measured as information escape.

The exact remaining source theorem is:

`[OPEN CORE]` Construct a divisor-independent prime-circle source potential from the theta/prime
formation current, prove finite Haar `L1` work and the affine covariance `(ICD.9)`, then recover its
divisor fibres. The present law proves that such a construction forces neutral horizontal grade.

No existence of that potential, and therefore no RH proof, is asserted here.

## Gates

- [x] 0 -> 1: mechanism and falsifiers isolated
- [x] 1 -> 2: dependency-closed conservation, Hahn fusion, and prime prediction proved
- [x] 2 -> 3: generic Hahn/Haar law and prime-circle/RH interface formalized unconditionally
- [ ] 3 -> 4: external synthesis and significance audit

## Log

- 2026-08-31 -- replaced continuous character descent by exact Haar-`L1` coboundary conservation;
  fused compact recurrence, gauge holonomy, and measurable Hahn reconstruction; predicted prime
  modular selection from an integrable rather than continuous source potential.
- 2026-08-31 -- Lean-certified generic `L1` cocycle classification, Hahn-density specialization,
  prime-circle classification, functional-equation neutrality, and global RH equivalence.
