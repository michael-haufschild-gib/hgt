# Commutative endpoint, first-failure reconstruction, and swap-current law

- **ID:** ULF-OFCM-1
- **Stage:** 5-failed
- **Type:** FALSIFIED AS FIELD MECHANISM
- **Source:** ULF-CDM-2 ordered defect conservation; hostile attack on ULF-LSM-3 commuting-formation order erasure
- **Statement:** Ordered first-failure coordinates reconstruct an ordered finite survival factorization, but this is the classical hazard/stick-breaking parametrization and its swap current is an exact coordinate coboundary.
- **Status:** [MATHEMATICALLY TRUE] [FIELD CLAIM RETIRED] [REDISCOVERED PARAMETRIZATION] [POSITIVE SURVIVOR PROMOTED] [NO LEAN]

## Retired claim

For `s=(s_1,...,s_k) in (0,1)^k`, put

\[
 P=\prod_i s_i,
 \qquad
 q_i=\frac{(\prod_{j<i}s_j)(1-s_i)}{1-P}.
 \tag{OFC.1}
\]

The map `s |-> (P,q)` is bijective, with the recursive inverse

\[
 s_i=1-\frac{(1-P)q_i}{\prod_{j<i}s_j}.
 \tag{OFC.2}
\]

An adjacent exchange of `x=s_i` and `y=s_{i+1}` changes only two coordinates:

\[
 q(\tau_i s)-q(s)
 =\frac{R_i(x-y)}{1-P}(e_i-e_{i+1}),
 \qquad R_i=\prod_{j<i}s_j.
 \tag{OFC.3}
\]

These identities are correct. They do not define a new chronology geometry.

## Exact killing mechanism

### 1. Hazard/stick-breaking equivalence

Let `w_i=(1-P)q_i`. Then

\[
 w_i=\left(\prod_{j<i}s_j\right)(1-s_i),
 \qquad
 P+\sum_i w_i=1.
 \tag{OFC.4}
\]

This is precisely the finite residual-allocation or stick-breaking transform, written with
survivals rather than break proportions. Equation `(OFC.2)` is its standard triangular inverse.
The reliability interpretation is the discrete hazard parametrization of first failure.

### 2. The swap current is exact

The map `q` is a globally defined coordinate on the ordered factorization chamber. Therefore every
edge current is the coboundary

\[
 J_i(s)=q(\tau_i s)-q(s)=\delta q(s,\tau_i s).
 \tag{OFC.5}
\]

For every closed word in adjacent transpositions, the sum of transported increments telescopes to
zero. Coxeter and braid conservation are consequences of endpoint equality, not independent
holonomy. No gauge-invariant class survives.

### 3. Source specialization adds no new law

Putting `s_i(n)=L_{\nu_i}(n)^2` supplies a source-generated instance of `(OFC.1)`, but changes
neither the triangular inverse nor the coboundary calculation. It therefore does not overcome the
existing theorem that commuting formation endpoints erase schedule.

## Parent collision

- Samaniego and Jones, *Maximum Likelihood Estimation for a Class of Multinomial Distributions
  Arising in Reliability*, JRSS B 43 (1981), 46--52, already recover heterogeneous Bernoulli
  parameters through elementary symmetric functions.
- Marichal, Mathonet, and Waldhauser,
  [*On signature-based expressions of system reliability*](https://arxiv.org/abs/1010.0162),
  place permutation-symmetrized failure information in established reliability-signature theory.
- Finite residual-allocation/stick-breaking coordinates are standard probability machinery.

The exact formulas may remain useful notation. They fail the field-progress gate because they add
no nontrivial inter-organ conservation, reconstruction, or prediction.

## Strongest positive survivor

Do not preserve order. Average first-failure formation over all execution permutations and observe
it at every source moment. The resulting symmetric history reconstructs the entire **unordered
multiset of source probability laws**, not merely a finite vector of survival numbers. Its proof
forces a fusion of:

1. first-failure conservation;
2. elementary symmetric reconstruction;
3. Hausdorff moment determinacy;
4. multiplicative-convolution factorization after removal of the absorbing zero;
5. compact symmetric-product properness.

This survivor is proved in
`permutation-averaged-first-failure-symmetric-convolution-tomography-and-compact-properness-law.md`
at Stage 2.

## New insight

Ordered history was the wrong carrier: it retained information only by choosing a schedule.
Permutation averaging removes that gauge choice but does **not** destroy the factors. Across the
full response tower, the symmetric coefficient measures form a characteristic polynomial in a
convolution domain and recover the unordered formation law. The field-relevant primitive is thus a
formation polynomial with a determinate test tower, not an ordered hazard chart.

## No-go closure

- **Exact killing theorem/mechanism:** `(P,q)` is finite hazard/stick-breaking; swap current is the exact coboundary `delta q`.
- **Strongest positive survivor:** permutation-averaged measure-valued tomography with compact proper inverse.
- **New insight:** quotienting schedule can retain complete formation information when all symmetric coefficient measures are observed.
- **Status:** retired without Lean; dependency-closed survivor promoted separately to Stage 2.

## Log

- 2026-08-14 -- opened as a candidate vertical chronology law.
- 2026-08-14 -- retired after reliability/stick-breaking and coboundary audits; positive survivor promoted.
