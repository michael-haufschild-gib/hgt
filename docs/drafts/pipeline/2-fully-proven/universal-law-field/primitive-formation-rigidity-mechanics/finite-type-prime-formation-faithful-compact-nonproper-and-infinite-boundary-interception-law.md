# Finite-type prime formation is faithful but compactly nonproper, forcing infinite boundary interception

- **ID:** ULF-PFRM-5
- **Stage:** 2 -- fully proven on paper
- **Type:** THEOREM / GLOBAL FORMATION--PROPERNESS CLASSIFICATION
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [BRIDGE]`
  `[COFINAL FAITHFULNESS] [HILBERT-SCHMIDT COMPACTNESS] [NONCLOSED RANGE]`
  `[ADAPTIVE ESCAPE] [FINITE BOUNDARY PORT NO-GO] [INFINITE-RANK SURVIVOR]`
  `[FUNCTIONAL-EQUATION INVARIANT] [NOT RH]`
- **Formal status:** not Lean-formalized. The prime-log uniqueness input is Lean-certified; the
  fused compactness/interception theorem is not yet an accepted AI proof under project rules.
- **Parents:**
  - `prime-jet-analytic-formation-transport-reporter-conservation-and-boundary-port-transmutation-law.md`;
  - `../formation-laplacian-properness-mechanics/source-response-laplacian-properness-pluecker-and-adaptive-escape-law.md`;
  - `formal/GaloisForLFunctions/RHTower/PrimeLogExponentialTypeUniqueness.lean`.

## 1. Purpose

The finite formation theorem found a derivative-carrying kernel at every prime aperture. The
formal prime-log uniqueness theorem proves that this kernel disappears cofinally on a
finite-exponential-type carrier. That closes algebraic formation faithfulness, but not selection.

This card proves the missing global properness classification:

\[
 \boxed{
 \text{summably weighted prime formation is injective but compact, hence nonproper}.}
 \tag{FCP.1}
\]

It also proves the decisive fourth-organ obstruction:

\[
 \boxed{
 \text{no finite-dimensional or compact boundary reporter can repair global properness}.}
 \tag{FCP.2}
\]

Therefore the required archimedean sector is not one scalar infinity port or any finite jet. It
must be an infinite-rank noncompact response that intercepts every adaptive prime-null sequence.

## 2. Abstract sampling setup

Let `H` be an infinite-dimensional complex reproducing-kernel Hilbert space of functions on a set
containing the prime-log nodes

\[
 \Lambda=\{\log p:p\text{ prime}\}.
 \tag{FCP.3}
\]

Write `k_p in H` for the representer of evaluation at `log p`:

\[
 f(\log p)=\langle k_p,f\rangle.
 \tag{FCP.4}
\]

Assume

\[
 \sup_p\|k_p\|\le K<\infty.
 \tag{FCP.5}
\]

Let `w_p>0` satisfy

\[
 \sum_p w_p<\infty.
 \tag{FCP.6}
\]

Define the global prime formation operator

\[
 A_w:H\longrightarrow\ell^2(\mathbb P),
 \qquad
 (A_wf)_p=\sqrt{w_p}\,f(\log p).
 \tag{FCP.7}
\]

## 3. Main theorem

### Theorem 3.1 -- faithful compact formation and adaptive escape

Assume every `f in H` is entire of finite exponential type. Then:

1. `A_w` is Hilbert--Schmidt and

   \[
   \boxed{
   \|A_w\|_{HS}^2
   =\sum_p w_p\|k_p\|^2
   \le K^2\sum_pw_p<\infty.}
   \tag{FCP.8}
   \]

2. `A_w` is injective.
3. `ran A_w` is not closed.
4. There is an orthonormal sequence `f_n in H` such that

   \[
   \boxed{\|A_wf_n\|_{\ell^2}\longrightarrow0.}
   \tag{FCP.9}
   \]

5. No positive constant `alpha` satisfies

   \[
   \|A_wf\|^2\ge\alpha\|f\|^2\qquad(f\in H).
   \tag{FCP.10}
   \]

Thus the all-prime response separates every fixed source law but admits unit adaptive histories of
vanishing formation energy.

#### Proof

Let `(e_p)` be the standard orthonormal basis of `ell^2(P)`. The adjoint satisfies

\[
 A_w^*e_p=\sqrt{w_p}\,k_p.
\]

Summing squared norms proves `(FCP.8)`, hence `A_w` is Hilbert--Schmidt and compact.

If `A_wf=0`, positivity of every `w_p` gives `f(log p)=0` for every prime. The formal theorem
`RHTower.eq_zero_of_exponentialType_of_primeLog_zeros` gives `f=0`, proving injectivity.

If `ran A_w` were closed, the bounded inverse theorem applied to the bijection
`A_w:H->ran A_w` would make `A_w` bounded below. The identity
`A_w^(-1) A_w` would then be compact, impossible on infinite-dimensional `H`. Therefore the range
is not closed and `(FCP.10)` fails.

For a direct adaptive witness, take any orthonormal sequence `f_n`. It converges weakly to zero;
compactness sends it to `A_wf_n->0` in norm, proving `(FCP.9)`. QED.

### Corollary 3.2 -- Paley--Wiener realization

For every bandwidth `sigma>0`, the Paley--Wiener space `PW_sigma^2` satisfies the hypotheses:

1. it is infinite-dimensional;
2. every member is entire of exponential type at most `sigma`;
3. real point evaluations have constant representer norm.

Hence every strictly positive summable prime weight gives an injective Hilbert--Schmidt prime
formation operator on `PW_sigma^2`, with nonclosed range and adaptive escape `(FCP.9)`.

This is a concrete source-independent model of global formation faithfulness without properness.

## 4. Boundary interception theorem

Let `Z` be another Hilbert space and let

\[
 R:H\longrightarrow Z
 \tag{FCP.11}
\]

be a boundary/archimedean response. Form

\[
 A_w^+f=(A_wf,Rf).
 \tag{FCP.12}
\]

### Theorem 4.1 -- compact boundary responses cannot unlock selection

If `R` is compact, then `A_w^+` is compact and is not bounded below. In particular:

1. no finite-dimensional boundary response repairs properness;
2. no finite collection of scalar archimedean ports repairs properness;
3. no compact germ truncation or finite jet repairs properness;
4. there exists an orthonormal sequence `g_n` with

   \[
   \boxed{
   \|A_wg_n\|^2+\|Rg_n\|^2\longrightarrow0.}
   \tag{FCP.13}
   \]

#### Proof

The direct sum of two compact operators is compact. Apply it to any orthonormal sequence: both
components converge to zero in norm. A compact operator on an infinite-dimensional Hilbert space
cannot be bounded below, proving all assertions. QED.

### Theorem 4.2 -- exact survivor condition

Suppose an enlarged response satisfies

\[
 \|A_wf\|^2+\|Rf\|^2\ge\alpha\|f\|^2
 \qquad(f\in H)
 \tag{FCP.14}
\]

for some `alpha>0`. Then for every unit adaptive prime-null sequence `f_n` with
`||A_wf_n||->0`,

\[
 \boxed{\liminf_n\|Rf_n\|\ge\sqrt\alpha.}
 \tag{FCP.15}
\]

Consequently `R` is noncompact and does not factor as `S A_w` through any bounded `S`.

#### Proof

Equation `(FCP.15)` follows by taking `liminf` in `(FCP.14)`. If `R` were compact, Theorem 4.1
would contradict `(FCP.14)`. If `R=SA_w`, then `||Rf_n||<=||S||||A_wf_n||->0`, contradicting
`(FCP.15)`. QED.

This is precisely the escape-interception law of formation-Laplacian properness, now instantiated
on a globally faithful arithmetic sampling system.

## 5. Functional-equation and recovery neutrality

Let `U:H->H` be unitary and let `V` be an isometry on the receiver. Then

\[
 \widetilde A=VA_wU
 \tag{FCP.16}
\]

is compact, injective, and nonclosed-range exactly when `A_w` is. Its singular values and lower
frame bound are unchanged. The same holds after the common-recovery isometric lift proved in the
packet-formation theorem.

Therefore functional-equation action and common recovery are information-neutral at the global
formation/properness level. They transport the obstruction; they do not cure it.

## 6. Admission--properness trilemma

For prime sampling on an infinite-dimensional analytic carrier, three properties are distinct:

1. **formation faithfulness:** `ker A={0}`;
2. **admission:** `A` is bounded into the chosen receiver;
3. **properness:** `A` is bounded below modulo its kernel.

The theorem realizes

\[
 \boxed{
 \text{faithful}+\text{admitted}+\text{nonproper}.}
 \tag{FCP.17}
\]

Summable weights buy admission by making the operator Hilbert--Schmidt, but that very compactness
destroys properness. Increasing weights may avoid compactness but can destroy admission. A valid
source law must land between these two failures.

This is the higher mechanism: selection is not produced by more exact finite relations. It is a
noncompact global response theorem.

## 7. Fourth-organ prediction

Any archimedean completion capable of turning faithful prime formation into a selector must supply
an operator `R` satisfying all of:

1. infinite-dimensional range;
2. noncompactness;
3. nonfactorization through prime sampling;
4. interception `(FCP.15)` of every adaptive prime-null sequence;
5. functional-equation covariance;
6. source-generated normalization before Xi specialization.

Therefore one Gamma scalar, one derivative port, one determinant line, or any finite jet is
provably insufficient. The smallest plausible receiver is an admitted infinite archimedean germ or
jet field coupled to the prime sector.

This prediction was not used in constructing `A_w`; it is forced by the global properness theorem.

## 8. Hostile audit and scope

1. **Classical machinery.** RKHS representers, Hilbert--Schmidt operators, compactness, the bounded
   inverse theorem, and Paley--Wiener spaces are classical.
2. **Corpus delta.** The formal prime-log uniqueness theorem is fused with formation properness to
   prove an exact faithful-but-nonproper arithmetic receiver and an infinite-rank necessity theorem
   for every unlocking boundary organ.
3. **Summability is load-bearing.** The theorem does not say every weighting is compact. It
   classifies the entire summable-weight chamber.
4. **Uniform evaluation is load-bearing.** It holds in Paley--Wiener and many translation-invariant
   RKHS carriers. Other carriers require the exact condition `sum_p w_p||k_p||^2<infinity`.
5. **Noncompactness is necessary, not sufficient.** A noncompact `R` may still miss an adaptive
   null sequence.
6. **No completed-flux realization yet.** The corpus's full prime--archimedean completed-flux germ
   is a candidate infinite response, but `(FCP.14)` has not been proved for it.
7. **No RH claim.** No zero location or physical Xi displacement enters the proof.

## 9. External parent audit

The abstract result belongs to classical sampling/frame/operator theory. Current interpolation work
also separates uniqueness from uniformly bounded reconstruction; see Ehring--Vogel--Haasdonk,
[Escaping the native space of Sobolev kernels by interpolation](https://arxiv.org/abs/2512.07262).
Prime-log sampling in de Branges/model spaces is already audited in
`critical-prime-sampling-microlocalization-law.md`. No external priority claim is made for the
operator-theoretic ingredients.

## 10. Next gate

Construct an infinite-rank pre-zero boundary response from the fixed archimedean completed-flux
germ and test `(FCP.14)`. The attempt must fail or prove all of:

1. bounded admission on the same source carrier as `A_w`;
2. noncompactness;
3. interception of every prime adaptive null sequence;
4. functional-equation covariance;
5. nonneutral physical landing only after the first four are closed.

## Log

- 2026-08-12 -- formal prime-log uniqueness fused with weighted RKHS formation. Summable prime
  formation proved injective Hilbert--Schmidt with nonclosed range. All compact/finite boundary
  repairs killed; infinite-rank noncompact interception extracted as exact survivor.
