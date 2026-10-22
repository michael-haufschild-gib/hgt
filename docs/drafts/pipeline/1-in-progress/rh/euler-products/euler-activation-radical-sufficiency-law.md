# Euler activation radical-sufficiency law

- **ID:** `euler-activation-radical-sufficiency-law`
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL INFORMATION LAW / RIEMANN-SOURCE PHASE CLASSIFICATION
- **Scientific status:** `[NEW CANDIDATE] [PAPER PROOF IN PROGRESS] [LEAN PENDING] [NOT RH]`
- **Novelty boundary:** Kakutani's product-measure theorem, Hellinger tensorization, geometric
  prime valuations, and squarefree Euler products are classical. Candidate-new content is their
  exact combination for the zero-modified Euler activation law: the squarefree radical alone
  determines its all-prime Hellinger/Kakutani phase, while the conditional valuation fibre changes
  finite information but cannot create another product-measure sector.

## Question

Diagonal Euler activation has local law
\[
 \nu_q(0)=\frac1{1+q},\qquad
 \nu_q(k)=\frac{(1-q)q^k}{1+q}\quad(k\geq1),\qquad 0<q<1.
\]
Its radical is the occupancy bit \(B_q=\mathbf 1_{\{k>0\}}\), with
\[
 \Pr(B_q=1)=\frac q{1+q}.
\]
Does the positive-valuation geometric mark carry an independent infinite-prime reflection phase,
or is the global measure class already fixed by the radical?

## Local theorem

Put \(q=x^2,\ r=y^2\), \(0<x,y<1\), and define the three Bhattacharyya affinities
\[
\begin{aligned}
 A_{\rm rad}(x,y)
   &=\frac{1+xy}{\sqrt{(1+x^2)(1+y^2)}},\\
 A_{\rm fib}(x,y)
   &=\frac{\sqrt{(1-x^2)(1-y^2)}}{1-xy},\\
 A_{\rm act}(x,y)
   &=\sum_{k\ge0}\sqrt{\nu_{x^2}(k)\nu_{y^2}(k)}.
\end{aligned}
\]
Direct summation gives
\[
 A_{\rm act}
 =\frac{1+xyA_{\rm fib}}{\sqrt{(1+x^2)(1+y^2)}}.
\]
Consequently the Hellinger deficit has the exact stratified decomposition
\[
\boxed{
 1-A_{\rm act}
  =(1-A_{\rm rad})
   +\frac{xy}{\sqrt{(1+x^2)(1+y^2)}}(1-A_{\rm fib}).
}\tag{RS1}
\]
Thus radical coarse-graining can only remove Hellinger discrepancy; the amount removed is exactly
occupancy overlap times conditional-fibre discrepancy.

Two difference-of-squares identities give
\[
\begin{aligned}
 1-A_{\rm rad}
 &=\frac{(x-y)^2}
 {\sqrt{(1+x^2)(1+y^2)}
  \bigl(\sqrt{(1+x^2)(1+y^2)}+1+xy\bigr)},\\
 1-A_{\rm fib}
 &=\frac{(x-y)^2}
 {(1-xy)\bigl(1-xy+\sqrt{(1-x^2)(1-y^2)}\bigr)}.
\end{aligned}\tag{RS2}
\]
If \(x^2,y^2\leq1/2\), their ratio satisfies
\[
 0\leq
 \frac{xy}{\sqrt{(1+x^2)(1+y^2)}}(1-A_{\rm fib})
 \leq 6(1-A_{\rm rad}).
\tag{RS3}
\]
Hence
\[
\boxed{
 1-A_{\rm rad}\leq1-A_{\rm act}\leq7(1-A_{\rm rad}).
}\tag{RS4}
\]
The constant is deliberately non-sharp; summability equivalence is the invariant.

## All-prime radical-sufficiency theorem

Let \(x_i,y_i\in(0,1)\) be two countable parameter families with
\(x_i,y_i\to0\). Then finite prefixes do not affect summability and `(RS4)` yields
\[
\boxed{
 \sum_i(1-A_{\rm act}(x_i,y_i))<\infty
 \quad\Longleftrightarrow\quad
 \sum_i(1-A_{\rm rad}(x_i,y_i))<\infty.
}\tag{RS5}
\]
By the classical Kakutani dichotomy, the corresponding infinite products of full activation laws
are equivalent exactly when the products of their squarefree radical pushforwards are equivalent.
The positive-valuation geometric fibres never refine the global product-measure phase.

The paper may use the measure-class interpretation only after either formalizing the required
Kakutani theorem or stating `(RS5)` as the proved result and citing Kakutani solely as classical
interpretation.

## Riemann reflection specialization

For the radial source family
\[
 x_p=p^{-1/2},\qquad y_{p,c}=p^{-(1/2-c)},\qquad |c|<1/2,
\]
the squared root-amplitude difference is the already established prime-valuation Hellinger
numerator
\[
 (x_p-y_{p,c})^2.
\]
The radical deficit is comparable to this numerator:
\[
 \frac18(x_p-y_{p,c})^2
 \leq 1-A_{\rm rad}(x_p,y_{p,c})
 \leq (x_p-y_{p,c})^2.
\tag{RS6}
\]
Therefore
\[
\boxed{
 \sum_p(1-A_{\rm act}(x_p,y_{p,c}))<\infty
 \Longleftrightarrow
 \sum_p(1-A_{\rm rad}(x_p,y_{p,c}))<\infty
 \Longleftrightarrow c=0.
}\tag{RS7}
\]
The critical line is the unique unfractured activation sector, and the squarefree radical already
detects it.

## What this explains

1. **Activation/Gamma split.** Gamma whitening resolves the conditional depth mark, but `(RS5)`
   proves that this mark contributes no new all-prime reflection sector.
2. **Breadth/depth grid.** Radical breadth and valuation depth are algebraically independent
   filtrations, but only breadth controls the Hellinger/Kakutani phase. Depth remains essential for
   logarithmic-current reconstruction and hypertranscendental noncompression.
3. **Critical radicalization.** At \(q_p=1/p\), radical occupancy is nonsummable while every fixed
   depth-\(\ge2\) tail is summable. The singular all-prime part is therefore squarefree; higher
   powers are a tail-finite correction.
4. **Reflection fracture.** Existing geometric Hellinger and finite-Rees no-sewing theorems become
   shadows of a sharper statement: the fracture survives the radical quotient and hence precedes
   every Gamma, Rees, Sonin, Calkin, or Ward consumer.
5. **Route boundary.** Any proposed orientation producer living only in the conditional
   valuation/Gamma fibre cannot repair reflected sector mismatch. A successful source theorem must
   act on the radical tail algebra or couple radical breadth to the divisor before scalarization.

## Significance and honesty gate

This law does **not** prove zero exclusion. Its scientific value is a source-localization theorem:
it removes the entire conditional valuation tower from the search for the missing global
reflection selector, despite that tower's genuine differential and current-reconstruction
content. It is paper-worthy only if:

1. exact local decomposition and all-prime summability equivalence are unconditional;
2. literature audit finds no prior activation-radical sufficiency theorem;
3. the final manuscript derives existing corpus no-gos as named consequences rather than appending
   them as parallel “main theorems”;
4. paper states the remaining zero-exclusion problem precisely: source-derived conservative action
   on the squarefree radical tail.

## Formal targets

Proposed module:
`formal/GaloisForLFunctions/RHTower/EulerActivationRadicalHellingerSufficiency.lean`.

Minimum declarations:

- exact activation, radical, and conditional-fibre affinities;
- `(RS1)` and `(RS2)`;
- nonnegativity and comparison `(RS4)`;
- abstract summability equivalence `(RS5)` under eventual half-aperture;
- radial-prime comparison `(RS6)` and critical uniqueness `(RS7)`;
- critical almost-sure radicalization only if the additional Borel--Cantelli proof adds genuine
  explanatory value after the main law is closed.

## Literature audit so far

- Classical zeta distributions use independent geometric prime valuations; this is not new.
- Nielsen computes information divergences between ordinary zeta distributions; this does not
  appear to treat the zero-modified activation law or radical sufficiency.
- Arratia and related probabilistic-number-theory work studies independent geometric prime
  multiplicities and couplings; this is prior art for the probabilistic source, not `(RS1)`--`(RS7)`.
- No exact hit has been found for the local activation affinity, its radical/fibre decomposition,
  or the all-prime reflected radical-sufficiency conclusion. Specialist priority audit remains
  open.
