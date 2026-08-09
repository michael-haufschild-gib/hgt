# Multilinear process tomography, blind sector, and positive-robustness law

- **ID:** ULF-MPTB-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** intervention-completeness attack on constitutive kernel geometry
- **Statement:** A finite law process is reconstructed exactly by a spanning family of joint interventions; every nonspanning family has a canonical annihilator blind sector, and interior positivity cannot remove that nonidentifiability.
- **Status:** [PAPER-PROVED] [ROUTE-INDEPENDENT PROCESS THEOREM] [CLASSICAL MULTILINEAR/PROCESS-TOMOGRAPHY PARENTS] [NOT RH] [NO LEAN]

## 1. Coordinate-free process

Let (E_1,\ldots,E_k) be nonzero finite-dimensional vector spaces over
\(\mathbb F\in\{\mathbb R,\mathbb C\}\). A (k)-slot constitutive process is a multilinear
functional

\[
W:E_1\times\cdots\times E_k\longrightarrow\mathbb F,
\]

equivalently

\[
W\in\left(E_1\otimes\cdots\otimes E_k\right)^*.
\tag{1}
\]

An experiment chooses a joint intervention tensor

\[
u=e_1\otimes\cdots\otimes e_k
\]

and reads (W(u)). Let \(\mathcal U\) be any family of allowed joint interventions and put

\[
U=\operatorname{span}\mathcal U
\subseteq E_1\otimes\cdots\otimes E_k.
\tag{2}
\]

## 2. Exact tomography theorem

### Theorem 2.1

1. The complete experiment record is the restriction

   \[
   \operatorname{res}_U(W)=W|_U.
   \]

2. Its exact blind sector is

   \[
   \boxed{
   \ker(\operatorname{res}_U)=U^\perp
   =\{\Delta:\Delta(u)=0\text{ for every }u\in U\}.}
   \tag{3}
   \]

3. The experiment family reconstructs every process exactly if and only if

   \[
   \boxed{U=E_1\otimes\cdots\otimes E_k.}
   \tag{4}
   \]

4. If (U\) is proper, then every process (W\) lies in a nontrivial affine family

   \[
   W+U^\perp
   \tag{5}
   \]

   of experimentally indistinguishable constitutive laws.

### Proof

Items 1 and 2 are the definition and kernel of linear restriction. In finite dimension, restriction
is injective exactly when its annihilator is zero, which is equivalent to (U) being the whole
tensor product. If (U) is proper, its annihilator contains a nonzero functional \(\Delta\), and
(W\) and (W+c\Delta\) agree on all allowed interventions for every scalar (c). QED.

### Product-instrument corollary

If allowed interventions contain all products from subsets (S_i\subseteq E_i), put
(V_i=\operatorname{span}S_i). Then

\[
U=V_1\otimes\cdots\otimes V_k,
\tag{6}
\]

so product tomography is complete exactly when every slot family spans (E_i). If
(d_i=\dim E_i) and (r_i=\dim V_i), then

\[
\boxed{
\dim U^\perp=\prod_i d_i-\prod_i r_i.}
\tag{7}
\]

This is the exact hidden constitutive dimension, not an analogy to missing coordinates.

## 3. Interior positivity does not repair incomplete experiments

Let \(\mathcal A\) be an affine subspace of Hermitian operators on a finite-dimensional Hilbert
space, representing normalization or causal constraints, and let

\[
\mathcal P=\{W\in\mathcal A:W\succeq0\}.
\]

Suppose (W_0\in\mathcal P) is positive definite and

\[
0\ne\Delta\in(\mathcal A-\mathcal A)\cap U^\perp
\]

is Hermitian. Then, for every

\[
0<\varepsilon<\frac{\lambda_{\min}(W_0)}{\|\Delta\|_{op}},
\]

both

\[
\boxed{W_\pm=W_0\pm\varepsilon\Delta}
\tag{8}
\]

belong to \(\mathcal P\), are distinct, and give identical values on all allowed interventions.

Indeed,

\[
W_\pm\succeq
\bigl(\lambda_{\min}(W_0)-\varepsilon\|\Delta\|_{op}\bigr)1\succ0,
\]

while affine constraints are preserved because \(\Delta\) is tangent to \(\mathcal A\), and
experimental equality follows from \(\Delta\in U^\perp\).

Thus positivity can shrink the law space but cannot generically fill a tomographic blind direction.

## 4. Passive kernels are not processes

`observationally-identical-law-systems-and-intervention-separation-law.md` supplies the sharp
two-bit example: opposite structural directions have the identical full passive joint probability
kernel, but one elementary intervention separates them. A static positive kernel is therefore only
a zero-slot or passive shadow of a constitutive process.

Theorem 2.1 gives the exact replacement. A process is a functional of interventions. Different proof
routes can be called local gauges only when they are proven to be different spanning instrument
families on the same (W). If their combined intervention span is proper, the no-go is the literal
annihilator (U^\perp); if it spans, process tomography reconstructs (W).

## 5. Quantum/process-tensor specialization

For finite quantum processes, each (E_i) may be the real vector space of Hermitian Choi operators
for an intervention slot, and (W\succeq0) the Choi operator of a process tensor/quantum comb subject
to causal trace constraints. The generalized Born rule is precisely the pairing (W(u)).
Tomographically complete instruments span the slot spaces; incomplete instruments leave the blind
sector (3), with positive robustness supplied by (8).

This specialization is established process-tensor theory. The theorem is stated abstractly so it
also applies to classical causal mechanisms, proof transformations, multilinear response systems,
and nonprobabilistic field-valued experiments.

## 6. Hostile scope

- Multilinear duality and tomography are classical.
- Quantum combs, process tensors, causal boxes, and generalized Born rules are occupied.
- A process tensor can be chosen to fit arbitrary finite experiment data.
- The theorem says when routes can be gauges of one process; it does not construct their common
  process.
- Positivity, composition, and causal constraints must be sourced, not declared after observation.
- Infinite process rank is not differential hypertranscendence.
- No physical cost, gravity law, or RH claim follows.

Primary process-tomography parent: G. A. L. White et al.,
*Non-Markovian Quantum Process Tomography*, https://arxiv.org/abs/2106.11722.

## Log

- 2026-08-09 — abstract process-tomography and positive blind-sector theorem proved.
