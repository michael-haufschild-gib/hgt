# Passive fibre size, hidden dimension, and minimal experiment law

- **ID:** ULF-EXPDIM-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** interventional repair of passive parallax
- **Statement:** Passive fibre size and linear hidden dimension give exact lower bounds on the number and capacity of experiments required for reconstruction.
- **Status:** [PAPER-PROVED] [ROUTE-INDEPENDENT] [INFORMATION/RANK BRIDGE] [NO LEAN]

## 1. Finite information theorem

Let \(X\) be a finite set, let \(q_0:X\to Y_0\) be a passive observer, and let
\(q_i:X\to Y_i\), \(1\le i\le r\), be experiments. Suppose the joint response

\[
Q=(q_0,q_1,\ldots,q_r):X\longrightarrow\prod_{i=0}^rY_i
\tag{1}
\]

is injective. Then for every passive fibre \(F_y=q_0^{-1}(y)\),

\[
|F_y|\le\prod_{i=1}^r|Y_i|.
\tag{2}
\]

Consequently, if \(|Y_i|\le k\) for every experiment, then

\[
r\ge
\left\lceil\log_k\left(\max_y|F_y|\right)\right\rceil.
\tag{3}
\]

### Proof

On a fixed passive fibre \(F_y\), the first component of (1) is constant. Injectivity of \(Q\)
therefore implies injectivity of

\[
(q_1,\ldots,q_r)|_{F_y}:F_y\longrightarrow\prod_{i=1}^rY_i.
\]

Counting gives (2), and (3) follows when every factor has size at most \(k\). QED.

## 2. Linear hidden-dimension theorem

Let \(V,W\) be vector spaces over a field \(k\), let \(q_0:V\to W\) be linear, and let
\(\ell_1,\ldots,\ell_r\in V^*\) be scalar response experiments. The joint linear observer

\[
Q=(q_0,\ell_1,\ldots,\ell_r):V\longrightarrow W\oplus k^r
\tag{4}
\]

is injective if and only if

\[
\ker q_0\cap\bigcap_{i=1}^r\ker\ell_i=0.
\tag{5}
\]

If \(d=\dim\ker q_0<\infty\), injectivity forces \(r\ge d\), and \(d\) experiments suffice. If
\(\ker q_0\) is infinite-dimensional, no finite scalar experiment family makes \(Q\) injective.

### Proof

The kernel of (4) is exactly the left side of (5). Restricting the \(r\) functionals to
\(K=\ker q_0\) gives a map \(K\to k^r\). If it is injective and \(K\) has finite dimension \(d\),
rank--nullity gives \(d\le r\). Conversely, choose a basis of \(K^*\), extend its \(d\) coordinate
functionals from \(K\) to \(V\), and (5) holds. If \(K\) is infinite-dimensional, every map
\(K\to k^r\) has nonzero kernel. QED.

## 3. Experimental dimension

Define the scalar experimental dimension of a linear passive observer by

\[
\operatorname{edim}(q_0)=
\min\{r:\text{some }r\text{ scalar experiments make (4) injective}\}.
\]

Then

\[
\boxed{\operatorname{edim}(q_0)=\dim\ker q_0}
\tag{6}
\]

with both sides allowed to be infinite.

## 4. Cross-organ consequence

Fibre loss and intervention complexity are not independent slots. The passive observer forces a
minimum experiment budget. In positive conditional-observer models, relative jet freedom creates an
infinite-dimensional hidden covariance space; theorem (6) then proves that no finite family of scalar
responses reconstructs every hidden direction.

This gives a precise noncompactness reading of hypertranscendental/jet-free behavior only when a
source theorem supplies the passive observer and identifies its hidden jet space. Hypertranscendence
alone is not redefined as experimental dimension.

## 5. Hostile scope

- The results are elementary information counting and rank--nullity.
- Nonlinear or vector-valued experiments can have different minimal counts.
- Injectivity is exact reconstruction, not stable, continuous, or efficient reconstruction.
- Taking all possible experiments makes reconstruction tautological; a field must specify a legal
  experiment class before measuring dimension.

## Log

- 2026-08-09 — exact fibre/experiment coupling proved after passive-parallax failure.
