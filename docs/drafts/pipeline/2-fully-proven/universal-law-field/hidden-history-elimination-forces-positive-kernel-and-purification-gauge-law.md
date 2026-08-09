# Hidden-history elimination forces positive kernel and purification-gauge law

- **ID:** ULF-HKPG-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** composition/observer-closure attack on polar history geometry
- **Statement:** Eliminating a hidden factor from a pure history amplitude canonically produces a positive semidefinite kernel whose rank is Schmidt rank; pure amplitudes are closed under elimination exactly in the separable case, and minimal hidden realizations are unique only up to unitary gauge.
- **Status:** [PAPER-PROVED] [FORCED CLOSURE THEOREM] [CLASSICAL GRAM/SCHMIDT/PURIFICATION PARENTS] [NOT RH] [NO LEAN]

## 1. Hidden-history elimination

Let (A) and (B) be finite nonempty sets and let

\[
\psi=\sum_{a\in A,\,b\in B}\psi_{ab}\,e_a\otimes e_b
\in\mathbb C^A\otimes\mathbb C^B
\]

be normalized. Define the visible kernel by eliminating the (A)-history:

\[
K_B=\operatorname{Tr}_A|\psi\rangle\langle\psi|,
\qquad
(K_B)_{bb'}=\sum_{a\in A}\psi_{ab}\overline{\psi_{ab'}}.
\tag{1}
\]

### Theorem 1.1

1. (K_B\) is positive semidefinite and \(\operatorname{Tr}K_B=1\).
2. If \(\Psi=(\psi_{ab})\) is the (A\times B) amplitude matrix, then

   \[
   \operatorname{rank}K_B=\operatorname{rank}\Psi.
   \tag{2}
   \]

3. (K_B) has rank one exactly when \(\psi\) is separable:

   \[
   \psi=\alpha\otimes\beta.
   \tag{3}
   \]

4. For every visible observable (X\in B(\mathbb C^B)\),

   \[
   \langle\psi,(1\otimes X)\psi\rangle
   =\operatorname{Tr}(K_BX).
   \tag{4}
   \]

### Proof

For (v\in\mathbb C^B),

\[
\langle v,K_Bv\rangle
=\sum_{a\in A}\left|\sum_{b\in B}\overline{v_b}\psi_{ab}\right|^2\ge0,
\]

and the trace is \(\sum_{a,b}|\psi_{ab}|^2=1\). Up to the harmless transpose convention in (1),
(K_B) is the Gram matrix of the columns of \(\Psi\), so its rank is the rank of \(\Psi\).
Rank one of the coefficient matrix is equivalent to factorization \(\psi_{ab}=\alpha_a\beta_b\),
which proves (3). Expanding both sides gives (4). QED.

## 2. Sharp Bell obstruction

For (d\ge2), take

\[
\Phi_d=\frac1{\sqrt d}\sum_{j=1}^d e_j\otimes e_j.
\]

Then

\[
\boxed{\operatorname{Tr}_A|\Phi_d\rangle\langle\Phi_d|=\frac1d I_d.}
\tag{5}
\]

The right side has rank (d), so it cannot equal \(|\beta\rangle\langle\beta|\) for any visible
amplitude \(\beta\). Therefore any history theory containing entangled amplitudes and closed under
discarding hidden histories must enlarge rank-one projective amplitudes to positive semidefinite
kernels.

This is a closure theorem, not a physical analogy.

## 3. Positive diagonal still does not determine coherence

The diagonal

\[
p_b=(K_B)_{bb}
\]

is the visible probability law. It does not determine the kernel. For example,

\[
\beta_\theta=\frac1{\sqrt2}(e_0+e^{i\theta}e_1)
\]

has the same diagonal ((1/2,1/2)) for every \(\theta\), while

\[
|\beta_\theta\rangle\langle\beta_\theta|
=\frac12
\begin{pmatrix}
1&e^{-i\theta}\\
e^{i\theta}&1
\end{pmatrix}
\tag{6}
\]

retains the relative phase off diagonal. Thus a positive kernel contains both classical positive
weights and coherent phase relations; diagonalization is a further observer quotient.

## 4. Purification gauge

Every positive semidefinite kernel (K\) of rank (r\) admits a factorization

\[
K=VV^*
\tag{7}
\]

with (V:\mathbb C^r\to\mathbb C^B\), hence a purification in
(\mathbb C^r\otimes\mathbb C^B\). If (V\) and (W\) are two minimal factorizations of the same
kernel, then

\[
W=VU
\tag{8}
\]

for a unitary (U\in U(r)\). This follows by identifying both coefficient spaces isometrically with
the range of (K^{1/2}).

Therefore the visible kernel determines the smallest hidden dimension but not a marked hidden
history. Hidden realizations form a unitary gauge orbit. Reconstruction of an actual source history
requires extra marking beyond positivity and all visible expectations (4).

## 5. Exact field consequence

The smallest finite observer-closed replacement for polar amplitudes is a positive kernel or density
operator. It simultaneously carries:

- exact relations through its nullspace;
- positive probabilities through its diagonal;
- coherent phase through off-diagonal entries;
- hidden-history capacity through rank;
- a canonical Hilbert/GNS realization through Gram factorization;
- unavoidable gauge ambiguity through (8).

This closes the representation-selection defect of a bare bialgebra only conditionally: the kernel
selects its GNS representation, but the source must still produce the kernel. Choosing one after
inspecting observer outputs is theatre.

## 6. Hostile scope and parent collision

- Gram factorization, Schmidt decomposition, partial trace, and purification are classical.
- Strongly positive decoherence functionals and density operators already provide this closure.
- Boes--Navascués prove that strong positivity is maximal under a natural composability demand for
  decoherence functionals; this strongly occupies the abstract closure mechanism.
- Positive kernels alone do not supply a preferred history composition, reversal, intervention, or
  physical cost.
- Kernel rank does not imply differential hypertranscendence.
- No universal field or RH theorem follows.

Primary parent: P. Boes and M. Navascués, *Composing decoherence functionals*,
https://arxiv.org/abs/1609.09723.

## Log

- 2026-08-09 — rank-one amplitude ontology forced to positive-kernel closure.
