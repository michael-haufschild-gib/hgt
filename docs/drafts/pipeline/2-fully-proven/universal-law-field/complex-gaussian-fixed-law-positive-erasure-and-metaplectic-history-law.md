# Complex Gaussian fixed law, positive erasure, and metaplectic history law

- **ID:** ULF-ACTION-1
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** Candidate L finite action-principle test
- **Statement:** One rotating quadratic action has fixed critical law and fixed positive Hessian while its oriented thimble and Gaussian determinant require a double cover.
- **Status:** [PAPER-PROVED] [BRIDGE] [CLASSICAL PICARD--LEFSCHETZ/METAPLECTIC MECHANISM] [NOT FIELD CORE] [NO LEAN]

## 1. Setup

For \(\theta\in\mathbb R\), define

\[
\mathcal S_\theta(z)=\frac12e^{i\theta}z^2,
\qquad z\in\mathbb C.
\tag{1}
\]

Let the oriented steepest-descent line \(L_\theta\) be parametrized by

\[
\iota_\theta:\mathbb R\longrightarrow\mathbb C,
\qquad
\iota_\theta(y)=e^{-i\theta/2}y,
\tag{2}
\]

with the orientation transported from increasing \(y\).

## 2. Theorem

For every \(\theta\):

1. \(\operatorname{Crit}(\mathcal S_\theta)=\{0\}\);
2. the complex Hessian is \(H_\theta=e^{i\theta}\), while its positive Gram shadow is
   \(H_\theta^*H_\theta=1\);
3. \(\mathcal S_\theta(\iota_\theta(y))=y^2/2\), so \(L_\theta\) is a convergent
   steepest-descent cycle;
4. the oriented Gaussian amplitude is

   \[
   Z(\theta)=\int_{L_\theta}e^{-\mathcal S_\theta(z)}\,dz
   =\sqrt{2\pi}\,e^{-i\theta/2};
   \tag{3}
   \]

5. the action, critical locus, positive Hessian, and unoriented line are \(2\pi\)-periodic, but

   \[
   Z(\theta+2\pi)=-Z(\theta),
   \qquad
   \iota_{\theta+2\pi}=-\iota_\theta;
   \tag{4}
   \]

6. the oriented determinant/thimble history closes only after \(4\pi\).

### Proof

Differentiating (1) gives \(d\mathcal S_\theta=e^{i\theta}z\,dz\), so the unique critical point is
zero and the Hessian is \(e^{i\theta}\). Its Hermitian square is one. Substituting (2) into (1)
gives

\[
\mathcal S_\theta(e^{-i\theta/2}y)
=\frac12e^{i\theta}e^{-i\theta}y^2
=\frac12y^2.
\]

Moreover \(dz=e^{-i\theta/2}dy\), hence

\[
Z(\theta)=e^{-i\theta/2}\int_{\mathbb R}e^{-y^2/2}\,dy
=\sqrt{2\pi}\,e^{-i\theta/2}.
\]

Replacing \(\theta\) by \(\theta+2\pi\) fixes \(e^{i\theta}\) but multiplies
\(e^{-i\theta/2}\) by \(-1\). Therefore the underlying line is fixed while its chosen orientation
and amplitude reverse. Repeating the loop twice restores both. QED.

## 3. Exact consequence

Neither the critical locus nor the positive Hessian shadow determines the oriented proof cycle or
Gaussian amplitude. The missing datum is not curvature: it is the square-root/determinant lift of a
loop in the space of nondegenerate quadratic laws.

Thus a complex action can genuinely produce several requested shadows from one formula. However,
this finite success is standard Picard--Lefschetz and metaplectic behavior. It validates an action
chart but does not establish a new universal field.

## 4. Hostile boundary

- The theorem does not produce hypertranscendence, arithmetic selection, completion, or a proof
  language.
- Replacing “proof” by “thimble” adds no mathematics unless a source canonically supplies the action.
- Derived critical loci and their shifted symplectic structures are established mathematics; the
  positive/phase split above is a classical Gaussian instance.
- Candidate L remains a possible local realization and is rejected as current universal ontology.

## 5. External parents

- Joyce, `A classical model for derived critical loci`, arXiv:1304.4508.
- Brav--Bussi--Joyce, `A Darboux theorem for derived schemes with shifted symplectic structure`,
  arXiv:1305.6302.
- Anel--Calaque, `Shifted symplectic reduction of derived critical loci`, arXiv:2106.06625.

## Log

- 2026-08-09 — finite action-principle gate closed; classified as bridge, not field core.
