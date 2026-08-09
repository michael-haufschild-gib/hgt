# Identity-sector radial-gauge blindness and cross-grade selection law

- **ID:** `identity-sector-radial-gauge-blindness-and-cross-grade-selection-law`
- **Stage:** 3-formalized
- **Type:** THEOREM / NO-GO / POSITIVE SURVIVOR (paper)
- **Status:** `[PAPER PROOF COMPLETE] [UNCONDITIONAL] [BRIDGE]`
  `[SOURCE-AXIOM IMPOSSIBILITY] [NO RH CLAIM] [LEAN COMPLETE] [UNCONDITIONAL] [NO SORRY] [NO NEW AXIOMS]`
- **Novelty:** group-graded gauge action and cyclic-sector decomposition are standard. New leverage is
  exact specialization to literal rational-adelic prime/inverse-prime source together with
  source-specific classification of first possible selector.

## Goal

Determine whether current literal arithmetic source operations can distinguish zero radial drift
from nonzero drift before divisor specialization.

## Setup

Let `G` be abelian group and let

\[
 A=\bigoplus_{g\in G}A_g,
 \qquad A_gA_h\subseteq A_{gh},
 \tag{1}
\]

be unital `G`-graded algebra over `C`. For character

\[
 \chi:G\longrightarrow\mathbb C^\times
 \tag{2}
\]

define

\[
 \Gamma_\chi(a_g)=\chi(g)a_g.
 \tag{3}
\]

Give cyclic bar chain `a_0 tensor ... tensor a_n` total grade

\[
 |a_0\otimes\cdots\otimes a_n|_G=g_0g_1\cdots g_n
 \tag{4}
\]

when `a_i in A_{g_i}`.

## Theorem 1: total-grade gauge law

1. `Gamma_chi` is algebra automorphism with inverse `Gamma_(chi^-1)`.
2. On homogeneous cyclic chain of total grade `g`,

   \[
   \Gamma_\chi^{\otimes(n+1)}=\chi(g)\,\mathrm{id}.
   \tag{5}
   \]

3. Every Hochschild face and degeneracy preserves total grade. Because `G` is abelian, cyclic
   rotation preserves it as well.
4. Consequently, total-grade-one cyclic subcomplex is pointwise fixed by every `Gamma_chi`.

### Proof

For homogeneous `a_g,b_h`,

\[
 \Gamma_\chi(a_gb_h)
 =\chi(gh)a_gb_h
 =\chi(g)\chi(h)a_gb_h
 =\Gamma_\chi(a_g)\Gamma_\chi(b_h).
\]

This proves algebra law and inverse. Tensor action multiplies chain by
`product_i chi(g_i)=chi(product_i g_i)`, proving `(5)`. Each Hochschild face replaces adjacent
grades `g_i,g_(i+1)` by product and therefore preserves `(4)`; last face preserves total product
because `G` is abelian. Degeneracy inserts unit of grade one. Rotation merely permutes commuting
grades. For total grade one, multiplier in `(5)` is `chi(1)=1`. QED.

## Corollary 2: literal rational-adelic source is radially blind

Take actual algebraic crossed product

\[
 A_0=\mathcal S(\mathbb A_{\mathbb Q})
      \rtimes_{\alpha,\mathrm{alg}}\mathbb Q^\times,
 \qquad A=\mathbb C\oplus A_0,
 \tag{6}
\]

graded by rational scaling label. For `c in R`, character

\[
 \chi_c(q)=|q|^c
 \tag{7}
\]

defines faithful one-parameter automorphism family

\[
 \Gamma_c(a_q)=|q|^c a_q.
 \tag{8}
\]

Both endpoint traces are invariant because they read only identity-scaling coefficient. For
literal prime/inverse-prime atom

\[
 u_p=(gU_p)\otimes(gU_{p^{-1}}),
 \qquad \varepsilon_0^{(1)}(u_p)=1,
 \tag{9}
\]

one has

\[
 \Gamma_c^{\otimes2}u_p=p^cp^{-c}u_p=u_p
 \tag{10}
\]

for every real `c`. Therefore no relation generated solely by ordinary Hochschild/cyclic faces,
degeneracies, rotations, endpoint traces, or arbitrary higher degree inside total-grade-one
source sector can select `c=0`.

### Proof

Equations `(6)`--`(10)` instantiate Theorem 1. Every named operation preserves relevant sector
and commutes with `Gamma_c`; any equation built functorially from them is carried to itself by the
whole radial family. QED.

This is a source-axiom impossibility, not claim that all conceivable source laws are blind.

## Theorem 3: Kummer detector is still radially equivariant

Define logarithmic grading derivation and cyclic one-cocycle

\[
 \partial_{\log}(a_q)=\log|q|\,a_q,
 \qquad
 \phi_{\log}(a_0,a_1)
 =\varepsilon_0(a_0\partial_{\log}a_1).
 \tag{11}
\]

Then

\[
 \partial_{\log}\Gamma_c=\Gamma_c\partial_{\log},
 \qquad
 \phi_{\log}(\Gamma_ca_0,\Gamma_ca_1)
 =\phi_{\log}(a_0,a_1).
 \tag{12}
\]

In particular, existing coefficient-faithful genuine multiplier cycle has nonzero Kummer period
`-log p`, yet complete radial orbit remains invisible to it.

### Proof

Both operators act diagonally on each grade, so first equality is immediate. Because `Gamma_c` is
algebra automorphism and `epsilon_0 Gamma_c=epsilon_0`,

\[
 \begin{aligned}
 \phi_{\log}(\Gamma_ca_0,\Gamma_ca_1)
 &=\varepsilon_0(\Gamma_ca_0\,
     \partial_{\log}\Gamma_ca_1)\\
 &=\varepsilon_0\Gamma_c(a_0\partial_{\log}a_1)\\
 &=\phi_{\log}(a_0,a_1).
 \end{aligned}
\]

QED.

Thus asymmetric one-leg valuation detection already exists. Missing datum is not another cyclic
cocycle; it must fail diagonal radial equivariance.

## Theorem 4: fixed cross-grade stabilizer is trivial

Let `g,h` be positive rational grades with `g != h`, and choose nonzero

\[
 x_g\in A_g,
 \qquad x_h\in A_h.
\]

Then line

\[
 L_{g,h}=\mathbb C(x_g+x_h)
 \tag{13}
\]

is invariant under `Gamma_c` if and only if `c=0`.

### Proof

Distinct homogeneous summands form direct sum. If line is invariant, some scalar `lambda`
satisfies

\[
 g^cx_g+h^cx_h=\lambda x_g+\lambda x_h.
\]

Comparing homogeneous components gives `g^c=lambda=h^c`. Since `g,h>0`, `g!=h`, and `c` is real,
this holds exactly for `c=0`. Converse is immediate. QED.

More generally, stabilizer of finite nonhomogeneous vector is intersection of equal-character
conditions across its grade support. Two distinct positive absolute grades already make it
trivial.

## Theorem 5: cross-grade relations form radial torsor

Theorem 4 does **not** select one relation. For `lambda>0`, set

\[
 L_\lambda=\mathbb C(x_g+\lambda x_h).
 \tag{14}
\]

Then

\[
 \Gamma_cL_\lambda
 =L_{\lambda(h/g)^c}.
 \tag{15}
\]

If `g!=h`, radial action is transitive on family `{L_lambda:lambda>0}`. Every member has trivial
stabilizer, yet no member is selected by radial-equivariant data.

### Proof

Scale `Gamma_c(x_g+lambda x_h)=g^c x_g+lambda h^c x_h` by nonzero scalar `g^(-c)` to obtain
`x_g+lambda(h/g)^c x_h`, proving `(15)`. Since positive number `(h/g)^c` ranges over all positive
reals as `c` ranges over `R`, action is transitive. Stabilizer statement is Theorem 4. QED.

Thus cross-grade line is a gauge slice, not gauge-breaking law, unless source independently
calibrates its coefficient. “Trivial stabilizer” is necessary but not sufficient.

## Countermodel: reciprocity and indefinite reflection remain blind

Take `A=C[Q_{>0}^times]` with coefficient-at-one trace and prime atom
`U_p tensor U_(p^-1)`. Every conclusion of Corollary 2 holds for all `c`. On reciprocal two-leg
space set

\[
 T_c=\begin{pmatrix}p^c&0\\0&p^{-c}\end{pmatrix},
 \qquad
 J=\begin{pmatrix}0&1\\1&0\end{pmatrix}.
 \tag{16}
\]

Then

\[
 T_c^*JT_c=J
 \tag{17}
\]

for every real `c`. Hence reciprocal product, reflection, nondegenerate indefinite pairing,
trace-one prime source, and all cyclic identities coexist with nonzero drift. Positive Hilbert
unitarity `T_c^*T_c=I` would force `c=0`, but source production of that positive premise is exactly
missing theorem.

Adelic product formula is equally blind:

\[
 \prod_v|q|_v^c=1
 \tag{18}
\]

for every principal idele `q` and every `c`.

## Literal RH specialization

At Xi divisor `rho`, established physical residue is

\[
 \operatorname{Res}(D_{n,\rho}u_p)
 =\bigl(\delta_n(\rho)-1\bigr)c_\rho,
 \qquad
 \delta_n(\rho)=e^{(2\Re\rho-1)\log n},
 \qquad c_\rho\ne0.
 \tag{19}
\]

Current source provides trace-one atom, genuine nonzero Kummer homology class, all-degree
boundary compatibility, Xi landing, Bockstein readout, and non-erasure. The class is nonzero; it
is not concealed higher cyclic boundary. Theorem 1 proves all current homogeneous operations are
equivariant under radial gauge family that `(19)` measures after physical landing.

Therefore exact missing selector is:

> a source-native, non-Morita-trivial **absolute radial calibration/anomaly** not equivariant
> under `Gamma_c`, produced before divisor specialization.

Theorem 4 gives smallest symmetry-breaking carrier, while Theorem 5 proves carrier family is
radial torsor. Source must select its coefficient, not merely construct some cross-grade line.
Equivalent possibilities are source-star/analytic-dagger identification with fixed absolute
normalization or nonprincipal prime--infinity boundary anomaly with source-derived affine origin.

## Seven conjecture/failure loops

1. **Trace one plus cyclicity:** fails by `(10)`.
2. **Adelic reciprocity:** fails by `(18)`.
3. **Reflection/Real structure:** fails by `(16)`--`(17)`.
4. **Finite-prime normality:** fails because finite positive measures with full support are
   mutually absolutely continuous; it cannot distinguish radial parameter.
5. **All-prime Kakutani normality:** can select zero drift, but proving Xi conormal lies in that
   normal source sector is RH-bearing missing premise, not derivation.
6. **Prime-torus recurrence:** phase torus sees angular characters, not radial multiplier `p^c`.
7. **Higher Hochschild/cyclic degree or Kummer class:** fails by Theorems 1 and 3 in all degrees.
8. **Any two-grade relation with trivial stabilizer:** insufficient by Theorem 5; all coefficients
   lie in one transitive radial orbit. Absolute calibration is missing.

## Nomotopy consequence

Current arithmetic objects are not under-represented. They are over-symmetric: every existing
observer descends through same diagonal radial gauge orbit. First genuine Nomogenic event must
produce **absolute calibration of a nonhomogeneous arithmetic relation**, not merely relation
with trivial point stabilizer. Otherwise it chooses coordinate in radial torsor by hand.

Falsifier: exhibit existing literal, divisor-independent source relation spanning distinct total
absolute grades, prove its coefficient is canonically normalized by source rather than gauge
choice, and show its physical image is dagger defect. Trivial stabilizer alone is insufficient.

## Hostile audit

1. This card does not construct missing relation and does not prove RH.
2. Cross-grade relation may always be adjoined by hand; that has no arithmetic content. Source
   must generate it canonically and independently of `rho`.
3. Standard graded-algebra theorem is not novel. Value is exact route closure: current source
   operations cannot produce radial selector.
4. Positive Hilbert completion, Kakutani equivalence, or same-orientation dagger can select only
   after adding premise whose source landing remains RH-equivalent.

## Literature boundary

Crossed-product cyclic decompositions and gauge actions are occupied parent mathematics; compare
Puschnigg, *Local cyclic homology of crossed products and Khalkhali's conjecture*, arXiv:2205.08880.
Infinite prime-torus recurrence refines angular dynamics, not radial selection; compare Baroni,
*The infinite prime torus and arithmetic Kronecker flows*, arXiv:2604.02213.

## Lean-return note

Formalized; see `identity-sector-radial-gauge-blindness-and-cross-grade-selection-law-formalized.md`.
Theorems 1, 3, 4 and 5 are proved for an arbitrary graded algebra over an arbitrary abelian grading
group.  The literal crossed-product instantiation of Corollary 2 is *not* rebuilt: the source
algebra stays where it is, and the countermodel identities `(16)`–`(18)` are proved for the
generalized-prime group algebra and for any field with an admissible family of absolute values.

## Log

- 2026-08-08 — seven-loop hostile arithmetic-source audit; proof promoted.
