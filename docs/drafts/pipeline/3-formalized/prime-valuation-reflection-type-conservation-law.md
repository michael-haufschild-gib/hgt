# Prime-valuation reflection-type conservation law

- **ID:** `prime-valuation-reflection-type-conservation-law`
- **Stage:** 3-formalized
- **Type:** UNIVERSAL THEOREM / RH PROOF-ARCHITECTURE CLASSIFICATION
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY AUDIT PENDING] [NOT RH]`
- **Formal modules:**
  - `formal/GaloisForLFunctions/RHTower/PrimeValuationHellingerReesReflectionFracture.lean`
  - `formal/GaloisForLFunctions/RHTower/AsymptoticTypeSuperselection.lean`
  - `formal/GaloisForLFunctions/RHTower/CriticalActivationReesSourceLaw.lean`
  - `formal/GaloisForLFunctions/RHTower/PrimeValuationHellingerReesJetStability.lean`
- **Source interfaces:**
  - `formal/GaloisForLFunctions/RHTower/EulerActivationSquarefreeDisintegration.lean`
  - `formal/GaloisForLFunctions/RHTower/GammaSewnMobiusXiWardJuliaTransport.lean`
  - `formal/GaloisForLFunctions/HTGeometry/PrimeResidueValuationInteractionSuperselection.lean`

## Discovery

The missing invariant is not a finite Rees grade. It is **asymptotic type**: membership in the
all-orders-flat radical. Finite grades may shift under a meromorphic or differential operation;
the flat radical cannot be crossed by any operator family whose full norm has any fixed finite
Rees order, even in arbitrary dimension.

The prime-valuation source realizes this invariant before divisor selection. Let
\[
 q_p=p^{-1},\qquad r_{p,c}=p^{-(1-2c)},\qquad
 u_{p,c}=p^{-(1-c)}
\]
and let
\[
 h_{p,c}^2
 =\frac{(1-q_p)(1-r_{p,c})}{(1-u_{p,c})^2}
\]
be the squared local Hellinger affinity between the critical geometric valuation law and its
radial twist. For
\[
 {\cal H}_N^{(2)}(c)=\prod_{p<N}h_{p,c}^2,\qquad
 a_N=\prod_{p<N}(1-p^{-1}),
\]
define
\[
 {\mathfrak F}_\infty(a)
 =\{f:\ f_N=o(a_N^K)\text{ for every }K\geq0\}.
\]

## Main theorem: exact three-phase reflection law

For every \(|c|<1/2\),
\[
 \boxed{
 {\cal H}^{(2)}(c)\in{\mathfrak F}_\infty(a)
 \quad\Longleftrightarrow\quad c>0.
 }
\]

More precisely, writing
\({\cal H}_N(c)=\sqrt{{\cal H}^{(2)}_N(c)}\):
\[
\begin{array}{c|c}
c<0&
{\cal H}^{(2)}_N(c)=\Theta(a_N),\quad
{\cal H}_N(c)=\Theta(\sqrt{a_N}),\\
c=0&
{\cal H}^{(2)}_N(0)={\cal H}_N(0)=1,\\
c>0&
{\cal H}^{(2)}(c),{\cal H}(c)\in\mathfrak F_\infty(a).
\end{array}
\]
For \(c<0\), the comparison is explicit:
\[
 a_N\le {\cal H}^{(2)}_N(c)
 \le
 \exp\!\left(6\sum_{n\ge1}n^{-(1-c)}\right)a_N.
\]
Thus the negative face is not merely nonflat; its exact finite grade is one for squared
affinity and one-half for affinity.

The normalization is now exact.  Define
\[
 Z_N(\beta)=\prod_{p<N}(1-p^{-\beta})^{-1}.
\]
Then
\[
 {\cal H}^{(2)}_N(c)
 =
 \frac{Z_N(1-c)^2}{Z_N(1)Z_N(1-2c)}
\]
for every \(c\) in the strip, and for \(c<0\),
\[
 \boxed{
 \frac{{\cal H}^{(2)}_N(c)}{a_N}
 \longrightarrow
 \frac{\zeta(1-c)^2}{\zeta(1-2c)}.
 }
\]
Thus the finite-grade face is the exact Hellinger midpoint-curvature ratio across the
Euler-product convergence wall, not only a \(\Theta\)-class.

Hence every noncritical reflected pair \(c,-c\) has opposite asymptotic types:
\[
 {\cal H}^{(2)}(c)\in{\mathfrak F}_\infty(a)
 \quad\Longleftrightarrow\quad
 {\cal H}^{(2)}(-c)\notin{\mathfrak F}_\infty(a).
\]

The proof is comparison-theoretic and does not need a prime-number-theorem asymptotic.

For \(c\leq0\), each local factor satisfies
\[
 1-p^{-1}\leq h_{p,c}^2,
\]
so
\[
 a_N\leq{\cal H}_N^{(2)}(c).
\]
Since \(a_N\to0\), the product cannot be flat beyond every power of \(a_N\). For \(c<0\), the
correction factor is bounded above because
\[
\frac{1-r_{p,c}}{(1-u_{p,c})^2}\le e^{6u_{p,c}},
\qquad
\sum_pu_{p,c}=\sum_pp^{-(1-c)}<\infty.
\]

For \(0<c<1/2\), for every \(L\) there is \(P_L\) such that
\[
 h_{p,c}^2\leq(1-p^{-1})^L\qquad(p\geq P_L).
\]
The finite prefix contributes one constant, hence
\[
 {\cal H}_N^{(2)}(c)=O(a_N^L).
\]
Taking \(L=K+1\) for every \(K\) proves all-orders flatness.

## Universal transport theorem

The operator theorem is arithmetic-independent.  Let \(E,F\) be arbitrary normed spaces,
let \(x\in\mathfrak F_\infty(a;E)\) be eventually nonzero, let
\(\|y_N\|=\Theta(a_N^d)\) for finite \(d\), and suppose
\[
R_Nx_N=y_N.
\]
Then
\[
a_N^{-K}=o(\|R_N\|)
\quad\text{for every fixed }K.
\]
In particular, if \(R_N:E\to F\) has
\[
 \|R_N\|_{\mathrm{op}}=O(a_N^{-K})
\]
for one finite \(K\), then
\[
 R{\mathfrak F}_\infty(a;E)\subseteq{\mathfrak F}_\infty(a;F).
\]
Therefore no such family can sew \({\cal H}^{(2)}(c)\) to
\({\cal H}^{(2)}(-c)\) when \(c\ne0\). Infinite rank is irrelevant; the full operator norm must
have an essential singularity beyond every Rees order, or the sewing must cease to be a bounded
operator.

This necessity is quantitative. For \(0<c<1/2\), the exact scalar sewing multiplier
\[
S_N(c)=
\frac{{\cal H}^{(2)}_N(-c)}
     {{\cal H}^{(2)}_N(c)}
\]
satisfies
\[
\boxed{
a_N^{-K}=o(S_N(c))
\quad\text{for every fixed }K.
}
\]
If bounded linear maps \(R_N:\mathbb R\to\mathbb R\) satisfy
\[
R_N({\cal H}^{(2)}_N(c))={\cal H}^{(2)}_N(-c),
\]
then
\[
a_N^{-K}=o(\|R_N\|)
\quad\text{for every fixed }K.
\]
Thus exact sewing has an essential Rees singularity; “unbounded” is not merely qualitative.

In the centered zeta coordinate \(c=\Re\rho-1/2\), the critical line is consequently the unique
locus where prime-valuation reflection does not fracture asymptotic type.

## Positive escape: modular retuning

Finite-Rees no-sewing is not a ban on reflection.  The normalized rank-one rational Weyl
complementary channel
\[
 \lambda_p(z)=\frac{pz^2-1}{p-z^2}
\]
has the exact defect
\[
 |pz^2-1|^2-|p-z^2|^2=(p^2-1)(|z|^4-1).
\]
Hence \(|\lambda_p(z)|=1\) exactly on \(|z|=1\).  On the real outward radial face
\(z=p^c\), \(0<c<1/2\),
\[
 p^{2c}<\lambda_p(p^c),
\]
and scalar gauge cannot change the complementary/spherical ratio.  Standard external Weyl
joining therefore crosses the Hellinger fracture by retuning modular class.  The conservation
law applies to source-internal reflection with fixed ordinary-prime modular class, not to every
adelic intertwiner.

## Activation and divisor consequences

The diagonal activation is
\[
 \frac{\zeta(s)}{\zeta(2s)}.
\]
At \(q_p=p^{-1}\), its valuation law disintegrates into radical occupancy and conditional depth:
\[
 \nu_p(0)=\frac1{1+q_p},\qquad
 \nu_p(k)=\frac{(1-q_p)q_p^k}{1+q_p}\quad(k\geq1).
\]
The same source has:

1. nonsummable occupancy mass \(1/(p+1)\);
2. summable fixed depth-\(\geq2\) tails;
3. nonsummable Fisher-whitened Gamma fibre
   \((p-1)/(p(p+1))\);
4. no nonzero finite recurrence on infinitely many reciprocal-prime nodes.

At a divisor of multiplicity \(d\), the overlap \(t^d\) and first Fisher numerator
\(dt^{d-1}\) have ratio
\[
 \frac{|dt^{d-1}|^2}{|t^d|^2}=\frac{d^2}{|t|^2}.
\]
A bounded positive \(2\times2\) Gram completion is therefore impossible. The singular overlap
division in the Möbius--Gamma source graph is forced by divisor grade loss; it is not a removable
normalization defect. That graph reconstructs the continued Xi current on the safe Euler domain.

## Hypertranscendental noncompression

The source has an independent algebraic obstruction. Valuation depth and residue-support breadth
form a joint grid. Every selected support sector is relatively hypertranscendental over its
complete complement, with exact rank
\[
 d\prod_{i\in S}(|A_i|-1).
\]
Every complete next valuation layer is relatively hypertranscendental over the full finite-depth
prefix. Prime-local fusion of two prefix carriers lands exactly in the next layer but outside the
differential field generated by the prefix.

Thus the same prime source is incompressible in three distinct categories:

1. **linear:** no finite recurrence compresses reciprocal-prime nodes;
2. **differential:** no finite differential field contains the fusion-complete valuation tower;
3. **asymptotic/operator:** no finite-Rees operator crosses the reflected flat radical.

These are not three unrelated no-go statements. They are shadows of one source-completeness law:
finite observation may retain a projection of the prime grid, but no finite algebraic, spectral,
or operator closure retains its fusion, divisor transgression, and reflection type simultaneously.

## RH-facing conclusion

The theorem does not prove RH. It does identify a new proof architecture and excludes a broad
class of substitutes:

- bounded Hilbert-space reflection;
- finite-order graded matrices;
- arbitrary-dimensional bounded operator families with polynomial Wold-volume growth;
- finite differential closures of the valuation tower;
- finite recurrences on the prime node spectrum.

The exact surviving object is a divisor-graded singular correspondence: unbounded on the
ungraded Hilbert source, finite on the associated Rees symbol, non-diagonal in the Julia
coordinate, and faithful to the complete prime-valuation grid. The existing Möbius--Gamma/Xi
graph supplies the forced singular division and the continued Xi current; the reflection-type
law supplies the critical-line selector.

The analytic consumer is also exact.  The finite-aperture Xi transport is unconditionally
four-unit nonexpansive on every right-half-plane Hardy packet.  Its zero-aperture derivative is
the continued anti-causal Ward response, and the scalar four-unit derivative law on the Euler
edge is equivalent to RH.  A strict-right pair violates the derivative bound at one adapted
node.  Thus the missing zero-exclusion input is source-controlled boundary-tangent passage, not
additional finite-aperture positivity.

## Scope controls

- No zero exclusion is claimed.
- No bounded source reflection is inferred from functional equation symmetry.
- No positivity theorem is inferred from the singular graph identity.
- Hellinger flatness uses actual rational primes and the exact Wold vacuum scale.
- “Infinite dimensional” is not treated as an escape from the no-sewing theorem.
- Hypertranscendence is used for source noncompression, not as a zero-location criterion.

## Gates

- [x] exact local squared Hellinger affinity
- [x] negative/nonpositive face bounded below by Wold vacuum volume
- [x] negative face exact Wold grade; unsquared affinity exact half-normal grade
- [x] exact Euler-partition midpoint ratio and zeta normalization on negative face
- [x] critical face has identically unit affinity
- [x] positive face flat beyond every Wold Rees order
- [x] reflected type fracture iff \(c\ne0\)
- [x] arbitrary-dimensional finite-Rees operator no-sewing theorem
- [x] exact rank-one Weyl modular-retuning escape and unitary locus
- [x] critical activation occupancy/depth/Fisher phase split
- [x] reciprocal-prime finite-recurrence rigidity
- [x] divisor Gram inverse-square blow-up
- [x] actual singular Möbius--Gamma graph reaches continued Xi current
- [x] finite-aperture four-unit nonexpansiveness and RH-complete boundary Ward tangent
- [x] HT depth--support superselection and fusion escape
- [x] targeted literature collision audit
- [ ] independent hostile referee audit
- [x] publication manuscript integration
