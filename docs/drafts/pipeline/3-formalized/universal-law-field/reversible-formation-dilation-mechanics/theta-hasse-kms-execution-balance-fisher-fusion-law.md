# Theta--Hasse--KMS execution balance and Fisher fusion law

- **ID:** ULF-RFDM-2
- **Stage:** 3-formalized
- **Type:** SOURCE-NATIVE FOUR-ORGAN FUSION / GLOBAL BALANCE COORDINATE
- **Parent field:** Reversible Formation-Dilation Mechanics
- **Status:** [PAPER-PROVED] [DEPENDENCY-CLOSED] [ONE PRE-ZERO SOURCE]
  [FUNCTIONAL-EQUATION ACTION] [COMMON RECOVERY] [PATH/STATE CONSERVATION]
  [GLOBAL REFLECTION BALANCE] [PROPER ONTO IMAGE] [FISHER RESPONSE]
  [LEAN-CERTIFIED CONTINUOUS THETA ASSEMBLY] [NOT RH]

## 1. The mechanism

The functional equation is a reversible action on the theta source. Hasse packet formation is a
parameter-independent recovery law. Toeplitz--KMS history is the same geometric recovery law read
as a Gibbs spectrum. Fresh packet execution is irreversible even though the endpoint action is
reversible.

These statements become one mechanism only after retaining all three grades:

1. the **source law** and its reflection action;
2. the **formed conditional packet** and its reversible dilation;
3. the **reset path law**, whose singularity measures information discarded by finite closure.

This card proves that one literal theta source generates all three grades and that reset-path
singularity is exactly conserved as KMS state mixedness. Its source average is a global coordinate
for the functional-equation tilt: reflected equality selects the center and only the center.

No zero, divisor point, critical-line premise, or route-local null relation enters the proof.

## 2. Literal theta source and functional-equation action

Let

\[
 \Phi(x)=\operatorname{thetaCuspFullSource}(x).
 \tag{THK.1}
\]

The established theta-source theorem gives:

- \(\Phi(x)>0\) for every \(x\in\mathbb R\);
- \(\Phi(-x)=\Phi(x)\);
- for \(|a|<1\),
  \[
   Z(a)=\int_{\mathbb R}e^{ax}\Phi(x)\,dx
       =\Xi_C(ia)\in(0,\infty);
   \tag{THK.2}
  \]
- differentiation under the integral is valid on every compact subinterval of \((-1,1)\).

Define the probability law

\[
 \nu_a(dx)=Z(a)^{-1}e^{ax}\Phi(x)\,dx,
 \qquad |a|<1.
 \tag{THK.3}
\]

For \(R(x)=-x\), evenness gives

\[
 Z(-a)=Z(a),
 \qquad
 R_*\nu_a=\nu_{-a}.
 \tag{THK.4}
\]

Put \(F(a)=\log Z(a)\). Then

\[
 F'(a)=\mathbb E_{\nu_a}X,
 \qquad
 F''(a)=\operatorname{Var}_{\nu_a}(X)>0.
 \tag{THK.5}
\]

Thus reflection is an exact functional-equation action and \(a\) is its signed source tilt.
Under the standard Xi convention \(\Xi_C(w)=\xi(1/2+iw)\), the corresponding real part is
\(\sigma=1/2-a\).

## 3. Common Hasse recovery and KMS reconstruction

For \(x\in\mathbb R\), set

\[
 t=e^x,
 \qquad
 q(x)=\frac{1-e^{-e^x}}2\in(0,1/2),
 \tag{THK.6}
\]

and define the Hasse recovery kernel

\[
 K_H(x,n)=(1-q(x))q(x)^n,
 \qquad n\in\mathbb N.
 \tag{THK.7}
\]

The formed theta--Hasse law is

\[
 \widehat Q_a(dx,n)=\nu_a(dx)K_H(x,n).
 \tag{THK.8}
\]

The kernel is independent of \(a\). Projection recovers \(\nu_a\), and common-kernel formation
preserves both directed KL divergence and Jeffreys work exactly.

The conditional packet itself reconstructs the source scale:

\[
 q(x)=\frac{K_H(x,n+1)}{K_H(x,n)},
 \qquad
 x=\log\!\bigl[-\log(1-2q(x))\bigr].
 \tag{THK.9}
\]

The ratio is independent of \(n\). Hence the conditional-law map \(x\mapsto K_H(x,\cdot)\) is
injective; no depth layer is selected.

Now let

\[
 \rho_x=(1-q(x))q(x)^N
 \tag{THK.10}
\]

be the Toeplitz Gibbs density in the history-depth basis. Its modular product is recovered by

\[
 \beta E(x)=-\log q(x)
 =\log\frac{K_H(x,n)}{K_H(x,n+1)}.
 \tag{THK.11}
\]

Thus the same marked source coordinate determines:

1. the theta observer law \(\nu_a\);
2. the Hasse conditional packet \(K_H(x,\cdot)\);
3. the KMS modular product and state spectrum \(\rho_x\).

The statement determines \(\beta E\), not a separate choice of inverse temperature and energy.

## 4. Fibrewise path/state conservation

For a probability vector \(p\), let \(\Delta_p\) be the deterministic-return coupling and
\(p\otimes p\) the fresh-reset coupling. For the geometric packet \(p_{q}(n)=(1-q)q^n\), define

\[
 v(q)=\frac{2q}{1+q},
 \tag{THK.12}
\]

\[
 h(q)=-\log(1-q)-\frac{q}{1-q}\log q.
 \tag{THK.13}
\]

The packet execution theorem and the Toeplitz spectral formula give, for every \(x\),

\[
 \boxed{
 \operatorname{TV}(\Delta_{K_H(x)},K_H(x)\otimes K_H(x))
 =v(q(x))
 =1-\operatorname{Tr}(\rho_x^2).}
 \tag{THK.14}
\]

Likewise,

\[
 \boxed{
 D(\Delta_{K_H(x)}\Vert K_H(x)\otimes K_H(x))
 =h(q(x))
 =S_{\mathrm{vN}}(\rho_x).}
 \tag{THK.15}
\]

The reverse divergence is infinite:

\[
 D(K_H(x)\otimes K_H(x)\Vert\Delta_{K_H(x)})=+\infty.
 \tag{THK.16}
\]

Equations (THK.14)--(THK.15) are not analogies. They identify two path-law defects with two
operator-state invariants exactly:

- total-variation failure of deterministic closure = linear entropy;
- directed-KL cost of deterministic closure = von Neumann entropy.

## 5. Global source averages

Define

\[
 \mathcal V(a)=\mathbb E_{\nu_a}[v(q(X))],
 \qquad
 \mathcal H(a)=\mathbb E_{\nu_a}[h(q(X))].
 \tag{THK.17}
\]

Because \(0<q(x)<1/2\),

\[
 0<v(q(x))<\frac23,
 \qquad
 0<h(q(x))<2\log2.
 \tag{THK.18}
\]

Both source averages are finite. Integrating (THK.14)--(THK.15) proves the exact four-organ
conservation law

\[
 \boxed{
 \mathcal V(a)
 =\mathbb E_{\nu_a}\operatorname{TV}(\Delta_{K_H(X)},K_H(X)^{\otimes2})
 =\mathbb E_{\nu_a}[1-\operatorname{Tr}(\rho_X^2)],}
 \tag{THK.19}
\]

\[
 \boxed{
 \mathcal H(a)
 =\mathbb E_{\nu_a}D(\Delta_{K_H(X)}\Vert K_H(X)^{\otimes2})
 =\mathbb E_{\nu_a}S_{\mathrm{vN}}(\rho_X).}
 \tag{THK.20}
\]

The source measure, recovery packet, path execution, and KMS state are therefore one conservative
formation chain.

## 6. Strict source response

### Lemma 6.1 -- monotone-statistic response

Let \(g:\mathbb R\to\mathbb R\) be bounded and strictly increasing. Put

\[
 M_g(a)=\mathbb E_{\nu_a}g(X).
 \tag{THK.21}
\]

Then \(M_g\) is differentiable on \((-1,1)\) and

\[
 \boxed{M_g'(a)=\operatorname{Cov}_{\nu_a}(g(X),X)>0.}
 \tag{THK.22}
\]

#### Proof

Exponential moments on compact substrips justify differentiating numerator and denominator in
(THK.21), giving the covariance identity. If \(X,Y\) are independent with law \(\nu_a\), then

\[
 2\operatorname{Cov}_{\nu_a}(g(X),X)
 =\mathbb E[(g(X)-g(Y))(X-Y)].
 \tag{THK.23}
\]

The integrand is nonnegative because \(g\) is increasing. It is strictly positive whenever
\(X\ne Y\). The law \(\nu_a\) has a positive continuous density on \(\mathbb R\), so
\(\mathbb P(X\ne Y)=1\). Hence the covariance is strictly positive. QED.

### Theorem 6.2 -- global execution response

Both \(x\mapsto v(q(x))\) and \(x\mapsto h(q(x))\) are bounded and strictly increasing. Therefore

\[
 \boxed{
 \mathcal V'(a)=\operatorname{Cov}_{\nu_a}(v(q(X)),X)>0,}
 \tag{THK.24}
\]

\[
 \boxed{
 \mathcal H'(a)=\operatorname{Cov}_{\nu_a}(h(q(X)),X)>0.}
 \tag{THK.25}
\]

#### Proof

One has

\[
 q'(x)=\frac12e^{x-e^x}>0,
 \qquad
 v'(q)=\frac2{(1+q)^2}>0,
 \tag{THK.26}
\]

and

\[
 h'(q)=-\frac{\log q}{(1-q)^2}>0
 \qquad(0<q<1).
 \tag{THK.27}
\]

Apply Lemma 6.1. QED.

## 7. Reflection balance is a proper global coordinate

For either \(g=v\circ q\) or \(g=h\circ q\), define the reflected execution gap

\[
 B_g(a)=M_g(a)-M_g(-a).
 \tag{THK.28}
\]

### Theorem 7.1 -- exact reflection-balance selection

The function \(B_g\) is continuous, odd, and strictly increasing on \((-1,1)\). Moreover,

\[
 \boxed{
 B_g(a)=\frac2{Z(a)}\int_0^\infty
   (g(x)-g(-x))\sinh(ax)\Phi(x)\,dx,}
 \tag{THK.29}
\]

and

\[
 \boxed{B_g(a)=0\iff a=0.}
 \tag{THK.30}
\]

Equivalently,

\[
 \boxed{
 \mathcal V(a)=\mathcal V(-a)\iff a=0,
 \qquad
 \mathcal H(a)=\mathcal H(-a)\iff a=0.}
 \tag{THK.31}
\]

Finally, \(B_g:(-1,1)\to B_g((-1,1))\) is a homeomorphism and therefore a proper map onto its
image.

#### Proof

Oddness is immediate from the definition. Theorem 6.2 gives

\[
 B_g'(a)=M_g'(a)+M_g'(-a)>0,
 \tag{THK.32}
\]

so \(B_g\) is strictly increasing. For (THK.29), use \(Z(-a)=Z(a)\), subtract the two tilted
integrals, split \(\mathbb R\) into positive and negative halves, and use evenness of \(\Phi\).
When \(a>0\), every factor in the integrand of (THK.29) is strictly positive; the sign reverses
for \(a<0\). This proves (THK.30)--(THK.31). A continuous strictly monotone map on an interval is
a homeomorphism onto its image. Every homeomorphism is proper onto its image because its inverse
maps compact sets to compact sets. QED.

This is the missing global statement that pointwise scale balance did not provide: the entire
source-averaged execution/KMS bundle has one and only one reflected balance fibre.

## 8. Fourier/Xi reconstruction

The same source law has characteristic function

\[
 \boxed{
 C_a(t)=\mathbb E_{\nu_a}e^{-itX}
 =\frac{\Xi_C(t+ia)}{\Xi_C(ia)}.}
 \tag{THK.33}
\]

#### Proof

By the theta Fourier theorem,

\[
 \int_{\mathbb R}e^{-iwx}\Phi(x)\,dx=\Xi_C(w).
\]

Substitute \(w=t+ia\), since \(e^{-i(t+ia)x}=e^{ax}e^{-itx}\), and divide by
\(Z(a)=\Xi_C(ia)\). QED.

Thus the Fourier/Xi observer reconstructs \(\nu_a\), while the marked Hasse ratios reconstruct
each conditional source scale \(x\). The two reconstructions are complementary rather than
duplicative:

- all \(t\)-values of \(C_a\) determine the global source law;
- one adjacent-depth conditional ratio determines the local source coordinate;
- the KMS spectrum gives the same local ratio as a modular product.

## 9. Fourth-organ Fisher prediction

The theta tilt Fisher information is

\[
 \mathcal I(a)=\operatorname{Var}_{\nu_a}(X)=F''(a).
 \tag{THK.34}
\]

Cauchy--Schwarz applied to (THK.24)--(THK.25) gives

\[
 (\mathcal V'(a))^2
 \le \mathcal I(a)\operatorname{Var}_{\nu_a}(v(q(X))),
 \tag{THK.35}
\]

\[
 (\mathcal H'(a))^2
 \le \mathcal I(a)\operatorname{Var}_{\nu_a}(h(q(X))).
 \tag{THK.36}
\]

Popoviciu's variance bound and (THK.18) yield the explicit predictions

\[
 \boxed{\mathcal I(a)\ge9(\mathcal V'(a))^2,}
 \tag{THK.37}
\]

\[
 \boxed{
 \mathcal I(a)\ge
 \frac{(\mathcal H'(a))^2}{(\log2)^2}.}
 \tag{THK.38}
\]

These inequalities were not used to define the source, recovery kernel, execution defect, or KMS
state. They are forced responses in a fourth organ: every realization of the same formation chain
must pay enough source Fisher information to support its observed execution-entropy response.

## 10. Exact selection interface

Under \(a=1/2-\sigma\), Theorem 7.1 says

\[
 \boxed{
 \text{reflected source-averaged execution balance}
 \Longrightarrow \sigma=1/2.}
 \tag{THK.39}
\]

This is not RH. The remaining RH-facing theorem is now sharply typed:

> Construct one pre-zero divisor comparison showing that every Xi zero forces equality of the two
> reflected source-averaged execution defects in (THK.31), or forces a uniformly bounded orbit in
> the proper coordinate \(B_g\).

If such a comparison is constructed without using the zero's real part, (THK.30) forces central
tilt. Functional equation and common recovery alone do not imply this equality; they only make the
comparison meaningful and information-neutral.

## 11. Hostile loops and scope

1. **Generic tilt monotonicity is the theorem. -- False.** Generic covariance response was already
   known and formalized. New content is literal source fusion (THK.19)--(THK.20), the reflected
   global coordinate (THK.29)--(THK.31), and the forced Fisher response (THK.37)--(THK.38).
2. **Raw Hasse/Fermi scale law carries the functional equation. -- False.** Reciprocal reflection
   fails for its nonsymmetric base density. The even theta source is load-bearing.
3. **Common-kernel KL isometry makes reset execution reversible. -- False.** It preserves endpoint
   information but (THK.16) proves path-level singularity in the reverse direction.
4. **An unmarked mixture of KMS states reconstructs the source. -- Not proved and generally
   false.** Reconstruction uses the marked base coordinate or the full conditional-state field.
5. **Separate \(\beta\) and \(E\) are reconstructed. -- False.** Only their product is canonical.
6. **Strict balance proves RH. -- False.** A divisor-to-execution equality remains open.
7. **Proper onto image means coercive on \(\mathbb R\). -- False.** The source chamber is
   \((-1,1)\); properness is relative to the intrinsic image coordinate.
8. **Positive KMS state alone gives functional reflection. -- False.** Reflection comes from the
   theta source and is transported through the common recovery law.

## 12. Literature boundary

Exponential-family covariance identities, monotone likelihood ratio order, KMS/Gibbs geometric
spectra, Markov dilations, and sufficient-statistic information geometry are established parent
mathematics. Relevant parents include Nagaoka, *The exponential family of Markov chains and its
information geometry* (arXiv:1701.06119), Dowty, *Chentsov's theorem for exponential families*
(arXiv:1701.08895), and Gregoratti's deterministic invertible dilations of discrete-time Markov
evolutions (arXiv:math/0512393 and math/0702690).

No priority claim is made for these ingredients. The field-level result is their exact constitutive
coupling by one HGT source:

\[
 \boxed{
 \text{theta functional equation}
 \to\text{ common Hasse recovery}
 \to\text{ reset-path singularity}
 \equiv\text{ KMS mixedness}
 \to\text{ global reflected balance/Fisher response}.}
 \tag{THK.40}
\]

## 13. Lean certification

`ConstitutiveThetaHasseKMSExecutionBalance.lean` and
`ThetaHasseKMSContinuousAssembly.lean` certify without placeholders:

1. exact geometric packet normalization and adjacent-layer parameter recovery;
2. purity/linear-entropy and Shannon/von-Neumann-entropy identities;
3. strict monotonicity of the Hasse ratio and both execution statistics;
4. unique reflected balance in every nondegenerate even two-point source fibre;
5. continuous theta-law normalization, bounded statistic integrability, and differentiation under
   the tilted integral;
6. exact continuous covariance response and strict positivity;
7. reflected half-line `sinh` formula, unique central balance, intrinsic-image homeomorphism, and
   properness;
8. continuous Cauchy--Schwarz and Popoviciu bounds with the exact constants in (THK.37)--(THK.38);
9. composition with the theta--Hasse common-recovery marginal, reflection lift, and directed-KL
   isometries;
10. the normalized theta characteristic-function/Xi identity (THK.33), imported from and assembled
    with the literal theta Fourier--Laplace theorem;
11. source-averaged purity/Shannon conservation and the central-`sigma` selection interface.

Certificate:
`docs/drafts/pipeline/3-formalized/universal-law-field/reversible-formation-dilation-mechanics/theta-hasse-kms-execution-balance-fisher-fusion-law-formalized.md`.

The literal theta integral/Fourier identity is inherited from existing theta-source modules and
assembled directly; no restated hypothesis or card-local axiom is used. All declarations in the
continuous assembly have the standard project axiom footprint only: `propext`,
`Classical.choice`, and `Quot.sound`.
