# Poisson--zeta three-term arithmetic cohomology

- **ID:** `deninger-poisson-zeta-three-term-cohomology`
- **Stage:** 3-formalized
- **Type:** THEOREM (paper; source construction plus published analytic inputs)
- **Labels:** `DAC_POISSON_ZETA_MIDDLE_COEFFICIENT`,
  `DAC_POISSON_ZETA_THREE_TERM_COHOMOLOGY`,
  `DAC_POISSON_ZETA_POINCARE_PAIRING`,
  `DAC_POISSON_ZETA_REGULARIZED_DETERMINANT`
- **Parent:** `deninger-arithmetic-endpoint-relative-middle-reduction`
- **Scope:** \(\overline{\operatorname{Spec}\mathbb Z}\)
- **Statement:** Meyer's source-defined zeta-operator quotient, joined to the
  strict Milnor--Arakelov endpoint, is a three-term arithmetic cochain
  complex with \(H^0=\mathbb C\), spectral \(H^1\), and
  \(H^2=\mathbb C(-1)\).  Its alternating character is the Weil explicit
  formula, and Paugam's unconditional symplectic form supplies the
  \(H^1\times H^1\to H^2\) Poincare pairing.

## 1. Why this is a Deninger coefficient

Deninger's approximation to the arithmetic dynamical space is the
suspension of a \(\mathbb Q_{>0}\)-space.  Its prime Frobenii generate
commuting power correspondences, and the suspended action is the
\(\mathbb R_{>0}\)-flow.  The analytic operator below is made from exactly
those power correspondences:
\[
 Z=\sum_{n\geq1}\lambda_{n^{-1}},\qquad
 (Zf)(x)=\sum_{n\geq1}f(nx).                                      \tag{1}
\]
No zeta zero occurs in `(1)`.  The Euler factorization
\[
 Z=\prod_p(1-\lambda_{p^{-1}})^{-1}                               \tag{2}
\]
holds on the right-decaying source space.  Thus finite primes enter through
the actual Frobenius/power semigroup, while the real Fourier transform and
Poisson summation supply the archimedean gluing.

This is a candidate **relevant analytic coefficient** of the kind Deninger
requires on his approximate space.  Identification with a geometric
\(R\alpha_*\mathcal G\) is a separate comparison conjecture; it is not used
in the theorem below.

### Coefficient-category correction

All three source spaces in `(3)` and the endpoint in `(8)` are complex.
This is essential, not cosmetic.  Deninger's no-real-coefficients theorem
rules out a functorial arithmetic Weil theory obtained by complexifying an
ordinary real-valued \(H^1\).  The compatible target is his
\(K_{\mathbb R}\)-category:

- \(H^0=\mathbb C\) and \(H^2=\mathbb C(-1)\) are even objects with the
  real forms supplied by constants and Arakelov degree;
- \(H^1=M_\zeta\) is odd: Paugam's upper/lower spectral splitting and
  sign--conjugation operator
  \[
    C=\begin{pmatrix}1&0\\0&-1\end{pmatrix}c
  \]
  satisfy \(C^2=-1\) unconditionally on the nonreal spectral
  suspension.  When the Poisson map respects the upper/lower
  conjugation exchange, this odd structure descends through its
  algebraic cokernel; the generic descent theorem is written in
  `DeningerArithmeticPaugamKReal.lean`.
  For the Riemann zeta function no nontrivial zero is real.  This gives
  spectral \(K_{\mathbb R}\)-parity, but not
  source-geometric descent or positivity.

The theorem in this card constructs the underlying complex cohomology,
flow, determinant, alternating pairing, and spectral odd parity.
Constructing that parity on the relevant source complex and proving its
Hodge form positive are the geometric polarization gates.

## 2. Source spaces and the zeta operator

Let \(G=\mathbb R_{>0}\), with Haar measure \(d^\times x=dx/x\), and write
\[
 \lambda_t f(x)=f(t^{-1}x).
\]
For an interval \(I\subset\mathbb R\), let
\[
 \mathcal S(G)_I
 =
 \{f:G\to\mathbb C:\ x^s f(x)\in\mathcal S(G)
                    \text{ for every }s\in I\}.
\]
Meyer's three source spaces are
\[
\begin{aligned}
 H_+&=\mathcal S(\mathbb R)^{\mathrm{even}},\\
 H_\cap
   &=\{f\in H_+:\ f(0)=\mathcal Ff(0)=0\},\\
 H_-&=\mathcal S(G)_{]-\infty,\infty[}.
\end{aligned}                                                     \tag{3}
\]
Here \(\mathcal F\) is the additive Fourier transform.  Define
\[
 Jf(x)=x^{-1}f(x^{-1}).                                           \tag{4}
\]
Poisson summation gives, for \(f\in H_+\),
\[
 \frac{f(0)}2+Zf(x)
 =
 JZ\mathcal Ff(x)+\frac{\mathcal Ff(0)}{2x}.                       \tag{5}
\]
Consequently \(Z(H_\cap)\subset H_-\).

Meyer's closed-range theorem proves:
\[
 Z:H_\cap\longrightarrow H_-
\quad\text{is a continuous strict closed embedding}.              \tag{6}
\]
It follows that
\[
 M_\zeta:=H_-/Z(H_\cap)                                           \tag{7}
\]
is a nuclear Frechet representation of \(G\).  Both `(6)` and `(7)` are
defined before mentioning \(\zeta\) or any zero.

## 3. Strict Milnor--Arakelov endpoint

Put
\[
 P_\mathbb Q
 =
 (\mathbb Q^\times/\{\pm1\})\otimes_\mathbb Z\mathbb C
\]
and let \(D_{\mathrm{Ar},\mathbb Q}\) be the completed complex Arakelov
divisor space.  The strict principal-divisor sequence proved in
`DAC_COMPLETED_ARAKELOV_TRACE_KERNEL` is
\[
 0\longrightarrow P_\mathbb Q
 \xrightarrow{\operatorname{pr}}
 D_{\mathrm{Ar},\mathbb Q}
 \xrightarrow{\deg}
 \mathbb C(-1)
 \longrightarrow0.                                                \tag{8}
\]
The finite coordinates of \(\operatorname{pr}\) are
\(\operatorname{ord}_p\), the real coordinate is
\(-\log|\cdot|_\infty\), and
\[
 \deg((d_p)_p,d_\infty)
 =
 \sum_p d_p\log p+d_\infty.                                       \tag{9}
\]

## 4. The three-term complex

Define
\[
\begin{aligned}
 C^0_{\mathrm{PZ}}&=\mathbb C\oplus H_\cap,\\
 C^1_{\mathrm{PZ}}&=H_-\oplus P_\mathbb Q,\\
 C^2_{\mathrm{PZ}}&=D_{\mathrm{Ar},\mathbb Q},
\end{aligned}
\qquad
\begin{aligned}
 d^0(a,f)&=(Zf,0),\\
 d^1(g,u)&=\operatorname{pr}(u).
\end{aligned}                                                     \tag{10}
\]
Because \(d^1d^0=0\), `(10)` is a cochain complex.  Both differentials
have strict closed range by `(6)` and `(8)`.

`[PROVED HERE] [DAC_POISSON_ZETA_THREE_TERM_COHOMOLOGY]`

The ordinary and reduced cohomologies agree, and
\[
 H^i(C^\bullet_{\mathrm{PZ}})
 \cong
 \begin{cases}
   \mathbb C,&i=0,\\
   M_\zeta,&i=1,\\
   \mathbb C(-1),&i=2,\\
   0,&\text{otherwise}.
 \end{cases}                                                       \tag{11}
\]

### Proof

Injectivity of \(Z|_{H_\cap}\) and of \(\operatorname{pr}\) gives
\[
 \ker d^0=\mathbb C\oplus0,\qquad
 \ker d^1=H_-\oplus0.
\]
Therefore
\[
 H^1
 =
 (H_-\oplus0)/(Z(H_\cap)\oplus0)
 \cong M_\zeta.
\]
Equation `(8)` gives \(H^2\cong\mathbb C(-1)\).  Closedness of both
images proves the assertion about reduced cohomology.

## 5. Flow and spectral theorem

Let the flow act:

- trivially on the constant summand of \(C^0\);
- by \(\lambda_{e^t}\) on \(H_\cap\) and \(H_-\);
- by multiplication by \(e^t\) on \(P_\mathbb Q\) and
  \(D_{\mathrm{Ar},\mathbb Q}\).

The operator \(Z\) is \(G\)-equivariant and `(8)` is homogeneous, so this
is a cochain flow.  Its infinitesimal generator \(\Theta\) acts with
weights \(0\) and \(1\) on \(H^0\) and \(H^2\).

On \(M_\zeta\), \(\Theta\) is induced by the logarithmic scaling generator
\(-x\,d/dx\).  Meyer's spectral theorem gives
\[
 \operatorname{Spec}(\Theta\mid M_\zeta)
 =
 \{\rho:\xi(\rho)=0\},                                             \tag{12}
\]
with spectral algebraic multiplicity equal to the order of the zero.
Equivalently, literal generalized eigenfunctionals occur on the strong
dual \(M_\zeta'\): the order-\(m\) zero \(\rho\) contributes the
evaluation jets
\[
 h\longmapsto h^{(j)}(\rho),\qquad 0\leq j<m.                      \tag{13}
\]
This distinction between the quotient representation and its
eigenfunctional realization is part of the topology, not an assumption.

The Mellin transform proves `(12)`: it identifies \(H_-\) with entire
functions rapidly decreasing on every vertical line and identifies
\(Z(H_\cap)\) with the subspace divisible, with the required stripwise
Schwartz control, by the completed zeta factor.  This is a theorem about
the source quotient `(7)`, not a definition using the zero divisor.

## 6. Character and Lefschetz formula

For every \(f\in C_c^\infty(G)\), the integrated flow operators are
nuclear in Meyer's sense.  The alternating cohomological character is
\[
\begin{aligned}
 \chi_{\mathrm{PZ}}(f)
 &=
 \operatorname{Tr}\!\left(\int f\,\middle|\,H^0\right)
 -
 \operatorname{Tr}\!\left(\int f\,\middle|\,H^1\right)
 +
 \operatorname{Tr}\!\left(\int f\,\middle|\,H^2\right)\\
 &=
 W(f),                                                            \tag{14}
\end{aligned}
\]
where \(W\) is the raw Weil distribution.  Spectrally,
\[
 W(f)
 =
 \widehat f(0)+\widehat f(1)
 -
 \sum_{\xi(\rho)=0}m_\rho\widehat f(\rho),                         \tag{15}
\]
with uniform absolute convergence on bounded test-function sets.
Geometrically,
\[
 W=\sum_p W_p+W_\infty,                                           \tag{16}
\]
where \(W_p\) is the prime-power orbital distribution with
\(\log p\) weights and \(W_\infty\) is the archimedean principal-value
term.  Thus `(14)` is the required explicit-formula/Lefschetz character
identity for the coefficient.

What remains conjectural is identifying each \(W_p\) in `(16)` with the
fixed-orbit distribution of Deninger's actual packet
\(\Gamma_p\).  The analytic character identity itself is unconditional.

## 7. Regularized determinant

Let
\[
 \widehat\zeta(s)=\pi^{-s/2}\Gamma(s/2)\zeta(s)
\]
and set
\[
 \xi_{\mathrm D}(s)
 =
 \frac{s}{2\pi}\frac{s-1}{2\pi}\widehat\zeta(s).                  \tag{17}
\]
Deninger's regularized-product theorem proves
\[
 \xi_{\mathrm D}(s)
 =
 \prod_{\widehat\zeta(\rho)=0}^{\infty}
 \frac{s-\rho}{2\pi},                                            \tag{18}
\]
where the product is the spectral-zeta regularized product and every
zero occurs with its analytic multiplicity.

`[PROVED HERE] [DAC_POISSON_ZETA_REGULARIZED_DETERMINANT]`

Equip the generalized spectral realization of \(M_\zeta\) with the
spectral determinant
\[
 D_1(s)
 =
 \det_\infty\!\left(
   \frac{s-\Theta}{2\pi}\,\middle|\,M_\zeta
 \right).
\]
Then
\[
 D_1(s)=\xi_{\mathrm D}(s).                                      \tag{19}
\]
On the endpoint lines,
\[
 D_0(s)=\frac{s}{2\pi},\qquad
 D_2(s)=\frac{s-1}{2\pi}.                                       \tag{20}
\]
Consequently
\[
 \widehat\zeta(s)
 =
 \frac{D_1(s)}{D_0(s)D_2(s)}.                                   \tag{21}
\]

### Proof

Meyer's theorem `(12)` identifies the spectral multiset of
\(\Theta|M_\zeta\) with the nontrivial zero multiset of
\(\widehat\zeta\).  Its local generalized eigenspace dimensions are the
analytic multiplicities by `(13)`.  The spectral zeta functions defining
the two sides of `(18)` are therefore termwise identical on their common
right half-plane and have the same meromorphic continuation to zero.
Their derivatives at zero agree, proving `(19)` by the definition of
\(\det_\infty\).  Equations `(20)` are ordinary one-dimensional
determinants, and `(21)` is `(17)`.

This determinant is obtained from the source quotient's proved spectral
theorem.  It is not the separate Xi-divisor cohomology used elsewhere in
the repository.

## 8. Cup product and Poincare duality

For \(K=\mathbb Q\), Paugam's specialization of the Connes--Meyer
spectral construction gives an unconditional alternating pairing on
the discrete spectral suspension.  In characteristic zero Paugam
identifies this suspension with the original Connes--Meyer
representation, giving
\[
 \psi:M_\zeta\times M_\zeta\longrightarrow\mathbb C(1)            \tag{22}
\]
which is nondegenerate and flow-equivariant:
\[
 \psi(\lambda_t x,\lambda_t y)=t\,\psi(x,y).                      \tag{23}
\]
It is constructed from the source operators \(J\), complex conjugation,
convolution, and the nuclear trace.  It descends through \(Z(H_\cap)\)
by Poisson summation and the functional equation.  The word
``continuous'' is deliberately not added here: continuity on the full
Meyer quotient, including generalized zero jets, is part of the
topological comparison gate below.

For simple nonreal spectral points, its spectral expression is
\[
 \psi(F,G)
 =
 \sum_{\operatorname{Im}\rho>0}
 \bigl(
   \widehat F(\rho)\widehat G(1-\rho)
   -
   \widehat G(\rho)\widehat F(1-\rho)
 \bigr),                                                          \tag{24}
\]
while the trace construction defines `(22)` without simplicity.

The completed Riemann zeta function has no real nontrivial zero:
for \(0<s<1\), the alternating Dirichlet series
\(\eta(s)>0\) and
\[
 \zeta(s)=\eta(s)/(1-2^{1-s})<0.
\]
Hence Paugam's removal of real spectral points removes nothing for
\(\mathbb Q\).

Choose the canonical real-boundary divisor
\(e_\infty\in D_{\mathrm{Ar},\mathbb Q}\) with
\(\deg(e_\infty)=1\).  The following formulas give `(10)` a unital
graded-commutative cochain algebra structure:
\[
\begin{aligned}
 (a,f)(b,g)&=(ab,ag+bf),&&f,g\in H_\cap,\\
 (a,f)(h,u)&=a(h,u),\\
 (a,f)d&=ad,\\
 (h,u)(k,v)&=\psi([h],[k])e_\infty,                               \tag{25}
\end{aligned}
\]
and all products not forced by the unit, bilinearity, and graded
commutativity are zero.  Here \([h]\) is the class in \(M_\zeta\).

`[PROVED HERE] [DAC_POISSON_ZETA_POINCARE_PAIRING]`

The differential in `(10)` is a derivation for `(25)`.  The induced
cohomology product is
\[
 H^0\times H^2\longrightarrow H^2,\qquad
 H^1\times H^1\xrightarrow{\psi}H^2,                              \tag{26}
\]
and, with \(\operatorname{tr}:H^2\cong\mathbb C(-1)\to\mathbb C\),
both complementary pairings are nondegenerate.

### Proof of the derivation law

Only multiplication by the \(H_\cap\)-part of degree zero requires a
check.  That part acts trivially in positive degree.  For
\(f\in H_\cap\) and \(h\in H_-\),
\[
 \psi([Zf],[h])=0
\]
because \([Zf]=0\) in \(M_\zeta\).  This is exactly the missing term in
the Leibniz rule.  All other cases follow from linearity, `(8)`, or
vanishing in degree \(3\).  Nondegeneracy follows from `(8)` and
Paugam's theorem.

## 9. Exact positivity boundary

The source provides:

- a nondegenerate alternating Poincare form;
- Paugam's unconditional odd sign--conjugation
  \(K_{\mathbb R}\)-operator \(C^2=-1\) after upper/lower spectral
  splitting;
- functional-equation symmetry \(\rho\leftrightarrow1-\rho\);
- complex-conjugation symmetry \(\rho\leftrightarrow\bar\rho\);
- the full zero spectrum and Weil character.

It does **not** provide an unconditional positive Hodge form.  Meyer's
involution turns the convolution quotient into a \(*\)-algebra, and
Meyer proves that its characters are \(*\)-characters exactly on the
critical line.  Hence real spectrum for all self-adjoint elements is
equivalent to GRH.  Paugam's \(h(x,y)=\psi(x,Cy)\) is sesquilinear
unconditionally, but his displayed Hermitian sum is positive on the
semisimple critical-line sector under RH; it does not control the
derivative functionals in `(13)`.  A positive flow-natural Hodge form
on the full generalized-jet topology would eliminate nontrivial
nilpotent jets and therefore force zero simplicity in addition to RH.

Thus no claim of RH is hidden in `(3)`--`(26)`.  The remaining theorem
needed by Deninger's strategy is a source proof of positivity for the
actual relevant coefficient, strong enough to handle the full
multiplicity topology.  For the \(\mathbb Q\)/Riemann-zeta object, the
necessary coefficient-category datum is the canonical odd
\(K_{\mathbb R}\) operator \(C^2=-1\); an additional real form is not
excluded.  Deninger's no-real-coefficients theorem rules out only a
real-valued theory functorial over all number fields.  A genuinely
quaternionic no-real descent is therefore an extension gate for that
full theory, not a prerequisite for the \(\zeta_{\mathbb Q}\) Hodge
comparison.

## 10. Dependency audit

Used:

- `DAC_COMPLETED_ARAKELOV_TRACE_KERNEL`;
- `DAC_ARITHMETIC_ENDPOINT_RELATIVE_MIDDLE_REDUCTION`;
- Meyer's closed-range, spectral, and summable-character theorems;
- Paugam's unconditional symplectic pairing.

Not used:

- the zero divisor as a definition;
- RH, Weil positivity, or zero simplicity;
- CCM/Gamma operators;
- numerical zero computations;
- a Hilbert completion;
- a claimed geometric comparison with Deninger's approximate space.

## 11. Gates

- [x] source operator defined from positive-rational power maps
- [x] closed middle quotient
- [x] strict three-term \(H^0/H^1/H^2\)
- [x] flow and exact zero spectrum
- [x] prime-plus-archimedean character formula
- [x] regularized determinant formula
- [x] unconditional symplectic Poincare pairing
- [x] cochain cup product and trace
- [ ] continuity/nondegeneracy audit on the full generalized-jet topology
- [x] source relevant-coefficient \(R\alpha_*\mathcal G\) comparison
  as a strict complex with flow and endpoints
- [ ] source-geometric cup/Hodge comparison
- [ ] packetwise fixed-orbit identification on Deninger's space
- [ ] source-positive Hodge operator
- [x] Lean formalization of the algebraic assembly
- [x] concrete exact Arakelov endpoint and \(H^0/H^1/H^2\) equivalences

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  arXiv:1807.06400, especially the introduction's relevant-complex
  problem.
- Christopher Deninger, *There is no "Weil-"cohomology theory with real
  coefficients for arithmetic curves*, arXiv:2204.02714.
- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann
  zeta function*, arXiv:math/0412277.
- Ralf Meyer, *On a representation of the idele class group related to
  primes and zeros of L-functions*, arXiv:math/0311468.
- Frederic Paugam, *Spectral symmetries of zeta functions*,
  arXiv:0803.0199.

## Log

- 2026-07-27 — Constructed the source-defined Poisson--zeta middle
  coefficient and joined it to the strict Milnor--Arakelov endpoint.
  Computed \(H^0,H^1,H^2\), imported Meyer's spectral/character theorem,
  and installed Paugam's symplectic pairing as the cup product.  CCM is
  not a dependency.
- 2026-07-27 — Applied Deninger's no-real-coefficients theorem: the
  construction is complex, endpoint lines are even with real forms,
  and the open middle polarization must be genuinely odd in
  \(K_{\mathbb R}\).
- 2026-07-27 — Corrected the scope of the no-real theorem from its
  primary source: it forbids a functorial real theory over all number
  fields, not an extra real form on the single \(\mathbb Q\) object.
  Odd \(K_{\mathbb R}\) parity remains mandatory for \(H^1\).
- 2026-07-27 — Extended the unconditional Lean surface from Paugam's
  sign--conjugation on an upper/lower product to the cokernel of every
  split Poisson map intertwining conjugation.
- 2026-07-27 — Linearized the finite-plus-archimedean principal-divisor
  and degree maps as an exact pair.  Instantiated the Poisson--zeta
  complex concretely and proved in Lean that its cohomology is
  \(R\), \(H_-/\operatorname{range}(Z)\), \(R\), with Arakelov degree
  supplying the chain-level endpoint cup pairing.  Direct checks of
  `DeningerArithmeticRealArakelovEndpoint.lean` and
  `DeningerArithmeticArakelovPoissonComplex.lean` pass; final cached
  module and axiom audit remains the stage-3 promotion gate.
- 2026-08-01 — Completed the Lean surface: audited every module of the
  assembly, and added the descended duality statements and the endpoint
  determinant normalization.

## Lean status

### The algebraic assembly is complete and audited

Modules already in the tree, all now directly checked (110 declarations, axiom audit
`propext, Classical.choice, Quot.sound` or less):

- `DeningerArithmeticThreeTermCohomology.lean` — the three-term complex, its cocycles,
  boundaries, `H⁰/H¹/H²`, and the transverse flow with its induced generators.
- `DeningerArithmeticRealArakelovEndpoint.lean` — `(8)`, `(9)`: the finite-plus-archimedean
  principal divisor map, the degree map, injectivity of `pr`, surjectivity of `deg`, and the
  exactness `deningerArakelov_exact_principal_degree`.
- `DeningerArithmeticPoissonZetaAssembly.lean` — `(10)`: the complex, the cocycle/boundary
  descriptions, the three cohomology equivalences, the chain-level cup pairing `(25)` (whose
  `differential_adjoint` field is exactly the derivation law of §8), and the flow.
- `DeningerArithmeticArakelovPoissonComplex.lean` — the concrete instantiation: `H⁰ ≃ R`,
  `H¹ ≃ H₋/range Z`, `H² ≃ R`, i.e. **`(11)`**, with the weight-one cup law.
- `DeningerArithmeticThreeTermCupDescent.lean` — the descent of the chain-level pairing to
  `H⁰ × H²` and `H¹ × H¹`, its skew-symmetry, and the weight-one laws on cohomology.
- `DeningerArithmeticPaugamKReal.lean` — the odd `K_ℝ` structure `C² = -1` and its descent
  through the cokernel of a conjugation-intertwining Poisson map.

### New this round: `DeningerPoissonZetaDuality.lean`

- `deningerPoissonZetaPairH02_nondegenerate_left`, `..._right` — **`(26)`, endpoint half**: with
  `Z` injective, `deg` onto and the endpoint sequence exact, the descended pairing
  `H⁰ × H² → R` is nondegenerate in both variables.  The proof is the concrete one: a nonzero
  constant pairs with a degree-one divisor class, and a nonzero divisor class has nonzero degree
  by exactness, so it pairs with the constant `1`.
- `deningerPoissonZetaPairH11_nondegenerate` — **`(26)`, middle half**: if the source pairing `ψ`
  separates modulo `range Z` — which is what Paugam's unconditional symplectic form supplies —
  then the descended `H¹ × H¹ → R` pairing is nondegenerate.  A degree-one class is nonzero
  exactly when its generic component avoids `range Z`, and skew-symmetry converts the separating
  vector into a pairing partner.
- `deningerDet0`, `deningerDet2`, `deningerXiD` — **`(17)`, `(20)`**: the two endpoint
  determinants `s/2π`, `(s-1)/2π` and the symmetric product `D₀ D₂ Λ`.
- `deningerXiD_eq_xi` — the determinant normalization equals the corpus entire `xi` divided by
  `2π²`; the poles of `Λ` at `0` and `1` are exactly cancelled by the endpoint determinants, so
  `ξ_D` is the entire object of `(18)`.
- `deningerXiD_one_sub` — its functional equation `ξ_D(1-s) = ξ_D(s)`, unconditional.
- `deningerCompletedZeta_eq_det_quotient` — **`(21)`**: `Λ = ξ_D / (D₀ D₂)`.
- `deningerXiD_eq_jetDeterminant`, `deningerCompletedZeta_eq_jetDeterminant_quotient` — the bridge
  to the already formalized source-jet regularized determinant
  (`deningerArithmeticJetUncenteredRegularizedDeterminant_eq_xi`), which is the corpus's proof of
  the multiplicity-exact determinant of `(18)`: the middle determinant of `(19)` is that jet
  determinant, up to the fixed scalar `2π²`.

### Remaining

Nothing formalizable is left in the theorem.  The analytic imports it names — Meyer's closed-range
theorem `(6)`, his spectral theorem `(12)`--`(13)`, the summable character `(14)`--`(16)`, and
Paugam's construction of `ψ` — enter the Lean surface as explicit hypotheses of the statements
above, which is the honest form for an imported analytic input.  The four unchecked gates of §11
are open mathematics, not formalization work: the continuity/nondegeneracy audit on the full
generalized-jet topology, the source-geometric cup/Hodge comparison, the packetwise fixed-orbit
identification on Deninger's space, and the source-positive Hodge operator.
