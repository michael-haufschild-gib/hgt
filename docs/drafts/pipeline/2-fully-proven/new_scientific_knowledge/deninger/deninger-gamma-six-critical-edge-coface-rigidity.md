# Gamma-six critical-edge Köthe and local-coface rigidity

- **Stage:** 2-fully-proven
- **Route:** L — Deninger/Green/Hodge source descent
- **Status:** [PAPER-PROVED] [NOVELTY AUDITED, PRIORITY UNVERIFIED] [NOT RH]
- **Date:** 2026-08-11
- **Exact advance:** the complete Gamma-six source has sharp tensor-square decay exponent one;
  its two evaluated normal orientations return to the corresponding critical-edge nuclear Köthe
  domain simultaneously exactly on the critical line. The natural adjacent-grade coface has
  lower endpoint charge \(K_6/6\), every fixed finite grade-local annihilator is either zero or a
  divisor-dependent receiver, and Euler depletion cannot improve Poisson admission. Hence the
  remaining Route-L theorem is precisely source-derived continuity of the completed Green
  comparison into both critical-edge orientation domains, not construction of another
  coefficient carrier or local recurrence.

## 1. Setup

Let \(\mathcal H\) be the Hilbert source of the complete Möbius transport, let \(U_t\) be its
unitary dilation group, and let \(0\ne\Theta\in\mathcal H\). The corrected Gamma-six tail is

\[
 H_m=\sum_{n\ge6}\mu(n)n^{-m/2}U_{-m\log n}\Theta,
 \qquad m\ge3.
\tag{1}
\]

Write \(u=[6]\) in the complex group algebra of
\(\mathbb Q_{>0}^{\times}\). The tensor-square normal orientations are

\[
 \Gamma_m^+=6^{-m}u^m,
 \qquad
 \Gamma_m^-=-6^{-m}u^{-m}.
\tag{2}
\]

For the real horizontal character
\(\chi_\delta([x])=x^\delta\), put

\[
 r_+(\delta)=6^{-1+\delta},\qquad
 r_-(\delta)=6^{-1-\delta}.
\tag{3}
\]

Then evaluation of (2) is

\[
 V_6(\delta)_m=(r_+(\delta)^m,-r_-(\delta)^m),
\tag{4}
\]

and its oriented codiagonal is

\[
 w_m(\delta)=r_+(\delta)^m-r_-(\delta)^m
 =6^{-m}(6^{m\delta}-6^{-m\delta}).
\tag{5}
\]

For a nontrivial Xi zero \(\rho\), the relevant parameter is
\(\delta=2\operatorname {Re}\rho-1\in(-1,1)\).

## 2. The tensor-square exponent one is forced by the first surviving Möbius atom

### Theorem 2.1 — sharp Gamma-six source decay

\[
 \boxed{
 \frac{\|H_m\|}{6^{-m/2}\|\Theta\|}\longrightarrow1.}
\tag{6}
\]

Consequently, in the Hilbert tensor square,

\[
 \boxed{
 \frac{\|H_m\otimes H_m\|}{6^{-m}\|\Theta\|^2}\longrightarrow1.}
\tag{7}
\]

### Proof

Since \(\mu(6)=1\), split (1) into its \(n=6\) term and the remaining tail. Unitarity gives

\[
 \left\|6^{-m/2}U_{-m\log6}\Theta\right\|
 =6^{-m/2}\|\Theta\|.
\]

With \(\alpha=m/2>1\), the triangle inequality gives

\[
 \left|
 \frac{\|H_m\|}{6^{-\alpha}\|\Theta\|}-1
 \right|
 \le 6^\alpha\sum_{n\ge7}n^{-\alpha}.
\tag{8}
\]

The integral test yields

\[
 \sum_{n\ge7}n^{-\alpha}
 \le7^{-\alpha}+\frac{7^{1-\alpha}}{\alpha-1},
\]

so the right side of (8) is bounded by

\[
 \left(\frac67\right)^\alpha
 \left(1+\frac7{\alpha-1}\right)\longrightarrow0.
\]

This proves (6). Equation (7) follows from
\(\|x\otimes x\|=\|x\|^2\). ∎

The exponent one in (7) is therefore not a chosen damping parameter. It is forced by the first
nonzero atom of the literal corrected Möbius source. Any topology whose boundary is placed at
the tensor-square rate \(6^{-m}\) is source-normalized, whereas moving that edge would change the
physical source.

## 3. Critical-edge self-admission

Define the two-slot critical-edge Köthe space

\[
 \mathcal K_6^{\partial}=
 \left\{c=(c_m^+,c_m^-)_{m\ge1}:
 q_a(c)=\sum_{m\ge1}6^{am}
   (|c_m^+|+|c_m^-|)<\infty
 \text{ for every }0<a<1\right\}.
\tag{9}
\]

Write \(\mathcal K_6^{\partial,+}\) and
\(\mathcal K_6^{\partial,-}\) for the two one-slot factors, each equipped with the seminorms
\(q_a(c)=\sum_{m\ge1}6^{am}|c_m|\).

For \(0<a<b<1\), the weight quotient is \(6^{-(b-a)m}\), whose sum is finite. Thus
\(\mathcal K_6^{\partial}\) is a nuclear Fréchet Köthe space.

### Theorem 3.1 — two one-sided walls and their exact intersection

The two evaluated orientations satisfy

\[
 \begin{aligned}
 (r_+(\delta)^m)_{m\ge1}
   &\in\mathcal K_6^{\partial,+}
       &&\Longleftrightarrow\quad\delta\le0,\\
 (r_-(\delta)^m)_{m\ge1}
   &\in\mathcal K_6^{\partial,-}
       &&\Longleftrightarrow\quad\delta\ge0.
 \end{aligned}
\tag{10}
\]

Therefore

\[
 \boxed{V_6(\delta)\in\mathcal K_6^{\partial}
        \Longleftrightarrow\delta=0.}
\tag{11}
\]

### Proof

For the forward slot,

\[
 \sum_{m\ge1}6^{am}|r_+(\delta)|^m
 =\sum_{m\ge1}6^{-m(1-\delta-a)}.
\tag{12}
\]

This converges for every \(a<1\) exactly when \(\delta\le0\). Indeed, if
\(\delta\le0\), then \(1-\delta-a>0\) for every \(a<1\). If \(\delta>0\), choose
\(a\in(\max\{0,1-\delta\},1)\); the summands in (12) do not tend to zero.

Replacing \(\delta\) by \(-\delta\) proves the reciprocal statement. Their intersection is
\(\delta=0\), proving (11). ∎

This is strictly stronger than the ambient mixed admission

\[
 V_6(\delta)\in(\ell^1\cap\ell^2)^2
 \Longleftrightarrow |\delta|<1.
\tag{13}
\]

Equation (13) admits every divisor character in the open strip. Equation (11) is the sharp
critical-edge graph-domain condition.

### Theorem 3.2 — biaxial multiplier superselection

On one slot define

\[
 (M_\delta c)_m=6^{m\delta}c_m.
\tag{14}
\]

Then \(M_\delta\) is an everywhere-defined continuous endomorphism of the forward critical-edge
space exactly when \(\delta\le0\). The reflected multiplier \(M_{-\delta}\) is an endomorphism
exactly when \(\delta\ge0\). Hence the diagonal two-orientation action

\[
                         M_\delta\oplus M_{-\delta}
\tag{15}
\]

preserves \(\mathcal K_6^{\partial}\) exactly when \(\delta=0\).

### Proof

If \(\delta\le0\), then \(q_a(M_\delta c)\le q_a(c)\) for every \(a\), so the map is continuous.
If \(\delta>0\), the source-normalized vector \(c_m=6^{-m}\) lies in every seminorm of the
critical-edge space, while \(M_\delta c=(r_+(\delta)^m)_m\) does not by Theorem 3.1. Thus the
multiplier is not even everywhere defined. Reflection gives the second statement, and
intersection gives (15). ∎

Theorem 3.2 does not prove that a Xi divisor character acts on this domain. It proves that
constructing such a simultaneous action from the arithmetic Green source would force the
critical line without any additional zero-location premise.

## 4. Exact adjacent-grade transgression

Let \(S\) be forward grade shift, \((Sf)_m=f_{m+1}\). The two
orientation-specific source cofaces are

\[
 A_+=S-\frac u6,\qquad
 A_-=S-\frac {u^{-1}}6.
\tag{16}
\]

They satisfy the unconditional source identities

\[
 A_+\Gamma^+=0,\qquad A_-\Gamma^-=0.
\tag{17}
\]

The common critical half-density coface is

\[
                             A_0=S-\frac16.
\tag{18}
\]

### Theorem 4.1 — the common coface exposes the physical endpoint charge

At the lower grade \(m=0\),

\[
 \boxed{
 (A_0\Gamma^+)_0+(A_0\Gamma^-)_0
 =\frac16(u-u^{-1}).}
\tag{19}
\]

After horizontal character evaluation, (19) is

\[
 \boxed{
 \chi_\delta\!\left(
 (A_0\Gamma^+)_0+(A_0\Gamma^-)_0
 \right)
 =\frac16(6^\delta-6^{-\delta})
 =\frac16K_6(\delta).}
\tag{20}
\]

### Proof

From (2),

\[
 (A_0\Gamma^+)_0=\frac16(u-1),\qquad
 (A_0\Gamma^-)_0=\frac16(1-u^{-1}).
\]

Adding gives (19), and character evaluation gives (20). ∎

Thus the natural common adjacent-grade coface is not the missing annihilator. It is an exact
pre-specialization realization of the already fixed physical anomaly. Using \(A_+\) and \(A_-\)
as target cofaces instead would make (17) flat for every character and erase the detector. The
choice is rigid:

- orientation-specific cofaces are source-flat but character-blind;
- the common critical coface is coefficient-faithful but carries endpoint charge \(K_6/6\).

An additional arithmetic boundary is required to cancel (19); finite-grade exactness alone does
not provide it.

## 5. No fixed finite local grade differential can be the producer

Let

\[
 P(z)=\sum_{j=0}^r a_jz^j\in\mathbb C[z],
 \qquad
 P(S)=\sum_{j=0}^r a_jS^j.
\tag{21}
\]

### Theorem 5.1 — finite-convolution rigidity

If there is a nonempty open interval \(I\subset\mathbb R\) such that

\[
 P(S)w(\delta)=0
 \quad\text{for every }\delta\in I
 \text{ and every grade},
\tag{22}
\]

then \(P=0\).

For one fixed \(\delta\ne0\), the monic minimal annihilator of the two orientation slots is

\[
 (z-r_+(\delta))(z-r_-(\delta))
 =z^2-\frac{6^\delta+6^{-\delta}}6z+\frac1{36}.
\tag{23}
\]

The common first-order critical coface \(z-1/6\) annihilates both slots exactly when
\(\delta=0\).

### Proof

Equation (22) reads

\[
 P(r_+(\delta))r_+(\delta)^m
 =P(r_-(\delta))r_-(\delta)^m.
\tag{24}
\]

For \(\delta\ne0\), compare (24) at two consecutive grades. Since
\(r_+(\delta)\ne r_-(\delta)\), both coefficients in (24) must vanish. Hence \(P\) vanishes on
the continuum \(\{r_+(\delta):\delta\in I,\delta\ne0\}\), so \(P=0\).

At fixed nonzero \(\delta\), the two geometric sequences have distinct nonzero ratios, proving
the minimal polynomial (23). Finally \(r_+(\delta)=r_-(\delta)=1/6\) exactly when
\(\delta=0\), proving the last statement. ∎

The coefficient of \(z\) in (23) is

\[
 \frac13\cosh(\delta\log6).
\tag{25}
\]

Replacing it by its critical value \(1/3\) is already equivalent to \(\delta=0\). Therefore a
finite local recurrence with coefficients specialized after reading the divisor is an RH
receiver, not a source producer. A fixed recurrence valid before divisor selection is zero by
Theorem 5.1.

## 6. Euler depletion does not supply the missing opposite charge

The finite \(2\)- and \(3\)-faces in the exact place-marked Gamma-six polygon are translation
defects. It is tempting to argue that an Euler-depleted face automatically lies in the
Meyer--Poisson kernel. This is false.

Let \(\Delta_L=1-\tau_L\) on the exponentially decreasing Meyer source, \(L>0\). If
\(\Delta_Lg=0\), then \(g\) is \(L\)-periodic; exponential decay forces \(g=0\). Thus
\(\Delta_L\) is injective. Consequently

\[
 \boxed{
 \Delta_Lg\in\Delta_L Z(H_\cap)
 \Longleftrightarrow g\in Z(H_\cap).}
\tag{26}
\]

Indeed, the forward implication writes \(\Delta_Lg=\Delta_LZf\) and uses injectivity; the reverse
implication is immediate. Hence Euler depletion transports Poisson admission conservatively. It
cannot turn either marked finite face into a new zero boundary. Combining all place faces still
gives only the tautological polygon cancellation \(K_6-K_6=0\).

## 7. Exact remaining Route-L theorem

The preceding results separate three domain levels:

1. the actual odd pole pair has ambient mixed \(\ell^1/\ell^2\) admission for every
   \(|\delta|<1\);
2. its source-forced critical-edge Köthe self-admission holds exactly at \(\delta=0\);
3. local cofaces and Euler depletion cannot prove passage from level 1 to level 2.

The remaining positive theorem can now be stated without an unspecified topology:

> **Gamma-six critical-edge strict descent.** Construct, before divisor selection, a
> place-marked Rost--Schmid-to-Meyer chain comparison carrying the completed/cofinal Xi Green
> primitive and the pole-germ pair
>
> \[
> \left(B_6(s),-\frac{A(s)}{A(1-s)}B_6(1-s)\right)
> \]
>
> into both slots of \(\mathcal K_6^{\partial}\), with the existing coefficient-faithful
> Calderón--Witt reader and all prime/depth/multiplicity labels retained.

Once this source-derived membership is proved, Theorem 3.1 gives
\(\delta_\rho=0\) for every nontrivial Xi zero, hence RH. The membership may not be installed as
the definition of the domain: that would merely assume the conclusion. It must follow from a
strict arithmetic chain identity for the completed Green primitive.

Theorems 4.1, 5.1, and (26) show what that identity cannot be:

- not the common adjacent-grade coface by itself;
- not an orientation-specific flattening;
- not a fixed finite convolution in grade;
- not Euler depletion of the marked \(2\)- or \(3\)-face;
- not the already-zero scalar functional-equation codiagonal.

It must be nonlocal in grade or place support and must contribute an independently source-derived
opposite endpoint charge while remaining coefficient-faithful.

The required nonlocal source object has since been constructed on paper. Ordinary-integer shell
amplification of the countertransported full tensor-square tail differs by a trace-class operator
from the shell reciprocal Green operator \(G_6\), and therefore defines a nonzero class in
\(\mathcal L^{1,\infty}/\mathcal L^1\). Its Wold compression satisfies the critical coface law
modulo trace class, while its normalized Green Gibbs reader is exactly
\(6^{-1}(1-6^{-\delta})\), the physical BV boundary coefficient. What remains is the strict
place-marked comparison preserving this trace-class subobject and carrying its two reflected
principal symbols to the completed Xi Green/Calderón--Witt target. Full proof:
`deninger-gamma-six-shell-green-trace-ideal-transgression.md`.

## 8. Novelty and hostile audit

1. Annihilating polynomials of geometric sequences, Köthe nuclearity, and injectivity of a
   translation defect on decaying functions are classical. No novelty is claimed for those
   parent facts.
2. Corpus search found no prior theorem combining the literal corrected Möbius Gamma-six tail,
   its sharp leading-atom exponent, the two oriented Kummer normals, the critical-edge Köthe
   intersection (11), and the exact endpoint transgression (19).
3. Targeted literature search found generic quasi-exponential difference operators and general
   rational-Witt/K-theoretic sources, but no collision with this Gamma-six/Green/Hodge
   conjunction. This is a collision audit, not a priority claim.
4. No Xi-zero location, RH predicate, positivity equivalent to RH, or numerical experiment enters
   Theorems 2.1--6.
5. Equation (11) is not counted as RH. The unproved step is the arithmetic theorem placing the
   actual completed Green image in that strict domain.
6. The critical edge is not fitted to make (11) true: Theorem 2.1 derives it from the first
   surviving Möbius atom \(n=6\).
7. The local-coface computation is coefficient-faithful: it produces \(K_6/6\) rather than
   declaring it zero.
8. The positive survivor is a precise strict-domain target plus a proof that every finite/local
   or depletion-only construction misses it.

## 9. Frontier ledger

- [x] prove sharp Gamma-six Hilbert and tensor-square decay exponents
- [x] derive the source-forced critical-edge nuclear Köthe domain
- [x] classify forward, reciprocal, and simultaneous self-admission
- [x] prove exact adjacent-grade endpoint charge \(K_6/6\)
- [x] classify all fixed finite grade-local annihilators
- [x] prove Euler depletion is admission-conservative
- [ ] construct source-derived strict Green landing in both critical-edge slots
- [ ] identify that landing with the existing Rost--Schmid/Meyer differential
- [ ] prove fixed Burnol/Deninger reader cyclic on the transported boundary
