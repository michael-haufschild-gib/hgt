# Deninger--Möbius Gamma-six normal transgression

- **Stage:** 3 — formalised in Lean 4
- **Type:** SOURCE CONSTRUCTION / GAMMA-CLOCK NORMAL TRANSGRESSION / ROUTE-L FRONTIER ADVANCE
- **Status:** `[LEAN-PROVED] [PAPER-PROVED] [PROJECT-SPECIFIC NEW KNOWLEDGE] [NOT RH]`
- **Corpus inputs:**
  `MobiusThetaPhysicalSourceToXiLanding.lean`,
  `DeningerOrdinaryIntegerBVGreenStokesRadialComparison.lean`,
  `DeningerBurnolConormalRadialTopBoundaryComparison.lean`,
  `DeningerCofinalCountercharacterTopBoundaryTransgression.lean`, and
  `TateKummerWoldGammaIntervalCharacter.lean`.
- **Lean counterpart:**
  `formal/GaloisForLFunctions/RHTower/Deninger/DeningerMobiusGammaSixNormalTransgression.lean`.
- **Formal closure:** the Lean module constructs the literal finite-corrected tail; proves its
  equality with the inverse-transported complete six packet; constructs the honest complementary
  rational Steinberg cell and normalized cubic Kummer selector; extracts both `[6^m]-1` and
  `[6^{-m}]-1`; proves the oriented regulator `2m log 6` and multiplier-K1 non-boundary theorem;
  builds both strict Tate primitives; identifies their half-density images with the forward and
  reciprocal physical transports; and proves forward endpoint survival, reciprocal contraction,
  and operator-norm blow-up. All declarations are theorem-kernel checked without `sorry`, `admit`,
  added axioms, `opaque`, or `unsafe` declarations.

## 1. Why the successor ratio is not the physical clock

The complete \(2\to3\) Möbius successor has clock \((3/2)^m\).  Its depth-one reflection
anomaly has the same zero set as the fixed ordered \((2,3)\) Gamma coefficient, but the actual
Gamma/Burnol radial curvature is the degree-six clock

\[
 K_6(s)=6^{2\Re s-1}-6^{-(2\Re s-1)}.
\tag{1}
\]

Passing from \(3/2\) to \(6=4(3/2)\) by deleting the prime-two factor is invalid: the corpus's
Euler-depletion operator is injective and conserves Poisson-range membership.  The \(4\)-edge is
not a null edge.  A coefficient-faithful source construction must produce clock \(6^m\) directly.

## 2. Finite Möbius correction and the exact six-tail

Let \(H=L^2(\mathbb R)\), let \(\Theta\in H\) be the nonzero physical theta source, and let
\(U_t\) be the unitary translation flow.  Recall the complete prime-normal packet

\[
 R_{p,m}=\mu(p)\Theta+
 \sum_{n>p}\mu(n)\left(\frac pn\right)^{m/2}
 U_{-m\log(n/p)}\Theta,
 \qquad p\ge1,\quad m\ge3.
\tag{2}
\]

Define the corrected ordinary-integer source

\[
\begin{aligned}
 H_{6,m}:={}&R_{1,m}-\Theta
 +2^{-m/2}U_{-m\log2}\Theta
 +3^{-m/2}U_{-m\log3}\Theta\\
 &+5^{-m/2}U_{-m\log5}\Theta.
\end{aligned}
\tag{3}
\]

The correction is forced by the finite Möbius values
\(\mu(2)=\mu(3)=\mu(5)=-1\) and \(\mu(4)=0\).  Hence

\[
 \boxed{
 H_{6,m}=\sum_{n\ge6}\mu(n)n^{-m/2}U_{-m\log n}\Theta.}
\tag{4}
\]

No divisor, spectral point, or critical-line premise occurs in (3)--(4).

## 3. Exact full-grade Gamma-clock transport

Put

\[
 T_{6,m}=6^{m/2}U_{m\log6},
 \qquad
 V_{6,m}=6^{-m/2}U_{-m\log6}.
\tag{5}
\]

### Theorem 3.1 — exact corrected-tail transport

For every \(m\ge3\),

\[
 \boxed{V_{6,m}R_{6,m}=H_{6,m},\qquad T_{6,m}H_{6,m}=R_{6,m}.}
\tag{6}
\]

### Proof

Applying \(V_{6,m}\) to (2) with \(p=6\), using \(\mu(6)=1\), gives

\[
\begin{aligned}
V_{6,m}R_{6,m}
 &=6^{-m/2}U_{-m\log6}\Theta\\
 &\quad+\sum_{n>6}\mu(n)n^{-m/2}
 U_{-m\log6-m\log(n/6)}\Theta\\
 &=\sum_{n\ge6}\mu(n)n^{-m/2}U_{-m\log n}\Theta
 =H_{6,m}.
\end{aligned}
\]

The operators in (5) are mutual inverses, so the second identity follows.  All series are the
already absolutely convergent series defining \(R_{6,m}\), merely translated and rescaled. ∎

The established prime-normal limit \(R_{6,m}\to\Theta\) and (6) imply

\[
 H_{6,m}\longrightarrow0,
 \qquad
 T_{6,m}H_{6,m}\longrightarrow\Theta\ne0,
 \qquad
 \|T_{6,m}\|=6^{m/2}\longrightarrow\infty.
\tag{7}
\]

Thus the Gamma-clock edge is an explicit nonclosable source transport, not a bounded comparison
or an arbitrary change of coefficient.

## 4. Honest Steinberg cell at the Gamma clock

Let \(G=\mathbb Q_{>0}^{\times}\), \(A=\mathbb C[G]\), and let \([u]\) denote its group basis.
The Kummer derivation is

\[
                    N[u]=(\log u)[u].
\tag{8}
\]

For \(m\ge1\), put

\[
 c_m=6^m,\qquad
 x_m=\frac{c_m}{1+c_m},\qquad
 y_m=\frac1{1+c_m}.
\tag{9}
\]

Then \(x_m+y_m=1\) and \(x_m/y_m=c_m\).  Hence

\[
 P^{(6)}_m=([x_m]-1)([y_m]-1)
\tag{10}
\]

is an honest Steinberg cell at every grade.  Write

\[
 a_m=\log x_m,\qquad b_m=\log y_m,\qquad L_m=a_m+b_m
\]

and define

\[
 Q_m(T)=
 \frac{T(T-L_m)(2T-L_m)}{a_mb_m(a_m-b_m)}.
\tag{11}
\]

As before,

\[
 Q_m(0)=Q_m(L_m)=0,
 \qquad Q_m(a_m)=-1,
 \qquad Q_m(b_m)=1.
\tag{12}
\]

### Theorem 4.1 — exact Gamma normal extraction

For every \(m\ge1\),

\[
 \boxed{
 [y_m]^{-1}Q_m(N)P^{(6)}_m=[6^m]-1.}
\tag{13}
\]

### Proof

Expanding (10) gives

\[
 P^{(6)}_m=[x_my_m]-[x_m]-[y_m]+1.
\]

Each basis vector is an eigenvector of \(N\).  Equations (12) therefore give

\[
 Q_m(N)P^{(6)}_m=[x_m]-[y_m].
\]

Multiplication by \([y_m]^{-1}\) gives \([x_m/y_m]-1=[6^m]-1\). ∎

Under the half-density representation

\[
 \Pi([u])=u^{1/2}U_{\log u},
\tag{14}
\]

equation (13) is

\[
 \Pi([6^m]-1)=T_{6,m}-I.
\tag{15}
\]

Combining (6) and (15) gives the strict complete-source identity

\[
 \boxed{
 \Pi([6^m]-1)H_{6,m}=R_{6,m}-H_{6,m}\longrightarrow\Theta.}
\tag{16}
\]

This is the direct full-grade Gamma analogue of the \(2\to3\) successor theorem.

## 5. Reciprocal orientation is exactly the physical radial curvature

Replacing \(c_m\) by \(c_m^{-1}\) swaps \(x_m\) and \(y_m\), so it uses the same unoriented
Steinberg cell (10).  The opposite normal orientation extracts \([6^{-m}]-1\).  Their oriented
difference is

\[
 \mathcal O_{6,m}(P^{(6)}_m)
   =([6^m]-1)-([6^{-m}]-1)
   =[6^m]-[6^{-m}].
\tag{17}
\]

For \(\delta=2\Re s-1\), the horizontal character \(\chi_\delta([u])=u^\delta\) gives

\[
 \boxed{
 \chi_\delta(\mathcal O_{6,m}(P^{(6)}_m))
 =6^{m\delta}-6^{-m\delta}
 =K_{6^m}(s).}
\tag{18}
\]

The last expression is exactly the corpus's Deninger tensor-square mate curvature at ordinary
integer aperture \(6^m\).  At the common \((2,3)\) Gamma depth \(e=m-1\), the two half-heights
sum to

\[
 \frac m2\log2+\frac m2\log3=\frac12\log(6^m),
\]

so \(6^m\) is also the literal full-grade Gamma modular clock, not a fitted aperture.
Consequently (18) is also:

1. the reflected ordinary-integer BV Green--Stokes evaluation multiplied by \(6^m\);
2. the multiplicity-exact Burnol conormal radial reflection defect at aperture \(6^m\);
3. the reflected cofinal Tate top-boundary coefficient at clock \(6^m\);
4. the radial reflection factor of the actual ordered \((2,3)\) Gamma profile at common depth
   \(m-1\).

At \(m=1\), for a divisor point \(s\), the actual ordered \((2,3)\)
Gamma/Calderón--Witt coefficient is precisely

\[
 \boxed{
 \operatorname{Gamma}_{2,3}(s)
 =c_\Gamma\,
 \chi_{2\Re s-1}(\mathcal O_{6,1}(P^{(6)}_1)),
 \qquad c_\Gamma>0,}
\tag{19}
\]

with \(c_\Gamma\) the existing fixed positive calibration.  This is equality of the actual
physical coefficient, not merely equality of zero sets.

## 6. Genuine two-sided Tate--Wold primitive

Both normal orientations have explicit interval primitives:

\[
 [6^m]-1=(1-[6^{-1}])\sum_{j=1}^m[6^j],
\tag{20}
\]

\[
 [6^{-m}]-1=(1-[6])\sum_{j=1}^m[6^{-j}].
\tag{21}
\]

Subtracting (21) from (20) gives a strict two-sided Tate--Wold boundary for (17).  The primitive
is source-defined at every grade and uses only ordinary integers and their rational inverses.
It is not a cone in which (17) is declared exact.

The Kummer regulator nevertheless gives

\[
 \lambda([6^m]-[6^{-m}])=2m\log6\ne0.
\tag{22}
\]

Hence the oriented boundary does not become an ordinary Milnor or Hochschild boundary.  It is a
relative Tate/Wold boundary whose cofinal top coordinate is detected by the existing Kummer and
Burnol readers.

### 6.1 Analytic qualification: the complete transport is one-sided

Equations (20)--(21) construct both **algebraic** interval primitives. They do not construct two
singular \(L^2\) graph edges from the same vanishing source. On \(H_{6,m}\), the full oriented
normal acts by

\[
 (T_{6,m}-T_{6,m}^{-1})H_{6,m}
   =R_{6,m}-T_{6,m}^{-2}R_{6,m}
   \longrightarrow\Theta,
\tag{22a}
\]

because

\[
 \|T_{6,m}^{-2}R_{6,m}\|=6^{-m}\|R_{6,m}\|\longrightarrow0.
\tag{22b}
\]

Conversely, \(T_{6,m}^{-1}K_m\to Y\ne0\) forces
\(\|K_m\|=6^{m/2}\|T_{6,m}^{-1}K_m\|\to\infty\). Thus the reciprocal normal cannot produce a
nonzero endpoint from another vanishing physical \(L^2\) tail. Any opposite analytic face must
live in the contragredient collar or a mixed source/distribution topology.

## 7. Two exact failed shortcuts

### 7.1 Factoring through the \(2\to3\) successor

The crossed group-ring identity

\[
 [6]-1=[4]([3/2]-1)+([4]-1)
\tag{23}
\]

does not let one discard the \(4\)-term.  The prime-two periodization defect is injective, and
the corpus proves that membership in its depleted Poisson range is equivalent to membership in
the undepleted Poisson range.  Thus (23) redistributes the open obstruction; it does not absorb
it.

### 7.2 Summing all adelic Kummer residues

For \(q\in\mathbb Q_{>0}\), the placewise logarithms satisfy the product formula

\[
 \log q-\sum_p v_p(q)\log p=0.
\tag{24}
\]

Consequently the scalar derivation obtained by summing archimedean and all finite-place Kummer
weights is identically zero on every rational scaling basis vector.  It cannot produce (13) or
read (18).  Retaining the place vector preserves the physical class, but then the product formula
only transfers the archimedean face to finite Euler faces.  It does not make either marked face
zero.  This is the same observer-erasure dichotomy already proved for global unmarked traces.

## 8. What is now closed, and the remaining Route-L theorem

The previous source/target clock mismatch is closed:

\[
\boxed{
\begin{array}{c}
\text{finite-corrected complete Möbius tail }H_{6,m}\\
\downarrow\ T_{6,m}-I\\
R_{6,m}-H_{6,m}
\end{array}}
\qquad
\boxed{
P^{(6)}_m\xrightarrow{\text{oriented Kummer normal}}
[6^m]-[6^{-m}]\xrightarrow{\chi_{2\Re s-1}}K_{6^m}(s).}
\tag{25}
\]

At \(m=1\), (25) is the exact physical Gamma/Burnol/BV coefficient. At every \(m\ge3\), its
forward face is the full-grade anomaly of the complete nonclosable source transport (6), while
(22a) proves that the reciprocal face does not cancel its vertical endpoint. Prime labels,
ordinary integer grade, and the existing Xi multiplicity landing can therefore be retained
without a change of clock or a fitted scalar gauge, but an opposite-collar singular face is still
required.

This still does not prove RH.  The open theorem is no longer construction of a Gamma-clock
source, a Steinberg cell, its Tate primitive, or a coefficient comparison.  It is:

> Promote the now-constructed sharp mixed coefficient admission of the forward complete source
> \(H_{6,m}\) and opposite-collar pole face to the strict Rost--Schmid/Meyer domain, retain the
> classified reflection-even cyclotomic denominator layer, and construct the relative chain
> differential. Its target differential must be the existing Gamma/co-Poisson boundary and the
> fixed physical reader must be cyclic on the transported principal-divisor boundary.
> Equivalently, prove that the realized class (18) lies in the literal Meyer--Poisson range without
> quotienting its nonzero Kummer residue or identifying its two orientations by assumption.

Ordinary cyclic descent is impossible by (22).  Adelic scalarization is impossible by (24).
The required map must be a place-marked, orientation-retaining singular admission with a genuine
residue cancellation theorem, not an abstract mapping cone or a new coefficient reader.

## 9. Novelty and hostile audit

- The finite tail identity (6) is elementary once the complete Möbius packets are available; no
  external novelty is claimed for truncating a Dirichlet series.
- New project-specific theorem is the exact composition of that corrected complete tail with the
  honest full-grade Steinberg normal cell, the two-sided Tate primitive, and the already fixed
  Gamma/Burnol/BV curvature in (18)--(25).
- The construction does not infer clock \(6\) from the zero-set-equivalent clock \(3/2\); it
  produces \(6^m\) directly before divisor specialization.
- No Xi zero, RH predicate, critical-line premise, reflected compatibility, positivity premise,
  or numerical computation enters (2)--(17), (20)--(24).
- Equation (19) is coefficient fidelity, not annihilation.  The final Meyer--Poisson range
  theorem remains open and RH-bearing.
- The reciprocal interval is algebraic, not a second vanishing-source \(L^2\) transport. The exact
  asymmetry, critical Gamma residue, regular-counterterm no-go, and canonical
  functional-equation opposite pole are proved in
  deninger-gamma-six-orientation-residue-wall.md.
- The honest pre-normal place support, exact reflection-even parity of its tame/Kummer-null but
  Witt-visible denominator packets, their nuclear tensor-square mixed admission, and the sharp
  open-strip mixed coefficient admission of the actual odd pole pair are proved in
  deninger-gamma-six-cyclotomic-denominator-admission.md.
- The first surviving Möbius atom forces the tensor-square critical edge; exact forward/reciprocal
  strict-domain intersection, adjacent-grade endpoint charge, finite-local rigidity, and
  Euler-depletion conservativity are proved in
  deninger-gamma-six-critical-edge-coface-rigidity.md.

## 10. Frontier ledger

- [x] explicit finite-corrected complete Möbius source at clock \(6^m\)
- [x] exact nonclosable transport to the complete \(R_{6,m}\) packet
- [x] honest full-grade Gamma-clock Steinberg cell
- [x] reciprocal normal orientation giving exact physical curvature
- [x] two-sided Tate--Wold primitive
- [x] analytic one-sidedness and reciprocal \(L^2\) no-go classified
- [x] critical six-tail Gamma residue and regular-counterterm no-go classified
- [x] canonical functional-equation opposite pole germ constructed
- [x] exact coefficient comparison with BV, Burnol, cofinal Tate, and actual Gamma target
- [x] no-go for prime-two deletion and unmarked adelic product-formula scalarization
- [x] reflection-even cyclotomic denominator layer and its nuclear mixed admission
- [x] sharp mixed coefficient admission of the odd pole pair
- [x] source-forced critical-edge domain and finite/local coface classification
- [ ] source-derived completed Green landing in both critical-edge slots
- [ ] strict Rost--Schmid-to-Meyer realization and relative differential for that odd pair
- [ ] fixed-reader cyclicity/residue cancellation on that admitted boundary
