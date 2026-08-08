# Multiple-Gamma three-face cofinal wall calibration

- **ID:** `ltg-multiple-gamma-three-face-cofinal-wall-calibration`
- **Stage:** 2 — fully proved on paper
- **Status:** `[PAPER-PROVED] [NON-RH THREE-FACE CALIBRATION] [FORMAL PARENTS READ-ONLY]`
  `[NO LEAN WRITTEN OR BUILT]`
- **Purpose:** exhibit one hypertranscendental source deformation whose differential phase,
  integral clock-relation lattice, and closed-range topology jump at the same cofinal wall while
  reflection and all finite coordinate tests remain unchanged.

## 1. Source family

For every integer `m>=1`, set

\[
 \tau_0=i,
 \qquad
 \tau_1^{(m)}=2i+\frac\pi m,
\]

and at the boundary set

\[
 \tau_0^{(\infty)}=i,
 \qquad
 \tau_1^{(\infty)}=2i.
\]

All periods lie in the upper half-plane. Let

\[
 G_m(z)=G_{\{0,1\}}(z;\tau_0,\tau_1^{(m)}),
 \qquad
 G_\infty(z)=G_{\{0,1\}}(z;i,2i)
\tag{1}
\]

be the Nishizawa two-period multiple elliptic Gamma functions.

Define the augmented integer period groups and relation lattices

\[
 \Lambda_m=\mathbb Z+\mathbb Zi+
 \mathbb Z\left(2i+\frac\pi m\right)\subset\mathbb C,
\tag{2}
\]

\[
 L_m=\left\{(a,b,c)\in\mathbb Z^3:
 a+bi+c\left(2i+\frac\pi m\right)=0\right\}.
\tag{3}
\]

For any integer period group `Lambda subset C`, put

\[
 (I_\Lambda x)(\lambda)
 =\frac{\lambda}{1+|\lambda|}x(\lambda),
 \qquad
 I_\Lambda:\ell^\infty(\Lambda^\times)
 \longrightarrow\ell^\infty(\Lambda^\times).
\tag{4}
\]

## 2. Three-face wall theorem

### Theorem 2.1

The following hold.

1. **Differential/jet face.** For every finite `m`, both `G_m` and `G_m'/G_m` are
   hypertranscendental over `C(z)`. At the boundary, both `G_infinity` and its logarithmic
   derivative are differentially algebraic. The transverse DA depth and period excess satisfy

   \[
    d_{\rm DA}(G_m)=e(\Lambda_m)=1,
    \qquad
    d_{\rm DA}(G_\infty)=e(\Lambda_\infty)=0.
   \tag{5}
   \]

2. **Integral clock/Betti face.** For finite `m`,

   \[
    L_m=0.
   \tag{6}
   \]

   At the boundary,

   \[
    L_\infty=\mathbb Z(0,-2,1),
    \qquad \tau_1^{(\infty)}=2\tau_0.
   \tag{7}
   \]

   In multiplicative nome coordinates the boundary gains `q_infinity=p^2`, while no finite
   packet has that relation.

3. **Topological/admission face.** Every finite `Lambda_m` is nondiscrete. Thus `I_(Lambda_m)` is
   injective with nonclosed, nonsurjective range. At the boundary,

   \[
    \Lambda_\infty=\mathbb Z+\mathbb Zi
   \tag{8}
   \]

   is discrete, and `I_(Lambda_infinity)` is boundedly invertible, surjective, and has closed
   range.

4. **Finite-shadow blindness.** Every restriction of every `I_(Lambda_m)` to finitely many
   nonzero coordinates is bijective, including at the boundary.

5. **Reflection face.** The even two-period product satisfies

   \[
    G_m(\tau_0+\tau_1^{(m)}-z)=G_m(z)^{-1}
   \tag{9}
   \]

   on its regular locus, both for finite `m` and at the boundary.

Hence one literal source deformation synchronizes a differential phase transition, birth of an
integral clock relation, and a closed-range topological transition. Reflection survives and no
finite coordinate restriction detects the cofinal wall.

## 3. Proof

For finite `m`, suppose

\[
 a+bi+c\left(2i+\frac\pi m\right)=0,
 \qquad a,b,c\in\mathbb Q.
\]

The real part is `a+c pi/m=0`. Irrationality of `pi` forces `a=c=0`; the imaginary part then gives
`b=0`. Therefore

\[
 \operatorname{rank}_{\mathbb Q}
 \langle1,i,2i+\pi/m\rangle=3.
\tag{10}
\]

At the boundary the rational span is `span_Q(1,i)` and has rank `2`. The all-parameter multiple-
Gamma dichotomy gives hypertranscendence at augmented rank at least `3` and differential
algebraicity at rank `2`. The established transverse-depth/period-excess theorem gives `(5)`.

The same calculation over `Z` proves `(6)`. At the boundary,

\[
 a+(b+2c)i=0
\]

iff `a=0` and `b=-2c`, proving `(7)`.

For finite `m`,

\[
 \Lambda_m=left(\mathbb Z+\frac\pi m\mathbb Z\right)+i\mathbb Z.
\tag{11}
\]

Dirichlet approximation gives nonzero elements of the real subgroup tending to zero, so
`Lambda_m` is nondiscrete. At the boundary `(8)` is a lattice. Every diagonal weight in `(4)` is
nonzero, so `I_Lambda` is injective and every finite restriction is bijective. If `Lambda` is
discrete, its nonzero elements have a uniform positive lower norm bound; inverse weights are then
uniformly bounded, giving bounded invertibility.

If `Lambda` is nondiscrete, choose nonzero `lambda_j->0` and coordinate unit vectors `u_j`. Then

\[
 \|u_j\|=1,
 \qquad
 \|I_\Lambda u_j\|
 =\frac{|\lambda_j|}{1+|\lambda_j|}\longrightarrow0.
\]

Closed injective range would give a bounded inverse onto the range, contradiction. This proves
Items 3--4. Item 5 is the established parity-inversion theorem for the even two-period hierarchy.
∎

## 4. Why this tests LTG rather than one route

The three changing faces are mathematically different:

\[
 \text{differential-algebraic phase}
 \quad+\quad
 \text{integral clock relation}
 \quad+\quad
 \text{closed-range topology}.
\tag{12}
\]

They share one explicit source wall: rational rank drops from `3` to `2`. This proves a non-RH
wall-synchronization theorem and the cofinal finite-shadow blindness predicted by LTG. Any claimed
lawspace realization placing these three jumps over different source loci is falsified.

It does **not** construct a twistor stack, nonzero Kodaira--Spencer class, exactification lift
stack, sourced moment map, Harder--Narasimhan filtration, harmonic metric, or natural cost.

## 5. Constitutive underdetermination countermodel

For the same source group `Lambda`, replace `(4)` by

\[
 (I_{\Lambda,f}x)(\lambda)=f(|\lambda|)x(\lambda).
\tag{13}
\]

The canonical choice `f(t)=t/(1+t)` has the wall above, while `f=1` is boundedly invertible for
the identical period group. Differential rank, integral relation lattice, translation characters,
and reflection are unchanged.

Therefore arithmetic/jet plus clock/Betti data do not determine topology, metric, cost, or harmonic
frame. A dynamical LTG must derive the incidence weight or equivalent polarization from a typed
constitutive law. Appending it by hand is not unification.

## 6. Corpus and formal support

This paper proof imports established results from:

- `pipeline/3-formalized/all-parameter-multiple-elliptic-gamma-dichotomy.md`;
- `pipeline/3-formalized/new_scientific_knowledge/gamma/multiple-gamma-period-excess-closure-phase-transition.md`;
- `pipeline/3-formalized/new_scientific_knowledge/gamma/multiple-elliptic-gamma-relative-log-characteristic-arrangement.md`;
- `pipeline/3-formalized/multiple-elliptic-gamma-parity-inversion.md`;
- `pipeline/4-publication-ready/multiple-elliptic-gamma-rational-rank-dichotomy/main.tex`.

These files and their Lean corpus were read only. No Lean code was written or built.

## 7. Lean boundary

Do not write Lean. The general rank dichotomy, period-excess/closure transition, and reflection
parents are already formalized. The explicit path `2i+pi/m -> 2i` can be formalized later only if
requested; its paper proof above is dependency-closed.

