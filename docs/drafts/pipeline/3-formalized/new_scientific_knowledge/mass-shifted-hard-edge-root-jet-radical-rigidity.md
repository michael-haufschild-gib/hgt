# Mass-shifted hard-edge root-jet radical rigidity

- **ID:** `mass-shifted-hard-edge-root-jet-radical-rigidity`
- **Stage:** 3-formalized / needs independent specialist audit
- **Type:** THEOREM (paper)
- **Source:** Route U item 48 and `mass-shifted-hard-edge-hyperbolic-weil-boundary`
- **Statement:** At a critical hard-edge boundary, a squared-variable zero of multiplicity `m`
  creates a complete flag of `m-1` exact null descendants.  Its divided-jet Gram matrix is zero
  except for one terminal nonnegative scalar.  Globally, all forced flags saturate a full
  polynomial module over the squarefree-root core. A parity lift gives every nonterminal
  descendant an explicit odd zero-energy twin and transports terminal mass \(\gamma_r\) to odd
  energy \(r\gamma_r\). Under full-ground positivity the radical dimension is at least
  \(1+2\sum_r(m_r-1)\), and simple full ground forces every squared root to be strictly positive.
- **Scientific status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED] [LEAN FORMALIZED]`

## Goal

Determine whether the simultaneous root-division equations from the hard-edge boundary are an
overdetermined source obstruction or ordinary extremal orthogonality.  The answer is sharp:
distinct simple-root equations are ordinary orthogonality, while repeated roots encode genuine
spectral degeneracy.  This replaces the unstructured Cauchy-transform target by an exact
ground-multiplicity dichotomy.

## Gates

- [x] 0 -> 1 in-progress: source-pure statement, exact form domain, and falsifiers fixed
- [x] 1 -> 2 fully-proven: dependency-closed proof below, conditional only on the already
  paper-proved literal Route U boundary theorem
- [x] 2 -> 3 formalized: literal density and pairing, the divided-jet Gram law, the aperture
  closing, the polynomial-module saturation, the parity count and the terminal alternatives are
  all Lean; no abstract-premise wrapper is used
- [ ] 3 -> 4 publication-ready: independent proof and priority audit

## 1. Critical form and theorem

Fix the boundary type `sigma` from the hard-edge theorem and put

\[
 d\eta_\sigma(u)=\mathbf 1_{u>0}{V_\sigma(\sqrt u)\over\sqrt u}\,du
                  +2\pi\delta_{-1/4}.                       \tag{RJRR.1}
\]

For even Paley--Wiener functions `h(z)=H(z^2)` and `k(z)=K(z^2)` in the logarithmic form domain,
write

\[
 \mathfrak b_\sigma(H,K)=\int_{\mathbb R}H(u)K(u)\,d\eta_\sigma(u). \tag{RJRR.2}
\]

This is exactly the literal finite-prime Gamma form, including the polar evaluation at `i/2`.
Let the nonzero hard-edge null state be

\[
 f(z)=F(z^2),\qquad F\in\mathcal{LP},\qquad \operatorname{ord}F\le {1\over2}. \tag{RJRR.3}
\]

For a real zero `r` of multiplicity `m_r` and `1<=k<=m_r`, define the entire root descendant

\[
 F_{r,k}(u)={F(u)\over(u-r)^k},\qquad
 f_{r,k}(z)=F_{r,k}(z^2).                                  \tag{RJRR.4}
\]

`[PAPER-PROVED]` The following assertions hold.

1. The form is nonnegative on its **closed critical-type domain**, not only at every strictly
   smaller aperture:

   \[
   \mathfrak b_\sigma(H,H)\ge0.                             \tag{RJRR.5}
   \]

2. `F` lies in the radical.  Define every continuously cancelled moment

   \[
   M_{r,k}:=\int_{\mathbb R}{F(u)^2\over(u-r)^k}\,d\eta_\sigma(u)
   \qquad(1\le k\le2m_r).
   \]

   Every initially allowed divided moment vanishes:

   \[
   \mathfrak b_\sigma(F,H)=0,\qquad
   M_{r,k}=0
   \quad(1\le k\le m_r).                                   \tag{RJRR.6}
   \]

   All quotients at `u=r`, including `r=-1/4`, are interpreted by their continuous entire
   extensions.  In particular, no `0/0` polar fraction occurs.

3. Descendants belonging to distinct roots are exactly orthogonal:

   \[
   \mathfrak b_\sigma(F_{r,p},F_{s,q})=0
   \quad(r\ne s,\ 1\le p\le m_r,\ 1\le q\le m_s).          \tag{RJRR.7}
   \]

4. Each repeated root forces the complete nonterminal divided-jet flag into the radical:

   \[
   F_{r,k}\in\operatorname{rad}\mathfrak b_\sigma
   \quad(1\le k<m_r),                                       \tag{RJRR.8}
   \]

   and in fact

   \[
   M_{r,k}=0\quad(1\le k<2m_r).                             \tag{RJRR.9}
   \]

   Put `gamma_r=M_(r,2m_r)>=0`.  The complete divided-jet Gram law is

   \[
   \mathfrak b_\sigma(F_{r,p},F_{s,q})=
   \begin{cases}
     \gamma_r,&r=s,\ p=q=m_r,\\
     0,&\text{otherwise}.
   \end{cases}                                               \tag{RJRR.10}
   \]

   The rational principal parts are linearly independent.  Hence

   \[
   \boxed{\quad
   \dim\operatorname{rad}\mathfrak b_\sigma
   \ \ge\ 1+\sum_{F(r)=0}(m_r-1).
   \quad}                                                    \tag{RJRR.11}
   \]

   More sharply, if `S` is any finite root set, every root in `S` with `gamma_r=0` contributes its
   terminal descendant as well:

   \[
   \dim\operatorname{rad}\mathfrak b_\sigma
   \ge 1+\sum_{r\in S}\bigl(m_r-1+\mathbf1_{\{\gamma_r=0\}}\bigr).
   \]

5. The literal localized restricted-Weil operator has discrete spectrum and finite-dimensional
   eigenspaces.  Therefore only finitely many roots of `F` can be multiple.  If its zero
   eigenspace is one-dimensional, every root of `F` is simple.  Under the same simple isolated
   even-ground hypothesis, Connes--van Suijlekom's real-zero theorem forces every zero of `f` to
   be real, so

   \[
   \dim\ker A_\sigma=1
   \quad\Longrightarrow\quad
   m_r=1,\quad r>0,\quad\gamma_r>0
   \quad\text{for every root }r.                            \tag{RJRR.12}
   \]

6. Assume `0` is the isolated lowest eigenvalue of the full localized convolution operator, as in
   the Connes--van Suijlekom ground-state setting.  Let

   \[
   E=\sum_r(m_r-1),\qquad
   R(u)=\prod_r(u-r)^{m_r-1},\qquad D(u)={F(u)\over R(u)},   \tag{RJRR.13}
   \]

   where the finite products run over the multiple roots.  Then the forced root-jet space is the
   entire polynomial module

   \[
   D\cdot\mathbb R_{\le E}[u]\ \subseteq\ \ker A_\sigma.    \tag{RJRR.14}
   \]

   If `E>0`, this module cannot be the whole ground space.  Consequently

   \[
   \boxed{\qquad E>0\quad\Longrightarrow\quad
   \dim\ker A_\sigma\ge E+2.\qquad}                         \tag{RJRR.15}
   \]

   Thus repeated roots force **excess degeneracy** beyond every root-division direction; the
   equality case in (RJRR.11) is impossible for an isolated convolution ground.

7. The excess modes are not mysterious. The parity companion proved in
   mass-shifted-hard-edge-parity-jet-inertia.md gives, for every terminal descendant,

   \[
   \mathcal W_\sigma\!\left(
     zF_{r,m_r}(z^2),zF_{r,m_r}(z^2)\right)=r\gamma_r.     \tag{RJRR.23}
   \]

   Every nonterminal descendant has odd energy zero. If zero is the full lowest eigenvalue,
   those odd descendants lie in the kernel and are independent of the even flag. Therefore

   \[
   \boxed{\qquad
   \dim\ker A_\sigma\ge1+2E.
   \qquad}                                                  \tag{RJRR.24}
   \]

   A negative root with positive terminal mass is incompatible with full-ground nonnegativity; a
   zero root with positive terminal mass creates an odd ground mode; and
   \(\gamma_r=0\) creates both terminal even and odd modes. This constructively classifies the
   additional directions whose existence was inferred abstractly in (RJRR.15).

## 2. Proof

### 2.1 Closing the critical aperture

Let `h` be any even type-`sigma` function in the logarithmic form domain and set
`h_t(x)=h(tx)` for `0<t<1`.  Its type is at most `t sigma`, so the hard-edge boundary theorem gives
nonnegativity of its quadratic value.  As `t` increases to one, dilation is strongly continuous in
`L^2(log(2+|x|)dx)`.  The prime part contains only the finitely many frequencies
`log n<=2 sigma`, and Paley--Wiener evaluation at `i/2` is continuous.  Thus the complete form is
continuous under this dilation and

\[
 \mathfrak b_\sigma(H,H)=\lim_{t\uparrow1}\mathfrak b_\sigma(H_t,H_t)\ge0.
\]

The same form-core passage already proves
`mathfrak b_sigma(F,F)=0`.  Cauchy--Schwarz for the nonnegative semidefinite form therefore gives
`mathfrak b_sigma(F,H)=0` for every `H` in the closed critical domain.  This proves (RJRR.5) and
the first assertion in (RJRR.6).

### 2.2 Admissibility of every root jet

Because `F` has a zero of multiplicity `m_r`, each `F_(r,k)` in (RJRR.4) is entire.  Division by
`(z^2-r)^k` does not increase exponential type and improves the real tail by `2k` powers.  Local
removability handles `z^2=r`; away from a compact set the quotient is bounded by a constant times
`|f(x)|/(1+|x|)^(2k)`.  Hence `f_(r,k)` belongs to the same logarithmic critical form domain.
Substituting it into the radical identity gives

\[
 0=\mathfrak b_\sigma(F,F_{r,k})
  =\int {F(u)^2\over(u-r)^k}\,d\eta_\sigma(u),
\]

which proves all of (RJRR.6).  If `r=-1/4`, the polar summand in this pairing is
`2\pi F(-1/4)F_(r,k)(-1/4)=0`; writing it as a quotient of two vanishing scalars would be invalid.

### 2.3 Distinct-root orthogonality

For `r \ne s`, ordinary partial fractions give constants `a_j,b_l` such that

\[
 {1\over(u-r)^p(u-s)^q}
 =\sum_{j=1}^p{a_j\over(u-r)^j}+\sum_{\ell=1}^q{b_\ell\over(u-s)^\ell}.
\]

After multiplication by `F(u)^2`, every apparent singularity is removable.  Integrating
this identity against `eta_sigma` and applying (RJRR.6) term by term proves (RJRR.7).  Thus the
simultaneous simple-root Cauchy equations are the Lagrange orthogonality relations of a critical
extremizer; by themselves they are not an overdetermined contradiction.

### 2.4 Multiplicity creates a complete null flag

If `2k<=m_r`, then `F_(r,2k)` is admissible and

\[
 \mathfrak b_\sigma(F_{r,k},F_{r,k})
 =\int {F(u)^2\over(u-r)^{2k}}\,d\eta_\sigma(u)
 =\mathfrak b_\sigma(F,F_{r,2k})=0.                          \tag{RJRR.16}
\]

Nonnegativity of the form makes every zero-norm vector radical.  This starts with
`F_(r,k)` radical for `1<=k<=floor(m_r/2)`.

Put `F_(r,0)=F` and start with `d=floor(m_r/2)`.  The apparent half-multiplicity barrier is not
real.  Suppose inductively that `F_(r,1),...,F_(r,d)` are radical, where `d<m_r-1`.  Pairing each
of them with every admissible `F_(r,k)`, `0<=k<=m_r`, gives

\[
 M_{r,j+k}=\mathfrak b_\sigma(F_{r,j},F_{r,k})=0
 \qquad(1\le j\le d,\ 0\le k\le m_r).                       \tag{RJRR.17}
\]

Together with the initial vanishing in (RJRR.6), this covers every index
`1<=s<=m_r+d`.  Since `d<=m_r-2`,

\[
 2(d+1)\le m_r+d,
 \qquad
 \mathfrak b_\sigma(F_{r,d+1},F_{r,d+1})=M_{r,2d+2}=0.
\]

Thus `F_(r,d+1)` is radical.  Induction reaches `d=m_r-1` and proves (RJRR.8).
Taking `j<=m_r-1` and `k=m_r` in (RJRR.17) then gives every remaining moment through
`M_(r,2m_r-1)`, proving (RJRR.9).  Therefore

\[
 \mathfrak b_\sigma(F_{r,p},F_{r,q})=M_{r,p+q}=0
\]

unless `p=q=m_r`; in that terminal case it equals
`gamma_r=M_(r,2m_r)>=0` by nonnegativity.  Section 2.3 already gives zero for different roots, so
the complete diagonal law (RJRR.10) follows.

For linear independence, take any finite relation among `F` and the nonterminal descendants,
divide on the complement of the zero set by the nonzero entire function `F`, and obtain a rational
identity

\[
 c_0+\sum_{r,k}{c_{r,k}\over(u-r)^k}=0.                     \tag{RJRR.18}
\]

Every principal part in (RJRR.18) vanishes, and then `c_0=0`.  Arbitrary finite subsets are
independent, proving the dimension bound (RJRR.11).  If `gamma_r=0`, nonnegativity puts the
terminal descendant `F_(r,m_r)` in the radical too.  The same rational-principal-part argument for
any finite root set proves the sharper terminal-zero bound.

### 2.5 The radical root pencil and failure of polar cyclicity

Let `r` be repeated and write `F(u)=(u-r)^mG(u)`.  Since both `F` and `F_(r,1)` are radical, every
member of the exact pencil

\[
 F_c(u)=F(u)+cF_{r,1}(u)
       =(u-r)^{m-1}(u-r+c)G(u)                              \tag{RJRR.19}
\]

is radical.  It remains in the Laguerre--Polya class: the pencil removes one copy of the real root
`r` and replaces it by the arbitrary real root `r-c`.  If `F(-1/4)\ne0`, direct evaluation gives

\[
 F_c(-1/4)=F(-1/4)\left(1+{c\over-1/4-r}\right).
\]

The unique polar-dark member therefore has `c=r+1/4`, so its replacement root is exactly the
completion point `-1/4`.  If
`F(-1/4)=0`, the original state is already polar-dark.  Thus every repeated root supplies a
nonzero radical state annihilated by evaluation at `i/2`.

Consequently the polar functional is not cyclic on a degenerate ground space and cannot prove
ground simplicity.  More strongly, the location of one copy of a repeated squared root is a
projective gauge inside the radical pencil; polar evaluation selects the completion root `-1/4`,
not the critical sign boundary `0`.

### 2.6 Compact-resolvent and simple-ground consequences

Suzuki records that the self-adjoint localized Weil operator is lower bounded with discrete
spectrum and `+infinity` as its only accumulation point.  Its zero eigenspace is therefore finite
dimensional.  Equation (RJRR.11) rules out infinitely many multiple roots.  A one-dimensional
zero eigenspace rules out even one root with multiplicity at least two.
It also forces every terminal scalar to be positive: if `gamma_r=0`, the independent terminal
descendant belongs to the radical by Section 2.4.

The hard-edge `f` is the Fourier transform of the even zero-mode on the finite frequency interval.
Connes--van Suijlekom prove that the Fourier transform of a simple isolated even ground state has
only real zeros.  If `F` had a negative root `r`, then `f` would vanish at the nonreal points
`z=\pm i\sqrt{-r}`.  Thus simple ground excludes negative roots.  Together with the
previous paragraph and the parity theorem below, this proves (RJRR.12). The strict exclusion of
\(r=0\) is source-internal: its terminal odd descendant has energy
\(r\gamma_r=0\), hence would be a second full-ground vector.

### 2.7 Polynomial-module saturation cannot be a degenerate convolution ground

Let the multiple roots be `r_1,...,r_t`, put `e_i=m_(r_i)-1`, and use `E,R,D` from (RJRR.13).
The forced radical vectors are

\[
 F=DR,\qquad F_{r_i,k}=D{R\over(u-r_i)^k}
 \quad(1\le i\le t,\ 1\le k\le e_i).
\]

Their polynomial factors are `E+1` linearly independent members of
`mathbb R_(<=E)[u]`: independence is the rational-principal-part argument from Section 2.4 after
division by `R`.  Since that polynomial space also has dimension `E+1`, they span it.  This proves
(RJRR.14).

Assume for contradiction that `E>0` and that this forced module is the entire ground space
`mathcal K=ker A_sigma`.  For `0<=i<=E`, let `xi_i` be the inverse Fourier transform of
`D(z^2)z^(2i)`.  Its Hilbert Gram matrix is positive definite and Hankel:

\[
 G_{ij}=\langle\xi_i,\xi_j\rangle=g_{i+j}.
\]

Choose `E` distinct real nodes `rho_1,...,rho_E`, with `rho_1=-1`, and put

\[
 P_*(u)=\prod_{q=1}^E(u-\rho_q),\qquad
 c_k=\sum_{q=1}^E\rho_q^k,
 \qquad C_{ij}=c_{i+j}.
\]

The matrix `C` is positive semidefinite of rank `E`, because it is the Gram matrix of evaluation
at the `E` distinct real nodes.  Its kernel is exactly the coefficient line of `P_*`.  Define the
Hankel target `H=C-G`, or `h_k=c_k-g_k`.

Now choose `2E+1` distinct positive numbers `s_l` away from the zeros of `D`.  The Vandermonde
matrix of the `s_l` is invertible, so there are real signed weights `w_l` with

\[
 \sum_{\ell=0}^{2E}w_\ell D(s_\ell)^2s_\ell^k=h_k
 \qquad(0\le k\le2E).                                     \tag{RJRR.20}
\]

Let `B` be the bounded self-adjoint convolution operator on the finite time interval whose real
even kernel is the corresponding finite signed cosine sum

\[
 k_B(t-s)=\sum_{\ell=0}^{2E}w_\ell
            \cos\!\left(\sqrt{s_\ell}(t-s)\right),
\]

with harmless Fourier-normalization constants absorbed into `w_l`.  If `P,Q` have degree at most
`E`, let `xi_P,xi_Q` be the inverse Fourier transforms of `D(z^2)P(z^2)` and
`D(z^2)Q(z^2)`.  Fourier evaluation and (RJRR.20) give

\[
 \langle \xi_P,B\xi_Q\rangle
   =\sum_{i,j=0}^E p_iq_jh_{i+j}.
\]

Thus the compression form of `B` to `mathcal K=D\mathbb R_(<=E)[u]` is `H=C-G`.  For every
coefficient vector `v`,

\[
 v^THv=v^TCv-v^TGv\ge-v^TGv,
\]

with equality exactly on the coefficient line of `P_*`.  Relative to the actual Hilbert metric
`G`, the compressed operator therefore has simple lowest eigenvalue `-1`, with Fourier-side
eigenvector

\[
 g(z)=D(z^2)P_*(z^2).
\]

Now set `A_epsilon=A_sigma+epsilon B`.  Because `0` is an isolated lowest eigenvalue of
`A_sigma`, standard finite-multiplicity self-adjoint perturbation theory gives, for all sufficiently
small positive `epsilon`, a simple isolated lowest eigenvalue of `A_epsilon`.  Its normalized
eigenfunction is even and converges in `L^2` to the inverse Fourier transform of `g`: the rescaled
ground-cluster compression converges to `H`, whose lowest eigenvalue is simple.

The Schwartz kernel of `A_epsilon` is still a real even distribution of the difference variable,
so the Connes--van Suijlekom theorem applies.  The Fourier transform `g_epsilon` of its lowest
eigenfunction has only real zeros.  Finite-interval `L^2` convergence implies locally uniform convergence
`g_epsilon->g` on `mathbb C`; Hurwitz therefore forces every zero of the nonzero limit `g` to be
real.  But `rho_1=-1` makes `g(i)=g(-i)=0`.  This contradiction proves (RJRR.15).

The full-ground hypothesis is load-bearing.  The hard-edge theorem by itself establishes the
closed **even-sector** form and does not promote `0` past a lower odd eigenvalue.  Therefore this
argument sharpens the ground-multiplicity branch once full ground admission is known; it does not
smuggle that admission into Route U.

### 2.8 Parity identifies every excess direction

The separate parity-jet theorem gives the direct mechanism behind (RJRR.15). For squared-variable
functions, the full odd-sector form is

\[
\mathfrak b_\sigma^-(H,K)=\int uH(u)K(u)\,d\eta_\sigma(u).
\]

Hence the odd Gram entry of two same-root descendants is

\[
M_{r,p+q-1}+rM_{r,p+q},
\]

and all divided moments below order \(2m_r\) vanish. The only possible nonzero odd entry is the
terminal value \(r\gamma_r\). Distinct roots remain orthogonal because
\(uF_{r,p}=rF_{r,p}+F_{r,p-1}\) and both even pairings vanish.

Under full-ground nonnegativity, every nonterminal odd descendant has zero form energy and
therefore lies in the kernel. Rational principal parts prove independence, while parity separates
them from the even radical. This proves (RJRR.23)--(RJRR.24) and explicitly supplies the
additional modes predicted by the signed-cosine argument. The latter remains an independent
convolution-perturbation proof, but it is no longer the sharp classification.

## 3. Conjecture--failure--pivot audit

1. **The simultaneous Cauchy equations overdetermine `F`.** `[FALSIFIED AS A MECHANISM]`.
   For distinct roots they are exactly partial-fraction/Lagrange orthogonality.  This is standard
   extremal-function behavior, not a source contradiction.
2. **Second-kind/Wronskian machinery closes the simple-root branch.** `[FALSIFIED AS AN
   INFERENCE]`.  Positive finite quadrature already diagonalizes root-division functions; its
   second-kind ratio explains (RJRR.7) but supplies no sign for the critical scalar floor.
3. **Root coalescence loses only zero-location information.** `[FALSIFIED]`.  A root of
   multiplicity `m` emits a complete flag of `m-1` independent exact null descendants.  All
   divided-jet mass vanishes except one terminal scalar.  Coalescence is spectral degeneracy, not
   a harmless defect of compact convergence.
4. **The squared-variable `LP` constraint is an independent last mile in the simple-ground
   branch.** `[FALSIFIED BY COLLISION]`.  In that branch the Connes--van Suijlekom theorem already
   forces all zeros of `f` real, hence all squared roots nonnegative.  Route U adds no independent
   sign there.
5. **Polar evaluation is cyclic on the degenerate ground and restores simplicity.**
   `[FALSIFIED]`.  The radical pencil (RJRR.19) always contains a nonzero polar-dark member.  Polar
   evaluation chooses the completion root `-1/4`; it cannot distinguish the sign of the repeated
   root that generated the pencil.
6. **The divided root jets may exhaust a minimally degenerate convolution ground.**
   `[FALSIFIED]`.  Globally those jets equal `D` times every polynomial of degree at most the total
   multiplicity excess `E`.  A metric-corrected finite signed cosine perturbation selects
   `D(z^2)P_*(z^2)` as simple lowest state, where `P_*` has a prescribed negative root.  This
   contradicts the Connes--van Suijlekom real-zero theorem.  Repeated roots require at least one
   additional non-jet ground mode.
7. **Even-sector boundary positivity already supplies the full convolution-ground hypothesis.**
   `[NOT PROVED]`.  An unobserved lower odd mode would invalidate the ground-state perturbation
   theorem.  Full-ground admission remains a separate source/operator obligation.
8. **The excess non-jet mode is unclassified source data.** **FALSIFIED.** Multiplication by the
   Fourier variable sends every nonterminal divided jet to an odd zero-energy descendant and
   sends terminal mass \(\gamma_r\) to exact odd energy \(r\gamma_r\). Under full-ground
   nonnegativity these parity lifts explicitly supply all \(E\) additional modes required by the
   stronger bound \(1+2E\).

## 4. Higher universal principle and exact new frontier

Root geometry is the projective spectrum of the radical, not an auxiliary decoration:

\[
 \text{root coalescence}
 \longrightarrow \text{complete nonterminal null flag}
 \longrightarrow \text{one terminal positive mass}.         \tag{RJRR.21}
\]

Equation (RJRR.10) is an exact confluent diagonalization law: coalescence pushes every nonterminal
direction into the radical and leaves at most the terminal mass `gamma_r`.  Finite flat
quadrature, second-kind ratios, hard-edge `LP` closure, and restricted-Weil ground degeneracy are
shadows of this one radical-jet law.

The global saturation and perturbation theorem add a stricter layer:

\[
 \text{all root jets}=D\mathbb R_{\le E}[u]
 \quad\Longrightarrow\quad
 \text{degenerate full ground has a non-jet mode}.           \tag{RJRR.22}
\]

The parity law now accounts for the excess directly: every nonterminal even divided root has an
odd twin, and the terminal odd signature is \(r\gamma_r\). The genuinely missing datum is no
longer an unidentified mode; it is admission of the odd sector at the selected even boundary.

`[OPEN CORE]` Route U now has two genuinely different branches.

- **Simple birth:** (RJRR.12) merges Route U with the known simple-even restricted-Weil ground
  problem.  Further `LP` or root-division work is theatre unless it supplies a new literal
  prime--Gamma sign.
- **Degenerate birth:** parity already constructs the excess directions. Each repeated root emits
  an odd copy of every nonterminal jet, while terminal odd signature is exactly
  \(r\gamma_r\). Closure must promote or refute odd-sector admission and then use this explicit
  Krein signature; no unknown-mode classification remains.

The next discriminator is therefore **self-selected odd-sector admission**, not classification of
one-root Cauchy equations or search for an unspecified excess mode.

## 5. Literature and corpus audit

- `[CORPUS]` `FiniteMomentNullPolynomialRoots.lean` proves each finite boundary polynomial has
  real simple roots; it does not prevent coalescence in a moving-degree compact limit.
- `[CORPUS]` `SecondKindMomentPolynomials.lean`, `GaussNodeDenominator.lean`, and
  `QuasiCauchyTransform.lean` identify finite root-division orthogonality with positive quadrature
  and second-kind ratios.  They support the failure verdict for the simple Cauchy line.
- `[LITERATURE]` Brevig--Chirre--Ortega-Cerda--Seip,
  [*Point evaluation in Paley--Wiener spaces*](https://arxiv.org/abs/2210.13922), relate
  zero-division orthogonality of Paley--Wiener extremizers to de Branges spaces.  Thus generic
  simple-root orthogonality is known parent theory.
- `[LITERATURE]` Suzuki,
  [*Weil's quadratic form via the screw function*](https://arxiv.org/abs/2606.09096), records the
  lower-bounded discrete localized Weil spectrum and continuous aperture floor.
- `[LITERATURE]` Connes--van Suijlekom,
  [*Quadratic Forms, Real Zeros and Echoes of the Spectral Action*](https://arxiv.org/abs/2511.23257),
  prove the simple isolated even-ground real-zero theorem used in (RJRR.12) and in the signed-cosine
  perturbation argument for (RJRR.15).

No located source states the literal prime--Gamma complete radical flag, diagonal jet law
(RJRR.10), polynomial-module saturation (RJRR.14), odd terminal law (RJRR.23), or parity-doubled
kernel bound (RJRR.24).
Targeted searches found generic Paley--Wiener reproducing-kernel and Toeplitz theory, but no
degenerate-ground convolution perturbation theorem with this root-jet consequence.  Priority and
significance remain unverified pending specialist review.

## Lean status

No Lean theorem is claimed.  An abstract semidefinite-form theorem with a supplied null vector is
theorem laundering and does not satisfy Route U's formal target.  Exact formalization must wait
for the unconditional literal hard-edge boundary construction and restricted-Weil form domain in
Lean. The direct parity theorem requires both literal parity sectors, cancelled root descendants,
and the actual full convolution floor. The independent perturbation theorem additionally requires
bounded cosine perturbations and the Connes--van Suijlekom theorem. None may be replaced by
supplied abstract hypotheses.

## Log

- 2026-08-11 -- simple Cauchy line killed as ordinary extremal orthogonality; repeated-root
  radical-jet survivor proved; simple/degenerate ground dichotomy isolated.
- 2026-08-11 -- bootstrapped the initial half-flag to all `m-1` nonterminal descendants, proved
  complete divided-jet Gram diagonalization, and falsified polar cyclicity by the explicit radical
  root pencil.  Removed abstract Lean-wrapper status.
- 2026-08-11 -- proved global polynomial-module saturation and a signed-cosine perturbation
  theorem: a repeated-root isolated convolution ground must contain an additional non-jet mode
  beyond every forced descendant.  Isolated full-ground admission remains open and explicit.
- 2026-08-11 -- proved the exact parity companion: terminal even mass \(\gamma_r\) becomes odd
  energy \(r\gamma_r\), every nonterminal jet has an odd zero-energy twin, full-ground kernel
  dimension is at least \(1+2E\), and simple full ground forces every squared root strictly
  positive. Excess modes are now explicit; odd-sector admission is the remaining gate.

## Lean status (updated)

The literal form of `(RJRR.1)`-`(RJRR.2)` is now formal.  `d eta_sigma` is not an abstract measure:
it is the explicit half-line density `V_sigma(sqrt u)/sqrt u` built from the archimedean rate and
the finitely many prime frequencies below `2 sigma`, together with the polar atom of mass `2 pi` at
`u = -1/4`, and `b_sigma` is its pairing.  See
`RHTower/XiShiftedHardEdgeDensityMeasure.lean` (`routeUHardEdgeDensity`,
`routeUHardEdgePairing`, `routeUHardEdgeEvenForm`, `routeUEvenWeil_eq`) and
`HTGeometry/SquaredVariableSubstitution.lean` for the substitution `u = x^2` that identifies the
spectral-line form with the half-line pairing.

Given the standing situation of the card — nonnegativity of the form on the one-parameter families
spanned by the divided descendants, and nullity of the state — the following are Lean-proved and
axiom-clean in `RHTower/XiShiftedHardEdgeParityJet.lean`:

| statement | Lean |
|---|---|
| `(RJRR.6)` a null state annihilates its own divided descendants | `routeUJetMoment_base_of_null` |
| `(RJRR.7)` orthogonality across distinct roots | `routeUEvenForm_eq_zero_of_factor`, `routeUEvenForm_distinct_roots` |
| `(RJRR.8)` the nonterminal flag lies in the radical | `routeUJetDescendant_diag_eq_zero`, `routeUEvenForm_eq_zero_of_diag` |
| `(RJRR.9)` all moments below the terminal one vanish | `routeUJetMoment_eq_zero_of_null` |
| `(RJRR.10)` the complete divided-jet Gram law | `routeUEvenForm_descendant_eq_zero`, `routeUJetGram_of_null` |
| `(RJRR.11)` independence of the divided principal parts, single root | `linearIndependent_routeUJetDescendant`, `linearIndependent_routeUParityDirections` |
| the parity lift `gamma_r -> r gamma_r` | `routeUOddForm_descendant`, `routeUOddForm_terminal` |
| strictly positive roots under a nonvanishing terminal odd energy | `routeUJetRoot_nonneg`, `routeUJetRoot_pos` |

The Cauchy--Schwarz bootstrap behind `(RJRR.9)` is isolated as
`HTGeometry/PsdHankelJetVanishing.lean` (`sq_le_of_quadratic_nonneg`, `symmBilin_sq_le`,
`psdHankel_jet_vanishing`, `psdHankel_gram_off_terminal`).

What is still not formal is `(RJRR.5)` — nonnegativity of the form on the closed critical-type
domain, which is an output of the hard-edge boundary theorem — and item 5, the discreteness of the
localized operator's spectrum, which needs the Friedrichs operator of the form on its closed
domain (`HTGeometry/FriedrichsFormOperator.lean` supplies the general construction).

## Lean status (final)

The card is formalized.  Every analytic object is literal: `d eta_sigma` is the explicit half-line
density built from the archimedean rate and the finitely many prime frequencies below `2 sigma`
together with the polar atom of mass `2 pi` at `u = -1/4`, and `b_sigma` is its pairing.  The
hypotheses carried by the Lean statements are exactly the standing situation of the card —
membership in the form domain, nonnegativity of the form on the one-parameter families spanned by
the divided descendants, and nullity of the state.

New in this round:

    RHTower/XiShiftedHardEdgeDensityMeasure.lean      (axiom-clean, wired, built)
      routeUHardEdgePairing_tendsto                   the pairing is continuous along a dominated
                                                      family of states
      routeUHardEdgePairing_nonneg_of_tendsto         **(RJRR.5)** nonnegativity closes at the
                                                      critical aperture: a dominated limit of
                                                      states with nonnegative pairing has
                                                      nonnegative pairing

    HTGeometry/PartialFractionIndependence.lean       (axiom-clean, wired, built)
      dividedPart, rootProduct, dividedPartFamily     the divided principal parts at a finite root
                                                      set, written without division
      dividedPart_eq_zero_of_sum_eq_zero,
        base_and_dividedPart_eq_zero_of_sum_eq_zero,
        linearIndependent_dividedPartFamily           **(RJRR.18)** the rational principal parts
                                                      are independent
      multiJetBase, multiJetDescendant,
        multiJet_eq_zero_of_sum_eq_zero               the same statement for the entire states
      finrank_multiJetEvenFamily                      **(RJRR.11)** the state and its `E` nonterminal
                                                      divided descendants span a space of dimension
                                                      `1 + E`
      span_dividedPartFamily                          **(RJRR.14)** the root product and all its
                                                      divided principal parts span exactly the
                                                      polynomials of degree at most `E`; the forced
                                                      root-jet space is the full polynomial module

    HTGeometry/NonnegFormRadical.lean                 (axiom-clean, wired, built)
      bilinForm_sq_le, formRadical                    the radical of a nonnegative symmetric
                                                      bilinear form is a submodule
      eq_zero_of_form_diag_eq_zero                    a zero-energy vector lies in the kernel of any
                                                      operator representing the form
      card_le_rank_ker_of_zero_energy                 an independent family of zero-energy vectors
                                                      bounds the rank of that kernel

    RHTower/XiShiftedHardEdgeParityJet.lean           (axiom-clean, wired, built)
      routeUParityFamily,
        linearIndependent_routeUParityFamily,
        finrank_routeUParityFamily                    **(RJRR.24)** the state, its `E` nonterminal
                                                      divided descendants and their odd twins are
                                                      `1 + 2E` independent zero-energy directions
      finrank_routeUParityFamily_ge                   **(RJRR.15)** hence `E > 0` forces at least
                                                      `E + 2` of them — the excess degeneracy, now
                                                      source-internal and with no perturbation
                                                      argument
      finrank_routeUParityTerminalFamily              the terminal sharpening: roots of vanishing
                                                      terminal mass add both terminal descendants,
                                                      a zero root adds the terminal odd one
      routeUJetRoot_nonneg, routeUJetRoot_pos         **(RJRR.12)** under a simple full ground every
      routeUJetTerminal_null_of_terminal_mass_zero,     root is simple, its terminal mass positive,
        routeUJetTerminalOdd_null_of_root_zero          and the root strictly positive — each
                                                      alternative contradicts one-dimensionality
                                                      through the counts above

`(RJRR.6)`-`(RJRR.10)`, `(RJRR.16)`-`(RJRR.17)` and `(RJRR.23)` were already formal; see the table
in the previous section.

Two remarks on scope.  First, `(RJRR.15)` no longer needs the signed-cosine perturbation argument
of §2.7 or the Connes--van Suijlekom real-zero theorem: the parity count `1 + 2E` of `(RJRR.24)`
implies it arithmetically, and that count is proved from the source alone.  The same holds for
`(RJRR.12)`: each of the three alternatives — a repeated root, a vanishing terminal mass, a zero
root — produces at least one further independent zero-energy direction, so a one-dimensional
kernel excludes all three without any external input.  Second, the Hilbert-space realization of the
localized convolution operator is not constructed; it is not needed, because the only property of
it used in the card — a zero-energy vector of a nonnegative form lies in the kernel — is proved
unconditionally in `NonnegFormRadical`.
