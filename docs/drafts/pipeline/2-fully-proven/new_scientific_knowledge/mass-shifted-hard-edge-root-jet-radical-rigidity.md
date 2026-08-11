# Mass-shifted hard-edge root-jet radical rigidity

- **ID:** `mass-shifted-hard-edge-root-jet-radical-rigidity`
- **Stage:** 2-fully-proven / needs independent specialist audit
- **Type:** THEOREM (paper)
- **Source:** Route U item 48 and `mass-shifted-hard-edge-hyperbolic-weil-boundary`
- **Statement:** At a critical hard-edge boundary, every repeated squared-variable zero creates
  additional exact null descendants; consequently root multiplicity is bounded by restricted-Weil
  ground multiplicity, and the one-dimensional-ground branch collapses to the known simple-ground
  real-zero problem.
- **Scientific status:** `[PAPER-PROVED] [NOVELTY UNVERIFIED] [LEAN NOT STARTED]`

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
- [ ] 2 -> 3 formalized: requires literal restricted-Weil form, hard-edge compactness, and
  boundary-state theorem in Lean; no abstract-premise wrapper is admissible
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

2. `F` lies in the radical and every allowed divided moment vanishes:

   \[
   \mathfrak b_\sigma(F,H)=0,\qquad
   M_{r,k}:=\int_{\mathbb R}{F(u)^2\over(u-r)^k}\,d\eta_\sigma(u)=0
   \quad(1\le k\le m_r).                                   \tag{RJRR.6}
   \]

   All quotients at `u=r`, including `r=-1/4`, are interpreted by their continuous entire
   extensions.  In particular, no `0/0` polar fraction occurs.

3. Descendants belonging to distinct roots are exactly orthogonal:

   \[
   \mathfrak b_\sigma(F_{r,p},F_{s,q})=0
   \quad(r\ne s,\ 1\le p\le m_r,\ 1\le q\le m_s).          \tag{RJRR.7}
   \]

4. Each repeated root forces extra radical dimension:

   \[
   F_{r,k}\in\operatorname{rad}\mathfrak b_\sigma
   \quad\left(1\le k\le\left\lfloor{m_r\over2}\right\rfloor\right), \tag{RJRR.8}
   \]

   and the rational principal parts are linearly independent.  Hence

   \[
   \boxed{\quad
   \dim\operatorname{rad}\mathfrak b_\sigma
   \ \ge\ 1+\sum_{F(r)=0}\left\lfloor{m_r\over2}\right\rfloor.
   \quad}                                                    \tag{RJRR.9}
   \]

5. The literal localized restricted-Weil operator has discrete spectrum and finite-dimensional
   eigenspaces.  Therefore only finitely many roots of `F` can be multiple.  If its zero
   eigenspace is one-dimensional, every root of `F` is simple.  Under the same simple isolated
   even-ground hypothesis, Connes--van Suijlekom's real-zero theorem forces every zero of `f` to
   be real, so

   \[
   \dim\ker A_\sigma=1
   \quad\Longrightarrow\quad
   \text{every root of }F\text{ is simple and nonnegative}. \tag{RJRR.10}
   \]

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
 =\sum_{j=1}^p{a_j\over(u-r)^j}+\sum_{\ell=1}^q{b_\ell\over(u-s)^\ell}. \tag{RJRR.11}
\]

After multiplication by `F(u)^2`, every apparent singularity is removable.  Integrating
(RJRR.11) against `eta_sigma` and applying (RJRR.6) term by term proves (RJRR.7).  Thus the
simultaneous simple-root Cauchy equations are the Lagrange orthogonality relations of a critical
extremizer; by themselves they are not an overdetermined contradiction.

### 2.4 Multiplicity creates null descendants

If `2k<=m_r`, then `F_(r,2k)` is admissible and

\[
 \mathfrak b_\sigma(F_{r,k},F_{r,k})
 =\int {F(u)^2\over(u-r)^{2k}}\,d\eta_\sigma(u)
 =\mathfrak b_\sigma(F,F_{r,2k})=0.                          \tag{RJRR.12}
\]

Nonnegativity of the form makes every zero-norm vector radical, proving (RJRR.8).

For linear independence, take any finite relation among `F` and the descendants in (RJRR.8),
divide on the complement of the zero set by the nonzero entire function `F`, and obtain a rational
identity

\[
 c_0+\sum_{r,k}{c_{r,k}\over(u-r)^k}=0.                     \tag{RJRR.13}
\]

Every principal part in (RJRR.13) vanishes, and then `c_0=0`.  Arbitrary finite subsets are
independent, proving the dimension bound (RJRR.9).

### 2.5 Compact-resolvent and simple-ground consequences

Suzuki records that the self-adjoint localized Weil operator is lower bounded with discrete
spectrum and `+infinity` as its only accumulation point.  Its zero eigenspace is therefore finite
dimensional.  Equation (RJRR.9) rules out infinitely many multiple roots.  A one-dimensional
zero eigenspace rules out even one root with multiplicity at least two.

The hard-edge `f` is the Fourier transform of the even zero-mode on the finite frequency interval.
Connes--van Suijlekom prove that the Fourier transform of a simple isolated even ground state has
only real zeros.  If `F` had a negative root `r`, then `f` would vanish at the nonreal points
`z=\pm i\sqrt{-r}`.  Thus simple ground excludes negative roots.  Together with the
previous paragraph this proves (RJRR.10).

## 3. Conjecture--failure--pivot audit

1. **The simultaneous Cauchy equations overdetermine `F`.** `[FALSIFIED AS A MECHANISM]`.
   For distinct roots they are exactly partial-fraction/Lagrange orthogonality.  This is standard
   extremal-function behavior, not a source contradiction.
2. **Second-kind/Wronskian machinery closes the simple-root branch.** `[FALSIFIED AS AN
   INFERENCE]`.  Positive finite quadrature already diagonalizes root-division functions; its
   second-kind ratio explains (RJRR.7) but supplies no sign for the critical scalar floor.
3. **Root coalescence loses only zero-location information.** `[FALSIFIED]`.  A root of
   multiplicity `m` emits `floor(m/2)` independent exact null descendants.  Coalescence is
   spectral degeneracy, not a harmless defect of compact convergence.
4. **The squared-variable `LP` constraint is an independent last mile in the simple-ground
   branch.** `[FALSIFIED BY COLLISION]`.  In that branch the Connes--van Suijlekom theorem already
   forces all zeros of `f` real, hence all squared roots nonnegative.  Route U adds no independent
   sign there.

## 4. Higher universal principle and exact new frontier

Root geometry is the projective spectrum of the radical, not an auxiliary decoration:

\[
 \text{root coalescence}
 \longrightarrow \text{divided null jets}
 \longrightarrow \text{ground-space multiplicity}.         \tag{RJRR.14}
\]

Finite flat quadrature, second-kind ratios, hard-edge `LP` closure, and restricted-Weil ground
degeneracy are shadows of this one radical-jet law.

`[OPEN CORE]` Route U now has two genuinely different branches.

- **Simple birth:** (RJRR.10) merges Route U with the known simple-even restricted-Weil ground
  problem.  Further `LP` or root-division work is theatre unless it supplies a new literal
  prime--Gamma sign.
- **Degenerate birth:** prove that the literal completed-Xi source forbids
  `dim ker A_sigma>=2`, or exploit two independent zero modes to force a source contradiction.
  This is the only branch where finite Hankel coalescence supplies information absent from the
  existing simple-ground literature.

The next discriminator is therefore a **source-derived simplicity or degeneracy contradiction**,
not classification of one-root Cauchy equations.

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
  prove the simple isolated even-ground real-zero theorem used only in (RJRR.10).

No located source states the literal prime--Gamma root-jet dimension bound (RJRR.9).  The algebraic
mechanism is elementary once the critical form closure is known, so priority and significance
remain unverified pending specialist review.

## Lean status

No Lean theorem is claimed.  An abstract semidefinite-form theorem with a supplied null vector
would be a wrapper and would not satisfy Route U's formal target.  Exact formalization must wait
for the unconditional literal hard-edge boundary construction and restricted-Weil form domain in
Lean, then prove (RJRR.5)--(RJRR.10) for those concrete objects.

## Log

- 2026-08-11 -- simple Cauchy line killed as ordinary extremal orthogonality; repeated-root
  radical-jet survivor proved; simple/degenerate ground dichotomy isolated.
