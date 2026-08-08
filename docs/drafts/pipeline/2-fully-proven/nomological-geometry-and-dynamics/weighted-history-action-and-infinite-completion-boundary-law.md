# Weighted history action and infinite completion-boundary law

- **ID:** `weighted-history-action-and-infinite-completion-boundary-law`
- **Stage:** 2 — fully proved on paper
- **Type:** THEOREM / CONSTITUTIVE DYNAMICS CALIBRATION
- **Status:** `[PAPER-PROVED WEIGHTED COMPLETION THEOREM] [THREE-LAW PACKAGE CONJECTURAL]`
  `[ROUTE-INDEPENDENT] [NOT RH] [NO LEAN WRITTEN OR BUILT]`

## 1. Why observer kinematics is insufficient

Native Cech descent determines what an observer identifies.  It does not determine which lifted
histories have finite action.  The minimal proposed CLG constitution therefore has three logically
independent parts:

1. coherent source response on the observer Cech nerve;
2. a vertical symbol conservative on a declared test class;
3. relative coercivity of lifted path action.

This card proves an exact model of Part 3 and proves that none of the three parts follows from the
other two.

## 2. Minimal typed package

Let `q:X->O` be a native observer and `N(q)` its Cech nerve.

### D — descent/Bianchi law

A source-defined response `rho_c` takes values in a declared Picard coefficient object and is
coherent on the full nerve.  In an additive groupoid chart,

\[
 \rho_c(x,x)=0,
 \qquad
 \rho_c(x,z)=\rho_c(x,y)+\rho_c(y,z).
\tag{D}
\]

### S_D — vertical-symbol conservativity

For the declared complexity-`D` test class `T_D`, the vertical linearization or finite-difference
symbol satisfies

\[
 \operatorname{Ann}_{\mathcal T_D}
 \bigl(\operatorname{im}\sigma_{c,D}\bigr)=0.
\tag{S_D}
\]

In a finite-dimensional Hilbert chart this is injectivity of `sigma_(c,D)^*`, equivalently a
positive lower singular-value bound.

### P — relative Hopf--Rinow law

A nonnegative source action `A_c`, subadditive under concatenation, is inf-compact relative to
observation when

\[
 \{\gamma:q\gamma\in C,\ A_c(\gamma)\le R\}
 \quad\text{is compact}
\tag{P}
\]

for every compact observed-history set `C` and finite `R`.

These are typed laws, not one heterogeneous scalar equation.  Their source-normalized joint
construction remains a Stage-1 field problem.

### Proposition 2.1 — logical independence

On the history group `H=(R,+)` with observer `H->*`, define the pair response
`rho_c(x,y)=rho(y-x)`, take test space `T=R^*`, vertical symbol
`sigma=rho'(0):R->R`, and action `A`.  Take:

1. `rho(v)=v+v^2`, `A(v)=|v|`: `S` and `P` hold, `D` fails;
2. `rho(v)=0`, `A(v)=|v|`: `D` and `P` hold, `S` fails;
3. `rho(v)=v`, `A(v)=0`: `D` and `S` hold, `P` fails.

#### Proof

Take the vertical symbol to be the derivative of `rho` at the identity.  Additivity is immediate
to check.  The symbol is nonzero exactly in Cases 1 and 3.  Absolute value has compact sublevels,
while the zero action has the noncompact sublevel `R`. ∎

## 3. Weighted-history completion theorem

Let `J` be countable.  For every `j in J`, let:

1. `K_j` be a compact Hausdorff group;
2. `Gamma_j <= K_j` be dense;
3. `ell_j:Gamma_j->N` be a proper symmetric length: it vanishes only at the identity, is
   subadditive and symmetric, and every finite-radius ball is finite.

Choose weights `w_j>0` such that

\[
 \{j:w_j\le R\}\text{ is finite for every }R<\infty.
\tag{17}
\]

Define

\[
 H=\bigoplus_{j\in J}\Gamma_j,
 \qquad
 \widehat H=\prod_{j\in J}K_j,
 \qquad
 A(h)=\sum_jw_j\ell_j(h_j).
\tag{18}
\]

### Theorem 3.1 — completion boundary has infinite relaxed action

The following hold:

1. `H->Hhat` has dense image and `Hhat` is its two-sided Hausdorff uniform completion;
2. every sublevel `{h:A(h)<=R}` is finite, so `A` is inf-compact;
3. `A` is subadditive;
4. the lower-semicontinuous relaxation

   \[
    \overline A(x)=
    \sup_{U\ni x}\inf\{A(h):h\in H\cap U\}
   \tag{19}
   \]

   satisfies

   \[
    \boxed{
    \overline A(x)=
    \begin{cases}
      A(x),&x\in H,\\
      +\infty,&x\in\widehat H\setminus H.
    \end{cases}}
   \tag{20}
   \]

Consequently compact observer completion adds histories, but every added history lies at infinite
**relaxed** source action.  Equivalently, `(H->Hhat,A)` is proper relative to bounded action.

#### Proof

Density and the completion statement are Theorem 2.1 of
`restricted-history-completion-and-robust-polynomial-saturation-law.md`.

If `A(h)<=R` and `h_j` is nonidentity, then `ell_j(h_j)>=1`, so `w_j<=R`.  Condition `(17)` leaves
only finitely many possible active coordinates.  At each such coordinate,
`ell_j(h_j)<=R/w_j`, and the corresponding length ball is finite.  Thus the sublevel is finite.
Subadditivity follows termwise.

Fix `x in H`.  Every neighbourhood contains `x`, so `bar A(x)<=A(x)`.  For `r<A(x)`, the finite
sublevel `{A<=r}` is closed in the Hausdorff product and excludes `x`; a neighbourhood of `x`
disjoint from it gives `bar A(x)>=r`.  Letting `r` increase to `A(x)` proves equality.

If `x notin H`, then for every finite `R` the finite closed set `{A<=R}` excludes `x`.  A
neighbourhood disjoint from this set has infimum at least `R`.  Since `R` is arbitrary,
`bar A(x)=+infinity`. ∎

## 4. Three-organ calibration

| Organ | Source response/symbol | Exact constitutive statement |
|---|---|---|
| Hurwitz HT | branch increment `sigma(e_(b,r))=Delta_b(r)` | deletion-robust spanning is `S_D`; weighted branch length supplies `P` but does not cause HT |
| Stokes inertia | `q=M:V->R^r`, vertical symbol from `Q^flat|ker M` | in finite dimension, positivity on `ker M` is vertical coercivity and gives `ind_-(Q)+dim Rad(Q)<=rank M` |
| recurrence/completion | marked deck displacement or phase response | observer loop may close while action grows; `P` places new completion-boundary histories at infinite action |

In the Hurwitz robust-symbol architecture, deletion of any `D` columns must leave at least `N+1`
branch-node directions to span an `N`-jet block.  Hence the proof infrastructure needs at least
`N+D+1` available columns.  Availability does not imply simultaneous nonidentity activation and
therefore gives no action lower bound without a separately defined installed-column cost.

## 5. Scalar field-equation no-go

The three organ ranks vary independently.  Products of:

1. `h` Hurwitz labels with distinct monodromy characters;
2. a `2p`-dimensional real space with `M(x,y)=x` and
   `Q(x,y)=-norm(x)^2+norm(y)^2`;
3. the cover `R^r->T^r`;

realize every triple `(h,p,r) in N^3`.  Therefore a real- or complex-coefficient polynomial scalar conservation equation
`F(h,p,r)=0` valid for all product charts must have `F=0`.  No nontrivial scalar rank law couples
HT, inertia, and recurrence.

Indeed, fix `p,r`; the one-variable polynomial `h->F(h,p,r)` has infinitely many roots and is zero.
Each coefficient, viewed next as a polynomial in `p`, vanishes on all natural numbers and is zero;
repeating in `r` kills every coefficient of `F`.

## 6. Exact next construction

The non-tautological field target is a source transgression

\[
 \tau_s:\Theta_s\longrightarrow
 Z^1\!\left(N_\bullet(q);\mathcal E_s\right),
 \qquad
 \rho_c=\tau_s(\theta_s),
\tag{21}
\]

defined before target specialization, together with a source polarization deriving `A_c`.  It must
be Cech/Morita natural and realize, through named comparison functors, Hurwitz branch increments,
Stokes vertical polarity, and recurrence deck displacement.  It must then prove `S_D` and `P` in
their native coefficient fibres.

Equation `(21)` is a Stage-1 construction problem, not a theorem of this card.  If no single source
transgression produces two nonisomorphic symbols with a genuine comparison functor, CLG remains a
typed recipe rather than a field.
