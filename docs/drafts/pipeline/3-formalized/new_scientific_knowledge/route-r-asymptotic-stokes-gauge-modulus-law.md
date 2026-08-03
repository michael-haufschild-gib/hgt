# Route R asymptotic Stokes gauge-modulus law

- **ID:** `route-r-asymptotic-stokes-gauge-modulus-law`
- **Stage:** 3 — formalized in Lean 4
- **Type:** ROUTE-R NO-GO / POSITIVE GAUGE-MODULUS CLASSIFICATION
- **Status:** `[LOCAL-RESEARCH] [FALSIFIED] [PAPER-PROVED] [LEAN-PROVED] [NOT RH]`
- **Parent:** `../../1-in-progress/route-r-source-positive-polarization-stokes-flatness.md`
- **Lean target:**
  `formal/GaloisForLFunctions/RHTower/PrimeDepthBVWoldAsymptoticStokesGaugeModulus.lean`
- **Target:** decide whether flatness plus the source framing at infinite Wold depth uniquely
  identifies the transported positive polarization with the fixed Cartier polarization.

## Exact frontier

Write
\[
 m_i=(1-p_i^{-1})p_i^{-e_i},\qquad
 \lambda_i=\log(p_i^{e_i+1}),\qquad
 q_i=\frac{m_i}{\lambda_i}.
\]
The resolved source frame is
\[
 G_{a,i}=\begin{pmatrix}\lambda_i^{-1}&a m_i\\0&\lambda_i\end{pmatrix},
 \qquad R_{a,ij}=G_{a,i}^{-1}G_{a,j}.
\]
The fixed source frame is `G_(0,i)`.  In its orthonormal physical coordinates define
\[
 L_{a,i}=G_{a,i}G_{0,i}^{-1},\qquad
 \widehat R_{a,ij}=G_{0,i}R_{a,ij}G_{0,j}^{-1}.
\tag{1}
\]

## Falsified conjecture

> **[CONJECTURE C1 — ASYMPTOTIC STOKES UNIQUENESS]**  A positive flat resolved metric whose
> physical frame approaches the fixed source frame at infinite depth must be the fixed Cartier
> metric.

This would have supplied Route R's missing same-fibre identification without selecting a divisor.
It is false.

## Exact counterfamily and classification

### Theorem 1 — unipotent normal form

For every real `a` and every source cell `i`,
\[
 L_{a,i}=N(aq_i),\qquad
 N(t)=\begin{pmatrix}1&t\\0&1\end{pmatrix},
\tag{2}
\]
and
\[
 \widehat R_{a,ij}=L_{a,i}^{-1}L_{a,j}
                  =N\bigl(a(q_j-q_i)\bigr).
\tag{3}
\]
Consequently every normalized cycle holonomy is the identity.

**Proof.**  The inverse fixed frame is
`G_(0,i)^(-1)=diag(lambda_i,lambda_i^(-1))`.  Direct multiplication gives `(2)`.
Using `R_(a,ij)=G_(a,i)^(-1)G_(a,j)` gives the first equality in `(3)`; the additive law
`N(x)N(y)=N(x+y)` gives the second.  Products around a cycle telescope.  No divisor data enter.
\(\square\)

### Theorem 2 — every gauge has the same infinite-depth framing

Fix an ordinary prime `p` and put `i_e=(p,e)`.  Then
\[
 q_{i_e}longrightarrow0,
 \qquad L_{a,i_e}z\longrightarrow z
\tag{4}
\]
for every `a` and every `z in C^2`.  In particular
`widehat R_(a,i_e,i_(e+1)) -> I`.

**Proof.**  Since `p>1`, `0<p^(-1)<1`, and
\[
 0<q_{i_e}
 =\frac{(1-p^{-1})p^{-e}}{(e+1)\log p}
 \leq \frac{1-p^{-1}}{\log p}\,p^{-e}.
\tag{5}
\]
The right side tends to zero geometrically, so `(4)` follows from `(2)`.  Formula `(3)` gives the
transition limit.  \(\square\)

### Theorem 3 — the invisible modulus is nontrivial and classified by `a`

At every finite source cell, `q_i>0`.  Hence
\[
 L_{a,i}(0,1)=(a q_i,1),
\]
so `a -> L_(a,i)` is injective.  Thus the asymptotically trivial positive flat frames contain a
literal real affine line of mutually distinct source gauges.  All of them have the same flat
cycle data and the same identity framing at depth infinity.

The associated fixed-Cartier vertical energy distinguishes that modulus:
\[
 E_i^{src}(R_{a,ij}v_c(j))-E_j^{src}(v_c(j))
 =a^2(q_i-q_j)^2|c|^2.
\tag{6}
\]

## Hostile verdict

`C1`: **FALSE**.  The family `(2)` is an explicit counterexample for every `a != 0`.
The failure is structural, not a missing estimate: the BV mass dies exponentially faster than
the Wold--Gamma clock grows, so the full unipotent Stokes modulus is invisible in the asymptotic
frame.

Generic irregular-connection theory already warns that formal/asymptotic type does not erase
Stokes moduli.  The source-specific advance is the exact modulus and its coefficient:
`a q_i = a m_i/lambda_i`, together with the proof that even the literal Wold-depth boundary cannot
select it.

## Hostile re-entry: associated grade is blind

The first stronger conjecture was too weak:

> **[FALSIFIED AS A SELECTOR — C2]** Preservation of the finite mass/clock filtration, or of its
> associated graded, forces `a=0`.

Let
\[
 h(c)=(c,0),\qquad \pi(z_1,z_2)=z_2,\qquad s(c)=(0,c).
\]
Here `h` is the horizontal subobject, `pi` is the vertical quotient, and `s` is the fixed
source-pointed splitting.  Formula `(2)` gives, for every `a` and every finite cell `i`,
\[
 L_{a,i}h=h,\qquad \pi L_{a,i}=\pi.                       \tag{7}
\]
Consequently every member of the counterfamily acts identically on the associated graded
`H plus Q`.  Finite grade preservation is therefore as nonselective as cycle flatness.

The missing coordinate survives only in the extension splitting:
\[
 L_{a,i}s(c)=s(c)+h(aq_i c).                              \tag{8}
\]
Since `q_i>0`, preservation of `s` at one finite cell is equivalent to `a=0`.  Equivalently, the
shear coefficient `a q_i` is the exact affine coordinate of the splitting torsor erased by both
the associated-graded functor and Wold-depth asymptotics.  Orthogonality of the two literal
summands would also force `a=0`, because
\[
 \langle L_{a,i}h(1),L_{a,i}s(1)\rangle=a q_i,
\]
but that condition is preservation of a distinguished splitting/dagger, not mere grade
preservation.

This classification is elementary extension theory in its parent form.  The source-specific
advance is the exact Route-R torsor coordinate `a m_i/lambda_i` and the simultaneous proof that
cycle data, associated grade, and infinite-depth framing all erase it.

## Actual source-pointed section

The rational-Witt/Koszul source already constructs the section that the first formulation of the
open core requested.  At a prime `p`, write
\[
 A_p^1=Q_p\oplus W_p,\qquad d_p:A_p^1\to A_p^2,
\]
let `sigma_p:A_p^2 -> A_p^1` be the canonical center section of `d_p`, let
`tau_p:A_p^2 -> C` be the normalized Haar orientation trace, and let
`epsilon_p:C -> A_p^2` be its constant-packet section.  Define
\[
 s_p^{\rm src}=\sigma_p\epsilon_p,
 \qquad
 \Phi_p(q,w)=\bigl(\lambda_p(q),\tau_p(d_p(q,w))\bigr).       \tag{9}
\]
All maps in `(9)` are defined before any Xi divisor.  The two source section laws give
\[
 \Phi_p s_p^{\rm src}(c)=(0,c).                              \tag{10}
\]
For `i=(p,e)`, put
\[
 \widetilde s_i^{\rm src}(c)
   =s_p^{\rm src}(c/\lambda_i).
\]
Then `Phi_p` sends this literal rational-Witt source section to the clock-normalized vertical
conormal `v_c(i)=(0,c/lambda_i)`.

The source side of the pointed splitting is therefore constructed.  Its comparison with Route R
has the exact defect
\[
 R_{a,ij}\Phi_p\widetilde s_j^{\rm src}(c)
   -\Phi_p\widetilde s_i^{\rm src}(c)
   =\left(-\frac{a\theta_{ij}}{\lambda_j}c,0\right)          \tag{11}
\]
for same-prime cells.  On any nonzero edge and nonzero `c`, the comparison square commutes iff
`a=0`.  Thus merely constructing the source section cannot prove RH; the missing theorem is the
independent singular comparison which makes `(11)` vanish.

## Stronger conjecture forced by the source comparison

> **[CONJECTURE C3 — SOURCE-POINTED SINGULAR CARTIER COMPARISON] [OPEN CORE]**  Construct, before
> divisor specialization, a coefficient-faithful nonannihilating singular Cartier comparison
> from the rational-Witt/Koszul source to the completed Gamma/co-Poisson Xi conormal.  Prove that
> it intertwines `s_p^src` with the actual leading Xi conormal and makes the edge comparison
> square in `(11)` commute.  Its definition may not use a metric, dagger, centered-rate-zero
> condition, divisor location, or vanishing of the Route-R anomaly.

If `C3` holds, `(11)` forces `a=0`; after the unconditional Xi specialization
`a_rho=2 Re(rho)-1`, every Xi divisor lies on the critical line.  Thus `C3` is sufficient for RH,
but it is not yet proved.  The exact research problem is now the singular comparison, not source
section existence.  Replacing it by associated-grade preservation or by orthogonality asserted
only after Xi landing is circular or nonselective.

## Positive survivor

`[PAPER-PROVED]` **Asymptotic Stokes gauge-modulus law.**  Route R's normalized resolved source
has an injective real line of nontrivial, positive-flat, cycle-trivial gauges all converging to the
same identity framing at infinite depth.  Therefore no theorem using only flatness, cycle
holonomy, moderate/rapid asymptotics, or boundary identity at Wold-depth infinity can supply the
missing Cartier identification.

**New frontier delta:** the distinguished rational-Witt/Koszul source splitting is now explicit
and coefficient-faithful.  Required theorem is its nonannihilating singular Cartier comparison,
not a new splitting.  Infinity normalization, exact cycle data, and associated-grade identity are
all excluded.

## Gates

- [x] internal Route-R and source-ambidexterity audit
- [x] parent irregular-Stokes collision audit
- [x] falsify asymptotic uniqueness by exact source counterfamily
- [x] dependency-closed paper proof of positive survivor
- [x] formalize exact counterfamily, depth limit, and injective modulus in Lean
- [x] hostile re-entry: prove finite associated-grade preservation is nonselective
- [x] construct literal rational-Witt/Koszul pointed section and scalar reporter
- [x] derive exact Route-R pointed-comparison defect
- [ ] construct `C3` singular Cartier comparison from the framed rational-Witt coefficient

## Formal verification

`PrimeDepthBVWoldAsymptoticStokesGaugeModulus.lean` proves the exact unipotent frame and normalized transport formulas, flat
composition, strict positivity of the finite potential, injectivity of the finite-cell gauge
family, geometric convergence of the potential and frames, successor-transition convergence,
the explicit nonzero strict no-go countergauge, identity on the horizontal subobject and vertical
quotient, the exact splitting displacement, and preservation of the distinguished splitting iff
the centered rate is zero.

`PrimeDepthBVWoldCalderonWittPointedSplittingObstruction.lean` constructs the actual pre-Xi
rational-Witt/Koszul pointed section and scalar reporter, proves reporter faithfulness, derives
the exact Route-R edge-comparison defect `(11)`, proves sharp zero-rate commutation, and identifies
global commutation on the actual leading Xi conormal with RH.

- direct `lake env lean` elaboration passes for both modules;
- targeted builds pass for both modules;
- axiom audit of the no-go, splitting, source-reporter, defect, sharpness, and Xi/RH capstones reports
  only `propext`, `Classical.choice`, and `Quot.sound`;
- neither module contains `sorry`, `admit`, new `axiom`, `opaque`, or `unsafe` declarations;
- repository lint reaches both umbrella imports and fails only on unrelated concurrently unwired
  CCM rational-adelic, cyclic, real-corona, sieve, and HTGeometry modules.
