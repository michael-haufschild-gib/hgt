# Gamma-six logarithmic Wold--Jordan transgression

- **ID:** `deninger-gamma-six-logarithmic-wold-jordan-transgression`
- **Stage:** 3-formalized
- **Route:** L — Deninger/Green/Hodge source descent
- **Type:** FORMALIZED SOURCE THEOREM
- **Status:** `[FORMALIZED] [NOVELTY NARROWED] [NOT RH]`

## Frontier

The literal complete Gamma-six source has nonzero principal class
`[G_6] in L^{1,infinity}/L^1` and Wold eigenvalue `1/6`.  Its ordinary Wold coface is trace
class.  The proved trace-ideal/Sonin obstruction therefore kills every strict comparison which
tries to send that ordinary coface to the noncompact physical receiver.  The missing source must
produce a non-trace-class coface before target transport, without changing the critical exponent
or inserting a divisor grade.

## Frozen conjecture

`[CONJECTURE] [DAC_DENINGER_GAMMA_SIX_LOGARITHMIC_WOLD_JORDAN_TRANSGRESSION]`

Let `d(n)=log_6(n+216)`, `g(n)=6^{-d(n)}`, and
`W(n)=6n+1080`, so `d(Wn)=d(n)+1` and `g(Wn)=g(n)/6`.  Define the critical logarithmic jet

\[
                  j(n)=d(n)\log(6)g(n).
\]

Let `G_6=diag(g)` and `J_6=diag(j)` on `ell^2(N)`, and let
`C_6(T)=S_6^*TS_6` be literal Wold compression.  Then:

1. `J_6` is the derivative at the neutral character of the forward shell family
   `diag(g^{1-delta})`; the reflected derivative is `-J_6`.
2. The exact Jordan transgression is

   \[
   \boxed{C_6(J_6)-\frac16J_6=\frac{\log6}{6}G_6.}
   \]

3. `J_6` is not weak Schatten one, but `J_6 G_6^epsilon` is trace class for every
   `epsilon>0`.  Thus the minimal source domain is one logarithmic ideal order above the
   already constructed weak-trace principal class.
4. Among shell-constant jets with affine dependence on shell depth, every jet with this coface is
   `J_6+bG_6`.  Thus the coface fixes the logarithmic slope and leaves exactly the ordinary Wold
   eigenspace as gauge.  Differentiation of the source family fixes `b=0`; the forward and reflected
   derivatives are `J_6` and `-J_6` and have opposite cofaces.
5. After tensoring with the actual nonzero leading Gamma-six source vector, the same equation
   holds in the rectangular source operator space.  Its right-hand side is the coefficient-faithful
   nonzero principal class of the complete corrected Mobius tensor source, modulo the already
   proved trace-class remainder.

Public meaning: horizontal orientation is not another eigenvector of the critical Wold source;
it is its canonical generalized eigenvector.  Differentiating before specialization turns the
trace-class zero-order coface into the noncompact principal class needed by the physical target.

## Hostile attacks

### H1 — routine differentiation only

The scalar identity is elementary and is not itself a novelty claim.  The scientific claim is the
source-specific ideal placement: actual Gamma-six shell multiplicity makes `G_6` weak trace class,
forces `J_6` outside weak Schatten one, and keeps every positively regularized jet trace class.
This is the exact minimal extension which escapes the proved trace-ideal/Sonin no-go.

### H2 — fitted critical exponent

The exponent is not fitted.  Existing source asymptotics prove that `6^{-m}` is the tensor square
of the first surviving Mobius atom.  The logarithmic factor is forced by differentiating that
source exponent; changing it changes the source family.

### H3 — hidden RH or divisor specialization

No Xi point occurs in the statement.  The parameter derivative is taken at the source-neutral
character before divisor evaluation.  It constructs a carrier; it does not assert that the
carrier lands in the fixed Sonin target or that its target coface is a boundary.

### H4 — trace-class correction could erase the jet

False if clause 3 holds: the jet coface is a nonzero multiple of `G_6`, which is not trace class.
Trace-class correction can change its representative but cannot erase its principal class.

### H5 — literature collision

Macaev/Lorentz ideals, Dixmier traces, logarithmic ideal scales, and generalized eigenvectors are
parent mathematics.  Current primary-source search located their general theory but no result
combining the corrected Gamma-six Mobius source, literal Wold clock, reflected exponent jet,
and the fixed Route-L source/physical obstruction.  Priority remains unverified.

**Preliminary verdict:** `SURVIVES PRELIMINARY ATTACK` as a project-specific source theorem;
novelty and significance depend on clauses 3--5, not the scalar differentiation.

### H6 — affine uniqueness as first frozen

**Failed.**  The coface annihilates every multiple of `G_6`, so it cannot distinguish
`J_6` from `J_6+bG_6`.  Clause 4 was too strong.  The corrected theorem is the exact affine
classification modulo the one-dimensional Wold eigenspace.  The actual exponent derivative, not
the coface alone, supplies the normalization `b=0`.  No later claim may silently use absolute
uniqueness.

### H7 — prior-corpus neutral-jet collision

General neutral-character differentiation is not new inside this corpus: Route T already
formalizes source-horizontal Wold neutral jets in
`SourceHorizontalWoldNeutralJetBridge.lean`.  This kills any novelty claim for the bare principle
"differentiate exponent to obtain a logarithmic jet."  What survives is narrower and
source-specific: exact Gamma-six approximation-number placement, escape from the proved
trace-ideal/Sonin obstruction, logarithmic nuclear control of the complete corrected Möbius tensor
remainder, and the non-trace-class full-source coface theorem.  External priority for that package
remains unverified.

## Dependency-closed paper proof

Write `d_n=d(n)`, `g_n=6^{-d_n}`, `c=log 6`, and let `S_6` be the isometry which sends coordinate
`n` to `W(n)`.  Existing arithmetic gives

\[
d_{W(n)}=d_n+1,\qquad g_{W(n)}=g_n/6.
\]

### 1. Source derivatives and exact Jordan coface

For the forward and reflected scalar shell families

\[
F_\delta(n)=g_n^{1-\delta},\qquad R_\delta(n)=g_n^{1+\delta},
\]

ordinary real differentiation at `delta=0` gives

\[
F'_0(n)=-\log(g_n)g_n=d_nc g_n=j_n,
\qquad R'_0(n)=\log(g_n)g_n=-j_n.
\]

Since Wold compression of a diagonal multiplier reads it at `W(n)`, coordinatewise

\[
\begin{aligned}
(C_6J_6)(n)-\frac16J_6(n)
 &= (d_n+1)c\frac{g_n}{6}-\frac16d_nc g_n\\
 &=\frac c6g_n.
\end{aligned}
\]

Equality of bounded diagonal multipliers proves the operator identity.  Boundedness follows from
the monotone shell sequence `m c 6^{-m}` for `m>=3`: indeed
`(m+1)c6^{-(m+1)} <= mc6^{-m}` is equivalent to `m+1<=6m`.

### 2. Exact ideal placement

The same monotonicity makes the approximation numbers of `J_6` exactly `j_n`.  On the last
coordinate of shell `m`, namely `n_m=6^{m+1}-217`,

\[
(n_m+1)a_{n_m}(J_6)
  =(6^{m+1}-216)mc6^{-m}
  =mc(6-216\,6^{-m}),
\]

which is unbounded.  Hence no constant can satisfy the weak-`S_1` bound
`a_n(J_6)<=C/(n+1)`, so `J_6` is not weak Schatten one.

For `epsilon>0`, the multiplier of `J_6G_6^epsilon` is
`mc6^{-(1+epsilon)m}` on a shell of cardinality `5*6^m`.  Its trace norm is therefore

\[
5c\sum_{m>=3}m6^{-\epsilon m}<\infty.
\]

Thus every positive power regularization is trace class.  This proves the sharp logarithmic
endpoint assertion without an asymptotic replacement of the literal shell model.

### 3. Affine classification and orientation

Let an affine shell jet have multiplier `h_m=(am+b)6^{-m}`.  Then

\[
h_{m+1}-\frac16h_m=\frac a6\,6^{-m}.
\]

It has coface `(c/6)G_6` iff `a=c`; hence it is exactly `J_6+bG_6`.  The free term is precisely the
kernel generated by the ordinary Wold eigenoperator.  The derivatives in part 1 have `b=0` and
opposite signs, proving the corrected classification and orientation statement.

### 4. Actual leading tensor source

Let `v_6` be the already constructed nonzero first surviving Gamma-six Mobius tensor vector and
let `E_6` be its coefficient-faithful diagonal embedding.  Define
`mathcal J_6=E_6 J_6`.  Rectangular Wold compression commutes with this constant block embedding,
so part 1 gives the exact, pre-quotient equation

\[
\mathcal C_6(\mathcal J_6)-\frac16\mathcal J_6
   =\frac c6\,E_6G_6
   =\frac c6\,\mathcal G_6^{\rm principal}.
\]

The existing normalized block reader is a left inverse to `E_6`; consequently trace-class
membership of `mathcal J_6` in any endpoint ideal would imply the corresponding false scalar
membership.  The right-hand side is therefore the actual nonzero coefficient-faithful principal
class, not a formal carrier with a declared coefficient.

### 5. Complete corrected source

Let `R_n` be the already constructed corrected-source remainder column, so
`sum_n ||R_n||<infinity`, and put

\[
R_n^{\log}=d_ncR_n.
\]

This logarithmically weighted correction remains summable.  To see this without discarding exact
shell multiplicity, write `m=j+3`.  Previous source estimates majorize

\[
6^m\lVert R_m\rVert
 \le A q^j+Bq^{2j},\qquad q=(6/7)^{1/2}<1.
\]

Multiplication by `mc=(j+3)c` leaves both geometric series summable.  Exact shell cardinality
`5*6^m` therefore gives `sum_n ||R_n^{log}||<infinity`.  The vector-diagonal operator
`mathcal R_6^{log}` is rectangular trace class.

Define the complete logarithmic source jet

\[
\mathcal J_6^{\rm full}=\mathcal J_6+\mathcal R_6^{\log}.
\]

Its difference from the leading logarithmic jet is trace class.  Wold compression preserves
rectangular trace class, as does scalar multiplication.  Since the complete corrected source is
`mathcal G_6^{full}=mathcal G_6^{principal}+mathcal R_6`, subtraction from the exact principal
identity yields

\[
\mathcal C_6(\mathcal J_6^{full})-\frac16\mathcal J_6^{full}
  -\frac c6\mathcal G_6^{full}\in\mathcal L^1_{rect}.
\]

Because `(c/6)mathcal G_6^{principal}` is not trace class while every displayed correction is,
the complete logarithmic coface is not trace class and represents exactly
`(c/6)[mathcal G_6^{full}]` in the rectangular principal quotient.  This proves clauses 1--5 for
the literal corrected Mobius tensor source.

**Paper verdict:** `PROVED UNCONDITIONALLY`; no Xi zero, RH-equivalent premise, target quotient,
or `1/Xi` multiplier occurs.  Claim is a source-carrier theorem, not RH.

## Lean realization

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerGammaSixLogarithmicWoldJordanTransgression.lean`
formalizes the dependency-closed package on the literal source objects:

- forward/reflected exponent derivatives at neutral grade;
- exact logarithmic Wold coface and affine classification modulo the principal eigenspace;
- exact approximation numbers, failure of weak Schatten one, and trace class after every positive
  shell-power regularization;
- actual leading-tensor lift with coefficient-faithful principal coface;
- logarithmically weighted corrected-source remainder as a rectangular trace-class operator;
- full corrected logarithmic coface equal to `(log 6 / 6)` times the literal full source modulo
  rectangular trace class, and proof that this coface is not trace class.

Verification: direct `lake env lean` pass; leaf-only `lake build
GaloisForLFunctions.RHTower.Deninger.DeningerGammaSixLogarithmicWoldJordanTransgression` pass; capstone
axiom audit reports only `propext`, `Classical.choice`, and `Quot.sound`; umbrella import wired
without umbrella build.  Global no-build lint reaches pre-existing unrelated unreachable-module
errors; new module itself contains no forbidden declaration.

## Exact open core after this conjecture

Even if proved, this theorem does not prove RH.  It replaces the impossible trace-class coface by
the first source-natural noncompact coface.  Remaining Route-L implication is:

> construct the actual place-marked Rost--Schmid/Meyer-to-Sonin comparison on this logarithmic
> Jordan domain, prove it preserves the ordinary trace-class subobject, and identify the Jordan
> coface with the fixed Gamma/co-Poisson target boundary on every multiplicity-labelled Xi fibre.

The trace-ideal obstruction no longer applies to that comparison because its distinguished
coface is not trace class.  A comparison defined only by quotienting the target, multiplying by
`1/Xi`, or declaring the receiver a boundary remains circular.

## Gates

- [x] internal frontier and failed-route audit
- [x] primary parent-literature collision search
- [x] conjecture frozen before proof search
- [x] hostile preliminary attack
- [x] dependency-closed paper proof
- [x] exact unconditional Lean theorem
- [x] targeted leaf verification and umbrella wiring
