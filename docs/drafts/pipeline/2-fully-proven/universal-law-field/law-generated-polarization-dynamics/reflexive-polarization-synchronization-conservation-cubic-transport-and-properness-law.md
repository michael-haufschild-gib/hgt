# Reflexive polarization synchronization, conservation, cubic transport, and properness law

- **ID:** ULF-LGPD-2
- **Stage:** 2 — fully proven on paper
- **Type:** UNIVERSAL-LAW FIELD THEOREM / NONLINEAR SOURCE-COHERENCE MECHANISM
- **Parent:** `legendre-residual-transduction-fusion-work-and-cubic-response-law.md`
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM NOT OBJECT]
  [NONLINEAR QUOTIENT--FUSION] [EXACT POWER CONSERVATION]
  [CUBIC TRANSPORT] [GLOBAL AMPLIFICATION SELECTION] [LEAN-CERTIFIED CORE] [NOT RH]`

## 1. Question and higher pivot

Suppose several mathematical organs report failures produced by one source state.  Each organ has
its own source-generated positive polarization and therefore its own locally optimal correction.
The source, however, can execute only one intervention.  What law relates the local corrections to
the executable fused correction?

The answer is not another obstruction object.  It is a four-part mechanism:

1. local polarizations convert local residual covectors into local intervention velocities;
2. their sum produces the unique source-executable velocity;
3. an exact Pythagorean identity conserves total correction power as executable power plus
   synchronization tension;
4. third response is the only nonlinear carrier that can move this tension under fused execution.

This theorem fuses law-generated polarization dynamics with source-coherent synchronization.  Its
static identity specializes to coordinate-free quotient--fusion genesis, but its transport and
global amplification laws are not contained in the static projection theorem.

## 2. Pointwise constitutive data

Let `V` be a finite-dimensional real vector space and let `I` be a finite nonempty channel set.
For every `i in I`, let

\[
 H_i:V\longrightarrow V^*
 \tag{RPS.1}
\]

be symmetric and positive definite.  Let `e_i in V*` be the current channel residual and define
the local intervention velocity by

\[
 H_i v_i=e_i.
 \tag{RPS.2}
\]

Put

\[
 H=\sum_iH_i,
 \qquad e=\sum_i e_i,
 \qquad Hv=e.
 \tag{RPS.3}
\]

The vector `v` is the unique intervention executable by the common source.  Define independent
local power, executable fused power, and synchronization tension by

\[
 \mathcal P_{\mathrm{loc}}=\sum_iH_i(v_i,v_i),
 \qquad
 \mathcal P_{\mathrm{fus}}=H(v,v),
 \tag{RPS.4}
\]

\[
 \mathcal S=\sum_iH_i(v_i-v,v_i-v).
 \tag{RPS.5}
\]

### Theorem 2.1 — nonlinear synchronization conservation

The relative velocity packet satisfies the balance law

\[
 \boxed{\sum_iH_i(v_i-v)=0.}
 \tag{RPS.6}
\]

The local and executable powers obey the exact conservation identity

\[
 \boxed{
 \mathcal P_{\mathrm{loc}}
 =\mathcal P_{\mathrm{fus}}+\mathcal S.}
 \tag{RPS.7}
\]

Consequently,

\[
 \mathcal S\ge0,
 \qquad
 \mathcal S=0\iff v_i=v\ \text{for every }i.
 \tag{RPS.8}
\]

Moreover, the data `(H_i,v,(v_i-v))` reconstruct every residual:

\[
 \boxed{e_i=H_i\bigl(v+(v_i-v)\bigr).}
 \tag{RPS.9}
\]

Thus executable intervention plus balanced relative packet is jointly reconstructive.  Fused
power alone sees only the total residual and can miss exact cancellation among channels.

#### Proof

Equations `(RPS.2)--(RPS.3)` give

\[
 \sum_iH_i(v_i-v)=\sum_ie_i-Hv=e-e=0,
\]

which proves `(RPS.6)`.  Expanding `(RPS.5)` and using symmetry gives

\[
\begin{aligned}
 \mathcal S
 &=\sum_iH_i(v_i,v_i)
   -2\sum_iH_i(v_i,v)+\sum_iH_i(v,v)\\
 &=\mathcal P_{\mathrm{loc}}-2e(v)+H(v,v)\\
 &=\mathcal P_{\mathrm{loc}}-\mathcal P_{\mathrm{fus}}.
\end{aligned}
\]

This proves `(RPS.7)`.  Positive definiteness proves nonnegativity and the zero classification.
Equation `(RPS.9)` is `(RPS.2)` after writing `v_i=v+(v_i-v)`.  QED.

## 3. Reflexive formation dynamics

Let `U subset V` be open.  For every channel let

\[
 A_i:U\longrightarrow\mathbb R
 \tag{RPS.10}
\]

be `C^3` and strictly convex, with Hessian `H_i=d^2A_i` and third response
`T_i=d^3A_i`.  Fix source-marked targets `m_i in V*` and put

\[
 e_i=m_i-dA_i(\theta),
 \qquad
 H=\sum_iH_i,
 \qquad
 e=\sum_i e_i.
 \tag{RPS.11}
\]

Run the fused source correction

\[
 \dot\theta=v=H^{-1}e,
 \qquad
 v_i=H_i^{-1}e_i.
 \tag{RPS.12}
\]

All quantities in Section 2 now vary along the same source history.

### Theorem 3.1 — cubic transport of synchronization tension

Along `(RPS.12)`,

\[
 \boxed{
 \dot{\mathcal P}_{\mathrm{loc}}
 =-2\mathcal P_{\mathrm{fus}}
  -\sum_iT_i(v,v_i,v_i),}
 \tag{RPS.13}
\]

\[
 \boxed{
 \dot{\mathcal P}_{\mathrm{fus}}
 =-2\mathcal P_{\mathrm{fus}}
  -\sum_iT_i(v,v,v),}
 \tag{RPS.14}
\]

and therefore

\[
 \boxed{
 \dot{\mathcal S}
 =\sum_i\bigl(T_i(v,v,v)-T_i(v,v_i,v_i)\bigr).}
 \tag{RPS.15}
\]

Writing `delta_i=v_i-v`, this becomes

\[
 \boxed{
 \dot{\mathcal S}
 =-\sum_i\left(2T_i(v,v,\delta_i)+T_i(v,\delta_i,\delta_i)\right).}
 \tag{RPS.16}
\]

Thus second response creates the synchronization tension, while third response transports it.
Positive Hessian data alone determine no sign for its motion.

#### Proof

Differentiating the channel residual and Hessian along `dot theta=v` gives

\[
 \dot e_i=-H_iv,
 \qquad
 \dot H_i=T_i(v,-,-).
 \tag{RPS.17}
\]

Differentiate `H_iv_i=e_i`:

\[
 H_i\dot v_i=-H_iv-T_i(v,v_i,-).
 \tag{RPS.18}
\]

Pairing with `v_i` and differentiating `H_i(v_i,v_i)` yields

\[
\begin{aligned}
 \frac d{dt}H_i(v_i,v_i)
 &=T_i(v,v_i,v_i)+2H_i(\dot v_i,v_i)\\
 &=-2H_i(v,v_i)-T_i(v,v_i,v_i).
\end{aligned}
\]

Summing and using `sum_i H_i(v,v_i)=sum_i e_i(v)=e(v)=P_fus` proves
`(RPS.13)`.  The one-potential correction-power identity applied to `A=sum_i A_i` proves
`(RPS.14)`; it also follows by differentiating `Hv=e`, using `dot e=-e` and
`dot H=sum_iT_i(v,-,-)`.  Subtracting `(RPS.14)` from `(RPS.13)` and using
`S=P_loc-P_fus` proves `(RPS.15)`.  Expanding `v_i=v+delta_i` in the symmetric trilinear form
proves `(RPS.16)`.  QED.

### Corollary 3.2 — quadratic formations preserve unresolved local failure

If every channel potential is quadratic, then every `T_i=0` and

\[
 \boxed{\dot{\mathcal S}=0.}
 \tag{RPS.19}
\]

The total residual still obeys `dot e=-e`, but local residual cancellation is not repaired.  More
precisely, every `delta_i=v_i-v` is constant and

\[
 e_i(t)=H_i\bigl(e^{-t}v(0)+\delta_i(0)\bigr).
 \tag{RPS.20}
\]

Hence `e(t) -> 0` while nonzero local residuals can converge to the balanced packet
`H_i delta_i`, whose sum is zero.  Total selection and joint selection are different laws.

#### Proof

When `T_i=0`, equations `(RPS.18)` and the corresponding fused identity give
`dot v_i=-v` and `dot v=-v`.  Therefore `dot delta_i=0`, `v(t)=e^{-t}v(0)`, and `(RPS.20)`
follows from `e_i=H_iv_i`.  Equation `(RPS.6)` makes the limiting packet balanced.  QED.

## 4. Global amplification and exact joint selection

Keep the pointwise polarizations `H_i` fixed and amplify every source residual by the same
`r>=0`:

\[
 e_i^{(r)}=r e_i.
 \tag{RPS.21}
\]

Let the corresponding velocities and powers carry a superscript `(r)`.

### Theorem 4.1 — homogeneous properness

For every `r>=0`,

\[
 v_i^{(r)}=rv_i,
 \qquad v^{(r)}=rv,
 \tag{RPS.22}
\]

and

\[
 \boxed{
 \mathcal P_{\mathrm{loc}}^{(r)}=r^2\mathcal P_{\mathrm{loc}},
 \quad
 \mathcal P_{\mathrm{fus}}^{(r)}=r^2\mathcal P_{\mathrm{fus}},
 \quad
 \mathcal S^{(r)}=r^2\mathcal S.}
 \tag{RPS.23}
\]

Fix `d>1`.  Then

\[
 \boxed{
 \sup_{n\ge0}\mathcal P_{\mathrm{loc}}^{(d^n)}<\infty
 \iff
 e_i=0\text{ for every }i.}
 \tag{RPS.24}
\]

The two weaker boundedness laws separate exactly:

\[
 \sup_n\mathcal P_{\mathrm{fus}}^{(d^n)}<\infty
 \iff \sum_i e_i=0,
 \tag{RPS.25}
\]

\[
 \sup_n\mathcal S^{(d^n)}<\infty
 \iff v_i=v\text{ for every }i.
 \tag{RPS.26}
\]

Thus bounded complete local power is the conjunction of total neutrality and synchronization.  It
selects the whole target packet, whereas either fused power or incompatibility alone leaves a
nontrivial blind sector.

#### Proof

Linearity and invertibility of the `H_i` and `H` give `(RPS.22)`.  Substitution in
`(RPS.4)--(RPS.5)` gives `(RPS.23)`.  If `P_loc>0`, then
`P_loc^(d^n)=d^(2n)P_loc -> infinity`; if it is zero, every term
`H_i(v_i,v_i)` is zero, hence every `v_i=0` and every `e_i=0`.  This proves `(RPS.24)`.
The same argument applied to `P_fus` and `S`, followed by their zero classifications, proves
`(RPS.25)--(RPS.26)`.  QED.

## 5. Functional-equation and recovery boundary

An invertible affine reparametrization of `V` transports covectors contragrediently, Hessians by
congruence, and velocities covariantly.  Every scalar in `(RPS.4)--(RPS.5)` and every identity
above is unchanged.  Adding affine gauges to the potentials shifts reporters and targets together
and changes neither residuals nor higher response.  Therefore a functional equation acting by
reparametrization plus affine gauge is information-neutral on synchronization power.

A common split recovery that is sufficient for every channel likewise preserves the channel
relative entropies and their Hessian germs.  It transports the law but cannot make nonzero
synchronization tension vanish.  A nonsufficient observer can lower the measured power only by
moving the missing amount into its recovery deficit.  This section is a consequence of the
existing packet-recovery theorems; it is not used in Theorems 2.1--4.1.

## 6. What is new to the field mechanism

The theorem yields the demanded cross-organ sequence without identifying the organs:

1. **common grammar:** local residual -> source polarization -> local velocity -> fused executable
   velocity;
2. **genuine fusion:** local Newton/Fisher corrections do not add; their Hessian-weighted barycenter
   is the only common-source correction;
3. **conservation:** local power = executable power + synchronization tension;
4. **fourth-organ prediction:** cubic response is exactly the transport law for incompatibility;
5. **global formation/properness:** source amplification turns bounded complete power into joint
   channel selection.

This is stronger than the scalar shared-gauge theorem.  At every point its static part is an
orthogonal-projection identity, but the polarizations themselves are generated by the current
source state, and `(RPS.15)` governs how the quotient--fusion defect moves under the resulting
nonlinear execution.

## 7. Hostile conjecture loops

1. **The static conservation identity is new mathematics. — False.**  Pointwise it is weighted
   Pythagoras/ANOVA and is contained abstractly in coordinate-free quotient--fusion genesis.
   **Survivor:** the reflexive cubic transport and amplification selector.
2. **Fused selection resolves every channel. — False.**  Corollary 3.2 gives balanced nonzero local
   residuals even while the total residual converges to zero.
3. **Positive Hessians dissipate synchronization tension. — False.**  Quadratic positive channels
   conserve it exactly; cubic response has no universal sign.
4. **Synchronization alone selects neutrality. — False.**  All local velocities may agree at one
   common nonzero velocity.  Fused neutrality and synchronization are independent clauses.
5. **Total neutrality alone selects every target. — False.**  Nonzero local residuals may cancel.
6. **Any amplification is physical. — False.**  Theorem 4.1 is a consumer.  An application must
   derive the common scale orbit from a marked source formation before endpoint specialization.
7. **Functional equation supplies selection. — False.**  Reversible reparametrization preserves all
   three powers.  It cannot create the missing boundedness premise.

## 8. Parent mathematics and scope

The ingredients are established: Hessian/natural-gradient dynamics, multiobjective and federated
Newton methods, weighted Pythagorean decompositions, Bregman work, and proper homogeneous actions.
The field content is their constitutive coupling: one source generates every channel reporter and
polarization; independent local corrections are non-executable; enforcing one executable
intervention produces a conserved synchronization tension; third response transports it; source
amplification makes the complete power a selector.

No external priority claim is made.  The theorem is finite-dimensional and pre-target.  It does
not construct an RH source realization, a cofinal inverse polarization, or the arithmetic bounded
power law.  Those remain the exact application gates.

## 9. Lean boundary

`GaloisForLFunctions.HTGeometry.ConstitutiveReflexivePolarizationSynchronization` certifies,
without new axioms or placeholders:

1. weighted local/fused/tension conservation;
2. balance and zero/synchronization classification;
3. homogeneous amplification and bounded-orbit selection;
4. the algebraic cubic transport identity;
5. a closed quadratic witness where fused power can vanish while local mismatch persists.

The analytic chain-rule derivation of `(RPS.13)--(RPS.16)` remains paper-certified; Lean certifies
its exact algebraic rate identity after the response equations have supplied the two instantaneous
rates.  No Stage-3 card claims a formalized Fréchet chain rule.

## Log

- 2026-08-14 — extracted by fusing source-coherent synchronization with law-generated Hessian
  correction; static rediscovery isolated, dynamic cubic transport and global joint selection
  closed on paper.
- 2026-08-14 — exact finite scalar-polarization core Lean-certified and wired into the
  `UniversalLawField` umbrella.
