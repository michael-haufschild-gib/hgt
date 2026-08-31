# Completion primitive, variance--Dirichlet conservation, and positive formation-action law

- **ID:** ULF-TAFM-16
- **Stage:** 3-formalized
- **Type:** THEOREM CANDIDATE / GLOBAL FORMATION-PROPERNESS MECHANISM
- **Source:** ULF-TAFM-15; literal Suzuki completed Abel and aligned transition-energy welds;
  online variance, discrete Dirichlet action, and exact one-dimensional current integration
- **Statement:** Anchored formation variance is exactly Dirichlet action of the formation
  potential. Every additive completion current has a canonical harmonic primitive, so completed
  source becomes pure connection current and its square is exact positive formation-energy
  production. For the literal Suzuki source, RH is equivalent to uniform boundedness of increments
  of this monotone divisor-free completed formation energy.
- **Status:** `[PAPER PROOF COMPLETE] [HOSTILE AUDIT PASSED] [BRIDGE] [NOT RH]`

## Goal

Remove two artificial obstructions left by ULF-TAFM-15:

1. the completed terminal field `R_N` should not remain an external error if it is itself an
   integrable scale current; and
2. squaring the source in Gamma/Xi should not be treated as phase loss only. It should be positive
   production of a route-independent formation energy.

Required theorem must create one monotone global action, prove exact local production, and express
the existing RH endpoint solely as bounded production of that source action.

## Gates

- [x] 0 → 1 in-progress: duplicate search clean; conjecture frozen; generic Lean scratch passes
- [x] 1 → 2 fully-proven: complete generic and literal paper proof; audit indices,
  coefficients, and the exact properness boundary
- [x] 2 → 3 formalized: direct Lean checks, targeted leaf builds, axiom audit, umbrella imports
- [ ] 3 → 4 publication-ready: unconditional arithmetic upper bound on formation production

## 1. Anchored variance and scale action

Retain the anchored potential and current of ULF-TAFM-15:

\[
 M_N(a)=\frac{3a_2+\sum_{j=3}^{N}a_j}{N+1},
 \qquad H_N(a)=a_{N+1}-M_N(a).                           \tag{VDC.1}
\]

Define the unnormalised anchored variance

\[
 V_N(a):=
 3a_2^2+\sum_{j=3}^{N}a_j^2-(N+1)M_N(a)^2.              \tag{VDC.2}
\]

For an arbitrary scale potential `P`, define its Dirichlet action

\[
 \mathscr D_N(P):=
 \sum_{k=2}^{N-1}(k+1)(k+2)(P_{k+1}-P_k)^2.             \tag{VDC.3}
\]

## 2. Generic variance--Dirichlet theorem

### Theorem ULF-TAFM-16A — positive formation action

For every real formation history `a` and `N≥2`:

1. **Centered variance identity.**

   \[
   V_N(a)=3(a_2-M_N)^2+
   \sum_{j=3}^{N}(a_j-M_N)^2\ge0.                        \tag{VDC.4}
   \]

2. **Constant-gauge quotient.** For every constant `c`,

   \[
   V_N(a+c)=V_N(a).                                      \tag{VDC.5}
   \]

3. **Exact production law.**

   \[
   V_{N+1}(a)-V_N(a)=\frac{N+1}{N+2}H_N(a)^2.            \tag{VDC.6}
   \]

4. **Variance--Dirichlet conservation.**

   \[
   V_N(a)=\mathscr D_N(M(a)).                             \tag{VDC.7}
   \]

Thus positivity after constant-phase quotient is not imposed by a receiver: it is exact production
of source dispersion along scale.

### Proof

The total anchored weight in `(VDC.1)` is `N+1`. Expanding the right side of `(VDC.4)` gives

\[
3a_2^2+\sum a_j^2
-2M_N\left(3a_2+\sum a_j\right)+(N+1)M_N^2.             \tag{VDC.8}
\]

The parenthesis is `(N+1)M_N`, so `(VDC.8)` is `(VDC.2)`. Nonnegativity and constant-gauge
invariance follow immediately.

Let `n=N+1`, `m=M_N`, and `h=H_N=a_{N+1}-m`. ULF-TAFM-15 gives

\[
M_{N+1}=m+\frac{h}{n+1}.                                \tag{VDC.9}
\]

The raw second moment gains `(m+h)^2`; substituting `(VDC.9)` into `(VDC.2)` gives

\[
V_{N+1}-V_N
=(m+h)^2-(n+1)\left(m+\frac{h}{n+1}\right)^2+nm^2
=\frac{n}{n+1}h^2,                                      \tag{VDC.10}
\]

which is `(VDC.6)`. Since `H_N=(N+2)(M_{N+1}-M_N)`, `(VDC.6)` becomes

\[
V_{N+1}-V_N=(N+1)(N+2)(M_{N+1}-M_N)^2.                 \tag{VDC.11}
\]

Now `V_2=0`. Summing `(VDC.11)` from `2` to `N-1` proves `(VDC.7)`. ∎

## 3. Canonical integration of completion currents

For any correction current `r : ℕ→ℝ`, define its harmonic primitive

\[
 U_N(r):=\sum_{k=2}^{N-1}\frac{r_k}{k+2},               \tag{VDC.12}
\]

and completed potential

\[
 \widehat P_N(a,r):=M_N(a)+U_N(r).                       \tag{VDC.13}
\]

### Theorem ULF-TAFM-16B — completion lift and positive completed action

For every `N≥2`:

1. **Exact primitive law.**

   \[
   U_{N+1}(r)-U_N(r)=\frac{r_N}{N+2}.                    \tag{VDC.14}
   \]

2. **Pure completed current.**

   \[
   (N+2)(\widehat P_{N+1}-\widehat P_N)=H_N(a)+r_N.      \tag{VDC.15}
   \]

3. **Completed Dirichlet energy.** Put

   \[
   \widehat V_N(a,r):=\mathscr D_N(\widehat P(a,r)).     \tag{VDC.16}
   \]

   Then

   \[
   \widehat V_{N+1}-\widehat V_N
   =\frac{N+1}{N+2}(H_N(a)+r_N)^2\ge0.                  \tag{VDC.17}
   \]

Hence every additive completion on one-dimensional scale space is an exact potential lift, and
the completed energy is monotone. There is no separate algebraic correction obstruction; only the
size of its primitive or current can fail properness.

### Proof

Equation `(VDC.14)` is the last-term identity for the finite sum `(VDC.12)`. Add it to the anchored
connection law `(ASC.3)` to obtain `(VDC.15)`. The successor increment of `(VDC.3)` is

\[
(N+1)(N+2)(\widehat P_{N+1}-\widehat P_N)^2.             \tag{VDC.18}
\]

Substitute `(VDC.15)` into `(VDC.18)` to get `(VDC.17)`. Positivity proves monotonicity. ∎

## 4. Literal Suzuki completion

Take

\[
a_N=\operatorname{suzukiCheckpointAffineSlope}(N),
\qquad r_N=R_N,                                         \tag{VDC.19}
\]

where `R_N` is the exact terminal correction isolated in ULF-TAFM-15. Define

\[
 \widehat P_N^{\rm Suz}:=\widehat P_N(a,R),
 \qquad
 \widehat V_N^{\rm Suz}:=\mathscr D_N(\widehat P^{\rm Suz}).\tag{VDC.20}
\]

Let `A_{N+1}` denote the literal completed Abel source.

### Theorem ULF-TAFM-16C — completed Abel as positive formation production

For every `N≥2`:

1. **Correction-free completed current.**

   \[
   \mathcal A_{N+1}
   =(N+2)(\widehat P^{\rm Suz}_{N+1}-\widehat P^{\rm Suz}_N).\tag{VDC.21}
   \]

2. **Exact positive production.**

   \[
   \widehat V^{\rm Suz}_{N+1}-\widehat V^{\rm Suz}_N
   =\frac{N+1}{N+2}\mathcal A_{N+1}^2.                  \tag{VDC.22}
   \]

3. **Gamma production law.** Whenever outgoing charge is nonzero,

   \[
   \mathcal E^\Gamma_{N+1}
   =\frac{\mathcal C_{N+1}}{Q_{N+1}^2}
    \frac{N+2}{N+1}
    \left(\widehat V^{\rm Suz}_{N+1}-\widehat V^{\rm Suz}_N\right).\tag{VDC.23}
   \]

4. **Uniform condition-number comparison.** Eventually,

   \[
   \frac{N+2}{N+1}\Delta\widehat V_N^{\rm Suz}
   \le \mathcal E^\Gamma_{N+1}
   \le K\frac{N+2}{N+1}\Delta\widehat V_N^{\rm Suz},  \tag{VDC.24}
   \]

   with the already-explicit constant
   `K=suzukiTransitionCoreAnchorConditionNumberBound`.

### Proof

ULF-TAFM-15 gives `A_{N+1}=H_N(a)+R_N`. Apply `(VDC.15)` to obtain `(VDC.21)` and `(VDC.17)` to
obtain `(VDC.22)`. Existing aligned-energy transport gives

\[
\mathcal E^\Gamma_{N+1}
=\mathcal C_{N+1}(\mathcal A_{N+1}/Q_{N+1})^2.           \tag{VDC.25}
\]

Substitute

\[
\mathcal A_{N+1}^2
=\frac{N+2}{N+1}\Delta\widehat V_N^{\rm Suz}            \tag{VDC.26}
\]

from `(VDC.22)` to prove `(VDC.23)`. Existing condition-number bounds say eventually

\[
Q_{N+1}^2\le\mathcal C_{N+1}\le KQ_{N+1}^2.             \tag{VDC.27}
\]

Combine `(VDC.23)` and `(VDC.27)` to get `(VDC.24)`. ∎

## 5. Exact RH properness coordinate

### Theorem ULF-TAFM-16D — bounded formation production iff RH

Define

\[
\operatorname{BFP}:\iff
\exists B\in\mathbb R\ \forall\text{ sufficiently large }N,
\widehat V^{\rm Suz}_{N+1}-\widehat V^{\rm Suz}_N\le B. \tag{VDC.28}
\]

Then

\[
\operatorname{RH}\iff\operatorname{BFP}.                \tag{VDC.29}
\]

### Proof

For `N≥2`, `(N+1)/(N+2)` lies in `[1/2,1]`. Therefore `(VDC.22)` gives

\[
\tfrac12\mathcal A_{N+1}^2
\le\Delta\widehat V_N^{\rm Suz}
\le\mathcal A_{N+1}^2.                                  \tag{VDC.30}
\]

Equivalently, `(VDC.24)` shows eventual boundedness of formation production is equivalent to
eventual boundedness of aligned Gamma energy. ULF-TAFM-15C, using the existing closed endpoint,
proves the latter equivalent to RH. This proves `(VDC.29)`. ∎

The important change from ULF-TAFM-15C is removal of transition geometry and charge from the final
property. The exact remaining source theorem is now:

> Completed formation Dirichlet energy has uniformly bounded local production.

This is a global formation/properness law in the new field, not another statement about one
post-selected divisor.

## 6. Interpretation across the full frontier

- **Positivity:** squared route energies are local production of gauge-quotiented source variance.
- **Recurrence:** bounded or slowly growing completed action constrains current production even
  when the scalar observer returns.
- **No-gos:** every failed bounded receiver identifies a place where completed action production
  cannot be controlled or transported.
- **Hypertranscendence/noncompactness:** an unbounded independent channel tower is one mechanism by
  which completed Dirichlet production escapes every compact action chamber.
- **Functional equation:** an information-neutral action may change the potential gauge but must
  preserve the completed current and its production law.

These are consequences of one conservation mechanism, not claims that route objects are equal.

## 7. Hostile boundary

- Monotonicity of completed formation energy is unconditional but does not bound its increments.
- A correction current is algebraically exact on the scale ray; its primitive may still escape.
- The RH equivalence `(VDC.29)` is a closed selection coordinate, not proof of BFP.
- No sign is recovered from Gamma/Xi energy; orientation remains in the unsquared completed current.
- The next research task must derive BFP from an independent source law or falsify this selection
  architecture, not manufacture another equivalent bounded receiver.

## Log

- 2026-08-31 — frozen after ULF-TAFM-15 exposed correction current and aligned-energy square.
- 2026-08-31 — generic variance--Dirichlet, completion-primitive, and monotone completed-action
  proofs completed in Lean scratch; literal proof reduced to certified ULF-15 and condition-number
  identities.
- 2026-08-31 — hostile audit passed: centered-variance weights, successor coefficients,
  completion primitive, Gamma rescaling, and eventual condition comparison are exact; promoted to
  Stage 2 with the bounded-production obligation explicitly open.
- 2026-08-31 — generic and literal laws formalized in Lean; targeted leaf builds and seventeen-
  declaration axiom audit passed; RH equivalence remains a selection coordinate, not proof of
  bounded production.
