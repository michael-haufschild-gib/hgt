# One-norm impossibility, formal-receiver collapse, and Wiener-scale fusion law

- **ID:** ULF-FSR-1
- **Stage:** 3-formalized
- **Type:** UNIVERSAL LAW-FIELD MECHANISM THEOREM
- **Parent:** ULF-WFM-1/2/3
- **Statement:** Faithful formation multiplication and ghost differentiation cannot coexist as
  bounded operations in one normed algebra; purely formal completion preserves algebra but has
  only the constant-term continuous complex receiver; the exact positive replacement is a scale of
  Wiener algebras on which multiplication, receivers, differentiation, Adams intervention, and
  exterior conservation obey typed exchange laws.
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [MECHANISM, NOT ROUTE]`
  `[ONE-NORM NO-GO + POSITIVE SCALE SURVIVOR] [FOUR-OPERATION FUSION]`
  `[RH COMPLETION GATE SHARPENED] [FULL SURFACE LEAN-CERTIFIED]`
  `[NOT RH]`

## 1. Why one completion was the wrong type

Finite Witt formation has five generated operations:

\[
 \text{multiplication/formation},\quad
 \text{exterior inversion},\quad
 \text{ghost differentiation},\quad
 \text{Adams substitution},\quad
 \text{receiver evaluation}.
 \tag{FSR1.1}
\]

ULF-WFM-3 correctly proves that a jointly convergent inverse pair remains inverse.  It does not
prove that every operation in `(FSR1.1)` can be bounded in the same norm.  The first theorem shows
that this stronger interpretation is impossible before arithmetic enters.

## 2. One-norm impossibility

Let `A` be a unital normed algebra over `C`, with submultiplicative norm.  Let `x in A` satisfy

\[
 x^n\ne0\qquad(n\ge1).
 \tag{FSR1.2}
\]

### Theorem 2.1 — no bounded faithful formation derivative

There is no bounded derivation

\[
 \delta:A\longrightarrow A
 \tag{FSR1.3}
\]

with `delta(x)=1`.

### Proof

Leibniz induction gives

\[
 \delta(x^n)=n x^{n-1}.
 \tag{FSR1.4}
\]

Multiplying by `x`, using submultiplicativity, and cancelling the nonzero norm of `x^n` gives

\[
 n\|x^n\|
 =\|x\delta(x^n)\|
 \le \|x\|\,\|\delta\|\,\|x^n\|,
 \qquad
 n\le \|x\|\,\|\delta\|.
 \tag{FSR1.5}
\]

The right side is fixed while `n` is arbitrary, a contradiction. QED.

Completeness was not used.  Thus no single normed algebra faithfully containing every polynomial
grade can make ordinary ghost differentiation bounded.  The legal exits are:

1. retain differentiation as an unbounded operator with its domain tower;
2. use a locally convex topology with multiple seminorms;
3. let differentiation move between different Banach fibres.

This theorem is independent of hypertranscendence.  The corpus's HT single-carrier theorem uses
nonzero modes at every jet grade to obstruct expanding dilation.  The present theorem instead uses
Leibniz and faithful formation powers to obstruct a bounded slice derivation.  Their conjunction
shows that both grading and ghost formation force scale geometry by different mechanisms.

## 3. Formal completion preserves laws but collapses analytic receivers

Give `C[[T]]` its `T`-adic topology.  A sequence tends to zero when its order tends to infinity;
in particular

\[
 c_nT^n\longrightarrow0
 \tag{FSR1.6}
\]

for every scalar sequence `(c_n)`, regardless of its growth.

### Theorem 3.1 — continuous complex receiver collapse

Every continuous unital `C`-algebra homomorphism

\[
 \chi:\mathbb C[[T]]\longrightarrow\mathbb C
 \tag{FSR1.7}
\]

is constant-term evaluation.  In particular `chi(T)=0`.

### Proof

Put `z=chi(T)`.  If `z!=0`, take `c_n=z^(-n)`.  Then `(FSR1.6)` tends to zero, while

\[
 \chi(c_nT^n)=z^{-n}z^n=1
 \tag{FSR1.8}
\]

for every `n`, contradicting continuity.  Hence `z=0`.

For `f=sum a_nT^n`, its polynomial truncations tend `T`-adically to `f`.  Continuity and
`chi(T)=0` give

\[
 \chi(f)=\lim_N\chi\left(\sum_{n\le N}a_nT^n\right)=a_0.
 \tag{FSR1.9}
\]

QED.

Thus the universal formal Witt completion is an exact algebraic source completion, but not the
analytic receiver completion needed by RH.  The missing step is receiver admission, not formal
existence of inverse packets.

## 4. Positive survivor: the Wiener receiver scale

For `R>0`, define

\[
 \mathcal W_R=
 \left\{f(T)=\sum_{n\ge0}a_nT^n:
        \|f\|_R:=\sum_{n\ge0}|a_n|R^n<\infty\right\}.
 \tag{FSR1.10}
\]

### Theorem 4.1 — Banach algebra and exact receiver spectrum

1. `W_R` is a unital Banach algebra under Cauchy multiplication and
   \[
    \|fg\|_R\le\|f\|_R\|g\|_R.
    \tag{FSR1.11}
   \]
2. For every `|z|<=R`, evaluation
   \[
    \operatorname{ev}_z(f)=\sum_na_nz^n
    \tag{FSR1.12}
   \]
   is a continuous unital character of norm at most one.
3. Every continuous unital complex character of `W_R` is `ev_z` for a unique `z` with
   `|z|<=R`.

### Proof

Absolute convolution and Tonelli give `(FSR1.11)`; completeness is the weighted `ell^1`
completeness after the isometry `(a_n) -> (a_nR^n)`.

If `|z|<=R`, absolute convergence gives

\[
 |\operatorname{ev}_z(f)|
 \le\sum_n|a_n||z|^n\le\|f\|_R.
 \tag{FSR1.13}
\]

Conversely let `chi` be continuous and put `z=chi(T)`.  Since

\[
 |z|^n=|\chi(T^n)|\le\|\chi\|R^n,
 \tag{FSR1.14}
\]

one must have `|z|<=R`; otherwise `(|z|/R)^n` is unbounded.  Polynomials are dense in `W_R`, so
continuity gives `chi(f)=sum a_nz^n`.  Uniqueness follows from the value on `T`. QED.

The receiver disc is therefore reconstructed from the completion itself.  It is not an externally
declared observer set.

## 5. Operation-generated scale transport

Let `0<r<R` and write `D f=f'`.

### Theorem 5.1 — exact derivative collar loss

Differentiation is a bounded map

\[
 D:\mathcal W_R\longrightarrow\mathcal W_r,
 \qquad
 \boxed{\|Df\|_r\le{1\over R-r}\|f\|_R.}
 \tag{FSR1.15}
\]

### Proof

Put `q=r/R`.  For `n>=1`,

\[
 nq^{n-1}
 \le1+q+\cdots+q^{n-1}
 \le{1\over1-q}.
 \tag{FSR1.16}
\]

Therefore

\[
 \sum_{n\ge1}n|a_n|r^{n-1}
 \le{1\over R-r}\sum_{n\ge1}|a_n|R^n.
 \tag{FSR1.17}
\]

QED.

For an integer `q>=1`, define the Adams substitution

\[
 \Psi_qf(T)=f(T^q)=\sum_{n\ge0}a_nT^{qn}.
 \tag{FSR1.18}
\]

### Theorem 5.2 — Adams aperture transport

If `r^q<=R`, then

\[
 \Psi_q:\mathcal W_R\longrightarrow\mathcal W_r,
 \qquad
 \boxed{\|\Psi_qf\|_r\le\|f\|_R.}
 \tag{FSR1.19}
\]

### Proof

Directly,

\[
 \|\Psi_qf\|_r
 =\sum_n|a_n|r^{qn}
 \le\sum_n|a_n|R^n.
 \tag{FSR1.20}
\]

QED.

### Theorem 5.3 — ghost/Adams/receiver exchange

If `r^q<R`, both sides below belong to `W_r` and

\[
 \boxed{D\Psi_qf=qT^{q-1}\Psi_q(Df).}
 \tag{FSR1.21}
\]

More precisely,

\[
 \|D\Psi_qf\|_r
 \le {q r^{q-1}\over R-r^q}\|f\|_R.
 \tag{FSR1.22}
\]

For every `z` with `|z|^q<=R`,

\[
 \boxed{\operatorname{ev}_z(\Psi_qf)=\operatorname{ev}_{z^q}(f).}
 \tag{FSR1.23}
\]

### Proof

Termwise differentiation gives

\[
 D\Psi_qf
 =\sum_{n\ge1}qn a_nT^{qn-1}
 =qT^{q-1}\Psi_q(Df).
\]

For membership, choose `s` with `r^q<s<R`.  The collar theorem gives `Df\in W_s`,
and the Adams theorem then gives `\Psi_q(Df)\in W_r`; multiplication by the polynomial
`qT^{q-1}` preserves `W_r`.

Apply `(FSR1.15)` with inner radius `r^q` and multiply by `q r^(q-1)` to obtain
`(FSR1.22)`.  Absolute convergence at `z^q` gives `(FSR1.23)`. QED.

This is the exact fusion law: ramification transports receiver aperture, ghost formation consumes
a collar, and their order of application is conserved by `(FSR1.21)`.

## 6. Exterior/formation conservation inside the scale

Let `x=(x_1,...,x_m)` be a finite marked mode packet satisfying

\[
 |x_i|R<1\qquad(1\le i\le m).
 \tag{FSR1.24}
\]

Define

\[
 H_x(T)=\prod_i(1-x_iT)^{-1},
 \qquad
 E_x(-T)=\prod_i(1-x_iT).
 \tag{FSR1.25}
\]

### Theorem 6.1 — admitted finite Witt fusion

Both packets lie in `W_R` and

\[
 \boxed{E_x(-T)H_x(T)=1.}
 \tag{FSR1.26}
\]

Moreover

\[
 \|(1-x_iT)^{-1}\|_R={1\over1-|x_i|R},
 \tag{FSR1.27}
\]

so the admission margin is quantitative.

### Proof

The geometric series for each inverse converges absolutely in `W_R` by `(FSR1.24)` and has norm
`(FSR1.27)`.  Finite products remain in the Banach algebra.  Multiplication cancels every factor,
proving `(FSR1.26)`. QED.

Together, Theorems 4.1, 5.1--5.3, and 6.1 realize four structurally different organs in one typed
mechanism:

| organ | generated law |
|---|---|
| formation/exterior | exact inverse conservation `(FSR1.26)` |
| primitive ghost | derivative with forced collar loss `(FSR1.15)` |
| Adams/ramification | aperture transport `(FSR1.19)` |
| analytic receiver | exact character disc and covariance `(FSR1.23)` |

## 7. Fourth-organ prediction and joint reconstruction

The receiver theorem was not assumed in defining differentiation or Adams substitution.  It is a
consequence of the scale algebra and supplies the withheld prediction:

\[
 \boxed{
 \operatorname{Spec}_{\mathrm{cont}}(\mathcal W_R)=\overline D_R,
 \qquad
 \Psi_q^*(z)=z^q.}
 \tag{FSR1.28}
\]

Thus the scale parameter, receiver domain, and Adams action determine one another.  A character is
reconstructed by the single marked value `chi(T)`, while every source response is reconstructed
from its coefficient packet.  The exact conservation identity `(FSR1.21)` predicts how the ghost
seen by that receiver changes under Adams intervention.

This also supplies a sharp falsifier.  Any proposed realization that keeps `D(T)=1` bounded in one
faithful Banach fibre contradicts Theorem 2.1.  Any proposed Adams realization that fixes receiver
aperture while violating `z -> z^q` is not a realization of the generated law.

## 8. Correction to the RH completion gate

ULF-WFM-3 asked for one source-generated joint formation/exterior completion on
`Re(s)>1/2`.  That remains sufficient for zero exclusion, but it is too coarse as the field
architecture if ghost and Adams operations are also required.

The corrected source theorem is:

> construct a compatible scale or locally convex sheaf of Hausdorff multiplicative fibres over
> the strict-right half-plane; construct source-formed exterior/formation inverse sections in
> those fibres; let ghost and Adams operations move between fibres according to typed transition
> laws; and retain continuous point receivers covering every point of the half-plane.

If the completed formation and exterior sections multiply to one in a fibre carrying evaluation
at `s`, their evaluated product is one and the formation does not vanish at `s`.  Covering the
strict-right half-plane therefore gives the same RH implication as ULF-WFM-3, but no impossible
bounded-derivative premise is hidden in one norm.

This is still not an RH proof.  The missing arithmetic theorem is now sharper: construct the
source-compatible scale/sheaf and its exterior section.  Formal completion alone cannot do it by
Theorem 3.1; a single Banach algebra carrying all operations cannot do it by Theorem 2.1.

## 9. Hostile boundaries

1. **Fréchet escape is real.** Theorem 2.1 excludes one norm, not a multi-seminorm Fréchet
   algebra.  The Arens--Michael envelope of `C[T]` is `O(C)`; differentiation, substitutions, and
   point evaluations are continuous there because its seminorms encode radius loss.
2. **Unbounded-operator escape is real.** A closed densely defined derivative on one Banach fibre
   is not excluded.  Its domain tower is part of the law.
3. **Formal targets differ.** Theorem 3.1 concerns ordinary complex receivers.  Adic or nilpotent
   targets can receive nonzero topologically nilpotent images of `T`.
4. **Boundary evaluation is allowed.** `W_R` uses absolute coefficient summability, so evaluation
   remains continuous on `|z|=R`; weaker analytic Banach spaces can have different boundary
   behaviour.
5. **Adams may be an endomorphism in a fibre.** If `R^q<=R`, `(FSR1.19)` allows this.  The theorem
   claims covariant aperture transport, not mandatory strict shrinkage in every numeric chamber.
6. **No divisor is selected.** Scale covariance controls admission and exchange.  It does not
   construct the Euler-shell exterior companion or prove RH.

## 10. Parent mathematics and corpus delta

The analytic estimates are classical Wiener/Cauchy-scale mathematics.  Banach scales and loss of
derivatives are standard in Cauchy--Kovalevskaya and Nash--Moser theory.  The corpus already proves
a distinct HT scale-rigidity theorem and builds an analytic Wiener scale for transverse clock
equations.  Arens--Michael envelopes and Hadamard Witt topology are established parents.

The exact delta here is mechanism-level:

\[
 \boxed{
 \text{Witt formation/exterior}
 +\text{ghost derivation}
 +\text{Adams intervention}
 +\text{analytic receiver}
 \Longrightarrow
 \text{operation-indexed scale, not one norm}.}
 \tag{FSR1.29}
\]

Unlike the HT parent, no hypertranscendence or jet freeness is assumed.  Unlike the clock Wiener
parent, the receiver spectrum, Adams covariance, and exterior conservation are part of the same
theorem.  The result changes the open source construction demanded by ULF-WFM-3.

Primary references:

- Marsden, *A Banach Space of Analytic Functions for Constant Coefficient Equations of Evolution*,
  Canadian Math. Bulletin 11 (1968), 599--601;
- Pedchenko, *The Arens--Michael envelopes of the Jordanian Plane and `U_q(sl(2))`*,
  [arXiv:2009.06477](https://arxiv.org/abs/2009.06477), especially the universal envelope
  definition and the completion by submultiplicative seminorms;
- Bilu--Das--Howe, *Zeta statistics and Hadamard functions*,
  [arXiv:2012.14841](https://arxiv.org/abs/2012.14841).

## 11. Lean target

Formalize only unconditional closed kernels:

1. bounded-derivation one-norm impossibility;
2. algebraic derivative/Adams exchange on polynomials or power-series coefficients;
3. finite-radius monomial inequalities underlying `(FSR1.15)`, `(FSR1.19)`, and `(FSR1.22)`;
4. finite Witt admission/conservation if not already inherited from ULF-WFM-2.

Do not formalize the open arithmetic scale/sheaf construction.

## Log

- 2026-08-11 — one-topology conjecture attacked.  One-norm model and purely formal analytic
  receiver both failed exactly; Wiener-scale construction, character classification, exchange
  identity, and corrected RH completion gate closed on paper.

## 12. Formalization state and remaining Lean surface

Modules: `GaloisForLFunctions.HTGeometry.FormationScaleReceiver` (the original core) and
`GaloisForLFunctions.HTGeometry.WienerFormationScale` (the scale itself), both wired into
`GaloisForLFunctions.HTGeometry.UniversalLawField`.

Closed in `FormationScaleReceiver`:

- Theorem 2.1, `(FSR1.2)`--`(FSR1.5)` — `no_bounded_derivation_of_generator`;
- a receiver-collapse surrogate — `continuous_receiver_kills_formal_generator`;
- the polynomial-level Theorem 5.3 exchange — `derivative_formationAdams`,
  `eval_formationAdams`, `eval_derivative_formationAdams`;
- a logarithmic-collar version of the ghost transport — `formationWienerSummable_ghost`,
  `formationWienerNorm_ghost_le`.

Closed in `WienerFormationScale` (the scale `W_R` in coefficient coordinates on `C[[X]]`):

- admission `WienerScaleAdmissible` and the norm `wienerScaleNorm` of `(FSR1.10)`, with the values
  on `0`, `1`, `X^m`;
- closure under sum, negation, scalar action and Cauchy product, and the submultiplicative bound
  `(FSR1.11)` — `WienerScaleAdmissible.mul`, `wienerScaleNorm_mul_le`;
- radius monotonicity — `WienerScaleAdmissible.mono`, `wienerScaleNorm_mono`;
- receiver evaluation `(FSR1.12)`, its contractive bound `(FSR1.13)`, additivity, scalar
  homogeneity, and multiplicativity — `wienerScaleEval`, `norm_wienerScaleEval_le`,
  `wienerScaleEval_mul`;
- Theorem 5.1 with the sharp constant `(FSR1.15)` — `wienerScale_collar_bound`,
  `WienerScaleAdmissible.derivative`, `wienerScaleNorm_derivative_le`;
- Theorem 5.2 with the exact radius law `norm of Psi_q f at r equals norm of f at r^q` —
  `wienerScaleNorm_adams`, `WienerScaleAdmissible.adams`, `wienerScaleNorm_adams_le` for
  `(FSR1.19)`;
- the receiver covariance `(FSR1.23)`, unconditionally — `wienerScaleEval_adams`;
- Theorem 6.1: the exterior/formation inverse identity `(FSR1.26)` for an arbitrary finite marked
  mode family, the admission of both packets, and the exact margin `(FSR1.27)` —
  `one_sub_mul_wienerScaleGeom`, `wienerScale_witt_fusion`,
  `wienerScaleAdmissible_witt_formation`, `wienerScaleAdmissible_witt_exterior`,
  `wienerScaleNorm_geom`.

Closed in `WienerFormationScale` (second pass):

- Theorem 5.3's series-level exchange `(FSR1.21)` and its composite bound `(FSR1.22)` —
  `derivative_wienerScaleAdams`, `wienerScaleNorm_derivative_adams_le`;
- the receiver algebra itself as a subalgebra of the formal packets — `wienerScaleAlgebra`;
- receiver evaluation as an honest character — `wienerScaleEvalHom`;
- truncation and the exact tail identity — `wienerScaleTrunc`, `coeff_wienerScaleTrunc`,
  `wienerScaleNorm_sub_trunc`;
- Theorem 4.1(3): every bounded unital character is `ev_z` with `|z| <= R`, and the receiver point
  is unique — `exists_eval_of_bounded_character`, `wienerScaleEval_injective_point`.

Closed in `GaloisForLFunctions.HTGeometry.WienerFormationBanach`:

- Theorem 4.1(1) in full: `W_R` carries `NormedCommRing`, `NormedAlgebra C` and `CompleteSpace`
  structures, so it is a unital Banach algebra, with `norm_one_eq` for the unit;
- completeness is proved through the weight isometry `f -> (a_n R^n)` onto `l^1(N)` —
  `weightCoord`, `toLp`, `ofLp`, `isometryLp`;
- the continuous-character form of Theorem 4.1(3) — `exists_eval_of_continuous_character`,
  with the contractive direction `norm_eval_le`.

Closed in `GaloisForLFunctions.HTGeometry.FormalAdicReceiverCollapse`:

- Theorem 3.1 for the literal `T`-adic topology: `formalAdicIdeal`,
  `formalAdic_tendsto_smul_X_pow` for `(FSR1.6)`, `formalAdic_tendsto_trunc`,
  `formalAdicCharacter_apply_X` for `(FSR1.8)`, and
  `formalAdicCharacter_eq_constantCoeff` for `(FSR1.9)`, with the uniqueness corollary
  `formalAdicCharacter_unique`.

Together with `(FSR1.28)`, whose two halves are `wienerScaleEvalHom` plus `norm_eval_le` and
`exists_eval_of_continuous_character`, and whose Adams action is `wienerScaleEval_adams`, the whole
displayed surface of sections 2 to 7 is closed unconditionally.  Axiom prints on the whole surface
report only `propext`, `Classical.choice` and `Quot.sound`.  The three modules are wired into
`GaloisForLFunctions.HTGeometry.UniversalLawField`; the foreground umbrella build completes 11,857
jobs.

The open arithmetic scale/sheaf construction of section 8 is deliberately not formalized: it is the
successor research problem, not a theorem of this card.
