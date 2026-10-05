# Character coinvariant defect, Green properness, and reflection--formation selection

- **ID:** ULF-SRSM-11
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** ULF-SRSM-10 complete character-twisted response geometry; functional-equation packet
  lift
- **Statement:** Positive convolution formation itself can be cofinally nonproper while its
  coinvariant defect is globally proper.  For every nontrivial probability delay law `nu`, the
  character-response operator `I-M_nu` is boundedly invertible with a positive Green-series
  inverse.  The anti-coinvariant operator `I+M_nu` is always boundedly invertible.  Consequently a
  finite zero-mass signed current fixed by nontrivial formation, or anti-fixed by any positive
  formation, is zero.  If a source functional equation identifies reflection with formation, its
  parity therefore selects the zero current.
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [UNCONDITIONAL CORE]`
  `[GLOBAL FORMATION PROPERNESS] [CANONICAL GREEN INVERSE] [CHOQUET-DENY RIGIDITY]`
  `[FUNCTIONAL-EQUATION SELECTION CONDITIONAL ONLY ON SOURCE COMPARISON]`
  `[LEAN-PROVED] [PRE-RH] [NOT RH]`

## 1. Why the previous properness fracture is not terminal

ULF-SRSM-10 proves that convolution by an atomless probability law acts on the `c_0` character
response by an injective compact diagonal operator with dense nonclosed range.  Direct
deconvolution is globally ill-conditioned.

That is not the operator selection needs.  A null law asks whether a current changes under
formation.  Its operator is the **coinvariant defect**

\[
 D_\nu^-=I-M_\nu,
 \tag{CDG.1}
\]

or, under reflection-odd parity, the anti-coinvariant defect

\[
 D_\nu^+=I+M_\nu.
 \tag{CDG.2}
\]

The compact collapse of `M_nu` makes these defects more proper, not less.  This reverses the
previous completion intuition and supplies the required global formation/properness law.

## 2. Character-response setup

Let `nu` be a probability measure on `[0,infinity)` and set

\[
 a_n=L_\nu(n)=\int_0^\infty e^{-nx}\,d\nu(x),\qquad n\ge1.
 \tag{CDG.3}
\]

Then

\[
 1\ge a_1\ge a_2\ge\cdots>0.
 \tag{CDG.4}
\]

Moreover,

\[
 a_1=1\quad\Longleftrightarrow\quad\nu=\delta_0.
 \tag{CDG.5}
\]

Indeed `e^{-x}<=1`, with equality exactly at `x=0`.

On `c_0`, let

\[
 (M_\nu b)_n=a_nb_n.
 \tag{CDG.6}
\]

For a finite zero-mass signed measure `J` with `J({0})=0`, its complete character response

\[
 \mathcal TJ=(b_n(J))_{n\ge1}
 \tag{CDG.7}
\]

belongs to `c_0`, and convolution covariance is

\[
 \mathcal T(J*\nu)=M_\nu\mathcal TJ.
 \tag{CDG.8}
\]

## 3. Global coinvariant-defect properness

### Theorem 3.1 — positive Green formation

If `nu != delta_0`, then `D_nu^-=I-M_nu` is a bounded automorphism of `c_0` and

\[
 \boxed{
 (1-a_1)\|b\|_\infty
 \le\|(I-M_\nu)b\|_\infty
 \le\|b\|_\infty.}
 \tag{CDG.9}
\]

Its inverse is the norm-convergent positive Green series

\[
 \boxed{
 (I-M_\nu)^{-1}=\sum_{k=0}^\infty M_\nu^k,
 \qquad
 \|(I-M_\nu)^{-1}\|=\frac1{1-a_1}.}
 \tag{CDG.10}
\]

If `nu=delta_0`, then `M_nu=I` and `D_nu^-=0`.  Therefore

\[
 \boxed{I-M_\nu\text{ is globally proper exactly when }\nu\ne\delta_0.}
 \tag{CDG.11}
\]

### Proof

By `(CDG.4)`,

\[
 1-a_n\ge1-a_1>0.
\]

The diagonal operator `I-M_nu` therefore satisfies `(CDG.9)` and has bounded diagonal inverse
`((1-a_n)^(-1))`.  Also

\[
 \|M_\nu\|=\sup_{n\ge1}a_n=a_1<1,
\]

so the Neumann series converges in operator norm and equals the inverse.  Positivity is
coordinatewise.  The norm is attained at the first coordinate, giving `(CDG.10)`.  The Dirac case
is immediate.  QED.

### Theorem 3.2 — anti-coinvariant properness

For every probability law `nu`, including `delta_0`,

\[
 \boxed{
 \|b\|_\infty
 \le\|(I+M_\nu)b\|_\infty
 \le2\|b\|_\infty.}
 \tag{CDG.12}
\]

Hence `I+M_nu` is always a bounded automorphism and

\[
 \|(I+M_\nu)^{-1}\|\le1.
 \tag{CDG.13}
\]

### Proof

The diagonal coefficients are `1+a_n in (1,2]`.  Coordinatewise inversion proves every claim.
QED.

## 4. Properness complementarity

Combining ULF-SRSM-10 with Theorem 3.1 gives an exact table.

| formation law | `M_nu` | `I-M_nu` |
|---|---|---|
| `nu=delta_0` | isometric identity | zero |
| `0<nu({0})<1` | boundedly invertible | boundedly invertible |
| `nu({0})=0` | injective compact, dense nonclosed range | boundedly invertible |

Thus direct formation recovery and formation-defect recovery are different geometries.  Atomless
formation destroys stable deconvolution but creates a maximal spectral gap at high character.

The exact conservation/properness quantity is

\[
 \boxed{\gamma_-(\nu)=1-L_\nu(1),\qquad\gamma_+(\nu)=1.}
 \tag{CDG.14}
\]

**Refinement (Lean):** `gamma_-` is attained at the first coordinate.  The value `gamma_+=1` is the
universal lower bound; the exact anti-coinvariant gap is `inf_n(1+a_n)=1+nu({0})`, which equals one
exactly for atomless laws (in particular for every all-subset phase law).

No fitted tuple weight, cutoff, or divisor data enter these gaps.

## 5. Half-line Choquet--Deny rigidity for signed currents

### Theorem 5.1 — fixed-current selection

Let `J` be a finite zero-mass signed measure on `[0,infinity)`.

1. If `nu != delta_0` and

   \[
   J*\nu=J,
   \tag{CDG.15}
   \]

   then `J=0`.
2. For arbitrary `nu`, if

   \[
   J*\nu=-J,
   \tag{CDG.16}
   \]

   then `J=0`.

No `J({0})=0` hypothesis is needed.

### Proof

Apply the integer Laplace reporter.  Equation `(CDG.15)` gives

\[
 (1-a_n)b_n(J)=0.
\]

For nontrivial `nu`, `a_n<=a_1<1`, hence every `b_n(J)=0`.  Equation `(CDG.16)` gives

\[
 (1+a_n)b_n(J)=0,
\]

and `1+a_n>0`.  In either case all positive integer responses vanish.  The complete zero-mass
reconstruction theorem ULF-SRSM-10 gives `J=0`.  QED.

### Quantitative response version

When `J({0})=0`, equations `(CDG.9)` and `(CDG.12)` give

\[
 \|\mathcal T(J-J*\nu)\|_\infty
 \ge(1-L_\nu(1))\|\mathcal TJ\|_\infty,
 \tag{CDG.17}
\]

and

\[
 \|\mathcal T(J+J*\nu)\|_\infty
 \ge\|\mathcal TJ\|_\infty.
 \tag{CDG.18}
\]

Thus the selector has a global response gap, not merely a uniqueness theorem.

## 6. Functional-equation reflection--formation selector

Let `R` be an involutive source action on the current space.  Suppose a literal source comparison
proves, before zero specialization,

\[
 \boxed{R_*J=J*\nu.}
 \tag{CDG.19}
\]

Suppose independently that source parity gives

\[
 R_*J=\varepsilon J,
 \qquad\varepsilon\in\{+1,-1\}.
 \tag{CDG.20}
\]

### Corollary 6.1 — reflection--formation selection law

Under `(CDG.19)`--`(CDG.20)`:

- if `epsilon=+1` and `nu != delta_0`, then `J=0`;
- if `epsilon=-1`, then `J=0` for every probability `nu`.

### Proof

The two equations give `J*nu=epsilon J`.  Apply Theorem 5.1.  QED.

This is the first exact selection mechanism produced by the source-response programme that uses
all of:

1. a functional-equation action;
2. positive formation;
3. a complete vertical reporter;
4. a global properness gap.

The common-recovery packet theorem proves that functional equation lifts information-neutrally
through formation.  It does **not** prove `(CDG.19)`.  That comparison is now the sharply typed
arithmetic gate: reflection must equal a nontrivial positive formation of the same pre-zero current,
not merely act on the same observer packet.

## 7. Literal all-subset phase consequence

Every nonempty all-subset phase law `nu_I` is a convolution of positive exponential laws.  Hence

\[
 \nu_I\ne\delta_0,
 \qquad
 L_{\nu_I}(1)=
 \prod_{\varnothing\ne S\subseteq I}
 \frac{\lambda_S}{\lambda_S+1}<1.
 \tag{CDG.21}
\]

Therefore its character coinvariant defect has the explicit global lower bound

\[
 \boxed{
 \gamma_I=1-
 \prod_{\varnothing\ne S\subseteq I}
 \frac{\lambda_S}{\lambda_S+1}>0.}
 \tag{CDG.22}
\]

As aperture grows, the product decreases, so `gamma_I` increases toward one.  High formation arity
strengthens the coinvariant gap even though direct deconvolution remains compact and nonproper.

This is a new prediction for the all-grade organ: the complete tower's difficult direct formation
topology coexists with an increasingly coercive formation-defect topology.

## 8. Hostile conjecture loops

### Loop A — nonproper formation implies nonproper selection defect

**False.**  If `nu` is atomless, `M_nu` is compact/dense-nonclosed while `I-M_nu` has lower bound
`1-L_nu(1)>0`.

**Survivor.**  Formation and coinvariant-defect properness are complementary axes.

### Loop B — functional-equation invariance alone gives `(CDG.19)`

**False.**  The common-recovery lift only proves naturality and information isometry.  A reflected
packet can regenerate latent history without being convolution of the original vertical current.

**Survivor.**  `(CDG.19)` is the precise new source comparison required for selection.

### Loop C — fixed-point rigidity needs positivity of `J`

**False.**  The complete signed character transform proves rigidity for every finite zero-mass
signed current.

### Loop D — origin mass controls every properness law

**False.**  Origin mass controls `M_nu`; nontrivial delay controls `I-M_nu`; `I+M_nu` is always
proper.

### Loop E — the Green inverse is a fitted regularizer

**False.**  It is the canonical Neumann inverse of the source-generated formation action, with
exact norm `1/(1-L_nu(1))`.

### Loop F — Corollary 6.1 proves RH

**False.**  No corpus theorem yet identifies the literal physical current with a half-line signed
current satisfying `(CDG.19)`.  Assuming that identity after Xi specialization would be circular.

## 9. Literature and significance audit

The fixed-point statement belongs to the broad Choquet--Deny world.

- Jaworski--Neufang, *The Choquet--Deny equation in a Banach space*, studies fixed vectors of
  convolution representations and their Poisson-boundary description:
  <https://arxiv.org/abs/math/0609035>.
- Frisch--Hartman--Tamuz--Vahidi Ferdowsi, *Choquet--Deny groups and the infinite conjugacy class
  property*, gives a modern group-level classification:
  <https://arxiv.org/abs/1802.00751>.
- Classical Laplace-transform uniqueness already implies the half-line finite-measure rigidity.

The new-to-programme content is not a claim to have invented Choquet--Deny theory.  It is the exact
operator complementarity

\[
 M_\nu\text{ nonproper}\quad\text{while}\quad I-M_\nu\text{ globally proper},
\]

its explicit all-subset prime-log gap, and the typing of reflection--formation comparison as the
remaining source selector.  This changes the research target: do not invert the positive formation;
prove the physical current lies in its fixed or anti-fixed defect.

## 10. Lean decision

Fully formalized, unconditionally: see the Lean certificate below.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.CoinvariantDefectGreenProperness`, `GaloisForLFunctions.HTGeometry.OriginAtomFormationProperness`, `GaloisForLFunctions.HTGeometry.HalfLineLaplaceTomography`, `GaloisForLFunctions.HTGeometry.HypoexponentialRateReconstruction`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

## Lean certificate

Module `GaloisForLFunctions.HTGeometry.CoinvariantDefectGreenProperness`, on top of ULF-SRSM-10
(`GaloisForLFunctions.HTGeometry.OriginAtomFormationProperness`, `GaloisForLFunctions.HTGeometry.HalfLineLaplaceTomography`,
`GaloisForLFunctions.HTGeometry.HypoexponentialRateReconstruction`).  Probability laws on `[0, ∞) = ℝ≥0`;
`a_n = L_ν(n)` is `mult ν (n - 1)`; `c_0 = C₀(ℕ, ℝ)` with coordinate `k` carrying `b_{k+1}`; `M_ν = diagMul ν`;
the signed convolution `J ∗ ν` is `convSigned J ν`; the all-subset law of a prime set `I` is
`halfLineLaw (primeLaw I)`.

| Claim | Lean declaration |
|-|-|
| (CDG.1)–(CDG.2) the defects `I ∓ M_ν` | `LaplaceTomography.one_sub_diagMul_apply`, `LaplaceTomography.one_add_diagMul_apply` |
| (CDG.3)–(CDG.4) `1 ≥ a_1 ≥ a_2 ≥ ⋯ > 0` | `LaplaceTomography.mult`, `LaplaceTomography.mult_antitone`, `LaplaceTomography.mult_pos`, `LaplaceTomography.mult_le_one` |
| (CDG.5) `a_1 = 1 ⟺ ν = δ_0` | `LaplaceTomography.mult_zero_eq_one_iff`, `LaplaceTomography.mult_zero_lt_one` |
| (CDG.6)–(CDG.8) `M_ν` on `c_0`, the response `𝒯J ∈ c_0`, `𝒯(J ∗ ν) = M_ν 𝒯J` | `LaplaceTomography.diagMul`, `LaplaceTomography.responseC0`, `LaplaceTomography.diagMul_responseC0`, `LaplaceTomography.charResponse_convSigned` |
| Theorem 3.1, (CDG.9) `(1 - a_1)‖b‖ ≤ ‖(I - M_ν)b‖ ≤ ‖b‖`; `‖M_ν‖ = a_1` | `LaplaceTomography.one_sub_diagMul_bounds`, `LaplaceTomography.norm_diagMul` |
| (CDG.10) Green series `Σ_k M_ν^k` is the two-sided inverse, coordinatewise `b_k/(1 - a_{k+1})`, positive, of norm `1/(1 - a_1)` | `LaplaceTomography.greenOp`, `LaplaceTomography.greenOp_spec` |
| (CDG.11) `I - M_ν` bounded below ⟺ `ν ≠ δ_0`; `M_{δ_0} = I` | `LaplaceTomography.one_sub_diagMul_proper_iff`, `LaplaceTomography.diagMul_dirac` |
| Theorem 3.2, (CDG.12)–(CDG.13) `‖b‖ ≤ ‖(I + M_ν)b‖ ≤ 2‖b‖`, inverse of norm `≤ 1` | `LaplaceTomography.one_add_diagMul_spec`, `LaplaceTomography.diagOp` |
| §4 table: `δ_0`, origin atom, atomless, off `δ_0` | `LaplaceTomography.properness_table`, `LaplaceTomography.originAtom_zero` |
| (CDG.14) `γ_- = 1 - L_ν(1)` attained; anti-coinvariant gap `inf_n(1 + a_n) = 1 + ν({0})` (`= 1` for atomless `ν`) | `LaplaceTomography.defect_gaps_exact`, `LaplaceTomography.one_add_diagMul_spec` |
| Theorem 5.1, (CDG.15)–(CDG.16) half-line signed Choquet–Deny | `LaplaceTomography.choquetDeny`, `LaplaceTomography.eq_zero_of_conv_eq_self`, `LaplaceTomography.eq_zero_of_conv_eq_neg`, `LaplaceTomography.eq_zero_of_charResponse_eq_zero` |
| (CDG.17)–(CDG.18) response gaps for `J ∓ J ∗ ν` | `LaplaceTomography.response_gaps`, `LaplaceTomography.charResponse_sub`, `LaplaceTomography.charResponse_add`, `LaplaceTomography.isFiniteMeasure_variation` |
| Corollary 6.1, (CDG.19)–(CDG.20) reflection–formation selection | `LaplaceTomography.reflection_formation_selection` |
| (CDG.21) `ν_I ≠ δ_0`, `L_{ν_I}(1) = Π_{∅≠S} λ_S/(λ_S+1) < 1` | `LaplaceTomography.mult_primeLaw_zero`, `LaplaceTomography.subsetProduct`, `LaplaceTomography.subsetProduct_lt_one`, `LaplaceTomography.allSubset_gap` |
| (CDG.22) `γ_I > 0` with the coinvariant bound, alongside compact nonproper deconvolution | `LaplaceTomography.allSubset_gap`, `LaplaceTomography.primeLaw_compact_response` |
| §7: `γ_I` increases with the aperture and tends to one along the first primes | `LaplaceTomography.subsetGap_mono`, `LaplaceTomography.subsetProduct_eq`, `LaplaceTomography.primeSubsetProduct`, `LaplaceTomography.tendsto_subsetProduct_firstPrimes`, `LaplaceTomography.tendsto_subsetGap_firstPrimes` |
| Loop A complementarity; Loop C signed rigidity; Loop D; Loop E exact Green norm | `LaplaceTomography.complementarity`, `LaplaceTomography.eq_zero_of_conv_eq_self`, `LaplaceTomography.properness_table`, `LaplaceTomography.greenOp_spec` |

Lean refinements: Theorem 5.1 holds without the zero-mass and origin hypotheses (as the card notes for the
origin).  In (CDG.14) the value `γ_+ = 1` is the universal lower bound; the exact anti-coinvariant gap is
`1 + ν({0})`, equal to `1` exactly for atomless laws (all subset-phase laws are atomless).  Loops B and F and
§9 state what is not claimed.

## Log

- 2026-08-14 — direct-deconvolution nonproperness attacked at the operator polynomial level rather
  than accepted as another obstruction.
- 2026-08-14 — proved `I-M_nu` globally proper exactly off `delta_0`, with positive Green-series
  inverse; proved `I+M_nu` always proper.
- 2026-08-14 — extracted half-line signed Choquet--Deny rigidity and the conditional
  reflection--formation selection theorem.
- 2026-08-14 — derived explicit all-subset prime-log formation gap; Lean audited read-only, no
  write/build.
- 2026-10-05 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
