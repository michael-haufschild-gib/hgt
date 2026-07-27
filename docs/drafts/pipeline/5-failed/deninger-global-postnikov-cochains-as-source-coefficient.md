# Global Postnikov cochains as Deninger's source coefficient

- **ID:** `deninger-global-postnikov-cochains-as-source-coefficient`
- **Stage:** 5-failed
- **Type:** REDISCOVERED CHART THEOREM / RETIRED SOURCE TYPE ERROR
- **Former label:** `DAC_GENERIC_RATIONAL_STEINBERG_POSTNIKOV_CORRECTION`
- **Parent:** `deninger-true-to-approximate-derived-coefficient`

## Retired claim

For a Kucharczyk--Scholze character component, set
\[
 A_{\mathrm{raw}}
 =R\Gamma(X_{\overline{\mathbb Q}},\underline{\mathbb Q})
\]
and use
\[
 \tau_{\leq1}^{E_\infty}A_{\mathrm{raw}}                           \tag{1}
\]
as the generic source coefficient in Deninger's arithmetic
cohomology.

The cohomology calculation behind `(1)` is valid: for fields algebraic
over \(\mathbb Q\), rational Milnor \(K_n\) vanishes for \(n\ge2\), so
the desired chartwise Milnor algebra has degrees zero and one only.
That calculation is already recorded more strongly and without an
ad hoc truncation in
`DAC_CHARACTER_SHAPE_FORMALITY` and
`DAC_ALGEBRAIC_CYCLOTOMIC_MILNOR_AMPLITUDE`.

## Failure

Expression `(1)` is a derived global-section algebra.  It is neither a
sheaf nor a stalk and therefore cannot be the coefficient
\(R\alpha_*\mathscr G\) required by Deninger.  It has no restriction
maps, prime residue maps, Gysin maps, or power-equivariant
sheafification data.

The failure is not cosmetic.  For the genuine sheaf-level
unit-amalgamated construction, a stalk at which the Kummer morphism
becomes null contains
\[
 \operatorname{Tor}_1^{\Lambda(V)}
   \bigl(k,\Lambda(V)/\Lambda^{\ge2}(V)\bigr)
 \cong\Lambda^2V.                                                   \tag{2}
\]
This is `DAC_KUMMER_SHEAF_STALK_TOR_OBSTRUCTION`.  Hence chartwise
two-term cohomology does not imply two-term homotopy sheaves.  Applying
`(1)` before sheafification silently deletes exactly the local derived
data needed for arithmetic localization.

Continuous Galois invariants do not repair the type error: even if
they compute the correct chartwise degree-one invariants, they still
do not construct a sheaf on Deninger's suspension or its
generic/closed-point descent diagram.

## Positive survivor

The correct source construction already exists on paper:
\[
 \widetilde{\mathscr A}^M_{F,\mathrm{geom}}
 =
 \mathscr T_X
 \mathop{\otimes}^{\mathbb L}_{\mathscr P_F}
 \underline{\mathcal K}^M_F,
 \qquad
 \mathscr P_F
 =\operatorname{Free}^{+}_{E_\infty,\mathscr T_X}
   (H V_F(1)[-1]).                                                  \tag{3}
\]
It is formed in commutative algebra objects in the derived category
of equivariant Tate-graded leafwise sheaves, before taking derived
sections.  Existence and functoriality of `(3)` are
`DAC_LEAFWISE_KUMMER_SHEAF_AMALGAMATION_EXISTENCE`.

The chartwise calculation survives as the comparison target
\[
 R\Gamma(X_F,\widetilde{\mathscr A}^M_{F,\mathrm{geom}})
 \simeq \mathcal K^M_{F,\mathbb R},                                \tag{4}
\]
not as the definition of the source.  Exact remaining gates are
`DAC_SHEAFIFIED_UNIT_AMALGAMATION_COMPARISON`, arithmetic
generic/prime localization, power descent, real signature gluing, and
the two-level derived-section window.

## No-go closure

- **Killed representation:** global cochains or their Postnikov
  truncation used as a coefficient sheaf.
- **Killing mechanism:** loss of sheaf structure plus nonzero stalk
  Tor `(2)`.
- **Strongest survivor:** genuine sheaf-level derived
  unit-amalgamation `(3)` with chartwise Milnor comparison `(4)`.
- **Paper status:** sheaf existence and the chart algebra are proved;
  comparison/descent is conjectural.
- **Lean status:** no Lean formalization claimed for the retired
  construction.

**Verdict:** `REDISCOVERED AS A CHART CALCULATION; FALSIFIED AS
DENINGER'S SOURCE SHEAF`.
