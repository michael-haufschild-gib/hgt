# Euler--Gamma Ward window multiplicity and semigroup-annulus bounds

- **ID:** `euler-gamma-ward-window-multiplicity-bound`
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean), `[BRIDGE]`
- **Scientific status:** `[FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT A 75% THEOREM]`
- **Lean file:**
  `formal/GaloisForLFunctions/RHTower/XiWardSourceWindowMultiplicity.lean`
- **Parent research card:**
  `../../1-in-progress/zeta23-beyond-bandwidth-one-proportion.md`
- **RH used:** no
- **Computation used as proof:** no

## Statement

Let `S` be any finite set of multiplicity copies of strict-right upper Xi zeros, with centered
points `a_q+i gamma_q`.  Fix `h>1/2`, a height center `c`, and a window radius `delta`.  If

```text
(gamma_q-c)^2 <= delta^2       for every q in S,
```

then

```text
Q_sharp(h,delta)
 = min(2h/(h^2+delta^2),
       2(h+1/2)/((h+1/2)^2+delta^2)),

card(S) * Q_sharp(h,delta)
  <= B_EG(h,c),

B_EG(h,c)
 = 2 Re[ 1/s + 1/(s-1) + (Gamma_R'/Gamma_R)(s)
         - sum_(n>=2) Lambda(n)n^(-s) ],
s=h+1/2+ic.
```

The right side lies in `Re s>1`, so its von Mangoldt series is absolutely convergent.  The lower
quantum is optimal using only the critical-strip width and window hypotheses, and is uniform for
every `a_q>0`, including arbitrarily small positive displacement.  Critical-line multiplicity is
absent by construction because the index type contains only strict-right copies.  The earlier
coarser quantum `2h/((h+1/2)^2+delta^2)` remains as a corollary-level theorem.

For the same strict-right copy `q`, let `E_h(q)` be the integrated square of the real Schwarz-pair
response on the vertical line of shift `h`.  The file also proves

```text
E_h(q) = 4 pi [1/(h+a_q) + (h+a_q)/((h+a_q)^2+gamma_q^2)],
pi <= E_(3/5)(q) - E_(8/5)(q).
```

The second inequality is uniform in height and in `a_q>0`, including `a_q -> 0+`.
The stronger source-safe specialization also proves

```text
3 pi <= E_(51/100)(q) - E_(1051/100)(q).
```

Using a gap of `150`, the same theorem family proves the near-ceiling bound

```text
(39/10) pi <= E_(51/100)(q) - E_(15051/100)(q).
```

The same file now proves two exact boundary facts.  First, the spatial cross kernel of every
positive-width annulus has zero total mass despite a strictly positive diagonal:

```text
integral_R [2x/((2x)^2+D^2)-2(x+d)/((2(x+d))^2+D^2)] dD = 0,
K_(x,d)(0)=d/[2x(x+d)]>0.                                (Z)
```

Second, the squared self-Cauchy singularity cancels the quadratic Plucker/Gabor coalescence for
every positive displacement `a`:

```text
u^2/2 <= [cosh(2au)-1] [1/(2a)]^2.                       (PW)
```

At the actual zero-adapted node, the continued Ward field strengthens this to a strict `2u^2`
quantum for every `u!=0`.  This is a local submicroscopic positive-shift separator, not yet a
source-defined global sampling law.

The same module proves that this uniform boundary jump is necessarily singular: no function
continuous at zero and vanishing there can stay above a fixed positive constant at every positive
argument.  Consequently the Plucker--Ward atom is discontinuous at zero for every nonzero
frequency.

Finally, shifting a complete positive Cauchy packet gives the multiplicity-exact shallow-layer
law.  If `0<a_j<=h`, then every cross term is positive and every self-diagonal costs at least
`m_j/h`, so

```text
sum_j m_j <= h * finiteOfflineCauchyEnergy(h+a, gamma, m).  (SL)
```

For Xi strict-right copies this excludes critical-line multiplicity by type.  Combining `(SL)`
with the exact divisor split proves a three-quarters receiver: if shallow energy times `h` plus
the strict-right deep count is at most `N/8`, then `N_0>=3N/4`.  The receiver is unconditional
algebra; the required prime--Gamma source upper bound at shrinking `h` is not proved.

## Proof

At `w=h+ic`, one Schwarz-pair Ward response is the sum of two positive Lorentzians.  Put
`x=h+a_q in (h,h+1/2)` and `D=delta^2`.  The term centered at `gamma_q` is bounded below by

```text
2x/(x^2+D).
```

For `h<=x<=H=h+1/2`, either `hx<=D`, in which case
`2h/(h^2+D)<=2x/(x^2+D)`, or `D<hx<=Hx`, in which case
`2H/(H^2+D)<=2x/(x^2+D)`.  Hence the endpoint minimum `Q_sharp` is a lower bound.  Summing over
`S` gives the left side.
Every remaining Schwarz-pair term has positive real part, so the finite sum is at most the complete
absolutely convergent Ward response.  Functional-equation reflection absorbs its complementary
divisor and boundary self-symbol, leaving the explicit source-only majorant `B_EG`.  Chaining the
three inequalities proves the theorem.

For the annulus bound, set `x=3/5+a_q` and `g=gamma_q^2`.  Then
`3/5<=x<=11/10` and `g>=0`.  After clearing positive denominators, the assertion that the shift
difference is at least `1/4` is a quadratic polynomial in `g`.  Its constant coefficient is
`x^2(x+1)^2(8-x^2-x)`, its linear coefficient is
`-2(x^2+x)^2+3(x^2+x)+4`, and its quadratic coefficient is `4-x^2-x`; all are nonnegative on the
stated interval.  Multiplication by `4 pi` and the exact energy identity gives the `pi` quantum.

More generally, for a positive shift gap `d`, the normalized difference is bounded below by
`d/[x(x+d)]-1/d`.  When its second summand is negative, the identity

```text
(x^2+g)((x+d)^2+g)=(g+x(x+d))^2+d^2g
```

bounds the negative part by `1/d`.  With `x<=101/100` and `d=10`, this coarse bound already exceeds
`3/4`; multiplying by `4 pi` yields the `3pi` theorem.

With `d=150`, the bound exceeds `39/40`; multiplication by `4 pi` gives `39pi/10`.

## Formal theorem map

| Content | Declaration |
|---|---|
| finite packet is below complete positive Ward series | `finite_sum_re_xiAntiCausalWardSchwarzPairResponse_le_continued` |
| critical-line relative resolvent is exact Poisson kernel | `re_two_I_relativeResolventTerm_critical_line_eq` |
| critical diagonal retained under reflection absorption | `re_boundary_add_critical_tsum_le_two_I_logDeriv_nonright` |
| hybrid strict-right plus critical source inequality | `re_continued_add_critical_tsum_le_sourceArithmetic` |
| finite hybrid height-window charge | `finite_strictRight_and_critical_window_charge_le_sourceArithmetic` |
| Cauchy--Schwarz conversion from window mass to raw energy | `sq_setIntegral_le_length_mul_setIntegral_sq` |
| abstract count-square raw-energy law | `ward_raw_quadratic_count_sq_le` |
| exact `N/8` raw-energy scale | `ward_raw_quadratic_energy_scale_at_eighth` |
| two-sided length-`2T` threshold `pi^2 N^2/(8T)` | `ward_raw_quadratic_energy_scale_at_eighth_twoTime` |
| integral form of the `N/8` threshold | `ward_setIntegral_energy_scale_at_eighth` |
| optimal endpoint quantum | `xiWardSharpWindowQuantum` |
| endpoint minimum bounds every admissible Lorentzian width | `xiWardSharpWindowQuantum_le_lorentzian` |
| sharp per-pair submicroscopic deposit | `sharp_interior_pair_quantum` |
| sharp multiplicity-exact source estimate | `finite_strictRight_window_card_mul_sharpQuantum_le_sourceArithmetic` |
| multiplicity-exact window quantum bounded by Euler--Gamma source | `finite_strictRight_window_card_mul_quantum_le_sourceArithmetic` |
| exact shifted real-channel diagonal energy | `integral_sq_re_xiAntiCausalWardSchwarzPairResponse_line` |
| algebraic `1/4` annulus quantum | `one_fourth_le_cauchy_shift_annulus` |
| uniform `pi` loss between source-safe shifts | `pi_le_realDiagonalEnergy_threeFifths_sub_eightFifths` |
| general coarse width-annulus bound | `cauchy_shift_annulus_ge_width_div_sub_inv` |
| normalized `3/4` ten-unit annulus | `three_fourths_le_cauchy_shift_annulus_ten` |
| uniform `3pi` source-safe loss | `threePi_le_realDiagonalEnergy_fiftyOneHundredths_sub_tenShift` |
| normalized `39/40` far annulus | `thirtyNineFortieths_le_cauchy_shift_annulus_oneHundredFifty` |
| uniform `39pi/10` source-safe loss | `thirtyNineTenthsPi_le_realDiagonalEnergy_fiftyOneHundredths_sub_oneHundredFiftyShift` |
| negative separated-ordinate cross channel | `cauchy_cross_shift_annulus_neg_of_sq_gt` |
| integrability of annular spatial kernel | `integrable_cauchy_cross_shift_annulus` |
| exact annular zero-frequency annihilation | `integral_cauchy_cross_shift_annulus_eq_zero` |
| positive annular diagonal despite zero mass | `cauchy_cross_shift_annulus_zero_eq_pos` |
| elementary hyperbolic coalescence bound | `two_mul_sq_le_cosh_two_mul_sub_one` |
| finite-band quadratic coalescence ceiling | `cosh_sub_one_le_sq_of_abs_le_one` |
| submicroscopic hyperbolic gap ceiling | `coshGap_le_four_mul_sq_of_submicroscopic` |
| squared Cauchy singularity cancels coalescence | `half_sq_le_coshGap_mul_sq_transverseCauchyKernel_self` |
| totalized boundary atom is zero | `pluckerWardRenormalizedAtom_zero` |
| every positive shift carries `u^2/2` | `pluckerWardRenormalizedAtom_ge_half_sq` |
| finite-band renormalized atom lies in `[u^2/2,u^2]` | `pluckerWardRenormalizedAtom_mem_Icc` |
| actual adapted Ward field carries strict `2u^2` | `two_mul_sq_lt_coshGap_mul_normSq_continuedWard_at_adaptedNode` |
| no continuous boundary-vanishing detector has a uniform positive quantum | `not_exists_uniform_positive_continuous_boundarySeparator` |
| Plucker--Ward atom is forced to be discontinuous at zero | `not_continuousAt_zero_pluckerWardRenormalizedAtom` |
| multiplicity-exact shallow Cauchy census | `sum_multiplicity_le_shift_mul_finiteOfflineCauchyEnergy` |
| shallow packet-cardinality census | `card_le_shift_mul_finiteOfflineCauchyEnergy` |
| actual Xi shallow-copy census | `xiRight_shallowLayer_card_le_shift_mul_finiteOfflineCauchyEnergy` |
| shallow/deep `75%` numerical receiver | `three_quarters_line_of_shallowEnergy_and_deepCount` |
| exact FE horizontal Cauchy curvature | `horizontalCauchyCurvatureAtom_eq` |
| positive-shift curvature floor `2/h^3` | `two_div_cube_le_horizontalCauchyCurvatureAtom` |
| half-width curvature ceiling `8/(3h^3)` | `horizontalCauchyCurvatureAtom_le_eight_div_three_cube` |
| critical diagonal curvature is zero | `horizontalCauchyCurvatureAtom_zero` |

Dependencies carrying analytic content are already unconditional corpus theorems:
`interior_pair_quantum` and
`re_continuedXiAntiCausalWardResponse_le_sourceArithmetic`.

## Exact boundary

This is the requested source-faithful submicroscopic separator, but it is a first-moment estimate.
The source majorant retains the universal Gamma baseline and grows like `log |c|` on a fixed
interior line.  Covering a dyadic height interval therefore yields census order `T log T`, without
the factor `1/8` needed to prove `N_off<=N/4`.  A 75% theorem still requires a centered quadratic
Euler--Gamma correlation bound or a height-local index estimate.

The initial parent-card reduction proposed an `O(N)` localized quadratic budget.  The formal
mass-to-energy scale audit here corrects that claim.  On a window of length `V`, a right-upper
count `R` and linear charge `4pi` satisfy

```text
16 pi^2 R^2 <= V E.
```

Thus `R=N/8` requires `E>=pi^2 N^2/(4V)`; for a two-sided window of asymptotic length `2T`, the
threshold is `pi^2 N(T,2T)^2/(8T)`, of natural order `T log^2 T`.  An `O(N)` energy bound would
instead imply `R=o(N)` and density one.  A 75% theorem therefore requires a source leading
constant below this corrected scale, not the previously recorded `(pi/2)N` bound.

The mathematical proof is a direct finite-sum consequence of existing Lorentzian positivity and
source absorption.  It closes an important formal interface but is not claimed as new external
scientific knowledge.

The annulus result removes the zero-frequency Gamma baseline at diagonal level, but it still does
not prove a global count.  The corresponding difference of packet energies has signed spatial
cross terms.  Positive-definite frequency weight controls the whole quadratic form, not its
diagonal separately.  Random signs indexed by unknown zeros would isolate the diagonal but are not
an Euler--Gamma source observable, and separate one-sided source bounds cannot be subtracted.
The formal cross-kernel theorem makes the first obstruction exact: once squared ordinate
separation exceeds `4x(x+d)`, the spatial annulus cross term is strictly negative.

In fact `(Z)` closes diagonal aggregation more sharply: the annulus annihilates the constant
spatial mode exactly, so dense nearly uniform ordinate packets can suppress aggregate energy while
their positive diagonal census grows.  No asymptotic diagonal-dominance argument survives without
an independent source trace/decorrelation law.

The renormalized atom `(PW)` repairs submicroscopic collapse locally.  It combines the exact
quadratic Gabor/Plucker gap with two inverse-displacement Hardy factors and vanishes at the
critical-line boundary under totalized inversion.  Its actual Ward version still evaluates at a
node and uses a factor adapted to the unknown zero.  Aggregating it by simply summing the divisor
would be circular; a 75% consequence needs a prime--Gamma construction of the corresponding
nonlinear sampling/trace observable.

The finite-band audit is now two-sided: for `|2au|<=1`, the renormalized atom is trapped in
`[u^2/2,u^2]`.  Hence quadratic coalescence and inverse-square normalization are sharp in order,
not proof losses.

Reflection absorption can also retain any selected critical-line stratum.  The resulting hybrid
inequality charges strict-right pairs and critical copies simultaneously under the same explicit
Euler--Gamma head.  Its height-window specialization is multiplicity-exact.  Integrated at leading
order, however, it restores only the natural Poisson charge per divisor copy and therefore gives
no improvement over the divisor split by itself.

The positive no-go survivor is FE horizontal curvature.  An off-line reflected pair has diagonal
widths `h+a,h-a`; subtracting two critical widths and dividing by `a^2` gives exactly
`2/[h(h^2-a^2)]`, between `2/h^3` and `8/(3h^3)` when `2a<=h`, while its totalized critical value is
zero.  This supplies a second rigorous submicroscopic separator.  Source-side aggregation still
requires the same singular tangent covariance.

The shifted positive Cauchy energy `(SL)` repairs the annular aggregation failure as well: its
off-diagonal terms are strictly positive, and it charges every shallow multiplicity at scale
`1/h`.  The exact remaining source theorem is correspondingly sharper.  At
`h asymp 1/log T`, prove

```text
h E_h(T) + R_deep(T;h) <= N(T,2T)/8 + o(N(T,2T)).
```

The source arithmetic bound formalized above applies only for an absolute-Euler displacement
greater than `1/2`.  Finite-aperture Hardy contractivity cannot simply be differentiated to obtain
the required tangent outer-product bound, and deconvolving the safe edge reaches the same missing
covariance.  Therefore this card records an unconditional local separator and exact conditional
receiver, not an improved zeta-zero proportion.

## Verification

- targeted module build passes;
- exported axiom audit: `[propext, Classical.choice, Quot.sound]` only;
- changed modules contain no forbidden `sorry`, `admit`, `axiom`, `opaque`, or `unsafe` token;
- repository-wide `scripts/formal_tools.py lint` is currently red on unrelated pre-existing
  umbrella reachability errors (Deninger, Hedenmalm, and Sieve modules); none names either changed
  theorem module.
