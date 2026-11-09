# Finite-energy arithmetic tent transport

- **ID:** euler-fe-finite-energy-tent-transport
- **Stage:** 3-formalized
- **Programme:** Euler–FE transport theory; Exact-event theory of Euler products.
- **Target:** Actual arithmetic tent identities and recurrence for square-integrable
  uncompleted functional-equation defects.

## Statement

Let `g` be measurable, polynomially bounded and square integrable. Let a positive
measure `ν`, supported on `[1,∞)`, have finite inverse-square moment and satisfy the
actual defective theta identity with real pole coefficient `β`. For `0<h≤1`, `n>1`,

    ½ ∫ max(1-|u/h-n|,0) dν(u)
      = h ∫ cos(2πhun) sinc²(πhu) dν(u) + hβ + E_g(h,n),
    E_g(h,n) = Re ∫ max(1-|y/h-n|,0) Bg(y) dy.

Here `B` is the canonical Hardy boundary operator, not a pointwise boundary
assumption. For every positive width and every real centre,

    |E_g(h,n)| ≤ √(2h) ‖Bg‖₂.

At fixed width `E_g(h,n)→0` as `n→+∞`. As `h↓0`, the error tends to zero uniformly
over all centres. For a countable Beurling integer measure with finite inverse-3/2
moment, write its physical tent mass as `A_h(y)=P_h(y)+E_g(h,y/h)`, where `P_h` is
the absolutely convergent cosine series plus the pole. Then

    P_h(y)<¼  ⇒  P_(h/2)(y)=0.

This is a nonlinear restriction on the actual Euler spectrum, with no recurrence
or error-smallness premise. It forces `Re Bg=0` almost everywhere on `(0,1)`.

## Proof

The interior theta/Laplace identity is paired with a tent. Polynomial boundedness
makes the actual defect holomorphic in the right half-plane, so this interior
pairing needs no `L¹` hypothesis. Strong Hardy convergence passes its defect term
to `Bg`: each tent belongs to `L²`, hence defines a continuous pairing. The atomic,
cosine and pole terms have the already proved boundary limits under the stated
support and moment conditions.

The tent is bounded by one and supported on an interval of length `2h`. Its `L²`
norm is therefore at most `√(2h)`, giving the error bound by Cauchy–Schwarz. The
pairing is unchanged if `Bg` is restricted to that interval. As its centre tends
to positive infinity, the restricted energy tends to zero by dominated
convergence, dominated by `|Bg|²`. This proves fixed-width decay. The uniform
small-width conclusion follows directly from the same bound.

The inverse-square moment makes both width-`h` and width-`h/2` cosine series
absolutely convergent; they have common arbitrarily distant almost periods.
Every Beurling atom has mass one. Thus `A_h(y)<¼` excludes every atom from the
half-width tent and forces `A_(h/2)(y)=0`. If the displayed restriction on `P`
failed, a common distant return would preserve its strict outer threshold and
nonzero inner value while both boundary errors tend to zero, contradicting that
atomic floor.

For each `y∈(0,1)`, sufficiently narrow outer tents lie inside the gap and have
error smaller than `¼`. Their atomic mass is zero, hence their recurrent part is
below `¼`. The half-width recurrent part is therefore zero; its atomic mass is
also zero, so its boundary pairing is exactly zero.

The normalized tent has mass one, support in `[y-h,y+h]`, and supremum at most
`1/h`, twice the inverse length of that interval. At every Lebesgue point of
`Re Bg`, its average therefore converges to `Re Bg(y)`: the error is bounded by
twice the interval average of `|Re Bg(x)-Re Bg(y)|`. Local integrability follows
from `L²`. The zero half-width averages give the claimed almost-everywhere gap.

## Formalization

The arithmetic identity and both error estimates pass direct Lean checks with only
`propext`, `Classical.choice` and `Quot.sound`, in
`EulerFETransportTheory/FiniteEnergyDefectsObeyTheTentIdentity.lean` and
`EulerFETransportTheory/FiniteEnergyTentErrorsVanish.lean`.
`EulerFETransportTheory/FiniteEnergyDefectsRetainAtomicRecurrence.lean` also passes
direct checks with those axioms: the actual Beurling identity, two-width recurrence,
and eventual exact vanishing of unit-gap tent pairings.
`EulerFETransportTheory/FiniteEnergyDefectsVanishInTheUnitGap.lean` verifies
`ae_tendsto_normalizedFiniteEnergyTentError` and
`beurling_finiteEnergyBoundary_re_eq_zero_on_unit_gap` with the same three axioms.
The recurrence conclusion reuses the audited common-return and atomic-floor
lemmas from `ExactEventTheory/TentRecurrenceOfIntegrableDefects.lean`.

Origin extraction and full finite-energy prime classification are further
obligations; height replication remains open.
