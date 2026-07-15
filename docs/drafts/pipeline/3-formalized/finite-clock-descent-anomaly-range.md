# Finite clock shadows are exactly source-descent anomalies

- **ID:** `finite-clock-descent-anomaly-range`
- **Stage:** 3-formalized
- **Type:** GENERAL HT NECESSITY THEOREM / FINITE COMPARISON GEOMETRY
- **Scientific status:** `[LEAN-FORMALIZED] [PRODUCT-TOPOLOGY NO-GO LEAN-FORMALIZED] [SIGNIFICANT MECHANISM] [NOVELTY UNVERIFIED]`
- **Parent:** `../1-in-progress/clock-descent-anomaly.md`
- **Statement:** If homogeneous source solutions realize every finite clock observation, then the
  range of any proposed finite shadow is exactly the range of its failure to descend from the
  source constraint. Exact finite intertwining therefore forces the shadow to be zero.

## Theorem

Let `S : V -> V` be a linear source constraint, `q : V -> O` a finite observation, `T : O -> O`
a proposed shadow, and `W subset ker(S)` a space of genuine homogeneous source variations. Put

```text
alpha = T q - q S.                                        (1)
```

If `q|W : W -> O` is surjective, then

```text
range(alpha|W) = range(T).                                 (2)
```

Indeed, for `w in W`, `S(w)=0`, hence `alpha(w)=T(q(w))`; surjectivity gives both range
inclusions. Therefore:

```text
alpha|W=0  implies  T=0,                                  (3)
q S = T q  implies  T=0.                                  (4)
```

Equation `(2)` is the positive statement left by `(4)`: every nonzero value of a finite shadow is
not descended source information but an actual comparison anomaly on a genuine source solution.

## Faithful-chart covariance

For invertible source and observation charts `eV` and `eO`, conjugate `S`, `q`, and `T` in the
usual way. Their anomaly satisfies

```text
alpha' = eO alpha eV^(-1).                                (5)
```

Thus the finite comparison object is intrinsic up to faithful linear representation. This does
not yet establish invariance under completion or inequivalent source topologies.

## Lean declarations

`GaloisForLFunctions.HTGeometry.ClockDescentAnomaly` contains:

- `clockDescentAnomaly` and `clockDescentAnomaly_on_sourceKernel`;
- `range_clockDescentAnomaly_domRestrict_eq_range_shadow`;
- `finiteShadow_eq_zero_of_anomaly_eq_zero_on_sourceKernel`;
- `finiteShadow_eq_zero_of_intertwines`;
- `tateClockFiniteObservation`;
- `tateClockFiniteShadow_range_eq_descentAnomaly`;
- `clockSourceInChart`, `clockObservationInChart`, `clockShadowInChart`;
- `clockDescentAnomaly_inChart`.
- `clockDescentAnomaly_truncate`.
- `quotientShadow_eq_zero_of_anomaly_mem_kernel`.
- `denseRange_subtype_of_tateClockFiniteObservableSurjective`;
- `continuousLinearMap_eq_zero_of_tateClockFiniteObservableSurjective`.

The last declaration proves the quotient form: if the anomaly of a source solution lies in a
declared quotient kernel and source solutions cover all quotient observations, the induced
quotient shadow vanishes.

The two topology declarations prove that a finite-observably free source tangent is dense in the
raw product clock and that every Hausdorff continuous linear observation annihilating it is zero.
Thus a nonzero constraint boundary requires a source-selected topology finer than the product
clock topology.

The new module had no cached object, so it received exactly one targeted module build followed by
one direct source check. After adding chart covariance, only the direct source check was rerun.
No full or concurrent Lean build was used.

## Scientific boundary

The algebraic proof of `(2)` is elementary. Noncommuting squares, mapping cones, and operator
defects are parent theory. The research content is the forced interpretation supplied by HT
finite freedom: no nonzero finite operator can be the constraint, and the entire proposed shadow
range is comparison failure rather than an approximation error. The coherent, self-dual
source-topological anomaly remains conjectural and is the candidate field-level object.

## Gates

- [x] exact range law proved on paper
- [x] exact range law formalized in Lean
- [x] zero-shadow no-go formalized
- [x] faithful finite-chart covariance formalized
- [x] truncation coherence formalized
- [x] quotient-shadow collapse formalized
- [x] product-density and Hausdorff-observation no-go formalized
- [ ] coherent pro-anomaly constructed
- [ ] source-topological chart invariance proved
- [ ] self-dual comparison cone constructed
- [ ] independent novelty/significance audit
