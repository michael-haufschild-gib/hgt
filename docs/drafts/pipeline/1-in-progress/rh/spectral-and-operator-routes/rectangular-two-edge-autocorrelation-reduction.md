# The rectangular Weil bridge is one explicit piecewise-linear autocorrelation

- **ID:** `rectangular-two-edge-autocorrelation-reduction`
- **Stage:** 1-in-progress
- **Type:** REDUCTION (paper) + FORMALIZATION PLAN
- **Scientific status:** `[PAPER-PROVED]` `[NOT NEW MATHEMATICS — it is an explicit computation]`
  `[NOT AN RH PROOF]`
- **Closes the vagueness in:** `ccm-critical-mellin-adjacent-block-subpower-lower.md`, gate
  *"formalize the critical-Mellin Stieltjes/autocorrelation identity"* (line 204), whose §"Formal
  endpoint" (line 188) identifies it as the bridge *from `I_L(n)` to the actual rectangular Weil
  value*.
- **Statement:** that bridge is the specialization of the already-formalized autocorrelation carrier
  to the two-edge rectangular window, and the required autocorrelation is an **explicit piecewise
  linear function** — a triangle at the origin plus a trapezoid at the far lag. No asymptotics, no
  PSWF, no oscillatory analysis enters.

## 1. Both endpoints are already in the tree

This is worth stating first, because the gate reads as if a whole analytic layer were missing.

| Needed | Already formalized |
|---|---|
| the carrier identity `(18)` | `RHTower/CCM/CCMPolarPrimeStieltjesAutocorrelation.lean` — `polarPrimeAutocorrelationQuadratic_eq_integral_sub_sum`, with `apertureAutocorrelation v h = ∫ v(x+h) conj(v x) dx` |
| the symbol identity `(18a)` | same module — `correctedCCMSymbol_eq_archimedean_add_stieltjes` |
| the cumulative critical-error form `(20)` | same module — `criticalMellinStieltjesCumulative_eq_criticalErrorForm` |
| Stieltjes integration by parts `(19)` | same module — `polarPrimeAutocorrelationQuadratic_integrationByParts_of_support` |
| the rectangular Weil value | `RHTower/CCM/CCMRectangularScrewCurvature.lean` — `xiWeilPolarization_rectangular_logSample_eq_xiScrewWindowCurvature` |
| the two-edge transform | `RHTower/CCM/CCMRectangularTwoEdge.lean` — `rectangularTwoEdgeTransform`, `xiRectangularTwoEdgeTransform` |

**Missing: only the physical-side autocorrelation of the two-edge window, and its pairing.**

## 2. Identifying the physical vector

`RHTower/CCM/CCMRectangularTwoEdge.lean` defines

```text
rectangularWindowAmplitude L w = (1 - exp(-L w))/w = integral_0^L exp(-w t) dt,
rectangularTwoEdgeTransform L a w
   = exp(a w) * A_L(w) + exp(-a w) * A_L(-w).
```

Since `exp(a w) A_L(w) = integral_0^L exp(w(a-t)) dt = integral_(a-L)^a exp(w u) du` and
`exp(-a w) A_L(-w) = integral_(-a)^(-a+L) exp(w u) du`, the transform is the bilateral Laplace
transform of the **two-edge indicator**

```text
v_(L,a) = 1_[a-L, a] + 1_[-a, -a+L].                                   (1)
```

So the "two rectangles placed at the two edges" of the definition's docstring is literally that
function, and the transform side already in the tree is its transform. This identification is the
first thing to formalize, because everything else is downstream of it.

## 3. The autocorrelation, explicitly

Let `A = [a-L, a]`, `B = [-a, -a+L]`, and assume `0 < L ≤ a`. For `h ≥ 0`,

```text
C(h) = |A ∩ (A-h)| + |B ∩ (B-h)| + |A ∩ (B-h)| + |B ∩ (A-h)|.
```

*Self terms.* `|A ∩ (A-h)| = |B ∩ (B-h)| = (L - h)_+`.

*Cross term `A ∩ (B-h)`.* `B - h = [-a-h, -a+L-h]` lies entirely to the left of `A = [a-L,a]`
whenever `-a+L-h < a-L`, i.e. `h > 2L - 2a`, which holds for all `h ≥ 0` when `L ≤ a`. So this term
is **zero**.

*Cross term `B ∩ (A-h)`.* `A - h = [a-L-h, a-h]`. Intersecting with `B = [-a, -a+L]`:

```text
|B ∩ (A-h)| = ( min(a-h, -a+L) - max(a-L-h, -a) )_+ .
```

Splitting at `h = 2a - L`:

```text
h < 2a - 2L        : 0
2a - 2L ≤ h ≤ 2a-L : 2L - 2a + h            (rising edge)
2a - L ≤ h ≤ 2a    : 2a - h                 (falling edge)
h > 2a             : 0
```

Hence, for `0 < L ≤ a` and `h ≥ 0`,

```text
C_(L,a)(h) = 2 (L - h)_+  +  T_(L,a)(h),                                (2)
```

with `T_(L,a)` the trapezoidal bump supported in `[2a-2L, 2a]`, rising linearly from `0` at
`2a-2L` to `L` at `2a-L`, then falling linearly to `0` at `2a`. Its peak value is `L` and its total
mass is `L^2`. Note `C_(L,a)(2a) = 0`, which is exactly the hypothesis of the already-formalized
`apertureAutocorrelation_two_mul_eq_zero`, and the reason the integration-by-parts form `(19)` is
available for this family.

`C` is **real, nonnegative, piecewise linear, compactly supported in `[-2a, 2a]`, and even**.

## 4. The consequence — the bridge is a finite explicit pairing

Substituting `(2)` into the formalized carrier `(18)`:

```text
Q_polarprime(v_(L,a)) = 2 Re integral_(0,2a) C_(L,a)(h) dR(h)
  = 2 [ integral_0^L 2(L-h) 2cosh(h/2) dh + integral_(2a-2L)^(2a) T_(L,a)(h) 2cosh(h/2) dh ]
    - 2 [ sum_(n ≤ e^L) Λ(n) n^(-1/2) · 2(L - log n)
        + sum_(e^(2a-2L) ≤ n ≤ e^(2a)) Λ(n) n^(-1/2) · T_(L,a)(log n) ].     (3)
```

Every continuous integral in `(3)` is elementary (`∫ (L-h)cosh(h/2) dh` and two linear-times-`cosh`
integrals). The two prime sums are exactly the near-lag and far-lag von Mangoldt blocks. **This is
the `I_L(n)` of `ccm-critical-mellin-adjacent-block-subpower-lower.md` in closed form**, and it
explains its "adjacent block" name: the far-lag block sits at `log n ∈ [2a-2L, 2a]`, i.e. at
`n ∈ [e^(2a)/e^(2L), e^(2a)]`, one dyadic-type block adjacent to the cutoff.

## 5. Formalization plan, in dependency order

1. `indicator_autocorrelation_eq_triangle` — for a single interval,
   `∫ 1_[c,d](x+h) 1_[c,d](x) dx = ((d-c) - |h|)_+`. Elementary, reusable, and absent from mathlib
   in this form.
2. `twoEdgeIndicator` — define `(1)` and prove its bilateral transform is
   `rectangularTwoEdgeTransform L a`. This is the identification of §2 and is the load-bearing link
   between the physical and transform sides.
3. `twoEdgeAutocorrelation_eq` — `(2)`, by bilinearity of the autocorrelation over the two
   indicators plus step 1 and the vanishing cross term.
4. `twoEdge_apertureAutocorrelation_two_mul_eq_zero` — immediate from `(2)`, feeding the existing
   integration-by-parts theorem.
5. The pairing `(3)`, by substituting into
   `polarPrimeAutocorrelationQuadratic_eq_integral_sub_sum`.

Steps 1, 3, 4 are elementary real analysis. Step 2 is a Fubini/Laplace computation. Step 5 is
substitution. **None of it needs PSWF, Fuchs, Dunster, or any asymptotic** — which is the point of
writing this card: the gate looked analytic and is not.

## 6. Honest status

- This is **not new mathematics**. It is an explicit computation that turns a vaguely stated gate
  into a finite dependency list with both endpoints already in the tree.
- It does not prove the subpower lower bound, which is the RH-bearing content of the parent card.
  It supplies the bridge that card names as its only missing paper-to-Lean link.
- The restriction `L ≤ a` is used in §3 to kill the `A ∩ (B-h)` cross term. For `L > a` the two
  rectangles overlap and `(2)` acquires a third piece; the parent card's regime is `L` fixed and
  `a = log(n)/2 → ∞`, so `L ≤ a` holds eventually and is the only regime needed.

## Gates

- [x] identify the physical two-edge vector behind the existing transform
- [x] compute the autocorrelation explicitly, including the vanishing cross term
- [x] verify `C(2a) = 0`, so the formalized integration-by-parts form applies
- [x] exhibit the closed form `(3)` and identify it with the parent card's `I_L(n)` shape
- [x] step 1: single-interval autocorrelation triangle in Lean —
      `formal/GaloisForLFunctions/RHTower/IntervalAutocorrelation.lean`, registered in the
      `GaloisForLFunctions.RHTower` umbrella, axiom-clean:
      `inter_shift_Icc` (the two shifted constraints cut out `Icc (max c (c-h)) (min d (d-h))`),
      `min_sub_max_eq` (its length is `(d-c) - |h|`), and
      `integral_indicator_Icc_shift_mul` :
      `∫ 1_[c,d](x+h) · 1_[c,d](x) dx = max ((d-c) - |h|) 0`.
- [x] step 2: transform identification in Lean — same module:
      `integral_indicator_Icc_mul_exp` (bilateral transform of one interval indicator) and
      `integral_twoEdgeIndicator_mul_exp` :
      `∫ twoEdgeIndicator L a x · exp(w x) dx = rectangularTwoEdgeTransform L a w` for `w ≠ 0`.
      This is the load-bearing physical/transform link: the corpus's transform-side object is now
      *proved* to be the transform of the two-edge window, rather than asserted in a docstring.
- [x] steps 3 and 4 in Lean —
      `formal/GaloisForLFunctions/RHTower/TwoEdgeWindowAutocorrelation.lean`, registered in the
      `GaloisForLFunctions.RHTower` umbrella, axiom-clean:
      `twoEdgeIndicator L a` (the physical window `1_[a-L,a] + 1_[-a,-a+L]`),
      `conj_twoEdgeIndicator`,
      `twoEdge_apertureAutocorrelation_eq` (the **exact four-term overlap form, with no hypotheses
      at all on `L`, `a`, `h`**),
      `twoEdge_backward_cross_eq_zero`,
      `twoEdge_apertureAutocorrelation_eq_of_le` (`= 2(L-h)⁺ + far-lag cross term`, for `L ≤ a`,
      `h ≥ 0`), and
      `twoEdge_apertureAutocorrelation_two_mul_eq_zero`.
      **Correction found while formalizing:** the plan asserted `C(2a) = 0` would follow from the
      window being supported in the closed aperture and hence from the existing
      `apertureAutocorrelation_two_mul_eq_zero`.  That is **wrong** — the window equals `1` at
      `x = ±a`, so it does *not* satisfy that lemma's hypothesis `∀ x, x ≤ -a ∨ a ≤ x → v x = 0`.
      The vanishing at lag `2a` is true but had to be proved directly from the exact overlap
      formula (the overlap at that lag is a single point, of measure zero).
- [x] step 5: the pairing in Lean — same module:
      `continuous_twoEdgeOverlap`, `integrable_twoEdge_autocorrelation_mul_cosh` (the carrier's
      integrability hypothesis is **automatic** for this family, since the autocorrelation is the
      continuous piecewise-linear `twoEdgeOverlap`), and
      `twoEdge_polarPrimeAutocorrelationQuadratic_eq` :
      `polarPrimeAutocorrelationQuadratic a (twoEdgeIndicator L a)
         = 2∫_{(0,2a]} twoEdgeOverlap L a h · 2cosh(h/2) dh
           − 2 Σ_{k=2}^{⌊e^{2a}⌋} criticalMellinAtomWeight k · twoEdgeOverlap L a (log k)`,
      with **no hypotheses on `L` or `a` at all**.
      **The bridge is closed.** The parent card's only named paper-to-Lean link now exists as an
      unconditional theorem: the rectangular polar–prime carrier equals an elementary `cosh`
      integral of an explicit piecewise-linear profile minus that profile sampled on the von
      Mangoldt atoms.
- [ ] independent audit

## Log

- 2026-07-27 (Claude): written as the first output of the verify-or-close pass over the 48 open
  Lean gates in the prolate/CCM lane. The gate was `VERIFIED-OPEN`, but with both endpoints already
  formalized — the missing piece is elementary and is specified above.
