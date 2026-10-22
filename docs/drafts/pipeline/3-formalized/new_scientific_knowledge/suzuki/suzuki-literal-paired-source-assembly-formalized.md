# Literal completed Suzuki modes assemble into the paired primitive-flux equation, formalized

- **ID:** `suzuki-literal-paired-source-assembly`
- **Stage:** 3 — formalized in Lean 4
- **Claim:** `[PROVED HERE] [NEW SCIENTIFIC KNOWLEDGE]`
- **Paper proof:** `./suzuki-literal-paired-source-assembly.md`
- **Lean:**
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiLiteralPairedSourceAssembly.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiPairedSourceL2Bound.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiPairedCutoffEventGeometry.lean`
  - `formal/GaloisForLFunctions/RHTower/Suzuki/SuzukiCoordinateCutoffPrimitiveFlux.lean`
  - `formal/GaloisForLFunctions/HTGeometry/SmoothTransitionDerivBound.lean`
  - `formal/GaloisForLFunctions/HTGeometry/ExponentialPolynomialLatticeWeight.lean`
  - `formal/GaloisForLFunctions/HTGeometry/LpSingleExtension.lean`

## Formal content

| Card | Lean |
|---|---|
| `(1)` the two rooted centre families | `suzukiSeamLocation` |
| `(2)` the paired-source profile | `pairedSourceEntry` |
| `(3)` the uniform `ℓ²` bound | `abs_pairedSourceEntry_le`, `sq_pairedSourceEntry_le`, `tsum_sq_pairedSourceEntry_le`, `summable_sq_pairedSourceEntry` |
| `(4)`, `(14)` the buffer arguments and the canonical cutoff | `suzukiRightScaleBufferArgument`, `suzukiLeftScaleBufferArgument`, `suzukiScaleBufferedCutoff`, `suzukiRightScaleBufferArgument_eq`, `suzukiLeftScaleBufferArgument_eq` |
| `(15)` literal aperture support | `suzukiScaleBufferedCutoff_ne_zero_iff` |
| item 2, the uniform cutoff derivative bound | `exists_bound_deriv_smoothTransition`, `deriv_smoothTransition_eq_zero_of_notMem`, `hasDerivAt_rightScaleBufferArgument`, `hasDerivAt_leftScaleBufferArgument`, `abs_deriv_transition_bufferArgument_le`, `abs_deriv_scaleBufferedCutoff_le` |
| `(5)`, `(20)` the two event windows | `rightEvent_window`, `leftEvent_window` |
| item 4, the root behaviour | `rootOutward_cutoff_eq_zero`, `rootInward_cutoff_eq_one` |
| `(11)`, `(12)` the rooted prime transport | `suzukiSeamLocation_add_sourceOrientedStep`, `suzukiSeamLocation_sub_sourceOrientedStep` |
| `(13±)` marked descendants plus centre constants | `suzuki_primeTranslate_sub_centered`, `suzuki_primeTranslate_add_centered` |
| `(6)`–`(9)`, `(18)`, `(19)` the exact source identity | `twoLPlus`, `linearCommutator`, `primitiveCutoffFlux_pointwise`, `primitiveCutoffFlux_with_zeroOrder_pointwise`, `literalPairedCutoffSourceAssembly_pointwise` |
| §6 the vector-valued distribution extension | `tendsto_sum_single`, `ext_of_eq_on_single`, `eq_zero_of_eq_zero_on_single` |
| `(10)`, `(21)` the finite-recurrence weighted source estimate | `summable_nat_polyGeom`, `summable_int_polyGeom`, `summable_prod_polyGeom`, `one_add_sum_le_prod`, `summable_latticeExpPoly`, `summable_recurrenceSourceWeight` |

## What the card actually closes

**The cutoff is canonical, not adapted.**  The scale-buffered cutoff is a product of two transitions
in the affine arguments `A^R(L) = e^L(a−x) − o` and `A^L(L) = e^L(a+x) + o`, and it is nonzero
*exactly* when the sampled point lies in the open aperture.  So multiplying by it never invokes the
interior equation outside its literal support — that is a theorem about the cutoff, not a
construction hypothesis.

**The derivative bound is a support fact.**  `(A^R)' = A^R + o` is unbounded in `L`, so the chain
rule alone gives nothing.  What saves it is that `ϑ'(A^R)` vanishes unless `A^R ∈ [0,1]`, and *there*
`|A^R + o| ≤ 2` for `|o| ≤ 1`.  Hence `|χ'| ≤ 4Λ` uniformly in the aperture, the coordinate, the
orientation and the scale, with `Λ` the derivative bound of the fixed transition — itself now a
theorem, since the transition is smooth and locally constant off `[0,1]`, so its derivative is
continuous with support in a compact interval.

**The events are `O(1)` wide and logarithmically placed.**  The same support restriction forces
`e^L(a−x) ∈ [1,2]` for the inward orientation, hence `−log(a−x) ≤ L ≤ log 2 − log(a−x)`: the block
sits at `−log|a−x|` and has width exactly `log 2`.  With the two rooted centre families this is the
card's `(20)`: transition times are `−log|ℓ(ν)| + O(1)` and `−log|2a − ℓ(ν)| + O(1)`.  At a physical
root the outward puncture cutoff is identically zero — its right argument is the constant `−1` — and
the inward one is eventually one.

**The source is uniformly `ℓ²`.**  Each coordinate is a weighted centred difference, so it is at
most `2‖u‖_∞ w_κ(ν)` using only boundedness of `u`; no continuity or modulus of continuity is
needed, and the bound does not depend on `L`.

**The weighted estimate is a lattice fact.**  A geometric weight in the `ℓ¹` length beats any fixed
polynomial factor, because both split over coordinates — exactly for the geometric one, and by
`1 + Σaᵢ ≤ ∏(1+aᵢ)` for the polynomial one.  With a recurrence clock `τ_ν ≤ R|ν|₁ + c` and a slope
gap `σR < κ`, the source weight `e^{−2κ|ν|₁}e^{2στ_ν}(1+τ_ν)^N` is summable.

**The assembly needs no exchange of limits.**  Every `ℓᵖ` vector is the unconditional sum of its
coordinate singles, so the finitely supported vectors are dense and two continuous linear maps
agreeing on singles agree everywhere.  Only finitely many coordinates are ever tested at once; the
passage to the whole carrier is continuity of the pairing, not an interchange of an infinite sum
with an integral.

## A note on the constant in `(3)`

The card displays `sup_L ‖F(L)‖_ℋ ≤ 2√2 ‖u‖_∞ ‖w_κ‖_{ℓ²}`.  Each entry is at most
`2‖u‖_∞ w_κ(ν)`, and the index set `{+,−} × G × {±1}` carries four sign combinations per `ν`, so
the direct bound against `‖w_κ‖_{ℓ²(G)}` is `4‖u‖_∞‖w_κ‖_{ℓ²(G)}`, which is larger than `2√2`.  The
display is correct under the reading in which `‖w_κ‖_{ℓ²}` is the norm over the whole index set
`ℋ`: there the bound is `2‖u‖_∞‖w_κ‖_{ℓ²(ℋ)}`, and `2 ≤ 2√2`.  The Lean statement is indexed by an
arbitrary type and proves the constant `2` against the norm over whichever index set is supplied, so
it yields the card's display under that reading and does not assert the other.

## Hypotheses

Object data only: the aperture, the centres, the orientations with `|o| ≤ 1`, the scale, the weight,
the eigenmode `u` with a sup bound, and — for the recurrence estimate — the linear clock bound and
the slope gap.  These are the card's own hypotheses.  The `ℓ²` and density statements are indexed by
an arbitrary type, so nothing about the two-coset structure is assumed beyond what the card
specifies.  No `sorry`, `axiom`, `opaque` or `unsafe`; every theorem named above audits to
`[propext, Classical.choice, Quot.sound]`.

## Open boundary

What stays open is what the card declares open, and all of it is research rather than missing Lean:
arbitrary finite-order expansion of every assembled completed mode, isolation of the all-orders-flat
residual, finite-type trace-zero `H¹₀`, recurrence-infinite apertures, and raw Evans positivity.
The assembly gate itself — the exact two-coset source equation with correct signs, canonical
support, uniform event geometry and a finite-recurrence weighted class — is closed.
