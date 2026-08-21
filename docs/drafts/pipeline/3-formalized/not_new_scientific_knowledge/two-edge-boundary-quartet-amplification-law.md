# Two-edge boundary profiles exponentially amplify every fixed off-line quartet

- **ID:** `two-edge-boundary-quartet-amplification-law`
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper) / POSITIVE NONCOMPACT DETECTOR LAW / `[BRIDGE]`
- **Scientific status:** `[PROVED HERE] [NOT NEW SCIENTIFIC KNOWLEDGE] [NOT AN RH PROOF]`
- **Parent results:** Mellin translation, elementary exponential sums, and
  `ht-weil-compact-detector-near-radical-alternative.md`
- **Statement:** The two-edge boundary families that asymptotically saturate the CCM frame detect
  every fixed off-line FE--Schwarz quartet: its Weil contribution has exponentially growing
  oscillatory amplitude and is negative along a cofinal aperture sequence, while an all-line
  reference divisor contributes only a uniformly bounded amount. More generally, a finite
  horizontally isolated rightmost off-line layer is detected. The remaining zeta globalization
  problem is to remove the rightmost-layer hypothesis.

## 1. Two-edge Mellin transform

Fix `L>0` and a nonzero real function

```text
f in C_c^infinity(0,L).                                      (1)
```

For `a>L`, put

```text
phi_a(x)=f(a-|x|),
G_a(1/2+w)=integral_R phi_a(x)exp(w x)dx.                     (2)
```

Define the one-sided Laplace transforms

```text
A_f(w)=integral_0^L f(s)exp(-w s)ds.                          (3)
```

Changing variables on the right and left boundary layers gives the exact identity

```text
G_a(1/2+w)
 =exp(a w)A_f(w)+exp(-a w)A_f(-w).                            (4)
```

Because `phi_a` is even,

```text
G_a(1/2-w)=G_a(1/2+w).                                      (5)
```

## 2. Fixed-quartet amplification

Let

```text
w=delta+iT,       delta>0, T>0,                              (6)
```

and insert the FE--Schwarz quartet `1/2 plus_or_minus w` and
`1/2 plus_or_minus conjugate(w)` into an all-line reference divisor. Its Weil-form contribution is

```text
Delta_(delta,T)(phi_a)
 =4 Re[G_a(1/2+w)G_a(1/2-w)]
 =4 Re[G_a(1/2+w)^2].                                       (7)
```

Expanding `(4)` gives

```text
Delta_(delta,T)(phi_a)
 =4exp(2a delta)
    Re[exp(2iaT)A_f(w)^2]
  +8 Re[A_f(w)A_f(-w)]
  +4exp(-2a delta)
    Re[exp(-2iaT)A_f(-w)^2].                                (8)
```

Assume `A_f(w) !=0`. Choose a cofinal sequence `a_j` such that

```text
Re[exp(2ia_j T)A_f(w)^2]=-|A_f(w)|^2.                        (9)
```

This is possible because `a` is a continuous aperture parameter and `T>0`. Equations `(8)`--`(9)`
give

```text
Delta_(delta,T)(phi_(a_j))
 =-4exp(2a_j delta)|A_f(w)|^2+O_f,w(1)
 ->-infinity.                                                (10)
```

The condition `A_f(w)!=0` is generic and can always be achieved: evaluation at `w` is a nonzero
continuous linear functional on `C_c^infinity(0,L)`.

## 3. Uniformly bounded all-line background

For the all-line carrier in `ht-weil-compact-detector-near-radical-alternative.md`, the centered
zero ordinates are the real points `plus_or_minus(alpha+n)`. At a real ordinate `t`, equation `(4)`
has no exponential aperture factor:

```text
|G_a(1/2+it)|<=|A_f(it)|+|A_f(-it)|.                          (11)
```

The right side decays faster than every power of `|t|`, uniformly in `a`. Hence the all-line Weil
form obeys

```text
sup_(a>L) W_0(phi_a)<infinity.                                (12)
```

Combining `(10)` and `(12)`, the quartet-augmented form is negative along the cofinal sequence:

```text
W_(delta,T)(phi_(a_j))<0                                     (13)
```

for all sufficiently large `j`.

Thus the two-edge family realizes the test-escape branch of the compact-detector alternative: its
support aperture grows, its all-line margin is asymptotically near-radical relative to the CCM
frame scale, and every fixed transverse quartet is nevertheless detected.

## 4. Finite isolated rightmost layer

The same argument applies to a finite set of off-line quartets

```text
w_k=delta_k+iT_k,
delta_* =max_k delta_k>0,                                    (14)
```

provided the layer `delta_k=delta_*` is nonempty and its leading coefficients do not all vanish.
After division by `exp(2a delta_*)`, every lower layer disappears and the leading contribution is a
nonzero real trigonometric polynomial

```text
P_f(a)=4 Re sum_(delta_k=delta_*)
  m_k exp(2iaT_k)A_f(w_k)^2.                                 (15)
```

It has zero Bohr mean because every `T_k>0`. A nonzero real trigonometric polynomial of zero mean
cannot be nonnegative everywhere. By almost periodic recurrence it is bounded above by a negative
constant along a cofinal sequence. Therefore the full augmented Weil form is negative along that
sequence.

The proof remains valid for an infinite divisor if the maximal transverse layer is finite and the
remaining divisor has a uniform horizontal gap `delta<=delta_*-epsilon` together with the standard
locally uniform zero-sum bounds.

## 5. Globalization is complete

Existence of an off-line zeta zero does not imply that

```text
sup_rho |Re rho-1/2|                                        (16)
```

is attained, that the rightmost layer is finite, or that it is separated by a horizontal gap. The
finite-layer argument above therefore cannot by itself handle the complete divisor.

This gap is closed in
`../new_scientific_knowledge/cofinal-two-edge-weil-completeness-landau-oscillation.md`. For every
fixed nontrivial boundary window, a residual set of real smooth profiles satisfies

```text
RH false
 ->liminf_(a->infinity)QW(phi_(a,f),phi_(a,f))=-infinity.     (17)
```

The proof applies Landau's oscillation theorem to the full exponential divisor sum. Its Laplace
transform has genuine poles at every off-line centered zero, its convergence abscissa is twice the
supremal transverse displacement, and it is holomorphic at the corresponding real point because
there is no real nontrivial zeta zero. Eventual one-sided boundedness would force a singularity at
that real abscissa, a contradiction. This removes the attained-layer hypothesis completely.

Thus the two-edge boundary carrier is a complete RH detector. The remaining CCM obligation is the
source-side cofinal lower-frame/nonnegativity theorem.

## Classification

The fixed-quartet and finite-layer proofs are elementary exponential-sum arguments. They are the
positive counterpart of the compact-detector obstruction, but remain a bridge rather than new
scientific knowledge.

## Lean formalization

Status: **complete and unconditional** for every theorem of this card (§§1--4).

Module `formal/GaloisForLFunctions/RHTower/TwoEdgeBoundaryQuartet.lean`.

**§1.**  `edgeLaplace`, `twoEdgeTransform`, **`twoEdgeTransform_eq`** — **equation `(4)`**,
`G_a(w) = e^{aw} A_f(w) + e^{-aw} A_f(-w)`, proved by the two boundary-layer substitutions
`x = a - s` and `x = s - a`.  No smoothness or decay of `f` is used, only that the layers are
`[a-L, a]` and its reflection.  `twoEdgeTransform_neg` is **equation `(5)`**.

**§2.**  `quartetEdge`, `quartetContribution` (**`(7)`**), `quartetContribution_eq_mul`,
**`quartetContribution_expand`** (**`(8)`**).  `apertureSeq` is the aperture sequence
`a_k = (π - 2 arg A_f(w) + 2πk)/(2T)`, and **`exp_apertureSeq_mul_sq`** is **equation `(9)`**: at
those apertures `e^{2ia_kT} A_f(w)²` is *exactly* `-‖A_f(w)‖²`.  `apertureSeq_atTop`,
`quartetContribution_apertureSeq_le` and **`tendsto_quartetContribution_atBot`** give **equation
`(10)`**: the quartet contribution tends to `-∞`.

**§3.**  `norm_twoEdgeTransform_imaginary_le` is **equation `(11)`**;
`abs_quartetContribution_imaginary_le`, `summable_quartetContribution_imaginary` and
**`abs_tsum_quartetContribution_imaginary_le`** give **equation `(12)`**: the all-line background
is bounded by `4 ∑ (‖A_f(it_n)‖ + ‖A_f(-it_n)‖)²`, *uniformly in the aperture*.  The summability of
that divisor sum is the all-line carrier's own datum, exactly as on the card.
**`eventually_augmented_neg`** is **equation `(13)`**: against any uniformly bounded background the
augmented form is negative along the aperture sequence.

**§4.**  `trigPoly`, `trigPoly_sq`, `conj_trigPoly`, `trigPoly_normSq`, `trigPolyRe_sq`,
`norm_integral_oscillatory_le'`, `norm_integral_indexedSum_le`, and
**`abs_integral_trigPolyRe_sq_sub_le`** — the mean-square (Parseval) law
`|∫_0^Y P² - (Y/2) ∑ ‖c_j‖²| ≤ C`, where the frequencies occurring in `P²` are `T_j + T_k > 0` and
`T_j - T_k ≠ 0`.  From it, **`exists_neg_trigPolyRe`** is **equation `(15)`**: a nonzero finite real
trigonometric polynomial with distinct strictly positive frequencies drops below a fixed negative
level at arbitrarily large apertures.  The proof is elementary — if `P ≥ -η` on a ray then
`Q = P + η ≥ 0` satisfies `∫ Q² ≤ (B+η) ∫ Q`, which is `O(1) + O(ηY)`, contradicting the linear
growth `(Y/2)∑‖c_j‖²` once `(B+η)η < (∑‖c_j‖²)/2`.  **No almost-periodic theory is used.**

Every declaration depends only on `propext`, `Classical.choice`, `Quot.sound`.

§5 is the statement of a *different* card
(`../new_scientific_knowledge/cofinal-two-edge-weil-completeness-landau-oscillation.md`) and is not
an obligation here.

## Gates

- [x] exact two-edge Mellin transform computed
- [x] fixed off-line quartet exponentially amplified
- [x] all-line background proved uniformly bounded
- [x] cofinal negative detector sequence constructed
- [x] finite isolated rightmost layer detected
- [x] nonattained-transverse-indicator obstruction isolated
- [x] prove the full zeta divisor globalization theorem `(17)`
- [ ] prove the source-side lower-frame inequality
- [ ] RH
