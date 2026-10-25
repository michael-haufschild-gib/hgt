# Zero cutoffs remove the smooth Vaughan obstruction

- **ID:** vaughan-zero-cutoffs-remove-the-smooth-obstruction
- **Stage:** 2-fully-proven
- **Type:** THEOREM (paper)
- **Source:** ../1-in-progress/q-i-selective-square-root-band.md
- **Statement:** When either Vaughan cutoff is zero, the admitted coefficient dimension below half damping is three or four according to admission of the actual receiver. At half damping it is four. This gives the exact boundary of the positive-cutoff dimension law.
- **Novelty status:** Algebraic corollary of the checked fixed-packet normal form; no external novelty claim.

## Exact degeneracy

Let `U=0` or `V=0`. The finite harmonic product `H_U H_V` is zero, so the smooth
coefficient `Q_w=c_ε H_U H_V(w_3-w_2)` vanishes for every coefficient vector.
The literal small-small piece `p_2` is identically zero, since one finite sum is empty.
Likewise `A_U A_V=0`, so its linear mean `c_2` is zero.

For every `ε>0`, admission reduces to

`B(P_w) ↔ L_w=0 and (w_3=0 or B(I_ε))`.

There is no equation on `w_2-w_3`. This is precisely where the positive-cutoff use of
finite Möbius harmonic nonvanishing ceases to apply.

The conclusion holds beyond the range of the smooth-power normal form. Replace `w_2`
by `w_3`: because `p_2=c_2=0`, neither the packet nor its linear mean changes. The
checked all-damping theorem
`pmPronicVaughanPacketAdmitted_iff_of_equal_convolution_coefficients` then applies after
linear centering. Necessity of zero linear mean holds at every positive damping.

## Exact coefficient spaces

Write `e_2=(0,0,1,0,0)` and retain the checked paid vectors
`b_U=(1,0,0,0,A_U/ρ)` and `b_V=(0,1,0,0,A_V/ρ)`.
For every `w` with `L_w=0`, direct substitution into the explicit mean vector gives

`w=(w_0-w_3)b_U+(w_1-w_3)b_V+(w_2-w_3)e_2+w_3(1,1,1,1,1)`.

The displayed four vectors are independent: coordinates 3, 2, 1, and 0 successively
recover all coefficients. The first three are always admitted; `e_2` gives the zero
packet. The last vector gives exactly the original interior receiver.

Thus the admitted subspace is the span of the first three vectors when the receiver
is not admitted, and the span of all four when it is admitted. Its dimension is
respectively three or four, and its coefficient quotient has dimension two or one.
All representations are unique by the same coordinate argument.

At `ε=1/2`, the actual interior receiver is admitted by the existing source budget and
the checked interior/source equivalence. The fixed normal form still applies. Since
the smooth coefficient is already zero, admission is exactly `L_w=0`, with dimension
four. For `ε>1/2`, the separate uniform critical-Wiener argument gives the same
dimension four for all cutoffs.

## Status

The general fixed-cutoff admission equivalence and the explicit mean, packet, and paid
vectors passed Lean audits. Five zero-cutoff and coefficient-replacement lemmas, including
the all-positive-damping admission equivalence, are drafted in `/tmp/QIZeroCutoffTools.lean`,
uncompiled. `/tmp/QIZeroCutoffDimensionsTools.lean` now drafts the four-vector
representation, independent frames, exact admitted spans, dimensions three/four, and
the quotient dimension test; those ten declarations remain uncompiled. Its imports
name the planned coefficient-space and zero-cutoff repository leaves, which have not
yet been created. The endpoint uses the
dependency-closed half-damping paper theorem. No receiver admission below half damping
is inferred.
