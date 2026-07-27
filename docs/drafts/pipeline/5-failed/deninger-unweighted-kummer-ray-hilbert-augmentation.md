# Unweighted Kummer-ray Hilbert augmentation

- **ID:** `deninger-unweighted-kummer-ray-hilbert-augmentation`
- **Stage:** 5-failed
- **Type:** FALSIFIED GREEN-DESCENT ROUTE
- **Label:** `DAC_UNWEIGHTED_KUMMER_RAY_HILBERT_AUGMENTATION_NO_GO`
- **Parent:** `deninger-kummer-poisson-green-boundary`
- **Claim tested:** suspend every projective Kummer harmonic ray,
  take their unweighted direct-sum Green energy, and descend to the
  single scalar radial Poisson complex by summing ray components.

## Hilbert quotient no-go

Let \(I\) be infinite, let \(H\ne0\) be a Hilbert space, and on the
finite-support direct sum define
\[
 \Sigma:\bigoplus_{i\in I}^{\mathrm{alg}}H\longrightarrow H,
 \qquad
 \Sigma((x_i))=\sum_i x_i.                                    \tag{1}
\]
Give the source the Hilbert direct-sum norm.

`[PROVED HERE]
[DAC_UNWEIGHTED_KUMMER_RAY_HILBERT_AUGMENTATION_NO_GO]`

The quotient seminorm induced by `(1)` is identically zero:
\[
 \inf_{\Sigma x=h}\sum_i\|x_i\|^2=0
 \qquad(h\in H).                                                \tag{2}
\]
Therefore the unweighted ray augmentation cannot transport a
strictly positive Green/Hodge metric to the scalar quotient.

### Proof

Choose \(N\) distinct indices and put \(x_i=h/N\) on them and zero
elsewhere.  Then \(\Sigma x=h\), while
\[
 \sum_i\|x_i\|^2
 =
 N\frac{\|h\|^2}{N^2}
 =
 \frac{\|h\|^2}{N}.
\]
Letting \(N\to\infty\) proves `(2)`.

## Weighted classification

For weights \(w=(w_i)\), define on finite-support vectors
\[
 \Sigma_w(x)=\sum_i\overline{w_i}x_i.                          \tag{3}
\]
This extends boundedly to \(\ell^2(I;H)\) exactly when
\(w\in\ell^2(I)\).  If \(w\ne0\), then
\[
 \inf_{\Sigma_wx=h}\|x\|_{\ell^2(I;H)}^2
 =
 \frac{\|h\|^2}{\|w\|_{\ell^2(I)}^2}.                          \tag{4}
\]

Indeed Cauchy--Schwarz gives the lower bound, and equality is attained
by
\[
 x_i=\frac{w_i}{\|w\|_2^2}h.
\]
Thus a nondegenerate Hilbert descent is equivalent to a nonzero
square-summable ray weight.

## Arithmetic consequence

Smooth suspension identifies each positive-rational orbit in the
nonzero Kummer lattice with one radial copy.  The algebraic
all-ones augmentation is canonical on finite-support nuclear
sections, but `(2)` proves that its Hilbert quotient loses all
positivity.

The missing source datum can therefore be stated sharply:
\[
 \boxed{\text{construct a canonical, Galois/correspondence-natural
 square-summable Kummer-ray density, or avoid raywise Hilbert
 quotienting.}}                                                \tag{5}
\]

No arbitrary enumeration or declared decaying weights are admissible.
The density must arise from the source Green operator, a transverse
measure/current, or a relative homological contraction before
completion.

## Strongest positive survivor

The unweighted sum remains continuous and meaningful on the
locally convex finite-support/nuclear direct sum.  Hence the valid
order remains:

1. smooth suspension and unit augmentation in the nuclear category;
2. take the scalar Poisson cohomology \(M_\zeta\);
3. descend a source-derived Green form only after proving its radical
   equals the augmentation kernel;
4. then complete the positive quotient.

Equivalently, a source transverse current may replace the raywise
Hilbert sum.  Its conservativity is part of the Hodge gate.

## Hostile audit

- The theorem does not reject nuclear augmentation.
- It classifies exactly when a raywise Hilbert quotient is positive.
- It does not choose a weight or assume its existence.
- No zeta zero, RH premise, CCM object, or numerical computation is
  used.

## Log

- 2026-07-27 — Proved collapse of the unweighted infinite-ray
  quotient norm, classified weighted positive descent, and retained
  nuclear-first augmentation as the positive survivor.
