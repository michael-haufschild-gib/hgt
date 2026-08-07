# Burnol divided-shift fixed-source leakage law

- **ID:** `burnol-divided-shift-source-leakage-law`
- **Stage:** 3-formalized
- **Type:** THEOREM, `[PROVED HERE] [FORMALIZED] [NOT AN RH PROOF]`
- **Statement:** at every actual right-half Xi divisor, the Mellin divided shift of one explicit
  co-Poisson sub-window atom has a quantitatively nonzero retained source projection.

## Goal and frontier delta

The previous Route R target asked for a pre-divisor subexponential/tightness upper bound on moving
zero-locus ladder kernels.  The exact cross-aperture Riesz law already in the corpus proves that
their exponential type is

```text
|Re rho - 1/2|.                                           (1)
```

Thus a direct subexponential estimate at every Xi zero is already RH-strength; generic Hilbert,
Sonine, reciprocal-seed, or finite-head estimates cannot produce it.  This card replaces the
unbounded ladder with one fixed-aperture source coordinate.  The replacement is not a renamed
tightness premise: it follows from the exact accretivity of Burnol's divided shift and gives a
quantitative lower bound on the source leakage forced by every hypothetical off-line zero.

## Conjecture loop

1. **Reciprocal closure forces tightness. — FALSIFIED.**  Reciprocal closure exchanges the two
   aperture orientations but leaves the exact type `(1)` unchanged.
2. **Subtracting a finite Mellin head forces tightness. — FALSIFIED.**  A fixed finite correction
   cannot change the cross-aperture exponential type.
3. **A co-Poisson annihilator zero makes the divided shift quotient-pure. — FALSIFIED, with positive
   survivor.**  Strict accretivity proves the opposite off the critical line: quotient-purity is
   impossible, and the retained source component has an explicit norm floor.

The third failure is the positive survivor formalized below.

## Theorem

Let `H = L²(R)` be the critical Mellin line and, for `Re rho > 1/2`, put

```text
delta = Re rho - 1/2 > 0,
m_rho(t) = 1 / (rho - (1/2 + i t)),
A_rho = M_{m_rho}.
```

Then

```text
Re m_rho(t) = delta |m_rho(t)|²,                         (2)
||m_rho||_infinity <= 1/delta,                           (3)
m_rho(t) != 0.                                           (4)
```

Consequently, for every `F in H`,

```text
Re <F, A_rho F> = delta ||A_rho F||².                    (5)
```

Let `S` be a closed source subspace, `F in S`, and `P_S` its orthogonal projection.  Since
`A_rho F - P_S A_rho F` lies in `S^perp`,

```text
<F, A_rho F> = <F, P_S A_rho F>.
```

Taking real parts and using Cauchy--Schwarz gives

```text
delta ||A_rho F||² <= ||F|| ||P_S A_rho F||.             (6)
```

Multiplication by the nowhere-zero symbol is injective.  Hence, for `F != 0`, the left side of
`(6)` is positive and

```text
P_S A_rho F != 0.                                        (7)
```

Transport `(5)`--`(7)` through the corpus's exact archimedean Mellin unitary.  Take `S` to be the
closed literal co-Poisson source space at aperture `b`.  Finally choose the explicit sub-window atom
`f_{c,d}`, with `0 < c < d` and `b = min(c,d^{-1})`; the existing source construction proves
`f_{c,d} in S` and `f_{c,d} != 0`.  For every actual Xi divisor point `rho` with
`Re rho > 1/2`,

```text
(Re rho - 1/2) ||A_rho f_{c,d}||²
  <= ||f_{c,d}|| ||P_S A_rho f_{c,d}||,

P_S A_rho f_{c,d} != 0.                                  (8)
```

No zero-location statement enters this proof; `rho` is used only as the Cauchy spectral parameter.

## Route R consequence

Define the remaining source producer to be the single fixed coordinate at `c=1/2`, `d=1`:

```text
for every right-half Xi divisor rho,
P_S A_rho f_{1/2,1} = 0.                                 (SF)
```

Theorem `(8)` contradicts `(SF)` at every right-half Xi divisor.  Therefore `(SF)` implies that Xi
has no zero in `Re s > 1/2`, and the existing unconditional `rh_iff_xi_ne_zero_right` closes RH.
This is formalized as
`riemannHypothesis_of_burnolXiDividedShiftSourceFlatness`.

This does **not** prove `(SF)`.  It changes the open core from a moving, unbounded-depth kernel bound
to annihilation of one explicit fixed-aperture projection.  Any proposed pre-divisor Stokes/Cartier
law can now be tested against one scalar/vector coordinate, and `(6)` quantifies exactly what it
must cancel.

## Literature boundary

Burnol's co-Poisson/Sonine work supplies the transform framework and divided-difference viewpoint,
but the fixed-source leakage inequality `(6)` and its explicit Xi-divisor instantiation `(8)` were
not found in the audited sources:

- J.-F. Burnol, *On Fourier and Zeta(s)*, arXiv:math/0112254.
- J.-F. Burnol, *Sur les espaces de Sonine associés par de Branges à la transformation de Fourier*,
  arXiv:math/0203120.
- J.-F. Burnol, *Entrelacement de co-Poisson*, Annales de l'Institut Fourier 57 (2007).

Classification: `[CORPUS-NEW SYNTHESIS]`; no claim of external priority.

## Lean certificate

Reusable measure-independent layer:

```text
formal/GaloisForLFunctions/HTGeometry/StrictAccretiveMultiplier.lean

lpBoundedMulCLM_re_inner_eq
lpBoundedMulCLM_inner_ne_zero_of_strictAccretive
lpBoundedMulCLM_not_mem_orthogonal_of_strictAccretive
lpBoundedMulCLM_sourceComponent_lower_bound
```

Burnol/Xi layer:

```text
formal/GaloisForLFunctions/RHTower/BurnolDividedShiftSourceLeakage.lean

re_burnolDividedShiftSymbol_eq
re_inner_burnolSpectralDividedShift_eq
re_inner_burnolMellinDividedShift_eq
burnolCoPoissonSourceProjection_mellinDividedShift_lower_bound
burnolCoPoissonSourceProjection_mellinDividedShift_ne_zero
xiDivisor_burnolSubWindow_mellinDividedShift_sourceProjection_lower_bound
xiDivisor_burnolSubWindow_mellinDividedShift_sourceProjection_ne_zero
riemannHypothesis_of_burnolXiDividedShiftSourceFlatness
```

Both modules are wired into their area umbrellas.  All theorems are unconditional; the final RH
consumer exposes `(SF)` as an explicit premise rather than hiding it behind an axiom.
