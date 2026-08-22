# BV prime-window dilation residue orientation

- **ID:** `bv-prime-window-dilation-residue-orientation`
- **Stage:** 3-formalized
- **Type:** exact source value relation / orientation bridge
- **Scientific status:** `[PROVED IN LEAN] [BRIDGE] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Lean:**
  `formal/GaloisForLFunctions/RHTower/BVPrimeWindowDilationOrientation.lean`
- **Parent:**
  `../../2-fully-proven/not_new_scientific_knowledge/11-rh-zero-divisor-geometry/bv-prime-window-laurent-orientation-polarization.md`

## Statement

Let `W` be an actual compactly supported complex BV prime window and let `r>0`.  Lean constructs
two new compact BV windows

```text
W_r^+(x)=W(r x),
W_r^-(x)=W(x/r).
```

Their Mellin transforms satisfy the unconditional source identities

```text
M_(W_r^+)(s)=r^(s-1) M_W(s),
M_(W_r^-)(s)=r^(1-s) M_W(s).                            (1)
```

For every positive integer `r`, the same two windows satisfy literal finite-source decimation.
Writing `p_W(n)` for the exact prime--polar coefficient, including its Mellin counterterm, Lean
proves

```text
T_(W_r^+)(n)=T_(W_r^-)(r^2 n),
p_(W_r^+)(n)=p_(W_r^-)(r^2 n).                          (1a)
```

The first equality is termwise equality of finite von-Mangoldt windows.  The second joins that
prime equality to the archimedean counterterm through the Mellin character and
`sqrt(r^2 n)=r sqrt(n)`.  Thus the action below is produced before continuation by the complete
prime--Gamma source, rather than installed on divisor fibres afterward.

For the canonical BV continued source, define its exact residue value at the shifted point
`rho+1/2` by

```text
R_W(rho)=2 M_W(rho+1/2)
  * analyticOrderAt(regularizedRiemannZeta,rho).toNat.   (2)
```

The existing divisor-tomography theorem proves that `(2)` is the actual punctured Laurent limit
whenever `rho` is a zero of the pole-filled zeta.  Equation `(1)` now gives

```text
R_(W_r^+)(rho)=r^(rho-1/2) R_W(rho),
R_(W_r^-)(rho)=r^(1/2-rho) R_W(rho).                    (3)
```

Consequently the source-produced oriented residue energy is exactly

```text
|R_(W_r^+)(rho)|^2-|R_(W_r^-)(rho)|^2
 =|R_W(rho)|^2
   (r^(2 Re(rho)-1)-r^(1-2 Re(rho))).                   (4)
```

If `r>1` and the window does not censor the residue, Lean proves

```text
(4)>0  iff Re(rho)>1/2,
(4)=0  iff Re(rho)=1/2.                                 (5)
```

Thus the horizontal orientation is not introduced as a zero-location predicate.  It is the exact
Hermitian imbalance between two explicit prime-window source channels, with the archimedean
half-shift fixed by the completed continuation.

## Proof contribution

The module closes the formal gap between finite coefficient decimation, the BV
continuation/residue theorem, and the proposed source contraction route:

```text
literal square-index decimation of finite prime--Gamma coefficients
  -> opposite Mellin characters on the two continued source channels
source-produced forward <= inverse residue contraction on right annihilator fibres
  -> residue orientation <= 0
  -> no right off-critical zero by (4)-(5)
  -> no off-critical zero by functional-equation reflection
  -> RH.
```

The remaining theorem is not `(4)` and not the assertion that the common charge vanishes.  It is
the positive source-effectivity statement constructing one Gamma-completed/co-Poisson graph on
which the coefficient decimation is contractive and these uncensored Laurent evaluations are
continuous.  Pairwise prime coherence plus cofinal decay would also kill the common charge, but is
not needed by the direct contraction chain.

## Anti-theatre boundary

- The module does not define the transformed residues by the desired characters; it constructs
  the transformed BV windows and proves their Mellin laws by change of variables.
- Its square-index relation is equality of the actual finite coefficients, including the
  archimedean polar term; it is not a sequence introduced to mimic a Laurent character.
- The residue values are tied to actual punctured limits by the previously formalized BV
  continuation theorem.
- No RH predicate, zero orientation, real-rootedness, positive divisor measure, anti-Herglotz
  property, or limiting sign is used.
- Equations `(1)` and `(3)` are classical Mellin covariance.  Their exact splice with the
  canonical prime-polar continuation is useful proof infrastructure, not new scientific
  knowledge.

## Lean declarations

- `CompactBVPrimeWindow.argumentDilation`;
- `CompactBVPrimeWindow.argumentExpansion`;
- `CompactBVPrimeWindow.mellinTransform_argumentDilation`;
- `CompactBVPrimeWindow.mellinTransform_argumentExpansion`;
- `CompactBVPrimeWindow.weightedPrimeWindow_argumentDilation_eq_argumentExpansion_sq_mul`;
- `CompactBVPrimeWindow.polarCoefficient_argumentDilation_eq_argumentExpansion_sq_mul`;
- `CompactBVPrimeWindow.continuedSourceResidueValue`;
- `CompactBVPrimeWindow.continuedSourceResidueValue_argumentDilation`;
- `CompactBVPrimeWindow.continuedSourceResidueValue_argumentExpansion`;
- `CompactBVPrimeWindow.continuedSourceResidueOrientation`;
- `CompactBVPrimeWindow.continuedSourceResidueOrientation_eq`;
- `CompactBVPrimeWindow.continuedSourceResidueOrientation_pos_iff`;
- `CompactBVPrimeWindow.continuedSourceResidueOrientation_eq_zero_iff`;
- `CompactBVPrimeWindow.tendsto_argumentDilation_expansion_continuedSource_residues`.

## Gates

- [x] positive dilation preserves the compact BV source class
- [x] forward and inverse Mellin characters proved
- [x] exact finite prime-window square-index decimation proved
- [x] exact prime--archimedean polar-coefficient decimation proved
- [x] exact continued-source residue covariance proved
- [x] actual punctured residue limits retained
- [x] oriented squared-norm factorization proved
- [x] strict right/critical sign classification proved under noncensorship
- [x] wired into the RHTower umbrella
- [ ] construct the source-effective positive graph producing the contraction
- [ ] compose that unconditional source theorem to RH
