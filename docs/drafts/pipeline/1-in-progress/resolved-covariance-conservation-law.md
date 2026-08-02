# Resolved covariance conservation law

- **ID:** HGT-resolved-covariance-conservation
- **Stage:** 1-in-progress
- **Type:** UNIVERSAL LAW / FRONTIER-LOCALIZATION
- **Source:** factored Deninger Green covariance, Calderón--Witt orientation transgression,
  Möbius--theta/Hellinger cofaces, pure-Hodge Gamma cofaces, relative admission naturality,
  HGT faithful deep packets, and resolved quantum recurrence.

## Universal law

Let

```text
X_0 --f_1--> X_1 --f_2--> ... --f_n--> X_n
```

carry generators `A_i`, and put `delta_i = A_i f_i - f_i A_(i-1)`.  Transport each local
defect to the common output while transporting its input through the preceding arrows.  Their
tuple is the **resolved covariance defect** `Delta_res`; summing its coordinates is the
augmentation `Sigma`.  The defect Leibniz rule gives

```text
A_n (f_n ... f_1) - (f_n ... f_1) A_0 = Sigma(Delta_res).       (RCC.1)
```

Therefore covariance of the composite says only

```text
Delta_res lies in ker Sigma.                                  (RCC.2)
```

It forces covariance of the factors exactly when the observation is conservative on the
source-selected resolved-defect span.  Independent retained grades are a sufficient and canonical
way to obtain this conservativity: coordinate projection isolates each local defect.  Any
observation factoring through `Sigma` annihilates every resolved defect in `ker Sigma` and no
downstream positivity, recurrence, completion, or scalar functional can reconstruct it.

For two factors the universal cancellation sequence is

```text
0 -> Z --(z |-> (z,-z))--> Z x Z --((u,v) |-> u+v)--> Z -> 0. (RCC.3)
```

The kernel of the codiagonal is exactly the antidiagonal.  Thus total covariance is a quotient
statement; factor covariance is the corresponding resolved statement before quotient.

## Exact Riemann specialization

For the finite Deninger Green factorization `G = -J C`, define

```text
Delta_G(a) = (delta_J(Ca), J(delta_C(a))).
```

The internal-defect cancellation law gives

```text
Sigma(Delta_G(a)) = 0                                         (RCC.4)
```

for every finite divisor jet, without RH.  Nevertheless

```text
RH  <->  Delta_G(a)=0 for every a.                            (RCC.5)
```

Indeed the conjugate Riesz map is surjective, so vanishing of the first resolved coordinate is
exactly commutation of the odd Hodge map with Frobenius; the existing purity theorem identifies
that commutation with RH.  Pointwise, the antidiagonal amplitude is the signed boundary fracture
`2(Re rho - 1/2)`.

This separates two statements previously conflated by every composite Green construction:

```text
completed Green covariance       = augmented defect vanishes (unconditional),
critical-line purity             = resolved defect vanishes (equivalent to RH).
```

## Corpus shadows

1. **Calderón--Witt orientation completeness.**  Regular consumers factor through the single
   orientation trace and annihilate exact boundaries.  Its secondary Green transgression is the
   only channel that can be conservative on the resolved defect.
2. **Möbius--theta physical source.**  Adjacent Hellinger cofaces form an absolute source
   resolution and their codiagonal telescopes to the theta source.  This proves landing but also
   identifies the augmentation that forgets individual exponent-grade boundaries.
3. **Pure-Hodge Gamma source.**  Actual admitted cofaces preserve the unsquared secondary charge,
   while factorial gauging makes their graph capacity vanish.  This supplies the resolved
   orientation axis but not its coefficient-faithful Xi solder.
4. **Sullivan--Milnor resolution.**  The square-zero quotient kills the degree-two ideal; the
   first Sullivan layer reifies that kernel as new degree-one generators.  It is an algebraic
   model of resolving before observing.
5. **HGT deep packets.**  Faithful face/shift coordinates and differential independence give a
   positive model of a conservative associated-graded detector.
6. **Resolved recurrence.**  A projective relation is invisible below its replica height and
   detected exactly at its first resolved grade; completed wall selection is necessarily
   singular.  This is the temporal shadow of the same law.
7. **Hedenmalm and scalar completions.**  Dense vertical multivaluedness, trace-rank fracture,
   and diagonal polarization are failures of conservativity on `ker Sigma`.
8. **Rees reflection fracture.**  Finite-order filtered maps preserve the flat radical, so a
   conservative lift between reflected finite/flat types must be singular and source-pointed.
9. **Horizontal/transverse graph no-go.**  Transverse graph powers do not detect the horizontal
   residue grade.  Required graph topology is at least bifiltered.
10. **Resolved Calderón--Witt source boundary.**  The canonical arithmetic self-cup is a nonzero
    antidiagonal pair before alternation; ordinary cup kills it.  Thus the Green antidiagonal has
    an exact nonzero source-side structural ancestor.
11. **Secondary-admission loss.**  The canonical global Gamma witness is excluded off the critical
    displacement while its rank-one primary pure-Hodge lift is always admitted.  The present lift
    is non-admission-reflecting exactly for nonzero displacement.
12. **Completed Xi pure-Hodge coface.**  Finite grades are coefficient-faithful and raw-norm
    recovery of the completed Xi Green vector holds for every displacement.  This closes raw
    completion and proves that it is displacement-blind.

## Sharpened frontier

Corpus now contains both marginals and their exact source-side antidiagonal:

```text
coefficient-faithful physical coface --(Fourier)--> Xi,
orientation-faithful pure-Hodge coface --(singular graph)--> admitted incidence.
```

What remains is one **secondary-admission-reflecting conservative external solder** between them:
a source-defined, bifiltered graph map whose resolved output keeps coefficient/exponent and
Hodge/incidence grades separate, is nonzero on exact source boundaries, reflects the global
secondary Gamma/Hodge admission class, and only then admits the completed Xi observation.

This is strictly narrower than “construct a source,” “construct a Green map,” or “prove
positivity.”  Those exist.  The missing theorem is not plain injectivity: the separate completed
coface is coefficient-faithful, while the current primary lift still loses global secondary
admission off line.  Required gate is joint injectivity plus admission reflection on the resolved-defect module before the
codiagonal/orientation augmentation.

## Hostile audit

- This does not prove the conservative external solder exists and therefore does not prove RH.
- (RCC.1)--(RCC.3) are universal algebra; significance comes from the exact Deninger
  specialization (RCC.4)--(RCC.5) and its simultaneous explanation of all source-route walls.
- A restatement as “RH iff a defect vanishes” would be decorative.  The nontrivial content is that
  the already-constructed unconditional Green covariance is proved to be precisely the quotient
  that kills the entire decisive defect.
- `[NOVELTY UNVERIFIED]` External literature comparison remains deferred by instruction.

## Gates

- [x] 0 -> 1: exact paper statement, proof, corpus nonduplication search, hostile audit
- [x] 1 -> 2: formalize universal antidiagonal/codiagonal exactness and resolved detection
- [x] 2 -> 3: formalize the Deninger `RH <-> resolved defect vanishes` specialization; direct
  checks complete
- [ ] 3 -> 4: construct a nontrivial source-side conservative solder or prove a new exact boundary
  for its existence

## Log

- 2026-08-02 — extracted the resolved/augmented distinction from exact Deninger internal-defect
  cancellation and identified all current source constructions as complementary resolutions of
  the same augmentation kernel.
- 2026-08-02 — source-side resolved cross-effect proved nonzero before cup augmentation; completed
  Xi Hellinger--Gamma coface proved coefficient-faithful in raw norm; canonical primary lift proved
  non-admission-reflecting exactly off the critical displacement.  Frontier sharpened to a
  secondary-admission-reflecting completed resolved comparison.
