# Deninger--Poisson relevant square-zero amalgamation

- **ID:** `deninger-poisson-relevant-square-zero-amalgamation`
- **Stage:** 2-fully-proven
- **Type:** SOURCE RELEVANT-COEFFICIENT CONSTRUCTION THEOREM
- **Label:** `DAC_DENINGER_POISSON_RELEVANT_COMPLEX_AMALGAMATION`
- **Parent:** `deninger-poisson-relevant-complex-comparison`
- **Statement:** adjoining the source radial Poisson complex as an
  augmented square-zero ideal of the pro-Stein Tate--Milnor relevant
  coefficient gives, after arithmetic residue totalization, exactly
  the Poisson--zeta three-term complex.

## 1. Why the gluing is not a tensor product

The generic Tate--Milnor relevant coefficient and the radial Poisson
coefficient have different arithmetic roles:

- the Tate--Milnor positive ideal supplies Kummer classes and
  finite/real residues;
- the radial positive ideal supplies the relative analytic middle
  class and has zero Kummer residue.

A raw completed tensor product creates mixed positive terms.  Even at
the cohomology level, tensoring
\[
 \bigl(\mathbb C\oplus P_{\mathbb Q}[-1]\bigr)
 \quad\text{with}\quad
 \bigl(\mathbb C\oplus M_\zeta[-1]\bigr)
                                                                    \tag{1}
\]
creates \(P_{\mathbb Q}\widehat\otimes M_\zeta\) in degree two.  A
nonzero pure tensor stays nonzero after applying nonzero continuous
linear functionals on both factors.  This cross term is absent from
Deninger's required three-term coefficient and is not the Arakelov
orientation line.

Thus the instruction “retain the phase coefficient” cannot mean
tensor every radial class with every positive Milnor class.  It means
retain both augmented sectors while identifying their common unit.

## 2. Source augmented sectors

Let \(\mathscr A_{\mathrm{Kum}}^+\) be the pro-Stein
Tate--Milnor relevant coefficient of
`DAC_DERIVED_STRATUM_KUMMER_ARITHMETIC_COEFFICIENT`, with rank
augmentation
\[
 \epsilon_{\mathrm{Kum}}:
 \mathscr A_{\mathrm{Kum}}^+\longrightarrow\underline{\mathbb C}.
                                                                    \tag{2}
\]
Its generic derived sections have the strict two-term representative
\[
 \mathbb C\longrightarrow P_{\mathbb Q}[-1],
 \qquad d=0,                                                       \tag{3}
\]
where the positive product is square-zero after the relative Milnor
cell comparison.

On the Hilbert--Kummer fine source, let
\(\mathscr R_{\mathrm{PZ}}^+\) be the augmented radial
Schwartz cosheaf complex whose compactly supported/rapid global
sections are
\[
 \left[
   \mathbb C\oplus H_\cap
   \xrightarrow{(a,f)\mapsto Zf}
   H_-
 \right]_{[0,1]}.                                                 \tag{4}
\]
The augmentation
\[
 \epsilon_{\mathrm{rad}}:
 \mathscr R_{\mathrm{PZ}}^+\longrightarrow\underline{\mathbb C}
                                                                    \tag{5}
\]
is projection to the constant unit.  The positive radial ideal is
square-zero at the coefficient level; its eventual
\(H^1\times H^1\to H^2\) cup product is a Poincaré \(k\)-invariant,
not an internal product before arithmetic boundary gluing.

Every object in `(2)`--`(5)` is defined from Deninger's characters,
flow, Kummer regulator, real Fourier transform, and endpoint maps.
No spectral divisor enters.

## 3. Amalgamated relevant coefficient

Define on the fine source
\[
 \boxed{
 \mathscr A_{\mathrm{rel}}^+
 =
 \mathscr A_{\mathrm{Kum}}^+
 \mathop{\times}^{h}_{\underline{\mathbb C}}
 \mathscr R_{\mathrm{PZ}}^+
 }                                                               \tag{6}
\]
in augmented complete locally convex complexes, or equivalently in
augmented square-zero commutative derived algebras.

`[PROVED HERE]
[DAC_DENINGER_POISSON_RELEVANT_COMPLEX_AMALGAMATION]`

After derived pushforward to Deninger's rational-Witt approximation
and arithmetic direct image, `(6)` has the strict generic
representative
\[
 A^0=\mathbb C\oplus H_\cap,
 \qquad
 A^1=H_-\oplus P_{\mathbb Q},
 \qquad
 d^0(a,f)=(Zf,0).                                                 \tag{7}
\]
The arithmetic residue morphism is
\[
 \partial_{\mathrm{ar}}(g,u)=\operatorname{pr}(u)
 \in D_{\mathrm{Ar},\mathbb Q};                                  \tag{8}
\]
it is zero on the radial summand and is the already-proved
finite-plus-real Kummer boundary on the Milnor summand.
Totalization therefore is literally
\[
\begin{aligned}
 C^0&=\mathbb C\oplus H_\cap,\\
 C^1&=H_-\oplus P_{\mathbb Q},\\
 C^2&=D_{\mathrm{Ar},\mathbb Q},
\end{aligned}
\qquad
\begin{aligned}
 d^0(a,f)&=(Zf,0),\\
 d^1(g,u)&=\operatorname{pr}(u),
\end{aligned}                                                     \tag{9}
\]
the complex `DAC_POISSON_ZETA_THREE_TERM_COHOMOLOGY`.

### Proof

Homotopy pullback over the common augmentation of two split
square-zero objects identifies their units and takes the direct sum
of their positive ideals.  Applying this degreewise to `(3)` and
`(4)` gives `(7)`.

Derived direct image is a right derived functor and preserves homotopy
limits.  The same is true of derived global sections.  Hence `(6)` may
be computed before or after the two pushforwards without changing the
homotopy pullback.

`DAC_PRO_STEIN_RELATIVE_CELL_GLOBAL_SECTIONS` computes the first
sector.  `DAC_MEYER_NUCLEAR_RADIAL_STRICTNESS` and
`DAC_HILBERT_KUMMER_STRICT_ANGULAR_COSHEAF_CONTRACTION` compute the
second sector, including its phase-preserving angular reduction.
The finite and real residue morphisms factor through the Kummer
augmentation ideal and vanish on scalar radial functions, which proves
`(8)`.  Finally
`DAC_STRICT_RESTRICTED_PRIME_PUSHFORWARD`,
`DAC_PRO_STEIN_REAL_BETTI_DERIVED_LIFT`, and
`DAC_COMPLETED_ARAKELOV_TRACE_KERNEL` identify the target and prove
strictness.  Thus the arithmetic fibre totalization is `(9)`.

## 4. Cohomology, flow, and determinant

Both differentials in `(9)` are strict with closed range.  Therefore
\[
 H^0=\mathbb C,\qquad
 H^1=M_\zeta,\qquad
 H^2=\mathbb C(-1),                                               \tag{10}
\]
with ordinary and reduced cohomology equal.

The flow is trivial on the unit, is dilation on the radial ideal, and
has Tate weight one on the Kummer/Arakelov sector.  Deninger's exact
identity
\[
 [F_nP,u]=[P,nu]=\phi^{\log n}[P,u]
\]
identifies the Poisson summands with the source Frobenius flow.
Meyer's theorem now identifies the spectrum of the strong-dual middle
representation, and Deninger's regularized product theorem gives the
completed zeta determinant.  Those are consequences of `(6)`--`(9)`,
not inputs to their definition.

## 5. Euler and endpoint compatibility

On the right-decaying radial core,
\[
 Z=\prod_p(1-F_p^{-1})^{-1}.                                     \tag{11}
\]
The \(F_p\) in `(11)` is the same rational-Witt power
correspondence whose Kummer residue labels the \(p\)-component of
`(8)`.  Equation `(11)` does not turn the radial ideal into a Kummer
class: its residue remains zero.  It states that the flow character of
the radial middle sector and the prime indexing of the endpoint sector
use the same source correspondence.

The two omitted radial functionals are exactly cone-apex restriction
and Kähler top trace.  They map to weights zero and one already present
in `(9)`, so no extra endpoint class is added.

## 6. Exact remaining geometric content

The theorem constructs Deninger's arithmetic relevant complex and
identifies its topology, cohomology, flow spectrum, character, and
regularized determinant with the Poisson--zeta model.

It does not yet prove:

1. that Paugam's global alternating pairing is the pushforward of a
   source leafwise cup/trace pairing;
2. packetwise equality between Meyer's prime distribution and the
   geometric fixed-orbit distribution;
3. a positive source Hodge operator faithful on generalized spectral
   jets.

These are cup/Hodge/Lefschetz theorems about the constructed
coefficient, not missing definitions of arithmetic cohomology.

## Hostile audit

- `(6)` is a sheaf/cosheaf-level homotopy pullback, not a Postnikov
  truncation of derived global cochains.
- The common unit is not duplicated.
- Positive phase and radial ideals are both retained; only their
  unsupported raw tensor cross term is excluded.
- Radial residue zero is forced by Milnor degree, not by declaring
  prime contributions absent.  Primes still act through `(11)` and
  the Kummer endpoint.
- No zeta zero, RH, Weil positivity, CCM object, or numerical
  computation defines `(6)`.

## References

- Christopher Deninger, *Dynamical systems for arithmetic schemes*,
  relevant complexes in the introduction and the power/flow identity
  in §6: https://arxiv.org/abs/1807.06400.
- Ralf Meyer, *A spectral interpretation for the zeros of the Riemann
  zeta function*: https://arxiv.org/abs/math/0412277.
- Jacob Lurie, *Higher Algebra*, limits of augmented derived algebras:
  https://www.math.ias.edu/~lurie/papers/HA.pdf.

## Log

- 2026-07-27 — Replaced the raw phase--radial tensor by the
  source-level augmented homotopy pullback, eliminating unsupported
  mixed positive terms and producing the strict PZ totalization.

## Lean status

### The amalgamation and its totalization landed

`formal/GaloisForLFunctions/RHTower/Deninger/DeningerSquareZeroAmalgamation.lean`.  Axiom audit:
`propext, Classical.choice, Quot.sound`.

The split square-zero augmented objects are mathlib's `TrivSqZeroExt k I` with its augmentation
`TrivSqZeroExt.fstHom`, and the amalgamation `(6)` is the strict fibre product over the common
augmentation, `AlgHom.equalizer`.

- `deningerSplitAugmentation_surjective` — the augmentation of a split square-zero extension is
  surjective, split by the unit inclusion.  This is why the strict fibre product already computes
  the homotopy fibre product of `(6)`; no further cofibrancy input is used.
- `deningerAmalgam`, `deningerMem_amalgam` — the amalgamation and its membership criterion
  (equality of the two augmentations).
- `deningerAmalgamEquiv` — **the proof step of `(6)`→`(7)`**: the amalgamation *identifies the two
  units and takes the direct sum of the two positive ideals*, i.e. it is the split square-zero
  extension of `I ⊕ J`, as `k`-algebras.
- `deningerZeroIdealEquiv`, `deningerAmalgamDegreeZero` — the degree-zero instance, where the
  Kummer ideal vanishes and the amalgamated algebra is the square-zero extension by the radial
  ideal `H_∩` alone.  Applying `deningerAmalgamEquiv` degreewise to `(3)` and `(4)` is exactly
  `A⁰ = ℂ ⊕ H_∩`, `A¹ = H_- ⊕ P_ℚ` of `(7)`.
- `deningerTotalD0`, `deningerTotalD1` — the totalized differentials `d⁰(a,f) = (Zf,0)` and
  `d¹(g,u) = pr(u)` of `(9)`, with `deningerTotalD0_apply`, `deningerTotalD1_apply`.
- `deningerTotal_comp` — **`(8)`–`(9)`**: `d¹ ∘ d⁰ = 0`, because the arithmetic residue is zero on
  the radial summand and the radial differential lands there.  So the totalization is a complex.
- `deningerTotal_ker_d0`, `deningerTotal_H0` — **`H⁰ = ℂ`**: the degree-zero cocycles are exactly
  the unit line, once the radial differential `Z` is injective (Meyer strictness, cited).
- `deningerTotal_ker_d1`, `deningerTotal_range_d0` — the middle cocycles and coboundaries.
- `deningerCocycleOneEquiv`, `deningerTotalH1`, `deningerTotal_H1Equiv` — **`H¹ = M_ζ`**: when the
  arithmetic residue is injective on the Milnor summand (Arakelov trace kernel, cited), the middle
  cohomology of the totalization is canonically the cokernel of `Z`, which is `M_ζ`.
- `deningerTotal_range_d1` — **`H² = ℂ(-1)`**: the degree-two coboundaries are exactly the image of
  the arithmetic residue, so `H²` is its cokernel; the identification of that cokernel with `ℂ(-1)`
  is the cited completed-Arakelov-trace-kernel computation.

### Remaining

Nothing in this card's own proof.  What is formalized is exactly what the card proves here: the
amalgamation formula for split augmented square-zero objects, the resulting degreewise shape `(7)`,
the totalized three-term complex `(8)`–`(9)`, and the cohomology `(10)` in terms of the two
strictness inputs.  Those inputs — computation of the two sectors `(3)`, `(4)`, injectivity of `Z`
and of the residue, and the identification of the residue cokernel with `ℂ(-1)` — are the cited
theorems of the parent cards, and appear as explicit hypotheses, not as assumptions of this card.
The three items of §6 remain open by the card's own statement.
