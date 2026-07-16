# Hypertranscendental polarization is a nontrivial fibre over derived constraint topology

- **ID:** `hypertranscendental-polarization-fibration`
- **Stage:** 1-in-progress
- **Type:** FOUNDATIONAL CONJECTURE / POLARIZATION MODULI / POSITIVITY SELECTOR
- **Scientific status:** `[CONJECTURE] [UNIVERSAL CUBE SEED FORMALIZED]`
  `[DERIVED-TOPOLOGY BLINDNESS PROVED] [FIELDS-SCALE OPEN CORE] [NOT AN RH RESULT]`
- **Parents:**
  - `../2-fully-proven/new_scientific_knowledge/hypertranscendental-hochster-source-coherence-duality.md`
  - `hypertranscendental-constraint-sheaf-reconstruction-duality.md`
  - `../3-formalized/new_scientific_knowledge/summable-residue-source-orientation-completion-law.md`
  - `../3-formalized/hypertranscendental-minimal-polarized-critical-completion-architecture.md`

## The forced geometric picture

Let `Kin_HT` denote the moduli of active derived constraint sheaves before a signed Hermitian
orientation is chosen, and let `Pol_HT` denote the moduli after pointing, real structure, and
polarization are retained.  There is a forgetful map

```text
pi : Pol_HT -> Kin_HT.                                    (1)
```

The universal prime-log orientation theorem proves that a fibre of `(1)` is highly nontrivial.
For one fixed universal HT differential field, one fixed finite Stanley--Reisner constraint
topology, its complete derived Hochster coherence, and one fixed compact-open completed ring,
every finite sign chamber occurs.  The labeled relative Hermitian forms recover the directed
differences of chambers and their exact Krein--Hamming distance.

Thus orientation is not a scalar consequence of the topology.  It is a coordinate in a genuine
moduli fibre over that topology.

## Exact finite seed `[PROVED FROM FORMALIZED PARENTS]`

Let `J,L` be finite subsets of the prime labels.  The corresponding residue surgeries have:

```text
same embedded differential field;
same finite Stanley--Reisner differential matroids;
same complete derived constraint topology;
same compact-open completed rational Cauchy ring.         (2)
```

Their relative polarized probe has

```text
ind_-(J,L)=#(J\L),
ind_+(J,L)=#(L\J),
d_Krein(J,L)=#(J symmetric_difference L).                (3)
```

Consequently the finite chamber fibre is a labeled Hamming cube, and the polarization is faithful
on it.  Forgetting polarization collapses the whole cube to one point.

The completion theorem strengthens this from finite chambers to the full summable sign cube: all
orientations generate one completed ring.  Herglotz positivity still singles out the all-positive
vertex.

This is the exact positive content behind the phrase “derived topology is blind to orientation
surgery.”  Blindness is not loss into chaos; the forgotten information has a concrete fibre
geometry.

## Polarization-fibration conjecture

> **[CONJECTURE -- HT POLARIZATION FIBRATION]** On the category of regular source-minimal active
> HT constraint sheaves, `(1)` is a derived fibration whose fibre over `B` is the moduli space of
> source-compatible real structures, Hermitian forms, integral/order data, and positive-cone
> reductions on the analytic realizations of `B`.  Its tangent and obstruction theory is governed
> by self-dual endomorphisms of `B`, while its connected components carry Witt/Krein invariants.

The universal prime-log cube is a discrete coordinate chart in one fibre.  In nonlinear sources
the fibre may have continuous components, automorphisms, and higher descent obstructions.

> **[CONJECTURE -- ARITHMETIC SECTION PRINCIPLE]** A natural arithmetic HT source does not merely
> determine a point of `Kin_HT`.  Its Euler, archimedean, growth, and normalization laws construct
> a canonical section
>
> ```text
> s_arith : B -> Pol_HT                                   (4)
> ```
>
> of the polarization fibration over its active constraint object.  Positivity is the assertion
> that `(4)` lands in the zero-negative-index component.  The section must be constructed before
> inspecting a target zero set or spectral divisor.

This separates three logically independent theorems:

```text
kinematic reconstruction: identify the derived constraint sheaf B;
orientation selection:    construct the source-canonical section s_arith;
fixed-locus theorem:       prove the selected polarization confines self-dual degeneracy.  (5)
```

No one of the three implies the other two.

## Strong RH audit

`[CONJECTURE; NOT AN RH RESULT]` A potential RH proof may use an unpolarized derived zeta object to
explain symmetry, multiplicity, continuation, or the existence of a degeneracy divisor.  It
cannot force critical-line confinement unless one exact step is sensitive to motion in the fibre
of `(1)`.

For any proposed proof, apply the audit:

```text
Which premise or inference changes under an orientation surgery that leaves (2) fixed?       (6)
```

If none changes, the proof cannot distinguish the positive chamber from an indefinite chamber
and cannot establish an orientation-sensitive conclusion.  If one changes, that inference is the
actual RH-bearing input and must be isolated as an arithmetic-section or fixed-locus theorem.

A completed-zeta package would therefore require:

1. a prime--archimedean construction of `B_zeta` independent of its zeros;
2. a source-canonical section `s_zeta` of `(1)`;
3. proof that `s_zeta` has zero negative index;
4. a conservative self-dual realization whose degeneracy support is the zeta divisor;
5. a fixed-locus theorem for that positive realization.

The critical zeros could then be the common self-dual degeneracy spectrum of the selected point.
Nothing here proves that the section or fixed-locus theorem exists.

## Why the fibre must be coupled to topology

Taking the Cartesian product of an arbitrary topology with an arbitrary sign cube is only the
universal kinematic phase.  A natural source must impose compatibility:

- Verdier or source-face duality pairs coherence degrees;
- restriction maps transport Hermitian forms and positive cones;
- monodromy acts by isometries or controlled similitudes;
- active carrier representations preserve the real structure;
- analytic growth determines which gauge transformations are admissible;
- pointing fixes the affine ambiguity of a polarization.

The nontrivial invariant is the coupling class of these data.  A free decoration by signs fails
the selector problem just as badly as forgetting signs.

## Parent-theory boundary

The following are established parents and not novelty claims:

- moduli of bilinear and Hermitian forms, Witt groups, and Krein signatures;
- real and Hermitian K-theory;
- self-dual and perverse sheaves, Verdier duality, and orientation data;
- determinant and Pfaffian line bundles;
- period domains and variations of polarized Hodge structure;
- real analytification and signed seminorm spectra.

The candidate-new mathematics is the HT-specific fibration `(1)`, the exact universal
constraint-topology/Krein-cube chart `(2)`--`(3)`, the intrinsic arithmetic section `(4)`, and a
proof that natural obstruction realizations are conservative on the selected polarized object.
Calling a Hermitian form a polarization is not new.

## Anti-theatre gate

Retire or enlarge the conjecture if:

1. the orientation cube does not embed into a single fibre after the full derived constraint
   object is fixed;
2. source-equivalent presentations produce inequivalent polarization fibres;
3. the arithmetic section is defined using the target divisor or desired positivity conclusion;
4. the fibre is a trivial product and compatibility imposes no restriction;
5. a positive section does not constrain degeneracy beyond self-dual symmetry;
6. the proposed realization functors forget the Witt/Krein component;
7. an existing polarized correspondence already proves the same HT essential-image theorem.

Every failure must yield a positive result: the exact residual fibre, the missing additional
structure, or a source class on which the fibration truncates and admits a unique section.

## Theorem targets

1. Package the already formalized prime-orientation family as an explicit fibre of `(1)` with
   fixed Stanley--Reisner derived boundary and exact Krein--Hamming metric.
2. Extend the Lean-formalized signed forms on the nodal Hochster line to restriction-compatible
   Witt/Hermitian forms on arbitrary finite constraint sheaves.
3. Construct restriction-compatible forms on the normal-crossing constraint-Hodge diamond.
4. Prove that Herglotz pointing is the unique positive section on the summable prime-log model.
5. Construct a second, non-Herglotz analytic realization of the same polarization fibre.
6. Prove a source-natural comparison between the two realizations.

## Gates

- [x] arbitrary finite topology and finite orientation coexist
- [x] full derived topology is invariant under residue surgery
- [x] finite Krein--Hamming fibre geometry is formalized
- [x] completed-ring blindness across the infinite summable sign cube is formalized
- [x] all-positive Herglotz vertex is distinguished
- [ ] define the polarization fibration functorially
- [ ] prove presentation/Morita invariance of its fibres
- [x] couple positive and negative polarizations to the same nodal Hochster line in Lean
- [ ] prove unique positive section in one analytic model
- [ ] construct an arithmetic section without target-divisor input
- [ ] prove a positive fixed-locus theorem away from RH
- [ ] complete specialist novelty and significance audit

## Lean seed

`formal/GaloisForLFunctions/HTGeometry/KoszulCohomology.lean` now proves:

- `nodalHochsterPolarization_positive_definite`;
- `nodalHochsterPolarization_negative_definite`;
- `nodalHochsterPolarization_positive_not_isometric_negative`.

These declarations use the same previously formalized nonboundary nodal Koszul class.  They make
the first polarization fibre literal: forgetting the form retains one underlying coherence line,
while retaining the form separates its positive and negative components.
