# Hypertranscendental Laurent-horizon residue field

- **ID:** `hypertranscendental-laurent-horizon-residue-field`
- **Stage:** 1-in-progress
- **Type:** UNIFIED FIELD THEORY / AFFINE BUILDING AND CENTRAL-SEAM PROGRAM
- **Scientific status:** `[CONJECTURE] [CLASSICAL LOCAL MODEL LEAN-FORMALIZED] [EULER SOURCE LAURENT DOUBLE PROVED] [PLUCKER IDENTITY LEAN-FORMALIZED] [GENERAL HT IDENTIFICATION OPEN]`
- **Parents:** `projective-horizon-a2-current-rank-jump`,
  `projective-horizon-solomon-tits-topological-charge`,
  `hypertranscendental-hilbert-cocycle-rigidity`

## Conjectural object

The common obstruction behind the RH chains is not a scalar and not the spherical horizon
building by itself.  It is the **basic determinant line over a Laurent double of the HT horizon
building**.  Infinitesimally, this is the central extension of the `A2` loop-current algebra;
globally, it is the basic line over the corresponding twin affine building or affine
Grassmannian.

The two one-sided horizon systems are the positive and negative halves.  Each half separately is
central-cocycle isotropic, so a proof chain confined to one half can propagate arbitrarily far
without seeing the global anomaly.  The obstruction appears only in the cross-gluing of opposite
modes.  This gives an exact structural explanation for the repeated pattern

```text
long internally consistent rank-one chain -> terminal seam.
```

It also respects the founding constraint principle: the Laurent double is a compatibility object
of simultaneous horizon charts, not a flow that generates the HT function.

## Classical local model

Let `g=sl3(K)` over a characteristic-zero field and let

```text
L g = g tensor K[t,t^(-1)].
```

For pure modes define

```text
omega(X tensor t^m, Y tensor t^n)
  = n delta_(m+n,0) trace(XY).                              (1)
```

Then:

1. `omega` is an alternating Lie `2`-cocycle;
2. `omega` vanishes identically on `g tensor K[t]` and on `g tensor K[t^(-1)]`;
3. for every nonzero `m`, the degree-`m` and degree-`-m` root spaces pair nondegenerately;
4. the resulting central extension is the residue extension

```text
[X tensor f,Y tensor g]^ = [X,Y] tensor fg
  + trace(XY) Res(f dg) c.                                 (2)
```

Items 1--4 are classical affine Kac--Moody/current-algebra theory.  They are the parent mechanism,
not the novelty claim.

The pure-mode content of items 1--3 is now formalized in
`ProjectiveHorizonLaurentResidueSeam.lean`, including exact seams on all three opposite `A2`
Chevalley-root pairs.  The full universal-extension theorem in item 4 remains parent theory rather
than a theorem reproved in the project.

## HT-specific rank jump

The live Lean tree already gives three inputs that do not occur together in the parent theory.

1. HT jet horizons form strict one-sided cusps attached to a spherical Tits building.
2. Depth-two horizon gauges generate polynomial current modes.
3. One third-horizon shear raises the projective-plane parabolic current algebra to all `A2`
   Chevalley polynomial modes.

The proposed new theorem is that the source's genuinely opposite punctured chart supplies the
negative current half and that its overlap with the positive half pulls `(2)` back to the actual
branch--clock--orientation seams.  Under this identification, the already-proved spherical
horizon building is the boundary at infinity of the affine double, while its Steinberg class is
the boundary shadow of the determinant line.

This is not implied by the current rank-jump theorem.  The polynomial arc parameter is one-sided;
projective inversion of the target does not by itself invert the arc parameter.  A source-defined
puncture or multiplicative scale chart is required.  Introducing a Laurent variable by hand would
fail the source-purity gate.

## Euler source-derived Laurent double `[PROVED SPECIALIZATION]`

The squarefree Euler source closes this gap without introducing a formal loop coordinate.  Center
at `z=s-1/2`.  Its positive characters are `n^(-z)` for positive integers `n`; functional-equation
reflection sends them to `n^z`.  The cancellative Dirichlet monoid group-completes canonically to
the positive rational character group:

```text
C[N_(>0)] -> C[Q_(>0)^x],
chi_q(z)=q^(-z),
chi_q(-z)=chi_(q^(-1))(z).                               (2a)
```

With scale derivation `D chi_q=-(log q)chi_q` and neutral-character coefficient `CT`, the source
residue seam is

```text
omega_E(f,g)=CT(f Dg),
omega_E(chi_q,chi_r)=-(log r)  if q r=1.                 (2b)
```

Both integer and inverse-integer halves are isotropic, while

```text
omega_E(chi_n,chi_(n^(-1)))=log n !=0                   (n>1). (2c)
```

For each prime, the two reflected squarefree apartment charts are exactly

```text
1+p^(-1/2)chi_p(z),
1+p^(-1/2)chi_(p^(-1))(z).                               (2d)
```

The full proof is in
`../2-fully-proven/not_new_scientific_knowledge/euler-dirichlet-laurent-residue-double.md`.
Thus the source-puncture and negative-mode gates are closed for the Euler specialization.  The
general HT theorem remains open: an arbitrary constrained HT source need not carry a
multiplicative Dirichlet monoid or a reflection-fixed scale coordinate.

## Gamma source puncture `[PROVED; LEAN-FORMALIZED BRIDGE]`

The inverse-Gamma exterior supplies a second actual source puncture without selecting an Xi zero.
On its logarithmic cover, put

```text
y(z)=-exp(-z),             t(z)=exp(z).
```

For every sufficiently late inverse sheet `I_n`, Lean proves

```text
Gamma(I_n(y(z)))=y(z),
t(z)=-1/y(z),              t(z)^(-1)=-y(z),
I_n(y(z+2*pi*i))=I_n(y(z)).                              (2e)
```

Thus the Gamma source itself supplies both scalar Laurent halves and the deck cover.  This closes
the source-puncture gate for the Gamma branch-clock row.  It does **not** close the negative-current
gate: the scalar functions in `(2e)` have not been identified with the negative `A2` arc action,
the affine residue cocycle, or the Xi prime-packet norm.  The tempting Xi-Hurwitz
“identification” was rejected because both sides were definitionally the same exponential
character and therefore added no proof content.

## Plucker packet and positive level

For an Xi fibre, let `a_p` be the canonical prime seam and use reciprocal-prime weights.  The
finite pair energy is

```text
E_s(a)=||a_s tensor 1_s-1_s tensor a_s||^2
      =2 det Gram(1_s,a_s).                                (3)
```

The Gram-determinant equality is now formalized as
`primePairDifferenceEnergy_eq_two_mul_pluckerGramDet` in
`XiPrimeSeamPairVariance.lean`, together with nonnegativity and the canonical Xi specialization.

Thus the obstruction is a determinant-line norm: it is the Plucker area of the two-plane spanned
by the constant and seam sections.  A positive-level representation of the Laurent central
extension supplies the missing orthogonality of opposite modes.  The required packetization
theorem is that each tensor in `(3)` is the cocycle value of one finite Laurent-root packet.

If that theorem is source-derived, affine fixed-point rigidity gives a uniform bound on `(3)`.
The existing Lean theorem that `not RH` produces arbitrarily large `E_s` then gives the
contradiction.  Neither the classical central extension nor the bare `A2` rank jump supplies this
packetization automatically.

## Cross-chain dictionary `[CONJECTURE]`

| Existing terminal obstruction | Proposed determinant-line pullback |
|---|---|
| prime/Hurwitz pair energy | Plucker norm of constant and seam sections |
| Boolean orientation/Krein inertia | polarization of the determinant-line metric |
| Böttcher deck ambiguity | integral holonomy of the Laurent central line |
| Gamma branch clock | residue of the negative/positive jet-chart overlap |
| spectral flow/Maslov defect | level of the same central extension in a unitary realization |
| completed-SEM winding charge | integral boundary character of the determinant line |

Every row must be proved by an exact commuting diagram.  Similar vocabulary is not evidence.

## Falsification gates

1. **Source puncture:** derive the Laurent coordinate from a source singularity, multiplicative
   scale chart, or two-ended completion that is defined without choosing an Xi zero.
2. **Negative modes:** prove that the opposite source chart generates actual negative arc modes;
   target projective inversion alone is insufficient.
3. **Residue identification:** pull the classical cocycle `(1)` back to at least two already
   formalized obstruction maps with exact constants and orientations.
4. **Packetization:** construct one group element per finite prime packet whose affine cocycle norm
   is exactly `(3)`.
5. **Positive level:** prove positivity from the source; an arbitrarily chosen unitary
   representation is not a resolution.
6. **Uniformity:** use one fixed finitely generated higher-rank group or prove a uniform relative
   rigidity theorem.  A cofinal union does not inherit property `(T)` automatically.
7. **Circularity:** the Laurent double and its pointing must be source-defined, not indexed by the
   divisor whose location RH asks to prove.

If gates 1 or 2 fail, the strong positive residue remains the one-sided-isotropy theorem: it proves
that no argument confined to a single polynomial horizon half can detect the central seam.  If
gate 4 fails, the Plucker identity still identifies the exact higher-rank geometry of the Xi
obstruction and explains why pointwise cocycle boundedness is irrelevant.

## Formalization plan

- [x] formalize the pure-mode residue pairing `(1)`;
- [x] prove alternation, the Lie `2`-cocycle identity, same-half isotropy, and exact opposite-mode
      pairing;
- [ ] connect the nonnegative half to the formalized `A2` projective-horizon current modes;
- [x] formalize the weighted Plucker/Gram identity `(3)` for the Xi pair energy;
- [x] derive the inverse-Gamma source puncture and its positive/negative scalar Laurent coordinates;
- [ ] identify the inverse-Gamma scalar negative modes with the negative `A2` current action;
- [x] derive the source-pure positive-rational Laurent double for the Euler specialization;
- [x] identify its reflected negative modes and exact opposite-mode residue weights;
- [x] formalize the Euler real-frequency characters, reflection, residue pairing, prime seams, and
      `A2` cocycle in `RHTower/EulerLaurentResidueDouble.lean`;
- [ ] derive a source-pure negative horizon chart for the general Laurent-integrable HT class;
- [ ] construct the determinant-line packet action;
- [ ] prove the exact obstruction pullback diagrams;
- [ ] close the RH contradiction and run the dual novelty/significance gate.

## Parent boundary and literature audit

- Universal central extensions of current algebras by `Omega^1_R/dR`, the residue cocycle for
  Laurent loops, affine Kac--Moody algebras, affine Grassmannian determinant lines, and twin
  buildings are classical.
- The repo's spherical horizon building and Steinberg top class are already proved; merely
  renaming them is not new.
- Kramer explicitly relates Laurent-polynomial loop groups, affine buildings, and affine
  Kac--Moody algebras.  Kassel's current-algebra extension gives `(2)` in the parent setting.
- Candidate novelty is only the source-derived HT Laurent double, its exact pullback to the
  obstruction corpus, and the determinant-line packetization that would force RH.

## Log

- 2026-07-15 -- pointwise property-`(T)` route failed because the Xi seam values decay to zero;
  finite-energy divergence was identified as Plucker packet growth.
- 2026-07-15 -- existing spherical-building topology audited and rejected as the missing unified
  object; the Laurent central double isolated as the first structure invisible on every
  individual horizon half.
