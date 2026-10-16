# 002: rational source calculus through all finite Xi resonances

Status: formalized and directly audited. One structural contribution combining
five leaves; individual definitions and helper lemmas are not separate counts.
Goal count after this contribution: 2/100.

## Obstacle removed and resulting constructions

The existing causal machinery gave right parametrices with finite packet defects,
and actual-source resolvents away from Xi zeros. It did not give matching left
identities, unique source solutions through arbitrary resonances, or a coherent
rational action allowing poles at Xi zeros.

For every finite word L in shifted generators, including repeated Xi roots, let
W_L be its actual generator word and P_S the canonical full resonant Xi packet.
There is now a canonical operator D_L on the chosen arithmetic source satisfying

`W_L D_L = 1-P_S = D_L W_L`, `P_S D_L = D_L P_S = 0`.

The actual operator `W_L(1-P_S)+P_S` is bijective on the whole source, with
explicit inverse `D_L+P_S`. Thus every forcing has a unique actual source solution
after precisely this finite resonance repair.

The quotient by all original finite causal modes is nonzero and carries a
compatible action of `RatFunc ℂ`. Every nonzero polynomial, including ones
vanishing at Xi zeros, acts bijectively. Pole division is represented by D_[rho]
on actual sources. The quotient has empty algebraic spectrum and no
polynomial-linear section back into the source. This identifies why finite
spectral correction terms must be retained when lifting the rational calculus.

## Corpus inputs and conjecture loop

- Meyer causal division and finite-word packet-kernel surjectivity supply actual
  preimages at every parameter. The exact homogeneous-word classification on
  the observable source removes homogeneous ambiguity.
- Hedenmalm source realization supplies the canonical full-multiplicity finite
  causal packets and their invariant projectors.
- Contribution 001 supplies the arithmetic actual-source complement, with no
  invisible vectors and with the original finite causal modes intact.
- Polynomial factorization and module localization extend unique shift division
  to a rational-function action. Cayley--Hamilton on finite packets identifies
  the unavoidable nonsplitting obstruction.

The initial attempt was to infer continuity or a topological splitting from
Poisson range closedness in another Meyer presentation. That inference was
rejected: closedness alone does not supply the missing topology bridge or a
continuous complement. No such theorem is asserted here.

The next conjectures succeeded: exact packet-complement bijectivity, two-sided
finite-defect division, and unique division on the non-finite quotient. The
further conjecture of an invariant rational summand failed. Its strongest
positive survivor—the actual repaired automorphisms and nonzero rational
quotient—was formalized alongside the obstruction. See the failed-route card
`../5-failed/meyer-rational-tail-invariant-section-2026-10-16.md`.

## Dependency-closed proof

1. Restrict the finite full-jet projectors to the arithmetic source V. Each
   projector commutes with the actual generator and every generator word.
   The word W_L is bijective on the kernel of its selected full packet: take a
   causal preimage and apply the global projector for surjectivity; transport
   the existing homogeneous classification for injectivity.

2. Invert that packet-kernel map and compose with `1-P_S`. The resulting D_L
   has zero selected packet and satisfies the right identity. Both D_L W_L u
   and `(1-P_S)u` lie in the packet kernel and have the same W_L image; its
   injectivity gives the left identity. The two identities and the zero-packet
   property prove that `D_L+P_S` and `W_L(1-P_S)+P_S` are mutual inverses.

3. Write F for the original finite causal span in V. If `(A-rho)u` belongs to
   F, its jets vanish outside a finite set S. At every Xi point outside
   `S ∪ {rho}`, local-unit jet cancellation forces the jets of u to vanish.
   Since V has no invisible vectors, u equals its finite projector and belongs
   to F. Therefore shifts are injective on V/F. Applying D_[rho] proves their
   surjectivity, because its exact defect lies in F.

4. The projected Gaussian is outside F, so V/F is nonzero. Complex polynomial
   factorization upgrades bijectivity of all shifts to bijectivity of every
   nonzero polynomial action. The identity map of this polynomial module meets
   `IsLocalizedModule` for the nonzero polynomials. Its localization structure
   equips the same quotient with a compatible `RatFunc ℂ` module structure.
   In particular, for p and nonzero q, `q • ((p/q) • u) = p • u`. The inverse
   of X-rho is explicitly identified with the class of D_[rho] applied to the
   original source.

5. For any polynomial-linear map from this rational quotient into V, compose
   with a finite packet map. The packet generator's characteristic polynomial
   is nonzero and kills the packet by Cayley--Hamilton. That polynomial acts
   surjectively on the rational quotient, so the composite is zero. Singleton
   packets imply all source jets vanish; observable-source injectivity makes
   the original map zero. The quotient map is surjective, but a section would
   annihilate its nonzero Gaussian class. Thus no such section exists.

6. Every shifted tail generator is bijective, so its algebraic spectrum is
   empty. This does not contradict the exact Xi spectrum on V: quotienting by
   F removes finite resonances through a nonsplit extension.

## Artifacts and validation

The following leaves in `formal/GaloisForLFunctions/RHTower/` all passed
foreground direct audits with `lake --old env lean -o <module.olean> <module.lean>`:

- `DeningerMeyerArithmeticPacketDivision.lean`
- `DeningerMeyerRationalSourceTail.lean`
- `DeningerMeyerRationalTailCalculus.lean`
- `DeningerMeyerRationalTailNonsplitting.lean`
- `DeningerMeyerArithmeticResonantInverses.lean`

All five are wired into `formal/GaloisForLFunctions/RHTower.lean`. A separate
`/tmp` audit checked 18 principal dependency closures and the key theorem types.
Every axiom report was exactly `[propext, Classical.choice, Quot.sound]`.
Installed mathlib API names were checked in scratch Lean files. No full or
umbrella build, numerical experiment, added axiom, proof hole, or heartbeat
increase was used. Owned scratch files and search outputs were removed; all
owned processes terminated.

Final repository lint reported only four unrelated missing umbrella imports:
`OddWeilGramLimit`, `OddWeilResolventApproximation`,
`OddWeilResolventArithmetic`, and `OddWeilResolventIntegral`. Those concurrent
files were left untouched. No lint error named this contribution. An earlier
lint run also listed `CHMDSmallScalePacketPositivityFirstOrder`; concurrent
umbrella work resolved that omission before the final check. The two heat-module
omissions reported during contribution 001 were already wired when this
contribution was audited.

## Scope and next frontier

These are unconditional algebraic constructions on actual source classes. They
do not prove continuity, positivity, trace convergence, disappearance of the
invisible kernel in the original full cohomology, or RH. Canonical division is
relative to the fixed arithmetic complement; the base complement remains
noncanonical. The rational quotient cannot be treated as an invariant direct
summand of V.

Routine additional identities of these inverses should not be counted as new
contributions. A further contribution must remove a distinct analytic,
topological, positivity, or arithmetic obstruction supported by the current
Lean corpus.
