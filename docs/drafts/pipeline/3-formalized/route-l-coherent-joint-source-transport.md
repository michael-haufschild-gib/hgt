# Route L: canonical joint-source transport and aperture cost

- **ID:** L-C37
- **Date:** 2026-09-11
- **Stage:** 3-formalized
- **Type:** THEOREM; canonical joint source and retained normalization obstruction
- **Depends on:** [C36](route-l-two-prime-joint-jet-source.md),
  [C34](route-l-real-polarized-source-balance.md)
- **Lean:** `formal/GaloisForLFunctions/RHTower/BurnolCoPoissonJointJetCanonicalTransport.lean`
- **RH status:** unproved

The chain remains complete original Green/BV source → cyclic/fixed
physical reader agreement → conormal vanishing → RH. This result closes
canonical joint-source selection and its actual dilation cost. It does
not prove the source-to-physical comparison.

## Exact statement

Let `rho` be an actual Xi divisor in the strict right half of the open
strip, `m` its unchanged exact conormal order, and `C_b` the actual closed
co-Poisson source at `b>0`. Let `F` be the actual unitary cosine involution.
The two readings are the literal completed derivatives

`q_b(f) = (d^m Mellin(f)(rho), d^m Mellin(F(f))(rho))`.

The already-proved bounded jet evaluator makes these continuous on
`C_b`. Define `K_b = C_b ∩ ker(q_b)` and `P_b = Id - proj(K_b)`.
The extension of `q_b` to the ambient even Hilbert space uses orthogonal
projection onto the actual extended Sonine carrier; it agrees with the
literal derivative on every admitted source.

1. `K_b` is closed and Fourier invariant. For every `f∈C_b`, `P_b f∈C_b`
   and `q_b(P_b f)=q_b(f)`. Also `P_b F=F P_b`.
2. `P_b f` depends only on `q_b(f)` and is its unique minimum-norm
   representative in the entire closed source. Exactly
   `norm(f)^2 = norm(P_b f)^2 + norm(f-P_b f)^2`.
3. Any two distinct original primes `p,q` supply actual preimages of
   every `(u,v)` at `A=exp(-2(log p+log q))`, by C36. Minimum selection
   therefore has no abstract surjectivity premise.
4. For `r≥1`, actual normalized dilation maps `C_b` into `C_(b/r)` and
   satisfies `q_(b/r)(U_r f)=(lambda*q_b(f).1,lambda^(-1)*q_b(f).2)`,
   where `lambda=r^(rho-1/2)`. The lower derivatives vanish at the
   original exact multiplicity, so Leibniz introduces no omitted terms.
5. Canonical transport is coherent:
   `P_(b/r) U_r P_b f = P_(b/r) U_r f`.
6. If `q_b(f)=(u,0)`, put `v=lambda^(-1) U_r f` and
   `g=P_(b/r) v`. Then `q_(b/r)(g)=(u,0)`, `g` is the unique minimum
   for that pair, and
   `norm(g) ≤ r^(1/2-Re(rho))*norm(f)`.
   The exact stronger identity is
   `(r^(1/2-Re(rho))*norm(f))^2 = norm(g)^2 + norm(v-g)^2`.
7. At the two-prime aperture and its dilations, every `eps>0` admits
   such a minimum source with `q(g)=(1,0)` and `0<norm(g)<eps`.
   Hence the actual first reader has no aperture-uniform bound
   `norm(q_b(g).1)≤C*norm(g)` on those admitted sources.
8. For the original window `f_L` at `b=exp(-2L)`, let `g=P_b f_L`.
   It is nonzero and retains the original leading jets `J_L,K_L`.
   Its normalized Fourier pair still satisfies
   `exp(L*(2*Re(rho)-1))*norm(J_L^(-1)g)^2
     < norm(K_L^(-1)F(g))^2`.

These are implications at an actual strict-right Xi divisor, not an
assertion that such a divisor exists. General raw-integral continuity
is used only in its proved right half-strip. No general left-half
raw/continued Mellin identity is asserted. Every lower derivative of
these closed sources still vanishes by the existing closed-source law.

## Conjecture, failure, and positive survivor

The initial scalar-filter idea required symmetry under inversion of
actual dilation. On the leading jets an inversion-symmetric scalar
filter multiplies both channels by the same factor, leaving their ratio
unchanged while nonzero. This paper calculation motivated the joint
kernel pivot; no standalone formal scalar-filter theorem is claimed.

The canonical joint-kernel pivot succeeds in preserving both leading
readings, selecting a minimum over the complete source, and transporting
coherently under Fourier and dilation. It fails as a radial-balance
producer: the exact strict bias survives on the **original window**, with
its original nonzero normalization factors. This is a proved failure of
that specific producer, not a retirement of Route L.

The strongest positive survivor is the actual canonical representative,
its coherence law, and its exact aperture/null-source energy split.
All are dependency-closed in Lean. The small-norm theorem records what
is lost at aperture collapse; covariance supplies no uniform physical
reader bound there. It does not identify the changed source with the
complete Green/BV source at every original prime and depth.

## Paper proof mechanism

Closedness follows from the bounded literal jet map and closed source.
Fourier swaps the two readings, hence preserves their common kernel;
unitarity and projection uniqueness give exact Fourier covariance.
The difference of two admitted sources with equal readings lies in the
joint kernel, yielding equality of canonical projections. Pythagoras
gives minimality and uniqueness. C36 supplies actual two-prime lifts.

The Mellin dilation identity is differentiated exactly `m` times.
Analyticity of the literal germ follows from its local agreement with
the already-proved completed continuation. Every Leibniz term except
the undifferentiated character times the `m`-th source derivative
vanishes by the actual closed lower-jet theorem. Fourier inverts the
dilation, giving the reciprocal channel. Applying the same joint map
to `U_r(P_b f)` and `U_r f` proves canonical coherence. Scaling and the
unitary dilation norm give the explicit energy split. The negative
real power tends to zero, producing the nonzero `(1,0)` minima and
contradicting any aperture-uniform reader bound.

For the original window, preservation of its nonzero `J_L` proves the
canonical source is nonzero. Fourier unitarity gives equal unnormalized
norms. Dividing by the two original jets and applying C34's strict
amplitude inequality proves the surviving normalization bias.

## Validation

- Twenty theorems and four definitions; duplicate check: 24 declarations,
  zero collisions.
- Final scratch: `lake env lean /tmp/route_l_joint_canonical_c37.lean`,
  session 19447, exit 0 with no output.
- Final leaf: `lake build GaloisForLFunctions.RHTower.BurnolCoPoissonJointJetCanonicalTransport`,
  session 46044, exit 0. Only this leaf was built (14 seconds); the
  11,574-job dependency graph was cached. Cached dependencies replayed
  their existing messages; the new leaf emitted no warning or error.
- Wired into `GaloisForLFunctions.RHTower`; no umbrella build.
- Formal index regenerated, session 25473, exit 0.
- Formal lint: session 50968, exit 0; `formal lint passed`. Existing
  repository-wide file-size warnings remain unrelated to this leaf.
- No axiom-print audit, numerical experiment, or added axiom. All owned
  Lean processes from the proof and final build have finished.

## Remaining mathematical obstacle and next attack

Derive the cyclic-to-fixed physical comparison from the complete original
Green/BV source while retaining prime, depth, multiplicity, nonzero Xi
coefficient and horizontal anchor. The next conjecture must concern an
actual source-derived contribution beyond the common measurement kernel:
a correction in that kernel preserves the now-proved normalization bias.
Any comparison across apertures must account for the exact metric loss
above and retain the original physical reading, rather than select a new
interpolated source or assume a uniform bound contradicted by the theorem.

## Corpus and external method audit

Four deep searches, each with a 150-second budget, inspect all twenty
candidate statements and all twenty source arguments and available
methods. All results are partial; no exhaustive proof-search claim is
made. Queries and artifacts:

- `coherent correction Fourier dilation Mellin kernel projection commutator aperture`:
  `/tmp/route_l_coherent_c37_deep.json`; semantic coverage
  2,350,986/2,351,771, generation 873988. Deadline/filter/source-refresh
  remain incomplete; no returned proof ideas or ingredient sets.
- `minimum norm lift joint linear measurement involution orthogonal kernel right inverse`:
  `/tmp/route_l_minimum_c37_deep.json`; semantic coverage
  2,351,166/2,351,916, generation 874005. Deadline/filter/source-refresh
  remain incomplete; no returned proof ideas or ingredient sets.
- `orthogonal complement closed kernel canonical lift covariance linear isometry minimum projection`:
  `/tmp/route_l_joint_projection_c37_deep.json`; semantic coverage
  2,351,232/2,351,971, generation 874034. Semantic/source refresh remain
  incomplete. Proposed kernel-complement ingredient set inspected.
- `projected transport composition kernel invariant smaller aperture coherent section exact defect`:
  `/tmp/route_l_coherent_composition_c37_deep.json`; semantic coverage
  2,351,631/2,352,223, generation 874097. Semantic/text/source refresh
  remain incomplete. Proposed transport/kernel ingredient set inspected.

The Hilbert port minimum-lift source in
`HTGeometry/ConstraintMotiveRelativity/CofinalInverseCapacityHilbert.lean`
provides the orthogonality and norm-splitting method, but its finite-stage
filling assumption is not imported as a producer. The actual pair is
filled by C36 and minimized in the complete source. The existing
`BurnolBilateralApertureDefectEnergy` retains two projected-transport
premises and treats zeroth evaluators; it does not supply the actual
multiplicity-top transport proved here. Generic coherent boundary
representative and aperture-corrector results likewise retain their
own defect/fixedness assumptions.

Broad recent arXiv searches were `reciprocity`, `compression`, and
`gluing`, without RH search terms. Two primary papers were read beyond
abstracts:

- [Reciprocity can halve what a mechanical network can learn](https://arxiv.org/html/2609.04169v1)
  (3 September 2026), Theorems 3 and 6. Symmetry alone does not supply
  passivity or transversality; neither extra hypothesis is transferred.
  The useful comparison is to construct the actual measurement image
  and retain the inaccessible component.
- [Cutting corners: exciting and magical bounds from the cusp bootstrap](https://arxiv.org/html/2609.04041v1)
  (3 September 2026), equations (5), (8)-(11). The argument establishes
  admissible normalizable states and a convergent expansion before
  applying Cauchy-Schwarz and comparing leading exponents. Its QFT
  completeness/reflection-positivity assumptions are not RH inputs.
  Here the corresponding admission, full lower-jet cancellation, and
  exact dilation character must be proved on the original source.

Compression hits concerned empirical LLM/FPGA methods and were rejected
at abstract screening. No numerical experiments or external theorem
premises are used. No axiom-print audit is run.
