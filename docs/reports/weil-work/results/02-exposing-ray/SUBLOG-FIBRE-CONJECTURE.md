# Sublogarithmic recovery versus gamma-energy escape

Status: original beta<1 conjecture remains OPEN. Cycles30–31 prove the
strict subrange0<=beta<1/2 on paper and in Lean; see
SUBHALF-LOG-FIBRE-PROOF.md. Six audited leaves derive the actual-separator
envelope, control both remote arithmetic windows at the same cutoff,
extend weighted separators, and prove exact finite positive fibre recovery,
including literal Fejer null recovery. Beta>=1/2 remains unresolved.
Verdict: BRIDGE, scientific novelty unestablished. Primary
energy diagnostic remains E-escape versus E-recovery in
POLAR-NULL-CLOSURE-CONJECTURE.md; universal WP02 remains unchanged.

## Exact conjecture

For 0<beta<1 set

    omega_beta(tau) = 1 + (log(2+|tau|))^beta.

Use the same actual finite positive compact complex C2 source mixtures,
rowwise two polar zeros, and exact raw integer-atom fibres K(v), Kpol(v)
as in POLAR-FIBRE-DENSITY-PROOF.md. Conjecture that for every finitely
supported real v,

    closure_L1(omega_beta d tau) Kpol(v)
      = closure_L1(omega_beta d tau) K(v).

Equivalently every actual full mixture has actual polar recovery in its
same whole integer fibre with arbitrarily small integral of
omega_beta*|rho_recovery-rho_full|. Every n>=2, including the zero tail,
remains an exact equation. No aperture, row count or profile restriction.

Competing conjecture: some beta in (0,1), exact fibre and actual full
source mixture have a positive distance from all actual polar recoveries
in this weighted norm. A counterexample must be source-realized; an
arbitrary positive measure is insufficient.

## Why this is the next diagnostic

Cycle29 proves the unweighted case, including literal Fejer null recovery.
Thus energy escape cannot be explained by nonexistence of any recovery.
The unbounded gamma weight has logarithmic growth in the existing corpus.
Recovery at the full logarithmic weight would force convergence of the
actual signed energy, and the literal negative Fejer source would then
produce a negative exact-null polar family. This is incompatible with the
WP02 lower bound at multiplier zero. No logarithmic recovery is assumed.

Sublogarithmic recovery would identify a possible critical boundary at
logarithmic energy. Its failure would expose a lower-cost obstruction.
Neither outcome alone proves the main inequality or E-escape. Before any
new formalization, require a substantive source estimate and explain its
consequence for the actual recovery-energy problem.

## First hostile audit (historical; subhalf range now resolved)

1. Unweighted L1 convergence has no automatic weighted upgrade. Arbitrarily
   small mass can escape to frequencies whose weight is arbitrarily large.
   Do not use dominated convergence, bounded mass, or diagonal extraction
   without a proved uniform tail bound.
2. The cycle27 divisor average transfers a CONSTANT Toeplitz bound. A
   bound growing like (log N)^beta cannot be inserted into that argument
   and silently replaced by a constant. This is the first analytic gap.
3. The actual generic far-polar multiplier approaches1 uniformly, hence
   approximates any one fixed source also in an integrable weighted norm.
   It does not preserve its integer trace. Exact repairs must be paid.
4. The corpus theorem
   WeilSingularArithmetic.exists_small_sqrt_mass_of_sublog_envelope
   concerns nonnegative coefficient mass and assumes a sublogarithmic
   harmonic envelope. It is not a weighted polar/full extension theorem.
   At that checkpoint no such absolute coefficient envelope had been
   derived. Cycles30–31 now derive it for beta<1/2; beyond that range it
   must still be proved, replaced by a cancellation argument, or refuted.
5. Prior fixed-profile/lattice repair obstructions do not cover these
   unrestricted finite positive mixtures. Prior coherent completion keeps
   an extra positive density and does not prove this recovery statement.

[OPEN CORE] Prove or refute an actual weighted recovery estimate in the
same complete fibre. A possible dual route is extension of arithmetic
lower bounds against all continuous linear functionals on this weighted
L1 space, but its growing Toeplitz cost must be resolved, not stipulated.
No conditional extension interface or abstract measure surrogate counts.

## Search status

The cycle29 deep search `sublogarithmic polar full positivity spectral
weight` was partial at its deadline;20 candidates and20 source arguments
were reviewed, mostly irrelevant. No proof ideas or ingredient sets were
returned. Lexical `sublog --module Weil` found the harmonic-envelope result
above; exact source read. Lexical `weighted recovery --module Weil`
returned no hit. These results do not prove absence or novelty. Broaden
with the exact weighted-fibre mechanism and audit external parent theories
before selecting a proof route. Classical positive-definite and separation
methods are not new scientific knowledge.

## Cycle30 derived estimate

The missing absolute coefficient estimate has a paper derivation for the
strict subrange beta<1/2. Omega(n)=k layers are primitive, so each has
square mass at most the squared resonator budget. Cauchy--Schwarz across
these layers, weighted by z^k, and the elementary bound
sum_{n<=N} z^Omega(n)/n=O_z((1+log N)^z),1<z<2, give
sum_{n<=N}|b(n)|/sqrt n=O((1+log N)^(beta+z/2)). Choosing
1<z<2(1-beta) makes that exponent less than1. Averaging the actual
far-polar errors at X and2X over the same interval then proves separator
extension. Exact weighted fibres follow by the audited separation argument.
This is not an assumed coefficient bound or a constant Toeplitz transfer.
No conclusion for beta>=1/2 or gamma energy follows. Formalization is
complete through exact-fibre and Fejer recovery: the six saved leaves and
all public axiom audits pass. The implemented simultaneous-error proof
uses discrete square blocks, section4a of SUBHALF-LOG-FIBRE-PROOF.md.
The half exponent is a limitation of this envelope argument, not a proved
threshold for actual recovery.
