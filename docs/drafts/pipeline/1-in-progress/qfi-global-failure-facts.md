# Global information-topology fact log

- **FACT.** `PrimeCoShiftModel` already gives the `n^(-s)` square-summability threshold at
  `Re(s)=1/2`.
- **FACT.** `PrimeClockScaleFactor` already gives the prime-coherent QFI threshold, reflected
  double failure, and the resulting RH reformulation.
- **FACT.** `ZetaFisherHorizon` already proves an infinite Fisher-distance boundary.
- **FACT.** Prime-product Hellinger/Kakutani sector topology and its reflected orientation refinement
  are already developed through publication-ready stage.
- **FACT.** A smooth normalized qubit path with nonzero QFI can have an exact zero transition
  amplitude at a regular parameter (`fisherQubitClock_information`,
  `fisherQubitClock_orthogonal_at_pi`).
- **NO-GO.** A QFI admission wall, divergence-rate tie, or Fisher horizon can select the critical
  line without supplying any law of zero occurrence.
- **NO-GO.** Homogeneous normalization erases a common analytic factor.  Multiple outputs sharing
  that factor remain one process for divisor detection.
- **NO-GO.** Reflecting one process does not establish process independence; split/collided
  reflected failure fibers already belong to arithmetic constraint hyperdescent.
- **NO-GO.** Replacing local amplitudes by an infinite product does not establish novelty; the
  Hellinger/Kakutani prime-sector route already owns that topology.
- **FACT.** Any surviving route must simultaneously establish source independence,
  QFI-essential global topology, and a pre-divisor arithmetic coupling to zero occurrence.
- **NO-GO.** A finite analytic vector does not make a common zero into an intrinsic projective
  puncture: factor the least common vanishing order and the projective state extends.  A genuine
  zero end needs an infinite, nonuniform, or mixed-state boundary mechanism.
- **NO-GO.** A smooth full-dimensional state chart cannot meet a boundary at an isolated interior
  point with full differential rank.  A boundary coordinate has an interior extremum there.  Using
  QFI nondegeneracy to exclude the hit is circular.
- **FACT.** The squarefree prime Fisher state is unchanged by arbitrary unimodular Euler phases,
  while a corresponding Helson continuation can have a prescribed simple off-line zero
  (`exists_phase_fisher_blind_with_prescribed_zero`).  Any viable QFI route must retain
  operator-conditioned phase/recovery data beyond Born weights and Fisher variance.
- **FACT.** For the equatorial mixed-qubit recovery chart with Bloch radius
  `r = R / sqrt(1+R^2)`, the SLD QFI metric is
  `dR^2/(1+R^2)^2 + R^2/(1+R^2) dtheta^2`.  Recovery infinity is at finite radial distance while
  its phase circle remains noncollapsed.  Paper derivation is exact; Lean formalization is open.
- **NO-GO.** Reflection quotient geometry alone does not turn a zero orbit into a link.  A closed
  circle for an off-line orbit and a seam-attached interval for a fixed orbit follow only after the
  source-accessible boundary is proved to be a full local circle.  Cofinal escape does not supply
  that premise.
- **NO-GO.** Reciprocal divergence alone is an occupied receiver.  A new route must construct the
  recovery family from finite Möbius coefficients and prove an exact cutoff-overflow law before
  selecting any zero.
- **LEAN FACT.** `finiteMobiusRecoveryHead` has norm at most `N` at every nontrivial zeta zero,
  while `finiteCutoffZeta` there is `O(N^-2)`.  Therefore their product tends to zero and the
  formation/recovery gluing defect tends to `-1`; theorem names are
  `tendsto_finiteCutoffZeta_mul_finiteMobiusRecoveryHead_at_zero` and
  `tendsto_finiteMobiusRecoveryGluingDefect_at_zero`.
- **NO-GO.** The raw truncated Möbius Dirichlet series cannot generate the proposed recovery end.
  Whole-route survival requires an overflow-forced renormalization derived before zero selection;
  an arbitrary reciprocal correction would merely insert the target.
- **LEAN FACT.** Every fixed logarithmic Möbius jet has norm at most
  `N * (log N)^k` at a nontrivial zero.  Literal finite continuation times any fixed jet, or any
  fixed finite complex linear packet of jets, tends to zero; each associated gluing defect tends to
  `-1`.
- **NO-GO.** Fixed finite derivative/tangent enrichment cannot create recovery infinity.  A live
  construction needs cofinal order or nonlocal cutoff data.
- **LEAN FACT.** With `H_N` the constant-coefficient head, `B_N` the Möbius head, `O_N` complete
  rectangle overflow, and `C_N = F_N - H_N`, the exact identity
  `F_N B_N - 1_{1 <= N} = O_N + C_N B_N` holds at every cutoff and parameter.  At every nontrivial
  zero its right side tends to `-1`.
- **FACT.** The pair `(O_N, C_N B_N)` is canonical multi-law source data, but finite total charge
  does not imply either coordinate escapes.  QFI completion is relevant only after cofinal
  noncompactness is proved.
- **NO-GO.** Exponentially damped Möbius recovery collides with existing natural-Abel divisor and
  Möbius--Laplace continuation routes.  Their zero propagation uses analytic uniqueness; QFI would
  only rename their singular boundary.
- **LEAN FACT.** On every open-strip point, the constant-coefficient head `H_N` and continuation
  correction `C_N = F_N-H_N` both leave every norm-bounded set, while the canonical scale
  `(1-s)N^(s-1)` sends them to `+1` and `-1`.  Their exact finite sum converges to `zeta(s)`; at a
  nontrivial zero it darkens.  Closed package:
  `finiteCutoffCompensatingInfinityAtZero_closed`.
- **NO-GO.** Ordinary product-QFI completion of `(H_N,C_N)` is zero-blind because its leading
  antidiagonal boundary occurs over the entire open strip.  Multiple infinities alone do not make
  zero ends.
- **LEAN FACT.** The finite QFI ball coordinate is injective and odd.  Antidiagonal coincidence of
  the head and correction images holds exactly when `finiteCutoffZeta` vanishes; pulling both images
  back and adding them returns `finiteCutoffZeta` identically.  Theorem names are
  `finiteCutoffQFIAntidiagonalDefect_eq_zero_iff` and
  `qfiInverseCompensatedCharge_eq_finiteCutoffZeta`.
- **NO-GO.** Inverse-chart higher contact adds no arithmetic law.  It is a reversible coordinate
  presentation of the finite continuation and therefore cannot make universal QFI boundary data
  zero-specific.
- **LEAN FACT.** At every strict-left nontrivial zero, rectangle overflow and the
  continuation--recovery interaction are both not tail bounded.  More strongly, after every cutoff
  and beyond every radius there is one later cutoff where both norms exceed that radius, while
  their exact total converges to `-1`.  Theorems:
  `finiteMobiusOverflow_not_isBoundedUnder_at_strictLeftZero` and
  `exists_joint_overflow_escape_after`.
- **LEAN FACT.** Every off-critical nontrivial-zero orbit has a strict-left functional-equation
  member with the same joint source escape.  Theorem:
  `offCriticalZeroOrbit_exists_joint_overflow_escape_after`.
- **FACT.** Joint norm escape plus bounded total charge creates an antidiagonal boundary
  accumulation point after choosing an escaping sequence and then a convergent boundary
  subsequence.  It does not make the original cutoff history converge or fill a boundary circle.
- **NO-GO.** Arbitrarily late joint spikes are not a QFI end.  They do not imply eventual escape,
  a QFI-Cauchy cutoff history, connectedness of the accumulation set, or control of its phase.
- **LEAN FACT.** Even eventual joint escape plus exact compensation does not fill the QFI boundary:
  `exists_eventual_joint_escape_exactly_compensated_single_qfi_phase` gives two processes whose
  norms tend to infinity and whose sum is always zero, while every first-coordinate QFI image lies
  on the real diameter and no reindexing converges to phase `i`.
- **NO-GO.** The equatorial mixed-qubit QFI completion is topologically a closed disk, exactly as
  the ordinary closure of its radial ball coordinate.  Mapping finite source values into this
  chart preserves phase but supplies no QFI-essential global topology.
- **LEAN FACT.** `CofinalDirectionCountermodel` proves that exact finite lattice provenance can
  converge to an arbitrary irrational direction.  Finite provenance and cofinal growth therefore
  cannot substitute for an arithmetic direction law.
- **LEAN FACT.** `framedHistory_typedSeparation` gives distinct winding histories with identical
  radial boundary report, phase tangent metric, and Berry quotient.
- **NO-GO.** QFI endpoint data do not reconstruct executed source history.
  `twoLevel_zeroComplexity_historyLength_unbounded` additionally gives exact endpoint returns with
  arbitrarily large executed information-geometric length.  A history route must derive its
  transition channel from source updates before selecting zeros.
- **FACT.** Upper-unipotent process composition represents the exact cutoff laws:
  `X(H_N)Y(B_N)` has central coordinate `H_NB_N=1+O_N`, while
  `X(C_N)X(H_N)Y(B_N)=X(F_N)Y(B_N)` has central coordinate
  `F_NB_N=1+O_N+C_NB_N` for `N >= 1`.
- **NO-GO.** This central promotion is not yet information geometry.  Generic Heisenberg carry and
  its loss under abelian projection are already formalized, and the complex central coordinate has
  no source-defined lattice.  A finite normalized endpoint state also does not retain process
  execution.  Matrix packaging without a new QFI path invariant is redressing.
- **FACT.** For normalized Choi vector `v(t)=I+t a E_12` of a `3 x 3` upper-unipotent stage, writing
  `A=|a|^2` gives exact pure-state QFI `12 A/(3+t^2 A)^2` and Fubini--Study length
  `arctan(|a|/sqrt(3))` on `0<=t<=1`.
- **NO-GO.** At coefficient infinity, normalized Choi density of that stage converges to the same
  rank-one `E_12` state for every phase of `a`.  Stage length saturates and endpoint phase is erased.
  A finite-dimensional normalized-Choi path cannot supply the required phase-retaining global end.
- **NO-GO.** A freely filled two-parameter surface, an infinite projective limit, a generic process
  tensor, or an ordinary derived limit is not new source content.  Corpus theorems already classify
  these as packaging or universal receivers; none supplies arithmetic zero location.
- **LEAN FACT.** For two complex channels `x,y`, opposite phase velocities give exact pure-state
  QFI `16|x|^2|y|^2/(|x|^2+|y|^2)^2`.  If `|x|` tends to infinity while `x+y` has any finite limit,
  this QFI tends to `4`; the conclusion is independent of common escape phase.  Theorem:
  `tendsto_compensatedPairRelativePhaseQFI_balanced`.
- **LEAN FACT.** The formation-head/continuation-correction pair has balanced relative-phase QFI
  limit `4` at every open-strip point.  It is a background information circle and is zero-blind.
  Theorem: `tendsto_headCorrectionRelativePhaseQFI_balanced`.
- **LEAN FACT.** At every strict-left open-strip point, with no zero premise, rectangle overflow is
  not tail bounded.  There is a strictly increasing cutoff subsequence on which its norm tends to
  infinity, actual continuation--recovery interaction divided by overflow tends to `-1`, and their
  controlled relative-phase QFI tends to `4`.  Theorem:
  `strictLeftPoint_exists_overflowRecoveryRelativePhaseQFI_balanced`.
- **NO-GO.** Overflow/recovery relative-phase QFI is not an exceptional zero circle.  It occurs at
  every strict-left point, including nonzeros.  Its product with the universal
  formation-head/correction circle is therefore generic leading left-half topology.
- **FACT.** Leading balanced-escape topology discards the finite compensation that separates zeros
  from nonzeros.  Recovering that subleading charge by rescaling returns to a scalar zeta-dependent
  observable, so no QFI-essential survivor remains in this route.
- **NO-GO.** Do not construct a global quotient from locally admitted QFI directions before proving
  that their incidence varies with the zero set.  Here the required variation is false, not merely
  open.
- **CORPUS FACT.** Chronological exponential products, iterated word coefficients, and their
  low-degree shuffle laws are already derived for literal deletion paths in
  `RHTower.SignatureWords`; the module states that these relations carry no arithmetic zero
  content.  Ordered area or rough-path packaging is not a new QFI route by itself.
- **CORPUS FACT.** Common recovery kernels and reflected recovery lifts are information-neutral in
  the existing constitutive corpus.  Recasting multiple-law failure as absence of a common parent
  process adds content only if a new source obstruction is proved first.
- **NO-GO.** Two independent cutoff parameters do not create a coupled information class when the
  experiment separates into a formation row and recovery column.  Existing rectangle-holonomy
  gauge laws remove all row-only and column-only phases; a source-coupled mixed term is required.
- **NO-GO.** Adding all orthogonal qubit control axes cannot recover information erased by
  projectivization.  The complete pure-state QFI covariance is determined by the normalized ray;
  the proved strict-left ratio sends every overflow/recovery pair to the same ray.  Retaining only
  the approach rate magnifies the subleading scalar compensation.
