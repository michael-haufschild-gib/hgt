# TG C9.18: maximal domain of the literal Gamma clock operator

- **Stage:** 1-in-progress
- **Route:** TG, singular Gamma reference/domain and actual functional calculus
- **Status:** C9.18a/b/c CLOSED in Lean; spectral, even physical, full physical and Fourier-domain gates audited
- **Conjecture:** The original finite Gamma clock operators converge strongly exactly on the maximal domain of multiplication by the C9.15 Gamma log-modulus symbol in the actual Mellin carrier. The resulting closed self-adjoint operator retains the original density and counterterm, and its domain is Fourier invariant.

## Corpus basis

C9.15: S(xi)=integral_0^infinity 2(cos(xi*u)-1)gamma(u)/u du
=2(log||Gamma(1/4+i*xi/2)||-log||Gamma(1/4)||), absolutely convergent.
CCMArchimedeanMellinTransport identifies every intrinsic L1 clock kernel's
literal integrated even dilation operator with its exact Mellin multiplier.
MaximalRealL2Multiplication constructs maximal measurable real multipliers,
proves density and self-adjointness, and supplies actual spectral cutoffs.
Its L2MultiplierContinuity dependency admits bounded multipliers by
pointwise convergence. DilationGeneratorNoPointSpectrum constructs the
physical Mellin carrier; this does not itself identify our Gamma cutoff
operator. C9.14/C9.16 force exclusion of the sharp physical ground from
the raw Gamma domain. C9.17 admits the relative remainder response only.
Searches: /tmp/tg-c918-reference-search.json (complete, nonpartial snapshot),
/tmp/tg-c918-maximal-search.json (lexical: tendsto_realEnergyCutoff),
/tmp/tg-c918-parity-search.json. No ready Gamma maximal-domain result used. Deep candidates/source arguments were inspected and are not a Gamma-domain producer. The parity lexical hits identify evenProjection, reflection and the existing parity multiplier; no complete two-block Mellin equivalence was found.

## New proof mechanism

For eps>0 put S_(eps,R)(xi)=integral_[eps,R]
2(cos(xi*u)-1)gamma(u)/u du. The integrand is nonpositive, so the full
literal source gives S(xi)<=S_(eps,R)(xi)<=0, even for an empty interval.
The scalar integrability already proved in C9.15 gives cofinal pointwise
convergence. Thus |S_(eps,R)-S|<=|S|, without a separate growth estimate.

For f with S*f in L2, use q_(eps,R)=S_(eps,R)/S where S!=0 and q=1
where S=0. This is bounded by one and tends pointwise to one. The actual
finite multiplier S_(eps,R)f equals q_(eps,R)(Sf). The existing bounded
multiplier convergence theorem therefore gives strong L2 convergence on
the maximal domain, without an assumed smooth core or an unproved
operator-norm integral. A direct dominated L2 proof is equivalent.

Conversely, if the actual finite multipliers converge strongly to g,
localize on every bounded energy band of |S|. On such a band the preceding
argument identifies the localized limit as S times localized f. The
countable energy bands exhaust the spectral line, so g=Sf almost
everywhere. Hence Sf is L2 and f belongs to the maximal domain. This
supplies necessity, not only an admissible sufficient domain.

To identify the physical operator, package the literal symmetrized
finite kernel k(u)=1_[eps,R](u)gamma(u)/u+
1_[eps,R](-u)gamma(-u)/(-u) as CCMLogKernel. Its integral is twice the
positive-ray mass. Mellin transport followed by subtraction of that
mass times identity yields exactly S_(eps,R). This step must be proved
for the actual strong integral; merely defining a multiplier is insufficient.

The existing Mellin unitary acts on the even physical carrier. The full
Sonin carrier additionally needs the odd block. The actual parity
multiplier commutes with dilation, so its odd-to-even transport should
supply the second identical spectral block. This construction and its
exact normalization remain obligations; do not claim the full carrier
from the even block alone. Once the full cutoff equivalence is proved,
finite Fourier commutation transfers through the domain criterion to
Fourier invariance of the maximal domain and its unbounded action.

## Remaining route obligations

After domain closure the genuine hard arithmetic problem remains
Summable soninPrimePolarGridEnergy, plus the completed source-to-Hardy
identification and strict sub-unit law. Domain construction cannot
substitute for those. No RH conclusion is claimed.

The first scalar-source draft is /tmp/tg-c918-domain.lean, not yet audited.
It proves the exact cutoff sign interval, error domination, scalar cofinal
limit and bounded quotient with exact source preservation. No production
C9.18 file or verified domain theorem exists yet. The C9.17 foundations
must finish before starting its Lean audit (one owned build at a time).

Second proof mechanism for necessity (stronger than local energy-band
argument): for any nontrivial countably generated cofinal filter, select
one sequence tending to it. Strong L2 convergence supplies an almost-everywhere
convergent subsequence via tendstoInMeasure_of_tendsto_Lp and
TendstoInMeasure.exists_seq_tendsto_ae. The exact pointwise cutoff-symbol
limit identifies this same subsequence as S*f. Hence the L2 limit equals
S*f almost everywhere and f lies in the maximal domain. This proves the
full arbitrary-cofinal-family iff without a bounded-energy assumption.
The necessity draft is /tmp/tg-c918-necessity-part.lean, not yet audited.
The current scalar+spectral sufficiency audit is /tmp/tg-c918-domain.lean;
its running handle is 70398. No C9.18 production file exists yet.

C9.18a spectral sufficiency and full arbitrary-filter necessity elaborate,
apart from one exact action-representation rewrite repaired using a local
ae theorem. Production SoninGammaClockSpectralDomain.lean is now wired
and undergoing final audit: owned Lean session 13877, log
/tmp/tg-c918-spectral-final.log. The previous scratch session73185 exited1;
no other owned Lean process is live. Axiom scratch is prepared at
/tmp/tg-c918-axioms.lean. Paper proof: P2 tg-gamma-clock-spectral-domain.
Physical identification and full parity-block construction remain open.

C9.18a required leaf audit exits 0 with empty diagnostics. The complete
spectral iff is verified, not only sufficiency. Fourteen foundation queries,
index and lint now running; no other owned Lean process. C9.18b next:
build the actual positive finite L1 clock kernel p, use existing
ccmLogKernelReflect to form p+reflect(p), subtract its mass times identity,
and prove exact Mellin symbol S_(eps,R) plus literal physical strong action.
CCMArchimedeanIntegratedScaling defines ccmLogDilationOrbit f u as
 evenDilationUnitary(exp(-u)) f.
CCMArchimedeanScalingStar supplies ccmLogKernelReflect_ae and the proved
Haar negation change of variables via measurePreserving_neg.integral_comp.
The Mellin unitary currently identifies the even carrier; full parity
transport and Fourier-domain invariance remain obligations.

2026-10-04 — C9.18a CLOSED. SoninGammaClockSpectralDomain final0 empty;
all14 public foundation queries0, only propext/Classical.choice/Quot.sound.
Index0 all14 verified, umbrella wired. Lint1 on14 unrelated unreachable
leaves (adds ThetaCuspC5InverseReserveGrowth to C17 list), no own finding.
P2 moved to P3 tg-gamma-clock-spectral-domain. All owned processes exited;
obsolete C18 scalar/spectral/necessity scratch files removed. Axiom scratch
and logs retained. Goal remains ACTIVE (last get_goal confirms).

Next conjecture C9.18b: the finite even physical operator
rho(p+reflect(p))-symbol(p+reflect(p),0) I has exact strong action
 integral_[eps,R] (gamma(u)/u)(D_exp(u)+D_exp(-u)-2I) f du
and its actual Mellin transform is gammaClockCutoffSpectralOperator.
Here p is the literal positive-window density as CCMLogKernel (L1), and
reflect is existing ccmLogKernelReflect. This avoids postulating any
operator-norm integral. The exact finite identity plus C18a transports
maximal-domain iff to the even physical carrier. Then build odd-to-even
transport with soninParityMultiplier 1, retain both orthogonal blocks,
and prove full physical-domain invariance under Fourier from finite
commutation. No C18b Lean code has yet been written.

Relevant read APIs: CCMArchimedeanIntegratedScaling lines19-46,82-144;
CCMArchimedeanScalingStar lines19-66 and116-147;
CCMArchimedeanMellinTransport lines24-188;
LinearPMapBoundedUnitaryTransport lines89-109 (domain comap and action);
SoninEvenCarrier lines37-106 (evenProjection, mem_evenSubspace_iff);
SoninPrimePolarGroundTransfer lines132-171 (parity definition, private ae
formula, public norm and dilation law). The actual spectral result is not
a replacement for this physical identification or either remaining RH gate.

C9.18b corpus search completed nonpartial snapshot; proposed candidates
and source arguments did not supply the desired literal Gamma identity.
The existing CCM integrated-scaling/Mellin proofs remain the basis.
Scratch /tmp/tg-c918b-physical.lean now constructs the actual positive L1
kernel, its reflection sum, mass subtraction, exact scalar Mellin identity,
finite physical-to-spectral intertwining, and equality with the literal
full physical strong Gamma integral on every even vector. Audit session
32629 is running. Earlier audit60223 exited1 on cast/Pi-reduction issues;
these were repaired without changing the conjecture or raising heartbeats.
No C18b production module yet. Next: transport maximal-domain iff to the
even carrier and prove full odd-block transport using the actual parity
multiplier. New parity search: /tmp/tg-c918c-parity-search.json.

C9.18b scratch70609 exits0 with empty diagnostics. Exact finite Mellin
identity, literal physical strong integral, self-adjoint maximal even operator
and full arbitrary-cofinal-family iff now elaborate. Production
SoninGammaClockEvenDomain is wired; final leaf audit running. No full or
umbrella build. Next C18c retains odd sector: J=soninParityMultiplier 1
anticommutes with reflection, J squared is identity, and J commutes with
positive dilation. Thus even projection P yields exact two-channel
reconstruction f=Pf+J P J f. Prove those source identities and use them
to transport both maximal even domains. The full-domain cutoff iff then
transports exact finite Fourier commutation to domain invariance.
Search /tmp/tg-c918c-sum-search.json: nonpartial snapshot; compiler metadata
mostly pending/stale, so all used APIs require direct Lean verification.
Candidates/source_arguments inspected; no direct full-Gamma result found.
Mathlib orthogonalDecomposition and withLpProdCongr provide genuine Hilbert
product machinery if needed for the full self-adjointness proof.

2026-10-04 — C9.18b CLOSED. Production final7951 exits0 empty. Allten
foundation queries80914 pass, only standard three foundations. Index82451
exits0 with allten API names; lint21215 exits1 on14 unrelated unreachable
leaves, no own finding. P2 promoted to P3. Full C18c paper proof recorded
in P2 tg-gamma-clock-full-physical-domain; scratch /tmp/tg-c918c-parity.lean
is under audit40498. No other owned Lean process. C18b obsolete working
scratch removed; final/foundation/index/lint logs retained.

C18c parity scratch40498 exits0 empty: J involution, reflection
anticommutation (origin excluded only ae), exact odd/even unitary and full
Hilbert two-sector decomposition verified. Appending maximal two-sector
operator exposed elaboration timeout in concrete Gamma linearity, not a
mathematical obstruction. Replaced by a generic private two-sector partial
operator construction; no heartbeat change. Audit21443 running on parity,
full self-adjoint operator, literal full cutoff action and maximal-domain iff.
Fourier source commutation and both-direction domain invariance drafted
in /tmp/tg-c918c-fourier-part.lean, not yet appended or audited. No other
owned Lean or index/lint process remains. C18b closed and scratch cleaned.

C18c full scratch60280 exits0 EMPTY, including both-sector maximal
self-adjointness, original strong finite Gamma action, arbitrary cofinal
cutoff convergence iff, and exact Fourier domain/action invariance. The
concrete linearity timeout was eliminated by explicit generic partial-map
linearity; actual isometry-to-CLM conversion repaired, no heartbeat changes.
Production SoninGammaClockPhysicalDomain is wired and under final audit.
All15 public foundation queries prepared. Both next-frontier searches
tg-c919-hardy-search and tg-c919-energy-search completed nonpartial snapshot;
all candidates/source arguments inspected. Hardy returns no direct completed
TG weld; energy finds the exact native covariance identity but no bound.
Their proposed ingredient sets still assume the required energy bound.
No summability or RH result inferred. Next arithmetic question must retain
the complete polar-centered covariance, not substitute a diagonal bound.

C18c final85389 exits0 EMPTY. Index1157 exits0 and all15 public
names present; lint95425 exits1 on20 unrelated unreachable leaves and no
owned C18c finding. Foundation audit18041 running, log
/tmp/tg-c918c-axioms.log. No other owned process. The corpus candidate
energy_le_two_modular_norm_sq_add_four is bounded by the still-uncontrolled
actual modular norm; its stretched ceiling grows with cutoff, and its
cofinal log bound is an RH premise. criticalPacketFields_asymptotic_isometry
uses thermal-rescaled clocks and a complementary-packet metric; it supplies
no domination of the TG reciprocal-maximum covariance. The complete-period
DFT identity preserves a gcd-square covariance under uniform period measure,
not the actual chronological reciprocal-maximum/polar source. None was
used as an unconditional energy estimate. Arithmetic summability remains
the direct next hard target; the exact signed source must be retained.

2026-10-04 — C9.18c CLOSED. Final85389 exits0 empty; all15 foundation
queries18041 exit0 with only propext/Classical.choice/Quot.sound. Index1157
exit0 all15 names; lint95425 exit1 on20 unrelated unreachable leaves, no
owned finding. P2 promoted to P3 tg-gamma-clock-full-physical-domain.
C18a/b/c now close spectral admission, literal even physical identification,
both physical parity sectors, full self-adjoint maximal domain, arbitrary
cofinal source cutoff convergence iff, and both-direction Fourier domain
invariance with exact action. All owned processes are terminal. Obsolete
C18c working scratch/parts removed; foundations and audit logs retained.
Persistent RH goal remains ACTIVE. Return to the direct C9.13/C9.19
arithmetic signed-covariance problem in tg-principal-polar-operator-cancellation;
completed source-to-Hardy cubic compatibility and strict sub-unit control
also remain genuinely open. No RH proof or falsification.
