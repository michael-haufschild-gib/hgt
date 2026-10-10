# Prime prefix escape, analytic cost, ambient rigidity — verified 2026-10-10

Active unbudgeted original goal: mechanically apply proven openai/math source results throughout native Lean corpus, all16 live+23 candidate routes in docs/reports/rh-current-frontier-map.md, no Weil priority. Source results are PROVEN. All39 focused reviews remain incomplete; do not mark goal complete. No agents spawned/authorized. No owned live processes at this boundary.

Latest complete batch: tmp/hgt-openai-math/prime-escape-audits.json. Previous prime-energy-audits.json. Upstream source pin fd4aeeb2ee4fc729c18d98444fed42fd0529eeeb, rechecked in previous energy batch; no additional upstream recheck asserted here. All117 StableCoordinate source leaves complete. Tracker stable-coordinate-native-port.json now270 completed modules =117source+153application,2749 public declarations. own-files.txt596 leaves,4862 public theorems/lemmas,6700 all public declarations. Every own leaf imported exactly once, no source-directory Lean artifacts.128 historical stored source hashes revalidated unchanged;131 now stored. Ledger unchanged hash971e9a674d00c1729580931274f49892d9dd181626f288ba5040703847aca0ec.

New3 leaves, namespace GaloisForLFunctions.HTGeometry,20theorems+2defs=22public. All3 object builds then final plain lake --old env lean <leaf> checks clean/empty. All22 #print axioms in /tmp/paper-prime-escape-axioms.lean only propext/Classical.choice/Quot.sound. Exact-path/name lexical searchback22/22. Wired into HTGeometry.lean, no umbrella build. Final full lint has6FOREIGN unreachable modules, none owned: RHTower.MertensPolylogStrictMultiplicity, XiGaussianHeatVerticalExponentialType, XiReciprocalSliceNearestZero; HTGeometry.QKrawtchoukCompanionTriangular, ReciprocalPositivityMinimumModulus, ToeplitzHessenbergReciprocal. Do not fix foreign work.

1. PaperMoebiusPrimePrefixEscape.lean (11public=10theorems1def):
- paperMoebiusPrimeTransport_time_one_below(p)(n:Fin p): actual T_p,1 mu n=0.
- _time_one_prime(p): coefficient at p=-1.
- paperEscapingPrime(N):Nat.Primes := choice from Nat.exists_infinite_primes(N+1), with paperEscapingPrime_gt N.
- paperMoebiusEscapingPrime_coefficient(N)(n:Fin(N+1)): prefix through N zero.
- _ne_zero: every escaping source nonzero.
- paperMoebiusPrimeTransport_time_one_laplace_below(p)(N:Fin p)(x): actual native finiteRealLaplacePencil zero.
- _time_one_energy_below(p)(N:Fin p)(r:Real): full native GammaHankel energy zero for EVERY real exponent.
- paperMoebiusEscapingPrime_laplace, _energy (line85) specialize chosen escaping family.
- _eventually_zero(n): every fixed coefficient eventually zero.
Private realTransport_prefix_zero pays shifted index n+1. Finite energy native denominator is Nat-cast ((m+n+2:Nat):Real)^r, NOT syntactically (m:Real)+n+2; avoid copying explicit sum and use mul_eq_zero then Finset.sum_eq_zero.

2. PaperPrimeEscapeAnalyticCost.lean (5theorems):
- paperPrimeTransportFactor_time_one_norm_envelope(p)(s): abs(norm(U_p,1(s))-(p:Real)^(s.re))<=1. Uses exact U=1-p^s and abs_norm_sub_norm_le(1-p^s)(-p^s).
- paperEscapingPrime_tendsto_atTop: chosen primes ->infinity in Real.
- paperPrimeEscape_factor_tendsto_atTop(s:{s:Complex//0<s.re}): norm multiplier ->infinity.
- _no_uniform_factor_bound: no pointwise uniform bound over N at any fixed positive-real-part point.
- paperPrimeEscape_fixed_ideal_unbounded_cost (line63)(N)(s:{0<s.re})(B): exists prime p such that ALL coefficients through N vanish, source NONZERO, native energy at cutoff N zero for ALL r, actual Xi ideal on Re>0 equals original, and multiplier norm>B. This exposes exact finite-observation escape despite preserved ideal/conormal. Existing paperPrimeTimeOneConormalEquiv gives full I/I² preservation.
API pitfalls verified in /tmp: tendsto_rpow_atTop is ROOT namespace (NOT Real.tendsto_rpow_atTop); Filter.Tendsto.atTop_sub_const does NOT exist. Used tendsto_atTop_atTop on threshold B+1. Reduce Function.comp with change before linarith, otherwise it treats power composition opaquely. Complex.norm_natCast_cpow_of_pos hp s verified. Nat.exists_infinite_primes lives Mathlib/Data/Nat/Prime/Infinite.lean, not NumberTheory/Primes/Infinite.

3. PaperPrimeTransportAmbientRigidity.lean (6public=5theorems1def):
Reuse existing native scalar-character uniqueness, DO NOT reprove it:
- RHTower/ArithmeticFunctionScalarEvaluation.lean fully read54lines: arithmeticFunctionAugmentation:A→a[C]C, arithmeticFunctionAlgHom_apply(phi)(f):phi f=f1, _eq_augmentation.
- RHTower/FiniteAbscissaArithmeticUnits.lean lines1-70,188-238 read, namespace RHTower.FiniteAbscissaUnits: algHom_apply(phi)(f):phi f=f.val1, plus unit criterion and inverse closure. Entire finite-abscissa union is local; does NOT assert fixed-half-plane inverse closure.
New paperArithmeticEndomorphism_augmentation(F)(f):F f1=f1 by composing native augmentation with F.
- paperMoebiusPrimeTransport_ambient_orbit_iff (line27)(p)(t u): exists ambient complex algebra endomorphism F with F(T_p,t mu)=T_p,u mu IFF t=u.
- _ambient_extension_iff(p)(t): exists ambient F sending original mu to T_p,t mu IFF t=0. Strictly strengthens old time1-only obstruction.
- paperMoebiusPrimeFiniteSource(p)(t): actual T_p,t mu in finiteAbscissaArithmeticSubalgebra, with convergence threshold1 paid by prior paperMoebiusPrimeTransport_LSeriesSummable.
- paperFiniteAbscissaEndomorphism_augmentation: same coefficient-one invariance on native finite-abscissa algebra.
- paperMoebiusPrimeTransport_finiteAbscissa_orbit_iff (line64): same exact t=u classification on native finite-abscissa sources.
Proof: coefficient one is1-t; native uniqueness gives1-t=1-u; identity pays converse. Positive classification, not only negative no-go. Core action remains genuine and multiplicative; its proper-carrier distinction is necessary.

Route interpretation: direct MSC and MC. MSC now has actual divisor/conormal-preserving prefix escape and a sharp analytic cost, plus ambient algebra/domain rigidity. MC has exact finite signed energy escape, not a uniform cancellation producer. Prime changes with cutoff; no RH estimate inferred. Preservation restricted Re>0 (time1 adds Euler zeros on Re=0). General prime action mixes coefficients, though on mu the specialized formula is a mask. Keep those scopes explicit.

Searches: prime-prefix-escape-search.json COMPLETE partialfalse/errors[]70248files0pending; native finite prime aperture source-consumption is distinct (retains ALL primes through cutoff rather than deleting prefix via one escaping prime). Related XiGammaSixWoldJordanPrimeEscape.lean lines74-103 read, different Deninger packet carrier.
prime-augmentation-rigidity-search.json PARTIAL budget120, text/source_retrieval interrupted,70254files0pending; candidate and source Lean hit names inspected, native scalar evaluation hit used. Lexical follow-up prime-augmentation-lexical-search.json returned18hits; exact scalar character and finite-abscissa uniqueness inspected. Exhaustive rg found only old time1 ambient extension obstruction, no new orbit classification. No cards/prose read.
FiniteAbscissaDirichletUpperEnd.lean lines1-57 read: carrier={f|exists H:Real,forall y:Real,H<y -> LSeriesSummable f (y:C)}. paperMoebiusPrimeFiniteSource picks H1 using prior theorem with complex point ofReal y.

Artifacts prime-escape-{manifest,preaudit,proof-audit,searchback-audit,audits}.json;3 final leaf logs empty; axioms log;3 exact searchback JSON; index/lint logs. Final axiom probe retained /tmp/paper-prime-escape-axioms.lean. Removed /tmp/paper-prime-escape-api.lean, /tmp/paper-prime-augmentation-api.lean, /tmp/paper-prime-escape-audit.py, /tmp/paper-prime-escape-finish.py. No own source-tree .olean/.ilean/.c/.olean.private/.olean.server; no active jobs.

Trackers updated: current_prime_escape_batch complete; prime_prefix_escape_candidate complete; arithmetic_lnd_rigidity_candidate records completed stronger individual-time application (all LND zero was ALREADY in PaperArithmeticLogRigidity, do not duplicate). all-route-applications.json MC/MSC entries updated, fields synchronized to corrected ledger. Removed stale scope_progress.next_mechanisms claim of103pending source leaves: all117 source leaves complete. Next: resume focused Lean review of unreviewed routes/candidates, other Fourier receivers, remaining TraceCone applications. All39 review still incomplete.

Mandatory: one foreground Lean process per agent; no full/umbrella build, computations, heartbeat increases, source axioms or unpaid RH premises. Source-only builds use -o .lake/build/lib/lean/...; final audit plain lake --old env lean file. Read only Lean search hits, no cards. Exact searchback path field relpath, no suffix-name matching. Public regex excludes private. AxioM multiline regex and comma-whitespace split. Batch independent nondependent reads/searches, but edits/builds sequential. Keep chat progress<=60s. No further init/skill rereads needed; no agents authorized.