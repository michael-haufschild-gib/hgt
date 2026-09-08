# Positive descent of actual curvature to compact modular orbit fields

- **ID:** selberg-actual-positive-quotient-curvature
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** [Active Selberg loop](../1-in-progress/selberg-quarter-conjecturing-loop.md), cycle 36; [actual measure transport](selberg-actual-curvature-transport.md).
- **Statement:** The literal space of full SL(2,Z) periodizations of compact continuous half-plane tests carries a unique positive real linear functional agreeing with every original actual curvature pairing. Original regulator integrals converge to it.

## Goal and scope

Establish consistent positive descent while retaining every seam contribution and every stabilizer repetition. All source assertions use the constructed measure of the original Maass source at any real eigenvalue. No quotient measure, seam-null hypothesis, automorphic lift, or spectral inequality is supplied. This constructs a functional on the literal periodization range. Identification with every compact continuous function on a topological quotient, a representing quotient measure, finite total quotient mass, and the quarter comparison are not asserted.

## Gates

- [x] 0 → 1: actual source and precise compact orbit-test space.
- [x] 1 → 2: dependency-closed paper proof below, [PROVED HERE].
- [ ] 2 → 3: all complete scratch proofs passed; final source/build/axiom/lint audits pending.
- [ ] 3 → 4: independent novelty/publication audit.

## Complete paper proof [PROVED HERE]

Let G=SL(2,Z), acting on H by its actual modular action, and let mu be the original source's constructed regular curvature measure. The existing source theorem proves A_*mu=mu for every A in G. For a compact continuous real test g set P(g)(z)=sum_A g(Az), with all group elements included.

Proper discontinuity of this actual action is available from the checked cast into SL(2,R). For every compact K and compact support L only finitely many A satisfy A K intersect L nonempty. Taking K={z} proves finite support of the orbit series at each point. Taking K to be a compact neighborhood of z proves that one fixed finite sum represents P(g) throughout that neighborhood. Therefore P(g) is continuous even across modular seams. Reindexing by right multiplication gives P(g)(Az)=P(g)(z). For two compact tests g,h, their products g(z)h(Az) vanish identically for all but finitely many A, by the same compact-overlap theorem.

Each overlap product is a continuous compact test, hence is genuinely integrable for mu. The series of its absolute integrals is finitely supported, so the integral/sum interchange is justified. Invariance of mu gives, term by term,

integral g(z) h(Az) dmu(z) = integral h(z) g(A^(-1)z) dmu(z).

Reindexing by inversion and summing proves the orbital pairing identity

integral g P(h) dmu = integral h P(g) dmu.

No fundamental cell or boundary-null statement is used in this identity.

For any compact K in H, its image in C is compact and has positive height. The checked compact smooth cutoff construction gives a nonnegative planar compact test equal to one on that image, supported inside H. Its checked restriction gives b in C_c(H,R) with b=1 on K. Because P(b) is a finite nonnegative sum including the identity term, P(b)>=b. The function

w(z)=b(z)/max(1,P(b)(z))

is continuous and compactly supported, with a globally positive denominator and w>=0. Denominator invariance gives the exact identity

P(w)=P(b)/max(1,P(b)).

Consequently P(w)<=1 everywhere and P(w)=1 on K. Every kernel and stabilizer repetition remains in both numerator and denominator; no injective parametrization of point orbits is presumed.

If K contains the support of g, then g P(w)=g pointwise, including outside K where g is zero. The orbital pairing identity gives

integral g dmu = integral w P(g) dmu.

For two tests choose K containing both supports. If P(g)=P(h), these weighted integrals agree. If P(g)<=P(h), the nonnegative common weight and genuine integrability of the compact products give the corresponding integral inequality. In particular P(g)>=0 implies integral g dmu>=0 even if g itself is signed.

Periodization is a real linear map: finite orbit sums commute with addition and scalar multiplication. Let V be its literal range as a submodule of real functions on H. Every F in V has a compact representative g. Define Q(F)=integral g dmu. The representative-independence theorem makes this well-defined; the proved integral equalities and scalar laws make it linear. Pointwise comparison on V and the comparison theorem make Q positive. Its value on every original orbit test is its original curvature integral. Every element of V has such a representative, so this property uniquely determines Q among positive linear functionals. Finally, the previously proved original regulator limit for each compact g gives J_e(g)->Q(P(g)) on the original nontrivial regulator filter.

## Multiplicity and noncompact limits

The construction deliberately uses the literal SL(2,Z) sum. In comparing it with a PSL(2,Z) fundamental-cell convention, the kernel {+1,-1} repeats each projective term twice. This normalization must be proved explicitly in any standard-cell mass formula; that comparison is not implemented here. Elliptic stabilizers produce further repetitions, already retained in the local normalization and orbital pairing. The proof does not need to delete atoms or seam curves.

The constant function one is not asserted to belong to V. Local normalized weights give one on prescribed compact regions, not on all of the noncompact quotient. Passing to total mass therefore needs a separate exhaustion and source tail argument. Existing compact-test convergence does not justify this passage by itself.

## Corpus mechanisms and conjecture loop

All alternative searches used --any. Pairing/cutoff-independence/orbit-normalization/double-counting: 28 declarations in 20 modules. Positive-descent/range-functional/kernel-inclusion: 15 in 12. Total-mass/exhaustion/tightness: 155 in 25. Counts are index coverage, not claims to inspect every result.

Inspected ThetaCuspHawkingBMSmoothModularPeriodization provided the local finite-sum mechanism, transferred here to real compact tests and the integral group. ConnesLemma3Unfolding supplied the inversion reindexing mechanism but required a fundamental-domain premise; the new proof instead uses two compact overlapping factors and the already constructed invariant measure. Existing SelbergLocalTestGreen and SelbergUpperHalfPlaneCompactTests construct the compact majorant. The actual normalized weight discharges every needed partition condition internally.

For the next total-mass conjecture, inspected GoldstoneFabriPicassoCorpusApplications.fabriPicasso_localWardInvisibility_globalMassEscape exhibits a separate corpus family with local vanishing but nonvanishing total mass; it is a mechanism showing why local convergence alone is insufficient, not a counterexample involving the Maass source. ScheffeCounting requires equality of total mass before its uniform-tail conclusion, so cannot be used to assume the missing total-mass identity. LeafTightness derives tail control from an already proved uniform moment; an analogous original-source cusp estimate remains to be constructed here.

## Lean and audit

- formal/GaloisForLFunctions/RHTower/SelbergCompactPeriodization.lean: 17 public declarations.
- formal/GaloisForLFunctions/RHTower/SelbergMaassCurvatureDescent.lean: 8 public declarations.
- formal/GaloisForLFunctions/RHTower/SelbergQuotientCurvature.lean: 15 public declarations including the actual orbit-test submodule alias.
- All three complete scratch proofs passed without warnings; finished modules are wired into RHTower.lean. Final audit pending below.
