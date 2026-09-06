# Actual parity-ground source moment and unavoidable pole coupling

Goal ACTIVE, actual mathlib RH UNPROVED. Previous turn was progress (physical Gamma/cancellation). This turn adds 18 audited public theorems in two wired, individually built leaves. Full chain remains exact source → ground-specific forcing control → exclude unique possible zero constrained ground → all finite aperture positive floors → weighted pole exclusion → RH. No numerical computation or oracle.

## Exact forcing scalar (7 publics, 1 definition)
`RHTower.CCMRestrictedWeilPolarGroundSourceMoment` imports prior source cancellation and parity forcing.
- `inner_ccmRestrictedWeilOperator_comm`: actual self-adjoint LinearPMap gives full complex mixed symmetry for actual domain vectors.
- `ccmPolarBoundarySourceFunctional a`: (innerSL ℂ actualBoundaryDefect).comp J_a, continuous on entire complete form domain.
- `ccmPolarBoundarySourceFunctional_eq_integral`: F_a(u)=∫cutoff exp(x/2)[B(a-x,a+x)-Epsi(exp(a-x))-EM(a+x)](J_a u)(x) dx, for EVERY complete form vector. Absolute product integrability is inherited from actual L² defect and Ju.
- `inner_ccmPolarApertureVector_half_self`: 2sinh(a); opposite Gram 2a already formal last turn.
- `polarParityGram_pos`: 2sinh(a)+2ar>0 for r=±1; uses corpus Real.self_lt_sinh_iff.
- `polarSingleForcing_coefficient_eq_source_div`: any actual domain state Ju constrained and HJu=EJu+c(p++r p-) has c=F_a(u)/(2sinh(a)+2ar), for either parity. Self-adjointness moves H to pole; <p+,Ju>=0 removes energy term.
- `norm_ccmPolarBoundarySourceFunctional_apply_le`: norm F≤norm literal defect *norm Ju.
- `exists_polarGround_boundarySource_forcing`: unconditional at every aperture, nonzero actual constrained parity ground has full operator equation with exactly that source quotient. No selected parity, sign, or vanished forcing.

## Endpoint/coupling and positive survivor (11 publics)
`RHTower.CCMRestrictedWeilPolarSourceNonvanishing` imports above.
- `tendsto_ccmGammaPolarBoundary_right`: B(a-x,a+x)→+∞ as x→a from below, since -1/2 log(1-exp(-2(a-x))) diverges; remaining L→2a terms finite.
- `tendsto_ccmPolarBoundaryArithmeticProfile_re_right`: actual K_a(x)=exp(x/2)[B-Epsi-EM]→+∞. On aperture psi(exp(a-x))≤psi(exp(2a)); EM≤log4+5. So B-Epsi-EM≥B-[psi(exp2a)+log4+5]. Exponential prefactor tends positive exp(a/2).
- `not_ae_bounded_ccmPolarBoundaryArithmeticProfile`: no essential upper bound on open aperture. Generic private proof: eventual near-endpoint lower bound C+1 contains positive-measure open interval, intersects any AE upper bound.
- `ccmPolarForcing_coeFn`: literal AE cutoff c+exp(x/2)+c-exp(-x/2).
- `ccmPolarWeilBoundaryDefect_ne_forcing`: actual source defect outside EVERY two-pole vector, using bounded continuous pole profile on compact aperture versus no AE bound.
- `exists_polarConstrained_boundarySource_ne_zero`: if F vanished on full constrained sector, existing continuous-annihilator theorem represents it by a pole vector; dense J identifies this with defect, contradiction.
- `polarConstrained_boundarySource_surjective`: scaling a nonzero source witness realizes every complex value on completed constrained space.
- `ccmRestrictedWeilOperator_polarPlus_ne_forcing`: actual H p+ outside entire two-pole span, since it differs from defect by a pole vector.
- `ccmGammaPolarBoundary_symmetric_decomposition`: B(R,L)=-[log(1-exp(-2R))+log(1-exp(-2L))]/2+log(1+exp(-L)), for L>0 (R arbitrary). Factor 1-e^-2L=(1-e^-L)(1+e^-L).
- `ccmGammaPolarBoundary_sub_swap`: for R,L>0, B(R,L)-B(L,R)=log(1+e^-L)-log(1+e^-R).
- `abs_ccmGammaPolarBoundary_sub_swap_lt`: absolute asymmetry <log2, since each log(1+e^-t)∈(0,log2).

## Interpretation and exact live gap
Automatic invariance of pole span is FALSE for actual unrestricted operator at every aperture. Positive survivor is actual nonzero/surjective constrained source coupling plus symmetric singular boundary decomposition and bounded reflection asymmetry. This does NOT say a particular ground has nonzero source moment, nor rule out its forced equation if moment nonzero. No universal linear sign on arbitrary constrained complex vectors can serve as source theorem; use selected ground's extra structure. RH route O remains LIVE, not retired.
Next conjecture: derive parity-specific source kernels from symmetric B plus reflected literal arithmetic errors. Need separate nonvanishing on BOTH parity sectors; nonvanishing on their sum does not prove that. New symmetric decomposition suggests both endpoint log coefficients are exp(a/2)+r exp(-a/2)>0 but this has NOT been welded/formalized for parity kernels. Then seek actual ground comparison; source moment presence alone cannot exclude zero energy. Corpus searches this turn: forcing coefficient, forcing annihilator, boundary unbounded, endpoint bounded, Gamma boundary symmetric, Weil positivity preserving, constrained oscillation. Relevant seed SuzukiBoundaryLogEndpointBlowUp; no independent constrained oscillation corpus hits.

## Files/audits
Formal card `docs/drafts/pipeline/3-formalized/weil-ground-source-moment-and-nonvanishing.md`, full dependency-closed proof and conjecture/fail/pivot/positive survivor. Active `1-in-progress/weil-gamma-pole-boundary-action.md` keeps only ground-specific comparison and future parity questions. Frontier O and universal STATUS updated current state. Scratch `/tmp/hgt-ground-source.3dwu8uiu/Force.lean`, Boundary.lean PASS. Named final leaf builds PASS 12s and8.3s; no full/umbrella builds. Audit.lean prints all18 exactly [propext,Classical.choice,Quot.sound] and actual RH. Whole formal lint PASS (Lint.txt/.err), only existing size warnings. git diff --check PASS. All owned Lean/build handles terminal; ps no Lean processes. No commit/push/subagent.

## Lean lessons
LinearPMap.adjoint_isFormalAdjoint takes dense-domain proof first (operator implicit). Rewrite self-adjoint equality using LinearPMap.isSelfAdjoint_def.mp; resulting formal-adjoint predicate applies to both domain vectors.
inner_smul_right and norm_inner_le_norm need explicit ℂ/vector/scalar arguments on these subtype spaces. `push_cast at hpair ⊢` together avoids mismatched Complex sinh normal forms. `module` can normalize a cast exponential differently on each side; retain let k, `change` the exact vector identity, expand sub_smul/add_smul, then abel.
`Ioo_mem_nhdsLT hl` may elaborate as raw filter-membership Exists when `.and` is used directly; `filter_upwards [Ioo_mem_nhdsLT hl,...]` works. Positive-measure AE witness is `Measure.exists_mem_of_measure_ne_zero_of_ae`, not root MeasureTheory. `mem_nhdsLT_iff_exists_Ioo_subset.mp` yields explicit nonempty short interval. `DenseRange.eq_of_inner_left ℂ` directly takes all-input pairing equality.
Serena previously ignores formal paths; new files use scratch→file writes. Always run Lake in formal/; accidental root-cwd named audit exits before doing any build.