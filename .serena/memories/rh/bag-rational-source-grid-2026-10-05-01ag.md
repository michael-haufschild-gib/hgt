# BAG continuation01ag: rational cofactors + actual grid attachment
ACTIVE unbudgeted RH goal; BAG only; no subagents, computations, resource hacks, added axioms or full/umbrella builds. All owned processes terminal. This turn PROGRESS on positive rational source transfer; no physical saving or RH proof.

Read previous context in mem:rh/bag-balanced-label-cofactor-pole-2026-10-05-01af. Current new leaves:
- formal/GaloisForLFunctions/RHTower/ChiRamanujanRationalCofactors.lean:317 lines,24 public declarations.
- ChiRamanujanRationalGridAttachment.lean:328 lines,16 public.
Both namespace RHTower.BAGTrace; each imported once in RHTower umbrella after CofactorPole.
Final production62049/15658 exit0 empty logs under lake --old env lean leaf -o. Axiom13267 exit0 all40 only propext/Classical.choice/Quot.sound. Index56173 exit0 all40 exact API rows checked. Lint78719 exit1,24 unrelated unreachable modules; all inspected, no new-leaf/proof-debt error; global lint NOT clean.
Completed owned scratch sources cleaned, /tmp/*01ag.log and search JSON retained. No live jobs.

RationalCofactors:
CriticalNumerator P = positive n coprime to R=criticalPrimeLevel P.
DenominatorValuations P = prime Finsupp integer vectors nonnegative outside P.
DenominatorRational P = positive q whose denominator prime support lies in P.
mixedValuationsEquiv: retained integer vector × CriticalNumerator ≃ DenominatorValuations.
denominatorRationalEquiv: valuation ↔ denominator-supported rational.
mixedRationalEquiv and mixedRationalPairEquiv preserve literal n*product p^v and BOTH arbitrary complex cpow characters.
Proof uses outside Finsupp filter, nonnegative exponents integer product, rational-product injectivity and natural factorization. No numerator prime restriction.
criticalRationalLabelCoefficient P r q = (A*a_r cast)*prod_l complexCoefficient(1/l)(v_l(q)+labelshift).
criticalRationalLabelCone P p q r s t w = Dp(w1)Dq(w2)Dr(w1*w2) rationalCharacter s w1 rationalCharacter t w2.
criticalRationalCone sums labels masked p=r OR q=r.
criticalRationalCone_equiv gives weighted valuation cone × both coprime numerator powers.
criticalRationalCone_hasSum (Re(s),Re(t)>1) = criticalCompletedConeEuler P s t.

GridAttachment:
criticalPrimeImage P=P.image Nat.val; grid modulus = R^2.
criticalGridRational P a = a/R^2 for positive integer a.
criticalGridRational_valuation=v_p(a)-2.
criticalIntegerBase p a=I_(p²|a)-I_(p|a)/p.
criticalIntegerTag p a=I_(p|a)/p-1/p².
criticalGridRational_base/tag/label/source: normalized complex factors match these exact integer weights.
criticalIntegerSource_grid: full label sum = actual ramanujanCriticalGridWeight.
criticalGridRational_actualMass: sum Dp(a/R²)=actual grouped critical atom mass at a modR²; EVERY positive lift including zero residue.
criticalRationalLabelCoefficient_off_grid: for denominator-supported q, den(q)∤R² forces every label coefficient zero.
criticalGridRational_exists: den(q)|R² implies q=a/R² for positive a.
criticalRationalLabelCoefficient_support: every nonzero Dp has positive grid lift.
This closes positive multiplicative cone source attachment; NOT full physical action/projector per-sector cancellation.

Docs current:
P1 docs/drafts/pipeline/1-in-progress/bag-critical-distinguished-prime-source.md
P2/P3 bag-rational-numerator-cofactors.md
Working log bagchi-quantitative-sparse-recurrence-working-log.md appended01ag.
Frontier docs/reports/rh-current-frontier-map.md C28.56ag.12.
P1 includes next exact conjecture and proof plan, NOT yet Lean-proved.

Searches all completed, nonpartial, no errors; full candidates20/source_arguments20/ingredient sets inspected:
44715 /tmp/bag-rational-cofactor-search-01ag.json inventory65764;
61153 /tmp/bag-grid-valuation-search-01ag.json inventory65766;
31155 /tmp/bag-physical-pole-pairing-search-01ag.json inventory65773;
5344 /tmp/bag-mellin-physical-pairing-search-01ag.json inventory65775;
29038 /tmp/bag-cone-schwartz-mellin-search-01ag.json inventory65775.
Refresh incomplete background indexer; compiler mostly pending/source_only; no absence claims.
Reject ABHN/coords_symm proposed pole cancellation. Reject proposed positive-axis Mellin norm⇒vertical integrability (different integrals). Sonin/Cap lemmas carry premises not proved for actual physical profile. Generic mellinInv_mellin_eq useful after actual convergence/verticalL1/continuity.

NEXT HARD ATTACK:
Phi_N(x,y)=Fourier(bagCubicPhysicalSchwartz)(x,y,-x*y), full physical polynomial cone restriction. Actual target primeGaussianCubicOffDiagonal is COMPLEX and its norm must be o(N/log²N); real-part smallness insufficient.
Construct Phi as Schwartz via current mathlib SchwartzMap.compCLM: need e.HasTemperateGrowth and ∃k C ∀x, norm x≤C*(1+norm(e x))^k. e=(x,y,-xy) polynomial; first coordinates give lower norm. Use EuclideanSpace R (Fin2) for Fourier; ordinary R×R uses max norm.
Then g(u,v)=exp(c*u+d*v)*Phi(exp u,exp v), c,d>1, should be Schwartz. Mixed derivatives finite sums of exponential weights times polynomially weighted Phi derivatives. Schwartz decay controls positive ends; c,d>0 controls negative ends incl mixed quadrants. Prove full 2D log profile Schwartz; Fourier inversion yields absolute two-variable Mellin inversion, no assumed vertical convergence.
On fixed vertical lines each complete rational source term has same norm as at real c,d; criticalRationalCone_hasSum supplies absolute sum, Mellin verticalL1 supplies integral majorant, justifying actual signed sum/integral exchange. This gives positive-cone physical pairing only. Full pole/near-cone/tail coupling, negative/zero sectors, growing moments, moving cofactors, common-height self-return and RH stay open.
Balanced double residue from01af is NONZERO negative; cannot claim cancellation by zero residue or replace full hyperbolic transition by stationary product.

Current APIs/source inspected:
mathlib Analysis/MellinInversion.lean49 mellin_eq_fourier;98 mellinInv_mellin_eq.
SchwartzSpace/Basic.lean918 compCLM (growth, polynomial lower bound);974 compCLM_apply;980 compCLMOfAntilipschitz.
Function.HasTemperateGrowth .comp/.add/.sub/.smul/.mul/.pow, CLM and CLE have growth, but no automatic pi/prod rule found in that source.
EuclideanSpace.equiv (Fin n) R=PiLp.continuousLinearEquiv; inverse sends ordinary pi tuple to WithLp.
PiLp.norm_apply_le.
Use FourierTransform.fourierCLM, not defining SchwartzMap.fourierTransformCLM directly per source comment.
ChiHyperbolicFourierTransition: complete bagHyperbolicTransition/bagHyperbolicKernel equality for r>0, exact full profile, no stationary truncation.
ChiPrimeGaussianCubicTransverse71 transition integral alpha,beta e(r υ α+r ξ β-rαβ)*Ffτ(alpha)*Ffτ(beta),77 entire Mellin tau profile. 198+ full r-integral Fourier identity.
ChiPrimeGaussianCubicWindowTransition42 actual fτ(p)=ηp*smoothAFECutoff(p/N)/logp * oscillation(-τlogp).
DeningerCapSchwartz contains log-weight proof pattern, but requires Cap; can't invoke for actual profile. Its paper mechanism adaptable only after proving generic replacements.

Development lessons:
Explicit fns in prime-image sum/prod reindexing avoid subtype coercion inference issues.
For integer v≥0 use rw[←zpow_natCast]; exact congrArg (fun i:Z=>(p:Q)^i) (Int.toNat_of_nonneg hv); don't reverse-rewrite through own exponent.
Specify inner Nat type before casting Finsupp.prod toQ.
Specify denominator argument in Nat.factorization_eq_zero_of_not_prime; otherwise wrong occurrence rewritten.
For positive rational numerator natAbs cast, congrArg Int→Rat then simpa only[Int.cast_natCast], not exact_mod_cast overnormalization.
Do not repeat successful leaf audits; no more code changed after audited builds.