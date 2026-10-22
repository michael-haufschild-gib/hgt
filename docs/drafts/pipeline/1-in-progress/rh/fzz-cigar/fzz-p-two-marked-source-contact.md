# FZZ-P: two marked source variations and the missing integrated sign

- **ID:** fzz-p-two-marked-source-contact
- **Stage:** 1-in-progress
- **Type:** CANDIDATE
- **Source:** `rh-current-frontier-map.md`, FZZ-P; literal replica weights in `FZZCigarReplicaBackreaction.lean` and marked Wick exponents in `FZZCigarParityMarkedOPEChargeIncidenceNoGo.lean`.
- **Statement:** Determine whether the second replica variation supplies the source orientation missing from the integrated replica–momentum Ward identity, retaining the direct second variation of the source as well as the covariance term.

## Proof chain and hard obstacle

Fixed theta/FZZ source occurrence → integrated mixed replica–momentum Ward identity in the canonical phase frame → external-Gamma vacuum-delay saturation → linear replica-area passivity → critical line → RH.

The first arrow into the Ward identity is unproved. Gamma phase order, its unique delay minimum, arithmetic occurrence, and the final equivalence do not prove that arrow. This card attacks the higher-replica-order option in the live frontier. No RH premise, positivity assumption on the target integral, or new axiom is permitted.

## Plan

- [x] Inspect current route, relevant memories, source formulas, and primary literature.
- [x] Search the whole indexed corpus, including deep search and proof-method records; inspect incomplete coverage.
- [x] Derive the complete two-marked OPE response from the literal radial and winding weights.
- [x] Test the conjecture that its second variation has a positive covariance interpretation without an additional source term.
- [x] Formalize the exact source decomposition and compact-integral scale law; check in scratch, build the leaf module, wire the umbrella, audit axioms and lint.
- [ ] Return to the actual integrated theta-source Ward sign with the retained terms; do not treat a finite source identity as RH.

## Attempts and pivots

1. **Normalized mixed differentiation.** Rejected as an independent producer: the existing complete-profile spectator cancellation also cancels its momentum derivatives. No duplicate theorem is needed.
2. **Growth/asymptotic phase fixing.** Corpus search found `OrderOneFixedDivisorRigidity.exists_expAffine_of_entire_quotient` and `GammaNormalizationHorizon.gamma_periodic_curvature_rigidity`. These require their actual growth/convexity inputs. They do not supply the integrated Ward identity. Fixing a representation alone is insufficient; no new growth premise is being imposed on the desired RH theorem.
3. **Second marked source variation.** The conjectured cancellation fails. Use two independent deficits, not a second derivative of a one-marked truncation. The finite-level radial and winding weights are affine separately, but their pair contraction is bilinear. A direct mixed source term remains even when a first marked same-charge response vanishes. Its exact charge decomposition and integrated scale dependence are the positive survivor, now closed in Lean.

## Paper derivation and closed Lean result

Write `r(d)=1-kd/(k-2)` and `w(d)=1-d`. For two distinct insertions with winding-charge product `q`, the Wick exponent is

`E_q(d,e)=-(k-2)r(d)r(e)/2+k q w(d)w(e)/2`.

Expansion gives the mixed coefficient

`K_q=k q/2-k^2/(2(k-2))`.

In particular `E_+(d,e)=1-kde/(k-2)` and
`E_-(d,e)=1-k+k(d+e)-k(k-1)de/(k-2)`.
The first same-charge tangent at the undeformed second insertion vanishes, but the mixed tangent is `-k/(k-2)`, strictly negative for every physical level. It must not be dropped when differentiating both insertions.

The two-charge coefficient form has the exact decomposition

`K_+(x^2+y^2)+2K_-xy = k(x-y)^2/2-k^2(x+y)^2/(2(k-2))`.

It is positive on `(x,-x)` and negative on `(x,x)` for nonzero `x`. This is the charge coefficient before multiplying the position logarithm, not a positivity statement for the complete correlator or a claim about an integration measure.

**Closed integrated test.** For the literal opposite-charge pair, use logarithmic squared radius `x`, so the radial area measure supplies `exp(x)`. The compact annular integral is

`Z_L(d,e)=integral_0^1 exp((1+E_-(d,e))(L+x)) dx`.

Pulling out the constant exponential gives
`log Z_L-log Z_0=L(1+E_-)`, hence its mixed replica derivative is `L K_-`. Every integral is finite and strictly positive. Thus the direct source term survives actual compact integration and its relative mixed response ranges over all real values as the annulus moves. This does not evaluate the neutral screening sum or its meromorphic continuation. It isolates a regulator contribution that a purported positive integrated identity must cancel or retain.

**Next conjecture.** In the full neutral screening source, the complete position-scaling contribution might cancel against zero-mode normalization, ghosts, or the prescribed counterterm. Test the full normalization, with all screening depths retained, before inferring a Ward sign. Even a proved scale cancellation would not alone force external momentum-delay saturation.

**Full-source check.** `FZZCigarTorusReplicaNeutrality` supplies neutrality and nonzero coefficients at every finite depth, but no evaluated position integral. `ThetaCuspHawkingFZZNeutralScreeningRecoilEndpoint` explicitly labels the shared-counterterm producer falsified: renormalizability does not force one subtraction across reflected Mellin charts. It also labels identification of FZZ screening depth with four-dimensional recoil depth as conjectural. These are not missing implementation lemmas. The new compact-annulus identity cannot be extended to the full torus by invoking those statements. The actual integrated neutral source, its continuation and complete counterterms still need to be constructed/evaluated.

**Retrieval caution.** A method-search record described the definition `ThetaFZZParikhWilczekCriticalNeutralTorusSewing` as proving its universal implication. Direct source inspection shows it is a `Prop` definition followed by an RH equivalence, not a proved source identity. Generated method descriptions are leads only; they cannot discharge assumptions.

**Radial normalization follow-up, 2026-09-11.** The [neutral radial zero-mode audit](../../fzz-p-radial-zero-mode-ward.md) now evaluates that factor in its positive effective-coupling chamber. Geometric radial-volume subtraction retains a nonzero logarithmic-coupling Ward contribution. Its real convergence chamber is classified exactly. This is the target-radial cutoff, not the worldsheet-position scale `L` above; the two terms cannot be identified or canceled without the complete source relation. Nonzero modes, continuation outside the real convergence chamber, and external momentum remain to be assembled.

## Search evidence

2026-09-10: deep requests `mixed replica momentum Ward opposite winding source`, `entire nonvanishing exponential polynomial growth logarithm rigidity`, and `connected covariance partition derivative mixed`; hybrid request `replica Hessian contact covariance`. Searches cover project sources, installed dependencies, notes, and available proof-method descriptions. Results are partial: deadline/reranking/Qdrant timeouts and pending source coverage were reported. Empty proof-idea/ingredient lists do not establish absence of a theorem. Exact source text is checked separately with `rg`.

Broad arXiv searches used `sewing`, `susceptibility`, `monodromy`, `reflectionless`, and `rigidity`, preferring June–September 2026. The first date-restricted searches returned no results. Opened [Lin–Tang–Xu, 30 August 2026](https://arxiv.org/html/2608.29520v1): canonical asymptotic fundamental solutions fix monodromy data for their specified q-difference system; no identification with this theta/FZZ source has been established. Opened [monodromy defects, 7 July 2026](https://arxiv.org/abs/2607.06669): its charge-conjugation defects and fusion data do not by themselves give the required arithmetic Ward sign.

The direct source is [arXiv:2402.00932v3, §3.2.3](https://arxiv.org/html/2402.00932v3#S3.SS2.SSS3), equations (3.29)–(3.33). Its stated first-order replica prescription does not establish a full higher-order off-shell action. A two-marked contraction derived from the displayed weights must be distinguished from a complete second derivative of that action, including contacts and the continuation of the screening integral.

Two attempted transfers from the recent papers fail at specific inputs. The q-difference construction requires a source system of its displayed `Ax+B` type and prescribed asymptotic data; no such theta/FZZ system was obtained. The [July charge-conjugation defect construction](https://arxiv.org/html/2607.06669v1) uses compact Chern–Simons groups and their integrable affine representation/fusion data. Those data have not been identified with the noncompact cigar's marked theta-source integral. Its involution alone cannot supply positivity: the derived two-charge form is already invariant under exchanging charges while retaining opposite signs in its two channels. These failures concern the attempted transfers, not the cited papers.

## Status

Closed module: `formal/GaloisForLFunctions/RHTower/FZZCigarParityTwoMarkedSourceContact.lean`, namespace `GaloisForLFunctions.RHTower`.

- `fzzTwoMarkedOPEExponent_same`, `fzzTwoMarkedOPEExponent_opposite`, and `fzzTwoMarkedOPEExponent_mixedDeriv`: exact two-marked source and derivative.
- `fzzTwoMarkedChargeForm_split` and `fzzTwoMarkedChargeForm_indefinite`: exact positive winding/negative radial decomposition.
- `fzzTwoMarkedAnnularIntegral_pos`, `fzzTwoMarkedAnnularIntegral_logRatio`, `fzzTwoMarkedAnnularIntegral_mixedLogRatio`, and `fzzTwoMarkedAnnularIntegral_response_surjective`: finite positive compact integration and arbitrary relative mixed response.

Verification on 2026-09-10:

- `lake env lean /tmp/fzzp_two_marked.lean` passed. The installed proof body matches this scratch exactly.
- `lake build GaloisForLFunctions.RHTower.FZZCigarParityTwoMarkedSourceContact` passed; only the new leaf was compiled, with cached dependency messages replayed.
- `lake env lean /tmp/fzzp_two_marked_axioms.lean` audited all 19 theorems: only `propext`, `Classical.choice`, and `Quot.sound`; no added axioms or target hypotheses.
- `python3 scripts/formal_tools.py lint` passed, with existing large-file warnings.
- The module is imported by `RHTower.lean`. No umbrella build, full build, or numerical experiment was run.

The failed shortcut is extending first marked cancellation to two distinct marks, or assigning a sign to their relative integrated response from positivity alone. Its positive survivor is the exact source decomposition and integrated scale law above. FZZ-P is not retired: the actual full neutral source, prescribed normalization/continuation, and momentum coupling remain open. RH remains unproved.
