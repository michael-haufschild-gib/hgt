# Paired Quasi-Elliptic Constraint Rigidity

- **ID:** paired-quasi-elliptic-constraint-rigidity
- **Stage:** 3-formalized / not new scientific knowledge
- **Type:** CLASSIFICATION BRIDGE / ANTI-NOVELTY RESULT
- **Scientific status:** `[BRIDGE — NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Statement:** The apparent class of one-pole paired quasi-elliptic primitives collapses exactly to nonzero scalar multiples of translates, plus constants, of the elliptic-gamma logarithmic derivative. Its spectrum theorem is therefore a reformulation of the elliptic-gamma theorem, not a broader discovery.

## Setup: a constraint-defined class

Let `tau,sigma in H` and assume that

`1,tau,sigma`

are linearly independent over `Q`. Put

`Lambda_tau=Z+Z tau`, `Lambda_sigma=Z+Z sigma`,

`H=Z+Z tau+Z sigma`.

Let `U_tau,U_sigma,F` be meromorphic functions on `C` satisfying

`Delta_1 U_tau=Delta_1 U_sigma=Delta_1 F=0`,

`Delta_tau U_tau=c`, `Delta_sigma U_sigma=c`,

`Delta_sigma F=U_tau`, `Delta_tau F=U_sigma`

for some `c in C`. Suppose that `U_tau` has exactly one simple pole, with nonzero residue, modulo `Lambda_tau`, and that `U_sigma` has exactly one simple pole, with nonzero residue, modulo `Lambda_sigma`.

The equality of the two constants is the compatibility condition forced by commuting the two constraints on `F`. Existence is assumed; uniqueness and differential complexity are conclusions.

Call such an `F` a **simple paired quasi-elliptic primitive**.

## Collapse theorem `[PROVED HERE]`

Let

`Psi=delta log Gamma(z;tau,sigma)`,

`lambda_tau=delta log theta_tau`, `lambda_sigma=delta log theta_sigma`,

with the same normalization of theta functions used by the elliptic gamma functional equations. Then every simple paired quasi-elliptic primitive is of the form

`F=r Psi(z+a)+C`

for a nonzero `r in C`, some `a in C`, and `C in C`; necessarily

`U_tau=r lambda_tau(z+a)`, `U_sigma=r lambda_sigma(z+a)`.

Indeed, let `p_tau` be the unique pole class of `U_tau` and `r_tau` its residue. The functions `U_tau` and `r_tau lambda_tau(z-p_tau)` have the same pole divisor and residues. Their difference is entire, `1`-periodic, and has constant `tau`-increment. Its derivative is an entire elliptic function and hence constant; `1`-periodicity forces that constant to vanish. Thus

`U_tau=r_tau lambda_tau(z-p_tau)+a_0`.

The same argument gives

`U_sigma=r_sigma lambda_sigma(z-p_sigma)+b_0`.

The common quasi-period `c` is the residue times the standard theta quasi-period, so compatibility forces `r_tau=r_sigma=:r`.

The unconditional theorem `triptic-orbit-residue-reciprocity` identifies the two one-point orbit divisors. Hence

`p_tau-p_sigma in Lambda_tau+Lambda_sigma=H`.

Choose `a in C` satisfying

`-a=p_tau mod Lambda_tau`, `-a=p_sigma mod Lambda_sigma`.

After using the constant quasi-periods of the theta logarithmic derivatives, the preceding formulas become

`U_tau=r lambda_tau(z+a)+a_1`, `U_sigma=r lambda_sigma(z+a)+b_1`.

Now `W=F-r Psi(z+a)` is `1`-periodic and has constant increments `Delta_sigma W=a_1`, `Delta_tau W=b_1`. Its derivative has periods `1,tau,sigma`; their group is nondiscrete, so `delta W` is constant, and `1`-periodicity forces `delta W=0`. Hence `W` is constant and `a_1=b_1=0`.

The abstract class therefore contains no functions beyond translated scalar-affine copies of the elliptic-gamma logarithmic derivative.

## Consequent spectrum theorem `[PROVED; SCIENTIFIC CLAIM SPLIT OUT]`

Every simple paired quasi-elliptic primitive has exact differential-algebraic translation spectrum

`Spec_DA(F)={h in C : Delta_h F is DA over C(z)}=H`.

More strongly, for arbitrary shifts `h_1,...,h_n`, let `m` be the number of distinct nonzero cosets among

`h_1+H,...,h_n+H in C/H`.

Then

`dtrdeg_(C(z)) C(z)<Delta_(h_1)F,...,Delta_(h_n)F>_delta=m`.

Thus the complete differential-algebraic dependence matroid of the translation defects is the partition matroid of `C/H`, with the zero coset algebraic.

In addition:

1. `F` is hypertranscendental over `C(z)`;
2. the four displayed constraint equations determine `F` uniquely up to addition of a constant;
3. every defect `Delta_h F` with `h notin H` is hypertranscendental.

Only the one-simple-pole hypothesis on one of the two quasi-elliptic increments is needed for the spectrum and matroid conclusions. The symmetric hypothesis identifies a natural self-contained class and makes the constraint system independent of a distinguished direction.

## Proof

### 1. The constraints are DA but do not generate `F`

The derivative `delta U_tau` is `Lambda_tau`-elliptic because both additive increments of `U_tau` are constant. Hence `delta U_tau`, and therefore `U_tau`, is DA over `C(z)`. Similarly `U_sigma` is DA.

The three structural differences of `F` are therefore DA. Since DA meromorphic functions form a differential field and translation preserves differential algebraicity,

`H subset Spec_DA(F)`.

This is only a constraint subgroup. It does not give a differential-algebraic construction of `F`.

### 2. Every translated defect obeys a paired elliptic system

For `h in C`, put `d_h=Delta_h F`. Commuting translations gives

`Delta_sigma d_h=Delta_h U_tau=:b_tau,h`,

`Delta_tau d_h=Delta_h U_sigma=:b_sigma,h`.

The constant quasi-periods cancel, so `b_tau,h` belongs to the elliptic function field `E_tau` of `C/Lambda_tau`, and `b_sigma,h` belongs to the elliptic function field `E_sigma` of `C/Lambda_sigma`.

Let `K=E_tau E_sigma` be their compositum inside the meromorphic functions. It is a translation-stable differential field and every element of it is DA over `C(z)`.

All elements of `K<d_h : h in A>_delta`, for any set `A`, are 1-periodic. An element fixed by both `T_tau` and `T_sigma` therefore has every period in the nondiscrete group `H`, so it is constant. Hence

`(K<d_h : h in A>_delta)^(T_tau,T_sigma)=C`.

This collapse of joint constants is the first rigidity input.

### 3. Paired telescoping lemma

We use the following consequence of several-automorphism parameterized Picard--Vessiot theory.

**Lemma.** Let a differential field `k` have commuting automorphisms `rho_1,rho_2`, algebraically closed common fixed field `C`, and zero derivation on `C`. Let a differential field extension `F/k`, stable under both automorphisms, have the same joint fixed field. If `y_i in F` and

`rho_j(y_i)-y_i=a_(j,i) in k`

and the `y_i` are differentially algebraically dependent over `k`, then there are `L_i in C[delta]`, not all zero, and one `g in k` such that `sum_i L_i(y_i)=g` and, simultaneously for `j=1,2`,

`sum_i L_i(a_(j,i))=rho_j(g)-g`.

To prove the lemma, extend `C` to a differential closure `Ctilde`. Regularity over the algebraically closed field `C` preserves domains and gives

`Frac(F tensor_C Ctilde)^(rho_1,rho_2)=Ctilde`.

For fractions, choose a finitely generated coefficient algebra `A subset Ctilde`. At a Zariski-dense set of `C`-specializations of `A`, an invariant fraction specializes into `F^(rho_1,rho_2)=C`. Expanding numerator and denominator in a finite `C`-basis, their coefficient vectors are proportional on that dense set. All two-by-two minors vanish, so the original fraction lies in `Frac(A) subset Ctilde`.

Over `Ctilde`, apply the several-automorphism Picard--Vessiot theory of Hardouin--Singer to the compatible unipotent system. Differential dependence makes its differential Galois group a proper differential algebraic subgroup of `G_a^n`. Cassidy's additive-group classification supplies a nonzero homogeneous linear differential form, and the fixed-field theorem supplies a single simultaneous telescoper `gtilde`.

Only finitely many coefficients occur. Fix numerator, denominator, and differential-order templates, clear denominators, and normalize one coefficient of the nonzero linear form to one. The simultaneous identities become a finite polynomial system over `C` with a solution over `Ctilde`. Algebraic closedness of `C` descends a solution to `C`, proving the lemma.

If a finite defect family is DA over `C(z)`, it is DA over `K`: use the common compositum `K(z)`, which is DA over `K` because `delta z=1`. Applying the lemma therefore yields operators `L_i in C[delta]`, not all zero, and one `g in K` with

`T_sigma(g)-g=sum_i L_i(b_tau,h_i)`,

`T_tau(g)-g=sum_i L_i(b_sigma,h_i)`.

### 4. Descent from the product to one elliptic curve

The fields `E_tau` and `E_sigma` are algebraically independent over `C`. Indeed, if nonconstant `f in E_tau` and `v in E_sigma` satisfy `P(f,v)=0`, then all `v(z+n tau)` are roots of the fixed polynomial `P(f(z),Y)`. Two coincide, so a nonzero integer multiple of `tau` is a period of `v`. The period lattice of a nonconstant `Lambda_sigma`-elliptic function is commensurable with `Lambda_sigma`, producing a nontrivial rational relation among `1,tau,sigma`, contradiction.

Thus `K` is the function field of the product of the two elliptic curves. The translation `T_sigma` acts on the `E_tau` factor and trivially on the `E_sigma` factor. Specializing the second factor at any point outside the denominator locus sends the first telescoping equation to

`T_sigma(g_tau)-g_tau=sum_i L_i(b_tau,h_i)`

for some `g_tau in E_tau`.

### 5. A single pole determines the exact spectrum

Let `p` be the unique pole class of `U_tau` on `C/Lambda_tau`, with residue `r ne 0`. The elliptic function

`b_tau,h=U_tau(z+h)-U_tau(z)`

has simple poles of residues `r` and `-r` at `p-h` and `p`. Their `T_sigma`-orbits coincide exactly when

`h in Lambda_tau+Z sigma=H`.

Let `L in C[delta]` be nonzero of order `N`. If `h notin H`, then on the orbit of `p-h`, the order-`N+1` principal-part coefficient of `L(b_tau,h)` is nonzero at exactly one orbit point. By contrast, every fixed-order principal-part coefficient of `T_sigma(u)-u`, for `u in E_tau`, sums to zero along each orbit: the finite pole support makes the sum telescope. Therefore

`L(b_tau,h) ne T_sigma(u)-u`

for every elliptic `u`. The paired telescoping lemma now excludes differential algebraicity of `d_h`. Together with Step 1 this proves `Spec_DA(F)=H`.

### 6. The finite-shift matroid

Choose shifts `h_1,...,h_m` representing distinct nonzero cosets of `H`. If their defects were differentially dependent, Step 3 and Step 4 would give

`T_sigma(g_tau)-g_tau=sum_i L_i(b_tau,h_i)`

with not all `L_i` zero. Choose a largest differential order `N` and an index `i` with nonzero order-`N` coefficient. The orbit of `p-h_i` is neither the orbit of `p` nor any orbit `p-h_j` for `j ne i`. Its order-`N+1` principal-part sum on the right is therefore one nonzero term, contradicting telescoping. The representative defects are differentially algebraically independent over `K`.

If `h in H`, then `Delta_h F` is DA. If `h_i-h_j in H`, then

`Delta_(h_i)F-Delta_(h_j)F=Delta_(h_i-h_j)F(z+h_j)`

is DA. This gives the upper bound for any finite family. Finally `K(z)` is DA over both `K` and `C(z)`, so differential transcendence degree is unchanged on passing through it. The lower and upper bounds agree and give the displayed matroid formula over `C(z)`.

### 7. Constraint uniqueness and hypertranscendence

The difference of two solutions of the four constraint equations has periods `1,tau,sigma`. Since `H` is nondiscrete, that difference is constant. Thus the constraints fix `F` up to one scalar constant.

Choose `h notin H`. The exact spectrum makes `Delta_h F` hypertranscendental. If `F` were DA, all its translates and translation differences would be DA. Hence `F` is hypertranscendental.

This realizes the constraint-first principle for elliptic gamma.  The collapse theorem shows that
the present one-pole axioms do not define a scientifically broader class.  It does **not** show
that the consequent theorem about the actual elliptic gamma function is known.  That scientific
claim is now separated in
`../new_scientific_knowledge/irrational-elliptic-gamma-hypertranscendence-matroid.md`.

## Elliptic gamma as a corollary

For the additive elliptic gamma function, take

`F=delta log Gamma(z;tau,sigma)`,

`U_tau=delta log theta_tau(z)`, `U_sigma=delta log theta_sigma(z)`.

The standard elliptic-gamma functional equations give the paired constraints. Each theta logarithmic derivative is 1-periodic, has constant increment under its second lattice generator, and has one simple pole of residue one modulo its lattice. The theorem therefore proves hypertranscendence of the elliptic-gamma logarithmic derivative and the exact rank-three spectrum and defect matroid. Logarithmic differentiation transfers the same spectrum and differential-transcendence-degree formula to all shift quotients `Gamma(z+h)/Gamma(z)`, and then to `Gamma` itself.

## Anti-novelty audit

### Exact parents used

1. Hardouin--Singer (2008): parameterized Picard--Vessiot theory, including several commuting automorphisms, and the additive telescoping criterion.
2. Cassidy: differential algebraic subgroups of the additive group.
3. Dreyfus--Hardouin--Roques--Singer (2018), Babbitt (2025), and Arreche--Babbitt (2025): orbital and panorbital residues for one translation on one elliptic curve.
4. Classical algebraic independence of elliptic function fields with noncommensurable lattices.

### What is not inherited from those parents

- The one-curve residue theory does not remove the nonconstant periodic constants in the ambient meromorphic solution field.
- The several-automorphism Galois formalism does not identify this paired quasi-elliptic class, its joint-constant collapse, or its pole-orbit geometry.
- Existing algebraic-independence results over elliptic fields concern multiplication endomorphisms or independence between solutions of separate operator equations, not a common meromorphic primitive constrained over two noncommensurable elliptic curves.
- No located source states the exact spectrum `H`, the finite defect-coset matroid, or constraint uniqueness together with hypertranscendence.

The proof mechanism is the combination of joint-constant collapse, simultaneous telescoping with one certificate in the product field, specialization to one elliptic factor, and orbit-local principal-part separation. Under the one-pole hypotheses it gives no additional scientific object beyond elliptic gamma.

### Preliminary literature verdict

Primary-source searches through 2026 found no theorem using this terminology.  The abstract class
still fails novelty because it collapses to a known special-function object.  However, Kato's 2021
paper explicitly states that differential algebraicity for non-rational periods was unknown.  The
actual irrational elliptic-gamma hypertranscendence theorem, its exact spectrum, and its defect
matroid therefore require a separate novelty and significance verdict; collapse of the class is
not evidence against novelty of a theorem about the resulting function.  This card is retained to
prevent the false abstraction from being promoted, while the function theorem is split out.

## Boundaries

1. If `1,tau,sigma` are rationally dependent, `H` is discrete and the joint fixed field need not collapse to `C`.
2. If the distinguished quasi-elliptic increment has several pole classes, the spectrum is controlled by the stabilizer and orbit relations of its pole divisor; it need not equal `H`.
3. If its unique pole has zero residue, it is not a genuine simple pole and the orbit separator disappears.
4. Existence of a paired primitive is not asserted for arbitrary compatible increments. The theorem classifies every meromorphic solution when one exists and proves that there is at most one modulo constants.

## Lean formalization (2026-08-31)

`[FORMALIZED]` The 2026-07 note that formalization "would presently be theatre" is superseded: the
elliptic layer it called missing was built for the elliptic-gamma cards, and the abstract class is
now Lean-proved on top of it.  Unconditional, axiom-clean (`propext`, `Classical.choice`,
`Quot.sound`), wired into `GaloisForLFunctions.HTGeometry`.

| Card statement | Lean |
|---|---|
| one-pole rigidity core: entire, `1`-periodic, constant `tau`-increment implies constant | `PairedQuasiEllipticRigidity.const_of_periodic_of_constant_increment` |
| matching principal parts leave no poles | `PrincipalPartMatching.nonneg_order_sub_of_matching_principal_parts` |
| one-pole classification of an increment | `PrincipalPartMatching.const_sub_of_matching_principal_parts` |
| theta logarithmic derivative has principal part `1/(w-q)` at each divisor point | `PrincipalPartMatching.hasPrincipalPart_logDeriv_of_simple_zero`, `ThetaSourceOnePole.hasPrincipalPart_thetaSource` |
| `U_tau = lambda_tau + const`, and its quasiperiod is forced to be `-2 pi i` | `ThetaSourceOnePole.const_sub_thetaSource_of_matching_principal_parts`, `PairedQuasiEllipticCollapse.eq_thetaLogDerivMero_add_const_of_matching_principal_parts` |
| the same for the recentred second face | `TranslatedThetaOnePole.const_sub_translate_thetaSource_of_matching_principal_parts`, `..._add_const_of_matching_principal_parts` |
| the nondiscrete rank-three collapse `delta W` constant, then `W` constant | `MeroRankThreeIncrementCollapse.exists_complex_of_rankThree_constIncrements`, `..._of_unit_period_of_constIncrements` |
| germ/function transport | `MeroRealizationTransport.realizesMero_eq_of_eventuallyEq` |
| **collapse theorem**: every simple paired quasi-elliptic primitive is the elliptic-gamma logarithmic derivative up to an additive constant | `SimplePairedQuasiEllipticCollapse.exists_complex_sub_ellipticGammaLogDerivMero` |
| constraint uniqueness modulo a constant | `PairedQuasiEllipticCollapse.exists_complex_sub_of_same_increments` |
| its defect family is the elliptic-gamma defect family | `SimplePairedQuasiEllipticCollapse.defect_eq_ellipticGammaExternalLogDerivDefectMero`, `PairedQuasiEllipticSpectrum.defectFamily_eq_ellipticGammaExternalDefectFamily` |
| **spectrum and complete finite-shift matroid** | `PairedQuasiEllipticSpectrum.pairedQuasiEllipticPrimitive_differentialMatroid` |
| **exact subpacket rank law** | `PairedQuasiEllipticSpectrum.pairedQuasiEllipticPrimitive_eRk` |

The spectrum and matroid conclusions are obtained exactly as the paper obtains them: the collapse
identifies the primitive with the elliptic-gamma logarithmic derivative up to a constant, and an
additive constant is invisible to every translation defect, so the already-formalized
elliptic-gamma period-coset matroid and rank law hold verbatim.  Cross-curve pole alignment is the
corpus's `TripticOrbitResidueReciprocity.triptic_orbit_residue_reciprocity`.

Rank-three period rigidity is not assumed: `MeroFieldConstants.exists_complex_of_deriv_eq_zero` and
`MeromorphicTranslationFixedField.exists_constant_of_rankThree_translation_fixed` are corpus
theorems, and the increment collapse is derived from them.

## Gates

- [x] Exact theorem and constraint-defined class stated.
- [x] Paper proof written without numerical discovery.
- [x] Exact spectrum strengthened to the complete finite-shift matroid.
- [ ] Independent significance of the **abstract class**: failed because it equals translated
  scalar-affine elliptic-gamma logarithmic derivatives.  The actual special-function theorem has a
  separate significance pass.
- [x] Exact/equivalent/stronger preliminary literature search across primary adjacent sources.
- [x] Elliptic gamma recovered as a consequential corollary rather than used as the definition.
- [ ] Independent expert audit of the paired telescoping descent remains relevant to the elliptic-gamma theorem.
- [x] complete unconditional Lean formalization

## Log

- 2026-07-10 - Extracted from the elliptic-gamma calculation after the proof was found to use only paired noncommensurable quasi-elliptic constraints and a one-pole orbit separator.
- 2026-07-10 - Proved constraint uniqueness, exact rank-three DA spectrum, and the complete finite-shift differential-dependence matroid for the abstract class.
- 2026-07-10 - Demoted after the anti-rediscovery gate: the one-pole hypotheses force the increments to be translated scalar theta logarithmic derivatives and the primitive to be a translated scalar-affine elliptic-gamma logarithmic derivative. The apparent class was only a renaming.
- 2026-07-10 - Corrected the collapse statement to include a common argument translate. Cross-curve orbit-residue reciprocity aligns the two pole classes modulo `H`; the exact spectrum and anti-novelty verdict are unchanged.
- 2026-07-16 - Corrected the scope of the anti-novelty verdict.  Collapse demotes the proposed
  class, not the theorem resolving the irrational elliptic-gamma regime; that theorem was split to
  a candidate-new card after checking Kato's explicit open statement.
