# Exact finite images and normal closure of marked Xi monodromy

- **ID:** RH-XIFM-20261007
- **Stage:** 3-formalized
- **Parent:** `../1-in-progress/xi-logarithmic-islands-monodromy.md`
- **Verdict:** actual-source classification; novelty uncertified; no RH conclusion

## Exact unconditional endpoints

For any finite real slope set A, put d_a(s)=xi(s)*exp(-a*s),
U_A={s : xi(s)!=0 and d_a(s)!=-1 for every a in A}, V=C minus {0,-1}.
Base U_A at0 and every target coordinate at1/2. Let Gamma_A be the product
of these target fundamental groups, mu_A the actual joint map, and w winding
about0. Set Delta_A={q : there exists k in Z with w(q_a)=k for every a}.

For every homomorphism f:Gamma_A->G to any finite group,

    f(image(mu_A)) = f(Delta_A).

No surjectivity assumption on f. Also, as an equality of discrete subgroups,

    normalClosure(image(mu_A)) = Delta_A.

The empty family is included. No RH, zero-location, regular-value,
inverse-disk or maximality premise remains. These results do not identify
image(mu_A) itself with Delta_A or construct a profinite completion.
C2-finite of the parent card is closed; the grandparent's abstract cubic
C2 is a different statement and is not closed here.

## Dependency-closed proof

Every coordinate winding equals the actual Xi source winding because an
exponential factor has winding zero. This gives the upper inclusion.
The audited packet theorem realizes every finite packet in one coordinate
kernel with all other coordinates nullhomotopic. One source connecting path
gives one conjugator for the whole packet. The finite normal-packet theorem
then puts the full product kernel into every finite image of actual joint
monodromy. See `xi-marked-finite-kernel-image.md`.

An unconditional actual simple critical-line Xi zero supplies a small
winding-one circle. Shrink it to avoid all auxiliary marked divisors. The
existing real-parameter Xi argument principle agrees with exponential-cover
degree: compose its continuous logarithm with affine interval parametrization
and subtract the initial value. Normalization of C* is a homeomorphism and
degree is bijective, so the local winding-one loop makes the actual map onto
pi1(C*). Naturality of path transport carries surjectivity to source0.

For q in Delta_A, choose an actual image u with the same common winding.
Then q*u^(-1) is in the product kernel, proving the finite-image equality.
For normal closure, singleton packets suffice: any normal subgroup containing
the actual image contains the unconjugated coordinate kernels. Their product
and the primitive diagonal element fill Delta_A. Conversely Delta_A is normal
and contains the image.

## Prior work and scope

The parent records corpus and primary-literature audits of classical winding,
transport, univalence and finite-group inputs. Generic inverse monodromy and
global class-B logarithmic tracts do not supply this actual joint theorem.
No exact antecedent appeared among inspected hits; this limited search is
not a novelty certificate. The classification supplies no source-derived
zero-location selection law.

## Final formal audit

- `HTGeometry/PuncturedWindingBaseChange.lean`: six public declarations.
- `RHTower/WindingNumberDegreeBridge.lean`: one public theorem.
- `RHTower/XiMarkedMeridian.lean`: two public theorems.
- `RHTower/XiMarkedFiniteMonodromy.lean`: three public declarations.
- `RHTower/XiMarkedNormalClosure.lean`: three public declarations.

All targeted builds and all five final actual-source `lake env lean` checks
pass. All15 public axiom closures use only propext, Classical.choice,
Quot.sound. Each leaf is imported once; no admissions or heartbeat changes.
Matching proof scratches removed after final checks. Earlier dependencies
have separate completed packet and kernel audit cards.

Evidence: `/tmp/rh-PuncturedWindingBaseChange-build.log`,
`/tmp/rh-marked-meridian-deps-build.log`, `/tmp/rh-XiMarkedMeridian-build.log`,
`/tmp/rh-XiMarkedFiniteMonodromy-build.log`, `/tmp/rh-XiMarkedNormalClosure-build.log`,
`/tmp/rh-final-<leaf>.log`, `/tmp/rh-marked-finite-axioms.log`.

Index refreshed. Global lint fails on seven unrelated unreachable modules:
RHTower.WeilConeZetaCarrierBoundary, RHTower.WeilConeZetaCarrierResonance;
HTGeometry.ApertureConeCalculus, ApertureConeWinding, ApertureLogTranslation,
ApertureOpenHistoryIdeal, BoundaryCoronaCStarAlgebra. No own-leaf lint error;
global gate is not clean. Logs: `/tmp/rh-marked-finite-index.log`,
`/tmp/rh-marked-finite-lint.log`.
