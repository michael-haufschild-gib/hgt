# Mass-shifted vacuum-free hard-edge source capacity

- **ID:** `mass-shifted-vacuum-free-hard-edge-source-capacity`
- **Stage:** 3-formalized / needs specialist novelty audit
- **Type:** arithmetic source producer / exact capacity and worldline conservation
- **Scientific status:** `[PAPER-PROVED] [LEAN-PROVED] [NOVELTY UNVERIFIED] [NOT RH]`
- **Depends on:** `mass-shifted-vacuum-free-nondegenerate-source-action`,
  `mass-shifted-adaptive-source-transverse-pade-capacity-law`, and
  `mass-shifted-hard-edge-worldline-source-conservation`

## Result

Let `A=P_n(y)` and `B=P_(n+1)(y)` be actual current and adjacent inverse-Hankel admissions. Let
`Q_n°(A,B)` be the unit-renormalized nondegenerate source polynomial already proved to satisfy

```text
2 L_y(Q_n°(A,B)) = S_n°(y),
2 N_n R_n² <= K_n S_n°.
```

Form its hard-edge producer before arithmetic aggregation:

```text
T_n°(U) = Clear(y,2n+2,2 Q_n°(A,B)).
```

Put `S(U)=Clear(y,n,A)`. Lean proves the exact source-polynomial factorization

```text
T_n° = AdaptiveMixedHardEdge(A) + S² Clear(y,2,C_n(A,B)),
```

where the explicit quadratic correction is

```text
C_n(A,B) = -2(n+1) X² + 2(1+A.nextCoeff) X
  + 4 A.nextCoeff²
  + 2((A.nextCoeff-B.nextCoeff)²-(A.nextCoeff-B.nextCoeff)).
```

Thus adjacent admission, chamber completion, and vacuum removal all occur inside source formation,
but every new channel has double current-root vanishing. At every nonzero current admitted root
`x`, with hard coordinate `u=x⁻¹-y`, one has

```text
T_n°(u)=0,
(T_n°)'(u)=-2*x⁻¹*S'(u)².
```

Define source-native transverse capacity

```text
C_n°(y,x)=-(x/2)(T_n°)'(x⁻¹-y).
```

Then

```text
C_n°(y,x)=S'(x⁻¹-y)²>=0.
```

It is exactly the diagonal adaptive capacity, but this equality is a theorem derived after the
two-amplitude source is formed. It is not a replacement by a diagonal reporter.

For actual Gauss weight `lambda`, Padé residue `rho=lambda/x`, and finite hard terminal mass

```text
Gamma=y*x⁴*lambda*P_n'(x)²,
C_eff°=y*x^(2n+1) C_n°,
```

the literal vacuum-free source obeys

```text
rho*C_eff°=Gamma.
```

Along any differentiable current root worldline in a positive chamber,

```text
u'(y)*rho*C_eff°=2*n*y*x²*N_n.
```

At `y=w²`, the parabolic law is

```text
(du/dw)*rho*C_eff°=4*n*w³*x²*N_n.
```

One source therefore has two exact faces:

1. its scalar completed rational--Gamma/von-Mangoldt aggregate pays logarithmic admission
   effectivity in the positive chamber;
2. its first hard-root jet preserves absolute Padé visibility and worldline forcing without any
   degree-decaying reporter.

Under compact hard-edge scaling, if normalized cleared derivative tends to `d`, then
`C_eff° -> d²`. At a simple limiting root, `d != 0`, so completion, vacuum subtraction, and moving
degree cannot cause capacity collapse or blow-up.

## Conjecture -> proof/failure -> pivot loop

1. **C1 — nondegenerate completion may destroy hard-root capacity. `[FALSIFIED]`** Exact
   factorization shows every extra channel is divisible by `S²`; its value and first derivative
   vanish at every current hard root.
2. **C2 — unit-vacuum subtraction may alter the transverse residue normalization. `[FALSIFIED]`**
   Vacuum subtraction changes only the same `S²` correction and leaves capacity exactly `S'²`.
3. **C3 — adjacent amplitude must be discarded to recover a root law. `[FALSIFIED]`** Adjacent
   amplitude enters before completed aggregation. Its disappearance from first jet is proved from
   double-root divisibility, not imposed by diagonalization.
4. **C4 — capacity identity is merely a fixed reporter. `[FALSIFIED]`** Producer polynomial,
   clearing depth, current root, adjacent amplitude, and normalization all move with admission.
   Exact reciprocal chart pullback recovers literal completed arithmetic source.
5. **C5 — capacity law alone proves RH. `[FALSIFIED]`** It eliminates source-capacity escape but
   permits terminal divided-root mass `Gamma` to vanish. In that branch Padé residue can still
   vanish despite nonzero capacity.
6. **C6 — flat contact may erase production because hard-root motion freezes. `[FALSIFIED]`** At a
   simple flat hard root, Lean proves `u'(y)=0` and `C_n°(y,x)>0` simultaneously. Carrier motion and
   source production are different jets; the obstruction moves to terminal mass/contact order.
7. **Positive survivor. `[PROVED]`** Missing arithmetic source law is a nonlinear two-face
   conservation law, not a degree-weighted sum: chamber effectivity and hard-root Padé capacity are
   two jets of one source-first current/adjacent `P^sharp` formation.

## Higher universal principle

Earlier fixed-degree action and hard-edge capacity looked unrelated because one divides by
admission norm and the other differentiates at an admitted zero. They are scalar and transverse
jets of the same source polynomial:

```text
source value / current norm  -> admission motion,
source derivative at hard root -> pole visibility.
```

Completion terms divisible by amplitude square can change scalar chamber coercivity while being
universally invisible to first transverse root jet. This is a source-jet filtration principle:
zeroth source jet pays bulk/effectivity; first nonvanishing root jet pays hard visibility. Fixed
linear reporting loses this filtration.

## Honest remaining burden

RH is not proved. The law closes completion/vacuum/capacity escape. Exact remaining branches are:

1. positive terminal mass: derive positive-axis extinction/local boundedness for canonical Padé
   resolvents from the literal source;
2. zero terminal mass: use parity-doubled hard-edge radical/contact-order source, rather than
   asserting a false capacity floor.

Worldline conservation controls `Gamma/N_n` inside positive chamber, not absolute `Gamma` at flat
face. No scale division is hidden here.

## Novelty audit

Corpus search found diagonal adaptive source capacity, worldline conservation, and vacuum-free
chamber effectivity separately, but no theorem showing that literal adjacent-amplitude vacuum-free
source has identical hard-root jet and simultaneously satisfies both conservation faces. Current
primary literature search found general lower-bounded convolution-ground real-zero localization
and Weil/screw-function operator frameworks, but no shifted-Xi reciprocal-Hankel current/adjacent
source-polynomial factorization or Padé-residue law in this form. No priority claim is made without
specialist audit.

## Lean certificate

Module:

```text
GaloisForLFunctions.RHTower.XiShiftedCanonicalAdmissionVacuumFreeHardEdgeSourceCapacity
```

Principal declarations:

```text
two_smul_unitRenormalizedNondegenerateShear_eq_adaptiveBilinear_add_sq_mul_correction
xiShiftedUnitRenormalizedNondegenerateHardEdgeSource_eq_adaptive_add_sq_mul_correction
derivative_xiShiftedUnitRenormalizedNondegenerateHardEdgeSource_eval_centeredReciprocal
xiShiftedUnitRenormalizedNondegenerateHardEdgeSourceTransverseCapacity_eq_sq
xiShiftedUnitRenormalizedNondegenerateNullFlagCompletedArithmeticSource_canonicalAdmission_eq_hardEdgeLanding
xiShiftedCanonicalAdmissionHardEdgeGaussPadeResidue_mul_unitRenormalizedNondegenerateEffectiveSourceCapacity_eq_terminalMass
xiShiftedCanonicalAdmissionHardEdgeWorldline_mul_residue_mul_unitRenormalizedNondegenerateSourceCapacity_eq_normSq
xiShiftedCanonicalAdmissionParabolicHardEdgeWorldline_mul_residue_mul_unitRenormalizedNondegenerateSourceCapacity_eq_normSq
literal_unitRenormalizedNondegenerateSource_pays_effectivity_and_hardRootCapacity
xiShiftedCanonicalAdmission_flatHardRoot_freezes_but_unitRenormalizedSourceCapacity_pos
tendsto_xiShiftedCanonicalAdmissionUnitRenormalizedNondegenerateHardEdgeEffectiveSourceCapacity
```

Direct `lake env lean` check passed. Module is wired into `RHTower.lean`. Targeted module build
passed (`11825/11825`). Forbidden-token scan found no `sorry`, `admit`, `axiom`, `opaque`, or
`unsafe`. `#print axioms` on eight capstones reports only `propext`, `Classical.choice`, and
`Quot.sound`.

Repository-wide `scripts/formal_tools.py lint` still exits nonzero solely because 37 concurrently
added modules are not yet reachable from `RHTower.lean`; none is this module. Large-file notices are
warnings. This producer itself is umbrella-reachable, directly elaborated, and target-built.
