# Modular cubic projection transgression law

- **ID:** ULF-MCPT-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Parents:** ULF-CCEL-001, ULF-FACHD-001, ULF-RUCRI-001
- **Status:** [PAPER-PROVED] [LEAN-PROVED] [NOT RH]
- **Lean:** formal/GaloisForLFunctions/HTGeometry/ModularCubicProjectionTransgression.lean

## 1. Big-picture meaning

The cubic formation defect contains more information than its ordinary trace. For three
projections, ordinary trace makes the cubic defect additive because it kills a nuclear
associator. A source modular weight is not ordinarily tracial. Its twisted cyclic law converts
that same associator into an exact modular-displacement term.

Thus source time can deform a completion extension without changing its ordinary Busby class:

~~~text
ordinary trace:  cubic associator -> 0,
source sigma-trace: cubic associator -> modular transgression.
~~~

This is neither another cubic operator nor another positive completion. It is a change in the
cyclic law used by the completion ideal. The relevant arithmetic candidate is therefore a
source-framed modular extension, not a new representative inside the old same-defect fibre.

## 2. Exact theorem

Let A be a ring, sigma:A->A a ring endomorphism, and tau:A->G an additive functional with

~~~text
tau(xy)=tau(sigma(y)x).                                  (MCPT.1)
~~~

For idempotents r,q,p, put

~~~text
a=r-q,  b=q-p,
C3(r,q,p)=(r-p)^3-(r-q)^3-(q-p)^3.                     (MCPT.2)
~~~

Projection algebra gives

~~~text
a^2 b + a b^2 = [ab,q].                                (MCPT.3)
~~~

Expanding the cube and retaining all noncommutative orderings yields

~~~text
C3(r,q,p)
 = 3[ab,q] + [ab,a] + [b,a^2] + [b,ab] + [b^2,a].     (MCPT.4)
~~~

Equation (MCPT.1) gives the exact twisted commutator law

~~~text
tau([x,y])=tau((sigma(y)-y)x).                          (MCPT.5)
~~~

Consequently

~~~text
tau(C3(r,q,p)) = tau(M3_sigma(r,q,p)),                  (MCPT.6)
~~~

where

~~~text
M3_sigma
 = 3(sigma(q)-q)ab
   +(sigma(a)-a)ab
   +(sigma(a^2)-a^2)b
   +(sigma(ab)-ab)b
   +(sigma(a)-a)b^2.                                   (MCPT.7)
~~~

If sigma fixes r,q,p, then M3_sigma=0. Ordinary trace is the special case sigma=id; it
necessarily erases the transgression.

## 3. Proof

Write r-p=a+b and expand (a+b)^3 without commuting factors. Subtracting a^3+b^3 leaves the six
mixed words. Subtract and add three copies of a^2b+ab^2; the four remaining differences are the
last four commutators in (MCPT.4). Idempotence of r,q,p proves (MCPT.3). Applying tau and
(MCPT.5) termwise proves (MCPT.6).

## 4. Exact two-block modular compression law

Let

~~~text
C=[[a,b],[c,d]],  delta=ad-bc != 0,  P=[[1,0],[0,0]],
sigma_C(X)=C^(-1)XC.
~~~

Direct block algebra gives

~~~text
P sigma_C(xP) P-xP = ((bc/delta)x)P.                  (MCPT.8)
~~~

Both displayed matrices for C and C^(-1) are proved to be mutual inverses. Hence (MCPT.8) is an
identity for a genuine inner modular automorphism, not a formal inverse notation. If bc=0, the
compression defect is exactly zero. Thus diagonal or block-separable source weights cannot
produce the extension deformation. Cross-sector source covariance is necessary.

The scalar bc/delta is not a proposed quadratic invariant. It is the exact obstruction to
compression naturality which feeds the cubic projection associator through (MCPT.6). The retained
class remains cubic in the three polarization increments.

## 5. Nontrivial closed witness

Over rational 2x2 matrices take

~~~text
p=[[1,0],[0,0]],
q=(1/2)[[1,1],[1,1]],
r=[[0,0],[0,1]],

rho=[[1/2,1/4],[1/4,1/4]],
rho^(-1)=[[4,-4],[-4,8]].
~~~

Let

~~~text
sigma(x)=rho^(-1)x rho,
tau(x)=Tr(rho x).
~~~

Then tau is a sigma-trace, Tr rho=3/4<1, and

~~~text
Tr C3(r,q,p)=0,
tau(C3(r,q,p))=tau(M3_sigma(r,q,p))=-1/8.              (MCPT.9)
~~~

Moreover

~~~text
p sigma(p) p-p=p.                                     (MCPT.10)
~~~

So a prime-mixed-type density can have strict sub-unit total mass while compression of its
projective modular action creates one rank-one unit. This does not prove an arithmetic unit
exists; it proves that the sub-unit budget and integral completion charge are not structurally
incompatible once modular compression, rather than ordinary trace continuity, carries the
defect.

## 6. Corpus consequence

ULF-FACHD-001 proves that the operator associator is nuclear and ordinary-traceless.
ULF-MCPT-001 identifies exactly what ordinary trace discarded: failure of the intermediate
polarization to lie in the source modular centralizer.

The arithmetic source already contains a candidate noncentral density:
commonRadialPrimeSourceSymbol is a literal prime-mixed positive trace-class covariance with trace
strictly below the primitive Euler budget. By contrast, the diagonal reflected prime-depth
incidence is a flat coboundary; all of its finite cyclic trace moments are horizontally blind.
Therefore any arithmetic specialization of (MCPT.6) must use the non-diagonal prime-mixed
covariance, not a diagonal prime-log weight.

## 7. What remains open

This card proves only the universal transgression law. It does not construct the theta completion
as a modular extension, prove modular compatibility of cofinal source compressions, or identify
the resulting boundary class with Xi escape multiplicity. Those are the arithmetic formation
gates of ULF-MCCED-001.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.ModularCubicProjectionTransgression`, `GaloisForLFunctions.HTGeometry.ModularCubicProjectionCrossIdentity`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.HTGeometry.ModularCubicProjectionTransgression` (50 constants) and
`GaloisForLFunctions.HTGeometry.ModularCubicProjectionCrossIdentity` (3 constants, added 2026-09-28); axiom audit clean.

| Claim | Lean declaration |
|-|-|
| (MCPT.1) σ-trace | `IsSigmaTrace` |
| (MCPT.2) `C₃(r,q,p)` | `cubicProjectionAssociatorAlgebra` |
| (MCPT.3) `a²b + ab² = [ab, q]` | `projection_cross_eq_modularCommutator` |
| (MCPT.4) five-commutator expansion | `cubicProjectionAssociatorAlgebra_eq_commutators` |
| (MCPT.5) twisted commutator law | `IsSigmaTrace.map_modularCommutator` |
| (MCPT.6)–(MCPT.7) `τ(C₃) = τ(M₃_σ)` | `cubicProjectionModularAnomaly`, `IsSigmaTrace.map_cubicProjectionAssociatorAlgebra` |
| σ fixing `r,q,p` ⇒ `M₃ = 0`; ordinary trace erases | `cubicProjectionModularAnomaly_eq_zero_of_fixed`, `cubicProjectionModularAnomaly_id`, `tracial_map_cubicProjectionAssociatorAlgebra_eq_zero` |
| §4 `C`, `C⁻¹` mutual inverses | `modularTwoBlockDensity_mul_inv`, `modularTwoBlockDensityInv_mul` |
| (MCPT.8) compression law; `bc = 0` ⇒ zero | `modularTwoBlockCompressionDefect`, `modularTwoBlockCompressionDefect_eq_zero_of_crossProduct_eq_zero` |
| §5 witness: idempotents, `ρ ρ⁻¹ = 1`, σ-trace, `Tr ρ = 3/4 < 1` | `modularCubicWitnessP_idempotent`, `_Q_`, `_R_`, `modularCubicWitnessDensity_mul_inv`, `modularCubicWitnessDensityInv_mul`, `modularCubicWitnessTrace_isSigmaTrace`, `trace_modularCubicWitnessDensity_eq`, `trace_modularCubicWitnessDensity_lt_one` |
| (MCPT.9) `Tr C₃ = 0`, `τ(C₃) = τ(M₃) = -1/8` | `trace_modularCubicWitness_associator_eq_zero`, `modularCubicWitnessTrace_associator_eq_neg_eighth`, `modularCubicWitnessTrace_anomaly_eq_neg_eighth` |
| (MCPT.10) `p σ(p) p - p = p` | `modularCubicWitness_compressionDefect_eq_projection` |
| closed conjunction | `modularCubicProjectionTransgression_closed` |

## Log

- 2026-09-28 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
