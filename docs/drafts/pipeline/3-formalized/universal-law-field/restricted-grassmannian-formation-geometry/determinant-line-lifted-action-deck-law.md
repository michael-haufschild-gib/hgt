# Determinant-line lifted-action deck law

- **ID:** ULF-DLLA-001
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Source:** `ULF-BGCA-001` · `ULF-BGAF-001`
- **Statement:** Determinant-line holonomy observes graph-cap action only modulo integers; two
  fillings of one boundary differ by an integral Schubert deck translation, and positive bubbling
  subtracts that integer from the residual lifted action.

## Provenance

- `[LITERATURE]` Chern--Weil, Stokes, determinant-line curvature, and integrality of the first
  Chern class.
- `[CORPUS]` `berryHolonomy_does_not_determine_windingAction` proves that identical Berry holonomy
  can hide different integral winding action.
- `[CORPUS]` `closed_observation_open_lift` proves a closed determinant loop can have a nonzero
  logarithmic lift increment equal to its winding integral.
- `[CORPUS]` `nomogenicPeriodicProducer_phaseQuotient_recurrence_openPrefix` proves one source
  history can close after phase quotient while retaining nonzero carry and open lifted history.
- `[CORPUS]` `xiShiftedStrictFrontier_integerHolonomyLaw` gives every occupied strict frontier an
  integer holonomy coordinate.
- `[PROVED HERE]` Exact specialization of this quotient/lift separation to the determinant line of
  the Burnol restricted-Grassmannian cap.

## 1. Holonomy of one graph cap

Let `L_det -> Gr_res,2` be the determinant line with unitary Chern connection `nabla_det`, normalized
by

```text
F_(nabla_det) = -2*pi*i*omega_det,
[omega_det] = c1(L_det).                              (DLLA.1)
```

For a Hilbert--Schmidt `A`, let `Gamma_A(z)=graph(zA)` and let

```text
E(A)=integral_D Gamma_A^* omega_det
    =Tr(K(I+K)^(-1)),  K=A* A.                        (DLLA.2)
```

**Theorem DLLA-A.** With positive boundary orientation,

```text
Hol_(nabla_det)(boundary Gamma_A)
  = exp(2*pi*i*E(A)).                                 (DLLA.3)
```

If `0<=E(A)<1`, then `E(A)` is the unique lift of this holonomy in `[0,1)`.

**Proof.** The determinant line is trivial over the graph cell, so choose its unitary frame on the
cap.  Stokes and `(DLLA.1)` give

```text
Hol(boundary Gamma_A)
  = exp(-integral_D Gamma_A^* F_(nabla_det))
  = exp(2*pi*i*integral_D Gamma_A^* omega_det).
```

Insert `(DLLA.2)`.  The exponential map `x -> exp(2*pi*i*x)` is injective on `[0,1)`, proving
uniqueness of the stated lift.  QED.

For `A=A_base`, `ULF-BGCA-001` proves `0<=E_base<1`.  Literal Euler formation therefore supplies
not only a determinant phase but its canonical principal real lift.

## 2. Relative filling and deck integer

Let `F_0:S_0->Gr_res,2` and `F_1:S_1->Gr_res,2` be oriented fillings with the same framed boundary
loop.  Glue `S_0` to `-S_1` along that frame and write `S=F_0 union (-F_1)` for the resulting closed
stable surface.

**Theorem DLLA-B.** Their lifted actions obey

```text
q(F_0,F_1)
  := integral_(S_0) F_0^*omega_det
     - integral_(S_1) F_1^*omega_det
   = <c1(L_det),[S]>
   in Int.                                             (DLLA.4)
```

Consequently both fillings have the same determinant holonomy and differ by the deck translation
`q`.  If `F_0` degenerates to a residual filling `F_1` plus positive holomorphic Schubert bubbles
of degrees `m_j`, then

```text
q(F_0,F_1)=sum_j m_j >= 0,
E(F_0)=E(F_1)+sum_j m_j.                              (DLLA.5)
```

**Proof.** Gluing and orientation give the first equality in `(DLLA.4)`.  Equation `(DLLA.1)`
identifies the closed integral with the first Chern number, hence an integer.  Exponentiating
annihilates this integer, so the boundary holonomies agree.  For a stable holomorphic
degeneration, additivity of the current and positivity of intersection with the determinant
Schubert divisor give one nonnegative integer `m_j` per bubble, proving `(DLLA.5)`.  QED.

## 3. The object `mathsf T` as a deck representative

`[INTERPRETATION]` The cubic defect

```text
mathsf T_D=(U_D* P U_D-P)^3
```

is the nuclear operator representative of the deck translation, not of determinant holonomy
itself.  Its trace is already the integral boundary winding.  The exact arithmetic sewing sought
in `ULF-TSBC-001` is the identification

```text
Tr mathsf T_D = q(Euler filling, theta residual filling). (DLLA.6)
```

This equation is **not** proved here.  DLLA-B proves that the right side is an integer once the two
coefficient-native fillings with common framed boundary are constructed.  `ULF-RUCRI-001` proves
that the left side is an integer.  TSBC must prove they are the same integer without using a Xi
divisor to build either filling.

If `(DLLA.6)` and positivity hold, then

```text
E_base=E_residual+Tr mathsf T_D,
0<=E_base<1,
E_residual>=0,
```

so `Tr mathsf T_D=0` and RH follows.

## 4. What this explains

The observer sees

```text
exp(2*pi*i*E),
```

while formation history lives in its real lift `E`.  Adding one bubble changes the lift by one
and leaves the observer exactly unchanged.  Therefore:

```text
positivity/phase quotient = observation modulo integral action,
closed recurrence         = return of determinant holonomy,
open lifted history       = nonzero Schubert deck translation,
cubic trace               = integral carry retained upstairs.
```

This is why phase, functional-equation, recurrence, and ordinary holonomy laws can all be exact
yet fail to select RH.  They live after quotienting by the integer that `mathsf T_D` records.

## 5. No-go and surviving requirement

The theorem kills any claim that common determinant holonomy alone transports the source budget:
holonomy is deliberately blind to `q`.  A successful theta correspondence must choose the
principal lift by a filtration/energy law, not by phase equality.

It must also preserve a framed determinant line.  Unframed boundary identification can change the
integer by a gauge winding and make `(DLLA.6)` tautological.

## 6. Audit status

- Paper dependencies: closed.
- Lean status: formalized unconditionally (Theorem DLLA-A for every Hilbert–Schmidt `A : E → F`,
  Theorem DLLA-B, (DLLA.5), the literal Burnol cap); see the Lean certificate.
- RH status: no claim.
- Exact open edge: coefficient-native common framing plus proof that the positive deck integer is
  `Tr mathsf T_D` and is paid from the Burnol action filtration.


## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.HTGeometry.DeterminantLineGraphCapHilbertSum`, `GaloisForLFunctions.HTGeometry.DeterminantLineFillingHolonomy`, `GaloisForLFunctions.HTGeometry.DeterminantLineBubblingDeckLaw`, `GaloisForLFunctions.HTGeometry.DeterminantLineUnitaryConnection`, `GaloisForLFunctions.RHTower.BurnolBaseCapPrincipalLift`, `GaloisForLFunctions.HTGeometry.HilbertSchmidtTraceIdeal`, `GaloisForLFunctions.HTGeometry.HilbertSchmidtCalculus`, `GaloisForLFunctions.HTGeometry.FiniteRankDeterminant`, `GaloisForLFunctions.HTGeometry.RestrictedGrassmannianKahlerForm`, `GaloisForLFunctions.HTGeometry.DeterminantLineConnection`, `GaloisForLFunctions.HTGeometry.AdmissibleFrameLifts`, `GaloisForLFunctions.HTGeometry.DeterminantLineGauge`, `GaloisForLFunctions.HTGeometry.DeterminantLineSquareStokes`, `GaloisForLFunctions.HTGeometry.DeterminantLineEdgeHolonomy`, `GaloisForLFunctions.HTGeometry.DeterminantLineSquareHolonomy`, `GaloisForLFunctions.HTGeometry.DeterminantLineChainIntegrality`, `GaloisForLFunctions.HTGeometry.DeterminantLineGraphCapHolonomy`, `GaloisForLFunctions.HTGeometry.DeterminantLineHolomorphicBubbles`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Card modules `GaloisForLFunctions.HTGeometry.DeterminantLineGraphCapHilbertSum` (Theorem DLLA-A),
`GaloisForLFunctions.HTGeometry.DeterminantLineFillingHolonomy` (Theorem DLLA-B),
`GaloisForLFunctions.HTGeometry.DeterminantLineBubblingDeckLaw` (DLLA.5),
`GaloisForLFunctions.HTGeometry.DeterminantLineUnitaryConnection` (DLLA.1) and
`GaloisForLFunctions.RHTower.BurnolBaseCapPrincipalLift` (the literal Burnol cap), built on the new
determinant-line infrastructure: `GaloisForLFunctions.HTGeometry.HilbertSchmidtTraceIdeal`,
`GaloisForLFunctions.HTGeometry.HilbertSchmidtCalculus`,
`GaloisForLFunctions.HTGeometry.FiniteRankDeterminant`,
`GaloisForLFunctions.HTGeometry.RestrictedGrassmannianKahlerForm`,
`GaloisForLFunctions.HTGeometry.DeterminantLineConnection`,
`GaloisForLFunctions.HTGeometry.AdmissibleFrameLifts`,
`GaloisForLFunctions.HTGeometry.DeterminantLineGauge`,
`GaloisForLFunctions.HTGeometry.DeterminantLineSquareStokes`,
`GaloisForLFunctions.HTGeometry.DeterminantLineEdgeHolonomy`,
`GaloisForLFunctions.HTGeometry.DeterminantLineSquareHolonomy`,
`GaloisForLFunctions.HTGeometry.DeterminantLineChainIntegrality`,
`GaloisForLFunctions.HTGeometry.DeterminantLineGraphCapHolonomy`,
`GaloisForLFunctions.HTGeometry.DeterminantLineHolomorphicBubbles`.
Model: `Gr_res(P₊)` is the set of orthogonal projections `P` with `P − P₊` Hilbert–Schmidt;
surfaces are smooth cubical chains (squares `ℝ² → SLSpace`, projection valued); frames are
`w = Q + Y`, admissible when the `ran Q`-part of `Y` has finite rank; `L_det` is trivialized by
finite-rank determinants of frame gauges; `α(w)[Ẏ] = Tr(Ĝ⁻¹w†Ẏ)`; `ω_det(X, Y) =
Im Tr(P[X, Y])/2π`; the holonomy of a path is computed from uniformly subdivided lifts and is
lift independent.  All names below are in namespace `GaloisForLFunctions.HTGeometry` except
`burnolBaseCap_principal_lift`, `burnolBaseCapChain`, `kahlerIntegral_burnolBaseCapChain` and
`burnolBaseCap_no_bubbling` (namespace `RHTower`).

| Claim | Lean declaration |
|-|-|
| `Gr_res`, `ω_det`, `Tr(P[X, Y]) = 2πi ω_det(X, Y)`, `ω_det` real and antisymmetric | `restrictedGrassmannian`, `detKahlerForm`, `detCurvature_eq_two_pi_I_mul`, `detKahlerForm_antisymm` |
| trace on HS products, finite-rank determinant, Jacobi formula | `hsTraceIdeal`, `opTrace_mul_comm_of_mem`, `finiteRankDet`, `finiteRankDet_mul`, `hasDerivAt_finiteRankDet` |
| admissible frames, clopen sectors (index zero), smooth local lifts | `IsAdmissibleFrame`, `exists_admissibleFrame_of_isPreconnected`, `liftY_isFrameOf`, `exists_local_lift` |
| (DLLA.1) connection form, gauge law, curvature `dα = Tr(P dP∧dP) = 2πi ω_det` | `detConnection`, `detConnection_gauge`, `detConnection_curvature`, `liftConn_divergence`, `squareCurvature_eq` |
| (DLLA.1) unitary Chern connection: `2 Re α = Tr(Ĝ⁻¹Ĝ̇)`, `α` complex linear, `|Hol| = 1` | `two_re_detConnection`, `detConnection_smul`, `norm_edgeHol_of_fills` |
| holonomy of paths and squares; Stokes on rectangles | `edgeHol`, `edgeHol_eq`, `integral_squareCurvature_eq`, `rect_holonomy`, `square_holonomy` |
| (DLLA.1) `[ω_det] = c₁(L_det)`: integral on cycles, closed on cubes | `GrChain.kahlerIntegral_mem_int`, `GrCube.bdry_bdryChain_eq_zero`, `GrCube.kahlerIntegral_bdryChain` |
| holonomy–curvature for fillings `Hol(γ) = exp(2πi ∫_c ω_det)` | `GrChain.Fills`, `edgeHol_eq_exp_kahlerIntegral` |
| (DLLA.2) `E(A) = ∫_D Γ_A^*ω_det = Tr(K(I + K)⁻¹)` | `integral_graphCapKahler`, `integral_capKahler`, `graphCapArea_graphBlockOp`, `graphCapArea_eq` |
| Theorem DLLA-A (DLLA.3): `Hol(∂Γ_A) = exp(2πi E(A))` | `graphCapBoundary`, `edgeHol_graphCapBoundary`, `edgeHol_capBoundary` |
| Theorem DLLA-A: `0 ≤ E(A) < 1` ⇒ unique lift in `[0, 1)` | `graphCapBoundary_unique_lift`, `capBoundary_unique_lift` |
| `A_base`: `0 ≤ E_base < 1`, canonical principal lift | `burnolBaseCap_principal_lift` |
| Theorem DLLA-B (DLLA.4): `q = ∫_{c₀}ω − ∫_{c₁}ω = ⟨c₁(L_det), c₀ − c₁⟩ ∈ ℤ` | `GrChain.add`, `GrChain.neg`, `GrChain.bdry_add`, `GrChain.bdry_neg`, `GrChain.deck_integer` |
| Theorem DLLA-B: both fillings have the boundary holonomy | `GrChain.fillings_same_holonomy` |
| holomorphic bubbles: `ω_det = Im(conj ∂ₛφ ∂ₜφ)‖(1−P)∂P P‖²/π ≥ 0`, sphere cycles, degree `m ∈ ℕ` | `detKahlerForm_tangent`, `HolChart.squareKahler_comp`, `HolChart.integral_north_nonneg`, `HolChart.integral_south_nonpos`, `HolSphere.isCycle`, `HolSphere.exists_degree_eq_nat` |
| (DLLA.5): `c₀ ≡ c₁ + Σ B_j + ∂R` ⇒ `q = Σ m_j ≥ 0`, `E(F₀) = E(F₁) + Σ m_j` | `GrChain.kahlerIntegral_eq_of_mult`, `GrChain.bubbling_deck_law` |

| §3 (positivity part): the Burnol cap cannot shed a positive bubble onto a residual of nonnegative area | `burnolBaseCapChain`, `kahlerIntegral_burnolBaseCapChain`, `burnolBaseCap_no_bubbling` |

§3 is interpretation: (DLLA.6) is explicitly not proved by the card; its two consequences recorded
there are the integrality of the right side (Theorem DLLA-B) and positivity (DLLA.5), and the
arithmetic step `E_base = E_res + n`, `0 ≤ E_res`, `E_base < 1` ⇒ `n = 0` is
`burnolBaseCap_no_bubbling`.  §4–§6 are commentary.

## Log

- 2026-09-03 — `[PROVED HERE]` graph-cap holonomy formula and relative integral deck law.
- 2026-10-06 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
