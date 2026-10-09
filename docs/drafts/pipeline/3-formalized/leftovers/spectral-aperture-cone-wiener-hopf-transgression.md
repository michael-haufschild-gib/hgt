# Spectral-aperture cone and Wiener--Hopf transgression

- **ID:** `ULF-SACWHT-001`
- **Stage:** `3-formalized`
- **Type:** unconditional pre-divisor topology/index fusion and direct-subunit no-go
- **Parents:** `ULF-POINH-001`, `ULF-INBSG-001`, `ULF-PBTIA-001`, `SoninLogShellCocycle`
- **Status:** `[PAPER-PROVED] [DEPENDENCY-CLOSED] [LEAN PROVED] [NOT RH]`
- **Lean status:** every claim formalized unconditionally (standard axioms only); certificate
  tables in "Lean progress" below

## What this changes

The positive boundary-transfer germs are not merely points in an unspecified corona.  They form
one canonical **cone extension**.  Closing the observer evaluates its endpoint.  The kernel is the
open scale-history suspension, and its winding is the boundary transgression of the closed unit.
After adjoining log-aperture translations, this becomes the one-dimensional Wiener--Hopf
extension.

This gives exact meanings to four corpus phrases:

```text
positivity quotient       = contractible cone algebra;
open lifted history       = suspension ideal;
closed observer           = endpoint quotient;
integral homotopy charge  = connecting-map winding / Wiener--Hopf index.
```

It also proves an important no-go.  Every multiplicative polarization is only another lift of
the **same** endpoint unit, so its primary integer is always one.  The sub-unit distance between
two lifts cannot bound that integer.  A viable RH mechanism must make prime formation twist the
extension class or quotient symbol; changing the positive lift inside one fixed cone cannot work.

## Corpus audit before theorem

`scripts/formal_tools.py research` was run for boundary-transfer scale germs, compact/open
descent, crossed products, log translations, shell cocycles, K-zero, and the direct-subunit
anchor.  Relevant exact inputs are:

- `positiveBoundaryTransfer`: `E_eps(cT)=cT(eps+cT)^(-1)`;
- `ULF-INBSG-001`: exact corona distance of two scale lifts;
- `ULF-PBTIA-001`: all scale information is in the open completion/observer interchange anomaly;
- `logTranslation_cutoffCocycle_eq_shell`: a log translation sweeps exactly one interval across
  the half-line boundary;
- `soninPhysicalLogShellWeight_eq_log`: its semifinite weight is `log p`;
- `soninPrimePowerLogShellTraceDensity_eq_fluxCoefficient`: pairing with the literal logarithmic
  Euler coefficient recovers the unsquared von Mangoldt coefficient;
- `logCrossedProductPairTrace_comm`: the degree-zero coefficient integral is cyclic on the
  algebraic log-translation crossed product;
- `DirectSubunitEscapeCapacityFusion`: strict-right escape multiplicity is one and the literal
  primitive source budget is below one escape quantum;
- `IntegralNuclearRelationIncidenceHorizon`: a supplied strict-right horizon projection has trace
  and trace norm one;
- `CCMRoutePCompletedCubicGreenIntegralDefectNoGo`: scaling an existing integral defect by a
  sub-unit scalar scales its trace too, so it is no longer the integral class.

The corpus contains algebraic crossed products and the Sonin shell cocycle, but the search found
no theorem identifying the positive boundary-transfer orbit with the cone extension below.

## 1. Boundary-transfer cone

Let `H` be infinite dimensional and let `T` be positive, compact, and injective.  In

```text
B = C_b((0,1], K(H)),    I = C_0((0,1], K(H)),    Q=B/I
```

put

```text
e_c = [eps |-> cT(eps+cT)^(-1)] in Q,    c>0.                 (SAC.1)
```

For `r>0` define the increasing fractional-linear map

```text
phi_r(t)=r t/(1+(r-1)t),    0<=t<=1.                          (SAC.2)
```

**Theorem SAC-A (one-generator law).** For all `c,d>0`,

```text
e_d = phi_(d/c)(e_c).                                        (SAC.3)
```

Every `e_c` has spectrum `[0,1]` in the unitization of `Q`.  Consequently

```text
C*(e_c : c>0) = C*(e_1) ~= C_0((0,1]).                       (SAC.4)
```

**Proof.** On a spectral value `lambda>0`, if

```text
x=c lambda/(eps+c lambda),
```

then direct substitution gives

```text
d lambda/(eps+d lambda)=phi_(d/c)(x),
```

proving `(SAC.3)` by functional calculus.  Positivity gives
`spectrum(e_c) subset [0,1]`.  Let `lambda_n -> 0` be positive eigenvalues of `T`.  For any
`x in (0,1)`, choose

```text
eps_n=c lambda_n(1-x)/x -> 0.
```

The `lambda_n` vector then reads `e_c(eps_n)` as exactly `x`.  An ultralimit of these vector
states annihilates `I`, hence descends to a state of `Q` taking `e_c` to `x`.  Thus every interior
point belongs to the spectrum; closedness adds `0,1`.  Continuous functional calculus proves
`(SAC.4)`, and `(SAC.3)` shows every scale generates the same algebra. QED.

This result is spectrum-independent.  Arithmetic enters by choosing the physical prime-mixed
`T` of `ULF-POINH-001`; no divisor enters.

## 2. Open-history ideal and exact integer

Let

```text
J_T=C*(e_c-e_d : c,d>0).                                    (SAC.5)
```

Under `(SAC.4)`, every difference vanishes at both endpoints.  Conversely the family separates
all points of `(0,1)` and has no common zero there.  Indeed, if all
`phi_c(t)-t` agree at `t,u`, sending `c -> infinity` gives `1-t=1-u`; strictness then gives
`t=u`.  The nonunital Stone--Weierstrass theorem therefore yields

```text
J_T ~= C_0((0,1)) ~= C_0(R).                                (SAC.6)
```

The strong closed observer is the endpoint map at `1`, giving the exact sequence

```text
0 -> J_T -> C*(e_1) -> C -> 0.                              (SAC.7)
```

The middle algebra is a cone and hence contractible.  Its six-term K-theory sequence makes the
connecting map

```text
delta : K_0(C)=Z -> K_1(J_T)=Z                              (SAC.8)
```

an isomorphism.  The endpoint unit lifts to the positive contraction `e_1`; the exponential
formula represents its boundary by

```text
u(t)=exp(2 pi i t),    t in (0,1),                           (SAC.9)
```

which winds once.  Thus `delta([1])=1`, with sign fixed by increasing aperture coordinate.

This is the integral charge already seen as theta first-exit/Fredholm index, now derived from the
completion topology itself.  It is created neither by a zero nor by positivity: positivity gives
the contractible middle cone, while the integer is the failure of its endpoint unit to close
inside the open-history ideal.

## 3. Polarization invariance and direct-subunit no-go

Every `e_c` satisfies `phi_c(1)=1`, so every scale is a lift of the same endpoint projection.
Its exponential boundary has winding one:

```text
delta_c([1])=[exp(2 pi i phi_c(t))]=1.                       (SAC.10)
```

Meanwhile `ULF-INBSG-001` gives

```text
||e_c-e_d||=|sqrt(c)-sqrt(d)|/(sqrt(c)+sqrt(d)) < 1.         (SAC.11)
```

There is no contradiction: `(SAC.10)` is a boundary class of either lift, whereas `(SAC.11)` is
the norm of their difference inside the suspension ideal.  The relative exponential

```text
exp(2 pi i (e_c-e_d))                                       (SAC.12)
```

is null-homotopic by multiplying its self-adjoint exponent by `r in [0,1]`.  Hence it has K-one
class zero for every `c,d`.

**Corollary SAC-B.** No continuous functional calculus of the positive scale orbit, no primary
cone boundary class, and no norm bound on `e_c-e_d` can produce an integer which is zero at
`c=d` and nonzero at `c!=d`.  The universal endpoint index is scale-blind; the relative scale
class is topologically trivial.

This kills the tempting direct-subunit argument

```text
universal index 1 <= ||e_c-e_(1/c)|| < 1.
```

The two quantities do not pair to the same class.

## 4. Adjoining history: Wiener--Hopf completion

Write `t=sigma(x)=e^x/(1+e^x)`.  Multiplicative scale becomes translation:

```text
phi_c(sigma(x))=sigma(x+log c).                              (SAC.13)
```

Translation acts on `(SAC.7)`, fixes the closed endpoint, and acts freely on the open ideal.
Crossing by `R` gives the one-dimensional Wiener--Hopf extension.  Its ideal is

```text
C_0(R) cross R ~= K(L^2(R)),                                (SAC.14)
```

by the Stone--von Neumann imprimitivity theorem, and its connecting map is the analytic
Wiener--Hopf index.  Thus the cone winding, theta first exit, and open-translation Fredholm index
are three presentations of one transgression.

The physical `T` gives a faithful source representation of the coefficient algebra.  For
`f in C_0(R)` define

```text
iota_T(f)=[eps |-> f(log T-log eps)].                        (SAC.15)
```

The same eigenvalue/aperture matching used in Theorem SAC-A proves
`||iota_T(f)||=||f||_infinity`; hence `iota_T` is faithful.  Aperture dilation implements the
translation action.  Because the chosen `T` is the P-G94 physical-overlap operator, this is a
single prime-mixed representation rather than a primewise direct sum.

## 5. Fourth-organ prediction: literal Euler flux

The crossed-product interpretation predicts that a prime-power translation by `k log p` must
produce a boundary shell of that exact length, and that pairing with the logarithmic Euler atom
must restore the unsquared von Mangoldt coefficient.  The independent Sonin organ already proves
exactly this:

```text
translation/cutoff commutator = interval projection,
semifinite trace(interval)     = k log p,
Euler log coefficient * trace = Lambda(p^k).                (SAC.16)
```

These are respectively `logTranslation_cutoffCocycle_eq_shell`,
`soninPhysicalLogShellWeight_eq_log`, and
`soninPrimePowerLogShellTraceDensity_eq_fluxCoefficient`.  Thus unsquared Euler provenance is a
cyclic-cocycle shadow of the same log-translation boundary, not an extra determinant insertion.
This agrees with POINH-B: `T` governs relations between formation and completion, never local
Euler multiplicity.

## 6. Exact surviving RH edge

The theorem changes the required producer.  It is not “identify the unit index with a sub-unit
positive distance”; Corollary SAC-B proves that impossible.  A viable source theorem must instead
construct a **prime-marked twist of the Wiener--Hopf extension** such that:

1. finite translation degree `k log p` has literal unsquared Euler coefficient;
2. theta completion fixes the quotient symbol before horizontal specialization;
3. a nonneutral horizontal character changes the relative extension/symbol class, rather than
   merely replacing `e_1` by the homotopic lift `e_c`;
4. the resulting failure-specific index equals the unsigned escape multiplicity;
5. its ideal representative inherits the proved primitive Euler nuclear budget.

Then one strict-right copy would give a nonzero integer bounded below one.  None of items 3--5 is
asserted here.  At a Xi divisor they must not be introduced as definitions, or the construction
would again be an RH receiver.

### 6.1 Modular-twist no-go

Prime marking by itself does not satisfy item 3.  Let

```text
Gamma=directSum_p Z,    ell(gamma)=sum_p gamma_p log p.
```

For every real grade `a`, the algebraic prime-translation crossed product admits the unitary
one-parameter automorphism

```text
beta_t^a(f U_gamma)=exp(i t a ell(gamma)) f U_gamma.          (SAC.17)
```

The character law for `ell` proves multiplicativity and star preservation, and its values have
unit modulus; hence the action extends to the full crossed product.  The nonunitary Euler factor
`exp(a ell(gamma))` is its imaginary-time value, not an obstruction to real-time C-star dynamics.
Functional-equation reflection sends `a` to `-a` and conjugates the flow.

The corpus independently proves off-wall KMS/detailed-balance systems and that global
detailed-balance neutrality is an RH classifier.  Therefore:

> Existence of prime-marked crossed-product dynamics, modular covariance, or a KMS
> interpretation cannot select the critical line.  The new condition must pair the twist with
> the Wiener--Hopf boundary class and the literal nuclear ideal; it cannot merely ask that the
> twist exist.

## Hostile review

- `[STANDARD ABSTRACT CORE]` Cone extensions, exponential boundary maps, transformation-group
  crossed products, and Wiener--Hopf index theory are established mathematics.
- `[NEW CORPUS LAW]` The exact identification `(SAC.1)--(SAC.16)` of the physical prime-mixed
  boundary-transfer history with that extension was not found in the corpus or checked sources.
- `[REAL ADVANCE]` It locates the integer and proves why the existing sub-unit germ norm cannot
  bound it.  This removes a false closure route rather than renaming its missing map.
- `[ROUTE-INDEPENDENT]` The cone theorem holds for every positive compact injective `T`; the HGT
  source selects one literal prime-mixed, trace-one, index-recovered instance.
- `[LIMIT]` The crossed product restores topology and index but does not make the index
  grade-sensitive.  Prime marking must change extension class, not only translate aperture.
- `[SECOND NO-GO]` Every real horizontal grade defines the modular flow `(SAC.17)`.  KMS or
  crossed-product admissibility without the failure-specific nuclear index pairing is nonselective.
- `[FALSIFIER]` Any proposed next theorem fails if its off-line integer is unchanged after
  forgetting prime labels, or if its “twist” is conjugate to `e_c` inside the fixed cone.

## Literature boundary

Wiener--Hopf C-star algebras and their analytic index maps are standard; see Alldridge--Johansen,
<https://arxiv.org/abs/math/0611196> and <https://arxiv.org/abs/math/0611198>.  Smooth crossed
products and Thom/Pimsner--Voiculescu K-theory are treated by Phillips--Schweitzer,
<https://arxiv.org/abs/funct-an/9211007>.  Connes--Consani use log scale, half-line cutoffs, and
quantized differentials in the zeta setting, <https://arxiv.org/abs/1910.14368>.  These sources do
not identify the P-G94 prime-mixed density's singular boundary-transfer orbit with the cone and
Sonin transgression proved above.

## Lean progress (2026-10-09)

| Claim | Lean |
|-|-|
| SAC-A, (SAC.1)–(SAC.4) | `HTGeometry/BoundaryCoronaCStarAlgebra`, `HTGeometry/ApertureConeCalculus` |
| (SAC.5)–(SAC.7) | `HTGeometry/ApertureOpenHistoryIdeal` (`openHistoryIdeal_eq_map`, `endpoint_exact_sequence`) |
| (SAC.8)–(SAC.12), SAC-B, cone contractible, `1 × 1` model | `HTGeometry/ApertureConeWinding` |
| (SAC.8) for the **stable** group `K₁(J_T) = colim π₀ U(M_n(J_T⁺))` | `HTGeometry/ApertureStableKTheory`: `StableK₁` (a `Group`), `stableK₁MulEquiv : StableK₁ ≃* Multiplicative ℤ`, `stableConnectingMap_bijective`, `projectionBoundary_class` (`δ[P] = rank P` on projections of `M_k(ℂ)`), `stable_boundaryExp_scaleGerm` (SAC.10), `stable_boundaryExp_sub` (SAC.12), `openK₁ToStable_bijective` |
| (SAC.13), (SAC.15), translation action | `HTGeometry/ApertureLogTranslation` |
| (SAC.16) | `RHTower/SoninLogShellCocycle` |
| §6.1 (SAC.17): prime-graded modular flow on the full crossed product, reflection `a ↦ -a`, imaginary-time Euler scaling | `HTGeometry/DiscreteCrossedProductCStar` (general full crossed product `A ⋊ Γ`, extension of automorphisms, strongly continuous dual flows), `HTGeometry/PrimeTranslationModularFlow` (`fullPrimeModularFlow_spec`, `primeReflection_conjugates`, `primeComplexTime_neg_I`, `primeEulerScaling_not_unitary`) |

Classification inside `ApertureStableKTheory`: free unitary loops are homotopic to based loops (path in
the connected `U(n)`), based loops with equal determinant are homotopic (`finiteUnitary_loops_homotopic_iff_det`),
determinant loops of equal winding are homotopic in `ℂ^×`.  All declarations of the three new modules
audit with `[propext, Classical.choice, Quot.sound]` only (168 + 185 + 25).

| (SAC.14) `C₀(ℝ) ⋊ ℝ ≅ 𝒦(L²(ℝ))` for the **full** crossed product | `HTGeometry/CStarEnvelope` (enveloping C⋆-algebra over `N`-bounded Hilbert representations), `HTGeometry/CompactKernelAlgebra` (twisted convolution core, kernel picture), `HTGeometry/CompactKernelL2Representation` (Schrödinger representation, Schur bound `‖T_k‖ ≤ ‖k‖_{L¹(ℝ,C₀)}`, matrix units), `HTGeometry/CompactKernelRankOneDensity` (Stone–Weierstrass density of rank-one kernels in `L¹(ℝ, C₀)`), `HTGeometry/RealTranslationCrossedProduct` (`schrodinger_injective`, `realCrossedProductEquivCompact : RealCrossedProduct ≃⋆ₐ[ℂ] CompactOps L2Real`, `KernelAlg.fibre_mul`/`fibre_star` = twisted convolution/involution) |

The five §4 modules audit with standard axioms only (63 + 41 + 79 + 37 + 43 declarations).

**Remaining for stage 3:** the crossed Wiener–Hopf extension `0 → 𝒦 → W → C*_r(ℝ) → 0` (symbol
at `+∞`, kernel `𝒦`) and the analytic index of its connecting map on the generator (Cayley unitary
`U = 1 + λ(g)`, `g(t) = -2eᵗ1_{t<0}`: lift `1 + P₊(U - 1)` is a co-isometry with one-dimensional
kernel, index `1`, symbol winding `1`).

### Wiener–Hopf extension and index — working plan (2026-10-09)

Formal reading of "crossing by ℝ gives the one-dimensional Wiener–Hopf extension … its connecting
map is the analytic Wiener–Hopf index":

1. **Operators on `L²(ℝ)`.** Half-line projection `P₊ = indicatorCutoff (Ici 0)`
   (`RHTower/SoninL2Model`), Fourier multipliers `C_φ = fourierMulCLM φ`
   (`HTGeometry/L2FourierMultiplier`), compactness of `M_{1_I} C_{1_J}` for bounded `I, J`
   (`isCompactOperator_cutoffFourierCutoff`).
2. **Cayley generator.** `U = 1 - 2V`, `(Vf)(x) = ∫_x^∞ e^{x-y} f(y) dy`; `U` is unitary
   (`V + V* = 2V*V = 2VV*`, kernel identities); `(1 - P₊) U P₊ = -2|e^{x}1_{x<0}⟩⟨e^{-y}1_{y>0}|`,
   `P₊ U (1 - P₊) = 0`, so `P₊ U P₊` is a co-isometry of `L²(ℝ₊)` with kernel `ℂ e^{-x}`:
   index `1` (`IsFredholmOp`, `fredholmIndex` of `HTGeometry/BoundedFredholmStability`).
3. **Symbol.** `U = C_c` with `c(ξ) = (−1 − 2πiξ)/(1 − 2πiξ)` (one Fourier integral); winding of `c`.
4. **General index.** `T_u = P₊ C_u P₊ + (1 - P₊)`; `T_u T_v − T_{uv}` compact; index locally
   constant (`IsFredholmOp.exists_stable`); uniform approximation of continuous unimodular symbols
   by powers of `c` times exponentials; so `Ind T_u = ± wind u`.
5. **Extension.** `W = C*(𝒦, M_χ C_φ)`, symbol at `+∞` (SOT limit of translates), kernel `𝒦`;
   connecting map `∂[u] = Ind(lift)` equals the winding isomorphism.
6. Full = reduced for the cone crossed product (envelope argument as in SAC.14).

### Wiener–Hopf extension — progress (2026-10-09, later)

Steps 1–6 of the working plan are done for scalar symbols, all with standard axioms only:

| Claim | Lean |
|-|-|
| General WH index: `T_U = P₊ C_U P₊ + (1-P₊)` is Fredholm with `ind T_U = wind(U)` for every continuous unimodular `U` on the circle | `HTGeometry/WienerHopfIndexTheorem` (`fredholmIndex_wienerHopfLift_eq_circleWinding`; compact Hankels by Stone–Weierstrass, Atkinson, `T_{zⁿ}` of index `n`, log of unimodular symbols, homotopy invariance) — 82 decls |
| Band-kernel operator calculus (common home of ideal, cone core, convolution algebra) | `HTGeometry/BandKernelOperators` — 86 |
| Cone core of `C₀((-∞,+∞]) ⋊ ℝ` (`χ(x)G(x-y) + k`), symbol at `+∞`, `L¹(ℝ, C₀((-∞,+∞]))` norm, full crossed product, `C*(ℝ)`, ideal and symbol maps (envelope functoriality) | `HTGeometry/ConeKernelCrossedProduct` — 120 |
| Full = reduced for `ℝ` (`‖π(G)‖ ≤ ‖C_G‖` for every `L¹`-bounded representation; support growth + Cauchy–Schwarz + Bernoulli) | `HTGeometry/RealGroupCStarFaithful` — 22 |
| Full = reduced for the cone crossed product (approximate unit on the essential subspace of the compact ideal; `C*(ℝ)` bound on its complement; symbol dominated by translation) | `HTGeometry/ConeCrossedProductFaithful` — 46 |
| `C*(ℝ) ≅ C₀(ℝ̂)` on the circle (`realGroupCStarEquiv`), circle multiplier representation isometric, inverse Cayley map, Riemann–Lebesgue descent | `HTGeometry/CircleSymbolGroupCStar` — 43 |
| Exact sequence `0 → C₀(ℝ)⋊ℝ → C₀((-∞,+∞])⋊ℝ → C*(ℝ) → 0` (`wienerHopf_extension_exact`); connecting map = analytic WH index on every unimodular symbol (`wienerHopf_connecting_index`, `wienerHopf_connecting_map`) | `HTGeometry/WienerHopfConeExtension` — 45 |

**Remaining for stage 3:** the stable (matrix) form of the connecting map: for unitary
`U ∈ M_n(C(S¹))`, lifts in `M_n` of the unitized cone crossed product act on `L²(ℝ)ⁿ` as Fredholm
operators of index `wind(det U)` (matrix Hankel compactness, matrix Atkinson, the homotopy
`U ≃ diag(det U, 1, …, 1)` from `finiteUnitary_loops_homotopic_iff_det`, block additivity of the
index), so that `∂ : K₁(C*(ℝ)) → K₀(𝒦) = ℤ` is the index on stable classes.

### Stable connecting map — done (2026-10-09)

| Claim | Lean |
|-|-|
| Operator matrices on `L²(ℝ)ⁿ` (`*`-homomorphism, compactness, continuity); block-diagonal index additivity; matrix Wiener–Hopf lift Fredholm for unitary matrix symbols | `HTGeometry/MatrixWienerHopfFredholm` — 58 decls |
| Matrix WH index theorem `ind T_U = wind(det U)` (loop ↔ symbol families, `finiteUnitary_loops_homotopic_iff_det`, base-point transport, `diag(det U, 1, …, 1)`) | `HTGeometry/MatrixWienerHopfIndex` (`fredholmIndex_matWH`) — 50 |
| Connecting map `K₁(C*(ℝ)) → K₀(𝒦) = ℤ` on stable classes: every unitary `U ∈ Mₙ(C(S¹))` lifts to `Mₙ` of the unitized cone crossed product, every lift has Schrödinger image of index `wind(det U)` | `HTGeometry/MatrixWienerHopfConnecting` (`wienerHopf_connecting_index_matrix`, `wienerHopf_connecting_map_matrix`) — 19 |

## Lean certificate (stage 3)

All claims (SAC-A, SAC-B, SAC.1–SAC.17, §4 Wiener–Hopf extension and connecting map, §6.1)
are formalized without hypotheses beyond the card's own data, without `sorry`/axioms:
`#print axioms` on every declaration of the modules listed above reports only
`[propext, Classical.choice, Quot.sound]` (audits of 2026-10-09: 168 + 185 + 25, 263, 82, 362, 127
declarations).  All modules are wired into `GaloisForLFunctions/HTGeometry.lean`; the `.ilean`
collision sweep against the whole corpus is clean.  §6 items 1–5 are explicitly not asserted by
the card.
