# External tensor polarization and group-like--primitive formation defect law

- **Stage:** 3-formalized

## Status

- **Label:** ULF-NIMM-2
- **Paper status:** fully proved
- **Lean status:** formalized in `RHTower.RouteRExternalTensorMonodromy`
- **Scope:** external polarization of square-zero critical-wall monodromy
- **RH claim:** none

## 1. Higher-law interpretation

The previous law found a precise blindness: in the summable Hadamard corona `A`, the nonzero
critical-wall tangent `h_a` satisfies `h_a^2=0`.  Hence every internal positive response beginning
with that square vanishes.  This does **not** mean second-order information is absent.  It means
formation multiplied two logically distinct legs after placing both in the same quotient.

Correct higher operation is external polarization:

\[
  h_a\boxtimes h_a:=h_a\otimes_{\mathbb C}h_a\in A\otimes_{\mathbb C}A.
\]

Over a field, a pure tensor of two nonzero vectors is nonzero.  Thus internal multiplication sends
the external class to zero,

\[
  m(h_a\otimes h_a)=h_a^2=0,
\]

while the class itself survives.  Positivity was not intrinsically blind; **diagonal
multiplication was the information-destroying observer**.

The same tensor is the exact defect between two formation laws.  Multiplicative monodromy treats
`q_a=1+h_a` as group-like and produces `q_a tensor q_a`.  First-order additive geometry treats
`h_a` as primitive and produces only `1 tensor 1 + h_a tensor 1 + 1 tensor h_a`.  Their difference
is `h_a tensor h_a`.

## 2. Corpus audit before formulation

Fresh corpus searches were run for:

```text
group-like square-zero primitive monodromy tensor h tensor h
critical wall primitive tangent coproduct groupLike
ind pro group-like landing critical wall RH
Route R critical wall external tensor square monodromy curvature positive polarization
```

Found facts:

- `routeRNilpotentMonodromy`: `q_a=1+h_a`, inversion under reflection, internal energy zero, odd
  curvature `2h_a`, and cofinal fixedness;
- `SquareZeroDualNumberEmbedding`: nonzero square-zero classes are faithful dual-number arcs and
  therefore formally ramified;
- `IndProGroupLikeLandingSelection`: universal group-like landing is already an RH terminal;
- group-like classifications for monoid/group/symmetric Hopf algebras;
- tensor-square receivers in Deninger and other organs.

Not found:

- external tensor square of the actual Route-R critical-wall corona class;
- exact group-like--primitive defect for that class;
- proof that the defect survives exactly off wall.

Therefore this card does not conjecture group-like landing.  It constructs the missing faithful
positive carrier and computes the obstruction that any source coalgebra comparison must address.

## 3. Pure-tensor fidelity

### Lemma 3.1

Let `k` be a field, `V` a `k`-vector space, and `v in V`. Then

\[
  v\otimes v=0\quad\Longleftrightarrow\quad v=0.
\tag{ETP.1}
\]

#### Proof

The reverse implication is immediate.  If `v` is nonzero, choose a linear functional `f:V->k`
with `f(v)=1`.  Applying `f tensor f` to `v tensor v=0` gives `1 tensor 1=0` in `k tensor_k k`.
The canonical left-unit isomorphism sends this to `1=0`, contradiction. QED.

## 4. Two formation laws

Let `A` be the Route-R summable Hadamard corona and let `h_a`, `q_a=1+h_a` be the already certified
critical-wall tangent and monodromy. Define

\[
\begin{aligned}
  G_a&:=q_a\otimes q_a,\\
  P_a&:=1\otimes1+h_a\otimes1+1\otimes h_a,\\
  C_a&:=h_a\otimes h_a.
\end{aligned}
\tag{ETP.2}
\]

`G` is multiplicative/group-like formation, `P` is primitive first-order formation, and `C` is
external tensor curvature.

### Theorem 4.1 — exact formation conservation

For every real grade `a`,

\[
  G_a=P_a+C_a.
\tag{ETP.3}
\]

Moreover,

\[
  C_a=0\Longleftrightarrow a=0,
  \qquad
  C_a\ne0\Longleftrightarrow a\ne0.
\tag{ETP.4}
\]

#### Proof

Bilinearity gives

\[
 (1+h_a)\otimes(1+h_a)
 =1\otimes1+h_a\otimes1+1\otimes h_a+h_a\otimes h_a.
\]

This is `(ETP.3)`.  Lemma 3.1 and the corpus theorem `h_a ne 0 iff a ne 0` give `(ETP.4)`. QED.

### Theorem 4.2 — reflection and recurrence

External curvature is reflection-even:

\[
  C_{-a}=(-h_a)\otimes(-h_a)=C_a.
\tag{ETP.5}
\]

It is also factorwise stationary under cofinal prime-tail deletion:

\[
  S(h_a)\otimes S(h_a)=h_a\otimes h_a=C_a.
\tag{ETP.6}
\]

#### Proof

Use the existing identities `h_{-a}=-h_a` and `S(h_a)=h_a`, then tensor bilinearity. QED.

### Corollary 4.3 — internal/external phase separation

For every `a`,

\[
 E(q_a,q_a^{-1})=0,
 \qquad
 G_a-P_a=C_a,
 \qquad
 C_a=0\Longleftrightarrow a=0.
\tag{ETP.7}
\]

Thus even reflected energy is identically neutral after internal multiplication, while external
even polarization remains a complete detector of wall displacement.

## 5. Four-organ prediction

The law predicts the same survivor in four structurally different organs:

| Organ | Predicted class |
|---|---|
| multiplicative monodromy | reduced coproduct of `q_a` |
| deformation geometry | quadratic obstruction to making `h_a` exactly primitive |
| positive information geometry | external polarization before diagonal contraction |
| two-copy/cross-prime incidence | non-diagonal pair class retaining independent provenance |

The fourth prediction is precise: any coefficient-faithful two-copy source comparison that keeps
the two prime histories independent must receive `C_a`, not the already vanished product `h_a^2`.
Conversely, any comparison factoring through diagonal multiplication is provably blind.

## 6. Exact RH closure

For each completed-Xi divisor copy with centered grade `a(rho)`, Theorem 4.1 gives

\[
 G_{a(\rho)}=P_{a(\rho)}
 \Longleftrightarrow C_{a(\rho)}=0
 \Longleftrightarrow a(\rho)=0
 \Longleftrightarrow \Re\rho=\tfrac12.
\tag{ETP.8}
\]

Hence RH follows from one exact source law:

> arithmetic monodromy formation and arithmetic primitive formation agree in a
> coefficient-faithful external tensor landing for every completed-Xi divisor copy.

This statement is not asserted here.  To be a producer rather than a renamed RH endpoint, its
proof must arise before divisor inspection from one source coalgebra/conservation mechanism.
Corpus already shows that merely postulating group-like ind--pro landing is terminal.  Required
next work is therefore narrower: identify a literal source operation carrying both formations and
prove their equality from a source boundary-square, coface, or conservation identity.  No
conjecture is active until that operation is located by corpus search.

## 7. Anti-theatre boundary

Proved:

- nonzero square-zero wall information survives external tensoring;
- diagonal multiplication is exactly the erasing observer;
- group-like minus primitive formation is exactly external tensor curvature;
- this curvature is nonzero exactly off wall, reflection-even, and cofinally stationary.

Not proved:

- arithmetic source coalgebra realization;
- source equality of group-like and primitive formations;
- RH.

## Lean certificate

- [x] 2 → 3: Lean `GaloisForLFunctions.RHTower.RouteRExternalTensorMonodromy`, `GaloisForLFunctions.RHTower.NilpotentMonodromyCriticalLineChain`, `GaloisForLFunctions.RHTower.RouteRNilpotentMonodromy`; `lake env lean` + module build pass; axiom audit `[propext, Classical.choice, Quot.sound]` only

Modules `GaloisForLFunctions.RHTower.RouteRExternalTensorMonodromy` (17 constants) and `GaloisForLFunctions.RHTower.NilpotentMonodromyCriticalLineChain` (7 constants), on `GaloisForLFunctions.RHTower.RouteRNilpotentMonodromy`; axiom audit clean.

| Claim | Lean declaration |
|-|-|
| Lemma 3.1 (ETP.1) `v ⊗ v = 0 ⟺ v = 0` over a field | `self_tmul_ne_zero_of_ne_zero`, `self_tmul_eq_zero_iff` |
| (ETP.2) `G_a`, `P_a`, `C_a` on `A ⊗_ℂ A`; diagonal multiplication | `RouteRExternalMonodromyTensor`, `routeRExternalGroupLikeFormation`, `routeRExternalPrimitiveFormation`, `routeRExternalTensorCurvature`, `routeRExternalDiagonalMultiplication` |
| Thm 4.1 (ETP.3) `G_a = P_a + C_a` | `routeRExternalGroupLikeFormation_eq_primitive_add_curvature` |
| Thm 4.1 (ETP.4) `C_a = 0 ⟺ a = 0` | `routeRExternalTensorCurvature_eq_zero_iff` |
| §1 internal multiplication kills `C_a` (`m(h ⊗ h) = h² = 0`) | `routeRExternalDiagonalMultiplication_curvature_eq_zero` |
| Thm 4.2 (ETP.5) reflection-even; (ETP.6) factorwise shift-stationary | `routeRExternalTensorCurvature_neg`, `routeRExternalTensorCurvature_shift_fixed` |
| Cor 4.3 (ETP.7) | `routeRExternal_phaseSeparation`, `routeRExternalTensorMonodromy_law` |
| (ETP.8) `G = P ⟺ C = 0 ⟺ a = 0 ⟺ Re ρ = 1/2` | `routeRExternalGroupLikeFormation_eq_primitive_iff`, `routeRExternalGroupLikeFormation_eq_primitive_iff_re` |

## Log

- 2026-09-28 — Lean certificate audited; every numbered claim mapped to a declaration; moved to 3-formalized.
