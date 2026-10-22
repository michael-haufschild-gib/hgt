# RH is a two-torsion class, and every reader in the corpus is real-valued

**Status:** core Lean-closed (axiom-clean). Diagnosis complete; producer open.
**Modules:** `RHTower/ReflectionTateParity.lean`, `RHTower/LagReflectionKernelNoGo.lean`.
**Ledger:** CANNOT-399, MUST-400 (building on CANNOT-397, MUST-398).

## The statement

Two involutions act on `Div(ξ)`:

| involution | fixed zeros | corpus name |
|---|---|---|
| `ρ ↦ 1 − ρ` (functional equation) | none | `xiZeroCopyReflectEquiv` |
| `ρ ↦ 1 − ρ̄` (Hermitian reflection) | **exactly the critical line** | `lagPartner` |

F302 warns the two must stay distinct. The second is the one that carries RH:

```
riemannHypothesis_iff_lagPartner_fst_eq :
  RiemannHypothesis ↔ ∀ q : XiZeroCopy, ((lagPartner q).1 : ℂ) = (q.1 : ℂ)
```

**RH is the triviality of a canonical `ℤ/2`-action on the divisor.** Not an inequality. Off-line
zeros are exactly the *free orbits* of that action; they come in pairs; the separating invariant is
the class of a free orbit in a `ℤ[ℤ/2]`-module — **2-torsion**.

## Why every corpus reader is blind (the diagnosis)

`horizontalGrade q = 2 Re ρ − 1` is the reflection-**odd** coordinate:

```
horizontalGrade_lagPartner      : horizontalGrade (lagPartner q) = - horizontalGrade q
horizontalGrade_lagPartner_eq_iff : ... = horizontalGrade q ↔ horizontalGrade q = 0
```

`ℝ` is torsion free, so the reflection's fixed locus in `ℝ` is `{0}` — the same degeneracy as the
group side (CANNOT-397). Hence:

```
reflectionEven_reader_eq_at_partner (F : ℝ → ℝ) (hF : ∀ a, F (-a) = F a) :
  F (horizontalGrade (lagPartner q)) = F (horizontalGrade q)
sq_horizontalGrade_nonneg : 0 ≤ horizontalGrade q ^ 2
```

Every reflection-even real-valued reader takes the *same value* on a copy and on its partner, and the
canonical even coordinate is `a²`, which is `≥ 0` for **every** grade. So a positivity statement about
`a²` is automatically consistent with an off-line zero.

This is the cause, not another instance, of F67 ("existing positive proofs mostly reconstruct or
conserve the anomaly; existing no-gos mostly show that hiding it forces payment elsewhere"). The
transports are ℝ-linear; the anomaly is 2-torsion; `Hom(ℤ/2, ℝ) = 0`.

It also explains, in one line each:
- **MUST-393** ("a positivity cannot produce a comparison") — a positivity is ℝ-valued.
- **CANNOT-110** ("odd orientation and even escape live in different graded pieces") — exactly this.
- **F205** ("the escape class is the unsigned support, reflection-even, and reflection doubles it").
- **HARD LOCK P**, **CANNOT-03/04/15**, the whole Weil/Hankel/Gram/energy/index family.

## The unification (MUST-400)

Four lanes the ledger treats as unrelated are one `𝔽₂` obstruction:

1. **Reflection kernel** — `K♯(x,y) = K(x,y⁻¹)`; fixed locus of inversion on `ℚ^×_{>0}` is a point
   (torsion free) ⇒ never PSD (CANNOT-397).
2. **Dual side** — the same inversion fixes the *quadratic characters* `∏_p{±1}`, but the zeros sit
   on the Kronecker line `γ ↦ (p^{iγ})_p`, which meets that locus only at the identity (prime logs
   ℚ-independent). Transverse ⇒ the reflection form is exactly **metabolic**: one hyperbolic plane
   per conjugate pair, Witt class zero (corpus F328, F331 read correctly).
3. **Twin rigidity / half-divisor** (F387, MUST-126) — every twin factorisation is a square root
   dressed by a unit; the open core is an analytic half-divisor.
4. **Dyadic root tower + parity wall** (F16a, F389) — a positive finite zero order is not divisible
   by every `2^k`; ξ has odd-order critical zeros above every height.

All four are the failure of the squaring map to admit a section: `1 → ∏_p𝔽₂ → ∏_p𝕋 →^{sq} ∏_p𝕋 → 1`
is topologically non-split **already at one prime** (`z ↦ z²` on the circle has no continuous root),
with class the generator of `H¹(𝕋, 𝔽₂) = 𝔽₂`.

## Producer direction

The one arithmetic machine that computes a global `ℤ/2`-cohomology class **exactly, from local
ramification, with no estimate**, is genus theory — the ambiguous class number formula. A producer
must exhibit `Div(ξ)` with its Hermitian involution as the module whose `Ĥ⁰` that formula computes,
and derive triviality of the action from local data **before** divisor specialisation.

## Falsifiers

- If some corpus reader is reflection-**odd** and real-valued and non-trivially detects a grade, the
  blindness diagnosis is incomplete for it. (Candidates: `xiReflectionSelfIntersectionCharge`,
  Kummer regulators. Check each: most are even or squared.)
- If the `ℤ/2`-action is supplied only after reading a zero, the construction is circular.
- If a genus-theoretic model exists but its `Ĥ⁰` is not the on-line count, the identification fails
  and this card is a re-description only.
