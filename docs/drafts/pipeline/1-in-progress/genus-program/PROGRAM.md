# The genus-theory programme for RH

**Origin:** MUST-400. **Coordinates:** CANNOT-397, CANNOT-399, MUST-401.
**Status:** Layer A started. Layers B, C open. This card is the plan and the gate list.

## Why this programme and not another

Three facts, all Lean-certified this cycle, force the shape:

1. `RiemannHypothesis ↔ ∀ q, lagPartner q = q` — RH is the **triviality of a `ℤ/2`-action** on
   `Div(ξ)`, where `σ : ρ ↦ 1 − ρ̄` is the Hermitian reflection. Off-line zeros are its **free
   orbits** (`ReflectionTateParity`).
2. The separating invariant is therefore **2-torsion**, and every reflection-**even** real-valued
   reader is blind to it: `Hom(ℤ/2, ℝ) = 0` (`reflectionEven_reader_eq_at_partner`). That is the
   structural cause of the corpus's universal positivity blindness, not another instance of it.
3. `σ` **preserves the ordinate**, so the action is fibred over the height and RH is the injectivity
   of the ordinate map (`OrdinateInjectivity`): a **separation** statement, not a resolution one.

Genus theory is the unique machine in arithmetic that computes a **global `ℤ/2`-cohomology class
exactly from local ramification data, with no estimate anywhere**. Chevalley's ambiguous class number
formula,

```
#Cl(L)^G  =  h_K · ∏_v e_v / ( [L:K] · [E_K : E_K ∩ N L^×] ),
```

is local data in the numerator and one global 2-torsion unit obstruction in the denominator. That is
exactly the shape (2) demands.

### Compatibility with the corpus's F₁ no-gos — the decisive check

The corpus has killed the neighbouring routes, and it matters that they die for reasons this one
does not share:

| no-go | what it kills | does it bite here? |
|---|---|---|
| F395 / CANNOT-195 `FrobeniusLatticeRigidity` | no finite free `ℤ`-module carries three Frobenii with eigenvalues `p^ρ, q^ρ, r^ρ`, `ρ` nonreal | **No.** Genus theory diagonalises nothing. |
| F390 `FrobeniusTorsionLaw` | Weil–Deligne integrality on the zeros contradicts RH | **No.** No integrality is imposed on the zeros. |
| MUST-129 | an F₁ construction must be integral on the **test-function** side; **it cannot have a characteristic polynomial** | **No — and this is the point.** Chevalley's formula is a counting/cohomology identity; no characteristic polynomial appears. |
| CANNOT-73 / F133 `ReflectionTateConservativeClassification` | *assuming* a conservative reflection-Tate charge is circular | **Partly.** We must **derive** the charge, not assume it. This is gate C2. |

So the programme is not excluded by anything currently on the ledger. That is a necessary condition,
not evidence.

## The layers

### Layer A — the machine (unconditional, no ζ, missing from mathlib)

- **A1** `ℤ/2` Tate cohomology: `Ĥ⁰ = ker(σ−1)/im N`, `Ĥ¹ = ker N/im(σ−1)`, `N = 1 + σ`.
- **A2** Herbrand quotient `h(M) = |Ĥ⁰|/|Ĥ¹|`: multiplicative in short exact sequences, invariant
  under finite index, `h = 1` for finite modules.
- **A3** Permutation modules: `Ĥ*(ℤ/2, ℤ[ℤ/2]) = 0`; `Ĥ⁰(ℤ/2, ℤ) = ℤ/2`, `Ĥ¹ = 0` (trivial action).
- **A4** Consequence: for a `ℤ/2`-set `X`, `dim_{𝔽₂} Ĥ⁰(ℤ/2, 𝔽₂[X]) = #Fix(σ)`.
- **A5** Chevalley's ambiguous class number formula.

**Done (this cycle, Lean, axiom-clean):** the `𝔽₂` core of A1/A3/A4 in the form that matters —
`DivisorGaloisNorm.lean`: over `𝔽₂` the two eigen-conditions collapse (`σ−1 = σ+1 = N`), the norm is
a **square-zero differential**, and

```
riemannHypothesis_iff_divisorNorm_eq_zero :
  RiemannHypothesis ↔ ∀ f, divisorNorm f = 0
```

**RH is the vanishing of the Galois norm of the reflection on the mod-2 divisor module.**

### Layer B — the bridge

- **B1** `Div(ξ)` as a `ℤ[ℤ/2]`-module under `supportPartner`. *(Done in the `𝔽₂` form.)*
- **B2** Per window `W`: `dim_{𝔽₂} Ĥ⁰(σ, 𝔽₂[Div_W]) = N₀(W)`, `dim 𝔽₂[Div_W] = N(W)`;
  RH ⟺ equality at every window. **Open — needs A4 with finiteness of the window.**
- **B3** An exact sequence of `ℤ/2`-modules relating `Div_W(ξ)` to an arithmetic module whose Tate
  groups are computable, plus multiplicativity of the Herbrand quotient. **Open, and the real work.**

### Layer C — the input (the gate)

- **C1** Which arithmetic object has `Div(ξ)` as its `σ`-module? The structural match to aim at:
  `σ` behaves as a **complex conjugation**, so the target is a CM-type structure and
  **RH becomes "the minus part vanishes"** — a Vandiver-shaped statement, not an analytic one.
- **C2** Its ramification data, derived **before** divisor specialisation (else CANNOT-73 applies).

## Gates, in order

| gate | statement | status |
|---|---|---|
| G1 | RH = vanishing of the Galois norm on `𝔽₂[Div]` | **closed** (`DivisorGaloisNorm`) |
| G2 | **slice** finiteness: `{ρ ∈ Div : Im ρ = t}` is a finite `ℤ/2`-set | **closed** (`DivisorSliceGenus.xiSlice_finite`) |
| G3 | slices are `σ`-stable; RH ⟺ every slice is a subsingleton | **closed** (`riemannHypothesis_iff_forall_xiSlice_subsingleton`) |
| G4 | an exact sequence with a computable third term | open — **the real gate** |
| G5 | ramification data derived pre-divisor | open |
| G6 | Chevalley applied; `N₀(W) = N(W)` | open |

## G2 closed (this cycle)

`finite_xiDivisorSupport_band` (corpus, `XiZeroBandFinite.lean`) at radius `0` gives it immediately:
the slice is the band of radius zero.  So `xiSlice_finite`, `supportPartner_mem_xiSlice`, and

```
riemannHypothesis_iff_forall_xiSlice_subsingleton :
  RiemannHypothesis ↔ ∀ t : ℝ, (xiSlice t).Subsingleton
```

with every slice finite.  **Falsifier 2 below is discharged**: the carrier is a family of finite
`ℤ/2`-sets, which is the category Chevalley's formula lives in.

## G2 — the route that was taken

`σ` preserves the ordinate (`lagPartner_im`), so the action is fibred and the natural finite object
is the **slice** `xiSlice t = {ρ : XiDivisorSupport | (ρ : ℂ).im = t}`, not a window.  Its image in
`ℂ` lies in the compact rectangle `[0,1] × {t}` because every zero has `0 < Re ρ < 1`
(`xi_zero_re_mem_open_unit`, `xi_eq_zero_of_mem_divisor_support`).  Candidate APIs, in order of
preference:

- `MeromorphicOn.divisor_support_finite_of_subset (hf) (hU : IsCompact U) (hV : V ⊆ U)`
  (mathlib, `Analysis/Meromorphic/Divisor.lean`), with `U = closedBall (1/2 + t·I) 1`;
- `Function.locallyFinsuppWithin.finiteSupport (hU : IsCompact U)`;
- the corpus's own `hlocal : LocallyFiniteSupport (fun z => MeromorphicOn.divisor xi Set.univ z)`
  from `xiDivisorSupport_univ_countable` (`XiCanonicalProduct.lean`), pushed through a
  `LocallyFinite`-meets-compact lemma.

Once G2 is closed, G3 is finite linear algebra over `𝔽₂`: on a finite `ℤ/2`-set the norm has
`rank N = #freeOrbits`, so `dim Ĥ⁰ = dim − 2·rank N = #Fix`, and RH is `dim Ĥ⁰ = dim` at every
slice.  **This is the point at which a genuinely finite `ℤ/2`-module exists, which falsifier 2 below
flags as the thing that could kill the programme outright.**

## Falsifiers — check these before spending a cycle

1. **Herbrand triviality.** `Ĥ¹(ℤ/2, 𝔽₂[X]) = Ĥ⁰` over `𝔽₂` (the complex is 2-periodic), so the
   Herbrand quotient of the mod-2 module is `1` and carries **no** information. Any argument that
   appears to extract RH from the Herbrand quotient alone is wrong. The information is in
   `dim Ĥ⁰` versus `dim` — a **rank** comparison, not a quotient.
2. **Infinite rank.** `Div(ξ)` is infinite; Chevalley applies to **finite** class groups. The
   programme must work window by window (G2) or find a genuinely finite quotient. If neither, it
   dies here.
3. **No `ℚ`-structure.** The zeros are not algebraic numbers, so Hasse–Minkowski / Hasse–Witt
   invariants over `ℚ` are **not** available. Only the `𝔽₂`/`ℤ[ℤ/2]`-module structure is. Any step
   using a discriminant in `ℚ^×/(ℚ^×)²` must first supply the `ℚ`-structure.
4. **Circularity.** If the ramification data (C2) is read off the zeros, CANNOT-73 applies and the
   whole thing is a receiver.
5. **Proves too much.** If a construction works for any entire function with ξ's functional
   equation, CANNOT-01 kills it: that class admits off-line zeros.

## Honest assessment

Layer A is real, missing infrastructure, and independently valuable. Layer B2/B3 is where a new
theorem could appear. Layer C is the same open problem the F₁ programme has had for decades, in a
coordinate that is at least not excluded by the corpus's own no-gos. The programme's value in the
near term is **falsification speed**: gates G2 and G4 are sharp enough to kill it quickly if it is
wrong, which is more than most of the routes in the ledger could say.
