# The doctrine-independent multiplicative core of the field with one element

- **ID:** field-one-multiplicative-core
- **Stage:** 3-formalized
- **Type:** THEOREM (Lean)
- **Labels:** `[LITERATURE] [BRIDGE] [PAPER-PROVED] [LEAN-FORMALIZED] [NOT NEW SCIENTIFIC KNOWLEDGE]`
- **Source:** Deitmar's monoid schemes; Toën–Vaquié relative schemes over
  `(Set, ×, *)`; Vezzani's equivalence of these two scheme theories; Lorscheid,
  *F₁ for everyone*.
- **Statement:** In pointed commutative multiplicative algebra,
  `F₁ = {0,1}` is the initial field-like commutative monoid with zero. Its
  contracted scalar extension to a commutative ring `R` is canonically `R`;
  its modules are pointed sets; the free rank-`I` module is `I₊ = I ⊔ {0}`;
  and its automorphism group is `Perm(I)`.

## Goal

Bank the exact common core shared by the minimal monoid approach and the
multiplicative shadows of richer approaches. This theorem does **not** choose
blueprints, bands, semirings, λ-rings, generalized rings, Γ-rings, or analytic
sites as the unique meaning of `F₁`.

## Definitions

1. `CMon₀` has commutative monoids with an absorbing zero as objects and maps
   preserving `0`, `1`, and multiplication as morphisms.
2. `F₁` is the two-element object `{0,1}` with `0x=0` and `1x=x`.
3. For a commutative ring `R` and `A ∈ CMon₀`, the **contracted monoid
   algebra**

   `R[A]ᶜ := R[A] / ([0_A])`

   kills the basis vector indexed by the absorbing zero. This contraction is
   load-bearing: the ordinary monoid algebra of `{0,1}` retains an unwanted
   idempotent and is not the desired scalar extension.
4. An `A`-module in the monoid theory is a pointed set `(M,0_M)` with an
   associative unital action satisfying `0_A m = 0_M`; module maps are
   equivariant pointed maps.
5. `I₊` is `I` with one disjoint basepoint.

## Complete paper proof

### Initiality and field-likeness

Let `A ∈ CMon₀`. A morphism `f : F₁ → A` must satisfy `f(0)=0_A` and
`f(1)=1_A`; these equations determine `f` on both elements. They also define
a morphism because the four products in `F₁` are preserved. Thus there is
exactly one such morphism, so `F₁` is initial.

The only nonzero element of `F₁` is `1`, and `1·1=1`; hence every nonzero
element is invertible. This is the precise field-like statement available
without addition. It is not an ordinary field: an ordinary nontrivial ring
has distinct elements `0` and `1`, hence at least two elements.

### Contracted base extension

Every element of `R[F₁]ᶜ` has a representative

`r₀[0] + r₁[1]`.

The quotient relation `[0]=0` leaves the unique representative `r₁[1]`.
Define `ε_R(r[1])=r`. It is additive, multiplicative, and unital because
`[1][1]=[1]`. Its inverse sends `r` to `r[1]`. Therefore

`R[F₁]ᶜ ≃ R`

canonically as commutative rings. In particular `Z[F₁]ᶜ ≃ Z`.

### Modules are pointed sets

Let `(M,0_M)` be a pointed set. An `F₁`-action, if it exists, is forced:

`0·m = 0_M`, `1·m = m`.

These formulas satisfy associativity and the unit and zero laws, so the
action exists uniquely. A function between two such modules is equivariant
iff it preserves the basepoint: equivariance at `0` is exactly basepoint
preservation, while equivariance at `1` is automatic. Thus the category of
`F₁`-modules is canonically equivalent to the category of pointed sets.

### Free modules and `GL_I(F₁)`

For a set `I`, let `I₊=I⊔{0}`. Given a pointed set `M`, restriction to `I`
gives a bijection

`Hom_*(I₊,M) ≃ (I → M)`,

since a pointed map must send the added basepoint to `0_M`, and every
function on `I` extends uniquely this way. Hence `I₊` is the free
`F₁`-module on `I`.

Every pointed automorphism of `I₊` fixes the basepoint and therefore
restricts to a permutation of `I`. Conversely every permutation of `I`
extends by fixing the basepoint. Restriction and extension are inverse and
respect composition, so

`Aut_{F₁}(I₊) ≃ Perm(I)`.

For `I=Fin n`, this is the Tits identity `GL_n(F₁) ≃ S_n`.

Under the module/Tits point convention, projectivization quotients the
nonzero vectors of `I₊` by `F₁ˣ={1}` and therefore has point set `I`.
Consequently `P^{n-1}(F₁)` has `n` module/Tits rational points. This must not
be conflated with the full topological point set of a monoid-scheme
projective space, whose generic strata encode nonempty subsets.

This closes every dependency. ∎

## Hostile audit

1. **Ordinary-field reading — `FALSE`.** A one-element nontrivial ring cannot
   exist. The construction is explicitly non-additive.
2. **Uncontracted monoid algebra — `FALSE`.** Keeping `[0]` produces an extra
   idempotent; scalar extension is not `R`. The contracted algebra is
   essential.
3. **All approaches have the same carrier — `FALSE`.** The initial band is
   `F₁±={0,1,−1}`, not `{0,1}`. Semiring and ring doctrines have initial
   objects `N` and `Z`. Only the multiplicative shadow is claimed here.
4. **All notions of rational point coincide — `FALSE`.** Module/Tits points,
   scheme morphisms, closed points, congruence points, and tropical points
   are different functors.

**Verdict:** `REDISCOVERED` / `BRIDGE`. The theorem is standard core
infrastructure, not new scientific knowledge. It survives because its scope
is exact.

## Gates

- [x] 0 → 1: internal and external frontier audited; statement typed; false
  stronger readings separated.
- [x] 1 → 2: complete dependency-closed proof above; hostile audit passed.
- [x] 2 → 3: exact Lean theorem package and axiom audit complete.
- [ ] 3 → 4: publication-ready extraction.

## Lean certificate

- **Module:** `GaloisForLFunctions.HTGeometry.FieldOneMultiplicativeCore`
- **Theorems:** `fieldOne_hom_unique`, `fieldOne_isUnit_of_ne_zero`,
  `contractedBaseChangeEquiv`, `freeFieldOneModuleHomEquiv`,
  `freeFieldOneModuleAutMulEquiv`, `card_projectiveModulePoints`
- **Audit:** direct `lake env lean` and final targeted `lake build` passed;
  `#print axioms` reports only standard Lean principles.

## No-go closure

- **Exact killing theorem/mechanism:** one carrier cannot literally be the
  initial object of pointed monoids (`{0,1}`) and bands
  (`{0,1,−1}`), and richer theories use non-equivalent point and scheme
  functors.
- **Strongest positive survivor:** the exact multiplicative-core theorem
  above, plus an indexed doctrine atlas rather than a privileged universal
  carrier.
- **New insight:** `F₁` has a stable multiplicative core, while addition,
  subtraction/null relations, descent, homotopy, and analysis are
  independent enhancement axes.
- **Status:** survivor is `[PAPER-PROVED] [LEAN-FORMALIZED]`.

## Log

- 2026-07-26 — external audit through current 2024–2026 band and band-module
  literature; paper proof closed; hostile audit downgraded claim to known
  multiplicative core.
- 2026-07-26 — formalized unconditionally; targeted build, axiom audit, and
  project lint passed; formal certificate and doctrine atlas integrated into
  `docs/the field with one element.md`.
