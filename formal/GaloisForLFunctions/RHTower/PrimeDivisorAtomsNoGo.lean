/-
No {σ_p}-graded refinement of the ξ-divisor exists at a pinned strip annulus.

A divisor refinement graded by the primes would attach, to the order of vanishing of ξ at a strip
point ρ, a finer prime-indexed structure — a decomposition of the multiplicity `analyticOrderAt xi ρ`
into pieces sourced by the individual Euler factors. Equivalently (the source-map form): a map from
the primes `{σ_p}` into the local divisor atoms at ρ.

Every finite prime layer is a **unit** at every strip point. On the whole right half-plane
`Re s > 0` the finite multiplicative truncation `eulerPartial P` is nonvanishing and analytic, so its
`analyticOrderAt` is `0` there (`eulerPartial_orderAt_zero`); it has no zeros in the half-plane at all
(`eulerPartial_zeroSet_eq_empty`). Multiplying ξ by any finite prime atlas therefore leaves the
divisor unchanged (`xi_divisor_prime_invisible`): the prime layers are invisible to the divisor.

Consequently a source map whose atoms are realized as zeros of the primes' own local factors is the
**zero map** (`sigma_source_map_trivial`): each factor is a unit, so it contributes no atom. At a
strip zero this is decisive (`source_atom_mismatch`): the additive Euler–Maclaurin carrier resolves
the order-`m` zero into `m ≥ 1` hole-atoms, while every prime-sourced count is `0`. The two content
regions are disjoint (`prime_content_and_divisor_disjoint`): where the Euler product converges to a
nonzero value and carries its prime content (`Re s ≥ 1`) ξ has no zeros, and where ξ's zeros live
(the strip) every finite prime atlas is a unit. The prime content and the divisor never share a
point in ℂ; the only object linking them is the `P → ∞` limit — analytic continuation across the
wall — which is a flow, not a pinned constraint.

The weld cross-term is closed too. The archimedean factor `π^(−s/2)·Γ(s/2)` — the `∂_s` side — is
also a unit at every strip point (`archimedeanFactor_orderAt_zero`), so the completed finite local
factor `archimedeanFactor · eulerPartial P`, the `∂_s × {σ_p}` weld in finite form, has order `0`
there (`completed_local_factor_orderAt_zero`). No finite piece of the completed Euler–Γ product —
prime side, archimedean side, or their weld — sources a divisor atom at a pinned strip point.
-/
import GaloisForLFunctions.RHTower.EulerTruncationRigidity

noncomputable section

namespace RHTower

open Complex Finset

/-! ### §1 Each finite prime layer is a unit at every strip point (order 0) -/

/-- A single local Euler factor `(1 − p^(−s))⁻¹` has vanishing analytic order at every point of the
right half-plane: it is a unit there, so it carries no divisor atom. -/
theorem eulerInvFactor_orderAt_zero {p : ℕ} (hp : 2 ≤ p) {ρ : ℂ} (hs : 0 < ρ.re) :
    analyticOrderAt (fun z => (1 - (p : ℂ) ^ (-z))⁻¹) ρ = 0 :=
  (AnalyticAt.analyticOrderAt_eq_zero (eulerInvFactor_analyticAt hp hs)).mpr
    (inv_ne_zero (eulerFactor_ne_zero hp hs))

/-- **Every finite prime atlas has vanishing order at every strip point.**  The finite multiplicative
truncation `eulerPartial P` is analytic and nonvanishing on the whole right half-plane, so its
`analyticOrderAt` is `0` there — it contributes nothing to the ξ-divisor at any point of the strip,
the wall, or beyond. -/
theorem eulerPartial_orderAt_zero {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) {ρ : ℂ} (hs : 0 < ρ.re) :
    analyticOrderAt (eulerPartial P) ρ = 0 :=
  (AnalyticAt.analyticOrderAt_eq_zero (eulerPartial_analyticAt hP hs)).mpr
    (eulerPartial_ne_zero hP hs)

/-- **The finite prime atlas has no zeros in the right half-plane at all.**  Its zero set on
`Re s > 0` is empty: the argument-principle count of any finite prime atlas around any strip loop is
`0`.  The zeros of ζ are emergent in the `P → ∞` limit, present at no finite level. -/
theorem eulerPartial_zeroSet_eq_empty {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) :
    {s : ℂ | 0 < s.re ∧ eulerPartial P s = 0} = ∅ := by
  ext s
  simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false, not_and]
  exact fun hs => eulerPartial_ne_zero hP hs

/-! ### §2 The divisor is prime-invisible -/

/-- **Multiplying ξ by any finite prime atlas leaves the divisor unchanged.**  Since the atlas has
order `0` at ρ, the order of `xi · eulerPartial P` equals that of ξ: the prime layers are invisible
to the ξ-divisor.  No finite set of primes accounts for any part of the multiplicity. -/
theorem xi_divisor_prime_invisible {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) {ρ : ℂ} (hs : 0 < ρ.re) :
    analyticOrderAt (xi * eulerPartial P) ρ = analyticOrderAt xi ρ := by
  have hxi : AnalyticAt ℂ xi ρ := (xi_analyticOnNhd Set.univ) ρ (Set.mem_univ ρ)
  have hep : AnalyticAt ℂ (eulerPartial P) ρ := eulerPartial_analyticAt hP hs
  rw [analyticOrderAt_mul hxi hep, eulerPartial_orderAt_zero hP hs, add_zero]

/-- The order of ξ at any of its zeros is nonzero. -/
theorem xi_zero_order_ne_zero {ρ : ℂ} (hz : xi ρ = 0) : analyticOrderAt xi ρ ≠ 0 :=
  analyticOrderAt_ne_zero.mpr ⟨(xi_analyticOnNhd Set.univ) ρ (Set.mem_univ ρ), hz⟩

/-- **The prime grading detects none of the multiplicity.**  At a strip zero of ξ the prime-atlas
order is `0` while the ξ-order is nonzero: no finite `{σ_p}`-graded piece of the divisor is nonempty,
so no such grading can be finer than — or even see — the multiplicity. -/
theorem no_sigma_graded_refinement {ρ : ℂ} (hs : 0 < ρ.re) (hz : xi ρ = 0)
    {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) :
    analyticOrderAt (eulerPartial P) ρ = 0 ∧ analyticOrderAt xi ρ ≠ 0 :=
  ⟨eulerPartial_orderAt_zero hP hs, xi_zero_order_ne_zero hz⟩

/-! ### §3 The source map from `{σ_p}` into local divisor atoms is the zero map -/

/-- A `{σ_p}`-source map into the local divisor atoms at ρ: for each prime `p`, a count `A p` of
atoms sourced by `p`, realized as zeros of that prime's own local factor `(1 − p^(−s))⁻¹` (so the
count is bounded by the factor's local order).  This is the non-flow, non-character, non-positivity
form of the map — it reads only the primes' own analytic content at the pinned point ρ. -/
def SigmaSourceMap (A : ℕ → ℕ) (ρ : ℂ) : Prop :=
  ∀ p, 2 ≤ p → (A p : ℕ∞) ≤ analyticOrderAt (fun z => (1 - (p : ℂ) ^ (-z))⁻¹) ρ

/-- The zero prime-source map always inhabits the pinned source interface. -/
theorem sigmaSourceMap_zero (ρ : ℂ) : SigmaSourceMap (fun _ => 0) ρ := by
  intro p hp
  simp

/-- **Every `{σ_p}`-source map is the zero map at a pinned strip point.**  Each local Euler factor
is a unit (order `0`), so a count bounded by its local order is forced to `0` for every prime.  The
primes' own analytic content sources no divisor atom anywhere on `Re s > 0`. -/
theorem sigma_source_map_trivial {A : ℕ → ℕ} {ρ : ℂ} (hs : 0 < ρ.re)
    (hA : SigmaSourceMap A ρ) : ∀ p, 2 ≤ p → A p = 0 := by
  intro p hp
  have h0 := eulerInvFactor_orderAt_zero hp hs
  have hle := hA p hp
  rw [h0] at hle
  have : (A p : ℕ∞) = 0 := LE.le.eq_zero hle
  exact_mod_cast this

/-- On the positive half-plane, the pinned prime-source interface is equivalent to being the zero
map on every prime index.  Thus its existence is nonvacuous but its image is completely classified. -/
theorem sigmaSourceMap_iff_eq_zero_on_primes {A : ℕ → ℕ} {ρ : ℂ} (hs : 0 < ρ.re) :
    SigmaSourceMap A ρ ↔ ∀ p, 2 ≤ p → A p = 0 := by
  constructor
  · exact sigma_source_map_trivial hs
  · intro hzero p hp
    rw [hzero p hp]
    simp

/-- **The atom-source mismatch at a strip zero.**  At a point `ρ` where `ξ` vanishes:

* the additive Euler–Maclaurin carrier resolves the order-`m` zero into `zs.length = m ≥ 1`
  hole-atoms (`emSplit_length_pos_at_xi_zero`);
* every `{σ_p}`-source map contributes `A p = 0` atoms for every prime.

The multiplicative (prime) side sources **zero** divisor atoms exactly where the additive side
sources `m ≥ 1`.  The source map from `{σ_p}` into local divisor atoms is the zero map on the
divisor. -/
theorem source_atom_mismatch {ρ : ℂ} (hs : 0 < ρ.re) (hz : xi ρ = 0)
    {A : ℕ → ℕ} (hA : SigmaSourceMap A ρ)
    {r₀ R : ℝ} {N : ℕ} {zs : List ℂ} {u : ℂ → ℂ} (hdata : EMSplitData ρ r₀ R N zs u) :
    (∀ p, 2 ≤ p → A p = 0) ∧ 1 ≤ zs.length :=
  ⟨sigma_source_map_trivial hs hA, emSplit_length_pos_at_xi_zero hz hdata⟩

/-! ### §4 Disjoint carriers: prime content and the divisor never share a point -/

/-- **The prime content and the ξ-divisor have disjoint carriers.**

* On `Re s ≥ 1`, where the Euler product converges to a nonzero value and carries its prime content,
  `ξ` has no zeros.
* On the strip, where `ξ`'s zeros live, every finite prime atlas is a unit (order `0`).

No point of ℂ carries both nonzero prime content and a ξ-zero.  The only object linking the two is
the `P → ∞` limit — analytic continuation across the wall `Re s = 1` — which is a flow, not a
pinned constraint; a source map built from it is not of the pinned form `SigmaSourceMap`. -/
theorem prime_content_and_divisor_disjoint {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p) :
    (∀ ρ : ℂ, 1 ≤ ρ.re → xi ρ ≠ 0) ∧
      (∀ ρ : ℂ, 0 < ρ.re → analyticOrderAt (eulerPartial P) ρ = 0) :=
  ⟨fun _ h1 => xi_ne_zero_of_one_le_re h1, fun _ hs => eulerPartial_orderAt_zero hP hs⟩

/-! ### §5 The weld cross-term: the archimedean factor is a unit too -/

/-- The archimedean factor `π^(−s/2) · Γ(s/2)` of the completed ζ — the `∂_s` side of the weld. -/
def archimedeanFactor : ℂ → ℂ := Complex.Gammaℝ

/-- The archimedean factor is nonvanishing on the right half-plane: `π^(−s/2)` never vanishes and
`Γ(s/2)` has its poles only at `s/2 ∈ {0, −1, −2, …}`, all with nonpositive real part. -/
theorem archimedeanFactor_ne_zero {ρ : ℂ} (hs : 0 < ρ.re) : archimedeanFactor ρ ≠ 0 := by
  simpa [archimedeanFactor] using Gammaℝ_ne_zero_of_re_pos hs

/-- The archimedean factor is analytic on the right half-plane (`Γ` has no poles for `Re s > 0`). -/
theorem archimedeanFactor_analyticAt {ρ : ℂ} (hs : 0 < ρ.re) :
    AnalyticAt ℂ archimedeanFactor ρ := by
  simpa [archimedeanFactor] using Gammaℝ_analyticAt (Gammaℝ_ne_zero_of_re_pos hs)

/-- The archimedean factor has vanishing order at every strip point: it too is a unit there. -/
theorem archimedeanFactor_orderAt_zero {ρ : ℂ} (hs : 0 < ρ.re) :
    analyticOrderAt archimedeanFactor ρ = 0 :=
  (AnalyticAt.analyticOrderAt_eq_zero (archimedeanFactor_analyticAt hs)).mpr
    (archimedeanFactor_ne_zero hs)

/-- **The weld cross-term sources no atom either.**  The completed finite local factor —
archimedean factor times a finite prime atlas, the `∂_s × {σ_p}` weld in finite form — has order `0`
at every strip point: a product of units.  No finite piece of the completed Euler–Γ product, of
either side or their weld, sources a divisor atom at a pinned strip point; the zero is emergent only
in the infinite-product limit. -/
theorem completed_local_factor_orderAt_zero {P : Finset ℕ} (hP : ∀ p ∈ P, 2 ≤ p)
    {ρ : ℂ} (hs : 0 < ρ.re) :
    analyticOrderAt (archimedeanFactor * eulerPartial P) ρ = 0 := by
  rw [analyticOrderAt_mul (archimedeanFactor_analyticAt hs) (eulerPartial_analyticAt hP hs),
    archimedeanFactor_orderAt_zero hs, eulerPartial_orderAt_zero hP hs, add_zero]

end RHTower
