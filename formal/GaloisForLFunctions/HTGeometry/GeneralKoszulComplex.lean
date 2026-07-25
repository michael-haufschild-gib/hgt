import GaloisForLFunctions.HTGeometry.StanleyReisnerVertexRelation

/-!
# The general vertex Koszul complex and `d² = 0`

The Koszul differential of an arbitrary commuting family `x : α → S` in a commutative ring `S`, acting
on index-tensors `(Fin p → α) → S` by prepending the contracted index, together with the fact that it
squares to zero for any tensor antisymmetric under (and vanishing on) an equal leading pair.

This is the degree-uniform backbone behind the concrete differentials `srKoszulBoundary, …,
srKoszulBoundary5` and their pairwise `d² = 0` laws: it exhibits the vertex Koszul complex as a genuine
chain complex at every degree, so `Tor` is well-defined throughout.  The single cancellation is the
`(k,l) ↔ (l,k)` involution against the symmetric coefficient products, exactly as in each concrete
degree, reduced to one general statement via the leading-pair swap identity `cons_cons_comp_swap`.
-/

namespace GaloisForLFunctions.HTGeometry

open Equiv

noncomputable section

variable {α S : Type*} [DecidableEq α] [Fintype α] [CommRing S]

omit [DecidableEq α] [Fintype α] in
/-- **Leading-pair swap identity.**  A double `Fin.cons` with its two prepended entries exchanged
equals the original precomposed with the transposition of positions `0` and `1`. -/
theorem cons_cons_comp_swap {p : ℕ} (u : Fin p → α) (k l : α) :
    Fin.cons k (Fin.cons l u) = (Fin.cons l (Fin.cons k u)) ∘ Equiv.swap (0 : Fin (p + 2)) 1 := by
  funext i
  refine Fin.cases ?_ (fun j => ?_) i
  · simp [Equiv.swap_apply_left]
  · refine Fin.cases ?_ (fun j' => ?_) j
    · simp [Equiv.swap_apply_right]
    · have h0 : (j'.succ.succ : Fin (p + 2)) ≠ 0 := Fin.succ_ne_zero _
      have h1 : (j'.succ.succ : Fin (p + 2)) ≠ 1 := by simp [Fin.ext_iff, Fin.val_succ]
      simp [Equiv.swap_apply_of_ne_of_ne h0 h1, Fin.cons_succ]

/-- The general Koszul differential of a commuting family `x`, prepending the contracted index:
`d(b)(w) = ∑_k b(k ∷ w) · x_k`. -/
def koszulD {p : ℕ} (x : α → S) (b : (Fin (p + 1) → α) → S) (w : Fin p → α) : S :=
  ∑ k, b (Fin.cons k w) * x k

omit [DecidableEq α] in
/-- **`d² = 0` for the general vertex Koszul complex.**  For any commuting family `x` and any tensor
`b` antisymmetric under, and vanishing on, an equal leading pair, the Koszul differential squares to
zero, so `Tor` is a well-defined subquotient at every degree.  The composite
`∑_{k,l} b(l ∷ k ∷ u) · x_l x_k` cancels by the `(k,l) ↔ (l,k)` involution: the leading-pair swap
identity converts the antisymmetry into the required sign, and the diagonal vanishes on the equal
leading pair — unconditionally, in every characteristic. -/
theorem koszulD_koszulD_eq_zero {p : ℕ} (x : α → S) (b : (Fin (p + 2) → α) → S)
    (hswap : ∀ v : Fin (p + 2) → α, b (v ∘ Equiv.swap 0 1) = - b v)
    (hdiag : ∀ v : Fin (p + 2) → α, v 0 = v 1 → b v = 0) :
    koszulD x (koszulD x b) = 0 := by
  funext u
  simp only [Pi.zero_apply, koszulD, Finset.sum_mul]
  rw [← Finset.sum_product']
  refine antisym_prod_sum_zero (fun k l => b (Fin.cons l (Fin.cons k u)) * x l * x k) ?_ ?_
  · intro k l
    show b (Fin.cons l (Fin.cons k u)) * x l * x k + b (Fin.cons k (Fin.cons l u)) * x k * x l = 0
    rw [cons_cons_comp_swap u k l, hswap]; ring
  · intro k
    have hz : b (Fin.cons k (Fin.cons k u)) = 0 := by
      apply hdiag
      rw [Fin.cons_zero, show (1 : Fin (p + 2)) = Fin.succ 0 from rfl, Fin.cons_succ, Fin.cons_zero]
    show b (Fin.cons k (Fin.cons k u)) * x k * x k = 0
    rw [hz]; ring

/-- A single-entry index-tensor: value `r` at the tuple `v₀`, zero at every other tuple. -/
def koszulSingleEntry {p : ℕ} (v₀ : Fin (p + 1) → α) (r : S) : (Fin (p + 1) → α) → S :=
  fun v => if v = v₀ then r else 0

/-- **General single-entry Koszul cycle criterion.**  A one-entry tensor `r · [v = v₀]` is a Koszul
cycle exactly when its value times the leading coordinate of its slot vanishes — every boundary term
sits at the truncated tuple and reads off `r · x_{v₀ 0}`.  This is the degree-uniform form of the
concrete single-edge/triple/tuple cycles `srSquareEdgeCycle, srPentTripleCycle, srHexTupleCycle`, whose
`r · x_{v₀ 0}` is an absent-diagonal product. -/
theorem koszulD_koszulSingleEntry_eq_zero {p : ℕ} (x : α → S) (v₀ : Fin (p + 1) → α) (r : S)
    (h : r * x (v₀ 0) = 0) :
    koszulD x (koszulSingleEntry v₀ r) = 0 := by
  funext w
  simp only [Pi.zero_apply, koszulD, koszulSingleEntry]
  by_cases hw : w = Fin.tail v₀
  · subst hw
    rw [Finset.sum_eq_single (v₀ 0)
        (fun k _ hk => by rw [if_neg (fun hc => hk (by simpa using congrFun hc 0)), zero_mul])
        (fun hc => absurd (Finset.mem_univ _) hc),
      if_pos (Fin.cons_self_tail v₀)]
    exact h
  · refine Finset.sum_eq_zero (fun k _ => ?_)
    rw [if_neg (fun hc => hw (by rw [← hc, Fin.tail_cons])), zero_mul]

omit [DecidableEq α] [Fintype α] [CommRing S] in
/-- **Prepend-shift of a transposition.**  Prepending an entry conjugates a positional transposition
by the successor shift: `k ∷ (v ∘ swap i j) = (k ∷ v) ∘ swap i⁺ j⁺`. -/
theorem cons_comp_swap {p : ℕ} (v : Fin p → α) (k : α) (i j : Fin p) :
    Fin.cons k (v ∘ Equiv.swap i j) = (Fin.cons k v) ∘ Equiv.swap i.succ j.succ := by
  funext m
  refine Fin.cases ?_ (fun m' => ?_) m
  · simp [Equiv.swap_apply_of_ne_of_ne (Fin.succ_ne_zero i).symm (Fin.succ_ne_zero j).symm]
  · simp only [Function.comp_apply, Fin.cons_succ]
    rw [show Equiv.swap i.succ j.succ m'.succ = (Equiv.swap i j m').succ from
      ((Fin.succ_injective p).map_swap i j m').symm, Fin.cons_succ]

/-- An alternating index-tensor: sign-reversing under every positional transposition and vanishing on
non-injective tuples (a repeated index). -/
structure IsAltTensor {p : ℕ} (b : (Fin p → α) → S) : Prop where
  swap_neg : ∀ (v : Fin p → α) (i j : Fin p), i ≠ j → b (v ∘ Equiv.swap i j) = - b v
  zero_of_not_injective : ∀ v : Fin p → α, ¬ Function.Injective v → b v = 0

omit [DecidableEq α] in
/-- **The Koszul differential preserves alternation.**  `koszulD x b` is again alternating: prepending
conjugates each transposition (`cons_comp_swap`), transporting the sign, and a repeated index in the
base tuple survives the prepend, transporting the vanishing. -/
theorem koszulD_isAltTensor {p : ℕ} (x : α → S) {b : (Fin (p + 1) → α) → S}
    (hb : IsAltTensor b) : IsAltTensor (koszulD x b) where
  swap_neg w i j hij := by
    refine eq_neg_of_add_eq_zero_left ?_
    simp only [koszulD, ← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => ?_
    rw [cons_comp_swap w k i j,
      hb.swap_neg (Fin.cons k w) i.succ j.succ (fun h => hij (Fin.succ_injective p h))]; ring
  zero_of_not_injective w hw := by
    simp only [koszulD]
    refine Finset.sum_eq_zero fun k _ => ?_
    obtain ⟨a, c, hac, hne⟩ := Function.not_injective_iff.mp hw
    rw [hb.zero_of_not_injective (Fin.cons k w)
      (fun hinj => hne (Fin.succ_injective p
        (hinj (by simp only [Fin.cons_succ]; exact hac)))), zero_mul]

omit [DecidableEq α] in
/-- **`d² = 0` on the alternating Koszul complex.**  For an alternating tensor the leading-pair
hypotheses of `koszulD_koszulD_eq_zero` hold automatically, so the differential squares to zero — the
general vertex Koszul complex is a genuine chain complex on alternating tensors, `Tor` well-defined at
every degree. -/
theorem koszulD_koszulD_eq_zero_of_isAltTensor {p : ℕ} (x : α → S)
    {b : (Fin (p + 2) → α) → S} (hb : IsAltTensor b) :
    koszulD x (koszulD x b) = 0 :=
  koszulD_koszulD_eq_zero x b
    (fun v => hb.swap_neg v 0 1 Fin.zero_ne_one)
    (fun v hv => hb.zero_of_not_injective v (fun hinj => Fin.zero_ne_one (hinj hv)))

/-- The Koszul differential packaged as an `S`-linear map on index-tensors. -/
def koszulDₗ {p : ℕ} (x : α → S) : ((Fin (p + 1) → α) → S) →ₗ[S] ((Fin p → α) → S) where
  toFun := koszulD x
  map_add' b₁ b₂ := by
    funext w; simp only [koszulD, Pi.add_apply, add_mul, Finset.sum_add_distrib]
  map_smul' s b := by
    funext w
    simp only [koszulD, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

/-- The alternating index-tensors form an `S`-submodule of all index-tensors — the carrier of the
Koszul complex on which `Tor` is taken. -/
def koszulAltTensors (p : ℕ) : Submodule S ((Fin p → α) → S) where
  carrier := {b | IsAltTensor b}
  zero_mem' := ⟨fun _ _ _ _ => by simp, fun _ _ => by simp⟩
  add_mem' {b₁ b₂} h₁ h₂ :=
    ⟨fun v i j hij => by
      simp only [Pi.add_apply]; rw [h₁.swap_neg v i j hij, h₂.swap_neg v i j hij]; ring,
     fun v hv => by
      simp only [Pi.add_apply]; rw [h₁.zero_of_not_injective v hv, h₂.zero_of_not_injective v hv,
        add_zero]⟩
  smul_mem' s b hb :=
    ⟨fun v i j hij => by
      simp only [Pi.smul_apply, smul_eq_mul]; rw [hb.swap_neg v i j hij]; ring,
     fun v hv => by
      simp only [Pi.smul_apply, smul_eq_mul]; rw [hb.zero_of_not_injective v hv, mul_zero]⟩

omit [DecidableEq α] in
/-- `koszulD` maps alternating tensors into alternating tensors — the differential of the alternating
Koszul complex `koszulAltTensors (p+1) → koszulAltTensors p`. -/
theorem koszulDₗ_mem_koszulAltTensors {p : ℕ} (x : α → S) {b : (Fin (p + 1) → α) → S}
    (hb : b ∈ koszulAltTensors (p + 1)) : koszulDₗ x b ∈ koszulAltTensors p :=
  koszulD_isAltTensor x hb

/-- Degree-`(p+1)` Koszul cycles: alternating tensors killed by the differential. -/
def koszulCycles {p : ℕ} (x : α → S) : Submodule S ((Fin (p + 1) → α) → S) :=
  LinearMap.ker (koszulDₗ x) ⊓ koszulAltTensors (p + 1)

/-- Degree-`(p+1)` Koszul boundaries: the image of the alternating `(p+2)`-tensors. -/
def koszulBoundaries {p : ℕ} (x : α → S) : Submodule S ((Fin (p + 1) → α) → S) :=
  Submodule.map (koszulDₗ x) (koszulAltTensors (p + 2))

omit [DecidableEq α] in
/-- **Boundaries are cycles.**  Every Koszul boundary is a Koszul cycle: it is alternating
(`koszulD_isAltTensor`) and killed by the next differential (`d²=0`), so the Koszul homology
`koszulCycles ⧸ koszulBoundaries` is a well-defined subquotient `S`-module at every degree. -/
theorem koszulBoundaries_le_koszulCycles {p : ℕ} (x : α → S) :
    koszulBoundaries x ≤ koszulCycles (p := p) x := by
  rintro _ ⟨c, hc, rfl⟩
  exact ⟨koszulD_koszulD_eq_zero_of_isAltTensor x hc, koszulD_isAltTensor x hc⟩

/-- The degree-`(p+1)` Koszul homology of the commuting family `x`: cycles modulo boundaries, a
well-defined `S`-module (`koszulBoundaries_le_koszulCycles`).  This is the general vertex-Koszul `Tor`,
whose graded pieces Hochster's formula identifies with reduced simplicial cohomology. -/
abbrev koszulTor {p : ℕ} (x : α → S) : Type _ :=
  koszulCycles (p := p) x ⧸ (koszulBoundaries x).comap (koszulCycles x).subtype

omit [DecidableEq α] in
/-- **A cycle represents a nonzero `Tor` class iff it is not a boundary.**  The class of a Koszul cycle
`z` in the homology `koszulTor` is nonzero exactly when `z` fails to be a Koszul boundary — the module
statement behind every concrete non-boundary theorem. -/
theorem koszulTor_mk_ne_zero {p : ℕ} (x : α → S) (z : koszulCycles (p := p) x)
    (hz : (z : (Fin (p + 1) → α) → S) ∉ koszulBoundaries x) :
    Submodule.Quotient.mk z ≠ (0 : koszulTor x) := by
  rw [Ne, Submodule.Quotient.mk_eq_zero]
  exact fun h => hz (Submodule.mem_comap.mp h)

omit [DecidableEq α] in
/-- **Degree-one bridge to the concrete Stanley–Reisner Koszul relation.**  Over the Stanley–Reisner
ring, with the vertex coordinates as the commuting family, the general Koszul differential in degree
one is exactly the concrete first Koszul relation `∑_v a_v x_v` — the two conventions coincide where
there are no index pairs to antisymmetrize. -/
theorem koszulD_srVertexX_eq_srKoszulRelation {R : Type*} [CommRing R] (facets : Finset (Finset α))
    (a : (Fin 1 → α) → stanleyReisnerRing R facets) (w : Fin 0 → α) :
    koszulD (srVertexX R facets) a w = srKoszulRelation facets (fun v => a (fun _ => v)) := by
  simp only [koszulD, srKoszulRelation]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 2
  funext i
  fin_cases i
  simp [Fin.cons_zero]

/-- The antisymmetrization of an index-tensor: `∑_σ sign(σ) • t(· ∘ σ)`. -/
def koszulAlt {p : ℕ} (t : (Fin p → α) → S) (v : Fin p → α) : S :=
  ∑ σ : Equiv.Perm (Fin p), (Equiv.Perm.sign σ : ℤ) • t (v ∘ σ)

omit [DecidableEq α] [Fintype α] in
/-- **The antisymmetrization is always alternating.**  `koszulAlt t` is an alternating tensor: sign
reversal follows from reindexing the permutation sum by a transposition, and vanishing on a repeated
index from the fixed-point-free involution `σ ↦ (i j)·σ` pairing off equal contributions.  This turns
any tensor into an alternating one — the source of alternating Koszul cycles at every degree. -/
theorem koszulAlt_isAltTensor {p : ℕ} (t : (Fin p → α) → S) : IsAltTensor (koszulAlt t) := by
  refine ⟨fun v i j hij => ?_, fun v hv => ?_⟩
  · have hreindex : koszulAlt t v
        = ∑ σ : Equiv.Perm (Fin p),
          (Equiv.Perm.sign (Equiv.swap i j * σ) : ℤ) • t (v ∘ ⇑(Equiv.swap i j * σ)) :=
      (Fintype.sum_bijective (Equiv.swap i j * ·) (Group.mulLeft_bijective _)
        (fun σ => (Equiv.Perm.sign (Equiv.swap i j * σ) : ℤ) • t (v ∘ ⇑(Equiv.swap i j * σ)))
        (fun σ => (Equiv.Perm.sign σ : ℤ) • t (v ∘ ⇑σ)) (fun _ => rfl)).symm
    rw [koszulAlt, hreindex]
    refine eq_neg_of_add_eq_zero_left ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun σ _ => ?_
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij, Equiv.Perm.coe_mul, ← Function.comp_assoc]
    push_cast
    rw [neg_one_mul, neg_smul, add_neg_cancel]
  · obtain ⟨i, j, hveq, hij⟩ := Function.not_injective_iff.mp hv
    have hvswap : v ∘ ⇑(Equiv.swap i j) = v := by
      funext x
      rcases eq_or_ne x i with rfl | hxi
      · simp [Equiv.swap_apply_left, hveq]
      · rcases eq_or_ne x j with rfl | hxj
        · simp [Equiv.swap_apply_right, hveq]
        · simp [Equiv.swap_apply_of_ne_of_ne hxi hxj]
    simp only [koszulAlt]
    apply Finset.sum_involution (fun σ _ => Equiv.swap i j * σ)
    · intro σ _
      rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hij, Equiv.Perm.coe_mul,
        ← Function.comp_assoc, hvswap]
      push_cast
      rw [neg_one_mul, neg_smul, add_neg_cancel]
    · intro σ _ _ hcon
      have h1 : Equiv.swap i j = 1 := mul_right_cancel (hcon.trans (one_mul σ).symm)
      have h2 : Equiv.swap i j i = i := by rw [h1]; rfl
      rw [Equiv.swap_apply_left] at h2
      exact hij h2.symm
    · intro σ _; exact Finset.mem_univ _
    · intro σ _
      rw [← mul_assoc, Equiv.swap_mul_self, one_mul]

omit [DecidableEq α] [Fintype α] in
/-- **Degree-two antisymmetrization formula.**  Over `Perm (Fin 2) = {1, (0 1)}`, the antisymmetrization
is `koszulAlt t = t - t(· ∘ (0 1))`. -/
theorem koszulAlt_two_apply (t : (Fin 2 → α) → S) (v : Fin 2 → α) :
    koszulAlt t v = t v - t (v ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) := by
  rw [koszulAlt,
    show (Finset.univ : Finset (Equiv.Perm (Fin 2))) = {1, Equiv.swap 0 1} from by decide,
    Finset.sum_pair (by decide), Equiv.Perm.sign_one,
    Equiv.Perm.sign_swap (show (0 : Fin 2) ≠ 1 by decide)]
  simp [sub_eq_add_neg]

omit [DecidableEq α] [Fintype α] in
/-- **Alternating tensors transform by the sign under any permutation.**  `b(v ∘ σ) = sign(σ) • b(v)`
for every permutation `σ`, by induction on `σ` as a product of transpositions (`swap_neg`). -/
theorem IsAltTensor.comp_perm {p : ℕ} {b : (Fin p → α) → S} (hb : IsAltTensor b)
    (σ : Equiv.Perm (Fin p)) (v : Fin p → α) :
    b (v ∘ ⇑σ) = (Equiv.Perm.sign σ : ℤ) • b v := by
  revert v
  refine Equiv.Perm.swap_induction_on σ (fun v => by simp) (fun f x y hxy ih v => ?_)
  rw [Equiv.Perm.coe_mul, ← Function.comp_assoc, ih (v ∘ ⇑(Equiv.swap x y)), hb.swap_neg v x y hxy,
    Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hxy]
  push_cast
  rw [smul_neg, neg_one_mul, neg_smul]

section SRC4

variable {R : Type*} [CommRing R]

/-- The degree-two `C₄` cycle over the Stanley–Reisner ring: the antisymmetrized single edge
`koszulAlt (koszulSingleEntry ![a,b] (x_c x_d))`, alternating for free by `koszulAlt_isAltTensor`. -/
noncomputable def srC4KoszulCycle (facets : Finset (Finset α)) (a b c d : α) :
    (Fin 2 → α) → stanleyReisnerRing R facets :=
  koszulAlt (koszulSingleEntry ![a, b] (srVertexX R facets c * srVertexX R facets d))

omit [Fintype α] in
/-- The antisymmetrized single edge is the two-entry alternating tensor `x_c x_d` at `![a,b]`,
`−x_c x_d` at `![b,a]` (degree-two antisymmetrization + the leading-pair swap of the tuple). -/
theorem srC4KoszulCycle_eq (facets : Finset (Finset α)) {a b c d : α} :
    srC4KoszulCycle facets a b c d
      = koszulSingleEntry ![a, b] (srVertexX R facets c * srVertexX R facets d)
        - koszulSingleEntry ![b, a] (srVertexX R facets c * srVertexX R facets d) := by
  funext v
  have hab_swap : (![a, b] : Fin 2 → α) ∘ ⇑(Equiv.swap (0 : Fin 2) 1) = ![b, a] := by
    funext i; fin_cases i <;> simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  have hba_swap : (![b, a] : Fin 2 → α) ∘ ⇑(Equiv.swap (0 : Fin 2) 1) = ![a, b] := by
    funext i; fin_cases i <;> simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
  have h2 : (v ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) ∘ ⇑(Equiv.swap 0 1) = v := by
    rw [Function.comp_assoc, ← Equiv.Perm.coe_mul, Equiv.swap_mul_self, Equiv.Perm.coe_one,
      Function.comp_id]
  rw [srC4KoszulCycle, koszulAlt_two_apply, Pi.sub_apply]
  congr 1
  simp only [koszulSingleEntry]
  refine if_congr ⟨fun h => ?_, fun h => ?_⟩ rfl rfl
  · calc v = (v ∘ ⇑(Equiv.swap (0 : Fin 2) 1)) ∘ ⇑(Equiv.swap 0 1) := h2.symm
      _ = ![a, b] ∘ ⇑(Equiv.swap 0 1) := by rw [h]
      _ = ![b, a] := hab_swap
  · rw [h]; exact hba_swap

/-- **The `C₄` edge cycle is a Koszul cycle.**  Its two boundary terms carry the absent diagonals
`x_a x_c` (from the `![a,b]` entry) and `x_b x_d` (from the `![b,a]` entry), both zero. -/
theorem koszulD_srC4KoszulCycle (facets : Finset (Finset α)) {a b c d : α}
    (hac : a ≠ c) (hac_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {a, c})
    (hbd : b ≠ d) (hbd_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {b, d}) :
    koszulD (srVertexX R facets) (srC4KoszulCycle facets a b c d) = 0 := by
  have hab0 : srVertexX R facets c * srVertexX R facets d * srVertexX R facets a = 0 := by
    linear_combination srVertexX R facets d *
      srVertexX_mul_eq_zero_of_not_isFace (R := R) facets hac hac_nf
  have hba0 : srVertexX R facets c * srVertexX R facets d * srVertexX R facets b = 0 := by
    linear_combination srVertexX R facets c *
      srVertexX_mul_eq_zero_of_not_isFace (R := R) facets hbd hbd_nf
  have e1 : koszulD (srVertexX R facets)
      (koszulSingleEntry ![a, b] (srVertexX R facets c * srVertexX R facets d)) = 0 :=
    koszulD_koszulSingleEntry_eq_zero (srVertexX R facets) ![a, b] _ hab0
  have e2 : koszulD (srVertexX R facets)
      (koszulSingleEntry ![b, a] (srVertexX R facets c * srVertexX R facets d)) = 0 :=
    koszulD_koszulSingleEntry_eq_zero (srVertexX R facets) ![b, a] _ hba0
  rw [srC4KoszulCycle_eq]
  show koszulDₗ (srVertexX R facets) (_ - _) = 0
  rw [map_sub]
  show koszulD (srVertexX R facets) _ - koszulD (srVertexX R facets) _ = 0
  rw [e1, e2, sub_zero]

/-- The `C₄` edge cycle lies in the degree-two Koszul cycles: alternating (`koszulAlt_isAltTensor`) and
killed by the differential. -/
theorem srC4KoszulCycle_mem_koszulCycles (facets : Finset (Finset α)) {a b c d : α}
    (hac : a ≠ c) (hac_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {a, c})
    (hbd : b ≠ d) (hbd_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {b, d}) :
    srC4KoszulCycle facets a b c d ∈ koszulCycles (srVertexX R facets) :=
  ⟨koszulD_srC4KoszulCycle facets hac hac_nf hbd hbd_nf, koszulAlt_isAltTensor _⟩

/-- **Pair detector of a `koszulD`-entry over the Stanley–Reisner ring.**  Reading the `x_u x_v`
coefficient of `koszulD(b)(w) = ∑_k b(k ∷ w) x_k` collapses to the two degree-one detectors of the
prepended slots. -/
theorem srPairDetector_koszulD {p : ℕ} (facets : Finset (Finset α)) {u v : α} (huv : u ≠ v)
    (hf : IsFaceOf (↑facets : Set (Finset α)) {u, v})
    (hu : IsFaceOf (↑facets : Set (Finset α)) {u}) (hv : IsFaceOf (↑facets : Set (Finset α)) {v})
    (b : (Fin (p + 1) → α) → stanleyReisnerRing R facets) (w : Fin p → α) :
    srPairDetector R facets u v huv hf (koszulD (srVertexX R facets) b w)
      = srH0Detector R facets v hv (b (Fin.cons u w))
        + srH0Detector R facets u hu (b (Fin.cons v w)) := by
  rw [koszulD, map_sum,
    Finset.sum_congr rfl (fun k _ =>
      srPairDetector_mul_srVertexX facets huv hf hu hv (b (Fin.cons k w))),
    Finset.sum_congr rfl (fun k _ => show
      (if k = u then srH0Detector R facets v hv (b (Fin.cons k w))
        else if k = v then srH0Detector R facets u hu (b (Fin.cons k w)) else 0)
      = (if k = u then srH0Detector R facets v hv (b (Fin.cons k w)) else 0)
        + (if k = v then srH0Detector R facets u hu (b (Fin.cons k w)) else 0) from by
      by_cases hku : k = u
      · subst hku; simp [huv]
      · by_cases hkv : k = v
        · subst hkv; simp [hku]
        · simp [hku, hkv]),
    Finset.sum_add_distrib, Finset.sum_ite_eq' Finset.univ u, Finset.sum_ite_eq' Finset.univ v]
  simp

/-- **The `C₄` edge cycle is a nonzero `Tor₂` class in the general framework.**  `srC4KoszulCycle` is
not a `koszulD`-boundary of any alternating 3-tensor, in every characteristic.  The edge detector
`Φ(t) = +{cd}∘t_{ab} − {ad}∘t_{bc} + {ab}∘t_{cd} − {bc}∘t_{da}` reads the cycle as `1` (from
`srC4KoszulCycle_eq`) and every boundary as `0`: the eight degree-one detector terms pair off by the
even-`3`-cycle permutation invariance of the alternating coefficient (`comp_perm`). -/
theorem srC4KoszulCycle_not_mem_koszulBoundaries [Nontrivial R] (facets : Finset (Finset α))
    {a b c d : α} (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (had : a ≠ d) (hac : a ≠ c) (hbd : b ≠ d)
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (hd : IsFaceOf (↑facets : Set (Finset α)) {d})
    (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (had_f : IsFaceOf (↑facets : Set (Finset α)) {a, d}) :
    srC4KoszulCycle facets a b c d ∉ koszulBoundaries (srVertexX R facets) := by
  rintro ⟨b3, hb3, heq⟩
  have heq' : koszulD (srVertexX R facets) b3 = srC4KoszulCycle facets a b c d := heq
  set Φ : ((Fin 2 → α) → stanleyReisnerRing R facets) → R := fun t =>
    srPairDetector R facets c d hcd hcd_f (t ![a, b])
      - srPairDetector R facets a d had had_f (t ![b, c])
      + srPairDetector R facets a b hab hab_f (t ![c, d])
      - srPairDetector R facets b c hbc hbc_f (t ![d, a]) with hΦ
  have hone : Φ (srC4KoszulCycle facets a b c d) = 1 := by
    have e0 : srC4KoszulCycle facets a b c d ![a, b]
        = srVertexX R facets c * srVertexX R facets d := by
      rw [srC4KoszulCycle_eq]; simp only [Pi.sub_apply, koszulSingleEntry, if_true]
      rw [if_neg fun h => hab (congrFun h 0), sub_zero]
    have e1 : srC4KoszulCycle facets a b c d ![b, c] = (0 : stanleyReisnerRing R facets) := by
      rw [srC4KoszulCycle_eq]; simp only [Pi.sub_apply, koszulSingleEntry]
      rw [if_neg fun h => hab (congrFun h 0).symm, if_neg fun h => hac (congrFun h 1).symm, sub_zero]
    have e2 : srC4KoszulCycle facets a b c d ![c, d] = (0 : stanleyReisnerRing R facets) := by
      rw [srC4KoszulCycle_eq]; simp only [Pi.sub_apply, koszulSingleEntry]
      rw [if_neg fun h => hac (congrFun h 0).symm, if_neg fun h => hbc (congrFun h 0).symm, sub_zero]
    have e3 : srC4KoszulCycle facets a b c d ![d, a] = (0 : stanleyReisnerRing R facets) := by
      rw [srC4KoszulCycle_eq]; simp only [Pi.sub_apply, koszulSingleEntry]
      rw [if_neg fun h => had (congrFun h 0).symm, if_neg fun h => hbd (congrFun h 0).symm, sub_zero]
    simp only [hΦ, e0, e1, e2, e3, map_zero, sub_zero, add_zero]
    rw [srPairDetector_srVertexX_mul facets hcd hcd_f]
  have hzero : Φ (koszulD (srVertexX R facets) b3) = 0 := by
    have r1 : b3 (Fin.cons c ![a, b]) = b3 (Fin.cons a ![b, c]) := by
      rw [show (Fin.cons c ![a, b] : Fin 3 → α)
          = Fin.cons a ![b, c] ∘ ⇑(Equiv.swap (0 : Fin 3) 1 * Equiv.swap (0 : Fin 3) 2) from by
        funext i; fin_cases i <;>
          simp [Equiv.Perm.coe_mul, Function.comp, Equiv.swap_apply_left, Equiv.swap_apply_right,
            Equiv.swap_apply_of_ne_of_ne, Fin.cons_zero], hb3.comp_perm]
      simp [show Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (0 : Fin 3) 2) = 1 from by decide]
    have r2 : b3 (Fin.cons b ![d, a]) = b3 (Fin.cons d ![a, b]) := by
      rw [show (Fin.cons b ![d, a] : Fin 3 → α)
          = Fin.cons d ![a, b] ∘ ⇑(Equiv.swap (0 : Fin 3) 1 * Equiv.swap (0 : Fin 3) 2) from by
        funext i; fin_cases i <;>
          simp [Equiv.Perm.coe_mul, Function.comp, Equiv.swap_apply_left, Equiv.swap_apply_right,
            Equiv.swap_apply_of_ne_of_ne, Fin.cons_zero], hb3.comp_perm]
      simp [show Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (0 : Fin 3) 2) = 1 from by decide]
    have r3 : b3 (Fin.cons d ![b, c]) = b3 (Fin.cons b ![c, d]) := by
      rw [show (Fin.cons d ![b, c] : Fin 3 → α)
          = Fin.cons b ![c, d] ∘ ⇑(Equiv.swap (0 : Fin 3) 1 * Equiv.swap (0 : Fin 3) 2) from by
        funext i; fin_cases i <;>
          simp [Equiv.Perm.coe_mul, Function.comp, Equiv.swap_apply_left, Equiv.swap_apply_right,
            Equiv.swap_apply_of_ne_of_ne, Fin.cons_zero], hb3.comp_perm]
      simp [show Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 1 * Equiv.swap (0 : Fin 3) 2) = 1 from by decide]
    have r4 : b3 (Fin.cons c ![d, a]) = b3 (Fin.cons a ![c, d]) := by
      rw [show (Fin.cons c ![d, a] : Fin 3 → α)
          = Fin.cons a ![c, d] ∘ ⇑(Equiv.swap (0 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1) from by
        funext i; fin_cases i <;>
          simp [Equiv.Perm.coe_mul, Function.comp, Equiv.swap_apply_left, Equiv.swap_apply_right,
            Equiv.swap_apply_of_ne_of_ne, Fin.cons_zero], hb3.comp_perm]
      simp [show Equiv.Perm.sign (Equiv.swap (0 : Fin 3) 2 * Equiv.swap (0 : Fin 3) 1) = 1 from by decide]
    simp only [hΦ]
    rw [srPairDetector_koszulD facets hcd hcd_f hc hd b3 ![a, b],
        srPairDetector_koszulD facets had had_f ha hd b3 ![b, c],
        srPairDetector_koszulD facets hab hab_f ha hb b3 ![c, d],
        srPairDetector_koszulD facets hbc hbc_f hb hc b3 ![d, a]]
    rw [r1, r2, r3, r4]
    abel
  rw [heq'] at hzero
  rw [hone] at hzero
  exact one_ne_zero hzero

/-- **Nonzero degree-two Koszul homology of `C₄` in the general framework.**  The `C₄` edge cycle
represents a nonzero class in `koszulTor` over the Stanley–Reisner ring — the first higher-degree
nonzero class of the general vertex-Koszul homology, realizing `H̃¹(C₄) = Tor₂`. -/
theorem srC4KoszulTor_ne_zero [Nontrivial R] (facets : Finset (Finset α)) {a b c d : α}
    (hab : a ≠ b) (hbc : b ≠ c) (hcd : c ≠ d) (had : a ≠ d) (hac : a ≠ c) (hbd : b ≠ d)
    (ha : IsFaceOf (↑facets : Set (Finset α)) {a}) (hb : IsFaceOf (↑facets : Set (Finset α)) {b})
    (hc : IsFaceOf (↑facets : Set (Finset α)) {c}) (hd : IsFaceOf (↑facets : Set (Finset α)) {d})
    (hab_f : IsFaceOf (↑facets : Set (Finset α)) {a, b})
    (hbc_f : IsFaceOf (↑facets : Set (Finset α)) {b, c})
    (hcd_f : IsFaceOf (↑facets : Set (Finset α)) {c, d})
    (had_f : IsFaceOf (↑facets : Set (Finset α)) {a, d})
    (hac_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {a, c})
    (hbd_nf : ¬ IsFaceOf (↑facets : Set (Finset α)) {b, d}) :
    Submodule.Quotient.mk (⟨srC4KoszulCycle facets a b c d,
        srC4KoszulCycle_mem_koszulCycles facets hac hac_nf hbd hbd_nf⟩ :
        koszulCycles (srVertexX R facets)) ≠ (0 : koszulTor (srVertexX R facets)) :=
  koszulTor_mk_ne_zero (srVertexX R facets) _
    (srC4KoszulCycle_not_mem_koszulBoundaries facets hab hbc hcd had hac hbd
      ha hb hc hd hab_f hbc_f hcd_f had_f)

end SRC4

section SRDisconnect

variable {R : Type*} [CommRing R]

/-- The degree-one disconnect cycle over the Stanley–Reisner ring: the single-entry tensor of value
`x_w` at the one-tuple `(v₀)`. -/
noncomputable def srDisconnectKoszulCycle (facets : Finset (Finset α)) (v₀ w : α) :
    (Fin 1 → α) → stanleyReisnerRing R facets :=
  koszulSingleEntry (fun _ => v₀) (srVertexX R facets w)

/-- The disconnect cycle is a Koszul cycle: `∑` collapses to `x_w x_{v₀}`, zero on a nonface pair, and
alternation is vacuous in degree one. -/
theorem srDisconnectKoszulCycle_mem_koszulCycles (facets : Finset (Finset α)) {v₀ w : α}
    (hwv : w ≠ v₀) (hnf : ¬ IsFaceOf (↑facets : Set (Finset α)) {w, v₀}) :
    srDisconnectKoszulCycle facets v₀ w ∈ koszulCycles (srVertexX R facets) :=
  ⟨koszulD_koszulSingleEntry_eq_zero (srVertexX R facets) (fun _ => v₀) (srVertexX R facets w)
      (srVertexX_mul_eq_zero_of_not_isFace facets hwv hnf),
    ⟨fun _ i j hij => absurd ((Fin.fin_one_eq_zero i).trans (Fin.fin_one_eq_zero j).symm) hij,
      fun _ hv => absurd (fun a c _ => (Fin.fin_one_eq_zero a).trans (Fin.fin_one_eq_zero c).symm) hv⟩⟩

/-- **The disconnect cycle is not a Koszul boundary.**  The two-point detector
`Φ(t) = srH0Det_w(t(v₀)) + srH0Det_{v₀}(t(w))` reads the cycle as `1`, but every boundary `koszulD b`
(with `b` alternating) as `0`, because the two constant-term readings are `srConstTerm(b_{w,v₀})` and
`srConstTerm(b_{v₀,w}) = −srConstTerm(b_{w,v₀})`. -/
theorem srDisconnectKoszulCycle_not_mem_koszulBoundaries [Nontrivial R] (facets : Finset (Finset α))
    {v₀ w : α} (hwv : w ≠ v₀) (hE : IsFaceOf (↑facets : Set (Finset α)) ∅)
    (hw : IsFaceOf (↑facets : Set (Finset α)) {w}) (hv₀ : IsFaceOf (↑facets : Set (Finset α)) {v₀}) :
    srDisconnectKoszulCycle facets v₀ w ∉ koszulBoundaries (srVertexX R facets) := by
  classical
  rintro ⟨b, hb, heq⟩
  have hΦa : srH0Detector R facets w hw (srDisconnectKoszulCycle facets v₀ w (fun _ => v₀))
      + srH0Detector R facets v₀ hv₀ (srDisconnectKoszulCycle facets v₀ w (fun _ => w)) = 1 := by
    have ha1 : srDisconnectKoszulCycle facets v₀ w (fun _ => v₀) = srVertexX R facets w := by
      simp [srDisconnectKoszulCycle, koszulSingleEntry]
    have ha2 : srDisconnectKoszulCycle facets v₀ w (fun _ => w) = (0 : stanleyReisnerRing R facets) := by
      have hne : (fun _ => w : Fin 1 → α) ≠ fun _ => v₀ :=
        fun h => hwv (congrFun h (0 : Fin 1))
      simp only [srDisconnectKoszulCycle, koszulSingleEntry, if_neg hne]
    rw [ha1, ha2, map_zero, add_zero, srH0Detector_srVertexX facets hw, if_pos rfl]
  have hΦb : srH0Detector R facets w hw (koszulDₗ (srVertexX R facets) b (fun _ => v₀))
      + srH0Detector R facets v₀ hv₀ (koszulDₗ (srVertexX R facets) b (fun _ => w)) = 0 := by
    have e1 : srH0Detector R facets w hw (koszulDₗ (srVertexX R facets) b (fun _ => v₀))
        = srConstTerm R facets hE (b (Fin.cons w (fun _ => v₀))) := by
      show srH0Detector R facets w hw (koszulD (srVertexX R facets) b (fun _ => v₀)) = _
      rw [koszulD, map_sum, Finset.sum_congr rfl (fun k _ =>
        srH0Detector_mul_srVertexX facets hE hw (b (Fin.cons k (fun _ => v₀)))),
        Finset.sum_ite_eq Finset.univ w
          (fun k => srConstTerm R facets hE (b (Fin.cons k (fun _ => v₀)))), if_pos (Finset.mem_univ w)]
    have e2 : srH0Detector R facets v₀ hv₀ (koszulDₗ (srVertexX R facets) b (fun _ => w))
        = srConstTerm R facets hE (b (Fin.cons v₀ (fun _ => w))) := by
      show srH0Detector R facets v₀ hv₀ (koszulD (srVertexX R facets) b (fun _ => w)) = _
      rw [koszulD, map_sum, Finset.sum_congr rfl (fun k _ =>
        srH0Detector_mul_srVertexX facets hE hv₀ (b (Fin.cons k (fun _ => w)))),
        Finset.sum_ite_eq Finset.univ v₀
          (fun k => srConstTerm R facets hE (b (Fin.cons k (fun _ => w)))), if_pos (Finset.mem_univ v₀)]
    rw [e1, e2]
    have hswapid : (Fin.cons v₀ (fun _ => w) : Fin 2 → α)
        = (Fin.cons w (fun _ => v₀)) ∘ Equiv.swap 0 1 := by
      funext i; fin_cases i <;> simp [Equiv.swap_apply_left, Equiv.swap_apply_right]
    rw [hswapid, hb.swap_neg (Fin.cons w (fun _ => v₀)) 0 1 (by decide), map_neg]
    ring
  rw [heq] at hΦb
  exact one_ne_zero (hΦa.symm.trans hΦb)

/-- **The general Koszul `Tor` over a Stanley–Reisner ring is nonzero.**  The disconnect cycle
represents a nonzero class in `koszulTor` — the general vertex-Koszul homology is genuinely nontrivial,
realizing the degree-zero reduced cohomology (`H̃⁰`) of a disconnected pair as an actual `Tor` class. -/
theorem srDisconnectKoszulTor_ne_zero [Nontrivial R] (facets : Finset (Finset α)) {v₀ w : α}
    (hwv : w ≠ v₀) (hnf : ¬ IsFaceOf (↑facets : Set (Finset α)) {w, v₀})
    (hE : IsFaceOf (↑facets : Set (Finset α)) ∅) (hw : IsFaceOf (↑facets : Set (Finset α)) {w})
    (hv₀ : IsFaceOf (↑facets : Set (Finset α)) {v₀}) :
    Submodule.Quotient.mk (⟨srDisconnectKoszulCycle facets v₀ w,
        srDisconnectKoszulCycle_mem_koszulCycles facets hwv hnf⟩ :
        koszulCycles (srVertexX R facets)) ≠ (0 : koszulTor (srVertexX R facets)) :=
  koszulTor_mk_ne_zero (srVertexX R facets) _
    (srDisconnectKoszulCycle_not_mem_koszulBoundaries facets hwv hE hw hv₀)

end SRDisconnect

end

end GaloisForLFunctions.HTGeometry
