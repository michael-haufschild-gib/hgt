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
