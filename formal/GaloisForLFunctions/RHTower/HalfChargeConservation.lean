/-
# Conservation of the half charge, and the seam-deposit law (Phase E, u-plane)

Allowing zeros on the seam (`Im w = 0`), a conjugation-symmetric configuration partitions into
upper / seam / lower, and reality bijects upper↔lower while fixing the seam:

  `Σ_S ord = 2·upperOrder + seamOrder`   (`aggregate_eq_two_upperOrder_add_seamOrder`).

The aggregate `Σ_S ord` is the winding of the (conjugation-symmetric) boundary loop, hence
homotopy-invariant (`windingNumber_of_homotopic`): an admissible deformation — one across whose outer
boundary no zero crosses — preserves it.  Conservation of the aggregate is therefore the
**seam-deposit law**

  `2·upperOrder S₀ + seamOrder S₀ = 2·upperOrder S₁ + seamOrder S₁`
  (`halfCharge_seam_deposit`),  i.e.  `Δ(seamOrder) = −2·Δ(upperOrder)`  (`halfCharge_deposit_eq`).

Consequences:

* **Half charge conserved when the seam is inert** (`upperOrder_conserved_of_seam_inert`): if no order
  crosses the seam, the half charge is exactly conserved.
* **The seam boundary term the half charge emits is even** (`seamOrder_parity_conserved`): the deposit
  `Δ(seamOrder) = 2·Δ(upperOrder)` is even, so the *mod-2 seam parity* is conserved — blind to the
  transfer.  The genuine emitted quantity is the integer deposit `2·Δ(upperOrder)`, the **relative
  half-seam class** the naive mod-2 seam parity cannot express.
* **Far-field drain** (`xiDescent_ne_zero_of_uSqrt_re_gt`, `xiDescentUpperOrder_eq_zero_of_no_upper_zero`):
  where `Re √u > 1/2` (so `Re s > 1`) `xiDescent` is zero-free, so the half charge there is `0`.
* **The `{i, −i}` witness** (`exists_halfCharge_seam_deposit_witness`): the collision
  `{i, −i}` (half charge `1`, seam `0`) → `{0}` (half charge `0`, seam `2`) has equal aggregate `2`;
  the half charge is carried onto the seam as order `2`.  A nonzero half charge must either persist to
  the far field (where it is `0`) or deposit an even seam order — it cannot simply vanish.
-/
import GaloisForLFunctions.RHTower.HalfPlaneCharge
import GaloisForLFunctions.RHTower.UPlaneWinding

namespace RHTower

open Complex

/-! ### §1 The seam order and the region partition -/

/-- The seam order of a configuration: `Σ_{w∈S, Im w=0} ord w` — the order carried on the real axis
(the fixed set of conjugation). -/
noncomputable def seamOrder (S : Finset ℂ) (ord : ℂ → ℕ) : ℕ :=
  ∑ w ∈ S.filter (fun w => w.im = 0), ord w

/-- **Region partition with reality.**  For a conjugation-symmetric configuration with a
conjugation-invariant weight, the total order splits as twice the upper-half order plus the seam
order: conjugation bijects the (off-seam) upper and lower halves and fixes the seam. -/
theorem aggregate_eq_two_upperOrder_add_seamOrder {S : Finset ℂ} (ord : ℂ → ℕ)
    (hSconj : ∀ w ∈ S, (starRingEnd ℂ) w ∈ S)
    (hord : ∀ w ∈ S, ord ((starRingEnd ℂ) w) = ord w) :
    ∑ w ∈ S, ord w = 2 * upperOrder S ord + seamOrder S ord := by
  classical
  set S' := S.filter (fun w => ¬ w.im = 0) with hS'
  have hsplit : ∑ w ∈ S, ord w = seamOrder S ord + ∑ w ∈ S', ord w := by
    rw [seamOrder, hS']
    exact (Finset.sum_filter_add_sum_filter_not S (fun w => w.im = 0) ord).symm
  have hS'conj : ∀ w ∈ S', (starRingEnd ℂ) w ∈ S' := by
    intro w hw
    rw [hS', Finset.mem_filter] at hw ⊢
    refine ⟨hSconj w hw.1, ?_⟩
    rw [Complex.conj_im]
    exact fun h => hw.2 (by linarith [neg_eq_zero.mp h])
  have hS'fix : ∀ w ∈ S', (starRingEnd ℂ) w ≠ w := by
    intro w hw hcw
    rw [hS', Finset.mem_filter] at hw
    exact hw.2 (by have := congrArg Complex.im hcw; rw [Complex.conj_im] at this; linarith)
  have hS'ord : ∀ w ∈ S', ord ((starRingEnd ℂ) w) = ord w := by
    intro w hw; rw [hS', Finset.mem_filter] at hw; exact hord w hw.1
  have h2 := seam_order_two_mul ord hS'conj hS'fix hS'ord
  have hup : (∑ w ∈ S'.filter (fun w => 0 < w.im), ord w) = upperOrder S ord := by
    unfold upperOrder
    rw [hS', Finset.filter_filter]
    apply Finset.sum_congr _ (fun _ _ => rfl)
    apply Finset.filter_congr
    intro w _
    exact ⟨fun h => h.2, fun h => ⟨ne_of_gt h, h⟩⟩
  rw [hsplit, h2, hup]; ring

/-! ### §2 The seam-deposit conservation law -/

/-- **The seam-deposit law.**  If two conjugation-symmetric configurations have the same aggregate
order (an admissible deformation across whose outer boundary no zero crosses), then twice the half
charge plus the seam order is conserved: the half charge can only change by depositing order on the
seam. -/
theorem halfCharge_seam_deposit {S₀ S₁ : Finset ℂ} (ord : ℂ → ℕ)
    (h0conj : ∀ w ∈ S₀, (starRingEnd ℂ) w ∈ S₀) (h0ord : ∀ w ∈ S₀, ord ((starRingEnd ℂ) w) = ord w)
    (h1conj : ∀ w ∈ S₁, (starRingEnd ℂ) w ∈ S₁) (h1ord : ∀ w ∈ S₁, ord ((starRingEnd ℂ) w) = ord w)
    (hagg : ∑ w ∈ S₀, ord w = ∑ w ∈ S₁, ord w) :
    2 * upperOrder S₀ ord + seamOrder S₀ ord = 2 * upperOrder S₁ ord + seamOrder S₁ ord := by
  rw [← aggregate_eq_two_upperOrder_add_seamOrder ord h0conj h0ord,
    ← aggregate_eq_two_upperOrder_add_seamOrder ord h1conj h1ord]
  exact hagg

/-- **The deposit is `−2·Δ(half charge)`.**  The change in seam order exactly compensates twice the
change in the half charge. -/
theorem halfCharge_deposit_eq {S₀ S₁ : Finset ℂ} (ord : ℂ → ℕ)
    (h0conj : ∀ w ∈ S₀, (starRingEnd ℂ) w ∈ S₀) (h0ord : ∀ w ∈ S₀, ord ((starRingEnd ℂ) w) = ord w)
    (h1conj : ∀ w ∈ S₁, (starRingEnd ℂ) w ∈ S₁) (h1ord : ∀ w ∈ S₁, ord ((starRingEnd ℂ) w) = ord w)
    (hagg : ∑ w ∈ S₀, ord w = ∑ w ∈ S₁, ord w) :
    (seamOrder S₁ ord : ℤ) - seamOrder S₀ ord
      = 2 * ((upperOrder S₀ ord : ℤ) - upperOrder S₁ ord) := by
  have h := halfCharge_seam_deposit ord h0conj h0ord h1conj h1ord hagg
  have h' : (2 * upperOrder S₀ ord + seamOrder S₀ ord : ℤ)
      = 2 * upperOrder S₁ ord + seamOrder S₁ ord := by exact_mod_cast h
  linarith

/-- **Half charge conserved when the seam is inert.**  If the aggregate is preserved and no order
crosses the seam (the seam order is unchanged), the half charge is exactly conserved. -/
theorem upperOrder_conserved_of_seam_inert {S₀ S₁ : Finset ℂ} (ord : ℂ → ℕ)
    (h0conj : ∀ w ∈ S₀, (starRingEnd ℂ) w ∈ S₀) (h0ord : ∀ w ∈ S₀, ord ((starRingEnd ℂ) w) = ord w)
    (h1conj : ∀ w ∈ S₁, (starRingEnd ℂ) w ∈ S₁) (h1ord : ∀ w ∈ S₁, ord ((starRingEnd ℂ) w) = ord w)
    (hagg : ∑ w ∈ S₀, ord w = ∑ w ∈ S₁, ord w)
    (hseam : seamOrder S₀ ord = seamOrder S₁ ord) :
    upperOrder S₀ ord = upperOrder S₁ ord := by
  have h := halfCharge_seam_deposit ord h0conj h0ord h1conj h1ord hagg
  omega

/-- **The emitted seam term is even — the mod-2 seam parity is blind to the transfer.**  Under an
admissible deformation the seam order changes by an even amount (`= 2·Δ(half charge)`), so its
parity is conserved.  The genuine emitted datum is the integer deposit `2·Δ(upperOrder)` — the
relative half-seam class the mod-2 parity cannot express. -/
theorem seamOrder_parity_conserved {S₀ S₁ : Finset ℂ} (ord : ℂ → ℕ)
    (h0conj : ∀ w ∈ S₀, (starRingEnd ℂ) w ∈ S₀) (h0ord : ∀ w ∈ S₀, ord ((starRingEnd ℂ) w) = ord w)
    (h1conj : ∀ w ∈ S₁, (starRingEnd ℂ) w ∈ S₁) (h1ord : ∀ w ∈ S₁, ord ((starRingEnd ℂ) w) = ord w)
    (hagg : ∑ w ∈ S₀, ord w = ∑ w ∈ S₁, ord w) :
    seamOrder S₀ ord % 2 = seamOrder S₁ ord % 2 := by
  have h := halfCharge_seam_deposit ord h0conj h0ord h1conj h1ord hagg
  omega

/-! ### §3 The far-field drain: where the half charge provably vanishes -/

/-- **The far-field drain is zero-free.**  If `Re √u > 1/2`, then `s = 1/2 + √u` has `Re s > 1`, where
`ξ` — hence `xiDescent` — does not vanish. -/
theorem xiDescent_ne_zero_of_uSqrt_re_gt {u : ℂ} (hu : u ∈ slitPlane)
    (hre : 1 / 2 < (uSqrt u).re) : xiDescent u ≠ 0 := by
  rw [xiDescent_of_ne_zero (slitPlane_ne_zero hu)]
  apply xi_ne_zero_of_one_le_re
  rw [Complex.add_re, show (1 / 2 : ℂ).re = (1 / 2 : ℝ) from by norm_num]
  linarith

/-- **The half charge vanishes on a zero-free upper half.**  If no upper-half point of the
configuration is a zero of `xiDescent` (in particular, in the far-field drain), the descended
upper-half order sum is `0`. -/
theorem xiDescentUpperOrder_eq_zero_of_no_upper_zero {S : Finset ℂ}
    (h : ∀ w ∈ S, 0 < w.im → xiDescent w ≠ 0) :
    upperOrder S (fun w => (analyticOrderAt xiDescent w).toNat) = 0 := by
  unfold upperOrder
  apply Finset.sum_eq_zero
  intro w hw
  rw [Finset.mem_filter] at hw
  rw [analyticOrderAt_eq_zero.mpr (Or.inr (h w hw.1 hw.2))]
  simp

/-! ### §4 The `{i, −i}` collision: a half charge carried onto the seam -/

/-- **The half charge is carried to the seam, not destroyed.**  There are two conjugation-symmetric
configurations of equal aggregate — `{i, −i}` (half charge `1`, seam order `0`) and `{0}` (half charge
`0`, seam order `2`) — modelling the collision of an off-line conjugate pair onto the seam.  The half
charge `1` is transferred as seam order `2 = 2·1`: exactly the deposit law.  A nonzero half charge
cannot simply vanish; it must persist or deposit an even seam order. -/
theorem exists_halfCharge_seam_deposit_witness :
    ∃ (S₀ S₁ : Finset ℂ) (ord₀ ord₁ : ℂ → ℕ),
      (∀ w ∈ S₀, (starRingEnd ℂ) w ∈ S₀) ∧ (∀ w ∈ S₀, ord₀ ((starRingEnd ℂ) w) = ord₀ w) ∧
      (∀ w ∈ S₁, (starRingEnd ℂ) w ∈ S₁) ∧ (∀ w ∈ S₁, ord₁ ((starRingEnd ℂ) w) = ord₁ w) ∧
      (∑ w ∈ S₀, ord₀ w) = (∑ w ∈ S₁, ord₁ w) ∧
      upperOrder S₀ ord₀ = 1 ∧ seamOrder S₀ ord₀ = 0 ∧
      upperOrder S₁ ord₁ = 0 ∧ seamOrder S₁ ord₁ = 2 := by
  have hIne : (I : ℂ) ≠ -I := by
    intro h; have := congrArg Complex.im h
    simp only [Complex.I_im, Complex.neg_im] at this; norm_num at this
  have hupper0 : upperOrder ({I, -I} : Finset ℂ) (fun _ => 1) = 1 := by
    unfold upperOrder
    rw [show (({I, -I} : Finset ℂ).filter (fun w => 0 < w.im)) = {I} from by
      ext z
      simp only [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl | rfl, hz⟩
        · rfl
        · exact absurd hz (by simp [Complex.neg_im, Complex.I_im])
      · rintro rfl; exact ⟨Or.inl rfl, by simp [Complex.I_im]⟩]
    rw [Finset.sum_singleton]
  have hseam0 : seamOrder ({I, -I} : Finset ℂ) (fun _ => 1) = 0 := by
    unfold seamOrder
    rw [show (({I, -I} : Finset ℂ).filter (fun w => w.im = 0)) = ∅ from by
      rw [Finset.filter_eq_empty_iff]
      intro z hz
      rw [Finset.mem_insert, Finset.mem_singleton] at hz
      rcases hz with rfl | rfl
      · simp [Complex.I_im]
      · simp [Complex.neg_im, Complex.I_im]]
    rfl
  refine ⟨{I, -I}, {0}, fun _ => 1, fun _ => 2, ?_, ?_, ?_, ?_, ?_, hupper0, hseam0, ?_, ?_⟩
  · intro w hw
    rw [Finset.mem_insert, Finset.mem_singleton] at hw ⊢
    rcases hw with rfl | rfl
    · exact Or.inr Complex.conj_I
    · left; rw [map_neg, Complex.conj_I, neg_neg]
  · intro _ _; rfl
  · intro w hw
    rw [Finset.mem_singleton] at hw ⊢; rw [hw, map_zero]
  · intro _ _; rfl
  · rw [Finset.sum_pair hIne, Finset.sum_singleton]
  · unfold upperOrder
    rw [show (({0} : Finset ℂ).filter (fun w => 0 < w.im)) = ∅ from by
      simp [Finset.filter_singleton, Complex.zero_im]]
    rfl
  · unfold seamOrder
    rw [show (({0} : Finset ℂ).filter (fun w => w.im = 0)) = {0} from by
      simp [Finset.filter_singleton, Complex.zero_im]]
    rw [Finset.sum_singleton]

end RHTower
