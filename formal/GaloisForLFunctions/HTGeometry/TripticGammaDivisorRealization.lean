import GaloisForLFunctions.HTGeometry.EllipticGammaConeOrder

/-!
# Every finite integral divisor is realized by a gamma product

Orders add under products and subtract under quotients, so the orbital charge does too.  A finite
product of translated elliptic gamma functions, with the classes of positive multiplicity in the
numerator and those of negative multiplicity in the denominator, therefore has any prescribed
finitely supported integral charge.

* `shiftOrder_pow`, `shiftOrder_div`, `tripticOrbitCharge_pow`, `tripticOrbitCharge_div`;
* `gammaDivisorSource`, `tripticOrbitCharge_gammaDivisorSource`.
-/

open Filter Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

theorem meromorphicOn_pow {Y : ℂ → ℂ} (hY : MeromorphicOn Y (Set.univ : Set ℂ)) (n : ℕ) :
    MeromorphicOn (fun z ↦ Y z ^ n) (Set.univ : Set ℂ) := fun z _ ↦
  (hY z (Set.mem_univ z)).pow n

theorem meromorphicOrderAt_pow_ne_top {Y : ℂ → ℂ} (hY : MeromorphicOn Y (Set.univ : Set ℂ))
    (hfin : ∀ w : ℂ, meromorphicOrderAt Y w ≠ ⊤) (n : ℕ) (w : ℂ) :
    meromorphicOrderAt (fun z ↦ Y z ^ n) w ≠ ⊤ := by
  induction n with
  | zero =>
      have hfun : (fun z : ℂ ↦ Y z ^ 0) = fun _ : ℂ ↦ (1 : ℂ) := by
        funext z
        simp
      rw [hfun]
      classical
      rw [meromorphicOrderAt_const]
      simp
  | succ k ih =>
      have hfun : (fun z : ℂ ↦ Y z ^ (k + 1)) = fun z : ℂ ↦ Y z ^ k * Y z := by
        funext z
        ring
      have hmul : meromorphicOrderAt (fun z : ℂ ↦ Y z ^ k * Y z) w
          = meromorphicOrderAt (fun z : ℂ ↦ Y z ^ k) w + meromorphicOrderAt Y w :=
        meromorphicOrderAt_mul ((meromorphicOn_pow hY k) w (Set.mem_univ w))
          (hY w (Set.mem_univ w))
      rw [hfun, hmul]
      exact WithTop.add_ne_top.mpr ⟨ih, hfin w⟩

/-- The shift order of a power is the multiple of the shift order. -/
theorem shiftOrder_pow {Y : ℂ → ℂ} {σ : ℂ} (hY : MeromorphicOn Y (Set.univ : Set ℂ))
    (hfin : ∀ w : ℂ, meromorphicOrderAt Y w ≠ ⊤) (n : ℕ) (w : ℂ) :
    shiftOrder (fun z ↦ Y z ^ n) σ w = n * shiftOrder Y σ w := by
  induction n with
  | zero =>
      have hfun : (fun z : ℂ ↦ Y z ^ 0) = fun _ : ℂ ↦ (1 : ℂ) := by
        funext z
        simp
      rw [hfun]
      simp only [Nat.cast_zero, zero_mul]
      classical
      have hone : ∀ u : ℂ, meromorphicOrderAt (fun _ : ℂ ↦ (1 : ℂ)) u = 0 := by
        intro u
        rw [meromorphicOrderAt_const]
        simp
      simp only [shiftOrder, hone]
      simp
  | succ k ih =>
      have hfun : (fun z : ℂ ↦ Y z ^ (k + 1)) = fun z : ℂ ↦ Y z ^ k * Y z := by
        funext z
        ring
      rw [hfun, shiftOrder_mul (meromorphicOn_pow hY k) hY
        (meromorphicOrderAt_pow_ne_top hY hfin k) hfin, ih]
      push_cast
      ring

/-- The shift order of a quotient is the difference of the shift orders. -/
theorem shiftOrder_div {Y₁ Y₂ : ℂ → ℂ} {σ : ℂ} (h₁ : MeromorphicOn Y₁ (Set.univ : Set ℂ))
    (h₂ : MeromorphicOn Y₂ (Set.univ : Set ℂ)) (hf₁ : ∀ w : ℂ, meromorphicOrderAt Y₁ w ≠ ⊤)
    (hf₂ : ∀ w : ℂ, meromorphicOrderAt Y₂ w ≠ ⊤) (w : ℂ) :
    shiftOrder (fun z ↦ Y₁ z / Y₂ z) σ w = shiftOrder Y₁ σ w - shiftOrder Y₂ σ w := by
  have hord : ∀ u : ℂ, meromorphicOrderAt (fun z ↦ Y₁ z / Y₂ z) u
      = meromorphicOrderAt Y₁ u - meromorphicOrderAt Y₂ u := fun u ↦
    meromorphicOrderAt_div (h₁ u (Set.mem_univ u)) (h₂ u (Set.mem_univ u))
  have huntop : ∀ u : ℂ, (meromorphicOrderAt (fun z ↦ Y₁ z / Y₂ z) u).untop₀
      = (meromorphicOrderAt Y₁ u).untop₀ - (meromorphicOrderAt Y₂ u).untop₀ := by
    intro u
    obtain ⟨n₁, hn₁⟩ := WithTop.ne_top_iff_exists.mp (hf₁ u)
    obtain ⟨n₂, hn₂⟩ := WithTop.ne_top_iff_exists.mp (hf₂ u)
    have hcast : ((n₁ : WithTop ℤ) - (n₂ : WithTop ℤ)) = (((n₁ - n₂ : ℤ)) : WithTop ℤ) := by
      rw [sub_eq_add_neg, sub_eq_add_neg]
      rfl
    rw [hord u, ← hn₁, ← hn₂, hcast]
    simp only [WithTop.untop₀_coe]
  simp only [shiftOrder, huntop]
  ring


/-! ### The orbital charge of powers, quotients and finite products -/

/-- A source whose shift order is nonzero at only finitely many points of an orbit. -/
def FiniteShiftSupport (Y : ℂ → ℂ) (σ p : ℂ) : Prop :=
  {m : ℤ | shiftOrder Y σ (p + (m : ℂ) * σ) ≠ 0}.Finite

theorem finiteShiftSupport_mul {Y₁ Y₂ : ℂ → ℂ} {σ p : ℂ}
    (h₁ : MeromorphicOn Y₁ (Set.univ : Set ℂ)) (h₂ : MeromorphicOn Y₂ (Set.univ : Set ℂ))
    (hf₁ : ∀ w : ℂ, meromorphicOrderAt Y₁ w ≠ ⊤) (hf₂ : ∀ w : ℂ, meromorphicOrderAt Y₂ w ≠ ⊤)
    (hs₁ : FiniteShiftSupport Y₁ σ p) (hs₂ : FiniteShiftSupport Y₂ σ p) :
    FiniteShiftSupport (fun z ↦ Y₁ z * Y₂ z) σ p := by
  refine (hs₁.union hs₂).subset fun m hm ↦ ?_
  simp only [Set.mem_setOf_eq, Set.mem_union] at hm ⊢
  by_contra hcon
  push Not at hcon
  exact hm (by rw [shiftOrder_mul h₁ h₂ hf₁ hf₂, hcon.1, hcon.2, add_zero])

theorem finiteShiftSupport_pow {Y : ℂ → ℂ} {σ p : ℂ} (hY : MeromorphicOn Y (Set.univ : Set ℂ))
    (hfin : ∀ w : ℂ, meromorphicOrderAt Y w ≠ ⊤) (hs : FiniteShiftSupport Y σ p) (n : ℕ) :
    FiniteShiftSupport (fun z ↦ Y z ^ n) σ p := by
  refine hs.subset fun m hm ↦ ?_
  simp only [Set.mem_setOf_eq] at hm ⊢
  intro hzero
  exact hm (by rw [shiftOrder_pow hY hfin, hzero, mul_zero])

theorem tripticOrbitCharge_pow {Y : ℂ → ℂ} {σ p : ℂ} (hY : MeromorphicOn Y (Set.univ : Set ℂ))
    (hfin : ∀ w : ℂ, meromorphicOrderAt Y w ≠ ⊤) (n : ℕ) :
    tripticOrbitCharge (fun z ↦ Y z ^ n) σ p = n * tripticOrbitCharge Y σ p := by
  simp only [tripticOrbitCharge]
  rw [finsum_congr (fun m : ℤ ↦ shiftOrder_pow hY hfin n (p + (m : ℂ) * σ))]
  exact (mul_finsum (fun m : ℤ ↦ shiftOrder Y σ (p + (m : ℂ) * σ)) (n : ℤ)).symm

theorem tripticOrbitCharge_div {Y₁ Y₂ : ℂ → ℂ} {σ p : ℂ}
    (h₁ : MeromorphicOn Y₁ (Set.univ : Set ℂ)) (h₂ : MeromorphicOn Y₂ (Set.univ : Set ℂ))
    (hf₁ : ∀ w : ℂ, meromorphicOrderAt Y₁ w ≠ ⊤) (hf₂ : ∀ w : ℂ, meromorphicOrderAt Y₂ w ≠ ⊤)
    (hs₁ : FiniteShiftSupport Y₁ σ p) (hs₂ : FiniteShiftSupport Y₂ σ p) :
    tripticOrbitCharge (fun z ↦ Y₁ z / Y₂ z) σ p
      = tripticOrbitCharge Y₁ σ p - tripticOrbitCharge Y₂ σ p := by
  simp only [tripticOrbitCharge]
  rw [finsum_congr (fun m : ℤ ↦ shiftOrder_div h₁ h₂ hf₁ hf₂ (p + (m : ℂ) * σ))]
  exact finsum_sub_distrib hs₁ hs₂

end

end GaloisForLFunctions.HTGeometry
