import Mathlib

/-!
# Horizontal charge transfer

For a finite divisor `m` on `ℂ` (the multiplicity function of the zeros of a self-dual completed
function in a bounded window) define, over the ordinates `γ` occurring in the support,

```text
H γ = ∑_{Im ρ = γ} m ρ,      N = ∑_ρ m ρ,
C   = ∑_γ (H γ)²,            D = ∑_ρ (m ρ)²,
O   = C − D,                 M = D − N.
```

`O` is the *off-line* (cross) charge and `M` the *multiplicity* charge.  This file proves the four
elementary multiset facts behind the pair-correlation distinction between diagonal and reflected
symmetric-diagonal terms:

* `offLineCharge_nonneg`, `multiplicityCharge_nonneg`, `even_offLineCharge`,
  `even_multiplicityCharge` — both charges are nonnegative even integers;
* `offLineCharge_eq_zero_iff` — for a self-dual divisor, `O = 0` exactly when every zero lies on
  the critical line;
* `census_split` — the horizontal excess splits exactly, `C − N = O + M`;
* `collision_transfer` (and its simple case `collision_transfer_simple`) — when a reflected
  off-line pair collides with a critical-line zero of multiplicity `r`, the charge moves
  `(O, M) : (4r + 2, r² − r) → (0, r² + 3r + 2)` while `C − N` is conserved.

The consequence for research is the last item: an entry-prevention theorem cannot be based on
`C − N`, because that statistic is *unchanged* by the collision.  It must control `O` separately
from `M`.

The Xi-specific instance of the first three items already lives in
`RHTower/XiHorizontalCollisionChargeEndpoint.lean`
(`xiStripWindowHorizontalSquareSum_eq_localSquare_add_collisionCharge`,
`xiHorizontalCollisionCharge_even`, `xiHorizontalCollisionCharge_eq_zero_iff_stripSupport_onLine`);
this module supplies the abstract multiset statement together with the multiplicity charge and the
collision arithmetic, which are not covered there.
-/

noncomputable section

open Complex Finset

namespace GaloisForLFunctions.HTGeometry.HorizontalCharge

open scoped Classical

/-- The total multiplicity carried by the horizontal fibre at an ordinate. -/
def horizontalMass (m : ℂ →₀ ℕ) (γ : ℝ) : ℕ :=
  ∑ ρ ∈ m.support.filter (fun ρ => ρ.im = γ), m ρ

/-- The total divisor mass. -/
def divisorMass (m : ℂ →₀ ℕ) : ℕ := ∑ ρ ∈ m.support, m ρ

/-- The census of squared horizontal-fibre masses. -/
def horizontalSquareMass (m : ℂ →₀ ℕ) : ℕ :=
  ∑ γ ∈ m.support.image Complex.im, (horizontalMass m γ) ^ 2

/-- The census of squared local multiplicities. -/
def localSquareMass (m : ℂ →₀ ℕ) : ℕ := ∑ ρ ∈ m.support, (m ρ) ^ 2

/-- The off-line (cross) charge `O`. -/
def offLineCharge (m : ℂ →₀ ℕ) : ℤ := (horizontalSquareMass m : ℤ) - localSquareMass m

/-- The multiplicity charge `M`. -/
def multiplicityCharge (m : ℂ →₀ ℕ) : ℤ := (localSquareMass m : ℤ) - divisorMass m

/-! ## Superset forms of the statistics -/

theorem divisorMass_eq_sum_of_subset {m : ℂ →₀ ℕ} {S : Finset ℂ} (hS : m.support ⊆ S) :
    divisorMass m = ∑ ρ ∈ S, m ρ := by
  refine Finset.sum_subset hS (fun ρ _ hρ => ?_)
  exact Finsupp.notMem_support_iff.mp hρ

theorem localSquareMass_eq_sum_of_subset {m : ℂ →₀ ℕ} {S : Finset ℂ} (hS : m.support ⊆ S) :
    localSquareMass m = ∑ ρ ∈ S, (m ρ) ^ 2 := by
  refine Finset.sum_subset hS (fun ρ _ hρ => ?_)
  rw [Finsupp.notMem_support_iff.mp hρ]
  simp

theorem horizontalMass_eq_sum_of_subset {m : ℂ →₀ ℕ} {S : Finset ℂ} (hS : m.support ⊆ S)
    (γ : ℝ) : horizontalMass m γ = ∑ ρ ∈ S.filter (fun ρ => ρ.im = γ), m ρ := by
  refine Finset.sum_subset (Finset.filter_subset_filter _ hS) (fun ρ _ hρ => ?_)
  by_contra hcon
  have hmem : ρ ∈ m.support := Finsupp.mem_support_iff.mpr (fun h => hcon (by rw [h]))
  exact hρ (Finset.mem_filter.mpr ⟨hmem, (Finset.mem_filter.mp ‹ρ ∈ S.filter _›).2⟩)

/-! ## The fibrewise decomposition -/

theorem sum_horizontalMass : ∀ m : ℂ →₀ ℕ,
    ∑ γ ∈ m.support.image Complex.im, horizontalMass m γ = divisorMass m := by
  intro m
  rw [divisorMass]
  exact Finset.sum_fiberwise_of_maps_to (fun ρ hρ => Finset.mem_image_of_mem _ hρ) _

theorem sum_localSquare_fiberwise (m : ℂ →₀ ℕ) :
    ∑ γ ∈ m.support.image Complex.im,
      (∑ ρ ∈ m.support.filter (fun ρ => ρ.im = γ), (m ρ) ^ 2) = localSquareMass m := by
  rw [localSquareMass]
  exact Finset.sum_fiberwise_of_maps_to (fun ρ hρ => Finset.mem_image_of_mem _ hρ) _

/-- The square of a fibre mass splits into the local squares and the ordered cross pairs. -/
theorem sq_sum_eq_sum_sq_add_offDiag (S : Finset ℂ) (f : ℂ → ℕ) :
    (∑ ρ ∈ S, f ρ) ^ 2 = (∑ ρ ∈ S, (f ρ) ^ 2) + ∑ p ∈ S.offDiag, f p.1 * f p.2 := by
  have h1 : (∑ ρ ∈ S, f ρ) ^ 2 = ∑ p ∈ S ×ˢ S, f p.1 * f p.2 := by
    rw [sq, Finset.sum_mul_sum]
    rw [Finset.sum_product]
  rw [h1, ← Finset.diag_union_offDiag S,
    Finset.sum_union (Finset.disjoint_diag_offDiag S)]
  congr 1
  rw [Finset.sum_diag]
  exact Finset.sum_congr rfl (fun ρ _ => by rw [sq])

/-- The ordered cross mass: all ordered pairs of distinct zeros in a common horizontal fibre. -/
def crossMass (m : ℂ →₀ ℕ) : ℕ :=
  ∑ γ ∈ m.support.image Complex.im,
    ∑ p ∈ (m.support.filter (fun ρ => ρ.im = γ)).offDiag, m p.1 * m p.2

/-- **The quadratic census identity** `C = D + O`. -/
theorem horizontalSquareMass_eq : ∀ m : ℂ →₀ ℕ,
    horizontalSquareMass m = localSquareMass m + crossMass m := by
  intro m
  rw [horizontalSquareMass, crossMass, ← sum_localSquare_fiberwise m, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl (fun γ _ => ?_)
  rw [horizontalMass]
  exact sq_sum_eq_sum_sq_add_offDiag _ _

theorem offLineCharge_eq_crossMass (m : ℂ →₀ ℕ) : offLineCharge m = (crossMass m : ℤ) := by
  rw [offLineCharge, horizontalSquareMass_eq]
  push_cast
  ring

/-! ## Positivity and parity -/

theorem localSquareMass_le_horizontalSquareMass (m : ℂ →₀ ℕ) :
    localSquareMass m ≤ horizontalSquareMass m := by
  rw [horizontalSquareMass_eq]
  exact Nat.le_add_right _ _

theorem divisorMass_le_localSquareMass (m : ℂ →₀ ℕ) : divisorMass m ≤ localSquareMass m := by
  refine Finset.sum_le_sum (fun ρ hρ => ?_)
  have h1 : 1 ≤ m ρ := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hρ)
  nlinarith

theorem offLineCharge_nonneg (m : ℂ →₀ ℕ) : 0 ≤ offLineCharge m := by
  rw [offLineCharge, sub_nonneg]
  exact_mod_cast localSquareMass_le_horizontalSquareMass m

theorem multiplicityCharge_nonneg (m : ℂ →₀ ℕ) : 0 ≤ multiplicityCharge m := by
  rw [multiplicityCharge, sub_nonneg]
  exact_mod_cast divisorMass_le_localSquareMass m

theorem two_dvd_sq_sub_self (n : ℕ) : (2 : ℤ) ∣ (n : ℤ) ^ 2 - n := by
  have h : ((n : ℤ) - 1) * n = (n : ℤ) ^ 2 - n := by ring
  rw [← h]
  rcases Int.even_or_odd (n : ℤ) with he | ho
  · exact Dvd.dvd.mul_left he.two_dvd _
  · have : Even ((n : ℤ) - 1) := by
      rcases ho with ⟨k, hk⟩
      exact ⟨k, by omega⟩
    exact Dvd.dvd.mul_right this.two_dvd _

theorem two_dvd_horizontalSquareMass_sub_divisorMass (m : ℂ →₀ ℕ) :
    (2 : ℤ) ∣ ((horizontalSquareMass m : ℤ) - divisorMass m) := by
  have hN : ((divisorMass m : ℤ))
      = ∑ γ ∈ m.support.image Complex.im, (horizontalMass m γ : ℤ) := by
    rw [← sum_horizontalMass m]
    push_cast
    ring
  have hC : ((horizontalSquareMass m : ℤ))
      = ∑ γ ∈ m.support.image Complex.im, ((horizontalMass m γ : ℤ)) ^ 2 := by
    rw [horizontalSquareMass]
    push_cast
    ring
  rw [hC, hN, ← Finset.sum_sub_distrib]
  exact Finset.dvd_sum (fun γ _ => two_dvd_sq_sub_self _)

theorem two_dvd_localSquareMass_sub_divisorMass (m : ℂ →₀ ℕ) :
    (2 : ℤ) ∣ ((localSquareMass m : ℤ) - divisorMass m) := by
  have hN : ((divisorMass m : ℤ)) = ∑ ρ ∈ m.support, (m ρ : ℤ) := by
    rw [divisorMass]; push_cast; ring
  have hD : ((localSquareMass m : ℤ)) = ∑ ρ ∈ m.support, ((m ρ : ℤ)) ^ 2 := by
    rw [localSquareMass]; push_cast; ring
  rw [hD, hN, ← Finset.sum_sub_distrib]
  exact Finset.dvd_sum (fun ρ _ => two_dvd_sq_sub_self _)

/-- **`M` is an even nonnegative integer.** -/
theorem even_multiplicityCharge (m : ℂ →₀ ℕ) : Even (multiplicityCharge m) := by
  rw [even_iff_two_dvd, multiplicityCharge]
  exact two_dvd_localSquareMass_sub_divisorMass m

/-- **`O` is an even nonnegative integer.** -/
theorem even_offLineCharge (m : ℂ →₀ ℕ) : Even (offLineCharge m) := by
  rw [even_iff_two_dvd, offLineCharge]
  have h : ((horizontalSquareMass m : ℤ) - localSquareMass m)
      = ((horizontalSquareMass m : ℤ) - divisorMass m)
        - ((localSquareMass m : ℤ) - divisorMass m) := by ring
  rw [h]
  exact dvd_sub (two_dvd_horizontalSquareMass_sub_divisorMass m)
    (two_dvd_localSquareMass_sub_divisorMass m)

/-- **The horizontal-multiplicity excess splits exactly**: `C − N = O + M`. -/
theorem census_split (m : ℂ →₀ ℕ) :
    (horizontalSquareMass m : ℤ) - divisorMass m = offLineCharge m + multiplicityCharge m := by
  rw [offLineCharge, multiplicityCharge]
  ring

/-! ## Off-line charge detects off-line zeros -/

/-- A divisor stable under the functional-equation reflection `ρ ↦ 1 − conj ρ`. -/
def SelfDual (m : ℂ →₀ ℕ) : Prop := ∀ ρ : ℂ, m (1 - (starRingEnd ℂ) ρ) = m ρ

theorem reflect_im (ρ : ℂ) : (1 - (starRingEnd ℂ) ρ).im = ρ.im := by
  simp

theorem reflect_re (ρ : ℂ) : (1 - (starRingEnd ℂ) ρ).re = 1 - ρ.re := by
  simp

/-- **`O = 0` exactly when every zero lies on the critical line.** -/
theorem offLineCharge_eq_zero_iff {m : ℂ →₀ ℕ} (hdual : SelfDual m) :
    offLineCharge m = 0 ↔ ∀ ρ ∈ m.support, ρ.re = 1 / 2 := by
  rw [offLineCharge_eq_crossMass]
  constructor
  · intro h0 ρ₀ hρ₀
    by_contra hre
    set ρ₁ : ℂ := 1 - (starRingEnd ℂ) ρ₀ with hρ₁def
    have hm1 : m ρ₁ = m ρ₀ := hdual ρ₀
    have hmem1 : ρ₁ ∈ m.support := by
      refine Finsupp.mem_support_iff.mpr ?_
      rw [hm1]
      exact Finsupp.mem_support_iff.mp hρ₀
    have hne : ρ₁ ≠ ρ₀ := by
      intro hcon
      have := congrArg Complex.re hcon
      rw [hρ₁def, reflect_re] at this
      apply hre
      linarith
    set γ : ℝ := ρ₀.im with hγ
    have hfilt : ρ₀ ∈ m.support.filter (fun ρ => ρ.im = γ) :=
      Finset.mem_filter.mpr ⟨hρ₀, rfl⟩
    have hfilt1 : ρ₁ ∈ m.support.filter (fun ρ => ρ.im = γ) := by
      refine Finset.mem_filter.mpr ⟨hmem1, ?_⟩
      rw [hρ₁def, reflect_im]
    have hpair : (ρ₀, ρ₁) ∈ (m.support.filter (fun ρ => ρ.im = γ)).offDiag :=
      Finset.mem_offDiag.mpr ⟨hfilt, hfilt1, fun hcon => hne hcon.symm⟩
    have hposinner : 0 < ∑ p ∈ (m.support.filter (fun ρ => ρ.im = γ)).offDiag, m p.1 * m p.2 := by
      refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun p : ℂ × ℂ => m p.1 * m p.2)
        (fun p _ => Nat.zero_le _) hpair)
      have h1 : 0 < m ρ₀ := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hρ₀)
      have h2 : 0 < m ρ₁ := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hmem1)
      exact Nat.mul_pos h1 h2
    have hγmem : γ ∈ m.support.image Complex.im := Finset.mem_image_of_mem _ hρ₀
    have hle : (∑ p ∈ (m.support.filter (fun ρ => ρ.im = γ)).offDiag, m p.1 * m p.2)
        ≤ crossMass m :=
      Finset.single_le_sum
        (f := fun γ : ℝ => ∑ p ∈ (m.support.filter (fun ρ => ρ.im = γ)).offDiag, m p.1 * m p.2)
        (fun _ _ => Nat.zero_le _) hγmem
    have : 0 < crossMass m := lt_of_lt_of_le hposinner hle
    omega
  · intro hline
    have hzero : crossMass m = 0 := by
      refine Finset.sum_eq_zero (fun γ _ => ?_)
      refine Finset.sum_eq_zero (fun p hp => ?_)
      exfalso
      obtain ⟨h1, h2, h3⟩ := Finset.mem_offDiag.mp hp
      obtain ⟨hs1, hi1⟩ := Finset.mem_filter.mp h1
      obtain ⟨hs2, hi2⟩ := Finset.mem_filter.mp h2
      refine h3 (Complex.ext ?_ ?_)
      · rw [hline _ hs1, hline _ hs2]
      · rw [hi1, hi2]
    rw [hzero]
    rfl

/-! ## Single-ordinate configurations and the collision transfer -/

/-- The point of the critical strip at ordinate `γ` and offset `a` from the critical line. -/
def offsetPoint (γ a : ℝ) : ℂ := ((1 / 2 + a : ℝ) : ℂ) + (γ : ℂ) * I

@[simp] theorem offsetPoint_re (γ a : ℝ) : (offsetPoint γ a).re = 1 / 2 + a := by
  simp [offsetPoint]

@[simp] theorem offsetPoint_im (γ a : ℝ) : (offsetPoint γ a).im = γ := by
  simp [offsetPoint]

theorem offsetPoint_injective {γ : ℝ} {a b : ℝ} (h : offsetPoint γ a = offsetPoint γ b) : a = b := by
  have := congrArg Complex.re h
  rw [offsetPoint_re, offsetPoint_re] at this
  linarith

/-- If every zero sits at one ordinate, the horizontal census is the square of the total mass. -/
theorem horizontalSquareMass_of_single_ordinate {m : ℂ →₀ ℕ} {γ : ℝ}
    (him : ∀ ρ ∈ m.support, ρ.im = γ) :
    horizontalSquareMass m = (divisorMass m) ^ 2 := by
  by_cases hne : m.support.Nonempty
  · have himg : m.support.image Complex.im = {γ} := by
      refine Finset.eq_singleton_iff_nonempty_unique_mem.mpr ⟨hne.image _, ?_⟩
      intro x hx
      obtain ⟨ρ, hρ, rfl⟩ := Finset.mem_image.mp hx
      exact him ρ hρ
    rw [horizontalSquareMass, himg, Finset.sum_singleton]
    congr 1
    rw [horizontalMass, divisorMass, Finset.filter_true_of_mem him]
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    simp [horizontalSquareMass, divisorMass, hne]

/-- The pre-collision divisor: a simple reflected off-line pair at offsets `±a`, together with a
critical-line zero of multiplicity `r`. -/
def collisionBefore (γ a : ℝ) (r : ℕ) : ℂ →₀ ℕ :=
  Finsupp.single (offsetPoint γ (-a)) 1 + Finsupp.single (offsetPoint γ a) 1
    + Finsupp.single (offsetPoint γ 0) r

/-- The post-collision divisor: the pair has entered the critical line. -/
def collisionAfter (γ : ℝ) (r : ℕ) : ℂ →₀ ℕ := Finsupp.single (offsetPoint γ 0) (r + 2)

section Collision

variable {γ a : ℝ} (ha : a ≠ 0) (r : ℕ)

include ha

theorem offsetPoint_ne_neg : offsetPoint γ (-a) ≠ offsetPoint γ a := by
  intro h
  exact ha (by linarith [offsetPoint_injective h])

theorem offsetPoint_neg_ne_zero : offsetPoint γ (-a) ≠ offsetPoint γ 0 := by
  intro h
  exact ha (by linarith [offsetPoint_injective h])

theorem offsetPoint_ne_zero' : offsetPoint γ a ≠ offsetPoint γ 0 := by
  intro h
  exact ha (offsetPoint_injective h)

theorem collisionBefore_support_subset :
    (collisionBefore γ a r).support
      ⊆ ({offsetPoint γ (-a), offsetPoint γ a, offsetPoint γ 0} : Finset ℂ) := by
  refine subset_trans Finsupp.support_add ?_
  refine Finset.union_subset (subset_trans Finsupp.support_add ?_) ?_
  · refine Finset.union_subset ?_ ?_
    · exact subset_trans Finsupp.support_single_subset (by intro x hx; simp at hx; simp [hx])
    · exact subset_trans Finsupp.support_single_subset (by intro x hx; simp at hx; simp [hx])
  · exact subset_trans Finsupp.support_single_subset (by intro x hx; simp at hx; simp [hx])

theorem collisionBefore_apply_neg : collisionBefore γ a r (offsetPoint γ (-a)) = 1 := by
  rw [collisionBefore, Finsupp.add_apply, Finsupp.add_apply, Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (offsetPoint_ne_neg ha),
    Finsupp.single_eq_of_ne (offsetPoint_neg_ne_zero ha)]
  omega

theorem collisionBefore_apply_pos : collisionBefore γ a r (offsetPoint γ a) = 1 := by
  rw [collisionBefore, Finsupp.add_apply, Finsupp.add_apply,
    Finsupp.single_eq_of_ne (Ne.symm (offsetPoint_ne_neg ha)), Finsupp.single_eq_same,
    Finsupp.single_eq_of_ne (offsetPoint_ne_zero' ha)]
  omega

theorem collisionBefore_apply_line : collisionBefore γ a r (offsetPoint γ 0) = r := by
  rw [collisionBefore, Finsupp.add_apply, Finsupp.add_apply,
    Finsupp.single_eq_of_ne (Ne.symm (offsetPoint_neg_ne_zero ha)),
    Finsupp.single_eq_of_ne (Ne.symm (offsetPoint_ne_zero' ha)), Finsupp.single_eq_same]
  omega

theorem divisorMass_collisionBefore : divisorMass (collisionBefore γ a r) = r + 2 := by
  rw [divisorMass_eq_sum_of_subset (collisionBefore_support_subset ha r)]
  rw [Finset.sum_insert (by
      simp [offsetPoint_ne_neg ha, offsetPoint_neg_ne_zero ha]),
    Finset.sum_insert (by simp [offsetPoint_ne_zero' ha]), Finset.sum_singleton,
    collisionBefore_apply_neg ha, collisionBefore_apply_pos ha, collisionBefore_apply_line ha]
  omega

theorem localSquareMass_collisionBefore :
    localSquareMass (collisionBefore γ a r) = r ^ 2 + 2 := by
  rw [localSquareMass_eq_sum_of_subset (collisionBefore_support_subset ha r)]
  rw [Finset.sum_insert (by
      simp [offsetPoint_ne_neg ha, offsetPoint_neg_ne_zero ha]),
    Finset.sum_insert (by simp [offsetPoint_ne_zero' ha]), Finset.sum_singleton,
    collisionBefore_apply_neg ha, collisionBefore_apply_pos ha, collisionBefore_apply_line ha]
  ring

theorem horizontalSquareMass_collisionBefore :
    horizontalSquareMass (collisionBefore γ a r) = (r + 2) ^ 2 := by
  rw [horizontalSquareMass_of_single_ordinate (γ := γ) (fun ρ hρ => ?_),
    divisorMass_collisionBefore ha]
  have hmem := collisionBefore_support_subset ha r hρ
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h <;> rw [h] <;> exact offsetPoint_im _ _

end Collision

theorem divisorMass_collisionAfter (γ : ℝ) (r : ℕ) :
    divisorMass (collisionAfter γ r) = r + 2 := by
  rw [collisionAfter, divisorMass_eq_sum_of_subset
    (S := ({offsetPoint γ 0} : Finset ℂ)) Finsupp.support_single_subset,
    Finset.sum_singleton, Finsupp.single_eq_same]

theorem localSquareMass_collisionAfter (γ : ℝ) (r : ℕ) :
    localSquareMass (collisionAfter γ r) = (r + 2) ^ 2 := by
  rw [collisionAfter, localSquareMass_eq_sum_of_subset
    (S := ({offsetPoint γ 0} : Finset ℂ)) Finsupp.support_single_subset,
    Finset.sum_singleton, Finsupp.single_eq_same]

theorem horizontalSquareMass_collisionAfter (γ : ℝ) (r : ℕ) :
    horizontalSquareMass (collisionAfter γ r) = (r + 2) ^ 2 := by
  rw [horizontalSquareMass_of_single_ordinate (γ := γ) (fun ρ hρ => ?_),
    divisorMass_collisionAfter]
  have hmem := Finsupp.support_single_subset (a := offsetPoint γ 0) (b := r + 2) hρ
  simp only [Finset.mem_singleton] at hmem
  rw [hmem]
  exact offsetPoint_im _ _

/-- **The collision transfer.**  When a simple reflected off-line pair collides with a
critical-line zero of multiplicity `r`, the off-line charge `4r + 2` is converted entirely into
multiplicity charge, and the total horizontal excess `C − N` is conserved. -/
theorem collision_transfer {γ a : ℝ} (ha : a ≠ 0) (r : ℕ) :
    offLineCharge (collisionBefore γ a r) = 4 * r + 2
      ∧ multiplicityCharge (collisionBefore γ a r) = (r : ℤ) ^ 2 - r
      ∧ offLineCharge (collisionAfter γ r) = 0
      ∧ multiplicityCharge (collisionAfter γ r) = (r : ℤ) ^ 2 + 3 * r + 2
      ∧ (horizontalSquareMass (collisionBefore γ a r) : ℤ) - divisorMass (collisionBefore γ a r)
          = (horizontalSquareMass (collisionAfter γ r) : ℤ)
            - divisorMass (collisionAfter γ r) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [offLineCharge, horizontalSquareMass_collisionBefore ha,
      localSquareMass_collisionBefore ha]
    push_cast
    ring
  · rw [multiplicityCharge, localSquareMass_collisionBefore ha,
      divisorMass_collisionBefore ha]
    push_cast
    ring
  · rw [offLineCharge, horizontalSquareMass_collisionAfter, localSquareMass_collisionAfter]
    ring
  · rw [multiplicityCharge, localSquareMass_collisionAfter, divisorMass_collisionAfter]
    push_cast
    ring
  · rw [horizontalSquareMass_collisionBefore ha, divisorMass_collisionBefore ha,
      horizontalSquareMass_collisionAfter, divisorMass_collisionAfter]

/-- **The simple case.**  A simple reflected pair entering the critical line moves the charge
`(O, M)` from `(2, 0)` to `(0, 2)`, leaving `C − N = 2` unchanged. -/
theorem collision_transfer_simple {γ a : ℝ} (ha : a ≠ 0) :
    offLineCharge (collisionBefore γ a 0) = 2
      ∧ multiplicityCharge (collisionBefore γ a 0) = 0
      ∧ offLineCharge (collisionAfter γ 0) = 0
      ∧ multiplicityCharge (collisionAfter γ 0) = 2
      ∧ (horizontalSquareMass (collisionBefore γ a 0) : ℤ)
          - divisorMass (collisionBefore γ a 0) = 2
      ∧ (horizontalSquareMass (collisionAfter γ 0) : ℤ)
          - divisorMass (collisionAfter γ 0) = 2 := by
  obtain ⟨h1, h2, h3, h4, _⟩ := collision_transfer (γ := γ) ha 0
  refine ⟨by simpa using h1, by simpa using h2, h3, by simpa using h4, ?_, ?_⟩
  · rw [horizontalSquareMass_collisionBefore ha, divisorMass_collisionBefore ha]
    norm_num
  · rw [horizontalSquareMass_collisionAfter, divisorMass_collisionAfter]
    norm_num

end GaloisForLFunctions.HTGeometry.HorizontalCharge
