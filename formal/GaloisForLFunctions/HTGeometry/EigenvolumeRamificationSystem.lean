import GaloisForLFunctions.HTGeometry.RamificationPoleFixedPoint

/-!
# The eigenvolume ramification system

A rational eigenvolume under a finite map obeys the local order law

`c x + 1 = e x * (c (F x) + 1)`,

where `F` sends a prime divisor to its image, `e x` is the ramification index and `c x` is the
order of the eigenvolume along `x`.  This module formalizes the combinatorial and arithmetic core
that this law forces, with no algebraic geometry beyond the law itself:

* the divisorial support is stable under taking preimages;
* if the image map is onto and the support is finite, every component of the support is periodic;
* on a periodic component with expanding ramification the order is exactly `-1`, so the support is
  a reduced boundary and no iterate of the map has to be taken;
* a prime with regular order on both sides is unramified, so all ramification is carried by the
  boundary, and the ramification coefficient is the pullback difference of the reduced boundary.
-/

namespace GaloisForLFunctions.HTGeometry

section RamificationSystem

variable {α : Type*} {F : α → α} {c : α → ℤ} {e : α → ℕ}

/-- The order law forbids `e x * (c (F x) + 1) = 1` unless both sides are trivial, so a prime
lying over the divisorial support belongs to the divisorial support. -/
theorem order_ne_zero_of_image_ne_zero
    (hlaw : ∀ x, c x + 1 = (e x : ℤ) * (c (F x) + 1))
    {x : α} (h : c (F x) ≠ 0) : c x ≠ 0 := by
  intro hx
  have h1 : (e x : ℤ) * (c (F x) + 1) = 1 := by
    rw [← hlaw x, hx]; ring
  have he : (0 : ℤ) ≤ (e x : ℤ) := Int.natCast_nonneg _
  have hex : (e x : ℤ) = 1 := Int.eq_one_of_mul_eq_one_right he h1
  rw [hex, one_mul] at h1
  exact h (by omega)

/-- Iterated form of preimage stability of the divisorial support. -/
theorem order_ne_zero_of_iterate_ne_zero
    (hlaw : ∀ x, c x + 1 = (e x : ℤ) * (c (F x) + 1)) :
    ∀ (n : ℕ) (x : α), c (F^[n] x) ≠ 0 → c x ≠ 0 := by
  intro n
  induction n with
  | zero => intro x hx; simpa using hx
  | succ m ih =>
    intro x hx
    refine order_ne_zero_of_image_ne_zero hlaw (ih (F x) ?_)
    rw [← Function.iterate_succ_apply F m x]
    exact hx

/-- Iterating the order law multiplies the shifted order by the ramification indices along the
forward orbit. -/
theorem shift_eq_prod_iterate
    (hlaw : ∀ x, c x + 1 = (e x : ℤ) * (c (F x) + 1)) :
    ∀ (n : ℕ) (x : α),
      c x + 1 = (∏ k ∈ Finset.range n, (e (F^[k] x) : ℤ)) * (c (F^[n] x) + 1) := by
  intro n
  induction n with
  | zero => intro x; simp
  | succ m ih =>
    intro x
    rw [Finset.prod_range_succ, mul_assoc, Function.iterate_succ_apply' F m x,
      ← hlaw (F^[m] x)]
    exact ih x

theorem one_lt_prod_iterate_of_expanding {x : α} :
    ∀ (n : ℕ), 0 < n → (∀ k < n, 1 < e (F^[k] x)) →
      1 < ∏ k ∈ Finset.range n, e (F^[k] x) := by
  intro n
  induction n with
  | zero => intro h; exact absurd h (lt_irrefl 0)
  | succ m ih =>
    intro _ hexp
    rcases Nat.eq_zero_or_pos m with hm | hm
    · subst hm
      simpa using hexp 0 (by omega)
    · have hprev : 1 < ∏ k ∈ Finset.range m, e (F^[k] x) :=
        ih hm fun k hk => hexp k (by omega)
      have hlast : 1 ≤ e (F^[m] x) := le_of_lt (hexp m (by omega))
      rw [Finset.prod_range_succ]
      calc 1 < ∏ k ∈ Finset.range m, e (F^[k] x) := hprev
        _ = (∏ k ∈ Finset.range m, e (F^[k] x)) * 1 := (mul_one _).symm
        _ ≤ (∏ k ∈ Finset.range m, e (F^[k] x)) * e (F^[m] x) :=
            Nat.mul_le_mul_left _ hlast

/-- **Simple logarithmic pole on every recurrent component.** A periodic prime in the divisorial
support of an eigenvolume, with expanding ramification along its cycle, has order exactly `-1`.
No iterate of the map is taken. -/
theorem eigenvolumeOrder_eq_neg_one_of_periodic
    (hlaw : ∀ x, c x + 1 = (e x : ℤ) * (c (F x) + 1))
    (hexp : ∀ y, c y ≠ 0 → 1 < e y)
    {x : α} (hx : c x ≠ 0) {n : ℕ} (hn : 0 < n) (hper : F^[n] x = x) :
    c x = -1 := by
  have horbit : ∀ k < n, c (F^[k] x) ≠ 0 := by
    intro k hk
    refine order_ne_zero_of_iterate_ne_zero hlaw (n - k) (F^[k] x) ?_
    rw [← Function.iterate_add_apply F (n - k) k x,
      show n - k + k = n from Nat.sub_add_cancel (le_of_lt hk), hper]
    exact hx
  have hprodpos : 1 < ∏ k ∈ Finset.range n, e (F^[k] x) :=
    one_lt_prod_iterate_of_expanding n hn fun k hk => hexp _ (horbit k hk)
  have hshift := shift_eq_prod_iterate hlaw n x
  rw [hper] at hshift
  refine ramificationShift_fixed_eq_neg_one hprodpos ?_
  rw [Nat.cast_prod]
  exact hshift

/-- A single ramified place on a cycle already makes the product of indices exceed one. -/
theorem one_lt_prod_iterate_of_exists_ramified {x : α} (hone : ∀ y, 1 ≤ e y)
    {n : ℕ} (hram : ∃ k < n, 1 < e (F^[k] x)) :
    1 < ∏ k ∈ Finset.range n, e (F^[k] x) := by
  classical
  obtain ⟨k, hk, hek⟩ := hram
  have hmem : k ∈ Finset.range n := Finset.mem_range.mpr hk
  rw [← Finset.mul_prod_erase _ _ hmem]
  have hrest : 1 ≤ ∏ j ∈ (Finset.range n).erase k, e (F^[j] x) :=
    Finset.one_le_prod' fun j _ => hone _
  calc 1 < e (F^[k] x) := hek
    _ = e (F^[k] x) * 1 := (mul_one _).symm
    _ ≤ e (F^[k] x) * ∏ j ∈ (Finset.range n).erase k, e (F^[j] x) :=
        Nat.mul_le_mul_left _ hrest

/-- **Sharp form of the horizon quantization.**  A periodic prime whose cycle carries ramification
at even one place already has eigenvolume order exactly `-1`.  No expansion at every component, no
finiteness of the support, and no surjectivity are needed. -/
theorem eigenvolumeOrder_eq_neg_one_of_ramifiedCycle
    (hone : ∀ y, 1 ≤ e y)
    (hlaw : ∀ x, c x + 1 = (e x : ℤ) * (c (F x) + 1))
    {x : α} {n : ℕ} (hper : F^[n] x = x)
    (hram : ∃ k < n, 1 < e (F^[k] x)) :
    c x = -1 := by
  have hprodpos : 1 < ∏ k ∈ Finset.range n, e (F^[k] x) :=
    one_lt_prod_iterate_of_exists_ramified hone hram
  have hshift := shift_eq_prod_iterate hlaw n x
  rw [hper] at hshift
  refine ramificationShift_fixed_eq_neg_one hprodpos ?_
  rw [Nat.cast_prod]
  exact hshift

end RamificationSystem

section BackwardOrbit

variable {α : Type*} {F : α → α}

/-- A backward orbit inside a preimage-stable set through a surjective map returns: every point of
a finite preimage-stable set is periodic. -/
theorem exists_pos_iterate_eq_self_of_backwardStable
    (hF : Function.Surjective F) {S : Set α} (hS : S.Finite)
    (hstab : ∀ x, F x ∈ S → x ∈ S) {x : α} (hx : x ∈ S) :
    ∃ n, 0 < n ∧ F^[n] x = x := by
  classical
  have _ : Finite S := hS.to_subtype
  set g : α → α := Function.surjInv hF with hg
  have hgspec : ∀ y, F (g y) = y := fun y => Function.surjInv_eq hF y
  have hmem : ∀ m : ℕ, g^[m] x ∈ S := by
    intro m
    induction m with
    | zero => simpa using hx
    | succ k ih =>
      refine hstab _ ?_
      rw [Function.iterate_succ_apply' g k x, hgspec]
      exact ih
  have hround : ∀ m : ℕ, F^[m] (g^[m] x) = x := by
    intro m
    induction m with
    | zero => simp
    | succ k ih =>
      rw [Function.iterate_succ_apply' g k x, Function.iterate_succ_apply F k _, hgspec]
      exact ih
  obtain ⟨i, j, hij, heq⟩ :=
    Finite.exists_ne_map_eq_of_infinite (fun m : ℕ => (⟨g^[m] x, hmem m⟩ : S))
  have hval : g^[i] x = g^[j] x := congrArg Subtype.val heq
  rcases Nat.lt_or_ge i j with hlt | hge
  · refine ⟨j - i, Nat.sub_pos_of_lt hlt, ?_⟩
    have hj : g^[j] x = g^[j - i] (g^[i] x) := by
      rw [← Function.iterate_add_apply g (j - i) i x,
        show j - i + i = j from Nat.sub_add_cancel (le_of_lt hlt)]
    calc F^[j - i] x = F^[j - i] (F^[i] (g^[i] x)) := by rw [hround i]
      _ = F^[j - i + i] (g^[i] x) := by rw [Function.iterate_add_apply F (j - i) i]
      _ = F^[j] (g^[i] x) := by
          rw [show j - i + i = j from Nat.sub_add_cancel (le_of_lt hlt)]
      _ = F^[j] (g^[j] x) := by rw [hval]
      _ = x := hround j
  · have hlt' : j < i := lt_of_le_of_ne hge (fun h => hij (by omega))
    refine ⟨i - j, Nat.sub_pos_of_lt hlt', ?_⟩
    calc F^[i - j] x = F^[i - j] (F^[j] (g^[j] x)) := by rw [hround j]
      _ = F^[i - j + j] (g^[j] x) := by rw [Function.iterate_add_apply F (i - j) j]
      _ = F^[i] (g^[j] x) := by
          rw [show i - j + j = i from Nat.sub_add_cancel (le_of_lt hlt')]
      _ = F^[i] (g^[i] x) := by rw [hval]
      _ = x := hround i

end BackwardOrbit

section Horizon

variable {α : Type*} {F : α → α} {c : α → ℤ} {e : α → ℕ}

/-- **The eigenvolume horizon is reduced.** If the image map on primes is onto, the divisorial
support of the eigenvolume is finite, and ramification is expanding on that support, then the
eigenvolume has a simple pole along every component of its support: `div Ω = -D` with `D`
reduced. -/
theorem eigenvolumeOrder_eq_neg_one
    (hF : Function.Surjective F)
    (hlaw : ∀ x, c x + 1 = (e x : ℤ) * (c (F x) + 1))
    (hfin : {y : α | c y ≠ 0}.Finite)
    (hexp : ∀ y, c y ≠ 0 → 1 < e y)
    {x : α} (hx : c x ≠ 0) :
    c x = -1 := by
  obtain ⟨n, hn, hper⟩ :=
    exists_pos_iterate_eq_self_of_backwardStable hF hfin
      (fun y hy => order_ne_zero_of_image_ne_zero hlaw hy) hx
  exact eigenvolumeOrder_eq_neg_one_of_periodic hlaw hexp hx hn hper

/-- **The horizon is totally invariant.** Under the hypotheses of the horizon theorem a prime lies
in the divisorial support exactly when its image does, so `f⁻¹(D) = D`. -/
theorem order_ne_zero_iff_image_ne_zero
    (hF : Function.Surjective F)
    (hone : ∀ x, 1 ≤ e x)
    (hlaw : ∀ x, c x + 1 = (e x : ℤ) * (c (F x) + 1))
    (hfin : {y : α | c y ≠ 0}.Finite)
    (hexp : ∀ y, c y ≠ 0 → 1 < e y)
    (x : α) : c x ≠ 0 ↔ c (F x) ≠ 0 := by
  refine ⟨fun hx => ?_, fun hx => order_ne_zero_of_image_ne_zero hlaw hx⟩
  have hxval : c x = -1 := eigenvolumeOrder_eq_neg_one hF hlaw hfin hexp hx
  have h := hlaw x
  rw [hxval] at h
  have hzero : (e x : ℤ) * (c (F x) + 1) = 0 := by linarith
  have hepos : (e x : ℤ) ≠ 0 := by
    have := hone x
    omega
  have : c (F x) + 1 = 0 := by
    rcases mul_eq_zero.mp hzero with h' | h'
    · exact absurd h' hepos
    · exact h'
  omega

/-- **The map is unramified off the horizon.** A prime outside the divisorial support carries
ramification index one, so the whole ramification divisor is supported on the boundary. -/
theorem ramificationIndex_eq_one_of_order_eq_zero
    (hlaw : ∀ x, c x + 1 = (e x : ℤ) * (c (F x) + 1))
    {x : α} (hx : c x = 0) : e x = 1 := by
  have himg : c (F x) = 0 := by
    by_contra hcon
    exact (order_ne_zero_of_image_ne_zero hlaw hcon) hx
  have h := hlaw x
  rw [hx, himg] at h
  have : (e x : ℤ) = 1 := by linarith
  exact_mod_cast this

/-- **Ramification is the pullback difference of the reduced boundary.** On the horizon the
boundary coefficient is `1` on both sides, so the ramification coefficient `e - 1` equals the
coefficient of `f^* D - D`. -/
theorem ramificationCoefficient_eq_pullback_sub
    {x : α} (hx : c x = -1) (hFx : c (F x) = -1) :
    ((e x : ℤ) - 1) = (e x : ℤ) * (-(c (F x))) - (-(c x)) := by
  rw [hx, hFx]; ring

/-- **The horizon is reduced under the sharp ramification hypothesis.**  It suffices that every
cycle inside the divisorial support carries ramification at one place; expansion at every
component is not needed. -/
theorem eigenvolumeOrder_eq_neg_one_of_someRamified
    (hF : Function.Surjective F)
    (hone : ∀ y, 1 ≤ e y)
    (hlaw : ∀ x, c x + 1 = (e x : ℤ) * (c (F x) + 1))
    (hfin : {y : α | c y ≠ 0}.Finite)
    (hram : ∀ y : α, c y ≠ 0 → ∀ n : ℕ, 0 < n → F^[n] y = y →
      ∃ k < n, 1 < e (F^[k] y))
    {x : α} (hx : c x ≠ 0) :
    c x = -1 := by
  obtain ⟨n, hn, hper⟩ :=
    exists_pos_iterate_eq_self_of_backwardStable hF hfin
      (fun y hy => order_ne_zero_of_image_ne_zero hlaw hy) hx
  exact eigenvolumeOrder_eq_neg_one_of_ramifiedCycle hone hlaw hper (hram x hx n hn hper)

end Horizon

section Sharpness

/-- **Expansion is necessary.** Without an expanding ramification index the order law has
nonlogarithmic solutions, even on a one-point support. -/
theorem exists_nonexpanding_order_ne_neg_one :
    ∃ (F : Unit → Unit) (c : Unit → ℤ) (e : Unit → ℕ),
      Function.Surjective F ∧
      (∀ x, c x + 1 = (e x : ℤ) * (c (F x) + 1)) ∧
      {y : Unit | c y ≠ 0}.Finite ∧
      ∃ x, c x ≠ 0 ∧ c x ≠ -1 := by
  refine ⟨id, fun _ => 5, fun _ => 1, Function.surjective_id, fun _ => by norm_num,
    Set.toFinite _, ⟨(), by norm_num, by norm_num⟩⟩

/-- **Finiteness of the divisorial support is necessary.** On an infinite support the order law
with expanding ramification has solutions of arbitrary positive order: the backward orbit never
returns, so no cycle equation is available. -/
theorem exists_infiniteSupport_order_ne_neg_one :
    ∃ (F : ℕ → ℕ) (c : ℕ → ℤ) (e : ℕ → ℕ),
      Function.Surjective F ∧
      (∀ x, c x + 1 = (e x : ℤ) * (c (F x) + 1)) ∧
      (∀ y, c y ≠ 0 → 1 < e y) ∧
      ∃ x, c x ≠ 0 ∧ c x ≠ -1 := by
  refine ⟨fun n => n - 1, fun n => 2 ^ n - 1, fun n => if n = 0 then 1 else 2, ?_, ?_, ?_,
    1, ?_, ?_⟩
  · exact fun n => ⟨n + 1, by simp⟩
  · intro x
    match x with
    | 0 => norm_num
    | (m + 1) =>
      have hne : m + 1 ≠ 0 := Nat.succ_ne_zero m
      simp only [Nat.add_sub_cancel, if_neg hne]
      push_cast
      ring
  · intro y hy
    match y with
    | 0 => simp at hy
    | (m + 1) =>
      have hne : m + 1 ≠ 0 := Nat.succ_ne_zero m
      simp only [if_neg hne]
      omega
  · norm_num
  · norm_num

end Sharpness

end GaloisForLFunctions.HTGeometry
