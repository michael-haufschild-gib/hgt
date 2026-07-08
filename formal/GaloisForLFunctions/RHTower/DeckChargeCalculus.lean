/-
The additive deck-charge calculus.

The obstruction to lifting a nonvanishing holomorphic `f` through `z ↦ z^n` around a loop is a
`2^k`-torsion class; on the two-chart annulus cover it is read off from the **integer** total
order `idx = Σ mᵢ` of the enclosed zeros as the multiplicative deck class `deckRed n idx ∈ μ_n`
(`box_charge_eq_deckRed`).  This file gives that same obstruction its **additive** avatar — the
charge `wCharge n idx = (idx : ℤ/n)` — and proves the two faces are the same object under a group
isomorphism `ℤ/n ≃* ⟨deckUnitHom n⟩ ≤ ℂˣ` (`deckIso`): the deck class is a genuine element of the
cyclic group `ℤ/n`, hence obeys an additive law.

The calculus deliverables:

* additivity `wCharge n (j + k) = wCharge n j + wCharge n k` (orders of a product add) with its
  multiplicative face `deckChar n (a + b) = deckChar n a * deckChar n b`;
* the power law `wCharge n (r * k) = r • wCharge n k` and `deckChar n (r • x) = deckChar n x ^ r`
  (an `r`-th power multiplies the index by `r`);
* vanishing `wCharge n idx = 0` iff `n ∣ idx` iff the multiplicative deck class is trivial iff a
  coherent global `n`-th root exists across the annulus (`exists_root_iff_wCharge_zero`);
* the additive conservation law `interior_charge_conservation`: if the total (outer-boundary)
  charge vanishes, the interior box charges sum to zero in `ℤ/n`.

The charge is a constraint invariant (a cocycle/obstruction class), not a propagated quantity:
every statement below is a property of the *given* index data, with no carrier or flow constructed.
-/
import GaloisForLFunctions.RHTower.SignatureParity
import GaloisForLFunctions.RHTower.DeckCocycle

open Complex

namespace RHTower

/-! ### §1 The additive deck charge `w ∈ ℤ/n` -/

/-- The additive deck charge of an integer winding/zero-index at modulus `n`: its residue class in
`ℤ/n`.  This is the additive avatar of the multiplicative deck class `deckRed n`. -/
def wCharge (n : ℕ) (idx : ℤ) : ZMod n := (idx : ZMod n)

@[simp] theorem wCharge_zero (n : ℕ) : wCharge n 0 = 0 := by simp [wCharge]

/-- **Additivity.**  The index of a product is the sum of the indices, so the charge is additive:
`w(fg) = w(f) + w(g)` at the level of the enclosed order. -/
theorem wCharge_add (n : ℕ) (j k : ℤ) : wCharge n (j + k) = wCharge n j + wCharge n k := by
  simp [wCharge]

theorem wCharge_neg (n : ℕ) (k : ℤ) : wCharge n (-k) = -wCharge n k := by simp [wCharge]

/-- **Power law.**  Taking an `r`-th power multiplies the index by `r`, so the charge scales:
`w(f^r) = r • w(f)`. -/
theorem wCharge_intMul (n : ℕ) (r k : ℤ) : wCharge n (r * k) = r • wCharge n k := by
  unfold wCharge; rw [Int.cast_mul, zsmul_eq_mul]

theorem wCharge_nsmul (n : ℕ) (r : ℕ) (k : ℤ) : wCharge n ((r : ℤ) * k) = r • wCharge n k := by
  unfold wCharge; rw [Int.cast_mul, Int.cast_natCast, nsmul_eq_mul]

/-- **Charge of a family.**  The total charge of a finite family of enclosed configurations is the
sum of the individual charges (the integer index is additive over the family). -/
theorem wCharge_sum (n : ℕ) {ι : Type*} (s : Finset ι) (idx : ι → ℤ) :
    wCharge n (∑ i ∈ s, idx i) = ∑ i ∈ s, wCharge n (idx i) := by
  simp only [wCharge]; push_cast; rfl

/-- **Vanishing criterion.**  The charge is zero exactly when the index is divisible by `n`. -/
theorem wCharge_eq_zero_iff {n : ℕ} [NeZero n] (idx : ℤ) :
    wCharge n idx = 0 ↔ (n : ℤ) ∣ idx :=
  ZMod.intCast_zmod_eq_zero_iff_dvd idx n

/-! ### §2 The multiplicative avatar: the `n`-th-root-of-unity character on `ℤ/n` -/

/-- Every `n`-th deck value is a root of unity: `(deckRed n k)^n = 1`. -/
theorem deckRed_pow_self {n : ℕ} (hn : 0 < n) (k : ℤ) : (deckRed n k) ^ n = 1 := by
  rw [deckRed, ← Complex.exp_nat_mul]
  have hn0 : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rw [show (n : ℂ) * (2 * (Real.pi : ℂ) * I * (k : ℂ) / (n : ℂ))
      = (k : ℂ) * (2 * (Real.pi : ℂ) * I) from by field_simp]
  exact Complex.exp_int_mul_two_pi_mul_I k

/-- The deck character on `ℤ/n`: the multiplicative avatar of the additive charge, `deckRed`
transported along the canonical section `ZMod.val`. -/
noncomputable def deckChar (n : ℕ) (x : ZMod n) : ℂ := deckRed n (ZMod.val x : ℤ)

private theorem deckChar_ne_zero (n : ℕ) (x : ZMod n) : deckChar n x ≠ 0 := deckRed_ne_zero _ _

private theorem val_natCast {n : ℕ} [NeZero n] (x : ZMod n) :
    ((ZMod.val x : ℕ) : ZMod n) = x := ZMod.natCast_rightInverse x

@[simp] theorem deckChar_zero (n : ℕ) [NeZero n] : deckChar n 0 = 1 := by
  unfold deckChar; simp [ZMod.val_zero, deckRed_zero]

/-- **The two avatars agree.**  The deck character of the additive charge is the multiplicative
deck class of the index: `deckChar n (wCharge n idx) = deckRed n idx`. -/
theorem deckChar_wCharge {n : ℕ} [NeZero n] (idx : ℤ) :
    deckChar n (wCharge n idx) = deckRed n idx := by
  unfold deckChar wCharge
  rw [deckRed_eq_iff_zmod (NeZero.pos n)]
  push_cast [val_natCast]; rfl

/-- **Multiplicativity of the character** = additivity of the charge, read multiplicatively. -/
theorem deckChar_mul {n : ℕ} [NeZero n] (a b : ZMod n) :
    deckChar n (a + b) = deckChar n a * deckChar n b := by
  unfold deckChar
  rw [← deckRed_add, deckRed_eq_iff_zmod (NeZero.pos n)]
  push_cast [val_natCast]; rfl

/-- The character is injective: distinct charges give distinct roots of unity. -/
theorem deckChar_injective {n : ℕ} [NeZero n] : Function.Injective (deckChar n) := by
  intro a b hab
  unfold deckChar at hab
  rw [deckRed_eq_iff_zmod (NeZero.pos n)] at hab
  push_cast [val_natCast] at hab
  exact hab

/-- The multiplicative power law: `deckChar n (r • x) = (deckChar n x)^r`. -/
theorem deckChar_nsmul {n : ℕ} [NeZero n] (r : ℕ) (x : ZMod n) :
    deckChar n (r • x) = (deckChar n x) ^ r := by
  induction r with
  | zero => simp
  | succ m ih => rw [succ_nsmul, deckChar_mul, ih, pow_succ]

/-- The multiplicative face of `wCharge_sum`: the character of a sum of charges is the product of
the characters (the conservation law's multiplicative form). -/
theorem deckChar_sum {n : ℕ} [NeZero n] {ι : Type*} (s : Finset ι) (w : ι → ZMod n) :
    deckChar n (∑ i ∈ s, w i) = ∏ i ∈ s, deckChar n (w i) := by
  classical
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a t ha ih
    rw [Finset.sum_insert ha, Finset.prod_insert ha, deckChar_mul, ih]

/-- The character lands in the `n`-th roots of unity. -/
theorem deckChar_pow_eq_one {n : ℕ} [NeZero n] (x : ZMod n) : (deckChar n x) ^ n = 1 :=
  deckRed_pow_self (NeZero.pos n) _

/-! ### §3 Charge zero ⟺ trivial deck class ⟺ a coherent global root exists -/

/-- The additive vanishing criterion in multiplicative form: charge zero ⟺ deck class trivial. -/
theorem wCharge_eq_zero_iff_deckRed_eq_one {n : ℕ} [NeZero n] (idx : ℤ) :
    wCharge n idx = 0 ↔ deckRed n idx = 1 :=
  (wCharge_eq_zero_iff idx).trans (deckRed_eq_one_iff (NeZero.pos n) idx).symm

/-- **Deformation transfer.**  Equal deck class forces equal additive charge; so any homotopy
invariance of the (multiplicative) deck class transfers to the additive charge. -/
theorem wCharge_eq_of_deckRed_eq {n : ℕ} [NeZero n] {i j : ℤ}
    (h : deckRed n i = deckRed n j) : wCharge n i = wCharge n j :=
  deckChar_injective (by rw [deckChar_wCharge, deckChar_wCharge]; exact h)

/-- **The two faces on the box geometry.**  On the slit-annulus two-chart cover, the box deck class
is the deck character of the additive charge of the enclosed integer index. -/
theorem box_deckClass_eq_deckChar_wCharge {ι : Type*} (s : Finset ι) (ρ : ι → ℂ) (m : ι → ℕ)
    {f h G₁ G₂ : ℂ → ℂ} {a : ℂ} {r₀ R : ℝ} (h0 : 0 ≤ r₀) (hrR : r₀ < R)
    {n : ℕ} [NeZero n]
    (hρ : ∀ i ∈ s, ‖ρ i - a‖ ≤ r₀)
    (hh : AnalyticOnNhd ℂ h (Metric.ball a R)) (hh0 : ∀ z ∈ Metric.ball a R, h z ≠ 0)
    (hfact : ∀ z ∈ Metric.ball a R, f z = (∏ i ∈ s, (z - ρ i) ^ m i) * h z)
    (hG₁ : AnalyticOnNhd ℂ G₁ (chartRA a r₀ R)) (hG₂ : AnalyticOnNhd ℂ G₂ (chartLA a r₀ R))
    (hpG₁ : ∀ z ∈ chartRA a r₀ R, G₁ z ^ n = f z)
    (hpG₂ : ∀ z ∈ chartLA a r₀ R, G₂ z ^ n = f z) :
    deckClass G₁ G₂ (a + (((r₀ + R) / 2 : ℝ) : ℂ) * I) (a - (((r₀ + R) / 2 : ℝ) : ℂ) * I) =
      deckChar n (wCharge n (↑(∑ i ∈ s, m i))) := by
  rw [deckChar_wCharge]
  exact box_charge_eq_deckRed s ρ m h0 hrR (NeZero.pos n) hρ hh hh0 hfact hG₁ hG₂ hpG₁ hpG₂

/-- **Vanishing charge ⟺ a coherent global `n`-th root.**  On any valid two-chart cover, once the
deck class is identified with the charge of an index `idx` (`hlink`, supplied concretely by
`box_deckClass_eq_deckChar_wCharge`/`box_charge_eq_deckRed`), the charge vanishes exactly when `f`
admits a global analytic `n`-th root across the cover. -/
theorem exists_root_iff_wCharge_zero {f g₁ g₂ : ℂ → ℂ} {U₁ U₂ VP VM : Set ℂ} {n : ℕ} [NeZero n]
    (hU₁ : IsOpen U₁) (hU₁c : IsPreconnected U₁) (hU₂ : IsOpen U₂) (hU₂c : IsPreconnected U₂)
    (hVP : IsOpen VP) (hVPc : IsPreconnected VP) (hVM : IsOpen VM) (hVMc : IsPreconnected VM)
    (hcap : U₁ ∩ U₂ = VP ∪ VM)
    (hg₁ : AnalyticOnNhd ℂ g₁ U₁) (hg₂ : AnalyticOnNhd ℂ g₂ U₂)
    (hpg₁ : ∀ s ∈ U₁, g₁ s ^ n = f s) (hpg₂ : ∀ s ∈ U₂, g₂ s ^ n = f s)
    {pP pM : ℂ} (hpP : pP ∈ VP) (hpM : pM ∈ VM) (hfP : f pP ≠ 0) (hfM : f pM ≠ 0)
    (idx : ℤ) (hlink : deckClass g₁ g₂ pP pM = deckRed n idx) :
    wCharge n idx = 0 ↔
      ∃ g : ℂ → ℂ, AnalyticOnNhd ℂ g (U₁ ∪ U₂) ∧ ∀ s ∈ U₁ ∪ U₂, g s ^ n = f s := by
  rw [wCharge_eq_zero_iff_deckRed_eq_one, ← hlink]
  exact deckClass_eq_one_iff_exists_root (NeZero.pos n) hU₁ hU₁c hU₂ hU₂c hVP hVPc hVM hVMc hcap
    hg₁ hg₂ hpg₁ hpg₂ hpP hpM hfP hfM

/-! ### §4 The cyclic-group structure and the additive conservation law -/

/-- The deck charge as a unit of `ℂ` — a genuine `n`-th root of unity in the group `ℂˣ`. -/
noncomputable def deckUnit (n : ℕ) (x : ZMod n) : ℂˣ :=
  Units.mk0 (deckChar n x) (deckChar_ne_zero n x)

@[simp] theorem deckUnit_val (n : ℕ) (x : ZMod n) : (deckUnit n x : ℂ) = deckChar n x := rfl

/-- The charge homomorphism `(ℤ/n, +) → ℂˣ`. -/
noncomputable def deckUnitHom (n : ℕ) [NeZero n] : Multiplicative (ZMod n) →* ℂˣ where
  toFun x := deckUnit n (Multiplicative.toAdd x)
  map_one' := by apply Units.ext; simp [deckUnit]
  map_mul' a b := by apply Units.ext; simp [deckUnit, deckChar_mul]

theorem deckUnitHom_injective (n : ℕ) [NeZero n] : Function.Injective (deckUnitHom n) := by
  intro a b hab
  have hval : deckChar n (Multiplicative.toAdd a) = deckChar n (Multiplicative.toAdd b) := by
    have := congrArg Units.val hab
    simpa [deckUnitHom, deckUnit] using this
  exact deckChar_injective hval

/-- **The deck charge is a cyclic-group element.**  `ℤ/n` is isomorphic, via the charge, to the
group of `n`-th roots of unity `⟨deckUnitHom n⟩ ≤ ℂˣ` — the exact sense in which the multiplicative
deck class and the additive charge are one object. -/
noncomputable def deckIso (n : ℕ) [NeZero n] :
    Multiplicative (ZMod n) ≃* (deckUnitHom n).range :=
  MonoidHom.ofInjective (deckUnitHom_injective n)

/-- **Boundary-crossing formula.**  The change in deck charge across a deformation equals the charge
of the net zero-order that crossed the boundary: `w(after) − w(before) = w(after − before)`.  In
particular a deformation across which no net order crosses (`after = before`) leaves the charge
invariant — the homotopy invariance of the charge, in additive form. -/
theorem wCharge_boundary_crossing (n : ℕ) (before after : ℤ) :
    wCharge n after - wCharge n before = wCharge n (after - before) := by
  simp [wCharge, Int.cast_sub]

/-- **Additive conservation.**  If the total (outer-boundary) charge vanishes, the interior box
charges sum to zero in `ℤ/n`: charge cannot be created or destroyed in the interior. -/
theorem interior_charge_conservation (n : ℕ) {ι : Type*} (s : Finset ι) (idx : ι → ℤ)
    (hbdry : wCharge n (∑ i ∈ s, idx i) = 0) :
    ∑ i ∈ s, wCharge n (idx i) = 0 := by rw [← wCharge_sum]; exact hbdry

/-! ### §5 The dyadic tower: the charge reduces coherently down the rungs -/

/-- **Dyadic-tower coherence.**  The ring reduction `ℤ/2^k ↠ ℤ/2^j` (for `j ≤ k`) carries the
rung-`k` charge to the rung-`j` charge: `wCharge (2^k) idx ↦ wCharge (2^j) idx`.  The additive deck
charge is one coherent system over the whole `2^k`-ladder, not a family of unrelated residues. -/
theorem wCharge_tower {j k : ℕ} (hjk : j ≤ k) (idx : ℤ) :
    ZMod.castHom (pow_dvd_pow 2 hjk) (ZMod (2 ^ j)) (wCharge (2 ^ k) idx) = wCharge (2 ^ j) idx := by
  unfold wCharge; rw [map_intCast]

/-- **Triviality descends the ladder.**  If the rung-`k` charge vanishes, so does every lower rung's:
a coherent `2^k`-th root forces coherent `2^j`-th roots for all `j ≤ k`. -/
theorem wCharge_eq_zero_of_le {j k : ℕ} (hjk : j ≤ k) {idx : ℤ}
    (h : wCharge (2 ^ k) idx = 0) : wCharge (2 ^ j) idx = 0 := by
  rw [← wCharge_tower hjk, h, map_zero]

end RHTower
