import Mathlib

/-!
# A separated comb is one orbit of the Frobenius monoid

The contacts of the pairing sit on the pairs `(x, kx)`, `k` a positive integer: a comb that
carries them is stable under the multiplications `F_k : x ↦ kx`. The jets are
`½(1/|x − y| + 1/(x + y))`: they are bounded off the diagonal only on a comb whose points are
uniformly separated. This file classifies the combs with both properties.

* **Incommensurable orbits collide** (`exists_near_collision`): for an irrational ratio `θ` the
  orbits `ℕ` and `θℕ` have points `j`, `kθ` at every positive distance below any `ε`. The jet
  between the two orbits is unbounded.
* **Ratios are rational** (`exists_ratio_of_separated`) and **denominators are bounded**
  (`den_le_of_separated`): in a separated stable comb every point is `α·a/b` with `b ≤ α/σ`,
  for a fixed point `α` and the separation `σ`. A point `α·a/b` in lowest terms and the point `α`
  have multiples at the distance `α/b`.
* **One orbit** (`exists_orbit_of_separated`): a set of positive reals that is stable under the
  Frobenius monoid and uniformly separated lies in one orbit `δℕ`.
* **The orbit of a generator** (`eq_orbit_of_generator_mem`): a stable subset of `δℕ` that
  contains `δ` is the whole orbit. Up to the torus, the comb of all degree points is the only
  separated comb that carries every contact from one point.
-/

noncomputable section

namespace GaloisForLFunctions.HodgeTheoryOfAFixedPart

/-- A comb is stable under the Frobenius monoid: with `x` it contains every `kx`, `k ≥ 1`. -/
def FrobeniusStable (S : Set ℝ) : Prop := ∀ x ∈ S, ∀ k : ℕ, 0 < k → (k : ℝ) * x ∈ S

/-- A comb is `σ`-separated: distinct points are at distance at least `σ`. -/
def Separated (σ : ℝ) (S : Set ℝ) : Prop := ∀ x ∈ S, ∀ y ∈ S, x ≠ y → σ ≤ |x - y|

/-- The orbit of `δ` under the Frobenius monoid. -/
def frobeniusOrbit (δ : ℝ) : Set ℝ := {x | ∃ n : ℕ, 0 < n ∧ x = n * δ}

theorem frobeniusStable_orbit (δ : ℝ) : FrobeniusStable (frobeniusOrbit δ) := by
  rintro x ⟨n, hn, rfl⟩ k hk
  exact ⟨k * n, Nat.mul_pos hk hn, by push_cast; ring⟩

theorem separated_orbit {δ : ℝ} (hδ : 0 < δ) : Separated δ (frobeniusOrbit δ) := by
  rintro x ⟨m, -, rfl⟩ y ⟨n, -, rfl⟩ hne
  have hmn : m ≠ n := fun h => hne (by rw [h])
  have h1 : (1 : ℝ) ≤ |(m : ℝ) - n| := by
    have : (1 : ℤ) ≤ |(m : ℤ) - n| := Int.one_le_abs (sub_ne_zero.mpr (by exact_mod_cast hmn))
    exact_mod_cast this
  rw [← sub_mul, abs_mul, abs_of_pos hδ]
  nlinarith

/-! ### Incommensurable orbits collide -/

/-- **Incommensurable orbits collide.** For an irrational `θ > 0` and every `ε > 0` there are
positive integers `k, j` with `0 < |kθ − j| < ε`. -/
theorem exists_near_collision {θ : ℝ} (hθ : Irrational θ) (hθ0 : 0 < θ) {ε : ℝ} (hε : 0 < ε) :
    ∃ k j : ℕ, 0 < k ∧ 0 < j ∧ (k : ℝ) * θ ≠ j ∧ |(k : ℝ) * θ - j| < ε := by
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (lt_min hε hθ0)
  obtain ⟨k, hk0, -, hk⟩ := Real.exists_nat_abs_mul_sub_round_le θ (Nat.succ_pos n)
  have hk0' : (1 : ℝ) ≤ k := by exact_mod_cast hk0
  have hsmall : |(k : ℝ) * θ - round ((k : ℝ) * θ)| < min ε θ := by
    refine lt_of_le_of_lt hk (lt_of_le_of_lt ?_ hn)
    have h1 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    rw [div_le_div_iff₀ (by positivity) h1]
    push_cast
    linarith
  have hlt1 := lt_of_lt_of_le hsmall (min_le_left _ _)
  have hlt2 := lt_of_lt_of_le hsmall (min_le_right _ _)
  -- the rounded value is a positive integer
  have hjpos : (0 : ℝ) < (round ((k : ℝ) * θ) : ℤ) := by
    have h1 := (abs_lt.mp hlt2).2
    nlinarith
  have hjpos' : 0 < round ((k : ℝ) * θ) := by exact_mod_cast hjpos
  have hcast : ((round ((k : ℝ) * θ)).toNat : ℝ) = (round ((k : ℝ) * θ) : ℤ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hjpos'.le)
  refine ⟨k, (round ((k : ℝ) * θ)).toNat, hk0, by omega, ?_, by rw [hcast]; exact hlt1⟩
  rw [hcast]
  intro h
  refine hθ ⟨(round ((k : ℝ) * θ) : ℚ) / k, ?_⟩
  have hk' : (k : ℝ) ≠ 0 := by positivity
  push_cast
  rw [← h]
  field_simp

/-! ### Ratios and denominators -/

variable {S : Set ℝ} {σ : ℝ}

/-- **In a separated stable comb all ratios are rational.** -/
theorem exists_ratio_of_separated (hpos : ∀ x ∈ S, 0 < x) (hst : FrobeniusStable S)
    (hσ : 0 < σ) (hsep : Separated σ S) {α x : ℝ} (hα : α ∈ S) (hx : x ∈ S) :
    ∃ r : ℚ, 0 < r ∧ x = α * r := by
  have hα0 := hpos α hα
  have hx0 := hpos x hx
  by_contra hnot
  have hirr : Irrational (x / α) := by
    rintro ⟨r, hr⟩
    refine hnot ⟨r, ?_, ?_⟩
    · have : (0 : ℝ) < r := by rw [hr]; positivity
      exact_mod_cast this
    · rw [hr]
      field_simp
  obtain ⟨k, j, hk, hj, hne, hlt⟩ :=
    exists_near_collision hirr (div_pos hx0 hα0) (div_pos hσ hα0)
  have h1 := hst x hx k hk
  have h2 := hst α hα j hj
  have hdiff : (k : ℝ) * x - j * α = α * ((k : ℝ) * (x / α) - j) := by
    field_simp
  have hne' : (k : ℝ) * x ≠ j * α := by
    intro h
    apply hne
    rw [← mul_div_assoc, h]
    field_simp
  have hs := hsep _ h1 _ h2 hne'
  rw [hdiff, abs_mul, abs_of_pos hα0] at hs
  have hup : α * |(k : ℝ) * (x / α) - j| < α * (σ / α) := mul_lt_mul_of_pos_left hlt hα0
  have e : α * (σ / α) = σ := by field_simp
  linarith

/-- **Denominators are bounded by the separation.** If `x = α·a/b` in lowest terms, then
`σ·b ≤ α`. -/
theorem den_le_of_separated (hst : FrobeniusStable S) (hsep : Separated σ S) {α x : ℝ}
    (hα0 : 0 < α) (hα : α ∈ S) (hx : x ∈ S) {a b : ℕ} (ha : 0 < a) (hb : 0 < b)
    (hab : Nat.Coprime a b) (hxab : x * b = α * a) : σ * b ≤ α := by
  rcases Nat.lt_or_ge 1 b with hb1 | hb1
  · -- `a k = b j + 1` with positive `k`, `j`
    obtain ⟨m, hm⟩ := Nat.exists_mul_emod_eq_one_of_coprime hab hb1
    have hdm := Nat.div_add_mod (a * m) b
    rw [hm] at hdm
    have hkey : a * (m + b) = b * (a * m / b + a) + 1 := by
      have e1 : a * (m + b) = a * m + a * b := by ring
      have e2 : b * (a * m / b + a) = b * (a * m / b) + a * b := by ring
      omega
    have hkS := hst x hx (m + b) (by omega)
    have hjS := hst α hα (a * m / b + a) (by omega)
    have hb' : (0 : ℝ) < b := by exact_mod_cast hb
    have hkey' : (a : ℝ) * ((m : ℝ) + b) = b * (((a * m / b : ℕ) : ℝ) + a) + 1 := by
      exact_mod_cast hkey
    have hdiff : ((m + b : ℕ) : ℝ) * x - ((a * m / b + a : ℕ) : ℝ) * α = α / b := by
      rw [eq_div_iff hb'.ne']
      push_cast
      have : ((m : ℝ) + b) * x * b = ((m : ℝ) + b) * (α * a) := by rw [mul_assoc, hxab]
      nlinarith
    have hne : ((m + b : ℕ) : ℝ) * x ≠ ((a * m / b + a : ℕ) : ℝ) * α := by
      intro h
      rw [h, sub_self] at hdiff
      have : 0 < α / b := by positivity
      linarith
    have hs := hsep _ hkS _ hjS hne
    rw [hdiff, abs_of_pos (by positivity), le_div_iff₀ hb'] at hs
    exact hs
  · obtain rfl : b = 1 := by omega
    have h2 := hst α hα 2 (by norm_num)
    have hne : ((2 : ℕ) : ℝ) * α ≠ α := by
      push_cast
      linarith
    have hs := hsep _ h2 _ hα hne
    have e : ((2 : ℕ) : ℝ) * α - α = α := by push_cast; ring
    rw [e, abs_of_pos hα0] at hs
    simpa using hs

/-! ### One orbit -/

/-- **A separated comb that is stable under the Frobenius monoid lies in one orbit.** -/
theorem exists_orbit_of_separated (hpos : ∀ x ∈ S, 0 < x) (hst : FrobeniusStable S)
    (hσ : 0 < σ) (hsep : Separated σ S) : ∃ δ : ℝ, 0 < δ ∧ S ⊆ frobeniusOrbit δ := by
  rcases S.eq_empty_or_nonempty with rfl | ⟨α, hα⟩
  · exact ⟨1, one_pos, Set.empty_subset _⟩
  have hα0 := hpos α hα
  refine ⟨α / ((⌊α / σ⌋₊).factorial : ℝ), by positivity, fun x hx => ?_⟩
  obtain ⟨r, hr0, hr⟩ := exists_ratio_of_separated hpos hst hσ hsep hα hx
  have hnum : 0 < r.num := Rat.num_pos.mpr hr0
  have hcast : ((r.num.toNat : ℕ) : ℝ) = (r.num : ℝ) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℝ)) (Int.toNat_of_nonneg hnum.le)
  have hden : (0 : ℝ) < r.den := by exact_mod_cast r.den_pos
  have hcop : Nat.Coprime r.num.toNat r.den := by
    have h := r.reduced
    have e : r.num.natAbs = r.num.toNat := by omega
    rwa [e] at h
  have hxab : x * r.den = α * (r.num.toNat : ℕ) := by
    rw [hr, hcast, Rat.cast_def]
    field_simp
  have hb := den_le_of_separated hst hsep hα0 hα hx (by omega : 0 < r.num.toNat) r.den_pos hcop
    hxab
  have hbB : r.den ≤ ⌊α / σ⌋₊ := Nat.le_floor (by rw [le_div_iff₀ hσ]; linarith)
  obtain ⟨t, ht⟩ := Nat.dvd_factorial r.den_pos hbB
  have ht0 : 0 < t := by
    rcases Nat.eq_zero_or_pos t with rfl | h
    · rw [mul_zero] at ht
      exact absurd ht (Nat.factorial_ne_zero _)
    · exact h
  have ht' : (0 : ℝ) < t := by exact_mod_cast ht0
  refine ⟨r.num.toNat * t, Nat.mul_pos (by omega) ht0, ?_⟩
  have hfac : ((⌊α / σ⌋₊).factorial : ℝ) = (r.den : ℝ) * t := by exact_mod_cast ht
  have hx' : x = α * (r.num.toNat : ℕ) / r.den := by
    rw [eq_div_iff hden.ne']
    exact hxab
  rw [hfac, hx']
  push_cast
  field_simp

/-- **The orbit of a generator.** A stable subset of the orbit of `δ` that contains `δ` is the
whole orbit. -/
theorem eq_orbit_of_generator_mem {δ : ℝ} (hst : FrobeniusStable S) (hsub : S ⊆ frobeniusOrbit δ)
    (hδ : δ ∈ S) : S = frobeniusOrbit δ :=
  Set.Subset.antisymm hsub fun _ ⟨n, hn, hx⟩ => hx ▸ hst δ hδ n hn

end GaloisForLFunctions.HodgeTheoryOfAFixedPart
