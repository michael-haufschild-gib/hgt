import GaloisForLFunctions.ConstituentTheoryOfTheZeros.TheJumpLawHoldsOnEveryStripAboutTheLine

/-!
# The jump law is the law of the carry

Over `𝔽_q[T]` the digits of a sum are the sums of the digits, and the proof of the Riemann
hypothesis by Newton polygons counts carry-free compositions. Over `ℤ` the carry is a cocycle that
is not a coboundary. What takes the place of the carry-free calculus is the carry itself, counted
with the weights of an expansion.

* **The carry** (`carry`): `κ(x, y) = {x} + {y} − {x + y} = ⌊x + y⌋ − ⌊x⌋ − ⌊y⌋ ∈ {0, 1}`, a
  cocycle (`carry_cocycle`); on `x/p`, `y/p` with natural `x`, `y` it is the carry of the last
  digits in base `p` (`carry_natCast_div`).
* **The carry series** (`carrySeries`): `Σ b_i κ(a_i u, a_i h)`, the defect of additivity of the
  series of fractional parts (`carrySeries_eq`).
* **The law of the carry** (`carrySeries_eq_of_strip`): if `−ζ G/s` is holomorphic on a strip
  about the line and bounded near it, the expansions of `G` on the two sides of the line have the
  same carries.
* **The carries determine the series** (`fractSeries_eq_of_carrySeries_eq`): two series of
  fractional parts with the same carries are equal; their difference is additive and `O(u^σ)`
  with `σ < 1`. So the law of the carry is the jump law, not a consequence of it.

Where the fractional part is additive there is no carry and the law is empty: this is the case of
a function field, whose zeta function has a Dirichlet polynomial as a constituent.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.ConstituentTheoryOfTheZeros

open GaloisForLFunctions.InfiniteRankPurityTheory

variable {ι : Type*} {κ : Type*}

/-! ### The carry -/

/-- The carry of two real numbers: `{x} + {y} − {x + y}`. -/
def carry (x y : ℝ) : ℝ := Int.fract x + Int.fract y - Int.fract (x + y)

theorem carry_eq_floor (x y : ℝ) : carry x y = ((⌊x + y⌋ - ⌊x⌋ - ⌊y⌋ : ℤ) : ℝ) := by
  unfold carry Int.fract
  push_cast
  ring

/-- The carry is `0` or `1`. -/
theorem carry_eq_zero_or_one (x y : ℝ) : carry x y = 0 ∨ carry x y = 1 := by
  have h1 := Int.le_floor_add x y
  have h2 := Int.le_floor_add_floor x y
  rw [carry_eq_floor]
  have h : ⌊x + y⌋ - ⌊x⌋ - ⌊y⌋ = 0 ∨ ⌊x + y⌋ - ⌊x⌋ - ⌊y⌋ = 1 := by omega
  rcases h with h | h
  · left
    rw [h, Int.cast_zero]
  · right
    rw [h, Int.cast_one]

theorem norm_carry_le (x y : ℝ) : ‖((carry x y : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs]
  rcases carry_eq_zero_or_one x y with h | h <;> rw [h] <;> simp

/-- **The carry is a cocycle.** -/
theorem carry_cocycle (x y z : ℝ) :
    carry x y + carry (x + y) z = carry y z + carry x (y + z) := by
  unfold carry
  rw [add_assoc x y z]
  ring

/-- **The carry of `x/p` and `y/p` is the carry of the last digits in base `p`.** -/
theorem carry_natCast_div {p : ℕ} (hp : 0 < p) (x y : ℕ) :
    carry ((x : ℝ) / p) ((y : ℝ) / p) = (((x % p + y % p) / p : ℕ) : ℝ) := by
  have hfloor : ∀ n : ℕ, ⌊(n : ℝ) / (p : ℝ)⌋ = ((n / p : ℕ) : ℤ) := fun n => by
    rw [Int.floor_div_natCast, Int.floor_natCast, Int.natCast_div]
  have hadd : (x : ℝ) / p + (y : ℝ) / p = ((x + y : ℕ) : ℝ) / p := by
    push_cast
    ring
  have hdiv : (x + y) / p = x / p + y / p + (x % p + y % p) / p := by
    rw [Nat.add_div hp]
    congr 1
    have hx := Nat.mod_lt x hp
    have hy := Nat.mod_lt y hp
    split_ifs with h
    · exact (Nat.div_eq_of_lt_le (by omega) (by omega)).symm
    · exact (Nat.div_eq_of_lt (by omega)).symm
  rw [carry_eq_floor, hadd, hfloor, hfloor, hfloor, hdiv]
  push_cast
  ring

/-! ### The carry series -/

/-- The carry series of an expansion: `Σ b_i κ(a_i u, a_i h)`. -/
def carrySeries (b : ι → ℂ) (a : ι → ℝ) (u h : ℝ) : ℂ :=
  ∑' i, b i * ((carry (a i * u) (a i * h) : ℝ) : ℂ)

/-- **The carry series is the defect of additivity of the series of fractional parts.** -/
theorem carrySeries_eq {b : ι → ℂ} {a : ι → ℝ} (ha : ∀ i, 0 < a i) {σ : ℝ} (h0 : 0 ≤ σ)
    (h1 : σ ≤ 1) (hsum : Summable fun i => ‖b i‖ * a i ^ σ) {u h : ℝ} (hu : 0 ≤ u)
    (hh : 0 ≤ h) :
    carrySeries b a u h = fractSeries b a u + fractSeries b a h - fractSeries b a (u + h) := by
  have s1 := summable_fractTerm ha h0 h1 hsum hu
  have s2 := summable_fractTerm ha h0 h1 hsum hh
  have s3 := summable_fractTerm ha h0 h1 hsum (add_nonneg hu hh)
  unfold carrySeries fractSeries
  rw [← s1.tsum_add s2, ← (s1.add s2).tsum_sub s3]
  refine tsum_congr fun i => ?_
  unfold carry fractC
  rw [mul_add (a i) u h]
  push_cast
  ring

/-- **The law of the carry.** Under the hypotheses of the jump law on a strip, the expansions on
the two sides of the line have the same carries: for all `u, h > 0`,
`Σ b_i κ(a_i u, a_i h) = Σ c_j κ(q_j u, q_j h)`. -/
theorem carrySeries_eq_of_strip [Countable ι] [Countable κ] {b : ι → ℂ} {a : ι → ℝ} {c : κ → ℂ}
    {q : κ → ℝ} (ha : ∀ i, 0 < a i) (hq : ∀ j, 0 < q j) {η : ℝ} (hη0 : 0 < η) (hη : η ≤ 1 / 2)
    (hR : ∀ σ : ℝ, 1 / 2 < σ → σ ≤ 1 / 2 + η → Summable fun i => ‖b i‖ * a i ^ σ)
    (hL : ∀ σ : ℝ, 1 / 2 - η ≤ σ → σ < 1 / 2 → Summable fun j => ‖c j‖ * q j ^ σ)
    {F : ℂ → ℂ} (hFd : DifferentiableOn ℂ F {s : ℂ | 1 / 2 - η < s.re ∧ s.re < 1 / 2 + η})
    {K : ℝ} (hFb : ∀ s : ℂ, 1 / 2 - η / 2 ≤ s.re → s.re ≤ 1 / 2 + η / 2 → ‖F s‖ ≤ K)
    (hFR : ∀ s : ℂ, 1 / 2 < s.re → s.re < 1 / 2 + η →
      F s = -(riemannZeta s / s) * ∑' i, b i * (a i : ℂ) ^ s)
    (hFL : ∀ s : ℂ, 1 / 2 - η < s.re → s.re < 1 / 2 →
      F s = -(riemannZeta s / s) * ∑' j, c j * (q j : ℂ) ^ s)
    {u h : ℝ} (hu : 0 < u) (hh : 0 < h) : carrySeries b a u h = carrySeries c q u h := by
  have heq : ∀ v : ℝ, 0 < v → fractSeries b a v = fractSeries c q v := fun v hv =>
    fractSeries_eq_of_strip ha hq hη0 hη hR hL hFd hFb hFR hFL hv
  rw [carrySeries_eq ha (by linarith) (by linarith) (hR (1 / 2 + η) (by linarith) le_rfl) hu.le
      hh.le,
    carrySeries_eq hq (by linarith) (by linarith) (hL (1 / 2 - η) le_rfl (by linarith)) hu.le
      hh.le, heq u hu, heq h hh, heq (u + h) (add_pos hu hh)]

/-! ### The carries determine the series -/

/-- A function on the positive reals that is additive and `O(u^σ₁ + u^σ₂)` with exponents below
one vanishes: `d(nu) = n d(u)` grows linearly in `n`, the bound like `n^σ`. -/
theorem eq_zero_of_additive_of_bound {d : ℝ → ℂ}
    (hadd : ∀ u h : ℝ, 0 < u → 0 < h → d (u + h) = d u + d h) {A B σ₁ σ₂ : ℝ} (hσ₁ : σ₁ < 1)
    (hσ₂ : σ₂ < 1) (hb : ∀ u : ℝ, 0 < u → ‖d u‖ ≤ A * u ^ σ₁ + B * u ^ σ₂) {u : ℝ} (hu : 0 < u) :
    d u = 0 := by
  have hmul : ∀ n : ℕ, d (((n : ℝ) + 1) * u) = ((n : ℂ) + 1) * d u := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have hpos : 0 < ((n : ℝ) + 1) * u := by positivity
      rw [show (((n + 1 : ℕ) : ℝ) + 1) * u = ((n : ℝ) + 1) * u + u by push_cast; ring,
        hadd _ _ hpos hu, ih]
      push_cast
      ring
  set σ : ℝ := max σ₁ σ₂ with hσdef
  have hσ : σ < 1 := max_lt hσ₁ hσ₂
  set C : ℝ := |A| * u ^ σ₁ + |B| * u ^ σ₂ with hC
  -- `(n + 1) ‖d u‖ ≤ C (n + 1)^σ`
  have hle : ∀ n : ℕ, ((n : ℝ) + 1) * ‖d u‖ ≤ C * ((n : ℝ) + 1) ^ σ := by
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [Nat.cast_nonneg (α := ℝ) n]
    have h := hb _ (show 0 < ((n : ℝ) + 1) * u by positivity)
    have hnorm : ‖((n : ℂ) + 1)‖ = (n : ℝ) + 1 := by
      rw [show ((n : ℂ) + 1) = (((n : ℝ) + 1 : ℝ) : ℂ) by push_cast; rfl, Complex.norm_real,
        Real.norm_of_nonneg hn.le]
    rw [hmul, norm_mul, hnorm, Real.mul_rpow hn.le hu.le, Real.mul_rpow hn.le hu.le] at h
    have e1 : A * (((n : ℝ) + 1) ^ σ₁ * u ^ σ₁) ≤ |A| * u ^ σ₁ * ((n : ℝ) + 1) ^ σ := by
      have h1 : ((n : ℝ) + 1) ^ σ₁ ≤ ((n : ℝ) + 1) ^ σ :=
        Real.rpow_le_rpow_of_exponent_le hn1 (le_max_left _ _)
      have h2 : A * (((n : ℝ) + 1) ^ σ₁ * u ^ σ₁) ≤ |A| * (((n : ℝ) + 1) ^ σ₁ * u ^ σ₁) :=
        mul_le_mul_of_nonneg_right (le_abs_self A)
          (mul_nonneg (Real.rpow_nonneg hn.le _) (Real.rpow_nonneg hu.le _))
      have h3 : |A| * (((n : ℝ) + 1) ^ σ₁ * u ^ σ₁) ≤ |A| * (((n : ℝ) + 1) ^ σ * u ^ σ₁) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hu.le _))
          (abs_nonneg A)
      linarith
    have e2 : B * (((n : ℝ) + 1) ^ σ₂ * u ^ σ₂) ≤ |B| * u ^ σ₂ * ((n : ℝ) + 1) ^ σ := by
      have h1 : ((n : ℝ) + 1) ^ σ₂ ≤ ((n : ℝ) + 1) ^ σ :=
        Real.rpow_le_rpow_of_exponent_le hn1 (le_max_right _ _)
      have h2 : B * (((n : ℝ) + 1) ^ σ₂ * u ^ σ₂) ≤ |B| * (((n : ℝ) + 1) ^ σ₂ * u ^ σ₂) :=
        mul_le_mul_of_nonneg_right (le_abs_self B)
          (mul_nonneg (Real.rpow_nonneg hn.le _) (Real.rpow_nonneg hu.le _))
      have h3 : |B| * (((n : ℝ) + 1) ^ σ₂ * u ^ σ₂) ≤ |B| * (((n : ℝ) + 1) ^ σ * u ^ σ₂) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right h1 (Real.rpow_nonneg hu.le _))
          (abs_nonneg B)
      linarith
    rw [hC, add_mul]
    linarith
  by_contra hne
  have hm : 0 < ‖d u‖ := norm_pos_iff.mpr hne
  -- `(n + 1)^{1 − σ}` exceeds `C/‖d u‖`
  obtain ⟨n, hn⟩ := (((tendsto_rpow_atTop (sub_pos.mpr hσ)).comp
    tendsto_natCast_atTop_atTop).eventually_gt_atTop (C / ‖d u‖)).exists
  have hn0 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hmono : (n : ℝ) ^ (1 - σ) ≤ ((n : ℝ) + 1) ^ (1 - σ) :=
    Real.rpow_le_rpow (Nat.cast_nonneg n) (by linarith) (by linarith)
  have hsplit : (n : ℝ) + 1 = ((n : ℝ) + 1) ^ σ * ((n : ℝ) + 1) ^ (1 - σ) := by
    rw [← Real.rpow_add hn0, add_sub_cancel, Real.rpow_one]
  have h := hle n
  rw [hsplit, mul_assoc, mul_comm C] at h
  have h' : ((n : ℝ) + 1) ^ (1 - σ) * ‖d u‖ ≤ C :=
    le_of_mul_le_mul_left h (Real.rpow_pos_of_pos hn0 _)
  have hn' : C / ‖d u‖ < ((n : ℝ) + 1) ^ (1 - σ) := lt_of_lt_of_le hn hmono
  rw [div_lt_iff₀ hm] at hn'
  linarith

/-- **The carries determine the series.** Two series of fractional parts, each `O(u^σ)` with an
exponent below one, that have the same carries are equal. -/
theorem fractSeries_eq_of_carrySeries_eq {b : ι → ℂ} {a : ι → ℝ} {c : κ → ℂ} {q : κ → ℝ}
    (ha : ∀ i, 0 < a i) (hq : ∀ j, 0 < q j) {σ₁ σ₂ : ℝ} (h₁ : 0 ≤ σ₁) (h₁' : σ₁ < 1)
    (h₂ : 0 ≤ σ₂) (h₂' : σ₂ < 1) (hb : Summable fun i => ‖b i‖ * a i ^ σ₁)
    (hc : Summable fun j => ‖c j‖ * q j ^ σ₂)
    (hcarry : ∀ u h : ℝ, 0 < u → 0 < h → carrySeries b a u h = carrySeries c q u h) {u : ℝ}
    (hu : 0 < u) : fractSeries b a u = fractSeries c q u := by
  have hd := eq_zero_of_additive_of_bound (d := fun v => fractSeries b a v - fractSeries c q v)
    (A := ∑' i, ‖b i‖ * a i ^ σ₁) (B := ∑' j, ‖c j‖ * q j ^ σ₂) (fun v h hv hh => ?_) h₁' h₂'
    (fun v hv => ?_) hu
  · exact sub_eq_zero.mp hd
  · have e3 := hcarry v h hv hh
    rw [carrySeries_eq ha h₁ h₁'.le hb hv.le hh.le, carrySeries_eq hq h₂ h₂'.le hc hv.le hh.le]
      at e3
    show fractSeries b a (v + h) - fractSeries c q (v + h) =
      fractSeries b a v - fractSeries c q v + (fractSeries b a h - fractSeries c q h)
    linear_combination (-1 : ℂ) * e3
  · exact (norm_sub_le _ _).trans (add_le_add (norm_fractSeries_le ha h₁ h₁'.le hb hv.le)
      (norm_fractSeries_le hq h₂ h₂'.le hc hv.le))

end GaloisForLFunctions.ConstituentTheoryOfTheZeros
