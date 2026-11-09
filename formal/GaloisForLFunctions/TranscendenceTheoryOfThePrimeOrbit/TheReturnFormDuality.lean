import GaloisForLFunctions.TailArithmeticOfThePrimeOrbit.TheCombOfAReturn

/-!
# The return–form duality

A height `t` is a `δ`-return of steps `ℓ` on `s` when every phase `tℓ_i/2π` lies within `δ` of `ℤ`.
Integer vectors `ν` give linear forms `Λ_ν = Σ ν_i ℓ_i` of height `|ν|₁`; for the primes,
`Λ_ν = log(a/b)` with `a, b` coprime and smooth.

* **Duality** (`dist01_linForm_le`). At a `δ`-return, `‖tΛ_ν/2π‖ ≤ |ν|₁ δ`. A form of height
  `h` therefore constrains `δ`-returns only while `hδ < ½`.
* **Windows** (`not_isDeltaReturn_of_window`). A nonzero form excludes `δ`-returns on the heights
  `2π|ν|₁δ < |t||Λ_ν| < 2π(1 − |ν|₁δ)`.
* **Depth at two steps** (`abs_round_mul_sub_round_mul_le`). A `δ`-return of `{i, j}` makes the binary
  form `n_i ℓ_j − n_j ℓ_i`, `n = round(tℓ/2π)`, at most `δ(|ℓ_i| + |ℓ_j|)`: its coefficients are
  `≍ t`, its value is `≍ δ`. This is where lower bounds for linear forms act.
* **Liouville at bounded height** (`inv_pow_le_abs_linForm_log`). For primes `≤ y` and `ν ≠ 0`,
  `|Λ_ν| ≥ y^{−|ν|₁}`.
* **The breadth cap** (`exists_matching_system_with_exact_return`). For `T ≥ 2πK y^K` the rounded
  system `ℓ'_p = 2π·round(T log p/2π)/T` agrees with `log p` on every form of height `≤ K` up to
  half its size, and returns exactly at `T`. So no statement about the forms of height `≤ K`
  excludes a return at such `T` (`no_bounded_height_certificate`): Diophantine information of
  bounded height reaches at most the Kronecker scale `y^{O(1/δ)}` at precision `δ`.
-/

open Real Finset

namespace GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit

noncomputable section

open PrimeTorusTheory (dist01)
open TailArithmeticOfThePrimeOrbit (dist01_add_le dist01_zero IsReturn)

variable {ι : Type*}

/-- `t` is a `δ`-return of the steps `ℓ` on `s`. -/
def IsDeltaReturn (s : Finset ι) (ℓ : ι → ℝ) (δ t : ℝ) : Prop :=
  ∀ i ∈ s, dist01 (t * ℓ i / (2 * π)) ≤ δ

/-- The linear form `Λ_ν = Σ_{i∈s} ν_i ℓ_i`. -/
def linForm (s : Finset ι) (ℓ : ι → ℝ) (ν : ι → ℤ) : ℝ := ∑ i ∈ s, (ν i : ℝ) * ℓ i

/-- The height `|ν|₁ = Σ_{i∈s} |ν_i|`. -/
def formHeight (s : Finset ι) (ν : ι → ℤ) : ℕ := ∑ i ∈ s, (ν i).natAbs

/-! ## Distance to the integers -/

theorem dist01_neg (x : ℝ) : dist01 (-x) = dist01 x := by
  apply le_antisymm
  · calc dist01 (-x) ≤ |-x - ((-round x : ℤ) : ℝ)| := round_le _ _
      _ = dist01 x := by unfold dist01; push_cast; rw [← abs_neg]; ring_nf
  · calc dist01 x ≤ |x - ((-round (-x) : ℤ) : ℝ)| := round_le _ _
      _ = dist01 (-x) := by unfold dist01; push_cast; rw [← abs_neg]; ring_nf

theorem dist01_intCast_mul_le (n : ℤ) (x : ℝ) : dist01 (n * x) ≤ |(n : ℝ)| * dist01 x := by
  calc dist01 (n * x) ≤ |(n : ℝ) * x - ((n * round x : ℤ) : ℝ)| := round_le _ _
    _ = |(n : ℝ)| * dist01 x := by unfold dist01; push_cast; rw [← abs_mul]; ring_nf

theorem dist01_sum_le (s : Finset ι) (x : ι → ℝ) : dist01 (∑ i ∈ s, x i) ≤ ∑ i ∈ s, dist01 (x i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dist01_zero]
  | insert a s ha ih =>
    rw [sum_insert ha, sum_insert ha]
    exact (dist01_add_le _ _).trans (by linarith)

/-- Points of `(h, 1 − h)` are farther than `h` from `ℤ`. -/
theorem lt_dist01_of_mem_Ioo {h x : ℝ} (h1 : h < x) (h2 : x < 1 - h) : h < dist01 x := by
  rcases lt_or_ge h 0 with h0 | h0
  · exact h0.trans_le (PrimeTorusTheory.dist01_nonneg x)
  unfold dist01
  rcases le_or_gt (round x) 0 with hn | hn
  · have : (round x : ℝ) ≤ 0 := by exact_mod_cast hn
    rw [abs_of_pos (by linarith)]; linarith
  · have : (1 : ℝ) ≤ round x := by exact_mod_cast hn
    rw [abs_of_neg (by linarith)]; linarith

/-! ## Returns and forms -/

/-- **Duality.** At a `δ`-return every form of height `h` has phase within `hδ` of `ℤ`. -/
theorem dist01_linForm_le {s : Finset ι} {ℓ : ι → ℝ} {δ t : ℝ} (hret : IsDeltaReturn s ℓ δ t)
    (ν : ι → ℤ) : dist01 (t * linForm s ℓ ν / (2 * π)) ≤ formHeight s ν * δ := by
  have e : t * linForm s ℓ ν / (2 * π) = ∑ i ∈ s, (ν i : ℝ) * (t * ℓ i / (2 * π)) := by
    unfold linForm; rw [mul_sum, sum_div]; refine sum_congr rfl fun i _ => by ring
  rw [e]
  refine (dist01_sum_le _ _).trans ?_
  unfold formHeight
  push_cast
  rw [sum_mul]
  refine sum_le_sum fun i hi => (dist01_intCast_mul_le _ _).trans ?_
  rw [Nat.cast_natAbs, Int.cast_abs]
  exact mul_le_mul_of_nonneg_left (hret i hi) (abs_nonneg _)

/-- **Windows.** A nonzero form of height `h` excludes `δ`-returns at the heights
`2πhδ < |t||Λ_ν| < 2π(1 − hδ)`. -/
theorem not_isDeltaReturn_of_window {s : Finset ι} {ℓ : ι → ℝ} {δ t : ℝ} (ν : ι → ℤ)
    (h1 : 2 * π * (formHeight s ν * δ) < |t| * |linForm s ℓ ν|)
    (h2 : |t| * |linForm s ℓ ν| < 2 * π * (1 - formHeight s ν * δ)) :
    ¬ IsDeltaReturn s ℓ δ t := by
  intro hret
  have hd := dist01_linForm_le hret ν
  set x := t * linForm s ℓ ν / (2 * π)
  have hx : |x| = |t| * |linForm s ℓ ν| / (2 * π) := by
    simp only [x, abs_div, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]
  have hpi : (0 : ℝ) < 2 * π := by positivity
  have hlt : formHeight s ν * δ < dist01 |x| := by
    refine lt_dist01_of_mem_Ioo ?_ ?_ <;> rw [hx]
    · rw [lt_div_iff₀ hpi]; linarith
    · rw [div_lt_iff₀ hpi]; linarith
  have habs : dist01 |x| = dist01 x := by
    rcases abs_choice x with h | h <;> rw [h]; exact dist01_neg x
  linarith

/-- **Depth at two steps.** A `δ`-return of `i, j` makes the binary form with coefficients
`n = round(tℓ/2π)` of size at most `δ(|ℓ_i| + |ℓ_j|)`. -/
theorem abs_round_mul_sub_round_mul_le {s : Finset ι} {ℓ : ι → ℝ} {δ t : ℝ}
    (hret : IsDeltaReturn s ℓ δ t) {i j : ι} (hi : i ∈ s) (hj : j ∈ s) :
    |(round (t * ℓ i / (2 * π)) : ℝ) * ℓ j - (round (t * ℓ j / (2 * π)) : ℝ) * ℓ i| ≤
      δ * (|ℓ i| + |ℓ j|) := by
  set x := t * ℓ i / (2 * π)
  set y := t * ℓ j / (2 * π)
  have hx : |x - round x| ≤ δ := hret i hi
  have hy : |y - round y| ≤ δ := hret j hj
  have e : (round x : ℝ) * ℓ j - (round y : ℝ) * ℓ i =
      (y - round y) * ℓ i - (x - round x) * ℓ j := by
    have : x * ℓ j = y * ℓ i := by simp only [x, y]; ring
    linarith
  rw [e]
  calc |(y - round y) * ℓ i - (x - round x) * ℓ j|
      ≤ |y - round y| * |ℓ i| + |x - round x| * |ℓ j| := by
        rw [← abs_mul, ← abs_mul]; exact abs_sub _ _
    _ ≤ δ * |ℓ i| + δ * |ℓ j| := by gcongr
    _ = δ * (|ℓ i| + |ℓ j|) := by ring

/-! ## Liouville at bounded height -/

/-- The product `Π_{p∈s} p^{e_p}` has exponent `e_p` at every prime `p ∈ s`. -/
theorem factorization_prod_pow {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) (e : ℕ → ℕ) {p : ℕ}
    (hp : p ∈ s) : (∏ q ∈ s, q ^ e q).factorization p = e p := by
  rw [Nat.factorization_prod fun q hq => pow_ne_zero _ (hs q hq).ne_zero,
    Finsupp.finsetSum_apply, sum_eq_single p]
  · rw [(hs p hp).factorization_pow, Finsupp.single_eq_same]
  · intro q hq hqp
    rw [(hs q hq).factorization_pow, Finsupp.single_eq_of_ne (Ne.symm hqp)]
  · intro h; exact absurd hp h

/-- `|log a − log b| ≥ 1/max(a, b)` for distinct positive integers. -/
theorem inv_max_le_abs_log_sub_log {a b : ℕ} (ha : 0 < a) (hb : 0 < b) (hab : a ≠ b) :
    ((max a b : ℕ) : ℝ)⁻¹ ≤ |Real.log a - Real.log b| := by
  wlog hlt : b < a generalizing a b
  · have h := this hb ha hab.symm (lt_of_le_of_ne (not_lt.mp hlt) hab)
    rwa [max_comm, abs_sub_comm]
  have ha' : (0 : ℝ) < a := by exact_mod_cast ha
  have hb' : (0 : ℝ) < b := by exact_mod_cast hb
  have hba : (b : ℝ) + 1 ≤ a := by exact_mod_cast hlt
  rw [max_eq_left hlt.le, ← Real.log_div ha'.ne' hb'.ne']
  have hq : 1 < (a : ℝ) / b := by rw [one_lt_div hb']; linarith
  rw [abs_of_pos (Real.log_pos hq)]
  have := Real.one_sub_inv_le_log_of_pos (div_pos ha' hb')
  rw [inv_div] at this
  have hfrac : (a : ℝ)⁻¹ ≤ 1 - b / a := by
    rw [one_sub_div ha'.ne', inv_eq_one_div]; gcongr; linarith
  linarith

/-- **Liouville at bounded height.** For primes `≤ y` and `ν ≠ 0` on `s`,
`|Σ ν_p log p| ≥ y^{−|ν|₁}`. -/
theorem inv_pow_le_abs_linForm_log {y : ℕ} {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime ∧ p ≤ y)
    {ν : ℕ → ℤ} (hν : ∃ p ∈ s, ν p ≠ 0) :
    ((y : ℝ) ^ formHeight s ν)⁻¹ ≤ |linForm s (fun p => Real.log p) ν| := by
  have hprime : ∀ p ∈ s, p.Prime := fun p hp => (hs p hp).1
  set a := ∏ p ∈ s, p ^ (ν p).toNat
  set b := ∏ p ∈ s, p ^ (-ν p).toNat
  have ha : 0 < a := prod_pos fun p hp => pow_pos (hprime p hp).pos _
  have hb : 0 < b := prod_pos fun p hp => pow_pos (hprime p hp).pos _
  have hform : linForm s (fun p => Real.log p) ν = Real.log a - Real.log b := by
    unfold linForm
    simp only [a, b, Nat.cast_prod, Nat.cast_pow]
    rw [Real.log_prod (fun p hp => pow_ne_zero _ (by exact_mod_cast (hprime p hp).ne_zero)),
      Real.log_prod (fun p hp => pow_ne_zero _ (by exact_mod_cast (hprime p hp).ne_zero)),
      ← sum_sub_distrib]
    refine sum_congr rfl fun p _ => ?_
    rw [Real.log_pow, Real.log_pow, ← sub_mul]
    congr 1
    have h := Int.toNat_sub_toNat_neg (ν p)
    exact_mod_cast h.symm
  have hab : a ≠ b := by
    obtain ⟨p, hp, hνp⟩ := hν
    intro h
    have h1 := factorization_prod_pow hprime (fun q => (ν q).toNat) hp
    have h2 := factorization_prod_pow hprime (fun q => (-ν q).toNat) hp
    change a.factorization p = _ at h1
    change b.factorization p = _ at h2
    rw [h] at h1
    have : (ν p).toNat = (-ν p).toNat := h1.symm.trans h2
    omega
  have hmax : ((max a b : ℕ) : ℝ) ≤ (y : ℝ) ^ formHeight s ν := by
    have hmab : max a b ≤ a * b := by
      rcases le_total a b with h | h
      · rw [max_eq_right h]; exact Nat.le_mul_of_pos_left _ ha
      · rw [max_eq_left h]; exact Nat.le_mul_of_pos_right _ hb
    have hprod : a * b = ∏ p ∈ s, p ^ (ν p).natAbs := by
      simp only [a, b, ← prod_mul_distrib, ← pow_add]
      refine prod_congr rfl fun p _ => ?_
      congr 1; omega
    have hle : ∏ p ∈ s, p ^ (ν p).natAbs ≤ y ^ formHeight s ν := by
      unfold formHeight
      rw [← prod_pow_eq_pow_sum]
      exact prod_le_prod' fun p hp => Nat.pow_le_pow_left (hs p hp).2 _
    exact_mod_cast (hmab.trans (hprod ▸ hle))
  have hpos : (0 : ℝ) < ((max a b : ℕ) : ℝ) := by exact_mod_cast lt_max_of_lt_left ha
  rw [hform]
  exact (inv_anti₀ hpos hmax).trans (inv_max_le_abs_log_sub_log ha hb hab)

/-! ## The rounded system and the breadth cap -/

/-- The rounded system at time `T`: each step moved to the nearest point of `(2π/T)ℤ`. -/
def roundedStep (T : ℝ) (ℓ : ι → ℝ) (i : ι) : ℝ := 2 * π * round (T * ℓ i / (2 * π)) / T

theorem phase_roundedStep {T : ℝ} (hT : 0 < T) (ℓ : ι → ℝ) (i : ι) :
    T * roundedStep T ℓ i / (2 * π) = round (T * ℓ i / (2 * π)) := by
  unfold roundedStep; field_simp

/-- The rounded system returns exactly at `T`, in both normalizations. -/
theorem isDeltaReturn_roundedStep {T : ℝ} (hT : 0 < T) (s : Finset ι) (ℓ : ι → ℝ) :
    IsDeltaReturn s (roundedStep T ℓ) 0 T ∧ IsReturn s (roundedStep T ℓ) 0 T := by
  refine ⟨fun i _ => ?_, fun i _ => ?_⟩
  · rw [phase_roundedStep hT]; simp [dist01]
  · have e : T * roundedStep T ℓ i = (round (T * ℓ i / (2 * π)) : ℝ) * (2 * π) := by
      have := phase_roundedStep hT ℓ i; field_simp at this ⊢; linarith
    rw [e, Real.cos_int_mul_two_pi]; simp

theorem abs_roundedStep_sub_le {T : ℝ} (hT : 0 < T) (ℓ : ι → ℝ) (i : ι) :
    |roundedStep T ℓ i - ℓ i| ≤ π / T := by
  have e : roundedStep T ℓ i - ℓ i = (2 * π / T) * (round (T * ℓ i / (2 * π)) - T * ℓ i / (2 * π)) := by
    unfold roundedStep; field_simp
  rw [e, abs_mul, abs_of_pos (by positivity : 0 < 2 * π / T), abs_sub_comm]
  calc 2 * π / T * |T * ℓ i / (2 * π) - round (T * ℓ i / (2 * π))| ≤ 2 * π / T * (1 / 2) :=
        mul_le_mul_of_nonneg_left (abs_sub_round _) (by positivity)
    _ = π / T := by ring

theorem abs_linForm_roundedStep_sub_le {T : ℝ} (hT : 0 < T) (s : Finset ι) (ℓ : ι → ℝ)
    (ν : ι → ℤ) : |linForm s (roundedStep T ℓ) ν - linForm s ℓ ν| ≤ formHeight s ν * (π / T) := by
  unfold linForm formHeight
  rw [← sum_sub_distrib]
  push_cast
  rw [sum_mul]
  refine (abs_sum_le_sum_abs _ _).trans (sum_le_sum fun i _ => ?_)
  rw [← mul_sub, abs_mul, Nat.cast_natAbs, Int.cast_abs]
  exact mul_le_mul_of_nonneg_left (abs_roundedStep_sub_le hT ℓ i) (abs_nonneg _)

/-- `ℓ'` agrees with `ℓ` on every nonzero form of height `≤ K`, up to half its size. -/
def MatchesToHeight (s : Finset ι) (K : ℕ) (ℓ ℓ' : ι → ℝ) : Prop :=
  ∀ ν : ι → ℤ, 0 < formHeight s ν → formHeight s ν ≤ K →
    |linForm s ℓ' ν - linForm s ℓ ν| ≤ |linForm s ℓ ν| / 2

/-- **The breadth cap.** For primes `≤ y` and `T ≥ 2πK y^K`, the rounded system matches `log p` on
every form of height `≤ K` and returns exactly at `T`. -/
theorem exists_matching_system_with_exact_return {y : ℕ} {s : Finset ℕ}
    (hs : ∀ p ∈ s, p.Prime ∧ p ≤ y) (K : ℕ) {T : ℝ} (hT0 : 0 < T)
    (hT : 2 * π * K * (y : ℝ) ^ K ≤ T) :
    MatchesToHeight s K (fun p => Real.log p) (roundedStep T fun p => Real.log p) ∧
      IsDeltaReturn s (roundedStep T fun p => Real.log p) 0 T ∧
      IsReturn s (roundedStep T fun p => Real.log p) 0 T := by
  refine ⟨fun ν hν hK => ?_, isDeltaReturn_roundedStep hT0 s _⟩
  have hex : ∃ p ∈ s, ν p ≠ 0 := by
    by_contra h
    push Not at h
    have : formHeight s ν = 0 := sum_eq_zero fun p hp => by rw [h p hp]; rfl
    omega
  have hlio := inv_pow_le_abs_linForm_log hs hex
  obtain ⟨p, hp, -⟩ := hex
  have hy1 : (1 : ℝ) ≤ y := by exact_mod_cast (hs p hp).1.one_lt.le.trans (hs p hp).2
  have hK1 : (1 : ℝ) ≤ K := by exact_mod_cast (show 1 ≤ K by omega)
  have hyK : (y : ℝ) ^ formHeight s ν ≤ (y : ℝ) ^ K := pow_le_pow_right₀ hy1 hK
  have hyK0 : (0 : ℝ) < (y : ℝ) ^ formHeight s ν := by positivity
  have hstep : (formHeight s ν : ℝ) * (π / T) ≤ ((y : ℝ) ^ formHeight s ν)⁻¹ / 2 := by
    have hH : (formHeight s ν : ℝ) ≤ K := by exact_mod_cast hK
    have hyK1 : (0 : ℝ) < (y : ℝ) ^ K := by positivity
    have h1 : (formHeight s ν : ℝ) * (π / T) ≤ K * (π / T) := by gcongr
    have h2 : (K : ℝ) * (π / T) ≤ ((y : ℝ) ^ K)⁻¹ / 2 := by
      rw [mul_div_assoc', div_le_iff₀ hT0, inv_eq_one_div, div_div, div_mul_eq_mul_div,
        le_div_iff₀ (by positivity)]
      nlinarith
    have h3 : ((y : ℝ) ^ K)⁻¹ ≤ ((y : ℝ) ^ formHeight s ν)⁻¹ := inv_anti₀ hyK0 hyK
    linarith
  calc |linForm s (roundedStep T fun p => Real.log p) ν - linForm s (fun p => Real.log p) ν|
      ≤ formHeight s ν * (π / T) := abs_linForm_roundedStep_sub_le hT0 s _ ν
    _ ≤ ((y : ℝ) ^ formHeight s ν)⁻¹ / 2 := hstep
    _ ≤ |linForm s (fun p => Real.log p) ν| / 2 := by gcongr

/-- **No certificate of bounded height.** A property of step systems that is insensitive to
changes of the forms of height `≤ K` by up to half their size cannot exclude a return of the primes
`≤ y` at any `T ≥ 2πK y^K`. -/
theorem no_bounded_height_certificate {y : ℕ} {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime ∧ p ≤ y)
    (K : ℕ) {T : ℝ} (hT0 : 0 < T) (hT : 2 * π * K * (y : ℝ) ^ K ≤ T)
    (Φ : (ℕ → ℝ) → Prop) (hΦ : ∀ ℓ', MatchesToHeight s K (fun p => Real.log p) ℓ' → Φ ℓ') :
    ¬ ∀ ℓ', Φ ℓ' → ¬ IsDeltaReturn s ℓ' 0 T := fun h =>
  let hcap := exists_matching_system_with_exact_return hs K hT0 hT
  h _ (hΦ _ hcap.1) hcap.2.1

end

end GaloisForLFunctions.TranscendenceTheoryOfThePrimeOrbit
