import Mathlib

open Complex Finset

namespace RHTower

noncomputable section

/-- The `p` multiples of `p` inside `ZMod (p ^ 2)`. -/
def primeSquareMultiples (p : ℕ) : Finset (ZMod (p ^ 2)) :=
  (Finset.range p).image (fun j => ((p * j : ℕ) : ZMod (p ^ 2)))

theorem mul_lt_prime_sq {p j : ℕ} (hp : 1 < p) (hj : j < p) : p * j < p ^ 2 := by
  have h : p ^ 2 = p * p := by ring
  rw [h]
  exact Nat.mul_lt_mul_of_le_of_lt (le_refl p) hj (by omega)

theorem val_natCast_of_lt' {p : ℕ} [NeZero p] {m : ℕ} (hm : m < p ^ 2) :
    ((m : ZMod (p ^ 2))).val = m := ZMod.val_natCast_of_lt hm

theorem mem_primeSquareMultiples_iff {p : ℕ} [NeZero p] (hp : 1 < p) (x : ZMod (p ^ 2)) :
    x ∈ primeSquareMultiples p ↔ (p : ℕ) ∣ x.val := by
  constructor
  · rintro hx
    rw [primeSquareMultiples, Finset.mem_image] at hx
    obtain ⟨j, hj, rfl⟩ := hx
    have hjp : j < p := Finset.mem_range.mp hj
    have hlt : p * j < p ^ 2 := mul_lt_prime_sq hp hjp
    rw [val_natCast_of_lt' hlt]
    exact ⟨j, rfl⟩
  · rintro ⟨j, hj⟩
    have hxlt : x.val < p ^ 2 := ZMod.val_lt x
    have hjp : j < p := by
      by_contra hcon
      have : p * p ≤ p * j := Nat.mul_le_mul_left p (by omega)
      have : p ^ 2 ≤ x.val := by
        rw [hj]
        calc p ^ 2 = p * p := by ring
          _ ≤ p * j := this
      omega
    rw [primeSquareMultiples, Finset.mem_image]
    refine ⟨j, Finset.mem_range.mpr hjp, ?_⟩
    rw [← hj, ZMod.natCast_val, ZMod.cast_id]

theorem card_primeSquareMultiples {p : ℕ} [NeZero p] (hp : 1 < p) :
    (primeSquareMultiples p).card = p := by
  rw [primeSquareMultiples, Finset.card_image_of_injOn, Finset.card_range]
  intro i hi j hj hij
  have hip : i < p := Finset.mem_range.mp hi
  have hjp : j < p := Finset.mem_range.mp hj
  have hilt : p * i < p ^ 2 := mul_lt_prime_sq hp hip
  have hjlt : p * j < p ^ 2 := mul_lt_prime_sq hp hjp
  have := congrArg ZMod.val hij
  rw [val_natCast_of_lt' hilt, val_natCast_of_lt' hjlt] at this
  exact Nat.eq_of_mul_eq_mul_left (by omega) this

/-- **The subgroup character sum.**  The additive character sums to `p` over the multiples of `p`
when the frequency is itself a multiple of `p`, and to zero otherwise. -/
theorem sum_stdAddChar_primeSquareMultiples {p : ℕ} [NeZero p] (hp : 1 < p) (k : ZMod (p ^ 2)) :
    ∑ x ∈ primeSquareMultiples p, ZMod.stdAddChar (k * x)
      = if (p : ZMod (p ^ 2)) * k = 0 then (p : ℂ) else 0 := by
  have hinj : Set.InjOn (fun j : ℕ => ((p * j : ℕ) : ZMod (p ^ 2))) (Finset.range p) := by
    intro i hi j hj hij
    have hip : i < p := Finset.mem_range.mp hi
    have hjp : j < p := Finset.mem_range.mp hj
    have hilt : p * i < p ^ 2 := mul_lt_prime_sq hp hip
    have hjlt : p * j < p ^ 2 := mul_lt_prime_sq hp hjp
    have := congrArg ZMod.val hij
    rw [val_natCast_of_lt' hilt, val_natCast_of_lt' hjlt] at this
    exact Nat.eq_of_mul_eq_mul_left (by omega) this
  rw [primeSquareMultiples, Finset.sum_image hinj]
  have hterm : ∀ j ∈ Finset.range p,
      ZMod.stdAddChar (k * ((p * j : ℕ) : ZMod (p ^ 2)))
        = (ZMod.stdAddChar ((p : ZMod (p ^ 2)) * k)) ^ j := by
    intro j _
    have hcast : (k : ZMod (p ^ 2)) * ((p * j : ℕ) : ZMod (p ^ 2))
        = j • ((p : ZMod (p ^ 2)) * k) := by
      push_cast
      rw [nsmul_eq_mul]
      ring
    rw [hcast, AddChar.map_nsmul_eq_pow]
  rw [Finset.sum_congr rfl hterm]
  set ζ : ℂ := ZMod.stdAddChar ((p : ZMod (p ^ 2)) * k) with hζ
  by_cases hk : (p : ZMod (p ^ 2)) * k = 0
  · rw [if_pos hk]
    have hζ1 : ζ = 1 := by rw [hζ, hk, AddChar.map_zero_eq_one]
    rw [hζ1]
    simp
  · rw [if_neg hk]
    have hζne : ζ ≠ 1 := by
      rw [hζ]
      intro hcon
      apply hk
      have := ZMod.injective_stdAddChar (N := p ^ 2)
      have h1 : ZMod.stdAddChar ((p : ZMod (p ^ 2)) * k) = ZMod.stdAddChar (0 : ZMod (p ^ 2)) := by
        rw [hcon, AddChar.map_zero_eq_one]
      exact this h1
    have hpow : ζ ^ p = 1 := by
      rw [hζ, ← AddChar.map_nsmul_eq_pow]
      have hzero : (p : ℕ) • ((p : ZMod (p ^ 2)) * k) = 0 := by
        rw [nsmul_eq_mul]
        have : ((p : ℕ) : ZMod (p ^ 2)) * ((p : ZMod (p ^ 2)) * k)
            = ((p ^ 2 : ℕ) : ZMod (p ^ 2)) * k := by
          push_cast
          ring
        rw [this, ZMod.natCast_self, zero_mul]
      rw [hzero, AddChar.map_zero_eq_one]
    have hgeom := geom_sum_eq hζne p
    rw [hgeom, hpow]
    simp

open scoped ZMod in
/-! ### Fourier transforms of the valuation strata -/

/-- Indicator of the multiples of `p` in `ZMod (p ^ 2)`. -/
def multipleIndicator (p : ℕ) [NeZero p] : ZMod (p ^ 2) → ℂ :=
  fun x => if (p : ℕ) ∣ x.val then 1 else 0

/-- Indicator of the unit residues in `ZMod (p ^ 2)`. -/
def unitIndicator (p : ℕ) [NeZero p] : ZMod (p ^ 2) → ℂ :=
  fun x => if (p : ℕ) ∣ x.val then 0 else 1

/-- The delta function at the origin of `ZMod (p ^ 2)`. -/
def deltaZero (p : ℕ) [NeZero p] : ZMod (p ^ 2) → ℂ :=
  fun x => if x = 0 then 1 else 0

theorem unitIndicator_add_multipleIndicator (p : ℕ) [NeZero p] (x : ZMod (p ^ 2)) :
    unitIndicator p x + multipleIndicator p x = 1 := by
  rw [unitIndicator, multipleIndicator]
  by_cases h : (p : ℕ) ∣ x.val <;> simp [h]

theorem sum_multipleIndicator {p : ℕ} [NeZero p] (hp : 1 < p) :
    ∑ x : ZMod (p ^ 2), multipleIndicator p x = (p : ℂ) := by
  classical
  have hfilter : ∀ x : ZMod (p ^ 2), multipleIndicator p x
      = if x ∈ primeSquareMultiples p then 1 else 0 := by
    intro x
    rw [multipleIndicator]
    by_cases h : (p : ℕ) ∣ x.val
    · rw [if_pos h, if_pos ((mem_primeSquareMultiples_iff hp x).mpr h)]
    · rw [if_neg h, if_neg (fun hcon => h ((mem_primeSquareMultiples_iff hp x).mp hcon))]
  simp only [hfilter]
  rw [Finset.sum_ite_mem, Finset.univ_inter, Finset.sum_const, card_primeSquareMultiples hp,
    nsmul_eq_mul, mul_one]

theorem sum_deltaZero (p : ℕ) [NeZero p] :
    ∑ x : ZMod (p ^ 2), deltaZero p x = 1 := by
  classical
  simp [deltaZero]

theorem sum_multipleIndicator_mul_deltaZero (p : ℕ) [NeZero p] (x : ZMod (p ^ 2)) :
    multipleIndicator p x * deltaZero p x = deltaZero p x := by
  rw [deltaZero, multipleIndicator]
  by_cases hx : x = 0
  · subst hx
    simp
  · simp [hx]

theorem multipleIndicator_sq (p : ℕ) [NeZero p] (x : ZMod (p ^ 2)) :
    multipleIndicator p x * multipleIndicator p x = multipleIndicator p x := by
  rw [multipleIndicator]
  by_cases h : (p : ℕ) ∣ x.val <;> simp [h]

theorem deltaZero_sq (p : ℕ) [NeZero p] (x : ZMod (p ^ 2)) :
    deltaZero p x * deltaZero p x = deltaZero p x := by
  rw [deltaZero]
  by_cases h : x = 0 <;> simp [h]

/-- **Fourier transform of the subgroup indicator.** -/
theorem dft_multipleIndicator {p : ℕ} [NeZero p] (hp : 1 < p) (k : ZMod (p ^ 2)) :
    ZMod.dft (multipleIndicator p) k
      = if (p : ZMod (p ^ 2)) * k = 0 then (p : ℂ) else 0 := by
  classical
  rw [ZMod.dft_apply]
  have hterm : ∀ x : ZMod (p ^ 2),
      ZMod.stdAddChar (-(x * k)) • multipleIndicator p x
        = if x ∈ primeSquareMultiples p then ZMod.stdAddChar ((-k) * x) else 0 := by
    intro x
    rw [multipleIndicator]
    by_cases h : (p : ℕ) ∣ x.val
    · rw [if_pos h, if_pos ((mem_primeSquareMultiples_iff hp x).mpr h)]
      rw [smul_eq_mul, mul_one]
      congr 1
      ring
    · rw [if_neg h, if_neg (fun hcon => h ((mem_primeSquareMultiples_iff hp x).mp hcon))]
      simp
  simp only [hterm]
  rw [Finset.sum_ite_mem, Finset.univ_inter, sum_stdAddChar_primeSquareMultiples hp (-k)]
  by_cases hk : (p : ZMod (p ^ 2)) * k = 0
  · rw [if_pos hk, if_pos (by rw [mul_neg, hk, neg_zero])]
  · rw [if_neg hk, if_neg (by
      intro hcon
      apply hk
      have : (p : ZMod (p ^ 2)) * k = -((p : ZMod (p ^ 2)) * -k) := by ring
      rw [this, hcon, neg_zero])]

/-- **Fourier transform of the delta function.** -/
theorem dft_deltaZero (p : ℕ) [NeZero p] (k : ZMod (p ^ 2)) :
    ZMod.dft (deltaZero p) k = 1 := by
  classical
  rw [ZMod.dft_apply]
  have hterm : ∀ x : ZMod (p ^ 2),
      ZMod.stdAddChar (-(x * k)) • deltaZero p x
        = if x = 0 then (1 : ℂ) else 0 := by
    intro x
    rw [deltaZero]
    by_cases hx : x = 0
    · subst hx
      simp
    · simp [hx]
  simp only [hterm]
  simp

/-- **Fourier transform of the constant one.** -/
theorem dft_one (p : ℕ) [NeZero p] (k : ZMod (p ^ 2)) :
    ZMod.dft (fun _ : ZMod (p ^ 2) => (1 : ℂ)) k
      = if k = 0 then ((p : ℂ) ^ 2) else 0 := by
  classical
  rw [ZMod.dft_apply]
  by_cases hk : k = 0
  · subst hk
    simp [ZMod.card]
  · have hchar : (ZMod.stdAddChar (N := p ^ 2)).mulShift (-k) ≠ 1 :=
      ZMod.isPrimitive_stdAddChar (p ^ 2) (neg_ne_zero.mpr hk)
    have hsum := AddChar.sum_eq_zero_of_ne_one hchar
    rw [if_neg hk]
    calc ∑ x : ZMod (p ^ 2), ZMod.stdAddChar (-(x * k)) • (1 : ℂ)
        = ∑ x : ZMod (p ^ 2), (ZMod.stdAddChar (N := p ^ 2)).mulShift (-k) x := by
          refine Finset.sum_congr rfl fun x _ => ?_
          rw [AddChar.mulShift_apply, smul_eq_mul, mul_one]
          congr 1
          ring
      _ = 0 := hsum

/-- **Fourier transform of the unit-residue indicator.** -/
theorem dft_unitIndicator {p : ℕ} [NeZero p] (hp : 1 < p) (k : ZMod (p ^ 2)) :
    ZMod.dft (unitIndicator p) k
      = (if k = 0 then ((p : ℂ) ^ 2) else 0) - (if (p : ZMod (p ^ 2)) * k = 0 then (p : ℂ) else 0) := by
  have hfun : unitIndicator p = (fun _ : ZMod (p ^ 2) => (1 : ℂ)) - multipleIndicator p := by
    funext x
    have := unitIndicator_add_multipleIndicator p x
    simp only [Pi.sub_apply]
    linear_combination this
  rw [hfun, map_sub, Pi.sub_apply, dft_one, dft_multipleIndicator hp]

/-! ### The orthonormal valuation strata and the Fourier compression -/

/-- The unitary additive Fourier transform on `ZMod (p ^ 2)`. -/
def primeSquareFourier (p : ℕ) [NeZero p] (f : ZMod (p ^ 2) → ℂ) : ZMod (p ^ 2) → ℂ :=
  fun k => (p : ℂ)⁻¹ * ZMod.dft f k

/-- The counting inner product on `ZMod (p ^ 2)`. -/
def countInner (p : ℕ) [NeZero p] (f g : ZMod (p ^ 2) → ℂ) : ℂ :=
  ∑ x : ZMod (p ^ 2), (starRingEnd ℂ) (f x) * g x

/-- The valuation-one stratum vector, before normalization. -/
def valOneVec (p : ℕ) [NeZero p] : ZMod (p ^ 2) → ℂ :=
  fun x => multipleIndicator p x - deltaZero p x

theorem sum_unitIndicator {p : ℕ} [NeZero p] (hp : 1 < p) :
    ∑ x : ZMod (p ^ 2), unitIndicator p x = (p : ℂ) ^ 2 - (p : ℂ) := by
  have htotal : ∑ x : ZMod (p ^ 2), (unitIndicator p x + multipleIndicator p x)
      = ((p : ℂ) ^ 2) := by
    have hone : ∀ x : ZMod (p ^ 2), unitIndicator p x + multipleIndicator p x = 1 :=
      unitIndicator_add_multipleIndicator p
    simp only [hone]
    rw [Finset.sum_const, Finset.card_univ, ZMod.card]
    ring_nf
  rw [Finset.sum_add_distrib, sum_multipleIndicator hp] at htotal
  linear_combination htotal

theorem unitIndicator_zero (p : ℕ) [NeZero p] : unitIndicator p 0 = 0 := by
  rw [unitIndicator, if_pos]
  simp

theorem multipleIndicator_zero (p : ℕ) [NeZero p] : multipleIndicator p 0 = 1 := by
  rw [multipleIndicator, if_pos]
  simp

theorem unitIndicator_mul_multipleIndicator (p : ℕ) [NeZero p] (x : ZMod (p ^ 2)) :
    unitIndicator p x * multipleIndicator p x = 0 := by
  rw [unitIndicator, multipleIndicator]
  by_cases h : (p : ℕ) ∣ x.val <;> simp [h]

theorem unitIndicator_mul_deltaZero (p : ℕ) [NeZero p] (x : ZMod (p ^ 2)) :
    unitIndicator p x * deltaZero p x = 0 := by
  rw [deltaZero]
  by_cases hx : x = 0
  · subst hx
    simp [unitIndicator_zero]
  · simp [hx]

theorem sum_valOneVec {p : ℕ} [NeZero p] (hp : 1 < p) :
    ∑ x : ZMod (p ^ 2), valOneVec p x = (p : ℂ) - 1 := by
  simp only [valOneVec]
  rw [Finset.sum_sub_distrib, sum_multipleIndicator hp, sum_deltaZero]

theorem sum_valOneVec_sq {p : ℕ} [NeZero p] (hp : 1 < p) :
    ∑ x : ZMod (p ^ 2), valOneVec p x * valOneVec p x = (p : ℂ) - 1 := by
  have hterm : ∀ x : ZMod (p ^ 2), valOneVec p x * valOneVec p x
      = multipleIndicator p x - deltaZero p x := by
    intro x
    simp only [valOneVec]
    have h1 := multipleIndicator_sq p x
    have h2 := deltaZero_sq p x
    have h3 := sum_multipleIndicator_mul_deltaZero p x
    linear_combination h1 - 2 * h3 + h2
  simp only [hterm]
  rw [Finset.sum_sub_distrib, sum_multipleIndicator hp, sum_deltaZero]

theorem sum_unitIndicator_sq {p : ℕ} [NeZero p] (hp : 1 < p) :
    ∑ x : ZMod (p ^ 2), unitIndicator p x * unitIndicator p x = (p : ℂ) ^ 2 - (p : ℂ) := by
  have hterm : ∀ x : ZMod (p ^ 2), unitIndicator p x * unitIndicator p x = unitIndicator p x := by
    intro x
    rw [unitIndicator]
    by_cases h : (p : ℕ) ∣ x.val <;> simp [h]
  simp only [hterm]
  exact sum_unitIndicator hp

theorem prime_mul_eq_zero_iff {p : ℕ} [NeZero p] (hp : 1 < p) (k : ZMod (p ^ 2)) :
    (p : ZMod (p ^ 2)) * k = 0 ↔ (p : ℕ) ∣ k.val := by
  have hcast : (p : ZMod (p ^ 2)) * k = ((p * k.val : ℕ) : ZMod (p ^ 2)) := by
    push_cast
    rw [ZMod.natCast_val, ZMod.cast_id]
  rw [hcast, ZMod.natCast_eq_zero_iff]
  constructor
  · intro h
    have hmul : p * p ∣ p * k.val := by
      calc p * p = p ^ 2 := by ring
        _ ∣ p * k.val := h
    exact (mul_dvd_mul_iff_left (by omega : p ≠ 0)).mp hmul
  · rintro ⟨c, hc⟩
    refine ⟨c, ?_⟩
    rw [hc]
    ring

/-- **Unitary Fourier image of the unit-residue stratum.** -/
theorem primeSquareFourier_unitIndicator {p : ℕ} [NeZero p] (hp : 1 < p) (k : ZMod (p ^ 2)) :
    primeSquareFourier p (unitIndicator p) k
      = (p : ℂ) * deltaZero p k - multipleIndicator p k := by
  have hp0 : ((p : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [primeSquareFourier, dft_unitIndicator hp]
  by_cases hk : k = 0
  · subst hk
    have hpk : (p : ZMod (p ^ 2)) * 0 = 0 := by ring
    rw [if_pos rfl, if_pos hpk, deltaZero, if_pos rfl, multipleIndicator_zero]
    field_simp
  · have hdelta : deltaZero p k = 0 := by rw [deltaZero, if_neg hk]
    by_cases hdvd : (p : ℕ) ∣ k.val
    · have hpk : (p : ZMod (p ^ 2)) * k = 0 := (prime_mul_eq_zero_iff hp k).mpr hdvd
      have hmult : multipleIndicator p k = 1 := by rw [multipleIndicator, if_pos hdvd]
      rw [if_neg hk, if_pos hpk, hdelta, hmult]
      field_simp
      ring
    · have hpk : ¬ (p : ZMod (p ^ 2)) * k = 0 :=
        fun hcon => hdvd ((prime_mul_eq_zero_iff hp k).mp hcon)
      have hmult : multipleIndicator p k = 0 := by rw [multipleIndicator, if_neg hdvd]
      rw [if_neg hk, if_neg hpk, hdelta, hmult]
      simp

/-- **Unitary Fourier image of the valuation-one stratum.** -/
theorem primeSquareFourier_valOneVec {p : ℕ} [NeZero p] (hp : 1 < p) (k : ZMod (p ^ 2)) :
    primeSquareFourier p (valOneVec p) k = multipleIndicator p k - ((p : ℂ))⁻¹ := by
  have hp0 : ((p : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hdft : ZMod.dft (valOneVec p) k
      = (if (p : ZMod (p ^ 2)) * k = 0 then (p : ℂ) else 0) - 1 := by
    have hfun : valOneVec p = multipleIndicator p - deltaZero p := by
      funext x
      simp [valOneVec]
    rw [hfun, map_sub, Pi.sub_apply, dft_multipleIndicator hp, dft_deltaZero]
  rw [primeSquareFourier, hdft]
  by_cases hdvd : (p : ℕ) ∣ k.val
  · have hpk : (p : ZMod (p ^ 2)) * k = 0 := (prime_mul_eq_zero_iff hp k).mpr hdvd
    have hmult : multipleIndicator p k = 1 := by rw [multipleIndicator, if_pos hdvd]
    rw [if_pos hpk, hmult]
    field_simp
  · have hpk : ¬ (p : ZMod (p ^ 2)) * k = 0 :=
      fun hcon => hdvd ((prime_mul_eq_zero_iff hp k).mp hcon)
    have hmult : multipleIndicator p k = 0 := by rw [multipleIndicator, if_neg hdvd]
    rw [if_neg hpk, hmult]
    field_simp
    ring

theorem conj_unitIndicator (p : ℕ) [NeZero p] (x : ZMod (p ^ 2)) :
    (starRingEnd ℂ) (unitIndicator p x) = unitIndicator p x := by
  rw [unitIndicator]
  by_cases h : (p : ℕ) ∣ x.val <;> simp [h]

theorem conj_multipleIndicator (p : ℕ) [NeZero p] (x : ZMod (p ^ 2)) :
    (starRingEnd ℂ) (multipleIndicator p x) = multipleIndicator p x := by
  rw [multipleIndicator]
  by_cases h : (p : ℕ) ∣ x.val <;> simp [h]

theorem conj_deltaZero (p : ℕ) [NeZero p] (x : ZMod (p ^ 2)) :
    (starRingEnd ℂ) (deltaZero p x) = deltaZero p x := by
  rw [deltaZero]
  by_cases h : x = 0 <;> simp [h]

theorem conj_valOneVec (p : ℕ) [NeZero p] (x : ZMod (p ^ 2)) :
    (starRingEnd ℂ) (valOneVec p x) = valOneVec p x := by
  simp only [valOneVec, map_sub, conj_multipleIndicator, conj_deltaZero]

theorem sum_unitIndicator_mul_deltaZero (p : ℕ) [NeZero p] :
    ∑ x : ZMod (p ^ 2), unitIndicator p x * deltaZero p x = 0 := by
  simp [unitIndicator_mul_deltaZero]

theorem sum_unitIndicator_mul_multipleIndicator (p : ℕ) [NeZero p] :
    ∑ x : ZMod (p ^ 2), unitIndicator p x * multipleIndicator p x = 0 := by
  simp [unitIndicator_mul_multipleIndicator]

theorem sum_multipleIndicator_mul_deltaZero_eq (p : ℕ) [NeZero p] :
    ∑ x : ZMod (p ^ 2), multipleIndicator p x * deltaZero p x = 1 := by
  simp only [sum_multipleIndicator_mul_deltaZero]
  exact sum_deltaZero p

theorem sum_multipleIndicator_sq {p : ℕ} [NeZero p] (hp : 1 < p) :
    ∑ x : ZMod (p ^ 2), multipleIndicator p x * multipleIndicator p x = (p : ℂ) := by
  simp only [multipleIndicator_sq]
  exact sum_multipleIndicator hp

theorem sum_deltaZero_sq (p : ℕ) [NeZero p] :
    ∑ x : ZMod (p ^ 2), deltaZero p x * deltaZero p x = 1 := by
  simp only [deltaZero_sq]
  exact sum_deltaZero p

/-- **The Fourier compression is transverse on the unit stratum.** -/
theorem countInner_unit_fourier_unit {p : ℕ} [NeZero p] (hp : 1 < p) :
    countInner p (unitIndicator p) (primeSquareFourier p (unitIndicator p)) = 0 := by
  rw [countInner]
  have hterm : ∀ x : ZMod (p ^ 2),
      (starRingEnd ℂ) (unitIndicator p x) * primeSquareFourier p (unitIndicator p) x
        = (p : ℂ) * (unitIndicator p x * deltaZero p x)
          - unitIndicator p x * multipleIndicator p x := by
    intro x
    rw [primeSquareFourier_unitIndicator hp, conj_unitIndicator]
    ring
  simp only [hterm, unitIndicator_mul_deltaZero, unitIndicator_mul_multipleIndicator]
  simp

/-- **The off-diagonal compression entry, valuation-one row.** -/
theorem countInner_valOne_fourier_unit {p : ℕ} [NeZero p] (hp : 1 < p) :
    countInner p (valOneVec p) (primeSquareFourier p (unitIndicator p)) = -((p : ℂ) - 1) := by
  rw [countInner]
  have hterm : ∀ x : ZMod (p ^ 2),
      (starRingEnd ℂ) (valOneVec p x) * primeSquareFourier p (unitIndicator p) x
        = deltaZero p x - multipleIndicator p x := by
    intro x
    rw [primeSquareFourier_unitIndicator hp, conj_valOneVec]
    simp only [valOneVec]
    have h1 := multipleIndicator_sq p x
    have h2 := deltaZero_sq p x
    have h3 := sum_multipleIndicator_mul_deltaZero p x
    linear_combination (p : ℂ) * h3 - h1 - (p : ℂ) * h2 + h3
  simp only [hterm]
  rw [Finset.sum_sub_distrib, sum_deltaZero, sum_multipleIndicator hp]
  ring

/-- **The off-diagonal compression entry, unit row.** -/
theorem countInner_unit_fourier_valOne {p : ℕ} [NeZero p] (hp : 1 < p) :
    countInner p (unitIndicator p) (primeSquareFourier p (valOneVec p)) = -((p : ℂ) - 1) := by
  have hp0 : ((p : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [countInner]
  have hterm : ∀ x : ZMod (p ^ 2),
      (starRingEnd ℂ) (unitIndicator p x) * primeSquareFourier p (valOneVec p) x
        = unitIndicator p x * multipleIndicator p x - ((p : ℂ))⁻¹ * unitIndicator p x := by
    intro x
    rw [primeSquareFourier_valOneVec hp, conj_unitIndicator]
    ring
  simp only [hterm]
  rw [Finset.sum_sub_distrib, sum_unitIndicator_mul_multipleIndicator, ← Finset.mul_sum,
    sum_unitIndicator hp]
  field_simp
  ring

/-- **The diagonal compression entry on the valuation-one stratum.** -/
theorem countInner_valOne_fourier_valOne {p : ℕ} [NeZero p] (hp : 1 < p) :
    countInner p (valOneVec p) (primeSquareFourier p (valOneVec p))
      = ((p : ℂ) - 1) ^ 2 / (p : ℂ) := by
  have hp0 : ((p : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  rw [countInner]
  have hterm : ∀ x : ZMod (p ^ 2),
      (starRingEnd ℂ) (valOneVec p x) * primeSquareFourier p (valOneVec p) x
        = multipleIndicator p x - ((p : ℂ))⁻¹ * multipleIndicator p x - deltaZero p x
          + ((p : ℂ))⁻¹ * deltaZero p x := by
    intro x
    rw [primeSquareFourier_valOneVec hp, conj_valOneVec]
    simp only [valOneVec]
    have h1 := multipleIndicator_sq p x
    have h3 := sum_multipleIndicator_mul_deltaZero p x
    linear_combination h1 - h3
  simp only [hterm]
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_sub_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, sum_multipleIndicator hp, sum_deltaZero]
  field_simp
  ring

/-! ### The deformed occupation line and its reflected Fourier coefficient -/

/-- The deformed occupation line, before normalization: `1_U + p^c (1_V)`. -/
def deformedOccupationRaw (p : ℕ) [NeZero p] (c : ℝ) : ZMod (p ^ 2) → ℂ :=
  fun x => unitIndicator p x + (((p : ℝ) ^ c : ℝ) : ℂ) * valOneVec p x

theorem deformedOccupationRaw_eq (p : ℕ) [NeZero p] (c : ℝ) :
    deformedOccupationRaw p c
      = unitIndicator p + (((p : ℝ) ^ c : ℝ) : ℂ) • valOneVec p := by
  funext x
  simp [deformedOccupationRaw, Pi.add_apply, Pi.smul_apply]

theorem countInner_deformedOccupationRaw {p : ℕ} [NeZero p] (hp : 1 < p) (c : ℝ) :
    countInner p (deformedOccupationRaw p (-c)) (primeSquareFourier p (deformedOccupationRaw p c))
      = ((p : ℂ) - 1) *
        ((((p : ℂ) - 1) / (p : ℂ))
          - ((((p : ℝ) ^ c : ℝ) : ℂ) + (((p : ℝ) ^ (-c) : ℝ) : ℂ))) := by
  have hp0 : ((p : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hpr : (0 : ℝ) < (p : ℝ) := by
    have : 0 < p := by omega
    exact_mod_cast this
  have hfourier : primeSquareFourier p (deformedOccupationRaw p c)
      = fun x => primeSquareFourier p (unitIndicator p) x
        + (((p : ℝ) ^ c : ℝ) : ℂ) * primeSquareFourier p (valOneVec p) x := by
    funext x
    simp only [primeSquareFourier]
    rw [deformedOccupationRaw_eq, map_add, map_smul]
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring
  have hconj : ∀ x : ZMod (p ^ 2), (starRingEnd ℂ) (deformedOccupationRaw p (-c) x)
      = unitIndicator p x + (((p : ℝ) ^ (-c) : ℝ) : ℂ) * valOneVec p x := by
    intro x
    rw [deformedOccupationRaw, map_add, map_mul, conj_unitIndicator, conj_valOneVec,
      Complex.conj_ofReal]
  rw [countInner]
  simp only [hconj, hfourier]
  have hexpand : ∀ x : ZMod (p ^ 2),
      (unitIndicator p x + (((p : ℝ) ^ (-c) : ℝ) : ℂ) * valOneVec p x) *
        (primeSquareFourier p (unitIndicator p) x
          + (((p : ℝ) ^ c : ℝ) : ℂ) * primeSquareFourier p (valOneVec p) x)
      = (starRingEnd ℂ) (unitIndicator p x) * primeSquareFourier p (unitIndicator p) x
        + (((p : ℝ) ^ c : ℝ) : ℂ) *
            ((starRingEnd ℂ) (unitIndicator p x) * primeSquareFourier p (valOneVec p) x)
        + (((p : ℝ) ^ (-c) : ℝ) : ℂ) *
            ((starRingEnd ℂ) (valOneVec p x) * primeSquareFourier p (unitIndicator p) x)
        + (((p : ℝ) ^ c : ℝ) : ℂ) * (((p : ℝ) ^ (-c) : ℝ) : ℂ) *
            ((starRingEnd ℂ) (valOneVec p x) * primeSquareFourier p (valOneVec p) x) := by
    intro x
    rw [conj_unitIndicator, conj_valOneVec]
    ring
  simp only [hexpand]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
  rw [← countInner, ← countInner, ← countInner, ← countInner,
    countInner_unit_fourier_unit hp, countInner_unit_fourier_valOne hp,
    countInner_valOne_fourier_unit hp, countInner_valOne_fourier_valOne hp]
  have hinv : (((p : ℝ) ^ c : ℝ) : ℂ) * (((p : ℝ) ^ (-c) : ℝ) : ℂ) = 1 := by
    rw [← Complex.ofReal_mul, ← Real.rpow_add hpr]
    simp
  rw [hinv]
  field_simp
  ring

theorem countInner_smul_left (p : ℕ) [NeZero p] (s : ℂ) (f g : ZMod (p ^ 2) → ℂ) :
    countInner p (fun x => s * f x) g = (starRingEnd ℂ) s * countInner p f g := by
  rw [countInner, countInner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [map_mul]
  ring

theorem countInner_smul_right (p : ℕ) [NeZero p] (t : ℂ) (f g : ZMod (p ^ 2) → ℂ) :
    countInner p f (fun x => t * g x) = t * countInner p f g := by
  rw [countInner, countInner, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x _ => ?_
  ring

theorem primeSquareFourier_smul (p : ℕ) [NeZero p] (t : ℂ) (g : ZMod (p ^ 2) → ℂ) :
    primeSquareFourier p (fun x => t * g x) = fun k => t * primeSquareFourier p g k := by
  funext k
  simp only [primeSquareFourier]
  have hsmul : (fun x => t * g x) = t • g := by
    funext x
    simp [Pi.smul_apply, smul_eq_mul]
  rw [hsmul, map_smul]
  simp only [Pi.smul_apply, smul_eq_mul]
  ring

/-- The normalized deformed occupation line `q_{p,c}`. -/
def deformedOccupationLine (p : ℕ) [NeZero p] (c : ℝ) : ZMod (p ^ 2) → ℂ :=
  fun x => ((Real.sqrt (((p : ℝ) - 1) * ((p : ℝ) + (p : ℝ) ^ (2 * c))) : ℝ) : ℂ)⁻¹
    * deformedOccupationRaw p c x

theorem deformedOccupationLine_eq (p : ℕ) [NeZero p] (c : ℝ) :
    deformedOccupationLine p c
      = fun x => ((Real.sqrt (((p : ℝ) - 1) * ((p : ℝ) + (p : ℝ) ^ (2 * c))) : ℝ) : ℂ)⁻¹
        * deformedOccupationRaw p c x := rfl

/-- The reflected-line Fourier coefficient `α_p(c)`. -/
def reflectedLineCoefficient (p : ℕ) [NeZero p] (c : ℝ) : ℂ :=
  countInner p (deformedOccupationLine p (-c)) (primeSquareFourier p (deformedOccupationLine p c))

/-- **The exact reflected-line coefficient.** -/
theorem reflectedLineCoefficient_eq {p : ℕ} [NeZero p] (hp : 1 < p) (c : ℝ) :
    reflectedLineCoefficient p c
      = ((((p : ℝ) - 1) / (p : ℝ) - ((p : ℝ) ^ c + (p : ℝ) ^ (-c)))
          / Real.sqrt (((p : ℝ) + (p : ℝ) ^ (2 * c)) * ((p : ℝ) + (p : ℝ) ^ (-2 * c))) : ℝ) := by
  have hpr : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hp1 : (0 : ℝ) < (p : ℝ) - 1 := by linarith
  have hposPlus : (0 : ℝ) < (p : ℝ) + (p : ℝ) ^ (2 * c) := by
    have := Real.rpow_pos_of_pos (by linarith : (0:ℝ) < (p:ℝ)) (2 * c)
    linarith
  have hposMinus : (0 : ℝ) < (p : ℝ) + (p : ℝ) ^ (-2 * c) := by
    have := Real.rpow_pos_of_pos (by linarith : (0:ℝ) < (p:ℝ)) (-2 * c)
    linarith
  have hsplit : Real.sqrt (((p : ℝ) - 1) * ((p : ℝ) + (p : ℝ) ^ (2 * -c)))
      * Real.sqrt (((p : ℝ) - 1) * ((p : ℝ) + (p : ℝ) ^ (2 * c)))
      = ((p : ℝ) - 1) * Real.sqrt (((p : ℝ) + (p : ℝ) ^ (2 * c)) * ((p : ℝ) + (p : ℝ) ^ (-2 * c))) := by
    have hrw : (2 : ℝ) * -c = -2 * c := by ring
    rw [hrw, ← Real.sqrt_mul (by positivity)]
    have hprod : ((p : ℝ) - 1) * ((p : ℝ) + (p : ℝ) ^ (-2 * c))
        * (((p : ℝ) - 1) * ((p : ℝ) + (p : ℝ) ^ (2 * c)))
        = ((p : ℝ) - 1) ^ 2 * (((p : ℝ) + (p : ℝ) ^ (2 * c)) * ((p : ℝ) + (p : ℝ) ^ (-2 * c))) := by
      ring
    rw [hprod, Real.sqrt_mul (by positivity), Real.sqrt_sq hp1.le]
  rw [reflectedLineCoefficient, deformedOccupationLine_eq, deformedOccupationLine_eq,
    primeSquareFourier_smul, countInner_smul_left, countInner_smul_right,
    countInner_deformedOccupationRaw hp]
  rw [Complex.conj_inv, Complex.conj_ofReal]
  have hcast : ((Real.sqrt (((p : ℝ) - 1) * ((p : ℝ) + (p : ℝ) ^ (2 * -c))) : ℝ) : ℂ)⁻¹
      * (((Real.sqrt (((p : ℝ) - 1) * ((p : ℝ) + (p : ℝ) ^ (2 * c))) : ℝ) : ℂ)⁻¹)
      = (((Real.sqrt (((p : ℝ) - 1) * ((p : ℝ) + (p : ℝ) ^ (2 * -c)))
          * Real.sqrt (((p : ℝ) - 1) * ((p : ℝ) + (p : ℝ) ^ (2 * c))) : ℝ)) : ℂ)⁻¹ := by
    rw [Complex.ofReal_mul, mul_inv]
  rw [← mul_assoc, hcast, hsplit]
  have hp0 : ((p : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hp1c : ((p : ℂ) - 1) ≠ 0 := by
    intro hcon
    have : (p : ℂ) = 1 := by linear_combination hcon
    have hnat : (p : ℝ) = 1 := by exact_mod_cast congrArg Complex.re this
    linarith
  have hsqrtpos : (0 : ℝ)
      < Real.sqrt (((p : ℝ) + (p : ℝ) ^ (2 * c)) * ((p : ℝ) + (p : ℝ) ^ (-2 * c))) :=
    Real.sqrt_pos.mpr (by positivity)
  push_cast
  field_simp

/-- **The critical reflected coefficient.**  At zero radial drift the reflected-line coefficient is
the transverse Fourier eigenvalue `-1/p`. -/
theorem reflectedLineCoefficient_zero {p : ℕ} [NeZero p] (hp : 1 < p) :
    reflectedLineCoefficient p 0 = -((p : ℂ))⁻¹ := by
  have hpr : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hp0 : ((p : ℂ)) ≠ 0 := Nat.cast_ne_zero.mpr (by omega)
  have hprne : ((p : ℝ)) ≠ 0 := by linarith
  rw [reflectedLineCoefficient_eq hp]
  have hzero : ((p : ℝ)) ^ (0 : ℝ) = 1 := Real.rpow_zero _
  have hzero' : ((p : ℝ)) ^ (-(0 : ℝ)) = 1 := by simp
  have hsq : Real.sqrt (((p : ℝ) + (p : ℝ) ^ (2 * (0:ℝ))) * ((p : ℝ) + (p : ℝ) ^ (-2 * (0:ℝ))))
      = (p : ℝ) + 1 := by
    have h1 : (2 : ℝ) * (0 : ℝ) = 0 := by ring
    have h2 : (-2 : ℝ) * (0 : ℝ) = 0 := by ring
    rw [h1, h2, hzero]
    have hsame : ((p : ℝ) + 1) * ((p : ℝ) + 1) = ((p : ℝ) + 1) ^ 2 := by ring
    rw [hsame, Real.sqrt_sq (by linarith)]
  rw [hsq, hzero, hzero']
  have hnum : (((p : ℝ) - 1) / (p : ℝ) - (1 + 1)) / ((p : ℝ) + 1) = -((p : ℝ))⁻¹ := by
    field_simp
    ring
  rw [hnum]
  push_cast
  simp

/-- The critical normalization `β_p(c) = α_p(c)/α_p(0)`. -/
def criticalNormalizedReflection (p : ℕ) (c : ℝ) : ℝ :=
  ((p : ℝ) * ((p : ℝ) ^ c + (p : ℝ) ^ (-c)) - ((p : ℝ) - 1))
    / Real.sqrt (((p : ℝ) + (p : ℝ) ^ (2 * c)) * ((p : ℝ) + (p : ℝ) ^ (-2 * c)))

theorem criticalNormalizedReflection_eq {p : ℕ} [NeZero p] (hp : 1 < p) (c : ℝ) :
    ((criticalNormalizedReflection p c : ℝ) : ℂ) = -(p : ℂ) * reflectedLineCoefficient p c := by
  have hpr : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hprne : ((p : ℝ)) ≠ 0 := by linarith
  have hreal : criticalNormalizedReflection p c
      = -(p : ℝ) * ((((p : ℝ) - 1) / (p : ℝ) - ((p : ℝ) ^ c + (p : ℝ) ^ (-c)))
          / Real.sqrt (((p : ℝ) + (p : ℝ) ^ (2 * c)) * ((p : ℝ) + (p : ℝ) ^ (-2 * c)))) := by
    rw [criticalNormalizedReflection]
    field_simp
    ring
  rw [reflectedLineCoefficient_eq hp, hreal]
  push_cast
  ring

/-- **The sharp criticality identity.**  The squared numerator minus the squared denominator of the
critically normalized reflection is `p(p-1)x(x-2)`. -/
theorem reflection_numerator_sq_sub (p r : ℝ) (hr : 0 < r) :
    ((p * (r + r⁻¹) - (p - 1)) ^ 2 - (p + r ^ 2) * (p + (r⁻¹) ^ 2))
      = p * (p - 1) * (r + r⁻¹) * ((r + r⁻¹) - 2) := by
  field_simp
  ring

theorem two_le_add_inv {r : ℝ} (hr : 0 < r) : 2 ≤ r + r⁻¹ := by
  have h := sq_nonneg (r - 1)
  have hrne : r ≠ 0 := ne_of_gt hr
  rw [← sub_nonneg]
  have hkey : r + r⁻¹ - 2 = (r - 1) ^ 2 / r := by
    field_simp
    ring
  rw [hkey]
  positivity

/-- **The local criticality law.**  The critically normalized reflected coefficient is at least
one, with equality exactly at zero radial drift. -/
theorem one_le_criticalNormalizedReflection {p : ℕ} (hp : 1 < p) (c : ℝ) :
    1 ≤ criticalNormalizedReflection p c := by
  have hpr : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  set r : ℝ := (p : ℝ) ^ c with hrdef
  have hr : 0 < r := Real.rpow_pos_of_pos hp0 c
  have hrinv : (p : ℝ) ^ (-c) = r⁻¹ := by
    rw [hrdef, ← Real.rpow_neg hp0.le]
  have hr2 : (p : ℝ) ^ (2 * c) = r ^ 2 := by
    rw [hrdef, ← Real.rpow_natCast ((p : ℝ) ^ c) 2, ← Real.rpow_mul hp0.le]
    congr 1
    push_cast
    ring
  have hrinv2 : (p : ℝ) ^ (-2 * c) = (r⁻¹) ^ 2 := by
    rw [← hrinv, ← Real.rpow_natCast ((p : ℝ) ^ (-c)) 2, ← Real.rpow_mul hp0.le]
    congr 1
    push_cast
    ring
  have hx : 2 ≤ r + r⁻¹ := two_le_add_inv hr
  have hN : 0 < (p : ℝ) * (r + r⁻¹) - ((p : ℝ) - 1) := by nlinarith
  have hDsq : (0 : ℝ) < ((p : ℝ) + r ^ 2) * ((p : ℝ) + (r⁻¹) ^ 2) := by positivity
  have hD : 0 < Real.sqrt (((p : ℝ) + r ^ 2) * ((p : ℝ) + (r⁻¹) ^ 2)) := Real.sqrt_pos.mpr hDsq
  have hDsq' : (Real.sqrt (((p : ℝ) + r ^ 2) * ((p : ℝ) + (r⁻¹) ^ 2))) ^ 2
      = ((p : ℝ) + r ^ 2) * ((p : ℝ) + (r⁻¹) ^ 2) := Real.sq_sqrt hDsq.le
  have hident := reflection_numerator_sq_sub (p : ℝ) r hr
  have hnonneg : (0 : ℝ) ≤ (p : ℝ) * ((p : ℝ) - 1) * (r + r⁻¹) * ((r + r⁻¹) - 2) := by
    have h1 : (0 : ℝ) ≤ (p : ℝ) - 1 := by linarith
    have h2 : (0 : ℝ) ≤ r + r⁻¹ := by linarith
    have h3 : (0 : ℝ) ≤ (r + r⁻¹) - 2 := by linarith
    positivity
  have hsqle : Real.sqrt (((p : ℝ) + r ^ 2) * ((p : ℝ) + (r⁻¹) ^ 2)) ^ 2
      ≤ ((p : ℝ) * (r + r⁻¹) - ((p : ℝ) - 1)) ^ 2 := by
    rw [hDsq']
    linarith [hident, hnonneg]
  have hge : Real.sqrt (((p : ℝ) + r ^ 2) * ((p : ℝ) + (r⁻¹) ^ 2))
      ≤ (p : ℝ) * (r + r⁻¹) - ((p : ℝ) - 1) :=
    le_of_pow_le_pow_left₀ two_ne_zero hN.le hsqle
  rw [criticalNormalizedReflection, hrinv, hr2, hrinv2, ← hrdef]
  rw [le_div_iff₀ hD]
  linarith

/-- **The equality locus of the criticality law is exactly zero radial drift.** -/
theorem criticalNormalizedReflection_eq_one_iff {p : ℕ} (hp : 1 < p) (c : ℝ) :
    criticalNormalizedReflection p c = 1 ↔ c = 0 := by
  have hpr : (1 : ℝ) < (p : ℝ) := by exact_mod_cast hp
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  constructor
  · intro hone
    set r : ℝ := (p : ℝ) ^ c with hrdef
    have hr : 0 < r := Real.rpow_pos_of_pos hp0 c
    have hrinv : (p : ℝ) ^ (-c) = r⁻¹ := by
      rw [hrdef, ← Real.rpow_neg hp0.le]
    have hr2 : (p : ℝ) ^ (2 * c) = r ^ 2 := by
      rw [hrdef, ← Real.rpow_natCast ((p : ℝ) ^ c) 2, ← Real.rpow_mul hp0.le]
      congr 1
      push_cast
      ring
    have hrinv2 : (p : ℝ) ^ (-2 * c) = (r⁻¹) ^ 2 := by
      rw [← hrinv, ← Real.rpow_natCast ((p : ℝ) ^ (-c)) 2, ← Real.rpow_mul hp0.le]
      congr 1
      push_cast
      ring
    have hx : 2 ≤ r + r⁻¹ := two_le_add_inv hr
    have hDsq : (0 : ℝ) < ((p : ℝ) + r ^ 2) * ((p : ℝ) + (r⁻¹) ^ 2) := by positivity
    have hD : 0 < Real.sqrt (((p : ℝ) + r ^ 2) * ((p : ℝ) + (r⁻¹) ^ 2)) := Real.sqrt_pos.mpr hDsq
    have hDsq' : (Real.sqrt (((p : ℝ) + r ^ 2) * ((p : ℝ) + (r⁻¹) ^ 2))) ^ 2
        = ((p : ℝ) + r ^ 2) * ((p : ℝ) + (r⁻¹) ^ 2) := Real.sq_sqrt hDsq.le
    rw [criticalNormalizedReflection, hrinv, hr2, hrinv2, ← hrdef, div_eq_one_iff_eq hD.ne'] at hone
    have hident := reflection_numerator_sq_sub (p : ℝ) r hr
    rw [hone, hDsq'] at hident
    have hzero : (p : ℝ) * ((p : ℝ) - 1) * (r + r⁻¹) * ((r + r⁻¹) - 2) = 0 := by
      linarith [hident]
    have hx2 : r + r⁻¹ = 2 := by
      have hne1 : (p : ℝ) ≠ 0 := hp0.ne'
      have hne2 : (p : ℝ) - 1 ≠ 0 := by
        intro hcon
        have : (p : ℝ) = 1 := by linarith
        linarith
      have hne3 : r + r⁻¹ ≠ 0 := by
        have : 0 < r + r⁻¹ := by linarith
        exact this.ne'
      rcases mul_eq_zero.mp hzero with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · rcases mul_eq_zero.mp h' with h'' | h''
          · exact absurd h'' hne1
          · exact absurd h'' hne2
        · exact absurd h' hne3
      · linarith
    have hr1 : r = 1 := by
      have hkey : (r - 1) ^ 2 / r = 0 := by
        have : r + r⁻¹ - 2 = (r - 1) ^ 2 / r := by
          field_simp
          ring
        rw [← this, hx2]
        ring
      have hsq : (r - 1) ^ 2 = 0 := by
        field_simp at hkey
        linarith [hkey]
      have : r - 1 = 0 := by
        exact pow_eq_zero_iff (n := 2) two_ne_zero |>.mp hsq
      linarith
    have hlog := congrArg Real.log hr1
    rw [hrdef, Real.log_rpow hp0, Real.log_one] at hlog
    have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hpr
    rcases mul_eq_zero.mp hlog with h | h
    · exact h
    · exact absurd h hlogp.ne'
  · rintro rfl
    have hzero : ((p : ℝ)) ^ (0 : ℝ) = 1 := Real.rpow_zero _
    have hzero' : ((p : ℝ)) ^ (-(0 : ℝ)) = 1 := by simp
    have h1 : (2 : ℝ) * (0 : ℝ) = 0 := by ring
    have h2 : (-2 : ℝ) * (0 : ℝ) = 0 := by ring
    rw [criticalNormalizedReflection, h1, h2, hzero, hzero']
    have hsame : ((p : ℝ) + 1) * ((p : ℝ) + 1) = ((p : ℝ) + 1) ^ 2 := by ring
    rw [hsame, Real.sqrt_sq (by linarith)]
    field_simp
    ring

end

end RHTower
