import GaloisForLFunctions.ArithmeticEffectivityTheory.TheBurgessMoment
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheBurgessEnergy
import GaloisForLFunctions.ArithmeticEffectivityTheory.TheCompletionLaw

/-!
# Burgess's bound for quadratic character sums

Let `p` be an odd prime, `χ` the quadratic character and `S(M, N) = Σ_{k<N} χ(M + k)`.

* **Hölder over fibres** (`pow_sum_le_holder`): `(Σ ν t)^{2r} ≤ (Σν)^{2r−2} (Σν²) (Σ t^{2r})`.
* **The Burgess inequality** (`abs_burgessSum_pow_le`): with `a ∈ (A, 2A]`, `b < B`, `4AN ≤ p`,
  `|Σ_{a,b} S(M + ab, N)|^{2r} ≤ (AN)^{2r−2} · E · (r^{2r}B^r p + 6rB^{2r}√p)`, where `E` is the
  energy of the box: `χ(M + m + ab) = χ(a) χ(ā(M + m) + b)`, so the sum is a weighted sum of the
  short sums `T(x) = Σ_{b<B} χ(x + b)` along the points `x = ā(M + m)`.
-/

open Finset

namespace GaloisForLFunctions.ArithmeticEffectivityTheory

/-- **Hölder for a weighted sum**: `(Σ ν t)^{2r} ≤ (Σν)^{2r−2} (Σ ν²) (Σ t^{2r})` for `ν, t ≥ 0`.
The power mean gives `(Σνt)^r ≤ (Σν)^{r−1} Σ ν t^r`, Cauchy–Schwarz the rest. -/
theorem pow_sum_le_holder {ι : Type*} (s : Finset ι) (ν t : ι → ℝ) (hν : ∀ i ∈ s, 0 ≤ ν i)
    (ht : ∀ i ∈ s, 0 ≤ t i) {r : ℕ} (hr : 1 ≤ r) :
    (∑ i ∈ s, ν i * t i) ^ (2 * r) ≤
      (∑ i ∈ s, ν i) ^ (2 * r - 2) * (∑ i ∈ s, ν i ^ 2) * ∑ i ∈ s, t i ^ (2 * r) := by
  set W := ∑ i ∈ s, ν i
  have hW0 : 0 ≤ W := Finset.sum_nonneg hν
  rcases hW0.lt_or_eq with hW | hW
  · have hmean : (∑ i ∈ s, ν i * t i) ^ r ≤ W ^ (r - 1) * ∑ i ∈ s, ν i * t i ^ r := by
      have h := Real.pow_arith_mean_le_arith_mean_pow s (fun i => ν i / W) t
        (fun i hi => div_nonneg (hν i hi) hW.le) (by rw [← Finset.sum_div, div_self hW.ne'])
        ht r
      have e1 : ∑ i ∈ s, ν i / W * t i = (∑ i ∈ s, ν i * t i) / W := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
      have e2 : ∑ i ∈ s, ν i / W * t i ^ r = (∑ i ∈ s, ν i * t i ^ r) / W := by
        rw [Finset.sum_div]; exact Finset.sum_congr rfl fun i _ => by ring
      rw [e1, e2, div_pow, div_le_div_iff₀ (pow_pos hW r) hW] at h
      have hWr : W ^ r = W ^ (r - 1) * W := by rw [← pow_succ]; congr 1; omega
      rw [hWr] at h
      refine le_of_mul_le_mul_right ?_ hW
      calc (∑ i ∈ s, ν i * t i) ^ r * W ≤ (∑ i ∈ s, ν i * t i ^ r) * (W ^ (r - 1) * W) := h
        _ = W ^ (r - 1) * (∑ i ∈ s, ν i * t i ^ r) * W := by ring
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq s ν (fun i => t i ^ r)
    have hpos : 0 ≤ (∑ i ∈ s, ν i * t i) ^ r :=
      pow_nonneg (Finset.sum_nonneg fun i hi => mul_nonneg (hν i hi) (ht i hi)) r
    calc (∑ i ∈ s, ν i * t i) ^ (2 * r) = ((∑ i ∈ s, ν i * t i) ^ r) ^ 2 := by
          rw [← pow_mul, mul_comm]
      _ ≤ (W ^ (r - 1) * ∑ i ∈ s, ν i * t i ^ r) ^ 2 := pow_le_pow_left₀ hpos hmean 2
      _ = W ^ (2 * r - 2) * (∑ i ∈ s, ν i * t i ^ r) ^ 2 := by
          rw [mul_pow, ← pow_mul]; congr 2; omega
      _ ≤ W ^ (2 * r - 2) * ((∑ i ∈ s, ν i ^ 2) * ∑ i ∈ s, (t i ^ r) ^ 2) :=
          mul_le_mul_of_nonneg_left hcs (pow_nonneg hW0 _)
      _ = _ := by
          simp_rw [← pow_mul, mul_comm r 2]; ring
  · have hν0 : ∀ i ∈ s, ν i = 0 := (Finset.sum_eq_zero_iff_of_nonneg hν).mp hW.symm
    rw [Finset.sum_eq_zero fun i hi => by rw [hν0 i hi, zero_mul], zero_pow (by omega)]
    refine mul_nonneg (mul_nonneg (pow_nonneg hW0 _) (Finset.sum_nonneg fun i _ => sq_nonneg _))
      (Finset.sum_nonneg fun i hi => pow_nonneg (ht i hi) _)

/-! ### The Burgess inequality -/

section Burgess

variable {p : ℕ} [hp : Fact p.Prime]

/-- `S(M, N) = Σ_{k<N} χ(M + k)`. -/
noncomputable def burgessS (p : ℕ) [Fact p.Prime] (M : ℤ) (N : ℕ) : ℝ :=
  ∑ k ∈ range N, chiR (((M + k : ℤ)) : ZMod p)

/-- The shifts `0, …, B − 1` as residues. -/
noncomputable def shiftSet (p B : ℕ) : Finset (ZMod p) :=
  Finset.image (fun b : ℕ => (b : ZMod p)) (Finset.range B)

omit hp in
theorem card_shiftSet {B : ℕ} (hB : B ≤ p) : (shiftSet p B).card = B := by
  rw [shiftSet, Finset.card_image_of_injOn, Finset.card_range]
  intro a ha b hb h
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  have := (ZMod.natCast_eq_natCast_iff' a b p).mp h
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this

theorem shiftSum_shiftSet {B : ℕ} (hB : B ≤ p) (x : ZMod p) :
    shiftSum (shiftSet p B) x = ∑ b ∈ range B, chiR (x + b) := by
  rw [shiftSum, shiftSet, Finset.sum_image]
  intro a ha b hb h
  simp only [Finset.coe_range, Set.mem_Iio] at ha hb
  have := (ZMod.natCast_eq_natCast_iff' a b p).mp h
  rwa [Nat.mod_eq_of_lt (by omega), Nat.mod_eq_of_lt (by omega)] at this

/-- The point `ā(M + m)` of the box. -/
noncomputable def boxPoint (p : ℕ) (M : ℤ) (q : ℕ × ℕ) : ZMod p :=
  ((q.1 : ZMod p))⁻¹ * ((M + q.2 : ℤ) : ZMod p)

/-- **The shift factorization**: for `0 < a < p`,
`Σ_{b<B} χ(M + m + ab) = χ(a) · T(ā(M + m))`. -/
theorem sum_shift_eq {B : ℕ} (hB : B ≤ p) (M : ℤ) {a m : ℕ} (ha0 : 0 < a) (hap : a < p) :
    ∑ b ∈ range B, chiR (((M + (a * b : ℕ) + m : ℤ)) : ZMod p) =
      chiR (a : ZMod p) * shiftSum (shiftSet p B) (boxPoint p M (a, m)) := by
  have ha : (a : ZMod p) ≠ 0 := by
    rw [Ne, ZMod.natCast_eq_zero_iff]
    exact fun h => absurd (Nat.le_of_dvd ha0 h) (by omega)
  rw [shiftSum_shiftSet hB, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [← chiR_mul]
  congr 1
  simp only [boxPoint]
  push_cast
  field_simp
  ring

theorem natCast_ne_zero_of_lt {a : ℕ} (ha0 : 0 < a) (hap : a < p) : (a : ZMod p) ≠ 0 := by
  rw [Ne, ZMod.natCast_eq_zero_iff]
  exact fun h => absurd (Nat.le_of_dvd ha0 h) (by omega)

/-- `Σ_x ν(x)² = #{(q, q') : g q = g q'}` for the fibre sizes `ν` of `g` on `X`. -/
theorem sum_sq_card_fiber {ι κ : Type*} [Fintype κ] [DecidableEq κ] [DecidableEq ι] (X : Finset ι)
    (g : ι → κ) :
    ∑ x : κ, ((X.filter fun q => g q = x).card : ℝ) ^ 2 =
      ((X ×ˢ X).filter fun qq => g qq.1 = g qq.2).card := by
  have h1 : ∀ x : κ, ((X.filter fun q => g q = x).card : ℝ) ^ 2 =
      ∑ q ∈ X.filter (fun q => g q = x), ((X.filter fun q' => g q' = g q).card : ℝ) := by
    intro x
    rw [sq, Finset.sum_congr rfl fun q hq => by rw [(Finset.mem_filter.mp hq).2], Finset.sum_const,
      nsmul_eq_mul]
  simp_rw [h1]
  rw [Finset.sum_fiberwise_of_maps_to (g := g) (t := univ) (fun _ _ => mem_univ _)
    (fun q => ((X.filter fun q' => g q' = g q).card : ℝ))]
  rw [Finset.card_filter, Finset.sum_product]
  push_cast
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [Finset.card_filter]
  push_cast
  exact Finset.sum_congr rfl fun q' _ => by simp only [eq_comm]

/-- **The energy is the collision count of the box points**: `Σ_x ν(x)² = E`. -/
theorem sum_sq_fiber_eq_energy {A N : ℕ} (hAp : 2 * A < p) (M : ℤ) :
    ∑ x : ZMod p, ((((Ioc A (2 * A)) ×ˢ (range N)).filter fun q => boxPoint p M q = x).card
      : ℝ) ^ 2 = burgessEnergy p A N M := by
  rw [sum_sq_card_fiber, burgessEnergy]
  congr 1
  refine Finset.card_nbij' (fun qq => ((qq.1.1, qq.2.1), (qq.1.2, qq.2.2)))
    (fun q => ((q.1.1, q.2.1), (q.1.2, q.2.2))) ?_ ?_ ?_ ?_
  · intro qq hqq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hqq ⊢
    obtain ⟨⟨⟨ha₁, hm₁⟩, ⟨ha₂, hm₂⟩⟩, he⟩ := hqq
    refine ⟨⟨⟨ha₁, ha₂⟩, ⟨hm₁, hm₂⟩⟩, ?_⟩
    have h1 := natCast_ne_zero_of_lt (p := p) (by have := (Finset.mem_Ioc.mp ha₁).1; omega)
      (by have := (Finset.mem_Ioc.mp ha₁).2; omega)
    have h2 := natCast_ne_zero_of_lt (p := p) (by have := (Finset.mem_Ioc.mp ha₂).1; omega)
      (by have := (Finset.mem_Ioc.mp ha₂).2; omega)
    simp only [boxPoint] at he
    push_cast
    field_simp at he
    linear_combination he
  · intro q hq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hq ⊢
    obtain ⟨⟨⟨ha₁, ha₂⟩, ⟨hm₁, hm₂⟩⟩, he⟩ := hq
    refine ⟨⟨⟨ha₁, hm₁⟩, ⟨ha₂, hm₂⟩⟩, ?_⟩
    have h1 := natCast_ne_zero_of_lt (p := p) (by have := (Finset.mem_Ioc.mp ha₁).1; omega)
      (by have := (Finset.mem_Ioc.mp ha₁).2; omega)
    have h2 := natCast_ne_zero_of_lt (p := p) (by have := (Finset.mem_Ioc.mp ha₂).1; omega)
      (by have := (Finset.mem_Ioc.mp ha₂).2; omega)
    simp only [boxPoint]
    push_cast at he
    field_simp
    linear_combination he
  · intro qq _; rfl
  · intro q _; rfl

end Burgess

end GaloisForLFunctions.ArithmeticEffectivityTheory
