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
* **Burgess's bound** (`abs_burgessS_le`): for `r ≥ 2`,
  `|S(M, N)| ≤ K_r N^{1−1/r} p^{(r+1)/(4r²)} (1 + log p)`, by strong induction on `N`. Short sums
  are trivial (`trivial_range`), long ones are Pólya–Vinogradov (`long_range`); in between
  `B = ⌊p^{1/(2r)}⌋`, `A = ⌊N/(32B)⌋`, the shifts cost sums of length `≤ N/16` (induction) and the
  averaged sum is the Burgess inequality (`abs_burgessSum_le_main`).

The only inputs are counts: the Weil bound on the curves `y² = Π(x + bᵢ)` (Stepanov, Gauss sums,
descent), the multiplicative energy of the box, and completion.
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
    have h1 := natCast_ne_zero_of_lt (p := p) (a := qq.1.1)
      (by have := (Finset.mem_Ioc.mp ha₁).1; omega) (by have := (Finset.mem_Ioc.mp ha₁).2; omega)
    have h2 := natCast_ne_zero_of_lt (p := p) (a := qq.2.1)
      (by have := (Finset.mem_Ioc.mp ha₂).1; omega) (by have := (Finset.mem_Ioc.mp ha₂).2; omega)
    simp only [boxPoint] at he
    push_cast
    field_simp at he
    push_cast at he ⊢
    linear_combination he
  · intro q hq
    simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_product] at hq ⊢
    obtain ⟨⟨⟨ha₁, ha₂⟩, ⟨hm₁, hm₂⟩⟩, he⟩ := hq
    refine ⟨⟨⟨ha₁, hm₁⟩, ⟨ha₂, hm₂⟩⟩, ?_⟩
    have h1 := natCast_ne_zero_of_lt (p := p) (a := q.1.1)
      (by have := (Finset.mem_Ioc.mp ha₁).1; omega) (by have := (Finset.mem_Ioc.mp ha₁).2; omega)
    have h2 := natCast_ne_zero_of_lt (p := p) (a := q.1.2)
      (by have := (Finset.mem_Ioc.mp ha₂).1; omega) (by have := (Finset.mem_Ioc.mp ha₂).2; omega)
    simp only [boxPoint]
    push_cast at he
    field_simp
    push_cast at he ⊢
    linear_combination he
  · intro qq _; rfl
  · intro q _; rfl

/-- **The Burgess inequality**: for `A, N ≥ 1`, `4AN ≤ p`, `B ≤ p`,
`|Σ_{a ∈ (A,2A], b < B} S(M + ab, N)|^{2r} ≤ (AN)^{2r−2} · E · (r^{2r} B^r p + 6r B^{2r} √p)`. -/
theorem abs_burgessSum_pow_le (hF : ringChar (ZMod p) ≠ 2) {A B N r : ℕ} (hA : 1 ≤ A) (hN : 1 ≤ N)
    (hAN : 4 * A * N ≤ p) (hB : B ≤ p) (hr : 1 ≤ r) (M : ℤ) :
    |∑ a ∈ Ioc A (2 * A), ∑ b ∈ range B, burgessS p (M + (a * b : ℕ)) N| ^ (2 * r) ≤
      ((A * N : ℕ) : ℝ) ^ (2 * r - 2) * burgessEnergy p A N M *
        (r ^ (2 * r) * B ^ r * p + 6 * r * B ^ (2 * r) * Real.sqrt p) := by
  set X := (Ioc A (2 * A)) ×ˢ (range N)
  set T := shiftSum (shiftSet p B)
  have hAp : 2 * A < p := by nlinarith
  have hexp : ∑ a ∈ Ioc A (2 * A), ∑ b ∈ range B, burgessS p (M + (a * b : ℕ)) N =
      ∑ q ∈ X, chiR (q.1 : ZMod p) * T (boxPoint p M q) := by
    rw [Finset.sum_product]
    refine Finset.sum_congr rfl fun a ha => ?_
    have ha' := Finset.mem_Ioc.mp ha
    simp only [burgessS]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun m _ => ?_
    exact sum_shift_eq hB M (by omega) (by omega)
  have habs : |∑ q ∈ X, chiR (q.1 : ZMod p) * T (boxPoint p M q)| ≤ ∑ q ∈ X, |T (boxPoint p M q)| := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun q _ => ?_)
    rw [abs_mul]
    exact mul_le_of_le_one_left (abs_nonneg _) (abs_chiR_le _)
  set ν : ZMod p → ℝ := fun x => ((X.filter fun q => boxPoint p M q = x).card : ℝ)
  have hfib : ∑ q ∈ X, |T (boxPoint p M q)| = ∑ x : ZMod p, ν x * |T x| := by
    rw [← Finset.sum_fiberwise_of_maps_to (g := boxPoint p M) (t := univ) (fun _ _ => mem_univ _)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [Finset.sum_congr rfl fun q hq => by rw [(Finset.mem_filter.mp hq).2], Finset.sum_const,
      nsmul_eq_mul]
  have hholder := pow_sum_le_holder univ ν (fun x => |T x|) (fun x _ => Nat.cast_nonneg _)
    (fun x _ => abs_nonneg _) hr
  have hν : ∑ x : ZMod p, ν x = ((A * N : ℕ) : ℝ) := by
    simp only [ν]
    rw [← Nat.cast_sum, ← Finset.card_eq_sum_card_fiberwise (fun _ _ => mem_univ _),
      Finset.card_product, Nat.card_Ioc, Finset.card_range, show 2 * A - A = A by omega]
  have hν2 : ∑ x : ZMod p, ν x ^ 2 = burgessEnergy p A N M := sum_sq_fiber_eq_energy hAp M
  have hmom : ∑ x : ZMod p, |T x| ^ (2 * r) ≤
      r ^ (2 * r) * B ^ r * p + 6 * r * B ^ (2 * r) * Real.sqrt p := by
    have h := sum_pow_two_mul_le hF (shiftSet p B) r
    rw [card_shiftSet hB, ZMod.card] at h
    refine le_trans (le_of_eq ?_) h
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [pow_abs, abs_of_nonneg (by rw [pow_mul]; positivity)]
  rw [hexp]
  calc |∑ q ∈ X, chiR (q.1 : ZMod p) * T (boxPoint p M q)| ^ (2 * r)
      ≤ (∑ q ∈ X, |T (boxPoint p M q)|) ^ (2 * r) := pow_le_pow_left₀ (abs_nonneg _) habs _
    _ = (∑ x : ZMod p, ν x * |T x|) ^ (2 * r) := by rw [hfib]
    _ ≤ (∑ x : ZMod p, ν x) ^ (2 * r - 2) * (∑ x : ZMod p, ν x ^ 2) *
          ∑ x : ZMod p, |T x| ^ (2 * r) := hholder
    _ ≤ _ := by
        rw [hν, hν2]
        exact mul_le_mul_of_nonneg_left hmom (by positivity)

/-! ### Shifts and the Pólya–Vinogradov range -/

/-- `S(M, N) + S(M + N, h) = S(M, h) + S(M + h, N)`: both are `S(M, N + h)`. -/
theorem burgessS_shift (M : ℤ) (N h : ℕ) :
    burgessS p M N = burgessS p (M + h) N + (burgessS p M h - burgessS p (M + N) h) := by
  have h1 : burgessS p M (N + h) = burgessS p M N + burgessS p (M + N) h := by
    simp only [burgessS]
    rw [Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast; ring_nf
  have h2 : burgessS p M (h + N) = burgessS p M h + burgessS p (M + h) N := by
    simp only [burgessS]
    rw [Finset.sum_range_add]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    push_cast; ring_nf
  rw [add_comm h N] at h2
  linarith

/-- The real character is periodic. -/
theorem burgessS_emod (M : ℤ) (N : ℕ) : burgessS p M N = burgessS p (M % p) N := by
  simp only [burgessS]
  refine Finset.sum_congr rfl fun k _ => ?_
  congr 1
  simp [ZMod.intCast_mod]

theorem chiC_ne_one (hp2 : p ≠ 2) : RHTower.Hyperelliptic.chiC (ZMod p) ≠ 1 := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  obtain ⟨c, hc⟩ := FiniteField.exists_nonsquare hF
  have hc0 : c ≠ 0 := fun h => hc (h ▸ ⟨0, by simp⟩)
  intro h
  have h1 : RHTower.Hyperelliptic.chiC (ZMod p) c = 1 := by
    rw [h]; exact MulChar.one_apply (isUnit_iff_ne_zero.mpr hc0)
  have h2 : RHTower.Hyperelliptic.chiC (ZMod p) c = ((chiR c : ℝ) : ℂ) := by
    rw [RHTower.Hyperelliptic.chiC_apply, chiR]; push_cast; rfl
  rw [h2, chiR_eq_neg_one hc] at h1
  norm_num at h1

/-- **Pólya–Vinogradov for `S`**: `|S(M, N)| ≤ 2√p (1 + log p)`. -/
theorem abs_burgessS_le_polyaVinogradov (hp2 : p ≠ 2) (M : ℤ) (N : ℕ) :
    |burgessS p M N| ≤ 2 * (Real.sqrt p * (1 + Real.log p)) := by
  rw [burgessS_emod]
  set M' := M % p
  have hM' : 0 ≤ M' := Int.emod_nonneg _ (by exact_mod_cast hp.out.ne_zero)
  obtain ⟨t, ht⟩ : ∃ t : ℕ, M' = t := ⟨M'.toNat, (Int.toNat_of_nonneg hM').symm⟩
  have hPV : ∀ n : ℕ, |∑ k ∈ range n, chiR ((k : ℕ) : ZMod p)| ≤ Real.sqrt p * (1 + Real.log p) := by
    intro n
    have h := norm_sum_range_le_polyaVinogradov (chiC_ne_one hp2) n
    have e : (∑ k ∈ range n, RHTower.Hyperelliptic.chiC (ZMod p) (k : ZMod p)) =
        ((∑ k ∈ range n, chiR ((k : ℕ) : ZMod p) : ℝ) : ℂ) := by
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [RHTower.Hyperelliptic.chiC_apply, chiR]
      push_cast; rfl
    rwa [e, Complex.norm_real, Real.norm_eq_abs] at h
  have hsplit : burgessS p M' N = ∑ k ∈ range (t + N), chiR ((k : ℕ) : ZMod p) -
      ∑ k ∈ range t, chiR ((k : ℕ) : ZMod p) := by
    rw [Finset.sum_range_add, add_sub_cancel_left, burgessS]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [ht]; push_cast; rfl
  rw [hsplit]
  calc |∑ k ∈ range (t + N), chiR ((k : ℕ) : ZMod p) - ∑ k ∈ range t, chiR ((k : ℕ) : ZMod p)|
      ≤ |∑ k ∈ range (t + N), chiR ((k : ℕ) : ZMod p)| + |∑ k ∈ range t, chiR ((k : ℕ) : ZMod p)| :=
        abs_sub _ _
    _ ≤ _ := by linarith [hPV (t + N), hPV t]

theorem abs_burgessS_le_length (M : ℤ) (N : ℕ) : |burgessS p M N| ≤ N := by
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc ∑ k ∈ range N, |chiR (((M + k : ℤ)) : ZMod p)| ≤ ∑ _k ∈ range N, (1 : ℝ) :=
        Finset.sum_le_sum fun k _ => abs_chiR_le _
    _ = N := by simp

/-! ### Exponent bookkeeping -/

omit hp in
theorem sqrtRoot_pow {r : ℕ} (hr : 1 ≤ r) (x : ℝ) (hx : 0 ≤ x) :
    (x ^ ((1 : ℝ) / (2 * r))) ^ r = Real.sqrt x := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, Real.sqrt_eq_rpow]
  congr 1
  have : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  field_simp

omit hp in
theorem burgessExp_pow {r : ℕ} (hr : 1 ≤ r) (x : ℝ) (hx : 0 < x) :
    (x ^ (((r : ℝ) + 1) / (4 * (r : ℝ) ^ 2))) ^ (2 * r) =
      Real.sqrt x * x ^ ((1 : ℝ) / (2 * r)) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le, Real.sqrt_eq_rpow, ← Real.rpow_add hx]
  congr 1
  have : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  push_cast
  field_simp
  ring

omit hp in
theorem theta_pow {r : ℕ} (hr : 1 ≤ r) (x : ℝ) (hx : 0 ≤ x) :
    (x ^ (1 - 1 / (r : ℝ))) ^ (2 * r) = x ^ (2 * r - 2) := by
  rw [← Real.rpow_natCast, ← Real.rpow_mul hx, ← Real.rpow_natCast]
  congr 1
  have : (r : ℝ) ≠ 0 := by exact_mod_cast (by omega : r ≠ 0)
  rw [Nat.cast_sub (by omega)]
  push_cast
  field_simp

omit hp in
/-- **Short sums are trivially small**: `N ≤ 64 B₀` (`B₀ = p^{1/(2r)}`) gives
`N ≤ 64 N^{1−1/r} p^{(r+1)/(4r²)}`. -/
theorem trivial_range {r : ℕ} (hr : 2 ≤ r) {x : ℝ} (hx : 1 ≤ x) {N : ℝ} (hN0 : 0 ≤ N)
    (hN : N ≤ 64 * x ^ ((1 : ℝ) / (2 * r))) :
    N ≤ 64 * N ^ (1 - 1 / (r : ℝ)) * x ^ (((r : ℝ) + 1) / (4 * (r : ℝ) ^ 2)) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast (by omega : 0 < r)
  rcases hN0.lt_or_eq with hNp | rfl
  · have hsplit : N = N ^ (1 - 1 / (r : ℝ)) * N ^ (1 / (r : ℝ)) := by
      rw [← Real.rpow_add hNp]; norm_num
    have h1 : N ^ (1 / (r : ℝ)) ≤ (64 * x ^ ((1 : ℝ) / (2 * r))) ^ (1 / (r : ℝ)) :=
      Real.rpow_le_rpow hN0 hN (by positivity)
    have h2 : (64 * x ^ ((1 : ℝ) / (2 * r))) ^ (1 / (r : ℝ)) =
        (64 : ℝ) ^ (1 / (r : ℝ)) * x ^ ((1 : ℝ) / (2 * r) * (1 / r)) := by
      rw [Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (by linarith)]
    have h3 : (64 : ℝ) ^ (1 / (r : ℝ)) ≤ 64 := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 64)
        (show 1 / (r : ℝ) ≤ 1 by rw [div_le_one hr0]; exact_mod_cast (by omega : 1 ≤ r))
      simpa using this
    have h4 : x ^ ((1 : ℝ) / (2 * r) * (1 / r)) ≤ x ^ (((r : ℝ) + 1) / (4 * (r : ℝ) ^ 2)) := by
      refine Real.rpow_le_rpow_of_exponent_le hx ?_
      rw [show (1 : ℝ) / (2 * r) * (1 / r) = 2 / (4 * r ^ 2) by field_simp; ring]
      refine div_le_div_of_nonneg_right ?_ (by positivity)
      have : (2 : ℝ) ≤ r := by exact_mod_cast hr
      linarith
    have hθ : 0 ≤ N ^ (1 - 1 / (r : ℝ)) := Real.rpow_nonneg hN0 _
    calc N = N ^ (1 - 1 / (r : ℝ)) * N ^ (1 / (r : ℝ)) := hsplit
      _ ≤ N ^ (1 - 1 / (r : ℝ)) * (64 * x ^ (((r : ℝ) + 1) / (4 * (r : ℝ) ^ 2))) := by
          refine mul_le_mul_of_nonneg_left (h1.trans ?_) hθ
          rw [h2]
          exact mul_le_mul h3 h4 (by positivity) (by norm_num)
      _ = _ := by ring
  · positivity

omit hp in
/-- **Long sums: Pólya–Vinogradov suffices**: if `B₀ x ≤ N²` then `√x ≤ N^{1−1/r} x^{(r+1)/(4r²)}`. -/
theorem long_range {r : ℕ} (hr : 2 ≤ r) {x : ℝ} (hx : 1 ≤ x) {N : ℝ} (hN0 : 0 ≤ N)
    (hN : x ^ ((1 : ℝ) / (2 * r)) * x ≤ N ^ 2) :
    Real.sqrt x ≤ N ^ (1 - 1 / (r : ℝ)) * x ^ (((r : ℝ) + 1) / (4 * (r : ℝ) ^ 2)) := by
  have hr1 : 1 ≤ r := by omega
  have hx0 : 0 < x := by linarith
  set B₀ := x ^ ((1 : ℝ) / (2 * r))
  have hB₀ : 0 ≤ B₀ := Real.rpow_nonneg hx0.le _
  refine (pow_le_pow_iff_left₀ (Real.sqrt_nonneg x) (by positivity) (by omega : 2 * r ≠ 0)).mp ?_
  rw [mul_pow, theta_pow hr1 N hN0, burgessExp_pow hr1 x hx0]
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 1 := ⟨r - 1, by omega⟩
  have hB₀r : B₀ ^ (s + 1) = Real.sqrt x := sqrtRoot_pow hr1 x hx0.le
  have hsq : Real.sqrt x ^ 2 = x := Real.sq_sqrt hx0.le
  have hN2 : (B₀ * x) ^ s ≤ (N ^ 2) ^ s := pow_le_pow_left₀ (by positivity) hN s
  calc Real.sqrt x ^ (2 * (s + 1)) = x ^ (s + 1) := by rw [pow_mul, hsq]
    _ = (B₀ * x) ^ s * (Real.sqrt x * B₀) := by
        have e : (B₀ * x) ^ s * (Real.sqrt x * B₀) = B₀ ^ (s + 1) * Real.sqrt x * x ^ s := by ring
        rw [e, hB₀r, ← sq, hsq, pow_succ']
    _ ≤ (N ^ 2) ^ s * (Real.sqrt x * B₀) :=
        mul_le_mul_of_nonneg_right hN2 (by positivity)
    _ = N ^ (2 * (s + 1) - 2) * (Real.sqrt x * B₀) := by
        rw [← pow_mul]; congr 2

/-- The constant of the main term, `C' = 576 · 2^r (r^{2r} + 6r)`. -/
noncomputable def burgessMainConst (r : ℕ) : ℝ := 576 * 2 ^ r * ((r : ℝ) ^ (2 * r) + 6 * r)

theorem one_le_burgessMainConst {r : ℕ} (hr : 1 ≤ r) : 1 ≤ burgessMainConst r := by
  unfold burgessMainConst
  have h1 : (1 : ℝ) ≤ 2 ^ r := one_le_pow₀ (by norm_num)
  have h2 : (1 : ℝ) ≤ (r : ℝ) ^ (2 * r) + 6 * r := by
    have : (1 : ℝ) ≤ r := by exact_mod_cast hr
    nlinarith [pow_nonneg (show (0 : ℝ) ≤ r by positivity) (2 * r)]
  nlinarith

/-- **The main term**: with `B ≤ B₀ ≤ 2B` (`B₀ = p^{1/(2r)}`), `N ≤ 64 B₀ A`, `A ≤ N`, `4AN ≤ p`,
`|Σ_{a,b} S(M + ab, N)| ≤ C' · AB · N^{1−1/r} p^{(r+1)/(4r²)} (1 + log p)`. -/
theorem abs_burgessSum_le_main (hp2 : p ≠ 2) {r A B N : ℕ} (hr : 2 ≤ r) (hA : 1 ≤ A) (hB : 1 ≤ B)
    (hN : 1 ≤ N) (hAN : 4 * A * N ≤ p) (hAleN : A ≤ N)
    (hBB₀ : (B : ℝ) ≤ (p : ℝ) ^ ((1 : ℝ) / (2 * r)))
    (hB₀B : (p : ℝ) ^ ((1 : ℝ) / (2 * r)) ≤ 2 * B)
    (hNA : (N : ℝ) ≤ 64 * (p : ℝ) ^ ((1 : ℝ) / (2 * r)) * A) (M : ℤ) :
    |∑ a ∈ Ioc A (2 * A), ∑ b ∈ range B, burgessS p (M + (a * b : ℕ)) N| ≤
      burgessMainConst r * (A * B) * (N : ℝ) ^ (1 - 1 / (r : ℝ)) *
        (p : ℝ) ^ (((r : ℝ) + 1) / (4 * (r : ℝ) ^ 2)) * (1 + Real.log p) := by
  have hF : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have hr1 : 1 ≤ r := by omega
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  set B₀ := (p : ℝ) ^ ((1 : ℝ) / (2 * r))
  set L := 1 + Real.log p
  set C' := burgessMainConst r
  set E := (burgessEnergy p A N M : ℝ)
  have hL : 1 ≤ L := by have := Real.log_nonneg hp1; linarith
  have hB₀r : B₀ ^ r = Real.sqrt p := sqrtRoot_pow hr1 p hp0.le
  have hBp : B ≤ p := by
    have : B₀ ≤ p := by
      calc B₀ ≤ (p : ℝ) ^ (1 : ℝ) := Real.rpow_le_rpow_of_exponent_le hp1 (by
            rw [div_le_one (by positivity)]
            have : (1 : ℝ) ≤ r := by exact_mod_cast hr1
            linarith)
        _ = p := Real.rpow_one _
    exact_mod_cast hBB₀.trans this
  have hV := abs_burgessSum_pow_le hF hA hN hAN hBp hr1 M
  -- the energy and the moment
  have hE : E ≤ 9 * A * N * L := by
    have h := burgessEnergy_le hA hAN M
    have h2A : (2 * A : ℝ) ≤ p := by
      have : 2 * A ≤ p := by nlinarith
      exact_mod_cast this
    have hlog : Real.log (2 * A) ≤ Real.log p :=
      Real.log_le_log (by positivity) h2A
    have hAA : (A : ℝ) ^ 2 ≤ A * N := by
      rw [sq]; exact mul_le_mul_of_nonneg_left (by exact_mod_cast hAleN) (by positivity)
    have hANp : (0 : ℝ) ≤ A * N := by positivity
    nlinarith
  have hBr : (B : ℝ) ^ r ≤ Real.sqrt p := by
    rw [← hB₀r]; exact pow_le_pow_left₀ (by positivity) hBB₀ r
  have hmom : (r : ℝ) ^ (2 * r) * B ^ r * p + 6 * r * B ^ (2 * r) * Real.sqrt p ≤
      ((r : ℝ) ^ (2 * r) + 6 * r) * B ^ r * p := by
    have : (B : ℝ) ^ (2 * r) * Real.sqrt p ≤ B ^ r * p := by
      have hsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
      calc (B : ℝ) ^ (2 * r) * Real.sqrt p = B ^ r * (B ^ r * Real.sqrt p) := by ring
        _ ≤ B ^ r * (Real.sqrt p * Real.sqrt p) := by
            refine mul_le_mul_of_nonneg_left ?_ (by positivity)
            exact mul_le_mul_of_nonneg_right hBr (Real.sqrt_nonneg _)
        _ = B ^ r * p := by rw [hsq]
    nlinarith [this, show (0 : ℝ) ≤ r by positivity]
  -- the target, raised to the power `2r`
  have hθ := theta_pow hr1 (N : ℝ) (Nat.cast_nonneg N)
  have hP : ((p : ℝ) ^ (((r : ℝ) + 1) / (4 * (r : ℝ) ^ 2))) ^ (2 * r) = Real.sqrt p * B₀ :=
    burgessExp_pow hr1 (p : ℝ) hp0
  have hC'1 := one_le_burgessMainConst hr1
  refine (pow_le_pow_iff_left₀ (abs_nonneg _) (by positivity) (by omega : 2 * r ≠ 0)).mp ?_
  refine hV.trans ?_
  have hpB : (p : ℝ) ≤ Real.sqrt p * (2 ^ r * B ^ r) := by
    have hsq : Real.sqrt p * Real.sqrt p = p := Real.mul_self_sqrt hp0.le
    have : Real.sqrt p ≤ 2 ^ r * B ^ r := by
      rw [← hB₀r, ← mul_pow]; exact pow_le_pow_left₀ (by positivity) hB₀B r
    nlinarith [Real.sqrt_nonneg p]
  have hkey : 9 * ((r : ℝ) ^ (2 * r) + 6 * r) * L * N * p ≤
      C' ^ (2 * r) * A * B ^ r * Real.sqrt p * B₀ * L ^ (2 * r) := by
    have hC'L : C' * L ≤ C' ^ (2 * r) * L ^ (2 * r) := by
      have h1 : C' ≤ C' ^ (2 * r) := le_self_pow₀ hC'1 (by omega)
      have h2 : L ≤ L ^ (2 * r) := le_self_pow₀ hL (by omega)
      exact mul_le_mul h1 h2 (by linarith) (by positivity)
    have hCr : (0 : ℝ) ≤ (r : ℝ) ^ (2 * r) + 6 * r := by positivity
    calc 9 * ((r : ℝ) ^ (2 * r) + 6 * r) * L * N * p
        ≤ 9 * ((r : ℝ) ^ (2 * r) + 6 * r) * L * (64 * B₀ * A) * (Real.sqrt p * (2 ^ r * B ^ r)) := by
          refine mul_le_mul (mul_le_mul_of_nonneg_left hNA (by positivity)) hpB (by positivity)
            (by positivity)
      _ = (C' * L) * A * B ^ r * Real.sqrt p * B₀ := by
          simp only [C', burgessMainConst]; ring
      _ ≤ (C' ^ (2 * r) * L ^ (2 * r)) * A * B ^ r * Real.sqrt p * B₀ := by
          gcongr
      _ = _ := by ring
  obtain ⟨s, rfl⟩ : ∃ s, r = s + 2 := ⟨r - 2, by omega⟩
  rw [mul_pow, mul_pow, mul_pow, mul_pow, hθ, hP]
  have e1 : 2 * (s + 2) - 2 = 2 * s + 2 := by omega
  rw [e1]
  push_cast
  calc ((A : ℝ) * N) ^ (2 * s + 2) * E * (((s : ℝ) + 2) ^ (2 * (s + 2)) * B ^ (s + 2) * p +
        6 * ((s : ℝ) + 2) * B ^ (2 * (s + 2)) * Real.sqrt p)
      ≤ ((A : ℝ) * N) ^ (2 * s + 2) * (9 * A * N * L) *
          ((((s : ℝ) + 2) ^ (2 * (s + 2)) + 6 * ((s : ℝ) + 2)) * B ^ (s + 2) * p) := by
        have hmom' := hmom
        push_cast at hmom'
        exact mul_le_mul (mul_le_mul_of_nonneg_left hE (by positivity)) hmom' (by positivity)
          (by positivity)
    _ = ((A : ℝ) ^ (2 * s + 3) * (N : ℝ) ^ (2 * s + 2) * (B : ℝ) ^ (s + 2)) *
          (9 * (((s : ℝ) + 2) ^ (2 * (s + 2)) + 6 * ((s : ℝ) + 2)) * L * N * p) := by ring
    _ ≤ ((A : ℝ) ^ (2 * s + 3) * (N : ℝ) ^ (2 * s + 2) * (B : ℝ) ^ (s + 2)) *
          (C' ^ (2 * (s + 2)) * A * B ^ (s + 2) * Real.sqrt p * B₀ * L ^ (2 * (s + 2))) := by
        have hkey' := hkey
        push_cast at hkey'
        exact mul_le_mul_of_nonneg_left hkey' (by positivity)
    _ = _ := by ring

/-- Burgess's constant `K_r = 2C' + 64`. -/
noncomputable def burgessConst (r : ℕ) : ℝ := 2 * burgessMainConst r + 64

omit hp in
theorem four_le_sixteen_rpow {r : ℕ} (hr : 2 ≤ r) : (4 : ℝ) ≤ (16 : ℝ) ^ (1 - 1 / (r : ℝ)) := by
  have hr0 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have h1 : (1 : ℝ) / 2 ≤ 1 - 1 / (r : ℝ) := by
    have : 1 / (r : ℝ) ≤ 1 / 2 := one_div_le_one_div_of_le (by norm_num) hr0
    linarith
  calc (4 : ℝ) = (16 : ℝ) ^ ((1 : ℝ) / 2) := by
        rw [← Real.sqrt_eq_rpow, show (16 : ℝ) = 4 ^ 2 by norm_num, Real.sqrt_sq (by norm_num)]
    _ ≤ _ := Real.rpow_le_rpow_of_exponent_le (by norm_num) h1

/-- **Burgess's bound.** For an odd prime `p`, the quadratic character `χ` and `r ≥ 2`,

  `|Σ_{k<N} χ(M + k)| ≤ K_r N^{1−1/r} p^{(r+1)/(4r²)} (1 + log p)`

for every `M ∈ ℤ` and `N ∈ ℕ`, with `K_r` depending only on `r`. Strong induction on `N`: the
shifts `n ↦ n + ab` cost sums of length `ab ≤ N/16`, bounded by the induction hypothesis; the
averaged sum is the Burgess inequality, i.e. counting on the curves `y² = Π(x + bᵢ)`. -/
theorem abs_burgessS_le (hp2 : p ≠ 2) {r : ℕ} (hr : 2 ≤ r) (N : ℕ) (M : ℤ) :
    |burgessS p M N| ≤ burgessConst r * (N : ℝ) ^ (1 - 1 / (r : ℝ)) *
      (p : ℝ) ^ (((r : ℝ) + 1) / (4 * (r : ℝ) ^ 2)) * (1 + Real.log p) := by
  induction N using Nat.strong_induction_on generalizing M with
  | _ N ih =>
  have hr1 : 1 ≤ r := by omega
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
  have hp0 : (0 : ℝ) < p := by linarith
  set θ := 1 - 1 / (r : ℝ)
  set P := (p : ℝ) ^ (((r : ℝ) + 1) / (4 * (r : ℝ) ^ 2))
  set L := 1 + Real.log p
  set K := burgessConst r
  set C' := burgessMainConst r
  set B₀ := (p : ℝ) ^ ((1 : ℝ) / (2 * r))
  have hL : 1 ≤ L := by have := Real.log_nonneg hp1; linarith
  have hP0 : 0 ≤ P := Real.rpow_nonneg hp0.le _
  have hB₀1 : 1 ≤ B₀ := Real.one_le_rpow hp1 (by positivity)
  have hC'1 := one_le_burgessMainConst hr1
  have hK : K = 2 * C' + 64 := rfl
  have hNθ : 0 ≤ (N : ℝ) ^ θ := Real.rpow_nonneg (Nat.cast_nonneg N) _
  rcases le_or_gt (N : ℝ) (64 * B₀) with hsmall | hbig
  · -- short sums: the trivial bound
    have h := trivial_range hr hp1 (Nat.cast_nonneg N) hsmall
    calc |burgessS p M N| ≤ N := abs_burgessS_le_length M N
      _ ≤ 64 * (N : ℝ) ^ θ * P := h
      _ ≤ K * (N : ℝ) ^ θ * P * L := by
          have : 64 * (N : ℝ) ^ θ * P ≤ K * (N : ℝ) ^ θ * P := by
            refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right ?_ hNθ) hP0
            linarith
          nlinarith [mul_nonneg (mul_nonneg (show (0 : ℝ) ≤ K by linarith) hNθ) hP0]
  rcases lt_or_ge (4 * B₀ * p) ((N : ℝ) ^ 2) with hlong | hmid
  · -- long sums: Pólya–Vinogradov
    have h := long_range hr hp1 (Nat.cast_nonneg N) (by nlinarith)
    calc |burgessS p M N| ≤ 2 * (Real.sqrt p * L) := abs_burgessS_le_polyaVinogradov hp2 M N
      _ ≤ 2 * ((N : ℝ) ^ θ * P * L) := by gcongr
      _ ≤ K * (N : ℝ) ^ θ * P * L := by
          have h0 : 0 ≤ (N : ℝ) ^ θ * P * L := by positivity
          nlinarith
  -- the Burgess range
  set B := ⌊B₀⌋₊
  have hB1 : 1 ≤ B := Nat.le_floor (by exact_mod_cast hB₀1)
  have hBB₀ : (B : ℝ) ≤ B₀ := Nat.floor_le (by linarith)
  have hB₀B : B₀ ≤ 2 * B := by
    have := Nat.lt_floor_add_one B₀
    have : (1 : ℝ) ≤ B := by exact_mod_cast hB1
    linarith
  have hBpos : (0 : ℝ) < B := by exact_mod_cast hB1
  set x := (N : ℝ) / (32 * B)
  have hx2 : 2 ≤ x := by
    rw [le_div_iff₀ (by positivity)]; nlinarith
  set A := ⌊x⌋₊
  have hA1 : 1 ≤ A := Nat.le_floor (by norm_num; linarith)
  have hAx : (A : ℝ) ≤ x := Nat.floor_le (by linarith)
  have hxA : x ≤ 2 * A := by
    have := Nat.lt_floor_add_one x
    have : (1 : ℝ) ≤ A := by exact_mod_cast hA1
    linarith
  have hApos : (0 : ℝ) < A := by exact_mod_cast hA1
  have hN1 : 1 ≤ N := by
    have : (1 : ℝ) ≤ N := by nlinarith
    exact_mod_cast this
  have hNA : (N : ℝ) ≤ 64 * B₀ * A := by
    have : (N : ℝ) = 32 * B * x := by
      simp only [x]; field_simp
    rw [this]; nlinarith
  have hAleN : A ≤ N := by
    have : (A : ℝ) ≤ N := by
      refine hAx.trans ?_
      rw [div_le_iff₀ (by positivity)]
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    exact_mod_cast this
  have h4AN : 4 * A * N ≤ p := by
    have h1 : (4 * A * N : ℝ) ≤ 4 * x * N := by
      have := Nat.cast_nonneg (α := ℝ) N; nlinarith
    have h2 : 4 * x * N = (N : ℝ) ^ 2 / (8 * B) := by
      simp only [x]; field_simp; ring
    have h3 : (N : ℝ) ^ 2 / (8 * B) ≤ p := by
      rw [div_le_iff₀ (by positivity)]; nlinarith
    have : (4 * A * N : ℝ) ≤ p := by linarith
    exact_mod_cast this
  -- shifting by `ab`
  have hshift : (A * B : ℝ) * burgessS p M N =
      (∑ a ∈ Ioc A (2 * A), ∑ b ∈ range B, burgessS p (M + (a * b : ℕ)) N) +
        ∑ a ∈ Ioc A (2 * A), ∑ b ∈ range B,
          (burgessS p M (a * b) - burgessS p (M + N) (a * b)) := by
    rw [← Finset.sum_add_distrib]
    have hcard : ((Ioc A (2 * A)).card : ℝ) = A := by
      rw [Nat.card_Ioc, show 2 * A - A = A by omega]
    rw [show (A * B : ℝ) * burgessS p M N =
      ∑ a ∈ Ioc A (2 * A), ∑ b ∈ range B, burgessS p M N by
        rw [Finset.sum_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul, nsmul_eq_mul,
          hcard]; ring]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun b _ => ?_
    exact burgessS_shift M N (a * b)
  -- the error terms, by induction
  have herr : |∑ a ∈ Ioc A (2 * A), ∑ b ∈ range B,
      (burgessS p M (a * b) - burgessS p (M + N) (a * b))| ≤
      (A * B : ℝ) * (K / 2 * (N : ℝ) ^ θ * P * L) := by
    have hterm : ∀ a ∈ Ioc A (2 * A), ∀ b ∈ range B,
        |burgessS p M (a * b) - burgessS p (M + N) (a * b)| ≤ K / 2 * (N : ℝ) ^ θ * P * L := by
      intro a ha b hb
      obtain ⟨-, ha2⟩ := Finset.mem_Ioc.mp ha
      have hb' := Finset.mem_range.mp hb
      have hab : ((a * b : ℕ) : ℝ) ≤ N / 16 := by
        have : (a * b : ℝ) ≤ 2 * A * B := by
          have h1 : (a : ℝ) ≤ 2 * A := by exact_mod_cast ha2
          have h2 : (b : ℝ) ≤ B := by exact_mod_cast hb'.le
          nlinarith [Nat.cast_nonneg (α := ℝ) b]
        have h3 : 2 * (A : ℝ) * B ≤ N / 16 := by
          have : (2 * A * B : ℝ) ≤ 2 * x * B := by nlinarith
          have e : 2 * x * B = N / 16 := by simp only [x]; field_simp; ring
          linarith
        push_cast; linarith
      have habN : a * b < N := by
        have : ((a * b : ℕ) : ℝ) < N := by
          have : (N : ℝ) / 16 < N := by
            have : (0 : ℝ) < N := by exact_mod_cast hN1
            linarith
          linarith
        exact_mod_cast this
      have hθab : ((a * b : ℕ) : ℝ) ^ θ ≤ (N : ℝ) ^ θ / 4 := by
        have hθ0 : 0 ≤ θ := by
          have : 1 / (r : ℝ) ≤ 1 := by
            rw [div_le_one (by positivity)]; exact_mod_cast hr1
          simp only [θ]; linarith
        calc ((a * b : ℕ) : ℝ) ^ θ ≤ ((N : ℝ) / 16) ^ θ :=
              Real.rpow_le_rpow (Nat.cast_nonneg _) hab hθ0
          _ = (N : ℝ) ^ θ / (16 : ℝ) ^ θ :=
              Real.div_rpow (Nat.cast_nonneg _) (by norm_num) _
          _ ≤ (N : ℝ) ^ θ / 4 :=
              div_le_div_of_nonneg_left hNθ (by norm_num) (four_le_sixteen_rpow hr)
      have h1 := ih (a * b) habN M
      have h2 := ih (a * b) habN (M + N)
      have hK0 : 0 ≤ K := by linarith
      have hmono : K * ((a * b : ℕ) : ℝ) ^ θ * P * L ≤ K * ((N : ℝ) ^ θ / 4) * P * L := by
        gcongr
      calc |burgessS p M (a * b) - burgessS p (M + N) (a * b)|
          ≤ |burgessS p M (a * b)| + |burgessS p (M + N) (a * b)| := abs_sub _ _
        _ ≤ K * ((a * b : ℕ) : ℝ) ^ θ * P * L + K * ((a * b : ℕ) : ℝ) ^ θ * P * L :=
            add_le_add h1 h2
        _ ≤ K * ((N : ℝ) ^ θ / 4) * P * L + K * ((N : ℝ) ^ θ / 4) * P * L := add_le_add hmono hmono
        _ = K / 2 * (N : ℝ) ^ θ * P * L := by ring
    have hcard : ((Ioc A (2 * A)).card : ℝ) = A := by
      rw [Nat.card_Ioc, show 2 * A - A = A by omega]
    calc |∑ a ∈ Ioc A (2 * A), ∑ b ∈ range B,
          (burgessS p M (a * b) - burgessS p (M + N) (a * b))|
        ≤ ∑ a ∈ Ioc A (2 * A), ∑ b ∈ range B,
            |burgessS p M (a * b) - burgessS p (M + N) (a * b)| :=
          (Finset.abs_sum_le_sum_abs _ _).trans
            (Finset.sum_le_sum fun a _ => Finset.abs_sum_le_sum_abs _ _)
      _ ≤ ∑ _a ∈ Ioc A (2 * A), ∑ _b ∈ range B, K / 2 * (N : ℝ) ^ θ * P * L :=
          Finset.sum_le_sum fun a ha => Finset.sum_le_sum fun b hb => hterm a ha b hb
      _ = (A * B : ℝ) * (K / 2 * (N : ℝ) ^ θ * P * L) := by
          rw [Finset.sum_const, Finset.sum_const, Finset.card_range, nsmul_eq_mul, nsmul_eq_mul,
            hcard]
          ring
  have hmain := abs_burgessSum_le_main hp2 hr hA1 hB1 hN1 h4AN hAleN hBB₀ hB₀B hNA M
  have hAB : (0 : ℝ) < A * B := by positivity
  refine le_of_mul_le_mul_left ?_ hAB
  calc (A * B : ℝ) * |burgessS p M N| = |(A * B : ℝ) * burgessS p M N| := by
        rw [abs_mul, abs_of_pos hAB]
    _ ≤ |∑ a ∈ Ioc A (2 * A), ∑ b ∈ range B, burgessS p (M + (a * b : ℕ)) N| +
        |∑ a ∈ Ioc A (2 * A), ∑ b ∈ range B,
          (burgessS p M (a * b) - burgessS p (M + N) (a * b))| := by
        rw [hshift]; exact abs_add_le _ _
    _ ≤ C' * (A * B) * (N : ℝ) ^ θ * P * L + (A * B : ℝ) * (K / 2 * (N : ℝ) ^ θ * P * L) :=
        add_le_add hmain herr
    _ ≤ (A * B : ℝ) * (K * (N : ℝ) ^ θ * P * L) := by
        have h0 : 0 ≤ (A * B : ℝ) * ((N : ℝ) ^ θ * P * L) := by positivity
        have : C' ≤ K / 2 := by rw [hK]; linarith
        nlinarith

end Burgess

end GaloisForLFunctions.ArithmeticEffectivityTheory
