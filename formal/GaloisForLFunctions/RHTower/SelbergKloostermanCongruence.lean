import GaloisForLFunctions.RHTower.SelbergPoincareFourier
import GaloisForLFunctions.RHTower.KloostermanUniform

open Complex RHTower.Sieve

/-!
# Weil's bound for the Kloosterman sums of `Γ(N)`

`S_N(m, n; c) = Σ_{d mod |c|N, d ≡ 1 (N), (d, c) = 1} e((m d̄ + n d)/(cN))` (`ksum`). Detecting `d ≡ 1 (N)` by the
additive characters of `ZMod N` (`ite_eq_one`) and lifting them to `ZMod (|c|N)` (`stdAddChar_cast`) writes it as
`N^{-1} Σ_t e(-t/N) S(sgn(c) n + t|c|, sgn(c) m; |c|N)` with classical Kloosterman sums, so
`|S_N(m, n; c)| ≤ kmaxU(sgn(c) m; |c|N)` uniformly in `n` (`norm_ksum_le`).
-/

namespace GaloisForLFunctions.RHTower.SelbergKloostermanCongruence
open GaloisForLFunctions.RHTower.SelbergPoincareFourier GaloisForLFunctions.RHTower.KloostermanUniform

/-- Sum over `range K` of a function of residues, restricted to units, is the sum over units. -/
theorem sum_range_units (K : ℕ) [NeZero K] (f : ZMod K → ℂ) :
    ∑ r ∈ Finset.range K, (if IsUnit (r : ZMod K) then f r else 0) = ∑ x : (ZMod K)ˣ, f x := by
  classical
  rw [← Finset.sum_filter]
  refine Finset.sum_bij' (fun r hr => (Finset.mem_filter.mp hr).2.unit) (fun x _ => (x : ZMod K).val)
    (fun _ _ => Finset.mem_univ _) (fun x _ => ?_) (fun r hr => ?_) (fun x _ => ?_) (fun r hr => ?_)
  · refine Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (ZMod.val_lt _), ?_⟩
    rw [ZMod.natCast_zmod_val]; exact x.isUnit
  · have hr' := Finset.mem_range.mp (Finset.mem_filter.mp hr).1
    simp only [IsUnit.unit_spec, ZMod.val_natCast, Nat.mod_eq_of_lt hr']
  · ext; simp
  · simp only [IsUnit.unit_spec]

/-- Additive-character detection of `a = 1` in `ZMod N`. -/
theorem ite_eq_one (N : ℕ) [NeZero N] (a : ZMod N) :
    (if a = 1 then (1 : ℂ) else 0) = (N : ℂ)⁻¹ * ∑ t : ZMod N, ZMod.stdAddChar (t * (a - 1)) := by
  rw [AddChar.sum_mulShift (a - 1) (ZMod.isPrimitive_stdAddChar N), ZMod.card]
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  by_cases h : a = 1
  · simp [h, hN]
  · simp [h, sub_eq_zero]

variable (N : ℕ)

theorem adm_iff {c : ℤ} (hNc : (N : ℤ) ∣ c) (r : ℕ) :
    (c, (r : ℤ)) ∈ adm N ↔ ((r : ZMod N) = 1 ∧ IsUnit ((r : ZMod (c.natAbs * N)))) := by
  simp only [adm, Set.mem_setOf_eq, Int.cast_natCast]
  rw [ZMod.isUnit_iff_coprime, Nat.coprime_mul_iff_right, Int.isCoprime_iff_gcd_eq_one]
  have hg : c.gcd (r : ℤ) = Nat.gcd c.natAbs r := by simp [Int.gcd]
  rw [hg]
  constructor
  · rintro ⟨_, h1, h2⟩
    refine ⟨h1, Nat.Coprime.symm h2, ?_⟩
    rw [← ZMod.isUnit_iff_coprime, h1]; exact isUnit_one
  · rintro ⟨h1, h2, _⟩
    exact ⟨hNc, h1, Nat.Coprime.symm h2⟩

theorem natAbs_mul_cast (c : ℤ) : ((c.natAbs * N : ℕ) : ℂ) = (c.sign : ℂ) * c * N := by
  have h1 : ((c.natAbs : ℕ) : ℤ) = c.sign * c := (Int.sign_mul_self c).symm
  have h : ((c.natAbs : ℕ) : ℂ) = (c.sign : ℂ) * c := by rw [← Int.cast_natCast, h1]; push_cast; ring
  rw [Nat.cast_mul, h]

theorem sign_sq {c : ℤ} (hc : c ≠ 0) : (c.sign : ℂ) * c.sign = 1 := by
  rcases lt_or_gt_of_ne hc with h | h
  · simp [Int.sign_eq_neg_one_of_neg h]
  · simp [Int.sign_eq_one_of_pos h]

theorem kphase_eq (m : ℕ) [NeZero N] {c : ℤ} (hc : c ≠ 0) (n : ℤ) (r : ℕ) :
    haveI : NeZero (c.natAbs * N) := ⟨Nat.mul_ne_zero (Int.natAbs_ne_zero.mpr hc) (NeZero.ne N)⟩
    kphase N m n (c, r) = ZMod.stdAddChar (((c.sign * n : ℤ) : ZMod (c.natAbs * N)) * (r : ZMod (c.natAbs * N)) +
      ((c.sign * m : ℤ) : ZMod (c.natAbs * N)) * (r : ZMod (c.natAbs * N))⁻¹) := by
  haveI : NeZero (c.natAbs * N) := ⟨Nat.mul_ne_zero (Int.natAbs_ne_zero.mpr hc) (NeZero.ne N)⟩
  set K := c.natAbs * N
  set v := ((r : ZMod K)⁻¹).val
  have harg : ((c.sign * n : ℤ) : ZMod K) * (r : ZMod K) + ((c.sign * m : ℤ) : ZMod K) * (r : ZMod K)⁻¹ =
      ((c.sign * (n * r + m * v) : ℤ) : ZMod K) := by
    push_cast
    rw [show ((v : ℕ) : ZMod K) = (r : ZMod K)⁻¹ from ZMod.natCast_zmod_val _]
    ring
  rw [harg, ZMod.stdAddChar_coe]
  unfold kphase phase
  simp only [Int.cast_natCast]
  rw [← Complex.exp_add]
  congr 1
  have hcC : (c : ℂ) ≠ 0 := by exact_mod_cast hc
  have hNC : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hK : ((K : ℕ) : ℂ) = (c.sign : ℂ) * c * N := natAbs_mul_cast N c
  have hs := sign_sq hc
  have hsC : (c.sign : ℂ) ≠ 0 := by intro h; rw [h, zero_mul] at hs; exact zero_ne_one hs
  rw [hK]
  push_cast
  field_simp
  ring

theorem stdAddChar_cast {K : ℕ} [NeZero N] [NeZero K] (hNK : N ∣ K) (t : ZMod N) (r : ℕ) :
    ZMod.stdAddChar (t * (r : ZMod N)) =
      ZMod.stdAddChar ((((t.val * (K / N) : ℕ)) : ZMod K) * (r : ZMod K)) := by
  have h1 : t * (r : ZMod N) = (((t.val * r : ℕ) : ℤ) : ZMod N) := by
    push_cast; rw [ZMod.natCast_zmod_val]
  have h2 : (((t.val * (K / N) : ℕ)) : ZMod K) * (r : ZMod K) = (((t.val * (K / N) * r : ℕ) : ℤ) : ZMod K) := by
    rw [Int.cast_natCast, Nat.cast_mul (t.val * (K / N)) r]
  rw [h1, h2, ZMod.stdAddChar_coe, ZMod.stdAddChar_coe]
  congr 1
  obtain ⟨q, hq⟩ := hNK
  have hN : (N : ℂ) ≠ 0 := by exact_mod_cast NeZero.ne N
  have hq0 : q ≠ 0 := by rintro rfl; exact NeZero.ne K (by simpa using hq)
  have hKN : K / N = q := by rw [hq]; exact Nat.mul_div_cancel_left q (Nat.pos_of_ne_zero (NeZero.ne N))
  rw [hKN, hq]
  have hqC : (q : ℂ) ≠ 0 := by exact_mod_cast hq0
  push_cast
  field_simp

/-- **Weil bound for `Γ(N)` Kloosterman sums**: `|S_N(m, n; c)| ≤ kmaxU(sgn(c) m; |c|N)`, uniformly in `n`. -/
theorem norm_ksum_le (m : ℕ) [NeZero N] {c : ℤ} (hc : c ≠ 0) (n : ℤ) :
    ‖ksum N m c n‖ ≤ kmaxU (c.sign * m) (c.natAbs * N) := by
  haveI hK : NeZero (c.natAbs * N) := ⟨Nat.mul_ne_zero (Int.natAbs_ne_zero.mpr hc) (NeZero.ne N)⟩
  set K := c.natAbs * N
  by_cases hNc : (N : ℤ) ∣ c
  · have hNK : N ∣ K := Dvd.intro_left _ rfl
    set B : ZMod K := ((c.sign * m : ℤ) : ZMod K)
    set A : ZMod N → ZMod K := fun t => (((c.sign * n + (t.val * (K / N) : ℕ) : ℤ)) : ZMod K)
    have hterm : ∀ r ∈ Finset.range K, (adm N).indicator (kphase N m n) (c, (r : ℤ)) =
        (N : ℂ)⁻¹ * ∑ t : ZMod N, ZMod.stdAddChar (-t) *
          (if IsUnit (r : ZMod K) then ZMod.stdAddChar (A t * (r : ZMod K) + B * (r : ZMod K)⁻¹) else 0) := by
      intro r _
      by_cases hu : IsUnit (r : ZMod K)
      · simp only [if_pos hu]
        have hind : (adm N).indicator (kphase N m n) (c, (r : ℤ)) =
            (if (r : ZMod N) = 1 then (1 : ℂ) else 0) * kphase N m n (c, r) := by
          by_cases h1 : (r : ZMod N) = 1
          · rw [Set.indicator_of_mem ((adm_iff N hNc r).mpr ⟨h1, hu⟩), if_pos h1, one_mul]
          · rw [Set.indicator_of_notMem (fun h => h1 ((adm_iff N hNc r).mp h).1), if_neg h1, zero_mul]
        rw [hind, ite_eq_one, kphase_eq N m hc n r, mul_assoc, Finset.sum_mul]
        congr 1
        apply Finset.sum_congr rfl
        intro t _
        rw [mul_sub, mul_one, sub_eq_add_neg, AddChar.map_add_eq_mul, stdAddChar_cast N hNK, mul_comm (ZMod.stdAddChar _) (ZMod.stdAddChar (-t)), mul_assoc,
          ← AddChar.map_add_eq_mul]
        congr 2
        simp only [A, Int.cast_add, Int.cast_natCast]
        ring
      · simp only [if_neg hu, mul_zero, Finset.sum_const_zero]
        exact Set.indicator_of_notMem (fun h => hu ((adm_iff N hNc r).mp h).2) _
    have hks : ksum N m c n = (N : ℂ)⁻¹ * ∑ t : ZMod N, ZMod.stdAddChar (-t) * kloostermanSum K (A t) B := by
      unfold ksum
      rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum, Finset.sum_comm]
      congr 1
      apply Finset.sum_congr rfl
      intro t _
      rw [← Finset.mul_sum, sum_range_units K (fun a => ZMod.stdAddChar (A t * a + B * a⁻¹))]
      congr 1
      unfold kloostermanSum kloostermanPhase
      apply Finset.sum_congr rfl
      intro x _
      rw [ZMod.inv_coe_unit]
    rw [hks, norm_mul, norm_inv, Complex.norm_natCast]
    have hN : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero (NeZero.ne N)
    rw [inv_mul_le_iff₀ hN]
    refine (norm_sum_le _ _).trans ?_
    have hb : ∀ t : ZMod N, ‖ZMod.stdAddChar (-t) * kloostermanSum K (A t) B‖ ≤ kmaxU (c.sign * m) K := by
      intro t
      rw [norm_mul, AddChar.norm_apply, one_mul]
      exact norm_kloostermanSum_le_kmaxU _ _ K
    calc ∑ t : ZMod N, ‖ZMod.stdAddChar (-t) * kloostermanSum K (A t) B‖ ≤ ∑ _t : ZMod N, kmaxU (c.sign * m) K :=
          Finset.sum_le_sum (fun t _ => hb t)
      _ = N * kmaxU (c.sign * m) K := by rw [Finset.sum_const, Finset.card_univ, ZMod.card, nsmul_eq_mul]
  · have h0 : ksum N m c n = 0 := by
      unfold ksum
      exact Finset.sum_eq_zero (fun r _ => Set.indicator_of_notMem (fun h => hNc h.1) _)
    rw [h0, norm_zero]
    exact kmaxU_nonneg _ _

end GaloisForLFunctions.RHTower.SelbergKloostermanCongruence
