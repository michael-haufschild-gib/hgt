import Mathlib.Tactic

/-!
# Upper Poincaré coefficient fields grow polynomially on vertical tubes

An element of a quasianalytic coefficient field has a complete Laurent–Poincaré expansion at upper
infinity whose first monomial `c · s^{-ν}` has `c ≠ 0`.  On an upper vertical tube of fixed radius
the modulus of the translate `s = z + iS` is comparable to the height `S`, so the leading monomial
pins the modulus of the element between two constant multiples of `S^{-ν}`.  Both the element and
its reciprocal therefore have at most polynomial growth on upper vertical tubes — the property that
makes the Bezout survival estimate work.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter

/-- Two-sided comparison of integer powers of comparable positive reals. -/
theorem zpow_two_sided_of_comparable {t S : ℝ} (ht : 0 < t) (hS : 0 < S)
    (h1 : S / 2 ≤ t) (h2 : t ≤ 2 * S) (n : ℤ) :
    (2 : ℝ) ^ (-|n|) * S ^ n ≤ t ^ n ∧ t ^ n ≤ (2 : ℝ) ^ |n| * S ^ n := by
  have hbase : ∀ k : ℕ, ((2 : ℝ) ^ k)⁻¹ * S ^ k ≤ t ^ k ∧ t ^ k ≤ (2 : ℝ) ^ k * S ^ k := by
    intro k
    constructor
    · have hstep : (S / 2) ^ k ≤ t ^ k := pow_le_pow_left₀ (by positivity) h1 k
      calc ((2 : ℝ) ^ k)⁻¹ * S ^ k = (S / 2) ^ k := by
            rw [div_pow]
            ring
        _ ≤ t ^ k := hstep
    · calc t ^ k ≤ (2 * S) ^ k := pow_le_pow_left₀ ht.le h2 k
        _ = 2 ^ k * S ^ k := by rw [mul_pow]
  by_cases hn : 0 ≤ n
  · lift n to ℕ using hn with k
    have habs : |(k : ℤ)| = (k : ℤ) := abs_of_nonneg (by positivity)
    rw [habs]
    simp only [zpow_neg, zpow_natCast]
    exact hbase k
  · push_neg at hn
    obtain ⟨m, hm⟩ : ∃ m : ℕ, n = -(m : ℤ) := ⟨(-n).toNat, by omega⟩
    subst hm
    have habs : |(-(m : ℤ))| = (m : ℤ) := by
      rw [abs_neg]
      exact abs_of_nonneg (by positivity)
    rw [habs, zpow_neg, zpow_neg, zpow_neg, zpow_natCast, zpow_natCast, zpow_natCast]
    obtain ⟨hlo, hhi⟩ := hbase m
    have htk : (0 : ℝ) < t ^ m := by positivity
    have hSk : (0 : ℝ) < S ^ m := by positivity
    have h2k : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
    constructor
    · have hstep : (t ^ m)⁻¹ ≥ ((2 : ℝ) ^ m * S ^ m)⁻¹ := inv_anti₀ htk hhi
      calc ((2 : ℝ) ^ m)⁻¹ * (S ^ m)⁻¹ = ((2 : ℝ) ^ m * S ^ m)⁻¹ := by rw [mul_inv]
        _ ≤ (t ^ m)⁻¹ := hstep
    · have hstep : (t ^ m)⁻¹ ≤ (((2 : ℝ) ^ m)⁻¹ * S ^ m)⁻¹ := inv_anti₀ (by positivity) hlo
      calc (t ^ m)⁻¹ ≤ (((2 : ℝ) ^ m)⁻¹ * S ^ m)⁻¹ := hstep
        _ = (2 : ℝ) ^ m * (S ^ m)⁻¹ := by
            rw [mul_inv, inv_inv]

/-- **A nonzero leading Poincaré monomial.**  On every upper vertical tube the translate of `b`
agrees with `c · s^{-ν}` up to `O(S^{-ν-1})`, and the leading coefficient `c` is nonzero. -/
structure LeadingPoincareMonomial (b : ℂ → ℂ) (c : ℂ) (ν : ℤ) : Prop where
  /-- The first Laurent coefficient does not vanish. -/
  ne_zero : c ≠ 0
  /-- The first monomial approximates the translate to one further order. -/
  approx : ∀ Rad : ℝ, 0 < Rad → ∃ K S₀ : ℝ, 0 < S₀ ∧ ∀ S : ℝ, S₀ ≤ S → ∀ z : ℂ, ‖z‖ ≤ Rad →
    ‖b (z + (S : ℂ) * Complex.I) - c * (z + (S : ℂ) * Complex.I) ^ (-ν)‖
      ≤ K * S ^ (-(ν : ℝ) - 1)

/-- On an upper vertical tube of radius `Rad`, the modulus of the translate is comparable to the
height. -/
theorem norm_translate_comparable {Rad S : ℝ} (hRad : 0 < Rad) (hS : 2 * Rad ≤ S)
    {z : ℂ} (hz : ‖z‖ ≤ Rad) :
    0 < ‖z + (S : ℂ) * Complex.I‖ ∧ S / 2 ≤ ‖z + (S : ℂ) * Complex.I‖ ∧
      ‖z + (S : ℂ) * Complex.I‖ ≤ 2 * S := by
  have hSI : ‖(S : ℂ) * Complex.I‖ = S := by
    rw [norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (by linarith)]
  have hup : ‖z + (S : ℂ) * Complex.I‖ ≤ 2 * S := by
    calc ‖z + (S : ℂ) * Complex.I‖ ≤ ‖z‖ + ‖(S : ℂ) * Complex.I‖ := norm_add_le _ _
      _ ≤ Rad + S := by rw [hSI]; linarith
      _ ≤ 2 * S := by linarith
  have hlow : S / 2 ≤ ‖z + (S : ℂ) * Complex.I‖ := by
    have hns := norm_sub_norm_le ((S : ℂ) * Complex.I) (-z)
    have hrw : (S : ℂ) * Complex.I - -z = z + (S : ℂ) * Complex.I := by ring
    rw [hrw, hSI, norm_neg] at hns
    linarith
  refine ⟨by linarith, hlow, hup⟩

/-- **Polynomial growth of an element and of its reciprocal on upper vertical tubes.**  The leading
monomial pins the modulus between two constant multiples of `S^{-ν}`; both bounds are polynomial
because `|ν|` is finite. -/
theorem exists_tube_two_sided_polyGrowth {b : ℂ → ℂ} {c : ℂ} {ν : ℤ}
    (h : LeadingPoincareMonomial b c ν) {Rad : ℝ} (hRad : 0 < Rad) :
    ∃ (C₀ C₁ S₀ : ℝ), 0 < C₀ ∧ 0 < C₁ ∧ 0 < S₀ ∧ ∀ S : ℝ, S₀ ≤ S → ∀ z : ℂ, ‖z‖ ≤ Rad →
      ‖b (z + (S : ℂ) * Complex.I)‖ ≤ C₁ * S ^ (ν.natAbs) ∧
        (C₀ * S ^ (ν.natAbs))⁻¹ ≤ ‖b (z + (S : ℂ) * Complex.I)‖ := by
  obtain ⟨K, S₁, hS₁, hKapp⟩ := h.approx Rad hRad
  set A : ℝ := (2 : ℝ) ^ (ν.natAbs) with hAdef
  have hA1 : (1 : ℝ) ≤ A := one_le_pow₀ (by norm_num)
  have hA0 : (0 : ℝ) < A := by linarith
  have hc0 : 0 < ‖c‖ := norm_pos_iff.mpr h.ne_zero
  set K' : ℝ := max K 0 with hK'def
  have hK'0 : 0 ≤ K' := le_max_right _ _
  have hKK' : K ≤ K' := le_max_left _ _
  -- the height threshold
  set S₀ : ℝ := max (max S₁ (2 * Rad)) (max 1 (4 * A * K' / ‖c‖)) with hS₀def
  have hS₀pos : 0 < S₀ := lt_of_lt_of_le (by norm_num) (le_trans (le_max_left 1 _) (le_max_right _ _))
  refine ⟨2 * A / ‖c‖, ‖c‖ * A + K', S₀, by positivity, by positivity, hS₀pos, ?_⟩
  intro S hS z hz
  have hSS₁ : S₁ ≤ S := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hS
  have hSRad : 2 * Rad ≤ S := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hS
  have hS1 : (1 : ℝ) ≤ S := le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hS
  have hSK : 4 * A * K' / ‖c‖ ≤ S := le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hS
  have hS0 : (0 : ℝ) < S := by linarith
  obtain ⟨htpos, hlo, hhi⟩ := norm_translate_comparable hRad hSRad hz
  set t : ℝ := ‖z + (S : ℂ) * Complex.I‖ with htdef
  obtain ⟨hzlo, hzhi⟩ := zpow_two_sided_of_comparable htpos hS0 hlo hhi (-ν)
  have habs : |(-ν)| = (ν.natAbs : ℤ) := by
    rw [abs_neg]
    exact Int.abs_eq_natAbs ν
  rw [habs] at hzlo hzhi
  have hApow : (2 : ℝ) ^ ((ν.natAbs : ℤ)) = A := by
    rw [hAdef, zpow_natCast]
  rw [hApow] at hzhi
  have hApow' : (2 : ℝ) ^ (-(ν.natAbs : ℤ)) = A⁻¹ := by
    rw [zpow_neg, hApow]
  rw [hApow'] at hzlo
  -- the monomial term
  have hmono : ‖c * (z + (S : ℂ) * Complex.I) ^ (-ν)‖ = ‖c‖ * t ^ (-ν) := by
    rw [norm_mul, norm_zpow, htdef]
  have happ := hKapp S hSS₁ z hz
  -- the error term
  have herr : K * S ^ (-(ν : ℝ) - 1) ≤ K' * (S ^ (-ν) / S) := by
    have hsplit : S ^ (-(ν : ℝ) - 1) = S ^ (-ν) / S := by
      rw [← Real.rpow_intCast S (-ν)]
      push_cast
      rw [Real.rpow_sub hS0, Real.rpow_one]
    rw [hsplit]
    have hpos : (0 : ℝ) < S ^ (-ν) / S := by positivity
    exact mul_le_mul_of_nonneg_right hKK' hpos.le
  have hSzpos : (0 : ℝ) < S ^ (-ν) := by positivity
  constructor
  · -- upper bound
    have hSnat : S ^ (-ν) ≤ S ^ (ν.natAbs) := by
      have hle : (-ν) ≤ (ν.natAbs : ℤ) := by omega
      calc S ^ (-ν) ≤ S ^ ((ν.natAbs : ℤ)) := zpow_le_zpow_right₀ hS1 hle
        _ = S ^ (ν.natAbs) := by rw [zpow_natCast]
    have htri : ‖b (z + (S : ℂ) * Complex.I)‖
        ≤ ‖c‖ * t ^ (-ν) + K * S ^ (-(ν : ℝ) - 1) := by
      have hns := norm_sub_norm_le (b (z + (S : ℂ) * Complex.I))
        (c * (z + (S : ℂ) * Complex.I) ^ (-ν))
      rw [hmono] at hns
      linarith [happ, hns]
    have hterm1 : ‖c‖ * t ^ (-ν) ≤ ‖c‖ * (A * S ^ (-ν)) :=
      mul_le_mul_of_nonneg_left hzhi hc0.le
    have hterm2 : K' * (S ^ (-ν) / S) ≤ K' * S ^ (-ν) := by
      refine mul_le_mul_of_nonneg_left ?_ hK'0
      rw [div_le_iff₀ hS0]
      nlinarith [hSzpos, hS1]
    have hcomb : ‖b (z + (S : ℂ) * Complex.I)‖ ≤ (‖c‖ * A + K') * S ^ (-ν) := by
      nlinarith [htri, hterm1, hterm2, herr]
    calc ‖b (z + (S : ℂ) * Complex.I)‖ ≤ (‖c‖ * A + K') * S ^ (-ν) := hcomb
      _ ≤ (‖c‖ * A + K') * S ^ (ν.natAbs) := by
          refine mul_le_mul_of_nonneg_left hSnat (by positivity)
  · -- lower bound
    have hterm1 : ‖c‖ * (A⁻¹ * S ^ (-ν)) ≤ ‖c‖ * t ^ (-ν) :=
      mul_le_mul_of_nonneg_left hzlo hc0.le
    have htri : ‖c‖ * t ^ (-ν) - K * S ^ (-(ν : ℝ) - 1) ≤ ‖b (z + (S : ℂ) * Complex.I)‖ := by
      have hns := norm_sub_norm_le (c * (z + (S : ℂ) * Complex.I) ^ (-ν))
        (b (z + (S : ℂ) * Complex.I))
      rw [hmono, norm_sub_rev] at hns
      linarith [happ, hns]
    have hsmall : K' * (S ^ (-ν) / S) ≤ ‖c‖ / 2 * (A⁻¹ * S ^ (-ν)) := by
      have hstep : K' / S ≤ ‖c‖ / (4 * A) := by
        rw [div_le_div_iff₀ hS0 (by positivity)]
        rw [div_le_iff₀ hc0] at hSK
        nlinarith [hSK, hA0, hc0, hK'0, hS0]
      have hpos : (0 : ℝ) < S ^ (-ν) := hSzpos
      calc K' * (S ^ (-ν) / S) = (K' / S) * S ^ (-ν) := by ring
        _ ≤ (‖c‖ / (4 * A)) * S ^ (-ν) := mul_le_mul_of_nonneg_right hstep hpos.le
        _ ≤ ‖c‖ / 2 * (A⁻¹ * S ^ (-ν)) := by
            have hfac : ‖c‖ / (4 * A) ≤ ‖c‖ / 2 * A⁻¹ := by
              rw [div_le_iff₀ (by positivity : (0 : ℝ) < 4 * A)]
              have hAinv : A⁻¹ * A = 1 := inv_mul_cancel₀ (ne_of_gt hA0)
              nlinarith [hAinv, hc0, hA0]
            have hmul := mul_le_mul_of_nonneg_right hfac (le_of_lt hpos)
            linarith [hmul]
    have hfinal : ‖c‖ / 2 * (A⁻¹ * S ^ (-ν)) ≤ ‖b (z + (S : ℂ) * Complex.I)‖ := by
      linarith [htri, hterm1, herr, hsmall]
    have hSnat : (S ^ (ν.natAbs))⁻¹ ≤ S ^ (-ν) := by
      have hle : (-(ν.natAbs : ℤ)) ≤ (-ν) := by omega
      calc (S ^ (ν.natAbs))⁻¹ = S ^ (-(ν.natAbs : ℤ)) := by rw [zpow_neg, zpow_natCast]
        _ ≤ S ^ (-ν) := zpow_le_zpow_right₀ hS1 hle
    have hinv : (2 * A / ‖c‖ * S ^ (ν.natAbs))⁻¹ = ‖c‖ / 2 * (A⁻¹ * (S ^ (ν.natAbs))⁻¹) := by
      field_simp
    rw [hinv]
    have hmono2 : ‖c‖ / 2 * (A⁻¹ * (S ^ (ν.natAbs))⁻¹) ≤ ‖c‖ / 2 * (A⁻¹ * S ^ (-ν)) := by
      refine mul_le_mul_of_nonneg_left ?_ (by positivity)
      exact mul_le_mul_of_nonneg_left hSnat (by positivity)
    linarith [hmono2, hfinal]


/-- **Polynomial growth of a coefficient along the imaginary axis**, the form used by the Bezout
survival estimate. -/
theorem exists_axis_polyGrowth {b : ℂ → ℂ} {c : ℂ} {ν : ℤ} (h : LeadingPoincareMonomial b c ν) :
    ∃ (C S₀ : ℝ) (M : ℕ), 0 < C ∧ 0 < S₀ ∧
      ∀ S : ℝ, S₀ ≤ S → ‖b ((S : ℂ) * Complex.I)‖ ≤ C * S ^ M := by
  obtain ⟨C₀, C₁, S₀, hC₀, hC₁, hS₀, hmain⟩ :=
    exists_tube_two_sided_polyGrowth h (Rad := 1) one_pos
  refine ⟨C₁, S₀, ν.natAbs, hC₁, hS₀, fun S hS => ?_⟩
  have h0 := (hmain S hS 0 (by simp)).1
  rwa [zero_add] at h0

/-- **Polynomial growth of the reciprocal along the imaginary axis.** -/
theorem exists_axis_polyGrowth_inv {b : ℂ → ℂ} {c : ℂ} {ν : ℤ}
    (h : LeadingPoincareMonomial b c ν) :
    ∃ (C S₀ : ℝ) (M : ℕ), 0 < C ∧ 0 < S₀ ∧
      ∀ S : ℝ, S₀ ≤ S → ‖(b ((S : ℂ) * Complex.I))⁻¹‖ ≤ C * S ^ M := by
  obtain ⟨C₀, C₁, S₀, hC₀, hC₁, hS₀, hmain⟩ :=
    exists_tube_two_sided_polyGrowth h (Rad := 1) one_pos
  refine ⟨C₀, S₀, ν.natAbs, hC₀, hS₀, fun S hS => ?_⟩
  have h0 := (hmain S hS 0 (by simp)).2
  rw [zero_add] at h0
  have hS0 : (0 : ℝ) < S := by
    have : (0 : ℝ) < S₀ := hS₀
    linarith
  have hden : (0 : ℝ) < (C₀ * S ^ ν.natAbs)⁻¹ := by positivity
  have hbpos : (0 : ℝ) < ‖b ((S : ℂ) * Complex.I)‖ := lt_of_lt_of_le hden h0
  rw [norm_inv]
  have hkey : (‖b ((S : ℂ) * Complex.I)‖)⁻¹ ≤ ((C₀ * S ^ ν.natAbs)⁻¹)⁻¹ := inv_anti₀ hden h0
  rwa [inv_inv] at hkey

end GaloisForLFunctions.HTGeometry
