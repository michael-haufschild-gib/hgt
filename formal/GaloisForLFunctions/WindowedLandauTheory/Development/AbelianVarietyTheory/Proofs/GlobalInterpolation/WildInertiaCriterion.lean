import GaloisForLFunctions.WindowedLandauTheory.Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TameValueGroup

/-! If inertia has trivial ratios on all tame radicals of the residue prime,
then its ratio at every nonzero element reduces to one. -/

noncomputable section

open IsLocalRing WindowedLandauTheory.ConjugateSelfDual ReciprocityTheory.Gal

namespace GlobalTheory.TameKummer

variable {K : Type} [Field K] (A : ValuationSubring K) {p : ℕ} [Fact p.Prime]

private theorem valuation_sub_one_lt_of_primePow (hp : A.valuation (p : K) < 1)
    {z : K} (a : ℕ) (hz : A.valuation (z ^ (p ^ a) - 1) < 1) :
    A.valuation (z - 1) < 1 := by
  have hp₀ := (Fact.out : p.Prime).ne_zero
  have hzle : A.valuation z ≤ 1 := by
    have h : A.valuation (z ^ p ^ a) ≤ 1 := by
      have he : z ^ p ^ a = (z ^ p ^ a - 1) + 1 := (sub_add_cancel _ _).symm
      rw [he]
      exact (Valuation.map_add _ _ _).trans (max_le hz.le (by rw [map_one]))
    rw [map_pow] at h
    exact le_of_not_gt fun hh => (not_lt_of_ge h) (one_lt_pow₀ hh (pow_ne_zero _ hp₀))
  let y : A := ⟨z, (A.valuation_le_one_iff _).mp hzle⟩
  letI : CharP (ResidueField A) p := by
    rw [CharP.charP_iff_prime_eq_zero Fact.out, ← map_natCast (residue A),
      residue_eq_zero_iff, A.valuation_lt_one_iff]
    simpa using hp
  have h : residue A (y ^ p ^ a - 1) = 0 := by
    rw [residue_eq_zero_iff, A.valuation_lt_one_iff]
    simpa [y] using hz
  have hy : residue A (y - 1) = 0 := by
    apply (pow_eq_zero_iff (n := p ^ a) (pow_ne_zero _ hp₀)).mp
    rw [map_sub, map_one, sub_pow_char_pow, one_pow,
      ← map_pow, ← map_one (residue A), ← map_sub, h]
  rw [residue_eq_zero_iff, A.valuation_lt_one_iff] at hy
  exact hy

variable {E : Type} [Field E] [NumberField E] [Algebra E K]

private def unitRatio (σ : G E K) : Kˣ →* Kˣ :=
  Units.map (σ : K →* K) / MonoidHom.id Kˣ

omit [NumberField E] in
private theorem coe_unitRatio (σ : G E K) (x : Kˣ) :
    ((unitRatio σ x : Kˣ) : K) = σ x / x := by
  simp [unitRatio]

private theorem unitRatio_mem_of_val_eq_one {σ : G E K} (hσ : σ ∈ Ine (F := E) A)
    {x : Kˣ} (hx : A.valuation (x : K) = 1) :
    unitRatio σ x ∈ A.principalUnitGroup := by
  rw [ValuationSubring.mem_principalUnitGroup_iff, coe_unitRatio,
    div_sub_one x.ne_zero, map_div₀, hx, div_one]
  exact hσ.2 _ hx.le

private theorem unitRatio_mem_of_val_eq_zpow {σ : G E K} (hσ : σ ∈ Ine (F := E) A)
    {x r : Kˣ} {k : ℤ} (hr : unitRatio σ r ∈ A.principalUnitGroup)
    (h : A.valuation (x : K) = A.valuation (r : K) ^ k) :
    unitRatio σ x ∈ A.principalUnitGroup := by
  have he : x = (x / r ^ k) * r ^ k := (div_mul_cancel _ _).symm
  rw [he, map_mul, map_zpow]
  refine mul_mem (unitRatio_mem_of_val_eq_one A hσ ?_) (zpow_mem hr k)
  have hrne : A.valuation (r : K) ^ k ≠ 0 := zpow_ne_zero _ (by simp)
  simp [h, hrne]

/-- It suffices to test wild inertia on radicals of degrees `p^d - 1`. -/
theorem valuation_sub_one_lt_of_trivial_tame [CharZero K] [Algebra.IsAlgebraic ℚ K]
    (hp : A.valuation (p : K) < 1) {σ : G E K} (hσ : σ ∈ Ine (F := E) A)
    (hroot : ∀ d, 0 < d → ∃ r : K, r ^ (p ^ d - 1) = (p : K) ∧
      A.valuation (σ r / r - 1) < 1) :
    ∀ y : K, y ≠ 0 → A.valuation (σ y / y - 1) < 1 := by
  intro y hy
  have hp' : p.Prime := Fact.out
  have hyalg : IsAlgebraic ℤ y := (IsFractionRing.isAlgebraic_iff ℤ ℚ K).mpr
    (Algebra.IsAlgebraic.isAlgebraic y)
  obtain ⟨m, k, hm, hv⟩ := exists_pow_valuation_eq_zpow A hp hy hyalg
  obtain ⟨a, b, hb, hmb⟩ := Nat.exists_eq_pow_mul_and_not_dvd hm p hp'.ne_one
  have hb₀ : b ≠ 0 := fun h => hb (h ▸ dvd_zero p)
  let d := b.totient
  have hd : 0 < d := Nat.totient_pos.mpr (Nat.pos_of_ne_zero hb₀)
  have hcop := hp'.coprime_iff_not_dvd.mpr hb
  have hdiv : b ∣ p ^ d - 1 := (Nat.modEq_iff_dvd' (Nat.one_le_pow _ _ hp'.pos)).mp
    (Nat.ModEq.pow_totient hcop).symm
  obtain ⟨c, hc⟩ := hdiv
  obtain ⟨r, hr, hrσ⟩ := hroot d hd
  have hN : p ^ d - 1 ≠ 0 := (Nat.sub_pos_of_lt (Nat.one_lt_pow hd.ne' hp'.one_lt)).ne'
  have hr₀ : r ≠ 0 := by
    rintro rfl
    rw [zero_pow hN] at hr
    exact Nat.cast_ne_zero.mpr hp'.ne_zero hr.symm
  let R := Units.mk0 r hr₀
  let Y := Units.mk0 (y ^ p ^ a) (pow_ne_zero _ hy)
  have hR : unitRatio σ R ∈ A.principalUnitGroup := by
    rw [ValuationSubring.mem_principalUnitGroup_iff, coe_unitRatio]
    exact hrσ
  have hval : A.valuation (Y : K) = A.valuation (R : K) ^ ((c : ℤ) * k) := by
    change A.valuation (y ^ p ^ a) = A.valuation r ^ ((c : ℤ) * k)
    rw [← pow_left_inj₀ zero_le zero_le hb₀, map_pow, ← pow_mul, ← hmb, hv, ← hr,
      map_pow, hc, ← zpow_natCast (A.valuation r) (b * c),
      ← zpow_natCast (A.valuation r ^ ((c : ℤ) * k)) b, ← zpow_mul, ← zpow_mul]
    congr 1
    push_cast
    ring
  have hY := unitRatio_mem_of_val_eq_zpow A hσ hR hval
  rw [ValuationSubring.mem_principalUnitGroup_iff, coe_unitRatio] at hY
  change A.valuation (σ (y ^ p ^ a) / y ^ p ^ a - 1) < 1 at hY
  rw [map_pow, ← div_pow] at hY
  exact valuation_sub_one_lt_of_primePow A hp a hY

end GlobalTheory.TameKummer
