import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.Scales.CoordinateCap

/-! # The balanced weak radius across the entire startup interval -/
open Set Filter Real
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer

/-- When N t h¹⁰=1, the count scale N h⁹ dominates the prefix
logarithm. Below J⁻³² the coordinate cap permits a coherent cut test.
Above J⁻³² the uncompensated quartic floor already applies. -/
theorem balanced_radius_scales {d L : ℝ} (hd : 0<d) :
    ∀ᶠ n : ℕ in atTop, let N : ℝ := (n+1:ℕ)
      let J := (prefixIndex n:ℝ)
      ∀ t∈Ioc (0:ℝ) 1, ∀ h∈Ioc (0:ℝ) 1, N*t*h^10=1 →
        1≤N*h ∧ 16*log N≤d*h^9*N ∧ (2000000*J^2*t≤h ∨ L≤N^9*t^49) := by
  let C : ℝ := 4*2^256
  let E := C+256
  let M : ℝ := 2000000
  have hC : 0<C := by positivity
  have hM : 0≤M := by norm_num [M]
  obtain ⟨k,hk⟩ := exists_nat_ge (max L (max (M^10*C) (16*E/d)))
  filter_upwards [prefixIndex_tendsto.eventually_ge_atTop k,eventually_ge_atTop (3:ℕ)] with n hnk hn
  intro N J t ht h hh he
  obtain ⟨hj,hlo,_⟩ := prefixIndex_bounds n hn
  have hJ : (1:ℝ)≤(prefixIndex n:ℝ) := by exact_mod_cast (show 1≤prefixIndex n from hj)
  have hJ₀ := zero_lt_one.trans_le hJ
  have hN : 0<N := Nat.cast_pos.mpr (Nat.succ_pos _)
  have hl : J^256≤N := by
    have hh := (Nat.cast_le (α:=ℝ)).mpr hlo
    simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at hh
    change 4*J^256≤N at hh
    linarith only [hh,pow_nonneg hJ₀.le 256]
  have hu : N≤C*J^256 :=
    ((Nat.cast_le (α:=ℝ)).mpr (Nat.le_succ (n+1))).trans (real_prefix_size n hn).2
  have hlog : log N≤E*J := calc
    _ ≤ log (C*J^256) := log_le_log hN hu
    _ = log C+256*log J := by rw [log_mul hC.ne' (pow_ne_zero 256 hJ₀.ne'),log_pow,Nat.cast_ofNat]
    _ ≤ _ := by dsimp only [E]; linarith only [log_le_sub_one_of_pos hC,log_le_sub_one_of_pos hJ₀,
      mul_le_mul_of_nonneg_left hJ hC.le]
  have hbig := hk.trans ((Nat.cast_le (α:=ℝ)).mpr hnk)
  have hL : L≤J := (le_max_left ..).trans hbig
  have hM' : M^10*C≤J := ((le_max_left ..).trans (le_max_right ..)).trans hbig
  have hd' : 16*E≤J*d := (div_le_iff₀ hd).mp (((le_max_right ..).trans (le_max_right ..)).trans hbig)
  have hu₁ : 1≤N*h^10 := calc
    _ = N*h^10*t := by linarith only [he]
    _ ≤ _ := mul_le_of_le_one_right (mul_nonneg hN.le (pow_nonneg hh.1.le 10)) ht.2
  have hmass : J^2≤N*h^9 := by
    have hl' : (J^2)^10≤N := (show (J^2)^10=J^20 by ring).trans_le
      ((pow_le_pow_right₀ hJ (by decide : 20≤256)).trans hl)
    have hpow : N≤N*(N*h^10)^9 := le_mul_of_one_le_right hN.le (one_le_pow₀ hu₁)
    by_contra! hlt
    exact (hl'.trans (hpow.trans_eq (by ring : N*(N*h^10)^9=(N*h^9)^10))).not_gt
      (pow_lt_pow_left₀ hlt (mul_nonneg hN.le (pow_nonneg hh.1.le 9)) (by decide : 10≠0))
  have hh₁ : h^10≤h := by simpa only [pow_one] using pow_le_pow_of_le_one hh.1.le hh.2 (by decide : 1≤10)
  refine ⟨hu₁.trans (mul_le_mul_of_nonneg_left hh₁ hN.le),?_,?_⟩
  · linarith only [hlog,mul_le_mul_of_nonneg_right hd' hJ₀.le,mul_le_mul_of_nonneg_left hmass hd.le]
  by_cases hdate : J^32*t≤1
  · left
    have hcut : N*t*(M*J^2*t)^10≤1 := calc
      _ ≤ (C*J^256)*t*(M*J^2*t)^10 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hu ht.1.le) (pow_nonneg (mul_nonneg (mul_nonneg hM (sq_nonneg J)) ht.1.le) 10)
      _ = (M^10*C)*J^276*t^11 := by ring
      _ ≤ J*J^276*t^11 := mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hM' (pow_nonneg hJ₀.le 276)) (pow_nonneg ht.1.le 11)
      _ ≤ J^352*t^11 := by
        rw [mul_comm J,←pow_succ]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hJ (by decide : 277≤352)) (pow_nonneg ht.1.le 11)
      _ = (J^32*t)^11 := by ring
      _ ≤ 1 := pow_le_one₀ (mul_nonneg (pow_nonneg hJ₀.le 32) ht.1.le) hdate
    by_contra! hlt
    exact (hcut.trans_eq he.symm).not_gt (mul_lt_mul_of_pos_left
      (pow_lt_pow_left₀ hlt hh.1.le (by decide : 10≠0)) (mul_pos hN ht.1))
  · right
    have ht' := (lt_of_not_ge hdate).le
    calc
      L ≤ J := hL
      _ ≤ J*(J^32*t)^49 := le_mul_of_one_le_right hJ₀.le (one_le_pow₀ ht')
      _ = J^1569*t^49 := by ring
      _ ≤ (J^256)^9*t^49 := by
        rw [←pow_mul]
        exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ hJ (by decide : 1569≤256*9)) (pow_nonneg ht.1.le 49)
      _ ≤ _ := mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (pow_nonneg hJ₀.le 256) hl 9) (pow_nonneg ht.1.le 49)

#print axioms balanced_radius_scales
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
