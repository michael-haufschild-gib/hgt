import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.Scales.CoordinateCap

/-! # Cutoff, population and variance on the coherent echo window -/
open Real Filter Set
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer

/-- For t=y⁹ below the previous polynomial onset, yJ≤1. Hence
N y⁴⁹≥D forces N y³⁶≥D J², enough for uniform Gaussian box counts.
The same inequality on y suppresses the localized echo variance. -/
theorem eventual_coherent_scales {a d D : ℝ} (ha : a∈Ioc (0:ℝ) 1) (hd : 0<d) (hD : 0<D) :
    ∀ᶠ n : ℕ in atTop, let N : ℝ := (n+1:ℕ)
      let J := (prefixIndex n:ℝ)
      ∀ y∈Ioc (0:ℝ) 1, y^9≤(1/J)^12 → D≤N*y^49 →
        let h := a*y^4
        1≤N*h ∧ 16*log N≤d*h^9*N ∧ 2000000*J^2*y^5≤a := by
  let C : ℝ := 4*2^256
  let E := C+256
  let A := a^9*D
  have hC : 0<C := by positivity
  have hA : 0<A := mul_pos (pow_pos ha.1 9) hD
  have hE : 0<E := by dsimp only [E]; positivity
  obtain ⟨k,hk⟩ := exists_nat_ge (max (1/A) (max (16*E/(d*A)) (2000000/a)))
  filter_upwards [prefixIndex_tendsto.eventually_ge_atTop k,eventually_ge_atTop (3:ℕ)] with n hn hk'
  intro N J y hy ht hN h
  obtain ⟨hj,_,_⟩ := prefixIndex_bounds n hk'
  have hJ₁ : (1:ℝ)≤(prefixIndex n:ℝ) := by exact_mod_cast (show 1≤prefixIndex n from hj)
  have hJ := zero_lt_one.trans_le hJ₁
  have hpos : 0<N := Nat.cast_pos.mpr (Nat.succ_pos _)
  have hK : N≤C*J^256 :=
    ((Nat.cast_le (α:=ℝ)).mpr (Nat.le_succ (n+1))).trans (real_prefix_size n hk').2
  have hlog : log N≤E*J := calc
    _ ≤ log (C*J^256) := log_le_log hpos hK
    _ = log C+256*log J := by rw [log_mul hC.ne' (pow_ne_zero 256 hJ.ne'),log_pow,Nat.cast_ofNat]
    _ ≤ _ := by dsimp only [E]; linarith only [log_le_sub_one_of_pos hC,log_le_sub_one_of_pos hJ,
      mul_le_mul_of_nonneg_left hJ₁ hC.le]
  have hjinv := one_div_pos.mpr hJ
  have h_le := ht.trans (pow_le_pow_of_le_one hjinv.le ((div_le_one hJ).mpr hJ₁) (by decide : 9≤12))
  have hyJ : y*J≤1 := (le_div_iff₀ hJ).mp (by
    by_contra! hgt
    exact h_le.not_gt (pow_lt_pow_left₀ hgt hjinv.le (by decide : 9≠0)))
  have hprod : y^13*J^2≤1 := calc
    _ ≤ y^2*J^2 := mul_le_mul_of_nonneg_right (pow_le_pow_of_le_one hy.1.le hy.2 (by decide : 2≤13)) (sq_nonneg J)
    _ = (y*J)^2 := (mul_pow ..).symm
    _ ≤ 1 := pow_le_one₀ (mul_nonneg hy.1.le hJ.le) hyJ
  have hmass : D*J^2≤N*y^36 := calc
    _ ≤ (N*y^49)*J^2 := mul_le_mul_of_nonneg_right hN (sq_nonneg J)
    _ = (N*y^36)*(y^13*J^2) := by ring
    _ ≤ _ := mul_le_of_le_one_right (mul_nonneg hpos.le (pow_nonneg hy.1.le 36)) hprod
  have hw : A*J^2≤h^9*N := by
    have hh := mul_le_mul_of_nonneg_left hmass (pow_nonneg ha.1.le 9)
    dsimp only [A,h]; rw [mul_pow]; linarith only [hh]
  have hbig := hk.trans ((Nat.cast_le (α:=ℝ)).mpr hn)
  have hbig₁ := (div_le_iff₀ hA).mp ((le_max_left ..).trans hbig)
  have hbig₂ := (div_le_iff₀ (mul_pos hd hA)).mp (((le_max_left ..).trans (le_max_right ..)).trans hbig)
  have hbig₃ := (div_le_iff₀ ha.1).mp (((le_max_right ..).trans (le_max_right ..)).trans hbig)
  have hh₀ : 0≤h := mul_nonneg ha.1.le (pow_nonneg hy.1.le 4)
  have hh₁ : h≤1 := (mul_le_mul ha.2 (pow_le_one₀ hy.1.le hy.2) (pow_nonneg hy.1.le 4) zero_le_one).trans_eq (one_mul 1)
  have hhy : h^9≤h := by simpa only [pow_one] using pow_le_pow_of_le_one hh₀ hh₁ (by decide : 1≤9)
  have hJ2 : J≤J^2 := by simpa only [pow_one] using pow_le_pow_right₀ hJ₁ (by decide : 1≤2)
  refine ⟨?_,?_,?_⟩
  · linarith only [hbig₁,hw,mul_le_mul_of_nonneg_left hJ2 hA.le,mul_le_mul_of_nonneg_right hhy hpos.le]
  · linarith only [hlog,mul_le_mul_of_nonneg_right hbig₂ hJ.le,mul_le_mul_of_nonneg_left hw hd.le]
  · have hmix : J^3*y^5≤1 := calc
      _ ≤ J^3*y^3 := mul_le_mul_of_nonneg_left (pow_le_pow_of_le_one hy.1.le hy.2 (by decide : 3≤5)) (pow_nonneg hJ.le 3)
      _ = (y*J)^3 := by ring
      _ ≤ 1 := pow_le_one₀ (mul_nonneg hy.1.le hJ.le) hyJ
    linarith only [mul_le_mul_of_nonneg_right hbig₃ (mul_nonneg (sq_nonneg J) (pow_nonneg hy.1.le 5)),
      mul_le_mul_of_nonneg_left hmix ha.1.le]

#print axioms eventual_coherent_scales
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
