import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-! # Space for geometrically many guarded packet tests on a path -/
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
noncomputable section

/-- For n ≥ B^(2L) the guard width is at most √n. Both lost boundary
sites and the space for all separated tests fit inside the density p. -/
theorem geometric_packet_capacity (R k : ℕ) (hR : 0 < R) (hk : 0 < k) {p : ℝ} (hp : 0 < p) :
    ∃ B : ℕ, 2 ≤ B ∧ ∀ L : ℕ, 0 < L → ∀ n : ℕ, B^(2*L) ≤ n →
      let r := R^L
      let w := 2*r+2
      let m := k^L*k^L
      w^2 ≤ n ∧ ((2*w*m+2*r:ℕ):ℝ) ≤ p*(n+1:ℕ) ∧
        2*(r:ℝ)+(4*(p/8))*(w:ℝ) ≤ (n:ℝ)*(4*(p/8)) := by
  obtain ⟨c,hc⟩ := exists_nat_gt (max 4 (max (10/p) ((4+4*p)/p)))
  let B := c*(R*(k*k))
  have hc₄ : (4:ℝ) < c := (le_max_left ..).trans_lt hc
  have hc₁ : 1 ≤ c := by exact_mod_cast (by linarith only [hc₄] : (1:ℝ) ≤ c)
  have hK₁ : 1 ≤ R*(k*k) := Nat.mul_pos hR (Nat.mul_pos hk hk)
  have hB₁ : c ≤ B := Nat.le_mul_of_pos_right c hK₁
  have hc₂ : 2 ≤ c := by exact_mod_cast (by linarith only [hc₄] : (2:ℝ) ≤ c)
  refine ⟨B,hc₂.trans hB₁,?_⟩
  intro L hL n hn r w m
  let u := r*m
  have hr₁ : 1 ≤ r := Nat.pow_pos hR
  have hm₁ : 1 ≤ m := Nat.mul_pos (Nat.pow_pos hk) (Nat.pow_pos hk)
  have hwp : w ≤ 4*r := by dsimp only [w]; omega
  have hu : u=(R*(k*k))^L := by simp only [u,r,m,mul_pow]
  have hru : r ≤ u := Nat.le_mul_of_pos_right r hm₁
  have hbig : c*u ≤ B^L := by
    rw [hu,show B^L=c^L*(R*(k*k))^L from mul_pow ..]
    exact Nat.mul_le_mul_right _ (le_self_pow₀ hc₁ hL.ne')
  have hlong : B^L ≤ n := by
    apply le_trans _ hn
    exact Nat.pow_le_pow_right ((Nat.zero_lt_one.trans_le hc₁).trans_le hB₁) (by omega)
  have hcu : (c:ℝ)*(u:ℝ) ≤ n := by exact_mod_cast hbig.trans hlong
  have h₁ : (10:ℝ) ≤ p*c := by
    have hh := (div_le_iff₀ hp).mp (((le_max_left ..).trans (le_max_right ..)).trans hc.le)
    simpa only [mul_comm p] using hh
  have h₂ : 4+4*p ≤ p*c := by
    have hh := (div_le_iff₀ hp).mp (((le_max_right ..).trans (le_max_right ..)).trans hc.le)
    simpa only [mul_comm p] using hh
  have hr' : (r:ℝ) ≤ u := Nat.cast_le.mpr hru
  have hw' : (w:ℝ) ≤ 4*(r:ℝ) := by exact_mod_cast hwp
  constructor
  · have hw : w ≤ B^L := hwp.trans ((Nat.mul_le_mul (by exact_mod_cast hc₄.le) hru).trans hbig)
    calc w^2 ≤ (B^L)^2 := Nat.pow_le_pow_left hw 2
         _ = B^(2*L) := by rw [←pow_mul,Nat.mul_comm L 2]
         _ ≤ n := hn
  constructor
  · have hroom : 10*(u:ℝ) ≤ p*n := by
      exact (mul_le_mul_of_nonneg_right h₁ (Nat.cast_nonneg _)).trans
        ((mul_assoc ..).le.trans (mul_le_mul_of_nonneg_left hcu hp.le))
    have hwm := mul_le_mul_of_nonneg_right hw' (Nat.cast_nonneg m)
    dsimp only [u] at hroom hr'
    push_cast at hroom hr' ⊢
    linarith only [hroom,hwm,hr',hp]
  · have hroom : (4+4*p)*(u:ℝ) ≤ p*n := by
      exact (mul_le_mul_of_nonneg_right h₂ (Nat.cast_nonneg _)).trans
        ((mul_assoc ..).le.trans (mul_le_mul_of_nonneg_left hcu hp.le))
    nlinarith only [hroom,hr',mul_le_mul_of_nonneg_left hw' hp.le,mul_le_mul_of_nonneg_left hr' hp.le]

end
end GaloisForLFunctions.HTGeometry.SpanningDensity.FixedHorizon
