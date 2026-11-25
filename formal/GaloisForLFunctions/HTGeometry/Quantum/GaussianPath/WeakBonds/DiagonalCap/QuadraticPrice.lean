import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.DiagonalCap.CarrierBox

/-! # Quadratic-in-qubit negative log probability for an all-time gate cap -/

open Set MeasureTheory Real
namespace GaloisForLFunctions.HTGeometry.WeakBonds.DiagonalCap
open PrescribedTimes
noncomputable section

/-- For every prescribed accuracy the probability of a diagonal-size
circuit cap holding for every physical time is at least a^(N²), with
one base a in (0,1) for every register size. -/
theorem gaussian_all_time_diagonal_cap {ε : ℝ} (hε : 0<ε) :
    ∃ a∈Ioo (0:ℝ) 1, ∀ n : ℕ, let N := n+2
      a^(N^2)≤pathPauliDisorderLaw.real {ω | ∀ t : ℝ,
        HasProjectiveCircuitApproximation N ε (2^N*(2*N+1))
          (unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t)} := by
  let R := 2*sqrt packConstant
  have hR : 0<R := mul_pos two_pos (sqrt_pos.mpr packConstant_pos)
  let b := min 1 (ε/R)
  have hb : 0<b := lt_min zero_lt_one (div_pos hε hR)
  have hb₁ : b≤1 := min_le_left ..
  have hbε : R*b≤ε := by
    rw [mul_comm]
    exact (le_div_iff₀ hR).mp (min_le_right ..)
  let f := _root_.HTGeometry.gaussianFloorConstant
  have hf : 0<f := _root_.HTGeometry.gaussianFloorConstant_pos
  let v := min (1/6:ℝ) (f*b/6)
  have hv : 0<v := lt_min (by norm_num) (div_pos (mul_pos hf hb) (by norm_num))
  have hv₁ : v<1 := (min_le_left ..).trans_lt (by norm_num)
  refine ⟨v^24,⟨pow_pos hv _,pow_lt_one₀ hv.le hv₁ (by decide)⟩,?_⟩
  intro n N
  let d := Fintype.card (PrefixIndex n)
  have hd : d≤12*N := by
    dsimp only [d,N]
    rw [Fintype.card_congr (pathCoeffEquiv n)]
    simp only [PathLabel,Fintype.card_sum,Fintype.card_prod,Fintype.card_fin]
    omega
  have hD : (d:ℝ)≤12*(2:ℝ)^N := by
    exact_mod_cast hd.trans (Nat.mul_le_mul_left 12 (Nat.lt_two_pow_self (n:=N)).le)
  let δ := b/(12*(6:ℝ)^N)
  have hδ : 0<δ := div_pos hb (by positivity)
  have hδ₁ : δ≤1 := (div_le_one (by positivity)).mpr (hb₁.trans (one_le_mul_of_one_le_of_one_le
    (by norm_num) (one_le_pow₀ (by norm_num))))
  have herr : R*(3:ℝ)^N*((d:ℝ)*δ)≤ε := by
    apply le_trans _ hbε
    calc
      _ ≤ R*(3:ℝ)^N*((12*(2:ℝ)^N)*δ) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hD hδ.le) (by positivity)
      _ = R*b := by
        dsimp only [δ]
        rw [show (6:ℝ)^N=3^N*2^N from by rw [←mul_pow]; norm_num]
        field_simp
  have hvδ : v^(N+1)≤f*(2*δ) := calc
    _ ≤ (1/6:ℝ)^N*(f*b/6) := by
      rw [pow_succ]
      exact mul_le_mul (pow_le_pow_left₀ hv.le (min_le_left ..) _) (min_le_right ..) hv.le (by positivity)
    _ = _ := by dsimp only [δ]; rw [_root_.one_div_pow]; ring
  have hpower : (N+1)*d≤24*N^2 := by
    have hz : 1≤N := by dsimp only [N]; omega
    have ha : N+1≤2*N := by omega
    exact (Nat.mul_le_mul ha hd).trans_eq (by ring)
  have hlow : (v^24)^(N^2)≤(f*(2*δ))^d := calc
    _ ≤ (v^(N+1))^d := by
      rw [←pow_mul,←pow_mul]
      exact pow_le_pow_of_le_one hv.le hv₁.le hpower
    _ ≤ _ := pow_le_pow_left₀ (pow_nonneg hv.le _) hvδ _
  apply hlow.trans (le_trans (gaussian_diagonal_cap_box n hδ hδ₁) ?_)
  letI : IsProbabilityMeasure pathPauliDisorderLaw := by unfold pathPauliDisorderLaw; infer_instance
  refine measureReal_mono ?_ (measure_ne_top _ _)
  intro ω hω t
  obtain ⟨z,hz,C,hC,h⟩ := hω t
  exact ⟨z,hz,C,hC,h.trans herr⟩

#print axioms gaussian_all_time_diagonal_cap
end
end GaloisForLFunctions.HTGeometry.WeakBonds.DiagonalCap
