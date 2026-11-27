import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.PrecisionProfile.CutSpeed
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.WeakBondDeficit.PrecisionProfile.SweepError
import GaloisForLFunctions.HTGeometry.Quantum.CircuitWindows.MaximumOccupation

/-! # Short-time distance to the full circuit set below one bond sweep -/

open Set Real Filter MeasureTheory
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
noncomputable section

/-- For d=Kh⁹ missing gates the distance to the entire budget grows
at speed comparable to Kh¹⁰, starting at zero and uniformly down to
arbitrarily small times. Here Kh²⁰ must exceed a fixed constant. -/
theorem gaussian_deficit_distance_speed :
    ∃ γ>0, ∃ Q>0, ∃ c>0, ∃ C>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let K : ℝ := (n+2:ℕ)
      let u := pathPauliDisorderShell ω n
      ∀ (d : ℕ) (h : ℝ), d≤n+1 → (d:ℝ)=K*h^9 → 0<h → h≤γ → Q≤K*h^20 →
        let V := K*h^10
        ∀ t : ℝ, |t| * V≤1 →
          let δ := Metric.infDist (unitaryEvolution (pathHamiltonian u) t) (phaseCircuitMatrixImageAtMost (n+2) (n+1-d))
          c*(|t| * V)≤δ ∧ δ≤C*(|t| * V) := by
  obtain ⟨g,hg,R,hR,A,hA,B,hB,hfit⟩ := gaussian_sweep_error
  obtain ⟨_,_,C,hC,hw⟩ := gaussian_weak_edge_counts
  obtain ⟨_,E,_,hE,hbulk⟩ := gaussian_path_eventual_coefficient_mass
  let M := max 1 (4*C)
  have hM : 1≤M := le_max_left ..
  have hm := zero_lt_one.trans_le hM
  have hM9 : 4*C≤M^9 := (le_max_right ..).trans (by
    calc M = M^1 := (pow_one _).symm
         _ ≤ _ := pow_le_pow_right₀ hM (by decide))
  let α := 1/(4*M)
  have hα : 0<α := by dsimp only [α]; positivity
  have hα' : α≤1 := (div_le_one (by positivity : 0<4*M)).mpr (by linarith only [hM])
  let S := 200*π/α
  have hS : 0<S := by dsimp only [S]; positivity
  let Q := max (max R 1) (max ((4*2^20)*M^20) (S^2*E))
  have hQ : 0<Q := hR.trans_le ((le_max_left ..).trans (le_max_left ..))
  refine ⟨min g 1,lt_min hg zero_lt_one,Q,hQ,α/(8*π),by positivity,A+B,add_pos hA hB,?_⟩
  filter_upwards [hfit,hw,hbulk] with ω hω hw he
  filter_upwards [hω,hw,he] with n hn hw he
  intro K u d h hdn hd hh hγ hscale V t ht δ
  have hK : 0<K := by dsimp only [K]; positivity
  have hV : 0<V := mul_pos hK (pow_pos hh _)
  let y := h/M
  have hy : 0<y := div_pos hh hm
  have hy₁ : y≤1 := (div_le_self hh.le hM).trans (hγ.trans (min_le_right ..))
  have hr : 4*2^20≤K*y^20 := by
    change 4*2^20≤K*(h/M)^20
    rw [div_pow,←mul_div_assoc,le_div_iff₀ (pow_pos hm _)]
    exact ((le_max_left ..).trans (le_max_right ..)).trans hscale
  have hw' := (hw y hy hy₁ hr).2
  have hcount : 4*(weakEdges u y).card≤d := by
    apply (Nat.cast_le (α:=ℝ)).mp
    rw [Nat.cast_mul,Nat.cast_ofNat,hd]
    apply (mul_le_mul_of_nonneg_left hw' (by norm_num : (0:ℝ)≤4)).trans
    change 4*(C*K*(h/M)^9)≤K*h^9
    rw [div_pow,←mul_div_assoc,←mul_div_assoc,div_le_iff₀ (pow_pos hm _)]
    nlinarith only [mul_le_mul_of_nonneg_right hM9 (mul_nonneg hK.le (pow_nonneg hh.le 9))]
  have hv2 : S^2*E*K≤V^2 := by
    have hp := mul_le_mul_of_nonneg_right (((le_max_right ..).trans (le_max_right ..)).trans hscale) hK.le
    change S^2*E*K≤_ at hp
    exact hp.trans_eq (by dsimp only [V]; ring)
  have hnorm : S*‖u‖≤V := by
    apply le_of_sq_le_sq _ hV.le
    rw [mul_pow]
    apply (mul_le_mul_of_nonneg_left he.2 (sq_nonneg S)).trans
    exact (mul_assoc (S^2) E K).ge.trans hv2
  have hmass : 200*π*‖u‖≤α*V := by
    have hs : α*S=200*π := by dsimp only [S]; field_simp
    rw [←hs,mul_assoc]
    exact mul_le_mul_of_nonneg_left hnorm hα.le
  constructor
  · have hf : HasProjectiveCircuitApproximation (n+2) δ (n+1-d) (unitaryEvolution (pathHamiltonian u) t) :=
      (hasProjectiveCircuitApproximation_iff_infDist ..).mpr le_rfl
    obtain ⟨z,hz,D,hD,herr⟩ := hf
    obtain ⟨cut,b,hc⟩ := missing_bond_mass u D d hy.le (by omega) hcount
    have hid : (d:ℝ)*y/4=α*V := by rw [hd]; dsimp only [α,V,y]; ring
    rw [hid] at hc
    have htv : |t| * (α*V)≤π := calc
      _ = α*(|t| * V) := by ring
      _ ≤ α*1 := mul_le_mul_of_nonneg_left ht hα.le
      _ ≤ π := by rw [mul_one]; linarith only [hα',pi_gt_three]
    have lo := (cut_speed u D cut b _ (mul_pos hα hV) hc hmass t htv z hz).trans herr
    exact le_trans (le_of_eq (by ring)) lo
  · obtain ⟨z,hz,D,hD,herr⟩ := hn h hh (hγ.trans (min_le_left ..))
      (((le_max_left ..).trans (le_max_left ..)).trans hscale) d hd.le t
    have hKV : K≤V^2 := calc
      _ ≤ K*(K*h^20) := le_mul_of_one_le_right hK.le
        (((le_max_right ..).trans (le_max_left ..)).trans hscale)
      _ = _ := by dsimp only [V]; ring
    have htime : K*t^2≤|t| * V := calc
      _ ≤ V^2*t^2 := mul_le_mul_of_nonneg_right hKV (sq_nonneg t)
      _ = (|t| * V)^2 := by rw [mul_pow |t| V,sq_abs,mul_comm]
      _ ≤ _ := by simpa only [sq,mul_one] using mul_le_mul_of_nonneg_left ht (mul_nonneg (abs_nonneg _) hV.le)
    apply (hasProjectiveCircuitApproximation_iff_infDist ..).mp
    refine ⟨z,hz,D,hD,herr.trans ?_⟩
    change A* |t| * V+B*K*t^2≤_
    linarith only [mul_le_mul_of_nonneg_left htime hB.le]

#print axioms gaussian_deficit_distance_speed
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.WeakBondDeficit
