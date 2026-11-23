import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.SpectatorCost.ExponentialFloor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.SpectralGapMass.SpectatorCost.GaussianFloor
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.PhysicalDensity

/-! # Extensive spectral gate cost at an inverse-size physical date -/
open Matrix MeasureTheory Filter Set
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.SpectralGapMass.SpectatorCost
noncomputable section

/-- After inverse-size onset the spectral gate floor varies as 1/(Nt²)
on every fixed signed horizon, uniformly over dates and bases. -/
theorem gaussian_inverse_square_floor :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ T : ℝ, ∀ᶠ n : ℕ in atTop,
      ∀ t : ℝ, A ≤ |t| *(n+1:ℕ) → |t| ≤ T →
      ∀ (W : unitaryGroup (Fin (n+2) → Bool) ℂ) (s : ℕ),
      HasProjectiveCircuitApproximation (n+2) (1/10) s
        (W.val*unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) t*star W.val) →
      1/(B*(n+2:ℕ)*t^2) ≤ Real.log 42+(s:ℝ)*Real.log 4 := by
  obtain ⟨A,hA,hfar⟩ := gaussian_scalar_departure
  obtain ⟨_,b,_,hb,hm⟩ := gaussian_path_eventual_coefficient_mass
  refine ⟨A,352800*b,hA,by positivity,?_⟩
  filter_upwards [hfar,hm] with ω hw hω
  intro T
  filter_upwards [hw T,hω] with n hn hm
  intro t ht hT W s hfit
  have ht₀ : t ≠ 0 := by
    rintro rfl
    rw [abs_zero,zero_mul] at ht
    exact hA.not_ge ht
  simpa only [mul_assoc] using spectral_gate_floor (pathPauliDisorderShell ω n) ht₀
    (mul_pos hb (by positivity : 0 < ((n+2:ℕ):ℝ))) hm.2 W (hn t ht hT) hfit

/-- A physical sweep fits the inverse-size evolution. Even with a free
choice of basis the required budget grows proportionally to chain length. -/
theorem gaussian_extensive_inverse_size :
    ∃ A K : ℝ, 0 < A ∧ 0 < K ∧ ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      let U := unitaryEvolution (pathHamiltonian (pathPauliDisorderShell ω n)) (A/(n+1:ℕ))
      HasProjectiveCircuitApproximation (n+2) (1/10) (n+1) U ∧
      ∀ (W : unitaryGroup (Fin (n+2) → Bool) ℂ) (s : ℕ),
        HasProjectiveCircuitApproximation (n+2) (1/10) s (W.val*U*star W.val) →
        ((n+1:ℕ):ℝ) ≤ K*(1+(s:ℝ)) := by
  obtain ⟨a,B,ha,hB,hf⟩ := gaussian_inverse_square_floor
  obtain ⟨c,hc,hu⟩ := SpanningDensity.gaussian_spanning_gate_density
  let A := max a Real.pi
  have hA : 0 < A := ha.trans_le (le_max_left ..)
  let K := 2*B*A^2*(Real.log 42+Real.log 4)
  have hl₁ := Real.log_pos (by norm_num : (1:ℝ)<42)
  have hl₂ := Real.log_pos (by norm_num : (1:ℝ)<4)
  refine ⟨A,K,hA,by dsimp only [K]; positivity,?_⟩
  obtain ⟨k,hk⟩ := exists_nat_gt (2*A^2/c)
  filter_upwards [hf,hu] with ω hω hu
  filter_upwards [hω A,hu 0,eventually_ge_atTop k] with n hn hup hlarge
  intro U
  let m := ((n+1:ℕ):ℝ)
  let N := ((n+2:ℕ):ℝ)
  have hm₁ : 1 ≤ m := by dsimp only [m]; exact_mod_cast (show 1 ≤ n+1 by omega)
  have hmpos := zero_lt_one.trans_le hm₁
  have hN : N ≤ 2*m := by dsimp only [N,m]; push_cast; linarith only [n.cast_nonneg (α:=ℝ)]
  have hN₀ : 0 < N := by dsimp only [N]; positivity
  let t := A/m
  have ht : 0 < t := div_pos hA hmpos
  have htm : |t| *m=A := by rw [abs_of_pos ht]; exact div_mul_cancel₀ A hmpos.ne'
  have hstart : a ≤ |t| *m := (le_max_left a Real.pi).trans htm.ge
  have hend : |t| ≤ A := (abs_of_pos ht).le.trans (div_le_self hA.le hm₁)
  have hkc : 2*A^2 < c*m := by
    have hkm : (k:ℝ) ≤ m := by dsimp only [m]; exact_mod_cast (show k≤n+1 by omega)
    simpa only [mul_comm m c] using (div_lt_iff₀ hc).mp (hk.trans_le hkm)
  have hsmall : t^2*N ≤ c := by
    dsimp only [t]
    rw [div_pow,div_mul_eq_mul_div,div_le_iff₀ (sq_pos_of_pos hmpos)]
    nlinarith only [mul_le_mul_of_nonneg_left hN (sq_nonneg A),mul_le_mul_of_nonneg_right hkc.le hmpos.le]
  constructor
  · have hp : Real.pi ≤ |t| *(1/((0+1:ℕ):ℝ))^2*(n+1:ℕ) := by
      simp only [zero_add,Nat.cast_one,div_one,one_pow,mul_one]
      exact (le_max_right a Real.pi).trans htm.ge
    obtain ⟨s,hs,_,hsN⟩ := hup t hp hsmall (1/10) ⟨by norm_num,by norm_num⟩
    obtain ⟨z,hz,C,hC,he⟩ := hs.1
    exact ⟨z,hz,C,hC.trans hsN,he⟩
  · intro W s hfit
    let x := Real.log 42+(s:ℝ)*Real.log 4
    have hx : 0 ≤ x := add_nonneg hl₁.le (mul_nonneg (Nat.cast_nonneg _) hl₂.le)
    have hh := hn t hstart hend W s hfit
    change 1/(B*N*(A/m)^2) ≤ x at hh
    have hmass' := (div_le_iff₀ (show 0<B*N*(A/m)^2 by positivity)).mp hh
    field_simp [hmpos.ne'] at hmass'
    have hlin : m ≤ 2*B*A^2*x := by
      apply (mul_le_mul_iff_left₀ hmpos).mp
      have hh' := mul_le_mul_of_nonneg_right hN (show 0 ≤ B*A^2*x by positivity)
      nlinarith only [hh',hmass']
    have hx' : x ≤ (Real.log 42+Real.log 4)*(1+(s:ℝ)) := by
      dsimp only [x]
      nlinarith only [mul_nonneg hl₁.le (Nat.cast_nonneg (α:=ℝ) s),hl₂.le]
    exact hlin.trans ((mul_le_mul_of_nonneg_left hx' (by positivity)).trans_eq (by dsimp only [K]; ring))

#print axioms gaussian_extensive_inverse_size
#print axioms gaussian_inverse_square_floor
end
end GaloisForLFunctions.HTGeometry.SpectralGapMass.SpectatorCost
