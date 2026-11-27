import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.SpanningDensity.BondTransfer.MovingDates.Scales.PrefixChoice
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Startup.FirstAscent.GaussianMass

/-! # A logarithmic coefficient cap valid through the moving startup date -/

open Filter MeasureTheory Finset Real
namespace GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
noncomputable section

/-- Cap for every interaction coordinate of one Gaussian prefix. -/
def coordinateCap (B : ℝ) (n : ℕ) := 1+2*sqrt (log (B*((n+2:ℕ):ℝ)))

/-- The reciprocal date brackets the chain size between two powers
with the same exponent. -/
theorem real_prefix_size (n : ℕ) (hn : 3≤n) :
    4*(prefixIndex n:ℝ)^256≤((n+2:ℕ):ℝ) ∧
      ((n+2:ℕ):ℝ)≤(4*2^256)*(prefixIndex n:ℝ)^256 := by
  obtain ⟨_,hl,hu⟩ := prefixIndex_bounds n hn
  have h₀ := (Nat.cast_le (α:=ℝ)).mpr (hl.trans (Nat.le_succ _))
  have h₁ := (Nat.cast_le (α:=ℝ)).mpr hu
  simp only [Nat.cast_mul,Nat.cast_pow,Nat.cast_ofNat] at h₀ h₁
  exact ⟨h₀,h₁.trans_eq (by rw [mul_pow,←mul_assoc])⟩

theorem gaussian_coordinate_window :
    ∃ B>0, ∀ᵐ ω ∂pathPauliDisorderLaw, ∀ᶠ n : ℕ in atTop,
      (∀ l, |pathPauliDisorderShell ω n l|≤coordinateCap B n) ∧
      3348*coordinateCap B n≤(prefixIndex n:ℝ) := by
  obtain ⟨B,hB,hw⟩ := FirstAscent.gaussian_subset_mass
  let C := B*(4*2^256)
  have hC : 0<C := by dsimp only [C]; positivity
  let A := |log C|+256
  obtain ⟨J,hJ⟩ := exists_nat_ge (max 6696 (13392^2*A))
  refine ⟨B,hB,?_⟩
  filter_upwards [hw] with ω hh
  filter_upwards [hh,eventually_ge_atTop (3:ℕ),prefixIndex_tendsto.eventually_ge_atTop J] with n hn hn₀ hnJ
  let j := prefixIndex n
  let K : ℝ := (n+2:ℕ)
  have hK : 0<K := by dsimp only [K]; positivity
  obtain ⟨hj,_,hup⟩ := prefixIndex_bounds n hn₀
  have hℝ : 1≤(j:ℝ) := by exact_mod_cast hj
  have hpos : (0:ℝ)<j := zero_lt_one.trans_le hℝ
  have hcut : max 6696 (13392^2*A)≤(j:ℝ) := hJ.trans (Nat.cast_le.mpr hnJ)
  have habs (l : PathLabel n) := hn {l} (singleton_nonempty l)
  simp only [sum_singleton,card_singleton,Nat.cast_one,one_pow,mul_one,div_one] at habs
  have hlog : 0≤log (B*K) := by
    have hs := habs (.inl (0,0))
    change |pathPauliDisorderShell ω n (.inl (0,0))|^2≤4*log (B*K) at hs
    linarith only [hs,sq_nonneg |pathPauliDisorderShell ω n (.inl (0,0))|]
  have hup' := (real_prefix_size n hn₀).2
  change K≤(4*2^256)*(j:ℝ)^256 at hup'
  have hl : log (B*K)≤A*(j:ℝ) := by
    have hx := log_le_log (mul_pos hB hK) ((mul_le_mul_of_nonneg_left hup' hB.le).trans_eq
      (mul_assoc B (4*2^256) ((j:ℝ)^256)).symm)
    rw [log_mul hC.ne' (pow_ne_zero _ hpos.ne'),log_pow] at hx
    have hc : log C ≤ |log C| *(j:ℝ) := (le_abs_self _).trans (by
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hℝ (abs_nonneg (log C)))
    have hlj : log (j:ℝ)≤(j:ℝ) := (log_le_sub_one_of_pos hpos).trans (sub_le_self _ zero_le_one)
    exact hx.trans ((add_le_add hc (mul_le_mul_of_nonneg_left hlj (by norm_num : (0:ℝ)≤256))).trans_eq
      (add_mul (abs (log C)) 256 (j:ℝ)).symm)
  have hsqrt : sqrt (log (B*K))≤(j:ℝ)/13392 := by
    have hz : (0:ℝ)≤(j:ℝ)/13392 := div_nonneg hpos.le (by norm_num)
    apply sqrt_le_iff.mpr ⟨hz,?_⟩
    have hd := (le_max_right _ _).trans hcut
    linarith only [hl,mul_le_mul_of_nonneg_right hd hpos.le]
  constructor
  · intro l
    have hh := habs l
    change |pathPauliDisorderShell ω n l|^2≤4*log (B*K) at hh
    have he : |pathPauliDisorderShell ω n l|≤2*sqrt (log (B*K)) :=
      (sq_le_sq₀ (abs_nonneg _) (mul_nonneg zero_le_two (sqrt_nonneg _))).mp
        (hh.trans_eq (by rw [mul_pow,sq_sqrt hlog]; ring))
    change _≤1+2*sqrt (log (B*K))
    linarith only [he]
  · change 3348*(1+2*sqrt (log (B*K)))≤(j:ℝ)
    linarith only [hsqrt,(le_max_left _ _).trans hcut]

#print axioms gaussian_coordinate_window
end
end GaloisForLFunctions.HTGeometry.SpanningDensity.BondTransfer
