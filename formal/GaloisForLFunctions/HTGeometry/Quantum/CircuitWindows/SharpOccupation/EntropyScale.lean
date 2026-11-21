import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! # Subextensive metric entropy on the Hilbert-space dimension scale -/
open Filter Topology
namespace GaloisForLFunctions.HTGeometry.SharpOccupation
noncomputable section

/-- The logarithm of a fixed-mesh circuit net is controlled by the qubit
count times the gate count, up to Hilbert-space dimension gates. -/
theorem net_envelope_le_exp (n s : ℕ) (δ : ℝ) (hδ : 0 < δ) (hs : s ≤ 2^n) :
    ((s:ℝ)+1)*((((n:ℝ)+1)^2)*(1+4*(s:ℝ)/δ)^32)^s ≤
      Real.exp ((36+128/δ)*((n:ℝ)+1)*((s:ℝ)+1)) := by
  have he : (2:ℝ) ≤ Real.exp 1 := by linarith only [Real.add_one_le_exp (1:ℝ)]
  have hd : (2:ℝ)^n ≤ Real.exp (n:ℝ) := by
    simpa only [←Real.exp_nat_mul,mul_one] using pow_le_pow_left₀ (by norm_num) he n
  have hs' : (s:ℝ) ≤ Real.exp (n:ℝ) := (by exact_mod_cast hs : (s:ℝ) ≤ (2:ℝ)^n).trans hd
  have h1 : 1 ≤ Real.exp (n:ℝ) := Real.one_le_exp (Nat.cast_nonneg _)
  have hS : (s:ℝ)+1 ≤ Real.exp ((n:ℝ)+1) := by
    rw [Real.exp_add]
    exact (add_le_add hs' h1).trans ((by rw [←mul_two] : Real.exp (n:ℝ)+Real.exp n ≤ Real.exp n*2).trans
      (mul_le_mul_of_nonneg_left he (Real.exp_pos _).le))
  let R := 4/δ
  have hR : 0 ≤ R := by dsimp [R]; positivity
  have hx : 1+4*(s:ℝ)/δ ≤ Real.exp (R+(n:ℝ)) := by
    rw [Real.exp_add]
    calc
      _ = 1+R*(s:ℝ) := by dsimp [R]; ring
      _ ≤ Real.exp (n:ℝ)+R*Real.exp n := add_le_add h1 (mul_le_mul_of_nonneg_left hs' hR)
      _ = (R+1)*Real.exp n := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_right (Real.add_one_le_exp R) (Real.exp_pos _).le
  have hbase : (((n:ℝ)+1)^2)*(1+4*(s:ℝ)/δ)^32 ≤ Real.exp (2*(n:ℝ)+32*(R+n)) := by
    rw [Real.exp_add]
    apply mul_le_mul (b := Real.exp (2*(n:ℝ))) _ _ (by positivity) (Real.exp_pos _).le
    · rw [show Real.exp (2*(n:ℝ))=(Real.exp n)^2 by simpa using Real.exp_nat_mul (n:ℝ) 2]
      exact pow_le_pow_left₀ (by positivity) (Real.add_one_le_exp (n:ℝ)) 2
    · rw [show Real.exp (32*(R+(n:ℝ)))=(Real.exp (R+n))^32 by simpa using Real.exp_nat_mul (R+n) 32]
      exact pow_le_pow_left₀ (by positivity) hx 32
  calc
    _ ≤ Real.exp ((n:ℝ)+1)*(Real.exp (2*(n:ℝ)+32*(R+n)))^s :=
      mul_le_mul hS (pow_le_pow_left₀ (by positivity) hbase _) (by positivity) (Real.exp_pos _).le
    _ = Real.exp ((n:ℝ)+1+(s:ℝ)*(2*(n:ℝ)+32*(R+n))) := by rw [Real.exp_add _ ((s:ℝ)*_),Real.exp_nat_mul]
    _ ≤ _ := by
      apply Real.exp_le_exp.mpr
      rw [show 128/δ = 32*R by dsimp [R]; ring]
      nlinarith only [Nat.cast_nonneg (α := ℝ) n,Nat.cast_nonneg (α := ℝ) s,hR,
        mul_nonneg (Nat.cast_nonneg (α := ℝ) n) (Nat.cast_nonneg (α := ℝ) s),
        mul_nonneg hR (Nat.cast_nonneg (α := ℝ) n),
        mul_nonneg (mul_nonneg hR (Nat.cast_nonneg (α := ℝ) n)) (Nat.cast_nonneg (α := ℝ) s)]

/-- A subexponential prefactor does not change the exponential rate of a
short-arc probability. Both limits use the actual register dimension. -/
theorem enlarged_arc_eventually_lt {s : ℕ → ℕ}
    (hs : Tendsto (fun n : ℕ => (((n:ℝ)+1)*((s n:ℝ)+1))/(2:ℝ)^n) atTop (𝓝 0))
    (C y b : ℝ) (hy : 0 < y) (hyb : y < b) :
    ∀ᶠ n : ℕ in atTop, Real.exp (C*((n:ℝ)+1)*((s n:ℝ)+1))*
      ((2:ℝ)^n*y^(2^n-1:ℕ)) < b^(2^n:ℕ) := by
  have hd : Tendsto (fun n : ℕ => (2:ℝ)^n) atTop atTop :=
    tendsto_pow_atTop_atTop_of_one_lt (by norm_num)
  have hl := Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero.comp hd
  have ha := (hs.const_mul C).add hl
  have hi := hd.inv_tendsto_atTop
  have hc := ha.add ((hi.const_sub 1).mul_const (Real.log y))
  have hlim : Tendsto (fun n : ℕ => C*(((n:ℝ)+1)*((s n:ℝ)+1)/(2:ℝ)^n) +
      Real.log ((2:ℝ)^n)/(2:ℝ)^n + (1-((2:ℝ)^n)⁻¹)*Real.log y) atTop (𝓝 (Real.log y)) := by
    simpa [Function.comp_def] using hc
  filter_upwards [hlim.eventually_lt_const (Real.log_lt_log hy hyb)] with n hn
  have hp : 0 < (2:ℝ)^n := by positivity
  have hD : 1 ≤ (2:ℕ)^n := one_le_pow₀ (by norm_num)
  have hd' : ((2^n-1:ℕ):ℝ)=(2:ℝ)^n-1 := by rw [Nat.cast_sub hD,Nat.cast_pow,Nat.cast_ofNat,Nat.cast_one]
  have hb : 0 < b := hy.trans hyb
  apply (Real.log_lt_log_iff (by positivity) (by positivity : 0 < b^(2^n:ℕ))).mp
  rw [Real.log_mul (Real.exp_pos _).ne' (by positivity),Real.log_exp,
    Real.log_mul hp.ne' (pow_pos hy _).ne',Real.log_pow y,Real.log_pow b,hd']
  push_cast
  have he : C*((n:ℝ)+1)*((s n:ℝ)+1)+(Real.log ((2:ℝ)^n)+((2:ℝ)^n-1)*Real.log y) =
      (C*(((n:ℝ)+1)*((s n:ℝ)+1)/(2:ℝ)^n) + Real.log ((2:ℝ)^n)/(2:ℝ)^n +
      (1-((2:ℝ)^n)⁻¹)*Real.log y)*(2:ℝ)^n := by field_simp; ring
  rw [he,mul_comm _ (Real.log b)]
  exact mul_lt_mul_of_pos_right hn hp

end
end GaloisForLFunctions.HTGeometry.SharpOccupation
