import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.InteriorProductShells
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.CappedConductorPrefixes

/-!
# The seven-fourths shell through every terminal conductor

The shell n^(7/4)<pv≤2 floor(n^(7/4)) eventually lies strictly between
the two horizon boundaries. Its signed contribution through any
N<M≤2N is O(N^(13/4) log(2N)).
-/

noncomputable section
open Finset Filter
open GaloisForLFunctions.CountingHolography.Sections
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

def sevenFourthsCut (n : ℕ) := ⌊(n:ℝ)^(7/4:ℝ)⌋₊

def sevenFourthsShell (n : ℕ) :=
  cappedUpperProductReading (sevenFourthsCut n) n n-
    cappedUpperProductReading (2*sevenFourthsCut n) n n

/-- The admissible conductors of a fixed pair form one half-open integer
interval. Both shell edges, the cofactor cap and the terminal fragment
are retained, including equality at the upper product cut. -/
theorem sevenFourthsShell_conductors (N M q v : ℕ) :
    (Ioc N M).filter (fun n => v≤n ∧ sevenFourthsCut n<q ∧ q≤2*sevenFourthsCut n) =
      Ico (max (max (N+1) v) ⌈(((q+1)/2:ℕ):ℝ)^(4/7:ℝ)⌉₊)
        (min (M+1) ⌈(q:ℝ)^(4/7:ℝ)⌉₊) := by
  ext n
  have hpos : (0:ℝ)<4/7 := by norm_num
  have hpow : ((n:ℝ)^(7/4:ℝ))^(4/7:ℝ)=(n:ℝ) := by
    rw [←Real.rpow_mul (Nat.cast_nonneg n)]; norm_num
  have hn₀ := Real.rpow_nonneg (Nat.cast_nonneg (α := ℝ) n) (7/4:ℝ)
  have hup : sevenFourthsCut n<q ↔ (n:ℝ)<(q:ℝ)^(4/7:ℝ) := by
    rw [sevenFourthsCut,Nat.floor_lt hn₀]
    simpa only [hpow] using (Real.rpow_lt_rpow_iff hn₀ (Nat.cast_nonneg q) hpos).symm
  have hlo : q≤2*sevenFourthsCut n ↔ (((q+1)/2:ℕ):ℝ)^(4/7:ℝ)≤n := by
    rw [show q≤2*sevenFourthsCut n ↔ (q+1)/2≤ sevenFourthsCut n by omega,
      sevenFourthsCut,Nat.le_floor_iff hn₀]
    simpa only [hpow] using (Real.rpow_le_rpow_iff (Nat.cast_nonneg (α := ℝ) ((q+1)/2)) hn₀ hpos).symm
  simp only [mem_filter,mem_Ioc,mem_Ico,max_le_iff,lt_min_iff,Nat.ceil_le,Nat.lt_ceil,hup,hlo]
  constructor
  · rintro ⟨⟨hl,hu⟩,hv,hq,hq'⟩
    exact ⟨⟨⟨hl,hv⟩,hq'⟩,Nat.lt_succ_of_le hu,hq⟩
  · rintro ⟨⟨⟨hl,hv⟩,hq'⟩,hu,hq⟩
    exact ⟨⟨hl,Nat.le_of_lt_succ hu⟩,hv,hq,hq'⟩

private theorem shell_geometry : ∀ᶠ n : ℕ in atTop,
    0<sevenFourthsCut n ∧ 2*(sevenFourthsCut n:ℝ)+1<Real.exp (-8)*(n:ℝ)^2 ∧
    productLower 1 (splineHorizon n)≤ sevenFourthsCut n := by
  obtain ⟨A,hA,hwin⟩ := successorSquare_window_bound
  have ht : Tendsto (fun n : ℕ => (n:ℝ)^(1/4:ℝ)) atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/4)).comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_ge_atTop (1:ℕ),ht.eventually_ge_atTop (max (4*Real.exp 8) (2*A))]
    with n hn hcut
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hn₀ := zero_lt_one.trans_le hn'
  let X := (n:ℝ)^(7/4:ℝ)
  let t := (n:ℝ)^(1/4:ℝ)
  have hX : 1≤X := Real.one_le_rpow hn' (by norm_num)
  have hm : X*t=(n:ℝ)^2 := by
    dsimp [X,t]; rw [←Real.rpow_add hn₀]; norm_num
  have he₀ := (le_max_left ..).trans hcut
  have h₂ := (le_max_right ..).trans hcut
  have hbirth : 3<Real.exp (-8)*t := by
    rw [Real.exp_neg,inv_mul_eq_div,lt_div_iff₀ (Real.exp_pos 8)]
    exact (by nlinarith only [Real.exp_pos 8] : 3*Real.exp 8<4*Real.exp 8).trans_le he₀
  have hV : (sevenFourthsCut n:ℝ)≤X := Nat.floor_le (zero_le_one.trans hX)
  refine ⟨(Nat.one_le_floor_iff _).mpr hX,?_,?_⟩
  · rw [←hm]
    have hh := mul_lt_mul_of_pos_right hbirth (zero_lt_one.trans_le hX)
    linarith only [hh,hX,hV]
  · apply Nat.le_floor
    have ht₃ := Real.rpow_le_rpow_of_exponent_le hn' (by norm_num : (1/4:ℝ)≤3/4)
    have he : X=(n:ℝ)^(3/4:ℝ)*n := by
      rw [show X=(n:ℝ)^((3/4:ℝ)+1) by norm_num [X],Real.rpow_add hn₀,Real.rpow_one]
    have hroot : Real.sqrt (splineHorizon n)≤A*n := by
      have h := Real.sqrt_le_sqrt (hwin hn)
      rwa [Real.sqrt_sq (mul_nonneg (zero_le_one.trans hA) hn₀.le)] at h
    have hl : (productLower 1 (splineHorizon n):ℝ)≤2*Real.sqrt (splineHorizon n) := by
      apply (Nat.cast_le.mpr (min_le_right ..)).trans
      push_cast
      exact mul_le_mul_of_nonneg_left (Nat.floor_le (Real.sqrt_nonneg _)) (by norm_num)
    change (productLower 1 (splineHorizon n):ℝ)≤X
    rw [he]
    exact hl.trans ((mul_le_mul_of_nonneg_left hroot (by norm_num : (0:ℝ)≤2)).trans
      (by linarith only [mul_le_mul_of_nonneg_right (h₂.trans ht₃) hn₀.le]))

/-- The cap and both sharp product endpoints are retained at each n. -/
theorem sevenFourthsShell_bound :
    ∃ C : ℝ, 0≤C ∧ ∀ {n : ℕ}, 0<n →
      |sevenFourthsShell n|≤C*(n:ℝ)^(1/4:ℝ)*conductorLog n := by
  obtain ⟨C,hC,h⟩ := capped_interior_shell_bound
  obtain ⟨N,hN⟩ := eventually_atTop.mp shell_geometry
  let F := ∑ k ∈ Icc 1 N, |sevenFourthsShell k|
  have hF : 0≤F := sum_nonneg (fun _ _ => abs_nonneg _)
  refine ⟨F+2*C,by positivity,fun {n} hn => ?_⟩
  have hn' : (1:ℝ)≤n := by exact_mod_cast hn
  have hn₀ := zero_lt_one.trans_le hn'
  have hr : 1≤(n:ℝ)^(1/4:ℝ) := Real.one_le_rpow hn' (by norm_num)
  have hL := conductorLog_one_le n
  by_cases hbig : N≤n
  swap
  · have hsingle : |sevenFourthsShell n|≤F := single_le_sum (fun k _ => abs_nonneg (sevenFourthsShell k))
        (mem_Icc.mpr ⟨hn,by omega⟩)
    exact hsingle.trans ((show F≤F+2*C by linarith only [hC]).trans
      ((le_mul_of_one_le_right (by positivity : 0≤F+2*C) hr).trans (le_mul_of_one_le_right (by positivity) hL)))
  obtain ⟨hv,hbirth,hY⟩ := hN n hbig
  let V := sevenFourthsCut n
  let X := (n:ℝ)^(7/4:ℝ)
  have hfloor : (V:ℝ)≤X := Nat.floor_le (Real.rpow_nonneg hn₀.le _)
  have hlog : 1+Real.log (2*(V:ℝ))≤2*conductorLog n := by
    have hv' : (0:ℝ)<V := Nat.cast_pos.mpr hv
    have hh := Real.log_le_log hv' hfloor
    dsimp only [X] at hh
    rw [Real.log_rpow hn₀] at hh
    rw [conductorLog,Real.log_mul (by norm_num : (2:ℝ)≠0) hv'.ne',Real.log_mul (by norm_num) hn₀.ne']
    linarith only [hh,Real.log_nonneg (by norm_num : (1:ℝ)≤2),Real.log_nonneg hn']
  have hscale : X^3=(n:ℝ)^(1/4:ℝ)*(n:ℝ)^5 := by
    dsimp only [X]
    rw [←Real.rpow_natCast _ 3,←Real.rpow_mul hn₀.le,←Real.rpow_natCast _ 5,←Real.rpow_add hn₀]
    norm_num
  apply (h hn hv hbirth hY).trans
  apply (div_le_iff₀ (pow_pos hn₀ 5)).mpr
  have hpos := Real.log_nonneg (by have hv' : (1:ℝ)≤V := by exact_mod_cast hv; linarith : (1:ℝ)≤2*V)
  have hh := mul_le_mul (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (Nat.cast_nonneg V) hfloor 3) hC)
    hlog (by positivity) (by positivity : 0≤C*X^3)
  rw [hscale] at hh
  linarith only [hh,mul_nonneg (mul_nonneg (mul_nonneg hF (zero_le_one.trans hr)) (zero_le_one.trans hL)) (pow_nonneg hn₀.le 5)]

/-- The signed sum through every terminal fragment of the octave costs
thirteen quarters and a single logarithm. -/
theorem sevenFourthsShell_terminal_prefix :
    ∃ C : ℝ, 0≤C ∧ ∀ N M : ℕ, N≤M → M≤2*N →
      |∑ n ∈ Ioc N M, (n:ℝ)^2*sevenFourthsShell n| ≤ C*(N:ℝ)^(13/4:ℝ)*conductorLog N := by
  obtain ⟨C,hC,h⟩ := sevenFourthsShell_bound
  refine ⟨8*C*(2:ℝ)^(1/4:ℝ),by positivity,fun N M hNM hM => ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl|hN
  · have hzero : M=0 := by omega
    simp [hzero,Real.zero_rpow (by norm_num : (13/4:ℝ)≠0)]
  have hN' : (1:ℝ)≤N := by exact_mod_cast hN
  have hN₀ := zero_lt_one.trans_le hN'
  have hL := zero_le_one.trans (conductorLog_one_le N)
  have hrow (n : ℕ) (hn : n ∈ Ioc N M) :
      |(n:ℝ)^2*sevenFourthsShell n|≤(2*(N:ℝ))^2*(C*(2*(N:ℝ))^(1/4:ℝ)*(2*conductorLog N)) := by
    obtain ⟨hl,hu⟩ := mem_Ioc.mp hn
    have hn₀ := hN.trans hl
    have hn' : (0:ℝ)<n := Nat.cast_pos.mpr hn₀
    have h2 : (n:ℝ)≤2*(N:ℝ) := by exact_mod_cast hu.trans hM
    have hlog : conductorLog n≤2*conductorLog N := by
      have hh := Real.log_le_log hn' h2
      rw [Real.log_mul (by norm_num : (2:ℝ)≠0) hN₀.ne'] at hh
      simp only [conductorLog,Real.log_mul (by norm_num : (2:ℝ)≠0) hn'.ne',
        Real.log_mul (by norm_num : (2:ℝ)≠0) hN₀.ne']
      linarith only [hh,Real.log_nonneg hN']
    rw [abs_mul,abs_of_nonneg (sq_nonneg _)]
    exact mul_le_mul (pow_le_pow_left₀ hn'.le h2 2) ((h hn₀).trans (mul_le_mul
      (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hn'.le h2 (by norm_num : (0:ℝ)≤1/4)) hC)
      hlog (zero_le_one.trans (conductorLog_one_le n)) (by positivity))) (abs_nonneg _) (sq_nonneg _)
  apply (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hrow).trans _)
  rw [sum_const,nsmul_eq_mul,Nat.card_Ioc]
  have hcard : ((M-N:ℕ):ℝ)≤N := by exact_mod_cast (show M-N≤N by omega)
  apply (mul_le_mul_of_nonneg_right hcard (by positivity)).trans_eq
  rw [Real.mul_rpow (by norm_num : (0:ℝ)≤2) hN₀.le]
  have hp : (N:ℝ)^(13/4:ℝ)=(N:ℝ)^3*(N:ℝ)^(1/4:ℝ) := by
    rw [←Real.rpow_natCast _ 3,←Real.rpow_add hN₀]; norm_num
  rw [hp]; ring

/-- The requested shell beats the seven-halves benchmark by an explicit
eighth, with all logarithms absorbed. -/
theorem sevenFourthsShell_conductor_saving :
    ∃ C : ℝ, 0≤C ∧ ∀ N M : ℕ, N≤M → M≤2*N →
      |∑ n ∈ Ioc N M, (n:ℝ)^2*sevenFourthsShell n| ≤ C*(N:ℝ)^(7/2-1/8:ℝ) := by
  obtain ⟨C,hC,h⟩ := sevenFourthsShell_terminal_prefix
  obtain ⟨B,hB,hlog⟩ := conductorLog_subpower (by norm_num : (0:ℝ)<1/8)
  refine ⟨C*B,mul_nonneg hC hB,fun N M hN hM => (h N M hN hM).trans ?_⟩
  rcases Nat.eq_zero_or_pos N with rfl|hn
  · simp [Real.zero_rpow (by norm_num : (13/4:ℝ)≠0), Real.zero_rpow (by norm_num : (7/2-1/8:ℝ)≠0)]
  have hh := (le_self_pow₀ (conductorLog_one_le N) (by decide : 6≠0)).trans (hlog hn)
  apply (mul_le_mul_of_nonneg_left hh (by positivity : 0≤C*(N:ℝ)^(13/4:ℝ))).trans_eq
  rw [show (7/2-1/8:ℝ)=13/4+1/8 by norm_num,Real.rpow_add (Nat.cast_pos.mpr hn : (0:ℝ)<N)]
  ring

#print axioms sevenFourthsShell_conductors
#print axioms sevenFourthsShell_bound
#print axioms sevenFourthsShell_terminal_prefix
#print axioms sevenFourthsShell_conductor_saving
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
