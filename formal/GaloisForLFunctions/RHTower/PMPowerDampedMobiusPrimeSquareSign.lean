import GaloisForLFunctions.RHTower.PMPowerDampedMobiusPrimeSquareDecomposition
import GaloisForLFunctions.RHTower.PMPowerDampedMobiusPrimeConvolution
import Mathlib.Analysis.Complex.ExponentialBounds

/-!
# Uniform negative prime-square source

The literal prime core has a negative square-scale slab for every sufficiently
small positive damping. Exact rough inversion, the signed prime convolution
and a square-inclusive semiprime bound retain the complete local source.
No L2-admission or Riemann-hypothesis premise is used.
-/

noncomputable section
open MeasureTheory Set Filter Topology ArithmeticFunction
namespace RHTower

private theorem pmqs_prime_count_log_le_theta {P : ℕ} (hP : 2 ≤ P)
    {Y : ℝ} (hY : (P : ℝ) ≤ Y) :
    (((Finset.Icc P ⌊Y⌋₊).filter Nat.Prime).card : ℝ)*Real.log P ≤
      Chebyshev.theta Y-Chebyshev.theta (P-1 : ℕ) := by
  have hP1 : 1 ≤ P := by omega
  have hP0 : (0 : ℝ) < P := by exact_mod_cast (by omega : 0 < P)
  have hY0 : 0 ≤ Y := hP0.le.trans hY
  have hfloor : P ≤ ⌊Y⌋₊ := (Nat.le_floor_iff hY0).mpr hY
  have hset : (Finset.Ioc (P-1) ⌊Y⌋₊).filter Nat.Prime =
      (Finset.Icc P ⌊Y⌋₊).filter Nat.Prime := by
    ext q
    simp only [Finset.mem_filter,Finset.mem_Ioc,Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hl,hu⟩,hp⟩
      exact ⟨⟨by omega,hu⟩,hp⟩
    · rintro ⟨⟨hl,hu⟩,hp⟩
      exact ⟨⟨by omega,hu⟩,hp⟩
  have hθ := chebyshevTheta_sub_eq_shellSum
    (x := ((P-1 : ℕ) : ℝ)) (y := Y) (by
      rw [Nat.floor_natCast]
      omega)
  rw [Nat.floor_natCast,hset] at hθ
  rw [hθ]
  calc
    _ = ∑ q ∈ (Finset.Icc P ⌊Y⌋₊).filter Nat.Prime,Real.log (P : ℝ) := by simp
    _ ≤ _ := Finset.sum_le_sum fun q hq => by
      have hPq : (P : ℝ) ≤ q := by
        exact_mod_cast (Finset.mem_Icc.mp (Finset.mem_filter.mp hq).1).1
      exact Real.log_le_log hP0 hPq

/-- Uniform prime-count control retaining the lower prime endpoint. -/
theorem pm_prime_square_interval_count {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ P : ℕ in atTop, ∀ y : ℝ, 1 ≤ y →
      (((Finset.Icc P ⌊y*(P : ℝ)⌋₊).filter Nat.Prime).card : ℝ)*
        Real.log P/(P : ℝ) ≤ y-1+δ*(y+1)+1/(P : ℝ) := by
  obtain ⟨R,hR⟩ := eventually_atTop.mp (chebyshevTheta_eventually_relative hδ)
  have hPR := (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (R+1)
  filter_upwards [hPR,eventually_ge_atTop (2 : ℕ)] with P hPR hP
  intro y hy
  have hP1 : 1 ≤ P := by omega
  have hPr : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < P := by linarith
  have hPm : ((P-1 : ℕ) : ℝ) = (P : ℝ)-1 := by
    rw [Nat.cast_sub hP1,Nat.cast_one]
  have hyP : (P : ℝ) ≤ y*(P : ℝ) := by nlinarith
  have hl := hR ((P-1 : ℕ) : ℝ) (by rw [hPm]; linarith)
  have hu := hR (y*(P : ℝ)) (by linarith)
  have hb := pmqs_prime_count_log_le_theta hP hyP
  rw [abs_le] at hl hu
  rw [hPm] at hl hb
  apply (div_le_iff₀ hP0).mpr
  have hRHS : (y-1+δ*(y+1)+1/(P : ℝ))*(P : ℝ) =
      y*(P : ℝ)-(P : ℝ)+δ*(y*(P : ℝ)+(P : ℝ))+1 := by field_simp
  rw [hRHS]
  linarith

private theorem pmqs_mass_normalization {ε P y J : ℝ}
    (hP : 1 < P) (hy : 0 < y) :
    Real.log (y*P^2)^2/(y*P^2)^(1-ε)*((J^2+J)/2*P^(-2*ε)) =
      y^(ε-1)*((J*Real.log P/P)^2+(J*Real.log P/P)*(Real.log P/P))/2*
        (Real.log (y*P^2)/Real.log P)^2 := by
  have hP0 : 0 < P := by linarith
  have hl : Real.log P ≠ 0 := (Real.log_pos hP).ne'
  have hp : P^(-2*ε) ≠ 0 := (Real.rpow_pos_of_pos hP0 _).ne'
  have hyp : y^(1-ε) ≠ 0 := (Real.rpow_pos_of_pos hy _).ne'
  have hpow : (y*P^2)^(1-ε) = y^(1-ε)*P^2*P^(-2*ε) := by
    rw [Real.mul_rpow hy.le (sq_nonneg _),← Real.rpow_natCast_mul hP0.le]
    norm_num only [Nat.cast_ofNat]
    rw [show (2 : ℝ)*(1-ε) = 2+(-2*ε) by ring,
      Real.rpow_add hP0,Real.rpow_two]
    ring
  have hyinv : y^(ε-1) = (y^(1-ε))⁻¹ := by
    rw [show ε-1 = -(1-ε) by ring,Real.rpow_neg hy.le]
  rw [hpow,hyinv]
  field_simp

/-- Uniform sharp upper limit of the square-inclusive rough-composite mass
on the coupled source slab. -/
theorem pmPrimeSquareRoughMass_uniform_upper {ε : ℝ} (hε : 0 ≤ ε)
    {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ P : ℕ in atTop, ∀ y : ℝ, 3/2 ≤ y → y ≤ 7/4 →
      Real.log (y*(P : ℝ)^2)^2/(y*(P : ℝ)^2)^(1-ε)*
        pmPrimeSquareRoughMass ε P (y*(P : ℝ)^2) ≤
        (7/4 : ℝ)^ε*(9/14+δ) := by
  let η := min (δ/12) (1/4 : ℝ)
  have hη : 0 < η := lt_min (by positivity) (by norm_num)
  have hηsmall : η ≤ 1/4 := min_le_right _ _
  have hηδ : 12*η ≤ δ := by have := min_le_left (δ/12) (1/4 : ℝ); dsimp [η]; linarith
  have hnat : Tendsto (fun P : ℕ => (P : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hU : Tendsto (fun P : ℕ => Real.log (P : ℝ)/(P : ℝ)) atTop (𝓝 0) := by
    have h := (Real.tendsto_pow_log_div_mul_add_atTop 1 0 1 one_ne_zero).comp hnat
    simp only [Function.comp_def,one_mul,add_zero,pow_one] at h
    exact h
  have hI : Tendsto (fun P : ℕ => 1/(P : ℝ)) atTop (𝓝 0) := by
    have h := tendsto_inv_atTop_zero.comp hnat
    change Tendsto (fun P : ℕ => (P : ℝ)⁻¹) atTop (𝓝 0) at h
    simpa only [one_div] using h
  have hL := (Real.tendsto_log_atTop.comp hnat).eventually_ge_atTop
    (Real.log (7/4 : ℝ)/η)
  filter_upwards [pm_prime_square_interval_count (by positivity : 0 < η/4),
    hU.eventually (gt_mem_nhds hη),hI.eventually (gt_mem_nhds (by positivity : 0 < η/4)),
    hL,eventually_ge_atTop (2 : ℕ)] with P hcount hU hI hL hP
  intro y hy hyhi
  have hPr : (2 : ℝ) ≤ P := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < P := by linarith
  have hlP : 0 < Real.log (P : ℝ) := Real.log_pos (by linarith)
  have hy0 : 0 < y := by linarith
  let J : ℝ := ((Finset.Icc P ⌊y*(P : ℝ)⌋₊).filter Nat.Prime).card
  let T : ℝ := J*Real.log P/(P : ℝ)
  let U : ℝ := Real.log (P : ℝ)/(P : ℝ)
  let L : ℝ := Real.log (y*(P : ℝ)^2)/Real.log P
  have hJ : 0 ≤ J := Nat.cast_nonneg _
  have hT : 0 ≤ T := by dsimp [T]; positivity
  have hUn : 0 ≤ U := by dsimp [U]; positivity
  have hUb : U ≤ η := hU.le
  have hTb : T ≤ y-1+η := by
    have hc := hcount y (by linarith)
    change T ≤ _ at hc
    have hprod := mul_le_mul_of_nonneg_left (by linarith : y+1 ≤ 3) (by positivity : 0 ≤ η/4)
    linarith
  have hT1 : T ≤ 1 := by linarith
  have hlog : Real.log (y*(P : ℝ)^2) = Real.log y+2*Real.log P := by
    rw [Real.log_mul hy0.ne' (pow_pos hP0 2).ne',Real.log_pow]
    norm_num
  have hlogy : Real.log y ≤ Real.log (7/4 : ℝ) := Real.log_le_log hy0 hyhi
  have hLη : Real.log (7/4 : ℝ) ≤ η*Real.log P := by
    change Real.log (7/4 : ℝ)/η ≤ Real.log P at hL
    have hh := (div_le_iff₀ hη).mp hL
    linarith only [hh]
  have hLn : 0 ≤ L := by
    dsimp [L]
    rw [hlog]
    have hylog := Real.log_nonneg (by linarith only [hy] : 1 ≤ y)
    exact div_nonneg (by linarith only [hylog,hlP]) hlP.le
  have hLb : L ≤ 2+η := by
    apply (div_le_iff₀ hlP).mpr
    rw [hlog]
    nlinarith only [hLη,hlogy]
  have hLsq : L^2 ≤ 4+6*η := by
    have hh := (sq_le_sq₀ hLn (by positivity : 0 ≤ 2+η)).mpr hLb
    nlinarith only [hh,hηsmall,hη.le]
  have hTsq : T^2 ≤ (y-1)^2+2*η := by
    have hh := (sq_le_sq₀ hT (by linarith only [hy,hη] : 0 ≤ y-1+η)).mpr hTb
    have hhη := mul_le_mul_of_nonneg_left hyhi hη.le
    nlinarith only [hh,hhη,hηsmall,hη.le]
  have hTU : T*U ≤ η := by
    have hh := mul_le_mul hT1 hUb hUn (by norm_num : (0 : ℝ) ≤ 1)
    simpa only [one_mul] using hh
  have hBsq : (y-1)^2 ≤ 1 := by nlinarith only [hy,hyhi]
  have hprod : (T^2+T*U)/2*L^2 ≤ 2*(y-1)^2+12*η := by
    calc
      _ ≤ ((y-1)^2+3*η)/2*(4+6*η) :=
        mul_le_mul (by linarith only [hTsq,hTU]) hLsq (sq_nonneg L) (by positivity)
      _ ≤ _ := by
        have hh := mul_le_mul_of_nonneg_left hBsq hη.le
        nlinarith only [hh,hη.le,hηsmall]
  have hpoly : (2*(y-1)^2+12*η)/y ≤ 9/14+12*η := by
    apply (div_le_iff₀ hy0).mpr
    have hh := mul_nonpos_of_nonpos_of_nonneg (by linarith : y-7/4 ≤ 0)
      (by linarith : 0 ≤ y-4/7)
    have hhη := mul_le_mul_of_nonneg_left (by linarith only [hy] : 1 ≤ y) hη.le
    nlinarith only [hh,hhη]
  have hypow : y^(ε-1) ≤ (7/4 : ℝ)^ε/y := by
    rw [Real.rpow_sub hy0,Real.rpow_one]
    exact div_le_div_of_nonneg_right (Real.rpow_le_rpow hy0.le hyhi hε) hy0.le
  have hm := pmPrimeSquareRoughMass_le_prime_pairs hε hP
    (X := y*(P : ℝ)^2) (by
      have hh := mul_le_mul_of_nonneg_right (by linarith only [hy] : 1 ≤ y) (sq_nonneg (P : ℝ))
      simpa only [one_mul] using hh)
    (mul_lt_mul_of_pos_right (by linarith only [hyhi] : y < 2) (sq_pos_of_pos hP0))
  have hcancel : y*(P : ℝ)^2/(P : ℝ) = y*(P : ℝ) := by field_simp
  rw [hcancel] at hm
  change pmPrimeSquareRoughMass ε P (y*(P : ℝ)^2) ≤ (J^2+J)/2*(P : ℝ)^(-2*ε) at hm
  calc
    _ ≤ Real.log (y*(P : ℝ)^2)^2/(y*(P : ℝ)^2)^(1-ε)*
        ((J^2+J)/2*(P : ℝ)^(-2*ε)) := mul_le_mul_of_nonneg_left hm (by positivity)
    _ = y^(ε-1)*((T^2+T*U)/2*L^2) := by
      rw [pmqs_mass_normalization (by linarith : (1 : ℝ) < P) hy0]
      dsimp [T,U,L]
      ring
    _ ≤ ((7/4 : ℝ)^ε/y)*(2*(y-1)^2+12*η) :=
      mul_le_mul hypow hprod (by positivity) (by positivity)
    _ = (7/4 : ℝ)^ε*((2*(y-1)^2+12*η)/y) := by ring
    _ ≤ (7/4 : ℝ)^ε*(9/14+12*η) := mul_le_mul_of_nonneg_left hpoly (by positivity)
    _ ≤ _ := mul_le_mul_of_nonneg_left (by linarith) (by positivity)

private theorem pmqs_full_source_negligible {ε : ℝ} (hε : 0 < ε)
    (hεhalf : ε < 1/2) {δ : ℝ} (hδ : 0 < δ) :
    ∀ᶠ X : ℝ in atTop,
      Real.log X^2/X^(1-ε)*‖pmPowerDampedFermiSource ε (1/X)‖ < δ := by
  obtain ⟨C,hC,hbound⟩ := pmPowerDampedFermiSource_reciprocal_eventually_log_four hε hεhalf
  have hlog : Tendsto (fun X : ℝ => Real.log X^2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp Real.tendsto_log_atTop
  have hlim : Tendsto (fun X : ℝ => C/Real.log X^2) atTop (𝓝 0) := by
    have h := (tendsto_inv_atTop_zero.comp hlog).const_mul C
    simpa only [Function.comp_def,mul_zero,div_eq_mul_inv] using h
  filter_upwards [hbound,hlim.eventually (gt_mem_nhds hδ),eventually_gt_atTop (1 : ℝ)]
    with X hb hδX hX
  have hX0 : 0 < X := by linarith only [hX]
  have hl : Real.log X ≠ 0 := (Real.log_pos hX).ne'
  have hp : X^(1-ε) ≠ 0 := (Real.rpow_pos_of_pos hX0 _).ne'
  calc
    _ ≤ Real.log X^2/X^(1-ε)*(C*X^(1-ε)/Real.log X^4) :=
      mul_le_mul_of_nonneg_left hb (by positivity)
    _ = C/Real.log X^2 := by field_simp
    _ < δ := hδX

private theorem pmqs_decomposition_re (ε : ℝ) {P : ℕ} (hP : 2 ≤ P)
    {X : ℝ} (hPX : (P : ℝ)^2 ≤ X) (hXP : X < 2*(P : ℝ)^2) :
    (pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (P-1)) ε (1/X)).re =
      (pmPowerDampedFermiSource ε (1/X)).re+
      pmPowerDampedPrimeConvolution ε ((P-1 : ℕ) : ℝ) X+pmPrimeSquareRoughMass ε P X := by
  classical
  have hP1 : 1 ≤ P := by omega
  have hset : Finset.Ioc (P-1) ⌊X⌋₊ = Finset.Icc P ⌊X⌋₊ := by
    ext q
    simp only [Finset.mem_Ioc,Finset.mem_Icc]
    constructor <;> rintro ⟨hl,hu⟩ <;> exact ⟨by omega,hu⟩
  have hprime :
      (∑ q ∈ Finset.Icc 1 ⌊X⌋₊,
        if q.Prime ∧ P ≤ q then (((q : ℝ)^(-ε) : ℝ) : ℂ)*
          pmPowerDampedFermiSource ε ((q : ℝ)/X) else 0).re =
        pmPowerDampedPrimeConvolution ε ((P-1 : ℕ) : ℝ) X := by
    simp only [Complex.re_sum,apply_ite,Complex.mul_re,Complex.ofReal_re,
      Complex.ofReal_im,zero_mul,sub_zero,Complex.zero_re,
      pmPowerDampedPrimeConvolution,Nat.floor_natCast,hset]
    have hs : Finset.Icc P ⌊X⌋₊ ⊆ Finset.Icc 1 ⌊X⌋₊ := by
      intro q hq
      obtain ⟨hl,hu⟩ := Finset.mem_Icc.mp hq
      exact Finset.mem_Icc.mpr ⟨hP1.trans hl,hu⟩
    rw [← Finset.sum_subset hs (fun q hq hn => by
      have hqP : ¬P ≤ q := by
        intro hh
        exact hn (Finset.mem_Icc.mpr ⟨hh,(Finset.mem_Icc.mp hq).2⟩)
      simp [hqP])]
    apply Finset.sum_congr rfl
    intro q hq
    have hPq := (Finset.mem_Icc.mp hq).1
    simp [hPq]
  have hd := congrArg Complex.re
    (pmFinitePrimePowerDampedFermiSource_prime_square_decomposition ε hP hPX hXP)
  simpa only [Complex.add_re,Complex.ofReal_re,hprime] using hd

private theorem pmqs_boundary_jet_gap :
    ∀ᶠ ε : ℝ in 𝓝[>] 0,
      (7/4 : ℝ)^ε*(2/3) < (pmPowerDampedBoundaryJet ε).re := by
  have hr : Tendsto (fun ε => (pmPowerDampedBoundaryJet ε).re) (𝓝[>] (0 : ℝ))
      (𝓝 (Real.log 2)) := by
    have h := Complex.continuous_re.continuousAt.tendsto.comp tendsto_pmPowerDampedBoundaryJet_zero
    simpa only [Function.comp_def,Complex.ofReal_re] using h
  have hc : Continuous (fun ε : ℝ => Real.exp (ε*Real.log (7/4 : ℝ))) := by fun_prop
  have ht : Tendsto (fun ε : ℝ => (7/4 : ℝ)^ε) (𝓝[>] 0) (𝓝 1) := by
    have h : Tendsto (fun ε : ℝ => Real.exp (ε*Real.log (7/4 : ℝ)))
        (𝓝[>] 0) (𝓝 (Real.exp (0*Real.log (7/4 : ℝ)))) :=
      (hc.tendsto 0).mono_left nhdsWithin_le_nhds
    simpa only [zero_mul,Real.exp_zero,Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 7/4),mul_comm] using h
  have hd := hr.sub (ht.mul_const (2/3 : ℝ))
  have hlog : (0 : ℝ) < Real.log 2-1*(2/3) := by linarith [Real.log_two_gt_d9]
  filter_upwards [hd.eventually (lt_mem_nhds hlog)] with ε hε
  linarith only [hε]

/-- For every sufficiently small positive damping parameter, the actual
canonical prime core has uniform negative mass on the coupled square slab. -/
theorem pmFinitePrimePowerDampedFermiSource_prime_square_negative :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, ∃ c : ℝ, 0 < c ∧
      ∀ᶠ P : ℕ in atTop, ∀ y : ℝ, 3/2 ≤ y → y ≤ 7/4 →
        (pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (P-1)) ε
          (1/(y*(P : ℝ)^2))).re ≤
          -c*(y*(P : ℝ)^2)^(1-ε)/Real.log (y*(P : ℝ)^2)^2 := by
  filter_upwards [pmqs_boundary_jet_gap,Ioo_mem_nhdsGT (by norm_num : (0 : ℝ) < 1/2)]
    with ε hjet hε
  let C : ℝ := (7/4 : ℝ)^ε
  have hC : 0 < C := Real.rpow_pos_of_pos (by norm_num) _
  let c : ℝ := C/168
  have hc : 0 < c := by dsimp [c]; positivity
  obtain ⟨R,hR⟩ := eventually_atTop.mp
    (pmPowerDampedFermiSource_prime_convolution_asymptotic hε.1 hε.2 c hc)
  obtain ⟨S,hS⟩ := eventually_atTop.mp (pmqs_full_source_negligible hε.1 hε.2 hc)
  have hnat : Tendsto (fun P : ℕ => (P : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  refine ⟨c,hc,?_⟩
  filter_upwards [pmPrimeSquareRoughMass_uniform_upper hε.1.le (by norm_num : (0 : ℝ) < 1/168),
    hnat.eventually_ge_atTop (max R S),eventually_ge_atTop (8 : ℕ)] with P hm hlarge hP
  intro y hy hyhi
  have hPr : (8 : ℝ) ≤ P := by exact_mod_cast hP
  have hP0 : (0 : ℝ) < P := by linarith only [hPr]
  have hP1 : 1 ≤ P := by omega
  have hPm : ((P-1 : ℕ) : ℝ) = (P : ℝ)-1 := by rw [Nat.cast_sub hP1,Nat.cast_one]
  let X : ℝ := y*(P : ℝ)^2
  have hPX : (P : ℝ)^2 ≤ X := by
    have hh := mul_le_mul_of_nonneg_right (by linarith only [hy] : 1 ≤ y) (sq_nonneg (P : ℝ))
    simpa only [one_mul] using hh
  have hXP : X < 2*(P : ℝ)^2 :=
    mul_lt_mul_of_pos_right (by linarith only [hyhi] : y < 2) (sq_pos_of_pos hP0)
  have hXhi : X ≤ 7/4*(P : ℝ)^2 := mul_le_mul_of_nonneg_right hyhi (sq_nonneg _)
  have hPX' : (P : ℝ) ≤ X := by nlinarith only [hPr,hPX]
  have hX1 : 1 < X := by linarith only [hPr,hPX']
  have hX0 : 0 < X := by linarith only [hX1]
  have hroot : Real.sqrt X ≤ 3/2*(P : ℝ) :=
    Real.sqrt_le_iff.mpr ⟨by positivity,by nlinarith only [hXhi,sq_nonneg (P : ℝ)]⟩
  have hlo : Real.sqrt X/2 ≤ ((P-1 : ℕ) : ℝ) := by
    rw [hPm]
    nlinarith only [hroot,hPr]
  have hhi : ((P-1 : ℕ) : ℝ) ≤ Real.sqrt X := by
    rw [hPm]
    have hh := Real.le_sqrt_of_sq_le hPX
    linarith only [hh]
  have hXR : R ≤ X := (le_max_left R S).trans (hlarge.trans hPX')
  have hXS : S ≤ X := (le_max_right R S).trans (hlarge.trans hPX')
  have hp := (abs_lt.mp (hR X hXR ((P-1 : ℕ) : ℝ) hlo hhi)).2
  have hs := hS X hXS
  have hm' := hm y hy hyhi
  change Real.log X^2/X^(1-ε)*pmPrimeSquareRoughMass ε P X ≤ C*(9/14+1/168) at hm'
  have hn : 0 < Real.log X^2/X^(1-ε) := by
    exact div_pos (sq_pos_of_pos (Real.log_pos hX1)) (Real.rpow_pos_of_pos hX0 _)
  have hsource : Real.log X^2/X^(1-ε)*(pmPowerDampedFermiSource ε (1/X)).re < c :=
    (mul_le_mul_of_nonneg_left (Complex.re_le_norm _) hn.le).trans_lt hs
  have hnorm : Real.log X^2/X^(1-ε)*
      (pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (P-1)) ε (1/X)).re ≤ -c := by
    rw [pmqs_decomposition_re ε (by omega) hPX hXP]
    dsimp only [c] at hp hsource ⊢
    change C*(2/3) < (pmPowerDampedBoundaryJet ε).re at hjet
    nlinarith only [hp,hsource,hm',hjet]
  have he := (le_div_iff₀ hn).mpr (by simpa only [mul_comm] using hnorm)
  have hpX : X^(1-ε) ≠ 0 := (Real.rpow_pos_of_pos hX0 _).ne'
  have hlX : Real.log X ≠ 0 := (Real.log_pos hX1).ne'
  change (pmFinitePrimePowerDampedFermiSource (mobiusFinitePrimeAperture (P-1)) ε (1/X)).re ≤
    -c*X^(1-ε)/Real.log X^2
  exact he.trans_eq (by field_simp)

end RHTower
