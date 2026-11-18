import GaloisForLFunctions.CountingHolography.Sections.IntegerRoundingOfCumulativeConductorWeights
import GaloisForLFunctions.CountingHolography.Sections.TheThetaWeightOfEachSquareConductor
import GaloisForLFunctions.CountingHolography.Sections.VariationOfTheSignedSquareGeneratorReading

/-!
# Integer products containing every conductor in a dyadic band

Theta assigns a bounded positive real exponent to every central conductor.
Integer prefix rounding preserves its signed cancellation at the natural
cubic scale because the leading spectral reading has subcubic variation.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology MeasureTheory Finset _root_.RHTower

private abbrev phi := thetaCuspFullSource
private abbrev T (N : ℕ) := 2*Real.log N
private abbrev F (N : ℕ) (x : ℝ) := phi x*squareLongTrace (T N+x)
private abbrev f (i : ℕ) := squareLongTrace (2*Real.log ((i:ℝ)+2))

/-- Finite conductor cutoff at scale N. Cell i represents conductor i+2. -/
def squareThetaCutoff (N : ℕ) := ⌈(N:ℝ)^(17/16:ℝ)⌉₊

/-- Integer exponent depending only on theta and the conductor cell. -/
def squareThetaExponent (A : ℝ) (N i : ℕ) := cumulativeWeightMultiplicity (conductorThetaWeight A N) i

/-- The actual rational product of the original diagonal ordinary generators. -/
def thetaSquareGeneratorProduct (A : ℝ) (N : ℕ) : ℚ :=
  ∏ i ∈ range (squareThetaCutoff N),
    ordinaryPrimeGenerator ((i+2) • successorSquareTriple (i+2))^(squareThetaExponent A N i)

private theorem integrable_phi : Integrable phi := by
  simpa only [zero_mul,Real.exp_zero,one_mul] using HedenmalmThetaSource.integrable_exp_abs_mul_thetaCuspFullSource 0

/-- Replacing the trace by the value at its upper integer root costs
at most a constant times the theta mass of the cell. -/
private theorem cell_trace_error : ∃ C : ℝ, 0 ≤ C ∧ ∀ N i : ℕ,
    |conductorThetaMass N i*f i-∫ x in conductorThetaCell N i, F N x| ≤ C*conductorThetaMass N i := by
  obtain ⟨C,hC,h⟩ := squareLongTrace_unit_root_step
  refine ⟨C,hC,fun N i => ?_⟩
  let S := conductorThetaCell N i
  have hnear (x : ℝ) (hx : x ∈ S) : |f i-squareLongTrace (T N+x)| ≤ C := by
    let y := Real.exp ((T N+x)/2)
    have hy := Real.exp_pos ((T N+x)/2)
    have hj : (0:ℝ)<(i:ℝ)+1 := by positivity
    have hj' : (0:ℝ)<(i:ℝ)+2 := by positivity
    change 2*Real.log ((i:ℝ)+1)-T N < x ∧ x ≤ 2*Real.log ((i:ℝ)+2)-T N at hx
    have hl : (i:ℝ)+1 ≤ y := by
      rw [← Real.exp_log hj]
      exact Real.exp_le_exp.mpr (by linarith only [hx.1])
    have hu : y ≤ (i:ℝ)+2 := by
      rw [← Real.exp_log hj']; exact Real.exp_le_exp.mpr (by linarith only [hx.2])
    have hy₁ := (le_add_of_nonneg_left (Nat.cast_nonneg (α := ℝ) i) : 1 ≤ (i:ℝ)+1).trans hl
    have hh := h hy₁ hu (show (i:ℝ)+2 ≤ y+1 by linarith only [hl])
    have he : 2*Real.log y=T N+x := by dsimp only [y]; rw [Real.log_exp]; ring
    rw [he] at hh
    have hp := Real.rpow_le_rpow_of_exponent_le hy₁ (by norm_num : (-(1/4):ℝ) ≤ 0)
    rw [Real.rpow_zero] at hp
    exact hh.trans (mul_le_of_le_one_right hC hp)
  have hfi := (thetaMean_squareLongTrace (T N)).1
  have hdiff : Integrable (fun x : ℝ => phi x*f i-F N x) := (integrable_phi.mul_const _).sub hfi
  change |(∫ x in S,phi x)*f i-(∫ x in S,F N x)| ≤ C*(∫ x in S,phi x)
  rw [← integral_mul_const,← integral_sub (integrable_phi.mul_const _).integrableOn hfi.integrableOn,← integral_const_mul]
  refine (abs_integral_le_integral_abs (μ := volume.restrict S)).trans (setIntegral_mono_on hdiff.abs.integrableOn
    (integrable_phi.const_mul C).integrableOn measurableSet_Ioc ?_)
  intro x hx
  change |phi x*f i-phi x*squareLongTrace (T N+x)| ≤ C*phi x
  rw [← mul_sub,abs_mul,abs_of_pos (thetaCuspFullSource_pos x),mul_comm C]
  exact mul_le_mul_of_nonneg_left (hnear x hx) (thetaCuspFullSource_pos x).le

/-- The window omitted beyond the arithmetic cutoff pays an absolute
amount. On its right tail log N is at most eight times the displacement. -/
private theorem clipped_trace_bound : ∃ D : ℝ, ∀ {N : ℕ}, 0 < N →
    |∫ x in Set.Ioc (conductorThetaEdge N 0) (conductorThetaEdge N (squareThetaCutoff N)), F N x| ≤ D := by
  obtain ⟨A,hA,hF⟩ := squareLongTrace_bound
  let g := fun x : ℝ => A*(Real.exp ((17/2)*|x|)*phi x)
  have hg : Integrable g := (HedenmalmThetaSource.integrable_exp_abs_mul_thetaCuspFullSource (17/2)).const_mul A
  refine ⟨∫ x : ℝ,g x,fun {N} hn => ?_⟩
  let M := squareThetaCutoff N
  let S := Set.Ioc (conductorThetaEdge N 0) (conductorThetaEdge N M)
  have hn₀ : (0:ℝ) < N := Nat.cast_pos.mpr hn
  have hlog := Real.log_natCast_nonneg N
  have hhi : Real.log N/8 ≤ conductorThetaEdge N M := by
    have hm : (N:ℝ)^(17/16:ℝ) ≤ (M:ℝ)+1 := (Nat.le_ceil _).trans (le_add_of_nonneg_right zero_le_one)
    have h := Real.log_le_log (Real.rpow_pos_of_pos hn₀ _) hm
    rw [Real.log_rpow hn₀] at h
    dsimp only [conductorThetaEdge]; linarith only [h]
  have hbound (x : ℝ) (hx : x ∈ Sᶜ) : |F N x| ≤ g x := by
    have he : 1/2*|T N+x| ≤ 17/2*|x| := by
      rcases le_or_gt x (conductorThetaEdge N 0) with hleft | hleft
      · have hu : x ≤ -(2*Real.log N) := by simpa [conductorThetaEdge] using hleft
        rw [abs_of_nonpos (by dsimp only [T]; linarith only [hu] : T N+x ≤ 0),
          abs_of_nonpos (by linarith only [hu,hlog] : x ≤ 0)]
        dsimp only [T]; linarith only [hlog,hu]
      · have hr := lt_of_not_ge fun hh => hx (show x ∈ S from ⟨hleft,hh⟩)
        have hx₀ : 0 ≤ x := by linarith only [hhi,hr,hlog]
        rw [abs_of_nonneg (by dsimp only [T]; linarith : 0 ≤ T N+x),abs_of_nonneg hx₀]
        dsimp only [T]; linarith only [hhi,hr]
    have h := (hF (T N+x)).trans (mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr he) hA)
    dsimp only [F,g]
    rw [abs_mul,abs_of_pos (thetaCuspFullSource_pos x)]
    exact (mul_le_mul_of_nonneg_left h (thetaCuspFullSource_pos x).le).trans_eq (by ring)
  obtain ⟨hi,he⟩ := thetaMean_squareLongTrace (T N)
  have hh := integral_add_compl (s := S) measurableSet_Ioc hi
  rw [he] at hh
  have hd : (∫ x in S,F N x)= -(∫ x in Sᶜ,F N x) := by
    change (∫ x in S,F N x)+(∫ x in Sᶜ,F N x)=0 at hh
    linarith only [hh]
  change |∫ x in S,F N x| ≤ _
  rw [hd,abs_neg]
  refine (abs_integral_le_integral_abs (μ := volume.restrict Sᶜ)).trans ((setIntegral_mono_on hi.abs.integrableOn hg.integrableOn
    measurableSet_Ioc.compl hbound).trans ?_)
  exact setIntegral_le_integral hg (ae_of_all _ fun x => mul_nonneg hA
    (mul_nonneg (Real.exp_pos _).le (thetaCuspFullSource_pos x).le))

private theorem real_weight_trace_bound : ∃ D : ℝ, 0 ≤ D ∧ ∀ {N : ℕ}, 0 < N →
    |∑ i ∈ range (squareThetaCutoff N), conductorThetaMass N i*f i| ≤ D := by
  obtain ⟨C,hC,h⟩ := cell_trace_error
  obtain ⟨E,hE⟩ := clipped_trace_bound
  refine ⟨C*|∫ x : ℝ,phi x|+|E|,by positivity,fun {N} hn => ?_⟩
  let M := squareThetaCutoff N
  let v := fun i : ℕ => ∫ x in conductorThetaCell N i,F N x
  have hsum : |∑ i ∈ range M,(conductorThetaMass N i*f i-v i)| ≤ C*|∫ x : ℝ,phi x| := by
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum (fun i _ => h N i)).trans ?_)
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left ((sum_conductorThetaMass_le N M).trans (le_abs_self _)) hC
  have hv : |∑ i ∈ range M,v i| ≤ |E| := by
    dsimp only [v]
    rw [integral_over_conductorThetaCells N M (thetaMean_squareLongTrace _).1]
    exact (hE hn).trans (le_abs_self _)
  rw [sum_sub_distrib] at hsum
  have htriangle := abs_add_le ((∑ i ∈ range M,conductorThetaMass N i*f i)-∑ i ∈ range M,v i) (∑ i ∈ range M,v i)
  rw [sub_add_cancel] at htriangle
  exact htriangle.trans (add_le_add hsum hv)

private theorem cutoff_growth {N : ℕ} (hn : 0 < N) :
    ((squareThetaCutoff N:ℝ)+2)^(11/4:ℝ) ≤ (4:ℝ)^(11/4:ℝ)*(N:ℝ)^3 := by
  have hn₁ : 1 ≤ (N:ℝ) := by exact_mod_cast hn
  have hn₀ : 0 < (N:ℝ) := Nat.cast_pos.mpr hn
  let z := (N:ℝ)^(17/16:ℝ)
  have hz : 1 ≤ z := Real.one_le_rpow hn₁ (by norm_num)
  have hm : (squareThetaCutoff N:ℝ) ≤ z+1 := (Nat.ceil_lt_add_one (zero_le_one.trans hz)).le
  have h := Real.rpow_le_rpow (by positivity : 0 ≤ (squareThetaCutoff N:ℝ)+2)
    (show (squareThetaCutoff N:ℝ)+2 ≤ 4*z by linarith only [hm,hz]) (by norm_num : (0:ℝ) ≤ 11/4)
  rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 4) (zero_le_one.trans hz)] at h
  refine h.trans (mul_le_mul_of_nonneg_left ?_ (by positivity))
  dsimp only [z]
  rw [← Real.rpow_mul hn₀.le]
  exact (Real.rpow_le_rpow_of_exponent_le hn₁ (by norm_num : (17/16:ℝ)*(11/4) ≤ 3)).trans_eq (by norm_num)

private theorem actual_product_log (A : ℝ) (N : ℕ) :
    Real.log (thetaSquareGeneratorProduct A N:ℝ)=
      ∑ i ∈ range (squareThetaCutoff N),(squareThetaExponent A N i:ℝ)*diagonalOrdinaryLog (i+2) := by
  unfold thetaSquareGeneratorProduct diagonalOrdinaryLog
  push_cast
  rw [Real.log_prod]
  · simp only [Real.log_pow]
  · intro i _
    apply pow_ne_zero
    exact ne_of_gt (by exact_mod_cast (show (0:ℚ)<ordinaryPrimeGenerator ((i+2) • successorSquareTriple (i+2))
      from prod_pos fun k _ => zpow_pos (Nat.cast_pos.mpr (contactBase_pos k)) _))

private theorem square_cost_variation (M : ℕ) :
    let c := fun i : ℕ => ((i:ℝ)+2)^2
    |c M|+∑ i ∈ range M, |c (i+1)-c i| ≤ 2*((M:ℝ)+2)^(11/4:ℝ) := by
  let c := fun i : ℕ => ((i:ℝ)+2)^2
  have hc (i : ℕ) : c i ≤ c (i+1) := by
    apply pow_le_pow_left₀ (by positivity); exact add_le_add (Nat.cast_le.mpr (Nat.le_succ i)) le_rfl
  change |c M|+(∑ i ∈ range M, |c (i+1)-c i|) ≤ _
  simp_rw [abs_of_nonneg (sub_nonneg.mpr (hc _))]
  rw [abs_of_nonneg (sq_nonneg _),sum_range_sub]
  have he : ((M:ℝ)+2)^2 ≤ ((M:ℝ)+2)^(11/4:ℝ) := by
    simpa only [Real.rpow_two] using Real.rpow_le_rpow_of_exponent_le
      (show 1 ≤ (M:ℝ)+2 by linarith only [Nat.cast_nonneg (α := ℝ) M]) (by norm_num : (2:ℝ) ≤ 11/4)
  dsimp only [c]
  linarith only [he]

/-- The centered real weights have bounded signed source price; integer
rounding charges total variation and the bounded quadratic corrections. -/
private theorem cubic_log_product_bound {A : ℝ} (hA : 0 < A) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N : ℕ}, 2 ≤ N → |Real.log (thetaSquareGeneratorProduct A N:ℝ)| ≤ C*(N:ℝ)^3 := by
  obtain ⟨D,hD,hmean⟩ := real_weight_trace_bound
  obtain ⟨V,hV,hvar⟩ := squareLongReading_variation
  obtain ⟨E,hE,herr⟩ := diagonalOrdinaryLog_smooth_error
  let Z := (4:ℝ)^(11/4:ℝ)
  let H := ∫ x : ℝ,phi x
  let C := A*D+V*Z+E*(A*|H|+2*Z)
  refine ⟨C,by dsimp only [C,Z]; positivity,fun {N} hn => ?_⟩
  have hn₀ : 0 < N := by omega
  let M := squareThetaCutoff N
  let S := range M
  let w := conductorThetaWeight A N
  let k := fun i => (squareThetaExponent A N i:ℝ)
  let g := fun i => squareLongReading (i+2)
  let c := fun i : ℕ => ((i:ℝ)+2)^2
  have hw (i : ℕ) : 0 ≤ w i := by
    have := conductorThetaMass_nonneg N i
    dsimp only [w,conductorThetaWeight]; positivity
  have hk (i : ℕ) : 0 ≤ k i := Nat.cast_nonneg _
  have hweight (i : ℕ) : w i*c i = A*(N:ℝ)^3*conductorThetaMass N i := by
    dsimp only [w,c,conductorThetaWeight]
    exact div_mul_cancel₀ _ (sq_pos_of_pos (by positivity)).ne'
  have hquad : (∑ i ∈ S,w i*c i) ≤ (A*(N:ℝ)^3)*|H| := by
    simp_rw [hweight]
    rw [← mul_sum]
    exact mul_le_mul_of_nonneg_left ((sum_conductorThetaMass_le N M).trans (le_abs_self H)) (by positivity)
  have hraw : |∑ i ∈ S,w i*g i| ≤ A*D*(N:ℝ)^3 := by
    have hr (i : ℕ) : w i*g i=A*(N:ℝ)^3*(conductorThetaMass N i*f i) := by
      change w i*((((i+2:ℕ):ℝ))^2*squareLongTrace (2*Real.log (i+2:ℕ)))=_
      push_cast
      change w i*(c i*f i)=_
      rw [← mul_assoc,hweight]; ring
    simp_rw [hr]
    rw [← mul_sum,abs_mul,abs_of_nonneg (by positivity : 0 ≤ A*(N:ℝ)^3)]
    exact (mul_le_mul_of_nonneg_left (hmean hn₀) (by positivity)).trans_eq (by ring)
  have hkg : |(∑ i ∈ S,k i*g i)-(∑ i ∈ S,w i*g i)| ≤ V*Z*(N:ℝ)^3 := by
    rw [← sum_sub_distrib]
    simp_rw [← sub_mul]
    exact ((cumulativeWeightMultiplicity_reading_error hw g M).trans (hvar M)).trans
      ((mul_le_mul_of_nonneg_left (cutoff_growth hn₀) hV).trans_eq (by ring))
  have hkc : (∑ i ∈ S,k i*c i) ≤ (A*|H|+2*Z)*(N:ℝ)^3 := by
    have hh := (cumulativeWeightMultiplicity_reading_error hw c M).trans (square_cost_variation M)
    change |∑ i ∈ S,(k i-w i)*c i| ≤ _ at hh
    simp_rw [sub_mul] at hh
    rw [sum_sub_distrib] at hh
    linarith only [(abs_le.mp hh).2,hquad,cutoff_growth hn₀]
  have hprice : |∑ i ∈ S,k i*(diagonalOrdinaryLog (i+2)+g i)| ≤ E*((A*|H|+2*Z)*(N:ℝ)^3) := by
    refine (abs_sum_le_sum_abs _ _).trans (le_trans (b := ∑ i ∈ S,E*(k i*c i)) (sum_le_sum (fun i _ => ?_)) ?_)
    · rw [abs_mul,abs_of_nonneg (hk i)]
      have h := herr (show 0 < i+2 by omega)
      push_cast at h
      exact (mul_le_mul_of_nonneg_left h (hk i)).trans_eq (by dsimp only [c]; ring)
    · rw [← mul_sum]; exact mul_le_mul_of_nonneg_left hkc hE
  dsimp only [C]
  rw [actual_product_log]
  change |∑ i ∈ S,k i*diagonalOrdinaryLog (i+2)| ≤ _
  simp_rw [mul_add] at hprice
  rw [sum_add_distrib] at hprice
  rw [abs_le] at hraw hkg hprice ⊢
  constructor <;> linarith only [hraw.1,hraw.2,hkg.1,hkg.2,hprice.1,hprice.2]

/-- At every sufficiently large scale a rational product contains every
diagonal generator in [N,2N], each conductor occurs a bounded number of
times, and its signed logarithm lies in a fixed cubic allowance. The
integer exponents depend only on theta and the scale. -/
theorem actual_square_generator_products_at_every_scale :
    ∃ (A C : ℝ) (K : ℕ), 0 < A ∧ 0 ≤ C ∧ ∀ᶠ N : ℕ in atTop,
      |Real.log (thetaSquareGeneratorProduct A N:ℝ)| ≤ C*(N:ℝ)^3 ∧
      (∀ i : ℕ, squareThetaExponent A N i ≤ K) ∧
      ∀ i : ℕ, N ≤ i+2 → i+2 ≤ 2*N → i < squareThetaCutoff N ∧ 0 < squareThetaExponent A N i := by
  obtain ⟨A,K,hA,h⟩ := square_conductor_theta_weight_bounds
  obtain ⟨C,hC,hcost⟩ := cubic_log_product_bound hA
  have ht := (tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/16)).comp tendsto_natCast_atTop_atTop
  refine ⟨A,C,K,hA,hC,?_⟩
  filter_upwards [eventually_ge_atTop 2,ht.eventually_ge_atTop 2] with N hn hp
  have hw (i : ℕ) := h hn i
  have hr (i : ℕ) (k : ℕ) (hk : (k:ℝ) ≤ conductorThetaWeight A N i) :=
    cumulativeWeightMultiplicity_interval (fun i => (hw i).1) i k K hk (hw i).2.1
  refine ⟨hcost hn,fun i => (hr i 0 (by simpa only [Nat.cast_zero] using (hw i).1)).2,fun i hl hu => ⟨?_,?_⟩⟩
  · have hn₀ : (0:ℝ) < N := Nat.cast_pos.mpr (by omega)
    have hm : 2*(N:ℝ) ≤ (squareThetaCutoff N:ℝ) := by
      refine le_trans ?_ (Nat.le_ceil _)
      rw [show (17/16:ℝ)=1/16+1 by norm_num,Real.rpow_add hn₀,Real.rpow_one]
      exact mul_le_mul_of_nonneg_right hp hn₀.le
    have ht' : 2*N ≤ squareThetaCutoff N := by exact_mod_cast hm
    omega
  · exact (hr i 1 (by simpa only [Nat.cast_one] using (hw i).2.2 hl hu)).1

/-- The same integer products are trapped between reciprocal rational
powers with a single integer base at all central scales. -/
theorem rational_theta_square_generator_product_bounds :
    ∃ (A : ℝ) (B K : ℕ), 0 < A ∧ 0 < B ∧ ∀ᶠ N : ℕ in atTop,
      thetaSquareGeneratorProduct A N ≤ (B:ℚ)^(N^3) ∧
      (thetaSquareGeneratorProduct A N)⁻¹ ≤ (B:ℚ)^(N^3) ∧
      (∀ i : ℕ, squareThetaExponent A N i ≤ K) ∧
      ∀ i : ℕ, N ≤ i+2 → i+2 ≤ 2*N → i < squareThetaCutoff N ∧ 0 < squareThetaExponent A N i := by
  obtain ⟨A,C,K,hA,_,h⟩ := actual_square_generator_products_at_every_scale
  let B := ⌈Real.exp C⌉₊
  have hB : 0 < B := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hb := (Real.le_log_iff_exp_le (Nat.cast_pos.mpr hB)).mpr (Nat.le_ceil (Real.exp C))
  refine ⟨A,B,K,hA,hB,h.mono ?_⟩
  rintro N ⟨hp,hu,hl⟩
  let q := thetaSquareGeneratorProduct A N
  have hq : 0 < q := prod_pos fun i _ => pow_pos
    (show (0:ℚ)<ordinaryPrimeGenerator ((i+2) • successorSquareTriple (i+2)) from
      prod_pos fun k _ => zpow_pos (Nat.cast_pos.mpr (contactBase_pos k)) _) _
  have hbound {a : ℚ} (ha : 0<a) (hlog : Real.log (a:ℝ) ≤ C*(N:ℝ)^3) : a ≤ (B:ℚ)^(N^3) := by
    have he : Real.log ((B:ℝ)^(N^3))=Real.log B*(N:ℝ)^3 := by rw [Real.log_pow,Nat.cast_pow,mul_comm]
    have hh := hlog.trans (mul_le_mul_of_nonneg_right hb (by positivity))
    rw [← he] at hh
    have hr := (Real.log_le_log_iff (by exact_mod_cast ha) (pow_pos (Nat.cast_pos.mpr hB) _)).mp hh
    exact_mod_cast hr
  change |Real.log (q:ℝ)| ≤ _ at hp
  refine ⟨hbound hq (abs_le.mp hp).2,hbound (inv_pos.mpr hq) ?_,hu,hl⟩
  rw [Rat.cast_inv,Real.log_inv]
  linarith only [(abs_le.mp hp).1]

#print axioms rational_theta_square_generator_product_bounds
#print axioms actual_square_generator_products_at_every_scale

end GaloisForLFunctions.CountingHolography.Sections
