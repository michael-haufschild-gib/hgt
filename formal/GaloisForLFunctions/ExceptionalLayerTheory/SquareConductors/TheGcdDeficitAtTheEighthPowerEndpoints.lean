import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.SquareAndSixthPowerSamplesOfTheReciprocalPrimeOctave
import GaloisForLFunctions.ExceptionalLayerTheory.GrowingQuotientBandsInBinomialCarries
import GaloisForLFunctions.RHTower.HarmonicHalfErrorBounds

/-!
# Continuous cofactor density of the sparse gcd product

In the range M < d ≤ 2M each multiple below mM has a cofactor at most m.
Counting that cofactor first leaves m exact Chebyshev intervals. Replacing
their masses by length yields the same harmonic difference at m=2k and 2k+1.
-/
noncomputable section
open Finset ArithmeticFunction
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Upper endpoint of the divisor interval belonging to cofactor j. -/
def cofactorEdge (m M j : ℕ) : ℝ := (M:ℝ)*min 2 ((m:ℝ)/j)

private theorem edge_mem {m M j : ℕ} (hj : j ∈ Ioc 0 m) :
    (M:ℝ) ≤ cofactorEdge m M j ∧ cofactorEdge m M j ≤ 2*(M:ℝ) := by
  obtain ⟨hj0,hjm⟩ := mem_Ioc.mp hj
  have hlow : (1:ℝ) ≤ min 2 ((m:ℝ)/j) := le_min (by norm_num)
    ((one_le_div (Nat.cast_pos.mpr hj0)).mpr (Nat.cast_le.mpr hjm))
  exact ⟨le_mul_of_one_le_right (Nat.cast_nonneg _) hlow,
    (mul_le_mul_of_nonneg_left (min_le_left _ _) (Nat.cast_nonneg _)).trans_eq (mul_comm _ _)⟩

private theorem cofactor_row {m M d : ℕ} (hd : d ∈ Ioc M (2*M)) :
    (((m*M/d:ℕ):ℝ)*vonMangoldt d) =
      ∑ j ∈ Ioc 0 m,if j*d ≤ m*M then vonMangoldt d else 0 := by
  obtain ⟨hlo,_⟩ := mem_Ioc.mp hd
  have hd0 := (Nat.zero_le _).trans_lt hlo
  have hcap : m*M/d ≤ m := Nat.le_of_lt_succ ((Nat.div_lt_iff_lt_mul hd0).mpr (by
    rw [Nat.succ_mul]
    exact (Nat.mul_le_mul_left m hlo.le).trans_lt (by omega)))
  have hh : (Ioc 0 m).filter (fun j => j*d ≤ m*M)=Ioc 0 (m*M/d) := by
    ext j
    simp only [mem_filter,mem_Ioc,←Nat.le_div_iff_mul_le hd0]
    omega
  rw [←sum_filter,hh,sum_const,Nat.card_Ioc,Nat.sub_zero,nsmul_eq_mul]

/-- Counting cofactors first gives the sharp Chebyshev intervals at a
horizon divisible by the lower endpoint. The final cofactor has zero mass. -/
theorem gcd_product_cofactor_intervals {M : ℕ} (hM : 0 < M) (m : ℕ) :
    Real.log (octaveGcdProduct M (m*M)) =
      ∑ j ∈ Ioc 0 m, (Chebyshev.psi (cofactorEdge m M j)-Chebyshev.psi M) := by
  rw [log_octave_gcd_product hM,sum_congr rfl (fun d hd => cofactor_row (m := m) hd),sum_comm]
  apply sum_congr rfl
  intro j hj
  have hjpos := (mem_Ioc.mp hj).1
  have hjr : (0:ℝ) < j := Nat.cast_pos.mpr hjpos
  have hr := edge_mem (M := M) hj
  have hr0 := (Nat.cast_nonneg M).trans hr.1
  have hMfloor := (Nat.le_floor_iff hr0).mpr hr.1
  have he : (Ioc M (2*M)).filter (fun d => j*d ≤ m*M)=Ioc M ⌊cofactorEdge m M j⌋₊ := by
    ext d
    have hmin : cofactorEdge m M j=min (2*(M:ℝ)) ((m:ℝ)*M/j) := by
      rw [cofactorEdge,mul_min_of_nonneg _ _ (Nat.cast_nonneg M)]
      congr 1 <;> ring
    simp only [mem_filter,mem_Ioc]
    rw [Nat.le_floor_iff hr0,hmin,le_min_iff,le_div_iff₀ hjr]
    have h1 : (d:ℝ) ≤ 2*M ↔ d ≤ 2*M := by exact_mod_cast Iff.rfl
    have h2 : (d:ℝ)*j ≤ (m:ℝ)*M ↔ j*d ≤ m*M := by rw [mul_comm (d:ℝ)]; exact_mod_cast Iff.rfl
    rw [h1,h2]
    tauto
  rw [←sum_filter,he,Chebyshev.psi,Chebyshev.psi,Nat.floor_natCast]
  linarith only [sum_Ioc_consecutive (fun d => vonMangoldt d) (Nat.zero_le M) hMfloor]

/-- Normalized cofactor density when every prime interval is given its length. -/
def cofactorIntervalDensity (m : ℕ) : ℝ :=
  (∑ j ∈ Ioc 0 m,(min 2 ((m:ℝ)/j)-1))/(m:ℝ)

private theorem cofactor_center (m M : ℕ) :
    (∑ j ∈ Ioc 0 m,(cofactorEdge m M j-(M:ℝ)))=(M:ℝ)*∑ j ∈ Ioc 0 m,(min 2 ((m:ℝ)/j)-1) := by
  rw [mul_sum]
  exact sum_congr rfl (fun j _ => by dsimp only [cofactorEdge]; ring)

/-- The complete sharp product differs from the continuous cofactor density
by the ordinary Chebyshev error at the same exponent, uniformly in m. -/
theorem gcd_product_density_above_zero_width {t : ℝ} (ht : _root_.RHTower.zeroReSup < t) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {M m : ℕ}, 1 ≤ M → 1 ≤ m →
      |Real.log (octaveGcdProduct M (m*M))/((m:ℝ)*M)-cofactorIntervalDensity m| ≤ C*(M:ℝ)^(t-1) := by
  obtain ⟨B,hB,hψ⟩ := _root_.RHTower.exists_abs_chebyshevPsi_sub_le_rpow ht
  have ht0 : 0 ≤ t := by linarith only [_root_.RHTower.half_le_zeroReSup,ht]
  refine ⟨B*((2:ℝ)^t+1),by positivity,?_⟩
  intro M m hM hm
  have hM1 : (1:ℝ) ≤ M := Nat.one_le_cast.mpr hM
  have hMr := zero_lt_one.trans_le hM1
  have hmr : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hden := mul_pos hmr hMr
  let f (j : ℕ) := (Chebyshev.psi (cofactorEdge m M j)-Chebyshev.psi M)-(cofactorEdge m M j-M)
  have hf (j : ℕ) (hj : j ∈ Ioc 0 m) : |f j| ≤ B*((2:ℝ)^t+1)*(M:ℝ)^t := by
    have hr := edge_mem (M := M) hj
    have hu := (hψ _ (hM1.trans hr.1)).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (hMr.le.trans hr.1) hr.2 ht0) hB)
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) hMr.le] at hu
    rw [show f j=(Chebyshev.psi (cofactorEdge m M j)-cofactorEdge m M j)-(Chebyshev.psi M-M) by dsimp only [f]; ring]
    exact (abs_sub _ _).trans ((add_le_add hu (hψ _ hM1)).trans_eq (by ring))
  have hh := (abs_sum_le_sum_abs f (Ioc 0 m)).trans (sum_le_sum hf)
  have he : Real.log (octaveGcdProduct M (m*M))/((m:ℝ)*M)-cofactorIntervalDensity m =
      (∑ j ∈ Ioc 0 m,f j)/((m:ℝ)*M) := by
    dsimp only [f]
    rw [sum_sub_distrib,cofactor_center,gcd_product_cofactor_intervals hM m,cofactorIntervalDensity]
    field_simp
  simp only [sum_const,Nat.card_Ioc,Nat.sub_zero,nsmul_eq_mul] at hh
  rw [he,abs_div,abs_of_pos hden,Real.rpow_sub_one hMr.ne']
  apply (div_le_iff₀ hden).mpr
  exact hh.trans_eq (by field_simp)

#print axioms gcd_product_cofactor_intervals
#print axioms gcd_product_density_above_zero_width

private theorem harmonic_prefix (n : ℕ) :
    (∑ j ∈ Ioc 0 n,1/(j:ℝ))=(harmonic n:ℝ) := by
  rw [show Ioc 0 n=Icc 1 n by ext j; simp only [mem_Ioc,mem_Icc]; omega,
    harmonic_eq_sum_Icc,Rat.cast_sum]
  simp only [Rat.cast_inv,Rat.cast_natCast,one_div]

/-- The continuous density is constant on each even/odd pair of horizons. -/
theorem cofactor_density_harmonic {m : ℕ} (hm : 0 < m) :
    cofactorIntervalDensity m=(harmonic (2*(m/2)):ℝ)-(harmonic (m/2):ℝ) := by
  let k := m/2
  let f (j : ℕ) := min 2 ((m:ℝ)/j)-1
  have hkm : k ≤ m := Nat.div_le_self _ _
  have hmr : (0:ℝ) < m := Nat.cast_pos.mpr hm
  have hprefix : (∑ j ∈ Ioc 0 k,f j)=(k:ℝ) := by
    have h (j : ℕ) (hj : j ∈ Ioc 0 k) : f j=1 := by
      obtain ⟨hj0,hjk⟩ := mem_Ioc.mp hj
      have hh : 2*(j:ℝ) ≤ m := by exact_mod_cast (show 2*j ≤ m by dsimp only [k] at hjk; omega)
      simp only [f,min_eq_left ((le_div_iff₀ (Nat.cast_pos.mpr hj0)).mpr hh)]
      norm_num
    rw [sum_congr rfl h,sum_const,Nat.card_Ioc,Nat.sub_zero,nsmul_eq_mul,mul_one]
  have hu : (∑ j ∈ Ioc k m,1/(j:ℝ))=(harmonic m:ℝ)-(harmonic k:ℝ) := by
    have hh := sum_Ioc_consecutive (fun j : ℕ => 1/(j:ℝ)) (Nat.zero_le k) hkm
    rw [harmonic_prefix,harmonic_prefix] at hh
    linarith only [hh]
  have hsuff : (∑ j ∈ Ioc k m,f j)=(m:ℝ)*((harmonic m:ℝ)-(harmonic k:ℝ))-((m:ℝ)-k) := by
    have h (j : ℕ) (hj : j ∈ Ioc k m) : f j=(m:ℝ)*(1/(j:ℝ))-1 := by
      have hjk := (mem_Ioc.mp hj).1
      have hh : (m:ℝ) ≤ 2*j := by exact_mod_cast (show m ≤ 2*j by dsimp only [k] at hjk; omega)
      dsimp only [f]
      rw [min_eq_right ((div_le_iff₀ (Nat.cast_pos.mpr ((Nat.zero_le _).trans_lt hjk))).mpr hh)]
      ring
    rw [sum_congr rfl h,sum_sub_distrib,←mul_sum,hu,sum_const,Nat.card_Ioc,nsmul_eq_mul,mul_one,Nat.cast_sub hkm]
  have hall := sum_Ioc_consecutive f (Nat.zero_le k) hkm
  rw [hprefix,hsuff] at hall
  change (∑ j ∈ Ioc 0 m,f j)/(m:ℝ)=(harmonic (2*k):ℝ)-(harmonic k:ℝ)
  rw [←hall,div_eq_iff hmr.ne']
  have hi : m=2*k ∨ m=2*k+1 := by dsimp only [k]; omega
  rcases hi with he | ho
  · rw [he]
    push_cast
    ring
  · have hH : (harmonic m:ℝ)=(harmonic (2*k):ℝ)+((m:ℝ))⁻¹ := by
      rw [ho,harmonic_succ]; push_cast; ring
    rw [hH]
    have hm' : (m:ℝ)=2*k+1 := by exact_mod_cast ho
    field_simp [hmr.ne']
    nlinarith only [hm']

private def harmonicRemainder (n : ℕ) : ℝ :=
  (harmonic n:ℝ)-Real.log n-Real.eulerMascheroniConstant-1/(2*(n:ℝ))

private theorem harmonic_remainder_sq {n : ℕ} (hn : 0 < n) :
    |harmonicRemainder n| ≤ 1/(n:ℝ)^2 := by
  obtain ⟨hl,hh⟩ := _root_.RHTower.harmonic_mascheroni_half_bounds hn
  have hr : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  dsimp only [harmonicRemainder]
  rw [abs_of_nonpos (sub_nonpos.mpr hh)]
  calc _ ≤ 1/(2*(n:ℝ))-1/(2*((n:ℝ)+1)) := by linarith only [hl]
       _ = 1/(2*(n:ℝ)*((n:ℝ)+1)) := by field_simp; ring
       _ ≤ _ := one_div_le_one_div_of_le (sq_pos_of_pos hr) (by nlinarith only [hr,sq_nonneg (n:ℝ)])

theorem cofactor_density_half_step {m : ℕ} (hm : 2 ≤ m) :
    |Real.log 2-cofactorIntervalDensity m-1/(2*(m:ℝ))| ≤ 20/(m:ℝ)^2 := by
  let k := m/2
  have hk : 1 ≤ k := by dsimp only [k]; omega
  have hkr : (0:ℝ) < k := Nat.cast_pos.mpr hk
  have hmr : (0:ℝ) < m := Nat.cast_pos.mpr (by omega)
  have hk1 : (1:ℝ) ≤ k := Nat.one_le_cast.mpr hk
  have hmlo : 2*(k:ℝ) ≤ m := by exact_mod_cast (show 2*k ≤ m by dsimp only [k]; omega)
  have hmhi : (m:ℝ) ≤ 2*k+1 := by exact_mod_cast (show m ≤ 2*k+1 by dsimp only [k]; omega)
  have hthree : (m:ℝ) ≤ 3*k := by linarith only [hk1,hmhi]
  have hmain :
      Real.log 2-cofactorIntervalDensity m-1/(2*(m:ℝ)) =
        (harmonicRemainder k-harmonicRemainder (2*k))+(1/(4*(k:ℝ))-1/(2*(m:ℝ))) := by
    rw [cofactor_density_harmonic (by omega)]
    change Real.log 2-((harmonic (2*k):ℝ)-(harmonic k:ℝ))-_ = _
    dsimp only [harmonicRemainder]
    rw [Nat.cast_mul,Nat.cast_ofNat,Real.log_mul (by norm_num : (2:ℝ) ≠ 0) hkr.ne']
    ring
  have herr' := harmonic_remainder_sq (show 0 < 2*k by omega)
  rw [Nat.cast_mul,Nat.cast_ofNat] at herr'
  have herr := (abs_sub (harmonicRemainder k) (harmonicRemainder (2*k))).trans
    (add_le_add (harmonic_remainder_sq hk) herr')
  have ht : 0 ≤ 1/(4*(k:ℝ))-1/(2*(m:ℝ)) :=
    sub_nonneg.mpr (one_div_le_one_div_of_le (by positivity) (by linarith only [hmlo]))
  have hfrac : |1/(4*(k:ℝ))-1/(2*(m:ℝ))| ≤ 1/(8*(k:ℝ)^2) := by
    rw [abs_of_nonneg ht,show 1/(4*(k:ℝ))-1/(2*(m:ℝ))=((m:ℝ)-2*k)/(4*k*m) by field_simp; ring]
    apply ((div_le_div_of_nonneg_right (by linarith only [hmhi] : (m:ℝ)-2*k ≤ 1) (by positivity))).trans
    apply one_div_le_one_div_of_le (by positivity)
    nlinarith only [mul_le_mul_of_nonneg_left hmlo hkr.le]
  rw [hmain]
  apply (abs_add_le _ _).trans ((add_le_add herr hfrac).trans ?_)
  calc _ = 11/(8*(k:ℝ)^2) := by field_simp; ring
       _ ≤ _ := (div_le_div_iff₀ (by positivity) (by positivity)).mpr (by
         nlinarith only [sq_nonneg (k:ℝ),sq_le_sq' (by linarith only [hkr,hmr] : -(3*(k:ℝ)) ≤ m) hthree])

/-- At the eighth/ninth-power horizon every sufficiently late actual
product has a positive deficit with main term 1/(2m). -/
theorem eighth_power_gcd_deficit_half_step {δ : ℝ} (hsmall : δ < 1/3000) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m : ℕ}, 2 ≤ m →
      |Real.log 2-Real.log (octaveGcdProduct (m^8) (m^9))/(m:ℝ)^9-1/(2*(m:ℝ))| ≤ C*(m:ℝ)^(-1-δ) := by
  let t := 1-(1+δ)/8
  have ht : _root_.RHTower.zeroReSup < t :=
    GaloisForLFunctions.ExceptionalLayerTheory.zeroReSup_le_sub_seven_eighths.trans_lt (by
      dsimp only [t]; linarith only [hsmall])
  obtain ⟨B,hB,h⟩ := gcd_product_density_above_zero_width ht
  refine ⟨20+B,by positivity,?_⟩
  intro m hm
  have hm' : 1 ≤ m := by omega
  have hr : (1:ℝ) ≤ m := Nat.one_le_cast.mpr hm'
  have hb := h (one_le_pow₀ hm' (n := 8)) hm'
  rw [Nat.cast_pow,show m*m^8=m^9 by ring,show (m:ℝ)*(m:ℝ)^8=(m:ℝ)^9 by ring] at hb
  rw [←Real.rpow_natCast (m:ℝ) 8,←Real.rpow_mul (zero_le_one.trans hr),Nat.cast_ofNat,
    show (8:ℝ)*(t-1) = -1-δ by dsimp only [t]; ring] at hb
  have hscale := Real.rpow_le_rpow_of_exponent_le hr (by linarith only [hsmall] : (-2:ℝ) ≤ -1-δ)
  rw [show (-2:ℝ) = -(2:ℝ) by norm_num,Real.rpow_neg (zero_le_one.trans hr),Real.rpow_two] at hscale
  have hD := cofactor_density_half_step hm
  rw [div_eq_mul_inv (20:ℝ)] at hD
  have he : Real.log 2-Real.log (octaveGcdProduct (m^8) (m^9))/(m:ℝ)^9-1/(2*(m:ℝ)) =
      (Real.log 2-cofactorIntervalDensity m-1/(2*(m:ℝ)))-
      (Real.log (octaveGcdProduct (m^8) (m^9))/(m:ℝ)^9-cofactorIntervalDensity m) := by ring
  rw [he]
  apply (abs_sub _ _).trans
  exact (add_le_add (hD.trans (mul_le_mul_of_nonneg_left hscale (by norm_num : (0:ℝ) ≤ 20))) hb).trans_eq (by ring)

#print axioms cofactor_density_harmonic
#print axioms cofactor_density_half_step
#print axioms eighth_power_gcd_deficit_half_step


/-- The accumulated positive deficit of the actual eighth/ninth-power
gcd products has logarithmic coefficient one half and a convergent remainder. -/
theorem eighth_gcd_deficit_centered_converges :
    ∃ c : ℝ, Filter.Tendsto (fun K : ℕ => powerGridGcdDeficit 8 K-(1/2:ℝ)*Real.log K)
      Filter.atTop (nhds c) := by
  let a (m : ℕ) := Real.log 2-Real.log (octaveGcdProduct (m^8) (m^9))/(m:ℝ)^9
  let f (i : ℕ) := max (a (i+1)) 0-1/(2*((i:ℝ)+1))
  let δ : ℝ := 1/6000
  obtain ⟨C,hC,h⟩ := eighth_power_gcd_deficit_half_step (δ := δ) (by norm_num [δ])
  have expneg : -1-δ < -1 := by norm_num [δ]
  have hf : Summable f := by
    apply ((Real.summable_nat_rpow.mpr expneg).mul_left C).of_norm_bounded_eventually_nat
    filter_upwards [Filter.eventually_ge_atTop 1] with n hn
    have hr : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
    have hu := h (m := n+1) (by omega)
    change |a (n+1)-1/(2*((n+1:ℕ):ℝ))| ≤ _ at hu
    rw [Nat.cast_succ] at hu
    have hm := Real.rpow_le_rpow_of_nonpos hr (by linarith only : (n:ℝ) ≤ n+1) (by linarith only [expneg] : -1-δ ≤ 0)
    have hb : 0 ≤ 1/(2*((n:ℝ)+1)) := by positivity
    have hc : |f n| ≤ |a (n+1)-1/(2*((n:ℝ)+1))| := by
      dsimp only [f]
      rcases le_total 0 (a (n+1)) with hp | hp
      · rw [max_eq_left hp]
      · rw [max_eq_right hp,zero_sub,abs_neg,abs_of_nonneg hb,abs_of_nonpos (sub_nonpos.mpr (hp.trans hb))]
        linarith only [hp]
    rw [Real.norm_eq_abs]
    exact hc.trans (hu.trans (mul_le_mul_of_nonneg_left hm hC))
  have hpre (K : ℕ) : powerGridGcdDeficit 8 K-(1/2:ℝ)*(harmonic K:ℝ)=∑ i ∈ range K,f i := by
    induction K with
    | zero => simp [powerGridGcdDeficit]
    | succ K ih =>
      rw [powerGridGcdDeficit] at ih ⊢
      rw [sum_Icc_succ_top (by omega : 1 ≤ K+1),Finset.sum_range_succ f K,harmonic_succ,←ih]
      dsimp only [f]
      have hrec : 1/(2*((K:ℝ)+1))=(1/2:ℝ)*((K:ℝ)+1)⁻¹ := by
        rw [one_div,mul_inv_rev]; ring
      rw [hrec]
      dsimp only [a]
      push_cast
      ring
  refine ⟨(∑' i, f i)+(1/2:ℝ)*Real.eulerMascheroniConstant,?_⟩
  have htot := hf.hasSum.tendsto_sum_nat.add (Real.tendsto_harmonic_sub_log.const_mul (1/2:ℝ))
  exact htot.congr fun K => by rw [←hpre]; ring

#print axioms eighth_gcd_deficit_centered_converges


/-- Log price of the ordinary primes selected by the two sharp sparse cutoffs. -/
def eighthOrdinaryPrimePrice (m : ℕ) : ℝ :=
  ∑ p ∈ (Ioc (m^8) (2*m^8)).filter Nat.Prime, ((m^9/p:ℕ):ℝ)*Real.log p

/-- Removing the proper prime powers preserves the pointwise half-step
at the original eighth/ninth-power endpoints. -/
theorem eighth_ordinary_prime_deficit_half_step {δ : ℝ} (hsmall : δ < 1/3000) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {m : ℕ}, 2 ≤ m →
      |Real.log 2-eighthOrdinaryPrimePrice m/(m:ℝ)^9-1/(2*(m:ℝ))| ≤ C*(m:ℝ)^(-1-δ) := by
  obtain ⟨B,hB,h⟩ := eighth_power_gcd_deficit_half_step hsmall
  obtain ⟨A,hA⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨B+|A| * Real.sqrt 2,by positivity,?_⟩
  intro m hm
  have hm0 : 0 < m := by omega
  have hr : 0 < (m:ℝ) := Nat.cast_pos.mpr hm0
  have hr1 : (1:ℝ) ≤ m := Nat.one_le_cast.mpr hm0
  let Q := Real.log (octaveGcdProduct (m^8) (m^9))
  let P := eighthOrdinaryPrimePrice m
  have hc := octave_gcd_product_ordinary_primes (pow_pos hm0 8) (m^9)
  change 0 ≤ Q-P ∧ Q-P ≤ _ at hc
  have hp := (hA ((2*m^8:ℕ):ℝ)).trans
    (mul_le_mul_of_nonneg_right (le_abs_self A) (Real.sqrt_nonneg _))
  have hi := hc.2.trans (mul_le_mul_of_nonneg_left hp (by positivity))
  push_cast at hi
  have hs : Real.sqrt ((m:ℝ)^8)=(m:ℝ)^4 := by
    rw [show (m:ℝ)^8=((m:ℝ)^4)^2 by ring,Real.sqrt_sq (pow_nonneg hr.le _)]
  rw [Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2),hs] at hi
  have hdiff : |(Q-P)/(m:ℝ)^9| ≤ (|A| * Real.sqrt 2)/(m:ℝ)^4 := by
    rw [abs_of_nonneg (div_nonneg hc.1 (pow_nonneg hr.le _))]
    apply (div_le_div_of_nonneg_right hi (pow_nonneg hr.le _)).trans_eq
    field_simp
  have hpow := Real.rpow_le_rpow_of_exponent_le hr1 (by linarith only [hsmall] : (-4:ℝ) ≤ -1-δ)
  rw [Real.rpow_neg hr.le,show (4:ℝ) = ((4:ℕ):ℝ) by norm_num,Real.rpow_natCast] at hpow
  have hh := abs_add_le (Real.log 2-Q/(m:ℝ)^9-1/(2*(m:ℝ))) ((Q-P)/(m:ℝ)^9)
  rw [show Real.log 2-eighthOrdinaryPrimePrice m/(m:ℝ)^9-1/(2*(m:ℝ)) =
      (Real.log 2-Q/(m:ℝ)^9-1/(2*(m:ℝ)))+((Q-P)/(m:ℝ)^9) by dsimp only [P]; ring]
  apply hh.trans ((add_le_add (h hm) hdiff).trans ?_)
  rw [div_eq_mul_inv (|A| * Real.sqrt 2),add_mul]
  exact add_le_add le_rfl (mul_le_mul_of_nonneg_left hpow (by positivity))

#print axioms eighth_ordinary_prime_deficit_half_step

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
