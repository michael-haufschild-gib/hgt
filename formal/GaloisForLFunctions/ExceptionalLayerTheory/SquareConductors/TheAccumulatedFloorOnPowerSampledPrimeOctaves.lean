import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheCenteredFloorOnPowerSampledPrimeOctaves
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheGcdProductOnOneMangoldtOctave
import GaloisForLFunctions.ExceptionalLayerTheory.GrowingQuotientBandsInBinomialCarries
import GaloisForLFunctions.RHTower.HarmonicHalfErrorBounds

/-!
# The accumulated floor correction on power-sampled prime octaves

The fractional parts at fixed divisor have a summable discrepancy on
successive octaves. The nonoscillating half contributes the harmonic
series, with the prime-counting error evaluated at the divisor endpoints.
-/

noncomputable section
open Finset Filter ArithmeticFunction Topology
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem octave_limit {F : ℕ → ℝ} {α A : ℝ} (hα : 0<α) (hA : 0 ≤ A)
    (hlocal : ∀ {m n : ℕ},1 ≤ m → m ≤ n → n ≤ 2*m → |F n-F m| ≤ A*(m:ℝ)^(-α)) :
    ∃ c B : ℝ, 0 ≤ B ∧ ∀ {m : ℕ},1 ≤ m → |F m-c| ≤ B*(m:ℝ)^(-α) := by
  let q := (2:ℝ)^(-α)
  have hq : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (neg_lt_zero.mpr hα)
  have hq0 : 0 ≤ q := Real.rpow_nonneg (by norm_num) _
  let B := A/(1-q)
  have hB : 0 ≤ B := div_nonneg hA (sub_pos.mpr hq).le
  have idB : B*(1-q)=A := div_mul_cancel₀ _ (sub_pos.mpr hq).ne'
  have hAB : A ≤ B := by nlinarith only [idB,mul_nonneg hB hq0]
  have all (j : ℕ) : ∀ {m n : ℕ},1 ≤ m → m ≤ n → n ≤ 2^j*m → |F n-F m| ≤ B*(m:ℝ)^(-α) := by
    induction j with
    | zero =>
      intro m n hm hmn hu
      have e : n=m := le_antisymm (by simpa only [pow_zero,one_mul] using hu) hmn
      rw [e,sub_self,abs_zero]
      positivity
    | succ j ih =>
      intro m n hm hmn hu
      by_cases hsmall : n ≤ 2*m
      · exact (hlocal hm hmn hsmall).trans (mul_le_mul_of_nonneg_right hAB (Real.rpow_nonneg (Nat.cast_nonneg _) _))
      have hub : n ≤ 2^j*(2*m) := by simpa only [pow_succ,Nat.mul_assoc] using hu
      have h1 := ih (show 1 ≤ 2*m by omega) (le_of_not_ge hsmall) hub
      have h2 := hlocal hm (show m ≤ 2*m by omega) le_rfl
      rw [Nat.cast_mul,Nat.cast_ofNat,Real.mul_rpow (by norm_num) (Nat.cast_nonneg m)] at h1
      change _ ≤ B*(q*(m:ℝ)^(-α)) at h1
      have eqn := congrArg (fun z : ℝ => z*(m:ℝ)^(-α)) idB
      have hs := abs_sub_le (F n) (F (2*m)) (F m)
      linarith only [hs,h1,h2,eqn]
  have bound {m n : ℕ} (hm : 1 ≤ m) (hmn : m ≤ n) : |F n-F m| ≤ B*(m:ℝ)^(-α) := by
    have hn : n < 2^n := Nat.lt_two_pow_self
    exact all n hm hmn (hn.le.trans (Nat.le_mul_of_pos_right _ hm))
  have hz : Tendsto (fun n : ℕ => B*(n:ℝ)^(-α)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,mul_zero] using (tendsto_const_nhds (x:=B)).mul
      ((tendsto_rpow_neg_atTop hα).comp (tendsto_natCast_atTop_atTop (R:=ℝ)))
  have cauchy : CauchySeq F := by
    rw [Metric.cauchySeq_iff]
    intro ε hε
    obtain ⟨N,hN⟩ := eventually_atTop.mp (hz.eventually_lt_const hε)
    refine ⟨max N 1,fun a ha b hb => ?_⟩
    rw [Real.dist_eq]
    rcases le_total a b with h | h
    · rw [abs_sub_comm]
      exact (bound ((le_max_right ..).trans ha) h).trans_lt (hN a ((le_max_left ..).trans ha))
    · exact (bound ((le_max_right ..).trans hb) h).trans_lt (hN b ((le_max_left ..).trans hb))
  obtain ⟨c,hc⟩ := cauchySeq_tendsto_of_complete cauchy
  refine ⟨c,B,hB,fun {m} hm => ?_⟩
  rw [abs_sub_comm]
  exact le_of_tendsto (hc.sub_const (F m)).abs ((eventually_ge_atTop m).mono fun n hn => bound hm hn)

private def floorMass (primesOnly : Bool) (d : ℕ) : ℝ :=
  if primesOnly=true ∧ ¬d.Prime then 0 else vonMangoldt d

private theorem abs_floor_mass (b : Bool) (d : ℕ) : |floorMass b d| ≤ vonMangoldt d := by
  unfold floorMass
  split_ifs
  · simpa only [abs_zero] using (vonMangoldt_nonneg : 0 ≤ vonMangoldt d)
  · exact (abs_of_nonneg vonMangoldt_nonneg).le

private def powerFloorPrice (s : ℕ) (b : Bool) (m : ℕ) : ℝ :=
  ((m:ℝ)^(s+2))⁻¹*∑ d ∈ Ioc (m^(s+1)) (2*m^(s+1)),floorMass b d*Int.fract ((m:ℝ)^(s+2)/d)

/-- Lost reciprocal mass from the floor at the upper product endpoint. -/
def powerGcdFloorPrice (r m : ℕ) : ℝ :=
  (∑ d ∈ Ioc (m^r) (2*m^r),vonMangoldt d/(d:ℝ))-Real.log (octaveGcdProduct (m^r) (m^(r+1)))/(m:ℝ)^(r+1)

/-- The same lost mass for ordinary primes alone. -/
def powerPrimeFloorPrice (r m : ℕ) : ℝ :=
  ∑ p ∈ (Ioc (m^r) (2*m^r)).filter Nat.Prime,
    (Real.log p/(p:ℝ)-((m^(r+1)/p:ℕ):ℝ)*Real.log p/(m:ℝ)^(r+1))

private theorem floor_log_price {m : ℕ} (hm : 1 ≤ m) (s : ℕ) (b : Bool) :
    powerFloorPrice s b m=(if b then powerPrimeFloorPrice (s+1) m else powerGcdFloorPrice (s+1) m) := by
  have hm0 := (Nat.cast_pos (α:=ℝ)).mpr hm
  have hden := pow_ne_zero (s+2) hm0.ne'
  have frac (d : ℕ) : Int.fract ((m:ℝ)^(s+2)/d)=(m:ℝ)^(s+2)/d-((m^(s+2)/d:ℕ):ℝ) := by
    rw [Int.fract]
    congr 1
    rw [←Nat.cast_pow,←Int.natCast_floor_eq_floor (div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)),
      Nat.floor_div_natCast,Nat.floor_natCast,Int.cast_natCast]
  cases b
  · simp only [Bool.false_eq_true,ite_false,Bool.false_eq_true,false_and,floorMass,powerFloorPrice,powerGcdFloorPrice,
      log_octave_gcd_product (pow_pos hm (s+1)),sum_div,mul_sum,←sum_sub_distrib,frac]
    apply sum_congr rfl
    intro d _
    field_simp [hden] <;> ring
  · change powerFloorPrice s true m = powerPrimeFloorPrice (s+1) m
    simp only [powerPrimeFloorPrice,powerFloorPrice,mul_sum,sum_filter,floorMass,true_and,frac]
    apply sum_congr rfl
    intro d _
    by_cases hp : d.Prime
    · simp only [hp,not_true_eq_false,if_false,if_true,vonMangoldt_apply_prime hp]
      field_simp [hden] <;> ring
    · simp [hp]

private theorem floor_mass_count_error :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ (b : Bool) (k : ℕ),
      |(∑ d ∈ Ioc 0 k,floorMass b d)-(k:ℝ)| ≤ A*(k:ℝ)^(8/9:ℝ) := by
  have ht : _root_.RHTower.zeroReSup < 8/9 :=
    GaloisForLFunctions.ExceptionalLayerTheory.zeroReSup_le_sub_seven_eighths.trans_lt (by norm_num)
  obtain ⟨A,hA,hψ⟩ := _root_.RHTower.exists_abs_chebyshevPsi_sub_le_rpow ht
  obtain ⟨B,hB⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨A+|B|,by positivity,?_⟩
  intro b k
  rcases eq_zero_or_pos k with rfl | hk
  · simp
  have hk1 := (Nat.one_le_cast (α:=ℝ)).mpr hk
  have base := hψ ((k:ℕ):ℝ) hk1
  have upper := Real.rpow_le_rpow_of_exponent_le hk1 (by norm_num : (1/2:ℝ) ≤ 8/9)
  rw [←Real.sqrt_eq_rpow] at upper
  have mass := (hB ((k:ℕ):ℝ)).trans (mul_le_mul (le_abs_self B) upper (Real.sqrt_nonneg _) (abs_nonneg _))
  cases b
  · have eqn : (∑ d ∈ Ioc 0 k,floorMass false d)=Chebyshev.psi k := by
      simp only [Chebyshev.psi,Nat.floor_natCast,floorMass,Bool.false_eq_true,false_and,if_false]
    rw [eqn]
    exact base.trans (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right (abs_nonneg B)) (Real.rpow_nonneg (Nat.cast_nonneg _) _))
  · have eqn : (∑ d ∈ Ioc 0 k,floorMass true d)=Chebyshev.theta k := by
      simp only [Chebyshev.theta,Nat.floor_natCast,sum_filter,floorMass,true_and]
      apply sum_congr rfl
      intro d _
      by_cases hp : d.Prime <;> simp [hp,vonMangoldt_apply_prime]
    rw [eqn,abs_le]
    have h := abs_le.mp base
    constructor <;> linarith only [h.1,h.2,mass,Chebyshev.theta_le_psi (k:ℝ),mul_nonneg (abs_nonneg B) (Real.rpow_nonneg (Nat.cast_nonneg (α:=ℝ) k) (8/9:ℝ))]

private def halfMassError (s : ℕ) (b : Bool) (m : ℕ) : ℝ :=
  ((∑ d ∈ Ioc (m^(s+1)) (2*m^(s+1)),floorMass b d)-(m:ℝ)^(s+1))/(2*(m:ℝ)^(s+2))

private theorem half_mass_error_bound (s : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ b {m : ℕ}, 1 ≤ m →
      |halfMassError s b m| ≤ A*(m:ℝ)^(-1-((s:ℝ)+1)/9) := by
  obtain ⟨C,hC,he⟩ := floor_mass_count_error
  let T : ℝ := 8/9
  let A := C*((2:ℝ)^T+1)/2
  refine ⟨A,by dsimp only [A,T]; positivity,?_⟩
  intro b m hm
  let M := m^(s+1)
  have hp := (Nat.cast_pos (α:=ℝ)).mpr hm
  let F := fun k : ℕ => (∑ d ∈ Ioc 0 k,floorMass b d)-(k:ℝ)
  have eh : (∑ d ∈ Ioc M (2*M),floorMass b d)-(M:ℝ)=F (2*M)-F M := by
    dsimp only [F]
    rw [←sum_Ioc_consecutive (floorMass b) (Nat.zero_le M) (by omega : M ≤ 2*M),Nat.cast_mul,Nat.cast_ofNat]
    ring
  have h := (abs_sub (F (2*M)) (F M)).trans (add_le_add (he b (2*M)) (he b M))
  change _ ≤ C*((2*M:ℕ):ℝ)^T+C*(M:ℝ)^T at h
  rw [Nat.cast_mul,Nat.cast_ofNat,Real.mul_rpow (by norm_num) (Nat.cast_nonneg _)] at h
  change |((∑ d ∈ Ioc M (2*M),floorMass b d)-(m:ℝ)^(s+1))/(2*(m:ℝ)^(s+2))| ≤ _
  rw [←Nat.cast_pow,eh,abs_div,abs_of_pos (by positivity : 0 < 2*(m:ℝ)^(s+2))]
  apply (div_le_div_of_nonneg_right h (by positivity)).trans_eq
  have exp : (M:ℝ)^T/(m:ℝ)^(s+2)=(m:ℝ)^(-1-((s:ℝ)+1)/9) := by
    dsimp only [M]
    rw [Nat.cast_pow,←Real.rpow_natCast (n:=s+1),←Real.rpow_mul hp.le,
      ←Real.rpow_natCast (n:=s+2),←Real.rpow_sub hp]
    congr 1
    dsimp only [T]
    push_cast
    ring
  rw [←exp]
  dsimp only [A]
  ring

private theorem centered_price_fragment (s : ℕ) (b : Bool) {D K : ℕ} (hD : 1 ≤ D) :
    (∑ m ∈ Ioc D K,(powerFloorPrice s b m-1/(2*(m:ℝ)))) =
      sparseFloorFragment s D K (floorMass b)+∑ m ∈ Ioc D K,halfMassError s b m := by
  rw [sparseFloorFragment,←sum_add_distrib]
  apply sum_congr rfl
  intro m hm
  have hm0 := (Nat.cast_pos (α:=ℝ)).mpr (hD.trans (mem_Ioc.mp hm).1.le)
  let S := Ioc (m^(s+1)) (2*m^(s+1))
  let v := fun d => Int.fract ((m:ℝ)^(s+2)/d)
  have h : (∑ d ∈ S,floorMass b d*centeredPowerQuotient s d m)=
      (∑ d ∈ S,floorMass b d*v d)-(∑ d ∈ S,floorMass b d)*(1/2:ℝ) := by
    simp only [centeredPowerQuotient,v,mul_sub,sum_sub_distrib,sum_mul]
  change ((m:ℝ)^(s+2))⁻¹*(∑ d ∈ S,floorMass b d*v d)-1/(2*(m:ℝ))=
    ((m:ℝ)^(s+2))⁻¹*(∑ d ∈ S,floorMass b d*centeredPowerQuotient s d m)+
      ((∑ d ∈ S,floorMass b d)-(m:ℝ)^(s+1))/(2*(m:ℝ)^(s+2))
  rw [h,pow_succ (m:ℝ) (s+1)]
  field_simp [hm0.ne'] <;> ring

private theorem accumulated_power_floor (s : ℕ) (b : Bool) :
    let α := min (1/3:ℝ) (((s:ℝ)+1)/9)
    ∃ c C : ℝ, ∀ {K : ℕ}, 1 ≤ K →
      |(∑ m ∈ Icc 1 K,powerFloorPrice s b m)-(1/2:ℝ)*Real.log K-c| ≤ C*(K:ℝ)^(-α) := by
  intro α
  have hα : 0 < α := lt_min (by norm_num) (by positivity)
  let r : ℝ := ((s:ℝ)+1)/9
  have hr0 : 0 ≤ r := by dsimp only [r]; positivity
  have hα1 : α ≤ 1/3 := min_le_left .. 
  have hαr : α ≤ r := min_le_right ..
  let f (m : ℕ) := powerFloorPrice s b m-1/(2*(m:ℝ))
  let F (k : ℕ) := ∑ m ∈ Ioc 0 k,f m
  obtain ⟨A,hA,hs⟩ := sparse_floor_fragment_cubic_saving s
  obtain ⟨B,hB,hb⟩ := half_mass_error_bound s
  have block {D K : ℕ} (hD : 1 ≤ D) (hDK : D ≤ K) (hK : K ≤ 2*D) :
      |F K-F D| ≤ (A+B)*(D:ℝ)^(-α) := by
    have hD0 := (Nat.cast_pos (α:=ℝ)).mpr hD
    have hD1 := (Nat.one_le_cast (α:=ℝ)).mpr hD
    have gain (x : ℝ) (hx : α ≤ x) : (D:ℝ)^(-x) ≤ (D:ℝ)^(-α) :=
      Real.rpow_le_rpow_of_exponent_le hD1 (neg_le_neg hx)
    have mass : |∑ m ∈ Ioc D K,halfMassError s b m| ≤ B*(D:ℝ)^(-r) := by
      apply (abs_sum_le_sum_abs ..).trans
      calc _ ≤ ∑ _ ∈ Ioc D K,B*(D:ℝ)^(-1-r) := by
                 apply sum_le_sum
                 intro m hm
                 have hDm := (mem_Ioc.mp hm).1.le
                 exact (hb b (hD.trans hDm)).trans (mul_le_mul_of_nonneg_left
                   (Real.rpow_le_rpow_of_nonpos hD0 (Nat.cast_le.mpr hDm)
                     (show -1-r ≤ 0 by linarith only [hr0])) hB)
           _ ≤ (D:ℝ)*(B*(D:ℝ)^(-1-r)) := by
                 rw [sum_const,nsmul_eq_mul,Nat.card_Ioc]
                 exact mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (by omega : K-D ≤ D)) (by positivity)
           _ = _ := by
                 have e : (D:ℝ)*(D:ℝ)^(-1-r)=(D:ℝ)^(-r) := by
                   calc _ = (D:ℝ)^(1+(-1-r)) := by rw [Real.rpow_add hD0,Real.rpow_one]
                        _ = _ := by rw [show (1:ℝ)+(-1-r)= -r by ring]
                 rw [←e]; ring
    have hfrag := (hs hD hDK hK _ (abs_floor_mass b)).trans (mul_le_mul_of_nonneg_left (gain _ hα1) hA)
    have hmass := mass.trans (mul_le_mul_of_nonneg_left (gain _ hαr) hB)
    have hsum : F K-F D=∑ m ∈ Ioc D K,f m :=
      (eq_sub_of_add_eq' (sum_Ioc_consecutive f (Nat.zero_le D) hDK)).symm
    rw [hsum,show (∑ m ∈ Ioc D K,f m)=_ from centered_price_fragment s b hD]
    exact (abs_add_le ..).trans ((add_le_add hfrag hmass).trans_eq (by ring))
  obtain ⟨c,C,hC,hlim⟩ := octave_limit hα (add_nonneg hA hB) block
  refine ⟨c+(1/2:ℝ)*Real.eulerMascheroniConstant,C+1,?_⟩
  intro K hK
  have hk0 := (Nat.cast_pos (α:=ℝ)).mpr hK
  have hk1 := (Nat.one_le_cast (α:=ℝ)).mpr hK
  have he : F K=(∑ m ∈ Icc 1 K,powerFloorPrice s b m)-(1/2:ℝ)*(harmonic K:ℝ) := by
    have hi : Ioc 0 K=Icc 1 K := by ext m; simp only [mem_Ioc,mem_Icc]; omega
    dsimp only [F]
    rw [hi,harmonic_eq_sum_Icc,Rat.cast_sum,mul_sum]
    simp only [f,sum_sub_distrib,Rat.cast_inv,Rat.cast_natCast,one_div,mul_inv_rev,mul_comm]
  have h := abs_le.mp (hlim hK)
  rw [he] at h
  have harm := _root_.RHTower.harmonic_mascheroni_half_bounds hK
  have hi := Real.rpow_le_rpow_of_exponent_le hk1 (show -(1:ℝ) ≤ -α by linarith only [hα1])
  rw [Real.rpow_neg hk0.le,Real.rpow_one] at hi
  have hsmall : 1/(2*(K:ℝ)) ≤ (K:ℝ)⁻¹ := by
    rw [one_div,mul_inv_rev]; exact mul_le_of_le_one_right (inv_nonneg.mpr hk0.le) (by norm_num)
  have hz : 0 ≤ (harmonic K:ℝ)-Real.log K-Real.eulerMascheroniConstant :=
    (by positivity : 0 ≤ 1/(2*((K:ℝ)+1))).trans harm.1
  rw [abs_le]
  constructor <;> linarith only [h.1,h.2,harm.2.trans (hsmall.trans hi),hz,Real.rpow_nonneg hk0.le (-α)]

/-- The normalized floor cost has logarithmic coefficient one half on
every power grid, with the power remainder for all positive endpoints.
The two constants may differ for Mangoldt and ordinary-prime weights. -/
theorem power_grid_floor_price_asymptotics {r : ℕ} (hr : 2 ≤ r) :
    let α := min (1/3:ℝ) ((r:ℝ)/9)
    (∃ c C : ℝ, ∀ {K : ℕ},1 ≤ K →
      |(∑ m ∈ Icc 1 K,powerGcdFloorPrice r m)-(1/2:ℝ)*Real.log K-c| ≤ C*(K:ℝ)^(-α)) ∧
    (∃ c C : ℝ, ∀ {K : ℕ},1 ≤ K →
      |(∑ m ∈ Icc 1 K,powerPrimeFloorPrice r m)-(1/2:ℝ)*Real.log K-c| ≤ C*(K:ℝ)^(-α)) := by
  obtain ⟨s,rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : r ≠ 0)
  dsimp only
  constructor
  · obtain ⟨c,C,h⟩ := accumulated_power_floor s false
    refine ⟨c,C,fun {K} hK => ?_⟩
    simpa only [Nat.cast_succ, sum_congr rfl fun m (hm : m ∈ Icc 1 K) =>
      (floor_log_price (mem_Icc.mp hm).1 s false).trans (if_neg (by decide))] using h hK
  · obtain ⟨c,C,h⟩ := accumulated_power_floor s true
    refine ⟨c,C,fun {K} hK => ?_⟩
    simpa only [Nat.cast_succ, sum_congr rfl fun m (hm : m ∈ Icc 1 K) =>
      (floor_log_price (mem_Icc.mp hm).1 s true).trans (if_pos rfl)] using h hK

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
