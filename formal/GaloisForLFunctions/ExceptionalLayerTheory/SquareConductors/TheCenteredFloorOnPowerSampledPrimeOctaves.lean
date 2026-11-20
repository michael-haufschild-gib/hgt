import GaloisForLFunctions.RHTower.SqrtTelescopeSums
import GaloisForLFunctions.RHTower.LogLatticePoissonAnticoncentration
import GaloisForLFunctions.PrimeExponentialSums.FractionalPartsOnIntegerReciprocalBlocks
import GaloisForLFunctions.RHTower.BourgainPartialSummation
import GaloisForLFunctions.RHTower.ZetaSymbolArchimedeanHorizon

/-!
# Centered floor errors at moving divisor endpoints

Fixing the divisor in the floor of m^(r+1)/d leaves a contiguous interval
of conductors. Its polynomial phase has curvature comparable to k/D
throughout D ≤ m ≤ 2D and d comparable to D^r. Summing conductors before
divisors gives a power saving after normalization by the product horizon,
uniformly over signed weights dominated by the von Mangoldt function.
-/

noncomputable section
open Finset

namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

private theorem monomial_derivative (a b x : ℝ) (n : ℕ) :
    HasDerivAt (fun y : ℝ => a*y^(n+1)+b) (a*((n:ℝ)+1)*x^n) x := by
  convert! ((((hasDerivAt_id x).pow (n+1)).const_mul a).add_const b) using 1
  simp only [id_eq,Nat.cast_succ,Nat.add_sub_cancel,mul_one]
  ring

private theorem monomial_derivative' (a x : ℝ) (n : ℕ) :
    HasDerivAt (fun y : ℝ => a*y^(n+1)) (a*((n:ℝ)+1)*x^n) x := by
  simpa only [add_zero] using monomial_derivative a 0 x n

/-- Every positive integral frequency has square-root cancellation up
to its frequency loss, uniformly over both ends of the conductor interval. -/
theorem conductor_monomial_phase_bound (s : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {D d k a b : ℝ} {N : ℕ}, 0 < D → 1 ≤ k →
      D^(s+1) ≤ d → d ≤ 2*(2*D)^(s+1) → D ≤ a →
      a+((N-1:ℕ):ℝ) ≤ 2*D → (N:ℝ) ≤ D →
      ‖∑ n ∈ range N, Complex.exp (((2*Real.pi*((k/d)*(a+n)^(s+2)+b) : ℝ) : ℂ)*Complex.I)‖ ≤
        C*Real.sqrt (D*k) := by
  let G : ℝ := ((s:ℝ)+2)*((s:ℝ)+1)*2^s
  let L : ℝ := 2*2^(s+1)
  have hG : 0 ≤ G := by dsimp only [G]; positivity
  have hL : 1 ≤ L := by
    have hh := one_le_pow₀ (by norm_num : (1:ℝ) ≤ 2) (n := s+1)
    dsimp only [L]; linarith
  have hC : 1 ≤ 8*G+12*Real.sqrt L+1 := by linarith only [hG,Real.sqrt_nonneg L]
  refine ⟨8*G+12*Real.sqrt L+1,hC,?_⟩
  intro D d k a b N hD hk hdlo hdhi ha hend hN
  have hkpos : 0 < k := zero_lt_one.trans_le hk
  have hd : 0 < d := (pow_pos hD _).trans_le hdlo
  have hroot := Real.sqrt_nonneg (D*k)
  have hsq := Real.sq_sqrt (mul_pos hD hkpos).le
  rcases eq_zero_or_pos N with rfl | hlen
  · simp only [range_zero,sum_empty,norm_zero]
    positivity
  by_cases hkD : k ≤ D
  · let A := k/d
    let t := A*D^s
    have hA : 0 < A := div_pos hkpos hd
    have ht : 0 < t := mul_pos hA (pow_pos hD _)
    have htd : t*D ≤ k := by
      change (k/d*D^s)*D ≤ k
      rw [mul_assoc,←pow_succ,div_mul_eq_mul_div,div_le_iff₀ hd]
      exact mul_le_mul_of_nonneg_left hdlo hkpos.le
    have ht1 : t ≤ 1 := (le_div_iff₀ hD).mpr (htd.trans hkD) |>.trans_eq (div_self hD.ne')
    have hdL : d ≤ L*D^(s+1) := by simpa only [L,mul_pow,mul_assoc] using hdhi
    have hkt : k ≤ L*(t*D) := by
      change k ≤ L*((k/d*D^s)*D)
      rw [mul_assoc (k/d),←pow_succ]
      calc k = (k/d)*d := (div_mul_cancel₀ _ hd.ne').symm
           _ ≤ (k/d)*(L*D^(s+1)) := mul_le_mul_of_nonneg_left hdL hA.le
           _ = _ := by ring
    let c := (s:ℝ)+2
    let e := (s:ℝ)+1
    have hce : 1 ≤ c*e := by
      apply one_le_mul_of_one_le_of_one_le <;> dsimp only [c,e] <;> linarith only [Nat.cast_nonneg (α:=ℝ) s]
    have hh := _root_.RHTower.Sieve.second_derivative_test'
      (fun x => A*x^(s+2)+b) (fun x => (A*c)*x^(s+1)) (fun x => (A*c*e)*x^s) a N hlen ht ht1
      (fun x _ => by simpa only [c,Nat.cast_succ,add_assoc,one_add_one_eq_two] using monomial_derivative A b x (s+1))
      (fun x _ => monomial_derivative' (A*c) x s)
      (fun x hx => by
        have h1 := pow_le_pow_left₀ hD.le (ha.trans hx.1) s
        calc t ≤ A*x^s := mul_le_mul_of_nonneg_left h1 hA.le
             _ ≤ c*e*(A*x^s) := le_mul_of_one_le_left (mul_nonneg hA.le (pow_nonneg (hD.le.trans (ha.trans hx.1)) _)) hce
             _ = _ := by ring)
      (hgrow := G)
      (fun x hx => by
        have h1 := pow_le_pow_left₀ (hD.le.trans (ha.trans hx.1)) (hx.2.trans hend) s
        have hp : 0 ≤ A*c*e := by dsimp only [c,e]; positivity
        calc A*c*e*x^s ≤ A*c*e*(2*D)^s := mul_le_mul_of_nonneg_left h1 hp
             _ = G*t := by dsimp only [G,t,c,e]; rw [mul_pow]; ring)
    have hprod : D*Real.sqrt t ≤ Real.sqrt (D*k) := by
      apply (Real.le_sqrt (by positivity) (by positivity)).mpr
      rw [mul_pow,Real.sq_sqrt ht.le]
      calc D^2*t = D*(t*D) := by ring
           _ ≤ D*k := mul_le_mul_of_nonneg_left htd hD.le
    have hk1 : 1 ≤ k^2 := one_le_pow₀ hk
    have hinv : 1/Real.sqrt t ≤ Real.sqrt L*Real.sqrt (D*k) := by
      rw [div_le_iff₀ (Real.sqrt_pos.mpr ht)]
      have h1 := mul_le_mul_of_nonneg_right hkt hkpos.le
      have h2 : 1 ≤ (Real.sqrt L*Real.sqrt (D*k)*Real.sqrt t)^2 := by
        simp only [mul_pow,Real.sq_sqrt (zero_le_one.trans hL),Real.sq_sqrt (mul_pos hD hkpos).le,Real.sq_sqrt ht.le]
        nlinarith only [hk1,h1]
      exact le_of_not_gt fun hz => (not_lt_of_ge h2) (by nlinarith only [mul_self_lt_mul_self (by positivity : 0 ≤ Real.sqrt L*Real.sqrt (D*k)*Real.sqrt t) hz])
    have hm := (mul_le_mul_of_nonneg_right hN (Real.sqrt_nonneg t)).trans hprod
    have hu := add_le_add (mul_le_mul_of_nonneg_left hm (by positivity : 0 ≤ 8*G))
      (mul_le_mul_of_nonneg_left hinv (by norm_num : (0:ℝ) ≤ 12))
    change _ ≤ 8*(N:ℝ)*G*Real.sqrt t+12/Real.sqrt t at hh
    apply hh.trans
    calc _ = 8*G*((N:ℝ)*Real.sqrt t)+12*(1/Real.sqrt t) := by ring
         _ ≤ _ := hu
         _ ≤ _ := by linarith only [hroot]
  · have hsmall : D ≤ Real.sqrt (D*k) := (Real.le_sqrt hD.le (mul_pos hD hkpos).le).mpr (by
      nlinarith only [mul_le_mul_of_nonneg_left (le_of_not_ge hkD) hD.le])
    apply (norm_sum_le _ _).trans
    simp only [Complex.norm_exp,Complex.mul_I_re,Complex.ofReal_im,neg_zero,Real.exp_zero,
      sum_const,card_range,nsmul_eq_mul,mul_one]
    exact (hN.trans hsmall).trans (le_mul_of_one_le_left hroot hC)

private def sqrtModeWeight (H j : ℕ) : ℝ :=
  if j ≤ H then 1/Real.sqrt j else (H:ℝ)/Real.sqrt ((j:ℝ)^3)

private theorem sqrt_mode_sum {H : ℕ} (hH : 0 < H) (N : ℕ) :
    ∑ j ∈ Ioo 0 N,sqrtModeWeight H j ≤ 4*Real.sqrt H := by
  let s := Ioo 0 N
  have hl : s.filter (· ≤ H) ⊆ Icc 1 H := fun _ h =>
    mem_Icc.mpr ⟨(mem_Ioo.mp (mem_filter.mp h).1).1,(mem_filter.mp h).2⟩
  have hu : s.filter (fun j => ¬j ≤ H) ⊆ Icc (H+1) (max N H) := by
    intro j h
    obtain ⟨hj,hj'⟩ := mem_filter.mp h
    exact mem_Icc.mpr ⟨by omega,(mem_Ioo.mp hj).2.le.trans (le_max_left ..)⟩
  have low := (sum_le_sum_of_subset_of_nonneg (f:=fun j : ℕ => 1/Real.sqrt j) hl
    fun _ _ _ => by positivity).trans (_root_.RHTower.sum_inv_sqrt_le H)
  have tail := _root_.RHTower.sum_inv_sqrt_cube_le (R:=H+1) (by omega) (max N H) (by omega)
  simp only [Nat.add_one_sub_one] at tail
  have high := (sum_le_sum_of_subset_of_nonneg
    (f:=fun j : ℕ => 1/Real.sqrt ((j:ℝ)^3)) hu fun _ _ _ => by positivity).trans tail
  change (∑ j ∈ s,_) ≤ _
  rw [←sum_filter_add_sum_filter_not s (· ≤ H) (sqrtModeWeight H)]
  have eqL (j : ℕ) (hj : j ∈ s.filter (· ≤ H)) :
      sqrtModeWeight H j=1/Real.sqrt j := if_pos (mem_filter.mp hj).2
  have eqU (j : ℕ) (hj : j ∈ s.filter (fun j => ¬j ≤ H)) :
      sqrtModeWeight H j=(H:ℝ)*(1/Real.sqrt ((j:ℝ)^3)) := by
    rw [sqrtModeWeight,if_neg (mem_filter.mp hj).2,mul_one_div]
  rw [sum_congr rfl eqL,sum_congr rfl eqU,←mul_sum]
  apply (add_le_add low (mul_le_mul_of_nonneg_left high (Nat.cast_nonneg H))).trans_eq
  have hp := Real.sqrt_pos.mpr (Nat.cast_pos.mpr hH : 0 < (H:ℝ))
  field_simp [hp.ne']
  nlinarith only [Real.sq_sqrt (Nat.cast_nonneg (α:=ℝ) H)]

/-- Summing square-root harmonic estimates below and above the inverse
smoothing width costs its square root, including the discontinuity at zero. -/
private theorem sqrt_harmonic_discrepancy :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {N H : ℕ}, 0 < H → ∀ (y : ℕ → ℝ) {M : ℝ}, 0 ≤ M →
      (∀ h : ℤ, h ≠ 0 → ‖∑ i ∈ range N,fourier h (y i : UnitAddCircle)‖ ≤ M*Real.sqrt |(h:ℝ)|) →
      |∑ i ∈ range N,(Int.fract (y i)-1/2)| ≤ B*((N:ℝ)/H+M*Real.sqrt H) := by
  obtain ⟨A,hA,hdec⟩ := GaloisForLFunctions.HTGeometry.SmoothedSawtooth.exists_saw_decomposition
  refine ⟨16*A,by positivity,?_⟩
  intro N H hH y M hM hmode
  have hp : 0 < (H:ℝ) := Nat.cast_pos.mpr hH
  let δ := (H:ℝ)⁻¹
  have hδ : 0 < δ := inv_pos.mpr hp
  obtain ⟨a,k,has,hks,ha,hk,hd⟩ := hdec δ hδ
  let E (h : ℤ) := ‖∑ i ∈ range N,fourier h (y i : UnitAddCircle)‖
  have head := hd (range N) y (fun _ => (1:ℂ)) (fun _ => (1:ℝ)) (fun _ => by simp)
  have sa := GaloisForLFunctions.HTGeometry.SmoothedSawtooth.summable_mul_norm_sum
    (range N) (fun _ => (1:ℂ)) y has
  have sk := GaloisForLFunctions.HTGeometry.SmoothedSawtooth.summable_mul_norm_sum
    (range N) (fun _ => (1:ℂ)) y hks
  simp only [one_mul,Complex.ofReal_one,←Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs,
    GaloisForLFunctions.HTGeometry.SmoothedSawtooth.saw] at head sa sk
  rw [←sa.tsum_add sk] at head
  apply head.trans
  apply le_of_tendsto (sa.add sk).hasSum
  apply Filter.Eventually.of_forall
  intro t
  let Z := A*δ*N
  have zbound : (∑ h ∈ t,if h=0 then Z else 0) ≤ Z := by
    rw [sum_ite_eq']
    split_ifs
    · exact le_rfl
    · dsimp only [Z]; positivity
  have total := _root_.RHTower.LogLatticePoisson.sum_int_natAbs_le (g:=sqrtModeWeight H)
    (fun j => by unfold sqrtModeWeight; split_ifs <;> positivity) (sqrt_mode_sum hH) t
  have ht : (∑ h ∈ t,(‖a h‖*E h+‖k h‖*E h)) ≤
      (∑ h ∈ t,if h=0 then Z else 0)+2*A*M*∑ h ∈ t.filter (fun h => h≠0),sqrtModeWeight H h.natAbs := by
    rw [sum_filter,mul_sum,←sum_add_distrib]
    apply sum_le_sum
    intro h _
    rcases eq_or_ne h 0 with rfl | hh
    · have ha0 : ‖a 0‖=0 := le_antisymm (by simpa using ha 0) (norm_nonneg _)
      have hk0 : ‖k 0‖ ≤ A*δ := by simpa using hk 0
      simpa [E,Z,ha0] using mul_le_mul_of_nonneg_right hk0 (Nat.cast_nonneg (α:=ℝ) N)
    · let u := |(h:ℝ)|
      have hu : 0 < u := abs_pos.mpr (by exact_mod_cast hh)
      have he : ((h:ℝ)*δ)^2=(u*δ)^2 := by dsimp only [u]; rw [mul_pow,mul_pow,sq_abs]
      have hav := ha h
      have hkv := hk h
      rw [he] at hav hkv
      change ‖a h‖ ≤ A*(1+(u*δ)^2)⁻¹/u at hav
      have hu' : (h.natAbs:ℝ)=u := by rw [Nat.cast_natAbs,Int.cast_abs]
      have ht : 0 < 1+(u*δ)^2 := by positivity
      have key : ‖a h‖+‖k h‖ ≤ A*(1+u*δ)/(u*(1+(u*δ)^2)) :=
        (add_le_add hav hkv).trans_eq (by field_simp)
      have hr := Real.sq_sqrt hu.le
      have hrs := Real.sqrt_pos.mpr hu
      have hz : (1+u*δ) ≤ 2*(1+(u*δ)^2) := by nlinarith only [sq_nonneg (u*δ-1/2)]
      have hzt : (1+u*δ)*(u*δ) ≤ 2*(1+(u*δ)^2) := by nlinarith only [sq_nonneg (u*δ-1/2)]
      have coeff := (mul_le_mul_of_nonneg_right key (norm_nonneg _)).trans
        (mul_le_mul_of_nonneg_left (hmode h hh) (by positivity))
      simp only [if_neg hh,if_pos hh,zero_add,←add_mul]
      apply coeff.trans
      change A*(1+u*δ)/(u*(1+(u*δ)^2))*(M*Real.sqrt u) ≤ _
      rw [sqrtModeWeight]
      have hsqr : Real.sqrt u/u=1/Real.sqrt u := by
        field_simp [hu.ne',hrs.ne']
        nlinarith only [hr]
      have repr : A*(1+u*δ)/(u*(1+(u*δ)^2))*(M*Real.sqrt u) =
          (A*M/Real.sqrt u)*((1+u*δ)/(1+(u*δ)^2)) := by
        calc _ = (A*M*((1+u*δ)/(1+(u*δ)^2)))*(Real.sqrt u/u) := by
                   simp only [div_eq_mul_inv,mul_inv_rev]
                   ring
             _ = _ := by rw [hsqr]; ring
      rw [repr]
      by_cases hj : h.natAbs ≤ H
      · rw [if_pos hj,hu']
        exact (mul_le_mul_of_nonneg_left ((div_le_iff₀ ht).mpr hz)
          (by positivity : 0 ≤ A*M/Real.sqrt u)).trans_eq (by ring)
      · rw [if_neg hj,hu',show u^3=u^2*u by ring,Real.sqrt_mul (sq_nonneg u),Real.sqrt_sq hu.le]
        calc _ = (A*M*(H:ℝ)/(u*Real.sqrt u))*((1+u*δ)*(u*δ)/(1+(u*δ)^2)) := by
                   dsimp only [δ]
                   field_simp [hu.ne',hrs.ne',hp.ne'] <;> ring
             _ ≤ (A*M*(H:ℝ)/(u*Real.sqrt u))*2 := mul_le_mul_of_nonneg_left ((div_le_iff₀ ht).mpr hzt) (by positivity)
             _ = _ := by ring
  apply ht.trans ((add_le_add zbound (mul_le_mul_of_nonneg_left total (by positivity))).trans ?_)
  dsimp only [Z,δ]
  rw [div_eq_mul_inv]
  linarith only [mul_nonneg (mul_nonneg hA (inv_nonneg.mpr hp.le)) (Nat.cast_nonneg (α:=ℝ) N)]

private theorem power_quotient_harmonics (s : ℕ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ {D d a : ℝ} {N : ℕ}, 0 < D → D^(s+1) ≤ d →
      d ≤ 2*(2*D)^(s+1) → D ≤ a → a+((N-1:ℕ):ℝ) ≤ 2*D → (N:ℝ) ≤ D →
      ∀ k : ℤ, k ≠ 0 → ‖∑ n ∈ range N,fourier k (((a+n)^(s+2)/d:ℝ) : UnitAddCircle)‖ ≤
        C*Real.sqrt D*Real.sqrt |(k:ℝ)| := by
  obtain ⟨C,hC,hf⟩ := conductor_monomial_phase_bound s
  refine ⟨C,hC,?_⟩
  intro D d a N hD hlo hhi ha he hN
  let y (n : ℕ) := (a+n)^(s+2)/d
  have posmode (k : ℤ) (hk : 0 < k) :
      ‖∑ n ∈ range N, fourier k (y n : UnitAddCircle)‖ ≤ C*Real.sqrt D*Real.sqrt |(k:ℝ)| := by
    have hk1 : (1:ℝ) ≤ k := by exact_mod_cast (show (1:ℤ) ≤ k by omega)
    have ht := hf (b := 0) hD hk1 hlo hhi ha he hN
    rw [Real.sqrt_mul hD.le] at ht
    rw [mul_assoc,abs_of_pos (zero_lt_one.trans_le hk1)]
    apply le_trans _ ht
    apply le_of_eq
    congr 1
    apply sum_congr rfl
    intro n _
    rw [fourier_coe_apply]
    dsimp only [y]
    congr 1
    push_cast
    ring
  have mode (k : ℤ) (hk : k ≠ 0) :
      ‖∑ n ∈ range N, fourier k (y n : UnitAddCircle)‖ ≤ C*Real.sqrt D*Real.sqrt |(k:ℝ)| := by
    rcases lt_or_gt_of_ne hk with hn | hp
    · simpa only [fourier_neg,←map_sum,RCLike.norm_conj,Int.cast_neg,abs_neg] using posmode (-k) (neg_pos.mpr hn)
    · exact posmode k hp
  exact mode

/-- Centered fractional parts on every subinterval, including divisibilities.
Taking δ equal to D^(-1/4) gives total discrepancy of order D^(3/4). -/
theorem centered_power_quotient_fragment (s : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {D d a : ℝ} {N : ℕ}, 0 < D → D^(s+1) ≤ d →
      d ≤ 2*(2*D)^(s+1) → D ≤ a → a+((N-1:ℕ):ℝ) ≤ 2*D → (N:ℝ) ≤ D →
      ∀ δ : ℝ, 0 < δ →
        |∑ n ∈ range N, (Int.fract ((a+n)^(s+2)/d)-1/2)| ≤ B*(δ*D+Real.sqrt D/δ) := by
  obtain ⟨C,hC,hf⟩ := power_quotient_harmonics s
  obtain ⟨K,hK,hs⟩ := GaloisForLFunctions.PrimeExponentialSums.sawtooth_of_sqrt_harmonics
  have hC0 := zero_le_one.trans hC
  refine ⟨K*C,mul_nonneg hK hC0,?_⟩
  intro D d a N hD hlo hhi ha he hN δ hδ
  let y (n : ℕ) := (a+n)^(s+2)/d
  have mode := hf hD hlo hhi ha he hN
  have ht := hs (range N) y (fun _ => (1:ℂ)) (fun _ => (1:ℝ)) hδ
    (mul_nonneg hC0 (Real.sqrt_nonneg D)) (fun _ => by simp) (fun k hk => by
      simpa only [Complex.ofReal_one,one_mul,and_self] using mode k hk)
  have hu : |∑ n ∈ range N, (Int.fract ((a+n)^(s+2)/d)-1/2)| ≤
      K*(δ*N+(C*Real.sqrt D)/δ) := by
    simpa only [one_mul,←Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs,
      GaloisForLFunctions.HTGeometry.SmoothedSawtooth.saw,y,sum_const,card_range,nsmul_eq_mul,mul_one] using ht
  have hmul := (mul_le_mul_of_nonneg_left hN hδ.le).trans
    (le_mul_of_one_le_left (mul_nonneg hδ.le hD.le) hC)
  apply hu.trans
  calc K*(δ*N+(C*Real.sqrt D)/δ) ≤ K*(C*(δ*D)+(C*Real.sqrt D)/δ) :=
           mul_le_mul_of_nonneg_left (add_le_add hmul le_rfl) hK
       _ = _ := by ring

private theorem sharp_power_quotient_fragment (s : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ {D d a : ℝ} {N : ℕ}, 1 ≤ D → D^(s+1) ≤ d →
      d ≤ 2*(2*D)^(s+1) → D ≤ a → a+((N-1:ℕ):ℝ) ≤ 2*D → (N:ℝ) ≤ D →
      |∑ n ∈ range N,(Int.fract ((a+n)^(s+2)/d)-1/2)| ≤ B*D^(2/3:ℝ) := by
  obtain ⟨C,hC,hm⟩ := power_quotient_harmonics s
  obtain ⟨B,hB,h⟩ := sqrt_harmonic_discrepancy
  have hC0 := zero_le_one.trans hC
  refine ⟨B*(1+2*C),by positivity,?_⟩
  intro D d a N hD hlo hhi ha he hN
  have hD0 := zero_lt_one.trans_le hD
  let R := D^(1/3:ℝ)
  let H := ⌈R⌉₊
  have hR : 1 ≤ R := Real.one_le_rpow hD (by norm_num)
  have hR0 := zero_lt_one.trans_le hR
  have hRH : R ≤ (H:ℝ) := Nat.le_ceil _
  have hHp := hR0.trans_le hRH
  have hH : (H:ℝ) ≤ 2*R := (Nat.ceil_lt_add_one hR0.le).le.trans (by linarith only [hR])
  have hs : Real.sqrt (H:ℝ) ≤ 2*Real.sqrt R := by
    calc Real.sqrt (H:ℝ) ≤ Real.sqrt (4*R) := Real.sqrt_le_sqrt (by linarith only [hH,hR])
         _ = _ := by rw [Real.sqrt_mul (by norm_num : (0:ℝ)≤4),show Real.sqrt 4=2 by norm_num]
  have hs' := h (Nat.cast_pos.mp hHp) (fun n : ℕ => (a+n)^(s+2)/d)
    (mul_nonneg hC0 (Real.sqrt_nonneg D)) (hm hD0 hlo hhi ha he hN)
  have he1 : D/R=D^(2/3:ℝ) := by
    calc _ = D^((1:ℝ)-1/3) := by rw [Real.rpow_sub hD0,Real.rpow_one]
         _ = _ := by norm_num
  have he2 : Real.sqrt D*Real.sqrt R=D^(2/3:ℝ) := by
    rw [Real.sqrt_eq_rpow,Real.sqrt_eq_rpow]
    dsimp only [R]
    rw [←Real.rpow_mul hD0.le,←Real.rpow_add hD0]
    norm_num
  have h1 := (div_le_div_of_nonneg_right hN hHp.le).trans (div_le_div_of_nonneg_left hD0.le hR0 hRH)
  rw [he1] at h1
  have h2 := mul_le_mul_of_nonneg_left hs (mul_nonneg hC0 (Real.sqrt_nonneg D))
  apply hs'.trans ((mul_le_mul_of_nonneg_left (add_le_add h1 h2) hB).trans_eq ?_)
  rw [←he2]
  ring

private def eligibleConductors (s D K d : ℕ) :=
  (Ioc D K).filter (fun m => m^(s+1) < d ∧ d ≤ 2*m^(s+1))

private theorem conductor_interval {s D K d : ℕ} (h : (eligibleConductors s D K d).Nonempty) :
    ∃ a b : ℕ, D < a ∧ b ≤ K ∧ a ≤ b ∧ eligibleConductors s D K d=Icc a b := by
  let S := eligibleConductors s D K d
  let a := S.min' h
  let b := S.max' h
  have ha : a ∈ S := min'_mem _ _
  have hb : b ∈ S := max'_mem _ _
  obtain ⟨haI,haL,haR⟩ := mem_filter.mp ha
  obtain ⟨hbI,hbL,hbR⟩ := mem_filter.mp hb
  refine ⟨a,b,(mem_Ioc.mp haI).1,(mem_Ioc.mp hbI).2,S.min'_le b hb,?_⟩
  ext m
  constructor
  · intro hm
    exact mem_Icc.mpr ⟨S.min'_le _ hm,S.le_max' _ hm⟩
  · intro hm
    obtain ⟨hl,hu⟩ := mem_Icc.mp hm
    exact mem_filter.mpr ⟨mem_Ioc.mpr ⟨(mem_Ioc.mp haI).1.trans_le hl,hu.trans (mem_Ioc.mp hbI).2⟩,
      (Nat.pow_le_pow_left hu _).trans_lt hbL,haR.trans (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hl _))⟩

/-- Centered fractional part of the original multiplication horizon divided by d. -/
def centeredPowerQuotient (s d m : ℕ) : ℝ := Int.fract ((m:ℝ)^(s+2)/d)-1/2

/-- At a fixed divisor the eligible power-sampled conductors form a
single sharp interval, even on an incomplete octave. -/
private theorem centered_conductors_at_divisor (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {D K d : ℕ}, 1 ≤ D → K ≤ 2*D →
      |∑ m ∈ eligibleConductors s D K d,centeredPowerQuotient s d m| ≤
        C*(D:ℝ)^(2/3:ℝ) := by
  obtain ⟨C,hC,hs⟩ := sharp_power_quotient_fragment s
  refine ⟨C,hC,?_⟩
  intro D K d hD hK
  rcases (eligibleConductors s D K d).eq_empty_or_nonempty with hz | hn
  · rw [hz,sum_empty,abs_zero]
    positivity
  obtain ⟨a,b,ha,hb,hab,he⟩ := conductor_interval hn
  have hma : a ∈ eligibleConductors s D K d := he ▸ left_mem_Icc.mpr hab
  obtain ⟨_,haL,haR⟩ := mem_filter.mp hma
  have hdlo : (D:ℝ)^(s+1) ≤ d := by
    exact_mod_cast (Nat.pow_le_pow_left ha.le (s+1)).trans haL.le
  have hdhi : (d:ℝ) ≤ 2*(2*(D:ℝ))^(s+1) := by
    exact_mod_cast haR.trans (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left (hab.trans (hb.trans hK)) (s+1)))
  let N := b+1-a
  have hN : (N:ℝ) ≤ D := by exact_mod_cast (show N ≤ D by dsimp only [N]; omega)
  have hend : (a:ℝ)+((N-1:ℕ):ℝ) ≤ 2*D := by
    exact_mod_cast (show a+(N-1) ≤ 2*D by dsimp only [N]; omega)
  have h := hs (Nat.one_le_cast.mpr hD) hdlo hdhi (Nat.cast_le.mpr ha.le) hend hN
  rw [he,←Ico_add_one_right_eq_Icc,sum_Ico_eq_sum_range]
  simpa only [centeredPowerQuotient,Nat.cast_add,N] using h

private def signedFloorCoefficient (s d m : ℕ) : ℝ :=
  if m^(s+1) < d ∧ d ≤ 2*m^(s+1) then centeredPowerQuotient s d m else 0

/-- A decreasing conductor weight costs only its first value on each
sharp fragment of the moving divisor interval. -/
private theorem weighted_conductors_at_divisor (s : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {D K : ℕ}, 1 ≤ D → D ≤ K → K ≤ 2*D →
      ∀ d : ℕ,
      |∑ m ∈ Ioc D K, ((m:ℝ)^(s+2))⁻¹*signedFloorCoefficient s d m| ≤
        C*(D:ℝ)^(2/3:ℝ)*((D:ℝ)^(s+2))⁻¹ := by
  obtain ⟨C,hC,h⟩ := centered_conductors_at_divisor s
  refine ⟨C,hC,?_⟩
  intro D K hD hDK hK d
  have hp : 0 < (D:ℝ) := Nat.cast_pos.mpr hD
  have hB : 0 ≤ C*(D:ℝ)^(2/3:ℝ) := by positivity
  rcases hDK.eq_or_lt with rfl | hlt
  · rw [Ioc_self,sum_empty,abs_zero]; positivity
  let w (m : ℕ) := ((m:ℝ)^(s+2))⁻¹
  have hw {a b : ℕ} (ha : 0 < a) (hab : a ≤ b) : w b ≤ w a :=
    inv_anti₀ (pow_pos (Nat.cast_pos.mpr ha) _) (pow_le_pow_left₀ (Nat.cast_nonneg _) (Nat.cast_le.mpr hab) _)
  have pref (n : ℕ) (hn : n ∈ Ioc D K) :
      ‖∑ m ∈ Ioc D n, ((signedFloorCoefficient s d m:ℝ):ℂ)‖ ≤ C*(D:ℝ)^(2/3:ℝ) := by
    rw [←Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs]
    simpa only [eligibleConductors,sum_filter,signedFloorCoefficient] using h hD ((mem_Ioc.mp hn).2.trans hK) (d := d)
  have hb := _root_.RHTower.norm_sum_Ioc_weight_mul_le (fun m => ((signedFloorCoefficient s d m:ℝ):ℂ)) w hlt
    (fun m => by dsimp only [w]; positivity) (fun m hm => hw (hD.trans (mem_Ioc.mp hm).1.le) (Nat.le_succ _)) pref
  simp only [←Complex.ofReal_mul,←Complex.ofReal_sum,Complex.norm_real,Real.norm_eq_abs] at hb
  exact hb.trans (mul_le_mul_of_nonneg_left (hw hD (Nat.le_succ _)) hB)


/-- Total centered division error, normalized by the product horizon,
on one arbitrary partial octave of conductors. -/
def sparseFloorFragment (s D K : ℕ) (w : ℕ → ℝ) : ℝ :=
  ∑ m ∈ Ioc D K, ((m:ℝ)^(s+2))⁻¹*
    ∑ d ∈ Ioc (m^(s+1)) (2*m^(s+1)), w d*centeredPowerQuotient s d m

private theorem transpose_floor_fragment (s D K : ℕ) (hK : K ≤ 2*D) (w : ℕ → ℝ) :
    sparseFloorFragment s D K w =
      ∑ d ∈ Icc 1 (2*(2*D)^(s+1)),w d *
        ∑ m ∈ Ioc D K,((m:ℝ)^(s+2))⁻¹*signedFloorCoefficient s d m := by
  let U := 2*(2*D)^(s+1)
  have he (m : ℕ) (hm : m ∈ Ioc D K) :
      (∑ d ∈ Ioc (m^(s+1)) (2*m^(s+1)), w d*centeredPowerQuotient s d m)=
        ∑ d ∈ Icc 1 U, w d*signedFloorCoefficient s d m := by
    have hu : 2*m^(s+1) ≤ U := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ((mem_Ioc.mp hm).2.trans hK) _)
    have hset : (Icc 1 U).filter (fun d => m^(s+1) < d ∧ d ≤ 2*m^(s+1)) =
        Ioc (m^(s+1)) (2*m^(s+1)) := by
      ext d; simp only [mem_filter,mem_Icc,mem_Ioc]; omega
    rw [←hset,sum_filter]
    exact sum_congr rfl fun d _ => by dsimp only [signedFloorCoefficient]; split_ifs <;> simp
  rw [sparseFloorFragment,sum_congr rfl (fun (m : ℕ) hm => congrArg (fun z : ℝ => ((m:ℝ)^(s+2))⁻¹*z) (he m hm))]
  simp only [mul_sum]
  rw [sum_comm]
  exact sum_congr rfl fun d _ => sum_congr rfl fun m _ => by ring

/-- The centered floor term costs a summable power on each octave even
after assigning independent signed weights up to Λ(d) to its divisors. -/
theorem sparse_floor_fragment_cubic_saving (s : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {D K : ℕ}, 1 ≤ D → D ≤ K → K ≤ 2*D →
      ∀ w : ℕ → ℝ, (∀ d, |w d| ≤ ArithmeticFunction.vonMangoldt d) →
      |sparseFloorFragment s D K w| ≤ A*(D:ℝ)^(-(1/3):ℝ) := by
  obtain ⟨C,hC,h⟩ := weighted_conductors_at_divisor s
  let L : ℝ := 2*2^(s+1)
  have hL : 0 ≤ L := by dsimp only [L]; positivity
  refine ⟨7*L*C,by positivity,?_⟩
  intro D K hD hDK hK w hw
  have hDr : 0 < (D:ℝ) := Nat.cast_pos.mpr hD
  let U := 2*(2*D)^(s+1)
  let V := C*(D:ℝ)^(2/3:ℝ)*((D:ℝ)^(s+2))⁻¹
  have hV : 0 ≤ V := by dsimp only [V]; positivity
  let f (d : ℕ) := ∑ m ∈ Ioc D K,((m:ℝ)^(s+2))⁻¹*signedFloorCoefficient s d m
  have hsum : |sparseFloorFragment s D K w| ≤ (7*(U:ℝ))*V := by
    rw [transpose_floor_fragment _ _ _ hK]
    apply (abs_sum_le_sum_abs _ _).trans
    calc (∑ d ∈ Icc 1 U, |w d*f d|) ≤ ∑ d ∈ Icc 1 U,ArithmeticFunction.vonMangoldt d*V := by
           apply sum_le_sum
           intro d _
           rw [abs_mul]
           exact mul_le_mul (hw _) (h hD hDK hK d) (abs_nonneg _) ArithmeticFunction.vonMangoldt_nonneg
         _ ≤ _ := by rw [←sum_mul]; exact mul_le_mul_of_nonneg_right (_root_.RHTower.sum_vonMangoldt_Icc_le_seven U) hV
  have hu : (U:ℝ)=L*(D:ℝ)^(s+1) := by dsimp only [U,L]; push_cast; rw [mul_pow]; ring
  have he : (D:ℝ)^(2/3:ℝ)=(D:ℝ)^(-(1/3):ℝ)*D := by
    rw [←show (D:ℝ)^((-(1/3):ℝ)+1)=(D:ℝ)^(-(1/3):ℝ)*D by rw [Real.rpow_add hDr,Real.rpow_one]]
    norm_num
  apply hsum.trans_eq
  rw [hu]
  dsimp only [V]
  rw [he,show (D:ℝ)^(s+2)=(D:ℝ)^(s+1)*D by rw [pow_succ]]
  field_simp

/-- The weaker quarter-power saving follows on the same partial octave. -/
theorem sparse_floor_fragment_uniform (s : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ {D K : ℕ}, 1 ≤ D → D ≤ K → K ≤ 2*D →
      ∀ w : ℕ → ℝ, (∀ d, |w d| ≤ ArithmeticFunction.vonMangoldt d) →
      |sparseFloorFragment s D K w| ≤ A*(D:ℝ)^(-(1/4):ℝ) := by
  obtain ⟨A,hA,h⟩ := sparse_floor_fragment_cubic_saving s
  refine ⟨A,hA,fun hD hDK hK w hw => (h hD hDK hK w hw).trans ?_⟩
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hD) (by norm_num)) hA

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
