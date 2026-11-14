import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.ZetaSamplingCompressionMatrix
import Zeta23.Final

/-!
# The pole does not affect the fourth prime compression moment

The established second source moment bounds the pure prime second moment after
removing the bounded archimedean and pole matrices. The pole operator estimate
then applies to the quartic perturbation bound without a prime fourth-moment
assumption.
-/

open MeasureTheory Matrix Real Zeta23 Filter Topology
open scoped ComplexConjugate Matrix.Norms.L2Operator

noncomputable section

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- The literal full source compression has the second moment computed by the
prime-side trace theorem, with its exact normalization. -/
theorem matrixFrobeniusEnergy_zetaSamplingCompression_nuX (P : Params) (T : ℝ) :
    matrixFrobeniusEnergy (zetaSamplingCompression P T (nuX (P.X T))) =
      P.trGtildeSq T / (P.a T ^ 2 * P.L T ^ 2) := by
  have he (i j : Fin (P.d T)) :
      zetaSamplingCompression P T (nuX (P.X T)) i j =
        ((P.Gentry T i j / (P.a T * P.L T ^ 2) : ℝ) : ℂ) := by
    rw [zetaSamplingCompression, Params.Gentry]
    congr 2
    apply integral_congr_ae
    filter_upwards [] with τ
    ring
  simp only [matrixFrobeniusEnergy, he, Complex.norm_real, Real.norm_eq_abs, sq_abs,
    div_pow, ← Finset.sum_div, Params.trGtildeSq]
  simp only [div_eq_mul_inv, mul_pow, mul_inv_rev, inv_pow]
  ring

/-- At bandwidth one the full source has a uniformly bounded normalized second moment. -/
theorem exists_zetaSamplingCompression_source_second_bound {P : Params}
    (hP : P.Valid) (hlam : P.lam = 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      matrixFrobeniusEnergy (zetaSamplingCompression P T (nuX (P.X T))) ≤ C * (P.d T : ℝ) := by
  obtain ⟨C,hC,T₁,htr⟩ := (PrimeSide.thm_traces hP paperInputs_zeta).tr2
  have hcal := (Assembly.calE_tendsto_zero P hP.lam_pos hP.lam_le_one
    (zero_le_one.trans hP.one_le_w)).eventually (Iio_mem_nhds (by norm_num : (0:ℝ)<1))
  obtain ⟨T₂,hT₂⟩ := eventually_atTop.mp hcal
  obtain ⟨T₃,hT₃⟩ := zetaSampling_bandwidth_eventually_ge hP
    (max (8*P.w) (max 1 |2*Real.log 2-1|))
  refine ⟨40*(C+1), by positivity, max T₁ (max T₂ (max T₃ (4*π))), fun T hT => ?_⟩
  have ht₁ : T₁ ≤ T := (le_max_left _ _).trans hT
  have ht₂ : T₂ ≤ T := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hT
  have ht₃ : T₃ ≤ T := (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hT
  have htπ : 4*π ≤ T := (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hT
  have hb := hT₃ T ht₃
  have hwL : 8*P.w ≤ P.L T := (le_max_left _ _).trans hb
  have hL1 : 1 ≤ P.L T := ((le_max_left _ _).trans (le_max_right _ _)).trans hb
  have hL0 : 0 < P.L T := zero_lt_one.trans_le hL1
  have hcL : |2*Real.log 2-1| ≤ P.L T := ((le_max_right _ _).trans (le_max_right _ _)).trans hb
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) htπ
  have ha := Params.half_le_a hP hwL
  have ha0 : 0 < P.a T := by linarith only [ha]
  have ha2 : 1/4 ≤ P.a T ^ 2 := by nlinarith only [ha]
  have heL : P.L T = l T := by change P.lam * l T = l T; rw [hlam,one_mul]
  have hell : |ell1 T| ≤ 2*P.L T := by
    change |l T + 2*Real.log 2-1| ≤ _
    have hh := abs_add_le (P.L T) (2*Real.log 2-1)
    rw [abs_of_pos hL0] at hh
    rw [← heL]
    linarith only [hh,hcL]
  have hell2 : ell1 T ^ 2 ≤ 4*P.L T ^ 2 := by
    have hh := mul_self_le_mul_self (abs_nonneg (ell1 T)) hell
    nlinarith only [hh, sq_abs (ell1 T)]
  let F : ℝ := P.L T*T/(2*π)
  have hF2 : 2 ≤ F := by
    dsimp [F]
    rw [le_div_iff₀ (by positivity : 0 < 2*π)]
    have hh := mul_le_mul_of_nonneg_right hL1 hT0.le
    nlinarith only [hh,htπ]
  have hF0 : 0 ≤ F := by linarith only [hF2]
  have hFd : F ≤ 2*(P.d T : ℝ) := by
    have hh : F < (P.d T : ℝ)+1 := Nat.lt_floor_add_one F
    linarith only [hh,hF2]
  have hm0 : 0 ≤ P.mainTr2 T := by unfold Params.mainTr2; positivity
  have hm : P.mainTr2 T ≤ F*(5*P.L T ^ 2) := by
    unfold Params.mainTr2
    have hfactor : ell1 T ^ 2 + P.L T ^ 2/3 ≤ 5*P.L T ^ 2 := by
      nlinarith only [hell2,sq_nonneg (P.L T)]
    simpa only [mul_comm T (P.L T)] using
      mul_le_mul_of_nonneg_left hfactor (show 0 ≤ F by linarith only [hF2])
  have htr' : P.trGtildeSq T ≤ (C+1)*P.mainTr2 T := by
    have hh := (le_abs_self (P.trGtildeSq T-P.mainTr2 T)).trans (htr T ht₁)
    have hh' := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (hT₂ T ht₂).le hC.le) hm0
    nlinarith only [hh,hh']
  rw [matrixFrobeniusEnergy_zetaSamplingCompression_nuX]
  calc
    _ ≤ ((C+1)*(F*(5*P.L T ^ 2))) / (P.a T ^ 2*P.L T ^ 2) := by
      apply div_le_div_of_nonneg_right
        (htr'.trans (mul_le_mul_of_nonneg_left hm (by positivity))) (by positivity)
    _ = 5*(C+1)*F/(P.a T ^ 2) := by field_simp <;> ring
    _ ≤ 5*(C+1)*F/(1/4) := by
      apply div_le_div_of_nonneg_left (by positivity) (by norm_num) ha2
    _ = 20*(C+1)*F := by ring
    _ ≤ 20*(C+1)*(2*(P.d T : ℝ)) := mul_le_mul_of_nonneg_left hFd (by positivity)
    _ = _ := by ring

/-- Chebyshev's prime-power bound gives the operator bound for the literal pure
prime matrix at every sufficiently large height. -/
theorem exists_zetaSamplingCompression_prime_norm_bound {P : Params} (hP : P.Valid) :
    ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ‖zetaSamplingCompression P T (PX (P.X T))‖ ≤ 2*π*Real.sqrt (P.X T)/(P.a T*P.L T) := by
  obtain ⟨x₀,hx₀⟩ := Cheb.chebyshevMertens.cheb1b
  obtain ⟨T₀,hT₀⟩ := zetaSampling_bandwidth_eventually_ge hP
    (max (8*P.w) (Real.log (max x₀ 1)))
  refine ⟨T₀, fun T hT => ?_⟩
  have hh := hT₀ T hT
  have hwL : 8*P.w ≤ P.L T := (le_max_left _ _).trans hh
  have hX : x₀ ≤ P.X T := by
    calc
      _ ≤ max x₀ 1 := le_max_left _ _
      _ = Real.exp (Real.log (max x₀ 1)) := (Real.exp_log (by positivity)).symm
      _ ≤ Real.exp (P.L T) := Real.exp_le_exp.mpr ((le_max_right _ _).trans hh)
  apply norm_zetaSamplingCompression_le_of_bound hP hwL (PrimeSide.PX_continuous _)
  intro τ
  calc
    _ ≤ (1/π)*∑ n ∈ Finset.Ioc 0 ⌊P.X T⌋₊,
        ArithmeticFunction.vonMangoldt n / Real.sqrt n := PX_abs_le _ _
    _ ≤ (1/π)*(3*Real.sqrt (P.X T)) :=
      mul_le_mul_of_nonneg_left (hx₀ _ hX) (by positivity)
    _ ≤ Real.sqrt (P.X T) := by
      rw [div_mul_eq_mul_div,one_mul,div_le_iff₀ Real.pi_pos]
      nlinarith only [Real.sqrt_nonneg (P.X T),Real.pi_gt_three]

/-- The literal full-line source splits into its three density matrices. -/
theorem zetaSamplingCompression_nuX_split {P : Params} (hP : P.Valid) {T : ℝ}
    (hwL : 8*P.w ≤ P.L T) :
    zetaSamplingCompression P T (nuX (P.X T)) =
      zetaSamplingCompression P T mu + zetaSamplingCompression P T (PiX (P.X T)) +
      zetaSamplingCompression P T (PX (P.X T)) := by
  obtain ⟨A,_,hμ⟩ := exists_mu_linear_bound
  have hL : 0 < P.L T := by linarith only [hwL,hP.one_le_w]
  have hX : 1 ≤ P.X T := by
    change 1 ≤ Real.exp (P.L T)
    simpa only [Real.exp_zero] using Real.exp_le_exp.mpr hL.le
  have hπ (τ : ℝ) : |PiX (P.X T) τ| ≤ 3*Real.sqrt (P.X T)+|τ| := by
    exact ((PiX_abs_le hX τ).trans
      (div_le_self (by positivity) (by linarith only [abs_nonneg τ]))).trans
      (le_add_of_nonneg_right (abs_nonneg τ))
  ext i j
  have hiμ := integrable_linearDensity_sampling_mul hP hwL gammaFacts.smooth.continuous hμ
    (P.tau T i) (P.tau T j)
  have hiπ := integrable_linearDensity_sampling_mul hP hwL
    (PiX_continuous (zero_lt_one.trans_le hX)) hπ (P.tau T i) (P.tau T j)
  have hip := integrable_linearDensity_sampling_mul hP hwL (PrimeSide.PX_continuous (P.X T))
    (fun τ => (PX_abs_le (P.X T) τ).trans (le_add_of_nonneg_right (abs_nonneg τ)))
    (P.tau T i) (P.tau T j)
  simp only [zetaSamplingCompression,Matrix.add_apply,nuX,add_mul]
  rw [integral_add (hiμ.add hiπ) hip,integral_add hiμ hiπ]
  push_cast
  ring

/-- The pure prime matrix has bounded normalized second moment at bandwidth one. -/
theorem exists_zetaSamplingCompression_prime_second_bound {P : Params}
    (hP : P.Valid) (hlam : P.lam = 1) :
    ∃ C : ℝ, 0 < C ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      matrixFrobeniusEnergy (zetaSamplingCompression P T (PX (P.X T))) ≤ C*(P.d T : ℝ) := by
  obtain ⟨C,hC,T₁,hT₁⟩ := exists_zetaSamplingCompression_source_second_bound hP hlam
  obtain ⟨T₂,hT₂⟩ := zetaSamplingCompression_archimedean_eventually_bounded hP hlam
  obtain ⟨T₃,hT₃⟩ := zetaSamplingCompression_pole_uniformly_small hP zero_lt_one
  obtain ⟨T₄,hT₄⟩ := zetaSampling_inverse_bandwidth_uniformly_small hP
    (show (0:ℝ) ≤ 0 from le_rfl) zero_lt_one
  refine ⟨4*C+38,by positivity,max T₁ (max T₂ (max T₃ T₄)),fun T hT => ?_⟩
  have ht₁ : T₁ ≤ T := (le_max_left _ _).trans hT
  have ht₂ : T₂ ≤ T := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hT
  have ht₃ : T₃ ≤ T := (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hT
  have ht₄ : T₄ ≤ T := (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hT
  obtain ⟨hwL,htπ,_⟩ := hT₄ T ht₄
  letI : Nonempty (Fin (P.d T)) := Fin.pos_iff_nonempty.mp (zetaSampling_dimension_pos hP hwL htπ)
  let S := zetaSamplingCompression P T (nuX (P.X T))
  let M := zetaSamplingCompression P T mu
  let Q := zetaSamplingCompression P T (PiX (P.X T))
  have he : zetaSamplingCompression P T (PX (P.X T)) = (S-M)-Q := by
    have hh := zetaSamplingCompression_nuX_split hP hwL
    dsimp [S,M,Q]
    rw [hh]
    abel
  have hM : matrixFrobeniusEnergy M ≤ 9*(P.d T : ℝ) := by
    calc
      _ ≤ (P.d T : ℝ)*‖M‖^2 := by simpa only [Fintype.card_fin] using matrixFrobeniusEnergy_le_dim_opNorm_sq M
      _ ≤ (P.d T : ℝ)*3^2 := by gcongr; exact hT₂ T ht₂
      _ = _ := by ring
  have hQ : matrixFrobeniusEnergy Q ≤ (P.d T : ℝ) := by
    calc
      _ ≤ (P.d T : ℝ)*‖Q‖^2 := by simpa only [Fintype.card_fin] using matrixFrobeniusEnergy_le_dim_opNorm_sq Q
      _ ≤ (P.d T : ℝ)*1^2 := by gcongr; exact hT₃ T ht₃
      _ = _ := by ring
  rw [he]
  have hh₁ := matrixFrobeniusEnergy_sub_le (S-M) Q
  have hh₂ := matrixFrobeniusEnergy_sub_le S M
  have hh₃ := hT₁ T ht₁
  change matrixFrobeniusEnergy S ≤ C*(P.d T : ℝ) at hh₃
  linarith only [hh₁,hh₂,hh₃,hM,hQ]

private theorem norm_trace_fourth_perturbation_scaled {n : Type*} [Fintype n] [DecidableEq n]
    [Nonempty n] (P Q : Matrix n n ℂ) {A B C L s : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hC : 0 ≤ C) (hL : 1 ≤ L) (hs : 1 ≤ s)
    (hP : ‖P‖ ≤ A*s/L) (hQ : ‖Q‖ ≤ B/(s*L))
    (hE : matrixFrobeniusEnergy P ≤ C*(Fintype.card n : ℝ)) :
    ‖((P+Q)^4-P^4).trace‖ ≤
      (4*A*B*C+6*B^2*C+4*B^3*Real.sqrt C+B^4)*(Fintype.card n : ℝ)/L^2 := by
  have hL0 : 0 < L := zero_lt_one.trans_le hL
  have hs0 : 0 < s := zero_lt_one.trans_le hs
  have hE0 : 0 ≤ matrixFrobeniusEnergy P := by unfold matrixFrobeniusEnergy; positivity
  have hq : ‖Q‖ ≤ B/L := hQ.trans (div_le_div_of_nonneg_left hB hL0
    (by nlinarith only [hL,hs]))
  have hpq : ‖P‖*‖Q‖ ≤ A*B/L^2 := by
    calc
      _ ≤ (A*s/L)*(B/(s*L)) := mul_le_mul hP hQ (norm_nonneg _) (by positivity)
      _ = _ := by field_simp <;> ring
  have hq2 : ‖Q‖^2 ≤ B^2/L^2 := by simpa only [div_pow] using pow_le_pow_left₀ (norm_nonneg _) hq 2
  have hL3 : L^2 ≤ L^3 := by
    nlinarith only [mul_nonneg (sq_nonneg L) (sub_nonneg.mpr hL)]
  have hL4 : L^2 ≤ L^4 := by
    have hh : 1 ≤ L^2 := by nlinarith only [hL]
    nlinarith only [mul_nonneg (sq_nonneg L) (sub_nonneg.mpr hh)]
  have hq3 : ‖Q‖^3 ≤ B^3/L^2 := by
    calc
      _ ≤ (B/L)^3 := pow_le_pow_left₀ (norm_nonneg _) hq 3
      _ = B^3/L^3 := div_pow _ _ _
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hL0) hL3
  have hq4 : ‖Q‖^4 ≤ B^4/L^2 := by
    calc
      _ ≤ (B/L)^4 := pow_le_pow_left₀ (norm_nonneg _) hq 4
      _ = B^4/L^4 := div_pow _ _ _
      _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (sq_pos_of_pos hL0) hL4
  have hroot : Real.sqrt (matrixFrobeniusEnergy P) ≤ Real.sqrt C * Real.sqrt (Fintype.card n : ℝ) := by
    simpa only [Real.sqrt_mul hC] using Real.sqrt_le_sqrt hE
  calc
    _ ≤ 4*‖P‖*‖Q‖*matrixFrobeniusEnergy P + 6*‖Q‖^2*matrixFrobeniusEnergy P +
        4*‖Q‖^3*Real.sqrt (Fintype.card n : ℝ)*Real.sqrt (matrixFrobeniusEnergy P) +
        (Fintype.card n : ℝ)*‖Q‖^4 := norm_trace_fourth_perturbation_le_secondMoment P Q
    _ ≤ 4*(A*B/L^2)*(C*(Fintype.card n : ℝ)) + 6*(B^2/L^2)*(C*(Fintype.card n : ℝ)) +
        4*(B^3/L^2)*Real.sqrt (Fintype.card n : ℝ)*(Real.sqrt C*Real.sqrt (Fintype.card n : ℝ)) +
        (Fintype.card n : ℝ)*(B^4/L^2) := by
      rw [mul_assoc 4 ‖P‖]
      gcongr
    _ = _ := by
      have hh : Real.sqrt (Fintype.card n : ℝ) *
          (Real.sqrt C * Real.sqrt (Fintype.card n : ℝ)) =
          Real.sqrt C * (Fintype.card n : ℝ) := by
        calc
          _ = Real.sqrt C * (Real.sqrt (Fintype.card n : ℝ) * Real.sqrt (Fintype.card n : ℝ)) := by ring
          _ = _ := by rw [Real.mul_self_sqrt (Nat.cast_nonneg _)]
      rw [mul_assoc (4*(B^3/L^2)),hh]
      ring

/-- At bandwidth one, adding the literal pole matrix changes the normalized prime
fourth trace by `O(L⁻²)`. Only the prime second moment is used. -/
theorem zetaSamplingCompression_pole_fourth_error_le_inverse_bandwidth_sq
    {P : Params} (hP : P.Valid) (hlam : P.lam = 1) :
    ∃ K : ℝ, 0 < K ∧ ∃ T₀ : ℝ, ∀ T : ℝ, T₀ ≤ T →
      ‖((zetaSamplingCompression P T (PX (P.X T)) +
          zetaSamplingCompression P T (PiX (P.X T)))^4 -
          (zetaSamplingCompression P T (PX (P.X T)))^4).trace‖ ≤
        K*(P.d T : ℝ)/P.L T ^ 2 := by
  obtain ⟨C,hC,T₁,hT₁⟩ := exists_zetaSamplingCompression_prime_second_bound hP hlam
  obtain ⟨T₂,hT₂⟩ := exists_zetaSamplingCompression_prime_norm_bound hP
  obtain ⟨T₃,hT₃⟩ := zetaSampling_bandwidth_eventually_ge hP (max (8*P.w) 1)
  let A : ℝ := 4*π
  let B : ℝ := 2*poleCompressionConstant P
  have hA : 0 < A := by dsimp [A]; positivity
  have hB : 0 < B := mul_pos (by norm_num) (poleCompressionConstant_pos P)
  refine ⟨4*A*B*C+6*B^2*C+4*B^3*Real.sqrt C+B^4,by positivity,
    max T₁ (max T₂ (max T₃ (4*π))),fun T hT => ?_⟩
  have ht₁ : T₁ ≤ T := (le_max_left _ _).trans hT
  have ht₂ : T₂ ≤ T := (le_trans (le_max_left _ _) (le_max_right _ _)).trans hT
  have ht₃ : T₃ ≤ T := (le_trans (le_max_left _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hT
  have htπ : 4*π ≤ T := (le_trans (le_max_right _ _) (le_trans (le_max_right _ _) (le_max_right _ _))).trans hT
  have hb := hT₃ T ht₃
  have hwL : 8*P.w ≤ P.L T := (le_max_left _ _).trans hb
  have hL1 : 1 ≤ P.L T := (le_max_right _ _).trans hb
  have hL : 0 < P.L T := zero_lt_one.trans_le hL1
  have hT0 : 0 < T := lt_of_lt_of_le (by positivity) htπ
  have ht1 : 1 ≤ T := by linarith only [htπ,Real.pi_gt_three]
  have hs : 1 ≤ Real.sqrt T := by simpa only [Real.sqrt_one] using Real.sqrt_le_sqrt ht1
  have hs0 : 0 < Real.sqrt T := Real.sqrt_pos.mpr hT0
  have ha := Params.half_le_a hP hwL
  have ha0 : 0 < P.a T := by linarith only [ha]
  have hX : P.X T ≤ T := by
    have he : P.X T = T/(2*π) := by
      change Real.exp (P.lam*l T) = _
      rw [hlam,one_mul,l,Real.exp_log (by positivity : 0<T/(2*π))]
    rw [he]
    exact div_le_self hT0.le (by linarith only [Real.pi_gt_three])
  have hF : 2 ≤ P.L T*T/(2*π) := by
    rw [le_div_iff₀ (by positivity : 0<2*π)]
    have hh := mul_le_mul_of_nonneg_right hL1 hT0.le
    nlinarith only [hh,htπ]
  have hdf : P.L T*T/(2*π) < (P.d T : ℝ)+1 := Nat.lt_floor_add_one _
  have hd : 0 < P.d T := by
    have hh : (0:ℝ) < P.d T := by linarith only [hF,hdf]
    exact_mod_cast hh
  letI : Nonempty (Fin (P.d T)) := Fin.pos_iff_nonempty.mp hd
  have hp : ‖zetaSamplingCompression P T (PX (P.X T))‖ ≤ A*Real.sqrt T/P.L T := by
    calc
      _ ≤ 2*π*Real.sqrt (P.X T)/(P.a T*P.L T) := hT₂ T ht₂
      _ ≤ 2*π*Real.sqrt T/(P.a T*P.L T) := by gcongr
      _ ≤ 2*π*Real.sqrt T/((1/2)*P.L T) := by
        apply div_le_div_of_nonneg_left (by positivity) (by positivity)
        exact mul_le_mul_of_nonneg_right ha hL.le
      _ = _ := by dsimp [A]; field_simp <;> ring
  have hq : ‖zetaSamplingCompression P T (PiX (P.X T))‖ ≤ B/(Real.sqrt T*P.L T) := by
    calc
      _ ≤ poleCompressionConstant P*Real.sqrt (P.X T)/(P.a T*P.L T*T) :=
        norm_zetaSamplingCompression_pole_le hP hwL hT0
      _ ≤ poleCompressionConstant P*Real.sqrt T/(P.a T*P.L T*T) := by
        have := poleCompressionConstant_pos P
        gcongr
      _ ≤ poleCompressionConstant P*Real.sqrt T/((1/2)*P.L T*T) := by
        apply div_le_div_of_nonneg_left (by have := poleCompressionConstant_pos P; positivity) (by positivity)
        gcongr
      _ = _ := by
        dsimp [B]
        calc
          _ = 2*poleCompressionConstant P*Real.sqrt T/(P.L T*T) := by field_simp <;> ring
          _ = 2*poleCompressionConstant P*Real.sqrt T/(P.L T*(Real.sqrt T)^2) := by
            rw [Real.sq_sqrt hT0.le]
          _ = _ := by field_simp <;> ring
  simpa only [Fintype.card_fin] using norm_trace_fourth_perturbation_scaled
    (zetaSamplingCompression P T (PX (P.X T))) (zetaSamplingCompression P T (PiX (P.X T)))
    hA.le hB.le hC.le hL1 hs hp hq (by simpa only [Fintype.card_fin] using hT₁ T ht₁)

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri

#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.exists_zetaSamplingCompression_prime_second_bound
#print axioms GaloisForLFunctions.ArithmeticCastelnuovoSeveri.zetaSamplingCompression_pole_fourth_error_le_inverse_bandwidth_sq
