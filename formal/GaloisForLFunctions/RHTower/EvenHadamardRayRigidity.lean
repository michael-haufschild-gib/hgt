import GaloisForLFunctions.RHTower.OrderOneHadamardFactorization
import GaloisForLFunctions.HTGeometry.OrderOneEnvelopeRootDivision

/-!
# Real-ray rigidity for reflected square differences

An even entire function of order one with imaginary zeros has real-ray modulus
at least its origin value. Applied to the even and odd parts of a square root,
this bounds the root whenever its reflected square difference is an exponential pair.
-/

open Complex Filter Topology
open GaloisForLFunctions.EntireZeroDivisor GaloisForLFunctions.CountableDivisor

namespace RHTower.OrderOneHadamard


theorem one_le_norm_weierstrassE1_of_re_zero {z : ℂ} (hz : z.re = 0) :
    1 ≤ ‖weierstrassE1 z‖ := by
  rw [weierstrassE1, norm_mul, Complex.norm_exp, hz, Real.exp_zero, mul_one]
  have h := Complex.re_le_norm (1 - z)
  simpa [hz] using h

theorem one_le_norm_hadamardProduct_real {f : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ f Set.univ) (hf0 : f 0 ≠ 0)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    (hzeros : ∀ z, f z = 0 → z.re = 0) (x : ℝ) :
    1 ≤ ‖hadamardProduct f x‖ := by
  have hsum := summable_inv_sq_zeroCopyPoint hC hf hf0 hbound
  have hmult := multipliable_canonicalProductE1Indexed (zeroCopyPoint_ne_zero hf hf0) hsum (x : ℂ)
  rw [hadamardProduct, canonicalProductE1Indexed, hmult.norm_tprod]
  apply le_of_tendsto_of_tendsto' tendsto_const_nhds hmult.norm.hasProd
  intro s
  apply Finset.one_le_prod
  intro q _
  apply one_le_norm_weierstrassE1_of_re_zero
  have hzero : f (zeroCopyPoint f q) = 0 := by
    by_contra hn
    have hdiv : (MeromorphicOn.divisor f Set.univ) (zeroCopyPoint f q) ≠ 0 := q.1.2
    apply hdiv
    rw [divisor_univ_eq_analyticOrder hf,
      (hf _ (Set.mem_univ _)).analyticOrderAt_eq_zero.mpr hn]
    simp
  have hz : (zeroCopyPoint f q).re = 0 := hzeros _ hzero
  simp [Complex.div_re, hz]

theorem norm_zero_le_norm_real_of_even_imaginary_zeros {f : ℂ → ℂ} {C : ℝ} (hC : 0 ≤ C)
    (hf : AnalyticOnNhd ℂ f Set.univ) (hf0 : f 0 ≠ 0)
    (hford : ∀ z, analyticOrderAt f z ≠ ⊤) (heven : ∀ z, f (-z) = f z)
    (hbound : ∀ z : ℂ, ‖f z‖ ≤ Real.exp (C * (1 + ‖z‖) * Real.log (2 + ‖z‖)))
    (hzeros : ∀ z, f z = 0 → z.re = 0) (x : ℝ) :
    ‖f 0‖ ≤ ‖f x‖ := by
  rw [eq_const_mul_hadamardProduct_of_even hC hf hf0 hford heven hbound (x : ℂ), norm_mul]
  exact le_mul_of_one_le_right (norm_nonneg (f 0)) (one_le_norm_hadamardProduct_real hC hf hf0 hbound hzeros x)

end RHTower.OrderOneHadamard

namespace RHTower.OrderOneHadamard
open GaloisForLFunctions.HTGeometry

private theorem norm_zero_le_real_of_envelope {f : ℂ → ℂ}
    (hf : Differentiable ℂ f) (ho : OrderOneEnvelope f) (h0 : f 0 ≠ 0)
    (he : ∀ z, f (-z) = f z) (hz : ∀ z, f z = 0 → z.re = 0) (x : ℝ) :
    ‖f 0‖ ≤ ‖f x‖ := by
  obtain ⟨C, hC, hb⟩ := ho
  have han : AnalyticOnNhd ℂ f Set.univ := fun z _ => hf.analyticAt z
  have hord : ∀ z, analyticOrderAt f z ≠ ⊤ := by
    intro z heq
    have hfzero : f = (fun _ => 0) := han.eq_of_eventuallyEq
      (fun _ _ => analyticAt_const) (analyticOrderAt_eq_top.mp heq)
    exact h0 (congrFun hfzero 0)
  exact norm_zero_le_norm_real_of_even_imaginary_zeros hC.le han h0 hord he hb hz x

private theorem re_zero_of_exp_reflect_eq {h : ℝ} (hh : h ≠ 0) {z : ℂ}
    (he : Complex.exp ((h : ℂ) * z) = Complex.exp ((h : ℂ) * (-z))) : z.re = 0 := by
  have hn := congrArg norm he
  simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.neg_re] at hn
  have hlin := Real.exp_injective hn
  have hz : h * z.re = 0 := by linarith
  exact (mul_eq_zero.mp hz).resolve_left hh

/-- A finite-order root whose reflected square difference is an exponential pair
has at most exponential growth on the positive real ray. -/
theorem exists_real_exp_bound_of_reflected_square_difference
    {g : ℂ → ℂ} (hg : Differentiable ℂ g) (hgo : OrderOneEnvelope g)
    {c : ℂ} (hc : c ≠ 0) {h : ℝ} (hh : h ≠ 0)
    (hrel : ∀ z : ℂ, g z ^ 2 - g (-z) ^ 2 =
      c * (Complex.exp ((h : ℂ) * z) - Complex.exp ((h : ℂ) * (-z)))) :
    ∃ A : ℝ, 0 < A ∧ ∀ x : ℝ, 1 ≤ x → ‖g x‖ ≤ A * Real.exp (|h| * x) := by
  let E : ℂ → ℂ := fun z => g z + g (-z)
  let O : ℂ → ℂ := fun z => g z - g (-z)
  let H : ℂ → ℂ := dslope O 0
  have hEd : Differentiable ℂ E := by dsimp [E]; fun_prop
  have hOd : Differentiable ℂ O := by dsimp [O]; fun_prop
  have hO0 : O 0 = 0 := by simp [O]
  have hHd : Differentiable ℂ H := by
    rw [← differentiableOn_univ]
    exact (Complex.differentiableOn_dslope (Filter.univ_mem : Set.univ ∈ 𝓝 (0 : ℂ))).mpr
      hOd.differentiableOn
  have hEO (z : ℂ) : E z * O z =
      c * (Complex.exp ((h : ℂ) * z) - Complex.exp ((h : ℂ) * (-z))) := by
    calc E z * O z = g z ^ 2 - g (-z) ^ 2 := by dsimp [E, O]; ring
      _ = _ := hrel z
  have hOH (z : ℂ) : z * H z = O z := by
    simpa [H, hO0, smul_eq_mul] using sub_smul_dslope O (0 : ℂ) z
  have hderivRight : HasDerivAt (fun z : ℂ =>
      c * (Complex.exp ((h : ℂ) * z) - Complex.exp ((h : ℂ) * (-z))))
      (2 * c * (h : ℂ)) 0 := by
    have hp : HasDerivAt (fun z : ℂ => Complex.exp ((h : ℂ) * z)) (h : ℂ) 0 := by
      simpa using (((hasDerivAt_id (0 : ℂ)).const_mul (h : ℂ)).cexp)
    have hm : HasDerivAt (fun z : ℂ => Complex.exp ((h : ℂ) * (-z))) (-(h : ℂ)) 0 := by
      simpa using ((((hasDerivAt_id (0 : ℂ)).neg).const_mul (h : ℂ)).cexp)
    have hd := (hp.sub hm).const_mul c
    have he : c * ((h : ℂ) - -(h : ℂ)) = 2 * c * (h : ℂ) := by ring
    rw [he] at hd
    exact hd
  have hderivLeft := (hEd 0).hasDerivAt.mul (hOd 0).hasDerivAt
  change HasDerivAt (fun z => E z * O z) _ _ at hderivLeft
  rw [show (fun z => E z * O z) = _ from funext hEO] at hderivLeft
  have hcenter : E 0 * H 0 = 2 * c * (h : ℂ) := by
    have heq := hderivLeft.unique hderivRight
    simpa [H, dslope_same, hO0] using heq
  have hcenter_ne : E 0 * H 0 ≠ 0 := by
    rw [hcenter]
    exact mul_ne_zero (mul_ne_zero (by norm_num) hc) (by exact_mod_cast hh)
  have hE0 := (mul_ne_zero_iff.mp hcenter_ne).1
  have hH0 := (mul_ne_zero_iff.mp hcenter_ne).2
  have hEeven (z : ℂ) : E (-z) = E z := by simp [E, add_comm]
  have hHeven (z : ℂ) : H (-z) = H z := by
    by_cases hz : z = 0
    · simp [hz]
    · have hneg := hOH (-z)
      have hpos := hOH z
      have hodd : O (-z) = -O z := by simp [O]
      rw [hodd] at hneg
      apply mul_left_cancel₀ hz
      linear_combination -hneg - hpos
  have hzero (z : ℂ) (hz : E z = 0 ∨ O z = 0) : z.re = 0 := by
    have hp := hEO z
    have hprod : E z * O z = 0 := by rcases hz with hz | hz <;> simp [hz]
    rw [hprod] at hp
    have heq := (mul_eq_zero.mp hp.symm).resolve_left hc
    exact re_zero_of_exp_reflect_eq hh (sub_eq_zero.mp heq)
  have hEzeros (z : ℂ) (hz : E z = 0) : z.re = 0 := hzero z (Or.inl hz)
  have hHzeros (z : ℂ) (hz : H z = 0) : z.re = 0 := by
    apply hzero z (Or.inr ?_)
    rw [← hOH z, hz, mul_zero]
  have hgrefl : OrderOneEnvelope (fun z => g (-z)) :=
    (hgo.comp_affine (-1) 0).congr (fun z => by simp)
  have hEo : OrderOneEnvelope E := hgo.add hgrefl
  have hOo : OrderOneEnvelope O :=
    (hgo.add (hgrefl.const_mul (-1))).congr (fun z => by dsimp [O]; ring)
  have hHo : OrderOneEnvelope H := hOo.dslope_zero hOd hO0
  have hElo := norm_zero_le_real_of_envelope hEd hEo hE0 hEeven hEzeros
  have hHlo := norm_zero_le_real_of_envelope hHd hHo hH0 hHeven hHzeros
  have hEpos : 0 < ‖E 0‖ := norm_pos_iff.mpr hE0
  have hHpos : 0 < ‖H 0‖ := norm_pos_iff.mpr hH0
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hc
  let A : ℝ := 2 * ‖c‖ / ‖H 0‖ + 2 * ‖c‖ / ‖E 0‖
  refine ⟨A, by dsimp [A]; positivity, fun x hx => ?_⟩
  have hx0 : 0 ≤ x := by linarith
  have hprodBound : ‖E x‖ * ‖O x‖ ≤ 2 * ‖c‖ * Real.exp (|h| * x) := by
    rw [← norm_mul, hEO, norm_mul]
    have heplus : ‖Complex.exp ((h : ℂ) * (x : ℂ))‖ ≤ Real.exp (|h| * x) := by
      simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        mul_zero, sub_zero]
      exact Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_right (le_abs_self h) hx0)
    have heminus : ‖Complex.exp ((h : ℂ) * (-(x : ℂ)))‖ ≤ Real.exp (|h| * x) := by
      simp only [Complex.norm_exp, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.neg_re, Complex.neg_im, neg_zero, mul_zero, sub_zero]
      apply Real.exp_le_exp.mpr
      nlinarith [mul_le_mul_of_nonneg_right (neg_le_abs h) hx0]
    have ht := norm_sub_le (Complex.exp ((h : ℂ) * (x : ℂ)))
      (Complex.exp ((h : ℂ) * (-(x : ℂ))))
    nlinarith [mul_le_mul_of_nonneg_left (ht.trans (add_le_add heplus heminus)) (norm_nonneg c)]
  have hOlo : ‖H 0‖ ≤ ‖O x‖ := by
    have hn := congrArg norm (hOH (x : ℂ))
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx0] at hn
    have hlo := hHlo x
    nlinarith [norm_nonneg (H x)]
  have hEup : ‖E x‖ ≤ (2 * ‖c‖ / ‖H 0‖) * Real.exp (|h| * x) := by
    have hp := mul_le_mul_of_nonneg_left hOlo (norm_nonneg (E x))
    have hb : ‖E x‖ * ‖H 0‖ ≤ 2 * ‖c‖ * Real.exp (|h| * x) := hp.trans hprodBound
    have hd := (le_div_iff₀ hHpos).mpr hb
    calc _ ≤ _ := hd
         _ = _ := by ring
  have hOup : ‖O x‖ ≤ (2 * ‖c‖ / ‖E 0‖) * Real.exp (|h| * x) := by
    have hp := mul_le_mul_of_nonneg_right (hElo x) (norm_nonneg (O x))
    have hb : ‖O x‖ * ‖E 0‖ ≤ 2 * ‖c‖ * Real.exp (|h| * x) := by nlinarith [hp, hprodBound]
    have hd := (le_div_iff₀ hEpos).mpr hb
    calc _ ≤ _ := hd
         _ = _ := by ring
  have hsum : E (x : ℂ) + O x = 2 * g x := by dsimp [E, O]; ring
  have hn := norm_add_le (E (x : ℂ)) (O x)
  rw [hsum, norm_mul, show ‖(2 : ℂ)‖ = (2 : ℝ) by norm_num] at hn
  dsimp [A]
  nlinarith [norm_nonneg (g x)]

end RHTower.OrderOneHadamard
