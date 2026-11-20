import GaloisForLFunctions.BezoutValuationIncidence.ReceiverBoundedInTheZeroFreeBandBelowHalfDamping

/-!
# Reciprocal octaves of a square-root counting law

Abel summation transfers a square-root asymptotic of the signed
prefix to its reciprocal-weighted octave. In the model prefix √n the
reciprocal increments telescope after a factor tending uniformly to one.
-/

noncomputable section
open Filter Finset
open scoped Topology
namespace GaloisForLFunctions.ReciprocalOctaves

private abbrev root (n : ℕ) : ℝ := Real.sqrt n
private def step (d : ℕ) := root d-root (d-1)
private def drop (d : ℕ) := (root (d-1))⁻¹-(root d)⁻¹

/-- Reciprocal reading of an arithmetic weight on the sharp octave (M,2M]. -/
def price (a : ℕ → ℝ) (M : ℕ) : ℝ := ∑ d ∈ Ioc M (2*M), a d/(d:ℝ)

private theorem prefix_step (n : ℕ) : ∑ d ∈ Icc 1 n, step d = root n := by
  induction n with
  | zero => simp [root]
  | succ n ih => rw [sum_Icc_succ_top (by omega),ih]; simp [step]

private theorem ratio_one :
    Tendsto (fun d : ℕ => root (d-1)/root d) atTop (𝓝 1) := by
  have h := (tendsto_const_nhds (x:=(1:ℝ))).div_atTop (tendsto_natCast_atTop_atTop (R:=ℝ))
  have hh := ((tendsto_const_nhds (x:=(1:ℝ))).sub h).sqrt
  rw [sub_zero,Real.sqrt_one] at hh
  apply hh.congr'
  filter_upwards [eventually_ge_atTop (1:ℕ)] with d hd
  rw [←Real.sqrt_div (Nat.cast_nonneg (d-1)),Nat.cast_sub hd,Nat.cast_one]
  congr 1
  field_simp [Nat.cast_ne_zero.mpr (Nat.ne_of_gt hd)]

private theorem drop_nonneg {d : ℕ} (hd : 2 ≤ d) : 0 ≤ drop d :=
  sub_nonneg.mpr (inv_anti₀ (Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega)))
    (Real.sqrt_le_sqrt (Nat.cast_le.mpr (Nat.sub_le ..))))

private theorem step_as_drop {d : ℕ} (hd : 2 ≤ d) :
    step d/d = drop d*(root (d-1)/root d) := by
  have hp := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega : 0<d-1) : 0<((d-1:ℕ):ℝ))
  have hq := Real.sqrt_pos.mpr (Nat.cast_pos.mpr (by omega : 0<d) : 0<(d:ℝ))
  calc step d/d = (root d-root (d-1))/(root d)^2 := by rw [Real.sq_sqrt (Nat.cast_nonneg d)]; rfl
       _ = _ := by dsimp only [drop,root]; field_simp

private theorem drop_sum {M : ℕ} (hm : 0 < M) :
    root M*(∑ d ∈ Ioc M (2*M), drop d) = 1-1/Real.sqrt 2 := by
  have tel {N : ℕ} (h : M ≤ N) : ∑ d ∈ Ioc M N, drop d = (root M)⁻¹-(root N)⁻¹ := by
    induction N,h using Nat.le_induction with
    | base => simp
    | succ n hn ih => rw [sum_Ioc_succ_top hn,ih]; simp [drop]
  rw [tel (by omega)]
  dsimp only [root]
  rw [Nat.cast_mul,Nat.cast_ofNat,Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2)]
  field_simp [Real.sqrt_pos.mpr (Nat.cast_pos.mpr hm : 0<(M:ℝ)) |>.ne']

private theorem model_octave :
    Tendsto (fun M : ℕ => root M*price step M) atTop (𝓝 (1-1/Real.sqrt 2)) := by
  apply Metric.tendsto_atTop.mpr
  intro ε ep
  obtain ⟨K,hK⟩ := eventually_atTop.mp ((ratio_one.eventually_const_lt
    (show 1-ε/2 < 1 by linarith only [ep])).and (ratio_one.eventually_lt_const
    (show 1 < 1+ε/2 by linarith only [ep])))
  refine ⟨max 1 K,fun M hm => ?_⟩
  have mp := (le_max_left 1 K).trans hm
  have hb (d : ℕ) (hd : d ∈ Ioc M (2*M)) := hK d ((le_max_right 1 K).trans (hm.trans (mem_Ioc.mp hd).1.le))
  have hn (d : ℕ) (hd : d ∈ Ioc M (2*M)) : 2 ≤ d := by have := (mem_Ioc.mp hd).1; omega
  have compare (d : ℕ) (hd : d ∈ Ioc M (2*M)) :
      |step d/d-drop d| ≤ (ε/2)*drop d := by
    rw [step_as_drop (hn d hd),show drop d*(root (d-1)/root d)-drop d=
      (root (d-1)/root d-1)*drop d by ring,abs_mul,abs_of_nonneg (drop_nonneg (hn d hd))]
    apply mul_le_mul_of_nonneg_right _ (drop_nonneg (hn d hd))
    exact abs_le.mpr ⟨by linarith only [(hb d hd).1],by linarith only [(hb d hd).2]⟩
  rw [Real.dist_eq,←drop_sum mp,←mul_sub,abs_mul,abs_of_nonneg (Real.sqrt_nonneg _)]
  dsimp only [price]
  rw [←sum_sub_distrib]
  have he := (abs_sum_le_sum_abs ..).trans (sum_le_sum compare)
  rw [←mul_sum] at he
  have hh := mul_le_mul_of_nonneg_left he (Real.sqrt_nonneg (M:ℝ))
  rw [mul_left_comm (Real.sqrt (M:ℝ)) (ε/2),drop_sum mp] at hh
  exact hh.trans_lt (by linarith only [ep,mul_nonneg ep.le (div_nonneg zero_le_one (Real.sqrt_nonneg 2))])

private theorem reciprocal_error {a : ℕ → ℝ}
    (ha : Tendsto (fun n : ℕ => (∑ d ∈ Icc 1 n, a d)/root n) atTop (𝓝 0)) :
    Tendsto (fun M : ℕ => root M*price a M) atTop (𝓝 0) := by
  apply Metric.tendsto_atTop.mpr
  intro ε ep
  obtain ⟨K,hK⟩ := Metric.tendsto_atTop.mp ha (ε/4) (by positivity)
  refine ⟨max K 1,fun M hM => ?_⟩
  have mp := (le_max_right K 1).trans hM
  have mr := Real.sqrt_pos.mpr (Nat.cast_pos.mpr mp : 0 < (M:ℝ))
  let L := ε/4/root M
  have l0 : 0 ≤ L := div_nonneg (by positivity) mr.le
  have bound (n : ℕ) (hn : M ≤ n) (_ : n ≤ 2*M) : |∑ d ∈ Icc 1 n, a d| ≤ L*n := by
    have nn := mp.trans hn
    have nr := Real.sqrt_pos.mpr (Nat.cast_pos.mpr nn : 0<(n:ℝ))
    have h := hK n ((le_max_left K 1).trans (hM.trans hn))
    rw [Real.dist_eq,sub_zero,abs_div,abs_of_pos nr] at h
    apply ((div_lt_iff₀ nr).mp h).le.trans
    calc ε/4*root n = L*(root M*root n) := by dsimp only [L]; field_simp
         _ ≤ L*(root n*root n) := mul_le_mul_of_nonneg_left
           (mul_le_mul_of_nonneg_right (Real.sqrt_le_sqrt (Nat.cast_le.mpr hn)) nr.le) l0
         _ = _ := by rw [Real.mul_self_sqrt (Nat.cast_nonneg n)]
  let w := fun n : ℕ => (n:ℝ)⁻¹
  have ab := BezoutValuationIncidence.abs_sum_Ioc_mul_le_of_linear (s:=a) (w:=w)
    (show M ≤ 2*M by omega) bound (fun n => inv_nonneg.mpr (Nat.cast_nonneg n))
    (fun d hd => inv_anti₀ (Nat.cast_pos.mpr (mp.trans hd.le)) (Nat.cast_le.mpr (Nat.le_succ d)))
  have sw : ∑ d ∈ Ioc M (2*M),w d ≤ 1 := by
    have he := sum_le_sum (s:=Ioc M (2*M)) (g:=fun _ => (M:ℝ)⁻¹) fun d hd =>
      inv_anti₀ (Nat.cast_pos.mpr mp) (Nat.cast_le.mpr (mem_Ioc.mp hd).1.le)
    simpa only [sum_const,Nat.card_Ioc,show 2*M-M=M by omega,nsmul_eq_mul,
      mul_inv_cancel₀ (Nat.cast_pos.mpr mp : 0<(M:ℝ)).ne',w] using he
  have mw : (M:ℝ)*w (M+1) ≤ 1 := by
    change (M:ℝ)*((M+1:ℕ):ℝ)⁻¹ ≤ 1
    rw [←div_eq_mul_inv,div_le_one (by positivity)]
    exact Nat.cast_le.mpr (Nat.le_succ M)
  rw [Real.dist_eq,sub_zero,abs_mul,abs_of_pos mr]
  have hprice : |price a M| ≤ L*3 := by
    simp only [price,div_eq_mul_inv] at ⊢
    exact ab.trans (mul_le_mul_of_nonneg_left (by linarith only [sw,mw]) l0)
  exact (mul_le_mul_of_nonneg_left hprice mr.le).trans_lt (by dsimp only [L]; field_simp; linarith only [ep])

/-- A signed prefix asymptotic to A√n has reciprocal octave mass
asymptotic to A(1−1/√2)/√M. No monotonicity of the weights is required. -/
theorem square_root_octave_transfer {a : ℕ → ℝ} {A : ℝ}
    (h : Tendsto (fun n : ℕ => (∑ d ∈ Icc 1 n, a d)/root n) atTop (𝓝 A)) :
    Tendsto (fun M : ℕ => root M*price a M) atTop (𝓝 (A*(1-1/Real.sqrt 2))) := by
  let e := fun d => a d-A*step d
  have hz : Tendsto (fun n : ℕ => (∑ d ∈ Icc 1 n,e d)/root n) atTop (𝓝 0) := by
    have hc := h.sub_const A
    rw [sub_self] at hc
    apply hc.congr'
    filter_upwards [eventually_ge_atTop (1:ℕ)] with n hn
    simp only [e,sum_sub_distrib,←mul_sum,prefix_step,sub_div]
    field_simp [Real.sqrt_pos.mpr (Nat.cast_pos.mpr hn : 0<(n:ℝ)) |>.ne']
  have lim := (reciprocal_error hz).add (model_octave.const_mul A)
  rw [zero_add] at lim
  apply lim.congr
  intro M
  simp only [price,e,sub_div,mul_div_assoc,sum_sub_distrib,←mul_sum]
  ring

#print axioms square_root_octave_transfer
end GaloisForLFunctions.ReciprocalOctaves
