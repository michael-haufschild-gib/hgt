import GaloisForLFunctions.RHTower.WeilWorkExposingRaySublogScales

/-!
# Actual weighted spectral separators extend from polar to full sources

For 0 ≤ β < 1/2, an actual polar separator with weight
1 + log(2 + |t|)^β automatically extends to every compact complex C2 source.
The separator itself gives simultaneous coefficient control at N and N^2.
At X = log N - 2a this pays both remote correlation windows of the actual
far-polar correction. Weighted spectral convergence pays the other side.
No absolute-growth, RH, full-positivity or recovery premise is added.

Paper: docs/reports/weil-work/results/02-exposing-ray/SUBHALF-LOG-FIBRE-PROOF.md.
-/

open MeasureTheory Filter Topology Set Complex Zeta23
open scoped ComplexConjugate
noncomputable section
namespace RHTower.ExposingRayTransfer
open WeilSpectral WeilOneSided


private theorem norm_atomicKernel_le_cutoff (b : ℕ → ℝ) {f : ℝ → ℂ} {a M : ℝ}
    (hs : tsupport f ⊆ Icc (-a) a) (hM : ∀ y, ‖EF.weilTest f f y‖ ≤ M)
    {H : ℕ} (hH : 1 ≤ H) {y : ℝ} (hy : |y|+2*a ≤ Real.log H) :
    ‖atomicKernel b 0 f y‖ ≤ 2*M*∑ n ∈ Finset.Icc 2 H, |b n| := by
  have hvan (u : ℝ) (hu : a < |u|) : f u=0 := by
    by_contra h
    have hh := hs (subset_tsupport f h)
    have hle := abs_le.mpr hh
    linarith
  have hzero (n : ℕ) (hn : n∉Finset.Icc 2 H) :
      ((if 2 ≤ n then b n else 0 : ℝ) : ℂ)*
        (EF.weilTest f f (Real.log n-y)+EF.weilTest f f (-Real.log n-y)) = 0 := by
    by_cases hn2 : 2 ≤ n
    · have hnH : H < n := by
        by_contra hh
        exact hn (Finset.mem_Icc.mpr ⟨hn2,by omega⟩)
      have hlog : Real.log (H:ℝ) < Real.log n := Real.log_lt_log
        (by exact_mod_cast (show 0 < H by omega)) (by exact_mod_cast hnH)
      have h1 : 2*a < |Real.log (n:ℝ)-y| := by
        linarith [le_abs_self (Real.log (n:ℝ)-y), le_abs_self y]
      have h2 : 2*a < |-Real.log (n:ℝ)-y| := by
        linarith [neg_le_abs (-Real.log (n:ℝ)-y), neg_le_abs y]
      rw [weilTest_self_eq_zero hvan h1, weilTest_self_eq_zero hvan h2]
      simp
    · simp [hn2]
  unfold atomicKernel atomicForm
  simp only [Complex.ofReal_zero,zero_mul,zero_sub,WeilSpectral.transl,norm_neg]
  rw [tsum_eq_sum (s := Finset.Icc 2 H) hzero]
  calc
    _ ≤ ∑ n ∈ Finset.Icc 2 H, ‖((if 2 ≤ n then b n else 0 : ℝ) : ℂ)*
        (EF.weilTest f f (Real.log n-y)+EF.weilTest f f (-Real.log n-y))‖ := norm_sum_le _ _
    _ ≤ 2*M*∑ n ∈ Finset.Icc 2 H, |b n| := by
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro n hn
      rw [if_pos (Finset.mem_Icc.mp hn).1,norm_mul,Complex.norm_real,Real.norm_eq_abs]
      have hh : ‖EF.weilTest f f (Real.log n-y)+EF.weilTest f f (-Real.log n-y)‖ ≤ 2*M :=
        (norm_add_le _ _).trans (by linarith [hM (Real.log n-y),hM (-Real.log n-y)])
      have hm := mul_le_mul_of_nonneg_left hh (abs_nonneg (b n))
      nlinarith only [hm]

private theorem norm_atomic_far_error_le (b : ℕ → ℝ) {f : ℝ → ℂ}
    (hf : Continuous f) (hs : HasCompactSupport f) (X U V : ℝ)
    (hU : ‖atomicKernel b 0 f X‖ ≤ U) (hUn : ‖atomicKernel b 0 f (-X)‖ ≤ U)
    (hV : ‖atomicKernel b 0 f (2*X)‖ ≤ V) (hVn : ‖atomicKernel b 0 f (-(2*X))‖ ≤ V) :
    ‖atomicForm b 0 (EF.weilTest (farSource X f) (farSource X f))-
        atomicForm b 0 (EF.weilTest f f)‖ ≤
      2*farPolarCoeff X*U+farPolarCoeff X^2/2*(‖atomicKernel b 0 f 0‖+V) := by
  let K := atomicKernel b 0 f
  have h0 : K 0 = atomicForm b 0 (EF.weilTest f f) := by
    change atomicForm b 0 (fun x => EF.weilTest f f (x-0)) = _
    simp only [sub_zero]
  have hr := farPolarCoeff_nonneg X
  have hn : ‖(farPolarCoeff X : ℂ)‖ = farPolarCoeff X := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg hr]
  have h1 : ‖(farPolarCoeff X : ℂ)*(K X+K (-X))‖ ≤ 2*farPolarCoeff X*U := by
    rw [norm_mul,hn]
    have hb : ‖K X+K (-X)‖ ≤ 2*U := (norm_add_le _ _).trans (by linarith)
    nlinarith [mul_le_mul_of_nonneg_left hb hr]
  have h2 : ‖(farPolarCoeff X : ℂ)^2/4*(2*K 0+K (2*X)+K (-(2*X)))‖ ≤
      farPolarCoeff X^2/2*(‖K 0‖+V) := by
    have hb : ‖2*K 0+K (2*X)+K (-(2*X))‖ ≤ 2*‖K 0‖+2*V := by
      calc
        _ ≤ ‖2*K 0+K (2*X)‖+‖K (-(2*X))‖ := norm_add_le _ _
        _ ≤ ‖2*K 0‖+‖K (2*X)‖+‖K (-(2*X))‖ :=
          add_le_add (norm_add_le (2*K 0) (K (2*X))) le_rfl
        _ ≤ _ := by rw [norm_mul,norm_ofNat]; linarith
    rw [norm_mul,norm_div,norm_pow,hn,norm_ofNat]
    nlinarith [mul_le_mul_of_nonneg_left hb (sq_nonneg (farPolarCoeff X))]
  rw [atomicForm_farSource b 0 hf hs X]
  change ‖K 0-(farPolarCoeff X : ℂ)*(K X+K (-X))+
    (farPolarCoeff X : ℂ)^2/4*(2*K 0+K (2*X)+K (-(2*X)))-_‖ ≤ _
  rw [← h0]
  have he (q u v : ℂ) : q-u+v-q = -u+v := by ring
  rw [he]
  have ht := norm_add_le (-((farPolarCoeff X : ℂ)*(K X+K (-X))))
    ((farPolarCoeff X : ℂ)^2/4*(2*K 0+K (2*X)+K (-(2*X))))
  rw [norm_neg] at ht
  exact ht.trans (add_le_add h1 h2)

private theorem farPolarCoeff_log_le {N : ℕ} (hN : 1 ≤ N) (a : ℝ) :
    farPolarCoeff (Real.log N-2*a) ≤ 2*Real.exp a/Real.sqrt N := by
  have hn : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hsq : Real.sqrt (N:ℝ) = Real.exp (Real.log N/2) := by
    have he : Real.exp (Real.log (N:ℝ)/2)*Real.exp (Real.log N/2) = N := by
      rw [← Real.exp_add,show Real.log (N:ℝ)/2+Real.log N/2=Real.log N by ring,Real.exp_log hn]
    have hs := Real.sq_sqrt hn.le
    nlinarith [Real.sqrt_nonneg (N:ℝ),Real.exp_pos (Real.log (N:ℝ)/2)]
  have he : Real.exp (-((Real.log (N:ℝ)-2*a)/2)) = Real.exp a/Real.sqrt N := by
    rw [hsq,← Real.exp_sub]
    congr 1
    ring
  have h := farPolarCoeff_le (Real.log N-2*a)
  rw [he] at h
  simpa only [mul_div_assoc] using h

private theorem farPolarCoeff_log_sq_le {N : ℕ} (hN : 1 ≤ N) (a : ℝ) :
    farPolarCoeff (Real.log N-2*a)^2 ≤ 4*Real.exp (2*a)/(N:ℝ) := by
  have hn : 0 < (N:ℝ) := by exact_mod_cast (show 0 < N by omega)
  have hc := farPolarCoeff_log_le hN a
  have hr := farPolarCoeff_nonneg (Real.log N-2*a)
  have hh := mul_le_mul hc hc hr (by positivity : 0 ≤ 2*Real.exp a/Real.sqrt N)
  have he : (2*Real.exp a/Real.sqrt N)^2 = 4*Real.exp (2*a)/(N:ℝ) := by
    rw [div_pow,mul_pow,Real.sq_sqrt hn.le,pow_two (Real.exp a),← Real.exp_add]
    rw [show a+a=2*a by ring]
    norm_num
  nlinarith only [hh,he]

private theorem exists_arithmetic_error_budget (b : ℕ → ℝ) (f : WeilTestFn) :
    ∃ a C : ℝ, 0 ≤ a ∧ 0 < C ∧ ∀ N : ℕ, 2 ≤ N → 0 ≤ Real.log N-2*a →
      |atomValue b (farTest (Real.log N-2*a) f).1-atomValue b f.1| ≤
        C*(farPolarCoeff (Real.log N-2*a)^2+
          (∑ n ∈ Finset.Icc 2 N, |b n|)/Real.sqrt N+
          (∑ n ∈ Finset.Icc 2 (N^2), |b n|)/(N:ℝ)) := by
  obtain ⟨a0,ha0⟩ := exists_abs_bound_of_hasCompactSupport f.2.2
  let a := |a0|
  have ha : 0 ≤ a := abs_nonneg _
  have hs : tsupport f.1 ⊆ Icc (-a) a := by
    apply closure_minimal _ isClosed_Icc
    intro x hx
    exact abs_le.mp ((ha0 x hx).trans (le_abs_self a0))
  have hc := (weilTest_self_data f.2.1 hs).2.1.continuous
  have hcs := EF.weilTest_hasCompactSupport f.2.2 f.2.2
  obtain ⟨M,hM⟩ := hc.bounded_above_of_compact_support hcs
  have hM0 : 0 ≤ M := (norm_nonneg _).trans (hM 0)
  let Q := ‖atomicKernel b 0 f.1 0‖
  let D := 8*M*Real.exp a
  let E := 4*M*Real.exp (2*a)
  let C := Q+D+E+1
  have hQ : 0 ≤ Q := norm_nonneg _
  have hD : 0 ≤ D := by dsimp [D]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hC : 0 < C := by dsimp [C]; linarith
  refine ⟨a,C,ha,hC,fun N hN hX => ?_⟩
  let X := Real.log (N:ℝ)-2*a
  let B := ∑ n ∈ Finset.Icc 2 N, |b n|
  let B2 := ∑ n ∈ Finset.Icc 2 (N^2), |b n|
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hB2 : 0 ≤ B2 := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have hN1 : 1 ≤ N := by omega
  have hN2 : 1 ≤ N^2 := by
    have hp : 0 < N^2 := by positivity
    exact hp
  have hcut : |X|+2*a ≤ Real.log (N:ℝ) := by rw [abs_of_nonneg hX]; linarith
  have hcutn : |-X|+2*a ≤ Real.log (N:ℝ) := by simpa only [abs_neg] using hcut
  have hcut2 : |2*X|+2*a ≤ Real.log ((N^2:ℕ):ℝ) := by
    rw [abs_of_nonneg (by dsimp [X]; linarith : 0 ≤ 2*X),Nat.cast_pow,Real.log_pow]
    dsimp [X]
    linarith
  have hcut2n : |-(2*X)|+2*a ≤ Real.log ((N^2:ℕ):ℝ) := by simpa only [abs_neg] using hcut2
  have hU := norm_atomicKernel_le_cutoff b hs hM hN1 hcut
  have hUn := norm_atomicKernel_le_cutoff b hs hM hN1 hcutn
  have hV := norm_atomicKernel_le_cutoff b hs hM hN2 hcut2
  have hVn := norm_atomicKernel_le_cutoff b hs hM hN2 hcut2n
  have herror := norm_atomic_far_error_le b f.2.1.continuous f.2.2 X (2*M*B) (2*M*B2) hU hUn hV hVn
  have hreal : |atomValue b (farTest X f).1-atomValue b f.1| ≤
      ‖atomicForm b 0 (EF.weilTest (farSource X f.1) (farSource X f.1))-
        atomicForm b 0 (EF.weilTest f.1 f.1)‖ := by
    have he : atomValue b (farTest X f).1-atomValue b f.1 =
        -(atomicForm b 0 (EF.weilTest (farSource X f.1) (farSource X f.1))-
          atomicForm b 0 (EF.weilTest f.1 f.1)).re := by
      simp only [atomValue,farTest,Complex.sub_re]
      ring
    rw [he,abs_neg]
    exact Complex.abs_re_le_norm _
  have hc1 := farPolarCoeff_log_le hN1 a
  have hc2 := farPolarCoeff_log_sq_le hN1 a
  have hfirst : 2*farPolarCoeff X*(2*M*B) ≤ D*(B/Real.sqrt N) := by
    have hh := mul_le_mul_of_nonneg_right hc1 (show 0 ≤ 4*M*B by positivity)
    calc
      _ = farPolarCoeff X*(4*M*B) := by ring
      _ ≤ (2*Real.exp a/Real.sqrt N)*(4*M*B) := hh
      _ = D*(B/Real.sqrt N) := by dsimp [D]; ring
  have hsecond : farPolarCoeff X^2/2*(Q+2*M*B2) ≤
      Q/2*farPolarCoeff X^2+E*(B2/(N:ℝ)) := by
    have hh := mul_le_mul_of_nonneg_right hc2 (show 0 ≤ M*B2 by positivity)
    calc
      _ = Q/2*farPolarCoeff X^2+farPolarCoeff X^2*(M*B2) := by ring
      _ ≤ Q/2*farPolarCoeff X^2+(4*Real.exp (2*a)/(N:ℝ))*(M*B2) := add_le_add le_rfl hh
      _ = Q/2*farPolarCoeff X^2+E*(B2/(N:ℝ)) := by dsimp [E]; ring
  have hsum := hreal.trans herror
  have hc0 : 0 ≤ farPolarCoeff X^2 := sq_nonneg _
  have hr1 : 0 ≤ B/Real.sqrt N := div_nonneg hB (Real.sqrt_nonneg _)
  have hr2 : 0 ≤ B2/(N:ℝ) := div_nonneg hB2 (Nat.cast_nonneg _)
  have hCQ : Q/2 ≤ C := by dsimp [C]; linarith
  have hCD : D ≤ C := by dsimp [C]; linarith
  have hCE : E ≤ C := by dsimp [C]; linarith
  change _ ≤ C*(farPolarCoeff X^2+B/Real.sqrt N+B2/(N:ℝ))
  nlinarith [mul_le_mul_of_nonneg_right hCQ hc0,
    mul_le_mul_of_nonneg_right hCD hr1,mul_le_mul_of_nonneg_right hCE hr2]

/-- The actual arithmetic form converges along arbitrarily late far-polar
corrections of each full source. Both remote windows use the same cutoff. -/
theorem exists_farTest_arithmetic_approx {β : ℝ} (hβ : 0 ≤ β) (hβhalf : β < 1/2)
    {b : ℕ → ℝ} {ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ}
    (h : ∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 hβ (by linarith) f))
    (f : WeilTestFn) {ε : ℝ} (hε : 0 < ε) (R : ℝ) :
    ∃ X : ℝ, R ≤ X ∧ |atomValue b (farTest X f).1-atomValue b f.1| < ε := by
  obtain ⟨a,C,ha,hC,hbudget⟩ := exists_arithmetic_error_budget b f
  let δ := ε/(2*C)
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have ht : Tendsto (fun X : ℝ => farPolarCoeff X^2) atTop (𝓝 0) := by
    simpa using tendsto_farPolarCoeff.pow 2
  obtain ⟨R0,hR0⟩ := eventually_atTop.mp (ht.eventually (Iio_mem_nhds hδ))
  let T := max 0 (max R R0)
  obtain ⟨K,hK⟩ := exists_nat_gt (Real.exp (T+2*a))
  obtain ⟨N,hN,hKN,hsmall⟩ := exists_small_two_scales_of_polar_log_bound hβ hβhalf h hδ K
  have hncast : (K:ℝ) ≤ N := by exact_mod_cast hKN
  have hlog := Real.log_lt_log (Real.exp_pos (T+2*a)) (hK.trans_le hncast)
  rw [Real.log_exp] at hlog
  let X := Real.log (N:ℝ)-2*a
  have hXT : T ≤ X := by dsimp [X]; linarith
  have hX0 : 0 ≤ X := (le_max_left 0 (max R R0)).trans hXT
  have hXR : R ≤ X := (le_trans (le_max_left R R0) (le_max_right 0 (max R R0))).trans hXT
  have hXR0 : R0 ≤ X := (le_trans (le_max_right R R0) (le_max_right 0 (max R R0))).trans hXT
  have hc := hR0 X hXR0
  have he := hbudget N hN hX0
  have hcancel : 2*C*δ=ε := by dsimp [δ]; field_simp
  refine ⟨X,hXR,?_⟩
  have hsum : farPolarCoeff X^2+
      (∑ n ∈ Finset.Icc 2 N, |b n|)/Real.sqrt N+
      (∑ n ∈ Finset.Icc 2 (N^2), |b n|)/(N:ℝ) < 2*δ := by linarith
  have hh := mul_lt_mul_of_pos_left hsum hC
  nlinarith only [he,hh,hcancel]

/-- Below the half-logarithmic weight, every actual polar spectral
separator extends to ALL full sources. No coefficient-growth premise,
full positivity, RH premise or recovery hypothesis is added. -/
theorem polarLogSpectralBound_iff_fullLogSpectralBound {β : ℝ}
    (hβ : 0 ≤ β) (hβhalf : β < 1/2) (b : ℕ → ℝ)
    (ell : Lp ℝ 1 (volume : Measure ℝ) →L[ℝ] ℝ) :
    (∀ f : WeilTestFn, (∃ a, IsPolarTest a f.1) →
      atomValue b f.1 ≤ ell (logDensityL1 hβ (by linarith) f)) ↔
    (∀ f : WeilTestFn, atomValue b f.1 ≤ ell (logDensityL1 hβ (by linarith) f)) := by
  constructor
  · intro h f
    apply le_of_forall_pos_le_add
    intro ε hε
    have ht := ell.continuous.tendsto (logDensityL1 hβ (by linarith) f) |>.comp
      (tendsto_logDensityL1_farTest hβ (by linarith) f)
    have he : Tendsto (fun X : ℝ =>
        |ell (logDensityL1 hβ (by linarith) (farTest X f))-
          ell (logDensityL1 hβ (by linarith) f)|) atTop (𝓝 0) := by
      simpa using (ht.sub_const (ell (logDensityL1 hβ (by linarith) f))).abs
    obtain ⟨R,hR⟩ := eventually_atTop.mp (he.eventually (Iio_mem_nhds (show 0 < ε/2 by positivity)))
    obtain ⟨X,hX,herror⟩ := exists_farTest_arithmetic_approx hβ hβhalf h f
      (show 0 < ε/2 by positivity) R
    have hscalar := hR X hX
    have hpolar := h (farTest X f) (isPolarTest_farSource f.2.1 f.2.2 X)
    have hA := neg_le_abs (atomValue b (farTest X f).1-atomValue b f.1)
    have hE := le_abs_self (ell (logDensityL1 hβ (by linarith) (farTest X f))-
      ell (logDensityL1 hβ (by linarith) f))
    linarith
  · intro h f _
    exact h f

end RHTower.ExposingRayTransfer
