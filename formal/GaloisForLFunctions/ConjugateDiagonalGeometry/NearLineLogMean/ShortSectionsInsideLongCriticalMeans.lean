import GaloisForLFunctions.HTGeometry.GeneralizedDirichletMeanValue
import GaloisForLFunctions.HTGeometry.FourierPowerBound
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheSharpHolderExponentForInfiniteGramRecovery
import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.TheEndpointFormOfTheMoebiusMean

/-!
# Short sections detected inside arbitrarily long polynomial sections

The weighted Fourier Gram argument of Gabet, Ferreira Da Costa and Lee
(arXiv:2611.18900, §4) also works for a rectangular Gram matrix. Every
frequency in the short section is separated from every distinct frequency
of the long section. Completing the square leaves the whole diagonal of
the short section as a lower bound for the observed energy.
-/

noncomputable section
open Complex Finset MeasureTheory Filter
open scoped FourierTransform Topology ComplexConjugate ContDiff
open _root_.HTGeometry (genPoly genPoly_mul_conj_bilinear)
open GaloisForLFunctions.HTGeometry (exists_pow_mul_norm_fourierIntegral_le norm_fourierIntegral_le_div_of_pow_bound)
open GaloisForLFunctions.ConjugateDiagonalGeometry.LogWindowRetrieval (local_log_spacing)
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

/-- Dirichlet section in logarithmic frequencies, with length-independent coefficients. -/
abbrev logSection (a : ℕ → ℂ) (N : ℕ) :=
  genPoly a (fun n => -Real.log n) (Icc 1 N)

private theorem section_cont (a : ℕ → ℂ) (N : ℕ) : Continuous (logSection a N) := by
  unfold logSection genPoly
  fun_prop

/-- Weighted correlation of two sections sampled at the same dilated time. -/
def logWindowCross (g : ℝ → ℝ) (a : ℕ → ℂ) (N H : ℕ) (T : ℝ) : ℂ :=
  ∫ x : ℝ, (g x : ℂ) * (logSection a N (T*x) * conj (logSection a H (T*x)))

private theorem weighted_integrable {g : ℝ → ℝ} (hc : Continuous g) (hs : HasCompactSupport g)
    (a : ℕ → ℂ) (N H : ℕ) (T : ℝ) : Integrable (fun x : ℝ =>
      (g x : ℂ) * (logSection a N (T*x) * conj (logSection a H (T*x)))) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (Complex.continuous_ofReal.comp hc).mul (((section_cont a N).comp
      (continuous_const.mul continuous_id)).mul (Complex.continuous_conj.comp
        ((section_cont a H).comp (continuous_const.mul continuous_id))))
  · exact (hs.comp_left (show ((0 : ℝ) : ℂ) = 0 by rfl)).mul_right

private theorem cross_kernel {g : ℝ → ℝ} (hc : Continuous g) (hs : HasCompactSupport g)
    (a : ℕ → ℂ) (N H : ℕ) (T : ℝ) :
    logWindowCross g a N H T =
      ∑ m ∈ Icc 1 H, ∑ n ∈ Icc 1 N,
        a n * conj (a m) * 𝓕 (fun x : ℝ => (g x : ℂ))
          (T*(Real.log n - Real.log m)/(2*Real.pi)) := by
  let D := fun n m : ℕ => -Real.log n - -Real.log m
  let W := fun n m : ℕ => fun x : ℝ =>
    (g x : ℂ) * (a n * conj (a m) * cexp (I * ((D n m : ℂ) * ((T*x : ℝ) : ℂ))))
  have hw (n m : ℕ) : Integrable (W n m) := by
    apply Continuous.integrable_of_hasCompactSupport
    · dsimp only [W]
      fun_prop
    · exact (hs.comp_left (show ((0 : ℝ) : ℂ) = 0 by rfl)).mul_right
  have expand (x : ℝ) : (g x : ℂ) * (logSection a N (T*x) * conj (logSection a H (T*x))) =
      ∑ m ∈ Icc 1 H, ∑ n ∈ Icc 1 N, W n m x := by
    rw [logSection, logSection, genPoly_mul_conj_bilinear, Finset.mul_sum, Finset.sum_comm]
    simp only [Finset.mul_sum, W, D]
  rw [logWindowCross]
  simp_rw [expand]
  rw [integral_finsetSum _ (fun m _ => integrable_finsetSum _ fun n _ => hw n m)]
  refine sum_congr rfl fun m _ => ?_
  rw [integral_finsetSum _ (fun n _ => hw n m)]
  refine sum_congr rfl fun n _ => ?_
  rw [Real.fourier_real_eq_integral_exp_smul, ← integral_const_mul]
  apply integral_congr_ae
  filter_upwards with x
  simp only [W, D, smul_eq_mul]
  have he : I * (((-Real.log n - -Real.log m : ℝ) : ℂ) * ((T*x : ℝ) : ℂ)) =
      ((-2*Real.pi*x*(T*(Real.log n - Real.log m)/(2*Real.pi)) : ℝ) : ℂ) * I := by
    push_cast
    field_simp [Real.pi_ne_zero]
    <;> ring
  rw [he]
  ring

/-- Energy of the first H coefficients. -/
def logSectionDiagonal (a : ℕ → ℂ) (H : ℕ) : ℝ := ∑ m ∈ Icc 1 H, ‖a m‖^2

/-- Every short-section coefficient can be tested against the full section,
with arbitrary polynomial decay in the ratio of its length to the height. -/
theorem rectangular_log_gram_error {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hs : HasCompactSupport g) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℕ → ℂ), (∀ n, 0 < n → ‖a n‖ ≤ 1) →
      ∀ (N H : ℕ), H ≤ N → ∀ T : ℝ, 0 < T →
      ‖logWindowCross g a N H T - (((∫ x, g x)*logSectionDiagonal a H : ℝ) : ℂ)‖ ≤
        C * N * H * ((H : ℝ)+1)^k / T^k := by
  let f := fun x : ℝ => (g x : ℂ)
  have hs' : HasCompactSupport f := hs.comp_left (show ((0 : ℝ) : ℂ) = 0 by rfl)
  have hf : ContDiff ℝ ∞ f := Complex.ofRealCLM.contDiff.comp hg
  obtain ⟨C, hC, hpow⟩ := exists_pow_mul_norm_fourierIntegral_le hs' hf k
  let B := C * (2 * Real.pi)^k
  have hB : 0 ≤ B := by dsimp [B]; positivity
  refine ⟨B, hB, fun a ha N H hHN T hT => ?_⟩
  let R := B * ((H : ℝ)+1)^k / T^k
  have hR : 0 ≤ R := by dsimp only [R]; positivity
  let freq := fun n m : ℕ => T * (Real.log n - Real.log m) / (2 * Real.pi)
  let entry := fun n m : ℕ => a n * conj (a m) * 𝓕 f (freq n m)
  have hzero : 𝓕 f 0 = ((∫ x, g x : ℝ) : ℂ) := by
    rw [Real.fourier_real_eq_integral_exp_smul]
    simp [f, integral_complex_ofReal]
  have hdiag (m : ℕ) : entry m m = ((∫ x, g x : ℝ) : ℂ)*((‖a m‖^2 : ℝ) : ℂ) := by
    simp [entry, freq, hzero, Complex.mul_conj, Complex.normSq_eq_norm_sq, mul_comm]
  have hdiff (n m : ℕ) (hn : n ∈ Icc 1 N) (hm : m ∈ Icc 1 H) (hne : n ≠ m) :
      ‖entry n m‖ ≤ R := by
    have hsp := local_log_spacing (mem_Icc.mp hm).1 (mem_Icc.mp hn).1 hne
    have hil := inv_anti₀ (by positivity : 0 < (m:ℝ)+1)
      (add_le_add_left ((Nat.cast_le (α := ℝ)).mpr (mem_Icc.mp hm).2) 1)
    have hp : 0 < 2*Real.pi := by positivity
    have hX : 0 < (H:ℝ)+1 := by positivity
    have hfreq : T/(2*Real.pi*((H:ℝ)+1)) ≤ |freq n m| := by
      dsimp only [freq]
      rw [abs_div, abs_mul, abs_of_pos hp, abs_of_pos hT]
      exact (by rw [mul_comm (2*Real.pi), ← div_div, div_eq_mul_inv T] :
          T/(2*Real.pi*((H:ℝ)+1)) = T*((H:ℝ)+1)⁻¹/(2*Real.pi)).le.trans
        (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left (hil.trans hsp) hT.le) hp.le)
    have hpos := (div_pos hT (mul_pos hp hX)).trans_le hfreq
    have hb := (norm_fourierIntegral_le_div_of_pow_bound hpow (abs_pos.mp hpos)).trans
      (div_le_div_of_nonneg_left hC (pow_pos (div_pos hT (mul_pos hp hX)) _) (pow_le_pow_left₀ (by positivity) hfreq k))
    have hh : ‖a n * conj (a m)‖ ≤ 1 := by
      rw [norm_mul, Complex.norm_conj]
      exact mul_le_one₀ (ha _ (mem_Icc.mp hn).1) (norm_nonneg _) (ha _ (mem_Icc.mp hm).1)
    dsimp only [entry]
    rw [norm_mul]
    calc
      _ ≤ 1 * ‖𝓕 f (freq n m)‖ := mul_le_mul_of_nonneg_right hh (norm_nonneg _)
      _ ≤ C / (T/(2*Real.pi*((H:ℝ)+1)))^k := by simpa only [one_mul] using hb
      _ = R := by dsimp only [R, B]; rw [div_pow, div_div_eq_mul_div, mul_pow (2*Real.pi) ((H:ℝ)+1) k]; ring
  have hdel (m : ℕ) (hm : m ∈ Icc 1 H) : m ∈ Icc 1 N :=
    mem_Icc.mpr ⟨(mem_Icc.mp hm).1, (mem_Icc.mp hm).2.trans hHN⟩
  have hsplit : logWindowCross g a N H T - (((∫ x, g x)*logSectionDiagonal a H : ℝ) : ℂ) =
      ∑ m ∈ Icc 1 H, ∑ n ∈ (Icc 1 N).erase m, entry n m := by
    rw [cross_kernel hg.continuous hs]
    change (∑ m ∈ Icc 1 H, ∑ n ∈ Icc 1 N, entry n m) - _ = _
    simp only [logSectionDiagonal, Complex.ofReal_mul, Complex.ofReal_sum, Finset.mul_sum,
      ← hdiag, ← Finset.sum_sub_distrib]
    refine sum_congr rfl fun m hm => ?_
    rw [← sum_erase_add _ _ (hdel m hm), add_sub_cancel_right]
  rw [hsplit]
  refine (norm_sum_le _ _).trans ?_
  have hrows (m : ℕ) (hm : m ∈ Icc 1 H) :
      ‖∑ n ∈ (Icc 1 N).erase m, entry n m‖ ≤ (N : ℝ)*R := by
    refine (norm_sum_le _ _).trans ((sum_le_sum fun n hn =>
      hdiff n m (mem_erase.mp hn).2 hm (mem_erase.mp hn).1).trans ?_)
    rw [sum_const, nsmul_eq_mul]
    apply mul_le_mul_of_nonneg_right _ hR
    exact_mod_cast (card_le_card (erase_subset m (Icc 1 N))).trans_eq (by simp [Nat.card_Icc])
  refine (sum_le_sum hrows).trans_eq ?_
  simp only [sum_const, nsmul_eq_mul, Nat.card_Icc, Nat.add_sub_cancel]
  dsimp only [R]
  ring

private theorem cross_re {g : ℝ → ℝ} (hc : Continuous g) (hs : HasCompactSupport g)
    (a : ℕ → ℂ) (N H : ℕ) (T : ℝ) :
    (logWindowCross g a N H T).re =
      ∫ x : ℝ, g x * (logSection a N (T*x)*conj (logSection a H (T*x))).re := by
  have h := integral_re (weighted_integrable hc hs a N H T)
  simp only [RCLike.re_to_complex] at h
  rw [logWindowCross, ← h]
  simp only [Complex.re_ofReal_mul]

private theorem cross_self {g : ℝ → ℝ} (hc : Continuous g) (hs : HasCompactSupport g)
    (a : ℕ → ℂ) (N : ℕ) (T : ℝ) :
    (logWindowCross g a N N T).re = ∫ x : ℝ, g x * ‖logSection a N (T*x)‖^2 := by
  rw [cross_re hc hs]
  simp only [Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

private theorem cross_square_completion {g : ℝ → ℝ} (hc : Continuous g)
    (hs : HasCompactSupport g) (hg : ∀ x, 0 ≤ g x) (a : ℕ → ℂ) (N H : ℕ) (T : ℝ) :
    2*(logWindowCross g a N H T).re ≤
      (logWindowCross g a N N T).re + (logWindowCross g a H H T).re := by
  have integrableRow (M : ℕ) : Integrable (fun x : ℝ => g x * ‖logSection a M (T*x)‖^2) :=
    (hc.mul (((section_cont a M).comp (continuous_const.mul continuous_id)).norm.pow 2)).integrable_of_hasCompactSupport hs.mul_right
  have mixed := (weighted_integrable hc hs a N H T).re
  simp only [RCLike.re_to_complex, Complex.re_ofReal_mul] at mixed
  rw [cross_re hc hs, cross_self hc hs, cross_self hc hs,
    ← integral_const_mul, ← integral_add (integrableRow N) (integrableRow H)]
  refine integral_mono (mixed.const_mul 2) ((integrableRow N).add (integrableRow H)) (fun x => ?_)
  let z := logSection a N (T*x)
  let w := logSection a H (T*x)
  have h : 2*(z*conj w).re ≤ ‖z‖^2+‖w‖^2 := by
    rw [← Complex.normSq_eq_norm_sq, ← Complex.normSq_eq_norm_sq]
    simp only [Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    nlinarith only [sq_nonneg (z.re-w.re), sq_nonneg (z.im-w.im)]
  change 2*(g x*(z*conj w).re) ≤ g x*‖z‖^2+g x*‖w‖^2
  linarith only [mul_le_mul_of_nonneg_left h (hg x)]

/-- A nonnegative smooth time window measures at least the short diagonal
up to an error with an arbitrary power of (H+1)/T. -/
theorem short_diagonal_below_long_energy {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hs : HasCompactSupport g) (hp : ∀ x, 0 ≤ g x) (k : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : ℕ → ℂ), (∀ n, 0 < n → ‖a n‖ ≤ 1) →
      ∀ (N H : ℕ), H ≤ N → ∀ T : ℝ, 0 < T →
      (∫ x, g x) * logSectionDiagonal a H ≤ (∫ x : ℝ, g x * ‖logSection a N (T*x)‖^2) +
        C * N * H * ((H : ℝ)+1)^k / T^k := by
  obtain ⟨C, hC, hGram⟩ := rectangular_log_gram_error hg hs k
  refine ⟨3*C, by positivity, fun a ha N H hHN T hT => ?_⟩
  let D := (∫ x, g x)*logSectionDiagonal a H
  let E := C*N*H*((H:ℝ)+1)^k/T^k
  have hab (M : ℕ) (hm : H ≤ M) : |(logWindowCross g a M H T).re - D| ≤
      C*M*H*((H:ℝ)+1)^k/T^k := by
    simpa only [Complex.sub_re, Complex.ofReal_re, D] using
      (Complex.abs_re_le_norm _).trans (hGram a ha M H hm T hT)
  have hwide := (abs_le.mp (hab N hHN)).1
  have hnarrow := (abs_le.mp (hab H le_rfl)).2
  have hgap : C*H*H*((H:ℝ)+1)^k/T^k ≤ E := by
    dsimp only [E]
    gcongr
  have hpos := cross_square_completion hg.continuous hs hp a N H T
  rw [cross_self hg.continuous hs a N T] at hpos
  dsimp only [D, E] at *
  have h3 : 3*C*(N:ℝ)*H*((H:ℝ)+1)^k/T^k = 3*(C*N*H*((H:ℝ)+1)^k/T^k) := by ring
  linarith only [hwide, hnarrow, hgap, hpos, h3]

private theorem error_at_power_cutoffs {η θ : ℝ} (hη : 0 < η) (hη1 : η < 1)
    (hθ : 0 < θ) (r : ℝ) :
    ∃ k : ℕ, ∀ C : ℝ, ∀ᶠ T : ℝ in atTop,
      C * (⌊T^θ⌋₊ : ℝ) * (⌊T^η⌋₊ : ℝ) * ((⌊T^η⌋₊ : ℝ)+1)^k / T^k ≤ T^(-r) := by
  obtain ⟨k, hk⟩ := exists_nat_gt ((θ+η+r)/(1-η))
  have hkg := (div_lt_iff₀ (sub_pos.mpr hη1)).mp hk
  let b := (k:ℝ)*(1-η)-θ-η-r
  have hb : 0 < b := by dsimp only [b]; linarith only [hkg]
  refine ⟨k, fun C => ?_⟩
  filter_upwards [eventually_ge_atTop (1:ℝ), (tendsto_rpow_atTop hb).eventually_ge_atTop (|C| * 2^k)] with T hT hbig
  have ht := zero_lt_one.trans_le hT
  have hU := Nat.floor_le (Real.rpow_nonneg ht.le η)
  have hV := Nat.floor_le (Real.rpow_nonneg ht.le θ)
  have hstep : (⌊T^η⌋₊ : ℝ) + 1 ≤ 2*T^η := by linarith only [hU, Real.one_le_rpow hT hη.le]
  apply (div_le_iff₀ (pow_pos ht k)).mpr
  have hlarge := mul_le_mul_of_nonneg_right hbig (Real.rpow_nonneg ht.le (θ+η+η*(k:ℝ)))
  rw [← Real.rpow_add ht] at hlarge
  have heq : b + (θ+η+η*(k:ℝ)) = -r+(k:ℝ) := by dsimp [b]; ring
  rw [heq, Real.rpow_add ht (-r), Real.rpow_natCast] at hlarge
  refine le_trans ?_ hlarge
  calc
    _ ≤ |C| * T^θ*T^η*(2*T^η)^k := by gcongr <;> first | exact le_abs_self _ | assumption
    _ = _ := by
      rw [mul_pow, ← Real.rpow_natCast (T^η) k, ← Real.rpow_mul ht.le,
        Real.rpow_add ht, Real.rpow_add ht]
      ring

/-- Any growing power section strictly shorter than height contributes its
whole diagonal, up to an error smaller than any inverse power of height.
The containing section can have any fixed polynomial length. -/
theorem long_energy_reads_short_sections {g : ℝ → ℝ} (hg : ContDiff ℝ ∞ g)
    (hs : HasCompactSupport g) (hp : ∀ x, 0 ≤ g x)
    {η θ : ℝ} (hη : 0 < η) (hη1 : η < 1) (hηθ : η ≤ θ) (r : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ (a : ℕ → ℂ), (∀ n, 0 < n → ‖a n‖ ≤ 1) →
      (∫ x, g x) * logSectionDiagonal a ⌊T^η⌋₊ ≤
      (∫ x : ℝ, g x * ‖logSection a ⌊T^θ⌋₊ (T*x)‖^2) + T^(-r) := by
  obtain ⟨k, hk⟩ := error_at_power_cutoffs hη hη1 (hη.trans_le hηθ) r
  obtain ⟨C, _, hcomp⟩ := short_diagonal_below_long_energy hg hs hp k
  filter_upwards [eventually_ge_atTop (1:ℝ), hk C] with T hT herror
  intro a ha
  exact (hcomp a ha _ _ (Nat.floor_mono (Real.rpow_le_rpow_of_exponent_le hT hηθ)) T
    (zero_lt_one.trans_le hT)).trans (add_le_add_right herror _)


/-- A smooth plateau with any prescribed mass below one and support
strictly inside (0,1). Its two unused boundary collars allow a sharp
height interval starting at one. -/
private theorem interior_plateau {a : ℝ} (ha : 0 < a) (ha1 : a < 1) :
    ∃ (g : ℝ → ℝ) (δ : ℝ), 0 < δ ∧ δ < 1 ∧ ContDiff ℝ ∞ g ∧
      HasCompactSupport g ∧ (∀ x, 0 ≤ g x ∧ g x ≤ 1) ∧
      Function.support g ⊆ Set.Ioc δ 1 ∧ a ≤ ∫ x, g x := by
  let p : ContDiffBump (1/2:ℝ) := ⟨a/2,(1+a)/4,by positivity,by linarith⟩
  let δ := (1-a)/4
  have hδ : 0 < δ := div_pos (sub_pos.mpr ha1) (by norm_num)
  have hδ1 : δ < 1 := by dsimp only [δ]; linarith
  refine ⟨p,δ,hδ,hδ1,p.contDiff,p.hasCompactSupport,fun _ => ⟨p.nonneg,p.le_one⟩,?_,?_⟩
  · intro x hx
    rw [p.support_eq] at hx
    change dist x (1/2:ℝ) < (1+a)/4 at hx
    rw [Real.dist_eq, abs_lt] at hx
    dsimp only [Set.mem_Ioc,δ]
    constructor <;> linarith only [hx.1,hx.2,ha1]
  · let l := (1-a)/2
    let u := (1+a)/2
    have hlu : l ≤ u := by dsimp only [l,u]; linarith
    have hconst : (∫ x in l..u, p x) = u-l := by
      rw [intervalIntegral.integral_congr (g := fun _ : ℝ => (1:ℝ))]
      · simp only [intervalIntegral.integral_const,smul_eq_mul,mul_one]
      · intro x hx
        rw [Set.uIcc_of_le hlu] at hx
        apply p.one_of_mem_closedBall
        change dist x (1/2:ℝ) ≤ a/2
        rw [Real.dist_eq,abs_le]
        obtain ⟨h₁,h₂⟩ := hx
        dsimp only [l,u] at h₁ h₂
        constructor <;> linarith
    have hmono := setIntegral_le_integral (μ := volume) (s := Set.Ioc l u)
      (p.continuous.integrable_of_hasCompactSupport p.hasCompactSupport) (.of_forall p.nonneg')
    rw [← intervalIntegral.integral_of_le hlu,hconst] at hmono
    simpa only [l,u,show (1+a)/2-(1-a)/2=a by ring] using hmono

/-- With a smooth test fitted inside [1,T], every fraction below one of
the short diagonal is a lower bound for the sharp normalized energy. -/
theorem short_diagonal_below_sharp_long_mean
    {η θ q : ℝ} (hη : 0 < η) (hη1 : η < 1) (hηθ : η ≤ θ) (hq : 0 < q) (hq1 : q < 1) (r : ℝ) :
    ∀ᶠ T : ℝ in atTop, ∀ (a : ℕ → ℂ), (∀ n, 0 < n → ‖a n‖ ≤ 1) →
      q*logSectionDiagonal a ⌊T^η⌋₊ ≤
      (∫ t in (1:ℝ)..T, ‖logSection a ⌊T^θ⌋₊ t‖^2)/T + T^(-r) := by
  obtain ⟨g,δ,hδ,hδ1,hg,hs,hpos,hsup,hmass⟩ := interior_plateau hq hq1
  filter_upwards [long_energy_reads_short_sections hg hs (fun x => (hpos x).1) hη hη1 hηθ r,
    eventually_ge_atTop (1/δ),eventually_ge_atTop (1:ℝ)] with T hread hwide hT
  intro a ha
  specialize hread a ha
  have hT0 := zero_lt_one.trans_le hT
  let N := ⌊T^θ⌋₊
  let H := ⌊T^η⌋₊
  let f := fun x : ℝ => ‖logSection a N (T*x)‖^2
  have hf : Continuous f := ((section_cont a N).comp (continuous_const.mul continuous_id)).norm.pow 2
  have hcol : 1/T ≤ δ := (div_le_iff₀ hT0).mpr (by linarith only [(div_le_iff₀ hδ).mp hwide])
  have hcol1 := hcol.trans hδ1.le
  have hsup' : Function.support (fun x => g x*f x) ⊆ Set.Ioc (1/T) 1 := by
    intro x hx
    have hb := hsup (left_ne_zero_of_mul hx)
    exact ⟨hcol.trans_lt hb.1,hb.2⟩
  have hcomp : (∫ x, g x*f x) ≤ (∫ t in (1:ℝ)..T, ‖logSection a N t‖^2)/T := by
    rw [← setIntegral_eq_integral_of_forall_compl_eq_zero (s := Set.Ioc (1/T) 1)
      (fun x hx => by_contra fun h => hx (hsup' h)), ← intervalIntegral.integral_of_le hcol1]
    have hmono := intervalIntegral.integral_mono_on (μ := volume) hcol1 ((hg.continuous.mul hf).intervalIntegrable _ _)
      (hf.intervalIntegrable _ _) fun x _ => (mul_le_mul_of_nonneg_right (hpos x).2 (sq_nonneg _)).trans_eq (one_mul _)
    refine hmono.trans_eq ?_
    dsimp only [f]
    rw [intervalIntegral.integral_comp_mul_left (fun t : ℝ => ‖logSection a N t‖^2) hT0.ne',
      mul_one, mul_one_div_cancel hT0.ne', smul_eq_mul, div_eq_inv_mul]
  have hD : 0 ≤ logSectionDiagonal a H := sum_nonneg fun _ _ => sq_nonneg _
  exact ((mul_le_mul_of_nonneg_right hmass hD).trans hread).trans (add_le_add_left hcomp _)

open GaloisForLFunctions.MultiscaleMollifiedZetaField
open _root_.RHTower.Sieve (squarefreeDensity squarefreeDensity_eq)

/-- Limiting logarithmic coefficient of the squarefree diagonal at a
power cutoff, including its floor. -/
private theorem scaled_harmonic_diagonal {η : ℝ} (hη : 0 < η) :
    Tendsto (fun T : ℝ => harmonicMoebiusDiagonal ⌊T^η⌋₊/Real.log T) atTop
      (𝓝 (squarefreeDensity*η)) := by
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  have hlim := Real.tendsto_log_atTop.inv_tendsto_atTop.const_mul (12+|squarefreeHarmonicConstant|)
  simp only [mul_zero] at hlim
  refine squeeze_zero' (.of_forall fun _ => norm_nonneg _) ?_ hlim
  filter_upwards [eventually_gt_atTop (1:ℝ)] with T hT
  have hp := zero_lt_one.trans hT
  have hl := Real.log_pos hT
  have hX := Real.one_le_rpow hT.le hη.le
  have hD := squarefree_harmonic_finite_part hX
  have htail := Real.rpow_le_one_of_one_le_of_nonpos hX (by norm_num : -(1/2:ℝ) ≤ 0)
  rw [Real.log_rpow hp] at hD
  let v := harmonicMoebiusDiagonal (T^η) - squarefreeDensity*(η*Real.log T)
  have hb : |v| ≤ 12+|squarefreeHarmonicConstant| := by
    have hh := abs_add_le (v-squarefreeHarmonicConstant) squarefreeHarmonicConstant
    rw [sub_add_cancel] at hh
    change |v-_| ≤ _ at hD
    linarith only [hh,hD,htail]
  have he : harmonicMoebiusDiagonal (⌊T^η⌋₊:ℝ)/Real.log T-squarefreeDensity*η=v/Real.log T := by
    dsimp only [v,harmonicMoebiusDiagonal]
    rw [Nat.floor_natCast]
    field_simp [hl.ne']
    <;> ring
  rw [Real.norm_eq_abs, he, abs_div, abs_of_pos hl]
  exact (div_le_div_of_nonneg_right hb hl.le).trans_eq (div_eq_mul_inv _ _)

/-- Every fixed power length has a logarithmic floor on every sufficiently
large height interval [1,T]. For lengths above T the guaranteed coefficient
stays at the full squarefree density. -/
theorem logarithmic_floor_on_translated_moebius_windows {θ q : ℝ} (hθ : 0 < θ)
    (hq : q < squarefreeDensity*min θ 1) :
    ∀ᶠ T : ℝ in atTop, ∀ A : ℝ, q*T*Real.log T <
      ∫ t in (1+A)..(T+A), ‖moebiusPoly ⌊T^θ⌋₊ (linePoint t)‖^2 := by
  have hd : 0 < squarefreeDensity := by rw [squarefreeDensity_eq]; positivity
  obtain ⟨η,hη,hηmax⟩ := _root_.exists_between (max_lt (lt_min hθ zero_lt_one) ((div_lt_iff₀ hd).mpr
    (by linarith only [hq] : q < min θ 1*squarefreeDensity)))
  have he0 := (le_max_left 0 (q/squarefreeDensity)).trans_lt hη
  have hsmall := hηmax.trans_le (min_le_right θ 1)
  have hθ' := hηmax.le.trans (min_le_left θ 1)
  have hqη := (div_lt_iff₀ hd).mp ((le_max_right 0 _).trans_lt hη)
  have hdη : 0 < squarefreeDensity*η := mul_pos hd he0
  obtain ⟨p,hp,hp1⟩ := _root_.exists_between (max_lt zero_lt_one ((div_lt_one hdη).mpr (by linarith only [hqη] : q < squarefreeDensity*η)))
  have hp0 := (le_max_left 0 (q/(squarefreeDensity*η))).trans_lt hp
  have hprice := (div_lt_iff₀ hdη).mp ((le_max_right 0 _).trans_lt hp)
  have ha (n : ℕ) (hn : 0 < n) : ‖criticalMoebiusAmplitude n‖ ≤ 1 := by
    have hμ : ((ArithmeticFunction.moebius n : ℤ):ℝ)^2 ≤ 1 := by
      rcases ArithmeticFunction.moebius_eq_or n with h|h|h <;> simp [h]
    have hN : (1:ℝ) ≤ n := by exact_mod_cast hn
    have hb := (div_le_one (zero_lt_one.trans_le hN)).mpr (hμ.trans hN)
    rw [← criticalMoebiusAmplitude_sq hn] at hb
    nlinarith only [hb,sq_nonneg (‖criticalMoebiusAmplitude n‖-1)]
  have hread := short_diagonal_below_sharp_long_mean he0 hsmall hθ' hp0 hp1 0
  have hlim := ((scaled_harmonic_diagonal he0).const_mul p).sub Real.tendsto_log_atTop.inv_tendsto_atTop
  rw [sub_zero] at hlim
  filter_upwards [hread, hlim.eventually (lt_mem_nhds hprice), eventually_gt_atTop (1:ℝ)] with T hread hbig hT
  have ht := zero_lt_one.trans hT
  have hl := Real.log_pos hT
  intro A
  let a := fun n => criticalMoebiusAmplitude n * cexp (I*((-Real.log n:ℝ):ℂ)*A)
  have hn (n : ℕ) : ‖a n‖ = ‖criticalMoebiusAmplitude n‖ := by
    dsimp only [a]
    rw [norm_mul, show I*((-Real.log n:ℝ):ℂ)*(A:ℂ) = ((-Real.log n*A:ℝ):ℂ)*I by push_cast; ring,
      Complex.norm_exp_ofReal_mul_I, mul_one]
  specialize hread a (fun n h => (hn n).le.trans (ha n h))
  have hD (N : ℕ) : logSectionDiagonal a N = harmonicMoebiusDiagonal N := by
    simpa only [logSectionDiagonal, hn] using critical_moebius_frequency_diagonal N
  have hshift (N : ℕ) (t : ℝ) : logSection a N t = moebiusPoly N (linePoint (t+A)) := by
    rw [critical_moebius_frequency_section,logSection,genPoly,genPoly]
    refine sum_congr rfl fun n _ => ?_
    dsimp only [a]
    rw [mul_assoc,←Complex.exp_add]
    congr 2
    push_cast
    ring
  simp only [neg_zero,Real.rpow_zero,hD,hshift] at hread
  rw [intervalIntegral.integral_comp_add_right (fun t : ℝ => ‖moebiusPoly ⌊T^θ⌋₊ (linePoint t)‖^2)] at hread
  change q < p*(harmonicMoebiusDiagonal ⌊T^η⌋₊/Real.log T) - (Real.log T)⁻¹ at hbig
  have hh := mul_lt_mul_of_pos_right hbig hl
  have he : (p*(harmonicMoebiusDiagonal ⌊T^η⌋₊/Real.log T) - (Real.log T)⁻¹)*Real.log T =
      p*harmonicMoebiusDiagonal ⌊T^η⌋₊-1 := by field_simp
  rw [he] at hh
  have H := (lt_div_iff₀ ht).mp (by linarith only [hread,hh] :
    q*Real.log T < (∫ t in (1+A)..(T+A), ‖moebiusPoly ⌊T^θ⌋₊ (linePoint t)‖^2)/T)
  linarith only [H]


theorem logarithmic_floor_of_long_moebius_mean {θ q : ℝ} (hθ : 0 < θ)
    (hq : q < squarefreeDensity*min θ 1) :
    ∀ᶠ T : ℝ in atTop, q*T*Real.log T <
      ∫ t in (1:ℝ)..T, ‖moebiusPoly ⌊T^θ⌋₊ (linePoint t)‖^2 :=
  (logarithmic_floor_on_translated_moebius_windows hθ hq).mono (fun T h => by simpa using h 0)

end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
