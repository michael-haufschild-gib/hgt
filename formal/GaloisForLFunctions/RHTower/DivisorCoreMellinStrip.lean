import GaloisForLFunctions.RHTower.DivisorCoreMellinBoundary
import GaloisForLFunctions.RHTower.LevinsonStripBound
import GaloisForLFunctions.HTGeometry.PhragmenLindelofPower
import GaloisForLFunctions.HTGeometry.VerticalStripContourShift

/-!
# Closed-strip decay and contour transport of the paired divisor source

The literal paired Mellin numerator is symmetric under s ↦ 2-s. Two
iterated divided differences remove both endpoint poles. Their combined
rational term already has quadratic tail decay. Polynomial zeta strip
bounds and Phragmén–Lindelöf propagate the proved boundary decay throughout
the closed strip. Every exponential-weighted vertical trace is integrable,
and its contour moves to the imaginary boundary with vanishing horizontal
edges. Identifying that contour with the physical signed head average is
not claimed here.
-/

noncomputable section
open Complex Filter Set Topology MeasureTheory Finset
open GaloisForLFunctions.HTGeometry
namespace RHTower

private def pairedEntireNumerator (P : Finset ℕ) (s : ℂ) : ℂ :=
  divisorCoreMellinNumerator P s*divisorCoreMellinNumerator P (2-s)

private lemma pairedEntireNumerator_diff (P : Finset ℕ) :
    Differentiable ℂ (pairedEntireNumerator P) :=
  (differentiable_divisorCoreMellinNumerator P).mul
    ((differentiable_divisorCoreMellinNumerator P).comp
      ((differentiable_const (2:ℂ)).sub differentiable_id))

private lemma entire_dslope {f : ℂ → ℂ} (hf : Differentiable ℂ f) (a : ℂ) :
    Differentiable ℂ (dslope f a) := by
  rw [← differentiableOn_univ]
  exact (Complex.differentiableOn_dslope (by simp : (univ : Set ℂ) ∈ 𝓝 a)).mpr hf.differentiableOn

/-- Entire paired remainder obtained by removing both symmetric endpoint poles. -/
def divisorCoreMellinPairEntire (P : Finset ℕ) (s : ℂ) : ℂ :=
  -dslope (dslope (pairedEntireNumerator P) 0) 2 s

/-- Both endpoint singularities are filled by the literal source's divided differences. -/
theorem differentiable_divisorCoreMellinPairEntire (P : Finset ℕ) :
    Differentiable ℂ (divisorCoreMellinPairEntire P) :=
  (entire_dslope (entire_dslope (pairedEntireNumerator_diff P) 0) 2).neg

private lemma numerator_zero (P : Finset ℕ) :
    pairedEntireNumerator P 0=2*divisorCoreMellinPairResidue P := by
  change divisorCoreMellinNumerator P 0*divisorCoreMellinNumerator P (2-0) =
    2*(divisorCoreMellinNumerator P 0*divisorCoreMellinNumerator P (2-0)/(2-0))
  ring

/-- Exact two-pole subtraction, whose combined rational term has quadratic decay. -/
theorem divisorCoreMellinPairEntire_eq (P : Finset ℕ) {s : ℂ}
    (hs0 : s ≠ 0) (hs2 : s ≠ 2) :
    divisorCoreMellinPairEntire P s = divisorCoreMellinPair P s-
      2*divisorCoreMellinPairResidue P/(s*(2-s)) := by
  have hsym : pairedEntireNumerator P 2=pairedEntireNumerator P 0 := by
    simp [pairedEntireNumerator,mul_comm]
  rw [divisorCoreMellinPairEntire,dslope_of_ne _ hs2,
    slope_def_field,dslope_of_ne _ hs0,dslope_of_ne _ (by norm_num : (2:ℂ) ≠ 0),
    slope_def_field,slope_def_field,hsym,sub_self,zero_div,sub_zero,
    numerator_zero P]
  rw [divisorCoreMellinPair,divisorCoreMellin,divisorCoreMellin,pairedEntireNumerator]
  have hs2' : 2-s ≠ 0 := sub_ne_zero.mpr hs2.symm
  field_simp
  ring

private lemma pair_symm (P : Finset ℕ) (s : ℂ) :
    divisorCoreMellinPair P (2-s)=divisorCoreMellinPair P s := by
  simp [divisorCoreMellinPair,mul_comm]

private lemma denominator_im (s : ℂ) : s.im^2 ≤ ‖s*(2-s)‖ := by
  have ha := Complex.abs_im_le_norm s
  have hb : |s.im| ≤ ‖2-s‖ := by simpa using Complex.abs_im_le_norm (2-s)
  rw [norm_mul]
  nlinarith [mul_le_mul ha hb (abs_nonneg _) (norm_nonneg _),sq_abs s.im]

private lemma entire_boundary_high (P : Finset ℕ) (hP : P.Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, (s.re=0 ∨ s.re=2) → 3 ≤ |s.im| →
      ‖divisorCoreMellinPairEntire P s‖ ≤ C/(1+s.im^2) := by
  obtain ⟨C,hC,hb⟩ := exists_bound_divisorCoreMellinPair_boundary P hP
  refine ⟨C+4*‖divisorCoreMellinPairResidue P‖,by positivity,?_⟩
  intro s hre ht
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at ht
  have hs2 : s ≠ 2 := by intro h; norm_num [h] at ht
  have hk : ‖divisorCoreMellinPair P s‖ ≤ C/(1+s.im^2) := by
    rcases hre with h0 | h2
    · have he : s=(s.im:ℂ)*I := by apply Complex.ext <;> simp [h0]
      simpa only [← he] using hb s.im ht
    · have he : 2-s=((-s.im:ℝ):ℂ)*I := by apply Complex.ext <;> simp [h2]
      have h := hb (-s.im) (by simpa using ht)
      rw [← he,pair_symm] at h
      simpa using h
  have hsq : 0 < s.im^2 := by nlinarith [sq_abs s.im]
  have hr : ‖2*divisorCoreMellinPairResidue P/(s*(2-s))‖ ≤
      (4*‖divisorCoreMellinPairResidue P‖)/(1+s.im^2) := by
    rw [norm_div,norm_mul,Complex.norm_ofNat]
    apply (div_le_div_of_nonneg_left (by positivity) hsq (denominator_im s)).trans
    rw [div_le_div_iff₀ hsq (by positivity : (0:ℝ)<1+s.im^2)]
    have ht1 : 1 ≤ s.im^2 := by nlinarith [sq_abs s.im]
    nlinarith [mul_nonneg (norm_nonneg (divisorCoreMellinPairResidue P)) (sub_nonneg.mpr ht1)]
  rw [divisorCoreMellinPairEntire_eq P hs0 hs2]
  apply (norm_sub_le _ _).trans
  rw [add_div]
  linarith


private lemma source_strip_polynomial :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ w : ℂ, |w.re| ≤ 2 → 3 ≤ |w.im| →
      ‖divisorSourceEntire w‖ ≤ C*(1+|w.im|)^N := by
  obtain ⟨C₁,N₁,hC₁,hζ⟩ := exists_bound_norm_riemannZeta_strip 2
  obtain ⟨C₂,N₂,hC₂,hder⟩ := exists_bound_norm_deriv_riemannZeta_strip 2
  let N := 2*(N₁+N₂+1)
  let C := C₂+C₁^2+2*|Real.eulerMascheroniConstant| *C₁
  have hC : 0 ≤ C := by dsimp [C]; positivity
  refine ⟨C*2^N,N,by positivity,?_⟩
  intro w hw ht
  have hbase : 1 ≤ 2*|w.im| := by linarith
  have hζ' : ‖riemannZeta w‖ ≤ C₁*(2*|w.im|)^N₁ := by
    have h := hζ w.re w.im hw (by linarith)
    rw [Complex.re_add_im] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_left₀ (abs_nonneg _) (by linarith : |w.im| ≤ 2*|w.im|) _) hC₁)
  have hd : ‖deriv riemannZeta w‖ ≤ C₂*(2*|w.im|)^N :=
    (hder w hw (by linarith)).trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hbase (by dsimp [N]; omega)) hC₂)
  have hsq : ‖riemannZeta w‖^2 ≤ C₁^2*(2*|w.im|)^N := by
    have h := pow_le_pow_left₀ (norm_nonneg _) hζ' 2
    rw [mul_pow,← pow_mul] at h
    exact h.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hbase (by dsimp [N]; omega)) (sq_nonneg C₁))
  have hlin : ‖riemannZeta w‖ ≤ C₁*(2*|w.im|)^N :=
    hζ'.trans (mul_le_mul_of_nonneg_left
      (pow_le_pow_right₀ hbase (by dsimp [N]; omega)) hC₁)
  have hw1 : w ≠ 1 := by intro h; norm_num [h] at ht
  rw [divisorSourceEntire_eq hw1]
  have hn : ‖-deriv riemannZeta w-riemannZeta w^2+
      2*(Real.eulerMascheroniConstant:ℂ)*riemannZeta w‖ ≤
      ‖deriv riemannZeta w‖+‖riemannZeta w‖^2+
        2*|Real.eulerMascheroniConstant| *‖riemannZeta w‖ := by
    have h₁ := norm_add_le (-deriv riemannZeta w-riemannZeta w^2)
      (2*(Real.eulerMascheroniConstant:ℂ)*riemannZeta w)
    have h₂ := norm_sub_le (-deriv riemannZeta w) (riemannZeta w^2)
    simp only [norm_neg,norm_pow,norm_mul,Complex.norm_ofNat,Complex.norm_real,
      Real.norm_eq_abs] at h₁ h₂
    linarith
  apply hn.trans
  have h₃ := mul_le_mul_of_nonneg_left hlin
    (show 0 ≤ 2*|Real.eulerMascheroniConstant| by positivity)
  have hb : ‖deriv riemannZeta w‖+‖riemannZeta w‖^2+
      2*|Real.eulerMascheroniConstant| *‖riemannZeta w‖ ≤ C*(2*|w.im|)^N := by
    dsimp [C]
    nlinarith
  apply hb.trans
  rw [mul_pow,← mul_assoc]
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (abs_nonneg _) (by linarith : |w.im| ≤ 1+|w.im|) _)
    (by positivity)


private lemma euler_strip_bound (P : Finset ℕ) {s : ℂ} (hs : 0 ≤ s.re) :
    ‖divisorCoreMellinEuler P s‖ ≤ ∏p∈P, (1+Real.exp (Real.log p/2)) := by
  rw [divisorCoreMellinEuler,norm_prod]
  apply prod_le_prod (fun _ _ => norm_nonneg _)
  intro p hp
  have hlog := Real.log_natCast_nonneg p
  calc
    _ ≤ ‖(1:ℂ)‖+‖Complex.exp ((1/2-s)*(Real.log p : ℂ))‖ := norm_sub_le _ _
    _ = 1+Real.exp ((1/2-s.re)*Real.log p) := by
      simp only [norm_one,norm_exp,mul_re,sub_re,ofReal_re,ofReal_im,mul_zero,sub_zero]
      norm_num
    _ ≤ _ := by gcongr; nlinarith

private lemma core_strip_polynomial (P : Finset ℕ) (hP : P.Nonempty) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 2 → 3 ≤ |s.im| →
      ‖divisorCoreMellin P s‖ ≤ C*(1+|s.im|)^N := by
  obtain ⟨C,N,hC,hB⟩ := source_strip_polynomial
  let D : ℝ := ∏p∈P, (1+Real.exp (Real.log p/2))
  have hD : 0 ≤ D := prod_nonneg (fun p hp => by positivity)
  refine ⟨C*D,N,by positivity,?_⟩
  intro s hs hs2 ht
  have hsH : s ≠ 1/2 := by intro h; norm_num [h] at ht
  have hw : |(s-1/2).re| ≤ 2 := by
    norm_num [abs_le]
    constructor <;> linarith
  have hi : (s-1/2).im=s.im := by simp
  have hb := hB (s-1/2) hw (by simpa [hi] using ht)
  rw [hi] at hb
  have he := euler_strip_bound P hs
  have hd : 1 ≤ ‖2*s*(s-1/2)‖ := by
    have h₁ := Complex.abs_im_le_norm s
    have h₂ : |s.im| ≤ ‖s-1/2‖ := by simpa using Complex.abs_im_le_norm (s-1/2)
    have hh := mul_le_mul h₁ h₂ (abs_nonneg _) (norm_nonneg _)
    rw [norm_mul,norm_mul,Complex.norm_ofNat]
    nlinarith [sq_abs s.im]
  rw [divisorCoreMellin_eq P hP hsH,norm_div,norm_mul]
  apply (div_le_div_of_nonneg_left (mul_nonneg (norm_nonneg _) (norm_nonneg _))
    zero_lt_one hd).trans
  rw [div_one]
  calc
    _ ≤ (C*(1+|s.im|)^N)*D := mul_le_mul hb he (norm_nonneg _) (by positivity)
    _ = _ := by ring

private def weightedPairEntire (P : Finset ℕ) (s : ℂ) : ℂ :=
  (s+1)^2*divisorCoreMellinPairEntire P s

private lemma weightedPairEntire_diff (P : Finset ℕ) :
    Differentiable ℂ (weightedPairEntire P) :=
  ((differentiable_id.add_const 1).pow 2).mul
    (differentiable_divisorCoreMellinPairEntire P)

private lemma strip_weight_bound {s : ℂ} (hs : 0 ≤ s.re) (hs2 : s.re ≤ 2) :
    ‖s+1‖^2 ≤ 9*(1+|s.im|)^2 := by
  have hn := Complex.norm_le_abs_re_add_abs_im (s+1)
  have hr : |(s+1).re|=s.re+1 := by simp [abs_of_nonneg (show 0 ≤ s.re+1 by linarith)]
  simp only [hr,Complex.add_im,Complex.one_im,add_zero] at hn
  have hb : ‖s+1‖ ≤ 3*(1+|s.im|) := by linarith [abs_nonneg s.im]
  have h := pow_le_pow_left₀ (norm_nonneg _) hb 2
  nlinarith

private lemma weighted_strip_polynomial (P : Finset ℕ) (hP : P.Nonempty) :
    ∃ (C : ℝ) (N : ℕ), 0 ≤ C ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 2 → 3 ≤ |s.im| →
      ‖weightedPairEntire P s‖ ≤ C*(1+|s.im|)^N := by
  obtain ⟨C,N,hC,hb⟩ := core_strip_polynomial P hP
  let D : ℝ := C^2+2*‖divisorCoreMellinPairResidue P‖
  have hD : 0 ≤ D := by dsimp [D]; positivity
  refine ⟨9*D,2*N+2,by positivity,?_⟩
  intro s hs hs2 ht
  have hs0 : s ≠ 0 := by intro h; norm_num [h] at ht
  have hs2' : s ≠ 2 := by intro h; norm_num [h] at ht
  have hi : |(2-s).im|=|s.im| := by simp
  have hb₁ := hb s hs hs2 ht
  have hb₂ := hb (2-s) (by simp; linarith) (by simp; linarith) (by simpa [hi] using ht)
  rw [hi] at hb₂
  have hk : ‖divisorCoreMellinPair P s‖ ≤ C^2*(1+|s.im|)^(2*N) := by
    rw [divisorCoreMellinPair,norm_mul]
    calc
      _ ≤ (C*(1+|s.im|)^N)*(C*(1+|s.im|)^N) :=
        mul_le_mul hb₁ hb₂ (norm_nonneg _) (by positivity)
      _ = _ := by rw [two_mul N,pow_add]; ring
  have hd : 1 ≤ ‖s*(2-s)‖ := by
    apply le_trans _ (denominator_im s)
    nlinarith [sq_abs s.im]
  have hr : ‖2*divisorCoreMellinPairResidue P/(s*(2-s))‖ ≤
      2*‖divisorCoreMellinPairResidue P‖ := by
    rw [norm_div,norm_mul,Complex.norm_ofNat]
    simpa using div_le_div_of_nonneg_left (by positivity : 0 ≤ 2*‖divisorCoreMellinPairResidue P‖)
      zero_lt_one hd
  have hpow : 1 ≤ (1+|s.im|)^(2*N) := one_le_pow₀ (by linarith [abs_nonneg s.im])
  have he : ‖divisorCoreMellinPairEntire P s‖ ≤ D*(1+|s.im|)^(2*N) := by
    rw [divisorCoreMellinPairEntire_eq P hs0 hs2']
    apply (norm_sub_le _ _).trans
    dsimp [D]
    nlinarith [mul_le_mul_of_nonneg_left hpow
      (show 0 ≤ 2*‖divisorCoreMellinPairResidue P‖ by positivity)]
  rw [weightedPairEntire,norm_mul,norm_pow]
  calc
    _ ≤ (9*(1+|s.im|)^2)*(D*(1+|s.im|)^(2*N)) :=
      mul_le_mul (strip_weight_bound hs hs2) he (norm_nonneg _) (by positivity)
    _ = _ := by rw [pow_add]; ring


/-- The entire two-pole remainder decays quadratically throughout the full
closed strip. All growth and both boundary inputs are proved for the actual source. -/
theorem exists_bound_divisorCoreMellinPairEntire_strip (P : Finset ℕ) (hP : P.Nonempty) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ s : ℂ, 0 ≤ s.re → s.re ≤ 2 →
      ‖divisorCoreMellinPairEntire P s‖ ≤ C/(1+s.im^2) := by
  obtain ⟨C,hC,hboundary⟩ := entire_boundary_high P hP
  have hedge (σ : ℝ) (hσ : σ=0 ∨ σ=2) :
      ∃ C' : ℝ, 0 ≤ C' ∧ ∀s : ℂ, s.re=σ → ‖weightedPairEntire P s‖ ≤ C' := by
    apply exists_line_bound_of_high (weightedPairEntire_diff P).continuous
      (σ := σ) (C := 18*C) (T := 3) (by positivity) (by norm_num)
    intro t ht
    let s : ℂ := (σ:ℂ)+(t:ℂ)*I
    have hs : s.re=0 ∨ s.re=2 := by simpa [s] using hσ
    have hs0 : 0 ≤ s.re := by rcases hs with h | h <;> simp [h]
    have hs2 : s.re ≤ 2 := by rcases hs with h | h <;> simp [h]
    have hi : s.im=t := by simp [s]
    have hb := hboundary s hs (by simpa [hi] using ht)
    rw [hi] at hb
    change ‖weightedPairEntire P s‖ ≤ _
    rw [weightedPairEntire,norm_mul,norm_pow]
    have hw := strip_weight_bound hs0 hs2
    rw [hi] at hw
    apply (mul_le_mul hw hb (norm_nonneg _) (by positivity)).trans
    have htq : (1+|t|)^2 ≤ 2*(1+t^2) := by nlinarith [sq_abs t,sq_nonneg (|t|-1)]
    rw [← mul_div_assoc,div_le_iff₀ (by positivity : (0:ℝ)<1+t^2)]
    nlinarith [mul_le_mul_of_nonneg_left htq hC]
  obtain ⟨C₀,hC₀,h₀⟩ := hedge 0 (Or.inl rfl)
  obtain ⟨C₂,hC₂,h₂⟩ := hedge 2 (Or.inr rfl)
  obtain ⟨D,N,hD,hpoly⟩ := weighted_strip_polynomial P hP
  have hhigh : ∀s : ℂ, (0:ℝ) ≤ s.re → s.re ≤ 2 → (3:ℝ) ≤ |s.im| →
      ‖weightedPairEntire P s‖ ≤ D*(1+|s.im|)^(N:ℝ) := by
    intro s hs hs2 ht
    simpa only [Real.rpow_natCast] using hpoly s hs hs2 ht
  obtain ⟨D',hD',hfull⟩ := exists_strip_bound_of_high
    (weightedPairEntire_diff P).continuous (by positivity : 0 ≤ (N:ℝ)) hD
    (by norm_num : (0:ℝ) ≤ 3) (by norm_num : (0:ℝ) ≤ 2) hhigh
  have hleft : ∀s : ℂ, s.re=0 → ‖weightedPairEntire P s‖ ≤ C₀*‖s-((-1:ℝ):ℂ)‖^(0:ℝ) := by
    intro s hs
    simpa using h₀ s hs
  have hright : ∀s : ℂ, s.re=2 → ‖weightedPairEntire P s‖ ≤ C₂*‖s-((-1:ℝ):ℂ)‖^(0:ℝ) := by
    intro s hs
    simpa using h₂ s hs
  have hPL := norm_le_mul_rpow_of_vertical_strip
    (by norm_num : (0:ℝ)<2) (by norm_num : (0:ℝ) ≤ 0) (by norm_num : (-1:ℝ)<0)
    (weightedPairEntire_diff P) hD' (by positivity : 0 ≤ (N:ℝ)) hfull hleft hright
  refine ⟨max C₀ C₂,le_trans hC₀ (le_max_left _ _),?_⟩
  intro s hs hs2
  have hb : ‖weightedPairEntire P s‖ ≤ max C₀ C₂ := by simpa using hPL s hs hs2
  have hw : 1+s.im^2 ≤ ‖s+1‖^2 := by
    rw [← Complex.normSq_eq_norm_sq,Complex.normSq_apply]
    simp only [Complex.add_re,Complex.one_re,Complex.add_im,Complex.one_im,add_zero]
    nlinarith
  rw [weightedPairEntire,norm_mul,norm_pow] at hb
  apply (le_div_iff₀ (by positivity : (0:ℝ)<1+s.im^2)).mpr
  nlinarith [mul_le_mul_of_nonneg_right hw (norm_nonneg (divisorCoreMellinPairEntire P s))]

/-- Every closed-strip vertical trace of the actual entire remainder is absolutely integrable. -/
theorem integrable_divisorCoreMellinPairEntire_line (P : Finset ℕ) (hP : P.Nonempty)
    {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ2 : σ ≤ 2) :
    Integrable (fun t : ℝ => divisorCoreMellinPairEntire P ((σ:ℂ)+(t:ℂ)*I)) := by
  obtain ⟨C,hC,hb⟩ := exists_bound_divisorCoreMellinPairEntire_strip P hP
  have hc : Continuous (fun t : ℝ => divisorCoreMellinPairEntire P ((σ:ℂ)+(t:ℂ)*I)) :=
    (differentiable_divisorCoreMellinPairEntire P).continuous.comp (by fun_prop)
  apply (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
  filter_upwards with t
  simpa [div_eq_mul_inv] using hb ((σ:ℂ)+(t:ℂ)*I) (by simpa using hσ0) (by simpa using hσ2)


private def exponentialPairEntire (P : Finset ℕ) (a : ℝ) (s : ℂ) : ℂ :=
  Complex.exp ((a:ℂ)*s)*divisorCoreMellinPairEntire P s

private lemma exponentialPairEntire_diff (P : Finset ℕ) (a : ℝ) :
    Differentiable ℂ (exponentialPairEntire P a) :=
  ((differentiable_id.const_mul (a:ℂ)).cexp).mul
    (differentiable_divisorCoreMellinPairEntire P)

private lemma exponential_strip_bound (P : Finset ℕ) (hP : P.Nonempty) (a : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀s : ℂ, 0 ≤ s.re → s.re ≤ 2 →
      ‖exponentialPairEntire P a s‖ ≤ C/(1+s.im^2) := by
  obtain ⟨C,hC,hb⟩ := exists_bound_divisorCoreMellinPairEntire_strip P hP
  refine ⟨Real.exp (2*|a|)*C,by positivity,?_⟩
  intro s hs hs2
  have he : ‖Complex.exp ((a:ℂ)*s)‖ ≤ Real.exp (2*|a|) := by
    rw [norm_exp]
    apply Real.exp_le_exp.mpr
    simp only [mul_re,ofReal_re,ofReal_im,zero_mul,sub_zero]
    calc a*s.re ≤ |a| *s.re := mul_le_mul_of_nonneg_right (le_abs_self a) hs
         _ ≤ |a| *2 := mul_le_mul_of_nonneg_left hs2 (abs_nonneg a)
         _ = _ := by ring
  rw [exponentialPairEntire,norm_mul]
  calc
    _ ≤ Real.exp (2*|a|)*(C/(1+s.im^2)) :=
      mul_le_mul he (hb s hs hs2) (norm_nonneg _) (by positivity)
    _ = _ := by ring

/-- The exponential Mellin weight preserves absolute integrability on every
line of the closed strip, for every fixed real logarithmic dilation. -/
theorem integrable_exp_mul_divisorCoreMellinPairEntire_line
    (P : Finset ℕ) (hP : P.Nonempty) (a : ℝ) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ2 : σ ≤ 2) :
    Integrable (fun t : ℝ => Complex.exp ((a:ℂ)*((σ:ℂ)+(t:ℂ)*I))*
      divisorCoreMellinPairEntire P ((σ:ℂ)+(t:ℂ)*I)) := by
  obtain ⟨C,hC,hb⟩ := exponential_strip_bound P hP a
  have hc : Continuous (fun t : ℝ => exponentialPairEntire P a ((σ:ℂ)+(t:ℂ)*I)) :=
    (exponentialPairEntire_diff P a).continuous.comp (by fun_prop)
  apply (integrable_inv_one_add_sq.const_mul C).mono' hc.aestronglyMeasurable
  filter_upwards with t
  simpa [div_eq_mul_inv] using hb ((σ:ℂ)+(t:ℂ)*I) (by simpa using hσ0) (by simpa using hσ2)

/-- The actual entire remainder's Mellin contour moves to the imaginary
boundary: both horizontal edges vanish by the proved full-strip bound. -/
theorem integral_exp_mul_divisorCoreMellinPairEntire_shift
    (P : Finset ℕ) (hP : P.Nonempty) (a : ℝ) {σ : ℝ} (hσ0 : 0 ≤ σ) (hσ2 : σ ≤ 2) :
    (∫ t : ℝ, Complex.exp ((a:ℂ)*((σ:ℂ)+(t:ℂ)*I))*
      divisorCoreMellinPairEntire P ((σ:ℂ)+(t:ℂ)*I)) =
    ∫ t : ℝ, Complex.exp ((a:ℂ)*(t:ℂ)*I)*divisorCoreMellinPairEntire P ((t:ℂ)*I) := by
  obtain ⟨C,hC,hb⟩ := exponential_strip_bound P hP a
  have hquad : Tendsto (fun T : ℝ => 1+T^2) atTop atTop :=
    tendsto_atTop_add_const_left _ 1 (tendsto_pow_atTop two_ne_zero)
  have hdec : Tendsto (fun T : ℝ => C/(1+T^2)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hquad
  have hlines := integral_vertical_line_eq_of_horizontal_tendsto
    (G := exponentialPairEntire P a) hσ0
    (exponentialPairEntire_diff P a).differentiableOn
    (integrable_exp_mul_divisorCoreMellinPairEntire_line P hP a (by norm_num) (by norm_num))
    (integrable_exp_mul_divisorCoreMellinPairEntire_line P hP a hσ0 hσ2)
  have htop : Tendsto (fun T : ℝ => ∫ u in (0:ℝ)..σ,
      exponentialPairEntire P a ((u:ℂ)+(T:ℂ)*I)) atTop (𝓝 0) := by
    apply tendsto_intervalIntegral_of_tendsto_bound (M := fun T : ℝ => C/(1+T^2))
      (hgt := fun T => T) _ hdec
    filter_upwards with T u hu
    have hu' : u ∈ Icc (0:ℝ) σ := by
      rw [← uIcc_of_le hσ0]
      exact uIoc_subset_uIcc hu
    simpa using hb ((u:ℂ)+(T:ℂ)*I) (by simpa using hu'.1) (by simpa using hu'.2.trans hσ2)
  have hbot : Tendsto (fun T : ℝ => ∫ u in (0:ℝ)..σ,
      exponentialPairEntire P a ((u:ℂ)+((-T:ℝ):ℂ)*I)) atTop (𝓝 0) := by
    apply tendsto_intervalIntegral_of_tendsto_bound (M := fun T : ℝ => C/(1+T^2))
      (hgt := fun T => -T) _ hdec
    filter_upwards with T u hu
    have hu' : u ∈ Icc (0:ℝ) σ := by
      rw [← uIcc_of_le hσ0]
      exact uIoc_subset_uIcc hu
    simpa using hb ((u:ℂ)+((-T:ℝ):ℂ)*I) (by simpa using hu'.1) (by simpa using hu'.2.trans hσ2)
  simpa [exponentialPairEntire,mul_assoc] using hlines hbot htop

end RHTower
