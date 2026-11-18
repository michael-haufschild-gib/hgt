import GaloisForLFunctions.CountingHolography.Sections.TheThetaMeanOfTheUnweightedSquarePrefix
import GaloisForLFunctions.CountingHolography.Sections.VariationOfTheSignedSquareGeneratorReading
import GaloisForLFunctions.CountingHolography.Sections.SquareGeneratorPrefix
import GaloisForLFunctions.SurfaceOfSpecZ.ScaleLocality.PrimeLogarithmicWindows

/-!
# Unweighted square-generator prefixes on blocks of endpoints

Integrating the smooth long trace in the root variable pays the sharp
prefix with each generator used once. The upper-root quadrature error is
cubic. A bounded normalized primitive pays every endpoint on a block of
quarter-power length at the original cubic allowance.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Filter Topology MeasureTheory Finset SurfaceOfSpecZ.ScaleLocality

private abbrev H (v : ℝ) := v^2*squareLongTrace (2*Real.log v)
private abbrev P (n : ℕ) := Real.log (squareGeneratorPrefix n:ℝ)
private abbrev I (X : ℝ) := ∫ v in (0:ℝ)..X, H v

private theorem root_envelope : ∃ A : ℝ, 0 ≤ A ∧
    (∀ x : ℝ, 0 < x → x ≤ 1 → |H x| ≤ A) ∧
    (∀ x : ℝ, 1 ≤ x → |squareLongTrace (2*Real.log x)| ≤ A*x) := by
  obtain ⟨A,hA,h⟩ := squareLongTrace_bound
  have he (x : ℝ) : 1/2*|2*Real.log x|=|Real.log x| := by
    rw [abs_mul,abs_of_pos two_pos]; ring
  refine ⟨A,hA,fun x hx h₁ => ?_,fun x hx => ?_⟩
  · have ht := h (2*Real.log x)
    rw [he,abs_of_nonpos (Real.log_nonpos hx.le h₁),Real.exp_neg,Real.exp_log hx] at ht
    rw [H,abs_mul,abs_of_nonneg (sq_nonneg _)]
    calc x^2*|squareLongTrace (2*Real.log x)| ≤ x^2*(A*x⁻¹) := mul_le_mul_of_nonneg_left ht (sq_nonneg _)
         _ = A*x := by field_simp [hx.ne']
         _ ≤ A := mul_le_of_le_one_right hA h₁
  · simpa only [he,abs_of_nonneg (Real.log_nonneg hx),Real.exp_log (zero_lt_one.trans_le hx)] using h (2*Real.log x)

private theorem root_interval {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) :
    IntervalIntegrable H volume a b := by
  rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hab]
  obtain ⟨A,hA,hl,hu⟩ := root_envelope
  let C := A+A*b^3
  have hi : IntegrableOn (fun _ : ℝ => C) (Set.Ioc a b) :=
    (show IntegrableOn (fun _ : ℝ => C) (Set.Icc a b) from continuousOn_const.integrableOn_Icc).mono_set Set.Ioc_subset_Icc_self
  refine hi.mono' ((measurable_id.pow_const 2).mul (continuous_squareLongTrace.measurable.comp
    (measurable_const.mul Real.measurable_log))).aestronglyMeasurable ?_
  filter_upwards [ae_restrict_mem (μ := volume) measurableSet_Ioc] with x hx
  rw [Real.norm_eq_abs]
  by_cases h₁ : x ≤ 1
  · exact (hl x (ha.trans_lt hx.1) h₁).trans (le_add_of_nonneg_right (mul_nonneg hA (pow_nonneg (ha.trans hab) 3)))
  have hx₀ := le_of_lt (ha.trans_lt hx.1)
  rw [H,abs_mul,abs_of_nonneg (sq_nonneg _)]
  calc x^2*|squareLongTrace (2*Real.log x)| ≤ x^2*(A*x) := mul_le_mul_of_nonneg_left (hu x (le_of_not_ge h₁)) (sq_nonneg _)
       _ = A*x^3 := by ring
       _ ≤ A*b^3 := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hx₀ hx.2 3) hA
       _ ≤ C := le_add_of_nonneg_left hA

/-- Scaling the real integral gives the exact normalized moving primitive. -/
private theorem integral_rescale {X : ℝ} (hX : 0 < X) : I X=X^3*squarePrefixTrace (2*Real.log X) := by
  have he := intervalIntegral.smul_integral_comp_mul_left (f := H) (a := (0:ℝ)) (b := 1) X
  simp only [smul_eq_mul,mul_zero,mul_one] at he
  have hs (r : ℝ) : H (X*r)=X^2*(r^2*squareLongTrace (2*Real.log X+2*Real.log r)) := by
    by_cases hr : r=0
    · simp [hr,H]
    rw [H,Real.log_mul hX.ne' hr,mul_add,mul_pow]; ring
  rw [I,← he]
  simp_rw [hs]
  rw [intervalIntegral.integral_const_mul,intervalIntegral.integral_of_le zero_le_one]
  dsimp only [squarePrefixTrace]
  ring

private theorem cell_error : ∃ C : ℝ, 0 ≤ C ∧ ∀ j : ℕ, 0 < j →
    |H j-(∫ x in ((j:ℝ)-1)..(j:ℝ),H x)| ≤ C*(j:ℝ)^2 := by
  obtain ⟨A,hA,hl,hg⟩ := root_envelope
  obtain ⟨K,hK,h⟩ := squareLongTrace_unit_root_step
  let C := 2*A+K
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  refine ⟨C,hC,fun j hj => ?_⟩
  have hj₁ : (1:ℝ) ≤ j := by exact_mod_cast hj
  have hj₀ := zero_lt_one.trans_le hj₁
  have hab : (j:ℝ)-1 ≤ j := sub_le_self _ zero_le_one
  have hj' : 0 ≤ (j:ℝ)-1 := sub_nonneg.mpr hj₁
  have hc : ∀ x ∈ Set.uIoc ((j:ℝ)-1) (j:ℝ), ‖H j-H x‖ ≤ C*(j:ℝ)^2 := by
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    have hx₀ := hj'.trans_lt hx.1
    rw [Real.norm_eq_abs]
    by_cases he : j=1
    · subst j
      simp only [Nat.cast_one,one_pow,mul_one] at hx ⊢
      have hh := abs_sub_le (H 1) 0 (H x)
      simp only [sub_zero,zero_sub,abs_neg] at hh
      dsimp only [C]; linarith only [hh,hl 1 zero_lt_one le_rfl,hl x hx₀ hx.2,hK]
    have hj₂ : (2:ℝ) ≤ j := by exact_mod_cast (by omega : 2 ≤ j)
    have hx₁ : 1 ≤ x := by linarith only [hj₂,hx.1]
    have ht := h hx₁ hx.2 (show (j:ℝ) ≤ x+1 by linarith only [hx.1])
    have he' := Real.rpow_le_rpow_of_exponent_le hx₁ (by norm_num : (-(1/4):ℝ) ≤ 0)
    rw [Real.rpow_zero] at he'
    have hk := ht.trans (mul_le_of_le_one_right hK he')
    have hxx := (hg x hx₁).trans (mul_le_mul_of_nonneg_left hx.2 hA)
    have hsq : x^2 ≤ (j:ℝ)^2 := pow_le_pow_left₀ hx₀.le hx.2 2
    have hdiff : (j:ℝ)^2-x^2 ≤ 2*j := by
      rw [show (j:ℝ)^2-x^2=((j:ℝ)-x)*((j:ℝ)+x) by ring]
      exact (mul_le_mul (show (j:ℝ)-x ≤ 1 by linarith only [hx.1]) (show (j:ℝ)+x ≤ 2*j by linarith only [hx.2])
        (add_nonneg hj₀.le hx₀.le) zero_le_one).trans_eq (one_mul _)
    have heq : H j-H x = (j:ℝ)^2*(squareLongTrace (2*Real.log j)-squareLongTrace (2*Real.log x))+
        ((j:ℝ)^2-x^2)*squareLongTrace (2*Real.log x) := by dsimp only [H]; ring
    rw [heq]
    refine (abs_add_le _ _).trans ?_
    rw [abs_mul,abs_mul,abs_of_nonneg (sq_nonneg _),abs_of_nonneg (sub_nonneg.mpr hsq)]
    have hterm := mul_le_mul hdiff hxx (abs_nonneg _) (mul_nonneg two_pos.le hj₀.le)
    dsimp only [C]
    linarith only [hterm,mul_le_mul_of_nonneg_left hk (sq_nonneg (j:ℝ))]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hc
  rw [intervalIntegral.integral_sub intervalIntegrable_const (root_interval hj' hab),intervalIntegral.integral_const,
    smul_eq_mul,show (j:ℝ)-(j-1)=1 by ring,one_mul,abs_one,Real.norm_eq_abs,mul_one] at hi
  exact hi

/-- The sharp sum and its continuous integral differ by at most one
quadratic allowance per row, including the first unit interval. -/
private theorem prefix_quadrature : ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, |P N+I N| ≤ C*(N:ℝ)^3 := by
  obtain ⟨D,hD,hd⟩ := cell_error
  obtain ⟨E,hE,he⟩ := diagonalOrdinaryLog_smooth_error
  let C := D+E
  have hC : 0 ≤ C := add_nonneg hD hE
  refine ⟨C,hC,fun N => ?_⟩
  induction N with
  | zero => simp [P,I,squareGeneratorPrefix]
  | succ n ih =>
    let j := n+1
    have hj : 0 < j := Nat.succ_pos n
    have hc := hd j hj
    have hg := he hj
    change |diagonalOrdinaryLog j+H (j:ℝ)| ≤ E*(j:ℝ)^2 at hg
    have hn : (j:ℝ)-1=(n:ℝ) := by dsimp only [j]; push_cast; ring
    rw [hn] at hc
    have hinc : P j=P n+diagonalOrdinaryLog j := by
      have hq : (0:ℚ) < ordinaryPrimeGenerator (j • successorSquareTriple j) :=
        prod_pos fun k _ => zpow_pos (Nat.cast_pos.mpr (contactBase_pos k)) _
      have hp : (0:ℝ)<(squareGeneratorPrefix n:ℝ) := by exact_mod_cast squareGeneratorPrefix_pos n
      change Real.log (((∏ k ∈ Ioc 0 (n+1),ordinaryPrimeGenerator (k • successorSquareTriple k)):ℚ):ℝ)=_
      rw [prod_Ioc_succ_top (Nat.zero_le n),Rat.cast_mul]
      exact Real.log_mul hp.ne' (by exact_mod_cast hq.ne')
    have hconv := intervalIntegral.integral_add_adjacent_intervals (root_interval (a := 0) le_rfl (Nat.cast_nonneg n))
      (root_interval (Nat.cast_nonneg n) (Nat.cast_le.mpr (Nat.le_succ n)))
    change |P j+I j| ≤ _
    rw [hinc,show I j=I n+(∫ x in (n:ℝ)..(j:ℝ),H x) from hconv.symm]
    have hstep : (n:ℝ)^3+(j:ℝ)^2 ≤ (j:ℝ)^3 := by dsimp only [j]; push_cast; nlinarith only [sq_nonneg (n:ℝ),Nat.cast_nonneg (α := ℝ) n]
    have hbound := mul_le_mul_of_nonneg_left hstep hC
    change _ ≤ C*(j:ℝ)^3
    rw [abs_le] at ih hg hc ⊢
    dsimp only [C] at ih hbound ⊢
    constructor <;> linarith only [ih.1,ih.2,hg.1,hg.2,hc.1,hc.2,hbound]

/-- A bounded primitive at X pays the unweighted prefix throughout the
next quarter-power block of integer endpoints. -/
private theorem prefix_from_primitive : ∃ C : ℝ, 0 ≤ C ∧ ∀ {X : ℝ}, 1 ≤ X → |I X| ≤ X^3 →
    ∀ {d : ℕ}, X ≤ (d:ℝ) → (d:ℝ) ≤ X+1+(d:ℝ)^(1/4:ℝ) → |P d| ≤ C*(d:ℝ)^3 := by
  obtain ⟨E,hE,hq⟩ := prefix_quadrature
  obtain ⟨K,hK,h⟩ := squareLongTrace_root_growth
  refine ⟨E+1+2*K,by positivity,fun {X} hX hI {d} hd hu => ?_⟩
  have hd₁ := hX.trans hd
  have hd₀ := zero_lt_one.trans_le hd₁
  have hb (x : ℝ) (hx : x ∈ Set.uIoc X (d:ℝ)) : ‖H x‖ ≤ K*(d:ℝ)^(11/4:ℝ) := by
    rw [Set.uIoc_of_le hd] at hx
    have hx₁ := hX.trans hx.1.le
    have hx₀ := zero_lt_one.trans_le hx₁
    rw [Real.norm_eq_abs,H,abs_mul,abs_of_nonneg (sq_nonneg x)]
    calc _ ≤ x^2*(K*x^(3/4:ℝ)) := mul_le_mul_of_nonneg_left (h hx₁) (sq_nonneg x)
         _ = K*x^(11/4:ℝ) := by
           rw [show (11/4:ℝ)=2+3/4 by norm_num,Real.rpow_add hx₀,Real.rpow_two]; ring
         _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow hx₀.le hx.2 (by norm_num)) hK
  have hgap : (d:ℝ)-X ≤ 2*(d:ℝ)^(1/4:ℝ) := by linarith only [hu,Real.one_le_rpow hd₁ (by norm_num : (0:ℝ) ≤ 1/4)]
  have hi := intervalIntegral.norm_integral_le_of_norm_le_const hb
  rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hd)] at hi
  have hsegment := hi.trans (mul_le_mul_of_nonneg_left hgap (mul_nonneg hK (Real.rpow_nonneg hd₀.le _)))
  have he : K*(d:ℝ)^(11/4:ℝ)*(2*(d:ℝ)^(1/4:ℝ))=2*K*(d:ℝ)^3 := by
    rw [show K*(d:ℝ)^(11/4:ℝ)*(2*(d:ℝ)^(1/4:ℝ))=2*K*((d:ℝ)^(11/4:ℝ)*(d:ℝ)^(1/4:ℝ)) by ring,
      ← Real.rpow_add hd₀,show (11/4:ℝ)+1/4=(3:ℕ) by norm_num,Real.rpow_natCast]
  rw [he] at hsegment
  have hjoin := intervalIntegral.integral_add_adjacent_intervals (root_interval (a := 0) le_rfl (zero_le_one.trans hX))
    (root_interval (zero_le_one.trans hX) hd)
  change I X+(∫ x in X..(d:ℝ),H x)=I d at hjoin
  have hQ := hq d
  rw [abs_le] at hI hQ hsegment ⊢
  have hpow := pow_le_pow_left₀ (zero_le_one.trans hX) hd 3
  constructor <;> linarith only [hI.1,hI.2,hQ.1,hQ.2,hsegment.1,hsegment.2,hpow,hjoin]

/-- Every sufficiently late logarithmic window contains a block of endpoints
whose literal unweighted rational prefixes lie between reciprocal cubic powers. -/
theorem squareGeneratorPrefix_blocks_in_every_window :
    ∃ B : ℕ, 0 < B ∧ ∀ᶠ T : ℝ in atTop, ∃ n : ℕ, 0 < n ∧
      |2*Real.log n-T| ≤ 10*Real.log (T+2) ∧ ∀ {d : ℕ}, n ≤ d →
      (d:ℝ) ≤ (n:ℝ)+(n:ℝ)^(1/4:ℝ) →
      squareGeneratorPrefix d ≤ (B:ℚ)^(d^3) ∧ (squareGeneratorPrefix d)⁻¹ ≤ (B:ℚ)^(d^3) := by
  obtain ⟨C,_,h⟩ := prefix_from_primitive
  let B := ⌈Real.exp C⌉₊
  have hB : 0 < B := Nat.ceil_pos.mpr (Real.exp_pos _)
  have hb := (Real.le_log_iff_exp_le (Nat.cast_pos.mpr hB)).mpr (Nat.le_ceil (Real.exp C))
  refine ⟨B,hB,?_⟩
  filter_upwards [squarePrefixTrace_bounded_in_every_window,primeLogarithmicRadius_shape,eventually_ge_atTop (Real.exp 1)] with T ⟨u,hu,hf⟩ hT heT
  have hlog : 1 ≤ Real.log (T+2) := by
    simpa only [Real.log_exp] using Real.log_le_log (Real.exp_pos 1) (heT.trans (show T ≤ T+2 by linarith))
  have hradius : 32*Real.log (T+2) ≤ T := hT.2
  have hu₀ : 0 ≤ u := by linarith only [(abs_le.mp hu).1,hradius,hlog]
  let X := Real.exp (u/2)
  let n := upperSquareIndex u
  have hX : 1 ≤ X := Real.one_le_exp (by linarith only [hu₀])
  have hx := zero_lt_one.trans_le hX
  have hn : X ≤ (n:ℝ) := Nat.le_ceil _
  have hn' : (n:ℝ) ≤ X+1 := (Nat.ceil_lt_add_one hx.le).le
  have hI : |I X| ≤ X^3 := by
    rw [integral_rescale hx,abs_mul,abs_of_nonneg (pow_nonneg hx.le 3),
      show 2*Real.log X=u by dsimp only [X]; rw [Real.log_exp]; ring]
    exact mul_le_of_le_one_right (pow_nonneg hx.le 3) hf
  obtain ⟨hl,hr⟩ := upperSquareIndex_log_near hu₀
  refine ⟨n,upperSquareIndex_pos _,abs_le.mpr ⟨?_,?_⟩,?_⟩
  · linarith only [hl,(abs_le.mp hu).1,hlog]
  · linarith only [hr,(abs_le.mp hu).2,hlog]
  intro d hd hd'
  have hdn : (n:ℝ) ≤ d := Nat.cast_le.mpr hd
  have hd₀ : X ≤ (d:ℝ) := hn.trans hdn
  have hvalue := h hX hI hd₀ (by linarith only [hd',hn',Real.rpow_le_rpow (Nat.cast_nonneg n) hdn (by norm_num : (0:ℝ) ≤ 1/4)])
  have upper {q : ℚ} (hq : 0 < q) (hlq : Real.log (q:ℝ) ≤ C*(d:ℝ)^3) : q ≤ (B:ℚ)^(d^3) := by
    have he : Real.log ((B:ℝ)^(d^3))=Real.log B*(d:ℝ)^3 := by rw [Real.log_pow,Nat.cast_pow,mul_comm]
    have ht := hlq.trans (mul_le_mul_of_nonneg_right hb (pow_nonneg (Nat.cast_nonneg d) 3))
    rw [← he] at ht
    exact_mod_cast (Real.log_le_log_iff (by exact_mod_cast hq) (pow_pos (Nat.cast_pos.mpr hB) _)).mp ht
  refine ⟨upper (squareGeneratorPrefix_pos d) (abs_le.mp hvalue).2,upper (inv_pos.mpr (squareGeneratorPrefix_pos d)) ?_⟩
  rw [Rat.cast_inv,Real.log_inv]
  linarith only [(abs_le.mp hvalue).1]

#print axioms squareGeneratorPrefix_blocks_in_every_window

end GaloisForLFunctions.CountingHolography.Sections
