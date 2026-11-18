import GaloisForLFunctions.CountingHolography.Sections.SquareGeneratorPrefix
import GaloisForLFunctions.CountingHolography.Sections.SparseSquareConductorsDetectTheZeroWidth
import GaloisForLFunctions.CountingHolography.Sections.TheDyadicPrimeWeightOfSquareConductors
import Mathlib.NumberTheory.LSeries.Convergence

/-! # The product over all smaller square conductors

A two-sided allowance for a cumulative signed logarithm gives one small
diagonal price in every sufficiently long power interval. These sparse
samples suffice to recover the zero width. Numerator and denominator
factors at different conductors may cancel in the prefix product.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology SquareRootThreshold SurfaceOfSpecZ

private def prefixSum (f : ℕ → ℝ) (N : ℕ) := ∑ n ∈ Ioc 0 N, f n

private theorem power_gaps_of_signed_prefix (f : ℕ → ℝ) {θ r C : ℝ}
    (hθ : 0 < θ) (hθ' : θ < 1) (hr : θ ≤ r) (hC : 0 ≤ C)
    (hprefix : ∀ N : ℕ, |prefixSum f N| ≤ C*(N:ℝ)^r) :
    ∃ A : ℝ, 0 ≤ A ∧ PowGaps θ {n : ℕ | 0 < n ∧ f n ≤ A*(n:ℝ)^(r-θ)} := by
  let A := 4*C*(2:ℝ)^(r-θ)
  have hA : 0 ≤ A := by dsimp only [A]; positivity
  obtain ⟨X,hX⟩ := eventually_atTop.mp (((eventually_ge_atTop (1:ℝ)).and
    ((tendsto_rpow_atTop hθ).eventually_ge_atTop 2)).and
    ((tendsto_rpow_atTop (sub_pos.mpr hθ')).eventually_ge_atTop 2))
  refine ⟨A,hA,fun _ hn => hn.1,1,X,zero_le_one,fun x hx => ?_⟩
  obtain ⟨⟨hx₁,hgrow⟩,hgap⟩ := hX x hx
  have hx₀ := zero_lt_one.trans_le hx₁
  have hxθ := Real.rpow_pos_of_pos hx₀ θ
  have hhalf : 2*x^θ ≤ x := by
    have h := mul_le_mul_of_nonneg_right hgap hxθ.le
    rwa [← Real.rpow_add hx₀,sub_add_cancel,Real.rpow_one] at h
  let a := ⌊x-x^θ⌋₊
  let b := ⌊x⌋₊
  have ha : (a:ℝ) ≤ x-x^θ := Nat.floor_le (by linarith only [hhalf,hxθ.le])
  have hb : (b:ℝ) ≤ x := Nat.floor_le hx₀.le
  have hax : x-x^θ < (a:ℝ)+1 := Nat.lt_floor_add_one _
  have hbx : x < (b:ℝ)+1 := Nat.lt_floor_add_one _
  have hab : a < b := by exact_mod_cast (show (a:ℝ) < b by linarith only [ha,hbx,hgrow])
  have hc : x^θ/2 ≤ ((Ioc a b).card:ℝ) := by
    rw [Nat.card_Ioc,Nat.cast_sub hab.le]
    linarith only [ha,hbx,hgrow]
  have hpow {j : ℕ} (hj : (j:ℝ) ≤ x) := Real.rpow_le_rpow (Nat.cast_nonneg j) hj (hθ.le.trans hr)
  have hb' := (abs_le.mp (hprefix b)).2.trans (mul_le_mul_of_nonneg_left (hpow hb) hC)
  have ha' := (neg_le_neg (mul_le_mul_of_nonneg_left (hpow (ha.trans (sub_le_self _ hxθ.le))) hC)).trans
    (abs_le.mp (hprefix a)).1
  have hsum := sum_Ioc_consecutive f (Nat.zero_le a) hab.le
  change prefixSum f a+(∑ j ∈ Ioc a b, f j)=prefixSum f b at hsum
  have he : x^θ*x^(r-θ)=x^r := by rw [← Real.rpow_add hx₀]; congr 1; ring
  have hlocal : ∃ j ∈ Ioc a b, f j ≤ 4*C*x^(r-θ) := by
    by_contra! hn
    have hh := sum_lt_sum_of_nonempty (s := Ioc a b)
      (show (Ioc a b).Nonempty from ⟨b,mem_Ioc.mpr ⟨hab,le_rfl⟩⟩) hn
    simp only [sum_const,nsmul_eq_mul] at hh
    have hlow := mul_le_mul_of_nonneg_right hc (by positivity : 0 ≤ 4*C*x^(r-θ))
    have hbnd : x^θ/2*(4*C*x^(r-θ))=2*C*x^r := by rw [← he]; ring
    linarith only [hh,hlow,hbnd,hsum,ha',hb']
  obtain ⟨j,hj,hjval⟩ := hlocal
  obtain ⟨haj,hjb⟩ := mem_Ioc.mp hj
  have hjlow : (a:ℝ)+1 ≤ j := by exact_mod_cast haj
  have hjx : x ≤ 2*(j:ℝ) := by linarith only [hhalf,hax,hjlow]
  have hjpow := Real.rpow_le_rpow hx₀.le hjx (sub_nonneg.mpr hr)
  rw [Real.mul_rpow two_pos.le (Nat.cast_nonneg _)] at hjpow
  refine ⟨j,⟨(Nat.zero_le a).trans_lt haj,hjval.trans ((mul_le_mul_of_nonneg_left hjpow
    (by positivity : 0 ≤ 4*C)).trans_eq (by dsimp only [A]; ring))⟩,
    (by exact_mod_cast hjb : (j:ℝ) ≤ b).trans hb,?_⟩
  rw [one_mul]
  linarith only [hax,hjlow]

private def price (n : ℕ) := Real.log (ordinaryPrimeGenerator (n • successorSquareTriple n):ℝ)

private theorem log_prefix (N : ℕ) : Real.log (squareGeneratorPrefix N:ℝ)=prefixSum price N := by
  unfold squareGeneratorPrefix prefixSum price
  push_cast
  apply Real.log_prod
  intro n _
  exact ne_of_gt (by exact_mod_cast (show (0:ℚ) < ordinaryPrimeGenerator (n • successorSquareTriple n) from
    prod_pos fun k _ => zpow_pos (Nat.cast_pos.mpr (contactBase_pos k)) _))

private theorem price_bound_at_strip {s : ℝ} (hw : zetaZeroWidth ≤ s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, 0 < n → |price n| ≤ C*(n:ℝ)^(2+2*s) := by
  obtain ⟨D,hD,h⟩ := successorSquare_diagonal_log_at_width
  have hs := zetaZeroWidth_nonneg.trans hw
  refine ⟨D*2^(2*s),by positivity,fun n hn => ?_⟩
  have hx : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hn' : 0 < (n:ℝ) := Nat.cast_pos.mpr hn
  have hs₀ := mul_nonneg two_pos.le hs
  have h₁ := Real.rpow_le_rpow_of_exponent_le (by linarith only [hx] : 1 ≤ (n:ℝ)+1)
    (mul_le_mul_of_nonneg_left hw two_pos.le)
  have h₂ := Real.rpow_le_rpow (by positivity : 0 ≤ (n:ℝ)+1)
    (by linarith only [hx] : (n:ℝ)+1 ≤ 2*n) hs₀
  rw [Real.mul_rpow two_pos.le hn'.le] at h₂
  refine (h n hn).trans ((mul_le_mul_of_nonneg_left (h₁.trans h₂)
    (mul_nonneg hD (sq_nonneg (n:ℝ)))).trans_eq ?_)
  rw [Real.rpow_add hn',Real.rpow_two]
  ring

private theorem width_of_dominating_prefix (f : ℕ → ℝ) (hdom : ∀ n, price n ≤ f n)
    {s C : ℝ} (hs : 0 ≤ s) (hC : 0 ≤ C)
    (h : ∀ N : ℕ, |prefixSum f N| ≤ C*(N:ℝ)^(3+2*s)) : zetaZeroWidth ≤ s := by
  by_contra! hw
  let gap := min (zetaZeroWidth-s) (1/2)
  have hg : 0 < gap := lt_min (sub_pos.mpr hw) (by norm_num)
  have hg₁ : gap ≤ 1/2 := min_le_right _ _
  have hgw : gap ≤ zetaZeroWidth-s := min_le_left _ _
  let θ := 1-gap
  let t := s+gap/2
  have ht : 0 ≤ t := add_nonneg hs (half_pos hg).le
  have htw : t < zetaZeroWidth := by dsimp only [t]; linarith only [hg,hgw]
  have hθ : 0 < θ := by dsimp only [θ]; linarith only [hg₁]
  have hθ' : θ < 1 := by dsimp only [θ]; linarith only [hg]
  have hr : θ ≤ 3+2*s := by linarith only [hθ',hs]
  obtain ⟨A,hA,hE⟩ := power_gaps_of_signed_prefix f hθ hθ' hr hC h
  have he : 3+2*s-θ=2+2*t := by dsimp only [θ,t]; ring
  apply htw.not_ge
  apply zetaZeroWidth_le_of_sparse_square_logs hθ' hE ht (htw.trans_le zetaZeroWidth_le_half) hA
  intro n hn
  rw [← he]
  exact (hdom n).trans hn.2

/-- The signed prefix product detects every strip at exponent three plus
twice its width. -/
theorem zetaZeroWidth_le_iff_square_generator_prefix {s : ℝ} (hs : 0 ≤ s) (hs' : s < 1/2) :
    zetaZeroWidth ≤ s ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      |Real.log (squareGeneratorPrefix N:ℝ)| ≤ C*(N:ℝ)^(3+2*s) := by
  constructor
  · intro hw
    obtain ⟨C,hC,hp⟩ := price_bound_at_strip hw
    refine ⟨C,hC,fun N => ?_⟩
    rw [log_prefix]
    by_cases hN : N=0
    · simp [hN,prefixSum,show (3:ℝ)+2*s≠0 by linarith]
    have hN₀ : 0 < (N:ℝ) := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hN)
    have hrow (n : ℕ) (hn : n ∈ Ioc 0 N) : |price n| ≤ C*(N:ℝ)^(2+2*s) :=
      (hp n (mem_Ioc.mp hn).1).trans (mul_le_mul_of_nonneg_left
        (Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast (mem_Ioc.mp hn).2) (by linarith only [hs])) hC)
    change |∑ n ∈ Ioc 0 N, price n| ≤ _
    refine (abs_sum_le_sum_abs _ _).trans ((sum_le_sum hrow).trans_eq ?_)
    rw [sum_const,nsmul_eq_mul,Nat.card_Ioc,Nat.sub_zero,show (3:ℝ)+2*s=1+(2+2*s) by ring,
      Real.rpow_add hN₀,Real.rpow_one]
    ring
  rintro ⟨C,hC,h⟩
  exact width_of_dominating_prefix price (fun _ => le_rfl) hs hC fun N => (log_prefix N) ▸ h N

private theorem rational_power_window {q : ℚ} (hq : 0 < q) {B : ℕ} (hB : 0 < B) (N : ℕ) :
    |Real.log (q:ℝ)| ≤ Real.log B*(N:ℝ)^3 ↔
      q ≤ (B:ℚ)^(N^3) ∧ q⁻¹ ≤ (B:ℚ)^(N^3) := by
  have upper {a : ℚ} (ha : 0 < a) : Real.log (a:ℝ) ≤ Real.log B*(N:ℝ)^3 ↔ a ≤ (B:ℚ)^(N^3) := by
    have he : Real.log ((B:ℝ)^(N^3))=Real.log B*(N:ℝ)^3 := by
      rw [Real.log_pow,Nat.cast_pow,mul_comm]
    rw [← he,Real.log_le_log_iff (by exact_mod_cast ha) (pow_pos (Nat.cast_pos.mpr hB) _)]
    constructor <;> intro h <;> exact_mod_cast h
  rw [← upper hq,← upper (inv_pos.mpr hq),Rat.cast_inv,Real.log_inv,abs_le]
  constructor <;> rintro ⟨h₁,h₂⟩ <;> constructor <;> linarith only [h₁,h₂]

/-- Positive logarithmic price of the reduced rational generator. -/
def squarePositiveLogPrice (n : ℕ) : ℂ :=
  (max (Real.log (ordinaryPrimeGenerator (n • successorSquareTriple n):ℝ)) 0 : ℝ)

private theorem positive_price_norm (n : ℕ) :
    ‖squarePositiveLogPrice n‖=max (price n) 0 := by
  rw [squarePositiveLogPrice,price,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg (le_max_right _ _)]

private theorem positive_price_prefix {r : ℝ} (hr : 0 ≤ r)
    (h : LSeriesSummable squarePositiveLogPrice (r:ℂ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N, |prefixSum (fun n => max (price n) 0) N| ≤ C*(N:ℝ)^r := by
  let g (n : ℕ) := ‖LSeries.term squarePositiveLogPrice (r:ℂ) n‖
  have hg : Summable g := h.norm
  refine ⟨∑' n, g n,tsum_nonneg (fun _ => norm_nonneg _),fun N => ?_⟩
  rw [prefixSum,abs_of_nonneg (sum_nonneg fun _ _ => le_max_right _ _)]
  have hrow (n : ℕ) (hn : n ∈ Ioc 0 N) : max (price n) 0 ≤ g n*(N:ℝ)^r := by
    obtain ⟨hpos,hle⟩ := mem_Ioc.mp hn
    have hp := Real.rpow_pos_of_pos (Nat.cast_pos.mpr hpos : 0 < (n:ℝ)) r
    have he : g n*(n:ℝ)^r=max (price n) 0 := by
      rw [g,LSeries.norm_term_eq,if_neg hpos.ne',positive_price_norm,Complex.ofReal_re,div_mul_cancel₀ _ hp.ne']
    exact he.ge.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (Nat.cast_nonneg n) (by exact_mod_cast hle) hr) (norm_nonneg _))
  exact (sum_le_sum hrow).trans ((le_of_eq (sum_mul ..).symm).trans
    (mul_le_mul_of_nonneg_right (hg.sum_le_tsum _ (fun _ _ => norm_nonneg _)) (Real.rpow_nonneg (Nat.cast_nonneg N) _)))

/-- Above the cubic threshold, the abscissa of absolute convergence for
the positive log prices measures exactly twice the zeta zero width. -/
theorem zetaZeroWidth_le_iff_positive_price_abscissa {s : ℝ} (hs : 0 ≤ s) :
    zetaZeroWidth ≤ s ↔ LSeries.abscissaOfAbsConv squarePositiveLogPrice ≤ ((3+2*s:ℝ):EReal) := by
  constructor
  · intro hw
    obtain ⟨C,hC,h⟩ := price_bound_at_strip hw
    have he := LSeries.abscissaOfAbsConv_le_of_le_const_mul_rpow (f := squarePositiveLogPrice)
      (x := 2+2*s) ⟨C,fun n hn => by
        rw [positive_price_norm]
        exact max_le ((le_abs_self _).trans (h _ (Nat.pos_of_ne_zero hn)))
          (mul_nonneg hC (Real.rpow_nonneg (Nat.cast_nonneg n) _))⟩
    convert he using 1 <;> norm_cast <;> ring
  intro h
  by_contra! hw
  let t := (s+zetaZeroWidth)/2
  have hst : s < t := by dsimp only [t]; linarith only [hw]
  have htw : t < zetaZeroWidth := by dsimp only [t]; linarith only [hw]
  have ht := hs.trans hst.le
  have hsum : LSeriesSummable squarePositiveLogPrice ((3+2*t:ℝ):ℂ) :=
    LSeriesSummable_of_abscissaOfAbsConv_lt_re (h.trans_lt
      (EReal.coe_lt_coe_iff.mpr (by simpa only [Complex.ofReal_re] using
        (show 3+2*s < 3+2*t by linarith only [hst]))))
  obtain ⟨C,hC,hP⟩ := positive_price_prefix (by linarith only [ht] : 0 ≤ 3+2*t) hsum
  exact htw.not_ge (width_of_dominating_prefix (fun n => max (price n) 0)
    (fun n => le_max_left _ _) ht hC hP)

/-- RH is equivalent to abscissa at most three for the positive log prices. -/
theorem riemannHypothesis_iff_positive_price_abscissa :
    RiemannHypothesis ↔ LSeries.abscissaOfAbsConv squarePositiveLogPrice ≤ 3 := by
  have he := zetaZeroWidth_le_iff_positive_price_abscissa (s := 0) le_rfl
  norm_num at he
  exact ⟨fun h => he.mp (riemannHypothesis_iff_zetaZeroWidth_eq_zero.mp h).le,
    fun h => riemannHypothesis_iff_zetaZeroWidth_eq_zero.mpr (le_antisymm (he.mpr h) zetaZeroWidth_nonneg)⟩

/-- One integer base bounds the cumulative rational product in both
directions exactly when every nontrivial zeta zero lies on the line. -/
theorem riemannHypothesis_iff_signed_square_generator_product :
    RiemannHypothesis ↔ ∃ B : ℕ, 0 < B ∧ ∀ N : ℕ,
      squareGeneratorPrefix N ≤ (B:ℚ)^(N^3) ∧ (squareGeneratorPrefix N)⁻¹ ≤ (B:ℚ)^(N^3) := by
  have he := zetaZeroWidth_le_iff_square_generator_prefix (s := 0) le_rfl (by norm_num)
  have hthree (x : ℝ) : x^(3:ℝ)=x^3 := Real.rpow_natCast x 3
  simp only [mul_zero,add_zero,hthree] at he
  constructor
  · intro hRH
    obtain ⟨C,_,hbound⟩ := he.mp (riemannHypothesis_iff_zetaZeroWidth_eq_zero.mp hRH).le
    let B := ⌈Real.exp C⌉₊
    have hB : 0 < B := Nat.ceil_pos.mpr (Real.exp_pos _)
    have hC := (Real.le_log_iff_exp_le (Nat.cast_pos.mpr hB)).mpr (Nat.le_ceil (Real.exp C))
    exact ⟨B,hB,fun N => (rational_power_window (squareGeneratorPrefix_pos N) hB N).mp
      ((hbound N).trans (mul_le_mul_of_nonneg_right hC (pow_nonneg (Nat.cast_nonneg _) _)))⟩
  · rintro ⟨B,hB,h⟩
    apply riemannHypothesis_iff_zetaZeroWidth_eq_zero.mpr
    exact le_antisymm (he.mpr ⟨Real.log B,Real.log_natCast_nonneg _,fun N =>
      (rational_power_window (squareGeneratorPrefix_pos N) hB N).mpr (h N)⟩) zetaZeroWidth_nonneg

#print axioms zetaZeroWidth_le_iff_square_generator_prefix
#print axioms riemannHypothesis_iff_positive_price_abscissa
#print axioms riemannHypothesis_iff_signed_square_generator_product

end GaloisForLFunctions.CountingHolography.Sections
