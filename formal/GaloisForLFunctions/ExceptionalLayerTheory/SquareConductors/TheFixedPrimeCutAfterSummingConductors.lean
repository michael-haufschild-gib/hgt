import GaloisForLFunctions.CountingHolography.Sections.OneSidedBoundsForTheSquareGeneratorPrefix
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePrimeMassAtAQuadraticProductDivider

/-!
# A fixed prime cutoff after summing square conductors

The integrated prefix profile is exactly linear below the first knot.
Its slope is the Mellin transform of the single-conductor profile at −1.
Consequently an upper cutoff fixed at the terminal conductor transfers
a positive multiple of the first prime moment to the lower side.
-/

noncomputable section
open Finset Filter MeasureTheory Zeta23 GaloisForLFunctions.BiScaleUncertainty.ChebyshevGauge
open GaloisForLFunctions.CountingHolography.Sections GaloisForLFunctions.SquareRootThreshold
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Slope of the integrated prime weight below the first spline knot. -/
def innerPrimeSlope : ℝ := 15/8*(Real.sinh (3/2)/(3/2))^8

theorem innerPrimeSlope_pos : 0 < innerPrimeSlope :=
  mul_pos (by norm_num) (pow_pos (div_pos (Real.sinh_pos_iff.mpr (by norm_num)) (by norm_num)) _)

/-- The exponent −1 selects the first prime moment in the conductor prefix. -/
theorem mellin_squarePrimeWeight_neg_one :
    mellin squarePrimeWeight (-1) = (innerPrimeSlope:ℂ) := by
  have hlog : Real.log 4 = 2*Real.log 2 := by
    rw [show (4:ℝ)=2^2 by norm_num,Real.log_pow]; norm_num
  have hexp : Real.exp ((-(3/2):ℝ)*Real.log 4) = 1/8 := by
    rw [hlog,show (-(3/2):ℝ)*(2*Real.log 2) = -(3*Real.log 2) by ring,
      Real.exp_neg,←show Real.log (2^3:ℝ)=3*Real.log 2 by rw [Real.log_pow]; norm_num,
      Real.exp_log (by norm_num : (0:ℝ)<2^3)]
    norm_num
  rw [mellin_squarePrimeWeight_formula]
  norm_num only [show (-1:ℂ)-1/2=-(3/2) by norm_num]
  let a := (3/2:ℂ)
  have hm := GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.paperFT_cubicSpline_div_I
    (z := -a) (by dsimp only [a]; norm_num)
  have hp := GaloisForLFunctions.ArithmeticCouplingTheory.ConeMoments.paperFT_cubicSpline_div_I
    (z := a) (by dsimp only [a]; norm_num)
  have he : Complex.exp (-a*(Real.log 4:ℝ))=((1/8:ℝ):ℂ) := by
    rw [←hexp,Complex.ofReal_exp]; congr 1; dsimp only [a]; push_cast; ring
  change (2-Complex.exp (-a*(Real.log 4:ℝ)))*
    (paperFT (fun x => (cubicSpline x:ℂ)) (-a/Complex.I) *
     paperFT (fun x => (cubicSpline x:ℂ)) (-(-a/Complex.I))) = _
  rw [he,hm,neg_div,neg_neg,hp,Complex.sinh_neg,neg_div_neg_eq]
  simp only [a,innerPrimeSlope,Complex.ofReal_mul,Complex.ofReal_div,Complex.ofReal_ofNat,
    Complex.ofReal_one,Complex.ofReal_pow,Complex.ofReal_sinh]
  ring

/-- On the entire inner interval the integrated weight is a positive linear
function, although each individual conductor has a zero weight there. -/
theorem squarePrefixPrimeWeight_before_first_knot {v : ℝ} (hv : 0 < v)
    (hcut : v ≤ Real.exp (-8)) :
    squarePrefixPrimeWeight v = (v:ℂ)*innerPrimeSlope := by
  let g (t : ℝ) := squarePrimeWeight t/(t:ℂ)^2
  have hm : mellin squarePrimeWeight (-1) = ∫ t in Set.Ioi (0:ℝ), g t := by
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t _
    simp only [g,show (-1:ℂ)-1=-(2:ℂ) by norm_num,Complex.cpow_neg,Complex.cpow_two,smul_eq_mul,
      div_eq_mul_inv,mul_comm]
  have he : (∫ t in Set.Ici v, g t) = ∫ t in Set.Ioi (0:ℝ), g t := by
    have hsub : Set.Ici v ⊆ Set.Ioi (0:ℝ) := fun _ ht => hv.trans_le ht
    rw [←Measure.restrict_restrict_of_subset hsub (μ := volume),←integral_indicator measurableSet_Ici]
    apply setIntegral_congr_fun measurableSet_Ioi
    intro t ht
    by_cases hk : v ≤ t
    · exact Set.indicator_of_mem hk _
    · have hzero := squarePrimeWeight_zero_outside ht (fun h => (lt_of_not_ge hk).not_ge (hcut.trans h.1))
      rw [Set.indicator_of_notMem (show t ∉ Set.Ici v from hk)]
      simp only [g,hzero,zero_div]
  rw [squarePrefixPrimeWeight_tail hv,←mellin_squarePrimeWeight_neg_one,hm]
  exact congrArg (fun z : ℂ => (v:ℂ)*z) he

/-- For any terminal N, every retained prime up to a fixed cutoff K below
the first knot has exactly the same multiplier of p log p. -/
theorem fixed_inner_prime_price {N K : ℕ} (hN : 0 < N)
    (hK : (K:ℝ) ≤ Real.exp (-8)*(N:ℝ)^2) :
    (N:ℂ)^2*(∑ p ∈ ordinaryPrimeLags K, (Real.log p:ℂ)*squarePrefixPrimeWeight ((p:ℝ)/(N:ℝ)^2)) =
      (innerPrimeSlope:ℂ)*∑ p ∈ ordinaryPrimeLags K, (p:ℂ)*Real.log p := by
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  rw [mul_sum,mul_sum]
  apply sum_congr rfl
  intro p hp
  have h := mem_filter.mp hp
  have hk := (Nat.cast_le.mpr (mem_Icc.mp h.1).2 : (p:ℝ) ≤ K).trans hK
  rw [squarePrefixPrimeWeight_before_first_knot (div_pos (Nat.cast_pos.mpr h.2.pos) (sq_pos_of_pos hn))
    ((div_le_iff₀ (sq_pos_of_pos hn)).mpr hk)]
  have hv : ((((p:ℝ)/(N:ℝ)^2:ℝ)):ℂ)*(N:ℂ)^2 = p := by
    rw [Complex.ofReal_div,Complex.ofReal_pow,Complex.ofReal_natCast,Complex.ofReal_natCast]
    exact div_mul_cancel₀ _ (pow_ne_zero 2 (Nat.cast_ne_zero.mpr hN.ne'))
  linear_combination (Real.log p*innerPrimeSlope:ℂ)*hv

/-- The rational price with the first prime moment restored at the same
terminal conductor. The uniform cubic error is charged once for both sides. -/
theorem fixed_prime_cut_price_comparison :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N K : ℕ}, 0 < N → (K:ℝ) ≤ Real.exp (-8)*(N:ℝ)^2 →
      let H := ⌊((N:ℝ)/squareConductorBVWindow.lower)^2⌋₊
      ‖(Real.log (squareGeneratorPrefix N:ℝ):ℂ) -
        ((innerPrimeSlope:ℂ)*(∑ p ∈ ordinaryPrimeLags K, (p:ℂ)*Real.log p) +
          (N:ℂ)^2*∑ p ∈ (ordinaryPrimeLags H).filter (K < ·),
            (Real.log p:ℂ)*squarePrefixPrimeWeight ((p:ℝ)/(N:ℝ)^2))‖ ≤ C*(N:ℝ)^3 := by
  obtain ⟨C,hC,hprice⟩ := squareGeneratorPrefix_prime_profile
  refine ⟨C,hC,fun {N K} hN hK => ?_⟩
  let H := ⌊((N:ℝ)/squareConductorBVWindow.lower)^2⌋₊
  let f (p : ℕ) := (Real.log p:ℂ)*squarePrefixPrimeWeight ((p:ℝ)/(N:ℝ)^2)
  have he : Real.exp (-8) ≤ 1 := Real.exp_le_one_iff.mpr (by norm_num)
  have hKH : K ≤ H := by
    apply Nat.le_floor
    apply hK.trans
    have hlo : squareConductorBVWindow.lower ≤ 1 := he
    have hsmall := mul_le_of_le_one_left (sq_nonneg (N:ℝ)) he
    exact hsmall.trans (pow_le_pow_left₀ (Nat.cast_nonneg N)
      (le_div_self (Nat.cast_nonneg N) squareConductorBVWindow.lower_pos hlo) 2)
  have hpr : (Ioc 0 H).filter Nat.Prime = ordinaryPrimeLags H := by
    ext p
    simp only [ordinaryPrimeLags,mem_filter,mem_Ioc,mem_Icc]
    exact ⟨fun h => ⟨⟨h.2.two_le,h.1.2⟩,h.2⟩,fun h => ⟨⟨h.2.pos,h.1.2⟩,h.2⟩⟩
  have hlow : (ordinaryPrimeLags H).filter (· ≤ K) = ordinaryPrimeLags K := by
    ext p
    simp only [ordinaryPrimeLags,mem_filter,mem_Icc]
    exact ⟨fun h => ⟨⟨h.1.1.1,h.2⟩,h.1.2⟩,
      fun h => ⟨⟨⟨h.1.1,h.1.2.trans hKH⟩,h.2⟩,h.1.2⟩⟩
  have hsplit := sum_filter_add_sum_filter_not (ordinaryPrimeLags H) (· ≤ K) f
  simp only [hlow,not_le] at hsplit
  have hp := hprice hN
  change ‖(Real.log (squareGeneratorPrefix N:ℝ):ℂ) -
    (N:ℂ)^2*∑ p ∈ (Ioc 0 H).filter Nat.Prime, f p‖ ≤ _ at hp
  rw [hpr,←hsplit,mul_add] at hp
  simpa only [f,fixed_inner_prime_price hN hK] using hp

/-- Integrated primes above a fixed terminal cutoff, after restoring the
quadratic main term of the missing first prime moment. -/
def centeredFixedPrimeTail (N K : ℕ) : ℂ :=
  let H := ⌊((N:ℝ)/squareConductorBVWindow.lower)^2⌋₊
  (N:ℂ)^2*(∑ p ∈ (ordinaryPrimeLags H).filter (K < ·),
    (Real.log p:ℂ)*squarePrefixPrimeWeight ((p:ℝ)/(N:ℝ)^2)) +
    ((innerPrimeSlope*((K:ℝ)*(K+1)/2):ℝ):ℂ)

private theorem centered_cut_of_moment {d : ℝ}
    (hmoment : ∃ C : ℝ, 0 ≤ C ∧ ∀ K : ℕ, 0 < K →
      |(∑ p ∈ ordinaryPrimeLags K, (p:ℝ)*Real.log p)-(K:ℝ)*((K:ℝ)+1)/2| ≤ C*(K:ℝ)^d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N K : ℕ}, 0 < N → 0 < K → (K:ℝ) ≤ Real.exp (-8)*(N:ℝ)^2 →
      ‖(Real.log (squareGeneratorPrefix N:ℝ):ℂ)-centeredFixedPrimeTail N K‖ ≤
        C*((N:ℝ)^3+(K:ℝ)^d) := by
  obtain ⟨A,hA,ha⟩ := fixed_prime_cut_price_comparison
  obtain ⟨B,hB,hb⟩ := hmoment
  let E := innerPrimeSlope*B
  have hE : 0 ≤ E := mul_nonneg innerPrimeSlope_pos.le hB
  refine ⟨A+E,add_nonneg hA hE,fun {N K} hN hK hcut => ?_⟩
  let H := ⌊((N:ℝ)/squareConductorBVWindow.lower)^2⌋₊
  let X := (N:ℂ)^2*∑ p ∈ (ordinaryPrimeLags H).filter (K < ·),
      (Real.log p:ℂ)*squarePrefixPrimeWeight ((p:ℝ)/(N:ℝ)^2)
  let P := (Real.log (squareGeneratorPrefix N:ℝ):ℂ)
  let M := ∑ p ∈ ordinaryPrimeLags K, (p:ℝ)*Real.log p
  let T := (K:ℝ)*(K+1)/2
  let V := (K:ℝ)^d
  have hv : 0 ≤ V := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hsub : ‖P-((innerPrimeSlope:ℂ)*(M:ℂ)+X)‖ ≤ A*(N:ℝ)^3 := by
    simpa only [P,M,X,H,Complex.ofReal_sum,Complex.ofReal_mul,Complex.ofReal_natCast] using ha hN hcut
  have hprime : ‖((innerPrimeSlope*(M-T):ℝ):ℂ)‖ ≤ E*V := by
    rw [Complex.norm_real,Real.norm_eq_abs,abs_mul,abs_of_pos innerPrimeSlope_pos]
    exact (mul_le_mul_of_nonneg_left (hb K hK) innerPrimeSlope_pos.le).trans_eq (mul_assoc ..).symm
  have he : P-(X+((innerPrimeSlope*T:ℝ):ℂ)) =
      (P-((innerPrimeSlope:ℂ)*(M:ℂ)+X))+((innerPrimeSlope*(M-T):ℝ):ℂ) := by
    push_cast; ring
  change ‖P-(X+((innerPrimeSlope*T:ℝ):ℂ))‖ ≤ _
  rw [he]
  apply (norm_add_le _ _).trans
  apply (add_le_add hsub hprime).trans
  change _ ≤ (A+E)*((N:ℝ)^3+V)
  linarith only [mul_nonneg hE (pow_nonneg (Nat.cast_nonneg (α := ℝ) N) 3),mul_nonneg hA hv]

/-- The two errors in elementary centering are cubic rounding at the
terminal conductor and prime counting at the smaller fixed cutoff. -/
theorem fixed_prime_cut_centered_comparison :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N K : ℕ}, 0 < N → 0 < K → (K:ℝ) ≤ Real.exp (-8)*(N:ℝ)^2 →
      ‖(Real.log (squareGeneratorPrefix N:ℝ):ℂ)-centeredFixedPrimeTail N K‖ ≤
        C*((N:ℝ)^3+(K:ℝ)^(17/9:ℝ)) :=
  centered_cut_of_moment first_prime_moment_at_cut

private theorem terminal_cut_comparison {d e : ℝ} (hd : 0 ≤ d) (he : 3 ≤ e)
    (hde : (17/9)*d ≤ e)
    (hcomp : ∃ C : ℝ, 0 ≤ C ∧ ∀ {N K : ℕ}, 0 < N → 0 < K → (K:ℝ) ≤ Real.exp (-8)*(N:ℝ)^2 →
      ‖(Real.log (squareGeneratorPrefix N:ℝ):ℂ)-centeredFixedPrimeTail N K‖ ≤ C*((N:ℝ)^3+(K:ℝ)^d)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < N →
      ‖(Real.log (squareGeneratorPrefix N:ℝ):ℂ) -
        centeredFixedPrimeTail N ⌊(N:ℝ)^(17/9:ℝ)⌋₊‖ ≤ C*(N:ℝ)^e := by
  have hg : ∀ᶠ n : ℕ in atTop, Real.exp 8 ≤ (n:ℝ)^(1/9:ℝ) :=
    ((tendsto_rpow_atTop (by norm_num : (0:ℝ)<1/9)).comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  obtain ⟨n₀,h₀⟩ := Filter.eventually_atTop.mp hg
  obtain ⟨A,hA,ha⟩ := hcomp
  let price (n : ℕ) := ‖(Real.log (squareGeneratorPrefix n:ℝ):ℂ) -
    centeredFixedPrimeTail n ⌊(n:ℝ)^(17/9:ℝ)⌋₊‖
  let D := ∑ n ∈ range n₀, price n
  have hD : 0 ≤ D := sum_nonneg fun _ _ => norm_nonneg _
  refine ⟨2*A+D,by positivity,fun N hN => ?_⟩
  have hn : (0:ℝ) < N := Nat.cast_pos.mpr hN
  have h₁ : (1:ℝ) ≤ N := by exact_mod_cast hN
  let Y := (N:ℝ)^e
  have hY : 1 ≤ Y := Real.one_le_rpow h₁ (by linarith only [he])
  change price N ≤ (2*A+D)*Y
  by_cases hlate : n₀ ≤ N
  · let K := ⌊(N:ℝ)^(17/9:ℝ)⌋₊
    have hK : 0 < K := Nat.le_floor (show ((1:ℕ):ℝ) ≤ (N:ℝ)^(17/9:ℝ) by
      push_cast; exact Real.one_le_rpow h₁ (by norm_num))
    have hf : (K:ℝ) ≤ (N:ℝ)^(17/9:ℝ) := Nat.floor_le (Real.rpow_nonneg hn.le _)
    have hcut : (K:ℝ) ≤ Real.exp (-8)*(N:ℝ)^2 := by
      apply hf.trans
      rw [Real.exp_neg,inv_mul_eq_div,le_div_iff₀ (Real.exp_pos 8)]
      have hh := mul_le_mul_of_nonneg_left (h₀ N hlate) (Real.rpow_nonneg hn.le (17/9:ℝ))
      rwa [←Real.rpow_add hn,show (17/9:ℝ)+1/9=2 by norm_num,Real.rpow_two] at hh
    have hq : (K:ℝ)^d ≤ Y := by
      apply (Real.rpow_le_rpow (Nat.cast_nonneg _) hf hd).trans
      rw [←Real.rpow_mul hn.le]
      exact Real.rpow_le_rpow_of_exponent_le h₁ hde
    have hcube : (N:ℝ)^3 ≤ Y := (Real.rpow_natCast (N:ℝ) 3).symm.le.trans
      (Real.rpow_le_rpow_of_exponent_le h₁ he)
    apply (ha hN hK hcut).trans
    apply (mul_le_mul_of_nonneg_left (add_le_add hcube hq) hA).trans
    linarith only [mul_nonneg hD (zero_le_one.trans hY)]
  · have he : price N ≤ D := single_le_sum (f := price) (fun n _ => norm_nonneg _) (mem_range.mpr (lt_of_not_ge hlate))
    apply he.trans ((le_mul_of_one_le_right hD hY).trans ?_)
    exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_left (by positivity)) (zero_le_one.trans hY)

/-- At the fixed terminal seventeen-ninths cut, elementary centering recovers
the rational price within exponent 289/81 at every endpoint. -/
theorem seventeenNinths_fixed_prime_cut_comparison :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < N →
      ‖(Real.log (squareGeneratorPrefix N:ℝ):ℂ) -
        centeredFixedPrimeTail N ⌊(N:ℝ)^(17/9:ℝ)⌋₊‖ ≤ C*(N:ℝ)^(289/81:ℝ) :=
  terminal_cut_comparison (by norm_num) (by norm_num) (by norm_num) fixed_prime_cut_centered_comparison

/-- Beyond cubic size the elementary first-moment centering error has a strict
power gap below the price exponent at the actual zero width. -/
theorem centered_fixed_cut_gap_at_width :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < N →
      ‖(Real.log (squareGeneratorPrefix N:ℝ):ℂ) -
        centeredFixedPrimeTail N ⌊(N:ℝ)^(17/9:ℝ)⌋₊‖ ≤
        C*(N:ℝ)^(3+2*max 0 (zetaZeroWidth-1/40)) := by
  apply terminal_cut_comparison (d := 1+(1/2+zetaZeroWidth+1/36))
  · linarith only [zetaZeroWidth_nonneg]
  · linarith only [le_max_left (0:ℝ) (zetaZeroWidth-1/40)]
  · linarith only [zetaZeroWidth_nonneg,le_max_right (0:ℝ) (zetaZeroWidth-1/40)]
  · exact centered_cut_of_moment first_prime_moment_at_width

/-- The one-sided growth of the high-prime sum with a known quadratic
counterterm detects every zero width. Its prime-counting error cannot
account for a positive width because the product cutoff is subquadratic. -/
theorem width_iff_centered_fixed_prime_tail {a : ℝ} (ha : 0 ≤ a) (ha' : a < 1/2) :
    zetaZeroWidth ≤ a ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < N →
      (centeredFixedPrimeTail N ⌊(N:ℝ)^(17/9:ℝ)⌋₊).re ≤ C*(N:ℝ)^(3+2*a) := by
  obtain ⟨A,hA,herr⟩ := centered_fixed_cut_gap_at_width
  let u := max 0 (zetaZeroWidth-1/40)
  let P (n : ℕ) := Real.log (squareGeneratorPrefix n:ℝ)
  let X (n : ℕ) := centeredFixedPrimeTail n ⌊(n:ℝ)^(17/9:ℝ)⌋₊
  have hdiff {b : ℝ} (hb : u ≤ b) (N : ℕ) (hN : 0 < N) :
      |P N-(X N).re| ≤ A*(N:ℝ)^(3+2*b) := by
    have hr := (Complex.abs_re_le_norm ((P N:ℂ)-X N)).trans (herr N hN)
    simp only [Complex.sub_re,Complex.ofReal_re] at hr
    have he : 3+2*u ≤ 3+2*b := by linarith only [hb]
    exact hr.trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN : (1:ℝ) ≤ N) he) hA)
  have oneSide {b : ℝ} (hb : 0 ≤ b) (hb' : b < 1/2) : zetaZeroWidth ≤ b ↔
      ∃ D : ℝ, 0 ≤ D ∧ ∀ N : ℕ, P N ≤ D*(N:ℝ)^(3+2*b) := by
    simpa only [P,one_mul] using
      zetaZeroWidth_le_iff_one_sided_square_prefix hb hb' (e := 1) (by norm_num)
  constructor
  · intro hw
    obtain ⟨B,hB,h⟩ := (oneSide ha ha').mp hw
    have hu : u ≤ a := max_le ha (by linarith only [hw])
    refine ⟨A+B,add_nonneg hA hB,fun N hN => ?_⟩
    have hl := (abs_le.mp (hdiff hu N hN)).1
    change (X N).re ≤ _
    linarith only [hl,h N]
  · rintro ⟨B,hB,h⟩
    by_contra! hw
    let b := max a u
    have hba : a ≤ b := le_max_left _ _
    have hbu : u ≤ b := le_max_right _ _
    have hbw : b < zetaZeroWidth := max_lt hw (max_lt (ha.trans_lt hw) (sub_lt_self _ (by norm_num)))
    apply hbw.not_ge
    apply (oneSide (ha.trans hba) (hbw.trans_le zetaZeroWidth_le_half)).mpr
    refine ⟨A+B,add_nonneg hA hB,fun N => ?_⟩
    rcases Nat.eq_zero_or_pos N with rfl | hN
    · simp [P,squareGeneratorPrefix,Real.zero_rpow (by linarith only [ha,hba] : 3+2*b≠0)]
    have hu := (abs_le.mp (hdiff hbu N hN)).2
    have hx : (X N).re ≤ B*(N:ℝ)^(3+2*b) := (h N hN).trans (mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN : (1:ℝ) ≤ N) (by linarith only [hba])) hB)
    linarith only [hu,hx]

theorem five_sixths_iff_centered_fixed_prime_tail :
    zetaZeroWidth ≤ 1/3 ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < N →
      (centeredFixedPrimeTail N ⌊(N:ℝ)^(17/9:ℝ)⌋₊).re ≤ C*(N:ℝ)^(11/3:ℝ) := by
  simpa only [show (3:ℝ)+2*(1/3)=11/3 by norm_num] using
    width_iff_centered_fixed_prime_tail (a := 1/3) (by norm_num) (by norm_num)

/-- A cubic upper bound on the deterministically centered ordinary-prime tail
is necessary and sufficient for RH. -/
theorem riemannHypothesis_iff_centered_fixed_prime_tail :
    RiemannHypothesis ↔ ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 0 < N →
      (centeredFixedPrimeTail N ⌊(N:ℝ)^(17/9:ℝ)⌋₊).re ≤ C*(N:ℝ)^3 := by
  have hz : zetaZeroWidth=0 ↔ zetaZeroWidth ≤ 0 :=
    ⟨fun h => h.le,fun h => le_antisymm h zetaZeroWidth_nonneg⟩
  rw [riemannHypothesis_iff_zetaZeroWidth_eq_zero,hz]
  simpa only [mul_zero,add_zero,show ∀ x : ℝ, x^(3:ℝ)=x^3 from fun x => Real.rpow_natCast x 3] using
    width_iff_centered_fixed_prime_tail (a := 0) le_rfl (by norm_num)

/-- The large-prime reading has the opposite first-moment term. Its
remainder is bounded by the full signed price and the fixed-cut errors. -/
theorem fixed_prime_cut_upper_price :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {N K : ℕ}, 0 < N → 0 < K → (K:ℝ) ≤ Real.exp (-8)*(N:ℝ)^2 →
      ‖centeredFixedPrimeTail N K‖ ≤ C*((N:ℝ)^(15/4:ℝ)+(K:ℝ)^(17/9:ℝ)) := by
  have hw : GaloisForLFunctions.SquareRootThreshold.zetaZeroWidth ≤ 3/8 := by
    apply (GaloisForLFunctions.SquareRootThreshold.zetaZeroWidth_le_iff_re_le (by norm_num)).mpr
    intro z hz
    by_contra! h
    exact GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_sub_seven_eighths_lt_re
      (by linarith only [h]) hz.1
  obtain ⟨D,hD,hd⟩ := (zetaZeroWidth_le_iff_square_generator_prefix (by norm_num) (by norm_num)).mp hw
  obtain ⟨A,hA,ha⟩ := fixed_prime_cut_centered_comparison
  refine ⟨D+A,add_nonneg hD hA,fun {N K} hN hK hcut => ?_⟩
  let P := (Real.log (squareGeneratorPrefix N:ℝ):ℂ)
  let U := (N:ℝ)^(15/4:ℝ)
  let V := (K:ℝ)^(17/9:ℝ)
  have hv : 0 ≤ V := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hp : ‖P‖ ≤ D*U := by
    simpa only [P,U,Complex.norm_real,Real.norm_eq_abs,show (3:ℝ)+2*(3/8)=15/4 by norm_num] using hd N
  have hn : (N:ℝ)^3 ≤ U := (Real.rpow_natCast (N:ℝ) 3).symm.le.trans
    (Real.rpow_le_rpow_of_exponent_le (by exact_mod_cast hN : (1:ℝ) ≤ N) (by norm_num))
  have hsub : ‖P-centeredFixedPrimeTail N K‖ ≤ A*(U+V) := (ha hN hK hcut).trans
    (mul_le_mul_of_nonneg_left (add_le_add hn (le_refl V)) hA)
  calc ‖centeredFixedPrimeTail N K‖ = ‖P-(P-centeredFixedPrimeTail N K)‖ := by rw [sub_sub_cancel]
       _ ≤ _ := (norm_sub_le _ _).trans ((add_le_add hp hsub).trans (by
         change _ ≤ (D+A)*(U+V)
         linarith only [mul_nonneg hD hv]))

#print axioms mellin_squarePrimeWeight_neg_one
#print axioms squarePrefixPrimeWeight_before_first_knot
#print axioms fixed_inner_prime_price
#print axioms fixed_prime_cut_price_comparison
#print axioms fixed_prime_cut_centered_comparison
#print axioms seventeenNinths_fixed_prime_cut_comparison
#print axioms centered_fixed_cut_gap_at_width
#print axioms width_iff_centered_fixed_prime_tail
#print axioms five_sixths_iff_centered_fixed_prime_tail
#print axioms riemannHypothesis_iff_centered_fixed_prime_tail
#print axioms fixed_prime_cut_upper_price
end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
