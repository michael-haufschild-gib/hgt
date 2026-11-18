import GaloisForLFunctions.CountingHolography.Sections.ThePrimeProfileOfThreeSquareConductors
import GaloisForLFunctions.CountingHolography.Sections.OneMultiplicityPerSquareConductor

/-!
# One fixed dyadic prime weight on all square conductors

Moving the upper conductor from (2n+1)² to 4n² costs bounded ordinary
prime contact. Its logarithmic displacement is at most 1/n and the
weighted prime window has square-root mass O(n).
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology ArithmeticFunction ArithmeticWeightTheory ArithmeticCastelnuovoSeveri
open BiScaleUncertainty.ChebyshevGauge _root_.RHTower.WeilDeletion SquareRootThreshold

/-- Limiting long-lag weight in the logarithm of the ordinary prime degree. -/
def squareLogProfile (t : ℝ) := 2*splineAutoCorr t-splineAutoCorr (t-Real.log 4)

/-- Multiplicative-coordinate weight at square-root normalization. -/
def squarePrimeWeight (v : ℝ) : ℂ := (Real.exp (-Real.log v/2)*squareLogProfile (Real.log v):ℝ)

/-- Signed reading of the same prime weight at every square conductor. -/
def dyadicPrimeContact (n : ℕ) :=
  ∑ k ∈ ordinaryPrimeLags (3*windowEnd ((2*n+1)^2+1)),
    (2/Real.sqrt k)*squareLogProfile (Real.log k-Real.log ((n:ℝ)^2))*vonMangoldt k

private theorem corr_even (x : ℝ) : splineAutoCorr (-x) = splineAutoCorr x := by
  simp only [splineAutoCorr_eq_eight_boxes,upow_neg]

private theorem corr_regular : ∃ K H : ℝ, 0 ≤ K ∧ 0 ≤ H ∧
    (∀ x, |splineAutoCorr x| ≤ H) ∧ ∀ x y, |splineAutoCorr x-splineAutoCorr y| ≤ K*|x-y| := by
  have hs := hasCompactSupport_upow 1 7
  have hc : ContDiff ℝ 6 (upow 1 7) := contDiff_upow one_pos 6
  obtain ⟨K,hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hc (by norm_num)
  obtain ⟨H,hH⟩ := hs.exists_bound_of_continuous hc.continuous
  refine ⟨K,H,K.coe_nonneg,((norm_nonneg _).trans (hH 0)),?_,?_⟩
  · intro x
    simpa only [splineAutoCorr_eq_eight_boxes,Real.norm_eq_abs] using hH x
  · intro x y
    simpa only [splineAutoCorr_eq_eight_boxes,Real.dist_eq] using hK.dist_le_mul x y

private theorem integrated_row_bound {H : ℝ} (hH : ∀ x, |splineAutoCorr x| ≤ H)
    {N : ℕ} (a : Fin N → ℤ) (k : ℕ) :
    |integratedContact a k| ≤ (2/Real.sqrt k)*(∑ i, |(a i:ℝ)|)^2*H := by
  let M := ∑ i, |(a i:ℝ)|
  let F := fun i j : Fin N => splineAutoCorr (-Real.log k-Real.log ((i:ℝ)+1)+Real.log ((j:ℝ)+1))
  have hrow (i : Fin N) : |∑ j, (a i:ℝ)*(a j:ℝ)*F i j| ≤ |(a i:ℝ)| * (M*H) := by
    refine (abs_sum_le_sum_abs _ _).trans ?_
    unfold M
    rw [sum_mul,mul_sum]
    refine sum_le_sum fun j _ => ?_
    rw [abs_mul,abs_mul,← mul_assoc]
    exact mul_le_mul_of_nonneg_left (hH _) (mul_nonneg (abs_nonneg _) (abs_nonneg _))
  have houter := (abs_sum_le_sum_abs (fun i => ∑ j, (a i:ℝ)*(a j:ℝ)*F i j) univ).trans
    (sum_le_sum (s := univ) fun i _ => hrow i)
  rw [← sum_mul] at houter
  rw [integratedContact_eq_autocorrelations,abs_mul,abs_of_nonneg (by positivity : 0 ≤ 2/Real.sqrt k)]
  exact (mul_le_mul_of_nonneg_left houter (by positivity)).trans_eq (by unfold M; ring)

private theorem fixed_profile (n k : ℕ) :
    squareLogProfile (Real.log k-Real.log ((n:ℝ)^2)) =
      2*splineAutoCorr (Real.log ((n:ℝ)^2)-Real.log k)-
        splineAutoCorr (Real.log ((n:ℝ)^2)+Real.log 4-Real.log k) := by
  unfold squareLogProfile
  conv_lhs => rw [show Real.log k-Real.log ((n:ℝ)^2) = -(Real.log ((n:ℝ)^2)-Real.log k) by ring]
  rw [corr_even,show -(Real.log ((n:ℝ)^2)-Real.log k)-Real.log 4 =
    -(Real.log ((n:ℝ)^2)+Real.log 4-Real.log k) by ring,corr_even]

private theorem log_shift {n : ℕ} (hn : 0 < n) :
    |Real.log (((2*n+1:ℕ):ℝ)^2)-(Real.log ((n:ℝ)^2)+Real.log 4)| ≤ 1/n := by
  have h : (0:ℝ)<n := Nat.cast_pos.mpr hn
  have h₂ : 0 < 2*(n:ℝ) := mul_pos two_pos h
  let r := (2*(n:ℝ)+1)/(2*n)
  have hr : 1 ≤ r := (one_le_div h₂).mpr (le_add_of_nonneg_right zero_le_one)
  have he : Real.log (((2*n+1:ℕ):ℝ)^2)-(Real.log ((n:ℝ)^2)+Real.log 4) = 2*Real.log r := by
    dsimp only [r]
    rw [Real.log_div (by positivity) h₂.ne',Real.log_mul two_ne_zero h.ne',
      show (4:ℝ)=2^2 by norm_num]
    simp only [Real.log_pow]
    push_cast
    ring
  have hid : 2*(r-1)=1/(n:ℝ) := by dsimp only [r]; field_simp; ring
  rw [he,abs_of_nonneg (mul_nonneg two_pos.le (Real.log_nonneg hr))]
  exact (mul_le_mul_of_nonneg_left (Real.log_le_sub_one_of_pos (zero_lt_one.trans_le hr)) two_pos.le).trans_eq hid

/-- Replacing the two moving long-lag rows by a fixed dyadic weight costs
one absolute constant, including the bounded prime degrees. -/
theorem dyadicPrimeContact_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {n : ℕ}, 0 < n →
      |ordinaryPrimeContact (successorSquareTriple n)-dyadicPrimeContact n| ≤ C := by
  obtain ⟨K,H,hK,hH,hbound,hreg⟩ := corr_regular
  obtain ⟨A,hA,hwindow⟩ := successorSquare_window_bound
  let Q := ⌈Real.exp (8+Real.log 9)⌉₊
  have hA' := zero_le_one.trans hA
  refine ⟨38*H*(7*Q)+68*K*A,by positivity,fun {n} hn => ?_⟩
  let L := 3*windowEnd ((2*n+1)^2+1)
  let S := ordinaryPrimeLags L
  let d := successorSquareTriple n
  let F := fun k : ℕ => (2/Real.sqrt k)*squareLogProfile (Real.log k-Real.log ((n:ℝ)^2))
  let tail := 2*K/(n:ℝ)
  have hn' : (0:ℝ) < n := Nat.cast_pos.mpr hn
  have htail : 0 ≤ tail := div_nonneg (mul_nonneg two_pos.le hK) hn'.le
  have hmass : (∑ i, |(d i:ℝ)|)^2 ≤ (4:ℝ)^2 :=
    pow_le_pow_left₀ (sum_nonneg fun _ _ => abs_nonneg _) (successorSquareTriple_mass n) 2
  have hrow {k : ℕ} (hk : k ∈ S) :
      |integratedContact d k-F k| ≤ (if k ≤ Q then 38*H else 0)+tail/Real.sqrt k := by
    have hp := (mem_filter.mp hk).2
    have hroot : 1 ≤ Real.sqrt k := (Real.sqrt_one ▸ Real.sqrt_le_sqrt (by exact_mod_cast hp.pos : (1:ℝ) ≤ k))
    have hf : 2/Real.sqrt k ≤ 2 := (div_le_iff₀ (zero_lt_one.trans_le hroot)).mpr
      (le_mul_of_one_le_right two_pos.le hroot)
    have hf₀ : 0 ≤ 2/Real.sqrt k := by positivity
    by_cases hcut : k ≤ Q
    · rw [if_pos hcut]
      have hv := integrated_row_bound hbound d k
      have he := mul_le_mul_of_nonneg_right
        (mul_le_mul hf hmass (sq_nonneg _) two_pos.le) hH
      have hs := abs_sub (2*splineAutoCorr (Real.log k-Real.log ((n:ℝ)^2)))
        (splineAutoCorr (Real.log k-Real.log ((n:ℝ)^2)-Real.log 4))
      rw [abs_mul,abs_two] at hs
      have hs' : |squareLogProfile (Real.log k-Real.log ((n:ℝ)^2))| ≤ 3*H := by
        dsimp only [squareLogProfile]
        linarith only [hs,hbound (Real.log k-Real.log ((n:ℝ)^2)),
          hbound (Real.log k-Real.log ((n:ℝ)^2)-Real.log 4)]
      have hF : |F k| ≤ 6*H := by
        dsimp only [F]
        rw [abs_mul,abs_of_nonneg hf₀]
        exact (mul_le_mul hf hs' (abs_nonneg _) two_pos.le).trans_eq (by ring)
      linarith only [abs_sub (integratedContact d k) (F k),hv,he,hF,div_nonneg htail (Real.sqrt_nonneg (k:ℝ))]
    rw [if_neg hcut,zero_add]
    have hgt : Real.exp (8+Real.log 9) < (k:ℝ) :=
      (Nat.le_ceil _).trans_lt (by exact_mod_cast lt_of_not_ge hcut : (Q:ℝ)<k)
    have hlarge := Real.log_lt_log (Real.exp_pos _) hgt
    rw [Real.log_exp] at hlarge
    dsimp only [F]
    rw [fixed_profile,show d = successorSquareTriple n from rfl,successorSquare_long_contact hn hlarge,← mul_sub]
    let s := Real.log ((n:ℝ)^2)
    let b := Real.log (((2*n+1:ℕ):ℝ)^2)
    let l := Real.log k
    change |(2/Real.sqrt k)*((2*splineAutoCorr (s-l)-splineAutoCorr (b-l))-
      (2*splineAutoCorr (s-l)-splineAutoCorr (s+Real.log 4-l)))| ≤ _
    rw [show (2*splineAutoCorr (s-l)-splineAutoCorr (b-l))-(2*splineAutoCorr (s-l)-splineAutoCorr (s+Real.log 4-l)) =
      splineAutoCorr (s+Real.log 4-l)-splineAutoCorr (b-l) by ring,abs_mul,abs_of_nonneg hf₀,abs_sub_comm]
    have hg := hreg (b-l) (s+Real.log 4-l)
    rw [show b-l-(s+Real.log 4-l)=b-(s+Real.log 4) by ring] at hg
    exact (mul_le_mul_of_nonneg_left (hg.trans (mul_le_mul_of_nonneg_left (log_shift hn) hK)) hf₀).trans_eq
      (by dsimp only [tail]; ring)
  have hsub : S.filter (fun k => k ≤ Q) ⊆ ordinaryPrimeLags Q := by
    intro k hk
    obtain ⟨hk,hkQ⟩ := mem_filter.mp hk
    exact mem_filter.mpr ⟨mem_Icc.mpr ⟨(mem_Icc.mp (mem_filter.mp hk).1).1,hkQ⟩,(mem_filter.mp hk).2⟩
  have hsmall : (∑ k ∈ S, (if k ≤ Q then 38*H else 0)*vonMangoldt k) ≤ 38*H*(7*Q) := by
    simp only [ite_mul,zero_mul,← sum_filter,← mul_sum]
    exact mul_le_mul_of_nonneg_left
      ((sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => vonMangoldt_nonneg)).trans (ordinaryPrimeLagSums Q).1)
      (by positivity)
  have hroot := Real.sqrt_le_sqrt (hwindow hn)
  rw [Real.sqrt_sq (mul_nonneg hA' hn'.le)] at hroot
  have hlarge : (∑ k ∈ S, tail/Real.sqrt k*vonMangoldt k) ≤ 68*K*A := by
    calc _ = tail*(∑ k ∈ S, vonMangoldt k/Real.sqrt k) := by
              rw [mul_sum]; exact sum_congr rfl fun k _ => by ring
      _ ≤ tail*(34*(A*n)) := mul_le_mul_of_nonneg_left ((ordinaryPrimeLagSums L).2.trans
          (mul_le_mul_of_nonneg_left hroot (by norm_num))) htail
      _ = _ := by dsimp only [tail]; field_simp; ring
  change |(∑ k ∈ S, integratedContact d k*vonMangoldt k)-(∑ k ∈ S, F k*vonMangoldt k)| ≤ _
  rw [← sum_sub_distrib]
  refine (abs_sum_le_sum_abs _ _).trans ?_
  calc _ ≤ ∑ k ∈ S, ((if k ≤ Q then 38*H else 0)+tail/Real.sqrt k)*vonMangoldt k :=
            sum_le_sum fun k hk => by
              rw [← sub_mul,abs_mul,abs_of_nonneg vonMangoldt_nonneg]
              exact mul_le_mul_of_nonneg_right (hrow hk) vonMangoldt_nonneg
    _ ≤ _ := by simp only [add_mul,sum_add_distrib]; exact add_le_add hsmall hlarge

/-- A one-sided power bound on the single prime weight recovers each
subcritical strip, including its endpoint exponent. -/
theorem zetaZeroWidth_le_iff_dyadicPrimeContact {s : ℝ} (hs : 0 ≤ s) (hs' : s < 1/2) :
    zetaZeroWidth ≤ s ↔ ∃ A : ℝ, ∀ n : ℕ, 0 < n →
      dyadicPrimeContact n ≤ A*((n:ℝ)+1)^(2*s) := by
  obtain ⟨C,hC,hc⟩ := dyadicPrimeContact_error
  obtain ⟨D,hD,hd⟩ := successorSquare_contact_degree
  have hscale (n : ℕ) : C+D ≤ (C+D)*((n:ℝ)+1)^(2*s) :=
    le_mul_of_one_le_right (add_nonneg hC hD) (Real.one_le_rpow
      (le_add_of_nonneg_left (Nat.cast_nonneg n)) (mul_nonneg two_pos.le hs))
  rw [zetaZeroWidth_le_iff_successorSquareTriple hs hs']
  constructor
  · rintro ⟨A,hA⟩
    exact ⟨A+(C+D),fun n hn => by
      linarith only [hA n hn,(abs_le.mp (hc hn)).1,(abs_le.mp (hd hn)).2,hscale n]⟩
  · rintro ⟨A,hA⟩
    exact ⟨A+(C+D),fun n hn => by
      linarith only [hA n hn,(abs_le.mp (hc hn)).2,(abs_le.mp (hd hn)).1,hscale n]⟩

/-- The signed logarithm on the diagonal gains the power 1−2w over
each of the two cubic heights, where w is the actual zero width. -/
theorem successorSquare_diagonal_log_at_width :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ n : ℕ, 0 < n →
      |Real.log (ordinaryPrimeGenerator (n • successorSquareTriple n):ℝ)| ≤
        A*(n:ℝ)^2*((n:ℝ)+1)^(2*zetaZeroWidth) := by
  obtain ⟨D,hD,hd⟩ := successorSquare_contact_error
  obtain ⟨C,hC,hc⟩ := successorSquare_contact_degree
  obtain ⟨A,hA,ha⟩ := successorSquare_degree_at_width
  refine ⟨A+C+D,by positivity,fun n hn => ?_⟩
  let g := ((n:ℝ)+1)^(2*zetaZeroWidth)
  have hg : 1 ≤ g := Real.one_le_rpow (le_add_of_nonneg_left (Nat.cast_nonneg n))
    (mul_nonneg two_pos.le zetaZeroWidth_nonneg)
  have hP : |ordinaryPrimeContact (successorSquareTriple n)| ≤ (A+C)*g := by
    rw [abs_le]
    constructor <;> linarith only [(abs_le.mp (hc hn)).1,(abs_le.mp (hc hn)).2,
      (abs_le.mp (ha n hn)).1,(abs_le.mp (ha n hn)).2,le_mul_of_one_le_right hC hg]
  have hpos := sq_nonneg (n:ℝ)
  have hallow := mul_le_mul_of_nonneg_left (le_mul_of_one_le_right hD hg) hpos
  have he := abs_le.mp (hd hn (le_refl n))
  change |_| ≤ (A+C+D)*(n:ℝ)^2*g
  rw [abs_le]
  constructor <;> linarith only [he.1,he.2,hallow,
    mul_le_mul_of_nonneg_left (abs_le.mp hP).1 hpos,mul_le_mul_of_nonneg_left (abs_le.mp hP).2 hpos]

/-- The original rational section comparison for RH is an upper bound on
a single dyadic weighting of ordinary primes at the square scales. -/
theorem riemannHypothesis_iff_dyadicPrimeContact_bounded :
    RiemannHypothesis ↔ ∃ A : ℝ, ∀ n : ℕ, 0 < n → dyadicPrimeContact n ≤ A := by
  have hrh : RiemannHypothesis ↔ zetaZeroWidth ≤ 0 :=
    riemannHypothesis_iff_zetaZeroWidth_eq_zero.trans ⟨fun h => h.le,fun h => le_antisymm h zetaZeroWidth_nonneg⟩
  simpa only [mul_zero,Real.rpow_zero,mul_one] using
    hrh.trans (zetaZeroWidth_le_iff_dyadicPrimeContact le_rfl (by norm_num))

#print axioms successorSquare_diagonal_log_at_width
#print axioms zetaZeroWidth_le_iff_dyadicPrimeContact
#print axioms dyadicPrimeContact_error
#print axioms riemannHypothesis_iff_dyadicPrimeContact_bounded

end GaloisForLFunctions.CountingHolography.Sections
