import GaloisForLFunctions.CountingHolography.Sections.PrimeSectionAllowanceAtTheStripEdge
import GaloisForLFunctions.CountingHolography.Sections.OrdinaryPrimeSectionModuli
import GaloisForLFunctions.SurfaceOfSpecZ.TheZeroFreeStripImprovesItself
import GaloisForLFunctions.SurfaceOfSpecZ.TheWidthLawAtEveryGapSet

/-!
# Three square conductors with one zero pole degree

For each prime p, the divisor p e₁ + (p−1)e_{p²} − e_{p⁴} has
zero positive pole degree. After normalization its only longer-range
correlation has a power saving at the actual zero width. The one-sided
width law at prime squares therefore applies to this single signed triple.
-/

noncomputable section
namespace GaloisForLFunctions.CountingHolography.Sections

open Finset Filter Topology ArithmeticScatteringHolography RenormalizedIntersectionTheory
open ArithmeticOrientationGeometry SurfaceOfSpecZ Zeta23 SquareRootThreshold

/-- Positive pole degree of the integer graph divisor, before multiplication
by the fixed moment of the common atom. -/
def positivePoleDegree {N : ℕ} (a : Fin N → ℤ) : ℝ :=
  ∑ i : Fin N, Real.sqrt ((i : ℝ)+1)*(a i : ℝ)

private def squareLabel (N r : ℕ) (h : r^2 < N) : Fin N := ⟨r^2-1,by omega⟩

private theorem degree_squareLabel {N r : ℕ} (h : r^2 < N) (hr : 0 < r) :
    ((squareLabel N r h : Fin N) : ℝ)+1 = (r : ℝ)^2 := by
  have hh : 0 < r^2 := pow_pos hr _
  change ((r^2-1 : ℕ) : ℝ)+1 = _
  rw [Nat.cast_sub hh,Nat.cast_pow,Nat.cast_one,sub_add_cancel]

/-- A signed divisor supported on three labelled graphs, allowing coincidences. -/
def threeGraphDivisor {N : ℕ} (i j k : Fin N) (A B C : ℤ) : Fin N → ℤ :=
  Pi.single i A + Pi.single j B + Pi.single k (-C)

private theorem square_le_fourth (p : ℕ) : p^2 ≤ p^4 := by
  simpa only [show p^4=p^2*p^2 by ring] using Nat.le_mul_self (p^2)

/-- Apply p minus dilation by p² to the effective pair of conductors 1
and p². The sole negative graph has multiplicity one. -/
def balancedPrimeTriple (p : ℕ) : Fin (p^4+1) → ℤ :=
  threeGraphDivisor 0 (squareLabel _ p (Nat.lt_succ_of_le (square_le_fourth p)))
    (squareLabel _ (p^2) (by rw [← pow_mul]; exact Nat.lt_succ_self _)) p ((p : ℤ)-1) 1

theorem sum_threeGraphDivisor {N : ℕ} (F : Fin N → ℝ) (i j k : Fin N) (A B C : ℤ) :
    ∑ l, F l * (threeGraphDivisor i j k A B C l : ℝ) = F i*A + F j*B - F k*C := by
  simp only [threeGraphDivisor,Pi.add_apply,Pi.single_apply,Int.cast_add,Int.cast_ite,Int.cast_zero,Int.cast_neg,
    mul_add,mul_ite,mul_zero,Finset.sum_add_distrib,Finset.sum_ite_eq',Finset.mem_univ,if_true]
  ring

theorem positivePoleDegree_balancedPrimeTriple {p : ℕ} (hp : p.Prime) :
    positivePoleDegree (balancedPrimeTriple p) = 0 := by
  unfold positivePoleDegree balancedPrimeTriple
  rw [sum_threeGraphDivisor,degree_squareLabel _ hp.pos,degree_squareLabel _ (pow_pos hp.pos _),
    Real.sqrt_sq (Nat.cast_nonneg (α := ℝ) p),Real.sqrt_sq (Nat.cast_nonneg (α := ℝ) (p^2))]
  simp only [Fin.val_zero,Nat.cast_zero,zero_add,Real.sqrt_one,
    Int.cast_natCast,Int.cast_sub,Int.cast_one,Nat.cast_pow]
  ring

/-- Among signed divisors with a nonzero lower coefficient and negative
top coefficient, the balanced triple is the unique one of least mass. -/
theorem balancedTriple_minimum {p A B C : ℤ} (hp : 2 ≤ p) (hA : 0 < A)
    (hC : 0 < C) (h : A+p*B = p^2*C) :
    2*p ≤ A+B+C ∧ (A+B+C = 2*p ↔ A = p ∧ B = p-1 ∧ C = 1) := by
  let r := p*C-B
  have hAr : A = p*r := by dsimp [r]; linarith only [h]
  have hpr : 0 < p*r := hAr ▸ hA
  have hr : 0 < r := pos_of_mul_pos_right hpr (by omega)
  have h₁ := mul_nonneg (show 0 ≤ p-1 by omega) (show 0 ≤ r-1 by omega)
  have h₂ := mul_nonneg (show 0 ≤ p+1 by omega) (show 0 ≤ C-1 by omega)
  have he : A+B+C-2*p = (p-1)*(r-1)+(p+1)*(C-1) := by
    rw [hAr]
    dsimp [r]
    ring
  refine ⟨by omega, ?_⟩
  constructor
  · intro ht
    have hr' : r = 1 := by
      by_contra! hne
      have := mul_pos (show 0 < p-1 by omega) (show 0 < r-1 by omega)
      omega
    have hC' : C = 1 := by
      by_contra! hne
      have := mul_pos (show 0 < p+1 by omega) (show 0 < C-1 by omega)
      omega
    rw [hr',mul_one] at hAr
    have hB' : B = p-1 := by
      dsimp only [r] at hr'
      rw [hC',mul_one] at hr'
      omega
    exact ⟨hAr,hB',hC'⟩
  · rintro ⟨rfl,rfl,rfl⟩
    ring

/-- Real part of the translated spline correlation. -/
def realSplineTrace (s : ℝ) := (splineSeries s).re

theorem integerProbe_threeGraphDivisor {N : ℕ} (i j k : Fin N) (A B C : ℤ) :
    integerProbe N (threeGraphDivisor i j k A B C) =
      (A : ℝ)^2*(atomGram N i i).re + (B : ℝ)^2*(atomGram N j j).re +
      (C : ℝ)^2*(atomGram N k k).re + 2*(A : ℝ)*B*(atomGram N j i).re -
      2*(A : ℝ)*C*(atomGram N k i).re - 2*(B : ℝ)*C*(atomGram N k j).re := by
  have sym (a b : Fin N) : (atomGram N a b).re = (atomGram N b a).re := by
    have h : starRingEnd ℂ (atomGram N b a) = atomGram N a b :=
      congr_fun (congr_fun (atomGram_isHermitian N) a) b
    simpa using (congrArg Complex.re h).symm
  let a := threeGraphDivisor i j k A B C
  let row (l : Fin N) := (atomGram N l i).re*A + (atomGram N l j).re*B - (atomGram N l k).re*C
  have hrow (l : Fin N) :
      ∑ t, (atomGram N l t).re*(a l : ℝ)*(a t : ℝ) = row l*(a l : ℝ) := by
    dsimp only [row]
    rw [← sum_threeGraphDivisor (fun t => (atomGram N l t).re) i j k A B C, Finset.sum_mul]
    exact sum_congr rfl fun _ _ => mul_right_comm _ _ _
  change integerProbe N a = _
  rw [integerProbe_eq_sum]
  simp only [hrow]
  rw [show ∑ l, row l*(a l : ℝ) = row i*A + row j*B - row k*C from sum_threeGraphDivisor row i j k A B C]
  dsimp only [row]
  rw [sym i j,sym i k,sym j k]
  ring

/-- The primitive divisor with fixed coefficients $1,2,-1$ at the squares
of $1,n,2n+1$. Its positive pole degree is zero at every conductor. -/
def successorSquareTriple (n : ℕ) : Fin ((2*n+1)^2+1) → ℤ :=
  threeGraphDivisor 0 (squareLabel _ n (Nat.lt_succ_of_le (Nat.pow_le_pow_left (by omega : n ≤ 2*n+1) 2)))
    (squareLabel _ (2*n+1) (Nat.lt_succ_self _)) 1 2 1

/-- Each primitive triple has total coefficient two. Its mesh resolution
after dilation is therefore at least the multiplicity. -/
theorem successorSquare_resolution_ge (n m : ℕ) : m ≤ resolution (m • successorSquareTriple n) := by
  rw [resolution_smul]
  apply Nat.le_mul_of_pos_right _ (resolution_pos ?_)
  intro hz
  have hs : ∑ i, (1:ℝ)*(successorSquareTriple n i : ℝ) = 2 := by
    unfold successorSquareTriple
    rw [sum_threeGraphDivisor (fun _ => 1)]
    norm_num
  norm_num [hz] at hs

private theorem threeGraphDivisor_support {N : ℕ} {i j k l : Fin N} {A B C : ℤ}
    (h : threeGraphDivisor i j k A B C l ≠ 0) : l = i ∨ l = j ∨ l = k := by
  by_contra! hn
  simp [threeGraphDivisor,hn.1,hn.2.1,hn.2.2] at h

/-- The only possible conductors in the fixed-multiplicity divisor. -/
theorem successorSquareTriple_support {n : ℕ} (hn : 0 < n) {i : Fin ((2*n+1)^2+1)}
    (hi : successorSquareTriple n i ≠ 0) :
    (i:ℝ)+1 = 1 ∨ (i:ℝ)+1 = (n:ℝ)^2 ∨ (i:ℝ)+1 = ((2*n+1:ℕ):ℝ)^2 := by
  unfold successorSquareTriple at hi
  obtain rfl | rfl | rfl := threeGraphDivisor_support hi
  · exact Or.inl (by simp)
  · exact Or.inr (Or.inl (degree_squareLabel _ hn))
  · exact Or.inr (Or.inr (degree_squareLabel _ (Nat.succ_pos (2*n))))

/-- Evaluate any real function of the conductor against the signed triple,
including collisions of its labels. -/
theorem sum_successorSquareTriple {n : ℕ} (hn : 0 < n) (F : ℝ → ℝ) :
    ∑ i : Fin ((2*n+1)^2+1), F ((i : ℝ)+1)*(successorSquareTriple n i : ℝ) =
      F 1+2*F ((n:ℝ)^2)-F (((2*n+1 : ℕ):ℝ)^2) := by
  unfold successorSquareTriple
  rw [sum_threeGraphDivisor (fun i => F ((i:ℝ)+1)),
    degree_squareLabel _ hn,degree_squareLabel _ (Nat.succ_pos (2*n))]
  simp only [Fin.val_zero,Nat.cast_zero,zero_add,Int.cast_one,Int.cast_ofNat,mul_one]
  ring

theorem positivePoleDegree_successorSquareTriple {n : ℕ} (hn : 0 < n) :
    positivePoleDegree (successorSquareTriple n) = 0 := by
  unfold positivePoleDegree successorSquareTriple
  rw [sum_threeGraphDivisor,degree_squareLabel _ hn,degree_squareLabel _ (Nat.succ_pos (2*n)),
    Real.sqrt_sq (Nat.cast_nonneg (α := ℝ) n),Real.sqrt_sq (Nat.cast_nonneg (α := ℝ) (2*n+1))]
  simp only [Fin.val_zero,Nat.cast_zero,zero_add,Real.sqrt_one,
    Int.cast_one,Int.cast_ofNat,Nat.cast_add,Nat.cast_mul,Nat.cast_one,Nat.cast_ofNat]
  ring

theorem integerProbe_successorSquareTriple {n : ℕ} (hn : 0 < n) :
    integerProbe _ (successorSquareTriple n) = 6*realSplineTrace 0 +
      4*realSplineTrace (2*Real.log n) - 2*realSplineTrace (2*Real.log ((2*n+1 : ℕ) : ℝ)) -
      4*realSplineTrace (2*(Real.log ((2*n+1 : ℕ) : ℝ)-Real.log n)) := by
  unfold successorSquareTriple
  rw [integerProbe_threeGraphDivisor]
  simp only [atomGram_eq_splineSeries,degree_squareLabel _ hn,degree_squareLabel _ (Nat.succ_pos (2*n)),
    Fin.val_zero,Nat.cast_zero,zero_add,Real.log_one,Real.log_pow,Int.cast_one,Int.cast_ofNat,
    Nat.cast_ofNat,sub_self,sub_zero,realSplineTrace,mul_sub]
  ring

/-- Signed degree normalized by the squared leading multiplicity. -/
def balancedPrimeDegree (p : ℕ) : ℝ := integerProbe _ (balancedPrimeTriple p)/(p : ℝ)^2

private def tailShare (p : ℕ) : ℝ := 1/(p : ℝ)
private def nearWeight (p : ℕ) : ℝ := 2*(1-tailShare p)^2
private def diagonalWeight (p : ℕ) : ℝ := 1+(1-tailShare p)^2+(tailShare p)^2

private theorem share_bounds {p : ℕ} (hp : p.Prime) :
    0 ≤ tailShare p ∧ tailShare p ≤ 1/2 := by
  have hp' : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  exact ⟨by unfold tailShare; positivity,one_div_le_one_div_of_le (by norm_num) hp'⟩

private theorem weights_bounds {p : ℕ} (hp : p.Prime) :
    1/2 ≤ nearWeight p ∧ nearWeight p ≤ 2 ∧ 0 ≤ diagonalWeight p ∧ diagonalWeight p ≤ 3 := by
  obtain ⟨hb,hb'⟩ := share_bounds hp
  have h₁ : 0 ≤ 1-tailShare p := by linarith only [hb']
  have h₂ : 1-tailShare p ≤ 1 := by linarith only [hb]
  have h₃ : (1/2:ℝ) ≤ 1-tailShare p := by linarith only [hb']
  have h₄ : tailShare p ≤ 1 := by linarith only [hb']
  unfold nearWeight diagonalWeight
  refine ⟨?_,?_,by positivity,?_⟩
  · nlinarith only [pow_le_pow_left₀ (by norm_num : (0:ℝ) ≤ 1/2) h₃ 2]
  · nlinarith only [pow_le_pow_left₀ h₁ h₂ 2]
  · nlinarith only [pow_le_pow_left₀ h₁ h₂ 2,pow_le_pow_left₀ hb h₄ 2]

private theorem balancedPrimeDegree_eq {p : ℕ} (hp : p.Prime) :
    balancedPrimeDegree p = diagonalWeight p*realSplineTrace 0 +
      nearWeight p*realSplineTrace (2*Real.log p) - 2*tailShare p*realSplineTrace (4*Real.log p) := by
  unfold balancedPrimeDegree balancedPrimeTriple
  rw [integerProbe_threeGraphDivisor]
  simp only [atomGram_eq_splineSeries,degree_squareLabel _ hp.pos,degree_squareLabel _ (pow_pos hp.pos _),
    Fin.val_zero,Nat.cast_zero,zero_add,Real.log_one,Nat.cast_pow,Real.log_pow,Int.cast_natCast,
    Int.cast_sub,Int.cast_one,sub_self,sub_zero,Nat.cast_ofNat]
  rw [show 2*((2:ℝ)*Real.log p)-2*Real.log p=2*Real.log p by ring,
    show 2*((2:ℝ)*Real.log p)=4*Real.log p by ring]
  unfold realSplineTrace nearWeight diagonalWeight tailShare
  field_simp [(Nat.cast_pos.mpr hp.pos : 0 < (p : ℝ)).ne']
  ring

private theorem trace_power_bound :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (p : ℕ) (k : ℝ), 0 < p → 0 ≤ k →
      |realSplineTrace (k*Real.log p)| ≤ K*(p : ℝ)^(k*zetaZeroWidth) := by
  obtain ⟨K,hK⟩ := (zeta_splineOrbit_rate_iff_zetaZeroWidth_le zetaZeroWidth_nonneg).mpr le_rfl
  refine ⟨|K|,abs_nonneg _,fun p k hp hk => ?_⟩
  have hp' : 0 < (p : ℝ) := Nat.cast_pos.mpr hp
  have h := hK (k*Real.log p) (mul_nonneg hk (Real.log_natCast_nonneg p))
  rw [orbitCorr_splineCycle_eq] at h
  have he : Real.exp (zetaZeroWidth*(k*Real.log p)) = (p : ℝ)^(k*zetaZeroWidth) := by
    rw [Real.rpow_def_of_pos hp']
    congr 1
    ring
  rw [he] at h
  exact h.trans (mul_le_mul_of_nonneg_right (le_abs_self K) (Real.rpow_nonneg hp'.le _))

private theorem longLag_error :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ p : ℕ, p.Prime →
      |balancedPrimeDegree p - nearWeight p*realSplineTrace (2*Real.log p)| ≤
        D*(p : ℝ)^(max 0 (4*zetaZeroWidth-1)) := by
  obtain ⟨K,hK,htr⟩ := trace_power_bound
  let T := |realSplineTrace 0|
  refine ⟨3*T+4*K,by dsimp [T]; positivity,fun p hp => ?_⟩
  have hp' : 0 < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  have hp₁ : 1 ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  obtain ⟨hb,_⟩ := share_bounds hp
  obtain ⟨_,_,hd0,hd3⟩ := weights_bounds hp
  let B := (p : ℝ)^(max 0 (4*zetaZeroWidth-1))
  have hB : 1 ≤ B := Real.one_le_rpow hp₁ (le_max_left _ _)
  have htail : 2*tailShare p*|realSplineTrace (4*Real.log p)| ≤ 4*K*B := by
    have hbp : tailShare p ≤ 2/(p : ℝ) := div_le_div_of_nonneg_right (by norm_num) hp'.le
    calc _ ≤ (2*(2/p))*(K*(p : ℝ)^(4*zetaZeroWidth)) :=
           mul_le_mul (mul_le_mul_of_nonneg_left hbp (by norm_num)) (htr p 4 hp.pos (by norm_num))
             (abs_nonneg _) (by positivity)
      _ = 4*K*(p : ℝ)^(4*zetaZeroWidth-1) := by rw [Real.rpow_sub hp',Real.rpow_one]; ring
      _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hp₁ (le_max_right _ _)) (by positivity)
  rw [balancedPrimeDegree_eq hp,show ∀ x y z : ℝ, x+y-z-y=x-z by intros; ring]
  have h := abs_sub_le (diagonalWeight p*realSplineTrace 0) 0 (2*tailShare p*realSplineTrace (4*Real.log p))
  simp only [sub_zero,zero_sub,abs_neg,abs_mul,abs_of_nonneg hd0,
    abs_of_nonneg hb,abs_two] at h
  calc _ ≤ diagonalWeight p*T + 2*tailShare p*|realSplineTrace (4*Real.log p)| := h
    _ ≤ 3*T*B+4*K*B := add_le_add
      ((mul_le_mul_of_nonneg_right hd3 (abs_nonneg _)).trans
        (le_mul_of_one_le_right (mul_nonneg (by norm_num : (0:ℝ) ≤ 3) (abs_nonneg (realSplineTrace 0))) hB)) htail
    _ = _ := by ring

/-- The one-sided growth exponent of the three-graph degree on primes
is exactly twice the zero width when measured against p. -/
theorem zetaZeroWidth_le_iff_balancedPrimeDegree {s : ℝ} (hs : 0 ≤ s) :
    zetaZeroWidth ≤ s ↔ ∃ A : ℝ, ∀ p : ℕ, p.Prime →
      -(A*(p : ℝ)^(2*s)) ≤ balancedPrimeDegree p := by
  obtain ⟨D,hD,hr⟩ := longLag_error
  have hw₀ := zetaZeroWidth_nonneg
  have hw₁ : zetaZeroWidth < 1/2 :=
    ZeroForcingCalculus.zetaZeroWidth_le_sub_three_eighths.trans_lt (by norm_num)
  constructor
  · intro hw
    obtain ⟨K,hK,htr⟩ := trace_power_bound
    refine ⟨2*K+D, fun p hp => ?_⟩
    have hp₁ : 1 ≤ (p : ℝ) := by exact_mod_cast hp.one_le
    obtain ⟨hwlo,hwhi,_,_⟩ := weights_bounds hp
    have hx := (abs_le.mp (htr p 2 hp.pos (by norm_num))).1
    have ht := mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le hp₁
      (show 2*zetaZeroWidth ≤ 2*s by linarith)) hK
    have hcorr : -(K*(p : ℝ)^(2*s)) ≤ realSplineTrace (2*Real.log p) := by linarith only [hx,ht]
    have herr := (abs_le.mp (hr p hp)).1
    have hex : max 0 (4*zetaZeroWidth-1) ≤ 2*s := max_le (by linarith) (by linarith)
    have hrem := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hp₁ hex) hD
    have hmul := mul_le_mul_of_nonneg_left hcorr (show 0 ≤ nearWeight p by linarith only [hwlo])
    have hslack := mul_le_mul_of_nonpos_right hwhi (neg_nonpos.mpr (mul_nonneg hK (Real.rpow_nonneg (zero_le_one.trans hp₁) (2*s))))
    linarith only [hrem,herr,hmul,hslack]
  · rintro ⟨A,hA⟩
    by_contra! hw
    let b := max s (2*zetaZeroWidth-1/2)
    have hb : 0 ≤ b := hs.trans (le_max_left _ _)
    have hbw : b < zetaZeroWidth := max_lt hw (by linarith)
    apply hbw.not_ge
    apply (zetaZeroWidth_le_iff_bddBelow_of_powGaps hb (hbw.trans hw₁) (by norm_num)
      (powGaps_kthPrimePowers (k := 2) (by norm_num))).mpr
    refine ⟨4*(|A|+D),?_⟩
    rintro d ⟨p,hp,rfl⟩
    have hp₁ : 1 ≤ (p : ℝ) := by exact_mod_cast hp.one_le
    have hp₀ : 0 ≤ (p : ℝ) := Nat.cast_nonneg _
    have hpow : ((p^2 : ℕ) : ℝ)^b = (p : ℝ)^(2*b) := by
      simpa only [Nat.cast_pow,Nat.cast_ofNat] using (Real.rpow_natCast_mul hp₀ 2 b).symm
    rw [hpow,← orbitCorr_eq_re_lagStructure_spline,orbitCorr_splineCycle_eq,Nat.cast_pow,Real.log_pow]
    change -(4*(|A|+D)*(p : ℝ)^(2*b)) ≤ 2*realSplineTrace (2*Real.log p)
    have hex : max 0 (4*zetaZeroWidth-1) ≤ 2*b := max_le (by linarith)
      (by linarith only [le_max_right s (2*zetaZeroWidth-1/2)])
    let B := (p : ℝ)^(2*b)
    have hB₀ : 0 ≤ B := Real.rpow_nonneg hp₀ _
    have he := (abs_le.mp (hr p hp)).2
    have hE := mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hp₁ hex) hD
    have hsb : s ≤ b := le_max_left _ _
    have hA' : A*(p : ℝ)^(2*s) ≤ |A| * B :=
      mul_le_mul (le_abs_self _) (Real.rpow_le_rpow_of_exponent_le hp₁ (by linarith only [hsb]))
        (Real.rpow_nonneg hp₀ _) (abs_nonneg _)
    have hshare := (weights_bounds hp).1
    by_cases hpos : 0 ≤ realSplineTrace (2*Real.log p)
    · exact (neg_nonpos.mpr (mul_nonneg (by positivity) hB₀)).trans (mul_nonneg two_pos.le hpos)
    have hm := mul_le_mul_of_nonpos_right hshare (le_of_not_ge hpos)
    change _ ≤ D*B at hE
    change -(4*(|A|+D)*B) ≤ _
    linarith only [hm,hA p hp,hA',he,hE]

/-- The true section degrees on these pole-balanced rays recover the
strip with an allowance at cofinal multiplicities. -/
theorem zetaZeroWidth_le_iff_balancedPrime_sections {s : ℝ} (hs : 0 ≤ s) :
    zetaZeroWidth ≤ s ↔ ∃ A : ℝ, ∀ p : ℕ, p.Prime → ∃ᶠ m : ℕ in atTop,
      Real.log (generator (m • balancedPrimeTriple p) : ℝ) ≤ radius (m • balancedPrimeTriple p) +
        (A*(p : ℝ)^(2*s)*(p : ℝ)^2)*(m : ℝ)^2 := by
  rw [zetaZeroWidth_le_iff_balancedPrimeDegree hs]
  constructor
  · rintro ⟨A,hA⟩
    refine ⟨A+1,fun p hp => ?_⟩
    have hp₀ : 0 < (p : ℝ) := Nat.cast_pos.mpr hp.pos
    have h₁ := (le_div_iff₀ (pow_pos hp₀ 2)).mp (hA p hp)
    have h₂ : -((A+1)*(p : ℝ)^(2*s)*(p : ℝ)^2) < integerProbe _ (balancedPrimeTriple p) := by
      linarith only [h₁,mul_pos (Real.rpow_pos_of_pos hp₀ (2*s)) (pow_pos hp₀ 2)]
    apply Eventually.frequently
    filter_upwards [(tendsto_splineDegree (balancedPrimeTriple p)).eventually_const_lt h₂,
      eventually_ge_atTop 1] with m hm hm1
    have h₃ := (lt_div_iff₀ (by positivity : 0 < (m : ℝ)^2)).mp hm
    linarith only [h₃]
  · rintro ⟨A,hA⟩
    refine ⟨A,fun p hp => ?_⟩
    have hp₀ : 0 < (p : ℝ) := Nat.cast_pos.mpr hp.pos
    apply (le_div_iff₀ (pow_pos hp₀ 2)).mpr
    by_contra! hneg
    obtain ⟨m,hm,hm',hm1⟩ := ((hA p hp).and_eventually
      (((tendsto_splineDegree (balancedPrimeTriple p)).eventually_lt_const hneg).and (eventually_ge_atTop 1))).exists
    have he := (div_lt_iff₀ (by positivity : 0 < (m : ℝ)^2)).mp hm'
    linarith only [hm,he]

theorem threeGraphDivisor_mass {N : ℕ} (i j k : Fin N) (A B C : ℤ) :
    ∑ l, |(threeGraphDivisor i j k A B C l : ℝ)| ≤ |(A : ℝ)|+|(B : ℝ)|+|(C : ℝ)| := by
  let a : Fin N → ℤ := Pi.single i A
  let b : Fin N → ℤ := Pi.single j B
  let c : Fin N → ℤ := Pi.single k (-C)
  have h (l : Fin N) : |(threeGraphDivisor i j k A B C l : ℝ)| ≤ |(a l : ℝ)|+|(b l : ℝ)|+|(c l : ℝ)| := by
    change |(((a l + b l + c l : ℤ) : ℝ))| ≤ _
    push_cast
    exact (abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)
  refine (sum_le_sum fun l _ => h l).trans ?_
  simp only [a,b,c,sum_add_distrib,Pi.single_apply,Int.cast_ite,Int.cast_zero,Int.cast_neg,
    apply_ite abs,abs_zero,abs_neg,sum_ite_eq',mem_univ,if_true,le_refl]

theorem successorSquareTriple_mass (n : ℕ) :
    ∑ i, |(successorSquareTriple n i : ℝ)| ≤ 4 := by
  unfold successorSquareTriple
  exact (threeGraphDivisor_mass _ _ _ _ _ _).trans (by norm_num)

theorem balancedPrimeTriple_mass {p : ℕ} (hp : p.Prime) (m : ℕ) :
    ∑ i, |((m • balancedPrimeTriple p) i : ℝ)| ≤ 2*(p : ℝ)*m := by
  have hp₁ : 1 ≤ (p : ℝ) := by exact_mod_cast hp.one_le
  have hm : ∑ i, |((m • balancedPrimeTriple p) i : ℝ)| =
      (m : ℝ)*∑ i, |(balancedPrimeTriple p i : ℝ)| := by
    simp only [Pi.smul_apply,nsmul_eq_mul,Int.cast_mul,Int.cast_natCast,abs_mul,
      abs_of_nonneg (Nat.cast_nonneg m : (0:ℝ) ≤ m),mul_sum]
  have h : ∑ i, |(balancedPrimeTriple p i : ℝ)| ≤ 2*(p : ℝ) := by
    unfold balancedPrimeTriple
    refine (threeGraphDivisor_mass _ _ _ _ _ _).trans ?_
    simp only [Int.cast_natCast,Int.cast_sub,Int.cast_one,abs_one,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) p),abs_of_nonneg (sub_nonneg.mpr hp₁)]
    linarith
  rw [hm,mul_comm (2*(p : ℝ))]
  exact mul_le_mul_of_nonneg_left h (Nat.cast_nonneg _)

/-- Along any fixed ray, the cost of dropping proper powers is quadratic
in total variation; the fixed horizon rounding term is absorbed on a tail. -/
theorem eventually_signed_prime_error :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (N : ℕ) (a : Fin N → ℤ), ∀ᶠ m : ℕ in atTop,
      |Real.log (generator (m • a) : ℝ) - Real.log (ordinaryPrimeGenerator (m • a) : ℝ)| ≤
        (C*(∑ i, |(a i : ℝ)|)^2+1)*(m : ℝ)^2 := by
  obtain ⟨C,hC,h⟩ := signed_generator_difference_bound
  refine ⟨C,hC,fun N a => ?_⟩
  let H : ℝ := ∑ k ∈ Icc 2 (3*windowEnd N), ArithmeticFunction.vonMangoldt k
  have hinf := (tendsto_pow_atTop (α := ℝ) two_ne_zero).comp tendsto_natCast_atTop_atTop
  filter_upwards [hinf.eventually_ge_atTop H] with m hm
  have he : ∑ i, |((m • a) i : ℝ)| = (m : ℝ)*∑ i, |(a i : ℝ)| := by
    simp only [Pi.smul_apply,nsmul_eq_mul,Int.cast_mul,Int.cast_natCast,abs_mul,
      abs_of_nonneg (Nat.cast_nonneg (α := ℝ) m),mul_sum]
  have hx := h N (m • a)
  rw [he] at hx
  change H ≤ (m : ℝ)^2 at hm
  change _ ≤ C*_ + H at hx
  linarith only [hx,hm]

private theorem ordinaryTriple_log_difference :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ p : ℕ, p.Prime → ∀ᶠ m : ℕ in atTop,
      |Real.log (generator (m • balancedPrimeTriple p) : ℝ) -
        Real.log (ordinaryPrimeGenerator (m • balancedPrimeTriple p) : ℝ)| ≤ D*(p : ℝ)^2*(m : ℝ)^2 := by
  obtain ⟨C,hC,h⟩ := eventually_signed_prime_error
  refine ⟨4*C+1,by positivity,fun p hp => ?_⟩
  have hmass := balancedPrimeTriple_mass hp 1
  simp only [one_smul,Nat.cast_one,mul_one] at hmass
  have ht := mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (sum_nonneg fun _ _ => abs_nonneg _) hmass 2) hC
  have h1 : (1 : ℝ) ≤ (p : ℝ)^2 := one_le_pow₀ (by exact_mod_cast hp.one_le)
  exact (h _ _).mono fun m hm => hm.trans (mul_le_mul_of_nonneg_right
    (by linarith only [ht,h1]) (sq_nonneg (m : ℝ)))

/-- The same exponent is detected by the rational generator formed only
from signed ordinary-prime contacts, at the original archimedean radius. -/
theorem zetaZeroWidth_le_iff_ordinaryTriple_sections {s : ℝ} (hs : 0 ≤ s) :
    zetaZeroWidth ≤ s ↔ ∃ A : ℝ, ∀ p : ℕ, p.Prime → ∃ᶠ m : ℕ in atTop,
      Real.log (ordinaryPrimeGenerator (m • balancedPrimeTriple p) : ℝ) ≤ radius (m • balancedPrimeTriple p) +
        (A*(p : ℝ)^(2*s)*(p : ℝ)^2)*(m : ℝ)^2 := by
  rw [zetaZeroWidth_le_iff_balancedPrime_sections hs]
  obtain ⟨D,hD,hd⟩ := ordinaryTriple_log_difference
  constructor <;> rintro ⟨A,hA⟩ <;> refine ⟨A+D,fun p hp => ?_⟩ <;>
    refine ((hA p hp).and_eventually (hd p hp)).mono fun m ⟨hm,he⟩ => ?_
  all_goals
    have hp₁ : (1:ℝ) ≤ p := by exact_mod_cast hp.one_le
    have hpow := Real.one_le_rpow hp₁ (show 0 ≤ 2*s by linarith)
    have hh := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left hpow hD) (by positivity : 0 ≤ (p : ℝ)^2)) (sq_nonneg (m : ℝ))
    obtain ⟨hl,hu⟩ := abs_le.mp he
    linarith only [hm,hl,hu,hh]

#print axioms balancedTriple_minimum
#print axioms sum_successorSquareTriple
#print axioms successorSquare_resolution_ge
#print axioms positivePoleDegree_balancedPrimeTriple
#print axioms zetaZeroWidth_le_iff_balancedPrimeDegree
#print axioms zetaZeroWidth_le_iff_balancedPrime_sections
#print axioms zetaZeroWidth_le_iff_ordinaryTriple_sections

end GaloisForLFunctions.CountingHolography.Sections
