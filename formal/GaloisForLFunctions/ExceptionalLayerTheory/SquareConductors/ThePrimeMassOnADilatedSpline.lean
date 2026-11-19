import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.TheIntegralOnTheRescaledProductShell
import GaloisForLFunctions.ExceptionalLayerTheory.SquareConductors.ThePrimeMassAtAQuadraticProductDivider

/-!
# Ordinary prime mass on a dilated spline

At any positive mesh spacing, the one-cell quotient estimate bounds the
Mangoldt discrepancy on a sharp interval. Removing proper powers and
integrating the remaining unit lattice retains the two end samples.
-/

noncomputable section
open Finset ArithmeticFunction MeasureTheory
open _root_.RHTower
namespace GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval

/-- Ordinary first primes through a sharp index, tested by a real spline dilation. -/
def primeSplineSamples (d : ℝ) (K : ℕ) :=
  ∑ p ∈ (Ioc 0 K).filter Nat.Prime, Real.log p*dyadicSpline (p*d)

private theorem spline_prime_discrepancy :
    ∃ C : ℝ, 0≤C ∧ ∀ {d : ℝ}, 0<d → ∀ K : ℕ,
      |primeSplineSamples d K - ∑ k ∈ Ioc 0 K, dyadicSpline (k*d)| ≤ C*(K:ℝ)^(8/9:ℝ) := by
  have hΘ : zeroReSup ≤ 20999/24000 := zeroReSup_le_of_forall_re_le fun q => by
    by_contra! hq
    exact GaloisForLFunctions.MetaplecticMobiusDescent.CubicEisenstein.riemannZeta_ne_zero_of_sub_seven_eighths_lt_re hq
      (riemannZeta_eq_zero_of_xiZeroCopy q)
  obtain ⟨A,hA,ha⟩ := quotientMeshProfile_prime_interval (by linarith only [hΘ] : zeroReSup<8/9)
  have hs : HasCompactSupport dyadicSpline := HasCompactSupport.intro isCompact_Icc
    (fun _ hx => dyadicSpline_eq_zero_outside hx)
  obtain ⟨B,hb⟩ := hs.exists_bound_of_continuous contDiff_six_dyadicSpline.continuous
  have hB : 0≤B := (norm_nonneg _).trans (hb 0)
  obtain ⟨E,he⟩ := Chebyshev.psi_sub_theta_le_mul_sqrt
  refine ⟨A+B*|E|,by positivity,fun {d} hd K => ?_⟩
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · simp [primeSplineSamples,Real.zero_rpow (by norm_num : (8/9:ℝ)≠0)]
  let f (k : ℕ) := dyadicSpline (k*d)
  let T := Ioc 0 K
  let S := ∑ k ∈ T, vonMangoldt k*f k
  let P := primeSplineSamples d K
  let U := ∑ k ∈ T, f k
  have hcell (x : ℝ) : quotientMeshProfile 1 x = -dyadicSpline x := by
    have hz : dyadicSpline 0=0 := if_neg (lt_irrefl _)
    simp [quotientMeshProfile,hz,centeredPrimeWeight_at_zero]
  have hmesh := ha 1 0 K hd (Nat.zero_le K)
  simp only [hcell,mul_neg,sum_neg_distrib,abs_neg] at hmesh
  have hSU : |S-U|≤A*(K:ℝ)^(8/9:ℝ) := by
    dsimp only [S,U,T,f]; rwa [←sum_sub_distrib,sum_congr rfl (fun k _ =>
      show vonMangoldt k*dyadicSpline (k*d)-dyadicSpline (k*d) =
        (vonMangoldt k-1)*dyadicSpline (k*d) by ring)]
  have hpr : P=∑ k ∈ T.filter Nat.Prime, vonMangoldt k*f k := by
    apply sum_congr rfl
    intro k hk
    rw [vonMangoldt_apply_prime (mem_filter.mp hk).2]
  have hsp := sum_filter_add_sum_filter_not T Nat.Prime (fun k => vonMangoldt k*f k)
  have hSP : S-P=∑ k ∈ T.filter (fun k => ¬k.Prime), vonMangoldt k*f k := by
    rw [hpr]
    dsimp only [S]
    linarith only [hsp]
  have hbad : |S-P|≤B*(Chebyshev.psi K-Chebyshev.theta K) := by
    rw [hSP,Chebyshev.psi_sub_theta_eq_sum_not_prime,Nat.floor_natCast,mul_sum]
    apply (abs_sum_le_sum_abs _ _).trans
    apply sum_le_sum
    intro k _
    rw [abs_mul,abs_of_nonneg vonMangoldt_nonneg,mul_comm B]
    exact mul_le_mul_of_nonneg_left (by simpa only [f,Real.norm_eq_abs] using hb (k*d)) vonMangoldt_nonneg
  have hpow : Real.sqrt K≤(K:ℝ)^(8/9:ℝ) := by
    rw [Real.sqrt_eq_rpow]
    exact Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hK) (by norm_num)
  have hsmall := (he K).trans (mul_le_mul (le_abs_self E) hpow (Real.sqrt_nonneg _) (abs_nonneg _))
  change |P-U| ≤ _
  rw [show P-U=(S-U)-(S-P) by ring]
  exact (abs_sub _ _).trans ((add_le_add hSU (hbad.trans (mul_le_mul_of_nonneg_left hsmall hB))).trans_eq (by ring))

/-- The lattice quadrature error is bounded by the Lipschitz constant times
the normalized terminal coordinate, uniformly down to the first sample. -/
theorem prime_spline_quadrature :
    ∃ A B : ℝ, 0≤A ∧ 0≤B ∧ ∀ {d : ℝ}, 0<d → ∀ K : ℕ,
      |primeSplineSamples d K-(∫ t in (0:ℝ)..(K:ℝ)*d, dyadicSpline t)/d| ≤
        A*(K:ℝ)^(8/9:ℝ)+B*((K:ℝ)*d) := by
  obtain ⟨A,hA,ha⟩ := spline_prime_discrepancy
  have hs : HasCompactSupport dyadicSpline := HasCompactSupport.intro isCompact_Icc
    (fun _ hx => dyadicSpline_eq_zero_outside hx)
  have hdiff : ContDiff ℝ 1 dyadicSpline := contDiff_six_dyadicSpline.of_le (by norm_num)
  obtain ⟨B,hB⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hs hdiff one_ne_zero
  refine ⟨A,B,hA,B.coe_nonneg,fun {d} hd K => ?_⟩
  let U := ∑ k ∈ Ioc 0 K, dyadicSpline (k*d)
  let I := ∫ t in (0:ℝ)..(K:ℝ)*d, dyadicSpline t
  have h := _root_.RHTower.abs_riemannSum_sub_integral_le (T := K*d)
    hB.lipschitzOnWith hdiff.continuous.continuousOn K hd.le le_rfl
  have he : U=∑ j ∈ range K, dyadicSpline (((j:ℝ)+1)*d) := by
    dsimp only [U]
    rw [show Ioc 0 K=Ico 1 (K+1) by ext j; simp only [mem_Ioc,mem_Ico]; omega,sum_Ico_eq_sum_range]
    simp only [show K+1-1=K by omega,Nat.add_comm 1,Nat.cast_add,Nat.cast_one]
  have hgrid : |d*U-I|≤(B:ℝ)*K*d^2 := by rwa [he]
  have hUI : |U-I/d|≤(B:ℝ)*((K:ℝ)*d) := by
    rw [show U-I/d=(d*U-I)/d by field_simp [hd.ne'],abs_div,abs_of_pos hd,div_le_iff₀ hd]
    exact hgrid.trans_eq (by ring)
  change |primeSplineSamples d K-I/d| ≤ _
  rw [show primeSplineSamples d K-I/d=(primeSplineSamples d K-U)+(U-I/d) by ring]
  exact (abs_add_le _ _).trans (add_le_add (ha hd K) hUI)

/-- For a fixed quadratic cutoff the coefficient is the integral through
the real endpoint. Rounding its last prime cell costs only a constant. -/
theorem doubled_prime_spline_at_quadratic_cut {u : ℝ} (hu : 0<u) :
    ∃ C : ℝ, 0≤C ∧ ∀ {n : ℕ}, 0<n →
      |primeSplineSamples (2/(n:ℝ)^2) ⌊u*(n:ℝ)^2⌋₊ -
        ((n:ℝ)^2/2)*(∫ t in (0:ℝ)..2*u, dyadicSpline t)| ≤ C*(n:ℝ)^(16/9:ℝ) := by
  obtain ⟨A,B,hA,hB,ha⟩ := prime_spline_quadrature
  have hs : HasCompactSupport dyadicSpline := HasCompactSupport.intro isCompact_Icc
    (fun _ hx => dyadicSpline_eq_zero_outside hx)
  have hc := contDiff_six_dyadicSpline.continuous
  obtain ⟨D,hD⟩ := hs.exists_bound_of_continuous hc
  have hD0 : 0≤D := (norm_nonneg _).trans (hD 0)
  refine ⟨A*u^(8/9:ℝ)+B*(2*u)+D,by positivity,fun {n} hn => ?_⟩
  have hn₁ : 1≤(n:ℝ) := Nat.one_le_cast.mpr hn
  have hn₀ := zero_lt_one.trans_le hn₁
  have hsq := sq_pos_of_pos hn₀
  let d := 2/(n:ℝ)^2
  let K := ⌊u*(n:ℝ)^2⌋₊
  let x := (K:ℝ)*d
  have hd : 0<d := div_pos two_pos hsq
  have hnorm : u*(n:ℝ)^2*d=2*u := by dsimp only [d]; field_simp
  have hx : x≤2*u := (mul_le_mul_of_nonneg_right (Nat.floor_le (mul_nonneg hu.le hsq.le)) hd.le).trans_eq hnorm
  have hx' : 2*u-x≤d := by
    have hh := mul_le_mul_of_nonneg_right (Nat.lt_floor_add_one (u*(n:ℝ)^2)).le hd.le
    rw [hnorm] at hh
    change 2*u-(K:ℝ)*d≤d
    linarith only [hh]
  have hI : |∫ t in x..2*u, dyadicSpline t|≤D*d := by
    have h := intervalIntegral.norm_integral_le_of_norm_le_const
      (fun t (_ : t ∈ Set.uIoc x (2*u)) => hD t)
    rw [Real.norm_eq_abs,abs_of_nonneg (sub_nonneg.mpr hx)] at h
    exact h.trans (mul_le_mul_of_nonneg_left hx' hD0)
  let I (t : ℝ) := ∫ y in (0:ℝ)..t, dyadicSpline y
  have hshift : |I x/d-((n:ℝ)^2/2)*I (2*u)|≤D := by
    have hid : ((n:ℝ)^2/2)*I (2*u) = I (2*u)/d := by dsimp only [d]; field_simp
    have hsplit : I (2*u)=I x+∫ t in x..2*u, dyadicSpline t :=
      (intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable 0 x) (hc.intervalIntegrable x (2*u))).symm
    rw [hid,←sub_div,hsplit,sub_add_eq_sub_sub,sub_self,zero_sub,abs_div,abs_neg,abs_of_pos hd,div_le_iff₀ hd]
    exact hI
  let X := (n:ℝ)^(16/9:ℝ)
  have hX : 1≤X := Real.one_le_rpow hn₁ (by norm_num)
  have hK : (K:ℝ)^(8/9:ℝ) ≤ u^(8/9:ℝ)*X := by
    apply (Real.rpow_le_rpow (Nat.cast_nonneg K) (Nat.floor_le (mul_nonneg hu.le hsq.le))
      (by norm_num : (0:ℝ)≤8/9)).trans_eq
    rw [Real.mul_rpow hu.le hsq.le,←Real.rpow_two (n:ℝ),←Real.rpow_mul hn₀.le]
    norm_num [X]
  have hprice := ha hd K
  change |primeSplineSamples d K-I x/d|≤A*(K:ℝ)^(8/9:ℝ)+B*x at hprice
  change |primeSplineSamples d K-((n:ℝ)^2/2)*I (2*u)|≤_*X
  rw [show primeSplineSamples d K-((n:ℝ)^2/2)*I (2*u)=
    (primeSplineSamples d K-I x/d)+(I x/d-((n:ℝ)^2/2)*I (2*u)) by ring]
  apply (abs_add_le _ _).trans ((add_le_add hprice hshift).trans _)
  have hb := le_mul_of_one_le_right (mul_nonneg hB (mul_nonneg two_pos.le hu.le)) hX
  have hd' := le_mul_of_one_le_right hD0 hX
  linarith only [mul_le_mul_of_nonneg_left hK hA,mul_le_mul_of_nonneg_left hx hB,hb,hd']

/-- Subtracting two sharp prime cutoffs retains the left-open and right-closed band. -/
theorem prime_spline_band {A B : ℕ} (hab : A≤B) (d : ℝ) :
    (∑ p ∈ (Ioc A B).filter Nat.Prime, Real.log p*dyadicSpline (p*d)) =
      primeSplineSamples d B-primeSplineSamples d A := by
  let f (p : ℕ) := if p.Prime then Real.log p*dyadicSpline (p*d) else 0
  have he := sum_Ioc_consecutive f (Nat.zero_le A) hab
  simp only [f,←sum_filter] at he
  unfold primeSplineSamples
  linarith only [he]

#print axioms prime_spline_band
#print axioms doubled_prime_spline_at_quadratic_cut
#print axioms prime_spline_quadrature

end GaloisForLFunctions.ExceptionalLayerTheory.FactorialInterval
