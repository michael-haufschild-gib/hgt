import GaloisForLFunctions.BezoutValuationIncidence.TheMoebiusEnergyTransfersAtEverySuperlinearHorizon
import GaloisForLFunctions.TransHorizonIncidenceMechanics.DampedDiscrepancyEnergyGrowthLaw
import GaloisForLFunctions.BezoutValuationIncidence.QuadraticOrderL1ObservabilityConstant

/-!
# Fibre masses of the Jordan weight

For the Jordan weight `J₂(q)/q² = Σ_{d ∣ q} μ(d)/d²` (`jordanTotient2_div_sq`) and squarefree `m`,
the fibre mass `U_m(N,j) = Σ_{q ≤ N, ⌊N/q⌋ = j, (q,m)=1} μ(q)² J₂(q)/q²` (`jordanFibreMass`)
satisfies (`abs_jordanFibreMass_sub_le`)

`|U_m(N,j) − δ(m) N/(j(j+1))| ≤ 2 ζ(3/2) τ(m) √N (2 + ζ(3/2) + log N) + 3 ζ(2)`,

with the density `δ(m) = Σ_{(d,m)=1} μ(d) D(dm)/d³` (`jordanCoprimeDensity`), `D` the
coprime-squarefree density. Mechanism: writing `q = dq'` (`jordanFibreMass_eq`) turns the fibre of
`N` into the fibre of `⌊N/d⌋` for squarefree `q'` prime to `dm`, an interval counted by
`abs_coprimeSquarefreeCount_sub_le`.
-/

open Finset Filter Topology ArithmeticFunction
open GaloisForLFunctions.TransHorizonIncidenceMechanics

namespace GaloisForLFunctions.BezoutValuationIncidence

noncomputable section
set_option autoImplicit false

/-! ### The Jordan weight -/

/-- `J₂(q)/q² = Σ_{d ∣ q} μ(d)/d²`. -/
theorem jordanTotient2_div_sq {q : ℕ} (hq : q ≠ 0) :
    BiScaleUncertainty.jordanTotient2 q / (q : ℝ) ^ 2 =
      ∑ d ∈ q.divisors, (moebius d : ℝ) / (d : ℝ) ^ 2 := by
  have hqR : (q : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hq
  rw [BiScaleUncertainty.jordanTotient2,
    show (∑ x ∈ q.divisorsAntidiagonal, ((moebius x.1 : ℤ) : ℝ) * (x.2 : ℝ) ^ (2 : ℕ)) =
      ∑ d ∈ q.divisors, ((moebius d : ℤ) : ℝ) * ((q / d : ℕ) : ℝ) ^ (2 : ℕ) from
      Nat.sum_divisorsAntidiagonal (fun a b => ((moebius a : ℤ) : ℝ) * (b : ℝ) ^ (2 : ℕ)), sum_div]
  refine sum_congr rfl fun d hd => ?_
  have hd0 : (d : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.pos_of_mem_divisors hd).ne'
  rw [Nat.cast_div (Nat.dvd_of_mem_divisors hd) hd0]
  field_simp

theorem coprimeSquarefreeDensity_nonneg (n : ℕ) : 0 ≤ coprimeSquarefreeDensity n := by
  unfold coprimeSquarefreeDensity
  refine mul_nonneg ?_ (prod_nonneg fun p _ => by positivity)
  rw [RHTower.Sieve.squarefreeDensity_eq]; positivity

theorem coprimeSquarefreeDensity_le_one (n : ℕ) : coprimeSquarefreeDensity n ≤ 1 := by
  unfold coprimeSquarefreeDensity
  have hρ : RHTower.Sieve.squarefreeDensity ≤ 1 := by
    rw [RHTower.Sieve.squarefreeDensity_eq, div_le_one (by positivity)]
    nlinarith [Real.pi_gt_three]
  have hρ0 : 0 ≤ RHTower.Sieve.squarefreeDensity := by
    rw [RHTower.Sieve.squarefreeDensity_eq]; positivity
  have hP : ∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) + 1) ≤ 1 :=
    prod_le_one (fun p _ => by positivity)
      (fun p _ => by rw [div_le_one (by positivity)]; linarith)
  have hP0 : 0 ≤ ∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) + 1) :=
    prod_nonneg fun p _ => by positivity
  calc RHTower.Sieve.squarefreeDensity * ∏ p ∈ n.primeFactors, (p : ℝ) / ((p : ℝ) + 1)
      ≤ 1 * 1 := mul_le_mul hρ hP hP0 zero_le_one
    _ = 1 := one_mul 1

/-! ### The density -/

/-- The term `[(d,m)=1] μ(d) D(dm)/d³`. -/
def jordanDensityTerm (m d : ℕ) : ℝ :=
  if Nat.Coprime d m then (moebius d : ℝ) * coprimeSquarefreeDensity (d * m) / (d : ℝ) ^ 3 else 0

theorem abs_jordanDensityTerm_le (m d : ℕ) : |jordanDensityTerm m d| ≤ ((d : ℝ) ^ 3)⁻¹ := by
  unfold jordanDensityTerm
  split_ifs
  · rcases Nat.eq_zero_or_pos d with rfl | hd
    · simp
    · have hd3 : (0 : ℝ) < (d : ℝ) ^ 3 := pow_pos (by exact_mod_cast hd) 3
      rw [abs_div, abs_of_pos hd3, div_eq_mul_inv]
      apply mul_le_of_le_one_left (inv_nonneg.mpr hd3.le)
      rw [abs_mul, abs_of_nonneg (coprimeSquarefreeDensity_nonneg _)]
      have h1 : |(moebius d : ℝ)| ≤ 1 := by exact_mod_cast abs_moebius_le_one
      have h2 := coprimeSquarefreeDensity_le_one (d * m)
      have h3 := coprimeSquarefreeDensity_nonneg (d * m)
      calc |(moebius d : ℝ)| * coprimeSquarefreeDensity (d * m) ≤ 1 * 1 :=
            mul_le_mul h1 h2 h3 zero_le_one
        _ = 1 := one_mul 1
  · rw [abs_zero]; positivity

theorem summable_jordanDensityTerm (m : ℕ) : Summable (jordanDensityTerm m) :=
  Summable.of_norm_bounded ((Real.summable_nat_pow_inv (p := 3)).mpr (by norm_num)) fun d => by
    rw [Real.norm_eq_abs]; exact abs_jordanDensityTerm_le m d

/-- The density `δ(m) = Σ_{(d,m)=1} μ(d) D(dm)/d³` of `μ(q)² J₂(q)/q² [(q,m)=1]`. -/
def jordanCoprimeDensity (m : ℕ) : ℝ := ∑' d, jordanDensityTerm m d

theorem abs_jordanCoprimeDensity_le (m : ℕ) :
    |jordanCoprimeDensity m| ≤ ∑' d : ℕ, ((d : ℝ) ^ 3)⁻¹ := by
  have h := norm_tsum_le_tsum_norm (summable_jordanDensityTerm m).norm
  rw [Real.norm_eq_abs] at h
  refine h.trans (Summable.tsum_le_tsum (fun d => ?_) (summable_jordanDensityTerm m).norm
    ((Real.summable_nat_pow_inv (p := 3)).mpr (by norm_num)))
  rw [Real.norm_eq_abs]; exact abs_jordanDensityTerm_le m d

/-- The tail beyond `N`: `|Σ_{d > N} [(d,m)=1] μ(d) D(dm)/d³| ≤ ζ(2)/(N+1)`. -/
theorem abs_tsum_jordanDensityTerm_tail_le (m N : ℕ) :
    |∑' i, jordanDensityTerm m (i + (N + 1))| ≤
      (∑' i : ℕ, (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹) / ((N : ℝ) + 1) := by
  have hsum2 : Summable (fun i : ℕ => (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by norm_num))
  have hN1 : (0 : ℝ) < (N : ℝ) + 1 := by positivity
  have hb : ∀ i : ℕ, ‖jordanDensityTerm m (i + (N + 1))‖ ≤
      ((N : ℝ) + 1)⁻¹ * (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
    intro i
    rw [Real.norm_eq_abs]
    refine (abs_jordanDensityTerm_le m _).trans ?_
    have hi1 : (0 : ℝ) < ((i + 1 : ℕ) : ℝ) := by positivity
    have hk : (((i + (N + 1) : ℕ) : ℝ)) = (i : ℝ) + (N : ℝ) + 1 := by push_cast; ring
    have hk1 : ((i + 1 : ℕ) : ℝ) = (i : ℝ) + 1 := by push_cast; ring
    rw [hk, hk1, ← mul_inv]
    apply inv_anti₀ (by positivity)
    have h1 : (N : ℝ) + 1 ≤ (i : ℝ) + N + 1 := by linarith [(Nat.cast_nonneg i : (0 : ℝ) ≤ i)]
    have h2 : ((i : ℝ) + 1) ^ 2 ≤ ((i : ℝ) + N + 1) ^ 2 :=
      pow_le_pow_left₀ (by positivity) (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)]) 2
    calc ((N : ℝ) + 1) * ((i : ℝ) + 1) ^ 2 ≤ ((i : ℝ) + N + 1) * ((i : ℝ) + N + 1) ^ 2 :=
          mul_le_mul h1 h2 (by positivity) (by positivity)
      _ = ((i : ℝ) + N + 1) ^ 3 := by ring
  have hbs : Summable (fun i : ℕ => ((N : ℝ) + 1)⁻¹ * (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹) :=
    hsum2.mul_left _
  have hsv : Summable (fun i : ℕ => jordanDensityTerm m (i + (N + 1))) :=
    Summable.of_norm_bounded hbs hb
  calc |∑' i, jordanDensityTerm m (i + (N + 1))|
      ≤ ∑' i, ‖jordanDensityTerm m (i + (N + 1))‖ := norm_tsum_le_tsum_norm hsv.norm
    _ ≤ ∑' i : ℕ, ((N : ℝ) + 1)⁻¹ * (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹ :=
        Summable.tsum_le_tsum hb hsv.norm hbs
    _ = (∑' i : ℕ, (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹) / ((N : ℝ) + 1) := by
        rw [tsum_mul_left, div_eq_inv_mul]

/-- `Σ_{d ≤ N} 1/d² ≤ ζ(2)`. -/
theorem sum_Icc_inv_sq_le_tsum (N : ℕ) :
    ∑ d ∈ Icc 1 N, ((d : ℝ) ^ 2)⁻¹ ≤ ∑' i : ℕ, (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
  have hsum2 : Summable (fun i : ℕ => (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹) :=
    (summable_nat_add_iff 1).mpr (Real.summable_nat_pow_inv.mpr (by norm_num))
  have h : ∑ i ∈ range N, (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹ = ∑ d ∈ Icc 1 N, ((d : ℝ) ^ 2)⁻¹ := by
    rw [Finset.range_eq_Ico, Finset.sum_Ico_add' (fun d : ℕ => ((d : ℝ) ^ 2)⁻¹) 0 N 1, zero_add,
      Finset.Ico_add_one_right_eq_Icc]
  rw [← h]
  exact hsum2.sum_le_tsum _ fun i _ => by positivity

/-- `Σ_{d ≤ N} d^{-3/2} ≤ ζ(3/2)`. -/
theorem sum_Icc_rpow_neg_three_halves_le (N : ℕ) :
    ∑ d ∈ Icc 1 N, (d : ℝ) ^ (-(3 / 2 : ℝ)) ≤ ∑' n : ℕ, (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
  (Real.summable_nat_rpow.mpr (by norm_num)).sum_le_tsum _
    fun n _ => Real.rpow_nonneg (Nat.cast_nonneg _) _

/-! ### Fibre masses -/

/-- The Jordan fibre mass `U_m(N,j) = Σ_{q ≤ N, ⌊N/q⌋ = j, (q,m)=1} μ(q)² J₂(q)/q²`. -/
def jordanFibreMass (m N j : ℕ) : ℝ :=
  ∑ q ∈ (Icc 1 N).filter (fun q => N / q = j),
    if Nat.Coprime q m then
      (moebius q : ℝ) ^ 2 * (BiScaleUncertainty.jordanTotient2 q / (q : ℝ) ^ 2) else 0

/-- Multiples of `d` in a fibre of `N` are `d` times the fibre of `⌊N/d⌋`. -/
theorem sum_fibre_dvd_eq {N j d : ℕ} (hd : 0 < d) (F : ℕ → ℝ) :
    ∑ q ∈ (Icc 1 N).filter (fun q => N / q = j ∧ d ∣ q), F q =
      ∑ q' ∈ (Icc 1 (N / d)).filter (fun q' => N / d / q' = j), F (d * q') := by
  have hbij : (Icc 1 N).filter (fun q => N / q = j ∧ d ∣ q) =
      ((Icc 1 (N / d)).filter (fun q' => N / d / q' = j)).image (fun q' => d * q') := by
    ext q
    simp only [mem_filter, mem_Icc, mem_image]
    constructor
    · rintro ⟨⟨hq1, hqN⟩, hj, ⟨q', rfl⟩⟩
      have hq'1 : 1 ≤ q' := by
        rcases Nat.eq_zero_or_pos q' with rfl | h
        · simp at hq1
        · exact h
      refine ⟨q', ⟨⟨hq'1, (Nat.le_div_iff_mul_le hd).mpr (by linarith [mul_comm d q'])⟩, ?_⟩, rfl⟩
      rw [Nat.div_div_eq_div_mul]
      exact hj
    · rintro ⟨q', ⟨⟨hq'1, hq'N⟩, hj⟩, rfl⟩
      have hle := (Nat.le_div_iff_mul_le hd).mp hq'N
      refine ⟨⟨Nat.mul_pos hd hq'1, by linarith [mul_comm d q']⟩, ?_, dvd_mul_right d q'⟩
      rw [← Nat.div_div_eq_div_mul]
      exact hj
  rw [hbij, sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hd h)]

/-- On `q = dq'` with `(d,m)=1`: `[(dq',m)=1] μ(dq')² μ(d)/d² = μ(d)/d² [(q',dm)=1] μ(q')²`. -/
theorem moebius_sq_mul_coprime_eq {d m q' : ℕ} (hdm : Nat.Coprime d m) :
    (if Nat.Coprime (d * q') m then (moebius (d * q') : ℝ) ^ 2 else 0) *
        ((moebius d : ℝ) / (d : ℝ) ^ 2) =
      (moebius d : ℝ) / (d : ℝ) ^ 2 * coprimeSquarefreeIndicator (d * m) q' := by
  unfold coprimeSquarefreeIndicator
  by_cases hdq : Nat.Coprime d q'
  · by_cases hq'm : Nat.Coprime q' m
    · have h1 : Nat.Coprime (d * q') m := Nat.coprime_mul_iff_left.mpr ⟨hdm, hq'm⟩
      have h2 : Nat.Coprime (d * m) q' :=
        Nat.coprime_mul_iff_left.mpr ⟨hdq, hq'm.symm⟩
      rw [if_pos h1, if_pos h2, isMultiplicative_moebius.map_mul_of_coprime hdq]
      push_cast
      rcases moebius_eq_or d with h | h | h <;> simp only [h] <;> push_cast <;> ring
    · rw [if_neg (fun h => hq'm (Nat.coprime_mul_iff_left.mp h).2),
        if_neg (fun h => hq'm (Nat.coprime_mul_iff_left.mp h).2.symm)]
      ring
  · have hz : (moebius (d * q') : ℝ) = 0 := by
      obtain ⟨p, hp, hpd, hpq⟩ := Nat.Prime.not_coprime_iff_dvd.mp hdq
      have hsq : ¬ Squarefree (d * q') := fun hs =>
        hp.one_lt.ne' (Nat.isUnit_iff.mp (hs p (Nat.mul_dvd_mul hpd hpq)))
      simp [moebius_eq_zero_of_not_squarefree hsq]
    rw [hz, if_neg (fun h => hdq (Nat.coprime_mul_iff_left.mp h).1)]
    split_ifs <;> simp

/-- **Fibre masses as coprime squarefree counts.** `U_m(N,j) = Σ_{d ≤ N} [(d,m)=1] μ(d)/d² ·
#{q' : ⌊⌊N/d⌋/q'⌋ = j, q' squarefree, (q', dm) = 1}`. -/
theorem jordanFibreMass_eq (m N j : ℕ) :
    jordanFibreMass m N j = ∑ d ∈ Icc 1 N,
      (if Nat.Coprime d m then (moebius d : ℝ) / (d : ℝ) ^ 2 else 0) *
        ∑ q' ∈ (Icc 1 (N / d)).filter (fun q' => N / d / q' = j),
          coprimeSquarefreeIndicator (d * m) q' := by
  unfold jordanFibreMass
  have hexp : ∀ q ∈ (Icc 1 N).filter (fun q => N / q = j),
      (if Nat.Coprime q m then
        (moebius q : ℝ) ^ 2 * (BiScaleUncertainty.jordanTotient2 q / (q : ℝ) ^ 2) else 0) =
        ∑ d ∈ Icc 1 N, if d ∣ q then
          (if Nat.Coprime q m then (moebius q : ℝ) ^ 2 else 0) * ((moebius d : ℝ) / (d : ℝ) ^ 2)
          else 0 := by
    intro q hq
    obtain ⟨hq1, hqN⟩ := mem_Icc.mp (mem_filter.mp hq).1
    have hdiv : q.divisors = (Icc 1 N).filter (fun d => d ∣ q) := by
      ext d
      simp only [Nat.mem_divisors, mem_filter, mem_Icc]
      constructor
      · rintro ⟨hdq, -⟩
        exact ⟨⟨Nat.pos_of_dvd_of_pos hdq (by omega), (Nat.le_of_dvd (by omega) hdq).trans hqN⟩,
          hdq⟩
      · rintro ⟨-, hdq⟩; exact ⟨hdq, by omega⟩
    rw [← sum_filter, ← hdiv]
    split_ifs with hqm
    · rw [jordanTotient2_div_sq (by omega), mul_sum]
    · simp
  rw [sum_congr rfl hexp, sum_comm]
  refine sum_congr rfl fun d hd => ?_
  have hd0 : 0 < d := (mem_Icc.mp hd).1
  rw [← sum_filter, filter_filter, sum_fibre_dvd_eq hd0, mul_sum]
  refine sum_congr rfl fun q' _ => ?_
  by_cases hdm : Nat.Coprime d m
  · rw [if_pos hdm]
    exact moebius_sq_mul_coprime_eq hdm
  · rw [if_neg hdm, zero_mul,
      if_neg (fun h => hdm (Nat.coprime_mul_iff_left.mp h).1), zero_mul]

/-- The coprime squarefree count on the fibre `⌊t/q'⌋ = j` is a difference of two counts. -/
theorem sum_fibre_coprimeSquarefreeIndicator (n t j : ℕ) (hj : 1 ≤ j) :
    ∑ q ∈ (Icc 1 t).filter (fun q => t / q = j), coprimeSquarefreeIndicator n q =
      coprimeSquarefreeCount n (t / j) - coprimeSquarefreeCount n (t / (j + 1)) := by
  rw [filter_div_eq_Ioc hj]
  unfold coprimeSquarefreeCount
  have h := Finset.sum_Ioc_consecutive (coprimeSquarefreeIndicator n) (Nat.zero_le (t / (j + 1)))
    (Nat.div_le_div_left (by omega : j ≤ j + 1) (by omega : 0 < j) : t / (j + 1) ≤ t / j)
  rw [Ioc_zero_eq_Icc_one, Ioc_zero_eq_Icc_one] at h
  linarith

/-- The count error for every `X`, including `X = 0`. -/
theorem abs_coprimeSquarefreeCount_sub_le' {n : ℕ} (hn : Squarefree n) (X : ℕ) :
    |coprimeSquarefreeCount n X - coprimeSquarefreeDensity n * X| ≤
      (n.divisors.card : ℝ) * Real.sqrt X *
        (2 + ∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ)) + Real.log X) := by
  rcases Nat.eq_zero_or_pos X with rfl | hX
  · simp [coprimeSquarefreeCount]
  · exact abs_coprimeSquarefreeCount_sub_le hn hX

/-- `d · √(N/d) / d² = √N · d^{-3/2}`. -/
theorem sqrt_div_mul_eq {N d : ℕ} (hd : 1 ≤ d) :
    (d : ℝ) * Real.sqrt ((N : ℝ) / d) * ((d : ℝ) ^ 2)⁻¹ =
      Real.sqrt N * (d : ℝ) ^ (-(3 / 2 : ℝ)) := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hsd : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd0
  rw [Real.sqrt_div' _ hd0.le]
  have hr : (d : ℝ) ^ (-(3 / 2 : ℝ)) = ((d : ℝ) * Real.sqrt d)⁻¹ := by
    rw [Real.rpow_neg hd0.le, Real.sqrt_eq_rpow, ← Real.rpow_one_add' hd0.le (by norm_num)]
    norm_num
  rw [hr]
  field_simp
  try ring

/-- **Fibre masses.** For squarefree `m`, `j ≥ 1`, `N ≥ 1`:
`|U_m(N,j) − δ(m) N/(j(j+1))| ≤ 2 ζ(3/2) τ(m) √N (2 + ζ(3/2) + log N) + 3 ζ(2)`. -/
theorem abs_jordanFibreMass_sub_le {m N j : ℕ} (hm : Squarefree m) (hj : 1 ≤ j) (hN : 1 ≤ N) :
    |jordanFibreMass m N j - jordanCoprimeDensity m * N / ((j : ℝ) * (j + 1))| ≤
      2 * (∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ))) * (m.divisors.card : ℝ) * Real.sqrt N *
          (2 + ∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ)) + Real.log N) +
        3 * ∑' i : ℕ, (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹ := by
  have hZ0 : 0 ≤ ∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ)) :=
    tsum_nonneg fun k => Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hZ20 : 0 ≤ ∑' i : ℕ, (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹ := tsum_nonneg fun i => by positivity
  generalize hZ : ∑' k : ℕ, (k : ℝ) ^ (-(3 / 2 : ℝ)) = Z at hZ0 ⊢
  generalize hZ2 : ∑' i : ℕ, (((i + 1 : ℕ) : ℝ) ^ 2)⁻¹ = Z2 at hZ20 ⊢
  have hNR : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by linarith
  have hlN : 0 ≤ Real.log N := Real.log_nonneg hNR
  have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj
  have hjj : (0 : ℝ) < (j : ℝ) * (j + 1) := by positivity
  have hτm : (0 : ℝ) ≤ (m.divisors.card : ℝ) := Nat.cast_nonneg _
  -- the density as a finite sum plus a tail
  have hsumv := summable_jordanDensityTerm m
  have hv0 : jordanDensityTerm m 0 = 0 := by simp [jordanDensityTerm]
  have hrange : ∑ i ∈ range (N + 1), jordanDensityTerm m i =
      ∑ d ∈ Icc 1 N, jordanDensityTerm m d := by
    have h : range (N + 1) = insert 0 (Icc 1 N) := by
      ext n; simp only [mem_range, mem_insert, mem_Icc]; omega
    rw [h, sum_insert (by simp), hv0, zero_add]
  have hsplit := hsumv.sum_add_tsum_nat_add (N + 1)
  rw [hrange] at hsplit
  have htail := abs_tsum_jordanDensityTerm_tail_le m N
  rw [hZ2] at htail
  -- per-`d` comparison
  have hpt : ∀ d ∈ Icc 1 N,
      |(if Nat.Coprime d m then (moebius d : ℝ) / (d : ℝ) ^ 2 else 0) *
          ∑ q' ∈ (Icc 1 (N / d)).filter (fun q' => N / d / q' = j),
            coprimeSquarefreeIndicator (d * m) q' -
        jordanDensityTerm m d * N / ((j : ℝ) * (j + 1))| ≤
      2 * (m.divisors.card : ℝ) * (2 + Z + Real.log N) * (Real.sqrt N * (d : ℝ) ^ (-(3 / 2 : ℝ))) +
        2 * ((d : ℝ) ^ 2)⁻¹ := by
    intro d hd
    have hd1 := (mem_Icc.mp hd).1
    have hdN := (mem_Icc.mp hd).2
    have hd0 : (0 : ℝ) < d := by exact_mod_cast hd1
    have hd2 : (0 : ℝ) < (d : ℝ) ^ 2 := by positivity
    have hR0 : 0 ≤ 2 * (m.divisors.card : ℝ) * (2 + Z + Real.log N) *
        (Real.sqrt N * (d : ℝ) ^ (-(3 / 2 : ℝ))) + 2 * ((d : ℝ) ^ 2)⁻¹ :=
      add_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hτm) (by linarith))
        (mul_nonneg (Real.sqrt_nonneg _) (Real.rpow_nonneg hd0.le _))) (by positivity)
    unfold jordanDensityTerm
    by_cases hdm : Nat.Coprime d m
    · rw [if_pos hdm, if_pos hdm]
      by_cases hsd : Squarefree d
      · have hn : Squarefree (d * m) := Nat.squarefree_mul_iff.mpr ⟨hdm, hsd, hm⟩
        rw [sum_fibre_coprimeSquarefreeIndicator _ _ _ hj]
        set X1 := N / d / j
        set X2 := N / d / (j + 1)
        have e1 := abs_coprimeSquarefreeCount_sub_le' hn X1
        have e2 := abs_coprimeSquarefreeCount_sub_le' hn X2
        rw [hZ] at e1 e2
        -- `τ(dm) ≤ d τ(m)`
        have hτ : ((d * m).divisors.card : ℝ) ≤ (d : ℝ) * (m.divisors.card : ℝ) := by
          rw [Nat.Coprime.card_divisors_mul hdm]
          push_cast
          exact mul_le_mul_of_nonneg_right (by exact_mod_cast Nat.card_divisors_le_self d) hτm
        -- `X_i ≤ N/d`
        have hX1 : (X1 : ℝ) ≤ (N : ℝ) / d := by
          have : ((N / d / j : ℕ) : ℝ) ≤ ((N / d : ℕ) : ℝ) := by
            exact_mod_cast Nat.div_le_self _ _
          exact this.trans Nat.cast_div_le
        have hX2 : (X2 : ℝ) ≤ (N : ℝ) / d := by
          have : ((N / d / (j + 1) : ℕ) : ℝ) ≤ ((N / d : ℕ) : ℝ) := by
            exact_mod_cast Nat.div_le_self _ _
          exact this.trans Nat.cast_div_le
        have hlog : ∀ X : ℕ, (X : ℝ) ≤ (N : ℝ) / d →
            ((d * m).divisors.card : ℝ) * Real.sqrt X * (2 + Z + Real.log X) ≤
              (m.divisors.card : ℝ) * (2 + Z + Real.log N) *
                ((d : ℝ) * Real.sqrt ((N : ℝ) / d)) := by
          intro X hX
          have hdR1 : (1 : ℝ) ≤ d := by exact_mod_cast hd1
          have hXN : (X : ℝ) ≤ N := hX.trans (div_le_self hN0.le hdR1)
          have hl : Real.log X ≤ Real.log N := by
            rcases Nat.eq_zero_or_pos X with h0 | hXp
            · rw [h0, Nat.cast_zero, Real.log_zero]; exact hlN
            · exact Real.log_le_log (by exact_mod_cast hXp) hXN
          have hlX0 := log_natCast_nonneg X
          have hs : Real.sqrt X ≤ Real.sqrt ((N : ℝ) / d) := Real.sqrt_le_sqrt hX
          have hτ0 : (0 : ℝ) ≤ ((d * m).divisors.card : ℝ) := Nat.cast_nonneg _
          calc ((d * m).divisors.card : ℝ) * Real.sqrt X * (2 + Z + Real.log X)
              ≤ ((d : ℝ) * (m.divisors.card : ℝ)) * Real.sqrt ((N : ℝ) / d) *
                  (2 + Z + Real.log N) :=
                mul_le_mul (mul_le_mul hτ hs (Real.sqrt_nonneg _) (by positivity)) (by linarith)
                  (by linarith) (by positivity)
            _ = (m.divisors.card : ℝ) * (2 + Z + Real.log N) *
                  ((d : ℝ) * Real.sqrt ((N : ℝ) / d)) := by ring
        -- the rounding of the fibre length
        have hround : |((X1 : ℝ) - X2) - (N : ℝ) / (d * (j * (j + 1)))| ≤ 1 := by
          have h1 : (X1 : ℝ) = (N : ℝ) / (d * j) - Int.fract ((N : ℝ) / ((d * j : ℕ) : ℝ)) := by
            rw [show X1 = N / (d * j) from Nat.div_div_eq_div_mul N d j, natCast_div_eq_sub_fract]
            push_cast; ring
          have h2 : (X2 : ℝ) = (N : ℝ) / (d * (j + 1)) -
              Int.fract ((N : ℝ) / ((d * (j + 1) : ℕ) : ℝ)) := by
            rw [show X2 = N / (d * (j + 1)) from Nat.div_div_eq_div_mul N d (j + 1),
              natCast_div_eq_sub_fract]
            push_cast; ring
          have he : (N : ℝ) / (d * j) - (N : ℝ) / (d * (j + 1)) = (N : ℝ) / (d * (j * (j + 1))) := by
            field_simp; ring
          rw [h1, h2]
          have f1 := Int.fract_nonneg ((N : ℝ) / ((d * j : ℕ) : ℝ))
          have f2 := Int.fract_lt_one ((N : ℝ) / ((d * j : ℕ) : ℝ))
          have f3 := Int.fract_nonneg ((N : ℝ) / ((d * (j + 1) : ℕ) : ℝ))
          have f4 := Int.fract_lt_one ((N : ℝ) / ((d * (j + 1) : ℕ) : ℝ))
          rw [abs_le]
          constructor <;> linarith
        have hD0 := coprimeSquarefreeDensity_nonneg (d * m)
        have hD1 := coprimeSquarefreeDensity_le_one (d * m)
        have hsplit' : (moebius d : ℝ) / (d : ℝ) ^ 2 *
            (coprimeSquarefreeCount (d * m) X1 - coprimeSquarefreeCount (d * m) X2) -
            (moebius d : ℝ) * coprimeSquarefreeDensity (d * m) / (d : ℝ) ^ 3 * N / ((j : ℝ) * (j + 1)) =
            (moebius d : ℝ) / (d : ℝ) ^ 2 *
              ((coprimeSquarefreeCount (d * m) X1 - coprimeSquarefreeDensity (d * m) * X1) -
                (coprimeSquarefreeCount (d * m) X2 - coprimeSquarefreeDensity (d * m) * X2) +
                coprimeSquarefreeDensity (d * m) * (((X1 : ℝ) - X2) - (N : ℝ) / (d * (j * (j + 1))))) := by
          have hdne : (d : ℝ) ≠ 0 := hd0.ne'
          have hjne : (j : ℝ) ≠ 0 := by linarith
          have hj1ne : (j : ℝ) + 1 ≠ 0 := by linarith
          field_simp
          ring
        rw [hsplit', abs_mul]
        have hμ : |(moebius d : ℝ) / (d : ℝ) ^ 2| ≤ ((d : ℝ) ^ 2)⁻¹ := by
          rw [abs_div, abs_of_pos hd2, div_eq_mul_inv]
          exact mul_le_of_le_one_left (inv_nonneg.mpr hd2.le) (by exact_mod_cast abs_moebius_le_one)
        have hin : |(coprimeSquarefreeCount (d * m) X1 - coprimeSquarefreeDensity (d * m) * X1) -
            (coprimeSquarefreeCount (d * m) X2 - coprimeSquarefreeDensity (d * m) * X2) +
            coprimeSquarefreeDensity (d * m) * (((X1 : ℝ) - X2) - (N : ℝ) / (d * (j * (j + 1))))| ≤
            2 * ((m.divisors.card : ℝ) * (2 + Z + Real.log N) *
              ((d : ℝ) * Real.sqrt ((N : ℝ) / d))) + 2 := by
          have e3 : |coprimeSquarefreeDensity (d * m) * (((X1 : ℝ) - X2) - (N : ℝ) / (d * (j * (j + 1))))|
              ≤ 1 := by
            rw [abs_mul, abs_of_nonneg hD0]
            calc coprimeSquarefreeDensity (d * m) * |((X1 : ℝ) - X2) - (N : ℝ) / (d * (j * (j + 1)))|
                ≤ 1 * 1 := mul_le_mul hD1 hround (abs_nonneg _) zero_le_one
              _ = 1 := one_mul 1
          have e1' := e1.trans (hlog X1 hX1)
          have e2' := e2.trans (hlog X2 hX2)
          calc _ ≤ |coprimeSquarefreeCount (d * m) X1 - coprimeSquarefreeDensity (d * m) * X1| +
                |coprimeSquarefreeCount (d * m) X2 - coprimeSquarefreeDensity (d * m) * X2| +
                |coprimeSquarefreeDensity (d * m) * (((X1 : ℝ) - X2) - (N : ℝ) / (d * (j * (j + 1))))| :=
                (abs_add_le _ _).trans (add_le_add (abs_sub _ _) le_rfl)
            _ ≤ _ := by linarith
        have hin0 : 0 ≤ 2 * ((m.divisors.card : ℝ) * (2 + Z + Real.log N) *
            ((d : ℝ) * Real.sqrt ((N : ℝ) / d))) + 2 :=
          add_nonneg (mul_nonneg (by norm_num) (mul_nonneg (mul_nonneg hτm (by linarith))
            (mul_nonneg hd0.le (Real.sqrt_nonneg _)))) (by norm_num)
        calc |(moebius d : ℝ) / (d : ℝ) ^ 2| * |_|
            ≤ ((d : ℝ) ^ 2)⁻¹ * (2 * ((m.divisors.card : ℝ) * (2 + Z + Real.log N) *
                ((d : ℝ) * Real.sqrt ((N : ℝ) / d))) + 2) :=
              mul_le_mul hμ hin (abs_nonneg _) (inv_nonneg.mpr hd2.le)
          _ = 2 * (m.divisors.card : ℝ) * (2 + Z + Real.log N) *
                ((d : ℝ) * Real.sqrt ((N : ℝ) / d) * ((d : ℝ) ^ 2)⁻¹) + 2 * ((d : ℝ) ^ 2)⁻¹ := by
              ring
          _ = _ := by rw [sqrt_div_mul_eq hd1]
      · have hz : (moebius d : ℝ) = 0 := by
          rw [moebius_eq_zero_of_not_squarefree hsd]; simp
        rw [hz]
        simp only [zero_div, zero_mul, sub_zero, abs_zero]
        exact hR0
    · rw [if_neg hdm, if_neg hdm, zero_mul, zero_mul, zero_div, sub_zero, abs_zero]
      exact hR0
  -- assemble
  have hmain : jordanCoprimeDensity m * N / ((j : ℝ) * (j + 1)) =
      ∑ d ∈ Icc 1 N, jordanDensityTerm m d * N / ((j : ℝ) * (j + 1)) +
        (∑' i, jordanDensityTerm m (i + (N + 1))) * N / ((j : ℝ) * (j + 1)) := by
    rw [jordanCoprimeDensity, ← hsplit, add_mul, add_div, sum_mul, sum_div]
  rw [jordanFibreMass_eq, hmain, ← sub_sub, ← sum_sub_distrib]
  have hsumd : ∑ d ∈ Icc 1 N, (2 * (m.divisors.card : ℝ) * (2 + Z + Real.log N) *
      (Real.sqrt N * (d : ℝ) ^ (-(3 / 2 : ℝ))) + 2 * ((d : ℝ) ^ 2)⁻¹) ≤
      2 * Z * (m.divisors.card : ℝ) * Real.sqrt N * (2 + Z + Real.log N) + 2 * Z2 := by
    rw [sum_add_distrib, ← mul_sum, ← mul_sum, ← mul_sum]
    have h32 := sum_Icc_rpow_neg_three_halves_le N
    have h2 := sum_Icc_inv_sq_le_tsum N
    rw [hZ] at h32
    rw [hZ2] at h2
    have hc : 0 ≤ 2 * (m.divisors.card : ℝ) * (2 + Z + Real.log N) * Real.sqrt N :=
      mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) hτm) (by linarith)) (Real.sqrt_nonneg _)
    have e : 2 * (m.divisors.card : ℝ) * (2 + Z + Real.log N) *
        (Real.sqrt N * ∑ d ∈ Icc 1 N, (d : ℝ) ^ (-(3 / 2 : ℝ))) =
        2 * (m.divisors.card : ℝ) * (2 + Z + Real.log N) * Real.sqrt N *
          ∑ d ∈ Icc 1 N, (d : ℝ) ^ (-(3 / 2 : ℝ)) := by ring
    rw [e]
    have := mul_le_mul_of_nonneg_left h32 hc
    nlinarith
  have htail' : |(∑' i, jordanDensityTerm m (i + (N + 1))) * N / ((j : ℝ) * (j + 1))| ≤ Z2 := by
    rw [abs_div, abs_mul, abs_of_pos hjj, abs_of_pos hN0]
    rw [div_le_iff₀ hjj]
    have h1 : |∑' i, jordanDensityTerm m (i + (N + 1))| * N ≤ Z2 := by
      have := mul_le_mul_of_nonneg_right htail hN0.le
      calc |∑' i, jordanDensityTerm m (i + (N + 1))| * N ≤ Z2 / ((N : ℝ) + 1) * N := this
        _ ≤ Z2 := by
            rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
            nlinarith
    have hjj1 : (1 : ℝ) ≤ (j : ℝ) * (j + 1) := by nlinarith
    nlinarith
  calc _ ≤ |∑ d ∈ Icc 1 N, ((if Nat.Coprime d m then (moebius d : ℝ) / (d : ℝ) ^ 2 else 0) *
          ∑ q' ∈ (Icc 1 (N / d)).filter (fun q' => N / d / q' = j),
            coprimeSquarefreeIndicator (d * m) q' -
          jordanDensityTerm m d * N / ((j : ℝ) * (j + 1)))| +
        |(∑' i, jordanDensityTerm m (i + (N + 1))) * N / ((j : ℝ) * (j + 1))| := abs_sub _ _
    _ ≤ (2 * Z * (m.divisors.card : ℝ) * Real.sqrt N * (2 + Z + Real.log N) + 2 * Z2) + Z2 :=
        add_le_add ((abs_sum_le_sum_abs _ _).trans ((sum_le_sum hpt).trans hsumd)) htail'
    _ = _ := by ring

end

end GaloisForLFunctions.BezoutValuationIncidence
