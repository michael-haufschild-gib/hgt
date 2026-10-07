import GaloisForLFunctions.RHTower.WeilWorkSingularArithmeticSharpReciprocal
import GaloisForLFunctions.RHTower.Sieve.DirichletMeanValueSharp
import GaloisForLFunctions.RHTower.Sieve.ConvolutionSummatorySwap
import GaloisForLFunctions.RHTower.DivisorBound

/-!
# Square mass of the literal reciprocal and zeta quotient

Full-cone Weil positivity supplies the all-twist sharp reciprocal estimate.
The finite Dirichlet-polynomial mean-value lower bound then gives square mass
`O(N^(1+ε))`. Divisor Cauchy–Schwarz transfers this to `1 * μλ`.
These are coefficient estimates, with no claim of uniform quotient boundedness.
-/

open Complex MeasureTheory Set
open GaloisForLFunctions.HTGeometry
open RHTower.Sieve

noncomputable section

namespace RHTower.WeilSingularArithmetic

private theorem finite_square_mass_le (N : ℕ) (a : Fin N → ℂ) {B : ℝ}
    (hP : ∀ t ∈ Icc (0 : ℝ) (208 * ((N : ℝ) + 1)), ‖dirPoly N a t‖ ≤ B) :
    ∑ m : Fin N, ‖a m‖ ^ 2 ≤ 2 * B ^ 2 := by
  let T : ℝ := 208 * ((N : ℝ) + 1)
  let S : ℝ := ∑ m : Fin N, ‖a m‖ ^ 2
  have hT : 0 < T := by dsimp [T]; positivity
  have hS : 0 ≤ S := Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hmass := dirichlet_meanValue_sharp N a T
  have hweight : ∑ m : Fin N, ((m : ℕ) + 1 : ℝ) * ‖a m‖ ^ 2 ≤ (N : ℝ) * S := by
    dsimp only [S]
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro m _
    apply mul_le_mul_of_nonneg_right _ (sq_nonneg _)
    exact_mod_cast m.isLt
  have hlow := (abs_le.mp hmass).1
  have hupper : (∫ t in (0 : ℝ)..T, ‖dirPoly N a t‖ ^ 2) ≤ T * B ^ 2 := by
    have hb := intervalIntegral.norm_integral_le_of_norm_le_const
      (a := (0 : ℝ)) (b := T) (f := fun t => ‖dirPoly N a t‖ ^ 2) (C := B ^ 2)
      (fun t ht => by
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        apply pow_le_pow_left₀ (norm_nonneg _) _ 2
        exact hP t (by
          have := Set.uIoc_subset_uIcc ht
          simpa only [Set.uIcc_of_le hT.le] using this))
    rw [Real.norm_eq_abs, abs_of_nonneg (intervalIntegral.integral_nonneg hT.le
      (fun _ _ => sq_nonneg _)), sub_zero, abs_of_pos hT] at hb
    nlinarith
  have hTS : T / 2 * S ≤ T * B ^ 2 := by
    dsimp only [S] at hweight ⊢
    have hNT : 104 * (N : ℝ) ≤ T / 2 := by dsimp [T]; linarith
    nlinarith [mul_le_mul_of_nonneg_right hNT hS]
  nlinarith

/-- Full positivity controls the square mass of the actual reciprocal
coefficients, uniformly in the arithmetic cutoff. -/
theorem exists_reciprocal_square_mass_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ∑ n ∈ Finset.Icc 1 N, ‖producerMobius (fun n => if 2 ≤ n then lam n else 0) n‖ ^ 2 ≤
        C * ((N : ℝ) + 1) ^ (1 + ε) := by
  let δ : ℝ := ε / 4
  have hδ : 0 < δ := by dsimp [δ]; positivity
  obtain ⟨C, hC, htwist⟩ := exists_sharp_twisted_reciprocal_sum_le hW hδ
  let b : ℕ → ℂ := producerMobius (fun n => if 2 ≤ n then lam n else 0)
  refine ⟨2 * (C * (210 : ℝ) ^ δ) ^ 2, by positivity, fun N => ?_⟩
  let B : ℝ := C * (210 : ℝ) ^ δ * ((N : ℝ) + 1) ^ (1 / 2 + 2 * δ)
  have hpoly : ∀ t : ℝ, dirPoly N (fun m => b ((m : ℕ) + 1)) t =
      ∑ n ∈ Finset.range (N + 1), b n * (n : ℂ) ^ (-(-t : ℂ) * I) := by
    intro t
    rw [dirPoly, Fin.sum_univ_eq_sum_range
      (fun n : ℕ => b (n + 1) * cexp (((t * Real.log ((n : ℝ) + 1) : ℝ) : ℂ) * I)) N,
      Finset.sum_range_succ']
    have hb0 : b 0 = 0 := producerMobius_zero _
    rw [hb0, zero_mul, add_zero]
    apply Finset.sum_congr rfl
    intro n _
    congr 1
    rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast Nat.succ_ne_zero n),
      ← Complex.natCast_log]
    congr 1
    push_cast
    ring
  have hP : ∀ t ∈ Icc (0 : ℝ) (208 * ((N : ℝ) + 1)),
      ‖dirPoly N (fun m => b ((m : ℕ) + 1)) t‖ ≤ B := by
    intro t ht
    rw [hpoly]
    have hh := htwist N (-t)
    rw [abs_neg, abs_of_nonneg ht.1] at hh
    have hbase : 2 + t ≤ 210 * ((N : ℝ) + 1) := by
      have := Nat.cast_nonneg (α := ℝ) N
      linarith [ht.2]
    calc
      _ ≤ C * ((N : ℝ) + 1) ^ (1 / 2 + δ) * (2 + t) ^ δ := by
        simpa only [Complex.ofReal_neg] using hh
      _ ≤ C * ((N : ℝ) + 1) ^ (1 / 2 + δ) * (210 * ((N : ℝ) + 1)) ^ δ := by
        gcongr
        linarith [ht.1]
      _ = B := by
        rw [Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 210) (by positivity)]
        dsimp [B]
        rw [show C * ((N : ℝ) + 1) ^ (1 / 2 + δ) *
            ((210 : ℝ) ^ δ * ((N : ℝ) + 1) ^ δ) =
          C * (210 : ℝ) ^ δ * (((N : ℝ) + 1) ^ (1 / 2 + δ) * ((N : ℝ) + 1) ^ δ) by ring,
          ← Real.rpow_add (by positivity)]
        congr 2
        ring
  have hmass := finite_square_mass_le N (fun m => b ((m : ℕ) + 1)) hP
  have hsum : (∑ n ∈ Finset.Icc 1 N, ‖b n‖ ^ 2) =
      ∑ m : Fin N, ‖b ((m : ℕ) + 1)‖ ^ 2 := by
    rw [Fin.sum_univ_eq_sum_range (fun n : ℕ => ‖b (n + 1)‖ ^ 2) N,
      ← Finset.Ico_add_one_right_eq_Icc,
      Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel, Nat.add_comm 1]
  rw [hsum]
  refine hmass.trans_eq ?_
  dsimp [B]
  rw [mul_pow, ← Real.rpow_mul_natCast (by positivity) (1 / 2 + 2 * δ) 2]
  have hexp : (1 / 2 + 2 * δ) * (2 : ℕ) = 1 + ε := by dsimp [δ]; ring
  rw [hexp]
  ring

private theorem norm_sq_convolution_one_le (b : ℕ → ℂ) (n : ℕ) :
    ‖LSeries.convolution 1 b n‖ ^ 2 ≤
      (n.divisors.card : ℝ) * LSeries.convolution 1 (fun k => ‖b k‖ ^ 2) n := by
  classical
  have hc : n.divisorsAntidiagonal.card = n.divisors.card := by
    rw [Finset.card_eq_sum_ones, Finset.card_eq_sum_ones,
      ← Nat.sum_divisorsAntidiagonal (fun _ _ => (1 : ℕ))]
  have hcs := Finset.sum_mul_sq_le_sq_mul_sq n.divisorsAntidiagonal
    (fun _ => (1 : ℝ)) (fun p => ‖b p.2‖)
  simp only [one_mul, one_pow, Finset.sum_const, nsmul_eq_mul, mul_one, hc] at hcs
  simp only [LSeries.convolution_def, Pi.one_apply, one_mul]
  exact (pow_le_pow_left₀ (norm_nonneg _) (norm_sum_le _ _) 2).trans hcs

/-- The literal zeta-quotient coefficients have square mass of exponent at most
one. The conclusion uses full positivity alone; it does not assert boundedness
of the actual quotient on a half-plane. -/
theorem exists_quotient_square_mass_le {lam : ℕ → ℝ} (hW : WeilPositiveFull lam)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ,
      ∑ n ∈ Finset.Icc 1 N,
        ‖LSeries.convolution 1 (producerMobius (fun n => if 2 ≤ n then lam n else 0)) n‖ ^ 2 ≤
        C * ((N : ℝ) + 1) ^ (1 + ε) := by
  let δ : ℝ := ε / 2
  have hδ : 0 < δ := by dsimp [δ]; positivity
  have ha : 0 ≤ 1 + δ := by linarith
  obtain ⟨C, hC, hmu⟩ := exists_reciprocal_square_mass_le hW hδ
  obtain ⟨D, hD, hdiv⟩ := card_divisors_le_const_mul_rpow hδ
  let b : ℕ → ℂ := producerMobius (fun n => if 2 ≤ n then lam n else 0)
  let v : ℕ → ℝ := fun n => ‖b n‖ ^ 2
  let Z : ℝ := ∑' m : ℕ, (m : ℝ) ^ (-(1 + δ))
  have hZs : Summable (fun m : ℕ => (m : ℝ) ^ (-(1 + δ))) :=
    Real.summable_nat_rpow.mpr (by linarith)
  have hZ : 0 ≤ Z := tsum_nonneg fun _ => by positivity
  refine ⟨D * C * (2 : ℝ) ^ (1 + δ) * Z, by positivity, fun N => ?_⟩
  have hv : ∀ n, 0 ≤ LSeries.convolution 1 v n := by
    intro n
    simp only [LSeries.convolution_def, Pi.one_apply, one_mul]
    exact Finset.sum_nonneg fun _ _ => sq_nonneg _
  have hpoint : ∀ n ∈ Finset.Icc 1 N, ‖LSeries.convolution 1 b n‖ ^ 2 ≤
      D * ((N : ℝ) + 1) ^ δ * LSeries.convolution 1 v n := by
    intro n hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hn
    refine (norm_sq_convolution_one_le b n).trans ?_
    apply mul_le_mul_of_nonneg_right _ (hv n)
    refine (hdiv n hn1).trans ?_
    apply mul_le_mul_of_nonneg_left _ hD.le
    apply Real.rpow_le_rpow (by positivity) _ hδ.le
    have : (n : ℝ) ≤ N := by exact_mod_cast hnN
    linarith
  have hmass : (∑ n ∈ Finset.Icc 1 N, LSeries.convolution 1 v n) ≤
      C * (2 : ℝ) ^ (1 + δ) * ((N : ℝ) + 1) ^ (1 + δ) * Z := by
    rw [sum_Icc_convolution_apply]
    simp only [Pi.one_apply, one_mul]
    have hterm : ∀ m ∈ Finset.Icc 1 N, (∑ n ∈ Finset.Icc 1 (N / m), v n) ≤
        C * (2 : ℝ) ^ (1 + δ) * ((N : ℝ) + 1) ^ (1 + δ) *
          (m : ℝ) ^ (-(1 + δ)) := by
      intro m hm
      obtain ⟨hm1, hmN⟩ := Finset.mem_Icc.mp hm
      have hm0 : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
      have hmN' : (m : ℝ) ≤ N := by exact_mod_cast hmN
      have hfloor : ((N / m : ℕ) : ℝ) + 1 ≤ 2 * ((N : ℝ) + 1) / m := by
        have hd := (le_div_iff₀ hm0).mp (Nat.cast_div_le (m := N) (n := m) (α := ℝ))
        apply (le_div_iff₀ hm0).mpr
        nlinarith
      calc
        _ ≤ C * (((N / m : ℕ) : ℝ) + 1) ^ (1 + δ) := hmu (N / m)
        _ ≤ C * (2 * ((N : ℝ) + 1) / m) ^ (1 + δ) := by
          apply mul_le_mul_of_nonneg_left _ hC
          exact Real.rpow_le_rpow (by positivity) hfloor ha
        _ = _ := by
          rw [Real.div_rpow (by positivity) (by positivity),
            Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) (by positivity),
            Real.rpow_neg (by positivity : (0 : ℝ) ≤ m)]
          ring
    calc
      _ ≤ ∑ m ∈ Finset.Icc 1 N,
          C * (2 : ℝ) ^ (1 + δ) * ((N : ℝ) + 1) ^ (1 + δ) *
            (m : ℝ) ^ (-(1 + δ)) := Finset.sum_le_sum hterm
      _ = C * (2 : ℝ) ^ (1 + δ) * ((N : ℝ) + 1) ^ (1 + δ) *
          ∑ m ∈ Finset.Icc 1 N, (m : ℝ) ^ (-(1 + δ)) := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (hZs.sum_le_tsum (Finset.Icc 1 N) (fun _ _ => by positivity)) (by positivity)
  calc
    _ ≤ ∑ n ∈ Finset.Icc 1 N, D * ((N : ℝ) + 1) ^ δ * LSeries.convolution 1 v n :=
      Finset.sum_le_sum hpoint
    _ = D * ((N : ℝ) + 1) ^ δ * ∑ n ∈ Finset.Icc 1 N, LSeries.convolution 1 v n := by
      rw [Finset.mul_sum]
    _ ≤ D * ((N : ℝ) + 1) ^ δ *
        (C * (2 : ℝ) ^ (1 + δ) * ((N : ℝ) + 1) ^ (1 + δ) * Z) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by
      rw [show D * ((N : ℝ) + 1) ^ δ *
          (C * (2 : ℝ) ^ (1 + δ) * ((N : ℝ) + 1) ^ (1 + δ) * Z) =
        (D * C * (2 : ℝ) ^ (1 + δ) * Z) *
          (((N : ℝ) + 1) ^ δ * ((N : ℝ) + 1) ^ (1 + δ)) by ring,
        ← Real.rpow_add (by positivity)]
      congr 2
      dsimp [δ]
      ring

end RHTower.WeilSingularArithmetic
