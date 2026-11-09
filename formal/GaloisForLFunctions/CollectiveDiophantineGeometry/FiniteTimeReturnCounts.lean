import GaloisForLFunctions.CollectiveDiophantineGeometry.ReciprocalRankBounds
import GaloisForLFunctions.RHTower.Sieve.HeathBrownSparseMeanValueBasic
import GaloisForLFunctions.RHTower.CCM.CCMPrimePoleFiniteCoherence

/-!
# Finite-time counts for returns of prime logarithms

Let `k` distinct prime logarithms have collective rank-`r` depth floor `Δ`
at coefficient height `N-1`. On any interval of length `T`, returns to any
specified torus point at precision `1/(2N)` have measure at most

`(5π/2) 4^k max(T/2, Δ⁻¹) / N^(k-r+1)`.

The estimate holds in both chord and radian precision. Once `T ≥ 2/Δ`,
the relative measure is at most `(5π/4) 4^k / N^(k-r+1)`.
The observation threshold is exactly a polynomial in coefficient height,
with degree `rC+r-1` for the collective exponent `C`.

All close smooth-number frequency differences lie in one rational subspace
of dimension at most `r-1`. Injective coordinate projection bounds their
weighted pair mass. The Fejér window estimate retains only those pairs;
a product of short geometric sums detects the actual return set.
-/

set_option autoImplicit false

noncomputable section
open Finset Real MeasureTheory ComplexConjugate
namespace GaloisForLFunctions.CollectiveDiophantineGeometry
open TranscendenceTheoryOfThePrimeOrbit
open RHTower.Matveev

/-- Integer difference of two smooth-number exponent vectors. -/
def smoothBoxDifference {k H : ℕ} (a b : Fin k → Fin (H + 1)) : Fin k → ℤ :=
  fun j => ((a j : ℕ) : ℤ) - ((b j : ℕ) : ℤ)

theorem abs_smoothBoxDifference_le {k H : ℕ} (a b : Fin k → Fin (H + 1)) (j : Fin k) :
    |smoothBoxDifference a b j| ≤ (H : ℤ) := by
  have ha := (a j).isLt
  have hb := (b j).isLt
  unfold smoothBoxDifference
  rw [abs_le]
  constructor <;> omega

/-- Logarithm of the smooth integer indexed by an exponent vector. -/
def smoothBoxFrequency {k H : ℕ} (p : Fin k → ℕ) (a : Fin k → Fin (H + 1)) : ℝ :=
  ∑ j, (a j : ℝ) * log (p j)

theorem primeLogForm_smoothBoxDifference {k H : ℕ}
    (p : Fin k → ℕ) (a b : Fin k → Fin (H + 1)) :
    primeLogForm p (smoothBoxDifference a b) = smoothBoxFrequency p a - smoothBoxFrequency p b := by
  simp only [primeLogForm, smoothBoxDifference, smoothBoxFrequency, Int.cast_sub,
    Int.cast_natCast, sub_mul, sum_sub_distrib]

/-- The common small-form span bounds all close ordered pairs in the exponent box. -/
theorem card_close_smoothBox_pairs_le {d r H : ℕ}
    (p : Fin (d + r + 1) → ℕ) (hp : Function.Injective p)
    (hprime : ∀ j, (p j).Prime) (hH : 1 ≤ H) :
    (univ.filter fun ab : (Fin (d + r + 1) → Fin (H + 1)) ×
      (Fin (d + r + 1) → Fin (H + 1)) =>
      |smoothBoxFrequency p ab.1 - smoothBoxFrequency p ab.2| <
        collectiveDepthFloor (r + 1) d (collectiveLogBound p) H).card ≤
      (H + 1) ^ (d + r + 1 + r) := by
  classical
  let Δ := collectiveDepthFloor (r + 1) d (collectiveLogBound p) H
  let V := Submodule.span ℚ
    (↑((nearRelationBox p H Δ).image HTGeometry.intVectorToRat) : Set (Fin (d + r + 1) → ℚ))
  have hdim : Module.finrank ℚ V ≤ r :=
    nearRelationBox_finrank_le_collective p hp hprime hH le_rfl
  -- Once the first vector is fixed, these coordinates determine the second.
  obtain ⟨φ, hφ⟩ := HTGeometry.exists_coordinateProjection_injective_on_submodule V
  let S := univ.filter fun ab : (Fin (d + r + 1) → Fin (H + 1)) ×
    (Fin (d + r + 1) → Fin (H + 1)) =>
      |smoothBoxFrequency p ab.1 - smoothBoxFrequency p ab.2| < Δ
  let f : ((Fin (d + r + 1) → Fin (H + 1)) ×
      (Fin (d + r + 1) → Fin (H + 1))) →
      (Fin (d + r + 1) → Fin (H + 1)) × (Fin (Module.finrank ℚ V) → Fin (H + 1)) :=
    fun ab => (ab.1, fun j => ab.2 (φ j))
  have hmem : ∀ ab ∈ S, HTGeometry.intVectorToRat (smoothBoxDifference ab.1 ab.2) ∈ V := by
    intro ab hab
    apply Submodule.subset_span
    apply mem_image.mpr
    refine ⟨smoothBoxDifference ab.1 ab.2, ?_, rfl⟩
    rw [mem_nearRelationBox]
    refine ⟨abs_smoothBoxDifference_le _ _, ?_⟩
    rw [primeLogForm_smoothBoxDifference]
    exact (mem_filter.mp hab).2
  have hf : Set.InjOn f S := by
    rintro ⟨a, b⟩ hab ⟨a', b'⟩ hab' heq
    have haa : a = a' := congrArg Prod.fst heq
    subst a'
    have hcoords := congrArg Prod.snd heq
    have hd : HTGeometry.intVectorToRat (smoothBoxDifference a b) =
        HTGeometry.intVectorToRat (smoothBoxDifference a b') := by
      apply hφ (hmem _ hab) (hmem _ hab')
      funext j
      have hj : b (φ j) = b' (φ j) := congrFun hcoords j
      simp only [HTGeometry.intVectorToRat, smoothBoxDifference, hj]
    have hbb : b = b' := by
      funext j
      apply Fin.ext
      have hj := congrFun (HTGeometry.intVectorToRat_injective hd) j
      dsimp [smoothBoxDifference] at hj
      exact_mod_cast (sub_right_inj.mp hj)
    exact Prod.ext rfl hbb
  calc S.card = (S.image f).card := (card_image_iff.mpr hf).symm
    _ ≤ Fintype.card ((Fin (d + r + 1) → Fin (H + 1)) ×
        (Fin (Module.finrank ℚ V) → Fin (H + 1))) := card_le_univ _
    _ = (H + 1) ^ (d + r + 1) * (H + 1) ^ Module.finrank ℚ V := by simp only [Fintype.card_prod, Fintype.card_fun, Fintype.card_fin]
    _ ≤ (H + 1) ^ (d + r + 1) * (H + 1) ^ r :=
      Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by omega) hdim)
    _ = (H + 1) ^ (d + r + 1 + r) := (pow_add _ _ _).symm

private def phaseExp (x : ℝ) : ℂ := Complex.exp (Complex.I * (x : ℂ))

private theorem norm_phaseExp (x : ℝ) : ‖phaseExp x‖ = 1 := by
  simpa only [phaseExp, mul_comm] using Complex.norm_exp_ofReal_mul_I x

private theorem phaseExp_mul (x y : ℝ) : phaseExp x * phaseExp y = phaseExp (x + y) := by
  unfold phaseExp
  rw [← Complex.exp_add]
  congr 1
  push_cast
  ring

private def phaseSum {ι : Type*} [Fintype ι] (ω θ : ι → ℝ) (t : ℝ) : ℂ :=
  ∑ a, phaseExp (ω a * t - θ a)

private theorem continuous_phaseSum {ι : Type*} [Fintype ι] (ω θ : ι → ℝ) :
    Continuous (phaseSum ω θ) := by
  unfold phaseSum phaseExp
  fun_prop

/-- The smooth exponent box, centred at an arbitrary target on the prime torus. -/
def smoothBoxSum {k : ℕ} (p : Fin k → ℕ) (θ : Fin k → ℝ) (H : ℕ) (t : ℝ) : ℂ :=
  ∑ a : Fin k → Fin (H + 1), Complex.exp (Complex.I *
    ((smoothBoxFrequency p a * t - ∑ j, (a j : ℝ) * θ j : ℝ) : ℂ))

theorem continuous_smoothBoxSum {k : ℕ} (p : Fin k → ℕ) (θ : Fin k → ℝ) (H : ℕ) :
    Continuous (smoothBoxSum p θ H) := continuous_phaseSum _ _

private theorem finiteFrequencyPoly_phase_shift {ι : Type*} [Fintype ι]
    (ω θ : ι → ℝ) (c u : ℝ) :
    RHTower.Sieve.finiteFrequencyPoly (fun a => phaseExp (ω a * c - θ a)) univ
      (fun a => ω a / (2 * π)) u = phaseSum ω θ (u + c) := by
  classical
  unfold RHTower.Sieve.finiteFrequencyPoly phaseSum
  apply sum_congr rfl
  intro a _
  have harg : 2 * π * (u * (ω a / (2 * π))) = ω a * u := by field_simp
  rw [harg, mul_comm (↑(ω a * u) : ℂ) Complex.I]
  change phaseExp (ω a * c - θ a) * phaseExp (ω a * u) = phaseExp (ω a * (u + c) - θ a)
  rw [phaseExp_mul]
  congr 1
  ring

private theorem phase_collisionWeight_le {ι : Type*} [Fintype ι]
    (ω θ : ι → ℝ) {W Δ : ℝ} (hWD : 1 / W ≤ Δ) (c : ℝ) :
    RHTower.Sieve.finiteFrequencyCollisionWeight (fun a => phaseExp (ω a * c - θ a)) univ
      (fun a => ω a / (2 * π)) (1 / (2 * π * W)) ≤
        ((univ.filter fun ab : ι × ι => |ω ab.1 - ω ab.2| < Δ).card : ℝ) := by
  classical
  have hscaled (a b : ι) : |ω a / (2 * π) - ω b / (2 * π)| < 1 / (2 * π * W) ↔
      |ω a - ω b| < 1 / W := by
    rw [← sub_div, abs_div, abs_of_pos Real.two_pi_pos]
    have heq : 1 / (2 * π * W) = (1 / W) / (2 * π) := by ring
    rw [heq, div_lt_div_iff_of_pos_right Real.two_pi_pos]
  unfold RHTower.Sieve.finiteFrequencyCollisionWeight
  simp only [norm_phaseExp, one_mul, hscaled]
  rw [← Fintype.sum_prod_type (fun ab : ι × ι =>
    if |ω ab.1 - ω ab.2| < 1 / W then (1 : ℝ) else 0)]
  calc (∑ ab : ι × ι, if |ω ab.1 - ω ab.2| < 1 / W then (1 : ℝ) else 0) ≤
      ∑ ab : ι × ι, if |ω ab.1 - ω ab.2| < Δ then (1 : ℝ) else 0 := by
        apply sum_le_sum
        intro ab _
        by_cases h : |ω ab.1 - ω ab.2| < 1 / W
        · rw [if_pos h, if_pos (h.trans_le hWD)]
        · rw [if_neg h]
          split_ifs <;> norm_num
    _ = _ := by rw [← sum_filter]; simp only [sum_const, nsmul_eq_mul, mul_one]

private theorem integral_phaseSum_norm_sq_le_collision {ι : Type*} [Fintype ι]
    (ω θ : ι → ℝ) {T Δ : ℝ} (hT : 0 ≤ T) (hΔ : 0 < Δ) (A : ℝ) :
    (∫ t in A..A + T, ‖phaseSum ω θ t‖ ^ 2) ≤
      (5 * π / 2) * max (T / 2) Δ⁻¹ *
        ((univ.filter fun ab : ι × ι => |ω ab.1 - ω ab.2| < Δ).card : ℝ) := by
  classical
  let W := max (T / 2) Δ⁻¹
  let c := A + T / 2
  have hW : 0 < W := (inv_pos.mpr hΔ).trans_le (le_max_right _ _)
  have hTW : T / 2 ≤ W := le_max_left _ _
  have hWD : 1 / W ≤ Δ := by
    rw [div_le_iff₀ hW]
    have h := mul_le_mul_of_nonneg_left (show Δ⁻¹ ≤ W from le_max_right _ _) hΔ.le
    simpa only [mul_inv_cancel₀ hΔ.ne'] using h
  have hδ : 0 < 1 / (2 * π * W) := by positivity
  have hscale : 2 * π * (1 / (2 * π * W)) * W ≤ 1 := by
    have heq : 2 * π * (1 / (2 * π * W)) * W = 1 := by field_simp
    exact heq.le
  have hmv := RHTower.Sieve.integral_Icc_normSq_finiteFrequencyPoly_le_collisionWeight
    (fun a => phaseExp (ω a * c - θ a)) univ (fun a => ω a / (2 * π)) hδ hscale
  simp_rw [finiteFrequencyPoly_phase_shift] at hmv
  have hcoef : 5 / (4 * (1 / (2 * π * W))) = (5 * π / 2) * W := by field_simp; ring
  rw [hcoef] at hmv
  have hc := phase_collisionWeight_le ω θ hWD c
  have hcont : Continuous fun u => ‖phaseSum ω θ (u + c)‖ ^ 2 := by
    exact ((continuous_phaseSum ω θ).comp (continuous_id.add continuous_const)).norm.pow 2
  have hshift : (∫ t in A..A + T, ‖phaseSum ω θ t‖ ^ 2) =
      ∫ u in -(T / 2)..T / 2, ‖phaseSum ω θ (u + c)‖ ^ 2 := by
    rw [intervalIntegral.integral_comp_add_right (fun t => ‖phaseSum ω θ t‖ ^ 2) c]
    congr 1 <;> dsimp [c] <;> ring
  rw [hshift, intervalIntegral.integral_of_le (by linarith only [hT])]
  have hsub : Set.Ioc (-(T / 2)) (T / 2) ⊆ Set.Icc (-W) W := by
    intro u hu
    exact ⟨by linarith only [hu.1, hTW], hu.2.trans hTW⟩
  refine (setIntegral_mono_set hcont.integrableOn_Icc
    (Filter.Eventually.of_forall fun u => sq_nonneg ‖phaseSum ω θ (u + c)‖)
    (LE.le.eventuallyLE hsub)).trans ?_
  exact hmv.trans (mul_le_mul_of_nonneg_left hc (by positivity))

/-- The whole time window is controlled by its arithmetic close-frequency pairs. -/
theorem integral_smoothBoxSum_norm_sq_le_collision {d r H : ℕ}
    (p : Fin (d + r + 1) → ℕ) (hp : Function.Injective p)
    (hprime : ∀ j, (p j).Prime) (hH : 1 ≤ H)
    (θ : Fin (d + r + 1) → ℝ) {T : ℝ} (hT : 0 ≤ T) (A : ℝ) :
    (∫ t in A..A + T, ‖smoothBoxSum p θ H t‖ ^ 2) ≤
      (5 * π / 2) * max (T / 2)
        (collectiveDepthFloor (r + 1) d (collectiveLogBound p) H)⁻¹ *
          (H + 1 : ℝ) ^ (d + r + 1 + r) := by
  have hΔ := collectiveDepthFloor_pos (d := d) (W := collectiveLogBound p)
    (show 1 ≤ r + 1 by omega) (show (0 : ℝ) < H by exact_mod_cast (show 0 < H by omega))
  have hc : ((univ.filter fun ab : (Fin (d + r + 1) → Fin (H + 1)) ×
      (Fin (d + r + 1) → Fin (H + 1)) =>
      |smoothBoxFrequency p ab.1 - smoothBoxFrequency p ab.2| <
        collectiveDepthFloor (r + 1) d (collectiveLogBound p) H).card : ℝ) ≤
      (H + 1 : ℝ) ^ (d + r + 1 + r) := by
    exact_mod_cast card_close_smoothBox_pairs_le p hp hprime hH
  have h := integral_phaseSum_norm_sq_le_collision (smoothBoxFrequency p)
    (fun a : Fin (d + r + 1) → Fin (H + 1) => ∑ j, (a j : ℝ) * θ j) hT hΔ A
  exact h.trans (mul_le_mul_of_nonneg_left hc (by positivity))

private theorem norm_pow_sub_one_le (z : ℂ) (hz : ‖z‖ = 1) (n : ℕ) :
    ‖z ^ n - 1‖ ≤ (n : ℝ) * ‖z - 1‖ := by
  induction n with
  | zero => simp only [pow_zero, sub_self, norm_zero, Nat.cast_zero, zero_mul, le_refl]
  | succ n ih =>
    have heq : z ^ (n + 1) - 1 = z ^ n * (z - 1) + (z ^ n - 1) := by rw [pow_succ]; ring
    rw [heq]
    calc _ ≤ ‖z ^ n * (z - 1)‖ + ‖z ^ n - 1‖ := norm_add_le _ _
      _ ≤ ‖z - 1‖ + (n : ℝ) * ‖z - 1‖ := by simpa only [norm_mul, norm_pow, hz, one_pow, one_mul] using add_le_add (le_refl ‖z ^ n * (z - 1)‖) ih
      _ = ((n + 1 : ℕ) : ℝ) * ‖z - 1‖ := by push_cast; ring

private theorem phaseExp_pow (x : ℝ) (n : ℕ) : phaseExp x ^ n = phaseExp ((n : ℝ) * x) := by
  induction n with
  | zero => simp only [pow_zero, Nat.cast_zero, zero_mul, phaseExp, Complex.ofReal_zero, mul_zero, Complex.exp_zero]
  | succ n ih =>
    rw [pow_succ, ih, phaseExp_mul]
    congr 1
    push_cast
    ring

private theorem smoothBoxSum_eq_prod {k : ℕ}
    (p : Fin k → ℕ) (θ : Fin k → ℝ) (H : ℕ) (t : ℝ) :
    smoothBoxSum p θ H t =
      ∏ j, ∑ n : Fin (H + 1), phaseExp (log (p j) * t - θ j) ^ (n : ℕ) := by
  classical
  have hp := Finset.prod_univ_sum (fun _ : Fin k => (univ : Finset (Fin (H + 1))))
    (fun j n => phaseExp (log (p j) * t - θ j) ^ (n : ℕ))
  simp only [Fintype.piFinset_univ] at hp
  rw [hp]
  unfold smoothBoxSum
  apply sum_congr rfl
  intro a _
  simp only [phaseExp_pow]
  simp only [phaseExp]
  rw [← Complex.exp_sum]
  congr 1
  unfold smoothBoxFrequency
  push_cast
  rw [sum_mul, ← sum_sub_distrib, mul_sum]
  apply sum_congr rfl
  intro j _
  ring

private theorem half_le_norm_phase_average {H : ℕ} {z : ℂ} (hz : ‖z‖ = 1)
    (hnear : ‖z - 1‖ ≤ 1 / (2 * (H + 1 : ℝ))) :
    (H + 1 : ℝ) / 2 ≤ ‖∑ n : Fin (H + 1), z ^ (n : ℕ)‖ := by
  have hN : (0 : ℝ) < H + 1 := by positivity
  have hterm (n : Fin (H + 1)) : ‖z ^ (n : ℕ) - 1‖ ≤ 1 / 2 := by
    have hn : (n : ℝ) ≤ H + 1 := by exact_mod_cast n.isLt.le
    calc _ ≤ (n : ℝ) * ‖z - 1‖ := norm_pow_sub_one_le z hz _
      _ ≤ (H + 1 : ℝ) * (1 / (2 * (H + 1 : ℝ))) :=
        mul_le_mul hn hnear (norm_nonneg _) hN.le
      _ = 1 / 2 := by field_simp
  have hsub : ‖(∑ n : Fin (H + 1), z ^ (n : ℕ)) - (H + 1 : ℂ)‖ ≤ (H + 1 : ℝ) / 2 := by
    have heq : (∑ n : Fin (H + 1), z ^ (n : ℕ)) - (H + 1 : ℂ) =
        ∑ n : Fin (H + 1), (z ^ (n : ℕ) - 1) := by
      rw [sum_sub_distrib]
      simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one, Nat.cast_add, Nat.cast_one]
    rw [heq]
    refine (norm_sum_le _ _).trans ((sum_le_sum fun n _ => hterm n).trans_eq ?_)
    simp only [sum_const, card_univ, Fintype.card_fin, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    ring
  have htriangle := norm_sub_norm_le (H + 1 : ℂ) (∑ n : Fin (H + 1), z ^ (n : ℕ))
  rw [norm_sub_rev] at htriangle
  have hnorm : ‖(H + 1 : ℂ)‖ = (H + 1 : ℝ) := by
    rw [← Complex.ofReal_natCast, ← Complex.ofReal_one, ← Complex.ofReal_add, Complex.norm_real,
      Real.norm_of_nonneg hN.le]
  rw [hnorm] at htriangle
  linarith only [htriangle, hsub]

/-- A finite interval of returns to a prescribed prime-torus point, in chord distance. -/
def primeReturnWindow {k : ℕ} (p : Fin k → ℕ) (θ : Fin k → ℝ) (ε A T : ℝ) : Set ℝ :=
  {t | t ∈ Set.Ioc A (A + T) ∧ ∀ j,
    ‖Complex.exp (Complex.I * ((log (p j) * t - θ j : ℝ) : ℂ)) - 1‖ ≤ ε}

/-- A product detector loses one fixed factor per prime, independently of the cutoff. -/
theorem smoothBoxSum_norm_sq_ge_on_return {k H : ℕ}
    (p : Fin k → ℕ) (θ : Fin k → ℝ) {t : ℝ}
    (hret : ∀ j, ‖Complex.exp (Complex.I * ((log (p j) * t - θ j : ℝ) : ℂ)) - 1‖ ≤
      1 / (2 * (H + 1 : ℝ))) :
    (H + 1 : ℝ) ^ (2 * k) / 4 ^ k ≤ ‖smoothBoxSum p θ H t‖ ^ 2 := by
  have hprod : ((H + 1 : ℝ) / 2) ^ k ≤ ‖smoothBoxSum p θ H t‖ := by
    rw [smoothBoxSum_eq_prod, norm_prod]
    have h := prod_le_prod (fun _ (_ : _ ∈ (univ : Finset (Fin k))) =>
      show (0 : ℝ) ≤ (H + 1) / 2 by positivity)
      (fun j _ => half_le_norm_phase_average (norm_phaseExp _) (hret j))
    simpa only [prod_const, card_univ, Fintype.card_fin] using h
  have hsq := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ ((H + 1 : ℝ) / 2) ^ k) hprod 2
  have heq : (((H + 1 : ℝ) / 2) ^ k) ^ 2 = (H + 1 : ℝ) ^ (2 * k) / 4 ^ k := by
    rw [← pow_mul, mul_comm k 2, pow_mul, div_pow]
    norm_num only [show (2 : ℝ) ^ 2 = 4 by norm_num]
    rw [div_pow, ← pow_mul]
  rwa [heq] at hsq

/-- Uniform finite-time return count with the arithmetic rank threshold discharged. -/
theorem measure_primeReturnWindow_le {d r H : ℕ}
    (p : Fin (d + r + 1) → ℕ) (hp : Function.Injective p)
    (hprime : ∀ j, (p j).Prime) (hH : 1 ≤ H)
    (θ : Fin (d + r + 1) → ℝ) {T : ℝ} (hT : 0 ≤ T) (A : ℝ) :
    volume.real (primeReturnWindow p θ (1 / (2 * (H + 1 : ℝ))) A T) ≤
      (5 * π / 2) * (4 : ℝ) ^ (d + r + 1) *
        max (T / 2) (collectiveDepthFloor (r + 1) d (collectiveLogBound p) H)⁻¹ /
          (H + 1 : ℝ) ^ (d + 1) := by
  let c : ℝ := (H + 1 : ℝ) ^ (2 * (d + r + 1)) / 4 ^ (d + r + 1)
  have hc : 0 < c := by dsimp [c]; positivity
  have hle : A ≤ A + T := by linarith only [hT]
  have hf : Continuous fun t => ‖smoothBoxSum p θ H t‖ ^ 2 :=
    (continuous_smoothBoxSum p θ H).norm.pow 2
  have hi := integral_smoothBoxSum_norm_sq_le_collision p hp hprime hH θ hT A
  rw [intervalIntegral.integral_of_le hle] at hi
  have hfi : IntegrableOn (fun t => ‖smoothBoxSum p θ H t‖ ^ 2) (Set.Ioc A (A + T)) :=
    (intervalIntegrable_iff_integrableOn_Ioc_of_le hle).mp (hf.intervalIntegrable _ _)
  have hmark := mul_meas_ge_le_integral_of_nonneg
    (Filter.Eventually.of_forall (fun t => sq_nonneg ‖smoothBoxSum p θ H t‖)) hfi c
  have hvol : volume.real (primeReturnWindow p θ (1 / (2 * (H + 1 : ℝ))) A T) ≤
      (volume.restrict (Set.Ioc A (A + T))).real {t | c ≤ ‖smoothBoxSum p θ H t‖ ^ 2} := by
    rw [measureReal_restrict_apply (measurableSet_le measurable_const hf.measurable)]
    apply measureReal_mono
    · intro t ht
      exact ⟨smoothBoxSum_norm_sq_ge_on_return p θ ht.2, ht.1⟩
    · exact (lt_of_le_of_lt (measure_mono Set.inter_subset_right)
        (measure_Ioc_lt_top (a := A) (b := A + T))).ne
  have hb := ((mul_le_mul_of_nonneg_left hvol hc.le).trans hmark).trans hi
  have hΔ := collectiveDepthFloor_pos (d := d) (W := collectiveLogBound p)
    (show 1 ≤ r + 1 by omega) (show (0 : ℝ) < H by exact_mod_cast (show 0 < H by omega))
  have hN : (H + 1 : ℝ) ≠ 0 := by positivity
  have hpow : (H + 1 : ℝ) ^ (2 * (d + r + 1)) =
      (H + 1 : ℝ) ^ (d + r + 1 + r) * (H + 1 : ℝ) ^ (d + 1) := by
    rw [← pow_add]
    congr 1
    omega
  calc
    _ ≤ ((5 * π / 2) * max (T / 2)
        (collectiveDepthFloor (r + 1) d (collectiveLogBound p) H)⁻¹ *
          (H + 1 : ℝ) ^ (d + r + 1 + r)) / c := by
      apply (le_div_iff₀ hc).mpr
      simpa only [mul_comm] using hb
    _ = _ := by
      dsimp [c]
      rw [hpow]
      field_simp [hN, hΔ.ne']

/-- The same return window in radian precision, with explicit integer windings. -/
def radianReturnWindow {k : ℕ} (p : Fin k → ℕ) (θ : Fin k → ℝ) (δ A T : ℝ) : Set ℝ :=
  {t | t ∈ Set.Ioc A (A + T) ∧ ∃ m : Fin k → ℤ,
    ∀ j, |log (p j) * t - θ j - 2 * π * m j| ≤ δ}

theorem radianReturnWindow_subset {k : ℕ}
    (p : Fin k → ℕ) (θ : Fin k → ℝ) (δ A T : ℝ) :
    radianReturnWindow p θ δ A T ⊆ primeReturnWindow p θ δ A T := by
  rintro t ⟨hwin, m, hm⟩
  refine ⟨hwin, fun j => ?_⟩
  exact (RHTower.norm_exp_I_mul_real_sub_one_le_mod_two_pi
    (log (p j) * t - θ j) (m j)).trans (hm j)

/-- Growing-dimensional count for actual radian returns of prime logarithms. -/
theorem measure_radianReturnWindow_le {d r H : ℕ}
    (p : Fin (d + r + 1) → ℕ) (hp : Function.Injective p)
    (hprime : ∀ j, (p j).Prime) (hH : 1 ≤ H)
    (θ : Fin (d + r + 1) → ℝ) {T : ℝ} (hT : 0 ≤ T) (A : ℝ) :
    volume.real (radianReturnWindow p θ (1 / (2 * (H + 1 : ℝ))) A T) ≤
      (5 * π / 2) * (4 : ℝ) ^ (d + r + 1) *
        max (T / 2) (collectiveDepthFloor (r + 1) d (collectiveLogBound p) H)⁻¹ /
          (H + 1 : ℝ) ^ (d + 1) := by
  refine (measureReal_mono (radianReturnWindow_subset p θ _ A T) ?_).trans
    (measure_primeReturnWindow_le p hp hprime hH θ hT A)
  exact (lt_of_le_of_lt (measure_mono (fun _ ht => ht.1))
    (measure_Ioc_lt_top (a := A) (b := A + T))).ne

/-- Beyond twice the inverse arithmetic floor, return density has the full
effective codimension saving without an additional resolution factor in time. -/
theorem relative_measure_radianReturnWindow_le {d r H : ℕ}
    (p : Fin (d + r + 1) → ℕ) (hp : Function.Injective p)
    (hprime : ∀ j, (p j).Prime) (hH : 1 ≤ H)
    (θ : Fin (d + r + 1) → ℝ) {T : ℝ}
    (hT : 2 / collectiveDepthFloor (r + 1) d (collectiveLogBound p) H ≤ T) (A : ℝ) :
    volume.real (radianReturnWindow p θ (1 / (2 * (H + 1 : ℝ))) A T) / T ≤
      (5 * π / 4) * (4 : ℝ) ^ (d + r + 1) / (H + 1 : ℝ) ^ (d + 1) := by
  have hΔ := collectiveDepthFloor_pos (d := d) (W := collectiveLogBound p)
    (show 1 ≤ r + 1 by omega) (show (0 : ℝ) < H by exact_mod_cast (show 0 < H by omega))
  have hTpos : 0 < T := (div_pos (by norm_num : (0 : ℝ) < 2) hΔ).trans_le hT
  have hhalf : (collectiveDepthFloor (r + 1) d (collectiveLogBound p) H)⁻¹ ≤ T / 2 := by
    have h := hT
    rw [div_eq_mul_inv] at h
    linarith only [h]
  have hm := measure_radianReturnWindow_le p hp hprime hH θ hTpos.le A
  rw [max_eq_left hhalf] at hm
  have hdiv := div_le_div_of_nonneg_right hm hTpos.le
  refine hdiv.trans_eq ?_
  field_simp [hTpos.ne']
  norm_num

/-- Degree of the polynomial observation horizon in coefficient height. -/
def collectiveTimeDegree (r d W : ℕ) : ℕ :=
  r * collectiveBase (d + r) W ^ (100 * collectiveRootDegree d r * (d + r + 1)) + r - 1

/-- Height-independent scale of the observation horizon. -/
def collectiveTimeScale (r d W : ℕ) : ℝ :=
  2 * r * r.factorial * exp (collectiveExponent r d W * (log (r.factorial : ℝ) + 2))

/-- The reciprocal arithmetic floor is exactly polynomial in coefficient height. -/
theorem collective_return_horizon_eq {r d W : ℕ} (hr : 1 ≤ r) {H : ℝ} (hH : 0 < H) :
    2 / collectiveDepthFloor r d W H =
      collectiveTimeScale r d W * H ^ collectiveTimeDegree r d W := by
  let C := collectiveBase (d + r) W ^ (100 * collectiveRootDegree d r * (d + r + 1))
  have hC : collectiveExponent r d W = (C : ℝ) := by
    simp only [collectiveExponent, C, Nat.cast_pow]
  have hfac : (0 : ℝ) < r.factorial := by exact_mod_cast r.factorial_pos
  have hlog : log ((r.factorial : ℝ) * H ^ r) + 2 =
      log (r.factorial : ℝ) + 2 + (r : ℝ) * log H := by
    rw [log_mul hfac.ne' (pow_pos hH r).ne', log_pow]
    ring
  have hs : collectiveExponent r d W * (log ((r.factorial : ℝ) * H ^ r) + 2) =
      collectiveExponent r d W * (log (r.factorial : ℝ) + 2) + (r * C : ℕ) * log H := by
    rw [hlog, hC]
    push_cast
    ring
  have he : exp (collectiveExponent r d W * (log ((r.factorial : ℝ) * H ^ r) + 2)) =
      exp (collectiveExponent r d W * (log (r.factorial : ℝ) + 2)) * H ^ (r * C) := by
    rw [hs, exp_add, exp_nat_mul, exp_log hH]
  unfold collectiveDepthFloor
  rw [div_eq_mul_inv, inv_div, div_eq_mul_inv, ← exp_neg, neg_neg, he]
  unfold collectiveTimeScale collectiveTimeDegree
  change 2 * (((r : ℝ) * r.factorial * H ^ (r - 1)) *
      (exp (collectiveExponent r d W * (log (r.factorial : ℝ) + 2)) * H ^ (r * C))) =
    (2 * r * r.factorial * exp (collectiveExponent r d W * (log (r.factorial : ℝ) + 2))) *
      H ^ (r * C + r - 1)
  calc _ = (2 * r * r.factorial * exp (collectiveExponent r d W * (log (r.factorial : ℝ) + 2))) *
      (H ^ (r - 1) * H ^ (r * C)) := by ring
    _ = _ := by
      have hindex (q : ℕ) : r - 1 + q = q + r - 1 := by omega
      rw [← pow_add, hindex]

end GaloisForLFunctions.CollectiveDiophantineGeometry
