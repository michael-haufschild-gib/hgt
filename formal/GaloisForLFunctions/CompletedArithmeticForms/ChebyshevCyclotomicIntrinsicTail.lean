import GaloisForLFunctions.CompletedArithmeticForms.ChebyshevCyclotomicTail
import GaloisForLFunctions.RHTower.Sieve.HarmonicLogBound
import GaloisForLFunctions.RHTower.RouteEFixedOrderTwoGradeMomentPayment

/-!
# Cyclotomic tails at the intrinsic zero abscissa

The coefficient mass of the actual Chebyshev packet has exponent `Θ-1/2`.
Root spacing therefore bounds its far energy by `N^(2Θ+ε)/K`, retaining
an arbitrary positive power saving from the removed frequency band.
-/

noncomputable section

open Finset

namespace GaloisForLFunctions.CompletedArithmeticForms

open _root_.RHTower

/-- The absolute coefficient mass is subpower-controlled at the actual zero abscissa. -/
theorem chebyshevConductor_mass_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N →
      (∑ j ∈ Icc 1 N, |chebyshevConductorCoeff j|) ≤
        C * (N : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε) := by
  obtain ⟨C, hC, hψ⟩ := exists_psiRemainder_le_rpow_zetaZeroAbscissa (ε / 2)
    (by positivity)
  refine ⟨C * (1 + 2 / ε), by positivity, fun N hN => ?_⟩
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have he : 0 ≤ zetaZeroAbscissa - 1 / 2 + ε / 2 := by
    linarith only [half_le_zetaZeroAbscissa, hε]
  have hterm (j : ℕ) (hj : j ∈ Icc 1 N) :
      |chebyshevConductorCoeff j| ≤
        C * (N : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε / 2) * (1 / (j : ℝ)) := by
    by_cases hj2 : j ≤ 2
    · rw [chebyshevConductorCoeff, chebyshevCesaroIncrement_zero_of_le_two hj2,
        zero_div, abs_zero]
      positivity
    have hj3 : 3 ≤ j := by omega
    have hjp : (0 : ℝ) < j := by exact_mod_cast (show 0 < j by omega)
    have hmp : (0 : ℝ) < ((j - 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 0 < j - 1 by omega)
    have hrem := hψ (j - 1) (by omega)
    rw [psiRemainder, chebyshevPsi_eq_psi] at hrem
    have hinc : |chebyshevCesaroIncrement j| ≤
        C * ((j - 1 : ℕ) : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε / 2) := by
      rw [chebyshevCesaroIncrement_eq hj3, abs_div, abs_of_pos (Real.sqrt_pos.mpr hmp)]
      calc
        _ ≤ (C * ((j - 1 : ℕ) : ℝ) ^ (zetaZeroAbscissa + ε / 2)) /
            Real.sqrt ((j - 1 : ℕ) : ℝ) :=
          div_le_div_of_nonneg_right hrem (Real.sqrt_nonneg _)
        _ = _ := by
          rw [Real.sqrt_eq_rpow, mul_div_assoc, ← Real.rpow_sub hmp]
          congr 2
          ring
    rw [chebyshevConductorCoeff, abs_div, abs_of_pos hjp]
    calc
      _ ≤ (C * ((j - 1 : ℕ) : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε / 2)) / j :=
        div_le_div_of_nonneg_right hinc hjp.le
      _ ≤ (C * (N : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε / 2)) / j := by
        apply div_le_div_of_nonneg_right _ hjp.le
        apply mul_le_mul_of_nonneg_left _ hC
        have hjN : j - 1 ≤ N := (Nat.sub_le j 1).trans (mem_Icc.mp hj).2
        exact Real.rpow_le_rpow hmp.le (by exact_mod_cast hjN) he
      _ = _ := by ring
  have hlog : 1 + Real.log (N : ℝ) ≤ (1 + 2 / ε) * (N : ℝ) ^ (ε / 2) := by
    have h1 : 1 ≤ (N : ℝ) ^ (ε / 2) := Real.one_le_rpow hN1 (by positivity)
    have h2 := Real.log_le_rpow_div hNp.le (by positivity : 0 < ε / 2)
    have hdiv : (N : ℝ) ^ (ε / 2) / (ε / 2) =
        (2 / ε) * (N : ℝ) ^ (ε / 2) := by ring
    rw [hdiv] at h2
    nlinarith only [h1, h2]
  calc
    _ ≤ ∑ j ∈ Icc 1 N,
        C * (N : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε / 2) * (1 / (j : ℝ)) :=
      sum_le_sum hterm
    _ = C * (N : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε / 2) *
        (∑ j ∈ Icc 1 N, 1 / (j : ℝ)) := (mul_sum _ _ _).symm
    _ ≤ C * (N : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε / 2) *
        ((1 + 2 / ε) * (N : ℝ) ^ (ε / 2)) :=
      mul_le_mul_of_nonneg_left
        ((Sieve.sum_Icc_one_div_le_one_add_log N).trans hlog) (by positivity)
    _ = _ := by
      rw [show zetaZeroAbscissa - 1 / 2 + ε =
        (zetaZeroAbscissa - 1 / 2 + ε / 2) + ε / 2 by ring,
        Real.rpow_add hNp (zetaZeroAbscissa - 1 / 2 + ε / 2) (ε / 2)]
      ring

private theorem packet_mode_mass_bound (Q k : ℕ) (a : ℕ → ℝ)
    (hk0 : 0 < k) (hkQ : k < Q) :
    ‖(1 + cyclotomicMode Q k) * prefixPacket Q a (cyclotomicMode Q k)‖ ^ 2 ≤
      (Q : ℝ) ^ 2 * (∑ j ∈ Ico 1 Q, |a j|) ^ 2 *
        (1 / (k : ℝ) ^ 2 + 1 / ((Q - k : ℕ) : ℝ) ^ 2) := by
  let ζ := cyclotomicMode Q k
  let P := prefixPacket Q a ζ
  let A := ∑ j ∈ Ico 1 Q, |a j|
  let r : ℝ := (min k (Q - k) : ℕ)
  have hr : 0 < r := by
    dsimp [r]
    exact_mod_cast lt_min hk0 (Nat.sub_pos_of_lt hkQ)
  have hQ : (0 : ℝ) < Q := by exact_mod_cast hk0.trans hkQ
  have hA : 0 ≤ A := sum_nonneg fun _ _ => abs_nonneg _
  have hζ : ‖ζ‖ = 1 := norm_cyclotomicMode Q k
  have hdiff : ‖(1 - ζ) * P‖ ≤ 2 * A := by
    dsimp [P]
    rw [prefixPacket_difference]
    have h1 : ‖∑ j ∈ Ico 1 Q, (a j : ℂ)‖ ≤ A := by
      simpa only [Complex.norm_real, Real.norm_eq_abs] using
        norm_sum_le (Ico 1 Q) (fun j => (a j : ℂ))
    have h2 : ‖∑ j ∈ Ico 1 Q, (a j : ℂ) * ζ ^ j‖ ≤ A := by
      simpa only [norm_mul, norm_pow, hζ, one_pow, mul_one,
        Complex.norm_real, Real.norm_eq_abs] using
        norm_sum_le (Ico 1 Q) (fun j => (a j : ℂ) * ζ ^ j)
    exact (norm_sub_le _ _).trans (by linarith only [h1, h2])
  rw [norm_mul] at hdiff
  have hgap : 4 * r ≤ (Q : ℝ) * ‖1 - ζ‖ := by
    have h := (div_le_iff₀ hQ).mp (cyclotomicMode_gap hk0 hkQ)
    simpa only [mul_comm] using h
  have hP : 2 * r * ‖P‖ ≤ (Q : ℝ) * A := by
    have h1 := mul_le_mul_of_nonneg_right hgap (norm_nonneg P)
    have h2 := mul_le_mul_of_nonneg_left hdiff hQ.le
    nlinarith only [h1, h2]
  have hplus : ‖(1 + ζ) * P‖ ≤ 2 * ‖P‖ := by
    rw [norm_mul]
    apply mul_le_mul_of_nonneg_right _ (norm_nonneg P)
    simpa only [norm_one, hζ, one_add_one_eq_two] using norm_add_le (1 : ℂ) ζ
  have hscaled : r * ‖(1 + ζ) * P‖ ≤ (Q : ℝ) * A := by
    have h := mul_le_mul_of_nonneg_left hplus hr.le
    nlinarith only [h, hP]
  have hs := pow_le_pow_left₀ (mul_nonneg hr.le (norm_nonneg _)) hscaled 2
  rw [mul_pow, mul_pow] at hs
  have hmode : ‖(1 + ζ) * P‖ ^ 2 ≤ (Q : ℝ) ^ 2 * A ^ 2 / r ^ 2 := by
    apply (le_div_iff₀ (sq_pos_of_pos hr)).mpr
    simpa only [mul_comm] using hs
  have hinv : 1 / r ^ 2 ≤ 1 / (k : ℝ) ^ 2 + 1 / ((Q - k : ℕ) : ℝ) ^ 2 := by
    rcases le_total k (Q - k) with h | h
    · dsimp [r]
      rw [min_eq_left h]
      exact le_add_of_nonneg_right (by positivity)
    · dsimp [r]
      rw [min_eq_right h]
      exact le_add_of_nonneg_left (by positivity)
  calc
    _ ≤ (Q : ℝ) ^ 2 * A ^ 2 / r ^ 2 := hmode
    _ = ((Q : ℝ) ^ 2 * A ^ 2) * (1 / r ^ 2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hinv (by positivity)

/-- The far packet costs conductor divided by bandwidth times the squared coefficient mass. -/
theorem chebyshevCyclotomicFar_le_mass (N : ℕ) {K : ℕ} (hK : 1 ≤ K) :
    chebyshevCyclotomicFar N K ≤
      2 * ((N : ℝ) + 1) * (∑ j ∈ Icc 1 N, |chebyshevConductorCoeff j|) ^ 2 / K := by
  let S := (Ico 1 (N + 1)).filter (fun k => K < k ∧ K < N + 1 - k)
  have hleft : ∑ k ∈ S, (1 : ℝ) / (k : ℝ) ^ 2 ≤ 1 / (K : ℝ) := by
    apply le_trans _ (routeE_invSqTail_Ioo_le K (N + 1) hK)
    apply sum_le_sum_of_subset_of_nonneg
    · intro k hk
      exact mem_Ioo.mpr ⟨(mem_filter.mp hk).2.1, (mem_Ico.mp (mem_filter.mp hk).1).2⟩
    · intro k _ _
      positivity
  have hinj : Set.InjOn (fun k => N + 1 - k) (↑S) := by
    intro k hk l hl heq
    have hkN := (mem_Ico.mp (mem_filter.mp hk).1).2
    have hlN := (mem_Ico.mp (mem_filter.mp hl).1).2
    change N + 1 - k = N + 1 - l at heq
    omega
  have hright : ∑ k ∈ S, (1 : ℝ) / ((N + 1 - k : ℕ) : ℝ) ^ 2 ≤ 1 / (K : ℝ) := by
    rw [← sum_image (f := fun k : ℕ => (1 : ℝ) / (k : ℝ) ^ 2) hinj]
    apply le_trans _ (routeE_invSqTail_Ioo_le K (N + 1) hK)
    apply sum_le_sum_of_subset_of_nonneg
    · intro l hl
      obtain ⟨k, hk, rfl⟩ := mem_image.mp hl
      obtain ⟨hkI, hkfar⟩ := mem_filter.mp hk
      have hk0 := (mem_Ico.mp hkI).1
      exact mem_Ioo.mpr ⟨hkfar.2, by omega⟩
    · intro k _ _
      positivity
  let A := ∑ j ∈ Icc 1 N, |chebyshevConductorCoeff j|
  have hmass : (∑ j ∈ Ico 1 (N + 1), |chebyshevConductorCoeff j|) = A := by
    congr 1
  have hb := sum_le_sum (s := S) (fun k hk => packet_mode_mass_bound (N + 1) k
    chebyshevConductorCoeff (mem_Ico.mp (mem_filter.mp hk).1).1
      (mem_Ico.mp (mem_filter.mp hk).1).2)
  simp only [hmass, Nat.cast_add, Nat.cast_one] at hb
  rw [← mul_sum, sum_add_distrib] at hb
  have hsum := hb.trans (mul_le_mul_of_nonneg_left (add_le_add hleft hright)
    (by positivity : 0 ≤ ((N : ℝ) + 1) ^ 2 * A ^ 2))
  unfold chebyshevCyclotomicFar
  apply (div_le_iff₀ (by positivity : 0 < (N : ℝ) + 1)).mpr
  exact hsum.trans_eq (by dsimp [A]; ring)

/-- The actual tail gains a factor `K` relative to its intrinsic zero-width exponent. -/
theorem chebyshevCyclotomicFar_subpower (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N K : ℕ, 2 ≤ N → 1 ≤ K →
      chebyshevCyclotomicFar N K ≤ C * (N : ℝ) ^ (2 * zetaZeroAbscissa + ε) / K := by
  obtain ⟨C, hC, hm⟩ := chebyshevConductor_mass_subpower (ε / 2) (by positivity)
  refine ⟨4 * C ^ 2, by positivity, fun N K hN hK => ?_⟩
  have hNp : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (show 1 ≤ N by omega)
  have hs := pow_le_pow_left₀ (sum_nonneg fun _ _ => abs_nonneg _) (hm N hN) 2
  calc
    _ ≤ 2 * ((N : ℝ) + 1) * (∑ j ∈ Icc 1 N, |chebyshevConductorCoeff j|) ^ 2 / K :=
      chebyshevCyclotomicFar_le_mass N hK
    _ ≤ 2 * ((N : ℝ) + 1) *
        (C * (N : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε / 2)) ^ 2 / K := by
      exact div_le_div_of_nonneg_right
        (mul_le_mul_of_nonneg_left hs (by positivity)) (by positivity)
    _ ≤ 4 * (N : ℝ) *
        (C * (N : ℝ) ^ (zetaZeroAbscissa - 1 / 2 + ε / 2)) ^ 2 / K := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact mul_le_mul_of_nonneg_right (by linarith only [hN1]) (sq_nonneg _)
    _ = _ := by
      rw [mul_pow, ← Real.rpow_mul_natCast hNp.le]
      rw [show 2 * zetaZeroAbscissa + ε =
        1 + (zetaZeroAbscissa - 1 / 2 + ε / 2) * (2 : ℕ) by ring,
        Real.rpow_add hNp, Real.rpow_one]
      ring

end GaloisForLFunctions.CompletedArithmeticForms
