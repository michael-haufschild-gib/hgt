import GaloisForLFunctions.RHTower.Sieve.MenonHarmonicRamareBlockSplitOn
import GaloisForLFunctions.RHTower.Sieve.RamareCofactorBlock
import GaloisForLFunctions.RHTower.Sieve.LadderProductDefect

/-!
# Harmonic cofactor support error

Changing a common cofactor interval to the exact prime-dependent Ramaré support is charged by
coefficient energy.  For harmonic coefficients this retains the reciprocal square of the lower
cofactor endpoint.
-/

namespace RHTower.Sieve

open MeasureTheory Finset

noncomputable section

/-- Mean-square cost of changing a finite support, retaining exact coefficient energies. -/
theorem integral_Icc_normSq_logPoly_sub_le_energy {a : ℕ → ℂ}
    {U V : Finset ℕ} (hU0 : (0 : ℕ) ∉ U) (hV0 : (0 : ℕ) ∉ V) {M : ℕ}
    (hUM : ∀ n ∈ U, n ≤ M) (hVM : ∀ n ∈ V, n ≤ M) {W : ℝ} (hW : 1 ≤ W) :
    (∫ w in Set.Icc (-W) W, ‖logPoly a U w - logPoly a V w‖ ^ (2 : ℕ))
      ≤ 2 * (5 * Real.pi / 2 * W + 5 * Real.exp 1 / 2 * (M : ℝ)) *
          ((∑ n ∈ U \ V, ‖a n‖ ^ (2 : ℕ)) + ∑ n ∈ V \ U, ‖a n‖ ^ (2 : ℕ)) := by
  classical
  have hUd0 : (0 : ℕ) ∉ U \ V := fun hc => hU0 (Finset.mem_sdiff.1 hc).1
  have hVd0 : (0 : ℕ) ∉ V \ U := fun hc => hV0 (Finset.mem_sdiff.1 hc).1
  have hUdM : ∀ n ∈ U \ V, n ≤ M := fun n hn => hUM n (Finset.mem_sdiff.1 hn).1
  have hVdM : ∀ n ∈ V \ U, n ≤ M := fun n hn => hVM n (Finset.mem_sdiff.1 hn).1
  have hEU := integral_Icc_normSq_logPoly_le_energy a hUd0 hUdM hW
  have hEV := integral_Icc_normSq_logPoly_le_energy a hVd0 hVdM hW
  have hpt : ∀ w : ℝ, ‖logPoly a U w - logPoly a V w‖ ^ (2 : ℕ)
      ≤ 2 * ‖logPoly a (U \ V) w‖ ^ (2 : ℕ) + 2 * ‖logPoly a (V \ U) w‖ ^ (2 : ℕ) := by
    intro w
    rw [logPoly_sub_eq_sdiff]
    have htri := norm_sub_le (logPoly a (U \ V) w) (logPoly a (V \ U) w)
    have hsq := pow_le_pow_left₀ (norm_nonneg _) htri 2
    nlinarith [hsq, sq_nonneg (‖logPoly a (U \ V) w‖ - ‖logPoly a (V \ U) w‖)]
  have hcont : Continuous fun w : ℝ => ‖logPoly a U w - logPoly a V w‖ ^ (2 : ℕ) :=
    (((continuous_logPoly a U).sub (continuous_logPoly a V)).norm).pow 2
  have hcontU : Continuous fun w : ℝ => ‖logPoly a (U \ V) w‖ ^ (2 : ℕ) :=
    ((continuous_logPoly a (U \ V)).norm).pow 2
  have hcontV : Continuous fun w : ℝ => ‖logPoly a (V \ U) w‖ ^ (2 : ℕ) :=
    ((continuous_logPoly a (V \ U)).norm).pow 2
  have hint1 : IntegrableOn (fun w : ℝ => ‖logPoly a U w - logPoly a V w‖ ^ (2 : ℕ))
      (Set.Icc (-W) W) volume := hcont.integrableOn_Icc
  have hint2 : IntegrableOn (fun w : ℝ =>
      2 * ‖logPoly a (U \ V) w‖ ^ (2 : ℕ) + 2 * ‖logPoly a (V \ U) w‖ ^ (2 : ℕ))
      (Set.Icc (-W) W) volume :=
    ((hcontU.const_mul 2).add (hcontV.const_mul 2)).integrableOn_Icc
  have hmono := setIntegral_mono_on hint1 hint2 measurableSet_Icc (fun w _ => hpt w)
  have hsplit : (∫ w in Set.Icc (-W) W,
      (2 * ‖logPoly a (U \ V) w‖ ^ (2 : ℕ) + 2 * ‖logPoly a (V \ U) w‖ ^ (2 : ℕ)))
      = 2 * (∫ w in Set.Icc (-W) W, ‖logPoly a (U \ V) w‖ ^ (2 : ℕ))
        + 2 * (∫ w in Set.Icc (-W) W, ‖logPoly a (V \ U) w‖ ^ (2 : ℕ)) := by
    have hiU : IntegrableOn (fun w : ℝ => 2 * ‖logPoly a (U \ V) w‖ ^ (2 : ℕ))
        (Set.Icc (-W) W) volume := (hcontU.const_mul 2).integrableOn_Icc
    have hiV : IntegrableOn (fun w : ℝ => 2 * ‖logPoly a (V \ U) w‖ ^ (2 : ℕ))
        (Set.Icc (-W) W) volume := (hcontV.const_mul 2).integrableOn_Icc
    rw [integral_add hiU hiV, integral_const_mul, integral_const_mul]
  rw [hsplit] at hmono
  nlinarith [hmono, hEU, hEV]

/-- A harmonic Ramaré cofactor has norm at most its reciprocal index. -/
theorem norm_harmonicRamareCofactorCoeff_le_inv (P : Finset ℕ) (m : ℕ) :
    ‖harmonicRamareCofactorCoeff P m‖ ≤ 1 / (m : ℝ) := by
  have heq : harmonicRamareCofactorCoeff P m = ramareCofactorCoeff P m / (m : ℂ) := by
    rw [harmonicRamareCofactorCoeff, harmonicMoebiusC, ramareCofactorCoeff]
    ring
  rw [heq, norm_div, Complex.norm_natCast]
  exact div_le_div_of_nonneg_right (norm_ramareCofactorCoeff_le_one P m)
    (Nat.cast_nonneg m)

/-- Coefficient energy on support bounded below by `L`, in harmonic normalization. -/
theorem sum_normSq_harmonicRamareCofactorCoeff_le_card_div_sq
    (P S : Finset ℕ) {L : ℕ} (hL : 1 ≤ L) (hSL : ∀ m ∈ S, L ≤ m) :
    (∑ m ∈ S, ‖harmonicRamareCofactorCoeff P m‖ ^ (2 : ℕ))
      ≤ (S.card : ℝ) * (1 / (L : ℝ)) ^ (2 : ℕ) := by
  have hterm : ∀ m ∈ S, ‖harmonicRamareCofactorCoeff P m‖ ^ (2 : ℕ)
      ≤ (1 / (L : ℝ)) ^ (2 : ℕ) := by
    intro m hm
    have hLR : (0 : ℝ) < (L : ℝ) := by exact_mod_cast (Nat.zero_lt_of_lt hL)
    have hLm : (L : ℝ) ≤ (m : ℝ) := by exact_mod_cast hSL m hm
    have hinv : 1 / (m : ℝ) ≤ 1 / (L : ℝ) := one_div_le_one_div_of_le hLR hLm
    exact pow_le_pow_left₀ (norm_nonneg _)
      ((norm_harmonicRamareCofactorCoeff_le_inv P m).trans hinv) 2
  calc
    (∑ m ∈ S, ‖harmonicRamareCofactorCoeff P m‖ ^ (2 : ℕ))
        ≤ ∑ _m ∈ S, (1 / (L : ℝ)) ^ (2 : ℕ) := Finset.sum_le_sum hterm
    _ = (S.card : ℝ) * (1 / (L : ℝ)) ^ (2 : ℕ) := by
      rw [Finset.sum_const, nsmul_eq_mul]

/-- Exact harmonic mean-square cost of replacing a prime-dependent cofactor support in a narrow
prime block by its common interval. -/
theorem integral_Icc_normSq_harmonicRamareCofactor_sub_common_le
    {P : Finset ℕ} {A₀ B₀ : ℕ} {Q eta W : ℝ}
    (hA₀ : 1 ≤ A₀) (hQ : 0 < Q) (heta : 0 ≤ eta) (hW : 1 ≤ W) {p : ℕ}
    (hp0 : 0 < p) (hplo : Q < (p : ℝ)) (hphi : (p : ℝ) ≤ Q * (1 + eta))
    (hleft : 1 ≤ ⌈(A₀ : ℝ) / (Q * (1 + eta))⌉₊) :
    (∫ w in Set.Icc (-W) W,
      ‖harmonicRamareCofactorPoly P (Finset.Icc A₀ B₀) p w -
        logPoly (harmonicRamareCofactorCoeff P)
          (Finset.Icc ⌈(A₀ : ℝ) / (Q * (1 + eta))⌉₊ ⌊(B₀ : ℝ) / Q⌋₊) w‖ ^ (2 : ℕ))
      ≤ 2 * (5 * Real.pi / 2 * W +
          5 * Real.exp 1 / 2 * (⌊(B₀ : ℝ) / Q⌋₊ : ℝ)) *
        ((((A₀ : ℝ) + (B₀ : ℝ)) * eta / Q + 4 + ((B₀ : ℝ) / Q ^ (2 : ℕ) + 1)) *
          (1 / (⌈(A₀ : ℝ) / (Q * (1 + eta))⌉₊ : ℝ)) ^ (2 : ℕ)) := by
  classical
  let L : ℕ := ⌈(A₀ : ℝ) / (Q * (1 + eta))⌉₊
  let M : ℕ := ⌊(B₀ : ℝ) / Q⌋₊
  let U : Finset ℕ := {m ∈ ramareCofactorSet (Finset.Icc A₀ B₀) p | ¬ p ∣ m}
  let C : Finset ℕ := Finset.Icc L M
  have hUsubC : U ⊆ C := by
    simpa only [U, C, L, M] using
      cofactorFilter_subset_common_at A₀ B₀ hQ heta hp0 hplo hphi
  have hU0 : (0 : ℕ) ∉ U := by
    intro hm
    have hmem := (Finset.mem_filter.1 hm).1
    have hpm := (mem_ramareCofactorSet_iff hp0).1 hmem
    simp only [mul_zero, Finset.mem_Icc] at hpm
    omega
  have hC0 : (0 : ℕ) ∉ C := by
    intro hm
    have hmC := Finset.mem_Icc.1 hm
    change 1 ≤ L at hleft
    omega
  have hUM : ∀ m ∈ U, m ≤ M := fun m hm => (Finset.mem_Icc.1 (hUsubC hm)).2
  have hCM : ∀ m ∈ C, m ≤ M := fun m hm => (Finset.mem_Icc.1 hm).2
  have hbase := integral_Icc_normSq_logPoly_sub_le_energy
    (a := harmonicRamareCofactorCoeff P) hU0 hC0 hUM hCM hW
  have hUCempty : U \ C = ∅ := Finset.sdiff_eq_empty_iff_subset.2 hUsubC
  have henergy : (∑ m ∈ C \ U, ‖harmonicRamareCofactorCoeff P m‖ ^ (2 : ℕ))
      ≤ ((C \ U).card : ℝ) * (1 / (L : ℝ)) ^ (2 : ℕ) := by
    exact sum_normSq_harmonicRamareCofactorCoeff_le_card_div_sq P (C \ U) hleft
      (fun m hm => (Finset.mem_Icc.1 (Finset.mem_sdiff.1 hm).1).1)
  have hcard : ((C \ U).card : ℝ) ≤
      ((A₀ : ℝ) + (B₀ : ℝ)) * eta / Q + 4 + ((B₀ : ℝ) / Q ^ (2 : ℕ) + 1) := by
    simpa [C, U, L, M] using card_cofactor_symmDiff_le hQ heta hp0 hplo hphi
  have hweight : (0 : ℝ) ≤ (1 / (L : ℝ)) ^ (2 : ℕ) := sq_nonneg _
  have henergy' : (∑ m ∈ C \ U, ‖harmonicRamareCofactorCoeff P m‖ ^ (2 : ℕ))
      ≤ (((A₀ : ℝ) + (B₀ : ℝ)) * eta / Q + 4 + ((B₀ : ℝ) / Q ^ (2 : ℕ) + 1)) *
          (1 / (L : ℝ)) ^ (2 : ℕ) :=
    henergy.trans (mul_le_mul_of_nonneg_right hcard hweight)
  rw [hUCempty, Finset.sum_empty, zero_add] at hbase
  change (∫ w in Set.Icc (-W) W,
      ‖logPoly (harmonicRamareCofactorCoeff P) U w -
        logPoly (harmonicRamareCofactorCoeff P) C w‖ ^ (2 : ℕ)) ≤ _
  change (∫ w in Set.Icc (-W) W,
      ‖logPoly (harmonicRamareCofactorCoeff P) U w -
        logPoly (harmonicRamareCofactorCoeff P) C w‖ ^ (2 : ℕ)) ≤ _ at hbase
  dsimp only [M] at hbase
  refine hbase.trans ?_
  have hcoef : (0 : ℝ) ≤ 2 * (5 * Real.pi / 2 * W +
      5 * Real.exp 1 / 2 * (⌊(B₀ : ℝ) / Q⌋₊ : ℝ)) := by positivity
  dsimp only [L] at henergy'
  exact mul_le_mul_of_nonneg_left henergy' hcoef

end

end RHTower.Sieve
