import GaloisForLFunctions.ArithmeticCountingPositivity.PrimeParityRamanujanCoordinates

/-!
# Harmonic density of finitely many prime flips

Adding one flipped prime gives an exact recurrence under division of the
horizon. The harmonic shell is bounded, and the recurrence contracts its
error. Finite-set induction yields a positive product density with bounded
error. The squared-correlation inequality converts it into a prime gap.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity
  GaloisForLFunctions.ArithmeticElectrostatics

/-- The harmonic density contributed by a finite set of prime-parity flips. -/
def finiteFlipHarmonicDensity (F : Finset ℕ) : ℝ :=
  ∏ p ∈ F, ((p : ℝ) - 1) / ((p : ℝ) + 1)

theorem finiteFlipHarmonicDensity_pos {F : Finset ℕ} (hF : ∀ p ∈ F, p.Prime) :
    0 < finiteFlipHarmonicDensity F := by
  apply prod_pos
  intro p hp
  have hp1 : (1 : ℝ) < p := by exact_mod_cast (hF p hp).one_lt
  exact div_pos (sub_pos.mpr hp1) (by positivity)

theorem finiteFlipHarmonicDensity_le_one {F : Finset ℕ} (hF : ∀ p ∈ F, p.Prime) :
    finiteFlipHarmonicDensity F ≤ 1 := by
  apply prod_le_one
  · intro p hp
    have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast (hF p hp).one_le
    exact div_nonneg (sub_nonneg.mpr hp1) (by positivity)
  · intro p _
    apply (div_le_one (by positivity : (0 : ℝ) < (p : ℝ) + 1)).mpr
    linarith

private theorem finiteFlipHarmonicDensity_insert {F : Finset ℕ} {p : ℕ} (hpF : p ∉ F) :
    finiteFlipHarmonicDensity (insert p F) =
      ((p : ℝ) - 1) / ((p : ℝ) + 1) * finiteFlipHarmonicDensity F :=
  prod_insert hpF

private theorem finiteFlip_insert {F : Finset ℕ} {p : ℕ} (hpF : p ∉ F) (n : ℕ) :
    finiteFlip (insert p F) n = (-1 : ℝ) ^ n.factorization p * finiteFlip F n :=
  prod_insert hpF

private theorem finiteFlip_unflipped_prime {F : Finset ℕ} {p : ℕ}
    (hp : p.Prime) (hpF : p ∉ F) : finiteFlip F p = 1 := by
  apply prod_eq_one
  intro q hq
  rw [hp.factorization, Finsupp.single_eq_of_ne (ne_of_mem_of_not_mem hq hpF), pow_zero]

/-- Adding a flipped prime exchanges the signs of its exact divisibility fibre. -/
theorem finiteFlip_harmonic_recurrence {F : Finset ℕ} {p : ℕ}
    (hp : p.Prime) (hpF : p ∉ F) (N : ℕ) :
    (p : ℝ) * gaugeHarmonicSum (finiteFlip (insert p F)) N +
        gaugeHarmonicSum (finiteFlip (insert p F)) (N / p) =
      (p : ℝ) * gaugeHarmonicSum (finiteFlip F) N -
        gaugeHarmonicSum (finiteFlip F) (N / p) := by
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hFp := finiteFlip_unflipped_prime hp hpF
  have hGp : finiteFlip (insert p F) p = -1 := by
    rw [finiteFlip_insert hpF, hp.factorization_self, pow_one, hFp, mul_one]
  have hsame {n : ℕ} (hn : ¬ p ∣ n) :
      finiteFlip (insert p F) n = finiteFlip F n := by
    rw [finiteFlip_insert hpF, Nat.factorization_eq_zero_of_not_dvd hn, pow_zero, one_mul]
  have hdiff : gaugeHarmonicSum (finiteFlip F) N -
      gaugeHarmonicSum (finiteFlip (insert p F)) N =
      (∑ n ∈ (Icc 1 N).filter (p ∣ ·), finiteFlip F n / n) -
        ∑ n ∈ (Icc 1 N).filter (p ∣ ·), finiteFlip (insert p F) n / n := by
    rw [gaugeHarmonicSum, gaugeHarmonicSum, ← sum_sub_distrib,
      ← sum_sub_distrib, sum_filter]
    refine sum_congr rfl fun n _ => ?_
    by_cases hn : p ∣ n
    · rw [if_pos hn]
    · rw [if_neg hn, hsame hn, sub_self]
  rw [gaugeHarmonicSum_multiples _ (finiteFlip_isSignGauge F) hp.pos,
    gaugeHarmonicSum_multiples _ (finiteFlip_isSignGauge (insert p F)) hp.pos,
    hFp, hGp] at hdiff
  field_simp [hp0] at hdiff
  linarith only [hdiff]

private theorem harmonicMass_shell {d : ℕ} (hd : 0 < d) (N : ℕ) :
    0 ≤ gaugeHarmonicSum (fun _ => 1) N - gaugeHarmonicSum (fun _ => 1) (N / d) ∧
      gaugeHarmonicSum (fun _ => 1) N - gaugeHarmonicSum (fun _ => 1) (N / d) ≤
        1 + Real.log d := by
  constructor
  · apply sub_nonneg.mpr
    apply sum_le_sum_of_subset_of_nonneg
    · intro n hn
      exact mem_Icc.mpr ⟨(mem_Icc.mp hn).1,
        (mem_Icc.mp hn).2.trans (Nat.div_le_self N d)⟩
    · intro n _ _
      positivity
  · have h := roughHarmonic_sub_div_le 0 N hd
    simpa only [roughHarmonic, roughInterval_zero, gaugeHarmonicSum] using h

/-- Every finite collection of prime flips has a uniformly bounded harmonic error. -/
theorem finiteFlip_harmonic_error_bounded (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ N : ℕ,
      |gaugeHarmonicSum (finiteFlip F) N -
        finiteFlipHarmonicDensity F * gaugeHarmonicSum (fun _ => 1) N| ≤ K := by
  revert hF
  induction F using Finset.induction_on with
  | empty =>
      intro _
      refine ⟨0, le_rfl, fun N => ?_⟩
      simp only [gaugeHarmonicSum, finiteFlip, finiteFlipHarmonicDensity, prod_empty, one_mul,
        sub_self, abs_zero, le_refl]
  | @insert p F hpF ih =>
      intro hF
      have hp := hF p (mem_insert_self p F)
      have hF' : ∀ q ∈ F, q.Prime := fun q hq => hF q (mem_insert_of_mem hq)
      obtain ⟨K, hK, hbound⟩ := ih hF'
      let c := finiteFlipHarmonicDensity F
      let L := 1 + Real.log p
      let C := 3 * K + 2 * L
      let E (M : ℕ) := gaugeHarmonicSum (finiteFlip (insert p F)) M -
        finiteFlipHarmonicDensity (insert p F) * gaugeHarmonicSum (fun _ => 1) M
      let Eold (M : ℕ) := gaugeHarmonicSum (finiteFlip F) M -
        c * gaugeHarmonicSum (fun _ => 1) M
      let a := 2 * c * (p : ℝ) / ((p : ℝ) + 1)
      have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
      have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
      have hp1 : (0 : ℝ) < (p : ℝ) + 1 := by positivity
      have hc : 0 ≤ c := (finiteFlipHarmonicDensity_pos hF').le
      have hc1 : c ≤ 1 := finiteFlipHarmonicDensity_le_one hF'
      have hL : 0 ≤ L := by
        have hlog : 0 ≤ Real.log p := Real.log_nonneg (by exact_mod_cast hp.one_le)
        dsimp only [L]
        linarith only [hlog]
      have hC : 0 ≤ C := by dsimp only [C]; positivity
      have ha0 : 0 ≤ a := by dsimp only [a]; positivity
      have ha2 : a ≤ 2 := by
        dsimp only [a]
        rw [div_le_iff₀ hp1]
        have hcp := mul_le_mul_of_nonneg_right hc1 hp0.le
        nlinarith only [hcp]
      refine ⟨C, hC, ?_⟩
      change ∀ N : ℕ, |E N| ≤ C
      intro N
      induction N using Nat.strong_induction_on with
      | h N ihN =>
          by_cases hN : N = 0
          · subst N
            simpa [E, gaugeHarmonicSum] using hC
          have hN0 : 0 < N := Nat.pos_of_ne_zero hN
          have hsmall : |E (N / p)| ≤ C := ihN (N / p) (Nat.div_lt_self hN0 hp.one_lt)
          have hshell := harmonicMass_shell hp.pos N
          have hcost : |a * (gaugeHarmonicSum (fun _ => 1) N -
              gaugeHarmonicSum (fun _ => 1) (N / p))| ≤ 2 * L := by
            rw [abs_of_nonneg (mul_nonneg ha0 hshell.1)]
            exact (mul_le_mul_of_nonneg_right ha2 hshell.1).trans
              (mul_le_mul_of_nonneg_left hshell.2 (by norm_num))
          have hrec := finiteFlip_harmonic_recurrence hp hpF N
          -- Subtracting the product means leaves only a bounded harmonic shell.
          have he : (p : ℝ) * E N =
              (p : ℝ) * Eold N - Eold (N / p) +
                a * (gaugeHarmonicSum (fun _ => 1) N -
                  gaugeHarmonicSum (fun _ => 1) (N / p)) - E (N / p) := by
            dsimp only [E, Eold, a, c]
            rw [finiteFlipHarmonicDensity_insert hpF]
            field_simp [hp1.ne']
            linear_combination ((p : ℝ) + 1) * hrec
          have htriangle : (p : ℝ) * |E N| ≤ (p + 1) * K + 2 * L + C := by
            calc
              (p : ℝ) * |E N| = |(p : ℝ) * E N| := by rw [abs_mul, abs_of_pos hp0]
              _ = |(p : ℝ) * Eold N - Eold (N / p) +
                  a * (gaugeHarmonicSum (fun _ => 1) N -
                    gaugeHarmonicSum (fun _ => 1) (N / p)) - E (N / p)| := congrArg abs he
              _ ≤ |(p : ℝ) * Eold N| + |Eold (N / p)| +
                  |a * (gaugeHarmonicSum (fun _ => 1) N -
                    gaugeHarmonicSum (fun _ => 1) (N / p))| + |E (N / p)| := by
                have h1 := abs_sub ((p : ℝ) * Eold N - Eold (N / p) +
                  a * (gaugeHarmonicSum (fun _ => 1) N -
                    gaugeHarmonicSum (fun _ => 1) (N / p))) (E (N / p))
                have h2 := abs_add_le ((p : ℝ) * Eold N - Eold (N / p))
                  (a * (gaugeHarmonicSum (fun _ => 1) N -
                    gaugeHarmonicSum (fun _ => 1) (N / p)))
                have h3 := abs_sub ((p : ℝ) * Eold N) (Eold (N / p))
                linarith only [h1, h2, h3]
              _ ≤ (p : ℝ) * K + K + 2 * L + C := by
                apply add_le_add (add_le_add (add_le_add ?_ (hbound (N / p))) hcost) hsmall
                rw [abs_mul, abs_of_pos hp0]
                exact mul_le_mul_of_nonneg_left (hbound N) hp0.le
              _ = _ := by ring
          have hpay : (p + 1) * K + 2 * L + C ≤ (p : ℝ) * C := by
            -- The contraction closes with C = 3K + 2L for every prime p >= 2.
            have h := mul_nonneg (sub_nonneg.mpr hp2) (add_nonneg hK hL)
            dsimp only [C]
            nlinarith only [h]
          exact le_of_mul_le_mul_left (htriangle.trans hpay) hp0

/-- The exact finite-prime harmonic mean is the product of the local parity means. -/
theorem finiteFlip_harmonicCorrelation_tendsto {F : Finset ℕ} (hF : ∀ p ∈ F, p.Prime) :
    Tendsto (harmonicCorrelation (finiteFlip F)) atTop (𝓝 (finiteFlipHarmonicDensity F)) := by
  obtain ⟨K, _, hbound⟩ := finiteFlip_harmonic_error_bounded F hF
  rw [Metric.tendsto_atTop]
  intro ε hε
  have hlog : Tendsto (fun N : ℕ => Real.log N) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.mp (hlog.eventually_gt_atTop (K / ε))
  refine ⟨max 1 N₀, fun N hN => ?_⟩
  have hN1 : 1 ≤ N := (le_max_left _ _).trans hN
  have hH := gaugeHarmonicSum_one_pos hN1
  have hlarge : K / ε < gaugeHarmonicSum (fun _ => 1) N :=
    (hN₀ N ((le_max_right _ _).trans hN)).trans_le (log_le_gaugeHarmonicSum_one hN1)
  have hsmall : K / gaugeHarmonicSum (fun _ => 1) N < ε := by
    rw [div_lt_iff₀ hε] at hlarge
    rw [div_lt_iff₀ hH]
    nlinarith only [hlarge]
  have he : harmonicCorrelation (finiteFlip F) N - finiteFlipHarmonicDensity F =
      (gaugeHarmonicSum (finiteFlip F) N -
        finiteFlipHarmonicDensity F * gaugeHarmonicSum (fun _ => 1) N) /
          gaugeHarmonicSum (fun _ => 1) N := by
    rw [harmonicCorrelation]
    field_simp [hH.ne']
  rw [Real.dist_eq, he, abs_div, abs_of_pos hH]
  exact (div_le_div_of_nonneg_right (hbound N) hH.le).trans_lt hsmall

/-- Every fixed finite set of prime flips retains the gap paid by its exact mean. -/
theorem finiteFlip_hasHyperplaneGap {F : Finset ℕ} (hF : ∀ p ∈ F, p.Prime) :
    HasHyperplaneGap (finiteFlip F) (2 * Real.log 2 * finiteFlipHarmonicDensity F ^ 2) := by
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  obtain ⟨N₀, hN₀⟩ := eventually_prime_gap_ge_squared_correlation hε2
  have hlim := ((finiteFlip_harmonicCorrelation_tendsto hF).pow 2).const_mul (2 * Real.log 2)
  have hevent : ∀ᶠ N : ℕ in atTop,
      2 * Real.log 2 * finiteFlipHarmonicDensity F ^ 2 - ε / 2 <
        2 * Real.log 2 * harmonicCorrelation (finiteFlip F) N ^ 2 :=
    hlim.eventually (lt_mem_nhds (sub_lt_self _ hε2))
  obtain ⟨N₁, hN₁⟩ := eventually_atTop.mp hevent
  refine ⟨max N₀ N₁, fun N hN x hx => ?_⟩
  have hsign (n : ℕ) : finiteFlip F n * finiteFlip F n = 1 := by
    by_cases hn : n = 0
    · subst n
      simp [finiteFlip]
    · exact (finiteFlip_isSignGauge F).mul_self hn
  have h := hN₀ N ((le_max_left _ _).trans hN) (finiteFlip F) hsign x hx
  have hcoeff := hN₁ N ((le_max_right _ _).trans hN)
  have hmass : 0 ≤ ∑ n ∈ Icc 1 N, x n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hpay := mul_le_mul_of_nonneg_right hcoeff.le hmass
  linarith only [h, hpay]

end GaloisForLFunctions.ArithmeticCountingPositivity
