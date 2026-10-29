import GaloisForLFunctions.ArithmeticCountingPositivity.OneDyadicProbeSelectsTheFinitePrimeSource

/-!
# Conductor mass controls loss of a finite-prime gap

Adding prime flips adds nonnegative conductor weights. Their exact total
mass bounds the whole secular increment, including every omitted conductor.
The reciprocal ground term then gives a square-root modulus for the greatest
gap. A remote prime changes a fixed constraint by a quantitatively small amount.
-/

noncomputable section

open Finset Filter Topology

namespace GaloisForLFunctions.ArithmeticCountingPositivity

open GaloisForLFunctions.RenormalizedArithmeticPotentialTheory
  GaloisForLFunctions.SelectiveMultiscaleArithmeticPositivity

open private conductor_energy_gap conductor_weight_nonneg from
  GaloisForLFunctions.ArithmeticCountingPositivity.FinitePrimeCountsDetermineTheFullResolvent
open private spectralWeight_one from
  GaloisForLFunctions.ArithmeticCountingPositivity.FinitePrimeFlipsHaveUnitConductorMass

local notation "γ" => Real.eulerMascheroniConstant
local notation "g₀" => 2 * Real.log 2

/-- The unnormalized conductor mass is the reciprocal squared harmonic mean. -/
theorem hasSum_finiteFlipSpectralWeight (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime) :
    HasSum (finiteFlipSpectralWeight F) (1 / finiteFlipHarmonicDensity F ^ 2) := by
  have hc : finiteFlipHarmonicDensity F ^ 2 ≠ 0 :=
    pow_ne_zero 2 (finiteFlipHarmonicDensity_pos hF).ne'
  have h := (hasSum_finiteFlipConductorCoefficient_sq F hF).mul_left
    (1 / finiteFlipHarmonicDensity F ^ 2)
  have he : (fun m : ℕ => (1 / finiteFlipHarmonicDensity F ^ 2) *
      finiteFlipConductorCoefficient F m ^ 2) = finiteFlipSpectralWeight F := by
    funext m
    rw [finiteFlipConductorCoefficient_sq, one_div, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]
  simpa only [he, mul_one] using h

private theorem conductor_weight_zero (F : Finset ℕ) : finiteFlipSpectralWeight F 0 = 0 := by
  simp [finiteFlipSpectralWeight]

private theorem hasSum_conductor_mass_increment {F G : Finset ℕ}
    (hF : ∀ p ∈ F, p.Prime) (hG : ∀ p ∈ G, p.Prime) :
    HasSum (fun k : ℕ => finiteFlipSpectralWeight G (k + 2) -
      finiteFlipSpectralWeight F (k + 2))
      (1 / finiteFlipHarmonicDensity G ^ 2 - 1 / finiteFlipHarmonicDensity F ^ 2) := by
  let D : ℕ → ℝ := fun m => finiteFlipSpectralWeight G m - finiteFlipSpectralWeight F m
  have h := (hasSum_finiteFlipSpectralWeight G hG).sub (hasSum_finiteFlipSpectralWeight F hF)
  have hs : Summable D := h.summable
  have hs1 : Summable (fun k : ℕ => D (k + 1)) := (summable_nat_add_iff 1).mpr hs
  have hs2 : Summable (fun k : ℕ => D (k + 2)) := (summable_nat_add_iff 2).mpr hs
  have hz : D 0 = 0 := by simp only [D, conductor_weight_zero, sub_self]
  have ho : D 1 = 0 := by simp only [D, spectralWeight_one, sub_self]
  have hv : (∑' m : ℕ, D m) =
      1 / finiteFlipHarmonicDensity G ^ 2 - 1 / finiteFlipHarmonicDensity F ^ 2 := h.tsum_eq
  rw [hs.tsum_eq_zero_add, hs1.tsum_eq_zero_add] at hv
  change D 0 + (D 1 + ∑' k : ℕ, D (k + 2)) = _ at hv
  simp only [hz, ho, zero_add] at hv
  simpa only [hv] using hs2.hasSum

/-- Added conductor mass bounds the complete secular increment below the first
excitation. No spectral tail is discarded. -/
theorem finiteFlipSecular_increment_le {F G : Finset ℕ} (hFG : F ⊆ G)
    (hG : ∀ p ∈ G, p.Prime) {s : ℝ} (hs : 0 < s) (hs2 : s < g₀) :
    finiteFlipSecular G s - finiteFlipSecular F s ≤
      (1 / finiteFlipHarmonicDensity G ^ 2 - 1 / finiteFlipHarmonicDensity F ^ 2) /
        (g₀ - s) := by
  have hF : ∀ p ∈ F, p.Prime := fun p hp => hG p (hFG hp)
  have hseries : HasSum (fun k : ℕ =>
      (finiteFlipSpectralWeight G (k + 2) - finiteFlipSpectralWeight F (k + 2)) /
        (ramanujanAdjunctionEnergy (k + 2) - γ - s))
      (finiteFlipSecular G s - finiteFlipSecular F s) := by
    have h := (summable_finiteFlipSecularTail G hG hs hs2).hasSum.sub
      (summable_finiteFlipSecularTail F hF hs hs2).hasSum
    have he : (∑' k : ℕ, finiteFlipSpectralWeight G (k + 2) /
        (ramanujanAdjunctionEnergy (k + 2) - γ - s)) -
        (∑' k : ℕ, finiteFlipSpectralWeight F (k + 2) /
        (ramanujanAdjunctionEnergy (k + 2) - γ - s)) =
        finiteFlipSecular G s - finiteFlipSecular F s := by
      unfold finiteFlipSecular
      ring
    rw [he] at h
    exact h.congr_fun fun k => by rw [sub_div]
  have hmajor := (hasSum_conductor_mass_increment hF hG).div_const (g₀ - s)
  have h := hseries.summable.tsum_mono hmajor.summable (fun k =>
    div_le_div_of_nonneg_left (sub_nonneg.mpr (finiteFlipSpectralWeight_mono hFG _))
      (sub_pos.mpr hs2) (sub_le_sub_right (conductor_energy_gap k) s))
  rwa [hseries.tsum_eq, hmajor.tsum_eq] at h

private theorem conductor_mass_increment_nonneg {F G : Finset ℕ} (hFG : F ⊆ G)
    (hG : ∀ p ∈ G, p.Prime) :
    0 ≤ 1 / finiteFlipHarmonicDensity G ^ 2 - 1 / finiteFlipHarmonicDensity F ^ 2 := by
  have h := (hasSum_finiteFlipSpectralWeight G hG).sub
    (hasSum_finiteFlipSpectralWeight F (fun p hp => hG p (hFG hp)))
  rw [← h.tsum_eq]
  exact tsum_nonneg fun m => sub_nonneg.mpr (finiteFlipSpectralWeight_mono hFG m)

private theorem secular_positive_tail_mono (F : Finset ℕ) (hF : ∀ p ∈ F, p.Prime)
    {s t : ℝ} (hs : 0 < s) (hst : s < t) (ht : t < g₀) :
    finiteFlipSecular F s + 1 / s ≤ finiteFlipSecular F t + 1 / t := by
  have h := Summable.tsum_mono
    (summable_finiteFlipSecularTail F hF hs (hst.trans ht))
    (summable_finiteFlipSecularTail F hF (hs.trans hst) ht)
    (fun k => div_le_div_of_nonneg_left (conductor_weight_nonneg F _)
      (sub_pos.mpr (ht.trans_le (conductor_energy_gap k)))
      (sub_le_sub_left hst.le _))
  dsimp only [finiteFlipSecular]
  linarith only [h]

/-- Gap loss times the remaining excitation margin is bounded by added
conductor mass times the two attained gaps. The ceiling endpoint is included. -/
theorem finiteFlipGreatestGap_loss_mul_ceiling_le {F G : Finset ℕ} (hFG : F ⊆ G)
    (hG : ∀ p ∈ G, p.Prime) :
    (finiteFlipGreatestGap F - finiteFlipGreatestGap G) * (g₀ - finiteFlipGreatestGap G) ≤
      (finiteFlipGreatestGap G * finiteFlipGreatestGap F) *
      (1 / finiteFlipHarmonicDensity G ^ 2 - 1 / finiteFlipHarmonicDensity F ^ 2) := by
  have hF : ∀ p ∈ F, p.Prime := fun p hp => hG p (hFG hp)
  have hFpos := finiteFlipGreatestGap_pos F hF
  have hGpos := finiteFlipGreatestGap_pos G hG
  have hFmax := (finiteFlipGreatestGap_bounds F hF).2
  have hmass := conductor_mass_increment_nonneg hFG hG
  have hle := finiteFlipGreatestGap_antitone hFG hG
  rcases lt_or_eq_of_le hle with hlt | heq
  · have hGbelow := hlt.trans_le hFmax
    have hz := finiteFlipSecular_greatestGap_eq_zero G hG hGbelow
    have hincrement := finiteFlipSecular_increment_le hFG hG hGpos hGbelow
    have hchar := (finiteFlip_hasHyperplaneGap_iff_secular F hF _).mp
      (isGreatest_finiteFlip_hyperplaneGap F hF).1
    have hnear : ∀ᶠ t : ℝ in 𝓝[<] (finiteFlipGreatestGap F), finiteFlipGreatestGap G < t :=
      (lt_mem_nhds hlt).filter_mono nhdsWithin_le_nhds
    have hbefore : ∀ᶠ t : ℝ in 𝓝[<] (finiteFlipGreatestGap F), t < finiteFlipGreatestGap F :=
      self_mem_nhdsWithin
    have hevent : ∀ᶠ t : ℝ in 𝓝[<] (finiteFlipGreatestGap F),
        1 / finiteFlipGreatestGap G - 1 / t ≤
          (1 / finiteFlipHarmonicDensity G ^ 2 - 1 / finiteFlipHarmonicDensity F ^ 2) /
            (g₀ - finiteFlipGreatestGap G) := by
      filter_upwards [hnear, hbefore] with t hGt htF
      have htail := secular_positive_tail_mono F hF hGpos hGt (htF.trans_le hFmax)
      have hsign := hchar.2 t (hGpos.trans hGt) htF
      linarith only [htail, hsign, hincrement, hz]
    have hlim : Tendsto (fun t : ℝ => 1 / finiteFlipGreatestGap G - 1 / t)
        (𝓝[<] (finiteFlipGreatestGap F))
        (𝓝 (1 / finiteFlipGreatestGap G - 1 / finiteFlipGreatestGap F)) :=
      (tendsto_const_nhds.sub
        (tendsto_const_nhds.div tendsto_id hFpos.ne')).mono_left nhdsWithin_le_nhds
    have hbound := le_of_tendsto hlim hevent
    have hrec : 1 / finiteFlipGreatestGap G - 1 / finiteFlipGreatestGap F =
        (finiteFlipGreatestGap F - finiteFlipGreatestGap G) /
          (finiteFlipGreatestGap G * finiteFlipGreatestGap F) := by
      field_simp [hGpos.ne', hFpos.ne']
    rw [hrec] at hbound
    have hprod := (div_le_div_iff₀ (mul_pos hGpos hFpos) (sub_pos.mpr hGbelow)).mp hbound
    exact hprod.trans_eq (mul_comm _ _)
  · rw [← heq, sub_self, zero_mul]
    exact mul_nonneg (mul_nonneg hGpos.le hGpos.le) hmass

/-- The squared loss of the greatest gap is paid by the total added conductor
mass, uniformly across both interior roots and the maximal plateau. -/
theorem finiteFlipGreatestGap_loss_sq_le {F G : Finset ℕ} (hFG : F ⊆ G)
    (hG : ∀ p ∈ G, p.Prime) :
    (finiteFlipGreatestGap F - finiteFlipGreatestGap G) ^ 2 ≤ g₀ ^ 2 *
      (1 / finiteFlipHarmonicDensity G ^ 2 - 1 / finiteFlipHarmonicDensity F ^ 2) := by
  have hF : ∀ p ∈ F, p.Prime := fun p hp => hG p (hFG hp)
  have hFpos := finiteFlipGreatestGap_pos F hF
  have hGpos := finiteFlipGreatestGap_pos G hG
  have hFmax := (finiteFlipGreatestGap_bounds F hF).2
  have hGmax := (finiteFlipGreatestGap_bounds G hG).2
  have hle := finiteFlipGreatestGap_antitone hFG hG
  have hmass := conductor_mass_increment_nonneg hFG hG
  have henergy : finiteFlipGreatestGap G * finiteFlipGreatestGap F ≤ g₀ ^ 2 := by
    simpa only [sq] using mul_le_mul hGmax hFmax hFpos.le (hGpos.trans_le hGmax).le
  calc
    _ ≤ (finiteFlipGreatestGap F - finiteFlipGreatestGap G) *
        (g₀ - finiteFlipGreatestGap G) := by
      rw [sq]
      exact mul_le_mul_of_nonneg_left (sub_le_sub_right hFmax _) (sub_nonneg.mpr hle)
    _ ≤ (finiteFlipGreatestGap G * finiteFlipGreatestGap F) *
        (1 / finiteFlipHarmonicDensity G ^ 2 - 1 / finiteFlipHarmonicDensity F ^ 2) :=
      finiteFlipGreatestGap_loss_mul_ceiling_le hFG hG
    _ ≤ _ := mul_le_mul_of_nonneg_right henergy hmass

private theorem inserted_prime_mass_increment {F : Finset ℕ} (hF : ∀ q ∈ F, q.Prime)
    {p : ℕ} (hp : p.Prime) (hpF : p ∉ F) :
    1 / finiteFlipHarmonicDensity (insert p F) ^ 2 - 1 / finiteFlipHarmonicDensity F ^ 2 =
      (4 * (p : ℝ) / ((p : ℝ) - 1) ^ 2) / finiteFlipHarmonicDensity F ^ 2 := by
  have hp1 : (p : ℝ) - 1 ≠ 0 := (sub_pos.mpr (by exact_mod_cast hp.one_lt)).ne'
  have hpp : (p : ℝ) + 1 ≠ 0 := by positivity
  have hc := (finiteFlipHarmonicDensity_pos hF).ne'
  have he : finiteFlipHarmonicDensity (insert p F) =
      (((p : ℝ) - 1) / ((p : ℝ) + 1)) * finiteFlipHarmonicDensity F := prod_insert hpF
  rw [he]
  field_simp [hp1, hpp, hc]
  ring

private theorem prime_mass_increment_le {p : ℕ} (hp : p.Prime) :
    4 * (p : ℝ) / ((p : ℝ) - 1) ^ 2 ≤ 16 / (p : ℝ) := by
  have hp2 : (2 : ℝ) ≤ p := by exact_mod_cast hp.two_le
  have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
  have hp1 : 0 < (p : ℝ) - 1 := by linarith only [hp2]
  rw [div_le_div_iff₀ (sq_pos_of_pos hp1) hp0]
  nlinarith only [mul_nonneg (sub_nonneg.mpr hp2)
    (by linarith only [hp2] : 0 ≤ 3 * (p : ℝ) - 2)]

/-- Flipping a prime p changes any fixed finite-prime gap by at most a constant
times p^(-1/2), with its harmonic mean retained explicitly. -/
theorem finiteFlipGreatestGap_insert_loss_sq_le (F : Finset ℕ)
    (hF : ∀ q ∈ F, q.Prime) {p : ℕ} (hp : p.Prime) :
    (finiteFlipGreatestGap F - finiteFlipGreatestGap (insert p F)) ^ 2 ≤
      16 * g₀ ^ 2 / ((p : ℝ) * finiteFlipHarmonicDensity F ^ 2) := by
  classical
  have hG : ∀ q ∈ insert p F, q.Prime := by
    intro q hq
    rcases mem_insert.mp hq with he | hq
    · simpa only [he] using hp
    · exact hF q hq
  by_cases hpF : p ∈ F
  · rw [insert_eq_of_mem hpF, sub_self, zero_pow (by decide : (2 : ℕ) ≠ 0)]
    positivity
  · have h := finiteFlipGreatestGap_loss_sq_le (subset_insert p F) hG
    rw [inserted_prime_mass_increment hF hp hpF] at h
    calc
      _ ≤ g₀ ^ 2 * ((4 * (p : ℝ) / ((p : ℝ) - 1) ^ 2) /
          finiteFlipHarmonicDensity F ^ 2) := h
      _ ≤ g₀ ^ 2 * ((16 / (p : ℝ)) / finiteFlipHarmonicDensity F ^ 2) :=
        mul_le_mul_of_nonneg_left
          (div_le_div_of_nonneg_right (prime_mass_increment_le hp) (sq_nonneg _))
          (sq_nonneg _)
      _ = _ := by ring

/-- At the fixed interior dyadic calibration, the loss caused by a prime p
is bounded by an explicit constant times 1/p. -/
theorem dyadicGreatestGap_prime_response_loss_le {p : ℕ} (hp : p.Prime) :
    finiteFlipGreatestGap {2} - finiteFlipGreatestGap (insert p {2}) ≤
      (16 * g₀ ^ 2 / ((p : ℝ) * finiteFlipHarmonicDensity {2} ^ 2)) /
        (g₀ - finiteFlipGreatestGap {2}) := by
  classical
  have h2 : ∀ q ∈ ({2} : Finset ℕ), q.Prime := by
    intro q hq
    have he : q = 2 := mem_singleton.mp hq
    subst q
    exact Nat.prime_two
  have hmargin : 0 < g₀ - finiteFlipGreatestGap {2} :=
    sub_pos.mpr dyadicFlipGreatestGap_lt_ceiling
  by_cases hp2 : p ∈ ({2} : Finset ℕ)
  · rw [insert_eq_of_mem hp2, sub_self]
    positivity
  · have hG : ∀ q ∈ insert p ({2} : Finset ℕ), q.Prime := by
      intro q hq
      rcases mem_insert.mp hq with he | hq
      · simpa only [he] using hp
      · exact h2 q hq
    have hsub : ({2} : Finset ℕ) ⊆ insert p {2} := subset_insert p {2}
    have hle := finiteFlipGreatestGap_antitone hsub hG
    have hmass := conductor_mass_increment_nonneg hsub hG
    have henergy : finiteFlipGreatestGap (insert p {2}) * finiteFlipGreatestGap {2} ≤ g₀ ^ 2 := by
      simpa only [sq] using mul_le_mul (finiteFlipGreatestGap_bounds _ hG).2
        (finiteFlipGreatestGap_bounds _ h2).2 (finiteFlipGreatestGap_pos _ h2).le
        ((finiteFlipGreatestGap_pos _ h2).trans_le (finiteFlipGreatestGap_bounds _ h2).2).le
    have hprod := (finiteFlipGreatestGap_loss_mul_ceiling_le hsub hG).trans
      (mul_le_mul_of_nonneg_right henergy hmass)
    rw [inserted_prime_mass_increment h2 hp hp2] at hprod
    have hpaid :
        (finiteFlipGreatestGap {2} - finiteFlipGreatestGap (insert p {2})) *
          (g₀ - finiteFlipGreatestGap (insert p {2})) ≤
        16 * g₀ ^ 2 / ((p : ℝ) * finiteFlipHarmonicDensity {2} ^ 2) := by
      calc
        _ ≤ g₀ ^ 2 * ((4 * (p : ℝ) / ((p : ℝ) - 1) ^ 2) /
            finiteFlipHarmonicDensity {2} ^ 2) := hprod
        _ ≤ g₀ ^ 2 * ((16 / (p : ℝ)) / finiteFlipHarmonicDensity {2} ^ 2) :=
          mul_le_mul_of_nonneg_left
            (div_le_div_of_nonneg_right (prime_mass_increment_le hp) (sq_nonneg _))
            (sq_nonneg _)
        _ = _ := by ring
    apply (le_div_iff₀ hmargin).mpr
    exact (mul_le_mul_of_nonneg_left (sub_le_sub_left hle _) (sub_nonneg.mpr hle)).trans hpaid

/-- Every fixed positive tolerance in the dyadic response admits a nontrivial
remote prime flip whose original greatest gap is still maximal. -/
theorem exists_maximal_flip_with_almost_unchanged_dyadic_gap (B : ℕ)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ p : ℕ, p.Prime ∧ B < p ∧ 11 ≤ p ∧
      IsGreatest {g : ℝ | HasHyperplaneGap (finiteFlip {p}) g} g₀ ∧
      finiteFlipGreatestGap {2} - ε < finiteFlipGreatestGap (insert p {2}) ∧
      finiteFlipGreatestGap (insert p {2}) < finiteFlipGreatestGap {2} := by
  have h2 : ∀ q ∈ ({2} : Finset ℕ), q.Prime := by
    intro q hq
    have he : q = 2 := mem_singleton.mp hq
    subst q
    exact Nat.prime_two
  let C : ℝ := 16 * g₀ ^ 2 / finiteFlipHarmonicDensity {2} ^ 2
  have hεsq : 0 < ε ^ 2 := sq_pos_of_pos hε
  obtain ⟨k, hk⟩ := exists_nat_gt (C / ε ^ 2)
  obtain ⟨p, hkp, hp⟩ := Nat.exists_infinite_primes (max 11 (max (B + 1) k))
  have hp11 : 11 ≤ p := (le_max_left _ _).trans hkp
  have hBk : max (B + 1) k ≤ p := (le_max_right _ _).trans hkp
  have hBp : B < p := by
    have hh := (le_max_left (B + 1) k).trans hBk
    omega
  have hsmall : 16 * g₀ ^ 2 / ((p : ℝ) * finiteFlipHarmonicDensity {2} ^ 2) < ε ^ 2 := by
    have hlarge : C / ε ^ 2 < (p : ℝ) :=
      hk.trans_le (by exact_mod_cast (le_max_right (B + 1) k).trans hBk)
    have hp0 : (0 : ℝ) < p := by exact_mod_cast hp.pos
    have hnum : C < (p : ℝ) * ε ^ 2 := (div_lt_iff₀ hεsq).mp hlarge
    have hdiv : C / (p : ℝ) < ε ^ 2 :=
      (div_lt_iff₀ hp0).mpr (by simpa only [mul_comm] using hnum)
    have he : C / (p : ℝ) =
        16 * g₀ ^ 2 / ((p : ℝ) * finiteFlipHarmonicDensity {2} ^ 2) := by
      dsimp only [C]
      ring
    rwa [he] at hdiv
  have hsquare := (finiteFlipGreatestGap_insert_loss_sq_le {2} h2 hp).trans_lt hsmall
  have hclose : finiteFlipGreatestGap {2} - ε <
      finiteFlipGreatestGap (insert p {2}) := by
    nlinarith only [hsquare, hε]
  have hG : ∀ q ∈ insert p ({2} : Finset ℕ), q.Prime := by
    intro q hq
    rcases mem_insert.mp hq with he | hq
    · simpa only [he] using hp
    · exact h2 q hq
  have hproper : ({2} : Finset ℕ) ⊂ insert p {2} := by
    refine ⟨subset_insert p {2}, ?_⟩
    intro hback
    have he : p = 2 := mem_singleton.mp (hback (mem_insert_self p {2}))
    omega
  have hbelow := (finiteFlipGreatestGap_antitone hproper.1 hG).trans_lt
    dyadicFlipGreatestGap_lt_ceiling
  exact ⟨p, hp, hBp, hp11, isGreatest_primeFlip_hyperplaneGap hp hp11, hclose,
    (finiteFlipGreatestGap_lt_iff_of_ssubset hproper hG).mpr hbelow⟩

end GaloisForLFunctions.ArithmeticCountingPositivity
