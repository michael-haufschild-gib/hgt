import GaloisForLFunctions.HTGeometry.PeriodicTentPacket
import GaloisForLFunctions.HTGeometry.KleinbockMargulis.LinearFlowIndexedFourierPacketWindow

open Real intervalIntegral MeasureTheory

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : ℕ}

/-- Integer torus character carried by a Fejér packet sheet. -/
def packetCharacter (k : Fin d → ℕ × ℕ) : Fin d → ℤ :=
  fun j => ((k j).1 : ℤ) - ((k j).2 : ℤ)

theorem dotProd_packetCharacter (ω : Fin d → ℝ) (k : Fin d → ℕ × ℕ) :
    KleinbockMargulis.dotProd (packetCharacter k) ω = packetFreq ω k := by
  simp only [KleinbockMargulis.dotProd, packetCharacter, packetFreq]
  exact Finset.sum_congr rfl fun j _ => by
    push_cast
    ring

/-- Nonconstant sheets of the product Fejér packet. -/
def nonconstantPacketIndexSet (N d : ℕ) : Finset (Fin d → ℕ × ℕ) :=
  (Fintype.piFinset fun _ : Fin d =>
      Finset.range (N + 1) ×ˢ Finset.range (N + 1)) \
    Fintype.piFinset (fun _ : Fin d => diagPairs N)

theorem packetCharacter_ne_zero_of_mem_nonconstantPacketIndexSet
    {N : ℕ} {k : Fin d → ℕ × ℕ}
    (hk : k ∈ nonconstantPacketIndexSet N d) : packetCharacter k ≠ 0 := by
  classical
  intro hzero
  have hfull : k ∈ Fintype.piFinset (fun _ : Fin d =>
      Finset.range (N + 1) ×ˢ Finset.range (N + 1)) :=
    (Finset.mem_sdiff.mp hk).1
  have hdiag : k ∈ Fintype.piFinset (fun _ : Fin d => diagPairs N) := by
    rw [Fintype.mem_piFinset]
    intro j
    have hj := Fintype.mem_piFinset.mp hfull j
    rw [Finset.mem_product] at hj
    have hz := congrFun hzero j
    have heq : (k j).1 = (k j).2 := by
      simp only [packetCharacter, Pi.zero_apply] at hz
      omega
    rw [diagPairs, Finset.mem_image]
    refine ⟨(k j).1, hj.1, ?_⟩
    apply Prod.ext
    · rfl
    · exact heq
  exact (Finset.mem_sdiff.mp hk).2 hdiag

/-- Exact multiplicative Fourier cost of the nonconstant Fejér sheets. -/
noncomputable def periodicFejerMultiplicativeCost
    (N : ℕ) (ρ : ℝ) (c : Fin d → ℝ) (eps : ℝ) : ℝ :=
  KleinbockMargulis.indexedMultiplicativeFourierL1Cost
    (ι := {k // k ∈ nonconstantPacketIndexSet N d})
    (fun k => packetAmp N ρ c k.1)
    (fun k => packetCharacter k.1) eps

/-- **Minimum-gap-free Fejér packet law.**  Strong extremality controls the
whole multivariate Fejér packet in every translated window by its exact
multiplicative Fourier cost.  Duplicate mode sheets are retained. -/
theorem exists_periodicProductFejerTent_multiplicativeWindowDiscrepancy
    {ω : Fin d → ℝ} (hω : ¬ KleinbockMargulis.VWMA ω)
    {eps : ℝ} (heps : 0 < eps) (N : ℕ) {ρ : ℝ}
    (hρ : 0 < ρ) (hρπ : ρ ≤ π) (c : Fin d → ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ u T : ℝ, 0 < T →
      ‖((1 / (T : ℂ)) *
          ∫ t in u..(u + T),
            ((periodicProductFejerTent N ρ c (fun j => t * ω j) : ℝ) : ℂ))
          - (((ρ / (2 * π)) ^ d : ℝ) : ℂ)‖ ≤
        (2 * C / T) * periodicFejerMultiplicativeCost N ρ c eps := by
  classical
  set S := nonconstantPacketIndexSet N d with hS
  obtain ⟨C, hC, hpacket⟩ :=
    KleinbockMargulis.exists_global_indexedFourierPacketHaarDiscrepancy
      (ι := {k // k ∈ S}) hω heps
  refine ⟨C, hC, ?_⟩
  intro u T hT
  have hpoint : ∀ t : ℝ,
      ((periodicProductFejerTent N ρ c (fun j => t * ω j) : ℝ) : ℂ) =
        (((ρ / (2 * π)) ^ d : ℝ) : ℂ)
          + ∑ i : {k // k ∈ S}, packetAmp N ρ c i.1 *
            Complex.exp ((t : ℂ) *
              (KleinbockMargulis.dotProd (packetCharacter i.1) ω : ℂ) *
                Complex.I) := by
    intro t
    rw [periodicProductFejerTent_eq_const_add N hρ hρπ]
    change (((ρ / (2 * π)) ^ d : ℝ) : ℂ) +
        ∑ k ∈ nonconstantPacketIndexSet N d,
          packetMode N ρ c (fun j => t * ω j) k = _
    rw [← hS]
    congr 1
    rw [Finset.sum_coe_sort S (fun k => packetAmp N ρ c k *
      Complex.exp ((t : ℂ) *
        (KleinbockMargulis.dotProd (packetCharacter k) ω : ℂ) * Complex.I))]
    exact Finset.sum_congr rfl fun k _ => by
      rw [packetMode_linearPhase N ρ c ω k t,
        dotProd_packetCharacter]
  have hmain := hpacket
    (((ρ / (2 * π)) ^ d : ℝ) : ℂ)
    (fun i : {k // k ∈ S} => packetAmp N ρ c i.1)
    (fun i : {k // k ∈ S} => packetCharacter i.1)
    (fun i => by
      apply packetCharacter_ne_zero_of_mem_nonconstantPacketIndexSet
      rw [← hS]
      exact i.2) u T hT
  rw [show periodicFejerMultiplicativeCost N ρ c eps =
      KleinbockMargulis.indexedMultiplicativeFourierL1Cost
        (ι := {k // k ∈ S})
        (fun i => packetAmp N ρ c i.1)
        (fun i => packetCharacter i.1) eps by rfl]
  have hInt :
      (∫ t in u..(u + T),
        ((periodicProductFejerTent N ρ c (fun j => t * ω j) : ℝ) : ℂ)) =
      ∫ t in u..(u + T),
        ((((ρ / (2 * π)) ^ d : ℝ) : ℂ)
          + ∑ i : {k // k ∈ S}, packetAmp N ρ c i.1 *
            Complex.exp ((t : ℂ) *
              (KleinbockMargulis.dotProd (packetCharacter i.1) ω : ℂ) *
                Complex.I)) :=
    intervalIntegral.integral_congr fun t _ => hpoint t
  rw [hInt]
  exact hmain

/-- Real lower form of the multiplicative Fejér packet law. -/
theorem exists_windowMean_periodicProductFejerTent_ge_multiplicative
    {ω : Fin d → ℝ} (hω : ¬ KleinbockMargulis.VWMA ω)
    {eps : ℝ} (heps : 0 < eps) (N : ℕ) {ρ : ℝ}
    (hρ : 0 < ρ) (hρπ : ρ ≤ π) (c : Fin d → ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ u T : ℝ, 0 < T →
      ((ρ / (2 * π)) ^ d : ℝ) -
          (2 * C / T) * periodicFejerMultiplicativeCost N ρ c eps ≤
        (1 / T) * ∫ t in u..(u + T),
          periodicProductFejerTent N ρ c (fun j => t * ω j) := by
  obtain ⟨C, hC, hdisc⟩ :=
    exists_periodicProductFejerTent_multiplicativeWindowDiscrepancy
      hω heps N hρ hρπ c
  refine ⟨C, hC, ?_⟩
  intro u T hT
  have hcont := continuous_periodicProductFejerTent N ρ c ω
  have hd := hdisc u T hT
  let Z : ℂ :=
    ((1 / (T : ℂ)) *
      ∫ t in u..(u + T),
        ((periodicProductFejerTent N ρ c (fun j => t * ω j) : ℝ) : ℂ))
      - (((ρ / (2 * π)) ^ d : ℝ) : ℂ)
  have hre : |Z.re| ≤ ‖Z‖ := Complex.abs_re_le_norm Z
  have hdZ : ‖Z‖ ≤
      (2 * C / T) * periodicFejerMultiplicativeCost N ρ c eps := by
    simpa [Z] using hd
  have hreal := (abs_le.mp (hre.trans hdZ)).1
  dsimp [Z] at hreal
  rw [re_window_mean_ofReal hcont hT u] at hreal
  linarith

/-- **Minimum-gap-free periodic-box occupancy floor.**  The actual periodic
tent inherits the arithmetic packet lower bound, losing only the explicit
Fejér displacement. -/
theorem exists_windowMean_periodicProductTent_ge_multiplicative
    {ω : Fin d → ℝ} (hω : ¬ KleinbockMargulis.VWMA ω)
    {eps : ℝ} (heps : 0 < eps) (N : ℕ) {ρ : ℝ}
    (hρ : 0 < ρ) (hρπ : ρ ≤ π) (c : Fin d → ℝ) :
    ∃ C : ℝ, 1 ≤ C ∧ ∀ u T : ℝ, 0 < T →
      ((ρ / (2 * π)) ^ d : ℝ)
          - (2 * C / T) * periodicFejerMultiplicativeCost N ρ c eps
          - (d : ℝ) * ((1 / ρ) *
              (2 * π / Real.sqrt ((N : ℝ) + 1))) ≤
        (1 / T) * ∫ t in u..(u + T),
          periodicProductTent ρ c (fun j => t * ω j) := by
  obtain ⟨C, hC, hmean⟩ :=
    exists_windowMean_periodicProductFejerTent_ge_multiplicative
      hω heps N hρ hρπ c
  refine ⟨C, hC, ?_⟩
  intro u T hT
  have hcontP := continuous_periodicProductFejerTent N ρ c ω
  have hcontf := continuous_periodicProductTent ρ c ω
  set D : ℝ := (d : ℝ) * ((1 / ρ) *
    (2 * π / Real.sqrt ((N : ℝ) + 1))) with hD
  have hdiff :
      |(1 / T) *
          (∫ t in u..(u + T),
            periodicProductFejerTent N ρ c (fun j => t * ω j))
        - (1 / T) *
          (∫ t in u..(u + T),
            periodicProductTent ρ c (fun j => t * ω j))| ≤ D := by
    have hsub :
        (1 / T) *
            (∫ t in u..(u + T),
              periodicProductFejerTent N ρ c (fun j => t * ω j))
          - (1 / T) *
            (∫ t in u..(u + T),
              periodicProductTent ρ c (fun j => t * ω j)) =
        (1 / T) * ∫ t in u..(u + T),
          (periodicProductFejerTent N ρ c (fun j => t * ω j)
            - periodicProductTent ρ c (fun j => t * ω j)) := by
      rw [intervalIntegral.integral_sub (hcontP.intervalIntegrable _ _)
        (hcontf.intervalIntegrable _ _)]
      ring
    rw [hsub, abs_mul, abs_of_nonneg (by positivity : 0 ≤ 1 / T)]
    have hπ : u ≤ u + T := by linarith
    have hpoint : ∀ t ∈ Set.Icc u (u + T),
        |periodicProductFejerTent N ρ c (fun j => t * ω j)
          - periodicProductTent ρ c (fun j => t * ω j)| ≤ D := by
      intro t _
      exact abs_periodicProductFejerTent_sub_le N hρ c _
    have hint :
        |∫ t in u..(u + T),
          (periodicProductFejerTent N ρ c (fun j => t * ω j)
            - periodicProductTent ρ c (fun j => t * ω j))| ≤ T * D := by
      calc
        |∫ t in u..(u + T),
          (periodicProductFejerTent N ρ c (fun j => t * ω j)
            - periodicProductTent ρ c (fun j => t * ω j))| ≤
            ∫ t in u..(u + T),
              |periodicProductFejerTent N ρ c (fun j => t * ω j)
                - periodicProductTent ρ c (fun j => t * ω j)| :=
          intervalIntegral.abs_integral_le_integral_abs hπ
        _ ≤ ∫ _t in u..(u + T), D := by
          refine intervalIntegral.integral_mono_on hπ
            ((hcontP.sub hcontf).abs.intervalIntegrable _ _)
            (continuous_const.intervalIntegrable _ _) hpoint
        _ = T * D := by
          rw [intervalIntegral.integral_const, add_sub_cancel_left,
            smul_eq_mul, mul_comm]
    calc
      (1 / T) *
          |∫ t in u..(u + T),
            (periodicProductFejerTent N ρ c (fun j => t * ω j)
              - periodicProductTent ρ c (fun j => t * ω j))| ≤
        (1 / T) * (T * D) := mul_le_mul_of_nonneg_left hint (by positivity)
      _ = D := by field_simp
  have hP := hmean u T hT
  have hlower := (abs_le.mp hdiff).2
  rw [hD]
  linarith

end

end GaloisForLFunctions.HTGeometry
