import GaloisForLFunctions.RHTower.Suzuki.SuzukiWardUnconditionalMassEscape

/-!
# Rank escape for positive Suzuki Ward channel resolutions

The literal Suzuki wall-light mass tends to infinity unconditionally.  This module tests the
whole class of positive finite-channel completions, rather than one fixed two-light splitting.
A resolution at aperture `N` consists of finitely many nonnegative channel masses whose sum is
the exact outgoing wall charge.

If every individual channel has one finite uniform ceiling, mass conservation forces the number
of channels to tend to infinity.  Hence no uniformly bounded fixed-rank positive/light-cone
assembly can realize the cofinal wall, and no fixed finite family can have finite coordinatewise
limits.  This closes the fixed-finite-rank positive branch of the remaining
`SUZUKI-FE-REFLECTED-WALL-WARD-ASSEMBLY` problem.

The positive survivor is sharp at architecture level: a viable RH producer must retain either
growing channel rank or signed relative renormalization between the co-divergent atomic and
continuous sectors.  The latter displacement is exactly the corpus predicate
`SuzukiWardAtomicContinuousImbalanceBounded`, already equivalent to RH.

No RH premise, Xi-zero hypothesis, numerical computation, or asymptotic interchange is used.
-/

open Filter Topology

noncomputable section

namespace GaloisForLFunctions.RHTower

/-- A nonnegative finite-channel resolution of the exact Suzuki wall mass at every aperture. -/
structure SuzukiWardPositiveChannelResolution where
  rank : ℕ → ℕ
  mass : (N : ℕ) → Fin (rank N) → ℝ
  nonneg : ∀ N i, 0 ≤ mass N i
  total : ∀ N,
    (∑ i, mass N i) = unitRieszCoherentPrimeOutgoingCharge (N + 2)

/-- Uniformly bounded channel masses bound total wall mass by rank times the common ceiling. -/
theorem SuzukiWardPositiveChannelResolution.outgoingCharge_le_rank_mul_of_le
    (R : SuzukiWardPositiveChannelResolution) {B : ℝ}
    (hcap : ∀ N i, R.mass N i ≤ B) (N : ℕ) :
    unitRieszCoherentPrimeOutgoingCharge (N + 2) ≤ (R.rank N : ℝ) * B := by
  rw [← R.total N]
  calc
    (∑ i, R.mass N i) ≤ ∑ _i : Fin (R.rank N), B :=
      Finset.sum_le_sum fun i _ => hcap N i
    _ = (R.rank N : ℝ) * B := by simp

private theorem tendsto_nat_add_two_atTop :
    Tendsto (fun N : ℕ => N + 2) atTop atTop := by
  rw [tendsto_atTop]
  intro b
  filter_upwards [eventually_ge_atTop b] with N hN
  omega

/-- **Positive-channel rank escape.**  Any exact positive wall resolution with one strictly
positive uniform per-channel ceiling must acquire unboundedly many channels, in the strong sense
that its rank tends to infinity along the full aperture sequence. -/
theorem SuzukiWardPositiveChannelResolution.rank_tendsto_atTop_of_uniform_le
    (R : SuzukiWardPositiveChannelResolution) {B : ℝ} (hB : 0 < B)
    (hcap : ∀ N i, R.mass N i ≤ B) :
    Tendsto R.rank atTop atTop := by
  have hout : Tendsto (fun N : ℕ =>
      unitRieszCoherentPrimeOutgoingCharge (N + 2)) atTop atTop :=
    tendsto_unitRieszCoherentPrimeOutgoingCharge_atTop.comp tendsto_nat_add_two_atTop
  rw [tendsto_atTop] at hout ⊢
  intro b
  filter_upwards [hout ((b : ℝ) * B)] with N hmass
  have hupper := R.outgoingCharge_le_rank_mul_of_le hcap N
  have hreal : (b : ℝ) ≤ (R.rank N : ℝ) := by
    nlinarith [hmass.trans hupper]
  exact_mod_cast hreal

/-- Fixed finite channel rank and a uniform per-channel ceiling are incompatible with exact
resolution of the Suzuki wall mass. -/
theorem not_exists_uniformly_bounded_fixedRank_SuzukiWardPositiveChannelResolution :
    ¬ ∃ (R : SuzukiWardPositiveChannelResolution) (B : ℝ) (r : ℕ),
      0 < B ∧ (∀ N i, R.mass N i ≤ B) ∧ (∀ N, R.rank N ≤ r) := by
  rintro ⟨R, B, r, hB, hcap, hrank⟩
  have hescape := R.rank_tendsto_atTop_of_uniform_le hB hcap
  have hevent : ∀ᶠ N in atTop, r + 1 ≤ R.rank N :=
    (tendsto_atTop.1 hescape) (r + 1)
  rcases hevent.exists with ⟨N, hN⟩
  exact (Nat.not_succ_le_self r)
    (by simpa only [Nat.succ_eq_add_one] using hN.trans (hrank N))

/-- **Fixed-rank absolute-completion no-go.**  No fixed finite positive channel family can have
finite coordinatewise cofinal limits while resolving the literal Suzuki wall mass. -/
theorem not_exists_fixedRank_positiveChannelResolution_with_coordinate_limits :
    ¬ ∃ (r : ℕ) (mass : ℕ → Fin r → ℝ) (limit : Fin r → ℝ),
      (∀ N i, 0 ≤ mass N i) ∧
      (∀ N, (∑ i, mass N i) =
        unitRieszCoherentPrimeOutgoingCharge (N + 2)) ∧
      (∀ i, Tendsto (fun N => mass N i) atTop (𝓝 (limit i))) := by
  rintro ⟨r, mass, limit, _hnonneg, htotal, hlim⟩
  have hsum : Tendsto (fun N => ∑ i, mass N i) atTop
      (𝓝 (∑ i, limit i)) := by
    exact tendsto_finsetSum Finset.univ (fun i _ => hlim i)
  have hout_nhds : Tendsto (fun N =>
      unitRieszCoherentPrimeOutgoingCharge (N + 2)) atTop
      (𝓝 (∑ i, limit i)) := by
    apply hsum.congr'
    filter_upwards with N
    exact htotal N
  have hout_top : Tendsto (fun N =>
      unitRieszCoherentPrimeOutgoingCharge (N + 2)) atTop atTop :=
    tendsto_unitRieszCoherentPrimeOutgoingCharge_atTop.comp tendsto_nat_add_two_atTop
  have hlarge : ∀ᶠ N in atTop,
      (∑ i, limit i) + 1 ≤ unitRieszCoherentPrimeOutgoingCharge (N + 2) :=
    (tendsto_atTop.1 hout_top) ((∑ i, limit i) + 1)
  have hsmall : ∀ᶠ N in atTop,
      unitRieszCoherentPrimeOutgoingCharge (N + 2) < (∑ i, limit i) + 1 / 2 :=
    hout_nhds
      (Iio_mem_nhds (by norm_num : (∑ i, limit i) < (∑ i, limit i) + 1 / 2))
  rcases (hlarge.and hsmall).exists with ⟨N, hlargeN, hsmallN⟩
  linarith

end GaloisForLFunctions.RHTower
