import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.Conductor.QuadraticConductorConfinement
import GaloisForLFunctions.RenormalizedArithmeticPotentialTheory.TheCompleteWeilFormIsDiagonalOnFiniteRamanujanPackets
import GaloisForLFunctions.CriticalScaleArithmeticRigidity.TerminalPrimeResiduals

/-!
# Conductor orthogonality survives restriction to a long prefix

A conductor packet has little mass on a terminal interval. Global orthogonality
therefore bounds the conductor projection of a restricted vector by its terminal
mass. The explicit reverse defect gap retains a full logarithmic prefix reserve.
-/

set_option autoImplicit false
noncomputable section
open Finset
open scoped Classical RealInnerProductSpace
namespace GaloisForLFunctions.CompletedArithmeticForms
open RenormalizedArithmeticPotentialTheory SuccessorShellArithmetic CriticalScaleArithmeticRigidity

private theorem profile_inner (x y : ℕ → ℝ) (N : ℕ) :
    ⟪horizonProfileVector x N, horizonProfileVector y N⟫ =
      ∑ n ∈ Icc 1 N, x n * y n := by
  rw [EuclideanSpace.inner_eq_star_dotProduct]
  change (∑ n : PrimeHorizonIndex N, y n * x n) = _
  rw [sum_coe_sort (Icc 1 N) (fun n => y n * x n)]
  exact sum_congr rfl fun n _ => mul_comm _ _

private theorem profile_packet_inner (x a : ℕ → ℝ) (Q N : ℕ) :
    ⟪horizonProfileVector x N, ∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N⟫ =
      (Real.sqrt (Real.log N))⁻¹ * ∑ n ∈ Icc 1 N, x n * ramanujanPacketProfile (Icc 1 Q) a n := by
  change ⟪horizonProfileVector x N, normalizedRamanujanPacketVector (Icc 1 Q) a N⟫ = _
  rw [normalizedRamanujanPacketVector_eq_smul_profile, real_inner_smul_right, profile_inner]

private theorem packetProfile_sq (Q : ℕ) (a : ℕ → ℝ) (n : ℕ) :
    ramanujanPacketProfile (Icc 1 Q) a n ^ 2 = normalizedConductorPacket Q a n ^ 2 / (n : ℝ) := by
  have he : ramanujanPacketProfile (Icc 1 Q) a n =
      normalizedConductorPacket Q a n / Real.sqrt n := by
    dsimp only [ramanujanPacketProfile, normalizedConductorPacket, ramanujanPoleProfile]
    rw [sum_div]
    exact sum_congr rfl fun m _ => by ring
  rw [he, div_pow, Real.sq_sqrt (Nat.cast_nonneg n)]

private theorem sum_prefix_add_terminal {M N : ℕ} (hMN : M ≤ N) (f : ℕ → ℝ) :
    (∑ n ∈ Icc 1 M, f n) + (∑ n ∈ Ioc M N, f n) = ∑ n ∈ Icc 1 N, f n := by
  have hs : (Ioc M N : Finset ℕ) = Icc 1 N \ Icc 1 M := by
    ext n
    simp only [Finset.mem_Ioc, Finset.mem_sdiff, Finset.mem_Icc]
    omega
  rw [hs, add_comm]
  exact sum_sdiff (Icc_subset_Icc le_rfl hMN)

/-- A global conductor-orthogonal vector leaks into the prefix conductor space only through its tail. -/
theorem norm_prefix_conductor_projection_sq_le {Q M N : ℕ}
    (hQ : 2 ≤ Q) (hM : 2 ≤ M) (hMN : M ≤ N) (hQM : Q * Q ≤ M)
    (hlog : 18 * (1 + Real.log Q) ≤ Real.log M)
    {w : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hw : w ∈ (conductorSubspace Q N)ᗮ) :
    ‖(conductorSubspace Q M).starProjection
      (horizonProfileVector (primeHorizonExtension w) M)‖ ^ 2 ≤
        2 * terminalPacketCost Q M N / Real.log M *
          ∑ n ∈ Ioc M N, primeHorizonExtension w n ^ 2 := by
  let x := primeHorizonExtension w
  let y := horizonProfileVector x M
  let p := (conductorSubspace Q M).starProjection y
  have hp : p ∈ conductorSubspace Q M := (conductorSubspace Q M).starProjection_apply_mem y
  obtain ⟨a, -, ha⟩ := (mem_conductorSubspace_iff (x := p)).mp hp
  have hL : 0 < Real.log M := Real.log_pos (by exact_mod_cast (show 1 < M by omega))
  have hLN : 0 < Real.log N := Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hframe : (∑ m ∈ Icc 1 Q, a m ^ 2) ≤ 2 * ‖p‖ ^ 2 := by
    have h := (half_and_three_halves_riesz_of_log_le hQ hQM hlog a).1
    rw [← ha] at h
    linarith only [h]
  have hpy : ⟪y, p⟫ = ‖p‖ ^ 2 := by
    have hh := (conductorSubspace Q M).starProjection_inner_eq_zero y p hp
    change ⟪y - p, p⟫ = 0 at hh
    rw [inner_sub_left, real_inner_self_eq_norm_sq] at hh
    linarith only [hh]
  have horth : ⟪w, ∑ m ∈ Icc 1 Q, a m • normalizedRamanujanHorizonVector m N⟫ = 0 :=
    by
      rw [real_inner_comm]
      exact Submodule.inner_right_of_mem_orthogonal
        (sum_normalizedRamanujanHorizonVector_mem_conductorSubspace Q N a) hw
  have hall : (∑ n ∈ Icc 1 N, x n * ramanujanPacketProfile (Icc 1 Q) a n) = 0 := by
    rw [← horizonProfileVector_extension w, profile_packet_inner] at horth
    exact (mul_eq_zero.mp horth).resolve_left (inv_ne_zero (Real.sqrt_pos.mpr hLN).ne')
  have hprefix : (∑ n ∈ Icc 1 M, x n * ramanujanPacketProfile (Icc 1 Q) a n) =
      -(∑ n ∈ Ioc M N, x n * ramanujanPacketProfile (Icc 1 Q) a n) := by
    have hh := sum_prefix_add_terminal hMN (fun n => x n * ramanujanPacketProfile (Icc 1 Q) a n)
    rw [hall] at hh
    linarith only [hh]
  have hid : ‖p‖ ^ 2 = -(Real.sqrt (Real.log M))⁻¹ *
      ∑ n ∈ Ioc M N, x n * ramanujanPacketProfile (Icc 1 Q) a n := by
    calc
      _ = ⟪y, p⟫ := hpy.symm
      _ = (Real.sqrt (Real.log M))⁻¹ *
          ∑ n ∈ Icc 1 M, x n * ramanujanPacketProfile (Icc 1 Q) a n := by
        rw [ha]
        exact profile_packet_inner x a Q M
      _ = _ := by rw [hprefix]; ring
  have hgram : (∑ n ∈ Ioc M N, ramanujanPacketProfile (Icc 1 Q) a n ^ 2) ≤
      terminalPacketCost Q M N * ∑ m ∈ Icc 1 Q, a m ^ 2 := by
    simp_rw [packetProfile_sq]
    exact harmonicConductorPacket_terminal_le hQ hMN a
  have htail0 : 0 ≤ ∑ n ∈ Ioc M N, x n ^ 2 := sum_nonneg fun _ _ => sq_nonneg _
  have hcs := sum_mul_sq_le_sq_mul_sq (Ioc M N) x (ramanujanPacketProfile (Icc 1 Q) a)
  have hb : (∑ n ∈ Ioc M N, x n * ramanujanPacketProfile (Icc 1 Q) a n) ^ 2 ≤
      (∑ n ∈ Ioc M N, x n ^ 2) * (terminalPacketCost Q M N * (2 * ‖p‖ ^ 2)) :=
    hcs.trans (mul_le_mul_of_nonneg_left
      (hgram.trans (mul_le_mul_of_nonneg_left hframe (terminalPacketCost_nonneg Q hMN))) htail0)
  have hs : (‖p‖ ^ 2) ^ 2 ≤
      (2 * terminalPacketCost Q M N / Real.log M * (∑ n ∈ Ioc M N, x n ^ 2)) * ‖p‖ ^ 2 := by
    calc
      _ = (∑ n ∈ Ioc M N, x n * ramanujanPacketProfile (Icc 1 Q) a n) ^ 2 / Real.log M := by
        conv_lhs => rw [hid]
        rw [mul_pow, neg_sq, inv_pow, Real.sq_sqrt hL.le]
        ring
      _ ≤ ((∑ n ∈ Ioc M N, x n ^ 2) * (terminalPacketCost Q M N * (2 * ‖p‖ ^ 2))) /
          Real.log M := div_le_div_of_nonneg_right hb hL.le
      _ = _ := by ring
  change ‖p‖ ^ 2 ≤ _
  by_cases hp0 : ‖p‖ = 0
  · rw [hp0, zero_pow (by decide)]
    exact mul_nonneg (div_nonneg (mul_nonneg zero_le_two (terminalPacketCost_nonneg Q hMN)) hL.le) htail0
  · have hp2 : 0 < ‖p‖ ^ 2 := sq_pos_of_ne_zero hp0
    rw [sq] at hs
    by_contra h
    exact (not_lt_of_ge hs) (mul_lt_mul_of_pos_right (lt_of_not_ge h) hp2)

/-- The reverse gap holds with a debit for the conductor projection, without a distance premise. -/
theorem poleDefect_ge_explicit_with_projection_debit {Q M : ℕ} (hQ : 2 ≤ Q) (hM : 2 ≤ M)
    (hscale : explicitConductorCutoffConstant ≤ Real.log Q)
    (y : EuclideanSpace ℝ (PrimeHorizonIndex M)) :
    (Real.log Q / explicitConductorCutoffConstant - 1) *
      ((15 / 16 : ℝ) * ‖y‖ ^ 2 - ‖(conductorSubspace Q M).starProjection y‖ ^ 2) ≤
        poleDefect M (primeHorizonExtension y) := by
  have hk : 0 ≤ Real.log Q / explicitConductorCutoffConstant - 1 := by
    rw [sub_nonneg, le_div_iff₀ explicitConductorCutoffConstant_pos, one_mul]
    exact hscale
  by_cases hd : (1 / 16 : ℝ) * ‖y‖ ^ 2 < ‖y - (conductorSubspace Q M).starProjection y‖ ^ 2
  · have hg := poleDefect_ge_explicit_of_norm_sub_starProjection_gt hQ hM hd
    have hh : (15 / 16 : ℝ) * ‖y‖ ^ 2 - ‖(conductorSubspace Q M).starProjection y‖ ^ 2 ≤ ‖y‖ ^ 2 := by
      linarith only [sq_nonneg ‖y‖, sq_nonneg ‖(conductorSubspace Q M).starProjection y‖]
    exact (mul_le_mul_of_nonneg_left hh hk).trans hg
  · have hdist := le_of_not_gt hd
    have hpy := norm_starProjection_sq_add_sub_sq (conductorSubspace Q M) y
    have hh : (15 / 16 : ℝ) * ‖y‖ ^ 2 - ‖(conductorSubspace Q M).starProjection y‖ ^ 2 ≤ 0 := by
      linarith only [hdist, hpy]
    exact (mul_nonpos_of_nonneg_of_nonpos hk hh).trans (poleDefect_nonneg M _)

private theorem poleDefect_restrict_profile (M : ℕ) (x : ℕ → ℝ) :
    poleDefect M (primeHorizonExtension (horizonProfileVector x M)) = poleDefect M x := by
  have he (n : ℕ) (hn : n ∈ Icc 1 M) :
      primeHorizonExtension (horizonProfileVector x M) n = x n := by
    rw [primeHorizonExtension_coe _ ⟨n, hn⟩]
    rfl
  unfold poleDefect
  apply sum_congr rfl
  intro m hm
  apply sum_congr rfl
  intro t ht
  have hmt : m * t ∈ Icc 1 M := by
    refine mem_Icc.mpr ⟨Nat.mul_pos (mem_Icc.mp hm).1 (mem_Icc.mp ht).1, ?_⟩
    have hh := (Nat.mul_le_mul_right m (mem_Icc.mp ht).2).trans (Nat.div_mul_le_self M m)
    simpa only [Nat.mul_comm] using hh
  rw [he (m * t) hmt, he m hm]

/-- The explicit reverse gap on the full orthogonal complement of the conductor space. -/
theorem poleDefect_ge_explicit_on_conductor_orthogonal {Q N : ℕ}
    (hQ : 2 ≤ Q) (hN : 2 ≤ N)
    {w : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hw : w ∈ (conductorSubspace Q N)ᗮ) :
    (Real.log Q / explicitConductorCutoffConstant - 1) * ‖w‖ ^ 2 ≤
      poleDefect N (primeHorizonExtension w) := by
  by_cases hw0 : w = 0
  · rw [hw0, norm_zero, zero_pow (by decide : 2 ≠ 0), mul_zero]
    exact poleDefect_nonneg N _
  let p := (conductorSubspace Q N).starProjection w
  have hp := (conductorSubspace Q N).starProjection_apply_mem w
  have hwp : ⟪w, p⟫ = 0 := by
    rw [real_inner_comm]
    exact Submodule.inner_right_of_mem_orthogonal hp hw
  have horth := (conductorSubspace Q N).starProjection_inner_eq_zero w p hp
  change ⟪w - p, p⟫ = 0 at horth
  rw [inner_sub_left, hwp, real_inner_self_eq_norm_sq] at horth
  have hp0 : p = 0 := norm_eq_zero.mp (by nlinarith only [horth])
  apply poleDefect_ge_explicit_of_norm_sub_starProjection_gt hQ hN
  change (1 / 16 : ℝ) * ‖w‖ ^ 2 < ‖w - p‖ ^ 2
  rw [hp0, sub_zero]
  have hn : 0 < ‖w‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hw0)
  linarith only [hn]

/-- Global conductor orthogonality gives a logarithmic prefix gap with only a terminal mass debit. -/
theorem poleDefect_prefix_ge_of_conductor_orthogonal {Q M N : ℕ}
    (hQ : 2 ≤ Q) (hM : 2 ≤ M) (hMN : M ≤ N) (hQM : Q * Q ≤ M)
    (hlog : 18 * (1 + Real.log Q) ≤ Real.log M)
    (hscale : explicitConductorCutoffConstant ≤ Real.log Q)
    {w : EuclideanSpace ℝ (PrimeHorizonIndex N)} (hw : w ∈ (conductorSubspace Q N)ᗮ) :
    (Real.log Q / explicitConductorCutoffConstant - 1) *
      ((15 / 16 : ℝ) * (∑ n ∈ Icc 1 M, primeHorizonExtension w n ^ 2) -
        2 * terminalPacketCost Q M N / Real.log M *
          (∑ n ∈ Ioc M N, primeHorizonExtension w n ^ 2)) ≤
      poleDefect M (primeHorizonExtension w) := by
  have hp := norm_prefix_conductor_projection_sq_le hQ hM hMN hQM hlog hw
  have hg := poleDefect_ge_explicit_with_projection_debit hQ hM hscale
    (horizonProfileVector (primeHorizonExtension w) M)
  rw [horizonProfileVector_norm_sq, poleDefect_restrict_profile] at hg
  have hk : 0 ≤ Real.log Q / explicitConductorCutoffConstant - 1 := by
    rw [sub_nonneg, le_div_iff₀ explicitConductorCutoffConstant_pos, one_mul]
    exact hscale
  exact (mul_le_mul_of_nonneg_left (sub_le_sub_left hp _) hk).trans hg

end GaloisForLFunctions.CompletedArithmeticForms

#print axioms GaloisForLFunctions.CompletedArithmeticForms.norm_prefix_conductor_projection_sq_le
#print axioms GaloisForLFunctions.CompletedArithmeticForms.poleDefect_ge_explicit_with_projection_debit
#print axioms GaloisForLFunctions.CompletedArithmeticForms.poleDefect_ge_explicit_on_conductor_orthogonal
#print axioms GaloisForLFunctions.CompletedArithmeticForms.poleDefect_prefix_ge_of_conductor_orthogonal
