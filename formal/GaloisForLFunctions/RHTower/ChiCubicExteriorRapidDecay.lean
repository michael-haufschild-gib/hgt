import GaloisForLFunctions.RHTower.ChiCubicExteriorEstimate

/-!
# Arbitrary decay of the actual shrinking-cone exterior

For the literal controlled physical cutoff H=N^(1/4) and full signed
cone width epsilon=N^(-1/8), every Schwartz seminorm of the canonical
exterior is O(N^(-a)) for every natural a. Normal order is chosen after
the recipient and desired decay order. The admissible domain includes
all sufficiently large original natural scales, not a subsequence.
The complete arithmetic source attachment and near-cone cancellation
are separate obligations.
-/

noncomputable section
open Set Filter
open scoped Topology ContDiff FourierTransform
namespace RHTower.BAGTrace

/-- Admissible physical scales for the already selected quarter-power
edge and the shrinking eighth-power cone. -/
abbrev BAGCubicExteriorScale :=
  {N : ℝ // Real.exp 1 ≤ N ∧ N^((1 : ℝ)/4) < N/2}

private theorem scale_one_lt (N : BAGCubicExteriorScale) : 1 < N.1 :=
  lt_of_lt_of_le (Real.one_lt_exp_iff.mpr zero_lt_one) N.2.1
private theorem scale_pos (N : BAGCubicExteriorScale) : 0 < N.1 :=
  lt_trans zero_lt_one (scale_one_lt N)

/-- Literal canonical exterior for the original controlled cutoff
H=N^(1/4) and the full signed cone width epsilon=N^(-1/8). -/
def bagCubicShrinkingExterior (N : BAGCubicExteriorScale) :
    SchwartzMap BAGPhysicalSpace ℂ :=
  bagCubicExteriorPhysical (N.1^(-(1 : ℝ)/8))
    (bagCubicExpControlledPhysicalSchwartz ⟨N.1,N.2.1⟩
      ⟨N.1^((1 : ℝ)/4),Real.rpow_pos_of_pos (scale_pos N) _,N.2.2⟩)

/-- The admissible scale domain contains EVERY sufficiently large
original natural scale; it is not a subsequence. -/
theorem bagCubicExteriorScale_eventually :
    ∀ᶠ N : ℕ in atTop,
      Real.exp 1 ≤ (N : ℝ) ∧ (N : ℝ)^((1 : ℝ)/4) < (N : ℝ)/2 := by
  have ht : Tendsto (fun N : ℕ => (N : ℝ)^((1 : ℝ)/4)/(N : ℝ)) atTop (𝓝 0) := by
    have h := (tendsto_rpow_neg_atTop (by norm_num : (0 : ℝ)<3/4)).comp
      tendsto_natCast_atTop_atTop
    apply h.congr'
    filter_upwards [eventually_ge_atTop (1 : ℕ)] with N hN
    have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (by omega : N ≠ 0)
    change (N : ℝ)^(-(3/4 : ℝ))=(N : ℝ)^((1 : ℝ)/4)/(N : ℝ)
    rw [show -(3/4 : ℝ)=(1 : ℝ)/4-1 by ring,Real.rpow_sub_one hN0]
  filter_upwards [tendsto_natCast_atTop_atTop.eventually_ge_atTop (Real.exp 1),
    ht.eventually (Iio_mem_nhds (by norm_num : (0 : ℝ)<1/2))] with N hN hsmall
  have hN0 : (0 : ℝ)<N := lt_of_lt_of_le (Real.exp_pos 1) hN
  exact ⟨hN,by linarith [(div_lt_iff₀ hN0).mp hsmall]⟩

/-- Arbitrary polynomial decay of EVERY physical Schwartz seminorm of
the complete shrinking-cone exterior of the actual amplitude. The order
of normal differentiation is chosen only after the recipient and decay
order. All large original scales, both cone sheets and infinity remain. -/
theorem bagCubicShrinkingExterior_rapid_decay (p n a : ℕ) :
    ∃ C : ℝ, 0 < C ∧ ∀ N : BAGCubicExteriorScale,
      SchwartzMap.seminorm ℂ p n (bagCubicShrinkingExterior N) ≤ C/N.1^a := by
  obtain ⟨M,R,hMR⟩ := bagCubicControlledPhysicalSchwartz_exterior_seminorm p n
  let k := 8*(M+a)+R
  obtain ⟨C,hC,hCb⟩ := hMR k
  refine ⟨C,hC,fun N => ?_⟩
  have hN : 0 < N.1 := scale_pos N
  have hN1 : 1 ≤ N.1 := (scale_one_lt N).le
  have hlog : 1 ≤ Real.log N.1 := (Real.le_log_iff_exp_le hN).mpr N.2.1
  have hH : 1 ≤ N.1^((1 : ℝ)/4) := Real.one_le_rpow hN1 (by norm_num)
  have hε : N.1^(-(1 : ℝ)/8) ∈ Ioc (0 : ℝ) 1 :=
    ⟨Real.rpow_pos_of_pos hN _,Real.rpow_le_one_of_one_le_of_nonpos hN1 (by norm_num)⟩
  have hb := hCb ⟨N.1,N.2.1⟩
    ⟨N.1^((1 : ℝ)/4),Real.rpow_pos_of_pos hN _,N.2.2⟩ hH
    ⟨N.1^(-(1 : ℝ)/8),hε⟩
  change SchwartzMap.seminorm ℂ p n (bagCubicShrinkingExterior N) ≤
    C*N.1^M/(N.1*Real.log N.1^3*(N.1^((1 : ℝ)/4))^k*(N.1^(-(1 : ℝ)/8))^(k+R)) at hb
  have he : (N.1^((1 : ℝ)/4))^k*(N.1^(-(1 : ℝ)/8))^(k+R)=N.1^(M+a) := by
    rw [← Real.rpow_mul_natCast hN.le,← Real.rpow_mul_natCast hN.le,← Real.rpow_add hN]
    rw [← Real.rpow_natCast N.1 (M+a)]
    congr 1
    dsimp only [k]
    push_cast
    ring
  have hbase : 1 ≤ N.1*Real.log N.1^3 := one_le_mul_of_one_le_of_one_le hN1 (one_le_pow₀ hlog)
  calc
    _ ≤ C*N.1^M/(N.1*Real.log N.1^3*N.1^(M+a)) := by
      convert hb using 1
      congr 1
      rw [mul_assoc (N.1*Real.log N.1^3),he]
    _ ≤ C*N.1^M/N.1^(M+a) := div_le_div_of_nonneg_left
      (mul_nonneg hC.le (pow_nonneg hN.le M)) (pow_pos hN _)
      (by simpa only [one_mul] using mul_le_mul_of_nonneg_right hbase (pow_nonneg hN.le (M+a)))
    _ = C/N.1^a := by rw [pow_add]; field_simp

end RHTower.BAGTrace
