import GaloisForLFunctions.ExclusionOfTheCriticalState.Wall.ThePrimeWaveAtTheWallIsTheBoundedOrderOfTheWallLaw
import GaloisForLFunctions.RHTower.PrimeTailHalfWeightWall

/-!
# The wall of a reflected integer row

On the last interval of length log 2, every reflected integer translate
except the unit translate vanishes. The surviving critical state has
infinite squared mass against inverse distance to the wall.
-/

noncomputable section
open MeasureTheory Set Filter Topology
namespace GaloisForLFunctions.ExclusionOfTheCriticalState
open ArithmeticHodgeTheoryOfDegenerations ArithmeticCastelnuovoSeveri CriticalArithmeticCorrelationTheory

/-- The first integer translate is isolated on the terminal logarithmic interval. -/
theorem reflected_integer_row_at_wall {Φ : ℝ → ℝ} (hs : ∀ u, 0 ≤ u → Φ u=0)
    {b : ℕ → ℝ} (h0 : b 0=0) {u : ℝ} (hu : -Real.log 2 ≤ u) :
    (∑' n : ℕ, b n*Φ (u+Real.log n)) = b 1*Φ u := by
  rw [tsum_eq_single 1]
  · simp
  · intro n hn
    rcases Nat.eq_zero_or_pos n with rfl | hp
    · rw [h0,zero_mul]
    have h2 : (2:ℝ) ≤ n := by exact_mod_cast (show 2 ≤ n by omega)
    have hl := Real.log_le_log (by norm_num : (0:ℝ)<2) h2
    rw [hs _ (by linarith only [hu,hl]),mul_zero]

/-- A positive inverse-logarithmic wall coefficient excludes integrability of
the squared trace divided by the distance to the wall, on every collar. -/
theorem wall_log_law_forces_infinite_inverse_distance_mass {f : ℝ → ℝ} {M : ℝ}
    (hM : 0 < M) (hl : Tendsto (fun x : ℝ => f (-x)^2*Real.log (1/x)) (𝓝[>] 0) (𝓝 M))
    {r : ℝ} (hr : 0 < r) : ¬ IntegrableOn (fun x : ℝ => f (-x)^2/x) (Ioo 0 r) := by
  intro hi
  have he := hl.eventually_const_lt (show M/2 < M by linarith only [hM])
  obtain ⟨a,ha,hlo⟩ := mem_nhdsGT_iff_exists_Ioo_subset.1 he
  let d := min (min a r) (1/2:ℝ)
  have hd : 0 < d := lt_min (lt_min ha hr) (by norm_num)
  have hda : d ≤ a := (min_le_left ..).trans (min_le_left ..)
  have hdr : d ≤ r := (min_le_left ..).trans (min_le_right ..)
  have hd1 : d < 1 := lt_of_le_of_lt (min_le_right ..) (by norm_num : (1/2:ℝ)<1)
  apply _root_.RHTower.not_integrableOn_inv_mul_log_inv hd hd1
  apply ((hi.mono_set (Ioo_subset_Ioo le_rfl hdr)).const_mul (2/M)).mono' (by fun_prop)
  filter_upwards [ae_restrict_mem measurableSet_Ioo] with x hx
  have hx0 : 0 < x := hx.1
  have hp := Real.log_pos ((one_lt_inv_iff₀).2 ⟨hx0,hx.2.trans hd1⟩)
  have hlow : M/2 ≤ f (-x)^2*Real.log x⁻¹ := by
    have h := hlo (show x ∈ Ioo 0 a from ⟨hx0,hx.2.trans_le hda⟩)
    simpa only [one_div] using le_of_lt h
  rw [Real.norm_eq_abs,abs_of_nonneg (inv_nonneg.2 (mul_pos hx0 hp).le),← one_div,div_le_iff₀ (mul_pos hx0 hp)]
  calc (1:ℝ) = (2/M)*(M/2) := by field_simp
    _ ≤ (2/M)*(f (-x)^2*Real.log x⁻¹) := mul_le_mul_of_nonneg_left hlow (by positivity)
    _ = _ := by field_simp [hx0.ne',hM.ne']; ring

/-- Failure of RH supplies a continuous state for which even the half-tilted
terminal trace has infinite inverse-distance mass on every collar. -/
theorem riemannHypothesis_or_infinite_half_tilted_wall_mass : RiemannHypothesis ∨
    ∃ (W₀ : ℝ) (F Φ : ℝ → ℝ), 0 < W₀ ∧
      (⨅ (a : ℝ) (_ : 0 ≤ a), windowThreshold a)=(W₀ : EReal) ∧
      IsCriticalHalfLineGroundState W₀ F ∧ Continuous Φ ∧ F =ᵐ[volume] Φ ∧
      (∀ u, 0 ≤ u → Φ u=0) ∧ ∀ r : ℝ, 0 < r →
        ¬ IntegrableOn (fun x : ℝ => (Real.exp (-x/2)*Φ (-x))^2/x) (Ioo 0 r) := by
  rcases riemannHypothesis_or_exists_criticalHalfLineGroundState with hr | ⟨W₀,F,hW,ht,hF⟩
  · exact Or.inl hr
  obtain ⟨_,_,Φ,hΦ,he,hs,_,_,hl,_⟩ := criticalState_exists_continuous_representative hW ht hF
  have hM := mul_pos (mul_pos (by norm_num : (0:ℝ)<8) (criticalAliasCoefficient_positive hW))
    (criticalState_exponentialMass_pos hW hF)
  have hcont : Continuous (fun x : ℝ => Real.exp (-x/2)^2) := by fun_prop
  have hlim : Tendsto (fun x : ℝ => Real.exp (-x/2)^2) (𝓝[>] 0) (𝓝 1) := by
    simpa using (hcont.tendsto 0).mono_left nhdsWithin_le_nhds
  refine Or.inr ⟨W₀,F,Φ,hW,ht,hF,hΦ,he,hs,fun r hr => ?_⟩
  apply wall_log_law_forces_infinite_inverse_distance_mass (f := fun u => Real.exp (u/2)*Φ u) hM _ hr
  simpa only [mul_pow,mul_assoc,one_mul] using hlim.mul hl

#print axioms reflected_integer_row_at_wall
#print axioms riemannHypothesis_or_infinite_half_tilted_wall_mass
end GaloisForLFunctions.ExclusionOfTheCriticalState
