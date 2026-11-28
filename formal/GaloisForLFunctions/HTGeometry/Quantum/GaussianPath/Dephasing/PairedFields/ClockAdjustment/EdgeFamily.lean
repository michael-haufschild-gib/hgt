import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.ClockAdjustment.GaussianPair

/-! # Simultaneous angular responses from a family of physical edges -/

open MeasureTheory Filter Finset Set
namespace GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.ClockAdjustment
open private continuous_edgeResponse from GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.PairedFields.ClockAdjustment.GaussianPair
noncomputable section

/-- A family of edge probes typically has total absolute response proportional to its size.
The probes may share couplings. Only their one-edge small-ball probabilities enter. -/
theorem gaussian_edge_family {n : ℕ} {J : Type*} [Fintype J] [Nonempty J]
    (e : J → Fin (n+1)) (a b : J → Fin 3) (r : ℝ) (hr : 0<r) :
    let D := (2:ℝ)^(n+2)
    let m : ℝ := Fintype.card J
    (fieldLaw n).real {h | (∑ j, |edgeResponse h (e j) (a j) (b j)|) < m*(D*r^3)} ≤ 12*r := by
  classical
  intro D m
  let μ := fieldLaw n
  let A := 2*D*r^3
  have hA : 0<A := by dsimp only [A,D]; positivity
  have hm : 0 < m := Nat.cast_pos.mpr Fintype.card_pos
  let S (j : J) := {h : Coeff n | |edgeResponse h (e j) (a j) (b j)|<A}
  let I (j : J) := (S j).indicator (fun _ => (1:ℝ))
  let f (h : Coeff n) := ∑ j, I j h
  have hS (j) : MeasurableSet (S j) :=
    measurableSet_lt (continuous_edgeResponse (e j) (a j) (b j)).abs.measurable measurable_const
  have hi (j) : Integrable (I j) μ := (integrable_const _).indicator (hS j)
  have hmean : (∫ h, f h ∂μ) ≤ m*(6*r) := by
    rw [show f=(fun h => ∑ j, I j h) from rfl,integral_finsetSum _ fun j _ => hi j]
    calc _ ≤ ∑ _j : J, 6*r := sum_le_sum fun j _ => by
           rw [show (∫ h, I j h ∂μ)=μ.real (S j) from integral_indicator_one (hS j)]
           exact gaussian_edge_response (e j) (a j) (b j) r hr
         _ = _ := by simp [m,nsmul_eq_mul]
  have hpos : 0 ≤ᵐ[μ] f := Eventually.of_forall fun h =>
    sum_nonneg fun j _ => Set.indicator_nonneg (fun _ _ => zero_le_one) _
  have hmark := (mul_meas_ge_le_integral_of_nonneg hpos (integrable_finsetSum _ fun j _ => hi j) (m/2)).trans hmean
  refine (measureReal_mono (s₂:={h | m/2 ≤ f h}) ?_ (measure_ne_top _ _)).trans ?_
  · intro h hsmall
    have hx (j : J) : A*(1-I j h) ≤ |edgeResponse h (e j) (a j) (b j)| := by
      by_cases hb : h∈S j
      · simp only [I,Set.indicator_of_mem hb,sub_self,mul_zero,abs_nonneg]
      · simp only [I,Set.indicator_of_notMem hb,sub_zero,mul_one]
        exact le_of_not_gt hb
    have hh := sum_le_sum (s:=univ) (fun j _ => hx j)
    rw [←mul_sum,sum_sub_distrib,sum_const,card_univ,nsmul_eq_mul,mul_one] at hh
    change A*(m-f h) ≤ _ at hh
    have hcut : m*(D*r^3)=(m/2)*A := by dsimp only [A]; ring
    change _ < m*(D*r^3) at hsmall
    rw [hcut,mul_comm (m/2) A] at hsmall
    have hhalf := (mul_lt_mul_iff_right₀ hA).mp (hh.trans_lt hsmall)
    change m/2 ≤ f h
    linarith only [hhalf]
  · exact (mul_le_mul_iff_right₀ (half_pos hm)).mp (hmark.trans_eq (by ring))

#print axioms gaussian_edge_family
end
end GaloisForLFunctions.HTGeometry.Dephasing.PairedFields.ClockAdjustment
