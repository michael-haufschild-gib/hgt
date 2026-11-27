import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.Dephasing.GappedSpin.CentralCut.FreeAxis.FirstExcursion
import GaloisForLFunctions.HTGeometry.Quantum.GaussianPath.WeakBonds.FixedRadius

/-! # Sixth-power first-wait tails at unit root-mean-square coupling strength -/
open Set Filter MeasureTheory ProbabilityTheory Real Finset
namespace GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut.FreeAxis
open PrescribedTimes WeakBonds
noncomputable section

private theorem rms_interval {n : ℕ} (x : PrefixIndex n→ℝ) (hx : ∀ i, x i∈Icc (1/20:ℝ) 4) :
    let R := sqrt (Fintype.card (PrefixIndex n):ℝ)
    (1/20)*R ≤ coefficientNorm x ∧ coefficientNorm x ≤ 4*R := by
  intro R
  have hR : R^2=(Fintype.card (PrefixIndex n):ℝ) := sq_sqrt (Nat.cast_nonneg _)
  have he : coefficientNorm x^2=∑ i, (x i)^2 := EuclideanSpace.real_norm_sq_eq _
  have hnn i := (by norm_num : (0:ℝ)≤1/20).trans (hx i).1
  have hlo := sum_le_sum (s:=univ) (fun (i : PrefixIndex n) _ =>
    pow_le_pow_left₀ (by norm_num : (0:ℝ)≤1/20) (hx i).1 2)
  have hhi := sum_le_sum (s:=univ) (fun (i : PrefixIndex n) _ =>
    pow_le_pow_left₀ (hnn i) (hx i).2 2)
  simp only [sum_const,card_univ,nsmul_eq_mul,←he] at hlo hhi
  constructor
  · apply (sq_le_sq₀ (mul_nonneg (by norm_num) (sqrt_nonneg _)) (norm_nonneg _)).mp
    rw [mul_pow,hR,mul_comm]; exact hlo
  · apply (sq_le_sq₀ (norm_nonneg _) (mul_nonneg (by norm_num) (sqrt_nonneg _))).mp
    rw [mul_pow,hR,mul_comm (4^2:ℝ)]; exact hhi

/-- Both clocks survive the same prescribed delay before and after
normalization. Every normalized coefficient lies in [1/80,80]. -/
theorem positive_rms_tail :
    ∃ C > (0:ℝ), ∀ᶠ k : ℕ in atTop,
      let n := k+1
      let K := n+2
      let P := nearHilbertContinuousCircuitBudget K
      let μ := Measure.pi fun _ : PrefixIndex n => gaussianReal 0 1
      let R := sqrt (Fintype.card (PrefixIndex n):ℝ)
      let J := fun (x : PrefixIndex n→ℝ) (t : ℝ) =>
        t < crossingOrigin n P (9/80) x ∧ ∀ s ≤ P/2, t < crossingWait n P s x
      ∀ T ≥ (1:ℝ), exp (-C*(K:ℝ)^2) ≤ (20*T)^6*μ.real {x |
        (∀ i, x i∈Icc (1/20:ℝ) 4) ∧ (∀ i, atRadius R x i∈Icc (1/80:ℝ) 80) ∧
          J x (20*T) ∧ J (atRadius R x) T} := by
  obtain ⟨C,hC,_,_,hsector⟩ := positive_first_excursions
  refine ⟨C,hC,?_⟩
  filter_upwards [hsector] with k hk
  intro n K P μ R J T hT
  have hbig : 1≤20*T := by linarith only [hT]
  obtain ⟨E,hE,hfloor,hprop⟩ := hk (20*T) hbig
  let X := fun (ω : PathPauliDisorder) i => pathPauliDisorderShell ω n (pathCoeffEquiv n i)
  have hX : MeasurePreserving X pathPauliDisorderLaw μ := gaussian_pauli_prefix_coordinates_law n
  have hn : Measurable (coefficientNorm (n:=n)) := (continuous_norm.comp (PiLp.continuous_toLp 2 _)).measurable
  have hrad : Measurable (atRadius (n:=n) R) := (measurable_const.div hn).smul measurable_id
  have hbox (a b : ℝ) : MeasurableSet {x : PrefixIndex n→ℝ | ∀ i, x i∈Icc a b} := by
    simp only [setOf_forall]
    exact MeasurableSet.iInter fun i => measurableSet_Icc.preimage (measurable_pi_apply i)
  have hJ (t : ℝ) : MeasurableSet {x | J x t} := by
    apply (measurableSet_lt measurable_const (measurable_crossingOrigin ..)).inter
    change MeasurableSet {x | ∀ s, s ≤ P/2 → t < crossingWait n P s x}
    simp only [setOf_forall]
    exact MeasurableSet.iInter fun s => MeasurableSet.iInter fun _ =>
      measurableSet_lt measurable_const (measurable_crossingWait n P s)
  have htest := (hbox (1/20) 4).inter (((hbox (1/80) 80).preimage hrad).inter
    ((hJ (20*T)).inter ((hJ T).preimage hrad)))
  let S := {x : PrefixIndex n→ℝ | (∀ i, x i∈Icc (1/20:ℝ) 4) ∧
    (∀ i, atRadius R x i∈Icc (1/80:ℝ) 80) ∧ J x (20*T) ∧ J (atRadius R x) T}
  have hS : MeasurableSet S := htest
  apply hfloor.trans (mul_le_mul_of_nonneg_left _ (by positivity))
  apply ENNReal.toReal_mono (measure_ne_top _ _)
  change pathPauliDisorderLaw E ≤ μ S
  apply le_trans _ (hX.measure_preimage hS.nullMeasurableSet).le
  apply measure_mono_ae
  filter_upwards [hprop] with ω h
  intro he
  obtain ⟨hs,ho,hw,_,_,_⟩ := h he
  let x := X ω
  letI : Nonempty (PrefixIndex n) := ⟨(pathCoeffEquiv n).symm (.inl (0,2))⟩
  have hR : 0<R := sqrt_pos.mpr (Nat.cast_pos.mpr Fintype.card_pos)
  obtain ⟨hl,hu⟩ := rms_interval x hs
  change 1/20*R ≤ coefficientNorm x at hl
  change coefficientNorm x ≤ 4*R at hu
  have hx : 0<coefficientNorm x := (mul_pos (by norm_num) hR).trans_le hl
  let q := R/coefficientNorm x
  have hq : 0<q := div_pos hR hx
  have h₁ : 1/4≤q := (le_div_iff₀ hx).mpr (by linarith only [hu])
  have h₂ : q≤20 := (div_le_iff₀ hx).mpr (by linarith only [hl])
  have hqT := mul_le_mul_of_nonneg_right h₂ (zero_le_one.trans hT)
  change (∀ i, x i∈Icc (1/20:ℝ) 4) ∧ (∀ i, atRadius R x i∈Icc (1/80:ℝ) 80) ∧ J x (20*T) ∧ J (atRadius R x) T
  refine ⟨hs,?_,⟨ho,hw⟩,?_,?_⟩
  · intro i
    change 1/80 ≤ q*x i ∧ q*x i ≤ 80
    exact ⟨(by norm_num : (1/80:ℝ)=(1/4)*(1/20)).le.trans
      (mul_le_mul h₁ (hs i).1 (by norm_num) hq.le),
      (mul_le_mul h₂ (hs i).2 ((by norm_num : (0:ℝ)≤1/20).trans (hs i).1) (by norm_num)).trans_eq (by norm_num)⟩
  · apply (mul_lt_mul_iff_right₀ hq).mp
    rw [show atRadius R x=q • x from rfl,smul_crossingOrigin _ _ _ hq]
    exact hqT.trans_lt ho
  · intro s hs'
    apply (mul_lt_mul_iff_right₀ hq).mp
    rw [show atRadius R x=q • x from rfl,smul_crossingWait _ _ _ hq]
    exact hqT.trans_lt (hw s hs')

#print axioms positive_rms_tail
end
end GaloisForLFunctions.HTGeometry.Dephasing.GappedSpin.CentralCut.FreeAxis
