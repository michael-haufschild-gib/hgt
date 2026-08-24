import GaloisForLFunctions.HTGeometry.CompactUniformDilation
import GaloisForLFunctions.HTGeometry.LocallyUniformProduct
import GaloisForLFunctions.HTGeometry.TateThetaDegeneration

/-!
# Compact-open Tate-theta degeneration
-/

open Filter Topology Set

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Uniform multiplication bridge for the two Pochhammer factors of theta. -/
theorem tendstoUniformlyOn_multiplicativeTheta_one_of_factors
    {ι X : Type*} [TopologicalSpace X] {l : Filter ι} {K : Set X}
    (a b : ι → X → ℂ) (q : ι → EulerNome)
    (hab : ∀ i x, ((q i : EulerNome) : ℂ) / a i x = b i x)
    (ha : TendstoUniformlyOn (fun i x => qPochhammerInf (a i x) (q i))
      (fun _ => 1) l K)
    (hb : TendstoUniformlyOn (fun i x => qPochhammerInf (b i x) (q i))
      (fun _ => 1) l K) :
    TendstoUniformlyOn (fun i x => multiplicativeTheta (q i) (a i x))
      (fun _ => 1) l K := by
  have hmul := tendstoUniformlyOn_mul_of_bound (M := 1) (by norm_num)
    (fun _ _ => by norm_num) (fun _ _ => by norm_num) ha hb
  simpa only [multiplicativeTheta, hab, one_mul] using hmul

/-- Both theta factors in the cancellation form converge uniformly on every compact annulus. -/
theorem tendstoUniformlyOn_tateTheta_factors_of_root_zero
    {ι : Type*} {l : Filter ι} (r : ι → TateQuarterNome)
    (hr : Tendsto (fun i => (r i).root) l (nhds 0))
    {K : Set ℂ} (hK : IsCompact K) (hKzero : K ⊆ {x : ℂ | x ≠ 0}) :
    TendstoUniformlyOn
        (fun i x => multiplicativeTheta (r i).nome ((r i).root * x))
        (fun _ => 1) l K ∧
      TendstoUniformlyOn
        (fun i x => multiplicativeTheta (r i).nome ((r i).root ^ 3 * x))
        (fun _ => 1) l K := by
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · subst K
    exact ⟨tendstoUniformlyOn_empty, tendstoUniformlyOn_empty⟩
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn continuousOn_id
  have hinvcont : ContinuousOn (fun x : ℂ => x⁻¹) K := by
    intro x hx
    exact (continuousAt_inv₀ (hKzero hx)).continuousWithinAt
  obtain ⟨N, hN⟩ := hK.exists_bound_of_continuousOn hinvcont
  obtain ⟨x₀, hx₀⟩ := hKne
  have hM0 : 0 ≤ M := (norm_nonneg x₀).trans (hM x₀ hx₀)
  have hN0 : 0 ≤ N := (norm_nonneg x₀⁻¹).trans (hN x₀ hx₀)
  have hq := tendsto_tateQuarterNome_nome_zero r hr
  have hr1M : Tendsto (fun i => (r i).root * M) l (nhds 0) := by
    convert hr.mul_const M using 1 <;> norm_num
  have hr3M : Tendsto (fun i => (r i).root ^ 3 * M) l (nhds 0) := by
    convert (hr.pow 3).mul_const M using 1 <;> norm_num
  have hr1N : Tendsto (fun i => (r i).root * N) l (nhds 0) := by
    convert hr.mul_const N using 1 <;> norm_num
  have hr3N : Tendsto (fun i => (r i).root ^ 3 * N) l (nhds 0) := by
    convert (hr.pow 3).mul_const N using 1 <;> norm_num
  have hA1 := tendstoUniformlyOn_qPochhammerInf_one_of_norm_le
    (fun i x => ((r i).root : ℂ) * x) (fun i => (r i).nome)
    (fun i => (r i).root * M) hr1M hq (by
      filter_upwards with i x hx
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (r i).root_pos]
      exact mul_le_mul_of_nonneg_left (hM x hx) (r i).root_pos.le)
  have hB1 := tendstoUniformlyOn_qPochhammerInf_one_of_norm_le
    (fun i x => ((r i).root : ℂ) ^ 3 / x) (fun i => (r i).nome)
    (fun i => (r i).root ^ 3 * N) hr3N hq (by
      filter_upwards with i x hx
      rw [div_eq_mul_inv, norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (r i).root_pos]
      exact mul_le_mul_of_nonneg_left (hN x hx) (pow_nonneg (r i).root_pos.le 3))
  have htheta1 := tendstoUniformlyOn_multiplicativeTheta_one_of_factors
    (fun i x => ((r i).root : ℂ) * x)
    (fun i x => ((r i).root : ℂ) ^ 3 / x) (fun i => (r i).nome) (by
      intro i x
      rw [TateQuarterNome.coe_nome]
      field_simp [(r i).root_complex_ne_zero]) hA1 hB1
  have hA3 := tendstoUniformlyOn_qPochhammerInf_one_of_norm_le
    (fun i x => ((r i).root : ℂ) ^ 3 * x) (fun i => (r i).nome)
    (fun i => (r i).root ^ 3 * M) hr3M hq (by
      filter_upwards with i x hx
      rw [norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (r i).root_pos]
      exact mul_le_mul_of_nonneg_left (hM x hx) (pow_nonneg (r i).root_pos.le 3))
  have hB3 := tendstoUniformlyOn_qPochhammerInf_one_of_norm_le
    (fun i x => ((r i).root : ℂ) / x) (fun i => (r i).nome)
    (fun i => (r i).root * N) hr1N hq (by
      filter_upwards with i x hx
      rw [div_eq_mul_inv, norm_mul, Complex.norm_real, Real.norm_eq_abs,
        abs_of_pos (r i).root_pos]
      exact mul_le_mul_of_nonneg_left (hN x hx) (r i).root_pos.le)
  have htheta3 := tendstoUniformlyOn_multiplicativeTheta_one_of_factors
    (fun i x => ((r i).root : ℂ) ^ 3 * x)
    (fun i x => ((r i).root : ℂ) / x) (fun i => (r i).nome) (by
      intro i x
      rw [TateQuarterNome.coe_nome]
      field_simp [(r i).root_complex_ne_zero]) hA3 hB3
  exact ⟨htheta1, htheta3⟩

/-- Literal compact-open cusp convergence of the Tate-theta gauge on `ℂˣ`. -/
theorem tendstoLocallyUniformlyOn_tateThetaGauge_of_root_zero
    {ι : Type*} {l : Filter ι} (r : ι → TateQuarterNome)
    (hr : Tendsto (fun i => (r i).root) l (nhds 0)) :
    TendstoLocallyUniformlyOn (fun i x => tateThetaGauge (r i) x) id l
      {x : ℂ | x ≠ 0} := by
  have hopen : IsOpen {x : ℂ | x ≠ 0} := by
    change IsOpen (({0} : Set ℂ)ᶜ)
    exact isOpen_compl_singleton
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hopen]
  intro K hKzero hK
  obtain ⟨h1, h3⟩ := tendstoUniformlyOn_tateTheta_factors_of_root_zero r hr hK hKzero
  have h1sq := TendstoUniformlyOn.pow_of_isCompact h1 hK continuousOn_const 2
  have h3sq := TendstoUniformlyOn.pow_of_isCompact h3 hK continuousOn_const 2
  have hx : TendstoUniformlyOn (fun _ : ι => fun x : ℂ => x) id l K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    exact Filter.Eventually.of_forall (fun i x hx => by simpa using hε)
  have hnum := TendstoUniformlyOn.mul_of_isCompact hx h3sq hK continuousOn_id
    (continuousOn_const.pow 2)
  have hquot := TendstoUniformlyOn.div_of_isCompact_of_ne_zero hK hnum h1sq
    (continuousOn_id.mul (continuousOn_const.pow 2)) (continuousOn_const.pow 2)
    (fun x hx => by norm_num)
  rw [Metric.tendstoUniformlyOn_iff] at hquot ⊢
  intro ε hε
  filter_upwards [hquot ε hε] with i hi
  intro x hxK
  have hx0 := hKzero hxK
  rw [tateThetaGauge_eq_surviving_ratio (r i) x hx0]
  have harg : ((r i).root : ℂ) ^ (1 : ℤ) * x = ((r i).root : ℂ) * x := by
    rw [zpow_one]
  have harg3 : ((r i).root : ℂ) ^ (3 : ℤ) * x = ((r i).root : ℂ) ^ (3 : ℕ) * x := by
    exact congrArg (fun z : ℂ => z * x) (zpow_natCast ((r i).root : ℂ) 3)
  rw [harg, harg3]
  simpa only [id_eq, one_pow, mul_one, div_one] using hi x hxK

/-- Normalized Tate-theta gauges converge locally uniformly to every integral character. -/
theorem tendstoLocallyUniformlyOn_pointedTateThetaGauge_of_root_zero
    {ι : Type*} {l : Filter ι} (r : ι → TateQuarterNome)
    (hr : Tendsto (fun i => (r i).root) l (nhds 0)) (m : ℤ) :
    TendstoLocallyUniformlyOn (fun i x => pointedTateThetaGauge (r i) m x)
      (fun x => x ^ m) l {x : ℂ | x ≠ 0} := by
  have hopen : IsOpen {x : ℂ | x ≠ 0} := by
    change IsOpen (({0} : Set ℂ)ᶜ)
    exact isOpen_compl_singleton
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hopen]
  intro K hKzero hK
  have hE := (tendstoLocallyUniformlyOn_tateThetaGauge_of_root_zero r hr)
  rw [tendstoLocallyUniformlyOn_iff_forall_isCompact hopen] at hE
  have hEK := hE K hKzero hK
  have hE1 := tendsto_tateThetaGauge_pointwise_of_root_zero r hr 1 one_ne_zero
  have hE1uniform : TendstoUniformlyOn
      (fun i => fun _ : ℂ => tateThetaGauge (r i) 1) (fun _ => 1) l K := by
    rw [Metric.tendstoUniformlyOn_iff]
    intro ε hε
    have hev := (Metric.tendsto_nhds.mp hE1) ε hε
    filter_upwards [hev] with i hi x hx
    simpa [dist_comm] using hi
  have hnormalized := TendstoUniformlyOn.div_of_isCompact_of_ne_zero hK hEK hE1uniform
    continuousOn_id continuousOn_const (fun x hx => one_ne_zero)
  have hnormalized' : TendstoUniformlyOn
      (fun i x => tateThetaGauge (r i) x / tateThetaGauge (r i) 1)
      (fun x : ℂ => x) l K := by
    rw [Metric.tendstoUniformlyOn_iff] at hnormalized ⊢
    intro ε hε
    filter_upwards [hnormalized ε hε] with i hi x hx
    simpa only [id_eq, div_one] using hi x hx
  have hpowers := TendstoUniformlyOn.zpow_of_isCompact_of_ne_zero hnormalized' hK
    continuousOn_id (fun x hx => hKzero hx) m
  simpa only [pointedTateThetaGauge] using hpowers

end

end GaloisForLFunctions.HTGeometry
