import GaloisForLFunctions.HTGeometry.HerglotzDiscreteSupportSeries
import GaloisForLFunctions.HTGeometry.PrimeLogHerglotz
import GaloisForLFunctions.HTGeometry.RealAnalyticInnerPhase
import GaloisForLFunctions.HTGeometry.EscapingRealSequenceCover

/-!
# Meromorphic-inner regularization at an escaping real divisor

An escaping injective real sequence carrying positive summable masses defines a discrete
Herglotz function.  Its Cayley transform extends analytically through every real pole, takes the
value `1` there, is contractive in the upper half-plane, and is unimodular on the real line.

This is the exact real-level-set regularizer used in the Makarov--Poltoratski removal of real
zeros.  No finiteness assumption is imposed on the divisor.
-/

open Complex Filter Metric Set Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

/-- Discrete positive Cauchy/Herglotz series used by the real-level regularizer. -/
def realLevelHerglotz (mass atoms : ℕ → ℝ) (z : ℂ) : ℂ :=
  discreteHerglotz atoms mass z

/-- Pole carrier of the real-level Herglotz series. -/
def realLevelPoleSet (atoms : ℕ → ℝ) : Set ℂ :=
  Set.range fun n => (atoms n : ℂ)

/-- The pole carrier of an escaping real sequence is closed. -/
theorem isClosed_realLevelPoleSet
    {atoms : ℕ → ℝ} (hescape : Tendsto (fun n => |atoms n|) atTop atTop) :
    IsClosed (realLevelPoleSet atoms) := by
  rw [← isOpen_compl_iff]
  exact isOpen_compl_discreteHerglotzPoleSet hescape

/-- Pole carrier with one chosen index omitted. -/
def realLevelPoleSetExcept (atoms : ℕ → ℝ) (n₀ : ℕ) : Set ℂ :=
  Set.range fun n : {n : ℕ // n ≠ n₀} => (atoms n : ℂ)

theorem isOpen_compl_realLevelPoleSetExcept
    {atoms : ℕ → ℝ} (hescape : Tendsto (fun n => |atoms n|) atTop atTop)
    (n₀ : ℕ) : IsOpen (realLevelPoleSetExcept atoms n₀)ᶜ := by
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  let R : ℝ := ‖z‖ + 1
  have hfinite : Set.Finite {n : ℕ | |atoms n| ≤ R} :=
    finite_abs_atoms_le_of_tendsto hescape R
  let F : Set {n : ℕ // n ≠ n₀} := {n | |atoms n| ≤ R}
  have hF : F.Finite := by
    exact hfinite.preimage (Set.injOn_of_injective Subtype.val_injective)
  let E : Set ℂ := (fun n : {n : ℕ // n ≠ n₀} => (atoms n : ℂ)) '' F
  have hE : E.Finite := hF.image _
  refine ⟨ball z 1 \ E, ?_, Metric.isOpen_ball.sdiff hE.isClosed, ?_⟩
  · intro w hw
    rw [Set.mem_compl_iff]
    rintro ⟨n, rfl⟩
    apply hw.2
    refine ⟨n, ?_, rfl⟩
    change |atoms n| ≤ R
    have hdist : ‖(atoms n : ℂ) - z‖ < 1 := by
      simpa [Complex.dist_eq, norm_sub_rev] using mem_ball.mp hw.1
    have hnorm : ‖(atoms n : ℂ)‖ ≤ ‖z‖ + 1 := by
      calc
        ‖(atoms n : ℂ)‖ ≤ ‖(atoms n : ℂ) - z‖ + ‖z‖ := by
          simpa using norm_add_le ((atoms n : ℂ) - z) z
        _ ≤ ‖z‖ + 1 := by linarith
    simpa [R, Complex.norm_real, Real.norm_eq_abs] using hnorm
  · refine ⟨mem_ball_self zero_lt_one, ?_⟩
    rintro ⟨n, hnF, hnz⟩
    exact hz ⟨n, hnz⟩

/-- Every listed point of an injective escaping real sequence is isolated from the other listed
points. -/
theorem exists_ball_inter_realLevelPoleSet_eq_singleton
    {atoms : ℕ → ℝ} (hinj : Function.Injective atoms)
    (hescape : Tendsto (fun n => |atoms n|) atTop atTop) (n₀ : ℕ) :
    ∃ r > 0, ball (atoms n₀ : ℂ) r ∩ realLevelPoleSet atoms = {(atoms n₀ : ℂ)} := by
  have hopen : IsOpen (realLevelPoleSetExcept atoms n₀)ᶜ :=
    isOpen_compl_realLevelPoleSetExcept hescape n₀
  have hmem : (atoms n₀ : ℂ) ∈ (realLevelPoleSetExcept atoms n₀)ᶜ := by
    rw [Set.mem_compl_iff]
    rintro ⟨n, hn⟩
    exact n.property (hinj (Complex.ofReal_injective hn))
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.1 hopen _ hmem
  refine ⟨r, hr, ?_⟩
  ext z
  constructor
  · rintro ⟨hzball, ⟨n, hn⟩⟩
    have hznot : z ∉ realLevelPoleSetExcept atoms n₀ := hball hzball
    have : z = (atoms n₀ : ℂ) := by
      by_contra hne
      have hn0 : n ≠ n₀ := by
        intro heq
        subst n
        exact hne hn.symm
      exact hznot ⟨⟨n, hn0⟩, hn⟩
    simpa [this]
  · intro hz
    have hz' : z = (atoms n₀ : ℂ) := by simpa using hz
    subst z
    exact ⟨mem_ball_self hr, ⟨n₀, rfl⟩⟩

/-- The series with one pole omitted. -/
def realLevelHerglotzTail (mass atoms : ℕ → ℝ) (n₀ : ℕ) (z : ℂ) : ℂ :=
  ∑' n : {n : ℕ // n ≠ n₀},
    ((mass n : ℝ) : ℂ) * ((atoms n : ℂ) - z)⁻¹

private theorem summableLocallyUniformlyOn_realLevelHerglotzTail
    {mass atoms : ℕ → ℝ} (hmass : Summable mass)
    (hescape : Tendsto (fun n => |atoms n|) atTop atTop)
    (n₀ : ℕ) {r : ℝ}
    (hball : ball (atoms n₀ : ℂ) r ∩ realLevelPoleSet atoms = {(atoms n₀ : ℂ)}) :
    SummableLocallyUniformlyOn
      (fun n : {n : ℕ // n ≠ n₀} => fun z : ℂ =>
        ((mass n : ℝ) : ℂ) * ((atoms n : ℂ) - z)⁻¹)
      (ball (atoms n₀ : ℂ) r) := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually Metric.isOpen_ball
  intro K hK hKcompact
  obtain ⟨R, hR⟩ := hKcompact.isBounded.exists_norm_le
  refine ⟨fun n : {n : ℕ // n ≠ n₀} => |mass n|,
    (by simpa [Real.norm_eq_abs, Function.comp_def] using
      hmass.norm.subtype (fun n : ℕ => n ≠ n₀)), ?_⟩
  have hfinite : Set.Finite {n : ℕ | |atoms n| ≤ R + 1} :=
    finite_abs_atoms_le_of_tendsto hescape (R + 1)
  have hfinite' : Set.Finite
      {n : {n : ℕ // n ≠ n₀} | |atoms n| ≤ R + 1} := by
    exact hfinite.preimage (Set.injOn_of_injective Subtype.val_injective)
  filter_upwards [hfinite'.eventually_cofinite_notMem] with n hn
  intro z hz
  have hatom : R + 1 < |atoms n| := by simpa using lt_of_not_ge hn
  have hzR : ‖z‖ ≤ R := hR z hz
  have hden : 1 ≤ ‖(atoms n : ℂ) - z‖ := by
    calc
      1 ≤ |atoms n| - R := by linarith
      _ ≤ ‖(atoms n : ℂ)‖ - ‖z‖ := by
        simpa [Complex.norm_real, Real.norm_eq_abs] using sub_le_sub_left hzR |atoms n|
      _ ≤ ‖(atoms n : ℂ) - z‖ := norm_sub_norm_le _ _
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  calc
    |mass n| * ‖(atoms n : ℂ) - z‖⁻¹ ≤ |mass n| * 1 := by
      gcongr
      exact (inv_le_one₀ (by positivity)).2 hden
    _ = |mass n| := mul_one _

theorem differentiableOn_realLevelHerglotzTail
    {mass atoms : ℕ → ℝ} (hmass : Summable mass)
    (hinj : Function.Injective atoms)
    (hescape : Tendsto (fun n => |atoms n|) atTop atTop) (n₀ : ℕ) :
    ∃ r > 0, DifferentiableOn ℂ (realLevelHerglotzTail mass atoms n₀)
      (ball (atoms n₀ : ℂ) r) := by
  obtain ⟨r, hr, hball⟩ :=
    exists_ball_inter_realLevelPoleSet_eq_singleton hinj hescape n₀
  refine ⟨r, hr, ?_⟩
  apply SummableLocallyUniformlyOn.differentiableOn Metric.isOpen_ball
    (summableLocallyUniformlyOn_realLevelHerglotzTail hmass hescape n₀ hball)
  intro n z hz
  have hne : (atoms n : ℂ) - z ≠ 0 := by
    intro heq
    have hzatom : z = (atoms n : ℂ) := (sub_eq_zero.mp heq).symm
    have hzpole : z ∈ realLevelPoleSet atoms := ⟨n, hzatom.symm⟩
    have hzsingle : z ∈ ({(atoms n₀ : ℂ)} : Set ℂ) := by
      rw [← hball]
      exact ⟨hz, hzpole⟩
    have heqAtoms : atoms n = atoms n₀ := by
      have : (atoms n : ℂ) = (atoms n₀ : ℂ) := by simpa [hzatom] using hzsingle
      exact Complex.ofReal_injective this
    exact n.property (hinj heqAtoms)
  exact (((differentiableAt_const (c := (atoms n : ℂ))).sub
    differentiableAt_id).inv hne).const_mul _

private theorem realLevelHerglotz_eq_term_add_tail
    {mass atoms : ℕ → ℝ} (hmass : Summable mass)
    (hescape : Tendsto (fun n => |atoms n|) atTop atTop) (n₀ : ℕ) :
    realLevelHerglotz mass atoms = fun z =>
      (mass n₀ : ℂ) * ((atoms n₀ : ℂ) - z)⁻¹ +
        realLevelHerglotzTail mass atoms n₀ z := by
  funext z
  have hs : Summable fun n =>
      (mass n : ℂ) * ((atoms n : ℂ) - z)⁻¹ := by
    apply Summable.of_norm_bounded_eventually hmass.norm
    have hfinite : Set.Finite {n : ℕ | |atoms n| ≤ ‖z‖ + 1} :=
      finite_abs_atoms_le_of_tendsto hescape (‖z‖ + 1)
    filter_upwards [hfinite.eventually_cofinite_notMem] with n hn
    have hden : 1 ≤ ‖(atoms n : ℂ) - z‖ := by
      have ha : ‖z‖ + 1 < |atoms n| := by simpa using lt_of_not_ge hn
      calc
        1 ≤ |atoms n| - ‖z‖ := by linarith
        _ = ‖(atoms n : ℂ)‖ - ‖z‖ := by simp [Complex.norm_real, Real.norm_eq_abs]
        _ ≤ ‖(atoms n : ℂ) - z‖ := norm_sub_norm_le _ _
    rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_of_le_one_right (abs_nonneg _)
      ((inv_le_one₀ (by positivity)).2 hden)
  rw [realLevelHerglotz, discreteHerglotz,
    hs.tsum_eq_add_tsum_ite n₀]
  congr 1
  unfold realLevelHerglotzTail
  let S : Set ℕ := {n | n ≠ n₀}
  calc
    (∑' n : ℕ, if n = n₀ then 0
      else (mass n : ℂ) * ((atoms n : ℂ) - z)⁻¹) =
        ∑' n : ℕ, S.indicator
          (fun n => (mass n : ℂ) * ((atoms n : ℂ) - z)⁻¹) n := by
      apply tsum_congr
      intro n
      by_cases hn : n = n₀ <;> simp [S, hn]
    _ = ∑' n : S, (mass n : ℂ) * ((atoms n : ℂ) - z)⁻¹ :=
      (tsum_subtype S _).symm

/-- Absolute convergence of the discrete Herglotz series at every non-pole point (indeed at every
point under Lean's totalized inverse). -/
theorem summable_realLevelHerglotz_term
    {mass atoms : ℕ → ℝ} (hmass : Summable mass)
    (hescape : Tendsto (fun n => |atoms n|) atTop atTop) (z : ℂ) :
    Summable fun n => (mass n : ℂ) * ((atoms n : ℂ) - z)⁻¹ := by
  apply Summable.of_norm_bounded_eventually hmass.norm
  have hfinite : Set.Finite {n : ℕ | |atoms n| ≤ ‖z‖ + 1} :=
    finite_abs_atoms_le_of_tendsto hescape (‖z‖ + 1)
  filter_upwards [hfinite.eventually_cofinite_notMem] with n hn
  have hden : 1 ≤ ‖(atoms n : ℂ) - z‖ := by
    have ha : ‖z‖ + 1 < |atoms n| := by simpa using lt_of_not_ge hn
    calc
      1 ≤ |atoms n| - ‖z‖ := by linarith
      _ = ‖(atoms n : ℂ)‖ - ‖z‖ := by simp [Complex.norm_real, Real.norm_eq_abs]
      _ ≤ ‖(atoms n : ℂ) - z‖ := norm_sub_norm_le _ _
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  exact mul_le_of_le_one_right (abs_nonneg _)
    ((inv_le_one₀ (by positivity)).2 hden)

private theorem summableLocallyUniformlyOn_realLevelHerglotz_off_poles
    {mass atoms : ℕ → ℝ} (hmass : Summable mass)
    (hescape : Tendsto (fun n => |atoms n|) atTop atTop) :
    SummableLocallyUniformlyOn
      (fun n z => (mass n : ℂ) * ((atoms n : ℂ) - z)⁻¹)
      (realLevelPoleSet atoms)ᶜ := by
  have hopen : IsOpen (realLevelPoleSet atoms)ᶜ := by
    change IsOpen (discreteHerglotzPoleSet atoms)ᶜ
    exact isOpen_compl_discreteHerglotzPoleSet hescape
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually
    hopen
  intro K hK hKcompact
  obtain ⟨R, hR⟩ := hKcompact.isBounded.exists_norm_le
  refine ⟨fun n => |mass n|,
    (by simpa [Real.norm_eq_abs] using hmass.norm), ?_⟩
  have hfinite : Set.Finite {n : ℕ | |atoms n| ≤ R + 1} :=
    finite_abs_atoms_le_of_tendsto hescape (R + 1)
  filter_upwards [hfinite.eventually_cofinite_notMem] with n hn
  intro z hz
  have hatom : R + 1 < |atoms n| := by simpa using lt_of_not_ge hn
  have hzR : ‖z‖ ≤ R := hR z hz
  have hden : 1 ≤ ‖(atoms n : ℂ) - z‖ := by
    calc
      1 ≤ |atoms n| - R := by linarith
      _ ≤ ‖(atoms n : ℂ)‖ - ‖z‖ := by
        simpa [Complex.norm_real, Real.norm_eq_abs] using sub_le_sub_left hzR |atoms n|
      _ ≤ ‖(atoms n : ℂ) - z‖ := norm_sub_norm_le _ _
  rw [norm_mul, norm_inv, Complex.norm_real, Real.norm_eq_abs]
  calc
    |mass n| * ‖(atoms n : ℂ) - z‖⁻¹ ≤ |mass n| * 1 := by
      gcongr
      exact (inv_le_one₀ (by positivity)).2 hden
    _ = |mass n| := mul_one _

/-- The discrete Herglotz series is holomorphic away from its escaping real pole carrier. -/
theorem differentiableOn_realLevelHerglotz_off_poles
    {mass atoms : ℕ → ℝ} (hmass : Summable mass)
    (hescape : Tendsto (fun n => |atoms n|) atTop atTop) :
    DifferentiableOn ℂ (realLevelHerglotz mass atoms) (realLevelPoleSet atoms)ᶜ := by
  have hopen : IsOpen (realLevelPoleSet atoms)ᶜ := by
    change IsOpen (discreteHerglotzPoleSet atoms)ᶜ
    exact isOpen_compl_discreteHerglotzPoleSet hescape
  apply SummableLocallyUniformlyOn.differentiableOn
    hopen
    (summableLocallyUniformlyOn_realLevelHerglotz_off_poles hmass hescape)
  intro n z hz
  have hne : (atoms n : ℂ) - z ≠ 0 := by
    intro h
    apply hz
    exact ⟨n, sub_eq_zero.mp h⟩
  exact (((differentiableAt_const (c := (atoms n : ℂ))).sub
    differentiableAt_id).inv hne).const_mul _

/-- Off its poles, the Herglotz series is real on the real axis. -/
theorem realLevelHerglotz_ofReal_im
    {mass atoms : ℕ → ℝ} (hmass : Summable mass)
    (hescape : Tendsto (fun n => |atoms n|) atTop atTop)
    {x : ℝ} (hx : (x : ℂ) ∉ realLevelPoleSet atoms) :
    (realLevelHerglotz mass atoms (x : ℂ)).im = 0 := by
  have hs := summable_realLevelHerglotz_term hmass hescape (x : ℂ)
  rw [realLevelHerglotz, discreteHerglotz, Complex.im_tsum hs]
  simp [Complex.mul_im, Complex.inv_im, Complex.sub_im]

/-- Reciprocal of `H+i`, filled by zero at every real pole of `H`. -/
noncomputable def realLevelHerglotzReciprocal
    (mass atoms : ℕ → ℝ) (z : ℂ) : ℂ := by
  classical
  exact if z ∈ realLevelPoleSet atoms then 0
    else (realLevelHerglotz mass atoms z + I)⁻¹

theorem realLevelHerglotzReciprocal_at_atom
    (mass atoms : ℕ → ℝ) (n : ℕ) :
    realLevelHerglotzReciprocal mass atoms (atoms n : ℂ) = 0 := by
  simp [realLevelHerglotzReciprocal, realLevelPoleSet]

/-- Local analytic formula filling the reciprocal at one Herglotz pole. -/
def realLevelHerglotzReciprocalLocal
    (mass atoms : ℕ → ℝ) (n₀ : ℕ) (z : ℂ) : ℂ :=
  ((atoms n₀ : ℂ) - z) /
    ((mass n₀ : ℂ) + ((atoms n₀ : ℂ) - z) *
      (realLevelHerglotzTail mass atoms n₀ z + I))

theorem analyticAt_realLevelHerglotzReciprocal_at_atom
    {mass atoms : ℕ → ℝ} (hmass : Summable mass)
    (hmassPos : ∀ n, 0 < mass n) (hinj : Function.Injective atoms)
    (hescape : Tendsto (fun n => |atoms n|) atTop atTop) (n₀ : ℕ) :
    AnalyticAt ℂ (realLevelHerglotzReciprocal mass atoms) (atoms n₀ : ℂ) := by
  obtain ⟨r, hr, htail⟩ :=
    differentiableOn_realLevelHerglotzTail hmass hinj hescape n₀
  obtain ⟨rIso, hrIso, hIso⟩ :=
    exists_ball_inter_realLevelPoleSet_eq_singleton hinj hescape n₀
  let ρ := min r rIso
  have hρ : 0 < ρ := lt_min hr hrIso
  have htailAnalytic : AnalyticAt ℂ (realLevelHerglotzTail mass atoms n₀)
      (atoms n₀ : ℂ) :=
    (htail.analyticOnNhd Metric.isOpen_ball) _ (mem_ball_self hr)
  have hdenAnalytic : AnalyticAt ℂ (fun z : ℂ =>
      (mass n₀ : ℂ) + ((atoms n₀ : ℂ) - z) *
        (realLevelHerglotzTail mass atoms n₀ z + I)) (atoms n₀ : ℂ) := by
    fun_prop
  have hdenNe : (mass n₀ : ℂ) +
      ((atoms n₀ : ℂ) - (atoms n₀ : ℂ)) *
        (realLevelHerglotzTail mass atoms n₀ (atoms n₀ : ℂ) + I) ≠ 0 := by
    simpa using Complex.ofReal_ne_zero.mpr (hmassPos n₀).ne'
  have hlocal : AnalyticAt ℂ
      (realLevelHerglotzReciprocalLocal mass atoms n₀) (atoms n₀ : ℂ) := by
    unfold realLevelHerglotzReciprocalLocal
    exact (analyticAt_const.sub analyticAt_id).div hdenAnalytic hdenNe
  apply hlocal.congr
  filter_upwards [Metric.ball_mem_nhds (atoms n₀ : ℂ) hρ] with z hz
  have hzIso : z ∈ ball (atoms n₀ : ℂ) rIso :=
    mem_ball.mpr ((mem_ball.mp hz).trans_le (min_le_right _ _))
  by_cases hza : z = (atoms n₀ : ℂ)
  · subst z
    simp [realLevelHerglotzReciprocalLocal,
      realLevelHerglotzReciprocal_at_atom]
  · have hzPole : z ∉ realLevelPoleSet atoms := by
      intro hpole
      have hzsingle : z ∈ ({(atoms n₀ : ℂ)} : Set ℂ) := by
        rw [← hIso]
        exact ⟨hzIso, hpole⟩
      exact hza (by simpa using hzsingle)
    rw [realLevelHerglotzReciprocal, if_neg hzPole,
      realLevelHerglotzReciprocalLocal,
      realLevelHerglotz_eq_term_add_tail hmass hescape n₀]
    have hsub : (atoms n₀ : ℂ) - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hza)
    field_simp [hsub]
    ring

/-- The filled reciprocal is analytic at every real point. -/
theorem analyticAt_realLevelHerglotzReciprocal_ofReal
    {mass atoms : ℕ → ℝ} (hmass : Summable mass)
    (hmassPos : ∀ n, 0 < mass n) (hinj : Function.Injective atoms)
    (hescape : Tendsto (fun n => |atoms n|) atTop atTop) (x : ℝ) :
    AnalyticAt ℂ (realLevelHerglotzReciprocal mass atoms) (x : ℂ) := by
  by_cases hx : (x : ℂ) ∈ realLevelPoleSet atoms
  · obtain ⟨n, hn⟩ := hx
    rw [← hn]
    exact analyticAt_realLevelHerglotzReciprocal_at_atom
      hmass hmassPos hinj hescape n
  · have hH : AnalyticAt ℂ (realLevelHerglotz mass atoms) (x : ℂ) :=
      ((differentiableOn_realLevelHerglotz_off_poles hmass hescape).analyticOnNhd
        (by
          change IsOpen (discreteHerglotzPoleSet atoms)ᶜ
          exact isOpen_compl_discreteHerglotzPoleSet hescape)) _ hx
    have hden : realLevelHerglotz mass atoms (x : ℂ) + I ≠ 0 := by
      intro hzero
      have him : (realLevelHerglotz mass atoms (x : ℂ) + I).im = 1 := by
        rw [Complex.add_im, I_im,
          realLevelHerglotz_ofReal_im hmass hescape hx]
        norm_num
      rw [hzero] at him
      norm_num at him
    have hinv := (hH.add analyticAt_const).inv hden
    apply hinv.congr
    have hev : ∀ᶠ z in 𝓝 (x : ℂ), z ∈ (realLevelPoleSet atoms)ᶜ :=
      ((by
        change IsOpen (discreteHerglotzPoleSet atoms)ᶜ
        exact isOpen_compl_discreteHerglotzPoleSet hescape) :
          IsOpen (realLevelPoleSet atoms)ᶜ).mem_nhds hx
    filter_upwards [hev] with z hz
    have hznot : z ∉ realLevelPoleSet atoms := hz
    change (realLevelHerglotz mass atoms z + I)⁻¹ =
      realLevelHerglotzReciprocal mass atoms z
    rw [realLevelHerglotzReciprocal]
    simp [hznot]

/-- Cayley transform of the discrete Herglotz series, filled by `1` at its real poles. -/
def realLevelMeromorphicInner (mass atoms : ℕ → ℝ) (z : ℂ) : ℂ :=
  1 - 2 * I * realLevelHerglotzReciprocal mass atoms z

theorem realLevelMeromorphicInner_at_atom
    (mass atoms : ℕ → ℝ) (n : ℕ) :
    realLevelMeromorphicInner mass atoms (atoms n : ℂ) = 1 := by
  simp [realLevelMeromorphicInner, realLevelHerglotzReciprocal_at_atom]

theorem analyticAt_realLevelMeromorphicInner_ofReal
    {mass atoms : ℕ → ℝ} (hmass : Summable mass)
    (hmassPos : ∀ n, 0 < mass n) (hinj : Function.Injective atoms)
    (hescape : Tendsto (fun n => |atoms n|) atTop atTop) (x : ℝ) :
    AnalyticAt ℂ (realLevelMeromorphicInner mass atoms) (x : ℂ) := by
  unfold realLevelMeromorphicInner
  exact analyticAt_const.sub
    ((analyticAt_const.mul analyticAt_const).mul
      (analyticAt_realLevelHerglotzReciprocal_ofReal
        hmass hmassPos hinj hescape x))

/-- Positive masses make the discrete series Herglotz in the upper half-plane. -/
theorem realLevelHerglotz_im_nonneg
    {mass atoms : ℕ → ℝ} (hmass : Summable mass)
    (hmassNonneg : ∀ n, 0 ≤ mass n) {z : ℂ} (hz : 0 < z.im) :
    0 ≤ (realLevelHerglotz mass atoms z).im := by
  exact discreteHerglotz_im_nonneg atoms mass z hz hmassNonneg
    (by simpa [Real.norm_eq_abs, abs_of_nonneg (hmassNonneg _)] using hmass)

private theorem realLevelMeromorphicInner_eq_cayley
    {mass atoms : ℕ → ℝ} {z : ℂ}
    (hzPole : z ∉ realLevelPoleSet atoms)
    (hden : realLevelHerglotz mass atoms z + I ≠ 0) :
    realLevelMeromorphicInner mass atoms z =
      (realLevelHerglotz mass atoms z - I) /
        (realLevelHerglotz mass atoms z + I) := by
  rw [realLevelMeromorphicInner, realLevelHerglotzReciprocal]
  simp only [if_neg hzPole]
  field_simp [hden]
  ring

/-- The regularizer is Schur-contracting in the upper half-plane. -/
theorem norm_realLevelMeromorphicInner_le_one
    {mass atoms : ℕ → ℝ} (hmass : Summable mass)
    (hmassNonneg : ∀ n, 0 ≤ mass n) {z : ℂ} (hz : 0 < z.im) :
    ‖realLevelMeromorphicInner mass atoms z‖ ≤ 1 := by
  have hzPole : z ∉ realLevelPoleSet atoms := by
    rintro ⟨n, hn⟩
    have him := congrArg Complex.im hn
    simp at him
    linarith
  have hHim := realLevelHerglotz_im_nonneg (atoms := atoms)
    hmass hmassNonneg hz
  have hden : realLevelHerglotz mass atoms z + I ≠ 0 := by
    intro hzero
    have him : (realLevelHerglotz mass atoms z + I).im =
        (realLevelHerglotz mass atoms z).im + 1 := by simp
    rw [hzero] at him
    simp at him
    linarith
  rw [realLevelMeromorphicInner_eq_cayley hzPole hden]
  exact GaloisForLFunctions.cayley_herglotz_schur
    (realLevelHerglotz mass atoms z) hHim hden

/-- The real boundary of the regularizer is everywhere unimodular, including its filled pole
values. -/
theorem norm_realLevelMeromorphicInner_ofReal
    {mass atoms : ℕ → ℝ} (hmass : Summable mass)
    (hescape : Tendsto (fun n => |atoms n|) atTop atTop) (x : ℝ) :
    ‖realLevelMeromorphicInner mass atoms (x : ℂ)‖ = 1 := by
  by_cases hx : (x : ℂ) ∈ realLevelPoleSet atoms
  · obtain ⟨n, hn⟩ := hx
    rw [← hn, realLevelMeromorphicInner_at_atom]
    norm_num
  · have hHim := realLevelHerglotz_ofReal_im hmass hescape hx
    have hden : realLevelHerglotz mass atoms (x : ℂ) + I ≠ 0 := by
      intro hzero
      have him : (realLevelHerglotz mass atoms (x : ℂ) + I).im = 1 := by
        rw [Complex.add_im, I_im, hHim]
        norm_num
      rw [hzero] at him
      norm_num at him
    rw [realLevelMeromorphicInner_eq_cayley hx hden, norm_div]
    have hconj : (starRingEnd ℂ)
        (realLevelHerglotz mass atoms (x : ℂ) + I) =
          realLevelHerglotz mass atoms (x : ℂ) - I := by
      apply Complex.ext <;> simp [hHim]
    rw [← hconj, norm_conj, div_self (norm_ne_zero_iff.mpr hden)]

/-- Package the exact phase input supplied by the real-level meromorphic inner. -/
theorem exists_monotone_phase_realLevelMeromorphicInner
    {mass atoms : ℕ → ℝ} (hmass : Summable mass)
    (hmassPos : ∀ n, 0 < mass n) (hinj : Function.Injective atoms)
    (hescape : Tendsto (fun n => |atoms n|) atTop atTop) :
    ∃ alpha : ℝ → ℝ, Monotone alpha ∧ ∀ x : ℝ,
      realLevelMeromorphicInner mass atoms (x : ℂ) =
        Complex.exp ((alpha x : ℂ) * I) := by
  exact exists_monotone_phase_of_realAnalytic_inner
    (fun x => analyticAt_realLevelMeromorphicInner_ofReal
      hmass hmassPos hinj hescape x)
    (norm_realLevelMeromorphicInner_ofReal hmass hescape)
    (fun z hz => norm_realLevelMeromorphicInner_le_one hmass
      (fun n => (hmassPos n).le) hz)

/-- Fixed strictly positive summable masses for real-level regularization. -/
def realLevelGeometricMass (n : ℕ) : ℝ := (1 / 2 : ℝ) ^ n

theorem summable_realLevelGeometricMass : Summable realLevelGeometricMass := by
  change Summable fun n : ℕ => (1 / 2 : ℝ) ^ n
  exact summable_geometric_of_norm_lt_one (K := ℝ) (x := (1 / 2 : ℝ)) (by norm_num)

theorem realLevelGeometricMass_pos (n : ℕ) : 0 < realLevelGeometricMass n := by
  simp [realLevelGeometricMass]

/-- Exact Makarov--Poltoratski real-zero regularizer package.  A nontrivial function analytic
through the whole real axis has a locally finite real zero divisor.  An escaping enumeration of
that divisor, equipped with fixed positive summable masses, produces a real-analytic meromorphic
inner function equal to `1` at every real zero, together with its monotone boundary phase. -/
theorem exists_realZero_meromorphicInner_regularization
    {F : ℂ → ℂ} (hF : ∀ x : ℝ, AnalyticAt ℂ F (x : ℂ))
    {x₀ : ℝ} (hF₀ : F (x₀ : ℂ) ≠ 0) :
    ∃ atoms : ℕ → ℝ, ∃ alpha : ℝ → ℝ,
      Function.Injective atoms ∧
      Tendsto (fun n => |atoms n|) atTop atTop ∧
      (∀ x : ℝ, AnalyticAt ℂ
        (realLevelMeromorphicInner realLevelGeometricMass atoms) (x : ℂ)) ∧
      (∀ z : ℂ, 0 < z.im →
        ‖realLevelMeromorphicInner realLevelGeometricMass atoms z‖ ≤ 1) ∧
      (∀ x : ℝ,
        ‖realLevelMeromorphicInner realLevelGeometricMass atoms (x : ℂ)‖ = 1) ∧
      (∀ x : ℝ, F (x : ℂ) = 0 →
        realLevelMeromorphicInner realLevelGeometricMass atoms (x : ℂ) = 1) ∧
      Monotone alpha ∧
      ∀ x : ℝ, realLevelMeromorphicInner realLevelGeometricMass atoms (x : ℂ) =
        Complex.exp ((alpha x : ℂ) * I) := by
  obtain ⟨atoms, hinj, hescape, hcover⟩ :=
    exists_injective_escaping_realZero_sequence hF hF₀
  obtain ⟨alpha, halpha, hphase⟩ :=
    exists_monotone_phase_realLevelMeromorphicInner
      summable_realLevelGeometricMass realLevelGeometricMass_pos hinj hescape
  refine ⟨atoms, alpha, hinj, hescape, ?_, ?_, ?_, ?_, halpha, hphase⟩
  · exact fun x => analyticAt_realLevelMeromorphicInner_ofReal
      summable_realLevelGeometricMass realLevelGeometricMass_pos hinj hescape x
  · exact fun z hz => norm_realLevelMeromorphicInner_le_one
      summable_realLevelGeometricMass (fun n => (realLevelGeometricMass_pos n).le) hz
  · exact norm_realLevelMeromorphicInner_ofReal
      summable_realLevelGeometricMass hescape
  · intro x hx
    obtain ⟨n, hn⟩ := hcover hx
    rw [← hn]
    exact realLevelMeromorphicInner_at_atom realLevelGeometricMass atoms n

end

end GaloisForLFunctions.HTGeometry
