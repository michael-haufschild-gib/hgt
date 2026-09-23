import GaloisForLFunctions.RHTower.EulerLogPrimePowerHerglotzMass
import GaloisForLFunctions.HTGeometry.PrimeLogHerglotz

namespace GaloisForLFunctions.RHTower

open GaloisForLFunctions.HTGeometry
open Set Filter Topology

noncomputable section

def eulerLogPrimePowerPoleSet : Set ℂ :=
  Set.range fun x : PrimePowerClockIndex => (eulerLogPrimePowerSupport x : ℂ)

theorem isOpen_compl_eulerLogPrimePowerPoleSet :
    IsOpen eulerLogPrimePowerPoleSetᶜ := by
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  let R : ℝ := z.re + 1
  let F : Set PrimePowerClockIndex := {x | eulerLogPrimePowerSupport x ≤ R}
  have hF : F.Finite := finite_eulerLogPrimePowerSupport_le R
  let E : Set ℂ := (fun x : PrimePowerClockIndex =>
    (eulerLogPrimePowerSupport x : ℂ)) '' F
  have hE : E.Finite := hF.image _
  refine ⟨{w : ℂ | w.re < R} \ E, ?_, ?_, ?_⟩
  · intro w hw
    rw [Set.mem_compl_iff]
    rintro ⟨x, hxw⟩
    apply hw.2
    refine ⟨x, ?_, hxw⟩
    change eulerLogPrimePowerSupport x ≤ R
    have hwre : eulerLogPrimePowerSupport x < R := by
      calc
        eulerLogPrimePowerSupport x =
            ((eulerLogPrimePowerSupport x : ℂ)).re := rfl
        _ = w.re := congrArg Complex.re hxw
        _ < R := hw.1
    exact hwre.le
  · exact (isOpen_lt Complex.continuous_re continuous_const).sdiff hE.isClosed
  · constructor
    · simp [R]
    · intro hzE
      rcases hzE with ⟨x, hxF, hxz⟩
      apply hz
      exact ⟨x, hxz⟩

lemma regularizedHerglotzKernel_eq_of_sub_ne
    {t : ℝ} {z : ℂ} (hden : (t : ℂ) - z ≠ 0) :
    regularizedHerglotzKernel t z =
      (nevanlinnaWeight t : ℂ) *
        (z + (1 + z ^ (2 : ℕ)) / ((t : ℂ) - z)) := by
  have hsq : (1 : ℂ) + (t : ℂ) ^ (2 : ℕ) ≠ 0 := one_add_sq_ne_zero t
  have hw : (nevanlinnaWeight t : ℂ) = (1 + (t : ℂ) ^ (2 : ℕ))⁻¹ := by
    rw [nevanlinnaWeight]
    push_cast
    ring
  rw [regularizedHerglotzKernel, hw]
  field_simp
  ring

theorem summableLocallyUniformlyOn_eulerLogPrimePowerHerglotz_off_poles :
    SummableLocallyUniformlyOn
      (fun x : PrimePowerClockIndex => fun z : ℂ =>
        (eulerLogPrimePowerWeight x.1 x.2 : ℂ) *
          regularizedHerglotzKernel (eulerLogPrimePowerSupport x) z)
      eulerLogPrimePowerPoleSetᶜ := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually
    isOpen_compl_eulerLogPrimePowerPoleSet
  intro K hK hKc
  obtain ⟨R, hR⟩ := hKc.isBounded.exists_norm_le
  let B : ℝ := max R 0
  let C : ℝ := B + (1 + B ^ (2 : ℕ))
  refine ⟨fun x => C * (eulerLogPrimePowerWeight x.1 x.2 *
    nevanlinnaWeight (eulerLogPrimePowerSupport x)),
    summable_eulerLogPrimePower_nevanlinnaMass.mul_left C, ?_⟩
  have hfinite := finite_eulerLogPrimePowerSupport_le (B + 1)
  filter_upwards [hfinite.eventually_cofinite_notMem] with x hx
  intro z hz
  have hB0 : 0 ≤ B := le_max_right _ _
  have hzNorm : ‖z‖ ≤ B := (hR z hz).trans (le_max_left _ _)
  have htLarge : B + 1 < eulerLogPrimePowerSupport x := by
    simpa using lt_of_not_ge hx
  have htPos : 0 < eulerLogPrimePowerSupport x :=
    eulerLogPrimePowerTime_pos x.1 x.2
  have htNorm : ‖(eulerLogPrimePowerSupport x : ℂ)‖ =
      eulerLogPrimePowerSupport x := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htPos]
  have hden : 1 ≤ ‖(eulerLogPrimePowerSupport x : ℂ) - z‖ := by
    calc
      (1 : ℝ) ≤ eulerLogPrimePowerSupport x - B := by linarith
      _ ≤ ‖(eulerLogPrimePowerSupport x : ℂ)‖ - ‖z‖ := by
        rw [htNorm]
        linarith
      _ ≤ ‖(eulerLogPrimePowerSupport x : ℂ) - z‖ := norm_sub_norm_le _ _
  have hdenNe : (eulerLogPrimePowerSupport x : ℂ) - z ≠ 0 :=
    norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans_le hden))
  have hinv : ‖((eulerLogPrimePowerSupport x : ℂ) - z)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact (inv_le_one₀ (zero_lt_one.trans_le hden)).2 hden
  have hzSq : ‖1 + z ^ (2 : ℕ)‖ ≤ 1 + B ^ (2 : ℕ) := by
    calc
      ‖1 + z ^ (2 : ℕ)‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ (2 : ℕ)‖ := norm_add_le _ _
      _ = 1 + ‖z‖ ^ (2 : ℕ) := by rw [norm_one, norm_pow]
      _ ≤ 1 + B ^ (2 : ℕ) := by gcongr
  have hinner : ‖z + (1 + z ^ (2 : ℕ)) /
      ((eulerLogPrimePowerSupport x : ℂ) - z)‖ ≤ C := by
    calc
      ‖z + (1 + z ^ (2 : ℕ)) /
          ((eulerLogPrimePowerSupport x : ℂ) - z)‖ ≤
        ‖z‖ + ‖1 + z ^ (2 : ℕ)‖ *
          ‖((eulerLogPrimePowerSupport x : ℂ) - z)⁻¹‖ := by
            rw [div_eq_mul_inv]
            calc
              ‖z + (1 + z ^ (2 : ℕ)) *
                  ((eulerLogPrimePowerSupport x : ℂ) - z)⁻¹‖ ≤
                ‖z‖ + ‖(1 + z ^ (2 : ℕ)) *
                  ((eulerLogPrimePowerSupport x : ℂ) - z)⁻¹‖ := norm_add_le _ _
              _ = ‖z‖ + ‖1 + z ^ (2 : ℕ)‖ *
                  ‖((eulerLogPrimePowerSupport x : ℂ) - z)⁻¹‖ := by rw [norm_mul]
      _ ≤ B + (1 + B ^ (2 : ℕ)) * 1 := by gcongr
      _ = C := by dsimp [C]; ring
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (eulerLogPrimePowerWeight_pos x.1 x.2),
    regularizedHerglotzKernel_eq_of_sub_ne hdenNe,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (nevanlinnaWeight_pos _)]
  calc
    eulerLogPrimePowerWeight x.1 x.2 *
        (nevanlinnaWeight (eulerLogPrimePowerSupport x) *
          ‖z + (1 + z ^ (2 : ℕ)) /
            ((eulerLogPrimePowerSupport x : ℂ) - z)‖) ≤
      eulerLogPrimePowerWeight x.1 x.2 *
        (nevanlinnaWeight (eulerLogPrimePowerSupport x) * C) := by
          gcongr
          exact (eulerLogPrimePowerWeight_pos x.1 x.2).le
          exact (nevanlinnaWeight_pos _).le
    _ = C * (eulerLogPrimePowerWeight x.1 x.2 *
        nevanlinnaWeight (eulerLogPrimePowerSupport x)) := by ring

theorem differentiableOn_eulerLogPrimePowerHerglotz_off_poles :
    DifferentiableOn ℂ eulerLogPrimePowerHerglotz
      eulerLogPrimePowerPoleSetᶜ := by
  apply SummableLocallyUniformlyOn.differentiableOn
    isOpen_compl_eulerLogPrimePowerPoleSet
    summableLocallyUniformlyOn_eulerLogPrimePowerHerglotz_off_poles
  intro x z hz
  have hne : (eulerLogPrimePowerSupport x : ℂ) - z ≠ 0 := by
    intro h
    apply hz
    exact ⟨x, sub_eq_zero.mp h⟩
  unfold regularizedHerglotzKernel
  apply DifferentiableAt.const_mul
  apply DifferentiableAt.sub
  · have hbase : DifferentiableAt ℂ
        (fun y : ℂ => (eulerLogPrimePowerSupport x : ℂ) - y) z :=
      (differentiableAt_const
        (c := (eulerLogPrimePowerSupport x : ℂ))).sub differentiableAt_id
    have hdiff : DifferentiableAt ℂ
        (fun y : ℂ => ((eulerLogPrimePowerSupport x : ℂ) - y)⁻¹) z :=
      hbase.inv hne
    simpa [one_div] using hdiff
  · exact differentiableAt_const _

def eulerLogPrimePowerPoleSetOn (S : Set PrimePowerClockIndex) : Set ℂ :=
  Set.range fun x : S => (eulerLogPrimePowerSupport x : ℂ)

theorem isOpen_compl_eulerLogPrimePowerPoleSetOn
    (S : Set PrimePowerClockIndex) :
    IsOpen (eulerLogPrimePowerPoleSetOn S)ᶜ := by
  rw [isOpen_iff_forall_mem_open]
  intro z hz
  let R : ℝ := z.re + 1
  let F : Set S := {x | eulerLogPrimePowerSupport x ≤ R}
  have hF : F.Finite := by
    change ((Subtype.val : S → PrimePowerClockIndex) ⁻¹'
      {x | eulerLogPrimePowerSupport x ≤ R}).Finite
    exact (finite_eulerLogPrimePowerSupport_le R).preimage
      (Set.injOn_of_injective Subtype.val_injective)
  let E : Set ℂ := (fun x : S =>
    (eulerLogPrimePowerSupport x : ℂ)) '' F
  have hE : E.Finite := hF.image _
  refine ⟨{w : ℂ | w.re < R} \ E, ?_, ?_, ?_⟩
  · intro w hw
    rw [Set.mem_compl_iff]
    rintro ⟨x, hxw⟩
    apply hw.2
    refine ⟨x, ?_, hxw⟩
    change eulerLogPrimePowerSupport (x : PrimePowerClockIndex) ≤ R
    have hwre : eulerLogPrimePowerSupport (x : PrimePowerClockIndex) < R := by
      calc
        eulerLogPrimePowerSupport (x : PrimePowerClockIndex) =
            ((eulerLogPrimePowerSupport (x : PrimePowerClockIndex) : ℂ)).re := rfl
        _ = w.re := congrArg Complex.re hxw
        _ < R := hw.1
    exact hwre.le
  · exact (isOpen_lt Complex.continuous_re continuous_const).sdiff hE.isClosed
  · constructor
    · simp [R]
    · intro hzE
      rcases hzE with ⟨x, hxF, hxz⟩
      apply hz
      exact ⟨x, hxz⟩

private theorem summableLocallyUniformlyOn_eulerLogPrimePowerHerglotz_on_off_poles
    (S : Set PrimePowerClockIndex) :
    SummableLocallyUniformlyOn
      (fun x : S => fun z : ℂ =>
        (eulerLogPrimePowerWeight
          (x : PrimePowerClockIndex).1 (x : PrimePowerClockIndex).2 : ℂ) *
          regularizedHerglotzKernel
            (eulerLogPrimePowerSupport (x : PrimePowerClockIndex)) z)
      (eulerLogPrimePowerPoleSetOn S)ᶜ := by
  apply SummableLocallyUniformlyOn.of_locally_bounded_eventually
    (isOpen_compl_eulerLogPrimePowerPoleSetOn S)
  intro K hK hKc
  obtain ⟨R, hR⟩ := hKc.isBounded.exists_norm_le
  let B : ℝ := max R 0
  let C : ℝ := B + (1 + B ^ (2 : ℕ))
  refine ⟨fun x : S => C *
    (eulerLogPrimePowerWeight
      (x : PrimePowerClockIndex).1 (x : PrimePowerClockIndex).2 *
      nevanlinnaWeight (eulerLogPrimePowerSupport (x : PrimePowerClockIndex))), ?_, ?_⟩
  · exact (summable_eulerLogPrimePower_nevanlinnaMass.mul_left C).subtype S
  · have hfinite : Set.Finite {x : S |
        eulerLogPrimePowerSupport (x : PrimePowerClockIndex) ≤ B + 1} := by
      change ((Subtype.val : S → PrimePowerClockIndex) ⁻¹'
        {x | eulerLogPrimePowerSupport x ≤ B + 1}).Finite
      exact (finite_eulerLogPrimePowerSupport_le (B + 1)).preimage
        (Set.injOn_of_injective Subtype.val_injective)
    filter_upwards [hfinite.eventually_cofinite_notMem] with x hx
    intro z hz
    have hB0 : 0 ≤ B := le_max_right _ _
    have hzNorm : ‖z‖ ≤ B := (hR z hz).trans (le_max_left _ _)
    have htLarge : B + 1 <
        eulerLogPrimePowerSupport (x : PrimePowerClockIndex) := by
      simpa using lt_of_not_ge hx
    have htPos : 0 < eulerLogPrimePowerSupport (x : PrimePowerClockIndex) :=
      eulerLogPrimePowerTime_pos
        (x : PrimePowerClockIndex).1 (x : PrimePowerClockIndex).2
    have htNorm : ‖(eulerLogPrimePowerSupport
        (x : PrimePowerClockIndex) : ℂ)‖ =
        eulerLogPrimePowerSupport (x : PrimePowerClockIndex) := by
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htPos]
    have hden : 1 ≤ ‖(eulerLogPrimePowerSupport
        (x : PrimePowerClockIndex) : ℂ) - z‖ := by
      calc
        (1 : ℝ) ≤ eulerLogPrimePowerSupport (x : PrimePowerClockIndex) - B := by
          linarith
        _ ≤ ‖(eulerLogPrimePowerSupport (x : PrimePowerClockIndex) : ℂ)‖ - ‖z‖ := by
          rw [htNorm]
          linarith
        _ ≤ ‖(eulerLogPrimePowerSupport (x : PrimePowerClockIndex) : ℂ) - z‖ :=
          norm_sub_norm_le _ _
    have hdenNe : (eulerLogPrimePowerSupport
        (x : PrimePowerClockIndex) : ℂ) - z ≠ 0 :=
      norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans_le hden))
    have hinv : ‖((eulerLogPrimePowerSupport
        (x : PrimePowerClockIndex) : ℂ) - z)⁻¹‖ ≤ 1 := by
      rw [norm_inv]
      exact (inv_le_one₀ (zero_lt_one.trans_le hden)).2 hden
    have hzSq : ‖1 + z ^ (2 : ℕ)‖ ≤ 1 + B ^ (2 : ℕ) := by
      calc
        ‖1 + z ^ (2 : ℕ)‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ (2 : ℕ)‖ := norm_add_le _ _
        _ = 1 + ‖z‖ ^ (2 : ℕ) := by rw [norm_one, norm_pow]
        _ ≤ 1 + B ^ (2 : ℕ) := by gcongr
    have hinner : ‖z + (1 + z ^ (2 : ℕ)) /
        ((eulerLogPrimePowerSupport (x : PrimePowerClockIndex) : ℂ) - z)‖ ≤ C := by
      calc
        ‖z + (1 + z ^ (2 : ℕ)) /
            ((eulerLogPrimePowerSupport (x : PrimePowerClockIndex) : ℂ) - z)‖ ≤
          ‖z‖ + ‖1 + z ^ (2 : ℕ)‖ *
            ‖((eulerLogPrimePowerSupport (x : PrimePowerClockIndex) : ℂ) - z)⁻¹‖ := by
              rw [div_eq_mul_inv]
              calc
                ‖z + (1 + z ^ (2 : ℕ)) *
                    ((eulerLogPrimePowerSupport
                      (x : PrimePowerClockIndex) : ℂ) - z)⁻¹‖ ≤
                  ‖z‖ + ‖(1 + z ^ (2 : ℕ)) *
                    ((eulerLogPrimePowerSupport
                      (x : PrimePowerClockIndex) : ℂ) - z)⁻¹‖ := norm_add_le _ _
                _ = ‖z‖ + ‖1 + z ^ (2 : ℕ)‖ *
                    ‖((eulerLogPrimePowerSupport
                      (x : PrimePowerClockIndex) : ℂ) - z)⁻¹‖ := by rw [norm_mul]
        _ ≤ B + (1 + B ^ (2 : ℕ)) * 1 := by gcongr
        _ = C := by dsimp [C]; ring
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (eulerLogPrimePowerWeight_pos
        (x : PrimePowerClockIndex).1 (x : PrimePowerClockIndex).2),
      regularizedHerglotzKernel_eq_of_sub_ne hdenNe,
      norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (nevanlinnaWeight_pos _)]
    calc
      eulerLogPrimePowerWeight
          (x : PrimePowerClockIndex).1 (x : PrimePowerClockIndex).2 *
          (nevanlinnaWeight (eulerLogPrimePowerSupport (x : PrimePowerClockIndex)) *
            ‖z + (1 + z ^ (2 : ℕ)) /
              ((eulerLogPrimePowerSupport (x : PrimePowerClockIndex) : ℂ) - z)‖) ≤
        eulerLogPrimePowerWeight
            (x : PrimePowerClockIndex).1 (x : PrimePowerClockIndex).2 *
          (nevanlinnaWeight (eulerLogPrimePowerSupport (x : PrimePowerClockIndex)) * C) := by
            gcongr
            exact (eulerLogPrimePowerWeight_pos
              (x : PrimePowerClockIndex).1 (x : PrimePowerClockIndex).2).le
            exact (nevanlinnaWeight_pos _).le
      _ = C * (eulerLogPrimePowerWeight
          (x : PrimePowerClockIndex).1 (x : PrimePowerClockIndex).2 *
          nevanlinnaWeight (eulerLogPrimePowerSupport (x : PrimePowerClockIndex))) := by
            ring

def eulerLogPrimePowerHerglotzTail
    (x₀ : PrimePowerClockIndex) (z : ℂ) : ℂ :=
  ∑' x : {x : PrimePowerClockIndex // x ∉ ({x₀} : Finset PrimePowerClockIndex)},
    (eulerLogPrimePowerWeight
      (x : PrimePowerClockIndex).1 (x : PrimePowerClockIndex).2 : ℂ) *
      regularizedHerglotzKernel
        (eulerLogPrimePowerSupport (x : PrimePowerClockIndex)) z

theorem eulerLogPrimePowerCenter_notMem_otherPoleSet
    (x₀ : PrimePowerClockIndex) :
    (eulerLogPrimePowerSupport x₀ : ℂ) ∈
      (eulerLogPrimePowerPoleSetOn
        {x | x ∉ ({x₀} : Finset PrimePowerClockIndex)})ᶜ := by
  rw [Set.mem_compl_iff]
  rintro ⟨x, hx⟩
  apply x.property
  rw [Finset.mem_singleton]
  apply eulerLogPrimePowerSupport_injective
  exact Complex.ofReal_injective hx

theorem differentiableAt_eulerLogPrimePowerHerglotzTail
    (x₀ : PrimePowerClockIndex) :
    DifferentiableAt ℂ (eulerLogPrimePowerHerglotzTail x₀)
      (eulerLogPrimePowerSupport x₀ : ℂ) := by
  let S : Set PrimePowerClockIndex :=
    {x | x ∉ ({x₀} : Finset PrimePowerClockIndex)}
  have hsum := summableLocallyUniformlyOn_eulerLogPrimePowerHerglotz_on_off_poles S
  have hdiff : DifferentiableOn ℂ (eulerLogPrimePowerHerglotzTail x₀)
      (eulerLogPrimePowerPoleSetOn S)ᶜ := by
    apply SummableLocallyUniformlyOn.differentiableOn
      (isOpen_compl_eulerLogPrimePowerPoleSetOn S) hsum
    intro x z hz
    have hne : (eulerLogPrimePowerSupport (x : PrimePowerClockIndex) : ℂ) - z ≠ 0 := by
      intro h
      apply hz
      exact ⟨x, sub_eq_zero.mp h⟩
    unfold regularizedHerglotzKernel
    apply DifferentiableAt.const_mul
    apply DifferentiableAt.sub
    · have hbase : DifferentiableAt ℂ
          (fun y : ℂ => (eulerLogPrimePowerSupport
            (x : PrimePowerClockIndex) : ℂ) - y) z :=
        (differentiableAt_const
          (c := (eulerLogPrimePowerSupport
            (x : PrimePowerClockIndex) : ℂ))).sub differentiableAt_id
      have hinv : DifferentiableAt ℂ
          (fun y : ℂ => ((eulerLogPrimePowerSupport
            (x : PrimePowerClockIndex) : ℂ) - y)⁻¹) z := hbase.inv hne
      simpa [one_div] using hinv
    · exact differentiableAt_const _
  exact (hdiff _ (eulerLogPrimePowerCenter_notMem_otherPoleSet x₀)).differentiableAt
    ((isOpen_compl_eulerLogPrimePowerPoleSetOn S).mem_nhds
      (eulerLogPrimePowerCenter_notMem_otherPoleSet x₀))

theorem summable_eulerLogPrimePowerHerglotzTerm_all (z : ℂ) :
    Summable fun x : PrimePowerClockIndex =>
      (eulerLogPrimePowerWeight x.1 x.2 : ℂ) *
        regularizedHerglotzKernel (eulerLogPrimePowerSupport x) z := by
  let B : ℝ := ‖z‖
  let C : ℝ := B + (1 + B ^ (2 : ℕ))
  apply Summable.of_norm_bounded_eventually
    (summable_eulerLogPrimePower_nevanlinnaMass.mul_left C)
  have hfinite := finite_eulerLogPrimePowerSupport_le (B + 1)
  filter_upwards [hfinite.eventually_cofinite_notMem] with x hx
  have hB0 : 0 ≤ B := by dsimp [B]; positivity
  have htLarge : B + 1 < eulerLogPrimePowerSupport x := by
    simpa using lt_of_not_ge hx
  have htPos : 0 < eulerLogPrimePowerSupport x :=
    eulerLogPrimePowerTime_pos x.1 x.2
  have htNorm : ‖(eulerLogPrimePowerSupport x : ℂ)‖ =
      eulerLogPrimePowerSupport x := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos htPos]
  have hden : 1 ≤ ‖(eulerLogPrimePowerSupport x : ℂ) - z‖ := by
    calc
      (1 : ℝ) ≤ eulerLogPrimePowerSupport x - B := by linarith
      _ = ‖(eulerLogPrimePowerSupport x : ℂ)‖ - ‖z‖ := by
        rw [htNorm]
      _ ≤ ‖(eulerLogPrimePowerSupport x : ℂ) - z‖ := norm_sub_norm_le _ _
  have hdenNe : (eulerLogPrimePowerSupport x : ℂ) - z ≠ 0 :=
    norm_ne_zero_iff.mp (ne_of_gt (zero_lt_one.trans_le hden))
  have hinv : ‖((eulerLogPrimePowerSupport x : ℂ) - z)⁻¹‖ ≤ 1 := by
    rw [norm_inv]
    exact (inv_le_one₀ (zero_lt_one.trans_le hden)).2 hden
  have hzSq : ‖1 + z ^ (2 : ℕ)‖ ≤ 1 + B ^ (2 : ℕ) := by
    calc
      ‖1 + z ^ (2 : ℕ)‖ ≤ ‖(1 : ℂ)‖ + ‖z ^ (2 : ℕ)‖ := norm_add_le _ _
      _ = 1 + ‖z‖ ^ (2 : ℕ) := by rw [norm_one, norm_pow]
      _ = 1 + B ^ (2 : ℕ) := rfl
  have hinner : ‖z + (1 + z ^ (2 : ℕ)) /
      ((eulerLogPrimePowerSupport x : ℂ) - z)‖ ≤ C := by
    calc
      ‖z + (1 + z ^ (2 : ℕ)) / ((eulerLogPrimePowerSupport x : ℂ) - z)‖ ≤
        ‖z‖ + ‖1 + z ^ (2 : ℕ)‖ *
          ‖((eulerLogPrimePowerSupport x : ℂ) - z)⁻¹‖ := by
            rw [div_eq_mul_inv]
            calc
              ‖z + (1 + z ^ (2 : ℕ)) *
                  ((eulerLogPrimePowerSupport x : ℂ) - z)⁻¹‖ ≤
                ‖z‖ + ‖(1 + z ^ (2 : ℕ)) *
                  ((eulerLogPrimePowerSupport x : ℂ) - z)⁻¹‖ := norm_add_le _ _
              _ = ‖z‖ + ‖1 + z ^ (2 : ℕ)‖ *
                  ‖((eulerLogPrimePowerSupport x : ℂ) - z)⁻¹‖ := by rw [norm_mul]
      _ ≤ B + (1 + B ^ (2 : ℕ)) * 1 := by gcongr
      _ = C := by dsimp [C]; ring
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (eulerLogPrimePowerWeight_pos x.1 x.2),
    regularizedHerglotzKernel_eq_of_sub_ne hdenNe,
    norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (nevanlinnaWeight_pos _)]
  calc
    eulerLogPrimePowerWeight x.1 x.2 *
        (nevanlinnaWeight (eulerLogPrimePowerSupport x) *
          ‖z + (1 + z ^ (2 : ℕ)) /
            ((eulerLogPrimePowerSupport x : ℂ) - z)‖) ≤
      eulerLogPrimePowerWeight x.1 x.2 *
        (nevanlinnaWeight (eulerLogPrimePowerSupport x) * C) := by
          gcongr
          exact (eulerLogPrimePowerWeight_pos x.1 x.2).le
          exact (nevanlinnaWeight_pos _).le
    _ = C * (eulerLogPrimePowerWeight x.1 x.2 *
        nevanlinnaWeight (eulerLogPrimePowerSupport x)) := by ring

def eulerLogPrimePowerHerglotzRegularPart
    (x₀ : PrimePowerClockIndex) (z : ℂ) : ℂ :=
  eulerLogPrimePowerHerglotzTail x₀ z -
    (eulerLogPrimePowerWeight x₀.1 x₀.2 : ℂ) *
      (eulerLogPrimePowerSupport x₀ : ℂ) /
        (1 + (eulerLogPrimePowerSupport x₀ : ℂ) ^ (2 : ℕ))

theorem differentiableAt_eulerLogPrimePowerHerglotzRegularPart
    (x₀ : PrimePowerClockIndex) :
    DifferentiableAt ℂ (eulerLogPrimePowerHerglotzRegularPart x₀)
      (eulerLogPrimePowerSupport x₀ : ℂ) := by
  exact (differentiableAt_eulerLogPrimePowerHerglotzTail x₀).sub
    (differentiableAt_const _)

theorem eulerLogPrimePowerHerglotz_add_polar_eq_regularPart
    (x₀ : PrimePowerClockIndex) (z : ℂ) :
    eulerLogPrimePowerHerglotz z +
        (eulerLogPrimePowerWeight x₀.1 x₀.2 : ℂ) *
          (z - (eulerLogPrimePowerSupport x₀ : ℂ))⁻¹ =
      eulerLogPrimePowerHerglotzRegularPart x₀ z := by
  let f : PrimePowerClockIndex → ℂ := fun x =>
    (eulerLogPrimePowerWeight x.1 x.2 : ℂ) *
      regularizedHerglotzKernel (eulerLogPrimePowerSupport x) z
  have hsum : Summable f := summable_eulerLogPrimePowerHerglotzTerm_all z
  have hsplit := hsum.sum_add_tsum_subtype_compl {x₀}
  have heq : f x₀ + eulerLogPrimePowerHerglotzTail x₀ z =
      eulerLogPrimePowerHerglotz z := by
    simpa [f, eulerLogPrimePowerHerglotzTail,
      eulerLogPrimePowerHerglotz, eulerLogPrimePowerSupport] using hsplit
  rw [← heq]
  have hinv : ((eulerLogPrimePowerSupport x₀ : ℂ) - z)⁻¹ =
      -(z - (eulerLogPrimePowerSupport x₀ : ℂ))⁻¹ := by
    rw [← inv_neg, neg_sub]
  rw [show f x₀ = (eulerLogPrimePowerWeight x₀.1 x₀.2 : ℂ) *
      regularizedHerglotzKernel (eulerLogPrimePowerSupport x₀) z by rfl,
    regularizedHerglotzKernel, one_div, hinv,
    eulerLogPrimePowerHerglotzRegularPart]
  ring

theorem hasSimplePoleAt_eulerLogPrimePowerHerglotz
    (x₀ : PrimePowerClockIndex) :
    HasSimplePoleAt eulerLogPrimePowerHerglotz
      (eulerLogPrimePowerSupport x₀ : ℂ)
      (-(eulerLogPrimePowerWeight x₀.1 x₀.2 : ℂ)) := by
  constructor
  · exact neg_ne_zero.mpr (Complex.ofReal_ne_zero.mpr
      (ne_of_gt (eulerLogPrimePowerWeight_pos x₀.1 x₀.2)))
  · have hreg :=
      (differentiableAt_eulerLogPrimePowerHerglotzRegularPart x₀).continuousAt
    convert hreg using 1
    funext z
    simpa using eulerLogPrimePowerHerglotz_add_polar_eq_regularPart x₀ z

end

end GaloisForLFunctions.RHTower
