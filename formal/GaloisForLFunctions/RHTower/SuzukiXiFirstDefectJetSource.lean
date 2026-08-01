import GaloisForLFunctions.RHTower.SuzukiGroundEdgeCayleyUniversality
import GaloisForLFunctions.RHTower.SuzukiXiFirstDefectJet

/-!
# Suzuki source consequences of the Xi first-defect jet gap

This file turns the unconditional Xi target theorem into an exact source-facing obligation.
If Suzuki's parity energies identify the Xi first defect, then their normalized shares lie in

`even share ∈ (81/85, 1)` and `odd share ∈ (0, 4/85)`.

Moreover, locally uniform convergence of the disk-conjugated finite Suzuki Livšic carriers forces
the actual finite defect angles to converge to the Xi scalar.  This excludes both the universal
free boundary (`κ → 0`) and exact ground saturation (`κ → 1`) as possible Xi-identifying limits.
The remaining frontier is therefore quantitative source selection inside this strict polarization
window.
-/

open Complex Filter

namespace RHTower

noncomputable section

/-- Matching the Xi first defect forces a strict `81/85`–`4/85` split of normalized Suzuki
even/odd resolvent energy. -/
theorem xiHedenmalmLivsic_matching_source_parity_shares
    {evenEnergy oddEnergy : ℝ}
    (hsum : evenEnergy + oddEnergy ≠ 0)
    (hmatch :
      GaloisForLFunctions.RHTower.suzukiDefectAngle evenEnergy oddEnergy =
        xiHedenmalmLivsicFirstDefectJet) :
    evenEnergy / (evenEnergy + oddEnergy) ∈
        Set.Ioo ((81 : ℝ) / 85) 1 ∧
      oddEnergy / (evenEnergy + oddEnergy) ∈
        Set.Ioo 0 ((4 : ℝ) / 85) := by
  have heven :
      evenEnergy / (evenEnergy + oddEnergy) =
        (1 + GaloisForLFunctions.RHTower.suzukiDefectAngle
          evenEnergy oddEnergy) / 2 := by
    rw [GaloisForLFunctions.RHTower.suzukiDefectAngle]
    field_simp
    ring
  have hodd :
      oddEnergy / (evenEnergy + oddEnergy) =
        (1 - GaloisForLFunctions.RHTower.suzukiDefectAngle
          evenEnergy oddEnergy) / 2 := by
    rw [GaloisForLFunctions.RHTower.suzukiDefectAngle]
    field_simp
    ring
  rw [heven, hodd, hmatch]
  rcases xiHedenmalmLivsicFirstDefectJet_mem_Ioo with ⟨hlower, hupper⟩
  constructor <;> constructor <;> linarith

/-- The disk-to-half-plane Cayley inverse has derivative `2i` at the origin. -/
theorem hasDerivAt_suzukiUpperCayleyInv_zero :
    HasDerivAt
      GaloisForLFunctions.RHTower.suzukiUpperCayleyInv (2 * I) 0 := by
  have hadd : HasDerivAt (fun w : ℂ => 1 + w) 1 0 := by
    simpa using! (hasDerivAt_const 0 (1 : ℂ)).add (hasDerivAt_id 0)
  have hsub : HasDerivAt (fun w : ℂ => 1 - w) (-1) 0 := by
    simpa using! (hasDerivAt_const 0 (1 : ℂ)).sub (hasDerivAt_id 0)
  have h := (hadd.div hsub (by norm_num : (1 : ℂ) - 0 ≠ 0)).const_mul I
  convert! h using 1
  ring

/-- The exact Xi Livšic target is differentiable at its normalized anchor. -/
theorem differentiableAt_xiHedenmalmLivsicTarget_I :
    DifferentiableAt ℂ xiHedenmalmLivsicTarget I := by
  have hXi : XiC I ≠ 0 := by
    apply XiC_ne_zero_of_abs_re_le_nine_halves
    norm_num
  have hlog : DifferentiableAt ℂ (logDeriv XiC) I := by
    have h1 : DifferentiableAt ℂ (deriv XiC) I :=
      (XiC_analytic I (Set.mem_univ I)).deriv.differentiableAt
    have h2 : DifferentiableAt ℂ XiC I :=
      (XiC_analytic I (Set.mem_univ I)).differentiableAt
    simpa [logDeriv] using h1.div h2 hXi
  have hm : DifferentiableAt ℂ xiHedenmalmDonoghueTarget I := by
    change DifferentiableAt ℂ
      (fun z : ℂ => (-logDeriv XiC z) /
        (xiHedenmalmDonoghueScale : ℂ)) I
    exact hlog.neg.div_const _
  have hne : xiHedenmalmDonoghueTarget I + I ≠ 0 := by
    rw [xiHedenmalmDonoghueTarget_I]
    intro h
    have him := congrArg Complex.im h
    norm_num at him
  change DifferentiableAt ℂ
    (fun z => (xiHedenmalmDonoghueTarget z - I) /
      (xiHedenmalmDonoghueTarget z + I)) I
  exact (hm.sub_const I).div (hm.add_const I) hne

/-- The derivative at zero of the disk-conjugated Xi Livšic target is exactly its first real
defect scalar. -/
theorem deriv_xiHedenmalmLivsicTarget_disk_zero :
    deriv (xiHedenmalmLivsicTarget ∘
      GaloisForLFunctions.RHTower.suzukiUpperCayleyInv) 0 =
      (xiHedenmalmLivsicFirstDefectJet : ℂ) := by
  have hinv :
      GaloisForLFunctions.RHTower.suzukiUpperCayleyInv 0 = I := by
    simp [GaloisForLFunctions.RHTower.suzukiUpperCayleyInv]
  have hout : HasDerivAt xiHedenmalmLivsicTarget
      (deriv xiHedenmalmLivsicTarget I)
      (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv 0) := by
    simpa only [hinv] using differentiableAt_xiHedenmalmLivsicTarget_I.hasDerivAt
  have hcomp := hout.comp 0 hasDerivAt_suzukiUpperCayleyInv_zero
  rw [hcomp.deriv, xiHedenmalmLivsicFirstDefectJet_complex]
  ring

/-- **Exact Suzuki source convergence obligation.**  Locally uniform convergence of the
disk-conjugated finite Livšic carriers to the normalized Xi target forces the finite parity defect
angles themselves to converge to the strict Xi first-defect scalar. -/
theorem suzuki_defectAngle_tendsto_xiHedenmalmLivsicFirstDefectJet
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (F : ι → ℂ → ℂ) (evenEnergy oddEnergy : ι → ℝ)
    (hconv : TendstoLocallyUniformlyOn
      (fun j w =>
        GaloisForLFunctions.RHTower.suzukiLivsicQuotient
          (GaloisForLFunctions.RHTower.suzukiFourierNumerator (F j))
          (GaloisForLFunctions.RHTower.suzukiFourierDenominator (F j))
          (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w))
      (xiHedenmalmLivsicTarget ∘
        GaloisForLFunctions.RHTower.suzukiUpperCayleyInv)
      l (Metric.ball 0 1))
    (hhol : ∀ᶠ j in l, DifferentiableOn ℂ
      (fun w =>
        GaloisForLFunctions.RHTower.suzukiLivsicQuotient
          (GaloisForLFunctions.RHTower.suzukiFourierNumerator (F j))
          (GaloisForLFunctions.RHTower.suzukiFourierDenominator (F j))
          (GaloisForLFunctions.RHTower.suzukiUpperCayleyInv w))
      (Metric.ball 0 1))
    (hsource : ∀ᶠ j in l,
      DifferentiableAt ℂ (F j) I ∧ DifferentiableAt ℂ (F j) (-I) ∧
      evenEnergy j + oddEnergy j ≠ 0 ∧
      F j I = (((evenEnergy j - oddEnergy j) : ℝ) : ℂ) ∧
      F j (-I) = (((evenEnergy j + oddEnergy j) : ℝ) : ℂ)) :
    Tendsto (fun j =>
      (GaloisForLFunctions.RHTower.suzukiDefectAngle
        (evenEnergy j) (oddEnergy j) : ℂ)) l
      (nhds (xiHedenmalmLivsicFirstDefectJet : ℂ)) := by
  have hderiv := hconv.deriv hhol Metric.isOpen_ball
  have hpoint := hderiv.tendsto_at
    (Metric.mem_ball_self (by norm_num : (0 : ℝ) < 1))
  simp only [Function.comp_apply] at hpoint
  rw [deriv_xiHedenmalmLivsicTarget_disk_zero] at hpoint
  refine hpoint.congr' ?_
  filter_upwards [hsource] with j hj
  rcases hj with ⟨hFi, hFni, hsum, hFiValue, hFniValue⟩
  exact GaloisForLFunctions.RHTower.deriv_suzukiFourierLivsic_disk_zero_eq_defectAngle
    hFi hFni hsum hFiValue hFniValue

/-- The Xi first-defect jet leaves a strictly positive quantitative gap below the
ground-saturated value `1`. -/
theorem xiHedenmalmLivsicFirstDefectJet_groundLeakageFloor_pos :
    0 < (1 - xiHedenmalmLivsicFirstDefectJet) / 4 := by
  have hupper := xiHedenmalmLivsicFirstDefectJet_mem_Ioo.2
  linarith

/-- **Persistent source leakage forced by Xi identification.**  If real source defect angles,
viewed in the complex derivative topology, converge to the exact Xi first-defect jet and satisfy
the ground-edge inequality `1 - κ ≤ 2ρ`, then their leakage stays eventually above the fixed
positive Xi floor `(1 - κ_Xi)/4`. -/
theorem eventually_groundLeakage_gt_xiHedenmalmLivsicFirstDefectJet_floor
    {ι : Type*} {l : Filter ι} [l.NeBot]
    (angle leakage : ι → ℝ)
    (hangle : Tendsto (fun j => (angle j : ℂ)) l
      (nhds (xiHedenmalmLivsicFirstDefectJet : ℂ)))
    (hbound : ∀ᶠ j in l, 1 - angle j ≤ 2 * leakage j) :
    ∀ᶠ j in l,
      (1 - xiHedenmalmLivsicFirstDefectJet) / 4 < leakage j := by
  have hangleReal :
      Tendsto angle l (nhds xiHedenmalmLivsicFirstDefectJet) := by
    have hre := Complex.continuous_re.continuousAt.tendsto.comp hangle
    have hfun : (Complex.re ∘ fun j => (angle j : ℂ)) = angle := by
      funext j
      simp
    rw [hfun] at hre
    exact hre
  have hupper := xiHedenmalmLivsicFirstDefectJet_mem_Ioo.2
  have hmid :
      xiHedenmalmLivsicFirstDefectJet <
        (1 + xiHedenmalmLivsicFirstDefectJet) / 2 := by
    linarith
  have hangleUpper : ∀ᶠ j in l,
      angle j < (1 + xiHedenmalmLivsicFirstDefectJet) / 2 :=
    (tendsto_order.1 hangleReal).2 _ hmid
  filter_upwards [hangleUpper, hbound] with j hj hleak
  linarith

/-- The abstract leakage floor applied to Suzuki's exact ground-pole resolvent bounds.  Thus an
Xi-identifying ground-edge family cannot enter the vanishing-leakage regime that collapses to the
universal Cayley carrier. -/
theorem suzukiGroundLeakage_eventually_gt_xiHedenmalmLivsicFirstDefectJet_floor
    {ι : Type*} {l : Filter ι} [l.NeBot]
    {τ gap groundMass oddBudget evenEnergy oddEnergy : ι → ℝ}
    (hdata : ∀ᶠ j in l,
      0 < τ j ∧ 0 < gap j ∧ 0 < groundMass j ∧ 0 ≤ oddBudget j ∧
        0 ≤ oddEnergy j ∧ groundMass j / τ j ≤ evenEnergy j ∧
        oddEnergy j ≤ oddBudget j / gap j)
    (hangle : Tendsto (fun j =>
      (GaloisForLFunctions.RHTower.suzukiDefectAngle
        (evenEnergy j) (oddEnergy j) : ℂ)) l
      (nhds (xiHedenmalmLivsicFirstDefectJet : ℂ))) :
    ∀ᶠ j in l,
      (1 - xiHedenmalmLivsicFirstDefectJet) / 4 <
        GaloisForLFunctions.RHTower.suzukiGroundLeakage
          (τ j) (oddBudget j) (gap j) (groundMass j) := by
  have hbound : ∀ᶠ j in l,
      1 - GaloisForLFunctions.RHTower.suzukiDefectAngle
          (evenEnergy j) (oddEnergy j) ≤
        2 * GaloisForLFunctions.RHTower.suzukiGroundLeakage
          (τ j) (oddBudget j) (gap j) (groundMass j) := by
    filter_upwards [hdata] with j hj
    rcases hj with ⟨hτ, hgap, hground, hbudget, hodd, heven, hoddUpper⟩
    exact
      (GaloisForLFunctions.RHTower.suzukiDefectAngle_ground_leakage_bound
        hτ hgap hground hbudget hodd heven hoddUpper).2
  exact eventually_groundLeakage_gt_xiHedenmalmLivsicFirstDefectJet_floor
    (fun j => GaloisForLFunctions.RHTower.suzukiDefectAngle
      (evenEnergy j) (oddEnergy j))
    (fun j => GaloisForLFunctions.RHTower.suzukiGroundLeakage
      (τ j) (oddBudget j) (gap j) (groundMass j))
    hangle hbound

end

end RHTower
