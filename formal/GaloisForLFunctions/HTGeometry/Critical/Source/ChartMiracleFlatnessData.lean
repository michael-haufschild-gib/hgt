import GaloisForLFunctions.HTGeometry.Critical.Chart.TowerFinite
import GaloisForLFunctions.HTGeometry.Critical.Source.ChartFinite
import GaloisForLFunctions.HTGeometry.IntegralExtensionKrullDim
import GaloisForLFunctions.HTGeometry.IntegralRegularLocalFree
import GaloisForLFunctions.HTGeometry.LocalizationLiftInjective
import GaloisForLFunctions.HTGeometry.RegularRingLocalization
import Mathlib.RingTheory.IntegralClosure.GoingDown
import Mathlib.RingTheory.Localization.Module

/-!
# Local miracle-flatness data for the critical source chart

At every prime of the observation chart, localize the critical source chart at
the image of the prime complement.  The resulting algebra is finite and
regular over the regular local observation ring, its structure map is
injective, and the two rings have equal Krull dimension.  These are the exact
commutative-algebra inputs needed by miracle flatness.
-/

namespace GaloisForLFunctions.HTGeometry

noncomputable section

set_option synthInstance.maxHeartbeats 1000000

variable (K : Type*) [Field K] [CharZero K] [IsAlgClosed K]
variable {m n : ℕ} [Fact (0 < m)] [Fact (0 < n)]

/-- Critical source chart localized above a prime of the observation chart. -/
abbrev criticalSourceChartAtObservationPrime
    (p : Ideal (criticalObservationChartRing K m n)) [p.IsPrime] :=
  Localization
    (Algebra.algebraMapSubmonoid (criticalSourceChartRing K m n) p.primeCompl)

/-- The observation-to-source chart map is injective. -/
theorem criticalObservationChartToSourceChart_algebraMap_injective :
    Function.Injective
      (algebraMap (criticalObservationChartRing K m n)
        (criticalSourceChartRing K m n)) := by
  intro x y hxy
  apply algebraMap_chartRing_injective K
  rw [IsScalarTower.algebraMap_apply
    (criticalObservationChartRing K m n)
    (criticalSourceChartRing K m n) (criticalSourceField K m n),
    IsScalarTower.algebraMap_apply
    (criticalObservationChartRing K m n)
    (criticalSourceChartRing K m n) (criticalSourceField K m n)]
  exact congrArg
    (algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n)) hxy

/-- The critical source chart is a domain, via its injective map to the critical source field. -/
noncomputable instance criticalSourceChartRing_isDomain :
    IsDomain (criticalSourceChartRing K m n) :=
  Function.Injective.isDomain
    (algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n))
    (algebraMap_criticalSourceChartRing_injective K m n)

/-- The observation chart acts faithfully on the source chart. -/
noncomputable instance criticalObservationChartToSourceChart_faithfulSMul :
    FaithfulSMul (criticalObservationChartRing K m n)
      (criticalSourceChartRing K m n) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  exact criticalObservationChartToSourceChart_algebraMap_injective K

variable (p : Ideal (criticalObservationChartRing K m n)) [p.IsPrime]

/-- The localized observation chart is regular local. -/
theorem criticalObservationChart_atPrime_isRegularLocalRing :
    IsRegularLocalRing (Localization.AtPrime p) := by
  infer_instance

/-- The critical source chart remains regular after localization above `p`. -/
theorem criticalSourceChartAtObservationPrime_isRegularRing :
    IsRegularRing (criticalSourceChartAtObservationPrime K p) := by
  infer_instance

/-- Every source chart localized above an observation prime is a domain. -/
noncomputable instance criticalSourceChartAtObservationPrime_isDomain :
    IsDomain (criticalSourceChartAtObservationPrime K p) := by
  have hM : (0 : criticalSourceChartRing K m n) ∉
      Algebra.algebraMapSubmonoid (criticalSourceChartRing K m n) p.primeCompl := by
    intro hzero
    change 0 ∈ Submonoid.map
      (algebraMap (criticalObservationChartRing K m n)
        (criticalSourceChartRing K m n)) p.primeCompl at hzero
    rw [Submonoid.mem_map] at hzero
    obtain ⟨r, hr, hr0⟩ := hzero
    have : r = 0 :=
      (criticalObservationChartToSourceChart_algebraMap_injective K) (by simpa using hr0)
    exact hr (by simpa [this] using p.zero_mem)
  let g := algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n)
  let hunit : ∀ s : Algebra.algebraMapSubmonoid
      (criticalSourceChartRing K m n) p.primeCompl, IsUnit (g s) :=
    fun s => isUnit_iff_ne_zero.mpr (fun hs =>
      hM (by
        have hs0 : (s : criticalSourceChartRing K m n) = 0 :=
          (algebraMap_criticalSourceChartRing_injective K m n) (by
            change g (s : criticalSourceChartRing K m n) = g 0
            simpa using hs)
        exact hs0 ▸ s.2))
  let toField : criticalSourceChartAtObservationPrime K p →+*
      criticalSourceField K m n :=
    IsLocalization.lift hunit
  exact Function.Injective.isDomain toField
    (injective_localizationLift_of_injective g
      (algebraMap_criticalSourceChartRing_injective K m n) hM)

/-- Source localization above `p` is finite over the local observation chart. -/
theorem criticalSourceChartAtObservationPrime_moduleFinite :
    Module.Finite (Localization.AtPrime p)
      (criticalSourceChartAtObservationPrime K p) := by
  infer_instance

/-- The local observation-to-source structure map is injective. -/
theorem criticalSourceChartAtObservationPrime_algebraMap_injective :
    Function.Injective
      (algebraMap (Localization.AtPrime p)
        (criticalSourceChartAtObservationPrime K p)) := by
  have hRS : Function.Injective
      (algebraMap (criticalObservationChartRing K m n)
        (criticalSourceChartRing K m n)) := by
    intro x y hxy
    apply algebraMap_chartRing_injective K
    calc
      algebraMap (criticalObservationChartRing K m n) (criticalSourceField K m n) x =
          algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n)
            (algebraMap (criticalObservationChartRing K m n)
              (criticalSourceChartRing K m n) x) :=
        IsScalarTower.algebraMap_apply
          (criticalObservationChartRing K m n) (criticalSourceChartRing K m n)
          (criticalSourceField K m n) x
      _ = algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n)
            (algebraMap (criticalObservationChartRing K m n)
              (criticalSourceChartRing K m n) y) :=
        congrArg
          (algebraMap (criticalSourceChartRing K m n) (criticalSourceField K m n)) hxy
      _ = algebraMap (criticalObservationChartRing K m n)
          (criticalSourceField K m n) y :=
        (IsScalarTower.algebraMap_apply
          (criticalObservationChartRing K m n) (criticalSourceChartRing K m n)
          (criticalSourceField K m n) y).symm
  letI : Nontrivial (criticalSourceChartRing K m n) :=
    ⟨⟨(0 : criticalSourceChartRing K m n), 1, fun h =>
      (zero_ne_one : (0 : criticalSourceField K m n) ≠ 1) (by
        simpa using congrArg (algebraMap (criticalSourceChartRing K m n)
          (criticalSourceField K m n)) h)⟩⟩
  have hST : Function.Injective
      (algebraMap (criticalSourceChartRing K m n)
        (criticalSourceChartAtObservationPrime K p)) := by
    apply IsLocalization.injective
      (M := Algebra.algebraMapSubmonoid
        (criticalSourceChartRing K m n) p.primeCompl)
      (criticalSourceChartAtObservationPrime K p)
    intro t ht
    rw [mem_nonZeroDivisors_iff_ne_zero]
    change t ∈ Submonoid.map
      (algebraMap (criticalObservationChartRing K m n)
        (criticalSourceChartRing K m n)) p.primeCompl at ht
    rw [Submonoid.mem_map] at ht
    rcases ht with ⟨r, hr, rfl⟩
    intro hzero
    have hrzero : r = 0 := by apply hRS; simpa using hzero
    exact hr (by simp [hrzero])
  have hzero : ∀ z : Localization.AtPrime p,
      algebraMap (Localization.AtPrime p)
        (criticalSourceChartAtObservationPrime K p) z = 0 → z = 0 := by
    intro z hz
    let a := (IsLocalization.sec p.primeCompl z).1
    let s := (IsLocalization.sec p.primeCompl z).2
    have hsec : z * algebraMap (criticalObservationChartRing K m n)
        (Localization.AtPrime p) s =
        algebraMap (criticalObservationChartRing K m n) (Localization.AtPrime p) a :=
      IsLocalization.sec_spec p.primeCompl z
    have htarget : algebraMap (criticalObservationChartRing K m n)
        (criticalSourceChartAtObservationPrime K p) a = 0 := by
      rw [IsScalarTower.algebraMap_apply
        (criticalObservationChartRing K m n) (Localization.AtPrime p)]
      rw [← hsec, map_mul, hz, zero_mul]
    have hsource : algebraMap (criticalObservationChartRing K m n)
        (criticalSourceChartRing K m n) a = 0 := by
      apply hST
      rw [map_zero]
      rw [← IsScalarTower.algebraMap_apply
        (criticalObservationChartRing K m n) (criticalSourceChartRing K m n)]
      simpa using htarget
    have ha : a = 0 := by apply hRS; simpa using hsource
    calc
      z = IsLocalization.mk' (Localization.AtPrime p) a s :=
        (IsLocalization.mk'_sec (Localization.AtPrime p) z).symm
      _ = 0 := by rw [ha]; exact IsLocalization.mk'_zero s
  intro x y hxy
  apply sub_eq_zero.mp
  apply hzero (x - y)
  rw [map_sub, hxy, sub_self]

/-- The local observation ring acts faithfully on the source localization above it. -/
noncomputable instance criticalSourceChartAtObservationPrime_faithfulSMul :
    FaithfulSMul (Localization.AtPrime p)
      (criticalSourceChartAtObservationPrime K p) := by
  rw [faithfulSMul_iff_algebraMap_injective]
  exact criticalSourceChartAtObservationPrime_algebraMap_injective K p

/-- Integral injectivity gives equal Krull dimensions after localization. -/
theorem ringKrullDim_criticalSourceChartAtObservationPrime :
    ringKrullDim (Localization.AtPrime p) =
      ringKrullDim (criticalSourceChartAtObservationPrime K p) := by
  apply ringKrullDim_eq_of_isIntegral
  exact (RingHom.ker_eq_bot_iff_eq_zero
    (algebraMap (Localization.AtPrime p)
      (criticalSourceChartAtObservationPrime K p))).mpr
        (fun x hx => by
          apply criticalSourceChartAtObservationPrime_algebraMap_injective K p
          simpa using hx)

/-- **Local miracle freeness for the critical source chart.** -/
theorem criticalSourceChartAtObservationPrime_free :
    Module.Free (Localization.AtPrime p)
      (criticalSourceChartAtObservationPrime K p) := by
  apply free_of_finite_integral_regular_of_goingDown

/-- **The critical source chart is flat over the observation chart.** -/
noncomputable instance criticalSourceChartRing_flat :
    Module.Flat (criticalObservationChartRing K m n)
      (criticalSourceChartRing K m n) := by
  apply Module.flat_of_isLocalized_maximal
    (criticalObservationChartRing K m n)
    (criticalSourceChartRing K m n)
    (fun p _ => criticalSourceChartAtObservationPrime K p)
    (fun p _ =>
      (IsScalarTower.toAlgHom
        (criticalObservationChartRing K m n)
        (criticalSourceChartRing K m n)
        (criticalSourceChartAtObservationPrime K p)).toLinearMap)
  intro p hp
  apply (Module.flat_iff_of_isLocalization
    (Localization.AtPrime p) p.primeCompl
    (criticalSourceChartAtObservationPrime K p)).mp
  letI : Module.Free (Localization.AtPrime p)
      (criticalSourceChartAtObservationPrime K p) :=
    criticalSourceChartAtObservationPrime_free K p
  infer_instance

end

end GaloisForLFunctions.HTGeometry
