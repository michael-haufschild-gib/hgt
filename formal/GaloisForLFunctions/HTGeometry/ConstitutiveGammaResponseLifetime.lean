import GaloisForLFunctions.RHTower.RouteRFixedTraceTailRoos
import Mathlib.Data.NNReal.Basic

namespace GaloisForLFunctions.HTGeometry

noncomputable section

universe u

variable {R V : Type u} [Semiring R] [AddCommMonoid V] [Module R V]

/-- Transport from the response kernel of a composite into the later response kernel. -/
def constitutiveKernelTransport (f g : V →ₗ[R] V) :
    LinearMap.ker (g.comp f) →ₗ[R] LinearMap.ker g where
  toFun x := ⟨f x, x.property⟩
  map_add' x y := by
    apply Subtype.ext
    exact f.map_add (x : V) (y : V)
  map_smul' c x := by
    apply Subtype.ext
    exact f.map_smul c (x : V)

theorem constitutiveKernelTransport_surjective
    (f g : V →ₗ[R] V) (hf : Function.Surjective f) :
    Function.Surjective (constitutiveKernelTransport f g) := by
  intro y
  obtain ⟨x, hx⟩ := hf y
  have hxker : x ∈ LinearMap.ker (g.comp f) := by
    change g (f x) = 0
    rw [hx]
    exact y.property
  refine ⟨⟨x, hxker⟩, ?_⟩
  apply Subtype.ext
  exact hx

theorem constitutiveKernelTransport_eq_zero_iff
    (f g : V →ₗ[R] V) (x : LinearMap.ker (g.comp f)) :
    constitutiveKernelTransport f g x = 0 ↔ (x : V) ∈ LinearMap.ker f := by
  rw [LinearMap.mem_ker]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact h

end

end GaloisForLFunctions.HTGeometry

namespace GaloisForLFunctions.HTGeometry

open _root_.RHTower

noncomputable section

/-- Fixed-corona quotient used by the Gamma response calibration. -/
abbrev ConstitutiveGammaCorona :=
  PrimeTraceSequence ⧸ primeFirstTraceSummableIdeal

/-- One-sided Gamma response on the fixed corona. -/
def constitutiveGammaCoronaResponse (s : NNReal) :
    ConstitutiveGammaCorona →ₗ[ℂ] ConstitutiveGammaCorona :=
  primeFirstTraceSummableIdeal.mapQ primeFirstTraceSummableIdeal
    (primeReflectedCharacterMultiplier (s : ℝ)) (by
      intro a ha
      exact primeReflectedCharacter_preservesFixedIdeal_of_nonneg s.property a ha)

theorem constitutiveGammaCoronaResponse_mk
    (s : NNReal) (a : PrimeTraceSequence) :
    constitutiveGammaCoronaResponse s (Submodule.Quotient.mk a) =
      Submodule.Quotient.mk (primeReflectedCharacterMultiplier (s : ℝ) a) := by
  rw [constitutiveGammaCoronaResponse, Submodule.mapQ_apply]

theorem constitutiveGammaCoronaResponse_surjective (s : NNReal) :
    Function.Surjective (constitutiveGammaCoronaResponse s) := by
  intro q
  obtain ⟨a, rfl⟩ := primeFirstTraceSummableIdeal.mkQ_surjective q
  refine ⟨Submodule.Quotient.mk (primeReflectedCharacterMultiplier (-(s : ℝ)) a), ?_⟩
  rw [constitutiveGammaCoronaResponse_mk]
  have h := DFunLike.congr_fun
    (primeReflectedCharacterMultiplier_involution (-(s : ℝ))) a
  change Submodule.Quotient.mk
      (primeReflectedCharacterMultiplier (s : ℝ)
        (primeReflectedCharacterMultiplier (-(s : ℝ)) a)) =
    Submodule.Quotient.mk a
  simpa only [neg_neg, LinearMap.comp_apply, LinearMap.id_apply] using
    congrArg (fun x : PrimeTraceSequence => Submodule.Quotient.mk x) h

theorem primeReflectedCharacterMultiplier_add (s t : ℝ) :
    (primeReflectedCharacterMultiplier s).comp
        (primeReflectedCharacterMultiplier t) =
      primeReflectedCharacterMultiplier (s + t) := by
  apply LinearMap.ext
  intro a
  funext p
  have hp : 0 < (p.1 : ℝ) := by exact_mod_cast p.2.pos
  simp only [LinearMap.comp_apply, primeReflectedCharacterMultiplier_apply]
  rw [← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add hp]
  congr 3
  ring

theorem constitutiveGammaCoronaResponse_add (s t : NNReal) :
    (constitutiveGammaCoronaResponse s).comp
        (constitutiveGammaCoronaResponse t) =
      constitutiveGammaCoronaResponse (s + t) := by
  apply LinearMap.ext
  intro q
  obtain ⟨a, rfl⟩ := primeFirstTraceSummableIdeal.mkQ_surjective q
  change constitutiveGammaCoronaResponse s
      (constitutiveGammaCoronaResponse t (Submodule.Quotient.mk a)) =
    constitutiveGammaCoronaResponse (s + t) (Submodule.Quotient.mk a)
  rw [constitutiveGammaCoronaResponse_mk,
    constitutiveGammaCoronaResponse_mk, constitutiveGammaCoronaResponse_mk]
  rw [← LinearMap.comp_apply, primeReflectedCharacterMultiplier_add]
  rfl

/-- Response-kernel filtration of the fixed-corona Gamma semigroup. -/
def constitutiveGammaResponseKernel (s : NNReal) : Submodule ℂ ConstitutiveGammaCorona :=
  LinearMap.ker (constitutiveGammaCoronaResponse s)

/-- Weighted source ideal whose Gamma-damped image is summable. -/
def constitutiveGammaWeightedIdeal (s : NNReal) : Submodule ℂ PrimeTraceSequence :=
  primeReflectedCharacterPullbackIdeal (s : ℝ)

/-- Weighted ideal modulo the fixed summable ideal, realized inside the fixed corona. -/
def constitutiveGammaWeightedKernel (s : NNReal) : Submodule ℂ ConstitutiveGammaCorona :=
  (constitutiveGammaWeightedIdeal s).map primeFirstTraceSummableIdeal.mkQ

/-- The response kernel is exactly the weighted source ideal modulo the fixed ideal. -/
theorem constitutiveGammaWeightedKernel_eq_responseKernel (s : NNReal) :
    constitutiveGammaWeightedKernel s = constitutiveGammaResponseKernel s := by
  apply le_antisymm
  · intro q hq
    rcases hq with ⟨a, ha, rfl⟩
    rw [constitutiveGammaResponseKernel, LinearMap.mem_ker]
    change constitutiveGammaCoronaResponse s (Submodule.Quotient.mk a) = 0
    rw [constitutiveGammaCoronaResponse_mk, Submodule.Quotient.mk_eq_zero]
    exact ha
  · intro q hq
    obtain ⟨a, rfl⟩ := primeFirstTraceSummableIdeal.mkQ_surjective q
    rw [constitutiveGammaResponseKernel, LinearMap.mem_ker] at hq
    change constitutiveGammaCoronaResponse s (Submodule.Quotient.mk a) = 0 at hq
    rw [constitutiveGammaCoronaResponse_mk, Submodule.Quotient.mk_eq_zero] at hq
    exact ⟨a, hq, rfl⟩

/-- Later Gamma time can erase every class erased at an earlier time. -/
theorem constitutiveGammaResponseKernel_mono :
    Monotone constitutiveGammaResponseKernel := by
  intro s t hst x hx
  rw [constitutiveGammaResponseKernel, LinearMap.mem_ker] at hx ⊢
  have hdecomp : t - s + s = t := tsub_add_cancel_of_le hst
  rw [← hdecomp, ← constitutiveGammaCoronaResponse_add,
    LinearMap.comp_apply, hx, map_zero]

/-- Exact transport from the response kernel at total time into the kernel at the first stage. -/
def constitutiveGammaKernelTransport (s t : NNReal) :
    constitutiveGammaResponseKernel (s + t) →ₗ[ℂ]
      constitutiveGammaResponseKernel s where
  toFun x := ⟨constitutiveGammaCoronaResponse t x, by
    rw [constitutiveGammaResponseKernel, LinearMap.mem_ker]
    rw [← LinearMap.comp_apply, constitutiveGammaCoronaResponse_add]
    exact x.property⟩
  map_add' x y := by
    apply Subtype.ext
    exact map_add _ (x : ConstitutiveGammaCorona) (y : ConstitutiveGammaCorona)
  map_smul' c x := by
    apply Subtype.ext
    exact map_smul _ c (x : ConstitutiveGammaCorona)

/-- Every earlier-kernel class lifts through the later response stage to total-kernel time. -/
theorem constitutiveGammaKernelTransport_surjective (s t : NNReal) :
    Function.Surjective (constitutiveGammaKernelTransport s t) := by
  intro y
  obtain ⟨x, hx⟩ := constitutiveGammaCoronaResponse_surjective t y
  have hxker : x ∈ constitutiveGammaResponseKernel (s + t) := by
    rw [constitutiveGammaResponseKernel, LinearMap.mem_ker]
    rw [← constitutiveGammaCoronaResponse_add, LinearMap.comp_apply, hx]
    exact y.property
  refine ⟨⟨x, hxker⟩, ?_⟩
  apply Subtype.ext
  exact hx

/-- Kernel of the total-to-earlier transport is exactly the later response kernel. -/
theorem constitutiveGammaKernelTransport_eq_zero_iff
    (s t : NNReal) (x : constitutiveGammaResponseKernel (s + t)) :
    constitutiveGammaKernelTransport s t x = 0 ↔
      (x : ConstitutiveGammaCorona) ∈ constitutiveGammaResponseKernel t := by
  change constitutiveGammaKernelTransport s t x = 0 ↔
    constitutiveGammaCoronaResponse t (x : ConstitutiveGammaCorona) = 0
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    apply Subtype.ext
    exact h

/-- Prime-indexed representative of the damped Gamma Bockstein. -/
def constitutiveGammaDampedBocksteinSequence (s t : ℝ) : PrimeTraceSequence :=
  fun p => (↑((p.1 : ℝ) ^ (-2 * s)) : ℂ) *
    (primeActivationOccupancyFisherComplexTwist (-t) p -
      primeActivationOccupancyFisherComplexTwist t p)

theorem constitutiveGammaCoronaResponse_bockstein
    (s : NNReal) (t : ℝ) :
    constitutiveGammaCoronaResponse s (primeGammaCofinalBockstein t) =
      Submodule.Quotient.mk
        (constitutiveGammaDampedBocksteinSequence (s : ℝ) t) := by
  rw [primeGammaCofinalBockstein, RHTower.primeFixedPhysicalFisherClass,
    RHTower.primeFixedPhysicalFisherClass, map_sub]
  rw [constitutiveGammaCoronaResponse_mk, constitutiveGammaCoronaResponse_mk]
  rw [← Submodule.Quotient.mk_sub]
  congr 1
  funext p
  simp [constitutiveGammaDampedBocksteinSequence,
    primeReflectedCharacterMultiplier_apply, mul_sub]

theorem norm_constitutiveGammaDampedBocksteinSequence
    (s t : ℝ) (p : Nat.Primes) :
    ‖constitutiveGammaDampedBocksteinSequence s t p‖ =
      primeGammaCofinalBocksteinDampedMass (2 * s) t p := by
  rw [constitutiveGammaDampedBocksteinSequence, norm_mul, Complex.norm_real]
  have hp0 : 0 ≤ (p.1 : ℝ) ^ (-2 * s) := by positivity
  rw [Real.norm_eq_abs, abs_of_nonneg hp0]
  simp only [primeActivationOccupancyFisherComplexTwist]
  rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  rw [primeGammaCofinalBocksteinDampedMass,
    primeGammaCofinalBocksteinMagnitude]
  congr 2
  ring

theorem constitutiveGammaDampedBocksteinSequence_summable_iff
    (s t : ℝ) :
    Summable (constitutiveGammaDampedBocksteinSequence s t) ↔
      t = 0 ∨ |t| < 2 * s := by
  rw [← summable_primeGammaCofinalBocksteinDampedMass_iff (2 * s) t]
  constructor
  · intro h
    exact (summable_norm_iff.mpr h).congr
      (fun p => norm_constitutiveGammaDampedBocksteinSequence s t p)
  · intro h
    apply summable_norm_iff.mp
    exact h.congr (fun p => (norm_constitutiveGammaDampedBocksteinSequence s t p).symm)

theorem constitutiveGammaBockstein_death_iff
    (s : NNReal) {t : ℝ} (ht : t ≠ 0) :
    constitutiveGammaCoronaResponse s (primeGammaCofinalBockstein t) = 0 ↔
      |t| / 2 < (s : ℝ) := by
  rw [constitutiveGammaCoronaResponse_bockstein,
    Submodule.Quotient.mk_eq_zero]
  change Summable (constitutiveGammaDampedBocksteinSequence (s : ℝ) t) ↔ _
  rw [constitutiveGammaDampedBocksteinSequence_summable_iff]
  constructor
  · rintro (hzero | hstrict)
    · exact False.elim (ht hzero)
    · linarith
  · intro h
    exact Or.inr (by linarith)

theorem constitutiveGammaBockstein_critical_survival
    {t : ℝ} (ht : t ≠ 0) :
    constitutiveGammaCoronaResponse ⟨|t| / 2, by positivity⟩
        (primeGammaCofinalBockstein t) ≠ 0 := by
  rw [ne_eq]
  intro hzero
  have hlt := (constitutiveGammaBockstein_death_iff _ ht).1 hzero
  exact (lt_irrefl (|t| / 2)) hlt

/-- Nonnegative response times at which the damped Bockstein representative enters the fixed
summable ideal. -/
def constitutiveGammaBocksteinDeathTimes (t : ℝ) : Set ℝ :=
  {s | 0 ≤ s ∧ Summable (constitutiveGammaDampedBocksteinSequence s t)}

/-- Constitutive lifetime is the lower boundary of the fixed-corona death set. -/
def constitutiveGammaBocksteinLifetime (t : ℝ) : ℝ :=
  sInf (constitutiveGammaBocksteinDeathTimes t)

theorem constitutiveGammaBocksteinDeathTimes_eq_Ioi
    {t : ℝ} (ht : t ≠ 0) :
    constitutiveGammaBocksteinDeathTimes t = Set.Ioi (|t| / 2) := by
  ext s
  simp only [constitutiveGammaBocksteinDeathTimes, Set.mem_setOf_eq, Set.mem_Ioi]
  rw [constitutiveGammaDampedBocksteinSequence_summable_iff]
  constructor
  · rintro ⟨_, hzero | hstrict⟩
    · exact False.elim (ht hzero)
    · linarith
  · intro h
    constructor
    · have habs : 0 ≤ |t| := abs_nonneg t
      linarith
    · exact Or.inr (by linarith)

/-- Exact response lifetime, including the nonattained critical boundary. -/
theorem constitutiveGammaBocksteinLifetime_eq (t : ℝ) :
    constitutiveGammaBocksteinLifetime t = |t| / 2 := by
  by_cases ht : t = 0
  · subst t
    have hdeath : constitutiveGammaBocksteinDeathTimes 0 = Set.Ici 0 := by
      ext s
      simp [constitutiveGammaBocksteinDeathTimes,
        constitutiveGammaDampedBocksteinSequence_summable_iff]
    rw [constitutiveGammaBocksteinLifetime, hdeath, csInf_Ici]
    norm_num
  · rw [constitutiveGammaBocksteinLifetime,
      constitutiveGammaBocksteinDeathTimes_eq_Ioi ht, csInf_Ioi]

/-- Centered divisor coordinate is read exactly as constitutive response lifetime. -/
theorem constitutiveGammaBocksteinLifetime_centered (x : ℝ) :
    constitutiveGammaBocksteinLifetime (2 * x - 1) = |x - 1 / 2| := by
  rw [constitutiveGammaBocksteinLifetime_eq]
  rw [show 2 * x - 1 = 2 * (x - 1 / 2) by ring, abs_mul]
  norm_num

end


end GaloisForLFunctions.HTGeometry
