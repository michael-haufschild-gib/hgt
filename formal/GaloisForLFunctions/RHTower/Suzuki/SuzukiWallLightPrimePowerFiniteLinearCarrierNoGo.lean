import GaloisForLFunctions.RHTower.Suzuki.SuzukiWallFieldLightConeKernelCompletion
import GaloisForLFunctions.RHTower.Suzuki.SuzukiCausalDepthGammaSchurCoherence
import GaloisForLFunctions.QuantumAlg.Util.Polynomial.Trigonometric

/-!
# Suzuki wall-light prime-power finite-linear-carrier no-go

The literal Suzuki positive- and negative-light amplitudes retain one distinct positive-frequency
character for every prime-power source.  Their reflected negative frequencies cannot collide with
those characters because all source frequencies are positive.  Dedekind independence therefore
makes every finite packet of distinct light amplitudes linearly independent.

Consequently neither complete light family can lie in the range of a linear decoder from any fixed
finite-dimensional complex carrier.  This obstruction uses no positivity, boundedness, continuity,
uniform coefficient bound, RH premise, or numerical computation.  Its positive survivor is exact:
the algebraic source dimension of either literal light family is infinite, with every finite packet
having dimension equal to its source count.

This kills the fixed finite-dimensional linear-source-carrier class for the Suzuki FE-reflected
wall Ward assembly.  It does not construct the remaining global Robin/Gamma/holonomy assembly.
-/

open Complex
open scoped BigOperators

namespace RHTower

noncomputable section

/-! ## Real-line character independence -/

/-- The real-frequency character of the additive real group, in multiplicative presentation. -/
def suzukiRealFrequencyCharacter (lam : ℝ) : Multiplicative ℝ →* ℂ where
  toFun x := Complex.exp (Complex.I * (((Multiplicative.toAdd x) * lam : ℝ) : ℂ))
  map_one' := by simp
  map_mul' := by
    intro x y
    have hto : Multiplicative.toAdd (x * y) =
        Multiplicative.toAdd x + Multiplicative.toAdd y := rfl
    rw [hto, ← Complex.exp_add]
    congr 1
    push_cast
    ring

@[simp] theorem suzukiRealFrequencyCharacter_apply (lam : ℝ) (x : Multiplicative ℝ) :
    suzukiRealFrequencyCharacter lam x =
      Complex.exp (Complex.I * (((Multiplicative.toAdd x) * lam : ℝ) : ℂ)) := rfl

/-- Distinct real frequencies induce distinct characters on the whole real line. -/
theorem suzukiRealFrequencyCharacter_injective :
    Function.Injective suzukiRealFrequencyCharacter := by
  intro a b h
  apply QuantumAlg.exp_I_real_inj
  intro t
  exact DFunLike.congr_fun h (Multiplicative.ofAdd t)

/-- Distinct real-frequency complex exponentials are linearly independent as functions of real
height. -/
theorem suzukiComplexExpRealFrequency_linearIndependent
    {ι : Type*} [Fintype ι] {lam : ι → ℝ} (hlam : Function.Injective lam) :
    LinearIndependent ℂ
      (fun k : ι => fun t : ℝ =>
        Complex.exp (Complex.I * (((t * lam k : ℝ)) : ℂ))) := by
  have hchars : LinearIndependent ℂ
      (fun k : ι => ⇑(suzukiRealFrequencyCharacter (lam k))) :=
    (linearIndependent_monoidHom (Multiplicative ℝ) ℂ).comp
      (fun k => suzukiRealFrequencyCharacter (lam k))
      (suzukiRealFrequencyCharacter_injective.comp hlam)
  rw [Fintype.linearIndependent_iff]
  intro c hc
  have hsum :
      (∑ k : ι, c k •
        (⇑(suzukiRealFrequencyCharacter (lam k)) : Multiplicative ℝ → ℂ)) = 0 := by
    funext x
    have hx := congrFun hc (Multiplicative.toAdd x)
    simpa only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul,
      suzukiRealFrequencyCharacter_apply, Pi.zero_apply] using hx
  exact Fintype.linearIndependent_iff.mp hchars c hsum

private def signedFrequency {ι : Type*} (lam : ι → ℝ) : Sum ι ι → ℝ :=
  Sum.elim lam (fun k => -lam k)

private theorem signedFrequency_injective
    {ι : Type*} {lam : ι → ℝ} (hlam : Function.Injective lam)
    (hpos : ∀ k, 0 < lam k) : Function.Injective (signedFrequency lam) := by
  intro i j hij
  cases i with
  | inl i =>
      cases j with
      | inl j =>
          apply congrArg Sum.inl
          exact hlam hij
      | inr j =>
          exfalso
          change lam i = -lam j at hij
          linarith [hpos i, hpos j]
  | inr i =>
      cases j with
      | inl j =>
          exfalso
          change -lam i = lam j at hij
          linarith [hpos i, hpos j]
      | inr j =>
          apply congrArg Sum.inr
          exact hlam (neg_injective hij)

private def twoSidedLightMode (eps : ℂ) (lam t : ℝ) : ℂ :=
  (Complex.exp (Complex.I * (((t * lam : ℝ)) : ℂ)) +
    eps * Complex.exp (Complex.I * (((t * (-lam) : ℝ)) : ℂ))) / 2

private theorem weighted_twoSidedLightMode_linearIndependent
    {ι : Type*} [Fintype ι] {lam : ι → ℝ} {weight : ι → ℂ}
    (hlam : Function.Injective lam) (hpos : ∀ k, 0 < lam k)
    (hweight : ∀ k, weight k ≠ 0) (eps : ℂ) :
    LinearIndependent ℂ
      (fun k : ι => fun t : ℝ => weight k * twoSidedLightMode eps (lam k) t) := by
  have hExp := suzukiComplexExpRealFrequency_linearIndependent
    (signedFrequency_injective hlam hpos)
  rw [Fintype.linearIndependent_iff]
  intro c hc
  let d : Sum ι ι → ℂ :=
    Sum.elim (fun k => c k * weight k / 2)
      (fun k => c k * weight k * eps / 2)
  have hd_sum :
      (∑ s : Sum ι ι,
        d s • (fun t : ℝ =>
          Complex.exp (Complex.I * (((t * signedFrequency lam s : ℝ)) : ℂ)))) = 0 := by
    funext t
    have hct := congrFun hc t
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hct ⊢
    simp only [Fintype.sum_sum_type, d, signedFrequency, Sum.elim_inl, Sum.elim_inr]
    rw [← Finset.sum_add_distrib, ← hct]
    apply Finset.sum_congr rfl
    intro k _
    simp only [twoSidedLightMode]
    ring
  have hd : d = 0 := by
    rw [Fintype.linearIndependent_iff] at hExp
    funext s
    exact hExp d hd_sum s
  intro k
  have hk := congrFun hd (Sum.inl k)
  change c k * weight k / 2 = 0 at hk
  have hmul : c k * weight k = 0 := by
    rcases div_eq_zero_iff.mp hk with h | h
    · exact h
    · norm_num at h
  exact (mul_eq_zero.mp hmul).resolve_right (hweight k)

/-! ## Literal Suzuki light-family independence -/

/-- Every prime-power bare wall amplitude is nonzero. -/
theorem suzukiCriticalEntryWallBareAmplitude_primePower_ne_zero
    (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalEntryWallBareAmplitude p e ≠ 0 := by
  have hsq := sq_suzukiCriticalEntryWallBareAmplitude_eq_vonMangoldt_div_sqrt p e
  have hpos := suzukiCriticalFarHingeWeight_pos p e
  intro hzero
  rw [hzero] at hsq
  norm_num at hsq
  linarith

private theorem suzukiCriticalWallPositiveLightAmplitude_eq_mode
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalWallPositiveLightAmplitude t p e =
      (suzukiCriticalEntryWallBareAmplitude p e : ℂ) *
        twoSidedLightMode Complex.I (suzukiCausalDepthGammaFrequency (p, e)) t := by
  rw [suzukiCriticalWallPositiveLightAmplitude,
    suzukiCriticalWallField_eq_bareAmplitude_mul_kernel,
    suzukiCriticalWallField_eq_bareAmplitude_mul_kernel]
  simp only [suzukiOscillatoryKernel, suzukiCausalDepthGammaFrequency,
    suzukiPrimePowerEntryWallAperture, twoSidedLightMode]
  push_cast
  ring_nf

private theorem suzukiCriticalWallNegativeLightAmplitude_eq_mode
    (t : ℝ) (p : Nat.Primes) (e : ℕ) :
    suzukiCriticalWallNegativeLightAmplitude t p e =
      (suzukiCriticalEntryWallBareAmplitude p e : ℂ) *
        twoSidedLightMode (-Complex.I) (suzukiCausalDepthGammaFrequency (p, e)) t := by
  rw [suzukiCriticalWallNegativeLightAmplitude,
    suzukiCriticalWallField_eq_bareAmplitude_mul_kernel,
    suzukiCriticalWallField_eq_bareAmplitude_mul_kernel]
  simp only [suzukiOscillatoryKernel, suzukiCausalDepthGammaFrequency,
    suzukiPrimePowerEntryWallAperture, twoSidedLightMode]
  push_cast
  ring_nf

/-- Every finite packet of distinct literal positive-light prime-power source amplitudes is
complex-linearly independent on the physical real-height line. -/
theorem suzukiCriticalWallPositiveLightAmplitude_linearIndependent
    {ι : Type*} [Fintype ι] (source : ι → Nat.Primes × ℕ)
    (hsource : Function.Injective source) :
    LinearIndependent ℂ
      (fun k : ι => fun t : ℝ =>
        suzukiCriticalWallPositiveLightAmplitude t (source k).1 (source k).2) := by
  have h := weighted_twoSidedLightMode_linearIndependent
    (suzukiCausalDepthGammaFrequency_injective.comp hsource)
    (fun k => suzukiCausalDepthGammaFrequency_pos (source k))
    (fun k => Complex.ofReal_ne_zero.mpr
      (suzukiCriticalEntryWallBareAmplitude_primePower_ne_zero
        (source k).1 (source k).2)) Complex.I
  convert h using 1
  ext k t
  simpa [Function.comp_apply] using
    (suzukiCriticalWallPositiveLightAmplitude_eq_mode
      t (source k).1 (source k).2)

/-- Every finite packet of distinct literal negative-light prime-power source amplitudes is
complex-linearly independent on the physical real-height line. -/
theorem suzukiCriticalWallNegativeLightAmplitude_linearIndependent
    {ι : Type*} [Fintype ι] (source : ι → Nat.Primes × ℕ)
    (hsource : Function.Injective source) :
    LinearIndependent ℂ
      (fun k : ι => fun t : ℝ =>
        suzukiCriticalWallNegativeLightAmplitude t (source k).1 (source k).2) := by
  have h := weighted_twoSidedLightMode_linearIndependent
    (suzukiCausalDepthGammaFrequency_injective.comp hsource)
    (fun k => suzukiCausalDepthGammaFrequency_pos (source k))
    (fun k => Complex.ofReal_ne_zero.mpr
      (suzukiCriticalEntryWallBareAmplitude_primePower_ne_zero
        (source k).1 (source k).2)) (-Complex.I)
  convert h using 1
  ext k t
  simpa [Function.comp_apply] using
    (suzukiCriticalWallNegativeLightAmplitude_eq_mode
      t (source k).1 (source k).2)

/-! ## Fixed finite-linear-carrier obstruction -/

private def depthPacket (n : ℕ) : Fin n → Nat.Primes × ℕ :=
  fun k => (⟨2, Nat.prime_two⟩, k.1)

private theorem depthPacket_injective (n : ℕ) : Function.Injective (depthPacket n) := by
  intro i j hij
  apply Fin.ext
  exact congrArg Prod.snd hij

/-- No finite-dimensional complex-linear decoder contains the complete positive-light source
family. -/
theorem suzukiCriticalWallPositiveLight_not_all_mem_range_finiteDimensional
    (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (decode : V →ₗ[ℂ] (ℝ → ℂ)) :
    ¬ ∀ pe : Nat.Primes × ℕ, ∃ v : V, decode v = fun t : ℝ =>
        suzukiCriticalWallPositiveLightAmplitude t pe.1 pe.2 := by
  intro hall
  let source := depthPacket (Module.finrank ℂ V + 1)
  choose v hv using fun k => hall (source k)
  have hamp := suzukiCriticalWallPositiveLightAmplitude_linearIndependent
    source (depthPacket_injective (Module.finrank ℂ V + 1))
  have hdecoded : LinearIndependent ℂ (⇑decode ∘ v) := by
    convert hamp using 1
    ext k t
    exact congrFun (hv k) t
  have hvli : LinearIndependent ℂ v := LinearIndependent.of_comp decode hdecoded
  have hle := hvli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hle
  omega

/-- No finite-dimensional complex-linear decoder contains the complete negative-light source
family. -/
theorem suzukiCriticalWallNegativeLight_not_all_mem_range_finiteDimensional
    (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (decode : V →ₗ[ℂ] (ℝ → ℂ)) :
    ¬ ∀ pe : Nat.Primes × ℕ, ∃ v : V, decode v = fun t : ℝ =>
        suzukiCriticalWallNegativeLightAmplitude t pe.1 pe.2 := by
  intro hall
  let source := depthPacket (Module.finrank ℂ V + 1)
  choose v hv using fun k => hall (source k)
  have hamp := suzukiCriticalWallNegativeLightAmplitude_linearIndependent
    source (depthPacket_injective (Module.finrank ℂ V + 1))
  have hdecoded : LinearIndependent ℂ (⇑decode ∘ v) := by
    convert hamp using 1
    ext k t
    exact congrFun (hv k) t
  have hvli : LinearIndependent ℂ v := LinearIndependent.of_comp decode hdecoded
  have hle := hvli.fintype_card_le_finrank
  simp only [Fintype.card_fin] at hle
  omega

/-- **Fixed finite-linear-carrier route kill.**  Every fixed finite-dimensional complex carrier and
linear decoder misses at least one literal source from each Suzuki light family. -/
theorem suzukiCriticalWallLightFixedFiniteLinearCarrierRouteKilled
    (V : Type*) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (decode : V →ₗ[ℂ] (ℝ → ℂ)) :
    (¬ ∀ pe : Nat.Primes × ℕ, ∃ v : V, decode v = fun t : ℝ =>
        suzukiCriticalWallPositiveLightAmplitude t pe.1 pe.2) ∧
      (¬ ∀ pe : Nat.Primes × ℕ, ∃ v : V, decode v = fun t : ℝ =>
        suzukiCriticalWallNegativeLightAmplitude t pe.1 pe.2) := by
  exact ⟨suzukiCriticalWallPositiveLight_not_all_mem_range_finiteDimensional V decode,
    suzukiCriticalWallNegativeLight_not_all_mem_range_finiteDimensional V decode⟩

end

end RHTower
