import GaloisForLFunctions.HTGeometry.FiniteAffineCyclicMomentSymmetryUniversalityLaw
import GaloisForLFunctions.RHTower.SeamOfflineReflection
import GaloisForLFunctions.RHTower.CarrierBoxCount

/-!
# Equivariant analytic order and finite cyclic spectra

The invariant local multiplier law and the invariant vector-valued deck-character law are the
trivial-character faces of one statement: if an analytic germ transforms through a scalar
character under an arbitrary analytic self-map fixing its base point, then that character is the
self-map multiplier raised to the germ's vanishing order.

For a finite cyclic spectrum, its centered characteristic product transforms through the character
`ζ ^ n`. Consequently the multiplicity at the rotation center is congruent to the total spectrum
size modulo the rotation order. Combining this with finite moment Torelli makes moment vanishing,
cyclic symmetry, polynomial covariance, and the order congruence one finite law.
-/

open scoped BigOperators
open Complex Filter Topology Finset

namespace RHTower

/-- **Equivariant analytic-order character law.** If a vector-valued analytic germ transforms by
the character `χ` under an analytic self-map fixing `c`, then `χ` equals the self-map multiplier
raised to the germ's vanishing order. The invariant multiplier and deck-character laws are the
special case `χ = 1`. -/
theorem multiplier_pow_analyticOrderAt_eq_character
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : ℂ → E} {τ : ℂ → ℂ} {c χ : ℂ}
    (hF : AnalyticOnNhd ℂ F Set.univ) (hτ : AnalyticAt ℂ τ c) (hfix : τ c = c)
    (hequiv : ∀ᶠ s in 𝓝 c, F (τ s) = χ • F s) (hne : analyticOrderAt F c ≠ ⊤) :
    (deriv τ c) ^ (analyticOrderAt F c).toNat = χ := by
  set m : ℕ := (analyticOrderAt F c).toNat with hm_def
  have hcoe : analyticOrderAt F c = (m : ℕ∞) := (ENat.coe_toNat hne).symm
  have hFc : AnalyticAt ℂ F c := hF c (Set.mem_univ c)
  obtain ⟨H, hHan, hH0, hfactor⟩ :=
    (hFc.analyticOrderAt_eq_natCast).mp hcoe
  set lam : ℂ := deriv τ c with hlam
  have hderiv : HasDerivAt τ lam c := hτ.differentiableAt.hasDerivAt
  have hslope : Tendsto (slope τ c) (𝓝[≠] c) (𝓝 lam) :=
    hasDerivAt_iff_tendsto_slope.mp hderiv
  have htauN : Tendsto τ (𝓝 c) (𝓝 c) := by
    have h0 := hτ.continuousAt.tendsto
    rw [hfix] at h0
    exact h0
  have hfactorSelf : ∀ᶠ s in 𝓝[≠] c, F s = (s - c) ^ m • H s :=
    hfactor.filter_mono nhdsWithin_le_nhds
  have hfactorMap : ∀ᶠ s in 𝓝[≠] c,
      F (τ s) = (τ s - c) ^ m • H (τ s) :=
    (htauN.mono_left nhdsWithin_le_nhds).eventually hfactor
  have key : ∀ᶠ s in 𝓝[≠] c,
      (slope τ c s) ^ m • H (τ s) = χ • H s := by
    have hequiv' : ∀ᶠ s in 𝓝[≠] c, F (τ s) = χ • F s :=
      hequiv.filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hequiv', hfactorSelf, hfactorMap]
      with s hs heqs e1 e2
    have hsc : s - c ≠ 0 := sub_ne_zero.mpr hs
    have hsl : slope τ c s * (s - c) = τ s - c := by
      rw [slope_def_field, hfix, div_mul_cancel₀ _ hsc]
    have hpow : (s - c) ^ m ≠ 0 := pow_ne_zero m hsc
    have heq : (s - c) ^ m • ((slope τ c s) ^ m • H (τ s)) =
        (s - c) ^ m • (χ • H s) := by
      calc
        (s - c) ^ m • ((slope τ c s) ^ m • H (τ s)) =
            (slope τ c s * (s - c)) ^ m • H (τ s) := by
              rw [mul_pow, smul_smul]
              congr 1
              ring
        _ = (τ s - c) ^ m • H (τ s) := by rw [hsl]
        _ = F (τ s) := e2.symm
        _ = χ • F s := heqs
        _ = (χ * (s - c) ^ m) • H s := by rw [e1, smul_smul]
        _ = ((s - c) ^ m * χ) • H s := by rw [mul_comm]
        _ = (s - c) ^ m • (χ • H s) := by rw [smul_smul]
    have hcancel := congrArg (fun v : E => ((s - c) ^ m)⁻¹ • v) heq
    simpa [smul_smul, hpow] using hcancel
  have htau : Tendsto τ (𝓝[≠] c) (𝓝 c) :=
    htauN.mono_left nhdsWithin_le_nhds
  have hHlim : Tendsto H (𝓝[≠] c) (𝓝 (H c)) :=
    hHan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hHmap : Tendsto (fun s => H (τ s)) (𝓝[≠] c) (𝓝 (H c)) :=
    hHan.continuousAt.tendsto.comp htau
  have hlhs : Tendsto (fun s => (slope τ c s) ^ m • H (τ s))
      (𝓝[≠] c) (𝓝 (lam ^ m • H c)) := (hslope.pow m).smul hHmap
  have hrhs : Tendsto (fun s => χ • H s) (𝓝[≠] c) (𝓝 (χ • H c)) :=
    tendsto_const_nhds.smul hHlim
  have hlim : lam ^ m • H c = χ • H c :=
    tendsto_nhds_unique (hlhs.congr' key) hrhs
  have hzero : (lam ^ m - χ) • H c = 0 := by
    rw [sub_smul, hlim, sub_self]
  rcases smul_eq_zero.mp hzero with hscalar | hvector
  · exact sub_eq_zero.mp hscalar
  · exact (hH0 hvector).elim

end RHTower

namespace GaloisForLFunctions

noncomputable section

/-- The characteristic product in coordinates centered at `c`. -/
def finiteCenteredSpectralProduct {n : ℕ} (f : Fin n → ℂ) (c z : ℂ) : ℂ :=
  ∏ i, (z - (f i - c))

/-- The analytic order of the centered characteristic product is exactly the multiplicity of the
rotation center in the finite spectrum. -/
theorem finiteCenteredSpectralProduct_analyticOrderAt_zero
    {n : ℕ} (f : Fin n → ℂ) (c : ℂ) :
    analyticOrderAt (finiteCenteredSpectralProduct f c) 0 =
      ((Finset.univ.filter fun i => f i = c).card : ℕ∞) := by
  have hfun : finiteCenteredSpectralProduct f c =
      ∏ i : Fin n, (fun z : ℂ => z - (f i - c)) := by
    funext z
    simp [finiteCenteredSpectralProduct]
  rw [hfun, RHTower.analyticOrderAt_finset_prod]
  · calc
      ∑ i : Fin n, analyticOrderAt (fun z : ℂ => z - (f i - c)) 0 =
          ∑ i : Fin n, if f i = c then (1 : ℕ∞) else 0 := by
            apply Finset.sum_congr rfl
            intro i hi
            by_cases hic : f i = c
            · simp only [hic, sub_self, if_pos]
              exact (analyticAt_id.sub analyticAt_const).analyticOrderAt_eq_one_of_zero_deriv_ne_zero
                (by simp) (by simp)
            · rw [if_neg hic, analyticOrderAt_eq_zero.mpr]
              exact Or.inr (sub_ne_zero.mpr (fun hci => hic (sub_eq_zero.mp hci.symm)))
      _ = ((Finset.univ.filter fun i => f i = c).card : ℕ∞) := by simp
  · intro i hi
    exact analyticAt_id.sub analyticAt_const

/-- Cyclic invariance of a finite spectrum makes its centered characteristic product transform
through the degree character `ζ ^ n`. -/
theorem finiteCenteredSpectralProduct_cyclic_covariant
    {n : ℕ} (f : Fin n → ℂ) (c ζ : ℂ)
    (hfixed : (Finset.univ.val.map f).map (fun z => c + ζ * (z - c)) =
      Finset.univ.val.map f) (z : ℂ) :
    finiteCenteredSpectralProduct f c (ζ * z) =
      ζ ^ n * finiteCenteredSpectralProduct f c z := by
  let A : Multiset ℂ := Finset.univ.val.map (fun i => f i - c)
  have hA : A.map (fun a => ζ * a) = A := by
    have hm := congrArg (Multiset.map (fun w : ℂ => w - c)) hfixed
    simp only [Multiset.map_map, Function.comp_apply] at hm
    dsimp [A]
    simp only [Multiset.map_map, Function.comp_apply]
    convert hm using 1
    apply Multiset.map_congr rfl
    intro i hi
    ring
  have hp := congrArg
    (fun B : Multiset ℂ => (B.map (fun a => ζ * z - a)).prod) hA
  have hp' : (∏ i, (ζ * z - (f i - c))) =
      ∏ i, ζ * (z - (f i - c)) := by
    dsimp [A] at hp
    simpa only [Multiset.map_map, Function.comp_apply, mul_sub] using hp.symm
  unfold finiteCenteredSpectralProduct
  rw [hp', Finset.prod_mul_distrib]
  simp

/-- Primitive cyclic invariance forces the center multiplicity to equal the total spectrum size
modulo the cyclic order. -/
theorem finiteCenteredSpectrum_centerMultiplicity_modEq_card
    {n d : ℕ} (f : Fin n → ℂ) (c : ℂ) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d)
    (hd : d ≠ 0)
    (hfixed : (Finset.univ.val.map f).map (fun z => c + ζ * (z - c)) =
      Finset.univ.val.map f) :
    Nat.ModEq d (Finset.univ.filter fun i => f i = c).card n := by
  have hcov : ∀ z : ℂ, finiteCenteredSpectralProduct f c (ζ * z) =
      ζ ^ n * finiteCenteredSpectralProduct f c z :=
    fun z => finiteCenteredSpectralProduct_cyclic_covariant f c ζ hfixed z
  have hfinite : analyticOrderAt (finiteCenteredSpectralProduct f c) 0 ≠ ⊤ := by
    rw [finiteCenteredSpectralProduct_analyticOrderAt_zero]
    simp
  have hchar := RHTower.multiplier_pow_analyticOrderAt_eq_character
    (F := finiteCenteredSpectralProduct f c) (τ := fun z : ℂ => ζ * z)
    (c := 0) (χ := ζ ^ n)
    (fun z hz => by
      unfold finiteCenteredSpectralProduct
      fun_prop)
    (analyticAt_const.mul analyticAt_id) (by simp)
    (by filter_upwards with z using by simpa only [smul_eq_mul] using hcov z) hfinite
  rw [deriv_const_mul_id] at hchar
  rw [finiteCenteredSpectralProduct_analyticOrderAt_zero] at hchar
  have hpow : ζ ^ (Finset.univ.filter fun i => f i = c).card = ζ ^ n := by
    simpa using hchar
  have hpow_mod : ∀ a : ℕ, ζ ^ (a % d) = ζ ^ a := by
    intro a
    nth_rewrite 2 [← Nat.mod_add_div a d]
    rw [pow_add, pow_mul, hζ.pow_eq_one, one_pow, mul_one]
  rw [Nat.ModEq]
  apply hζ.pow_inj (Nat.mod_lt _ (Nat.pos_of_ne_zero hd))
    (Nat.mod_lt _ (Nat.pos_of_ne_zero hd))
  exact (hpow_mod _).trans (hpow.trans (hpow_mod _).symm)

/-- **Finite cyclic moment--character--order universality.** Vanishing of the first sharp block of
nontrivial-character centered moments is equivalent to cyclic multiset symmetry together with the
induced characteristic-product character and the resulting center-multiplicity congruence. -/
theorem finiteAffineCyclicMomentCharacterOrderUniversalityLaw
    {n d : ℕ} (f : Fin n → ℂ) (c : ℂ) {ζ : ℂ} (hζ : IsPrimitiveRoot ζ d)
    (hd : d ≠ 0) :
    (∀ k, k ≤ n → ¬ d ∣ k → ∑ i, (f i - c) ^ k = 0) ↔
      (Finset.univ.val.map f).map (fun z => c + ζ * (z - c)) =
          Finset.univ.val.map f ∧
        (∀ z, finiteCenteredSpectralProduct f c (ζ * z) =
          ζ ^ n * finiteCenteredSpectralProduct f c z) ∧
        Nat.ModEq d (Finset.univ.filter fun i => f i = c).card n := by
  rw [← finiteAffineCyclicSpectrum_fixed_iff_firstCenteredCharacterMoments_vanish f c hζ]
  constructor
  · intro hfixed
    exact ⟨hfixed,
      fun z => finiteCenteredSpectralProduct_cyclic_covariant f c ζ hfixed z,
      finiteCenteredSpectrum_centerMultiplicity_modEq_card f c hζ hd hfixed⟩
  · exact fun h => h.1

end

end GaloisForLFunctions
