import GaloisForLFunctions.HTGeometry.LogarithmicResidueQuantization
import GaloisForLFunctions.RHTower.SeamOfflineReflection

/-!
# Meromorphic equivariant residue-character universality

For a vector-valued meromorphic germ, arbitrary analytic self-map equivariance identifies its
scalar character with the nonzero self-map multiplier raised to the signed Laurent order. In the
scalar case, the same integer is independently recovered as the logarithmic-derivative residue.

This is the signed-order extension of the analytic equivariant character law: zeros give positive
charges, nonvanishing germs give charge zero, and poles give negative charges.
-/

open Complex Filter Topology

namespace GaloisForLFunctions.HTGeometry

/-- **Meromorphic equivariant character law.** If a vector-valued meromorphic germ of signed order
`n` transforms through character `χ` under an analytic self-map fixing its base point, and the
self-map multiplier is nonzero, then that multiplier to the Laurent charge is `χ`. -/
theorem multiplier_zpow_meromorphicOrder_eq_character
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    {F : ℂ → E} {τ : ℂ → ℂ} {c χ : ℂ} {n : ℤ}
    (hF : MeromorphicAt F c) (hτ : AnalyticAt ℂ τ c) (hfix : τ c = c)
    (hderiv : deriv τ c ≠ 0)
    (hequiv : ∀ᶠ s in 𝓝 c, F (τ s) = χ • F s)
    (horder : meromorphicOrderAt F c = n) :
    (deriv τ c) ^ n = χ := by
  obtain ⟨G, hGan, hG0, hfactor⟩ :=
    (meromorphicOrderAt_eq_int_iff hF).mp horder
  set lam : ℂ := deriv τ c with hlam
  have hlam0 : lam ≠ 0 := by simpa only [hlam] using hderiv
  have hτderiv : HasDerivAt τ lam c := hτ.differentiableAt.hasDerivAt
  have hslope : Tendsto (slope τ c) (𝓝[≠] c) (𝓝 lam) :=
    hasDerivAt_iff_tendsto_slope.mp hτderiv
  have hslope0 : ∀ᶠ s in 𝓝[≠] c, slope τ c s ≠ 0 :=
    hslope.eventually (eventually_ne_nhds hlam0)
  have htauN : Tendsto τ (𝓝 c) (𝓝 c) := by
    have h0 := hτ.continuousAt.tendsto
    rw [hfix] at h0
    exact h0
  have htau0 : ∀ᶠ s in 𝓝[≠] c, τ s ≠ c := by
    filter_upwards [self_mem_nhdsWithin, hslope0] with s hs hsl0
    have hsc : s - c ≠ 0 := sub_ne_zero.mpr hs
    have hsl : slope τ c s * (s - c) = τ s - c := by
      rw [slope_def_field, hfix, div_mul_cancel₀ _ hsc]
    exact sub_ne_zero.mp (hsl ▸ mul_ne_zero hsl0 hsc)
  have htauWithin : Tendsto τ (𝓝[≠] c) (𝓝[≠] c) := by
    rw [tendsto_nhdsWithin_iff]
    exact ⟨htauN.mono_left nhdsWithin_le_nhds,
      htau0.mono (fun s hs => by simpa using hs)⟩
  have hfactorSelf : ∀ᶠ s in 𝓝[≠] c, F s = (s - c) ^ n • G s := hfactor
  have hfactorMap : ∀ᶠ s in 𝓝[≠] c,
      F (τ s) = (τ s - c) ^ n • G (τ s) := htauWithin.eventually hfactor
  have key : ∀ᶠ s in 𝓝[≠] c,
      (slope τ c s) ^ n • G (τ s) = χ • G s := by
    have hequiv' : ∀ᶠ s in 𝓝[≠] c, F (τ s) = χ • F s :=
      hequiv.filter_mono nhdsWithin_le_nhds
    filter_upwards [self_mem_nhdsWithin, hequiv', hfactorSelf, hfactorMap]
      with s hs heqs e1 e2
    have hsc : s - c ≠ 0 := sub_ne_zero.mpr hs
    have hsl : slope τ c s * (s - c) = τ s - c := by
      rw [slope_def_field, hfix, div_mul_cancel₀ _ hsc]
    have hpow : (s - c) ^ n ≠ 0 := zpow_ne_zero n hsc
    have heq : (s - c) ^ n • ((slope τ c s) ^ n • G (τ s)) =
        (s - c) ^ n • (χ • G s) := by
      calc
        (s - c) ^ n • ((slope τ c s) ^ n • G (τ s)) =
            ((slope τ c s) ^ n * (s - c) ^ n) • G (τ s) := by
              rw [smul_smul]
              congr 1
              ring
        _ = (slope τ c s * (s - c)) ^ n • G (τ s) := by rw [mul_zpow]
        _ = (τ s - c) ^ n • G (τ s) := by rw [hsl]
        _ = F (τ s) := e2.symm
        _ = χ • F s := heqs
        _ = (χ * (s - c) ^ n) • G s := by rw [e1, smul_smul]
        _ = ((s - c) ^ n * χ) • G s := by rw [mul_comm]
        _ = (s - c) ^ n • (χ • G s) := by rw [smul_smul]
    have hcancel := congrArg (fun v : E => ((s - c) ^ n)⁻¹ • v) heq
    simpa [smul_smul, hpow] using hcancel
  have hGlim : Tendsto G (𝓝[≠] c) (𝓝 (G c)) :=
    hGan.continuousAt.tendsto.mono_left nhdsWithin_le_nhds
  have hGmap : Tendsto (fun s => G (τ s)) (𝓝[≠] c) (𝓝 (G c)) :=
    hGan.continuousAt.tendsto.comp (htauN.mono_left nhdsWithin_le_nhds)
  have hlhs : Tendsto (fun s => (slope τ c s) ^ n • G (τ s))
      (𝓝[≠] c) (𝓝 (lam ^ n • G c)) :=
    (hslope.zpow₀ n (Or.inl hlam0)).smul hGmap
  have hrhs : Tendsto (fun s => χ • G s) (𝓝[≠] c) (𝓝 (χ • G c)) :=
    tendsto_const_nhds.smul hGlim
  have hlim : lam ^ n • G c = χ • G c :=
    tendsto_nhds_unique (hlhs.congr' key) hrhs
  have hzero : (lam ^ n - χ) • G c = 0 := by
    rw [sub_smul, hlim, sub_self]
  rcases smul_eq_zero.mp hzero with hscalar | hvector
  · exact sub_eq_zero.mp hscalar
  · exact (hG0 hvector).elim

/-- **Meromorphic residue-character law.** For a scalar meromorphic germ, one signed integer is
simultaneously its multiplicative self-map character exponent and the additive residue of its
logarithmic derivative. -/
theorem meromorphicEquivariant_residueCharacterLaw
    {f τ : ℂ → ℂ} {c χ : ℂ} {n : ℤ}
    (hf : MeromorphicAt f c) (hτ : AnalyticAt ℂ τ c) (hfix : τ c = c)
    (hderiv : deriv τ c ≠ 0)
    (hequiv : ∀ᶠ s in 𝓝 c, f (τ s) = χ * f s)
    (horder : meromorphicOrderAt f c = n) :
    (deriv τ c) ^ n = χ ∧
      Tendsto (fun s => (s - c) * logDeriv f s) (𝓝[≠] c) (𝓝 (n : ℂ)) := by
  exact ⟨multiplier_zpow_meromorphicOrder_eq_character
      hf hτ hfix hderiv
      (by filter_upwards [hequiv] with s hs using by simpa only [smul_eq_mul] using hs)
      horder,
    logDeriv_residue_of_meromorphicOrder hf horder⟩

end GaloisForLFunctions.HTGeometry
