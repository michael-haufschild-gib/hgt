import GaloisForLFunctions.HTGeometry.VanishingMassResidueRigidity

/-!
# Logarithmic residue quantization

The logarithmic derivative of a meromorphic germ has residue equal to its integer
meromorphic order.  Consequently, a finite real-linear family of logarithmic derivatives
produces exactly the finite quantized correction used in the vanishing-mass residue-rigidity
law.
-/

open Filter Topology Complex

namespace GaloisForLFunctions.HTGeometry

/-- The logarithmic derivative of a meromorphic function has residue equal to its
integer meromorphic order.  Positive orders are zeros and negative orders are poles. -/
theorem logDeriv_residue_of_meromorphicOrder {f : ℂ → ℂ} {rho : ℂ} {n : ℤ}
    (hf : MeromorphicAt f rho)
    (horder : meromorphicOrderAt f rho = n) :
    Tendsto (fun s => (s - rho) * logDeriv f s) (𝓝[≠] rho) (𝓝 (n : ℂ)) := by
  rcases (meromorphicOrderAt_eq_int_iff hf).1 horder with ⟨g, hg, hg0, hfac⟩
  rw [eventually_nhdsWithin_iff] at hfac
  rcases mem_nhds_iff.mp hfac with ⟨U, hU, hUopen, hrhoU⟩
  have hgne : ∀ᶠ z in 𝓝 rho, g z ≠ 0 := hg.continuousAt.eventually_ne hg0
  have hlogGcont : ContinuousAt (logDeriv g) rho :=
    (hg.deriv.continuousAt).div hg.continuousAt hg0
  have ha : Tendsto (fun s : ℂ => s - rho) (𝓝[≠] rho) (𝓝 0) :=
    ((continuous_id.sub continuous_const).tendsto' rho 0 (by simp)).mono_left
      nhdsWithin_le_nhds
  have hb : Tendsto (logDeriv g) (𝓝[≠] rho) (𝓝 (logDeriv g rho)) :=
    hlogGcont.mono_left nhdsWithin_le_nhds
  have htend0 : Tendsto (fun s => (s - rho) * logDeriv g s) (𝓝[≠] rho) (𝓝 0) := by
    simpa using ha.mul hb
  have htend1 :
      Tendsto (fun s => (n : ℂ) + (s - rho) * logDeriv g s)
        (𝓝[≠] rho) (𝓝 (n : ℂ)) := by
    simpa using tendsto_const_nhds.add htend0
  refine htend1.congr' ?_
  filter_upwards [self_mem_nhdsWithin,
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (hUopen.mem_nhds hrhoU),
    hgne.filter_mono nhdsWithin_le_nhds,
    hg.eventually_analyticAt.filter_mono nhdsWithin_le_nhds]
      with s hs hsU hgs hgana
  have hsrho : s ≠ rho := by simpa using hs
  have hsrho0 : s - rho ≠ 0 := sub_ne_zero.mpr hsrho
  have hFeq : f =ᶠ[𝓝 s] (fun z => (z - rho) ^ n * g z) := by
    filter_upwards [hUopen.mem_nhds hsU, eventually_ne_nhds hsrho] with z hzU hzrho
    rw [hU hzU (by simpa using hzrho), smul_eq_mul]
  have hlogf : logDeriv f s = logDeriv (fun z => (z - rho) ^ n * g z) s := by
    rw [logDeriv_apply, logDeriv_apply, hFeq.deriv_eq, hFeq.eq_of_nhds]
  have hdz : DifferentiableAt ℂ (fun z : ℂ => z - rho) s := by fun_prop
  have hdzpow : DifferentiableAt ℂ (fun z : ℂ => (z - rho) ^ n) s :=
    hdz.zpow (Or.inl hsrho0)
  have hderiv : deriv (fun z : ℂ => z - rho) s = 1 := by simp
  have hld : logDeriv (fun z => z - rho) s = (s - rho)⁻¹ := by
    rw [logDeriv_apply, hderiv, one_div]
  rw [hlogf,
    logDeriv_mul (f := fun z => (z - rho) ^ n) (g := g) s
      (zpow_ne_zero n hsrho0) hgs hdzpow hgana.differentiableAt,
    logDeriv_fun_zpow hdz n, hld]
  field_simp

/-- The residue of a finite real-linear combination of logarithmic derivatives is the
corresponding real-linear combination of the integer meromorphic orders. -/
theorem finiteLogDeriv_residue_of_meromorphicOrders
    {J : Type*} [Fintype J]
    (F : J → ℂ → ℂ) (rho : ℂ) (coefficient : J → ℝ) (order : J → ℤ)
    (hF : ∀ j, MeromorphicAt (F j) rho)
    (horder : ∀ j, meromorphicOrderAt (F j) rho = order j) :
    Tendsto
      (fun s => (s - rho) * ∑ j, (coefficient j : ℂ) * logDeriv (F j) s)
      (𝓝[≠] rho)
      (𝓝 (∑ j, (coefficient j : ℂ) * (order j : ℂ))) := by
  have hsum :
      Tendsto
        (fun s => ∑ j, (s - rho) *
          ((coefficient j : ℂ) * logDeriv (F j) s))
        (𝓝[≠] rho)
        (𝓝 (∑ j, (coefficient j : ℂ) * (order j : ℂ))) := by
    apply tendsto_finsetSum
    intro j _hj
    have hj := logDeriv_residue_of_meromorphicOrder (hF j) (horder j)
    convert hj.const_mul (coefficient j : ℂ) using 1
    funext s
    ring
  simpa only [Finset.mul_sum] using hsum

/-- The local analytic residue of a prime-indexed finite logarithmic gauge family is exactly
the finite quantized residue correction used by the vanishing-mass rigidity theorem. -/
theorem finiteLogDeriv_residue_eq_finiteQuantizedResidueCorrection
    {J P : Type*} [Fintype J]
    (F : J → P → ℂ → ℂ) (center : P → ℂ)
    (coefficient : J → ℝ) (order : J → P → ℤ)
    (hF : ∀ j p, MeromorphicAt (F j p) (center p))
    (horder : ∀ j p, meromorphicOrderAt (F j p) (center p) = order j p)
    (p : P) :
    Tendsto
      (fun s => (s - center p) *
        ∑ j, (coefficient j : ℂ) * logDeriv (F j p) s)
      (𝓝[≠] center p)
      (𝓝 (finiteQuantizedResidueCorrection coefficient order p : ℂ)) := by
  have h := finiteLogDeriv_residue_of_meromorphicOrders
    (fun j => F j p) (center p) coefficient (fun j => order j p)
    (fun j => hF j p) (fun j => horder j p)
  convert h using 1
  simp [finiteQuantizedResidueCorrection]

end GaloisForLFunctions.HTGeometry
