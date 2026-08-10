import GaloisForLFunctions.HTGeometry.EulerQGammaRenormProduct

/-!
# Holomorphy of the renormalised Euler q-Gamma product

On a compact subset of the convergence half plane the local deviations admit a single summable
majorant — obtained by bounding `‖s‖` above and `Re s` below on the compact set — so the
renormalised product converges locally uniformly and is therefore holomorphic there.
-/

namespace GaloisForLFunctions.HTGeometry

open Filter Topology

noncomputable section

/-- The convergence half plane `Re s > 1/(2σ) − 1` of the renormalised product. -/
def eqgRenormDomain (σ : EulerSigma) : Set ℂ := {s : ℂ | 1 / (2 * σ.val) - 1 < s.re}

theorem isOpen_eqgRenormDomain (σ : EulerSigma) : IsOpen (eqgRenormDomain σ) :=
  isOpen_lt continuous_const Complex.continuous_re

theorem mapsTo_one_add_qHalfPlane (σ : EulerSigma) :
    Set.MapsTo (fun s : ℂ => 1 + s) (eqgRenormDomain σ) qHalfPlane :=
  fun _ hs => one_add_mem_qHalfPlane σ hs

theorem continuousOn_eqgRenormLocal_sub_one (σ : EulerSigma) (p : Nat.Primes) :
    ContinuousOn (fun s : ℂ => eqgRenormLocal (eqgNome σ p) s - 1) (eqgRenormDomain σ) := by
  have hshift : ContinuousOn (fun s : ℂ => 1 + s) (eqgRenormDomain σ) :=
    (continuous_const.add continuous_id).continuousOn
  have hgamma : ContinuousOn (fun s : ℂ => qGammaOn (eqgNome σ p) (1 + s))
      (eqgRenormDomain σ) :=
    ContinuousOn.comp (differentiableOn_qGammaOn (eqgNome σ p)).continuousOn hshift
      (mapsTo_one_add_qHalfPlane σ)
  have hcpow : Continuous (fun s : ℂ => (((eqgNome σ p).val : ℂ)) ^ (1 + s)) := by
    refine Continuous.const_cpow (continuous_const.add continuous_id) (Or.inl ?_)
    exact (eqgNome σ p).complex_ne_zero
  have hact : Continuous (fun s : ℂ => eqgActivation (eqgNome σ p) s) := by
    refine Continuous.add ?_ hcpow
    exact continuous_const.mul (continuous_id.sub continuous_const)
  have hexp : Continuous (fun s : ℂ => Complex.exp (-(eqgActivation (eqgNome σ p) s))) :=
    Complex.continuous_exp.comp hact.neg
  exact (hgamma.mul hexp.continuousOn).sub continuousOn_const

/-! ## Uniform convergence on compacts -/

theorem hasProdUniformlyOn_eqgRenormLocal (σ : EulerSigma) {K : Set ℂ}
    (hKsub : K ⊆ eqgRenormDomain σ) (hK : IsCompact K) :
    HasProdUniformlyOn (fun (p : Nat.Primes) (s : ℂ) => eqgRenormLocal (eqgNome σ p) s)
      (fun s => ∏' p : Nat.Primes, eqgRenormLocal (eqgNome σ p) s) K := by
  have hfun : (fun (p : Nat.Primes) (s : ℂ) =>
        1 + (eqgRenormLocal (eqgNome σ p) s - 1))
      = fun (p : Nat.Primes) (s : ℂ) => eqgRenormLocal (eqgNome σ p) s := by
    funext p s
    ring
  have hval : (fun s : ℂ => ∏' p : Nat.Primes, (1 + (eqgRenormLocal (eqgNome σ p) s - 1)))
      = fun s : ℂ => ∏' p : Nat.Primes, eqgRenormLocal (eqgNome σ p) s := by
    funext s
    refine tprod_congr fun p => ?_
    ring
  rcases K.eq_empty_or_nonempty with hKe | hKne
  · subst hKe
    have hu : Summable (fun _ : Nat.Primes => (0 : ℝ)) := summable_zero
    have hbound : ∀ᶠ p : Nat.Primes in cofinite, ∀ s ∈ (∅ : Set ℂ),
        ‖eqgRenormLocal (eqgNome σ p) s - 1‖ ≤ 0 := by
      filter_upwards with p
      intro s hs
      exact absurd hs (Set.notMem_empty s)
    have hcont : ∀ p : Nat.Primes,
        ContinuousOn (fun s : ℂ => eqgRenormLocal (eqgNome σ p) s - 1) (∅ : Set ℂ) :=
      fun p => continuousOn_empty _
    have hmain := Summable.hasProdUniformlyOn_one_add hK hu hbound hcont
    rw [hfun, hval] at hmain
    exact hmain
  · obtain ⟨z₀, hz₀K, hz₀⟩ := hK.exists_isMinOn hKne Complex.continuous_re.continuousOn
    obtain ⟨z₁, _, hz₁⟩ := hK.exists_isMaxOn hKne continuous_norm.continuousOn
    set M : ℝ := ‖z₁‖ with hM
    set w : ℝ := eqgShiftExponent σ z₀ with hw
    have hwhalf : 1 / 2 < w := half_lt_eqgShiftExponent σ (hKsub hz₀K)
    have hσ : (0 : ℝ) < σ.val := σ.pos
    have hshiftge : ∀ s ∈ K, w ≤ eqgShiftExponent σ s := by
      intro s hs
      have hre : z₀.re ≤ s.re := hz₀ hs
      rw [hw, eqgShiftExponent, eqgShiftExponent]
      nlinarith
    set u : Nat.Primes → ℝ := fun p =>
      4 * (eqgPowerMajorAt σ M p + eqgNumerMajor σ p + 2 * eqgDenomMajorAt σ w p) with hu_def
    have hu : Summable u := by
      refine Summable.mul_left 4 ?_
      exact ((summable_eqgPowerMajorAt σ M).add (summable_eqgNumerMajor σ)).add
        ((summable_eqgDenomMajorAt σ hwhalf).mul_left 2)
    have hev1 := eventually_prime_rpow_le_half hwhalf
    have hev2 : ∀ᶠ p : Nat.Primes in cofinite, eqgPowerMajorAt σ M p ≤ 1 :=
      ((summable_eqgPowerMajorAt σ M).tendsto_cofinite_zero.eventually_lt_const
        (by norm_num)).mono fun p h => h.le
    have hev3 : ∀ᶠ p : Nat.Primes in cofinite, eqgNumerMajor σ p ≤ 1 :=
      ((summable_eqgNumerMajor σ).tendsto_cofinite_zero.eventually_lt_const
        (by norm_num)).mono fun p h => h.le
    have hev4 : ∀ᶠ p : Nat.Primes in cofinite, 2 * eqgDenomMajorAt σ w p ≤ 1 :=
      ((summable_eqgDenomMajorAt σ hwhalf).tendsto_cofinite_zero.eventually_lt_const
        (show (0 : ℝ) < 1 / 2 by norm_num)).mono fun p h => by linarith
    have hbound : ∀ᶠ p : Nat.Primes in cofinite, ∀ s ∈ K,
        ‖eqgRenormLocal (eqgNome σ p) s - 1‖ ≤ u p := by
      filter_upwards [hev1, hev2, hev3, hev4] with p h1 h2 h3 h4
      intro s hs
      have hsK : s ∈ eqgRenormDomain σ := hKsub hs
      have hhalfp := one_add_mem_qHalfPlane σ hsK
      have hnormM : ‖s‖ ≤ M := hz₁ hs
      have hshift : ((p : ℕ) : ℝ) ^ (-eqgShiftExponent σ s) ≤ 1 / 2 :=
        le_trans (rpow_neg_le_of_le (hshiftge s hs)) h1
      have hPow : eqgPowerMajor σ s p ≤ eqgPowerMajorAt σ M p :=
        eqgPowerMajor_le_at σ hnormM p
      have hDen : eqgDenomMajor σ s p ≤ eqgDenomMajorAt σ w p := by
        rw [eqgDenomMajor_eq_at]
        exact eqgDenomMajorAt_antitone σ (hshiftge s hs) p
      have hc2 : eqgDenomMajor σ s p ≤ 1 / 2 := by linarith
      have hbnd := norm_eqgRenormLocal_sub_one_le (eqgNome σ p) hhalfp
        (norm_eqgPowerFactor_prime_le σ s p) (norm_eqgNumerFactor_prime_le σ p)
        (norm_eqgDenomFactorRenorm_prime_le σ s p hshift) hc2
      have hcomp := composite_le (eqgPowerMajor_nonneg σ s p) (eqgNumerMajor_nonneg σ p)
        (eqgDenomMajor_nonneg σ s p) (le_trans hPow h2) h3 (by linarith)
      have hfinal : 4 * (eqgPowerMajor σ s p + eqgNumerMajor σ p + 2 * eqgDenomMajor σ s p)
          ≤ u p := by
        rw [hu_def]
        have : eqgPowerMajor σ s p + eqgNumerMajor σ p + 2 * eqgDenomMajor σ s p
            ≤ eqgPowerMajorAt σ M p + eqgNumerMajor σ p + 2 * eqgDenomMajorAt σ w p := by
          linarith
        linarith
      linarith [le_trans hbnd hcomp]
    have hcont : ∀ p : Nat.Primes,
        ContinuousOn (fun s : ℂ => eqgRenormLocal (eqgNome σ p) s - 1) K :=
      fun p => (continuousOn_eqgRenormLocal_sub_one σ p).mono hKsub
    have hmain := Summable.hasProdUniformlyOn_one_add hK hu hbound hcont
    rw [hfun, hval] at hmain
    exact hmain

/-- **Theorem 9.1, holomorphy clause.**  The renormalised Euler q-Gamma product converges locally
uniformly on `Re s > 1/(2σ) − 1`. -/
theorem hasProdLocallyUniformlyOn_eqgRenormLocal (σ : EulerSigma) :
    HasProdLocallyUniformlyOn (fun (p : Nat.Primes) (s : ℂ) => eqgRenormLocal (eqgNome σ p) s)
      (fun s => ∏' p : Nat.Primes, eqgRenormLocal (eqgNome σ p) s) (eqgRenormDomain σ) := by
  refine hasProdLocallyUniformlyOn_of_forall_compact (isOpen_eqgRenormDomain σ) ?_
  intro K hKsub hK
  exact hasProdUniformlyOn_eqgRenormLocal σ hKsub hK

/-- **Theorem 9.1, analytic half.**  The renormalised Euler q-Gamma product is holomorphic on the
half plane `Re s > 1/(2σ) − 1`. -/
theorem differentiableOn_eqgRenormProduct (σ : EulerSigma) :
    DifferentiableOn ℂ (fun s => ∏' p : Nat.Primes, eqgRenormLocal (eqgNome σ p) s)
      (eqgRenormDomain σ) := by
  have hprod := hasProdLocallyUniformlyOn_eqgRenormLocal σ
  have ht := hasProdLocallyUniformlyOn_iff_tendstoLocallyUniformlyOn.mp hprod
  have hd1 : ∀ p : Nat.Primes,
      DifferentiableOn ℂ (fun s : ℂ => eqgRenormLocal (eqgNome σ p) s) (eqgRenormDomain σ) := by
    intro p
    have hshift : DifferentiableOn ℂ (fun s : ℂ => 1 + s) (eqgRenormDomain σ) :=
      (differentiable_const 1).add differentiable_id |>.differentiableOn
    have hgamma : DifferentiableOn ℂ (fun s : ℂ => qGammaOn (eqgNome σ p) (1 + s))
        (eqgRenormDomain σ) :=
      DifferentiableOn.comp (differentiableOn_qGammaOn (eqgNome σ p)) hshift
        (mapsTo_one_add_qHalfPlane σ)
    have hcpow : Differentiable ℂ (fun s : ℂ => (((eqgNome σ p).val : ℂ)) ^ (1 + s)) := by
      intro s
      refine DifferentiableAt.const_cpow ?_ (Or.inl (eqgNome σ p).complex_ne_zero)
      exact (differentiableAt_const _).add differentiableAt_id
    have hact : Differentiable ℂ (fun s : ℂ => eqgActivation (eqgNome σ p) s) := by
      refine Differentiable.add ?_ hcpow
      exact (differentiable_const _).mul (differentiable_id.sub (differentiable_const _))
    have hexp : Differentiable ℂ (fun s : ℂ => Complex.exp (-(eqgActivation (eqgNome σ p) s))) :=
      Complex.differentiable_exp.comp hact.neg
    exact hgamma.mul hexp.differentiableOn
  have hd : ∀ᶠ S : Finset Nat.Primes in atTop,
      DifferentiableOn ℂ (fun s : ℂ => ∏ p ∈ S, eqgRenormLocal (eqgNome σ p) s)
        (eqgRenormDomain σ) := by
    filter_upwards with S
    exact DifferentiableOn.fun_finsetProd fun p _ => hd1 p
  exact ht.differentiableOn hd (isOpen_eqgRenormDomain σ)

end

end GaloisForLFunctions.HTGeometry
