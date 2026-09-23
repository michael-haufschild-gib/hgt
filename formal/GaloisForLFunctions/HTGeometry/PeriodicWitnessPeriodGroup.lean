import GaloisForLFunctions.HTGeometry.PeriodicHypertranscendentalWitness

/-!
# The period group of the witness is exactly `ℤ`

The dichotomy says the period group of a hypertranscendental meromorphic function is infinite
cyclic; for the explicit witness it can be computed outright.

A period `c` of `g (exp (a z))` makes `g` invariant under multiplication by `λ = exp (a c)` off the
origin, hence — both sides being continuous and the punctured plane dense — everywhere.
Differentiating at the origin gives `λ · g'(0) = g'(0)`, so `λ = 1` as soon as `g'(0) ≠ 0`, and then
`a c` is an integer multiple of `2πi`.  The layer-tower function has *every* Taylor coefficient
nonzero, so this applies to it.

* **`mem_zmultiples_of_periodic_comp_exp`** — the general bound;
* **`periodSubgroup_periodicWitness`** — `periodSubgroup periodicWitness = AddSubgroup.zmultiples 1`.
-/

namespace GaloisForLFunctions.HTGeometry

/-- A period of `g (exp (a ·))` rotates `g` by `exp (a c)` off the origin. -/
theorem rotation_of_periodic_comp_exp {g : ℂ → ℂ} {a c : ℂ} (ha : a ≠ 0)
    (hper : Function.Periodic (fun z => g (Complex.exp (a * z))) c) {w : ℂ} (hw : w ≠ 0) :
    g (Complex.exp (a * c) * w) = g w := by
  obtain ⟨z, hz⟩ : ∃ z : ℂ, Complex.exp (a * z) = w := by
    refine ⟨Complex.log w / a, ?_⟩
    rw [mul_div_cancel₀ _ ha, Complex.exp_log hw]
  have hstep := hper z
  have hmul : Complex.exp (a * (z + c)) = Complex.exp (a * c) * w := by
    rw [mul_add, Complex.exp_add, ← hz]
    ring
  rw [show (fun z => g (Complex.exp (a * z))) (z + c) = g (Complex.exp (a * (z + c))) from rfl,
    show (fun z => g (Complex.exp (a * z))) z = g (Complex.exp (a * z)) from rfl, hmul, hz] at hstep
  exact hstep

/-- **The period bound.**  If `g` is entire with `g'(0) ≠ 0`, every period of `g (exp (a z))` is an
integer multiple of `2πi/a`. -/
theorem mem_zmultiples_of_periodic_comp_exp {g : ℂ → ℂ} (hg : ContDiff ℂ (⊤ : ℕ∞) g)
    (hg0 : deriv g 0 ≠ 0) {a c : ℂ} (ha : a ≠ 0)
    (hper : Function.Periodic (fun z => g (Complex.exp (a * z))) c) :
    c ∈ AddSubgroup.zmultiples (2 * Real.pi * Complex.I / a) := by
  set lam : ℂ := Complex.exp (a * c) with hlam
  have hgdiff : Differentiable ℂ g := hg.differentiable (by simp)
  have hall : ∀ w : ℂ, g (lam * w) = g w := by
    have hcont₁ : Continuous fun w : ℂ => g (lam * w) :=
      hgdiff.continuous.comp (continuous_const.mul continuous_id)
    have heq : Set.EqOn (fun w : ℂ => g (lam * w)) g ({0}ᶜ) := by
      intro w hw
      exact rotation_of_periodic_comp_exp ha hper hw
    have := Continuous.ext_on (dense_compl_singleton (0 : ℂ)) hcont₁ hgdiff.continuous heq
    exact fun w => congrFun this w
  have hderiv : lam * deriv g 0 = deriv g 0 := by
    have hfun : (fun w : ℂ => g (lam * w)) = g := funext hall
    have hinner : HasDerivAt (fun y : ℂ => lam * y) lam 0 := by
      simpa using (hasDerivAt_id (0 : ℂ)).const_mul lam
    have hd : HasDerivAt (fun w : ℂ => g (lam * w)) (deriv g (lam * 0) * lam) 0 :=
      ((hgdiff (lam * 0)).hasDerivAt).comp 0 hinner
    rw [hfun] at hd
    have hdd := hd.deriv
    rw [mul_zero] at hdd
    rw [mul_comm]
    exact hdd.symm
  have hlam1 : lam = 1 := by
    have : (lam - 1) * deriv g 0 = 0 := by
      rw [sub_mul, one_mul, hderiv, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hg0
  obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp (by rw [← hlam]; exact hlam1)
  refine AddSubgroup.mem_zmultiples_iff.mpr ⟨n, ?_⟩
  have hac : a * c = (n : ℂ) * (2 * Real.pi * Complex.I) := hn
  have hc : c = (n : ℂ) * (2 * Real.pi * Complex.I) / a := by
    rw [eq_div_iff ha, mul_comm]
    exact hac
  rw [zsmul_eq_mul, hc]
  ring

/-! ### The witness -/

theorem coeff_taylorPS_periodicWitnessBase_ne_zero (n : ℕ) :
    PowerSeries.coeff n (taylorPS dyadicLayerEntireFunction) ≠ 0 := by
  intro h
  have hnorm := norm_coeff_taylorPS_dyadicLayerEntireFunction n
  rw [h, norm_zero] at hnorm
  exact absurd hnorm.symm (ne_of_gt (Real.exp_pos _))

theorem deriv_dyadicLayerEntireFunction_zero_ne_zero :
    deriv dyadicLayerEntireFunction 0 ≠ 0 := by
  have h := coeff_taylorPS_periodicWitnessBase_ne_zero 1
  rw [coeff_taylorPS] at h
  intro h0
  apply h
  rw [iteratedDeriv_one, h0, zero_div]

/-- **The period group of the witness is exactly the integers.**  It contains `1` by construction,
and every period is an integer by the rotation bound. -/
theorem periodSubgroup_periodicWitness :
    periodSubgroup periodicWitness = AddSubgroup.zmultiples (1 : ℂ) := by
  refine le_antisymm ?_ ?_
  · intro c hc
    have hmem := mem_zmultiples_of_periodic_comp_exp contDiff_dyadicLayerEntireFunction
      deriv_dyadicLayerEntireFunction_zero_ne_zero twoPiI_ne_zero_periodicHypertranscendentalWitness hc
    rwa [div_self twoPiI_ne_zero_periodicHypertranscendentalWitness] at hmem
  · rw [AddSubgroup.zmultiples_le]
    exact periodic_periodicWitness

end GaloisForLFunctions.HTGeometry
