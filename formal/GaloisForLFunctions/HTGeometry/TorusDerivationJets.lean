import GaloisForLFunctions.HTGeometry.TorusOrbitPolyannulusUniqueness

/-!
# Time differentiation is a torus derivation

A quasiperiodic function is the restriction of a phase observable to the phase
orbit.  Differentiating in time is then the derivation

```
δ = ∑_j i ω_j z_j ∂_j
```

on the polyannulus: the `k`-th time jet of the quasiperiodic function is the
restriction of `δ^k` of the phase observable.  The derivation preserves
holomorphy, so every time jet is again a phase observable.

This is what lets the minimal autonomous order of the quasiperiodic function be
read off from the phase functions themselves.
-/

open Complex Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

/-! ### The complex phase point and its strip -/

/-- The phase point of the quasiperiodic flow at complex time. -/
def phasePoint (omega : d → ℝ) (t : ℂ) : d → ℂ :=
  fun j => Complex.exp (Complex.I * (omega j : ℂ) * t)

omit [Fintype d] [DecidableEq d] in
theorem phasePoint_ofReal (omega : d → ℝ) (t : ℝ) :
    phasePoint omega (t : ℂ) = torusOrbitPoint omega t := by
  funext j
  rw [phasePoint, torusOrbitPoint]
  congr 1
  push_cast
  ring

omit [Fintype d] [DecidableEq d] in
theorem norm_phasePoint (omega : d → ℝ) (t : ℂ) (j : d) :
    ‖phasePoint omega t j‖ = Real.exp (-(omega j * t.im)) := by
  rw [phasePoint, Complex.norm_exp]
  congr 1
  simp [Complex.mul_re, Complex.mul_im]

/-- The horizontal strip of complex times whose phase point stays inside the
polyannulus. -/
def phaseStrip (ρ omega : d → ℝ) : Set ℂ := {t : ℂ | ∀ j, |omega j * t.im| < ρ j}

omit [DecidableEq d] in
theorem isOpen_phaseStrip (ρ omega : d → ℝ) : IsOpen (phaseStrip ρ omega) := by
  have hset : phaseStrip ρ omega =
      ⋂ j : d, {t : ℂ | |omega j * t.im| < ρ j} := by
    ext t
    simp [phaseStrip]
  rw [hset]
  refine isOpen_iInter_of_finite fun j => ?_
  exact isOpen_lt (by fun_prop) continuous_const

omit [Fintype d] [DecidableEq d] in
theorem ofReal_mem_phaseStrip {ρ omega : d → ℝ} (hρ : ∀ j, 0 < ρ j) (t : ℝ) :
    (t : ℂ) ∈ phaseStrip ρ omega := by
  intro j
  simpa using hρ j

omit [Fintype d] [DecidableEq d] in
theorem phasePoint_mem_polyannulus {ρ omega : d → ℝ} {t : ℂ}
    (ht : t ∈ phaseStrip ρ omega) : phasePoint omega t ∈ polyannulus ρ := by
  intro j
  have hj := ht j
  rw [mem_logAnnulus_iff, norm_phasePoint]
  rw [abs_lt] at hj
  exact ⟨Real.exp_lt_exp.2 (by linarith), Real.exp_lt_exp.2 (by linarith)⟩

/-! ### The torus derivation -/

/-- The `j`-th partial derivative of a phase observable. -/
def coordDeriv (F : (d → ℂ) → ℂ) (j : d) (z : d → ℂ) : ℂ :=
  fderiv ℂ F z (Pi.single j 1)

/-- The time derivation `δ = ∑_j i ω_j z_j ∂_j` on the polyannulus. -/
def torusDerivation (omega : d → ℝ) (F : (d → ℂ) → ℂ) : (d → ℂ) → ℂ :=
  fun z => ∑ j, Complex.I * (omega j : ℂ) * z j * coordDeriv F j z

theorem analyticOnNhd_coordDeriv {F : (d → ℂ) → ℂ} {s : Set (d → ℂ)}
    (hF : AnalyticOnNhd ℂ F s) (j : d) :
    AnalyticOnNhd ℂ (coordDeriv F j) s := by
  have h := ContinuousLinearMap.comp_analyticOnNhd
    (ContinuousLinearMap.apply ℂ ℂ (Pi.single j (1 : ℂ))) hF.fderiv
  intro z hz
  exact h z hz

theorem analyticOnNhd_torusDerivation {F : (d → ℂ) → ℂ} {s : Set (d → ℂ)}
    (omega : d → ℝ) (hF : AnalyticOnNhd ℂ F s) :
    AnalyticOnNhd ℂ (torusDerivation omega F) s := by
  refine Finset.analyticOnNhd_fun_sum Finset.univ fun j _ => ?_
  refine AnalyticOnNhd.mul ?_ (analyticOnNhd_coordDeriv hF j)
  refine analyticOnNhd_const.mul ?_
  exact (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : d => ℂ) j).analyticOnNhd s

theorem analyticOnNhd_torusDerivation_iterate {F : (d → ℂ) → ℂ} {s : Set (d → ℂ)}
    (omega : d → ℝ) (hF : AnalyticOnNhd ℂ F s) (k : ℕ) :
    AnalyticOnNhd ℂ ((torusDerivation omega)^[k] F) s := by
  induction k with
  | zero => simpa using hF
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact analyticOnNhd_torusDerivation omega ih

/-! ### The jet identity -/

/-- The quasiperiodic function attached to a phase observable. -/
def phaseFunction (omega : d → ℝ) (F : (d → ℂ) → ℂ) : ℂ → ℂ :=
  fun t => F (phasePoint omega t)

omit [Fintype d] [DecidableEq d] in
theorem hasDerivAt_phasePoint (omega : d → ℝ) (t : ℂ) :
    HasDerivAt (phasePoint omega)
      (fun j => Complex.I * (omega j : ℂ) * phasePoint omega t j) t := by
  refine hasDerivAt_pi.2 fun j => ?_
  have hlin : HasDerivAt (fun s : ℂ => Complex.I * (omega j : ℂ) * s)
      (Complex.I * (omega j : ℂ)) t := by
    simpa using (hasDerivAt_id t).const_mul (Complex.I * (omega j : ℂ))
  have hexp := hlin.cexp
  simpa [phasePoint, mul_comm] using hexp

/-- The differential of a phase observable in coordinates. -/
theorem fderiv_apply_eq_sum_complexJets (F : (d → ℂ) → ℂ) (z v : d → ℂ) :
    fderiv ℂ F z v = ∑ j, v j * coordDeriv F j z := by
  classical
  have hsingle : ∀ j : d,
      (fun j' : d => if j = j' then (1 : ℂ) else 0) = Pi.single j (1 : ℂ) := by
    intro j
    funext j'
    rw [Pi.single_apply]
    by_cases h : j' = j
    · simp [h]
    · simp [h, Ne.symm h]
  conv_lhs => rw [pi_eq_sum_univ v]
  rw [map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, hsingle j]
  simp [coordDeriv, smul_eq_mul]

/-- **Time differentiation is the torus derivation.** -/
theorem deriv_phaseFunction {ρ omega : d → ℝ} {F : (d → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) {t : ℂ}
    (ht : t ∈ phaseStrip ρ omega) :
    deriv (phaseFunction omega F) t =
      phaseFunction omega (torusDerivation omega F) t := by
  have hmem : phasePoint omega t ∈ polyannulus ρ := phasePoint_mem_polyannulus ht
  have hFd : HasFDerivAt F (fderiv ℂ F (phasePoint omega t)) (phasePoint omega t) :=
    (hF _ hmem).differentiableAt.hasFDerivAt
  have hcomp := hFd.comp_hasDerivAt t (hasDerivAt_phasePoint omega t)
  have hderiv : deriv (phaseFunction omega F) t =
      fderiv ℂ F (phasePoint omega t)
        (fun j => Complex.I * (omega j : ℂ) * phasePoint omega t j) :=
    hcomp.deriv
  rw [hderiv, fderiv_apply_eq_sum_complexJets]
  rfl

/-- **The time jets of a quasiperiodic function are the iterated torus
derivatives of its phase observable.** -/
theorem iteratedDeriv_phaseFunction {ρ omega : d → ℝ} {F : (d → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) (k : ℕ) :
    ∀ t ∈ phaseStrip ρ omega,
      iteratedDeriv k (phaseFunction omega F) t =
        phaseFunction omega ((torusDerivation omega)^[k] F) t := by
  induction k with
  | zero =>
      intro t _
      simp
  | succ k ih =>
      intro t ht
      have hev : iteratedDeriv k (phaseFunction omega F)
          =ᶠ[𝓝 t] phaseFunction omega ((torusDerivation omega)^[k] F) := by
        refine Filter.eventuallyEq_of_mem
          ((isOpen_phaseStrip ρ omega).mem_nhds ht) fun s hs => ?_
        exact ih s hs
      rw [iteratedDeriv_succ, hev.deriv_eq,
        deriv_phaseFunction (analyticOnNhd_torusDerivation_iterate omega hF k) ht,
        ← Function.iterate_succ_apply' (torusDerivation omega) k]

/-- The jet identity along the real orbit. -/
theorem iteratedDeriv_phaseFunction_ofReal {ρ omega : d → ℝ}
    (hρ : ∀ j, 0 < ρ j) {F : (d → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) (k : ℕ) (t : ℝ) :
    iteratedDeriv k (phaseFunction omega F) (t : ℂ) =
      (torusDerivation omega)^[k] F (torusOrbitPoint omega t) := by
  rw [iteratedDeriv_phaseFunction hF k _ (ofReal_mem_phaseStrip hρ t)]
  rw [phaseFunction, phasePoint_ofReal]

end

end GaloisForLFunctions.HTGeometry
