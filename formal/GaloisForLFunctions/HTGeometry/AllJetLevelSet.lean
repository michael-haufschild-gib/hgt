import GaloisForLFunctions.HTGeometry.ActivePhaseLattice
import GaloisForLFunctions.HTGeometry.PhaseJetRelationTransfer

/-!
# The common level set of all phase jets

Multiplicative translation of the polyannulus commutes with the torus
derivation, because the vector fields `z_j ∂_j` are translation invariant.  So
the phase jets of a translated observable are the translates of its phase jets.

Two torus points with the same values of every phase jet therefore give
quasiperiodic functions with the same Taylor series at the origin; being
holomorphic on the connected strip they agree there, hence along the whole real
orbit, hence — the orbit being dense in the torus and the torus a uniqueness set
for the polyannulus — the observable is invariant under the corresponding
translation.

Combined with the stabilizer theorem, the common level set of all phase jets
through a torus point is exactly its coset under the annihilator of the active
lattice.
-/

open Complex Set Filter Topology

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {d : Type} [Fintype d] [DecidableEq d]

/-! ### Analytic functions with the same jets at a point -/

/-- **Two analytic functions with the same jets at an interior point of a
connected open set agree on it.** -/
theorem eqOn_of_iteratedDeriv_eq {U : Set ℂ} (hU : IsPreconnected U)
    {f g : ℂ → ℂ} (hf : AnalyticOnNhd ℂ f U) (hg : AnalyticOnNhd ℂ g U)
    {z₀ : ℂ} (hz₀ : z₀ ∈ U)
    (h : ∀ k, iteratedDeriv k f z₀ = iteratedDeriv k g z₀) :
    Set.EqOn f g U := by
  have hd : AnalyticOnNhd ℂ (f - g) U := hf.sub hg
  have hzero : ∀ k, iteratedDeriv k (f - g) z₀ = 0 := by
    intro k
    rw [iteratedDeriv_sub ((hf z₀ hz₀).contDiffAt) ((hg z₀ hz₀).contDiffAt), h k,
      sub_self]
  have hall : ∀ n : ℕ, (n : ℕ∞) ≤ analyticOrderAt (f - g) z₀ := by
    intro n
    exact (natCast_le_analyticOrderAt_iff_iteratedDeriv_eq_zero (hd z₀ hz₀)).2
      fun i _ => hzero i
  have htop : analyticOrderAt (f - g) z₀ = ⊤ := by
    by_contra hne
    obtain ⟨k, hk⟩ := ENat.ne_top_iff_exists.1 hne
    have hle := hall (k + 1)
    rw [← hk] at hle
    exact absurd hle (by exact_mod_cast (Nat.lt_succ_self k).not_ge)
  have hev : (f - g) =ᶠ[𝓝 z₀] 0 := analyticOrderAt_eq_top.1 htop
  have hzeroOn := hd.eqOn_zero_of_preconnected_of_eventuallyEq_zero hU hz₀ hev
  intro z hz
  have hzz := hzeroOn hz
  have : f z - g z = 0 := hzz
  linear_combination this

/-! ### The strip is convex -/

omit [Fintype d] [DecidableEq d] in
theorem convex_phaseStrip (ρ omega : d → ℝ) : Convex ℝ (phaseStrip ρ omega) := by
  have happ : ∀ (j : d) (t : ℂ), (omega j • Complex.imLm) t = omega j * t.im := by
    intro j t
    rfl
  have hset : phaseStrip ρ omega =
      ⋂ j : d, ((omega j • Complex.imLm) ⁻¹' Set.Ioo (-(ρ j)) (ρ j)) := by
    ext t
    simp only [phaseStrip, Set.mem_setOf_eq, Set.mem_iInter, Set.mem_preimage,
      Set.mem_Ioo, happ]
    exact forall_congr' fun j => abs_lt
  rw [hset]
  refine convex_iInter fun j => ?_
  exact (convex_Ioo _ _).linear_preimage (omega j • Complex.imLm)

omit [Fintype d] [DecidableEq d] in
theorem isPreconnected_phaseStrip (ρ omega : d → ℝ) :
    IsPreconnected (phaseStrip ρ omega) :=
  (convex_phaseStrip ρ omega).isPreconnected

omit [Fintype d] [DecidableEq d] in
theorem zero_mem_phaseStrip {ρ omega : d → ℝ} (hρ : ∀ j, 0 < ρ j) :
    (0 : ℂ) ∈ phaseStrip ρ omega := by
  intro j
  simpa using hρ j

/-! ### The phase function is analytic on the strip -/

omit [DecidableEq d] in
theorem analyticOnNhd_phasePoint (omega : d → ℝ) (s : Set ℂ) :
    AnalyticOnNhd ℂ (phasePoint omega) s := by
  refine analyticOnNhd_pi_iff.mpr fun j => ?_
  exact (analyticOnNhd_const.mul analyticOnNhd_id).cexp

omit [DecidableEq d] in
theorem analyticOnNhd_phaseFunction {ρ omega : d → ℝ} {F : (d → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) :
    AnalyticOnNhd ℂ (phaseFunction omega F) (phaseStrip ρ omega) :=
  hF.comp (analyticOnNhd_phasePoint omega _) fun _ ht => phasePoint_mem_polyannulus ht

/-! ### The torus derivation commutes with scaling -/

/-- Multiplicative translation as a continuous linear map. -/
def torusScaleL (h : d → ℂ) : (d → ℂ) →L[ℂ] (d → ℂ) :=
  ContinuousLinearMap.pi fun j =>
    (h j) • (ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : d => ℂ) j)

omit [Fintype d] [DecidableEq d] in
@[simp] theorem torusScaleL_apply (h z : d → ℂ) : torusScaleL h z = torusScale h z := by
  funext j
  rfl

omit [Fintype d] in
theorem torusScaleL_single (h : d → ℂ) (j : d) :
    torusScaleL h (Pi.single j 1) = h j • Pi.single j (1 : ℂ) := by
  funext j'
  rw [torusScaleL_apply, torusScale]
  by_cases hj : j' = j
  · subst hj
    simp
  · simp [hj]

theorem coordDeriv_comp_torusScale {ρ : d → ℝ} {h : d → ℂ}
    (hh : h ∈ unitTorus d) {F : (d → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) (j : d) {z : d → ℂ}
    (hz : z ∈ polyannulus ρ) :
    coordDeriv (fun w => F (torusScale h w)) j z
      = h j * coordDeriv F j (torusScale h z) := by
  have hmem : torusScale h z ∈ polyannulus ρ := torusScale_mem_polyannulus hh hz
  have hFd : HasFDerivAt F (fderiv ℂ F (torusScale h z)) (torusScale h z) :=
    (hF _ hmem).differentiableAt.hasFDerivAt
  have hSd : HasFDerivAt (torusScale h) (torusScaleL h) z := by
    have := (torusScaleL h).hasFDerivAt (x := z)
    refine this.congr_of_eventuallyEq ?_
    filter_upwards with w
    rw [torusScaleL_apply]
  have hcomp : HasFDerivAt (fun w => F (torusScale h w))
      ((fderiv ℂ F (torusScale h z)).comp (torusScaleL h)) z := hFd.comp z hSd
  rw [coordDeriv, hcomp.fderiv]
  rw [ContinuousLinearMap.coe_comp, Function.comp_apply, torusScaleL_single,
    map_smul, smul_eq_mul, coordDeriv]

theorem torusDerivation_comp_torusScale {ρ : d → ℝ} (omega : d → ℝ) {h : d → ℂ}
    (hh : h ∈ unitTorus d) {F : (d → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) :
    ∀ z ∈ polyannulus ρ,
      torusDerivation omega (fun w => F (torusScale h w)) z
        = torusDerivation omega F (torusScale h z) := by
  intro z hz
  rw [torusDerivation, torusDerivation]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coordDeriv_comp_torusScale hh hF j hz]
  show Complex.I * (omega j : ℂ) * z j * (h j * coordDeriv F j (torusScale h z))
    = Complex.I * (omega j : ℂ) * (h j * z j) * coordDeriv F j (torusScale h z)
  ring

theorem torusDerivation_congr {U : Set (d → ℂ)} (hU : IsOpen U) (omega : d → ℝ)
    {F G : (d → ℂ) → ℂ} (h : ∀ z ∈ U, F z = G z) :
    ∀ z ∈ U, torusDerivation omega F z = torusDerivation omega G z := by
  intro z hz
  have hev : F =ᶠ[𝓝 z] G := by
    filter_upwards [hU.mem_nhds hz] with w hw
    exact h w hw
  rw [torusDerivation, torusDerivation]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [coordDeriv, coordDeriv, hev.fderiv_eq]

theorem phaseJet_comp_torusScale {ρ : d → ℝ} (omega : d → ℝ) {h : d → ℂ}
    (hh : h ∈ unitTorus d) {F : (d → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) (k : ℕ) :
    ∀ z ∈ polyannulus ρ,
      phaseJet omega (fun w => F (torusScale h w)) k z
        = phaseJet omega F k (torusScale h z) := by
  induction k with
  | zero =>
      intro z _
      rfl
  | succ k ih =>
      intro z hz
      have hstep : phaseJet omega (fun w => F (torusScale h w)) (k + 1) z
          = torusDerivation omega (phaseJet omega (fun w => F (torusScale h w)) k) z := by
        rw [phaseJet, phaseJet, Function.iterate_succ_apply']
      rw [hstep]
      have hcong := torusDerivation_congr (isOpen_polyannulus ρ) omega
        (F := phaseJet omega (fun w => F (torusScale h w)) k)
        (G := fun w => phaseJet omega F k (torusScale h w)) ih z hz
      rw [hcong]
      have hjet := torusDerivation_comp_torusScale omega hh
        (analyticOnNhd_phaseJet omega hF k) z hz
      rw [hjet]
      show torusDerivation omega ((torusDerivation omega)^[k] F) (torusScale h z)
        = (torusDerivation omega)^[k + 1] F (torusScale h z)
      rw [Function.iterate_succ_apply']

/-! ### Jets at the origin of a translated phase function -/

omit [Fintype d] [DecidableEq d] in
theorem phasePoint_zero (omega : d → ℝ) :
    phasePoint omega (0 : ℂ) = fun _ : d => (1 : ℂ) := by
  funext j
  rw [phasePoint, mul_zero, Complex.exp_zero]

omit [Fintype d] [DecidableEq d] in
theorem torusScale_one (h : d → ℂ) : torusScale h (fun _ : d => (1 : ℂ)) = h := by
  funext j
  rw [torusScale, mul_one]

omit [Fintype d] [DecidableEq d] in
theorem one_mem_polyannulus {ρ : d → ℝ} (hρ : ∀ j, 0 < ρ j) :
    (fun _ : d => (1 : ℂ)) ∈ polyannulus ρ :=
  unitTorus_subset_polyannulus hρ fun _ => by simp

theorem iteratedDeriv_phaseFunction_comp_torusScale_zero {ρ omega : d → ℝ}
    (hρ : ∀ j, 0 < ρ j) {h : d → ℂ} (hh : h ∈ unitTorus d)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) (k : ℕ) :
    iteratedDeriv k (phaseFunction omega (fun w => F (torusScale h w))) 0
      = phaseJet omega F k h := by
  rw [iteratedDeriv_phaseFunction (analyticOnNhd_comp_torusScale hh hF) k 0
    (zero_mem_phaseStrip hρ)]
  rw [phaseFunction, phasePoint_zero]
  have hone := phaseJet_comp_torusScale omega hh hF k _ (one_mem_polyannulus hρ)
  rw [torusScale_one] at hone
  exact hone

/-! ### The all-jet level set -/

/-- **Equation `(19)`: equal phase jets force equality along the orbit.** -/
theorem eqOn_polyannulus_of_phaseJet_eq {ρ omega : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hindep : RationallyIndependentFrequency omega) {F : (d → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) {u v : UnitAddTorus d}
    (h : ∀ k, phaseJet omega F k (circleCoords u) =
      phaseJet omega F k (circleCoords v)) :
    ∀ z ∈ polyannulus ρ,
      F (torusScale (circleCoords u) z) = F (torusScale (circleCoords v) z) := by
  have hu := circleCoords_mem_unitTorus (d := d) u
  have hv := circleCoords_mem_unitTorus (d := d) v
  have hGu : AnalyticOnNhd ℂ (fun z => F (torusScale (circleCoords u) z))
      (polyannulus ρ) := analyticOnNhd_comp_torusScale hu hF
  have hGv : AnalyticOnNhd ℂ (fun z => F (torusScale (circleCoords v) z))
      (polyannulus ρ) := analyticOnNhd_comp_torusScale hv hF
  have hjets : ∀ k,
      iteratedDeriv k (phaseFunction omega
          (fun w => F (torusScale (circleCoords u) w))) 0
        = iteratedDeriv k (phaseFunction omega
          (fun w => F (torusScale (circleCoords v) w))) 0 := by
    intro k
    rw [iteratedDeriv_phaseFunction_comp_torusScale_zero hρ hu hF k,
      iteratedDeriv_phaseFunction_comp_torusScale_zero hρ hv hF k]
    exact h k
  have hstrip := eqOn_of_iteratedDeriv_eq (isPreconnected_phaseStrip ρ omega)
    (analyticOnNhd_phaseFunction (omega := omega) hGu)
    (analyticOnNhd_phaseFunction (omega := omega) hGv)
    (zero_mem_phaseStrip hρ) hjets
  have horbit : ∀ t : ℝ,
      (fun z => F (torusScale (circleCoords u) z))
          (torusOrbitPoint omega t) -
        (fun z => F (torusScale (circleCoords v) z))
          (torusOrbitPoint omega t) = 0 := by
    intro t
    have hmem : ((t : ℝ) : ℂ) ∈ phaseStrip ρ omega := ofReal_mem_phaseStrip hρ t
    have hval := hstrip hmem
    rw [phaseFunction, phaseFunction, phasePoint_ofReal] at hval
    show F (torusScale (circleCoords u) (torusOrbitPoint omega t))
      - F (torusScale (circleCoords v) (torusOrbitPoint omega t)) = 0
    rw [hval, sub_self]
  have hall := eqOn_zero_polyannulus_of_eqOn_zero_orbit hρ hindep (hGu.sub hGv) horbit
  intro z hz
  have hzz : F (torusScale (circleCoords u) z) -
      F (torusScale (circleCoords v) z) = 0 := hall z hz
  linear_combination hzz

/-! ### The all-jet level set is the stabilizer coset -/

omit [Fintype d] [DecidableEq d] in
theorem torusScale_torusScale (a b z : d → ℂ) :
    torusScale a (torusScale b z) = torusScale (torusScale a b) z := by
  funext j
  rw [torusScale, torusScale, torusScale, torusScale, mul_assoc]

omit [Fintype d] [DecidableEq d] in
theorem torusScale_one_left (z : d → ℂ) :
    torusScale (fun _ : d => (1 : ℂ)) z = z := by
  funext j
  rw [torusScale, one_mul]

omit [Fintype d] [DecidableEq d] in
theorem circleCoords_zero :
    circleCoords (0 : UnitAddTorus d) = fun _ : d => (1 : ℂ) := by
  funext j
  show fourier 1 ((0 : UnitAddTorus d) j) = 1
  simp

theorem phaseJet_congr {U : Set (d → ℂ)} (hU : IsOpen U) (omega : d → ℝ)
    {F G : (d → ℂ) → ℂ} (h : ∀ z ∈ U, F z = G z) (k : ℕ) :
    ∀ z ∈ U, phaseJet omega F k z = phaseJet omega G k z := by
  induction k with
  | zero => exact h
  | succ k ih =>
      intro z hz
      show (torusDerivation omega)^[k + 1] F z = (torusDerivation omega)^[k + 1] G z
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact torusDerivation_congr hU omega ih z hz

/-- **Equation `(22)`, forward: equal phase jets give an invariance.** -/
theorem eqOn_comp_torusScale_sub_of_phaseJet_eq {ρ omega : d → ℝ}
    (hρ : ∀ j, 0 < ρ j) (hindep : RationallyIndependentFrequency omega)
    {F : (d → ℂ) → ℂ} (hF : AnalyticOnNhd ℂ F (polyannulus ρ))
    {u v : UnitAddTorus d}
    (h : ∀ k, phaseJet omega F k (circleCoords u) =
      phaseJet omega F k (circleCoords v)) :
    ∀ z ∈ polyannulus ρ, F (torusScale (circleCoords (v - u)) z) = F z := by
  have hbase := eqOn_polyannulus_of_phaseJet_eq hρ hindep hF h
  intro w hw
  have hnu : circleCoords (-u) ∈ unitTorus d := circleCoords_mem_unitTorus _
  have hz : torusScale (circleCoords (-u)) w ∈ polyannulus ρ :=
    torusScale_mem_polyannulus hnu hw
  have hval := hbase _ hz
  have hA : torusScale (circleCoords u) (circleCoords (-u))
      = fun _ : d => (1 : ℂ) := by
    rw [← circleCoords_add, add_neg_cancel, circleCoords_zero]
  have hB : torusScale (circleCoords v) (circleCoords (-u))
      = circleCoords (v - u) := by
    rw [← circleCoords_add, sub_eq_add_neg]
  rw [torusScale_torusScale, torusScale_torusScale, hA, hB,
    torusScale_one_left] at hval
  exact hval.symm

/-- **Equation `(22)`, backward: an invariance equalizes all phase jets.** -/
theorem phaseJet_eq_of_eqOn_comp_torusScale_sub {ρ omega : d → ℝ}
    (hρ : ∀ j, 0 < ρ j) {F : (d → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) {u v : UnitAddTorus d}
    (h : ∀ z ∈ polyannulus ρ, F (torusScale (circleCoords (v - u)) z) = F z)
    (k : ℕ) :
    phaseJet omega F k (circleCoords u) = phaseJet omega F k (circleCoords v) := by
  have hh : circleCoords (v - u) ∈ unitTorus d := circleCoords_mem_unitTorus _
  have hcong := phaseJet_congr (isOpen_polyannulus ρ) omega
    (F := fun z => F (torusScale (circleCoords (v - u)) z)) (G := F) h k
  have hscale := phaseJet_comp_torusScale omega hh hF k
  have hu : circleCoords u ∈ polyannulus ρ :=
    unitTorus_subset_polyannulus hρ (circleCoords_mem_unitTorus u)
  have h1 := hscale _ hu
  have h2 := hcong _ hu
  have hpt : torusScale (circleCoords (v - u)) (circleCoords u) = circleCoords v := by
    rw [← circleCoords_add, sub_add_cancel]
  rw [hpt] at h1
  rw [← h1, h2]

/-- **The all-jet level set is the stabilizer coset.**  Two torus points have
the same values of every phase jet exactly when their difference annihilates
every active character. -/
theorem phaseJet_eq_iff_mFourier_eq_one {ρ omega : d → ℝ} (hρ : ∀ j, 0 < ρ j)
    (hindep : RationallyIndependentFrequency omega) {F : (d → ℂ) → ℂ}
    (hF : AnalyticOnNhd ℂ F (polyannulus ρ)) (u v : UnitAddTorus d) :
    (∀ k, phaseJet omega F k (circleCoords u) =
        phaseJet omega F k (circleCoords v)) ↔
      ∀ m ∈ activeSupport F, UnitAddTorus.mFourier m (v - u) = 1 := by
  constructor
  · intro h
    exact mFourier_eq_one_of_eqOn_comp_torusScale hρ
      (eqOn_comp_torusScale_sub_of_phaseJet_eq hρ hindep hF h)
  · intro h
    exact fun k => phaseJet_eq_of_eqOn_comp_torusScale_sub hρ hF
      (eqOn_comp_torusScale_of_mFourier_eq_one hρ hF h) k

end

end GaloisForLFunctions.HTGeometry
