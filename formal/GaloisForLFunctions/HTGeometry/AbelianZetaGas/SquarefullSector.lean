import GaloisForLFunctions.HTGeometry.AbelianZetaGas.ModeExpectation

/-!
# The depth-tail sectors of the gas

Restricting the gas to the modes of depth at least `g` and reading them through the canonical
reindexing `(p,j) ↦ (p, j+g-1)` produces the gas again, at the socle fugacity raised by `(g−1)σ`.
For `g = 2` this is the squarefull sector of Theorem 5.1: above the wall `σ = 1/2` the shifted
parameters lie in the convergence chamber, so the squarefull part of the gas is itself an honest
almost surely finite random abelian group, with partition function `∏_{j≥2} ζ(jσ)`.
-/

namespace GaloisForLFunctions.HTGeometry

namespace AbelianZetaParameters

/-- Raising the depth of every mode by `n` is the socle-fugacity shift `τ ↦ τ + n·σ`. -/
def depthShiftBy (θ : AbelianZetaParameters) (n : ℕ) : AbelianZetaParameters where
  sigma := θ.sigma
  tau := θ.tau + (n : ℝ) * θ.sigma
  sigma_pos := θ.sigma_pos
  tau_nonneg := by
    have h1 := θ.tau_nonneg
    have h2 := θ.sigma_pos
    have h3 : (0 : ℝ) ≤ (n : ℝ) * θ.sigma := by positivity
    linarith

@[simp] theorem depthShiftBy_sigma (θ : AbelianZetaParameters) (n : ℕ) :
    (θ.depthShiftBy n).sigma = θ.sigma := rfl

@[simp] theorem depthShiftBy_tau (θ : AbelianZetaParameters) (n : ℕ) :
    (θ.depthShiftBy n).tau = θ.tau + (n : ℝ) * θ.sigma := rfl

/-- **The depth shift is the fugacity shift, mode by mode.** -/
theorem ratio_depthShiftBy (θ : AbelianZetaParameters) (n : ℕ) (m : AbelianZetaMode) :
    θ.ratio (m.1, m.2 + n) = (θ.depthShiftBy n).ratio m := by
  rw [ratio, ratio, exponent, exponent]
  congr 2
  simp only [AbelianZetaMode.depth, depthShiftBy_sigma, depthShiftBy_tau]
  push_cast
  ring

theorem success_depthShiftBy (θ : AbelianZetaParameters) (n : ℕ) (m : AbelianZetaMode) :
    θ.success (m.1, m.2 + n) = (θ.depthShiftBy n).success m := by
  refine Subtype.ext ?_
  show 1 - θ.ratio (m.1, m.2 + n) = 1 - (θ.depthShiftBy n).ratio m
  rw [ratio_depthShiftBy]

theorem modeLaw_depthShiftBy (θ : AbelianZetaParameters) (n : ℕ) (m : AbelianZetaMode) :
    θ.modeLaw (m.1, m.2 + n) = (θ.depthShiftBy n).modeLaw m := by
  rw [modeLaw, modeLaw, success_depthShiftBy]

end AbelianZetaParameters

/-! ## The depth-tail marginal -/

theorem tailEquiv_apply {g : ℕ} (hg : 1 ≤ g) (m : AbelianZetaMode) :
    ((abelianZetaTailModeEquiv g hg m : {m : AbelianZetaMode // g ≤ AbelianZetaMode.depth m})
      : AbelianZetaMode) = (m.1, m.2 + (g - 1)) := rfl

theorem gasMeasure_map_restrict_depthTail (θ : AbelianZetaParameters) (g : ℕ) :
    θ.gasMeasure.map (Set.restrict ({m : AbelianZetaMode | g ≤ AbelianZetaMode.depth m}))
      = MeasureTheory.Measure.infinitePi (fun i : {m : AbelianZetaMode | g ≤ AbelianZetaMode.depth m} => θ.modeLaw i) := by
  rw [AbelianZetaParameters.gasMeasure]
  exact MeasureTheory.Measure.infinitePi_map_restrict' (μ := θ.modeLaw)

/-- **The depth-tail marginal of the gas is the gas at the shifted fugacity.**  Reading the modes
of depth at least `g` through `(p,j) ↦ (p, j+g-1)` reproduces the gas at `τ + (g−1)σ`. -/
theorem gasMeasure_map_depthTail (θ : AbelianZetaParameters) {g : ℕ} (hg : 1 ≤ g) :
    θ.gasMeasure.map (fun k : AbelianZetaMode → ℕ =>
        fun m : AbelianZetaMode => k (m.1, m.2 + (g - 1)))
      = (θ.depthShiftBy (g - 1)).gasMeasure := by
  classical
  set e := abelianZetaTailModeEquiv g hg with he
  have hcongr := MeasureTheory.Measure.infinitePi_map_piCongrLeft
    (μ := fun i : {m : AbelianZetaMode | g ≤ AbelianZetaMode.depth m} => θ.modeLaw i) e
  have hmeasE : Measurable
      (MeasurableEquiv.piCongrLeft (fun _ : {m : AbelianZetaMode | g ≤ AbelianZetaMode.depth m} => ℕ) e) :=
    (MeasurableEquiv.piCongrLeft (fun _ : {m : AbelianZetaMode | g ≤ AbelianZetaMode.depth m} => ℕ) e).measurable
  have hmeasBack : Measurable
      (fun x : ({m : AbelianZetaMode | g ≤ AbelianZetaMode.depth m}) → ℕ => fun m : AbelianZetaMode => x (e m)) := by
    fun_prop
  have hback : (MeasureTheory.Measure.infinitePi
        (fun i : {m : AbelianZetaMode | g ≤ AbelianZetaMode.depth m} => θ.modeLaw i)).map
      (fun x : ({m : AbelianZetaMode | g ≤ AbelianZetaMode.depth m}) → ℕ => fun m : AbelianZetaMode => x (e m))
      = MeasureTheory.Measure.infinitePi
        (fun i : AbelianZetaMode => θ.modeLaw ((e i : AbelianZetaMode))) := by
    rw [← hcongr, MeasureTheory.Measure.map_map hmeasBack hmeasE]
    have hid : ((fun x : ({m : AbelianZetaMode | g ≤ AbelianZetaMode.depth m}) → ℕ => fun m : AbelianZetaMode => x (e m))
        ∘ (MeasurableEquiv.piCongrLeft (fun _ : {m : AbelianZetaMode | g ≤ AbelianZetaMode.depth m} => ℕ) e)) = id := by
      funext y m
      show (MeasurableEquiv.piCongrLeft (fun _ : {m : AbelianZetaMode | g ≤ AbelianZetaMode.depth m} => ℕ) e) y (e m) = y m
      rw [MeasurableEquiv.coe_piCongrLeft, Equiv.piCongrLeft_apply_apply]
    rw [hid, MeasureTheory.Measure.map_id]
  have hfin : MeasureTheory.Measure.infinitePi
        (fun i : AbelianZetaMode => θ.modeLaw ((e i : AbelianZetaMode)))
      = (θ.depthShiftBy (g - 1)).gasMeasure := by
    rw [AbelianZetaParameters.gasMeasure]
    congr 1
    funext m
    rw [tailEquiv_apply hg m]
    exact θ.modeLaw_depthShiftBy (g - 1) m
  have hsplit : (fun k : AbelianZetaMode → ℕ =>
        fun m : AbelianZetaMode => k (m.1, m.2 + (g - 1)))
      = (fun x : ({m : AbelianZetaMode | g ≤ AbelianZetaMode.depth m}) → ℕ => fun m : AbelianZetaMode => x (e m))
        ∘ Set.restrict ({m : AbelianZetaMode | g ≤ AbelianZetaMode.depth m}) := rfl
  rw [hsplit, ← MeasureTheory.Measure.map_map (by fun_prop) (by fun_prop),
    gasMeasure_map_restrict_depthTail θ g, hback, hfin]

end GaloisForLFunctions.HTGeometry
