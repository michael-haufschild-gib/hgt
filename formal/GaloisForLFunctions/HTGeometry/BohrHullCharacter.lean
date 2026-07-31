import GaloisForLFunctions.HTGeometry.BohrHullGroup
import GaloisForLFunctions.HTGeometry.BohrConvolution

/-!
# Bohr frequencies are characters of the hull group

Every frequency in the Bohr spectrum of `f` extends from the line to a continuous character of the
Bohr hull of `f`.  The mechanism is the mode-extraction identity

`M_u( f (u + t) · e^{-iμu} ) = e^{iμt} · c_μ(f)`,

whose left-hand side is `1`-Lipschitz in `t` for the translation distance of `f`.  Hence, as soon as
`c_μ(f) ≠ 0`, the exponential `t ↦ e^{iμt}` is Lipschitz for that distance and therefore extends to
the completion.  Multiplicativity and unit modulus pass to the extension by density.

So the compact abelian hull group carries the whole phase of `f`: its character group receives the
frequency module of `f`.
-/

open Filter Topology Metric

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

open HTGeometry

noncomputable section

/-- A function with a totally bounded translation orbit is bounded. -/
theorem exists_norm_le_of_hasTotallyBoundedOrbit {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    (h : HasTotallyBoundedOrbit f) : ∃ C : ℝ, ∀ x : ℝ, ‖f x‖ ≤ C := by
  obtain ⟨S, hSne, hS⟩ := h 1 one_pos
  refine ⟨S.sup' hSne (fun s => ‖f s‖) + 1, fun x => ?_⟩
  obtain ⟨s, hsS, hs⟩ := hS x
  have h0 := hs 0
  rw [zero_add, zero_add] at h0
  have hle : ‖f s‖ ≤ S.sup' hSne (fun s => ‖f s‖) := Finset.le_sup' (fun s => ‖f s‖) hsS
  have : ‖f x‖ ≤ ‖f s‖ + 1 := by
    have := norm_sub_norm_le (f x) (f s)
    linarith [h0, this]
  linarith

/-- An almost-periodic continuous function packaged as a bounded continuous function. -/
def toBC {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) (hcont : Continuous f)
    (h : HasTotallyBoundedOrbit f) : ℝ →ᵇ E :=
  ⟨⟨f, hcont⟩, by
    obtain ⟨C, hC⟩ := exists_norm_le_of_hasTotallyBoundedOrbit h
    refine ⟨2 * C, fun x y => ?_⟩
    calc dist (f x) (f y) ≤ ‖f x‖ + ‖f y‖ := dist_le_norm_add_norm _ _
      _ ≤ C + C := add_le_add (hC x) (hC y)
      _ = 2 * C := by ring⟩

@[simp] theorem toBC_apply {E : Type*} [NormedAddCommGroup E] (f : ℝ → E) (hcont : Continuous f)
    (h : HasTotallyBoundedOrbit f) (x : ℝ) : toBC f hcont h x = f x := rfl

variable {f : ℝ →ᵇ ℂ}

/-- **The mode of `f` at a frequency is Lipschitz for the translation distance.** -/
theorem dist_expChar_mul_bohrCoefficient_le (hfa : HTGeometry.IsBohrAlmostPeriodic (fun x => f x))
    (mu : ℝ) (s t : BohrLine f) :
    ‖expChar mu t.val * bohrCoefficient (fun x => f x) mu
        - expChar mu s.val * bohrCoefficient (fun x => f x) mu‖ ≤ dist s t := by
  have hfc : Continuous (fun x => f x) := f.continuous
  have ht := bohrMean_translate_mul_bohrChar hfc hfa mu t.val
  have hs := bohrMean_translate_mul_bohrChar hfc hfa mu s.val
  rw [← ht, ← hs]
  refine norm_bohrMean_sub_le
    (f := fun u => f (u + t.val) * bohrChar mu u) (g := fun u => f (u + s.val) * bohrChar mu u)
    ((hfc.comp (continuous_id.add continuous_const)).mul (continuous_bohrChar mu))
    (isBohrAlmostPeriodic_mul_bohrChar (hfc.comp (continuous_id.add continuous_const))
      (isBohrAlmostPeriodic_comp_add_const hfa t.val) mu)
    ((hfc.comp (continuous_id.add continuous_const)).mul (continuous_bohrChar mu))
    (isBohrAlmostPeriodic_mul_bohrChar (hfc.comp (continuous_id.add continuous_const))
      (isBohrAlmostPeriodic_comp_add_const hfa s.val) mu) ?_
  intro u
  have hb : ‖(f (u + t.val) : ℂ) * bohrChar mu u - (f (u + s.val) : ℂ) * bohrChar mu u‖
      = ‖(f (u + t.val) : ℂ) - f (u + s.val)‖ := by
    rw [← sub_mul, norm_mul, norm_bohrChar, mul_one]
  rw [hb]
  have hd := BoundedContinuousFunction.dist_coe_le_dist
    (f := translateBC t.val f) (g := translateBC s.val f) u
  rw [translateBC_apply, translateBC_apply, dist_eq_norm] at hd
  rw [BohrLine.dist_eq, dist_comm]
  exact hd

/-- The exponential attached to a Bohr frequency is uniformly continuous for the translation
distance. -/
theorem uniformContinuous_expChar_bohrLine
    (hfa : HTGeometry.IsBohrAlmostPeriodic (fun x => f x)) {mu : ℝ}
    (hmu : bohrCoefficient (fun x => f x) mu ≠ 0) :
    UniformContinuous (fun t : BohrLine f => expChar mu t.val) := by
  set c : ℂ := bohrCoefficient (fun x => f x) mu with hc
  have hcpos : 0 < ‖c‖ := norm_pos_iff.mpr hmu
  refine (LipschitzWith.of_dist_le_mul (K := Real.toNNReal ‖c‖⁻¹) fun s t => ?_).uniformContinuous
  have hkey := dist_expChar_mul_bohrCoefficient_le hfa mu s t
  have hfac : ‖expChar mu t.val * c - expChar mu s.val * c‖
      = ‖expChar mu t.val - expChar mu s.val‖ * ‖c‖ := by
    rw [← sub_mul, norm_mul]
  rw [hfac] at hkey
  have hdist : dist (expChar mu s.val) (expChar mu t.val)
      = ‖expChar mu t.val - expChar mu s.val‖ := by
    rw [dist_eq_norm, norm_sub_rev]
  rw [hdist, Real.coe_toNNReal _ (by positivity)]
  rw [inv_mul_eq_div, le_div_iff₀ hcpos]
  exact hkey

/-- The character of the Bohr hull attached to a frequency. -/
def bohrHullChar (f : ℝ →ᵇ ℂ) (mu : ℝ) : BohrHull f → ℂ :=
  UniformSpace.Completion.extension (fun t : BohrLine f => expChar mu t.val)

@[simp] theorem bohrHullChar_bohrIota (hfa : HTGeometry.IsBohrAlmostPeriodic (fun x => f x))
    {mu : ℝ} (hmu : bohrCoefficient (fun x => f x) mu ≠ 0) (t : ℝ) :
    bohrHullChar f mu (bohrIota f t) = expChar mu t :=
  UniformSpace.Completion.extension_coe (uniformContinuous_expChar_bohrLine hfa hmu)
    (BohrLine.of f t)

theorem continuous_bohrHullChar (f : ℝ →ᵇ ℂ) (mu : ℝ) : Continuous (bohrHullChar f mu) :=
  UniformSpace.Completion.continuous_extension

/-- The extension is multiplicative: it is a character of the hull group. -/
theorem bohrHullChar_add (hfa : HTGeometry.IsBohrAlmostPeriodic (fun x => f x))
    {mu : ℝ} (hmu : bohrCoefficient (fun x => f x) mu ≠ 0) (x y : BohrHull f) :
    bohrHullChar f mu (x + y) = bohrHullChar f mu x * bohrHullChar f mu y := by
  have hcont := continuous_bohrHullChar f mu
  have h1 : Continuous fun p : BohrHull f × BohrHull f => bohrHullChar f mu (p.1 + p.2) :=
    hcont.comp continuous_add
  have h2 : Continuous fun p : BohrHull f × BohrHull f =>
      bohrHullChar f mu p.1 * bohrHullChar f mu p.2 :=
    (hcont.comp continuous_fst).mul (hcont.comp continuous_snd)
  have hdense : Dense (Set.range (bohrIota f) ×ˢ Set.range (bohrIota f)) := by
    have := (denseRange_bohrIota f).prodMap (denseRange_bohrIota f)
    simpa [DenseRange, Prod.map] using this
  have heq : Set.EqOn (fun p : BohrHull f × BohrHull f => bohrHullChar f mu (p.1 + p.2))
      (fun p : BohrHull f × BohrHull f => bohrHullChar f mu p.1 * bohrHullChar f mu p.2)
      (Set.range (bohrIota f) ×ˢ Set.range (bohrIota f)) := by
    rintro ⟨x, y⟩ ⟨⟨s, rfl⟩, ⟨t, rfl⟩⟩
    simp only
    rw [← bohrIota_add, bohrHullChar_bohrIota hfa hmu, bohrHullChar_bohrIota hfa hmu,
      bohrHullChar_bohrIota hfa hmu]
    unfold expChar
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  exact congrFun (Continuous.ext_on hdense h1 h2 heq) (x, y)

@[simp] theorem bohrHullChar_zero (hfa : HTGeometry.IsBohrAlmostPeriodic (fun x => f x))
    {mu : ℝ} (hmu : bohrCoefficient (fun x => f x) mu ≠ 0) :
    bohrHullChar f mu 0 = 1 := by
  have h := bohrHullChar_bohrIota hfa hmu (0 : ℝ)
  rw [bohrIota_zero] at h
  rw [h]
  unfold expChar
  norm_num

/-- The character has unit modulus. -/
theorem norm_bohrHullChar (hfa : HTGeometry.IsBohrAlmostPeriodic (fun x => f x))
    {mu : ℝ} (hmu : bohrCoefficient (fun x => f x) mu ≠ 0) (x : BohrHull f) :
    ‖bohrHullChar f mu x‖ = 1 := by
  have hcont := continuous_bohrHullChar f mu
  have heq : Set.EqOn (fun x : BohrHull f => ‖bohrHullChar f mu x‖) (fun _ : BohrHull f => (1 : ℝ))
      (Set.range (bohrIota f)) := by
    rintro x ⟨t, rfl⟩
    simp only
    rw [bohrHullChar_bohrIota hfa hmu]
    unfold expChar
    exact Complex.norm_exp_ofReal_mul_I _
  exact congrFun (Continuous.ext_on (denseRange_bohrIota f) hcont.norm continuous_const heq) x

end

end GaloisForLFunctions
