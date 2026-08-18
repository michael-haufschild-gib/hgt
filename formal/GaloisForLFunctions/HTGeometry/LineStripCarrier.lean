import GaloisForLFunctions.HTGeometry.BohrHullComparison
import GaloisForLFunctions.HTGeometry.StripThreeLinesTransfer
import GaloisForLFunctions.HTGeometry.StripTranslateCurve
import GaloisForLFunctions.HTGeometry.JetSampleAtlas

/-!
# The line carrier embeds in the strip carrier

The translation distance measured on the central line is dominated by the one measured on a
substrip — the line sits inside the substrip — and dominates it by the three-line theorem.  So the
identity of the line extends to carrier maps in both directions, which compose to the identity on a
dense set; in particular the map from the line carrier to the strip carrier is a continuous
injection.

That is what lets a jet atlas built on the strip carrier, where the points are holomorphic functions
and jets make sense, bound the rational frequency rank of the line restriction, where the frequency
group lives.
-/

open Filter Topology Metric Set

open scoped BoundedContinuousFunction

namespace GaloisForLFunctions

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
variable {F : ℂ → E} {σ R r r' M : ℝ}

theorem mem_closedStrip_center (σ r : ℝ) (hr : 0 ≤ r) : ((σ : ℂ)) ∈ closedStrip σ r := by
  show |((σ : ℂ)).re - σ| ≤ r
  simp [hr]

omit [NormedSpace ℂ E] [CompleteSpace E] in
/-- The line translation distance is dominated by the strip translation distance. -/
theorem dist_line_le_dist_strip (hr : 0 ≤ r)
    {f : ℝ →ᵇ E} (hf : ∀ x : ℝ, f x = F ((σ : ℂ) + (x : ℂ) * Complex.I))
    {Gb : ℝ →ᵇ ((closedStrip σ r) →ᵇ E)}
    (hGb : ∀ (τ : ℝ) (z : closedStrip σ r), Gb τ z = F ((z : ℂ) + (τ : ℂ) * Complex.I))
    (s t : ℝ) :
    dist (translateBC s f) (translateBC t f) ≤ dist (translateBC s Gb) (translateBC t Gb) := by
  refine (BoundedContinuousFunction.dist_le dist_nonneg).mpr fun x => ?_
  set z₀ : closedStrip σ r := ⟨(σ : ℂ), mem_closedStrip_center σ r hr⟩ with hz₀
  have hval : ∀ u : ℝ, f u = Gb u z₀ := by
    intro u
    rw [hf u, hGb u z₀, hz₀]
  have h1 : translateBC s f x = Gb (x + s) z₀ := by
    show f (x + s) = Gb (x + s) z₀
    exact hval (x + s)
  have h2 : translateBC t f x = Gb (x + t) z₀ := by
    show f (x + t) = Gb (x + t) z₀
    exact hval (x + t)
  rw [h1, h2]
  calc dist (Gb (x + s) z₀) (Gb (x + t) z₀) ≤ dist (Gb (x + s)) (Gb (x + t)) :=
        BoundedContinuousFunction.dist_coe_le_dist _
    _ ≤ dist (translateBC s Gb) (translateBC t Gb) := by
        have h := BoundedContinuousFunction.dist_coe_le_dist
          (f := translateBC s Gb) (g := translateBC t Gb) x
        simpa using h

/-- **The strip translation distance is controlled by the line translation distance**, by three
lines. -/
theorem dist_strip_lt_of_dist_line_lt (hr0 : 0 ≤ r) (hrr' : r < r') (hr'R : r' < R)
    (hMpos : 0 < M) (hF : DifferentiableOn ℂ F (verticalStrip σ R))
    (hbound : ∀ z ∈ closedStrip σ r', ‖F z‖ ≤ M)
    {f : ℝ →ᵇ E} (hf : ∀ x : ℝ, f x = F ((σ : ℂ) + (x : ℂ) * Complex.I))
    {Gb : ℝ →ᵇ ((closedStrip σ r) →ᵇ E)}
    (hGb : ∀ (τ : ℝ) (z : closedStrip σ r), Gb τ z = F ((z : ℂ) + (τ : ℂ) * Complex.I)) :
    ∀ ε : ℝ, 0 < ε → ∃ δ : ℝ, 0 < δ ∧ ∀ s t : ℝ,
      dist (translateBC s f) (translateBC t f) < δ →
        dist (translateBC s Gb) (translateBC t Gb) < ε := by
  intro ε hε
  obtain ⟨δ, hδpos, hδ⟩ :=
    exists_delta_strip_of_line hr0 hrr' hr'R hMpos hF hbound (ε / 2) (by linarith)
  refine ⟨δ, hδpos, fun s t hst => ?_⟩
  have hline : ∀ x : ℝ, ‖F ((σ : ℂ) + ((x + s : ℝ) : ℂ) * Complex.I)
      - F ((σ : ℂ) + ((x + t : ℝ) : ℂ) * Complex.I)‖ ≤ δ := by
    intro x
    have h := BoundedContinuousFunction.dist_coe_le_dist
      (f := translateBC s f) (g := translateBC t f) x
    have hval1 : translateBC s f x = F ((σ : ℂ) + ((x + s : ℝ) : ℂ) * Complex.I) := by
      show f (x + s) = _
      exact hf (x + s)
    have hval2 : translateBC t f x = F ((σ : ℂ) + ((x + t : ℝ) : ℂ) * Complex.I) := by
      show f (x + t) = _
      exact hf (x + t)
    rw [hval1, hval2] at h
    rw [← dist_eq_norm]
    exact le_trans h (le_of_lt hst)
  have hstrip := hδ s t hline
  have hbdd : dist (translateBC s Gb) (translateBC t Gb) ≤ ε / 2 := by
    refine (BoundedContinuousFunction.dist_le (by linarith)).mpr fun x => ?_
    refine (BoundedContinuousFunction.dist_le (by linarith)).mpr fun z => ?_
    have hval1 : (translateBC s Gb) x z = F ((z : ℂ) + ((x + s : ℝ) : ℂ) * Complex.I) := by
      show Gb (x + s) z = _
      exact hGb (x + s) z
    have hval2 : (translateBC t Gb) x z = F ((z : ℂ) + ((x + t : ℝ) : ℂ) * Complex.I) := by
      show Gb (x + t) z = _
      exact hGb (x + t) z
    rw [hval1, hval2, dist_eq_norm]
    have hz : ((z : ℂ) + (x : ℂ) * Complex.I) ∈ closedStrip σ r :=
      mem_closedStrip_add_I σ r (z : ℂ) z.2 x
    have h := hstrip _ hz
    have hrw1 : ((z : ℂ) + (x : ℂ) * Complex.I) + (s : ℂ) * Complex.I
        = (z : ℂ) + ((x + s : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    have hrw2 : ((z : ℂ) + (x : ℂ) * Complex.I) + (t : ℂ) * Complex.I
        = (z : ℂ) + ((x + t : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring
    rw [hrw1, hrw2] at h
    exact h
  linarith

/-- **The line carrier embeds in the strip carrier.** -/
theorem exists_injective_line_to_strip (hr0 : 0 ≤ r) (hrr' : r < r') (hr'R : r' < R)
    (hMpos : 0 < M) (hF : DifferentiableOn ℂ F (verticalStrip σ R))
    (hbound : ∀ z ∈ closedStrip σ r', ‖F z‖ ≤ M)
    {f : ℝ →ᵇ E} (hf : ∀ x : ℝ, f x = F ((σ : ℂ) + (x : ℂ) * Complex.I))
    {Gb : ℝ →ᵇ ((closedStrip σ r) →ᵇ E)}
    (hGb : ∀ (τ : ℝ) (z : closedStrip σ r), Gb τ z = F ((z : ℂ) + (τ : ℂ) * Complex.I)) :
    ∃ ν : BohrHull f → BohrHull Gb, Continuous ν ∧ Function.Injective ν ∧
      ∀ t : ℝ, ν (bohrIota f t) = bohrIota Gb t := by
  obtain ⟨ν, hνcont, hνι⟩ := exists_hull_map
    (f := Gb) (g := f) (dist_strip_lt_of_dist_line_lt hr0 hrr' hr'R hMpos hF hbound hf hGb)
  obtain ⟨μ, hμcont, hμι⟩ := exists_hull_map (f := f) (g := Gb)
    (fun ε hε => ⟨ε, hε, fun s t hst =>
      lt_of_le_of_lt (dist_line_le_dist_strip hr0 hf hGb s t) hst⟩)
  exact ⟨ν, hνcont, injective_of_hull_maps hμcont hμι hνcont hνι, hνι⟩

/-- **A separating jet atlas on the strip carrier bounds the frequency rank of the line
restriction.** -/
theorem rank_le_of_strip_jetAtlas {F : ℂ → ℂ} (hr0 : 0 ≤ r) (hrr' : r < r') (hr'R : r' < R)
    (hMpos : 0 < M) (hF : DifferentiableOn ℂ F (verticalStrip σ R))
    (hbound : ∀ z ∈ closedStrip σ r', ‖F z‖ ≤ M)
    {f : ℝ →ᵇ ℂ} (hf : ∀ x : ℝ, f x = F ((σ : ℂ) + (x : ℂ) * Complex.I))
    (hfu : UniformContinuous (fun x => f x)) (hftb : HasTotallyBoundedOrbit (fun x => f x))
    [MeasurableSpace (BohrHull f)] [BorelSpace (BohrHull f)]
    {Gb : ℝ →ᵇ ((closedStrip σ r) →ᵇ ℂ)}
    (hGb : ∀ (τ : ℝ) (z : closedStrip σ r), Gb τ z = F ((z : ℂ) + (τ : ℂ) * Complex.I))
    {T : Finset ℝ} {N : ℕ} {J : ℝ → BohrHull Gb → (Fin N → ℂ)} {U : ℝ → Set (BohrHull Gb)}
    (hJcont : ∀ t, Continuous (J t)) (hcov : ∀ y : BohrHull Gb, ∃ t ∈ T, y ∈ U t)
    (hsep : ∀ (t : ℝ) (x y : BohrHull Gb), x ∈ U t → J t x = J t y → x = y) :
    Module.rank ℤ (bohrHullFrequencies f) ≤ ((2 * (T.card * N) : ℕ) : Cardinal) := by
  obtain ⟨ν, hνcont, hνinj, -⟩ :=
    exists_injective_line_to_strip hr0 hrr' hr'R hMpos hF hbound hf hGb
  refine rank_le_of_jetAtlas hfu hftb (J := fun t x => J t (ν x)) (U := fun t => ν ⁻¹' (U t))
    (fun t => (hJcont t).comp hνcont) (fun x => ?_) (fun t x y hx hxy => ?_)
  · obtain ⟨t, htT, htU⟩ := hcov (ν x)
    exact ⟨t, htT, htU⟩
  · exact hνinj (hsep t (ν x) (ν y) hx hxy)

end GaloisForLFunctions
