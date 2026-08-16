import GaloisForLFunctions.RHTower.SuzukiCoalescingParityLocking

/-!
# Boundary-layer schedules for the coalescing defect

A shift that enters the ground pole as the anchor collapses produces parity energies with a pole in
the collapse parameter.  Writing `t` for the squared anchor, the two admissible boundary layers are

* an **odd-leading** floor, where the odd energy carries the pole `O(t) = B/(ρ t) + O(1)` and the
  even energy stays bounded, and
* an **even-leading** floor, where the even energy stays bounded and the odd energy vanishes
  linearly, `O(t) = t(D + B/ρ) + O(t²)`.

In both cases the oriented defect divided by `2t` has a finite limit, because

`1 + κ = 2E/(E+O)`,   `1 - κ = 2O/(E+O)`

for `κ = (E-O)/(E+O)`.  The limits are the two boundary coefficients

`(ρC + A)/B`   and   `(Dρ + B)/(Cρ + A)`,

the first affine and strictly increasing in `ρ`, the second fractional-linear with the literal
ground endpoint `B/A` at `ρ = 0` and the reduced-resolvent endpoint `D/C` at `ρ = ∞`.  Each is
therefore invertible at a prescribed source value, with an explicit positive root exactly when the
source value lies on the right side of the corresponding endpoint.
-/

open Filter Topology

noncomputable section

namespace RHTower

open GaloisForLFunctions.RHTower

/-! ## The two boundary-layer limits -/

/-- **The odd-leading boundary layer.**  If the odd energy has a simple pole in the collapse
parameter and the even energy converges, the reversed oriented defect has the finite limit
`E-coefficient / O-pole-residue`. -/
theorem tendsto_suzukiDefectAngle_boundaryLayer_odd
    {E O : ℝ → ℝ} {Ecoef Ocoef : ℝ}
    (hE : Tendsto E (𝓝[>] (0 : ℝ)) (𝓝 Ecoef))
    (hO : Tendsto (fun t : ℝ => t * O t) (𝓝[>] (0 : ℝ)) (𝓝 Ocoef))
    (hOne : Ocoef ≠ 0)
    (hsum : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), E t + O t ≠ 0) :
    Tendsto (fun t : ℝ => (1 + suzukiDefectAngle (E t) (O t)) / (2 * t))
      (𝓝[>] (0 : ℝ)) (𝓝 (Ecoef / Ocoef)) := by
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hden : Tendsto (fun t : ℝ => t * E t + t * O t) (𝓝[>] (0 : ℝ)) (𝓝 Ocoef) := by
    have h1 : Tendsto (fun t : ℝ => t * E t) (𝓝[>] (0 : ℝ)) (𝓝 0) := by
      simpa using hid.mul hE
    simpa using h1.add hO
  have hlim := hE.div hden hOne
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hsum] with t ht hne
  have htne : t ≠ 0 := ne_of_gt ht
  simp only [Pi.div_apply, suzukiDefectAngle]
  field_simp
  ring

/-- **The even-leading boundary layer.**  If the even energy converges to a nonzero limit and the
odd energy vanishes linearly, the oriented defect has the finite limit
`O-linear-coefficient / E-coefficient`. -/
theorem tendsto_suzukiDefectAngle_boundaryLayer_even
    {E O : ℝ → ℝ} {Ecoef Ocoef : ℝ}
    (hE : Tendsto E (𝓝[>] (0 : ℝ)) (𝓝 Ecoef))
    (hEne : Ecoef ≠ 0)
    (hO : Tendsto (fun t : ℝ => O t / t) (𝓝[>] (0 : ℝ)) (𝓝 Ocoef))
    (hsum : ∀ᶠ t : ℝ in 𝓝[>] (0 : ℝ), E t + O t ≠ 0) :
    Tendsto (fun t : ℝ => (1 - suzukiDefectAngle (E t) (O t)) / (2 * t))
      (𝓝[>] (0 : ℝ)) (𝓝 (Ocoef / Ecoef)) := by
  have hid : Tendsto (fun t : ℝ => t) (𝓝[>] (0 : ℝ)) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hOzero : Tendsto O (𝓝[>] (0 : ℝ)) (𝓝 0) := by
    have h := hid.mul hO
    rw [zero_mul] at h
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with t ht
    have htne : t ≠ 0 := ne_of_gt ht
    field_simp
  have hden : Tendsto (fun t : ℝ => E t + O t) (𝓝[>] (0 : ℝ)) (𝓝 Ecoef) := by
    simpa using hE.add hOzero
  have hlim := hO.div hden hEne
  refine hlim.congr' ?_
  filter_upwards [self_mem_nhdsWithin, hsum] with t ht hne
  have htne : t ≠ 0 := ne_of_gt ht
  simp only [Pi.div_apply, suzukiDefectAngle]
  field_simp
  ring

/-! ## The odd-leading coefficient is affine and strictly increasing -/

/-- The odd-leading boundary coefficient `(ρC + A)/B`. -/
def oddBoundaryCoefficient (C A B ρ : ℝ) : ℝ := (ρ * C + A) / B

theorem strictMono_oddBoundaryCoefficient {C A B : ℝ} (hC : 0 < C) (hB : 0 < B) :
    StrictMono (oddBoundaryCoefficient C A B) := by
  intro x y hxy
  rw [oddBoundaryCoefficient, oddBoundaryCoefficient, div_lt_div_iff_of_pos_right hB]
  nlinarith

/-- **The odd-leading schedule root.**  The affine coefficient meets a prescribed source value at
exactly one shift rate, given explicitly. -/
theorem oddBoundaryCoefficient_eq_iff {C A B τ ρ : ℝ} (hC : 0 < C) (hB : 0 < B) :
    oddBoundaryCoefficient C A B ρ = τ ↔ ρ = (B * τ - A) / C := by
  rw [oddBoundaryCoefficient, div_eq_iff hB.ne']
  constructor
  · intro h
    field_simp
    linarith
  · intro h
    rw [h]
    field_simp
    ring

/-- The odd-leading schedule root is positive exactly when the source value clears the literal
ground ratio. -/
theorem oddBoundaryCoefficient_root_pos_iff {C A B τ : ℝ} (hC : 0 < C) :
    0 < (B * τ - A) / C ↔ A < B * τ := by
  rw [div_pos_iff]
  constructor
  · rintro (⟨h1, _⟩ | ⟨_, h2⟩)
    · linarith
    · exact absurd h2 (not_lt.2 hC.le)
  · intro h
    exact Or.inl ⟨by linarith, hC⟩

/-! ## The even-leading coefficient is fractional-linear -/

/-- The even-leading boundary coefficient `(Dρ + B)/(Cρ + A)`. -/
def evenBoundaryCoefficient (D B C A ρ : ℝ) : ℝ := (D * ρ + B) / (C * ρ + A)

/-- At zero shift rate the even-leading coefficient is the literal ground ratio. -/
@[simp] theorem evenBoundaryCoefficient_zero (D B C A : ℝ) :
    evenBoundaryCoefficient D B C A 0 = B / A := by
  rw [evenBoundaryCoefficient]
  ring_nf

/-- At infinite shift rate the even-leading coefficient is the reduced-resolvent ratio. -/
theorem tendsto_evenBoundaryCoefficient_atTop {D B C A : ℝ} (hC : 0 < C) (hA : 0 < A) :
    Tendsto (evenBoundaryCoefficient D B C A) atTop (𝓝 (D / C)) := by
  have hBdiv : Tendsto (fun ρ : ℝ => B / ρ) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id
  have hAdiv : Tendsto (fun ρ : ℝ => A / ρ) atTop (𝓝 0) :=
    Filter.Tendsto.div_atTop tendsto_const_nhds Filter.tendsto_id
  have hnum : Tendsto (fun ρ : ℝ => D + B / ρ) atTop (𝓝 D) := by
    simpa using tendsto_const_nhds.add hBdiv
  have hden : Tendsto (fun ρ : ℝ => C + A / ρ) atTop (𝓝 C) := by
    simpa using tendsto_const_nhds.add hAdiv
  have hlim := hnum.div hden hC.ne'
  refine hlim.congr' ?_
  filter_upwards [eventually_gt_atTop (0 : ℝ)] with ρ hρ
  have hρne : ρ ≠ 0 := ne_of_gt hρ
  have hpos : 0 < C * ρ + A := by positivity
  simp only [Pi.div_apply, evenBoundaryCoefficient]
  field_simp

/-- **The even-leading schedule root.**  When the source value lies strictly between the literal
ground endpoint `B/A` and the reduced-resolvent endpoint `D/C`, the fractional-linear coefficient
meets it at an explicit positive shift rate. -/
theorem evenBoundaryCoefficient_root {D B C A τ : ℝ} (hC : 0 < C) (hA : 0 < A)
    (hlow : B / A < τ) (hhigh : τ < D / C) :
    0 < (τ * A - B) / (D - τ * C) ∧
      evenBoundaryCoefficient D B C A ((τ * A - B) / (D - τ * C)) = τ := by
  have h1 : B < τ * A := by
    rw [div_lt_iff₀ hA] at hlow
    linarith
  have h2 : τ * C < D := by
    rw [lt_div_iff₀ hC] at hhigh
    linarith
  have hρ : 0 < (τ * A - B) / (D - τ * C) := div_pos (by linarith) (by linarith)
  refine ⟨hρ, ?_⟩
  have hden : 0 < C * ((τ * A - B) / (D - τ * C)) + A := by positivity
  have hDτ : D - τ * C ≠ 0 := by linarith
  rw [evenBoundaryCoefficient, div_eq_iff hden.ne']
  field_simp
  ring

/-- **Strict monotonicity of the fractional-linear coefficient.**  On the nonnegative axis the sign
of `D A - B C` decides the direction, so the coefficient sweeps the interval between its two
endpoints injectively. -/
theorem strictMonoOn_evenBoundaryCoefficient {D B C A : ℝ} (hC : 0 < C) (hA : 0 < A)
    (hsign : B * C < D * A) :
    StrictMonoOn (evenBoundaryCoefficient D B C A) (Set.Ici (0 : ℝ)) := by
  intro x hx y hy hxy
  have hx0 : (0 : ℝ) ≤ x := hx
  have hy0 : (0 : ℝ) ≤ y := hy
  have hdx : 0 < C * x + A := by positivity
  have hdy : 0 < C * y + A := by positivity
  rw [evenBoundaryCoefficient, evenBoundaryCoefficient, div_lt_div_iff₀ hdx hdy]
  nlinarith

end RHTower
