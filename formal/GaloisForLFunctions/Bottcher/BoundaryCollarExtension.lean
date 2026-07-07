import GaloisForLFunctions.Bottcher.ArcContinuation

open Complex Metric Set Filter Topology

namespace Bottcher

/-- The midpoint of two distinct unit vectors has modulus `< 1`. -/
theorem norm_midpoint_lt_one {ζ ζ' : ℂ} (hζ : ‖ζ‖ = 1) (hζ' : ‖ζ'‖ = 1) (hne : ζ ≠ ζ') :
    ‖(ζ + ζ') / 2‖ < 1 := by
  have hsub : 0 < ‖ζ - ζ'‖ := by
    rw [norm_pos_iff]; exact sub_ne_zero.mpr hne
  -- parallelogram law: ‖ζ+ζ'‖² + ‖ζ-ζ'‖² = 2‖ζ‖² + 2‖ζ'‖² = 4
  have hpar : ‖ζ + ζ'‖ ^ 2 + ‖ζ - ζ'‖ ^ 2 = 2 * ‖ζ‖ ^ 2 + 2 * ‖ζ'‖ ^ 2 := by
    have := norm_add_sq_real ζ ζ'
    have h2 := norm_sub_sq_real ζ ζ'
    rw [this, h2]; ring
  rw [hζ, hζ'] at hpar
  have hlt : ‖ζ + ζ'‖ ^ 2 < 4 := by nlinarith [hsub, sq_nonneg ‖ζ - ζ'‖]
  have hnn : (0:ℝ) ≤ ‖ζ + ζ'‖ := norm_nonneg _
  have h4 : ‖ζ + ζ'‖ < 2 := by nlinarith [hlt, hnn]
  have h2ne : ‖(2 : ℂ)‖ = 2 := by norm_num
  rw [norm_div, h2ne, div_lt_one (by norm_num : (0:ℝ) < 2)]
  exact h4

/-- **task02 §1 endpoint.** If `h` is holomorphic on the open unit disk and continues holomorphically
across *every* boundary point of the disk, then it extends to a holomorphic function on a strictly
larger disk `ball 0 ρ`, `ρ > 1`. Proof: the continuation charts cover the compact unit circle; a
Lebesgue radius `δ` gives, at each boundary direction, a convex chart; two such charts overlap in a
convex region that dips into the disk (their midpoint has modulus `< 1`), where both equal `h`, so the
identity theorem forces them to agree — the glued function is holomorphic on `ball 0 (1 + δ/2)`. -/
theorem holo_extend_of_continuesAcross_all {h : ℂ → ℂ}
    (hhd : DifferentiableOn ℂ h (ball 0 1))
    (hcont : ∀ ζ : ℂ, ‖ζ‖ = 1 → ContinuesAcross h ζ) :
    ∃ ρ : ℝ, 1 < ρ ∧ ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball 0 ρ) ∧ EqOn H h (ball 0 1) := by
  classical
  -- chart data indexed by the circle subtype
  set S : Set ℂ := sphere (0 : ℂ) 1 with hSdef
  have hmemS : ∀ ζ : S, ‖(ζ : ℂ)‖ = 1 := fun ζ => mem_sphere_zero_iff_norm.mp ζ.2
  -- Uf ζ = chart, Gf ζ = extension
  set Uf : S → Set ℂ := fun ζ => (hcont ζ (hmemS ζ)).choose with hUfdef
  have hUf : ∀ ζ : S, IsOpen (Uf ζ) ∧ (ζ : ℂ) ∈ Uf ζ ∧
      ∃ G : ℂ → ℂ, DifferentiableOn ℂ G (Uf ζ) ∧ Set.EqOn G h (Uf ζ ∩ ball 0 1) := by
    intro ζ; exact (hcont ζ (hmemS ζ)).choose_spec
  set Gf : S → (ℂ → ℂ) := fun ζ => (hUf ζ).2.2.choose with hGfdef
  have hGf : ∀ ζ : S, DifferentiableOn ℂ (Gf ζ) (Uf ζ) ∧
      Set.EqOn (Gf ζ) h (Uf ζ ∩ ball 0 1) := fun ζ => (hUf ζ).2.2.choose_spec
  have hUfopen : ∀ ζ : S, IsOpen (Uf ζ) := fun ζ => (hUf ζ).1
  -- the charts cover the circle
  have hcover : S ⊆ ⋃ ζ : S, Uf ζ := by
    intro x hx
    exact Set.mem_iUnion.mpr ⟨⟨x, hx⟩, (hUf ⟨x, hx⟩).2.1⟩
  -- Lebesgue number
  obtain ⟨δ, hδ, hleb⟩ :=
    lebesgue_number_lemma_of_metric (isCompact_sphere (0 : ℂ) 1) hUfopen hcover
  -- for x on the circle, a chart whose δ-ball contains ball x δ
  set ρ : ℝ := 1 + δ / 2 with hρdef
  have hρ1 : 1 < ρ := by rw [hρdef]; linarith
  -- projection to the circle
  have hproj : ∀ z : ℂ, z ≠ 0 → (z / (‖z‖ : ℂ)) ∈ S := by
    intro z hz
    rw [hSdef, mem_sphere_zero_iff_norm, norm_div]
    simp [div_self (show ‖z‖ ≠ 0 from norm_ne_zero_iff.mpr hz)]
  -- chart index chosen for each circle point
  set ζof : ∀ x : ℂ, x ∈ S → S := fun x hx => (hleb x hx).choose with hζofdef
  have hζof : ∀ (x : ℂ) (hx : x ∈ S), ball x δ ⊆ Uf (ζof x hx) := fun x hx => (hleb x hx).choose_spec
  -- projection of a nonzero z, together with the sphere-membership proof
  set pr : ∀ z : ℂ, z ≠ 0 → S := fun z hz => ⟨z / (‖z‖ : ℂ), hproj z hz⟩ with hprdef
  -- the extension H
  set H : ℂ → ℂ := fun z =>
    if hz1 : ‖z‖ < 1 then h z
    else if hz0 : z = 0 then h z
    else Gf (ζof (pr z hz0) (pr z hz0).2) z with hHdef
  -- norm of the radial gap
  have hcollar_norm : ∀ u : ℂ, u ≠ 0 → ‖u - u / (‖u‖ : ℂ)‖ = |‖u‖ - 1| := by
    intro u hu
    have hun : (‖u‖ : ℂ) ≠ 0 := by
      simpa using (norm_ne_zero_iff.mpr hu)
    have hfac : u - u / (‖u‖ : ℂ) = (((‖u‖ - 1 : ℝ)) : ℂ) * (u / (‖u‖ : ℂ)) := by
      have hcast : (((‖u‖ - 1 : ℝ)) : ℂ) = (‖u‖ : ℂ) - 1 := by push_cast; ring
      rw [hcast]; field_simp
    rw [hfac, norm_mul]
    have h1 : ‖u / (‖u‖ : ℂ)‖ = 1 := by
      rw [norm_div]; simp [div_self (norm_ne_zero_iff.mpr hu)]
    rw [h1, mul_one, Complex.norm_real, Real.norm_eq_abs]
  -- chart agreement: two charts covering `w` agree at `w`
  have hagree : ∀ (x y : ℂ) (hx : x ∈ S) (hy : y ∈ S) (w : ℂ),
      w ∈ ball x δ → w ∈ ball y δ → Gf (ζof x hx) w = Gf (ζof y hy) w := by
    intro x y hx hy w hwx hwy
    by_cases hxy : x = y
    · subst hxy; rfl
    · have hxn : ‖x‖ = 1 := mem_sphere_zero_iff_norm.mp hx
      have hyn : ‖y‖ = 1 := mem_sphere_zero_iff_norm.mp hy
      set O : Set ℂ := ball x δ ∩ ball y δ with hOdef
      have hOopen : IsOpen O := isOpen_ball.inter isOpen_ball
      have hOconv : IsPreconnected O :=
        ((convex_ball x δ).inter (convex_ball y δ)).isPreconnected
      have hOsub1 : O ⊆ Uf (ζof x hx) := fun p hp => hζof x hx hp.1
      have hOsub2 : O ⊆ Uf (ζof y hy) := fun p hp => hζof y hy hp.2
      have hA1 : AnalyticOnNhd ℂ (Gf (ζof x hx)) O :=
        ((hGf (ζof x hx)).1.mono hOsub1).analyticOnNhd hOopen
      have hA2 : AnalyticOnNhd ℂ (Gf (ζof y hy)) O :=
        ((hGf (ζof y hy)).1.mono hOsub2).analyticOnNhd hOopen
      -- balls overlap ⇒ ‖x-y‖ < 2δ
      have hxyd : ‖x - y‖ < 2 * δ := by
        have htri : ‖x - y‖ ≤ ‖x - w‖ + ‖w - y‖ := by
          simpa only [dist_eq_norm] using dist_triangle x w y
        have hwx' : ‖x - w‖ < δ := by
          rw [norm_sub_rev]; simpa [dist_eq_norm] using (mem_ball.mp hwx)
        have hwy' : ‖w - y‖ < δ := by
          simpa [dist_eq_norm] using (mem_ball.mp hwy)
        linarith
      -- midpoint lies in both balls and in the disk
      set m : ℂ := (x + y) / 2 with hmdef
      have hmx : m ∈ ball x δ := by
        rw [mem_ball, dist_eq_norm, hmdef, show (x + y) / 2 - x = (y - x) / 2 by ring,
          norm_div, norm_sub_rev]
        rw [show ‖(2 : ℂ)‖ = 2 by norm_num]; linarith
      have hmy : m ∈ ball y δ := by
        rw [mem_ball, dist_eq_norm, hmdef, show (x + y) / 2 - y = (x - y) / 2 by ring,
          norm_div]
        rw [show ‖(2 : ℂ)‖ = 2 by norm_num]; linarith
      have hm1 : m ∈ ball (0 : ℂ) 1 := by
        rw [mem_ball_zero_iff, hmdef]; exact norm_midpoint_lt_one hxn hyn hxy
      have hev : Gf (ζof x hx) =ᶠ[𝓝 m] Gf (ζof y hy) := by
        have hopen : IsOpen (O ∩ ball 0 1) := hOopen.inter isOpen_ball
        filter_upwards [hopen.mem_nhds ⟨⟨hmx, hmy⟩, hm1⟩] with q hq
        rw [(hGf (ζof x hx)).2 ⟨hOsub1 hq.1, hq.2⟩, (hGf (ζof y hy)).2 ⟨hOsub2 hq.1, hq.2⟩]
      exact hA1.eqOn_of_preconnected_of_eventuallyEq hA2 hOconv ⟨hmx, hmy⟩ hev ⟨hwx, hwy⟩
  refine ⟨ρ, hρ1, H, ?_, ?_⟩
  · -- DifferentiableOn ℂ H (ball 0 ρ)
    intro z hz
    rw [mem_ball_zero_iff] at hz
    apply DifferentiableAt.differentiableWithinAt
    by_cases hz1 : ‖z‖ < 1
    · -- interior of the disk: H = h near z
      have hev : H =ᶠ[𝓝 z] h := by
        have hmem : {w : ℂ | ‖w‖ < 1} ∈ 𝓝 z :=
          (isOpen_lt continuous_norm continuous_const).mem_nhds hz1
        filter_upwards [hmem] with w hw
        simp only [hHdef, dif_pos hw]
      have hdh : DifferentiableAt ℂ h z :=
        hhd.differentiableAt (isOpen_ball.mem_nhds (mem_ball_zero_iff.mpr hz1))
      exact hdh.congr_of_eventuallyEq hev
    · -- collar: 1 ≤ ‖z‖ < ρ
      push Not at hz1
      have hz0 : z ≠ 0 := by rintro rfl; rw [norm_zero] at hz1; linarith
      have hx₀S : z / (‖z‖ : ℂ) ∈ S := hproj z hz0
      -- z lies in its own δ-chart
      have hzx₀ : z ∈ ball (z / (‖z‖ : ℂ)) δ := by
        rw [mem_ball, dist_eq_norm, hcollar_norm z hz0, abs_of_nonneg (by linarith : (0:ℝ) ≤ ‖z‖ - 1)]
        rw [hρdef] at hz; linarith
      set ζ₀ := ζof (z / (‖z‖ : ℂ)) hx₀S with hζ₀def
      have hev : H =ᶠ[𝓝 z] Gf ζ₀ := by
        filter_upwards [isOpen_ball.mem_nhds hzx₀] with w hw
        by_cases hw1 : ‖w‖ < 1
        · simp only [hHdef, dif_pos hw1]
          exact ((hGf ζ₀).2 ⟨hζof _ hx₀S hw, mem_ball_zero_iff.mpr hw1⟩).symm
        · have hw0 : w ≠ 0 := by rintro rfl; rw [norm_zero] at hw1; exact hw1 (by norm_num)
          simp only [hHdef, dif_neg hw1, dif_neg hw0]
          -- w lies in its own δ-chart
          have hwlt : ‖w‖ < 1 + δ := by
            have hins : ‖w‖ ≤ ‖z / (‖z‖ : ℂ)‖ + ‖z / (‖z‖ : ℂ) - w‖ := norm_le_insert _ _
            rw [mem_sphere_zero_iff_norm.mp hx₀S] at hins
            have hwd : ‖z / (‖z‖ : ℂ) - w‖ < δ := by
              rw [norm_sub_rev]; simpa [dist_eq_norm] using (mem_ball.mp hw)
            linarith
          have hwx₀' : w ∈ ball (w / (‖w‖ : ℂ)) δ := by
            push Not at hw1
            rw [mem_ball, dist_eq_norm, hcollar_norm w hw0,
              abs_of_nonneg (by linarith : (0:ℝ) ≤ ‖w‖ - 1)]
            linarith
          exact hagree (w / (‖w‖ : ℂ)) (z / (‖z‖ : ℂ)) (hproj w hw0) hx₀S w hwx₀' hw
      have hdζ₀ : DifferentiableAt ℂ (Gf ζ₀) z :=
        (hGf ζ₀).1.differentiableAt ((hUfopen ζ₀).mem_nhds (hζof _ hx₀S hzx₀))
      exact hdζ₀.congr_of_eventuallyEq hev
  · -- EqOn H h (ball 0 1)
    intro z hz
    rw [mem_ball_zero_iff] at hz
    simp only [hHdef, dif_pos hz]

/-- **Iterated doubling of a boundary continuation.** If `h` solves the Böttcher functional equation on
the disk and continues across a boundary point `ζ` (with `|ζ| = 1`), then it continues across every
dyadic power `ζ^{2ⁿ}`. Immediate induction on `n` from `continuesAcross_sq`. -/
theorem continuesAcross_pow_two_iter {h : ℂ → ℂ} {c : ℂ} {ζ : ℂ} (hζ : ‖ζ‖ = 1)
    (hfe : ∀ t ∈ ball (0 : ℂ) 1, h (t ^ 2) = (h t) ^ 2 + c * t ^ 2)
    (hcont : ContinuesAcross h ζ) (n : ℕ) :
    ContinuesAcross h (ζ ^ (2 ^ n)) := by
  induction n with
  | zero => simpa using hcont
  | succ k ih =>
    have hnorm : ‖ζ ^ (2 ^ k)‖ = 1 := by rw [norm_pow, hζ, one_pow]
    have hstep := continuesAcross_sq hnorm hfe ih
    have he : (ζ ^ (2 ^ k)) ^ 2 = ζ ^ (2 ^ (k + 1)) := by rw [← pow_mul, pow_succ]
    rwa [he] at hstep

/-- **task02 §1, packaged.** If `h` is holomorphic on the unit disk, solves the Böttcher functional
equation there, and continues across every point of a boundary set `A` whose dyadic-doubling orbit
covers the whole circle (`hgen`), then `h` extends holomorphically to a strictly larger disk. This
isolates the sole remaining geometric input of §1 as the elementary combinatorial fact `hgen` — a
positive-length arc's doubling orbit fills the circle — decoupled from all the analytic content
(heart `continuesAcross_sq`, iteration `continuesAcross_pow_two_iter`, and glue
`holo_extend_of_continuesAcross_all`). -/
theorem holo_extend_of_continuesAcross_generating {h : ℂ → ℂ} {c : ℂ} {A : Set ℂ}
    (hhd : DifferentiableOn ℂ h (ball 0 1))
    (hfe : ∀ t ∈ ball (0 : ℂ) 1, h (t ^ 2) = (h t) ^ 2 + c * t ^ 2)
    (hA : ∀ ζ ∈ A, ‖ζ‖ = 1 ∧ ContinuesAcross h ζ)
    (hgen : ∀ ζ : ℂ, ‖ζ‖ = 1 → ∃ ζ' ∈ A, ∃ n : ℕ, ζ = ζ' ^ (2 ^ n)) :
    ∃ ρ : ℝ, 1 < ρ ∧ ∃ H : ℂ → ℂ, DifferentiableOn ℂ H (ball 0 ρ) ∧ EqOn H h (ball 0 1) := by
  refine holo_extend_of_continuesAcross_all hhd ?_
  intro ζ hζ
  obtain ⟨ζ', hζ'A, n, rfl⟩ := hgen ζ hζ
  obtain ⟨hζ'1, hζ'cont⟩ := hA ζ' hζ'A
  exact continuesAcross_pow_two_iter hζ'1 hfe hζ'cont n

end Bottcher
