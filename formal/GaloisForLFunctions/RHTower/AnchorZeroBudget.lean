/-
The zero budget of the anchored disc: what the anchor face owes the Jensen tier.

The Jensen-quotient face of the window certificates caps the carrier's zero count in the
anchored inner disc at one.  Consequently: a second carrier zero in the inner disc refutes
the face triple (center floor, sphere sup, quotient), and — since every sign bracket of the
real completed carrier on the line produces a carrier zero between its endpoints — two
strict sign brackets in disjoint line subintervals of the inner disc refute it as well.
An anchor floor at height `τ` is therefore admissible only at radii containing at most one
sign change of the completed carrier: the anchor face and the disc radius are coupled to
the carrier's on-line oscillation scale, and any anchor supplier must certify its floor at
a radius below the local sign-change spacing.
-/
import GaloisForLFunctions.RHTower.JensenCount
import GaloisForLFunctions.RHTower.ArchWinding

open Complex Metric

namespace RHTower

/-- A sign bracket of the real completed carrier yields an on-line zero of the finite
carrier itself: the completed carrier vanishes between the endpoints by the intermediate
value theorem, and the archimedean envelope is nonvanishing on the line. -/
theorem gN_line_zero_of_sign_bracket (N : ℕ) {t₁ t₂ : ℝ} (h12 : t₁ ≤ t₂)
    (hsign : (completedGN N (linePt t₁)).re * (completedGN N (linePt t₂)).re ≤ 0) :
    ∃ τ ∈ Set.Icc t₁ t₂, gN N (linePt τ) = 0 := by
  obtain ⟨τ, hτ, hzero⟩ := exists_online_carrier_zero_of_sign_change N h12
    (by simpa [linePt] using hsign)
  refine ⟨τ, hτ, ?_⟩
  have hz : completedGN N (linePt τ) = 0 := by
    simpa [linePt] using hzero
  have hz' : archFactor (linePt τ) * gN N (linePt τ) = 0 := hz
  exact (mul_eq_zero.mp hz').resolve_left (archFactor_linePt_ne_zero τ)

/-- **A second carrier zero in the anchored disc refutes the certificate faces.**  The
center floor, the sphere sup, and the Jensen quotient below two admit at most one carrier
zero in the inner disc. -/
theorem anchor_jensen_faces_false_of_second_zero {N : ℕ} {c z₁ z₂ : ℂ}
    {r R M_J m_J : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hball : ∀ z ∈ closedBall c R, z.re < 1)
    (hmJ0 : 0 < m_J) (hmJ : m_J ≤ ‖gN N c‖)
    (hM : 1 ≤ M_J)
    (hbound : ∀ z ∈ sphere c R, ‖gN N z‖ ≤ M_J)
    (hjensen : Real.log (M_J / m_J) / Real.log (R / r) < 2)
    (hz₁ : z₁ ∈ closedBall c r) (hz₂ : z₂ ∈ closedBall c r) (hne : z₁ ≠ z₂)
    (h01 : gN N z₁ = 0) (h02 : gN N z₂ = 0) : False := by
  have hfc : gN N c ≠ 0 := by
    intro h
    rw [h, norm_zero] at hmJ
    linarith
  have hgan : AnalyticOnNhd ℂ (gN N) (closedBall c R) := by
    intro z hz
    exact gN_analyticAt (Gammaℝ_ne_zero_of_re_pos (by
      rw [Complex.sub_re, Complex.one_re]
      linarith [hball z hz]))
  have hM0 : (0 : ℝ) < M_J := lt_of_lt_of_le one_pos hM
  have hnorm_pos : 0 < ‖gN N c‖ := lt_of_lt_of_le hmJ0 hmJ
  have hjensen' : Real.log (M_J / ‖gN N c‖) / Real.log (R / r) < 2 := by
    have harg : M_J / ‖gN N c‖ ≤ M_J / m_J :=
      div_le_div₀ hM0.le le_rfl hmJ0 hmJ
    have hlog := Real.log_le_log (by positivity) harg
    have hlogRr : 0 < Real.log (R / r) :=
      Real.log_pos ((one_lt_div hr).mpr hrR)
    calc Real.log (M_J / ‖gN N c‖) / Real.log (R / r)
        ≤ Real.log (M_J / m_J) / Real.log (R / r) := by gcongr
      _ < 2 := hjensen
  obtain ⟨_, hone, _⟩ := simple_zero_structure_of_jensen hr hrR hgan hfc hM
    hbound hjensen' hz₁ h01
  exact absurd h02 (hone z₂ hz₂ (Ne.symm hne))

/-- **The anchored disc admits at most one sign change.**  Two sign brackets of the real
completed carrier in disjoint line subintervals of the anchored inner disc refute the
anchor, sphere-sup, and Jensen-quotient faces: each bracket produces an on-line carrier
zero, the brackets' disjointness makes the zeros distinct, and the Jensen count admits at
most one.  An anchor floor is therefore certifiable only at radii below the local
sign-change spacing of the completed carrier. -/
theorem anchor_jensen_faces_false_of_two_sign_brackets {N : ℕ} {τc : ℝ}
    {r R M_J m_J t₁ t₂ t₃ t₄ : ℝ}
    (hr : 0 < r) (hrR : r < R)
    (hball : ∀ z ∈ closedBall (linePt τc) R, z.re < 1)
    (hmJ0 : 0 < m_J) (hmJ : m_J ≤ ‖gN N (linePt τc)‖)
    (hM : 1 ≤ M_J)
    (hbound : ∀ z ∈ sphere (linePt τc) R, ‖gN N z‖ ≤ M_J)
    (hjensen : Real.log (M_J / m_J) / Real.log (R / r) < 2)
    (h12 : t₁ ≤ t₂) (h23 : t₂ < t₃) (h34 : t₃ ≤ t₄)
    (hin : ∀ t ∈ Set.Icc t₁ t₄, linePt t ∈ closedBall (linePt τc) r)
    (hsign₁ : (completedGN N (linePt t₁)).re * (completedGN N (linePt t₂)).re ≤ 0)
    (hsign₂ : (completedGN N (linePt t₃)).re * (completedGN N (linePt t₄)).re ≤ 0) :
    False := by
  obtain ⟨τa, hτa, hza⟩ := gN_line_zero_of_sign_bracket N h12 hsign₁
  obtain ⟨τb, hτb, hzb⟩ := gN_line_zero_of_sign_bracket N h34 hsign₂
  have hne : linePt τa ≠ linePt τb := by
    intro h
    have him : τa = τb := by
      have h' := congrArg Complex.im h
      unfold linePt at h'
      simpa using h'
    rw [him] at hτa
    linarith [hτa.2, hτb.1]
  exact anchor_jensen_faces_false_of_second_zero hr hrR hball hmJ0 hmJ hM hbound hjensen
    (hin τa ⟨hτa.1, by linarith [hτa.2]⟩)
    (hin τb ⟨by linarith [hτb.1], hτb.2⟩)
    hne hza hzb

end RHTower
