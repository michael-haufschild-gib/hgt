import GaloisForLFunctions.HTGeometry.StripTranslateCurve
import Mathlib.Analysis.Complex.Hadamard

/-!
# Three lines: the central line controls the whole substrip

Hadamard's three-line theorem interpolates a bound on the two edges of a vertical strip across the
strip.  Applied to the difference of two vertical translates of a holomorphic function — bounded by
the strip bound on the outer edge and by the *line* bound on the central line — it says that
smallness of a translated difference on the central line propagates, with a Hölder exponent, to any
narrower substrip.

Consequently the line pseudometric and the substrip pseudometric induce the same uniform structure on
the translation parameter: the phase carrier built on a line and the one built on a strip are the
same object.  This is the quantitative form of the analytic transfer of eq. (19), and it is what
makes a jet embedding of the strip carrier a statement about the frequency group of the line
restriction.
-/

open Filter Topology Metric Set

namespace GaloisForLFunctions

theorem closedStrip_eq (σ r : ℝ) :
    closedStrip σ r = Complex.HadamardThreeLines.verticalClosedStrip (σ - r) (σ + r) := by
  ext z
  simp only [closedStrip, Complex.HadamardThreeLines.verticalClosedStrip, Set.mem_setOf_eq, Set.mem_preimage,
    Set.mem_Icc, abs_le]
  constructor
  · intro h; exact ⟨by linarith [h.1], by linarith [h.2]⟩
  · intro h; exact ⟨by linarith [h.1], by linarith [h.2]⟩

/-- A closed mathlib strip sits inside our closed substrip when the bounds do. -/
theorem hadamardClosedStrip_subset_closedStrip {σ r a b : ℝ} (ha : σ - r ≤ a) (hb : b ≤ σ + r) :
    Complex.HadamardThreeLines.verticalClosedStrip a b ⊆ closedStrip σ r := by
  intro z hz
  have h : z.re ∈ Set.Icc a b := hz
  show |z.re - σ| ≤ r
  rw [abs_le]
  exact ⟨by linarith [h.1], by linarith [h.2]⟩

theorem closure_hadamardStrip_subset {a b : ℝ} :
    closure (Complex.HadamardThreeLines.verticalStrip a b) ⊆ Complex.HadamardThreeLines.verticalClosedStrip a b := by
  refine closure_minimal ?_ ?_
  · intro z hz
    exact ⟨le_of_lt hz.1, le_of_lt hz.2⟩
  · exact isClosed_Icc.preimage Complex.continuous_re

/-- **Three-lines transfer.**  A bound on the central line of a strip, together with a bound on the
whole substrip, gives a Hölder-interpolated bound on every narrower substrip. -/
theorem norm_sub_le_of_line_bound {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {F : ℂ → E} {σ R r r' M ε : ℝ}
    (hr0 : 0 ≤ r) (hrr' : r < r') (hr'R : r' < R)
    (hεpos : 0 < ε) (hεM : ε ≤ 2 * M)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R))
    (hbound : ∀ z ∈ closedStrip σ r', ‖F z‖ ≤ M)
    {s t : ℝ}
    (hline : ∀ x : ℝ, ‖F ((σ : ℂ) + ((x + s : ℝ) : ℂ) * Complex.I)
      - F ((σ : ℂ) + ((x + t : ℝ) : ℂ) * Complex.I)‖ ≤ ε) :
    ∀ z ∈ closedStrip σ r, ‖F (z + (s : ℂ) * Complex.I) - F (z + (t : ℂ) * Complex.I)‖
      ≤ ε * ((2 * M) / ε) ^ (r / r') := by
  classical
  set G : ℂ → E := fun z => F (z + (s : ℂ) * Complex.I) - F (z + (t : ℂ) * Complex.I) with hGdef
  have hr'pos : 0 < r' := lt_of_le_of_lt hr0 hrr'
  have hMpos : 0 < 2 * M := lt_of_lt_of_le hεpos hεM
  -- holomorphy of the difference on the big strip
  have hGdiff : DifferentiableOn ℂ G (verticalStrip σ R) := by
    intro z hz
    have hz1 : z + (s : ℂ) * Complex.I ∈ verticalStrip σ R := by
      show |(z + (s : ℂ) * Complex.I).re - σ| < R
      have : (z + (s : ℂ) * Complex.I).re = z.re := by simp
      rw [this]
      exact hz
    have hz2 : z + (t : ℂ) * Complex.I ∈ verticalStrip σ R := by
      show |(z + (t : ℂ) * Complex.I).re - σ| < R
      have : (z + (t : ℂ) * Complex.I).re = z.re := by simp
      rw [this]
      exact hz
    have hd1 : DifferentiableAt ℂ (fun w : ℂ => F (w + (s : ℂ) * Complex.I)) z :=
      (hF.differentiableAt ((isOpen_verticalStrip σ R).mem_nhds hz1)).comp z
        ((differentiable_id.add_const _) z)
    have hd2 : DifferentiableAt ℂ (fun w : ℂ => F (w + (t : ℂ) * Complex.I)) z :=
      (hF.differentiableAt ((isOpen_verticalStrip σ R).mem_nhds hz2)).comp z
        ((differentiable_id.add_const _) z)
    exact (hd1.sub hd2).differentiableWithinAt
  have hG2M : ∀ z ∈ closedStrip σ r', ‖G z‖ ≤ 2 * M := by
    intro z hz
    have hz1 : z + (s : ℂ) * Complex.I ∈ closedStrip σ r' := mem_closedStrip_add_I σ r' z hz s
    have hz2 : z + (t : ℂ) * Complex.I ∈ closedStrip σ r' := mem_closedStrip_add_I σ r' z hz t
    calc ‖G z‖ ≤ ‖F (z + (s : ℂ) * Complex.I)‖ + ‖F (z + (t : ℂ) * Complex.I)‖ := norm_sub_le _ _
      _ ≤ M + M := add_le_add (hbound _ hz1) (hbound _ hz2)
      _ = 2 * M := by ring
  have hGline : ∀ z : ℂ, z.re = σ → ‖G z‖ ≤ ε := by
    intro z hz
    have h1 : z + (s : ℂ) * Complex.I = (σ : ℂ) + ((z.im + s : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hz]
    have h2 : z + (t : ℂ) * Complex.I = (σ : ℂ) + ((z.im + t : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext <;> simp [hz]
    rw [hGdef]
    simp only
    rw [h1, h2]
    exact hline z.im
  -- interpolation on each half
  have hconv : ∀ (a b θ : ℝ), 0 < a → 0 < b → a ^ (1 - θ) * b ^ θ = a * (b / a) ^ θ := by
    intro a b θ ha hb
    rw [Real.div_rpow hb.le ha.le, Real.rpow_sub ha, Real.rpow_one]
    field_simp
  have hdcc : ∀ l u : ℝ, σ - r' ≤ l → u ≤ σ + r' →
      DiffContOnCl ℂ G (Complex.HadamardThreeLines.verticalStrip l u) := by
    intro l u hl hu
    have hsub : Complex.HadamardThreeLines.verticalClosedStrip l u ⊆ closedStrip σ r' :=
      hadamardClosedStrip_subset_closedStrip hl hu
    have hsub2 : closedStrip σ r' ⊆ verticalStrip σ R := closedStrip_subset_verticalStrip hr'R
    refine DiffContOnCl.mk ?_ ?_
    · refine hGdiff.mono ?_
      intro z hz
      exact hsub2 (hsub ⟨le_of_lt hz.1, le_of_lt hz.2⟩)
    · refine hGdiff.continuousOn.mono ?_
      intro z hz
      exact hsub2 (hsub (closure_hadamardStrip_subset hz))
  have hBdd : ∀ l u : ℝ, σ - r' ≤ l → u ≤ σ + r' →
      BddAbove ((norm ∘ G) '' Complex.HadamardThreeLines.verticalClosedStrip l u) := by
    intro l u hl hu
    refine ⟨2 * M, ?_⟩
    rintro y ⟨z, hz, rfl⟩
    exact hG2M z (hadamardClosedStrip_subset_closedStrip hl hu hz)
  have hkey : ∀ z ∈ closedStrip σ r, ‖G z‖ ≤ ε * ((2 * M) / ε) ^ (|z.re - σ| / r') := by
    intro z hz
    have hzabs : |z.re - σ| ≤ r := hz
    rcases le_or_gt σ z.re with hge | hlt
    · -- right half
      have hzmem : z ∈ Complex.HadamardThreeLines.verticalClosedStrip σ (σ + r') := by
        refine ⟨hge, ?_⟩
        have := (abs_le.mp hzabs).2
        linarith
      have happ := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
        (f := G) (z := z) (a := ε) (b := 2 * M) (l := σ) (u := σ + r')
        (by linarith) hzmem (hdcc σ (σ + r') (by linarith) (by linarith))
        (hBdd σ (σ + r') (by linarith) (by linarith))
        (fun w hw => hGline w hw) (fun w hw => hG2M w (by
          have hwre : w.re = σ + r' := hw
          show |w.re - σ| ≤ r'
          rw [hwre]
          simp [abs_of_nonneg hr'pos.le]))
      have hθ : (z.re - σ) / (σ + r' - σ) = |z.re - σ| / r' := by
        rw [abs_of_nonneg (by linarith : (0:ℝ) ≤ z.re - σ)]
        ring_nf
      rw [hθ, hconv ε (2 * M) _ hεpos hMpos] at happ
      exact happ
    · -- left half
      have hzmem : z ∈ Complex.HadamardThreeLines.verticalClosedStrip (σ - r') σ := by
        refine ⟨?_, le_of_lt hlt⟩
        have := (abs_le.mp hzabs).1
        linarith
      have happ := Complex.HadamardThreeLines.norm_le_interp_of_mem_verticalClosedStrip'
        (f := G) (z := z) (a := 2 * M) (b := ε) (l := σ - r') (u := σ)
        (by linarith) hzmem (hdcc (σ - r') σ (by linarith) (by linarith))
        (hBdd (σ - r') σ (by linarith) (by linarith))
        (fun w hw => hG2M w (by
          have hwre : w.re = σ - r' := hw
          show |w.re - σ| ≤ r'
          rw [hwre]
          have : σ - r' - σ = -r' := by ring
          rw [this, abs_neg, abs_of_nonneg hr'pos.le]))
        (fun w hw => hGline w hw)
      have hθ : (z.re - (σ - r')) / (σ - (σ - r')) = 1 - |z.re - σ| / r' := by
        rw [abs_of_nonpos (by linarith : z.re - σ ≤ 0),
          show σ - (σ - r') = r' by ring]
        field_simp
        ring
      rw [hθ] at happ
      have hexp2 : (1 : ℝ) - (1 - |z.re - σ| / r') = |z.re - σ| / r' := by ring
      rw [hexp2, mul_comm, hconv ε (2 * M) _ hεpos hMpos] at happ
      exact happ
  -- monotonicity in the exponent
  intro z hz
  refine le_trans (hkey z hz) ?_
  have hbase : (1 : ℝ) ≤ (2 * M) / ε := by
    rw [le_div_iff₀ hεpos]
    linarith
  have hexp : |z.re - σ| / r' ≤ r / r' := by
    have hzabs : |z.re - σ| ≤ r := hz
    gcongr
  exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_le hbase hexp) hεpos.le

/-- **The line distance controls the strip distance.**  For every strip tolerance there is a line
tolerance forcing it: uniform smallness of a translated difference on the central line propagates,
by three lines, to uniform smallness on any narrower substrip. -/
theorem exists_delta_strip_of_line {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [CompleteSpace E] {F : ℂ → E} {σ R r r' M : ℝ}
    (hr0 : 0 ≤ r) (hrr' : r < r') (hr'R : r' < R) (hMpos : 0 < M)
    (hF : DifferentiableOn ℂ F (verticalStrip σ R))
    (hbound : ∀ z ∈ closedStrip σ r', ‖F z‖ ≤ M) :
    ∀ ε' : ℝ, 0 < ε' → ∃ δ : ℝ, 0 < δ ∧ ∀ s t : ℝ,
      (∀ x : ℝ, ‖F ((σ : ℂ) + ((x + s : ℝ) : ℂ) * Complex.I)
        - F ((σ : ℂ) + ((x + t : ℝ) : ℂ) * Complex.I)‖ ≤ δ) →
      ∀ z ∈ closedStrip σ r, ‖F (z + (s : ℂ) * Complex.I) - F (z + (t : ℂ) * Complex.I)‖ ≤ ε' := by
  intro ε' hε'
  have hr'pos : 0 < r' := lt_of_le_of_lt hr0 hrr'
  set θ : ℝ := r / r' with hθdef
  have hθ0 : 0 ≤ θ := by rw [hθdef]; positivity
  have hθ1 : θ < 1 := by
    rw [hθdef, div_lt_one hr'pos]
    exact hrr'
  -- the interpolated bound tends to zero with the line tolerance
  have hlim : Tendsto (fun δ : ℝ => δ ^ (1 - θ) * (2 * M) ^ θ) (nhds 0) (nhds 0) := by
    have h1 : Tendsto (fun δ : ℝ => δ ^ (1 - θ)) (nhds 0) (nhds 0) := by
      have hcont : ContinuousAt (fun δ : ℝ => δ ^ (1 - θ)) 0 :=
        Real.continuousAt_rpow_const 0 (1 - θ) (Or.inr (by linarith))
      have hval : (0 : ℝ) ^ (1 - θ) = 0 := Real.zero_rpow (by linarith)
      have hct := hcont
      rw [ContinuousAt, hval] at hct
      exact hct
    have := h1.mul (tendsto_const_nhds (x := ((2 * M) ^ θ)) (f := nhds (0:ℝ)))
    simpa using this
  obtain ⟨δ₀, hδ₀pos, hδ₀⟩ : ∃ δ₀ : ℝ, 0 < δ₀ ∧ ∀ δ : ℝ, 0 < δ → δ < δ₀ →
      δ ^ (1 - θ) * (2 * M) ^ θ ≤ ε' := by
    have hev := (Metric.tendsto_nhds.mp hlim) ε' hε'
    rw [Metric.eventually_nhds_iff] at hev
    obtain ⟨δ₀, hδ₀pos, hδ₀⟩ := hev
    refine ⟨δ₀, hδ₀pos, fun δ hδpos hδlt => ?_⟩
    have hdist : dist δ 0 < δ₀ := by
      rw [Real.dist_eq, sub_zero, abs_of_pos hδpos]
      exact hδlt
    have h := hδ₀ hdist
    rw [Real.dist_eq, sub_zero] at h
    calc δ ^ (1 - θ) * (2 * M) ^ θ ≤ |δ ^ (1 - θ) * (2 * M) ^ θ| := le_abs_self _
      _ ≤ ε' := le_of_lt h
  refine ⟨min (δ₀ / 2) M, by positivity, fun s t hline z hz => ?_⟩
  set δ : ℝ := min (δ₀ / 2) M with hδdef
  have hδpos : 0 < δ := by rw [hδdef]; positivity
  have hδlt : δ < δ₀ := lt_of_le_of_lt (min_le_left _ _) (by linarith)
  have hδM : δ ≤ 2 * M := le_trans (min_le_right _ _) (by linarith)
  have hmain := norm_sub_le_of_line_bound hr0 hrr' hr'R hδpos hδM hF hbound hline z hz
  have hconv : δ * ((2 * M) / δ) ^ θ = δ ^ (1 - θ) * (2 * M) ^ θ := by
    rw [Real.div_rpow (by linarith) hδpos.le, Real.rpow_sub hδpos, Real.rpow_one]
    field_simp
  rw [hconv] at hmain
  exact le_trans hmain (hδ₀ δ hδpos hδlt)

end GaloisForLFunctions
