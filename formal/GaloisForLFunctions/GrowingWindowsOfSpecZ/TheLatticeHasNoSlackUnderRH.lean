import GaloisForLFunctions.GrowingWindowsOfSpecZ.MarginsAreBoundedByRecurrence
import GaloisForLFunctions.RHTower.WeilConditionalConstantSignRigidity
import GaloisForLFunctions.RHTower.GammaHardyPhaseRateLevyKhintchine
import GaloisForLFunctions.HTGeometry.SimultaneousDirichlet

/-!
# The lattice has no slack under RH

Under RH Weil's form is the zero sum `Q(g) = Σ_ρ m_ρ|ĝ(γ_ρ)|²` (RHTower
`re_W_eq_tsum_zeroTerm`), and a translate multiplies `ĝ(γ)` by a unimodular phase. Hence the energy
of the Frobenius difference of a bump is an absolutely convergent cosine series with nonnegative
weights (`weilQuad_frobeniusDiff_eq`):

`Q(φ − φ(· + ph)) = Σ_ρ w_ρ·2(1 − cos(γ_ρph))`, `w_ρ = m_ρ|φ̂(γ_ρ)|²`.

Simultaneous Dirichlet approximation of finitely many ordinates makes it as small as we like at some
`p ≥ 1` (`exists_frobeniusDiff_lt`): the orbit correlation of every bump recurs on every lattice. With
the recurrence bound `E_p ≤ Q(φ − φ(· + ph))` (`levinsonErr_weilSeq_le`):

* **No slack** (`tendsto_levinsonErr_of_riemannHypothesis`): under RH every lattice canonical system
  of Spec ℤ has positive margins tending to `0`.
* **RH as a singular evolution** (`riemannHypothesis_iff_singular_lattices`): RH holds iff for every
  bump and step the lattice margins are positive and tend to `0`.

In Szegő's language the spectral measure of every lattice of Spec ℤ is singular under RH: the
evolution never stays a fixed distance inside the positive cone, and the margins that the prime kicks
must respect shrink to zero along every lattice. This is the no-slack wall as a theorem about the
causal evolution.
-/

noncomputable section

open MeasureTheory Set Filter Topology Complex

namespace GaloisForLFunctions.GrowingWindowsOfSpecZ

open CohomologyOfWindowsOfSpecZ DimensionZeroGeometryOfSpecZ SpacingScaleHarmonicAnalysis
  ArithmeticCastelnuovoSeveri Zeta23 RHTower.WeilConditional

variable {φ : ℝ → ℝ} {h : ℝ}

/-- **The Frobenius difference as a cosine series.** Under RH,
`Q(φ − φ(· + ph)) = Σ_ρ m_ρ|φ̂(γ_ρ)|²·2(1 − cos(γ_ρph))`. -/
theorem weilQuad_frobeniusDiff_eq (hRH : RiemannHypothesis) (hφ : φ ∈ realTests) (h : ℝ) (p : ℤ) :
    weilQuad (fun u => 1 * φ u + -1 * latticeTranslate φ h p u) =
      ∑' ρ, zeroTerm (cx φ) ρ * (2 * (1 - Real.cos ((ρ : ℂ).im * ((p : ℝ) * h)))) := by
  have hg : (fun u => 1 * φ u + -1 * latticeTranslate φ h p u) ∈ realTests := by
    have := realTests.add_mem (realTests.smul_mem 1 hφ)
      (realTests.smul_mem (-1) (latticeTranslate_mem hφ h p))
    convert this using 1
    funext u
    simp
  rw [LogCells.weilQuad_eq_zetaW hg.1 hg.2,
    re_W_eq_tsum_zeroTerm (f := fun u => ((1 * φ u + -1 * latticeTranslate φ h p u : ℝ) : ℂ)) hRH
      (cx_contDiff hg.1) (cx_hasCompactSupport hg.2)]
  refine tsum_congr fun ρ => ?_
  have hfun : (fun u => ((1 * φ u + -1 * latticeTranslate φ h p u : ℝ) : ℂ)) =
      fun u => cx φ u - cx φ (u + (p : ℝ) * h) := by
    funext u; simp [cx, latticeTranslate]; ring
  have hint : Integrable (cx φ) :=
    (cx_contDiff hφ.1).continuous.integrable_of_hasCompactSupport (cx_hasCompactSupport hφ.2)
  simp only [zeroTerm]
  rw [show (fun u => ((1 * φ u + -1 * latticeTranslate φ h p u : ℝ) : ℂ)) =
      fun u => cx φ u - cx φ (u + (p : ℝ) * h) from hfun,
    RHTower.paperFT_sub_comp_add_right hint, norm_mul, mul_pow,
    RHTower.norm_one_sub_cexp_ofReal_mul_I_sq, Real.cos_neg]
  ring

/-- **The orbit of every bump recurs on every lattice** (under RH): for every `ε > 0` some `p ≥ 1`
has `Q(φ − φ(· + ph)) < ε`. -/
theorem exists_frobeniusDiff_lt (hRH : RiemannHypothesis) (hφ : φ ∈ realTests) (h : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ p : ℕ, 1 ≤ p ∧ weilQuad (fun u => 1 * φ u + -1 * latticeTranslate φ h p u) < ε := by
  classical
  set w := zeroTerm (cx φ)
  have hw : Summable w := summable_zeroTerm hRH (cx_contDiff hφ.1) (cx_hasCompactSupport hφ.2)
  have hw0 : ∀ ρ, 0 ≤ w ρ := fun ρ => zeroTerm_nonneg _ ρ
  set W := ∑' ρ, w ρ
  have hW0 : 0 ≤ W := tsum_nonneg hw0
  -- a finite set of zeros carrying all but `ε/8` of the weight
  have htail := tendsto_tsum_compl_atTop_zero w
  obtain ⟨F, hF⟩ :=
    Filter.eventually_atTop.mp (htail.eventually_lt_const (by linarith : (0 : ℝ) < ε / 8))
  have hFtail : ∑' q : {x // x ∉ F}, w q < ε / 8 := hF F le_rfl
  -- the resolution of the simultaneous approximation
  set Q : ℕ := ⌈8 * Real.pi ^ 2 * W / ε⌉₊ + 1 with hQdef
  have hQ0 : 0 < Q := by omega
  have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ0
  have hQ1 : (1 : ℝ) ≤ Q := by exact_mod_cast hQ0
  have hQge : 8 * Real.pi ^ 2 * W / ε < Q := by
    have := Nat.le_ceil (8 * Real.pi ^ 2 * W / ε)
    rw [hQdef]; push_cast; linarith
  have hδ : (2 * Real.pi / Q) ^ 2 * W < ε / 2 := by
    have h1 : (2 * Real.pi / Q) ^ 2 * W = 4 * Real.pi ^ 2 * W / ((Q : ℝ) ^ 2) := by
      field_simp; ring
    have h2 : 4 * Real.pi ^ 2 * W / ((Q : ℝ) ^ 2) ≤ 4 * Real.pi ^ 2 * W / Q := by
      apply div_le_div_of_nonneg_left (by positivity) hQpos
      nlinarith
    have h3 : 4 * Real.pi ^ 2 * W / (Q : ℝ) < ε / 2 := by
      rw [div_lt_iff₀ hQpos]
      have := (div_lt_iff₀ hε).mp hQge
      nlinarith [Real.pi_pos]
    linarith
  -- the frequencies of the finitely many zeros
  let e := F.equivFin
  let β : Fin F.card → ℝ := fun i => (((e.symm i).1 : ℂ).im) * h / (2 * Real.pi)
  obtain ⟨p, hp1, -, hclose⟩ := HTGeometry.exists_simultaneous_dirichlet β hQ0
  refine ⟨p, hp1, ?_⟩
  rw [weilQuad_frobeniusDiff_eq hRH hφ h p]
  set f : zetaZeroConfig.carrier → ℝ := fun ρ =>
    w ρ * (2 * (1 - Real.cos ((ρ : ℂ).im * (((p : ℤ) : ℝ) * h)))) with hf
  have hfle : ∀ ρ, 0 ≤ f ρ ∧ f ρ ≤ 4 * w ρ := fun ρ => by
    have hc := Real.neg_one_le_cos ((ρ : ℂ).im * (((p : ℤ) : ℝ) * h))
    have hc' := Real.cos_le_one ((ρ : ℂ).im * (((p : ℤ) : ℝ) * h))
    exact ⟨mul_nonneg (hw0 ρ) (by linarith), by nlinarith [hw0 ρ]⟩
  have hfs : Summable f := (hw.mul_left 4).of_nonneg_of_le (fun ρ => (hfle ρ).1) fun ρ => (hfle ρ).2
  -- the finite part is small by the simultaneous approximation
  have hfinF : ∀ ρ ∈ F, f ρ ≤ w ρ * (2 * Real.pi / Q) ^ 2 := by
    intro ρ hρ
    obtain ⟨k, hk⟩ := hclose (e ⟨ρ, hρ⟩)
    have hβ : β (e ⟨ρ, hρ⟩) = (ρ : ℂ).im * h / (2 * Real.pi) := by
      simp only [β, Equiv.symm_apply_apply]
    rw [hβ] at hk
    have hx : (ρ : ℂ).im * (((p : ℤ) : ℝ) * h) =
        2 * Real.pi * ((p : ℝ) * ((ρ : ℂ).im * h / (2 * Real.pi)) - k) + k * (2 * Real.pi) := by
      push_cast
      field_simp
      ring
    have hcos : 1 - (2 * Real.pi * ((p : ℝ) * ((ρ : ℂ).im * h / (2 * Real.pi)) - k)) ^ 2 / 2 ≤
        Real.cos ((ρ : ℂ).im * (((p : ℤ) : ℝ) * h)) := by
      rw [hx, Real.cos_add_int_mul_two_pi]; exact Real.one_sub_sq_div_two_le_cos
    have habs : |2 * Real.pi * ((p : ℝ) * ((ρ : ℂ).im * h / (2 * Real.pi)) - k)| ≤
        2 * Real.pi / Q := by
      rw [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
      calc 2 * Real.pi * |(p : ℝ) * ((ρ : ℂ).im * h / (2 * Real.pi)) - k|
          ≤ 2 * Real.pi * (1 / Q) := mul_le_mul_of_nonneg_left hk.le (by positivity)
        _ = 2 * Real.pi / Q := by ring
    have hsq : (2 * Real.pi * ((p : ℝ) * ((ρ : ℂ).im * h / (2 * Real.pi)) - k)) ^ 2 ≤
        (2 * Real.pi / Q) ^ 2 := by
      rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) habs 2
    simp only [hf]
    have := hw0 ρ
    nlinarith
  have hFsum : ∑ ρ ∈ F, f ρ ≤ (2 * Real.pi / Q) ^ 2 * W := by
    calc ∑ ρ ∈ F, f ρ ≤ ∑ ρ ∈ F, w ρ * (2 * Real.pi / Q) ^ 2 := Finset.sum_le_sum hfinF
      _ = (∑ ρ ∈ F, w ρ) * (2 * Real.pi / Q) ^ 2 := by rw [Finset.sum_mul]
      _ ≤ W * (2 * Real.pi / Q) ^ 2 :=
          mul_le_mul_of_nonneg_right (hw.sum_le_tsum F fun ρ _ => hw0 ρ) (by positivity)
      _ = (2 * Real.pi / Q) ^ 2 * W := by ring
  -- the tail is small because the weights are
  have htailf : ∑' q : ↑(↑F : Set zetaZeroConfig.carrier)ᶜ, f q ≤ 4 * (ε / 8) := by
    have h1 : ∑' q : ↑(↑F : Set zetaZeroConfig.carrier)ᶜ, f q ≤
        ∑' q : ↑(↑F : Set zetaZeroConfig.carrier)ᶜ, 4 * w q :=
      Summable.tsum_le_tsum (fun q => (hfle q).2) (hfs.subtype _) ((hw.mul_left 4).subtype _)
    have h2 : ∑' q : ↑(↑F : Set zetaZeroConfig.carrier)ᶜ, 4 * w q =
        4 * ∑' q : {x // x ∉ F}, w q := by
      rw [tsum_mul_left]; rfl
    rw [h2] at h1
    linarith
  rw [← hfs.sum_add_tsum_compl (s := F)]
  linarith

/-- **No slack.** Under RH every lattice canonical system of Spec ℤ has positive margins tending to
`0`. -/
theorem tendsto_levinsonErr_of_riemannHypothesis (hRH : RiemannHypothesis) (hφ : φ ∈ realTests)
    (hφ0 : φ ≠ 0) (hh : 0 < h) :
    (∀ n, 0 < levinsonErr (weilSeq φ h) n) ∧
      Tendsto (fun n => levinsonErr (weilSeq φ h) n) atTop (𝓝 0) := by
  have hpos : ∀ n, 0 < levinsonErr (weilSeq φ h) n := fun n =>
    riemannHypothesis_iff_levinsonErr_pos.mp hRH φ hφ hφ0 h hh n
  refine ⟨hpos, Metric.tendsto_atTop.mpr fun ε hε => ?_⟩
  obtain ⟨p, hp1, hp⟩ := exists_frobeniusDiff_lt hRH hφ h hε
  obtain ⟨m, rfl⟩ : ∃ m, p = m + 1 := ⟨p - 1, by omega⟩
  have hbound := levinsonErr_weilSeq_le hφ
    (toeplitzPosDef_of_riemannHypothesis hRH hφ hφ0 hh (m + 1))
  have hcast : (((m + 1 : ℕ) : ℤ)) = (m : ℤ) + 1 := by push_cast; ring
  rw [hcast] at hp
  refine ⟨m + 1, fun n hn => ?_⟩
  have hanti : levinsonErr (weilSeq φ h) n ≤ levinsonErr (weilSeq φ h) (m + 1) := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le hn
    induction k with
    | zero => simp
    | succ k ih =>
      exact (levinsonErr_succ_le (hpos _)).trans (ih (by omega))
  rw [Real.dist_eq, sub_zero, abs_of_pos (hpos n)]
  linarith

/-- **RH is the singularity of every lattice evolution.** RH holds iff for every nonzero bump and
every step the lattice margins of Spec ℤ are positive and tend to `0`. -/
theorem riemannHypothesis_iff_singular_lattices :
    RiemannHypothesis ↔
      ∀ φ ∈ realTests, φ ≠ 0 → ∀ h : ℝ, 0 < h →
        (∀ n, 0 < levinsonErr (weilSeq φ h) n) ∧
          Tendsto (fun n => levinsonErr (weilSeq φ h) n) atTop (𝓝 0) :=
  ⟨fun hRH _ hφ hφ0 _ hh => tendsto_levinsonErr_of_riemannHypothesis hRH hφ hφ0 hh,
    fun H => riemannHypothesis_iff_levinsonErr_pos.mpr fun φ hφ hφ0 h hh => (H φ hφ hφ0 h hh).1⟩

end GaloisForLFunctions.GrowingWindowsOfSpecZ
