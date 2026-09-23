import GaloisForLFunctions.HTGeometry.WaveTracePoleTransform

/-!
# Reinforcement of residues at an active resolvent pole

Frequencies sharing a square contribute identical resolvent terms: the trace coefficient and
the phase numerator each change sign under `gamma ↦ -gamma`, so their product is invariant.
Therefore the residues of a common pole reinforce and can never cancel, and the pole of an
active frequency is genuine.

At the pole the phase numerator collapses to the frequency itself, which is nonzero, so the
head of the series is an honest simple pole while the remaining terms stay bounded.
-/

open Complex Filter MeasureTheory Set Topology

namespace GaloisForLFunctions.HTGeometry

namespace WaveSpectrum

noncomputable section

variable {G : Type*} (S : WaveSpectrum G)

/-- Locally finite frequency divisor: only finitely many frequencies in any bounded region. -/
def IsLocallyFiniteSpectrum : Prop := ∀ R : ℝ, {g : G | ‖S.gamma g‖ ≤ R}.Finite

/-- Frequencies sharing their square with a given one. -/
def squareFiber (g₀ : G) : Set G := {g | S.gamma g ^ (2 : ℕ) = S.gamma g₀ ^ (2 : ℕ)}

theorem norm_eq_of_mem_squareFiber {g₀ g : G} (hg : g ∈ S.squareFiber g₀) :
    ‖S.gamma g‖ = ‖S.gamma g₀‖ := by
  have hsq : ‖S.gamma g‖ ^ (2 : ℕ) = ‖S.gamma g₀‖ ^ (2 : ℕ) := by
    rw [← norm_pow, ← norm_pow]
    exact congrArg norm hg
  have h1 : (0 : ℝ) ≤ ‖S.gamma g‖ := norm_nonneg _
  have h2 : (0 : ℝ) ≤ ‖S.gamma g₀‖ := norm_nonneg _
  nlinarith [hsq, h1, h2]

theorem squareFiber_finite (hlf : S.IsLocallyFiniteSpectrum) (g₀ : G) :
    (S.squareFiber g₀).Finite :=
  Set.Finite.subset (hlf ‖S.gamma g₀‖) fun _ hg => le_of_eq (S.norm_eq_of_mem_squareFiber hg)

theorem gamma_eq_or_eq_neg_of_mem_squareFiber {g₀ g : G} (hg : g ∈ S.squareFiber g₀) :
    S.gamma g = S.gamma g₀ ∨ S.gamma g = -S.gamma g₀ := by
  have hfac : (S.gamma g - S.gamma g₀) * (S.gamma g + S.gamma g₀) = 0 := by
    have : S.gamma g ^ (2 : ℕ) = S.gamma g₀ ^ (2 : ℕ) := hg
    linear_combination this
  rcases mul_eq_zero.mp hfac with h | h
  · exact Or.inl (by linear_combination h)
  · exact Or.inr (by linear_combination h)

/-- **Square separation.** A locally finite divisor keeps every other frequency square at a
positive distance from a given one. -/
theorem exists_square_separation (hlf : S.IsLocallyFiniteSpectrum) (g₀ : G) :
    ∃ d : ℝ, 0 < d ∧
      ∀ g : G, g ∉ S.squareFiber g₀ → d ≤ ‖S.gamma g ^ (2 : ℕ) - S.gamma g₀ ^ (2 : ℕ)‖ := by
  classical
  set R : ℝ := ‖S.gamma g₀‖ + 1 with hR
  set F : Finset G := (hlf R).toFinset with hF
  set Fbad : Finset G := F.filter (fun g => S.gamma g ^ (2 : ℕ) ≠ S.gamma g₀ ^ (2 : ℕ)) with hFbad
  have hfar : ∀ g : G, R < ‖S.gamma g‖ → (1 : ℝ) ≤ ‖S.gamma g ^ (2 : ℕ) - S.gamma g₀ ^ (2 : ℕ)‖ := by
    intro g hg
    have h1 : ‖S.gamma g₀‖ + 1 < ‖S.gamma g‖ := hg
    have h2 : (0 : ℝ) ≤ ‖S.gamma g₀‖ := norm_nonneg _
    have hlow : ‖S.gamma g₀‖ ^ (2 : ℕ) + 1 ≤ ‖S.gamma g‖ ^ (2 : ℕ) := by nlinarith
    have hge : ‖S.gamma g‖ ^ (2 : ℕ) - ‖S.gamma g₀‖ ^ (2 : ℕ) ≤ ‖S.gamma g ^ (2 : ℕ) - S.gamma g₀ ^ (2 : ℕ)‖ := by
      have := norm_sub_norm_le (S.gamma g ^ (2 : ℕ)) (S.gamma g₀ ^ (2 : ℕ))
      rwa [norm_pow, norm_pow] at this
    linarith
  by_cases hne : Fbad.Nonempty
  · set d0 : ℝ := Fbad.inf' hne (fun g => ‖S.gamma g ^ (2 : ℕ) - S.gamma g₀ ^ (2 : ℕ)‖) with hd0
    have hd0pos : 0 < d0 := by
      rw [hd0, Finset.lt_inf'_iff]
      intro g hg
      have hgne : S.gamma g ^ (2 : ℕ) ≠ S.gamma g₀ ^ (2 : ℕ) := (Finset.mem_filter.mp hg).2
      exact norm_pos_iff.mpr (sub_ne_zero.mpr hgne)
    refine ⟨min d0 1, lt_min hd0pos one_pos, fun g hg => ?_⟩
    by_cases hsmall : ‖S.gamma g‖ ≤ R
    · have hmemF : g ∈ F := by
        rw [hF, Set.Finite.mem_toFinset]
        exact hsmall
      have hmem : g ∈ Fbad := Finset.mem_filter.mpr ⟨hmemF, hg⟩
      exact le_trans (min_le_left _ _) (Finset.inf'_le _ hmem)
    · exact le_trans (min_le_right _ _) (hfar g (lt_of_not_ge hsmall))
  · refine ⟨1, one_pos, fun g hg => ?_⟩
    by_cases hsmall : ‖S.gamma g‖ ≤ R
    · exfalso
      have hmemF : g ∈ F := by
        rw [hF, Set.Finite.mem_toFinset]
        exact hsmall
      exact hne ⟨g, Finset.mem_filter.mpr ⟨hmemF, hg⟩⟩
    · exact hfar g (lt_of_not_ge hsmall)

/-! ## Reinforcement of residues -/

variable {S}

/-- The phase numerator collapses to the frequency itself at its own resolvent pole. -/
theorem poleNumer_at_pole (T : ℝ) (g : G) :
    S.poleNumer T (Complex.I * S.gamma g) g = S.gamma g := by
  rw [poleNumer]
  have hEuler : Complex.cos (S.gamma g * (T : ℂ)) +
      Complex.sin (S.gamma g * (T : ℂ)) * Complex.I =
      Complex.exp (S.gamma g * (T : ℂ) * Complex.I) := (Complex.exp_mul_I _).symm
  have hrw : Complex.I * S.gamma g * Complex.sin (S.gamma g * (T : ℂ)) +
      S.gamma g * Complex.cos (S.gamma g * (T : ℂ)) =
      S.gamma g * Complex.exp (S.gamma g * (T : ℂ) * Complex.I) := by
    rw [← hEuler]; ring
  rw [hrw]
  rw [← mul_assoc, mul_comm (Complex.exp (-(Complex.I * S.gamma g) * (T : ℂ))) (S.gamma g),
    mul_assoc, ← Complex.exp_add]
  rw [show -(Complex.I * S.gamma g) * (T : ℂ) + S.gamma g * (T : ℂ) * Complex.I = 0 by ring]
  simp

/-- Frequencies of the same square contribute identical resolvent numerators: both factors
change sign together, so residues reinforce. -/
theorem traceCoeff_mul_poleNumer_eq_of_mem_squareFiber (P : Polynomial ℝ) (T : ℝ) (s : ℂ)
    {g₀ g : G} (hg : g ∈ S.squareFiber g₀) :
    S.traceCoeff P g * S.poleNumer T s g = S.traceCoeff P g₀ * S.poleNumer T s g₀ := by
  have hsq : S.gamma g ^ (2 : ℕ) = S.gamma g₀ ^ (2 : ℕ) := hg
  rcases S.gamma_eq_or_eq_neg_of_mem_squareFiber hg with hgamma | hgamma
  · rw [traceCoeff, traceCoeff, poleNumer, poleNumer, hgamma]
  · have hcoeff : S.traceCoeff P g = -S.traceCoeff P g₀ := by
      rw [traceCoeff, traceCoeff, hsq, hgamma]
      ring
    have hnumer : S.poleNumer T s g = -S.poleNumer T s g₀ := by
      rw [poleNumer, poleNumer, hgamma]
      rw [show -S.gamma g₀ * (T : ℂ) = -(S.gamma g₀ * (T : ℂ)) by ring,
        Complex.sin_neg, Complex.cos_neg]
      ring
    rw [hcoeff, hnumer]
    ring


/-! ## Divergence at an active pole -/

variable (S)

theorem continuous_poleNumer (T : ℝ) (g : G) :
    Continuous (fun s : ℂ => S.poleNumer T s g) := by
  unfold poleNumer
  fun_prop

/-- Off the pole of `g₀`, the resolvent series splits into the reinforced head of the square
fiber and a tail that is uniformly bounded near the pole. -/
theorem poleTransform_eq_head_add_tail [Countable G] (hlf : S.IsLocallyFiniteSpectrum)
    (P : Polynomial ℝ) (T : ℝ) {g₀ : G} {s : ℂ} {d M : ℝ} (hd : 0 < d)
    (hsq : s ^ (2 : ℕ) + S.gamma g₀ ^ (2 : ℕ) ≠ 0)
    (hsep : ∀ g : G, g ∉ S.squareFiber g₀ → d ≤ ‖s ^ (2 : ℕ) + S.gamma g ^ (2 : ℕ)‖)
    (hM : ‖s‖ ≤ M) :
    ∃ tail : ℂ,
      S.poleTransform P T s =
        ((S.squareFiber_finite hlf g₀).toFinset.card : ℂ) *
          (S.traceCoeff P g₀ * S.poleNumer T s g₀) / (s ^ (2 : ℕ) + S.gamma g₀ ^ (2 : ℕ)) + tail ∧
      ‖tail‖ ≤ ∑' g : G, S.poleMajorant P T M d g := by
  classical
  set E : Finset G := (S.squareFiber_finite hlf g₀).toFinset with hE
  have hmemE : ∀ g : G, g ∈ E ↔ g ∈ S.squareFiber g₀ := by
    intro g; rw [hE, Set.Finite.mem_toFinset]
  have hden : ∀ g : G, min d ‖s ^ (2 : ℕ) + S.gamma g₀ ^ (2 : ℕ)‖ ≤ ‖s ^ (2 : ℕ) + S.gamma g ^ (2 : ℕ)‖ := by
    intro g
    by_cases hg : g ∈ S.squareFiber g₀
    · have hgs : S.gamma g ^ (2 : ℕ) = S.gamma g₀ ^ (2 : ℕ) := hg
      rw [hgs]
      exact min_le_right _ _
    · exact le_trans (min_le_left _ _) (hsep g hg)
  have hdmin : 0 < min d ‖s ^ (2 : ℕ) + S.gamma g₀ ^ (2 : ℕ)‖ := lt_min hd (norm_pos_iff.mpr hsq)
  have hsummable : Summable fun g : G => S.poleTerm P T s g :=
    Summable.of_norm_bounded
      (S.summable_poleMajorant P T M (min d ‖s ^ (2 : ℕ) + S.gamma g₀ ^ (2 : ℕ)‖))
      (fun g => S.norm_poleTerm_le P T hdmin hM g (hden g))
  refine ⟨∑' g : ↥(↑E : Set G)ᶜ, S.poleTerm P T s g, ?_, ?_⟩
  · rw [poleTransform, ← hsummable.sum_add_tsum_compl (s := E)]
    congr 1
    have hhead : ∀ g ∈ E, S.poleTerm P T s g =
        S.traceCoeff P g₀ * S.poleNumer T s g₀ / (s ^ (2 : ℕ) + S.gamma g₀ ^ (2 : ℕ)) := by
      intro g hg
      have hgs : g ∈ S.squareFiber g₀ := (hmemE g).mp hg
      have hgsq : S.gamma g ^ (2 : ℕ) = S.gamma g₀ ^ (2 : ℕ) := hgs
      rw [poleTerm, hgsq, traceCoeff_mul_poleNumer_eq_of_mem_squareFiber (S := S) P T s hgs]
    rw [Finset.sum_congr rfl hhead, Finset.sum_const, nsmul_eq_mul]
    ring
  · have hmajnn : ∀ g : G, 0 ≤ S.poleMajorant P T M d g := by
      intro g
      unfold poleMajorant
      have hgp := S.norm_gamma_pos g
      have hMnn : 0 ≤ M := le_trans (norm_nonneg s) hM
      have hC : 0 ≤ polyBallBound P (S.lower⁻¹ ^ (2 : ℕ)) := polyBallBound_nonneg P (by positivity)
      positivity
    refine le_trans (norm_tsum_le_tsum_norm ((hsummable.subtype _).norm)) ?_
    refine le_trans (Summable.tsum_le_tsum (fun g => ?_) ((hsummable.subtype _).norm)
      ((S.summable_poleMajorant P T M d).subtype _)) ?_
    · refine S.norm_poleTerm_le P T hd hM (g : G) (hsep (g : G) ?_)
      intro hmem
      exact (g.2 : (g : G) ∈ (↑E : Set G)ᶜ) ((hmemE (g : G)).mpr hmem)
    · have hsplit := (S.summable_poleMajorant P T M d).sum_add_tsum_compl (s := E)
      have hheadnn : 0 ≤ ∑ g ∈ E, S.poleMajorant P T M d g :=
        Finset.sum_nonneg (fun g _ => hmajnn g)
      simp only [Function.comp_def]
      linarith [hsplit]

/-! ## The pole domain -/

/-- The resolvent pole divisor of the spectrum. -/
def poleSet : Set ℂ := {s : ℂ | ∃ g : G, s ^ (2 : ℕ) + S.gamma g ^ (2 : ℕ) = 0}

/-- A locally finite divisor keeps every non-pole at a positive distance from the whole
resolvent denominator family. -/
theorem exists_denominator_lower_bound (hlf : S.IsLocallyFiniteSpectrum) {w : ℂ}
    (hw : w ∉ S.poleSet) :
    ∃ d : ℝ, 0 < d ∧ ∀ g : G, d ≤ ‖w ^ (2 : ℕ) + S.gamma g ^ (2 : ℕ)‖ := by
  classical
  set R : ℝ := ‖w‖ + 1 with hR
  set F : Finset G := (hlf R).toFinset with hF
  have hfar : ∀ g : G, R < ‖S.gamma g‖ → (1 : ℝ) ≤ ‖w ^ (2 : ℕ) + S.gamma g ^ (2 : ℕ)‖ := by
    intro g hg
    have h1 : ‖w‖ + 1 < ‖S.gamma g‖ := hg
    have h2 : (0 : ℝ) ≤ ‖w‖ := norm_nonneg _
    have hlow : ‖w‖ ^ (2 : ℕ) + 1 ≤ ‖S.gamma g‖ ^ (2 : ℕ) := by nlinarith
    have hge : ‖S.gamma g‖ ^ (2 : ℕ) - ‖w‖ ^ (2 : ℕ) ≤ ‖w ^ (2 : ℕ) + S.gamma g ^ (2 : ℕ)‖ := by
      have hnn := norm_sub_norm_le (S.gamma g ^ (2 : ℕ)) (-(w ^ (2 : ℕ)))
      rw [sub_neg_eq_add, norm_neg, norm_pow, norm_pow] at hnn
      rw [add_comm (w ^ (2 : ℕ)) (S.gamma g ^ (2 : ℕ))]
      exact hnn
    linarith
  by_cases hne : F.Nonempty
  · set d0 : ℝ := F.inf' hne (fun g => ‖w ^ (2 : ℕ) + S.gamma g ^ (2 : ℕ)‖) with hd0
    have hd0pos : 0 < d0 := by
      rw [hd0, Finset.lt_inf'_iff]
      intro g _
      refine norm_pos_iff.mpr ?_
      intro hz
      exact hw ⟨g, hz⟩
    refine ⟨min d0 1, lt_min hd0pos one_pos, fun g => ?_⟩
    by_cases hsmall : ‖S.gamma g‖ ≤ R
    · refine le_trans (min_le_left _ _) (Finset.inf'_le _ ?_)
      rw [hF, Set.Finite.mem_toFinset]
      exact hsmall
    · exact le_trans (min_le_right _ _) (hfar g (lt_of_not_ge hsmall))
  · refine ⟨1, one_pos, fun g => ?_⟩
    by_cases hsmall : ‖S.gamma g‖ ≤ R
    · exact absurd ⟨g, by rw [hF, Set.Finite.mem_toFinset]; exact hsmall⟩ hne
    · exact hfar g (lt_of_not_ge hsmall)

theorem exists_ball_denominator_bound (hlf : S.IsLocallyFiniteSpectrum) {w : ℂ}
    (hw : w ∉ S.poleSet) :
    ∃ ε d : ℝ, 0 < ε ∧ 0 < d ∧
      ∀ s ∈ Metric.ball w ε, ∀ g : G, d ≤ ‖s ^ (2 : ℕ) + S.gamma g ^ (2 : ℕ)‖ := by
  obtain ⟨d0, hd0, hbound⟩ := S.exists_denominator_lower_bound hlf hw
  refine ⟨min 1 (d0 / (2 * (2 * ‖w‖ + 1))), d0 / 2, lt_min one_pos (by positivity),
    by linarith, fun s hs g => ?_⟩
  set ε : ℝ := min 1 (d0 / (2 * (2 * ‖w‖ + 1))) with hε
  have hsw : ‖s - w‖ < ε := by
    rw [← Complex.dist_eq]
    exact hs
  have hε1 : ε ≤ 1 := min_le_left _ _
  have hε2 : ε ≤ d0 / (2 * (2 * ‖w‖ + 1)) := min_le_right _ _
  have hsnorm : ‖s‖ ≤ ‖w‖ + ε := by
    have := norm_add_le (s - w) w
    simp only [sub_add_cancel] at this
    linarith
  have hshift : ‖s ^ (2 : ℕ) - w ^ (2 : ℕ)‖ ≤ d0 / 2 := by
    have hfac : s ^ (2 : ℕ) - w ^ (2 : ℕ) = (s - w) * (s + w) := by ring
    have hsum : ‖s + w‖ ≤ 2 * ‖w‖ + 1 := by
      refine le_trans (norm_add_le _ _) ?_
      linarith
    have hprod : ‖s ^ (2 : ℕ) - w ^ (2 : ℕ)‖ ≤ ε * (2 * ‖w‖ + 1) := by
      rw [hfac, norm_mul]
      exact mul_le_mul hsw.le hsum (norm_nonneg _) (le_of_lt (lt_of_le_of_lt (norm_nonneg _) hsw))
    have hpos : (0 : ℝ) < 2 * ‖w‖ + 1 := by positivity
    have hle : ε * (2 * ‖w‖ + 1) ≤ d0 / 2 := by
      calc ε * (2 * ‖w‖ + 1) ≤ d0 / (2 * (2 * ‖w‖ + 1)) * (2 * ‖w‖ + 1) :=
            mul_le_mul_of_nonneg_right hε2 hpos.le
        _ = d0 / 2 := by field_simp
    linarith
  have hsplit : s ^ (2 : ℕ) + S.gamma g ^ (2 : ℕ) = (w ^ (2 : ℕ) + S.gamma g ^ (2 : ℕ)) + (s ^ (2 : ℕ) - w ^ (2 : ℕ)) := by ring
  have hlow := hbound g
  have htri := norm_sub_norm_le (w ^ (2 : ℕ) + S.gamma g ^ (2 : ℕ)) (-(s ^ (2 : ℕ) - w ^ (2 : ℕ)))
  rw [sub_neg_eq_add, norm_neg] at htri
  rw [hsplit]
  linarith

theorem isOpen_compl_poleSet (hlf : S.IsLocallyFiniteSpectrum) : IsOpen (S.poleSet)ᶜ := by
  rw [Metric.isOpen_iff]
  intro w hw
  obtain ⟨ε, d, hε, hd, hbound⟩ := S.exists_ball_denominator_bound hlf hw
  refine ⟨ε, hε, fun s hs => ?_⟩
  intro hmem
  obtain ⟨g, hg⟩ := hmem
  have := hbound s hs g
  rw [hg, norm_zero] at this
  linarith

theorem differentiableOn_poleTransform_compl (hlf : S.IsLocallyFiniteSpectrum)
    (P : Polynomial ℝ) (T : ℝ) :
    DifferentiableOn ℂ (S.poleTransform P T) (S.poleSet)ᶜ := by
  intro w hw
  refine DifferentiableAt.differentiableWithinAt ?_
  obtain ⟨ε, d, hε, hd, hbound⟩ := S.exists_ball_denominator_bound hlf hw
  have hdiff : DifferentiableOn ℂ (S.poleTransform P T) (Metric.ball w ε) := by
    refine S.differentiableOn_poleTransform P T Metric.isOpen_ball (M := ‖w‖ + ε) hd
      (fun s hs => ?_) (fun s hs g => hbound s hs g)
    have hsw : ‖s - w‖ < ε := by rw [← Complex.dist_eq]; exact hs
    have := norm_add_le (s - w) w
    simp only [sub_add_cancel] at this
    linarith
  exact hdiff.differentiableAt (Metric.ball_mem_nhds w hε)

theorem countable_poleSet [Countable G] : (S.poleSet).Countable := by
  have hsub : S.poleSet ⊆ (Set.range fun g : G => Complex.I * S.gamma g) ∪
      (Set.range fun g : G => -(Complex.I * S.gamma g)) := by
    rintro s ⟨g, hg⟩
    have hfac : (s - Complex.I * S.gamma g) * (s + Complex.I * S.gamma g) = 0 := by
      linear_combination hg - (S.gamma g ^ (2 : ℕ)) * Complex.I_sq
    rcases mul_eq_zero.mp hfac with h | h
    · exact Or.inl ⟨g, by linear_combination -h⟩
    · exact Or.inr ⟨g, by linear_combination -h⟩
  exact Set.Countable.mono hsub ((Set.countable_range _).union (Set.countable_range _))

theorem isPreconnected_compl_poleSet [Countable G] : IsPreconnected (S.poleSet)ᶜ :=
  ((S.countable_poleSet).isConnected_compl_of_one_lt_rank
    (by rw [Complex.rank_real_complex]; norm_num)).isPreconnected

/-- **Uniform real-part gap.** A locally finite divisor with no purely imaginary frequency
keeps every resolvent pole off the real axis by a fixed amount. -/
theorem exists_re_lower_bound (hlf : S.IsLocallyFiniteSpectrum)
    (hnoim : ∀ g : G, (S.gamma g).re ≠ 0) :
    ∃ rho : ℝ, 0 < rho ∧ ∀ g : G, rho ≤ |(S.gamma g).re| := by
  classical
  set R : ℝ := S.width + 1 with hR
  set F : Finset G := (hlf R).toFinset with hF
  have hnormsq : ∀ g : G, ‖S.gamma g‖ ^ (2 : ℕ) = (S.gamma g).re ^ (2 : ℕ) + (S.gamma g).im ^ (2 : ℕ) := by
    intro g
    have := Complex.normSq_eq_norm_sq (S.gamma g)
    simp only [Complex.normSq_apply] at this
    nlinarith [this]
  have hfar : ∀ g : G, R < ‖S.gamma g‖ → (1 : ℝ) ≤ |(S.gamma g).re| := by
    intro g hg
    have hw : |(S.gamma g).im| ≤ S.width := S.im_le g
    have hwnn : 0 ≤ S.width := S.width_nonneg
    have him : (S.gamma g).im ^ (2 : ℕ) ≤ S.width ^ (2 : ℕ) := by
      have := sq_abs (S.gamma g).im
      nlinarith [abs_nonneg (S.gamma g).im]
    have hgt : S.width + 1 < ‖S.gamma g‖ := hg
    have hsq : (S.width + 1) ^ (2 : ℕ) < ‖S.gamma g‖ ^ (2 : ℕ) := by nlinarith [norm_nonneg (S.gamma g)]
    have hre : 1 ≤ (S.gamma g).re ^ (2 : ℕ) := by
      have := hnormsq g
      nlinarith
    have habs := sq_abs (S.gamma g).re
    nlinarith [abs_nonneg (S.gamma g).re]
  by_cases hne : F.Nonempty
  · set d0 : ℝ := F.inf' hne (fun g => |(S.gamma g).re|) with hd0
    have hd0pos : 0 < d0 := by
      rw [hd0, Finset.lt_inf'_iff]
      intro g _
      exact abs_pos.mpr (hnoim g)
    refine ⟨min d0 1, lt_min hd0pos one_pos, fun g => ?_⟩
    by_cases hsmall : ‖S.gamma g‖ ≤ R
    · refine le_trans (min_le_left _ _) (Finset.inf'_le _ ?_)
      rw [hF, Set.Finite.mem_toFinset]
      exact hsmall
    · exact le_trans (min_le_right _ _) (hfar g (lt_of_not_ge hsmall))
  · refine ⟨1, one_pos, fun g => ?_⟩
    by_cases hsmall : ‖S.gamma g‖ ≤ R
    · exact absurd ⟨g, by rw [hF, Set.Finite.mem_toFinset]; exact hsmall⟩ hne
    · exact hfar g (lt_of_not_ge hsmall)


/-- **Genuine pole.** At the resolvent pole of an active frequency the transform is unbounded
on every punctured neighbourhood: the reinforced head blows up while the tail stays bounded. -/
theorem exists_norm_poleTransform_gt [Countable G] (hlf : S.IsLocallyFiniteSpectrum)
    (P : Polynomial ℝ) (T : ℝ) {g₀ : G} (hactive : S.traceCoeff P g₀ ≠ 0)
    (C : ℝ) {r : ℝ} (hr : 0 < r) :
    ∃ s : ℂ, ‖s - Complex.I * S.gamma g₀‖ < r ∧ s ∉ S.poleSet ∧
      C < ‖S.poleTransform P T s‖ := by
  classical
  set s₀ : ℂ := Complex.I * S.gamma g₀ with hs₀def
  set n : ℝ := ‖S.gamma g₀‖ with hn
  have hnpos : 0 < n := S.norm_gamma_pos g₀
  have hs₀norm : ‖s₀‖ = n := by rw [hs₀def, norm_mul, Complex.norm_I, one_mul]
  have hs₀sq : s₀ ^ (2 : ℕ) = -S.gamma g₀ ^ (2 : ℕ) := by
    rw [hs₀def, mul_pow, Complex.I_sq]
    ring
  obtain ⟨d, hd, hsep0⟩ := S.exists_square_separation hlf g₀
  set M : ℝ := n + 1 with hM
  set B : ℝ := ∑' g : G, S.poleMajorant P T M (d / 2) g with hB
  set A : ℝ := max (C + B) 1 with hA
  have hApos : 0 < A := lt_of_lt_of_le one_pos (le_max_right _ _)
  -- lower bound on the phase numerator near the pole
  have hcont : ContinuousAt (fun z : ℂ => ‖S.poleNumer T z g₀‖) s₀ :=
    (continuous_norm.comp (S.continuous_poleNumer T g₀)).continuousAt
  have hval : ‖S.poleNumer T s₀ g₀‖ = n := by
    rw [hs₀def, poleNumer_at_pole (S := S) T g₀]
  obtain ⟨r₁, hr₁, hr₁spec⟩ :=
    Metric.continuousAt_iff.mp hcont (n / 2) (by linarith)
  have hcnorm : 0 < ‖S.traceCoeff P g₀‖ := norm_pos_iff.mpr hactive
  set m : ℝ :=
    min r (min r₁ (min 1 (min n (min (d / (6 * n))
      (‖S.traceCoeff P g₀‖ * n / (6 * n * A)))))) with hm
  have hmpos : 0 < m := by
    rw [hm]
    repeat' refine lt_min ?_ ?_
    all_goals positivity
  set δ : ℝ := m / 2 with hδ
  have hδpos : 0 < δ := by rw [hδ]; linarith
  have hδm : δ < m := by rw [hδ]; linarith
  have hδr : δ < r := lt_of_lt_of_le hδm (min_le_left _ _)
  have hδr₁ : δ < r₁ := lt_of_lt_of_le hδm (le_trans (min_le_right _ _) (min_le_left _ _))
  have hδ1 : δ < 1 :=
    lt_of_lt_of_le hδm (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (min_le_left _ _)))
  have hδn : δ < n :=
    lt_of_lt_of_le hδm (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _) (min_le_left _ _))))
  have hδd : δ < d / (6 * n) :=
    lt_of_lt_of_le hδm (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_left _ _)))))
  have hδA : δ < ‖S.traceCoeff P g₀‖ * n / (6 * n * A) :=
    lt_of_lt_of_le hδm (le_trans (min_le_right _ _)
      (le_trans (min_le_right _ _) (le_trans (min_le_right _ _)
        (le_trans (min_le_right _ _) (min_le_right _ _)))))
  set s : ℂ := s₀ + (δ : ℂ) with hs
  have hdiff : s - s₀ = (δ : ℂ) := by rw [hs]; ring
  have hsnorm : ‖s - s₀‖ = δ := by
    rw [hdiff, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδpos]
  -- the shifted denominator
  have hfac : s ^ (2 : ℕ) + S.gamma g₀ ^ (2 : ℕ) = (δ : ℂ) * (2 * s₀ + (δ : ℂ)) := by
    rw [hs]
    linear_combination hs₀sq
  have h2s₀ : n ≤ ‖2 * s₀ + (δ : ℂ)‖ := by
    have h1 : ‖(2 : ℂ) * s₀‖ = 2 * n := by rw [norm_mul]; simp [hs₀norm]
    have h2 := norm_sub_norm_le ((2 : ℂ) * s₀) (-(δ : ℂ))
    have h3 : ‖(-(δ : ℂ))‖ = δ := by
      rw [norm_neg, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδpos]
    rw [h1, h3, sub_neg_eq_add] at h2
    linarith
  have hupper : ‖s ^ (2 : ℕ) + S.gamma g₀ ^ (2 : ℕ)‖ ≤ 3 * n * δ := by
    rw [hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδpos]
    have h1 : ‖2 * s₀ + (δ : ℂ)‖ ≤ 2 * n + δ := by
      refine le_trans (norm_add_le _ _) ?_
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδpos]
      simp [hs₀norm]
    nlinarith [h1, hδn.le, hδpos.le]
  have hsqne : s ^ (2 : ℕ) + S.gamma g₀ ^ (2 : ℕ) ≠ 0 := by
    rw [hfac]
    refine mul_ne_zero ?_ ?_
    · exact_mod_cast ne_of_gt hδpos
    · intro hz
      rw [hz, norm_zero] at h2s₀
      linarith
  have hlower : δ * n ≤ ‖s ^ (2 : ℕ) + S.gamma g₀ ^ (2 : ℕ)‖ := by
    rw [hfac, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδpos]
    exact mul_le_mul_of_nonneg_left h2s₀ hδpos.le
  -- separation for the tail
  have hsep : ∀ g : G, g ∉ S.squareFiber g₀ → d / 2 ≤ ‖s ^ (2 : ℕ) + S.gamma g ^ (2 : ℕ)‖ := by
    intro g hg
    have hsplit : s ^ (2 : ℕ) + S.gamma g ^ (2 : ℕ) =
        (S.gamma g ^ (2 : ℕ) - S.gamma g₀ ^ (2 : ℕ)) + (s ^ (2 : ℕ) + S.gamma g₀ ^ (2 : ℕ)) := by ring
    have h1 := hsep0 g hg
    have h2 := norm_sub_norm_le (S.gamma g ^ (2 : ℕ) - S.gamma g₀ ^ (2 : ℕ)) (-(s ^ (2 : ℕ) + S.gamma g₀ ^ (2 : ℕ)))
    rw [sub_neg_eq_add, norm_neg] at h2
    have h3 : 3 * n * δ ≤ d / 2 := by
      have : δ * (6 * n) < d := by
        rw [lt_div_iff₀ (by positivity)] at hδd
        linarith
      linarith
    rw [hsplit]
    linarith [h2, hupper, h3]
  have hMbound : ‖s‖ ≤ M := by
    refine le_trans (norm_add_le _ _) ?_
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hδpos, hs₀norm, hM]
    linarith
  -- split and estimate
  obtain ⟨tail, hsplit, htail⟩ :=
    S.poleTransform_eq_head_add_tail hlf P T (by linarith : (0:ℝ) < d / 2) hsqne hsep hMbound
  have hnotpole : s ∉ S.poleSet := by
    rintro ⟨g, hg⟩
    by_cases hgm : g ∈ S.squareFiber g₀
    · have hgs : S.gamma g ^ (2 : ℕ) = S.gamma g₀ ^ (2 : ℕ) := hgm
      rw [hgs] at hg
      exact hsqne hg
    · have hb := hsep g hgm
      rw [hg, norm_zero] at hb
      linarith
  refine ⟨s, by rw [hsnorm]; exact hδr, hnotpole, ?_⟩
  -- lower bound for the head
  have hNlow : n / 2 < ‖S.poleNumer T s g₀‖ := by
    have hd' : dist s s₀ < r₁ := by
      rw [Complex.dist_eq, hsnorm]; exact hδr₁
    have hspec := hr₁spec hd'
    rw [Real.dist_eq, hval] at hspec
    have h4 := abs_lt.mp hspec
    linarith [h4.1]
  have hkpos : 1 ≤ ((S.squareFiber_finite hlf g₀).toFinset.card : ℝ) := by
    have hmem : g₀ ∈ (S.squareFiber_finite hlf g₀).toFinset := by
      rw [Set.Finite.mem_toFinset]
      exact rfl
    exact_mod_cast Finset.card_pos.mpr ⟨g₀, hmem⟩
  set X : ℂ := ((S.squareFiber_finite hlf g₀).toFinset.card : ℂ) *
      (S.traceCoeff P g₀ * S.poleNumer T s g₀) / (s ^ (2 : ℕ) + S.gamma g₀ ^ (2 : ℕ)) with hX
  have hXnorm : ‖X‖ =
      ((S.squareFiber_finite hlf g₀).toFinset.card : ℝ) *
        (‖S.traceCoeff P g₀‖ * ‖S.poleNumer T s g₀‖) / ‖s ^ (2 : ℕ) + S.gamma g₀ ^ (2 : ℕ)‖ := by
    rw [hX, norm_div, norm_mul, norm_mul, Complex.norm_natCast]
  have hXlow : A < ‖X‖ := by
    rw [hXnorm]
    have hnum : ‖S.traceCoeff P g₀‖ * (n / 2) ≤
        ((S.squareFiber_finite hlf g₀).toFinset.card : ℝ) *
          (‖S.traceCoeff P g₀‖ * ‖S.poleNumer T s g₀‖) := by
      have h1 : ‖S.traceCoeff P g₀‖ * (n / 2) ≤
          ‖S.traceCoeff P g₀‖ * ‖S.poleNumer T s g₀‖ :=
        mul_le_mul_of_nonneg_left hNlow.le hcnorm.le
      have hxnn : 0 ≤ ‖S.traceCoeff P g₀‖ * ‖S.poleNumer T s g₀‖ := by positivity
      have h2 : ‖S.traceCoeff P g₀‖ * ‖S.poleNumer T s g₀‖ ≤
          ((S.squareFiber_finite hlf g₀).toFinset.card : ℝ) *
            (‖S.traceCoeff P g₀‖ * ‖S.poleNumer T s g₀‖) :=
        le_mul_of_one_le_left hxnn hkpos
      linarith
    have hden : 0 < ‖s ^ (2 : ℕ) + S.gamma g₀ ^ (2 : ℕ)‖ := norm_pos_iff.mpr hsqne
    rw [lt_div_iff₀ hden]
    have hAd : A * ‖s ^ (2 : ℕ) + S.gamma g₀ ^ (2 : ℕ)‖ ≤ A * (3 * n * δ) :=
      mul_le_mul_of_nonneg_left hupper hApos.le
    have hkey : A * (3 * n * δ) < ‖S.traceCoeff P g₀‖ * (n / 2) := by
      have hlt : δ * (6 * n * A) < ‖S.traceCoeff P g₀‖ * n := by
        rw [lt_div_iff₀ (by positivity)] at hδA
        linarith
      nlinarith [hlt]
    linarith [hAd, hkey, hnum]
  have hAC : C + B ≤ A := le_max_left _ _
  have hge : ‖X‖ - ‖tail‖ ≤ ‖X + tail‖ := by
    have h := norm_sub_le (X + tail) tail
    simp only [add_sub_cancel_right] at h
    linarith
  rw [hsplit]
  linarith [hge, htail, hXlow, hAC]


end

end WaveSpectrum

end GaloisForLFunctions.HTGeometry
