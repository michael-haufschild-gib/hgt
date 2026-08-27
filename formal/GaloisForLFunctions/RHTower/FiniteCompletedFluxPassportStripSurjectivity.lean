import GaloisForLFunctions.HTGeometry.AffineFluxTaylorCoeff
import GaloisForLFunctions.RHTower.FiniteCompletedFluxPassportPartnerSurjectivity
import GaloisForLFunctions.RHTower.QuartetPassportStripGuards

noncomputable section

open GaloisForLFunctions.HTGeometry

namespace RHTower

/-- Centered-coordinate image of `1 - ρ` under `z = -i(s - 1/2)`. -/
def stripPassportCenter (ρ : ℂ) : ℂ :=
  Complex.I * (ρ - ((1 / 2 : ℝ) : ℂ))

/-- The strip quartet `1 - ρ, ρ, conj ρ, 1 - conj ρ`, indexed compatibly with
`quartetVertex (stripPassportCenter ρ)`. -/
def stripQuartetPoint (ρ : ℂ) (q : Fin 4) : ℂ :=
  ((1 / 2 : ℝ) : ℂ) + Complex.I * quartetVertex (stripPassportCenter ρ) q

/-- The strip coordinate sends the strip quartet exactly to its centered quartet. -/
theorem stripCoordinate_stripQuartetPoint (ρ : ℂ) (q : Fin 4) :
    -Complex.I * (stripQuartetPoint ρ q - ((1 / 2 : ℝ) : ℂ)) =
      quartetVertex (stripPassportCenter ρ) q := by
  rw [stripQuartetPoint, add_sub_cancel_left, ← mul_assoc]
  have hI : -Complex.I * Complex.I = 1 := by
    rw [neg_mul, Complex.I_mul_I]
    simp
  rw [hI, one_mul]

@[simp] theorem stripQuartetPoint_zero (ρ : ℂ) :
    stripQuartetPoint ρ 0 = 1 - ρ := by
  simp [stripQuartetPoint, stripPassportCenter, quartetVertex]
  rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  ring

@[simp] theorem stripQuartetPoint_one (ρ : ℂ) :
    stripQuartetPoint ρ 1 = ρ := by
  simp [stripQuartetPoint, stripPassportCenter, quartetVertex]
  rw [← mul_assoc, Complex.I_mul_I, neg_one_mul, neg_neg]
  ring

@[simp] theorem stripQuartetPoint_two (ρ : ℂ) :
    stripQuartetPoint ρ 2 = (starRingEnd ℂ) ρ := by
  simp [stripQuartetPoint, stripPassportCenter, quartetVertex, map_sub, map_mul, map_ofNat]
  norm_num
  rw [← mul_assoc, Complex.I_mul_I, neg_one_mul, neg_neg]
  ring

@[simp] theorem stripQuartetPoint_three (ρ : ℂ) :
    stripQuartetPoint ρ 3 = 1 - (starRingEnd ℂ) ρ := by
  simp [stripQuartetPoint, stripPassportCenter, quartetVertex, map_sub, map_mul, map_ofNat]
  norm_num
  rw [← mul_assoc, Complex.I_mul_I, neg_one_mul]
  ring

/-- Affine covariance of completed-flux Taylor coefficients for the quartet strip realizer. -/
theorem fluxGermTaylorCoeff_quartetRealizerStrip
    {a : ℝ} {B : Polynomial ℂ} {s : ℂ} {m : ℕ}
    (hord : analyticOrderAt (quartetRealizer a B)
      (-Complex.I * (s - ((1 / 2 : ℝ) : ℂ))) = m) (n : ℕ) :
    fluxGermTaylorCoeff (quartetRealizerStrip a B) s n =
      (-Complex.I) ^ n * fluxGermTaylorCoeff (quartetRealizer a B)
        (-Complex.I * (s - ((1 / 2 : ℝ) : ℂ))) n := by
  have hfun : quartetRealizerStrip a B =
      (fun w : ℂ => quartetRealizer a B
        ((-Complex.I) * w + Complex.I / 2)) := by
    funext w
    simp only [quartetRealizerStrip]
    congr 1
    push_cast
    ring
  rw [hfun]
  have hcoord : (-Complex.I) * s + Complex.I / 2 =
      -Complex.I * (s - ((1 / 2 : ℝ) : ℂ)) := by
    push_cast
    ring
  have hord' : analyticOrderAt (quartetRealizer a B)
      ((-Complex.I) * s + Complex.I / 2) = m := by
    rw [hcoord]
    exact hord
  have haff := fluxGermTaylorCoeff_comp_affine (f := quartetRealizer a B)
      (z := s) (μ := -Complex.I) (ν := Complex.I / 2) (m := m)
      (by simp) (quartetRealizer_analyticAt a B) hord' n
  rw [hcoord] at haff
  exact haff

/-- Full finite completed-flux passport surjectivity in the critical-strip coordinate.
Every finite graded-real passport is realized simultaneously; every selected partner pair first
separates at its freely prescribed transverse next coefficient. -/
theorem exists_strip_quartet_passport_flux_realizer_of_graded_passport
    {J : Type} [Fintype J] [DecidableEq J] [Nonempty J]
    (ρ : J → ℂ) (N : J → ℕ) (passport : J → ℕ → ℂ) (η : J → ℂ)
    (hpassport0 : ∀ j, passport j 0 = -1)
    (hgraded : ∀ (j : J) (n : ℕ), n ≤ N j →
      passport j n = (-1 : ℂ) ^ n * (starRingEnd ℂ) (passport j n))
    (hη : ∀ j, η j ≠
      (-1 : ℂ) ^ (N j + 1) * (starRingEnd ℂ) (η j))
    (_hρre : ∀ j, 0 < (ρ j).re ∧ (ρ j).re < 1 / 2)
    (hρim : ∀ j, 0 < (ρ j).im)
    (hinj : Function.Injective
      (fun i : J × Fin 4 => stripQuartetPoint (ρ i.1) i.2)) :
    ∃ a₀ : ℝ, 0 < a₀ ∧ ∃ B : Polynomial ℂ,
      0 < B.degree ∧
      (∀ s : ℂ, AnalyticAt ℂ (quartetRealizerStrip a₀ B) s) ∧
      (∀ s : ℂ, quartetRealizerStrip a₀ B (1 - s) = quartetRealizerStrip a₀ B s) ∧
      (∀ s : ℂ, quartetRealizerStrip a₀ B ((starRingEnd ℂ) s) =
        (starRingEnd ℂ) (quartetRealizerStrip a₀ B s)) ∧
      (∀ t : ℝ, quartetRealizerStrip a₀ B (t : ℂ) ≠ 0) ∧
      (∀ h : ℂ, Function.Periodic (quartetRealizerStrip a₀ B) h → h = 0) ∧
      (∃ Kupper Klower R : ℝ,
        0 < Kupper ∧ 0 < Klower ∧
        (∀ s : ℂ, ‖quartetRealizerStrip a₀ B s‖ ≤
          Kupper * (1 + ‖s‖) ^ B.natDegree * Real.exp (2 * ‖s‖)) ∧
        ∀ x : ℝ, R ≤ x → Klower * Real.exp (2 * x) ≤
          ‖quartetRealizerStrip a₀ B
            (((1 / 2 : ℝ) : ℂ) + Complex.I * (x : ℂ))‖) ∧
      (∀ i : J × Fin 4,
        quartetRealizerStrip a₀ B (stripQuartetPoint (ρ i.1) i.2) = 0 ∧
        deriv (quartetRealizerStrip a₀ B) (stripQuartetPoint (ρ i.1) i.2) ≠ 0) ∧
      (∀ (j : J) (n : ℕ), n ≤ N j →
        fluxGermTaylorCoeff (quartetRealizerStrip a₀ B) (1 - ρ j) n = passport j n ∧
        fluxGermTaylorCoeff (quartetRealizerStrip a₀ B) ((starRingEnd ℂ) (ρ j)) n =
          passport j n) ∧
      ∀ j : J,
        fluxGermTaylorCoeff (quartetRealizerStrip a₀ B) (1 - ρ j) (N j + 1) = η j ∧
        fluxGermTaylorCoeff (quartetRealizerStrip a₀ B) ((starRingEnd ℂ) (ρ j))
            (N j + 1) =
          (-1 : ℂ) ^ (N j + 1) * (starRingEnd ℂ) (η j) ∧
        fluxGermTaylorCoeff (quartetRealizerStrip a₀ B) (1 - ρ j) (N j + 1) ≠
          fluxGermTaylorCoeff (quartetRealizerStrip a₀ B) ((starRingEnd ℂ) (ρ j))
            (N j + 1) := by
  let β : J → ℂ := fun j => stripPassportCenter (ρ j)
  let target : J → ℕ → ℂ := fun j n => if n ≤ N j then passport j n else η j
  let jet : J → ℕ → ℂ := fun j n =>
    (n.factorial : ℂ) * Complex.I ^ n * target j n
  have hjet0 : ∀ j, jet j 0 = -1 := by
    intro j
    simp [jet, target, hpassport0]
  have hβre : ∀ j, (β j).re ≠ 0 := by
    intro j
    simpa [β, stripPassportCenter] using neg_ne_zero.mpr (ne_of_gt (hρim j))
  have hinjβ : Function.Injective
      (fun i : J × Fin 4 => quartetVertex (β i.1) i.2) := by
    intro i i' hii'
    apply hinj
    have := congrArg (fun z : ℂ => ((1 / 2 : ℝ) : ℂ) + Complex.I * z) hii'
    simpa [stripQuartetPoint, β] using this
  obtain ⟨a₀, ha₀, B, hdeg, heven, hreal, haxis, hperiod, horder,
      hsimple, hjets⟩ :=
    exists_quartet_passport_flux_realizer_of_full_finite_jet_passport
      β (fun j => N j + 1) jet hjet0 hβre hinjβ
  have hf : ∀ z, AnalyticAt ℂ (quartetRealizer a₀ B) z :=
    quartetRealizer_analyticAt a₀ B
  have hord (i : J × Fin 4) :
      analyticOrderAt (quartetRealizer a₀ B) (quartetVertex (β i.1) i.2) = (1 : ℕ) :=
    (hf _).analyticOrderAt_eq_one_of_zero_deriv_ne_zero (hsimple i).1 (hsimple i).2
  have hcenterCoeff (j : J) (n : ℕ) (hn : n ≤ N j + 1) :
      fluxGermTaylorCoeff (quartetRealizer a₀ B) (quartetVertex (β j) 0) n =
        Complex.I ^ n * target j n := by
    rw [fluxGermTaylorCoeff, hjets j 0 n hn]
    have hfac : (n.factorial : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    simp [quartetFluxJet, jet]
    field_simp
  have hconjCenterCoeff (j : J) (n : ℕ) (hn : n ≤ N j + 1) :
      fluxGermTaylorCoeff (quartetRealizer a₀ B) (quartetVertex (β j) 2) n =
        (-Complex.I) ^ n * (starRingEnd ℂ) (target j n) := by
    rw [fluxGermTaylorCoeff, hjets j 2 n hn]
    have hfac : (n.factorial : ℂ) ≠ 0 := by
      exact_mod_cast Nat.factorial_ne_zero n
    simp [quartetFluxJet, jet, map_mul, map_pow]
    field_simp
  have hnegIpowI (n : ℕ) : (-Complex.I) ^ n * Complex.I ^ n = 1 := by
    rw [← mul_pow]
    have hI : -Complex.I * Complex.I = 1 := by
      rw [neg_mul, Complex.I_mul_I]
      simp
    rw [hI, one_pow]
  have hnegIsq (n : ℕ) : (-Complex.I) ^ n * (-Complex.I) ^ n = (-1 : ℂ) ^ n := by
    rw [← mul_pow]
    congr 1
    rw [neg_mul_neg, Complex.I_mul_I]
  have hstripCoeff0 (j : J) (n : ℕ) (hn : n ≤ N j + 1) :
      fluxGermTaylorCoeff (quartetRealizerStrip a₀ B) (stripQuartetPoint (ρ j) 0) n =
        target j n := by
    have hord0 : analyticOrderAt (quartetRealizer a₀ B)
        (-Complex.I *
          (stripQuartetPoint (ρ j) 0 - ((1 / 2 : ℝ) : ℂ))) = (1 : ℕ) := by
      rw [stripCoordinate_stripQuartetPoint]
      simpa [β] using hord (j, 0)
    rw [fluxGermTaylorCoeff_quartetRealizerStrip hord0]
    rw [stripCoordinate_stripQuartetPoint, hcenterCoeff j n hn]
    rw [← mul_assoc, hnegIpowI, one_mul]
  have hstripCoeff2 (j : J) (n : ℕ) (hn : n ≤ N j + 1) :
      fluxGermTaylorCoeff (quartetRealizerStrip a₀ B) (stripQuartetPoint (ρ j) 2) n =
        (-1 : ℂ) ^ n * (starRingEnd ℂ) (target j n) := by
    have hord2 : analyticOrderAt (quartetRealizer a₀ B)
        (-Complex.I *
          (stripQuartetPoint (ρ j) 2 - ((1 / 2 : ℝ) : ℂ))) = (1 : ℕ) := by
      rw [stripCoordinate_stripQuartetPoint]
      simpa [β] using hord (j, 2)
    rw [fluxGermTaylorCoeff_quartetRealizerStrip hord2]
    rw [stripCoordinate_stripQuartetPoint, hconjCenterCoeff j n hn]
    rw [← mul_assoc, hnegIsq]
  refine ⟨a₀, ha₀, B, hdeg, quartetRealizerStrip_analyticAt a₀ B, ?_, ?_, ?_, ?_,
    quartetRealizerStrip_exact_order_one_bounds_of_centered horder, ?_, ?_, ?_⟩
  · intro s
    change quartetRealizer a₀ B
        (-Complex.I * ((1 - s) - ((1 / 2 : ℝ) : ℂ))) =
      quartetRealizer a₀ B (-Complex.I * (s - ((1 / 2 : ℝ) : ℂ)))
    rw [show -Complex.I * ((1 - s) - ((1 / 2 : ℝ) : ℂ)) =
      -(-Complex.I * (s - ((1 / 2 : ℝ) : ℂ))) by push_cast; ring, heven]
  · intro s
    change quartetRealizer a₀ B
        (-Complex.I * ((starRingEnd ℂ) s - ((1 / 2 : ℝ) : ℂ))) =
      (starRingEnd ℂ)
        (quartetRealizer a₀ B (-Complex.I * (s - ((1 / 2 : ℝ) : ℂ))))
    have hcoord : -Complex.I * ((starRingEnd ℂ) s - ((1 / 2 : ℝ) : ℂ)) =
        -((starRingEnd ℂ) (-Complex.I * (s - ((1 / 2 : ℝ) : ℂ)))) := by
      rw [map_mul, map_sub, map_neg, Complex.conj_I, Complex.conj_ofReal]
      ring
    rw [hcoord, heven, hreal]
  · intro t
    have hcoord : -Complex.I * ((t : ℂ) - ((1 / 2 : ℝ) : ℂ)) =
        ((1 / 2 - t : ℝ) : ℂ) * Complex.I := by
      push_cast
      ring_nf
    rw [quartetRealizerStrip, hcoord]
    exact haxis (1 / 2 - t)
  · intro h hh
    exact quartetRealizerStrip_period_eq_zero_of_centered hperiod hh
  · intro i
    have hs := hsimple i
    constructor
    · rw [quartetRealizerStrip, stripCoordinate_stripQuartetPoint]
      exact hs.1
    · rw [deriv_quartetRealizerStrip, stripCoordinate_stripQuartetPoint]
      exact mul_ne_zero (by simp) hs.2
  · intro j n hn
    constructor
    · simpa [target, hn] using hstripCoeff0 j n (hn.trans (Nat.le_succ _))
    · rw [← stripQuartetPoint_two]
      rw [hstripCoeff2 j n (hn.trans (Nat.le_succ _))]
      simpa [target, hn] using (hgraded j n hn).symm
  · intro j
    have hn : N j + 1 ≤ N j + 1 := le_rfl
    have hnot : ¬ N j + 1 ≤ N j := Nat.not_succ_le_self (N j)
    have hfirst :
        fluxGermTaylorCoeff (quartetRealizerStrip a₀ B) (1 - ρ j) (N j + 1) = η j := by
      rw [← stripQuartetPoint_zero]
      simpa [target, hnot] using hstripCoeff0 j (N j + 1) hn
    have hsecond :
        fluxGermTaylorCoeff (quartetRealizerStrip a₀ B) ((starRingEnd ℂ) (ρ j))
            (N j + 1) =
          (-1 : ℂ) ^ (N j + 1) * (starRingEnd ℂ) (η j) := by
      rw [← stripQuartetPoint_two]
      simpa [target, hnot] using hstripCoeff2 j (N j + 1) hn
    exact ⟨hfirst, hsecond, hfirst.symm ▸ hsecond.symm ▸ hη j⟩

end RHTower
