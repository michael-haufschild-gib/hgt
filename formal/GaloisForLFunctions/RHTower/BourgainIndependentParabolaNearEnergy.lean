/-
# Sharp near energy for two independent parabola triples

In osculating phase coordinates, two separated quadratic curve pieces become
independent copies of `(s,s²)`.  Natural coordinate scales force every near
pair to agree in all four integer moments.  The two Eisenstein-divisor fiber
bounds then factor and give an `H^ε` estimate.
-/
import GaloisForLFunctions.RHTower.BourgainPairedTripleNearPerturbation
import GaloisForLFunctions.RHTower.BourgainSquareRootQuadraticNearEnergy

open scoped BigOperators

namespace RHTower

noncomputable section

/-- Left copy of a sampled discrete parabola in four-dimensional phase
coordinates. -/
def bourgainLeftParabolaSample
    {H : ℕ} (D : ℝ) (n : Fin H) : BourgainPhaseSpace :=
  ![(bourgainIndex n : ℝ) / D,
    ((bourgainIndex n : ℝ) / D) ^ (2 : ℕ), 0, 0]

/-- Right independent copy of the sampled parabola. -/
def bourgainRightParabolaSample
    {H : ℕ} (D : ℝ) (n : Fin H) : BourgainPhaseSpace :=
  ![0, 0, (bourgainIndex n : ℝ) / D,
    ((bourgainIndex n : ℝ) / D) ^ (2 : ℕ)]

theorem bourgainPairedTripleCloud_leftRight_zero
    {H : ℕ} (D : ℝ)
    (hk : (Fin 3 → Fin H) × (Fin 3 → Fin H)) :
    bourgainPairedTripleCloud
        (bourgainLeftParabolaSample D)
        (bourgainRightParabolaSample D) hk 0 =
      ((bourgainParabolaTripleMoment hk.1).1 : ℝ) / D := by
  simp [bourgainPairedTripleCloud, bourgainTripleCloud,
    bourgainLeftParabolaSample, bourgainRightParabolaSample,
    bourgainParabolaTripleMoment, Fin.sum_univ_three]
  ring

theorem bourgainPairedTripleCloud_leftRight_one
    {H : ℕ} (D : ℝ)
    (hk : (Fin 3 → Fin H) × (Fin 3 → Fin H)) :
    bourgainPairedTripleCloud
        (bourgainLeftParabolaSample D)
        (bourgainRightParabolaSample D) hk 1 =
      ((bourgainParabolaTripleMoment hk.1).2 : ℝ) /
        D ^ (2 : ℕ) := by
  simp [bourgainPairedTripleCloud, bourgainTripleCloud,
    bourgainLeftParabolaSample, bourgainRightParabolaSample,
    bourgainParabolaTripleMoment, Fin.sum_univ_three]
  field_simp
  ring

theorem bourgainPairedTripleCloud_leftRight_two
    {H : ℕ} (D : ℝ)
    (hk : (Fin 3 → Fin H) × (Fin 3 → Fin H)) :
    bourgainPairedTripleCloud
        (bourgainLeftParabolaSample D)
        (bourgainRightParabolaSample D) hk 2 =
      ((bourgainParabolaTripleMoment hk.2).1 : ℝ) / D := by
  simp [bourgainPairedTripleCloud, bourgainTripleCloud,
    bourgainLeftParabolaSample, bourgainRightParabolaSample,
    bourgainParabolaTripleMoment, Fin.sum_univ_three]
  ring

theorem bourgainPairedTripleCloud_leftRight_three
    {H : ℕ} (D : ℝ)
    (hk : (Fin 3 → Fin H) × (Fin 3 → Fin H)) :
    bourgainPairedTripleCloud
        (bourgainLeftParabolaSample D)
        (bourgainRightParabolaSample D) hk 3 =
      ((bourgainParabolaTripleMoment hk.2).2 : ℝ) /
        D ^ (2 : ℕ) := by
  simp [bourgainPairedTripleCloud, bourgainTripleCloud,
    bourgainLeftParabolaSample, bourgainRightParabolaSample,
    bourgainParabolaTripleMoment, Fin.sum_univ_three]
  field_simp
  ring

/-- A natural-scale near pair in the independent model agrees in both
parabola moment pairs. -/
theorem bourgainIndependentParabolaMoments_eq_of_near
    {H : ℕ} {D : ℝ} (hD : 0 < D)
    {Y : BourgainPhaseSpace}
    (hY0 : D ≤ 2 * Y 0)
    (hY1 : D ^ (2 : ℕ) ≤ 2 * Y 1)
    (hY2 : D ≤ 2 * Y 2)
    (hY3 : D ^ (2 : ℕ) ≤ 2 * Y 3)
    {hk hk' : (Fin 3 → Fin H) × (Fin 3 → Fin H)}
    (hnear :
      BourgainScaledNear Y
        (bourgainPairedTripleCloud
          (bourgainLeftParabolaSample D)
          (bourgainRightParabolaSample D) hk)
        (bourgainPairedTripleCloud
          (bourgainLeftParabolaSample D)
          (bourgainRightParabolaSample D) hk')) :
    bourgainParabolaTripleMoment hk.1 =
        bourgainParabolaTripleMoment hk'.1 ∧
      bourgainParabolaTripleMoment hk.2 =
        bourgainParabolaTripleMoment hk'.2 := by
  constructor
  · apply Prod.ext
    · apply nat_eq_of_scaled_div_near hD hY0
      have h := hnear (0 : Fin 4)
      rw [bourgainPairedTripleCloud_leftRight_zero,
        bourgainPairedTripleCloud_leftRight_zero] at h
      exact h
    · apply nat_eq_of_scaled_div_near (sq_pos_of_pos hD) hY1
      have h := hnear (1 : Fin 4)
      rw [bourgainPairedTripleCloud_leftRight_one,
        bourgainPairedTripleCloud_leftRight_one] at h
      exact h
  · apply Prod.ext
    · apply nat_eq_of_scaled_div_near hD hY2
      have h := hnear (2 : Fin 4)
      rw [bourgainPairedTripleCloud_leftRight_two,
        bourgainPairedTripleCloud_leftRight_two] at h
      exact h
    · apply nat_eq_of_scaled_div_near (sq_pos_of_pos hD) hY3
      have h := hnear (3 : Fin 4)
      rw [bourgainPairedTripleCloud_leftRight_three,
        bourgainPairedTripleCloud_leftRight_three] at h
      exact h

/-- The independent-model near energy is dominated by the product of the two
exact moment-pair energies. -/
theorem bourgainIndependentParabola_nearEnergy_le
    {H : ℕ} {D : ℝ} (hD : 0 < D)
    (Y : BourgainPhaseSpace)
    (hY0 : D ≤ 2 * Y 0)
    (hY1 : D ^ (2 : ℕ) ≤ 2 * Y 1)
    (hY2 : D ≤ 2 * Y 2)
    (hY3 : D ^ (2 : ℕ) ≤ 2 * Y 3)
    (w₁ w₂ : (Fin 3 → Fin H) → ℝ)
    (hw₁ : ∀ h, 0 ≤ w₁ h)
    (hw₂ : ∀ h, 0 ≤ w₂ h) :
    bourgainWeightedScaledNearEnergy Y
        (bourgainPairedTripleCloud
          (bourgainLeftParabolaSample D)
          (bourgainRightParabolaSample D))
        (fun hk => w₁ hk.1 * w₂ hk.2) ≤
      (∑ h : Fin 3 → Fin H, ∑ h' : Fin 3 → Fin H,
        if bourgainParabolaTripleMoment h =
            bourgainParabolaTripleMoment h'
        then w₁ h * w₁ h' else 0) *
      (∑ k : Fin 3 → Fin H, ∑ k' : Fin 3 → Fin H,
        if bourgainParabolaTripleMoment k =
            bourgainParabolaTripleMoment k'
        then w₂ k * w₂ k' else 0) := by
  classical
  let A : (Fin 3 → Fin H) → (Fin 3 → Fin H) → ℝ :=
    fun h h' =>
      if bourgainParabolaTripleMoment h =
          bourgainParabolaTripleMoment h'
      then w₁ h * w₁ h' else 0
  let B : (Fin 3 → Fin H) → (Fin 3 → Fin H) → ℝ :=
    fun k k' =>
      if bourgainParabolaTripleMoment k =
          bourgainParabolaTripleMoment k'
      then w₂ k * w₂ k' else 0
  calc
    bourgainWeightedScaledNearEnergy Y
          (bourgainPairedTripleCloud
            (bourgainLeftParabolaSample D)
            (bourgainRightParabolaSample D))
          (fun hk => w₁ hk.1 * w₂ hk.2)
        ≤ ∑ hk :
              (Fin 3 → Fin H) × (Fin 3 → Fin H),
            ∑ hk' :
              (Fin 3 → Fin H) × (Fin 3 → Fin H),
              A hk.1 hk'.1 * B hk.2 hk'.2 := by
          unfold bourgainWeightedScaledNearEnergy
          apply Finset.sum_le_sum
          intro hk hhk
          apply Finset.sum_le_sum
          intro hk' hhk'
          by_cases hnear :
              BourgainScaledNear Y
                (bourgainPairedTripleCloud
                  (bourgainLeftParabolaSample D)
                  (bourgainRightParabolaSample D) hk)
                (bourgainPairedTripleCloud
                  (bourgainLeftParabolaSample D)
                  (bourgainRightParabolaSample D) hk')
          · obtain ⟨hleft, hright⟩ :=
              bourgainIndependentParabolaMoments_eq_of_near
                hD hY0 hY1 hY2 hY3 hnear
            simp [hnear, A, B, hleft, hright]
            ring
          · simp only [hnear, if_false]
            dsimp [A, B]
            split_ifs <;> positivity
    _ = (∑ h : Fin 3 → Fin H, ∑ h' : Fin 3 → Fin H, A h h') *
          (∑ k : Fin 3 → Fin H, ∑ k' : Fin 3 → Fin H, B k k') := by
      simp_rw [Fintype.sum_prod_type]
      rw [Fintype.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro h hh
      rw [Fintype.sum_mul_sum]
      apply Finset.sum_congr rfl
      intro h' hh'
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro k' hk'
      ring
    _ = _ := by rfl

/-- Sharp subpower near-energy bound for two independent parabola triples. -/
theorem bourgainIndependentParabola_nearEnergy_subpower
    {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧
      ∀ (H : ℕ), 0 < H →
      ∀ (D : ℝ), 0 < D →
      ∀ (Y : BourgainPhaseSpace),
        D ≤ 2 * Y 0 →
        D ^ (2 : ℕ) ≤ 2 * Y 1 →
        D ≤ 2 * Y 2 →
        D ^ (2 : ℕ) ≤ 2 * Y 3 →
      ∀ (w₁ w₂ : (Fin 3 → Fin H) → ℝ),
        (∀ h, 0 ≤ w₁ h) →
        (∀ h, 0 ≤ w₂ h) →
        bourgainWeightedScaledNearEnergy Y
            (bourgainPairedTripleCloud
              (bourgainLeftParabolaSample D)
              (bourgainRightParabolaSample D))
            (fun hk => w₁ hk.1 * w₂ hk.2) ≤
          C * (H : ℝ) ^ ε *
            (∑ h : Fin 3 → Fin H, w₁ h ^ (2 : ℕ)) *
            (∑ k : Fin 3 → Fin H, w₂ k ^ (2 : ℕ)) := by
  obtain ⟨C₀, hC₀, hmoment⟩ :=
    bourgainMomentPairEnergy_subpower
      (show 0 < ε / 2 by linarith)
  refine ⟨C₀ ^ (2 : ℕ), sq_pos_of_pos hC₀, ?_⟩
  intro H hH D hD Y hY0 hY1 hY2 hY3 w₁ w₂ hw₁ hw₂
  let E₁ : ℝ :=
    ∑ h : Fin 3 → Fin H, ∑ h' : Fin 3 → Fin H,
      if bourgainParabolaTripleMoment h =
          bourgainParabolaTripleMoment h'
      then w₁ h * w₁ h' else 0
  let E₂ : ℝ :=
    ∑ k : Fin 3 → Fin H, ∑ k' : Fin 3 → Fin H,
      if bourgainParabolaTripleMoment k =
          bourgainParabolaTripleMoment k'
      then w₂ k * w₂ k' else 0
  have hE₁0 : 0 ≤ E₁ := by
    dsimp [E₁]
    positivity
  have hE₂0 : 0 ≤ E₂ := by
    dsimp [E₂]
    positivity
  have h₁ :
      E₁ ≤ C₀ * (H : ℝ) ^ (ε / 2) *
        ∑ h : Fin 3 → Fin H, w₁ h ^ (2 : ℕ) :=
    hmoment H w₁ hw₁
  have h₂ :
      E₂ ≤ C₀ * (H : ℝ) ^ (ε / 2) *
        ∑ h : Fin 3 → Fin H, w₂ h ^ (2 : ℕ) :=
    hmoment H w₂ hw₂
  have hHr : (0 : ℝ) < H := by exact_mod_cast hH
  calc
    _ ≤ E₁ * E₂ :=
      bourgainIndependentParabola_nearEnergy_le
        hD Y hY0 hY1 hY2 hY3 w₁ w₂ hw₁ hw₂
    _ ≤
        (C₀ * (H : ℝ) ^ (ε / 2) *
            ∑ h : Fin 3 → Fin H, w₁ h ^ (2 : ℕ)) *
          (C₀ * (H : ℝ) ^ (ε / 2) *
            ∑ k : Fin 3 → Fin H, w₂ k ^ (2 : ℕ)) := by
      exact mul_le_mul h₁ h₂ hE₂0
        (mul_nonneg
          (mul_nonneg hC₀.le (Real.rpow_nonneg hHr.le _))
          (Finset.sum_nonneg fun h hh => sq_nonneg _))
    _ = C₀ ^ (2 : ℕ) * (H : ℝ) ^ ε *
          (∑ h : Fin 3 → Fin H, w₁ h ^ (2 : ℕ)) *
          (∑ k : Fin 3 → Fin H, w₂ k ^ (2 : ℕ)) := by
      rw [show ε = ε / 2 + ε / 2 by ring, Real.rpow_add hHr]
      ring

end

end RHTower
