import GaloisForLFunctions.RHTower.RadialLeakageWeakConvergenceTransfer

open MeasureTheory Filter Set

noncomputable section

namespace RHTower

/-- Literal diagonal of the finite-aperture radial dilation Gram matrix.  This is equation `(20)`
before its elementary dilation change of variables. -/
def radialLeakageGramDiagonal (lam k : ℝ) (q : ℝ → ℂ) : ℝ :=
  lam * ∫ x in Ioi (1 : ℝ), ‖q (lam * (k * x))‖ ^ (2 : ℕ)

/-- Exact finite-aperture identity relating the literal radial Gram diagonal to the `k`-tail of
the normalized leakage density, including the load-bearing factor `1/k`. -/
theorem radialLeakageGramDiagonal_eq_scaled_nuLambda_tail
    {lam d k : ℝ} (hlam : 0 < lam) (hd : d ≠ 0) (hk : 0 < k) (q : ℝ → ℂ) :
    radialLeakageGramDiagonal lam k q / d =
      (1 / k) * ∫ y in Ioi k, nuLambdaDensity lam d q y := by
  have hscale := integral_comp_mul_left_Ioi
    (fun y : ℝ => ‖q (lam * y)‖ ^ (2 : ℕ)) 1 hk
  simp only [mul_one, smul_eq_mul] at hscale
  unfold radialLeakageGramDiagonal nuLambdaDensity
  rw [integral_div, integral_const_mul]
  rw [hscale]
  field_simp

/-- A tail integral over `Ioi k`, `k ≥ 1`, is exactly the corresponding indicator test over the
base radial ray `Ioi 1`. -/
theorem integral_Ioi_eq_integral_Ioi_indicator_tail
    {f : ℝ → ℝ} {k : ℝ} (hk : 1 ≤ k) :
    ∫ x in Ioi (1 : ℝ), (Ioi k).indicator (fun _ => (1 : ℝ)) x * f x =
      ∫ x in Ioi k, f x := by
  have hsub : Ioi k ⊆ Ioi (1 : ℝ) := fun x hx => lt_of_le_of_lt hk hx
  calc
    ∫ x in Ioi (1 : ℝ), (Ioi k).indicator (fun _ => (1 : ℝ)) x * f x =
        ∫ x, (Ioi (1 : ℝ)).indicator
          (fun x => (Ioi k).indicator (fun _ => (1 : ℝ)) x * f x) x := by
            rw [integral_indicator measurableSet_Ioi]
    _ = ∫ x, (Ioi k).indicator f x := by
          apply integral_congr_ae
          exact Eventually.of_forall fun x => by
            by_cases hx : x ∈ Ioi k
            · have hx1 : x ∈ Ioi (1 : ℝ) := hsub hx
              simp [Set.indicator_of_mem hx, Set.indicator_of_mem hx1]
            · simp [Set.indicator_of_notMem hx]
    _ = ∫ x in Ioi k, f x := by
          rw [integral_indicator measurableSet_Ioi]

/-- The literal normalized finite radial Gram diagonal converges to the card's exact arcsine
spectrum once the pointwise finite-density law and its mass convergence hold. -/
theorem radialLeakageGramDiagonal_tendsto
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {lam d : ι → ℝ} {q : ι → ℝ → ℂ}
    (hparam : ∀ᶠ i in l, 0 < lam i ∧ 0 < d i)
    (hint : ∀ᶠ i in l,
      Integrable (nuLambdaDensity (lam i) (d i) (q i))
        (volume.restrict (Ioi (1 : ℝ))))
    (hae : ∀ᵐ x ∂(volume.restrict (Ioi (1 : ℝ))),
      Tendsto (fun i => nuLambdaDensity (lam i) (d i) (q i) x) l
        (nhds (nuInfinityDensity x)))
    (hmass : Tendsto (fun i =>
      ∫ x in Ioi (1 : ℝ), nuLambdaDensity (lam i) (d i) (q i) x)
        l (nhds (4 / 11)))
    {k : ℝ} (hk : 1 ≤ k) :
    Tendsto (fun i => radialLeakageGramDiagonal (lam i) k (q i) / d i)
      l (nhds (8 / (11 * Real.pi * k) * Real.arcsin (1 / k))) := by
  have hconv := nuLambdaDensity_tendsto_radialGramDiagonal
    (hparam.mono fun _ hi => ⟨hi.1.le, hi.2⟩) hint hae hmass hk
  apply hconv.congr'
  filter_upwards [hparam] with i hi
  rw [radialLeakageGramDiagonal_eq_scaled_nuLambda_tail hi.1 hi.2.ne'
    (lt_of_lt_of_le one_pos hk)]
  rw [integral_Ioi_eq_integral_Ioi_indicator_tail hk]

theorem integral_Ioi_nuLambdaDensity_eq_scaled_tail
    {lam d : ℝ} (hlam : 0 < lam) (hd : d ≠ 0) (q : ℝ → ℂ) :
    ∫ x in Ioi (1 : ℝ), nuLambdaDensity lam d q x =
      (∫ y in Ioi lam, ‖q y‖ ^ (2 : ℕ)) / d := by
  have hscale := integral_comp_mul_left_Ioi (fun y : ℝ => ‖q y‖ ^ (2 : ℕ)) 1 hlam
  simp only [mul_one, smul_eq_mul] at hscale
  change (∫ x in Ioi (1 : ℝ), lam * ‖q (lam * x)‖ ^ (2 : ℕ) / d) = _
  rw [integral_div, integral_const_mul, hscale]
  field_simp

theorem integrableOn_Ioi_nuLambdaDensity
    {lam d : ℝ} (hlam : 0 < lam) (q : ℝ → ℂ)
    (hq : IntegrableOn (fun y : ℝ => ‖q y‖ ^ (2 : ℕ)) (Ioi lam)) :
    IntegrableOn (nuLambdaDensity lam d q) (Ioi (1 : ℝ)) := by
  have hcomp : IntegrableOn (fun x : ℝ => ‖q (lam * x)‖ ^ (2 : ℕ)) (Ioi (1 : ℝ)) := by
    exact (integrableOn_Ioi_comp_mul_left_iff (fun y : ℝ => ‖q y‖ ^ (2 : ℕ)) 1 hlam).2
      (by simpa using hq)
  exact (hcomp.const_mul lam).div_const d

theorem integral_Iic_norm_sq_eq_integral_Ioi_of_even
    {lam : ℝ} {q : ℝ → ℂ} (hq : Function.Even q) :
    ∫ y in Iic (-lam), ‖q y‖ ^ (2 : ℕ) = ∫ y in Ioi lam, ‖q y‖ ^ (2 : ℕ) := by
  have href := integral_comp_neg_Iic (-lam) (fun y : ℝ => ‖q y‖ ^ (2 : ℕ))
  simp only [neg_neg] at href
  rw [← href]
  apply setIntegral_congr_fun measurableSet_Iic
  intro y _
  change ‖q y‖ ^ (2 : ℕ) = ‖q (-y)‖ ^ (2 : ℕ)
  rw [hq y]

theorem integral_Ioi_nuLambdaDensity_eq_half_exterior
    {lam d delta : ℝ} (hlam : 0 < lam) (hd : d ≠ 0) {q : ℝ → ℂ}
    (hq : Function.Even q)
    (hexterior :
      (∫ y in Iic (-lam), ‖q y‖ ^ (2 : ℕ)) + ∫ y in Ioi lam, ‖q y‖ ^ (2 : ℕ) = delta) :
    ∫ x in Ioi (1 : ℝ), nuLambdaDensity lam d q x = delta / (2 * d) := by
  rw [integral_Ioi_nuLambdaDensity_eq_scaled_tail hlam hd]
  have heven := integral_Iic_norm_sq_eq_integral_Ioi_of_even (lam := lam) hq
  rw [heven] at hexterior
  rw [← hexterior]
  field_simp
  ring

theorem tendsto_integral_Ioi_nuLambdaDensity_of_exterior_ratio
    {ι : Type*} {l : Filter ι} {lam d delta : ι → ℝ} {q : ι → ℝ → ℂ}
    (hparam : ∀ᶠ i in l, 0 < lam i ∧ d i ≠ 0)
    (hq : ∀ i, Function.Even (q i))
    (hexterior : ∀ i,
      (∫ y in Iic (-lam i), ‖q i y‖ ^ (2 : ℕ)) + ∫ y in Ioi (lam i), ‖q i y‖ ^ (2 : ℕ) = delta i)
    (hratio : Tendsto (fun i => delta i / d i) l (nhds (8 / 11))) :
    Tendsto (fun i => ∫ x in Ioi (1 : ℝ), nuLambdaDensity (lam i) (d i) (q i) x)
      l (nhds (4 / 11)) := by
  have hhalf : Tendsto (fun i => (1 / 2 : ℝ) * (delta i / d i)) l
      (nhds ((1 / 2 : ℝ) * (8 / 11))) := hratio.const_mul (1 / 2)
  have heq : (fun i => ∫ x in Ioi (1 : ℝ),
      nuLambdaDensity (lam i) (d i) (q i) x) =ᶠ[l]
      (fun i => (1 / 2 : ℝ) * (delta i / d i)) := by
    filter_upwards [hparam] with i hi
    rw [integral_Ioi_nuLambdaDensity_eq_half_exterior hi.1 hi.2 (hq i) (hexterior i)]
    ring
  convert hhalf.congr' heq.symm using 1
  norm_num

/-- Scheffé transfer with total-mass convergence discharged exactly from evenness and normalized
exterior leakage.  The only asymptotic input left is the pointwise radial density law. -/
theorem nuLambdaDensity_tendsto_L1_of_exterior_ratio
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {lam d delta : ι → ℝ} {q : ι → ℝ → ℂ}
    (hparam : ∀ᶠ i in l, 0 < lam i ∧ 0 < d i)
    (hqeven : ∀ i, Function.Even (q i))
    (hexterior : ∀ i,
      (∫ y in Iic (-lam i), ‖q i y‖ ^ (2 : ℕ)) + ∫ y in Ioi (lam i), ‖q i y‖ ^ (2 : ℕ) = delta i)
    (hratio : Tendsto (fun i => delta i / d i) l (nhds (8 / 11)))
    (hqint : ∀ᶠ i in l,
      IntegrableOn (fun y : ℝ => ‖q i y‖ ^ (2 : ℕ)) (Ioi (lam i)))
    (hae : ∀ᵐ x ∂(volume.restrict (Ioi (1 : ℝ))),
      Tendsto (fun i => nuLambdaDensity (lam i) (d i) (q i) x) l
        (nhds (nuInfinityDensity x))) :
    Tendsto (fun i =>
      ∫ x in Ioi (1 : ℝ),
        |nuLambdaDensity (lam i) (d i) (q i) x - nuInfinityDensity x|)
      l (nhds 0) := by
  have hparamWeak : ∀ᶠ i in l, 0 ≤ lam i ∧ 0 < d i :=
    hparam.mono fun _ hi => ⟨hi.1.le, hi.2⟩
  have hint : ∀ᶠ i in l,
      Integrable (nuLambdaDensity (lam i) (d i) (q i))
        (volume.restrict (Ioi (1 : ℝ))) := by
    filter_upwards [hparam, hqint] with i hi hqi
    exact integrableOn_Ioi_nuLambdaDensity hi.1 (q i) hqi
  have hmass := tendsto_integral_Ioi_nuLambdaDensity_of_exterior_ratio
    (hparam.mono fun _ hi => ⟨hi.1, hi.2.ne'⟩) hqeven hexterior hratio
  exact nuLambdaDensity_tendsto_L1 hparamWeak hint hae hmass

/-- Literal diagonal limit with the finite-density total mass discharged from exact exterior
energy and evenness.  Only the actual pointwise PSWF density asymptotic remains as input. -/
theorem radialLeakageGramDiagonal_tendsto_of_exterior_ratio
    {ι : Type*} {l : Filter ι} [l.IsCountablyGenerated]
    {lam d delta : ι → ℝ} {q : ι → ℝ → ℂ}
    (hparam : ∀ᶠ i in l, 0 < lam i ∧ 0 < d i)
    (hqeven : ∀ i, Function.Even (q i))
    (hexterior : ∀ i,
      (∫ y in Iic (-lam i), ‖q i y‖ ^ (2 : ℕ)) + ∫ y in Ioi (lam i), ‖q i y‖ ^ (2 : ℕ) = delta i)
    (hratio : Tendsto (fun i => delta i / d i) l (nhds (8 / 11)))
    (hqint : ∀ᶠ i in l,
      IntegrableOn (fun y : ℝ => ‖q i y‖ ^ (2 : ℕ)) (Ioi (lam i)))
    (hae : ∀ᵐ x ∂(volume.restrict (Ioi (1 : ℝ))),
      Tendsto (fun i => nuLambdaDensity (lam i) (d i) (q i) x) l
        (nhds (nuInfinityDensity x)))
    {k : ℝ} (hk : 1 ≤ k) :
    Tendsto (fun i => radialLeakageGramDiagonal (lam i) k (q i) / d i)
      l (nhds (8 / (11 * Real.pi * k) * Real.arcsin (1 / k))) := by
  have hint : ∀ᶠ i in l,
      Integrable (nuLambdaDensity (lam i) (d i) (q i))
        (volume.restrict (Ioi (1 : ℝ))) := by
    filter_upwards [hparam, hqint] with i hi hqi
    exact integrableOn_Ioi_nuLambdaDensity hi.1 (q i) hqi
  have hmass := tendsto_integral_Ioi_nuLambdaDensity_of_exterior_ratio
    (hparam.mono fun _ hi => ⟨hi.1, hi.2.ne'⟩) hqeven hexterior hratio
  exact radialLeakageGramDiagonal_tendsto hparam hint hae hmass hk

end RHTower
