import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.HaarCellEffectivity
import GaloisForLFunctions.ArithmeticIndexDescent.ArithmeticSectionsHaveOnlyPresentationRadicals
import GaloisForLFunctions.HTGeometry.PositiveDefiniteMatrixLimit

/-!
# Positive smooth spaces from balanced complete-cell sections

Pole-preserving smoothing is linear on the actual source. Polarizing its scalar
Weil limits gives entrywise convergence of every finite Gram matrix, so one
smoothing scale preserves positivity on the entire finite coefficient space.
-/

noncomputable section
open MeasureTheory Set Filter Topology Matrix
open _root_.RHTower

namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
open ArithmeticIndexDescent SpacingScaleHarmonicAnalysis HTGeometry

private def sourceMassForm : LinearMap.BilinForm ℝ realTests where
  toFun f :=
    { toFun := fun g => ∫ x, f.1 x * g.1 x
      map_add' g h := by
        change (∫ x, f.1 x * (g.1 x + h.1 x)) = _
        simp_rw [mul_add]
        exact integral_add (integrable_mul_of_mem_realTests f.2 g.2)
          (integrable_mul_of_mem_realTests f.2 h.2)
      map_smul' r g := by
        change (∫ x, f.1 x * (r * g.1 x)) = r * ∫ x, f.1 x * g.1 x
        simp_rw [mul_left_comm (f.1 _) r]
        exact integral_const_mul _ _ }
  map_add' f g := by
    ext h
    change (∫ x, (f.1 x + g.1 x) * h.1 x) = _
    simp_rw [add_mul]
    exact integral_add (integrable_mul_of_mem_realTests f.2 h.2)
      (integrable_mul_of_mem_realTests g.2 h.2)
  map_smul' r f := by
    ext g
    change (∫ x, (r * f.1 x) * g.1 x) = r * ∫ x, f.1 x * g.1 x
    simp_rw [mul_assoc]
    exact integral_const_mul _ _

private def halfMassWeilForm : LinearMap.BilinForm ℝ realTests :=
  realWeilForm - (1 / 2 : ℝ) • sourceMassForm

private theorem halfMassWeilForm_apply (f g : realTests) :
    halfMassWeilForm f g = weilPair f.1 g.1 - (1 / 2 : ℝ) * ∫ x, f.1 x * g.1 x := rfl

private theorem halfMassWeilForm_symm (f g : realTests) :
    halfMassWeilForm f g = halfMassWeilForm g f := by
  rw [halfMassWeilForm_apply, halfMassWeilForm_apply, weilPair_comm]
  simp only [mul_comm]

private theorem eventually_positive_smooth_map {d : ℕ}
    (B : LinearMap.BilinForm ℝ realTests) (hB : ∀ f g, B f g = B g f)
    (F : ℕ → (Fin d → ℝ) →ₗ[ℝ] realTests) (Q : (Fin d → ℝ) → ℝ)
    (hlim : ∀ c, Tendsto (fun n => B (F n c) (F n c)) atTop (𝓝 (Q c)))
    (hpos : ∀ c, c ≠ 0 → 0 < Q c) :
    ∀ᶠ n in atTop, ∀ c, c ≠ 0 → 0 < B (F n c) (F n c) := by
  classical
  let e : Fin d → Fin d → ℝ := fun i => Pi.single i 1
  let M : ℕ → Matrix (Fin d) (Fin d) ℝ := fun n i j =>
    B (F n (e i)) (F n (e j))
  let A : Matrix (Fin d) (Fin d) ℝ := fun i j => (Q (e i + e j) - Q (e i) - Q (e j)) / 2
  have he (c : Fin d → ℝ) : (∑ i, c i • e i) = c := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, e, Pi.single_apply]
    simp
  have hsyn (n : ℕ) (c : Fin d → ℝ) :
      F n c = realTestSynthesis (fun i => F n (e i)) c := by
    change F n c = ∑ i, c i • F n (e i)
    conv_lhs => rw [← he c]
    simp only [map_sum, map_smul]
  have hquad (n : ℕ) (c : Fin d → ℝ) :
      B (F n c) (F n c) = c ⬝ᵥ (M n).mulVec c := by
    simp only [hsyn n c, realTestSynthesis, map_sum, map_smul, LinearMap.sum_apply,
      LinearMap.smul_apply, smul_eq_mul, dotProduct, mulVec, M]
    apply Finset.sum_congr rfl
    intro i _hi
    congr 1
    apply Finset.sum_congr rfl
    intro j _hj
    rw [hB (F n (e j)) (F n (e i))]
    exact mul_comm (c j) (B (F n (e i)) (F n (e j)))
  have hpolar (n : ℕ) (i j : Fin d) : M n i j =
      (B (F n (e i + e j)) (F n (e i + e j)) -
        B (F n (e i)) (F n (e i)) - B (F n (e j)) (F n (e j))) / 2 := by
    simp only [map_add, LinearMap.add_apply]
    rw [hB (F n (e j)) (F n (e i))]
    dsimp only [M]
    ring
  have hentry (i j : Fin d) : Tendsto (fun n => M n i j) atTop (𝓝 (A i j)) := by
    have h := (((hlim (e i + e j)).sub (hlim (e i))).sub (hlim (e j))).div_const 2
    exact h.congr' (Eventually.of_forall fun n => (hpolar n i j).symm)
  have hQ (c : Fin d → ℝ) : Q c = c ⬝ᵥ A.mulVec c := by
    have hmat : Tendsto (fun n => c ⬝ᵥ (M n).mulVec c) atTop (𝓝 (c ⬝ᵥ A.mulVec c)) := by
      unfold dotProduct mulVec
      apply tendsto_finsetSum
      intro i _hi
      apply tendsto_const_nhds.mul
      apply tendsto_finsetSum
      intro j _hj
      exact (hentry i j).mul_const (c j)
    exact tendsto_nhds_unique (hlim c)
      (hmat.congr' (Eventually.of_forall fun n => (hquad n c).symm))
  have hHerm (n : ℕ) : (M n).IsHermitian := by
    ext i j
    change B (F n (e j)) (F n (e i)) = B (F n (e i)) (F n (e j))
    exact hB _ _
  have hAHerm : A.IsHermitian := by
    ext i j
    change (Q (e j + e i) - Q (e j) - Q (e i)) / 2 =
      (Q (e i + e j) - Q (e i) - Q (e j)) / 2
    rw [add_comm (e j) (e i)]
    ring
  have hA : A.PosDef := by
    rw [Matrix.posDef_iff_dotProduct_mulVec]
    refine ⟨hAHerm, fun c hc => ?_⟩
    rw [star_trivial, ← hQ]
    exact hpos c hc
  filter_upwards [posDef_eventually_of_tendsto hA (Eventually.of_forall hHerm) hentry]
    with n hn c hc
  rw [hquad]
  simpa only [star_trivial] using (Matrix.posDef_iff_dotProduct_mulVec.mp hn).2 hc

private def haarBlockCoeffs (A d : ℕ) (c : Fin d → ℝ) (a : ℕ) : ℝ :=
  if h : A ≤ a ∧ a < A + d then c ⟨a - A, by omega⟩ else 0

private theorem haarBlockCoeffs_add (A d : ℕ) (c v : Fin d → ℝ) :
    haarBlockCoeffs A d (c + v) = haarBlockCoeffs A d c + haarBlockCoeffs A d v := by
  funext a
  by_cases h : A ≤ a ∧ a < A + d
  · simp only [haarBlockCoeffs, dif_pos h, Pi.add_apply]
  · simp only [haarBlockCoeffs, dif_neg h, Pi.add_apply, zero_add]

private theorem haarBlockCoeffs_smul (A d : ℕ) (r : ℝ) (c : Fin d → ℝ) :
    haarBlockCoeffs A d (r • c) = r • haarBlockCoeffs A d c := by
  funext a
  by_cases h : A ≤ a ∧ a < A + d
  · simp only [haarBlockCoeffs, dif_pos h, Pi.smul_apply, smul_eq_mul]
  · simp only [haarBlockCoeffs, dif_neg h, Pi.smul_apply, smul_eq_mul, mul_zero]

private theorem haarBlockCoeffs_tail (A d : ℕ) (c : Fin d → ℝ) :
    haarTailCoeffs A (haarBlockCoeffs A d c) = haarBlockCoeffs A d c := by
  funext a
  by_cases h : A ≤ a
  · simp only [haarTailCoeffs, if_pos h]
  · have hn : ¬ (A ≤ a ∧ a < A + d) := fun hh => h hh.1
    simp only [haarTailCoeffs, if_neg h, haarBlockCoeffs, dif_neg hn]

private theorem haarSectionProfile_add (c v : ℕ → ℝ) (X : ℕ) :
    haarSectionProfile (c + v) X = haarSectionProfile c X + haarSectionProfile v X := by
  funext x
  simp only [haarSectionProfile, Pi.add_apply, add_mul, Finset.sum_add_distrib]

private theorem haarSectionProfile_smul (r : ℝ) (c : ℕ → ℝ) (X : ℕ) :
    haarSectionProfile (r • c) X = r • haarSectionProfile c X := by
  funext x
  simp only [haarSectionProfile, Pi.smul_apply, smul_eq_mul, mul_assoc, Finset.mul_sum]

private theorem poleSmooth_add_bv {f g : ℝ → ℝ}
    (hf : BoundedVariationOn f univ) (hg : BoundedVariationOn g univ) (n : ℕ) :
    poleSmooth (f + g) n = poleSmooth f n + poleSmooth g n := by
  apply poleSmooth_add (measurable_of_boundedVariation_univ hf) (measurable_of_boundedVariation_univ hg)
    (show 0 ≤ ‖f 0‖ + (eVariationOn f univ).toReal by positivity)
    (show 0 ≤ ‖g 0‖ + (eVariationOn g univ).toReal by positivity)
  · intro x
    simpa only [Real.norm_eq_abs] using norm_le_of_boundedVariation_univ hf x
  · intro x
    simpa only [Real.norm_eq_abs] using norm_le_of_boundedVariation_univ hg x

/-- The common regularization of a block of consecutive balanced complete pairs. -/
def smoothHaarBlockMap (A d n : ℕ) : (Fin d → ℝ) →ₗ[ℝ] realTests where
  toFun c := ⟨poleSmooth (haarSectionProfile (haarBlockCoeffs A d c) (A + d)) n,
    poleSmooth_contDiff (memLp_haarSectionProfile _ _) n,
    poleSmooth_compact (haarSectionProfile_compact _ _) n⟩
  map_add' c v := Subtype.ext <| by
    change poleSmooth (haarSectionProfile (haarBlockCoeffs A d (c + v)) (A + d)) n =
      poleSmooth (haarSectionProfile (haarBlockCoeffs A d c) (A + d)) n +
        poleSmooth (haarSectionProfile (haarBlockCoeffs A d v) (A + d)) n
    rw [haarBlockCoeffs_add, haarSectionProfile_add]
    exact poleSmooth_add_bv (haarSectionProfile_bv _ _) (haarSectionProfile_bv _ _) n
  map_smul' r c := Subtype.ext <| by
    change poleSmooth (haarSectionProfile (haarBlockCoeffs A d (r • c)) (A + d)) n =
      r • poleSmooth (haarSectionProfile (haarBlockCoeffs A d c) (A + d)) n
    rw [haarBlockCoeffs_smul, haarSectionProfile_smul]
    exact poleSmooth_const_mul r _ n

private theorem block_mass_pos {A d : ℕ} (hA : 1 ≤ A) {c : Fin d → ℝ} (hc : c ≠ 0) :
    0 < ∑ a ∈ Finset.Icc 1 (A + d), haarMass a * haarBlockCoeffs A d c a ^ 2 := by
  obtain ⟨i, hi⟩ : ∃ i, c i ≠ 0 := by
    by_contra h
    push Not at h
    exact hc (funext h)
  have ha : A + i.val ∈ Finset.Icc 1 (A + d) := Finset.mem_Icc.mpr ⟨by omega, by omega⟩
  have hcoef : haarBlockCoeffs A d c (A + i.val) = c i := by
    have hbound : A ≤ A + i.val ∧ A + i.val < A + d := ⟨by omega, by omega⟩
    simp only [haarBlockCoeffs, dif_pos hbound, Nat.add_sub_cancel_left]
  have hp : 0 < haarMass (A + i.val) * haarBlockCoeffs A d c (A + i.val) ^ 2 := by
    rw [hcoef]
    exact mul_pos (haarMass_pos (by omega)) (sq_pos_of_ne_zero hi)
  exact hp.trans_le (Finset.single_le_sum
    (fun a ha => mul_nonneg (haarMass_pos (Finset.mem_Icc.mp ha).1).le (sq_nonneg _)) ha)

private theorem linearIndependent_of_map_positive {d : ℕ}
    (F : (Fin d → ℝ) →ₗ[ℝ] realTests)
    (hpos : ∀ c, c ≠ 0 → 0 < realWeilForm (F c) (F c)) :
    LinearIndependent ℝ (fun i : Fin d => F (Pi.single i 1)) := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro c hc i
  by_contra hi
  have hn : c ≠ 0 := fun h => hi (congrFun h i)
  have he : (∑ j, c j • Pi.single j (1 : ℝ)) = c := by
    ext j
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
    simp
  have hF : F c = 0 := by
    calc
      F c = F (∑ j, c j • Pi.single j (1 : ℝ)) := congrArg F he.symm
      _ = ∑ j, c j • F (Pi.single j 1) := by simp only [map_sum, map_smul]
      _ = 0 := hc
  have h := hpos c hn
  rw [hF, map_zero] at h
  exact (lt_irrefl 0) h

/-- A fixed arithmetic tail contains positive smooth spaces of every finite dimension. -/
theorem exists_smooth_haar_positive_spaces : ∃ A : ℕ, 1 ≤ A ∧ ∀ d : ℕ, ∃ n : ℕ,
    LinearIndependent ℝ (fun i : Fin d => smoothHaarBlockMap A d n (Pi.single i 1)) ∧
    (∀ c : Fin d → ℝ, c ≠ 0 →
      0 < weilPair (smoothHaarBlockMap A d n c).1 (smoothHaarBlockMap A d n c).1) ∧
    ∀ c : Fin d → ℝ,
      (1 / 2 : ℝ) * (∫ x, (smoothHaarBlockMap A d n c).1 x ^ 2) ≤
        weilPair (smoothHaarBlockMap A d n c).1 (smoothHaarBlockMap A d n c).1 := by
  obtain ⟨A, hA, hfloor⟩ := exists_haarTail_roughWeil_floor
  refine ⟨A, hA, fun d => ?_⟩
  let Q : (Fin d → ℝ) → ℝ := fun c =>
    roughWeil (haarSectionProfile (haarBlockCoeffs A d c) (A + d)) -
      (1 / 2 : ℝ) * ∫ x, haarSectionProfile (haarBlockCoeffs A d c) (A + d) x ^ 2
  have hlim (c : Fin d → ℝ) :
      Tendsto (fun n => halfMassWeilForm (smoothHaarBlockMap A d n c) (smoothHaarBlockMap A d n c))
        atTop (𝓝 (Q c)) := by
    simp only [halfMassWeilForm_apply, ← pow_two]
    change Tendsto (fun n => weilQuad
      (poleSmooth (haarSectionProfile (haarBlockCoeffs A d c) (A + d)) n) -
      (1 / 2 : ℝ) * ∫ x, poleSmooth (haarSectionProfile (haarBlockCoeffs A d c) (A + d)) n x ^ 2)
      atTop (𝓝 (Q c))
    exact (tendsto_poleSmooth_weilQuad (haarSectionProfile_bv _ _) (haarSectionProfile_compact _ _)
      (haarSectionProfile_supported _ _)).sub
        ((tendsto_poleSmooth_square_mass (memLp_haarSectionProfile _ _)).const_mul (1 / 2))
  have hpos (c : Fin d → ℝ) (hc : c ≠ 0) : 0 < Q c := by
    have h := hfloor (haarBlockCoeffs A d c) (A + d)
    rw [haarBlockCoeffs_tail] at h
    have hm := block_mass_pos hA hc
    dsimp only [Q]
    rw [integral_haarSectionProfile_sq]
    linarith only [h, hm]
  obtain ⟨n, hn⟩ := (eventually_positive_smooth_map halfMassWeilForm halfMassWeilForm_symm
    (smoothHaarBlockMap A d) Q hlim hpos).exists
  have hw (c : Fin d → ℝ) (hc : c ≠ 0) :
      0 < realWeilForm (smoothHaarBlockMap A d n c) (smoothHaarBlockMap A d n c) := by
    have h := hn c hc
    rw [halfMassWeilForm_apply] at h
    have hm : 0 ≤ ∫ x, (smoothHaarBlockMap A d n c).1 x * (smoothHaarBlockMap A d n c).1 x :=
      integral_nonneg fun x => mul_self_nonneg _
    change 0 < weilPair _ _
    linarith only [h, hm]
  refine ⟨n, linearIndependent_of_map_positive _ hw, hw, fun c => ?_⟩
  by_cases hc : c = 0
  · subst c
    simp only [map_zero, Submodule.coe_zero, Pi.zero_apply, zero_pow (by norm_num : 2 ≠ 0),
      integral_zero, mul_zero]
    change 0 ≤ realWeilForm 0 0
    simp only [map_zero, le_refl]
  · have h := hn c hc
    rw [halfMassWeilForm_apply] at h
    simp only [← pow_two] at h
    exact (sub_pos.mp h).le

/-- The source-defined span of one common smoothing of consecutive balanced pairs. -/
def smoothHaarBlockTests (A d n : ℕ) : Submodule ℝ realTests :=
  LinearMap.range (smoothHaarBlockMap A d n)

private theorem smoothHaarBlockTests_eq_span (A d n : ℕ) :
    smoothHaarBlockTests A d n = Submodule.span ℝ
      (Set.range (fun i : Fin d => smoothHaarBlockMap A d n (Pi.single i 1))) := by
  classical
  apply le_antisymm
  · rintro f ⟨c, rfl⟩
    have he : (∑ i, c i • Pi.single i (1 : ℝ)) = c := by
      ext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.single_apply]
      simp
    rw [← he, map_sum]
    apply Submodule.sum_mem
    intro i _hi
    rw [map_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · apply Submodule.span_le.mpr
    rintro f ⟨i, rfl⟩
    exact ⟨Pi.single i 1, rfl⟩

/-- Whole-cell source spaces of every finite dimension carry Riemann–Roch and ampleness. -/
theorem exists_smooth_haar_effectivity : ∃ A : ℕ, 1 ≤ A ∧ ∀ d : ℕ, ∃ n : ℕ,
    LinearIndependent ℝ (fun i : Fin d => smoothHaarBlockMap A d n (Pi.single i 1)) ∧
    Module.finrank ℝ (smoothHaarBlockTests A d n) = d ∧
    (scalingSubsurface (smoothHaarBlockTests A d n)).RiemannRochAxiom
      (l2SourceCone (1 / 2) (smoothHaarBlockTests A d n)) ∧
    (scalingSubsurface (smoothHaarBlockTests A d n)).AmpleAxiom
      (l2SourceCone (1 / 2) (smoothHaarBlockTests A d n)) ∧
    (scalingSubsurface (smoothHaarBlockTests A d n)).HodgeIndex := by
  obtain ⟨A, hA, hspace⟩ := exists_smooth_haar_positive_spaces
  refine ⟨A, hA, fun d => ?_⟩
  obtain ⟨n, hind, _hpos, hfloor⟩ := hspace d
  have hf (f : smoothHaarBlockTests A d n) :
      (1 / 2 : ℝ) * (∫ x, f.1.1 x ^ 2) ≤ weilPair f.1.1 f.1.1 := by
    obtain ⟨c, hc⟩ := f.2
    have h := hfloor c
    rw [hc] at h
    exact h
  have hdim : Module.finrank ℝ (smoothHaarBlockTests A d n) = d := by
    rw [smoothHaarBlockTests_eq_span]
    simpa only [Fintype.card_fin] using finrank_span_eq_card hind
  refine ⟨n, hind, hdim, (l2SourceCone_riemannRoch_iff_weilPair_ge (by norm_num) _).mpr hf,
    l2SourceCone_ample (by norm_num) _,
    (scalingSubsurface_hodgeIndex_iff_weilPair_nonneg _).mpr ?_⟩
  intro f
  exact (mul_nonneg (by norm_num) (integral_nonneg fun x => sq_nonneg (f.1.1 x))).trans (hf f)

#print axioms smoothHaarBlockMap
#print axioms exists_smooth_haar_positive_spaces
#print axioms exists_smooth_haar_effectivity

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri.LogCells
