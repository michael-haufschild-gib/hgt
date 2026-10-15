import GaloisForLFunctions.RHTower.XiGaussianHeatEndpointRigidity
import GaloisForLFunctions.RHTower.XiGaussianHeatHankelDeterminantBlowup
import GaloisForLFunctions.HTGeometry.HankelBoundaryExtension
import GaloisForLFunctions.HTGeometry.FiniteHankelBoundaryQuadrature

/-!
# Every HCF first contact is a regular Hankel boundary

At every rank, the actual heat section either stays positive definite for all
positive heat times or has a first contact with the following structure:

* its preceding head is strictly positive;
* its nullspace is exactly one terminal-normalized line;
* the null polynomial has distinct real roots, carrying positive quadrature
  weights that reproduce every visible moment;
* the next rank has its own first contact at a strictly earlier time.

The new input is `heatMoment_head_posDef_at_endpoint`: positivity along the
actual heat flow prevents collapse of the preceding head. Compactness and the
established small heat window produce the contact itself. Thus the regular
Hankel boundary is obtained without assuming a generic time, a minimal failing
rank, a simple determinant zero, or a source sign.

The final theorem `hcf_first_contact_resolution` has no such premises. It does
not determine the first omitted moment or exclude the contact branch.
-/

open Polynomial Matrix Set Filter Topology
open HTGeometry GaloisForLFunctions.HTGeometry

noncomputable section
namespace RHTower

theorem heatMomentMatrix_posDef_mono {a : ℝ} {m n : ℕ} (hmn : m ≤ n)
    (h : (momentHankelMatrix (heatRealMoments a) n).PosDef) :
    (momentHankelMatrix (heatRealMoments a) m).PosDef := by
  exact h.submatrix (e := Fin.castLE hmn) (Fin.castLE_injective hmn)

theorem heatMomentMatrix_posDef_of_mul_le {a : ℝ} (ha : 0 < a) {n : ℕ}
    (hwin : a * n ≤ routeUCompletedPrimeGammaAperture) :
    (momentHankelMatrix (heatRealMoments a) n).PosDef := by
  rw [heatMomentMatrix_eq]
  apply posDef_leadingMatrix_of_det_pos (heatMomentArray_symm a)
  intro k hk
  exact heatMomentDet_pos_of_mul_le ha
    ((mul_le_mul_of_nonneg_left (Nat.cast_le.mpr hk) ha.le).trans hwin)

theorem heatMomentMatrix_posSemidef_at_endpoint {n : ℕ} {T : ℝ} (hT : 0 < T)
    (hpos : ∀ t ∈ Ioo 0 T, (momentHankelMatrix (heatRealMoments t) n).PosDef) :
    (momentHankelMatrix (heatRealMoments T) n).PosSemidef := by
  refine Matrix.posSemidef_iff_dotProduct_mulVec.mpr
    ⟨momentHankelMatrix_isHermitian _ _, fun x => ?_⟩
  have hc : ContinuousAt (fun t => momentInner (heatRealMoments t)
      (Polynomial.ofFn n x) (Polynomial.ofFn n x)) T :=
    (hasDerivAt_heatMomentInner _ _ hT).continuousAt
  have he : ∀ᶠ t in 𝓝[<] T, 0 ≤ momentInner (heatRealMoments t)
      (Polynomial.ofFn n x) (Polynomial.ofFn n x) := by
    filter_upwards [Ioo_mem_nhdsLT hT] with t ht
    simpa only [momentInner_ofFn_ofFn, star_trivial] using
      (hpos t ht).posSemidef.dotProduct_mulVec_nonneg x
  simpa only [momentInner_ofFn_ofFn, star_trivial] using
    ge_of_tendsto (hc.tendsto.mono_left nhdsWithin_le_nhds) he

/-- Actual first failure of a heat section: its preceding head is strictly
positive and its entire nullspace is one canonically normalized line. -/
structure HeatFirstContact (n : ℕ) where
  time : ℝ
  time_pos : 0 < time
  before : ∀ t ∈ Ioo 0 time, (momentHankelMatrix (heatRealMoments t) (n + 1)).PosDef
  nonnegative : (momentHankelMatrix (heatRealMoments time) (n + 1)).PosSemidef
  head_positive : (momentHankelMatrix (heatRealMoments time) n).PosDef
  nullVector : Fin (n + 1) → ℝ
  nullEquation : momentHankelMatrix (heatRealMoments time) (n + 1) *ᵥ nullVector = 0
  terminal : nullVector (Fin.last n) = 1
  nullspace : ∀ v, momentHankelMatrix (heatRealMoments time) (n + 1) *ᵥ v = 0 →
    v = v (Fin.last n) • nullVector

private theorem exists_heatFirstContact_of_failure (n : ℕ) {b : ℝ} (hb : 0 < b)
    (hfail : ¬ (momentHankelMatrix (heatRealMoments b) (n + 1)).PosDef) :
    ∃ c : HeatFirstContact n, c.time ≤ b := by
  classical
  let a₀ := routeUCompletedPrimeGammaAperture / (n + 2)
  have hκ := routeUCompletedPrimeGammaAperture_pos
  have ha₀ : 0 < a₀ := by dsimp [a₀]; positivity
  have hsmall : ∀ t, 0 < t → t ≤ a₀ →
      (momentHankelMatrix (heatRealMoments t) (n + 1)).PosDef := by
    intro t ht hta
    apply heatMomentMatrix_posDef_of_mul_le ht
    apply (mul_le_mul_of_nonneg_right hta (Nat.cast_nonneg (n + 1))).trans
    dsimp [a₀]
    rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
    push_cast
    nlinarith
  have hab : a₀ < b := by
    by_contra h
    exact hfail (hsmall b hb (le_of_not_gt h))
  let S : Set ℝ := ⋃ k : Fin (n + 2),
    Icc a₀ b ∩ (heatMomentDet k) ⁻¹' Iic 0
  have hclosed : IsClosed S := by
    apply isClosed_iUnion_of_finite
    intro k
    exact ((continuousOn_heatMomentDet k).mono
      (fun x hx => ha₀.trans_le hx.1)).preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hsubset : S ⊆ Icc a₀ b := by
    intro x hx
    obtain ⟨k, hk⟩ := mem_iUnion.mp hx
    exact hk.1
  have hcompact : IsCompact S := isCompact_Icc.of_isClosed_subset hclosed hsubset
  have hbad : ∃ k ≤ n + 1, heatMomentDet k b ≤ 0 := by
    by_contra h
    simp only [not_exists, not_and, not_le] at h
    apply hfail
    rw [heatMomentMatrix_eq]
    exact posDef_leadingMatrix_of_det_pos (heatMomentArray_symm b) h
  obtain ⟨k, hk, hkbad⟩ := hbad
  have hbS : b ∈ S := mem_iUnion.mpr
    ⟨⟨k, by omega⟩, ⟨⟨hab.le, le_rfl⟩, hkbad⟩⟩
  obtain ⟨T, hleast⟩ := hcompact.exists_isLeast ⟨b, hbS⟩
  have hTinterval := hsubset hleast.1
  have hT : 0 < T := ha₀.trans_le hTinterval.1
  have hbefore : ∀ t ∈ Ioo 0 T,
      (momentHankelMatrix (heatRealMoments t) (n + 1)).PosDef := by
    intro t ht
    by_cases hta : t ≤ a₀
    · exact hsmall t ht.1 hta
    rw [heatMomentMatrix_eq]
    apply posDef_leadingMatrix_of_det_pos (heatMomentArray_symm t)
    intro j hj
    by_contra hnonpos
    have htS : t ∈ S := mem_iUnion.mpr
      ⟨⟨j, by omega⟩, ⟨⟨(lt_of_not_ge hta).le, ht.2.le.trans hTinterval.2⟩,
        le_of_not_gt hnonpos⟩⟩
    exact (not_le_of_gt ht.2) (hleast.2 htS)
  have hhead := heatMoment_head_posDef_at_endpoint hT hbefore
  have hpsd := heatMomentMatrix_posSemidef_at_endpoint hT hbefore
  obtain ⟨j, hj⟩ := mem_iUnion.mp hleast.1
  have hjbad : heatMomentDet j T ≤ 0 := by
    simpa only [mem_preimage, mem_Iic] using hj.2
  have hjtop : (j : ℕ) = n + 1 := by
    by_contra hne
    have hjle : (j : ℕ) ≤ n := by omega
    have hp := (heatMomentMatrix_posDef_mono hjle hhead).det_pos
    change 0 < heatMomentDet j T at hp
    exact (not_le_of_gt hp) hjbad
  have hdet : (momentHankelMatrix (heatRealMoments T) (n + 1)).det = 0 := by
    have hn : heatMomentDet (n + 1) T ≤ 0 := by simpa only [hjtop] using hjbad
    exact le_antisymm hn hpsd.det_nonneg
  obtain ⟨u, hune, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  have hu : u (Fin.last n) ≠ 0 :=
    hankelNullVector_terminal_ne_zero_of_head_posDef _ _ u hhead hune hker
  let c : Fin (n + 1) → ℝ := (u (Fin.last n))⁻¹ • u
  have hc : momentHankelMatrix (heatRealMoments T) (n + 1) *ᵥ c = 0 := by
    change momentHankelMatrix (heatRealMoments T) (n + 1) *ᵥ
      ((u (Fin.last n))⁻¹ • u) = 0
    rw [Matrix.mulVec_smul, hker, smul_zero]
  have hc1 : c (Fin.last n) = 1 := by
    simp only [c, Pi.smul_apply, smul_eq_mul, inv_mul_cancel₀ hu]
  have hline : ∀ v, momentHankelMatrix (heatRealMoments T) (n + 1) *ᵥ v = 0 →
      v = v (Fin.last n) • c := by
    intro v hv
    have hdiff : momentHankelMatrix (heatRealMoments T) (n + 1) *ᵥ
        (v - v (Fin.last n) • c) = 0 := by
      rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hv, hc, smul_zero, sub_zero]
    have hz : v - v (Fin.last n) • c = 0 := by
      by_contra hne
      have hh := hankelNullVector_terminal_ne_zero_of_head_posDef _ _ _ hhead hne hdiff
      exact hh (by simp only [Pi.sub_apply, Pi.smul_apply, hc1, smul_eq_mul, mul_one, sub_self])
    exact sub_eq_zero.mp hz
  exact ⟨⟨T, hT, hbefore, hpsd, hhead, c, hc, hc1, hline⟩, hTinterval.2⟩

/-- **Unconditional regularity of every HCF first contact.** Either a fixed rank
is always strictly positive, or its first contact has a positive preceding head
and exactly one normalized null direction. No sign or nondegeneracy premise. -/
theorem hcf_first_contact_structure (n : ℕ) :
    (∀ t : ℝ, 0 < t → (momentHankelMatrix (heatRealMoments t) (n + 1)).PosDef) ∨
      Nonempty (HeatFirstContact n) := by
  by_cases h : ∀ t : ℝ, 0 < t → (momentHankelMatrix (heatRealMoments t) (n + 1)).PosDef
  · exact Or.inl h
  · push Not at h
    obtain ⟨t, ht, hf⟩ := h
    obtain ⟨c, -⟩ := exists_heatFirstContact_of_failure n ht hf
    exact Or.inr ⟨c⟩

namespace HeatFirstContact

theorem not_posDef {n : ℕ} (c : HeatFirstContact n) :
    ¬ (momentHankelMatrix (heatRealMoments c.time) (n + 1)).PosDef := by
  intro hp
  have hne : c.nullVector ≠ 0 := by
    intro hz
    have h := c.terminal
    rw [hz, Pi.zero_apply] at h
    exact zero_ne_one h
  have h := hp.dotProduct_mulVec_pos hne
  rw [c.nullEquation, dotProduct_zero] at h
  exact lt_irrefl 0 h

theorem time_unique {n : ℕ} (c d : HeatFirstContact n) : c.time = d.time := by
  apply le_antisymm
  · by_contra h
    exact d.not_posDef (c.before _ ⟨d.time_pos, lt_of_not_ge h⟩)
  · by_contra h
    exact c.not_posDef (d.before _ ⟨c.time_pos, lt_of_not_ge h⟩)

/-- Successive first contacts cannot collide: the next rank fails strictly earlier. -/
theorem exists_successor_earlier {n : ℕ} (c : HeatFirstContact n) :
    ∃ d : HeatFirstContact (n + 1), d.time < c.time := by
  have hf : ¬ (momentHankelMatrix (heatRealMoments c.time) ((n + 1) + 1)).PosDef := by
    intro h
    exact c.not_posDef (heatMomentMatrix_posDef_mono (by omega) h)
  obtain ⟨d, hd⟩ := exists_heatFirstContact_of_failure (n + 1) c.time_pos hf
  refine ⟨d, lt_of_le_of_ne hd ?_⟩
  intro heq
  exact c.not_posDef (by simpa only [heq] using d.head_positive)

/-- The contact is an exact positive quadrature on distinct real nodes through
degree `2n`, one degree beyond ordinary Gaussian quadrature. -/
theorem positive_quadrature {n : ℕ} (c : HeatFirstContact n) :
    (finiteHankelBoundaryNodes c.nullVector).card = n ∧
    (∀ x ∈ finiteHankelBoundaryNodes c.nullVector,
      0 < finiteHankelBoundaryWeight (heatRealMoments c.time) c.nullVector x) ∧
    (finiteHankelNullPolynomial c.nullVector).Splits ∧
    (finiteHankelNullPolynomial c.nullVector).roots.Nodup ∧
    ∀ P : ℝ[X], P.degree ≤ ((2 * n : ℕ) : WithBot ℕ) →
      momentFunctional (heatRealMoments c.time) P =
        ∑ x ∈ finiteHankelBoundaryNodes c.nullVector,
          finiteHankelBoundaryWeight (heatRealMoments c.time) c.nullVector x * P.eval x := by
  have ht : c.nullVector (Fin.last n) ≠ 0 := by rw [c.terminal]; exact one_ne_zero
  exact ⟨finiteHankelBoundaryNodes_card _ c.head_positive c.nullEquation ht,
    fun _ hx => finiteHankelBoundaryWeight_pos _ c.head_positive c.nullEquation ht hx,
    finiteHankelNullPolynomial_splits _ c.head_positive c.nullEquation ht,
    finiteHankelNullPolynomial_roots_nodup _ c.head_positive c.nullEquation ht,
    fun P hP => momentFunctional_eq_finiteHankelBoundarySum _ c.head_positive c.nullEquation ht P hP⟩

end HeatFirstContact

/-- **The actual HCF first-contact resolution.** Each finite heat section either
stays strictly positive at every positive time, or reaches a unique null line
with an exact positive quadrature; the next section reaches its own contact
strictly earlier. All objects are produced from the actual heat moments. -/
theorem hcf_first_contact_resolution (n : ℕ) :
    (∀ t : ℝ, 0 < t → (momentHankelMatrix (heatRealMoments t) (n + 1)).PosDef) ∨
    ∃ c : HeatFirstContact n,
      (finiteHankelBoundaryNodes c.nullVector).card = n ∧
      (∀ x ∈ finiteHankelBoundaryNodes c.nullVector,
        0 < finiteHankelBoundaryWeight (heatRealMoments c.time) c.nullVector x) ∧
      (finiteHankelNullPolynomial c.nullVector).Splits ∧
      (finiteHankelNullPolynomial c.nullVector).roots.Nodup ∧
      (∀ P : ℝ[X], P.degree ≤ ((2 * n : ℕ) : WithBot ℕ) →
        momentFunctional (heatRealMoments c.time) P =
          ∑ x ∈ finiteHankelBoundaryNodes c.nullVector,
            finiteHankelBoundaryWeight (heatRealMoments c.time) c.nullVector x * P.eval x) ∧
      ∃ d : HeatFirstContact (n + 1), d.time < c.time := by
  rcases hcf_first_contact_structure n with h | hc
  · exact Or.inl h
  · let c : HeatFirstContact n := Classical.choice hc
    obtain ⟨hcard, hweight, hsplits, hroots, hquad⟩ := c.positive_quadrature
    exact Or.inr ⟨c, hcard, hweight, hsplits, hroots, hquad, c.exists_successor_earlier⟩

end RHTower
