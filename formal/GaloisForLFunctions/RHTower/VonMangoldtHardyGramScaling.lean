import GaloisForLFunctions.RHTower.CCM.CCMComplexMellinColligation
import GaloisForLFunctions.RHTower.PrimePolarResidueCancellation
import GaloisForLFunctions.HTGeometry.KreinLangerInertia

/-!
# The scaled von Mangoldt source Gram converges to the Hardy Gram

The raw von Mangoldt observation at horizontal scale `t` has kernel

`t * (-ζ'/ζ)(1 + t s)`.

The residue `+1` of `-ζ'/ζ` at `1` forces this kernel to converge to `1 / s` as
`t →0+`.  Entrywise, every finite positive source Gram therefore converges to the universal
right-half-plane Cauchy/Hardy Gram.  This constructs the metric end of the depth-one scaling
problem from the prime source.  It does not identify the scaled Gamma-contact response with the
continued Ward column and therefore is not an RH proof.
-/

open scoped ComplexConjugate ComplexOrder
open Filter Set Complex

noncomputable section

namespace RHTower

/-- The residue of the von Mangoldt channel produces the universal Cauchy kernel under positive
horizontal dilation. -/
theorem tendsto_scaled_vonMangoldtPrimeLaplaceChannelComplex
    (s : ℂ) (hs : 0 < s.re) :
    Tendsto
      (fun t : ℝ => (t : ℂ) *
        vonMangoldtPrimeLaplaceChannelComplex ((t : ℂ) * s))
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (1 / s)) := by
  have hs0 : s ≠ 0 := by
    intro h
    rw [h] at hs
    norm_num at hs
  have hshift :
      Tendsto (fun z : ℂ => z + 1)
        (nhdsWithin 0 ({0} : Set ℂ)ᶜ) (nhdsWithin 1 ({1} : Set ℂ)ᶜ) := by
    simpa [sub_eq_add_neg] using sub_const_punctured_tendsto (0 : ℂ) (-1)
  have hres :
      Tendsto
        (fun z : ℂ => z *
          (-deriv riemannZeta (z + 1) / riemannZeta (z + 1)))
        (nhdsWithin 0 ({0} : Set ℂ)ᶜ) (nhds 1) := by
    refine (neg_logDeriv_zeta_residue.comp hshift).congr' ?_
    exact Filter.Eventually.of_forall (fun z => by
      simp only [Function.comp_apply]
      congr 1
      ring)
  have hscale :
      Tendsto (fun t : ℝ => (t : ℂ) * s)
        (nhdsWithin 0 (Set.Ioi 0)) (nhdsWithin 0 ({0} : Set ℂ)ᶜ) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hnhds : Tendsto (fun t : ℝ => (t : ℂ) * s) (nhds 0) (nhds 0) := by
        simpa using! (Complex.continuous_ofReal.mul continuous_const).tendsto 0
      exact hnhds.mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with t ht
      simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
      exact mul_ne_zero (ofReal_ne_zero.mpr (ne_of_gt ht)) hs0
  have hscaled := hres.comp hscale
  have hdiv := hscaled.div_const s
  refine hdiv.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  have htpos : 0 < t := ht
  have htre : 0 < (((t : ℂ) * s).re) := by
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    exact mul_pos htpos hs
  rw [vonMangoldtPrimeLaplaceChannelComplex_eq_logDeriv htre]
  simp only [Function.comp_apply]
  field_simp

/-- The canonical norm-two Euler contact carried by the same scaled source. -/
def scaledVonMangoldtEulerContactResponse (t : ℝ) (w : ℂ) : ℂ :=
  2 * (t : ℂ) *
    vonMangoldtPrimeLaplaceChannelComplex ((t : ℂ) * (w + 1 / 2))

/-- The canonical contact response converges to the coefficient-two Hardy kernel at `1 / 2`. -/
theorem tendsto_scaledVonMangoldtEulerContactResponse
    (w : ℂ) (hw : 0 < w.re) :
    Tendsto (fun t : ℝ => scaledVonMangoldtEulerContactResponse t w)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (2 / (w + 1 / 2))) := by
  have hs : 0 < (w + 1 / 2).re := by
    have hre : (w + 1 / 2).re = w.re + 1 / 2 := by norm_num
    rw [hre]
    linarith
  have h := (tendsto_scaled_vonMangoldtPrimeLaplaceChannelComplex
    (w + 1 / 2) hs).const_mul 2
  simpa [scaledVonMangoldtEulerContactResponse, div_eq_mul_inv, mul_assoc] using h

/-- Squared source norm of the canonical scaled Euler contact. -/
def scaledVonMangoldtEulerContactNormSq (t : ℝ) : ℂ :=
  4 * (t : ℂ) * vonMangoldtPrimeLaplaceChannelComplex (t : ℂ)

/-- The canonical scaled Euler contact has limiting squared norm four. -/
theorem tendsto_scaledVonMangoldtEulerContactNormSq :
    Tendsto scaledVonMangoldtEulerContactNormSq
      (nhdsWithin 0 (Set.Ioi 0)) (nhds 4) := by
  have h := (tendsto_scaled_vonMangoldtPrimeLaplaceChannelComplex 1 (by norm_num)).const_mul 4
  change Tendsto
    (fun t : ℝ => 4 * (t : ℂ) * vonMangoldtPrimeLaplaceChannelComplex (t : ℂ))
    (nhdsWithin 0 (Set.Ioi 0)) (nhds 4)
  simpa [mul_assoc] using h

/-- The raw von Mangoldt observation Gram after horizontal source dilation. -/
def scaledVonMangoldtPrimeRightHalfPlaneGram
    {N : ℕ} (t : ℝ) (w : Fin N → ℂ) : Matrix (Fin N) (Fin N) ℂ :=
  (t : ℂ) • vonMangoldtPrimeRightHalfPlaneGram (fun i => (t : ℂ) * w i)

/-- Every positive-scale approximant is a positive source Gram. -/
theorem scaledVonMangoldtPrimeRightHalfPlaneGram_posSemidef
    {N : ℕ} (w : Fin N → ℂ) (hw : ∀ i, 0 < (w i).re)
    {t : ℝ} (ht : 0 < t) :
    (scaledVonMangoldtPrimeRightHalfPlaneGram t w).PosSemidef := by
  apply Matrix.PosSemidef.smul
  · apply vonMangoldtPrimeRightHalfPlaneGram_posSemidef
    intro i
    simp only [mul_re, ofReal_re, ofReal_im, zero_mul, sub_zero]
    exact mul_pos ht (hw i)
  · apply Complex.nonneg_iff.mpr
    exact ⟨ht.le, by simp⟩

/-- Finite positive von Mangoldt source Grams converge entrywise to the universal Hardy Gram. -/
theorem tendsto_scaledVonMangoldtPrimeRightHalfPlaneGram
    {N : ℕ} (w : Fin N → ℂ) (hw : ∀ i, 0 < (w i).re) :
    Tendsto (fun t : ℝ => scaledVonMangoldtPrimeRightHalfPlaneGram t w)
      (nhdsWithin 0 (Set.Ioi 0)) (nhds (cauchyRightHalfPlaneGram w)) := by
  apply tendsto_pi_nhds.mpr
  intro i
  apply tendsto_pi_nhds.mpr
  intro j
  have hs : 0 < (w i + star (w j)).re := by
    change 0 < (w i).re + (w j).re
    linarith [hw i, hw j]
  simpa [scaledVonMangoldtPrimeRightHalfPlaneGram,
    vonMangoldtPrimeRightHalfPlaneGram, cauchyRightHalfPlaneGram, mul_add]
    using tendsto_scaled_vonMangoldtPrimeLaplaceChannelComplex
      (w i + star (w j)) hs

/-- The finite canonical contact column converges to the Euler-pole Hardy response. -/
theorem tendsto_scaledVonMangoldtEulerContactResponse_packet
    {N : ℕ} (w : Fin N → ℂ) (hw : ∀ i, 0 < (w i).re) :
    Tendsto (fun t i => scaledVonMangoldtEulerContactResponse t (w i))
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (fun i => 2 / (w i + 1 / 2))) := by
  apply tendsto_pi_nhds.mpr
  intro i
  exact tendsto_scaledVonMangoldtEulerContactResponse (w i) (hw i)

/-- The universal Hardy Gram has no finite dependence on a packet of distinct right-half-plane
nodes.  Thus its ordinary represented matroid is free on every such finite packet. -/
theorem cauchyRightHalfPlaneGram_rows_linearIndependent
    {N : ℕ} (w : Fin N → ℂ) (hw : ∀ i, 0 < (w i).re)
    (hwinj : Function.Injective w) :
    LinearIndependent ℂ (cauchyRightHalfPlaneGram w).row := by
  have hz : Function.Injective (fun j => -star (w j)) := by
    intro i j hij
    apply hwinj
    have := congrArg (fun z : ℂ => -star z) hij
    simpa using this
  have hwz : ∀ i j, w i ≠ -star (w j) := by
    intro i j hij
    have hre := congrArg Complex.re hij
    have hre' : (w i).re = -(w j).re := by
      calc
        (w i).re = (-star (w j)).re := hre
        _ = -(w j).re := by simp
    linarith [hw i, hw j]
  change LinearIndependent ℂ (fun i j => 1 / (w i + star (w j)))
  simpa only [sub_neg_eq_add, one_div]
    using GaloisForLFunctions.cauchy_linearIndependent
      w (fun j => -star (w j)) hwinj hz hwz

/-- The limiting Hardy Gram of a distinct right-half-plane packet is nonsingular. -/
theorem det_cauchyRightHalfPlaneGram_ne_zero
    {N : ℕ} (w : Fin N → ℂ) (hw : ∀ i, 0 < (w i).re)
    (hwinj : Function.Injective w) :
    (cauchyRightHalfPlaneGram w).det ≠ 0 := by
  have hunit : IsUnit (cauchyRightHalfPlaneGram w) :=
    Matrix.linearIndependent_rows_iff_isUnit.mp
      (cauchyRightHalfPlaneGram_rows_linearIndependent w hw hwinj)
  rw [Matrix.isUnit_iff_isUnit_det] at hunit
  exact isUnit_iff_ne_zero.mp hunit

/-- Consequently every finite distinct packet of the scaled von Mangoldt source is eventually
full rank.  Applied simultaneously to the finitely many subpackets, this says that its ordinary
represented matroid stabilizes to the free matroid and therefore cannot retain a Xi-divisor
dependence. -/
theorem eventually_det_scaledVonMangoldtPrimeRightHalfPlaneGram_ne_zero
    {N : ℕ} (w : Fin N → ℂ) (hw : ∀ i, 0 < (w i).re)
    (hwinj : Function.Injective w) :
    ∀ᶠ t in nhdsWithin 0 (Set.Ioi 0),
      (scaledVonMangoldtPrimeRightHalfPlaneGram t w).det ≠ 0 := by
  have hdet : Tendsto
      (fun t : ℝ => (scaledVonMangoldtPrimeRightHalfPlaneGram t w).det)
      (nhdsWithin 0 (Set.Ioi 0))
      (nhds (cauchyRightHalfPlaneGram w).det) :=
    continuous_id.matrix_det.continuousAt.tendsto.comp
      (tendsto_scaledVonMangoldtPrimeRightHalfPlaneGram w hw)
  exact hdet.eventually_ne (det_cauchyRightHalfPlaneGram_ne_zero w hw hwinj)

end RHTower
