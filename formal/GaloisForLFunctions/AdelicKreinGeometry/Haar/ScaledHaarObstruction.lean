import GaloisForLFunctions.AdelicKreinGeometry.Haar.FiniteIndexObstruction
import GaloisForLFunctions.HeckeKreinToeplitz.TheIndexUnderRotationDampingAndCoalescence

/-!
# Nonzero Haar scalars force infinite index

Negative Haar scalars give arbitrarily large negative translation Grams. Positive scalars
normalize to the integer successor, so continuity of the dilation reading forces infinite index.
-/

open Filter Topology Module Complex
open scoped ComplexConjugate
open GaloisForLFunctions.ArithmeticPositiveDuality
open GaloisForLFunctions.HeckeKreinToeplitz
noncomputable section
namespace GaloisForLFunctions.AdelicKreinGeometry

/-- A negative Haar scalar already forces infinite index on rational translations. -/
theorem negIndex_eq_top_of_negative_haar {k : AffineGroupQ → ℂ} {z : ℂ}
    (hk : IsHermKernel k) (hz : z.re < 0)
    (hs : ∀ b : ℚ, k (translation b) = if b.den = 1 then z else 0) :
    negIndex k = ⊤ := by
  have hno (r : ℕ) (hi : negIndex k ≤ r) : False := by
    let b : ℚ := ((r + 1 : ℕ) : ℚ)⁻¹
    let v (i : Fin (r + 1)) :=
      ((kernelColumnRepresentation k (translation b)) ^ i.val) (kernelColumnPoint k (dilation 1))
    have hd : (b / ((1 : ℚˣ) : ℚ)).den = r + 1 := by
      simp only [Units.val_one, div_one, b, Rat.inv_natCast_den, Nat.add_one_ne_zero, ite_false]
    have he (i j : Fin (r + 1)) : kernelColumnPairing k (v i) (v j) =
        if i = j then z else 0 := by
      have h := haar_translation_orbit_pairing hk hs 1 b
        (i := i.val) (j := j.val) (by rw [hd]; exact i.isLt) (by rw [hd]; exact j.isLt)
      simpa only [Fin.ext_iff] using h
    have hb := card_le_index_of_orthogonal_negative_columns hk hi v
      (fun i => by rw [he, if_pos rfl]; exact hz)
      (fun i j hij => by rw [he, if_neg hij])
    simp only [Fintype.card_fin] at hb
    omega
  refine ENat.eq_top_iff_forall_ge.mpr fun n => ?_
  by_contra hn
  exact hno n (le_of_lt (lt_of_not_ge hn))

/-- Every nonzero scaled Haar successor is incompatible with continuous dilations at finite index. -/
theorem negIndex_eq_top_of_nonzero_haar_continuous_dilation
    {k : AffineGroupQ → ℂ} {z : ℂ} (hk : IsHermKernel k) (hz : z ≠ 0)
    (hs : ∀ b : ℚ, k (translation b) = if b.den = 1 then z else 0)
    {f : ℝ → ℂ} (hf : ContinuousAt f 1)
    (hdil : ∀ u : ℚˣ, 0 < (u : ℚ) → k (dilation u) = f (u : ℚ)) :
    negIndex k = ⊤ := by
  have hone : k 1 = z := by
    simpa only [translation_zero, Rat.den_zero, ite_true] using hs 0
  have hreal : (z.re : ℂ) = z := by
    have h := hk 1
    rw [inv_one, hone] at h
    exact Complex.conj_eq_iff_re.mp h.symm
  have hre : z.re ≠ 0 := by
    intro h
    exact hz (by rw [← hreal, h, Complex.ofReal_zero])
  rcases lt_or_gt_of_ne hre with hneg | hpos
  · exact negIndex_eq_top_of_negative_haar hk hneg hs
  · let K : AffineGroupQ → ℂ := fun g => (((z.re)⁻¹ : ℝ) : ℂ) * k g
    have hK : IsHermKernel K := by
      intro g
      change (((z.re)⁻¹ : ℝ) : ℂ) * k g⁻¹ = conj ((((z.re)⁻¹ : ℝ) : ℂ) * k g)
      rw [hk, map_mul, Complex.conj_ofReal]
    have hS : HasIntegerSuccessor K := by
      intro b
      change (((z.re)⁻¹ : ℝ) : ℂ) * k (translation b) = _
      rw [hs]
      by_cases hb : b.den = 1
      · rw [if_pos hb, if_pos hb]
        calc
          _ = (((z.re)⁻¹ : ℝ) : ℂ) * (z.re : ℂ) :=
            congrArg (fun w : ℂ => (((z.re)⁻¹ : ℝ) : ℂ) * w) hreal.symm
          _ = 1 := by
            rw [← Complex.ofReal_mul, inv_mul_cancel₀ hre, Complex.ofReal_one]
      · rw [if_neg hb, if_neg hb, mul_zero]
    have hF : ContinuousAt (fun x => (((z.re)⁻¹ : ℝ) : ℂ) * f x) 1 :=
      continuousAt_const.mul hf
    have hD (u : ℚˣ) (hu : 0 < (u : ℚ)) :
        K (dilation u) = (((z.re)⁻¹ : ℝ) : ℂ) * f (u : ℚ) := by
      change (((z.re)⁻¹ : ℝ) : ℂ) * k (dilation u) = _
      rw [hdil u hu]
    have htop := negIndex_eq_top_of_haar_continuous_dilation hK hS hF hD
    apply le_antisymm le_top
    rw [← htop]
    exact negIndex_smul_le (inv_nonneg.mpr hpos.le) k

#print axioms negIndex_eq_top_of_negative_haar
#print axioms negIndex_eq_top_of_nonzero_haar_continuous_dilation
end GaloisForLFunctions.AdelicKreinGeometry
