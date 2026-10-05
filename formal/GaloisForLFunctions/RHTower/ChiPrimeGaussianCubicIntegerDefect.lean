import GaloisForLFunctions.RHTower.ChiPrimeGaussianCubicTransverse

/-!
# Complete physical integer defect coordinates

An exact integer bijection resolves every rationally shifted Fourier lift
into two tangential numerators and the transverse defect. Three divisibility
conditions characterize its full image. Schwartz summability and the exact
physical phase survive the reindexing. Both contraction translations are
retained at a common denominator, including their mixed term.
No sum is exchanged with the physical integral and no signed saving is asserted.
-/

noncomputable section
open MeasureTheory Set Filter
open scoped BigOperators FourierTransform Topology ContDiff
namespace RHTower.BAGTrace

abbrev BAGIntegerTriple := ℤ × ℤ × ℤ

def bagGridShift (Q : ℕ+) (s : BAGIntegerTriple) : ℝ × ℝ × ℝ :=
  ((s.1 : ℝ)/(Q : ℝ),(s.2.1 : ℝ)/(Q : ℝ),(s.2.2 : ℝ)/(Q : ℝ))

def BAGDefectIndex (Q : ℕ+) (s : BAGIntegerTriple) :=
  {w : BAGIntegerTriple // (Q : ℤ) ∣ w.1+s.1 ∧ (Q : ℤ) ∣ w.2.1+s.2.1 ∧
    (Q : ℤ)^2 ∣ w.2.2-w.1*w.2.1+(Q : ℤ)*s.2.2}

private lemma q_int_ne (Q : ℕ+) : (Q : ℤ) ≠ 0 := by exact_mod_cast Q.property.ne'
private lemma q_real_ne (Q : ℕ+) : (Q : ℝ) ≠ 0 := by exact_mod_cast Q.property.ne'

/-- Complete lifted defect coordinates, with all three exact congruences. -/
def bagDefectEquiv (Q : ℕ+) (s : BAGIntegerTriple) : BAGIntegerTriple ≃ BAGDefectIndex Q s where
  toFun k := ⟨((Q : ℤ)*k.1-s.1,(Q : ℤ)*k.2.1-s.2.1,
    (Q : ℤ)^2*k.2.2-(Q : ℤ)*s.2.2+((Q : ℤ)*k.1-s.1)*((Q : ℤ)*k.2.1-s.2.1)),
      ⟨⟨k.1,by ring⟩,⟨k.2.1,by ring⟩,⟨k.2.2,by ring⟩⟩⟩
  invFun w := ((w.val.1+s.1)/(Q : ℤ),(w.val.2.1+s.2.1)/(Q : ℤ),
    (w.val.2.2-w.val.1*w.val.2.1+(Q : ℤ)*s.2.2)/(Q : ℤ)^2)
  left_inv k := by
    apply Prod.ext
    · dsimp
      rw [sub_add_cancel,Int.mul_ediv_cancel_left _ (q_int_ne Q)]
    · apply Prod.ext
      · dsimp
        rw [sub_add_cancel,Int.mul_ediv_cancel_left _ (q_int_ne Q)]
      · dsimp
        rw [show (Q : ℤ)^2*k.2.2-(Q : ℤ)*s.2.2+
            ((Q : ℤ)*k.1-s.1)*((Q : ℤ)*k.2.1-s.2.1)-
            ((Q : ℤ)*k.1-s.1)*((Q : ℤ)*k.2.1-s.2.1)+(Q : ℤ)*s.2.2=
              (Q : ℤ)^2*k.2.2 by ring,
          Int.mul_ediv_cancel_left _ (pow_ne_zero 2 (q_int_ne Q))]
  right_inv w := by
    apply Subtype.ext
    have ha := Int.mul_ediv_cancel' w.property.1
    have hb := Int.mul_ediv_cancel' w.property.2.1
    have hc := Int.mul_ediv_cancel' w.property.2.2
    apply Prod.ext
    · dsimp
      rw [ha]
      ring
    · apply Prod.ext
      · dsimp
        rw [hb]
        ring
      · dsimp
        rw [ha,hb,hc]
        ring

/-- The physical node is recovered from the tangential numerators and defect. -/
def bagDefectNode (Q : ℕ+) (w : BAGIntegerTriple) : BAGPhysicalSpace :=
  WithLp.toLp 2 ![(w.1 : ℝ)/(Q : ℝ),(w.2.1 : ℝ)/(Q : ℝ),
    ((w.2.2 : ℝ)-(w.1 : ℝ)*(w.2.1 : ℝ))/(Q : ℝ)^2]

theorem bagDefectNode_equiv (Q : ℕ+) (s k : BAGIntegerTriple) :
    bagDefectNode Q (bagDefectEquiv Q s k).val =
      bagIntegerTriple k-WithLp.toLp 2 ![(bagGridShift Q s).1,
        (bagGridShift Q s).2.1,(bagGridShift Q s).2.2] := by
  ext i
  fin_cases i <;>
    dsimp [bagDefectNode,bagDefectEquiv,bagIntegerTriple,bagGridShift] <;>
    (push_cast; field_simp [q_real_ne Q])
  all_goals ring

theorem bagDefectNode_defect (Q : ℕ+) (w : BAGIntegerTriple) :
    bagDefectNode Q w 2+bagDefectNode Q w 0*bagDefectNode Q w 1=
      (w.2.2 : ℝ)/(Q : ℝ)^2 := by
  change ((w.2.2 : ℝ)-(w.1 : ℝ)*(w.2.1 : ℝ))/(Q : ℝ)^2+
    ((w.1 : ℝ)/(Q : ℝ))*((w.2.1 : ℝ)/(Q : ℝ))=(w.2.2 : ℝ)/(Q : ℝ)^2
  field_simp
  ring

/-- All integer lifts are retained; the transverse coordinate is an integer congruence fibre. -/
def bagDefectLiftedTest (Q : ℕ+) (s : BAGIntegerTriple)
    (f : SchwartzMap BAGPhysicalSpace ℂ) : ℂ :=
  ∑' w : BAGDefectIndex Q s, (𝓕 f) (bagDefectNode Q w.val)

theorem summable_norm_bagDefectLiftedTest (Q : ℕ+) (s : BAGIntegerTriple)
    (f : SchwartzMap BAGPhysicalSpace ℂ) :
    Summable (fun w : BAGDefectIndex Q s => ‖(𝓕 f) (bagDefectNode Q w.val)‖) := by
  apply (bagDefectEquiv Q s).summable_iff.mp
  simpa only [Function.comp_def,bagDefectNode_equiv,sub_eq_add_neg] using
    summable_norm_bagFourierIntegerTriple f
      (-WithLp.toLp 2 ![(bagGridShift Q s).1,(bagGridShift Q s).2.1,(bagGridShift Q s).2.2])

theorem bagDefectLiftedTest_eq (Q : ℕ+) (s : BAGIntegerTriple)
    (f : SchwartzMap BAGPhysicalSpace ℂ) :
    bagDefectLiftedTest Q s f=bagLiftedFourierTest f (bagGridShift Q s) := by
  unfold bagDefectLiftedTest
  rw [← (bagDefectEquiv Q s).tsum_eq]
  simp only [bagDefectNode_equiv]
  rfl

/-- Exact transverse phase on every congruence-admitted integer defect. -/
theorem bagDefectNode_physical {N : ℝ} (hN : 1 < N) {η : ℝ → ℝ}
    (hη : ContDiff ℝ ∞ η) (hc : HasCompactSupport η)
    (hz : ∀ p : ℝ, p ∉ Ioo N (2*N) → η p=0)
    (Q : ℕ+) (w : BAGIntegerTriple) :
    (𝓕 (bagCubicPhysicalSchwartz hN hη hz)) (bagDefectNode Q w) =
      ∫ r : ℝ, (2*Real.pi : ℂ)*(starRingEnd ℂ) (bagCubicMellinSliceValue N η 0 r)*
        bourgainOscillation (2*Real.pi*(-r*((w.2.2 : ℝ)/(Q : ℝ)^2)))*
          bagCubicTransverseProfile N η r ((w.1 : ℝ)/(Q : ℝ)) ((w.2.1 : ℝ)/(Q : ℝ)) := by
  rw [(bagCubicPhysicalFourier_eq_transverse hN hη hc hz _).2,bagDefectNode_defect]
  rfl

/-- Common-denominator lift of both literal contraction translations. -/
def bagProjectedNumerator (Q D : ℕ+) (s : BAGIntegerTriple) (u v : ℤ) : BAGIntegerTriple :=
  ((D : ℤ)*s.1+(Q : ℤ)*u,(D : ℤ)*s.2.1+(Q : ℤ)*v,
    (D : ℤ)*s.2.2-(Q : ℤ)*u-(Q : ℤ)*v)

theorem bagProjectedNumerator_shift (Q D : ℕ+) (s : BAGIntegerTriple) (u v : ℤ) :
    bagGridShift (Q*D) (bagProjectedNumerator Q D s u v) =
      ramanujanTripleTranslate (0,1,-1) ((v : ℝ)/(D : ℝ))
        (ramanujanTripleTranslate (1,0,-1) ((u : ℝ)/(D : ℝ)) (bagGridShift Q s)) := by
  apply Prod.ext
  · dsimp [bagGridShift,bagProjectedNumerator,ramanujanTripleTranslate]
    push_cast
    field_simp [q_real_ne Q,q_real_ne D]
    ring
  · apply Prod.ext <;> dsimp [bagGridShift,bagProjectedNumerator,ramanujanTripleTranslate] <;>
      push_cast <;> field_simp [q_real_ne Q,q_real_ne D] <;> ring

/-- All four contraction terms retain their entire integer defect fibres. -/
def bagProjectedDefectTest (Q D : ℕ+) (s : BAGIntegerTriple)
    (f : SchwartzMap BAGPhysicalSpace ℂ) : ℂ :=
  bagDefectLiftedTest (Q*D) (bagProjectedNumerator Q D s 0 0) f-
  (D : ℂ)⁻¹*∑ v : Fin (D : ℕ), bagDefectLiftedTest (Q*D)
    (bagProjectedNumerator Q D s 0 v.val) f-
  (D : ℂ)⁻¹*∑ u : Fin (D : ℕ), bagDefectLiftedTest (Q*D)
    (bagProjectedNumerator Q D s u.val 0) f+
  (D : ℂ)⁻¹^2*∑ u : Fin (D : ℕ), ∑ v : Fin (D : ℕ),
    bagDefectLiftedTest (Q*D) (bagProjectedNumerator Q D s u.val v.val) f

theorem bagProjectedDefectTest_eq (Q D : ℕ+) (s : BAGIntegerTriple)
    (f : SchwartzMap BAGPhysicalSpace ℂ) :
    bagProjectedDefectTest Q D s f =
      ramanujanNoncontractingProjector (D : ℕ) (bagLiftedFourierTest f) (bagGridShift Q s) := by
  have hz (v x : ℝ × ℝ × ℝ) : ramanujanTripleTranslate v 0 x=x := by
    rcases x with ⟨x,y,z⟩
    simp [ramanujanTripleTranslate]
  simp only [bagProjectedDefectTest,bagDefectLiftedTest_eq,bagProjectedNumerator_shift,
    Int.cast_zero,zero_div,hz,Int.cast_natCast]
  dsimp [ramanujanNoncontractingProjector,ramanujanContract13,ramanujanContract23,
    ramanujanTranslationAverage]
  simp only [Finset.sum_sub_distrib,mul_sub,← Finset.mul_sum]
  ring

end RHTower.BAGTrace
