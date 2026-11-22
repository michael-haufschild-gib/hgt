import GaloisForLFunctions.HTGeometry.BaseThreeSignSeparation
import Mathlib.Analysis.CStarAlgebra.Matrix

/-! # Resolving commuting spin observables from a single weighted sum -/
open Matrix
open scoped Matrix.Norms.L2Operator
namespace GaloisForLFunctions.HTGeometry.DisconnectedReturns
noncomputable section
variable {d : Type*} [Fintype d] [DecidableEq d] [Nonempty d]
private abbrev Mat (d : Type*) := Matrix d d ℂ

omit [Nonempty d] in
/-- If a unitary involution has weight larger than the norm of the
commuting remainder, commuting with their sum forces commutation with
the involution. Its commutator connects the two opposite eigenspaces. -/
theorem commute_dominant {P B X : Mat d} {w : ℝ} (hP : P∈unitary (Mat d))
    (hinv : P*P=1) (hc : Commute P B) (hw : ‖B‖<w)
    (hx : Commute X ((w:ℂ) • P+B)) : Commute X P := by
  let Y := P*X-X*P
  let A := (w:ℂ) • P+B
  have hAP : Commute A P := ((Commute.refl P).smul_left (w:ℂ)).add_left hc.symm
  have hAY : Commute A Y := (hAP.mul_right hx.symm).sub_right (hx.symm.mul_right hAP)
  have hanti : Y*P= -(P*Y) := by
    dsimp only [Y]
    rw [sub_mul,mul_sub,mul_assoc X P P,←mul_assoc P P X,hinv,mul_one,one_mul,mul_assoc]
    abel
  have heq := hAY.eq
  dsimp only [A] at heq
  rw [add_mul,mul_add,Matrix.smul_mul,Matrix.mul_smul,hanti,smul_neg] at heq
  have he : ((2*w:ℝ):ℂ) • (P*Y) = Y*B-B*Y := by
    rw [show ((2*w:ℝ):ℂ)=(w:ℂ)+w by push_cast; ring,add_smul]
    linear_combination (norm := abel) heq
  have hw0 : 0<w := (norm_nonneg B).trans_lt hw
  have hn := congrArg norm he
  rw [norm_smul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (by positivity : 0<2*w),
    CStarRing.norm_mem_unitary_mul Y hP] at hn
  have hle := (norm_sub_le (Y*B) (B*Y)).trans (add_le_add (norm_mul_le Y B) (norm_mul_le B Y))
  have hzero : ‖Y‖=0 := by
    by_contra! h
    have hp := mul_pos (sub_pos.mpr hw) (lt_of_le_of_ne (norm_nonneg Y) (Ne.symm h))
    nlinarith only [hn,hle,hp]
  exact (sub_eq_zero.mp (norm_eq_zero.mp hzero)).symm

private theorem norm_lower_weights {m : ℕ} (P : Fin m → Mat d)
    (hP : ∀ i, P i∈unitary (Mat d)) (s : Finset (Fin m)) (j : Fin m)
    (hs : ∀ i∈s, i<j) : ‖∑ i∈s, (3:ℂ)^i.val • P i‖ < (3:ℝ)^j.val := by
  have hsub : (s.image Fin.val) ⊆ Finset.range j.val := by
    rintro k hk
    obtain ⟨i,hi,rfl⟩ := Finset.mem_image.mp hk
    exact Finset.mem_range.mpr (hs i hi)
  calc
    _ ≤ ∑ i∈s, ‖(3:ℂ)^i.val • P i‖ := norm_sum_le _ _
    _ ≤ ∑ i∈s, (2:ℝ)*3^i.val := by
      apply Finset.sum_le_sum
      intro i _
      rw [norm_smul,norm_pow,CStarRing.norm_of_mem_unitary (hP i),mul_one]
      norm_num
    _ = ∑ i∈s.image Fin.val, (2:ℝ)*3^i := by
      rw [Finset.sum_image (fun _ _ _ _ h => Fin.val_injective h)]
    _ ≤ ∑ i∈Finset.range j.val, (2:ℝ)*3^i :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun _ _ _ => by positivity)
    _ < _ := by rw [sum_lt_three_pow]; linarith

/-- The commutant of any selected ternary-weighted sum of commuting
unitary involutions equals their joint commutant, including selections
with repeated or dependent observables. -/
theorem commute_weighted_spins {m : ℕ} (P : Fin m → Mat d)
    (hP : ∀ i, P i∈unitary (Mat d)) (hinv : ∀ i, P i*P i=1)
    (X : Mat d) (s : Finset (Fin m)) (hc : ∀ i∈s, ∀ j∈s, Commute (P i) (P j)) :
    Commute X (∑ i∈s, (3:ℂ)^i.val • P i) ↔ ∀ i∈s, Commute X (P i) := by
  classical
  constructor
  · revert hc
    induction s using Finset.strongInduction with
    | H s ih =>
      intro hc h i hi
      let j := s.max' ⟨i,hi⟩
      have hj : j∈s := s.max'_mem _
      let R := s.erase j
      let B := ∑ k∈R, (3:ℂ)^k.val • P k
      have hw : ‖B‖<(3:ℝ)^j.val := norm_lower_weights P hP R j (fun k hk =>
        lt_of_le_of_ne (s.le_max' k (Finset.mem_of_mem_erase hk)) (Finset.ne_of_mem_erase hk))
      have hb : Commute (P j) B := Commute.sum_right _ _ _ (fun k hk =>
        (hc j hj k (Finset.mem_of_mem_erase hk)).smul_right _)
      have hh : Commute X ((3:ℂ)^j.val • P j+B) := by
        rw [←Finset.add_sum_erase s (fun k => (3:ℂ)^k.val • P k) hj] at h
        exact h
      have hmain : Commute X (P j) := commute_dominant (hP j) (hinv j) hb hw (by
        simpa only [Complex.ofReal_pow,Complex.ofReal_ofNat] using hh)
      by_cases he : i=j
      · simpa only [he] using hmain
      · have hR : Commute X B := by
          simpa only [add_sub_cancel_left] using hh.sub_right (hmain.smul_right ((3:ℂ)^j.val))
        exact ih R (Finset.erase_ssubset hj)
          (fun a ha b hb' => hc a (Finset.mem_of_mem_erase ha) b (Finset.mem_of_mem_erase hb'))
          hR i (Finset.mem_erase.mpr ⟨he,hi⟩)
  · intro h
    exact Commute.sum_right _ _ _ (fun i hi => (h i hi).smul_right _)

#print axioms commute_weighted_spins
end
end GaloisForLFunctions.HTGeometry.DisconnectedReturns
