/-
The three-factor shell-overlap law for even Sonin dilation corners.

Each mixed shell translation is, modulo compact operators, the Gram entry of two dilation
corners across the even Sonin projection.  This file computes the chain product of two mixed
shell translations sharing a middle scale.  Within one polarization the product is exact: the
composite is again a shell translation between the outer scales, with inner shell floor raised
by the middle scale.  Consequently the middle factor cancels exactly when the middle scale
dominates one of the outer scales, and pinches the transported shell otherwise.  The initial
and final Calkin projections of a chain are two-polarization shells whose multiplicative
thickness is the minimum of all three scales, and a strictly pinched chain is never compactly
equal to the direct Gram entry: middle-scale absorption holds precisely on `min p r ≤ q`.
-/
import GaloisForLFunctions.RHTower.SoninEulerCalkinPartialIsometry

noncomputable section

namespace RHTower

open MeasureTheory Set Filter Topology
open FourierTransform
open scoped ENNReal InnerProduct InnerProductSpace

/-! ### Indicator shell algebra -/

/-- Two co-anchored physical shells multiply to the shell with the larger floor. -/
theorem evenIndicatorCutoff_shellProduct
    (t u v : ℝ) (hut : u ≤ t) (hvt : v ≤ t) :
    (evenIndicatorCutoff t - evenIndicatorCutoff u) *
        (evenIndicatorCutoff t - evenIndicatorCutoff v) =
      evenIndicatorCutoff t - evenIndicatorCutoff (max u v) := by
  have htt : evenIndicatorCutoff t * evenIndicatorCutoff t = evenIndicatorCutoff t :=
    evenIndicatorCutoff_mul_of_le t t le_rfl
  have htv : evenIndicatorCutoff t * evenIndicatorCutoff v = evenIndicatorCutoff v :=
    evenIndicatorCutoff_mul_of_le_rev v t hvt
  have hut' : evenIndicatorCutoff u * evenIndicatorCutoff t = evenIndicatorCutoff u :=
    evenIndicatorCutoff_mul_of_le u t hut
  rcases le_total u v with h | h
  · have huv : evenIndicatorCutoff u * evenIndicatorCutoff v = evenIndicatorCutoff u :=
      evenIndicatorCutoff_mul_of_le u v h
    rw [max_eq_right h, sub_mul, mul_sub, mul_sub, htt, htv, hut', huv]
    abel
  · have huv : evenIndicatorCutoff u * evenIndicatorCutoff v = evenIndicatorCutoff v :=
      evenIndicatorCutoff_mul_of_le_rev v u h
    rw [max_eq_left h, sub_mul, mul_sub, mul_sub, htt, htv, hut', huv]
    abel

/-- Two co-anchored Fourier shells multiply to the shell with the larger floor. -/
theorem evenFourierCutoff_shellProduct
    (t u v : ℝ) (hut : u ≤ t) (hvt : v ≤ t) :
    (evenFourierCutoff t - evenFourierCutoff u) *
        (evenFourierCutoff t - evenFourierCutoff v) =
      evenFourierCutoff t - evenFourierCutoff (max u v) := by
  have htt : evenFourierCutoff t * evenFourierCutoff t = evenFourierCutoff t :=
    evenFourierCutoff_mul_of_le t t le_rfl
  have htv : evenFourierCutoff t * evenFourierCutoff v = evenFourierCutoff v :=
    evenFourierCutoff_mul_of_le_rev v t hvt
  have hut' : evenFourierCutoff u * evenFourierCutoff t = evenFourierCutoff u :=
    evenFourierCutoff_mul_of_le u t hut
  rcases le_total u v with h | h
  · have huv : evenFourierCutoff u * evenFourierCutoff v = evenFourierCutoff u :=
      evenFourierCutoff_mul_of_le u v h
    rw [max_eq_right h, sub_mul, mul_sub, mul_sub, htt, htv, hut', huv]
    abel
  · have huv : evenFourierCutoff u * evenFourierCutoff v = evenFourierCutoff v :=
      evenFourierCutoff_mul_of_le_rev v u h
    rw [max_eq_left h, sub_mul, mul_sub, mul_sub, htt, htv, hut', huv]
    abel

/-- A physical shell followed by a central complement raises the floor to the maximum. -/
theorem evenIndicatorCutoff_shellComplementProduct
    (t u v : ℝ) (hvt : v ≤ t) :
    (evenIndicatorCutoff t - evenIndicatorCutoff u) * (1 - evenIndicatorCutoff v) =
      evenIndicatorCutoff t - evenIndicatorCutoff (max u v) := by
  have htv : evenIndicatorCutoff t * evenIndicatorCutoff v = evenIndicatorCutoff v :=
    evenIndicatorCutoff_mul_of_le_rev v t hvt
  rcases le_total u v with h | h
  · have huv : evenIndicatorCutoff u * evenIndicatorCutoff v = evenIndicatorCutoff u :=
      evenIndicatorCutoff_mul_of_le u v h
    rw [max_eq_right h, mul_sub, mul_one, sub_mul, htv, huv]
    abel
  · have huv : evenIndicatorCutoff u * evenIndicatorCutoff v = evenIndicatorCutoff v :=
      evenIndicatorCutoff_mul_of_le_rev v u h
    rw [max_eq_left h, mul_sub, mul_one, sub_mul, htv, huv]
    abel

/-- A Fourier shell followed by a central complement raises the floor to the maximum. -/
theorem evenFourierCutoff_shellComplementProduct
    (t u v : ℝ) (hvt : v ≤ t) :
    (evenFourierCutoff t - evenFourierCutoff u) * (1 - evenFourierCutoff v) =
      evenFourierCutoff t - evenFourierCutoff (max u v) := by
  have htv : evenFourierCutoff t * evenFourierCutoff v = evenFourierCutoff v :=
    evenFourierCutoff_mul_of_le_rev v t hvt
  rcases le_total u v with h | h
  · have huv : evenFourierCutoff u * evenFourierCutoff v = evenFourierCutoff u :=
      evenFourierCutoff_mul_of_le u v h
    rw [max_eq_right h, mul_sub, mul_one, sub_mul, htv, huv]
    abel
  · have huv : evenFourierCutoff u * evenFourierCutoff v = evenFourierCutoff v :=
      evenFourierCutoff_mul_of_le_rev v u h
    rw [max_eq_left h, mul_sub, mul_one, sub_mul, htv, huv]
    abel

/-- A central complement acting before a shell whose floor clears the cutoff is absorbed. -/
theorem evenIndicatorCutoff_complement_shellProduct
    (t u v : ℝ) (hvu : v ≤ u) (hvt : v ≤ t) :
    (1 - evenIndicatorCutoff v) * (evenIndicatorCutoff t - evenIndicatorCutoff u) =
      evenIndicatorCutoff t - evenIndicatorCutoff u := by
  have h₁ : evenIndicatorCutoff v * evenIndicatorCutoff t = evenIndicatorCutoff v :=
    evenIndicatorCutoff_mul_of_le v t hvt
  have h₂ : evenIndicatorCutoff v * evenIndicatorCutoff u = evenIndicatorCutoff v :=
    evenIndicatorCutoff_mul_of_le v u hvu
  rw [sub_mul, one_mul, mul_sub, h₁, h₂]
  abel

/-- A Fourier complement acting before a shell whose floor clears the cutoff is absorbed. -/
theorem evenFourierCutoff_complement_shellProduct
    (t u v : ℝ) (hvu : v ≤ u) (hvt : v ≤ t) :
    (1 - evenFourierCutoff v) * (evenFourierCutoff t - evenFourierCutoff u) =
      evenFourierCutoff t - evenFourierCutoff u := by
  have h₁ : evenFourierCutoff v * evenFourierCutoff t = evenFourierCutoff v :=
    evenFourierCutoff_mul_of_le v t hvt
  have h₂ : evenFourierCutoff v * evenFourierCutoff u = evenFourierCutoff v :=
    evenFourierCutoff_mul_of_le v u hvu
  rw [sub_mul, one_mul, mul_sub, h₁, h₂]
  abel

/-! ### The exact windowed chain law, one polarization at a time -/

/-- Physical windowed chain law.  Two windowed shell translations sharing the middle scale `q`
compose exactly to the windowed shell translation between the outer scales, the inner floor
being the maximum of the first floor and the dilated second floor. -/
theorem physicalWindowedShellTranslation_chain_mul
    (a b c p q r : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hbp : b ≤ p * a) (hac : a ≤ c) (hcq : c ≤ q * a) :
    (evenIndicatorCutoff (p * a) - evenIndicatorCutoff b) *
        evenDilationCLM (p⁻¹ * q)
          (mul_pos (inv_pos.mpr (zero_lt_one.trans hp)) (zero_lt_one.trans hq)) *
        (1 - evenIndicatorCutoff a) *
      ((evenIndicatorCutoff (q * a) - evenIndicatorCutoff c) *
        evenDilationCLM (q⁻¹ * r)
          (mul_pos (inv_pos.mpr (zero_lt_one.trans hq)) (zero_lt_one.trans hr)) *
        (1 - evenIndicatorCutoff a)) =
      (evenIndicatorCutoff (p * a) - evenIndicatorCutoff (max b ((p * q⁻¹) * c))) *
        evenDilationCLM (p⁻¹ * r)
          (mul_pos (inv_pos.mpr (zero_lt_one.trans hp)) (zero_lt_one.trans hr)) *
        (1 - evenIndicatorCutoff a) := by
  have hp0 := zero_lt_one.trans hp
  have hq0 := zero_lt_one.trans hq
  have hr0 := zero_lt_one.trans hr
  let A := evenIndicatorCutoff a
  let Ap := evenIndicatorCutoff (p * a)
  let Aq := evenIndicatorCutoff (q * a)
  let Ab := evenIndicatorCutoff b
  let Ac := evenIndicatorCutoff c
  let Ax := evenIndicatorCutoff ((p * q⁻¹) * c)
  let U₁ := evenDilationCLM (p⁻¹ * q) (mul_pos (inv_pos.mpr hp0) hq0)
  let U₂ := evenDilationCLM (q⁻¹ * r) (mul_pos (inv_pos.mpr hq0) hr0)
  let U₃ := evenDilationCLM (p⁻¹ * r) (mul_pos (inv_pos.mpr hp0) hr0)
  have haq : a ≤ q * a := by nlinarith
  have hE : (1 - A) * (Aq - Ac) = Aq - Ac :=
    evenIndicatorCutoff_complement_shellProduct (q * a) c a hac haq
  have hmove : U₁ * (Aq - Ac) = (Ap - Ax) * U₁ := by
    have hq' := evenDilationCLM_mul_evenIndicatorCutoff (q * a) (p⁻¹ * q)
      (mul_pos (inv_pos.mpr hp0) hq0)
    have hc' := evenDilationCLM_mul_evenIndicatorCutoff c (p⁻¹ * q)
      (mul_pos (inv_pos.mpr hp0) hq0)
    have hsq : (p⁻¹ * q)⁻¹ * (q * a) = p * a := by field_simp
    have hsc : (p⁻¹ * q)⁻¹ * c = (p * q⁻¹) * c := by field_simp
    rw [hsq] at hq'
    rw [hsc] at hc'
    change U₁ * Aq = Ap * U₁ at hq'
    change U₁ * Ac = Ax * U₁ at hc'
    rw [mul_sub, hq', hc', sub_mul]
  have hcomp : U₁ * U₂ = U₃ := by
    have h := evenDilationCLM_mul (p⁻¹ * q) (q⁻¹ * r)
      (mul_pos (inv_pos.mpr hp0) hq0) (mul_pos (inv_pos.mpr hq0) hr0)
    have hscale : (p⁻¹ * q) * (q⁻¹ * r) = p⁻¹ * r := by field_simp
    have hU : U₃ = evenDilationCLM ((p⁻¹ * q) * (q⁻¹ * r))
        (mul_pos (mul_pos (inv_pos.mpr hp0) hq0) (mul_pos (inv_pos.mpr hq0) hr0)) := by
      dsimp only [U₃]
      congr 1
      exact hscale.symm
    rw [hU]
    exact h
  have hxpa : (p * q⁻¹) * c ≤ p * a := by
    have h1 : (p * q⁻¹) * c ≤ (p * q⁻¹) * (q * a) :=
      mul_le_mul_of_nonneg_left hcq (by positivity)
    have h2 : (p * q⁻¹) * (q * a) = p * a := by field_simp
    linarith
  have hshell : (Ap - Ab) * (Ap - Ax) =
      Ap - evenIndicatorCutoff (max b ((p * q⁻¹) * c)) :=
    evenIndicatorCutoff_shellProduct (p * a) b ((p * q⁻¹) * c) hbp hxpa
  change (Ap - Ab) * U₁ * (1 - A) * ((Aq - Ac) * U₂ * (1 - A)) =
    (Ap - evenIndicatorCutoff (max b ((p * q⁻¹) * c))) * U₃ * (1 - A)
  calc
    (Ap - Ab) * U₁ * (1 - A) * ((Aq - Ac) * U₂ * (1 - A)) =
        (Ap - Ab) * U₁ * ((1 - A) * (Aq - Ac)) * (U₂ * (1 - A)) := by
      noncomm_ring
    _ = (Ap - Ab) * (U₁ * (Aq - Ac)) * (U₂ * (1 - A)) := by
      rw [hE]; noncomm_ring
    _ = (Ap - Ab) * ((Ap - Ax) * U₁) * (U₂ * (1 - A)) := by rw [hmove]
    _ = ((Ap - Ab) * (Ap - Ax)) * (U₁ * U₂) * (1 - A) := by noncomm_ring
    _ = (Ap - evenIndicatorCutoff (max b ((p * q⁻¹) * c))) * U₃ * (1 - A) := by
      rw [hshell, hcomp]

/-- Fourier windowed chain law, mirror of the physical case under the opposite dilation
covariance. -/
theorem fourierWindowedShellTranslation_chain_mul
    (a b c p q r : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hbp : b ≤ p * a) (hac : a ≤ c) (hcq : c ≤ q * a) :
    (evenFourierCutoff (p * a) - evenFourierCutoff b) *
        evenDilationCLM (p * q⁻¹)
          (mul_pos (zero_lt_one.trans hp) (inv_pos.mpr (zero_lt_one.trans hq))) *
        (1 - evenFourierCutoff a) *
      ((evenFourierCutoff (q * a) - evenFourierCutoff c) *
        evenDilationCLM (q * r⁻¹)
          (mul_pos (zero_lt_one.trans hq) (inv_pos.mpr (zero_lt_one.trans hr))) *
        (1 - evenFourierCutoff a)) =
      (evenFourierCutoff (p * a) - evenFourierCutoff (max b ((p * q⁻¹) * c))) *
        evenDilationCLM (p * r⁻¹)
          (mul_pos (zero_lt_one.trans hp) (inv_pos.mpr (zero_lt_one.trans hr))) *
        (1 - evenFourierCutoff a) := by
  have hp0 := zero_lt_one.trans hp
  have hq0 := zero_lt_one.trans hq
  have hr0 := zero_lt_one.trans hr
  let R := evenFourierCutoff a
  let Rp := evenFourierCutoff (p * a)
  let Rq := evenFourierCutoff (q * a)
  let Rb := evenFourierCutoff b
  let Rc := evenFourierCutoff c
  let Rx := evenFourierCutoff ((p * q⁻¹) * c)
  let U₁ := evenDilationCLM (p * q⁻¹) (mul_pos hp0 (inv_pos.mpr hq0))
  let U₂ := evenDilationCLM (q * r⁻¹) (mul_pos hq0 (inv_pos.mpr hr0))
  let U₃ := evenDilationCLM (p * r⁻¹) (mul_pos hp0 (inv_pos.mpr hr0))
  have haq : a ≤ q * a := by nlinarith
  have hE : (1 - R) * (Rq - Rc) = Rq - Rc :=
    evenFourierCutoff_complement_shellProduct (q * a) c a hac haq
  have hmove : U₁ * (Rq - Rc) = (Rp - Rx) * U₁ := by
    have hq' := evenDilationCLM_mul_evenFourierCutoff (q * a) (p * q⁻¹)
      (mul_pos hp0 (inv_pos.mpr hq0))
    have hc' := evenDilationCLM_mul_evenFourierCutoff c (p * q⁻¹)
      (mul_pos hp0 (inv_pos.mpr hq0))
    have hsq : (p * q⁻¹) * (q * a) = p * a := by field_simp
    rw [hsq] at hq'
    change U₁ * Rq = Rp * U₁ at hq'
    change U₁ * Rc = Rx * U₁ at hc'
    rw [mul_sub, hq', hc', sub_mul]
  have hcomp : U₁ * U₂ = U₃ := by
    have h := evenDilationCLM_mul (p * q⁻¹) (q * r⁻¹)
      (mul_pos hp0 (inv_pos.mpr hq0)) (mul_pos hq0 (inv_pos.mpr hr0))
    have hscale : (p * q⁻¹) * (q * r⁻¹) = p * r⁻¹ := by field_simp
    have hU : U₃ = evenDilationCLM ((p * q⁻¹) * (q * r⁻¹))
        (mul_pos (mul_pos hp0 (inv_pos.mpr hq0)) (mul_pos hq0 (inv_pos.mpr hr0))) := by
      dsimp only [U₃]
      congr 1
      exact hscale.symm
    rw [hU]
    exact h
  have hxpa : (p * q⁻¹) * c ≤ p * a := by
    have h1 : (p * q⁻¹) * c ≤ (p * q⁻¹) * (q * a) :=
      mul_le_mul_of_nonneg_left hcq (by positivity)
    have h2 : (p * q⁻¹) * (q * a) = p * a := by field_simp
    linarith
  have hshell : (Rp - Rb) * (Rp - Rx) =
      Rp - evenFourierCutoff (max b ((p * q⁻¹) * c)) :=
    evenFourierCutoff_shellProduct (p * a) b ((p * q⁻¹) * c) hbp hxpa
  change (Rp - Rb) * U₁ * (1 - R) * ((Rq - Rc) * U₂ * (1 - R)) =
    (Rp - evenFourierCutoff (max b ((p * q⁻¹) * c))) * U₃ * (1 - R)
  calc
    (Rp - Rb) * U₁ * (1 - R) * ((Rq - Rc) * U₂ * (1 - R)) =
        (Rp - Rb) * U₁ * ((1 - R) * (Rq - Rc)) * (U₂ * (1 - R)) := by
      noncomm_ring
    _ = (Rp - Rb) * (U₁ * (Rq - Rc)) * (U₂ * (1 - R)) := by
      rw [hE]; noncomm_ring
    _ = (Rp - Rb) * ((Rp - Rx) * U₁) * (U₂ * (1 - R)) := by rw [hmove]
    _ = ((Rp - Rb) * (Rp - Rx)) * (U₁ * U₂) * (1 - R) := by noncomm_ring
    _ = (Rp - evenFourierCutoff (max b ((p * q⁻¹) * c))) * U₃ * (1 - R) := by
      rw [hshell, hcomp]

/-! ### Unit-scale collapse and floor normal form -/

/-- A windowed physical shell translation at the trivial composite scale collapses to its
shell. -/
theorem physicalWindowedShellTranslation_scaleOne
    (a b p : ℝ) (hp : 1 < p) (hab : a ≤ b) (hbp : b ≤ p * a) :
    (evenIndicatorCutoff (p * a) - evenIndicatorCutoff b) *
        evenDilationCLM (p⁻¹ * p)
          (mul_pos (inv_pos.mpr (zero_lt_one.trans hp)) (zero_lt_one.trans hp)) *
        (1 - evenIndicatorCutoff a) =
      evenIndicatorCutoff (p * a) - evenIndicatorCutoff b := by
  have hp0 := zero_lt_one.trans hp
  have hU : evenDilationCLM (p⁻¹ * p) (mul_pos (inv_pos.mpr hp0) hp0) =
      (1 : evenSubspace →L[Complex] evenSubspace) := by
    have h1 : evenDilationCLM (p⁻¹ * p) (mul_pos (inv_pos.mpr hp0) hp0) =
        evenDilationCLM 1 zero_lt_one := by
      congr 1
      field_simp
    rw [h1, evenDilationCLM_one]
  rw [hU, mul_one]
  have h := evenIndicatorCutoff_shellComplementProduct (p * a) b a (by nlinarith)
  rw [max_eq_left hab] at h
  exact h

/-- A windowed Fourier shell translation at the trivial composite scale collapses to its
shell. -/
theorem fourierWindowedShellTranslation_scaleOne
    (a b p : ℝ) (hp : 1 < p) (hab : a ≤ b) (hbp : b ≤ p * a) :
    (evenFourierCutoff (p * a) - evenFourierCutoff b) *
        evenDilationCLM (p * p⁻¹)
          (mul_pos (zero_lt_one.trans hp) (inv_pos.mpr (zero_lt_one.trans hp))) *
        (1 - evenFourierCutoff a) =
      evenFourierCutoff (p * a) - evenFourierCutoff b := by
  have hp0 := zero_lt_one.trans hp
  have hU : evenDilationCLM (p * p⁻¹) (mul_pos hp0 (inv_pos.mpr hp0)) =
      (1 : evenSubspace →L[Complex] evenSubspace) := by
    have h1 : evenDilationCLM (p * p⁻¹) (mul_pos hp0 (inv_pos.mpr hp0)) =
        evenDilationCLM 1 zero_lt_one := by
      congr 1
      field_simp
    rw [h1, evenDilationCLM_one]
  rw [hU, mul_one]
  have h := evenFourierCutoff_shellComplementProduct (p * a) b a (by nlinarith)
  rw [max_eq_left hab] at h
  exact h

/-- Physical floor normal form: the trailing central complement is equivalent to raising the
written floor by the dilated cutoff. -/
theorem physicalWindowedShellTranslation_normalForm
    (a b p r : ℝ) (ha : 0 < a) (hp : 1 < p) (hr : 1 < r) :
    (evenIndicatorCutoff (p * a) - evenIndicatorCutoff b) *
        evenDilationCLM (p⁻¹ * r)
          (mul_pos (inv_pos.mpr (zero_lt_one.trans hp)) (zero_lt_one.trans hr)) *
        (1 - evenIndicatorCutoff a) =
      (evenIndicatorCutoff (p * a) - evenIndicatorCutoff (max b ((p * r⁻¹) * a))) *
        evenDilationCLM (p⁻¹ * r)
          (mul_pos (inv_pos.mpr (zero_lt_one.trans hp)) (zero_lt_one.trans hr)) := by
  have hp0 := zero_lt_one.trans hp
  have hr0 := zero_lt_one.trans hr
  have hmove : evenDilationCLM (p⁻¹ * r) (mul_pos (inv_pos.mpr hp0) hr0) *
      (1 - evenIndicatorCutoff a) =
      (1 - evenIndicatorCutoff ((p * r⁻¹) * a)) *
        evenDilationCLM (p⁻¹ * r) (mul_pos (inv_pos.mpr hp0) hr0) := by
    have h := evenDilationCLM_mul_evenIndicatorCutoff a (p⁻¹ * r)
      (mul_pos (inv_pos.mpr hp0) hr0)
    have hs : (p⁻¹ * r)⁻¹ * a = (p * r⁻¹) * a := by field_simp
    rw [hs] at h
    rw [mul_sub, mul_one, h, sub_mul, one_mul]
  rw [mul_assoc, hmove, ← mul_assoc]
  congr 1
  have hy : (p * r⁻¹) * a ≤ p * a := by
    have h1 : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
    nlinarith [mul_pos hp0 ha]
  exact evenIndicatorCutoff_shellComplementProduct (p * a) b ((p * r⁻¹) * a) hy

/-- Fourier floor normal form. -/
theorem fourierWindowedShellTranslation_normalForm
    (a b p r : ℝ) (ha : 0 < a) (hp : 1 < p) (hr : 1 < r) :
    (evenFourierCutoff (p * a) - evenFourierCutoff b) *
        evenDilationCLM (p * r⁻¹)
          (mul_pos (zero_lt_one.trans hp) (inv_pos.mpr (zero_lt_one.trans hr))) *
        (1 - evenFourierCutoff a) =
      (evenFourierCutoff (p * a) - evenFourierCutoff (max b ((p * r⁻¹) * a))) *
        evenDilationCLM (p * r⁻¹)
          (mul_pos (zero_lt_one.trans hp) (inv_pos.mpr (zero_lt_one.trans hr))) := by
  have hp0 := zero_lt_one.trans hp
  have hr0 := zero_lt_one.trans hr
  have hmove : evenDilationCLM (p * r⁻¹) (mul_pos hp0 (inv_pos.mpr hr0)) *
      (1 - evenFourierCutoff a) =
      (1 - evenFourierCutoff ((p * r⁻¹) * a)) *
        evenDilationCLM (p * r⁻¹) (mul_pos hp0 (inv_pos.mpr hr0)) := by
    have h := evenDilationCLM_mul_evenFourierCutoff a (p * r⁻¹)
      (mul_pos hp0 (inv_pos.mpr hr0))
    rw [mul_sub, mul_one, h, sub_mul, one_mul]
  rw [mul_assoc, hmove, ← mul_assoc]
  congr 1
  have hy : (p * r⁻¹) * a ≤ p * a := by
    have h1 : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
    nlinarith [mul_pos hp0 ha]
  exact evenFourierCutoff_shellComplementProduct (p * a) b ((p * r⁻¹) * a) hy

/-! ### Windowed cross-polarization compactness -/

/-- A windowed physical shell translation followed by a windowed Fourier shell translation is
compact, for arbitrary shell endpoints and dilation scales. -/
theorem isCompactOperator_physicalWindow_mul_fourierWindow
    (a b c d e x y : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx : 0 < x) (hy : 0 < y) :
    IsCompactOperator
      (((evenIndicatorCutoff b - evenIndicatorCutoff c) * evenDilationCLM x hx *
          (1 - evenIndicatorCutoff a) *
        ((evenFourierCutoff d - evenFourierCutoff e) * evenDilationCLM y hy *
          (1 - evenFourierCutoff a)) : evenSubspace →L[Complex] evenSubspace)) := by
  let A := evenIndicatorCutoff a
  let R := evenFourierCutoff a
  let AB := evenIndicatorCutoff b - evenIndicatorCutoff c
  let RD := evenFourierCutoff (x * d) - evenFourierCutoff (x * e)
  let Ax := evenIndicatorCutoff (x⁻¹ * a)
  let Ux := evenDilationCLM x hx
  let Uy := evenDilationCLM y hy
  have hmoveA : Ux * (1 - A) = (1 - Ax) * Ux := by
    have h := evenDilationCLM_mul_evenIndicatorCutoff a x hx
    change Ux * A = Ax * Ux at h
    rw [mul_sub, mul_one, h, sub_mul, one_mul]
  have hmoveR : Ux * (evenFourierCutoff d - evenFourierCutoff e) = RD * Ux := by
    have hd' := evenDilationCLM_mul_evenFourierCutoff d x hx
    have he' := evenDilationCLM_mul_evenFourierCutoff e x hx
    change Ux * evenFourierCutoff d = evenFourierCutoff (x * d) * Ux at hd'
    change Ux * evenFourierCutoff e = evenFourierCutoff (x * e) * Ux at he'
    rw [mul_sub, hd', he', ← sub_mul]
  have hdirect : IsCompactOperator (AB * RD) :=
    isCompactOperator_evenIndicatorDiff_mul_evenFourierDiff b c (x * d) (x * e) hb hc
  have hAx : IsCompactOperator (Ax * RD) := by
    have h₁ := isCompactOperator_evenIndicatorFourierBlock (x⁻¹ * a) (x * d)
      (mul_pos (inv_pos.mpr hx) ha)
    have h₂ := isCompactOperator_evenIndicatorFourierBlock (x⁻¹ * a) (x * e)
      (mul_pos (inv_pos.mpr hx) ha)
    have heq : Ax * RD =
        evenIndicatorCutoff (x⁻¹ * a) * evenFourierCutoff (x * d) -
          evenIndicatorCutoff (x⁻¹ * a) * evenFourierCutoff (x * e) := by
      dsimp only [Ax, RD]
      rw [mul_sub]
    rw [heq]
    exact h₁.sub h₂
  have hbracket : IsCompactOperator
      ((AB * (1 - Ax) * RD : evenSubspace →L[Complex] evenSubspace)) := by
    have h : IsCompactOperator
        ((AB * RD - AB * (Ax * RD) : evenSubspace →L[Complex] evenSubspace)) :=
      hdirect.sub (hAx.clm_comp AB)
    have heq : (AB * (1 - Ax) * RD : evenSubspace →L[Complex] evenSubspace) =
        AB * RD - AB * (Ax * RD) := by
      rw [mul_sub AB 1 Ax, mul_one, sub_mul, mul_assoc]
    rw [heq]
    exact h
  have heq :
      AB * Ux * (1 - A) * ((evenFourierCutoff d - evenFourierCutoff e) * Uy * (1 - R)) =
        (AB * (1 - Ax) * RD) * (Ux * Uy * (1 - R)) := by
    calc
      AB * Ux * (1 - A) * ((evenFourierCutoff d - evenFourierCutoff e) * Uy * (1 - R)) =
          AB * (Ux * (1 - A)) * (evenFourierCutoff d - evenFourierCutoff e) * Uy * (1 - R) := by
        simp only [mul_assoc]
      _ = AB * ((1 - Ax) * Ux) * (evenFourierCutoff d - evenFourierCutoff e) * Uy * (1 - R) := by
        rw [hmoveA]
      _ = AB * (1 - Ax) * (Ux * (evenFourierCutoff d - evenFourierCutoff e)) * Uy * (1 - R) := by
        simp only [mul_assoc]
      _ = AB * (1 - Ax) * (RD * Ux) * Uy * (1 - R) := by rw [hmoveR]
      _ = (AB * (1 - Ax) * RD) * (Ux * Uy * (1 - R)) := by simp only [mul_assoc]
  change IsCompactOperator
    ((AB * Ux * (1 - A) * ((evenFourierCutoff d - evenFourierCutoff e) * Uy * (1 - R)) :
      evenSubspace →L[Complex] evenSubspace))
  rw [heq]
  exact hbracket.comp_clm (Ux * Uy * (1 - R))

/-- A windowed Fourier shell translation followed by a windowed physical shell translation is
compact, for arbitrary shell endpoints and dilation scales. -/
theorem isCompactOperator_fourierWindow_mul_physicalWindow
    (a b c d e x y : ℝ) (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hx : 0 < x) (hy : 0 < y) :
    IsCompactOperator
      (((evenFourierCutoff b - evenFourierCutoff c) * evenDilationCLM x hx *
          (1 - evenFourierCutoff a) *
        ((evenIndicatorCutoff d - evenIndicatorCutoff e) * evenDilationCLM y hy *
          (1 - evenIndicatorCutoff a)) : evenSubspace →L[Complex] evenSubspace)) := by
  let A := evenIndicatorCutoff a
  let R := evenFourierCutoff a
  let RB := evenFourierCutoff b - evenFourierCutoff c
  let AD := evenIndicatorCutoff (x⁻¹ * d) - evenIndicatorCutoff (x⁻¹ * e)
  let Rx := evenFourierCutoff (x * a)
  let Ux := evenDilationCLM x hx
  let Uy := evenDilationCLM y hy
  have hmoveR : Ux * (1 - R) = (1 - Rx) * Ux := by
    have h := evenDilationCLM_mul_evenFourierCutoff a x hx
    change Ux * R = Rx * Ux at h
    rw [mul_sub, mul_one, h, sub_mul, one_mul]
  have hmoveA : Ux * (evenIndicatorCutoff d - evenIndicatorCutoff e) = AD * Ux := by
    have hd' := evenDilationCLM_mul_evenIndicatorCutoff d x hx
    have he' := evenDilationCLM_mul_evenIndicatorCutoff e x hx
    change Ux * evenIndicatorCutoff d = evenIndicatorCutoff (x⁻¹ * d) * Ux at hd'
    change Ux * evenIndicatorCutoff e = evenIndicatorCutoff (x⁻¹ * e) * Ux at he'
    rw [mul_sub, hd', he', ← sub_mul]
  have hdirect : IsCompactOperator (RB * AD) :=
    isCompactOperator_evenFourierDiff_mul_evenIndicatorDiff b c (x⁻¹ * d) (x⁻¹ * e) hb hc
  have hRx : IsCompactOperator (Rx * AD) := by
    have h₁ := isCompactOperator_evenFourierIndicatorBlock (x * a) (x⁻¹ * d)
      (mul_pos hx ha)
    have h₂ := isCompactOperator_evenFourierIndicatorBlock (x * a) (x⁻¹ * e)
      (mul_pos hx ha)
    have heq : Rx * AD =
        evenFourierCutoff (x * a) * evenIndicatorCutoff (x⁻¹ * d) -
          evenFourierCutoff (x * a) * evenIndicatorCutoff (x⁻¹ * e) := by
      dsimp only [Rx, AD]
      rw [mul_sub]
    rw [heq]
    exact h₁.sub h₂
  have hbracket : IsCompactOperator
      ((RB * (1 - Rx) * AD : evenSubspace →L[Complex] evenSubspace)) := by
    have h : IsCompactOperator
        ((RB * AD - RB * (Rx * AD) : evenSubspace →L[Complex] evenSubspace)) :=
      hdirect.sub (hRx.clm_comp RB)
    have heq : (RB * (1 - Rx) * AD : evenSubspace →L[Complex] evenSubspace) =
        RB * AD - RB * (Rx * AD) := by
      rw [mul_sub RB 1 Rx, mul_one, sub_mul, mul_assoc]
    rw [heq]
    exact h
  have heq :
      RB * Ux * (1 - R) * ((evenIndicatorCutoff d - evenIndicatorCutoff e) * Uy * (1 - A)) =
        (RB * (1 - Rx) * AD) * (Ux * Uy * (1 - A)) := by
    calc
      RB * Ux * (1 - R) * ((evenIndicatorCutoff d - evenIndicatorCutoff e) * Uy * (1 - A)) =
          RB * (Ux * (1 - R)) * (evenIndicatorCutoff d - evenIndicatorCutoff e) * Uy * (1 - A) := by
        simp only [mul_assoc]
      _ = RB * ((1 - Rx) * Ux) * (evenIndicatorCutoff d - evenIndicatorCutoff e) * Uy * (1 - A) := by
        rw [hmoveR]
      _ = RB * (1 - Rx) * (Ux * (evenIndicatorCutoff d - evenIndicatorCutoff e)) * Uy * (1 - A) := by
        simp only [mul_assoc]
      _ = RB * (1 - Rx) * (AD * Ux) * Uy * (1 - A) := by rw [hmoveA]
      _ = (RB * (1 - Rx) * AD) * (Ux * Uy * (1 - A)) := by simp only [mul_assoc]
  change IsCompactOperator
    ((RB * Ux * (1 - R) * ((evenIndicatorCutoff d - evenIndicatorCutoff e) * Uy * (1 - A)) :
      evenSubspace →L[Complex] evenSubspace))
  rw [heq]
  exact hbracket.comp_clm (Ux * Uy * (1 - A))

/-! ### The three-scale shell translation -/

/-- Physical branch of the three-scale shell translation: the `(p,r)` shell translation whose
inner floor is pinched by the middle scale `q`. -/
def evenPhysicalTripleShellTranslation (a p q r : ℝ) (hp : 1 < p) (hr : 1 < r) :
    evenSubspace →L[Complex] evenSubspace :=
  (evenIndicatorCutoff (p * a) - evenIndicatorCutoff (max a ((p * q⁻¹) * a))) *
    evenDilationCLM (p⁻¹ * r)
      (mul_pos (inv_pos.mpr (zero_lt_one.trans hp)) (zero_lt_one.trans hr)) *
    (1 - evenIndicatorCutoff a)

/-- Fourier branch of the three-scale shell translation. -/
def evenFourierTripleShellTranslation (a p q r : ℝ) (hp : 1 < p) (hr : 1 < r) :
    evenSubspace →L[Complex] evenSubspace :=
  (evenFourierCutoff (p * a) - evenFourierCutoff (max a ((p * q⁻¹) * a))) *
    evenDilationCLM (p * r⁻¹)
      (mul_pos (zero_lt_one.trans hp) (inv_pos.mpr (zero_lt_one.trans hr))) *
    (1 - evenFourierCutoff a)

/-- The three-scale shell translation: compact-quotient normal form of a chain of two mixed
Gram entries through the middle scale `q`. -/
def evenSoninTripleShellTranslation (a p q r : ℝ) (hp : 1 < p) (hr : 1 < r) :
    evenSubspace →L[Complex] evenSubspace :=
  evenPhysicalTripleShellTranslation a p q r hp hr +
    evenFourierTripleShellTranslation a p q r hp hr

/-- Exact physical chain law: two physical mixed shell translations through a common middle
scale multiply to the physical three-scale shell translation. -/
theorem physicalShellTranslation_chain_mul
    (a p q r : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) :
    evenPhysicalMixedShellTranslation a p q hp hq *
        evenPhysicalMixedShellTranslation a q r hq hr =
      evenPhysicalTripleShellTranslation a p q r hp hr := by
  have h := physicalWindowedShellTranslation_chain_mul a a a p q r ha hp hq hr
    (by nlinarith [zero_lt_one.trans hp]) le_rfl (by nlinarith [zero_lt_one.trans hq])
  dsimp only [evenPhysicalMixedShellTranslation, evenPhysicalTripleShellTranslation]
  exact h

/-- Exact Fourier chain law. -/
theorem fourierShellTranslation_chain_mul
    (a p q r : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) :
    evenFourierMixedShellTranslation a p q hp hq *
        evenFourierMixedShellTranslation a q r hq hr =
      evenFourierTripleShellTranslation a p q r hp hr := by
  have h := fourierWindowedShellTranslation_chain_mul a a a p q r ha hp hq hr
    (by nlinarith [zero_lt_one.trans hp]) le_rfl (by nlinarith [zero_lt_one.trans hq])
  dsimp only [evenFourierMixedShellTranslation, evenFourierTripleShellTranslation]
  exact h

/-- **Three-factor shell-overlap law.**  The chain of two mixed shell translations through a
common middle scale is, modulo compact operators, the three-scale shell translation. -/
theorem evenSoninMixedShellTranslation_chain_compactEq_triple
    (a p q r : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) :
    evenSoninMixedShellTranslation a p q hp hq *
        evenSoninMixedShellTranslation a q r hq hr =ₖ
      evenSoninTripleShellTranslation a p q r hp hr := by
  have hPP := CompactOperatorEq.of_eq (physicalShellTranslation_chain_mul a p q r ha hp hq hr)
  have hFF := CompactOperatorEq.of_eq (fourierShellTranslation_chain_mul a p q r ha hp hq hr)
  have hPF : evenPhysicalMixedShellTranslation a p q hp hq *
      evenFourierMixedShellTranslation a q r hq hr =ₖ 0 :=
    compactOperatorEq_zero_of_isCompact
      (isCompactOperator_physicalShellTranslation_mul_fourierShellTranslation
        a p q q r ha hp hq hq hr)
  have hFP : evenFourierMixedShellTranslation a p q hp hq *
      evenPhysicalMixedShellTranslation a q r hq hr =ₖ 0 :=
    compactOperatorEq_zero_of_isCompact
      (isCompactOperator_fourierShellTranslation_mul_physicalShellTranslation
        a p q q r ha hp hq hq hr)
  have hsum := CompactOperatorEq.add
    (CompactOperatorEq.add hPP hPF) (CompactOperatorEq.add hFP hFF)
  dsimp only [evenSoninMixedShellTranslation, evenSoninTripleShellTranslation]
  simpa only [mul_add, add_mul, add_zero, zero_add, add_assoc,
    add_left_comm, add_comm] using hsum

/-- The chain of two actual Sonin quadratic corners through a common middle scale is, modulo
compact operators, the three-scale shell translation. -/
theorem evenCentralSoninQuadraticCorner_chain_compactEq_triple
    (a p q r : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) :
    evenCentralSoninQuadraticCorner a p q hp hq *
        evenCentralSoninQuadraticCorner a q r hq hr =ₖ
      evenSoninTripleShellTranslation a p q r hp hr :=
  (CompactOperatorEq.mul
    (evenCentralSoninQuadraticCorner_compactEq_shellTranslation a p q ha hp hq)
    (evenCentralSoninQuadraticCorner_compactEq_shellTranslation a q r ha hq hr)).trans
    (evenSoninMixedShellTranslation_chain_compactEq_triple a p q r ha hp hq hr)

/-! ### Middle-scale absorption -/

/-- **Absorption law.**  If the middle scale dominates one of the outer scales, the three-scale
shell translation is exactly the two-scale mixed shell translation between the outer scales. -/
theorem evenSoninTripleShellTranslation_eq_pair_of_absorb
    (a p q r : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (habs : min p r ≤ q) :
    evenSoninTripleShellTranslation a p q r hp hr =
      evenSoninMixedShellTranslation a p r hp hr := by
  have hp0 := zero_lt_one.trans hp
  have hq0 := zero_lt_one.trans hq
  have hr0 := zero_lt_one.trans hr
  rcases min_le_iff.mp habs with hpq | hrq
  · have hfloor : max a ((p * q⁻¹) * a) = a := by
      apply max_eq_left
      have h1 : p * q⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv]
        exact (div_le_one hq0).mpr hpq
      nlinarith
    dsimp only [evenSoninTripleShellTranslation, evenPhysicalTripleShellTranslation,
      evenFourierTripleShellTranslation, evenSoninMixedShellTranslation,
      evenPhysicalMixedShellTranslation, evenFourierMixedShellTranslation]
    rw [hfloor]
  · have hP1 := physicalWindowedShellTranslation_normalForm a
      (max a ((p * q⁻¹) * a)) p r ha hp hr
    have hP2 := physicalWindowedShellTranslation_normalForm a a p r ha hp hr
    have hF1 := fourierWindowedShellTranslation_normalForm a
      (max a ((p * q⁻¹) * a)) p r ha hp hr
    have hF2 := fourierWindowedShellTranslation_normalForm a a p r ha hp hr
    have hfloor : max (max a ((p * q⁻¹) * a)) ((p * r⁻¹) * a) =
        max a ((p * r⁻¹) * a) := by
      have hqr : q⁻¹ ≤ r⁻¹ := by
        rw [inv_le_inv₀ hq0 hr0]
        exact hrq
      have h1 : (p * q⁻¹) * a ≤ (p * r⁻¹) * a := by
        have h2 : p * q⁻¹ ≤ p * r⁻¹ := mul_le_mul_of_nonneg_left hqr hp0.le
        exact mul_le_mul_of_nonneg_right h2 ha.le
      rw [max_assoc]
      congr 1
      exact max_eq_right h1
    dsimp only [evenSoninTripleShellTranslation, evenPhysicalTripleShellTranslation,
      evenFourierTripleShellTranslation, evenSoninMixedShellTranslation,
      evenPhysicalMixedShellTranslation, evenFourierMixedShellTranslation]
    rw [hP1, hP2, hF1, hF2, hfloor]

/-- Middle-scale absorption for the actual Sonin corners: whenever the middle scale dominates
one of the outer scales, the chain of two quadratic corners is compactly equal to the direct
quadratic corner between the outer scales. -/
theorem evenCentralSoninQuadraticCorner_chain_absorb
    (a p q r : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (habs : min p r ≤ q) :
    evenCentralSoninQuadraticCorner a p q hp hq *
        evenCentralSoninQuadraticCorner a q r hq hr =ₖ
      evenCentralSoninQuadraticCorner a p r hp hr :=
  ((evenCentralSoninQuadraticCorner_chain_compactEq_triple a p q r ha hp hq hr).trans
    (CompactOperatorEq.of_eq
      (evenSoninTripleShellTranslation_eq_pair_of_absorb a p q r ha hp hq hr habs))).trans
    (evenCentralSoninQuadraticCorner_compactEq_shellTranslation a p r ha hp hr).symm

/-! ### Polar data of the chain -/

/-- The composite floor of a reversed three-scale product is the maximum of the three
single-scale floors. -/
theorem tripleRevFloor_eq
    (a p q r : ℝ) (hp0 : 0 < p) (hq0 : 0 < q) (hr0 : 0 < r) :
    max (max a ((p * q⁻¹) * a)) ((p * r⁻¹) * max a ((r * q⁻¹) * a)) =
      max a (max ((p * q⁻¹) * a) ((p * r⁻¹) * a)) := by
  have hdist : (p * r⁻¹) * max a ((r * q⁻¹) * a) =
      max ((p * r⁻¹) * a) ((p * q⁻¹) * a) := by
    rw [mul_max_of_nonneg _ _ (by positivity : (0:ℝ) ≤ p * r⁻¹)]
    congr 1
    field_simp
  rw [hdist, max_assoc]
  congr 1
  rw [max_comm ((p * r⁻¹) * a) ((p * q⁻¹) * a), ← max_assoc, max_self]

/-- Exact physical reversed product: a three-scale shell translation composed with its reversed
companion is the physical shell with floor pinched by all three scales. -/
theorem physicalTripleShellTranslation_mul_rev
    (a p q r : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) :
    evenPhysicalTripleShellTranslation a p q r hp hr *
        evenPhysicalTripleShellTranslation a r q p hr hp =
      evenIndicatorCutoff (p * a) -
        evenIndicatorCutoff (max a (max ((p * q⁻¹) * a) ((p * r⁻¹) * a))) := by
  have hp0 := zero_lt_one.trans hp
  have hq0 := zero_lt_one.trans hq
  have hr0 := zero_lt_one.trans hr
  have hqinv : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  have hb1 : a ≤ max a ((p * q⁻¹) * a) := le_max_left _ _
  have hb2 : max a ((p * q⁻¹) * a) ≤ p * a :=
    max_le (by nlinarith) (by nlinarith [mul_pos hp0 ha])
  have hc1 : a ≤ max a ((r * q⁻¹) * a) := le_max_left _ _
  have hc2 : max a ((r * q⁻¹) * a) ≤ r * a :=
    max_le (by nlinarith) (by nlinarith [mul_pos hr0 ha])
  have hcore := physicalWindowedShellTranslation_chain_mul a
    (max a ((p * q⁻¹) * a)) (max a ((r * q⁻¹) * a)) p r p ha hp hr hp
    hb2 hc1 hc2
  have hbound : max (max a ((p * q⁻¹) * a)) ((p * r⁻¹) * max a ((r * q⁻¹) * a)) ≤ p * a := by
    apply max_le hb2
    have h1 : (p * r⁻¹) * max a ((r * q⁻¹) * a) ≤ (p * r⁻¹) * (r * a) :=
      mul_le_mul_of_nonneg_left hc2 (by positivity)
    have h2 : (p * r⁻¹) * (r * a) = p * a := by field_simp
    linarith
  have hscale := physicalWindowedShellTranslation_scaleOne a
    (max (max a ((p * q⁻¹) * a)) ((p * r⁻¹) * max a ((r * q⁻¹) * a))) p hp
    (le_trans hb1 (le_max_left _ _)) hbound
  dsimp only [evenPhysicalTripleShellTranslation]
  rw [hcore, hscale, tripleRevFloor_eq a p q r hp0 hq0 hr0]

/-- Exact Fourier reversed product. -/
theorem fourierTripleShellTranslation_mul_rev
    (a p q r : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) :
    evenFourierTripleShellTranslation a p q r hp hr *
        evenFourierTripleShellTranslation a r q p hr hp =
      evenFourierCutoff (p * a) -
        evenFourierCutoff (max a (max ((p * q⁻¹) * a) ((p * r⁻¹) * a))) := by
  have hp0 := zero_lt_one.trans hp
  have hq0 := zero_lt_one.trans hq
  have hr0 := zero_lt_one.trans hr
  have hqinv : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  have hb1 : a ≤ max a ((p * q⁻¹) * a) := le_max_left _ _
  have hb2 : max a ((p * q⁻¹) * a) ≤ p * a :=
    max_le (by nlinarith) (by nlinarith [mul_pos hp0 ha])
  have hc1 : a ≤ max a ((r * q⁻¹) * a) := le_max_left _ _
  have hc2 : max a ((r * q⁻¹) * a) ≤ r * a :=
    max_le (by nlinarith) (by nlinarith [mul_pos hr0 ha])
  have hcore := fourierWindowedShellTranslation_chain_mul a
    (max a ((p * q⁻¹) * a)) (max a ((r * q⁻¹) * a)) p r p ha hp hr hp
    hb2 hc1 hc2
  have hbound : max (max a ((p * q⁻¹) * a)) ((p * r⁻¹) * max a ((r * q⁻¹) * a)) ≤ p * a := by
    apply max_le hb2
    have h1 : (p * r⁻¹) * max a ((r * q⁻¹) * a) ≤ (p * r⁻¹) * (r * a) :=
      mul_le_mul_of_nonneg_left hc2 (by positivity)
    have h2 : (p * r⁻¹) * (r * a) = p * a := by field_simp
    linarith
  have hscale := fourierWindowedShellTranslation_scaleOne a
    (max (max a ((p * q⁻¹) * a)) ((p * r⁻¹) * max a ((r * q⁻¹) * a))) p hp
    (le_trans hb1 (le_max_left _ _)) hbound
  dsimp only [evenFourierTripleShellTranslation]
  rw [hcore, hscale, tripleRevFloor_eq a p q r hp0 hq0 hr0]

/-- The reversed product of a three-scale shell translation and its companion is, modulo
compact operators, the two-polarization shell pinched by all three scales. -/
theorem evenSoninTripleShellTranslation_mul_rev_compactEq_shell
    (a p q r : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) :
    evenSoninTripleShellTranslation a p q r hp hr *
        evenSoninTripleShellTranslation a r q p hr hp =ₖ
      evenTwoPolarizationShell (max a (max ((p * q⁻¹) * a) ((p * r⁻¹) * a))) (p * a) := by
  have hp0 := zero_lt_one.trans hp
  have hr0 := zero_lt_one.trans hr
  have hPP := CompactOperatorEq.of_eq
    (physicalTripleShellTranslation_mul_rev a p q r ha hp hq hr)
  have hFF := CompactOperatorEq.of_eq
    (fourierTripleShellTranslation_mul_rev a p q r ha hp hq hr)
  have hPF : evenPhysicalTripleShellTranslation a p q r hp hr *
      evenFourierTripleShellTranslation a r q p hr hp =ₖ 0 :=
    compactOperatorEq_zero_of_isCompact (by
      dsimp only [evenPhysicalTripleShellTranslation, evenFourierTripleShellTranslation]
      exact isCompactOperator_physicalWindow_mul_fourierWindow a (p * a)
        (max a ((p * q⁻¹) * a)) (r * a) (max a ((r * q⁻¹) * a)) (p⁻¹ * r) (r * p⁻¹)
        ha (by positivity) (lt_of_lt_of_le ha (le_max_left _ _))
        (mul_pos (inv_pos.mpr hp0) hr0) (mul_pos hr0 (inv_pos.mpr hp0)))
  have hFP : evenFourierTripleShellTranslation a p q r hp hr *
      evenPhysicalTripleShellTranslation a r q p hr hp =ₖ 0 :=
    compactOperatorEq_zero_of_isCompact (by
      dsimp only [evenPhysicalTripleShellTranslation, evenFourierTripleShellTranslation]
      exact isCompactOperator_fourierWindow_mul_physicalWindow a (p * a)
        (max a ((p * q⁻¹) * a)) (r * a) (max a ((r * q⁻¹) * a)) (p * r⁻¹) (r⁻¹ * p)
        ha (by positivity) (lt_of_lt_of_le ha (le_max_left _ _))
        (mul_pos hp0 (inv_pos.mpr hr0)) (mul_pos (inv_pos.mpr hr0) hp0))
  have hsum := CompactOperatorEq.add
    (CompactOperatorEq.add hPP hPF) (CompactOperatorEq.add hFP hFF)
  dsimp only [evenSoninTripleShellTranslation, evenTwoPolarizationShell]
  simpa only [mul_add, add_mul, add_zero, zero_add, add_assoc,
    add_left_comm, add_comm] using hsum

/-- The adjoint of a chain of two quadratic corners is the reversed chain. -/
theorem adjoint_evenCentralSoninChainCorner
    (a p q r : ℝ) (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) :
    (evenCentralSoninQuadraticCorner a p q hp hq *
        evenCentralSoninQuadraticCorner a q r hq hr)† =
      evenCentralSoninQuadraticCorner a r q hr hq *
        evenCentralSoninQuadraticCorner a q p hq hp := by
  rw [adjoint_mul_clm, adjoint_evenCentralSoninQuadraticCorner,
    adjoint_evenCentralSoninQuadraticCorner]

/-- Final Calkin projection of the chain: a two-polarization shell at the first outer scale,
pinched by all three scales. -/
theorem evenCentralSoninChainCorner_mul_adjoint_compactEq_shell
    (a p q r : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) :
    (evenCentralSoninQuadraticCorner a p q hp hq *
        evenCentralSoninQuadraticCorner a q r hq hr) *
      (evenCentralSoninQuadraticCorner a p q hp hq *
        evenCentralSoninQuadraticCorner a q r hq hr)† =ₖ
      evenTwoPolarizationShell (max a (max ((p * q⁻¹) * a) ((p * r⁻¹) * a))) (p * a) := by
  rw [adjoint_evenCentralSoninChainCorner]
  exact (CompactOperatorEq.mul
    (evenCentralSoninQuadraticCorner_chain_compactEq_triple a p q r ha hp hq hr)
    (evenCentralSoninQuadraticCorner_chain_compactEq_triple a r q p ha hr hq hp)).trans
    (evenSoninTripleShellTranslation_mul_rev_compactEq_shell a p q r ha hp hq hr)

/-- Initial Calkin projection of the chain: a two-polarization shell at the last outer scale,
pinched by all three scales. -/
theorem evenCentralSoninChainCorner_adjoint_mul_compactEq_shell
    (a p q r : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) :
    (evenCentralSoninQuadraticCorner a p q hp hq *
        evenCentralSoninQuadraticCorner a q r hq hr)† *
      (evenCentralSoninQuadraticCorner a p q hp hq *
        evenCentralSoninQuadraticCorner a q r hq hr) =ₖ
      evenTwoPolarizationShell (max a (max ((r * q⁻¹) * a) ((r * p⁻¹) * a))) (r * a) := by
  rw [adjoint_evenCentralSoninChainCorner]
  exact (CompactOperatorEq.mul
    (evenCentralSoninQuadraticCorner_chain_compactEq_triple a r q p ha hr hq hp)
    (evenCentralSoninQuadraticCorner_chain_compactEq_triple a p q r ha hp hq hr)).trans
    (evenSoninTripleShellTranslation_mul_rev_compactEq_shell a r q p ha hr hq hp)

/-- Every chain of two quadratic corners through a middle scale is a partial isometry in the
Calkin algebra. -/
theorem evenCentralSoninChainCorner_isCalkinPartialIsometry
    (a p q r : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) :
    IsCalkinPartialIsometry
      (evenCentralSoninQuadraticCorner a p q hp hq *
        evenCentralSoninQuadraticCorner a q r hq hr) := by
  have hp0 := zero_lt_one.trans hp
  have hq0 := zero_lt_one.trans hq
  have hr0 := zero_lt_one.trans hr
  have hqinv : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  have hI := evenCentralSoninChainCorner_adjoint_mul_compactEq_shell a p q r ha hp hq hr
  have hF := evenCentralSoninChainCorner_mul_adjoint_compactEq_shell a p q r ha hp hq hr
  have hpinv : p⁻¹ < 1 := inv_lt_one_of_one_lt₀ hp
  have hrinv : r⁻¹ < 1 := inv_lt_one_of_one_lt₀ hr
  have hIs : 0 < max a (max ((r * q⁻¹) * a) ((r * p⁻¹) * a)) :=
    lt_of_lt_of_le ha (le_max_left _ _)
  have hIst : max a (max ((r * q⁻¹) * a) ((r * p⁻¹) * a)) ≤ r * a := by
    apply max_le (by nlinarith)
    exact max_le (by nlinarith [mul_pos hr0 ha]) (by nlinarith [mul_pos hr0 ha])
  have hFs : 0 < max a (max ((p * q⁻¹) * a) ((p * r⁻¹) * a)) :=
    lt_of_lt_of_le ha (le_max_left _ _)
  have hFst : max a (max ((p * q⁻¹) * a) ((p * r⁻¹) * a)) ≤ p * a := by
    apply max_le (by nlinarith)
    exact max_le (by nlinarith [mul_pos hp0 ha]) (by nlinarith [mul_pos hp0 ha])
  exact ⟨compactEq_idempotent_of_compactEq hI
      (evenTwoPolarizationShell_mul_compactEq_self _ _ hIs hIst),
    compactEq_idempotent_of_compactEq hF
      (evenTwoPolarizationShell_mul_compactEq_self _ _ hFs hFst)⟩

/-- **Tropical thickness law.**  The floor of the chain's initial shell multiplied by the
minimum of the three scales recovers the shell ceiling: the multiplicative thickness of every
chain shell is exactly the minimum scale visited. -/
theorem tripleShellFloor_mul_min
    (a p q r : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) :
    max a (max ((r * q⁻¹) * a) ((r * p⁻¹) * a)) * min p (min q r) = r * a := by
  have hp0 := zero_lt_one.trans hp
  have hq0 := zero_lt_one.trans hq
  have hr0 := zero_lt_one.trans hr
  rcases le_total p (min q r) with h1 | h1
  · have hpq : p ≤ q := h1.trans (min_le_left _ _)
    have hpr : p ≤ r := h1.trans (min_le_right _ _)
    have hmin : min p (min q r) = p := min_eq_left h1
    have hqp : q⁻¹ ≤ p⁻¹ := by
      rw [inv_le_inv₀ hq0 hp0]
      exact hpq
    have hx : (r * q⁻¹) * a ≤ (r * p⁻¹) * a := by
      have h2 : r * q⁻¹ ≤ r * p⁻¹ := mul_le_mul_of_nonneg_left hqp hr0.le
      exact mul_le_mul_of_nonneg_right h2 ha.le
    have hy : a ≤ (r * p⁻¹) * a := by
      have h2 : 1 ≤ r * p⁻¹ := by
        rw [← div_eq_mul_inv]
        exact (le_div_iff₀ hp0).mpr (by simpa using hpr)
      nlinarith
    rw [hmin, max_eq_right hx, max_eq_right hy]
    field_simp
  · rcases le_total q r with h2 | h2
    · have hqp : q ≤ p := by
        have := min_eq_left h2 ▸ h1
        exact this
      have hmin : min p (min q r) = q := by
        rw [min_eq_left h2, min_eq_right hqp]
      have hpq : p⁻¹ ≤ q⁻¹ := by
        rw [inv_le_inv₀ hp0 hq0]
        exact hqp
      have hx : (r * p⁻¹) * a ≤ (r * q⁻¹) * a := by
        have h3 : r * p⁻¹ ≤ r * q⁻¹ := mul_le_mul_of_nonneg_left hpq hr0.le
        exact mul_le_mul_of_nonneg_right h3 ha.le
      have hy : a ≤ (r * q⁻¹) * a := by
        have h3 : 1 ≤ r * q⁻¹ := by
          rw [← div_eq_mul_inv]
          exact (le_div_iff₀ hq0).mpr (by simpa using h2)
        nlinarith
      rw [hmin, max_eq_left hx, max_eq_right hy]
      field_simp
    · have hrp : r ≤ p := by
        have := min_eq_right h2 ▸ h1
        exact this
      have hmin : min p (min q r) = r := by
        rw [min_eq_right h2, min_eq_right hrp]
      have hrq : r * q⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv]
        exact (div_le_one hq0).mpr h2
      have hrp' : r * p⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv]
        exact (div_le_one hp0).mpr hrp
      have hx : (r * q⁻¹) * a ≤ a := by nlinarith
      have hy : (r * p⁻¹) * a ≤ a := by nlinarith
      rw [hmin, max_eq_left (max_le hx hy)]
      ring

/-! ### General-order initial shells for pair and triple chains -/

/-- General-order initial projection of a mixed Gram entry: no order relation between the two
scales is assumed. -/
theorem evenSoninMixedShellTranslation_mul_pair_compactEq_shell
    (a p r : ℝ) (ha : 0 < a) (hp : 1 < p) (hr : 1 < r) :
    evenSoninMixedShellTranslation a r p hr hp *
        evenSoninMixedShellTranslation a p r hp hr =ₖ
      evenTwoPolarizationShell (max a ((r * p⁻¹) * a)) (r * a) := by
  have hp0 := zero_lt_one.trans hp
  have hr0 := zero_lt_one.trans hr
  have hPP : evenPhysicalMixedShellTranslation a r p hr hp *
      evenPhysicalMixedShellTranslation a p r hp hr =
      evenIndicatorCutoff (r * a) - evenIndicatorCutoff (max a ((r * p⁻¹) * a)) := by
    have hcore := physicalWindowedShellTranslation_chain_mul a a a r p r ha hr hp hr
      (by nlinarith) le_rfl (by nlinarith)
    have hbound : max a ((r * p⁻¹) * a) ≤ r * a := by
      apply max_le (by nlinarith)
      have h1 : (r * p⁻¹) * a ≤ (r * p⁻¹) * (p * a) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      have h2 : (r * p⁻¹) * (p * a) = r * a := by field_simp
      linarith
    have hscale := physicalWindowedShellTranslation_scaleOne a
      (max a ((r * p⁻¹) * a)) r hr (le_max_left _ _) hbound
    dsimp only [evenPhysicalMixedShellTranslation]
    rw [hcore, hscale]
  have hFF : evenFourierMixedShellTranslation a r p hr hp *
      evenFourierMixedShellTranslation a p r hp hr =
      evenFourierCutoff (r * a) - evenFourierCutoff (max a ((r * p⁻¹) * a)) := by
    have hcore := fourierWindowedShellTranslation_chain_mul a a a r p r ha hr hp hr
      (by nlinarith) le_rfl (by nlinarith)
    have hbound : max a ((r * p⁻¹) * a) ≤ r * a := by
      apply max_le (by nlinarith)
      have h1 : (r * p⁻¹) * a ≤ (r * p⁻¹) * (p * a) :=
        mul_le_mul_of_nonneg_left (by nlinarith) (by positivity)
      have h2 : (r * p⁻¹) * (p * a) = r * a := by field_simp
      linarith
    have hscale := fourierWindowedShellTranslation_scaleOne a
      (max a ((r * p⁻¹) * a)) r hr (le_max_left _ _) hbound
    dsimp only [evenFourierMixedShellTranslation]
    rw [hcore, hscale]
  have hPF : evenPhysicalMixedShellTranslation a r p hr hp *
      evenFourierMixedShellTranslation a p r hp hr =ₖ 0 :=
    compactOperatorEq_zero_of_isCompact
      (isCompactOperator_physicalShellTranslation_mul_fourierShellTranslation
        a r p p r ha hr hp hp hr)
  have hFP : evenFourierMixedShellTranslation a r p hr hp *
      evenPhysicalMixedShellTranslation a p r hp hr =ₖ 0 :=
    compactOperatorEq_zero_of_isCompact
      (isCompactOperator_fourierShellTranslation_mul_physicalShellTranslation
        a r p p r ha hr hp hp hr)
  have hsum := CompactOperatorEq.add
    (CompactOperatorEq.add (CompactOperatorEq.of_eq hPP) hPF)
    (CompactOperatorEq.add hFP (CompactOperatorEq.of_eq hFF))
  dsimp only [evenSoninMixedShellTranslation, evenTwoPolarizationShell]
  simpa only [mul_add, add_mul, add_zero, zero_add, add_assoc,
    add_left_comm, add_comm] using hsum

/-- Initial shell of a pinched chain, read against the reversed pair: the middle scale enters
the floor. -/
theorem evenSoninMixedShellTranslation_mul_triple_compactEq_shell
    (a p q r : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) :
    evenSoninMixedShellTranslation a r p hr hp *
        evenSoninTripleShellTranslation a p q r hp hr =ₖ
      evenTwoPolarizationShell (max a ((r * p⁻¹) * max a ((p * q⁻¹) * a))) (r * a) := by
  have hp0 := zero_lt_one.trans hp
  have hq0 := zero_lt_one.trans hq
  have hr0 := zero_lt_one.trans hr
  have hqinv : q⁻¹ < 1 := inv_lt_one_of_one_lt₀ hq
  have hm2a : a ≤ max a ((p * q⁻¹) * a) := le_max_left _ _
  have hm2p : max a ((p * q⁻¹) * a) ≤ p * a :=
    max_le (by nlinarith) (by nlinarith [mul_pos hp0 ha])
  have hbound : max a ((r * p⁻¹) * max a ((p * q⁻¹) * a)) ≤ r * a := by
    apply max_le (by nlinarith)
    have h1 : (r * p⁻¹) * max a ((p * q⁻¹) * a) ≤ (r * p⁻¹) * (p * a) :=
      mul_le_mul_of_nonneg_left hm2p (by positivity)
    have h2 : (r * p⁻¹) * (p * a) = r * a := by field_simp
    linarith
  have hPP : evenPhysicalMixedShellTranslation a r p hr hp *
      evenPhysicalTripleShellTranslation a p q r hp hr =
      evenIndicatorCutoff (r * a) -
        evenIndicatorCutoff (max a ((r * p⁻¹) * max a ((p * q⁻¹) * a))) := by
    have hcore := physicalWindowedShellTranslation_chain_mul a a
      (max a ((p * q⁻¹) * a)) r p r ha hr hp hr
      (by nlinarith) hm2a hm2p
    have hscale := physicalWindowedShellTranslation_scaleOne a
      (max a ((r * p⁻¹) * max a ((p * q⁻¹) * a))) r hr (le_max_left _ _) hbound
    dsimp only [evenPhysicalMixedShellTranslation, evenPhysicalTripleShellTranslation]
    rw [hcore, hscale]
  have hFF : evenFourierMixedShellTranslation a r p hr hp *
      evenFourierTripleShellTranslation a p q r hp hr =
      evenFourierCutoff (r * a) -
        evenFourierCutoff (max a ((r * p⁻¹) * max a ((p * q⁻¹) * a))) := by
    have hcore := fourierWindowedShellTranslation_chain_mul a a
      (max a ((p * q⁻¹) * a)) r p r ha hr hp hr
      (by nlinarith) hm2a hm2p
    have hscale := fourierWindowedShellTranslation_scaleOne a
      (max a ((r * p⁻¹) * max a ((p * q⁻¹) * a))) r hr (le_max_left _ _) hbound
    dsimp only [evenFourierMixedShellTranslation, evenFourierTripleShellTranslation]
    rw [hcore, hscale]
  have hPF : evenPhysicalMixedShellTranslation a r p hr hp *
      evenFourierTripleShellTranslation a p q r hp hr =ₖ 0 :=
    compactOperatorEq_zero_of_isCompact (by
      dsimp only [evenPhysicalMixedShellTranslation, evenFourierTripleShellTranslation]
      exact isCompactOperator_physicalWindow_mul_fourierWindow a (r * a) a (p * a)
        (max a ((p * q⁻¹) * a)) (r⁻¹ * p) (p * r⁻¹)
        ha (by positivity) ha
        (mul_pos (inv_pos.mpr hr0) hp0) (mul_pos hp0 (inv_pos.mpr hr0)))
  have hFP : evenFourierMixedShellTranslation a r p hr hp *
      evenPhysicalTripleShellTranslation a p q r hp hr =ₖ 0 :=
    compactOperatorEq_zero_of_isCompact (by
      dsimp only [evenFourierMixedShellTranslation, evenPhysicalTripleShellTranslation]
      exact isCompactOperator_fourierWindow_mul_physicalWindow a (r * a) a (p * a)
        (max a ((p * q⁻¹) * a)) (r * p⁻¹) (p⁻¹ * r)
        ha (by positivity) ha
        (mul_pos hr0 (inv_pos.mpr hp0)) (mul_pos (inv_pos.mpr hp0) hr0))
  have hsum := CompactOperatorEq.add
    (CompactOperatorEq.add (CompactOperatorEq.of_eq hPP) hPF)
    (CompactOperatorEq.add hFP (CompactOperatorEq.of_eq hFF))
  dsimp only [evenSoninMixedShellTranslation, evenSoninTripleShellTranslation,
    evenTwoPolarizationShell]
  simpa only [mul_add, add_mul, add_zero, zero_add, add_assoc,
    add_left_comm, add_comm] using hsum

/-! ### Noncompactness of nondegenerate shells -/

/-- A cutoff acting on a normalized indicator whose support it contains is the identity. -/
theorem indicatorCutoff_normalizedIndicator_of_subset
    (c s : Set ℝ) (hc : MeasurableSet c) (hs : MeasurableSet s)
    (hfin : volume s ≠ ∞) (hsub : s ⊆ c) :
    indicatorCutoff c hc (normalizedIndicator s hs hfin) =
      normalizedIndicator s hs hfin := by
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae c hc (normalizedIndicator s hs hfin),
    normalizedIndicator_ae s hs hfin] with x hcut hnorm
  rw [hcut]
  by_cases hxc : x ∈ c
  · rw [Set.indicator_of_mem hxc]
  · have hxs : x ∉ s := fun hmem => hxc (hsub hmem)
    rw [Set.indicator_of_notMem hxc, hnorm, Set.indicator_of_notMem hxs]
    simp

/-- A cutoff acting on a normalized indicator whose support it misses is zero. -/
theorem indicatorCutoff_normalizedIndicator_of_disjoint
    (c s : Set ℝ) (hc : MeasurableSet c) (hs : MeasurableSet s)
    (hfin : volume s ≠ ∞) (hdisj : ∀ x ∈ c, x ∉ s) :
    indicatorCutoff c hc (normalizedIndicator s hs hfin) = 0 := by
  apply Lp.ext
  filter_upwards [indicatorCutoff_ae c hc (normalizedIndicator s hs hfin),
    normalizedIndicator_ae s hs hfin,
    Lp.coeFn_zero (E := Complex) (p := 2) (μ := (volume : Measure ℝ))] with x hcut hnorm hzero
  rw [hcut, hzero]
  by_cases hxc : x ∈ c
  · rw [Set.indicator_of_mem hxc, hnorm, Set.indicator_of_notMem (hdisj x hxc)]
    simp
  · rw [Set.indicator_of_notMem hxc]
    simp

/-- A physical cutoff at least the ceiling fixes every symmetric shell vector. -/
theorem evenIndicatorCutoff_evenShellVectorEven_of_le
    (s t t' : ℝ) (hst : s < t) (htt' : t ≤ t') (n : ℕ) :
    evenIndicatorCutoff t' (evenShellVectorEven s t hst n) =
      evenShellVectorEven s t hst n := by
  apply Subtype.ext
  rw [coe_evenIndicatorCutoff_apply, coe_evenShellVectorEven]
  dsimp only [evenShellVector]
  apply indicatorCutoff_normalizedIndicator_of_subset
  intro x hx
  have hmem := evenShellCell_subset_Icc hst n hx
  change x ∈ Set.Icc (-t') t'
  exact ⟨by linarith [hmem.1], by linarith [hmem.2]⟩

/-- A physical cutoff at most the floor annihilates every symmetric shell vector. -/
theorem evenIndicatorCutoff_evenShellVectorEven_eq_zero
    (s t s' : ℝ) (hst : s < t) (hs' : s' ≤ s) (n : ℕ) :
    evenIndicatorCutoff s' (evenShellVectorEven s t hst n) = 0 := by
  apply Subtype.ext
  rw [coe_evenIndicatorCutoff_apply, coe_evenShellVectorEven]
  dsimp only [evenShellVector]
  rw [indicatorCutoff_normalizedIndicator_of_disjoint]
  · rfl
  · intro x hxc hxs
    have h1 : |x| ≤ s' := by
      have hxc' : x ∈ Set.Icc (-s') s' := hxc
      exact abs_le.mpr ⟨hxc'.1, hxc'.2⟩
    have h2 : shellLeft s t n < |x| := (Set.mem_preimage.mp hxs).1
    have h3 : s < shellLeft s t n := lt_shellLeft hst n
    linarith

/-- A nondegenerate physical shell projection is not compact: it fixes an orthonormal shell
sequence. -/
theorem not_isCompactOperator_evenIndicatorShellDiff
    (s t : ℝ) (hs : 0 < s) (hst : s < t) :
    ¬ IsCompactOperator (evenIndicatorCutoff t - evenIndicatorCutoff s) := by
  intro hcpt
  have hfix : ∀ n, (evenIndicatorCutoff t - evenIndicatorCutoff s)
      (evenShellVectorEven s t hst n) = evenShellVectorEven s t hst n := by
    intro n
    have h1 := evenIndicatorCutoff_evenShellVectorEven_of_le s t t hst le_rfl n
    have h0 := evenIndicatorCutoff_evenShellVectorEven_eq_zero s t s hst le_rfl n
    rw [ContinuousLinearMap.sub_apply, h1, h0, sub_zero]
  have hnull := IsCompactOperator.norm_apply_tendsto_zero_of_orthonormal
    (evenIndicatorCutoff t - evenIndicatorCutoff s) hcpt
    (evenShellVectorEven_orthonormal s t hs hst)
  have hone : (fun n => ‖(evenIndicatorCutoff t - evenIndicatorCutoff s)
      (evenShellVectorEven s t hst n)‖) = fun _ => (1 : ℝ) := by
    funext n
    rw [hfix n]
    exact (evenShellVectorEven_orthonormal s t hs hst).norm_eq_one n
  rw [hone] at hnull
  have := tendsto_nhds_unique hnull tendsto_const_nhds
  norm_num at this

/-- A nondegenerate two-polarization shell is not compact. -/
theorem not_isCompactOperator_evenTwoPolarizationShell
    (s t : ℝ) (hs : 0 < s) (hst : s < t) :
    ¬ IsCompactOperator (evenTwoPolarizationShell s t) := by
  intro hcpt
  have hcross : IsCompactOperator
      ((evenIndicatorCutoff t - evenIndicatorCutoff s) *
        (evenFourierCutoff t - evenFourierCutoff s)) :=
    isCompactOperator_evenIndicatorDiff_mul_evenFourierDiff t s t s (hs.trans hst) hs
  have hmul : IsCompactOperator
      ((evenIndicatorCutoff t - evenIndicatorCutoff s) * evenTwoPolarizationShell s t) :=
    hcpt.clm_comp (evenIndicatorCutoff t - evenIndicatorCutoff s)
  have hexpand : (evenIndicatorCutoff t - evenIndicatorCutoff s) *
      evenTwoPolarizationShell s t =
      (evenIndicatorCutoff t - evenIndicatorCutoff s) +
        (evenIndicatorCutoff t - evenIndicatorCutoff s) *
          (evenFourierCutoff t - evenFourierCutoff s) := by
    dsimp only [evenTwoPolarizationShell]
    rw [mul_add, evenIndicatorShell_mul_self s t hst.le]
  have hshell : IsCompactOperator (evenIndicatorCutoff t - evenIndicatorCutoff s) := by
    have h : IsCompactOperator
        ((evenIndicatorCutoff t - evenIndicatorCutoff s) * evenTwoPolarizationShell s t -
          (evenIndicatorCutoff t - evenIndicatorCutoff s) *
            (evenFourierCutoff t - evenFourierCutoff s)) := hmul.sub hcross
    have heq : evenIndicatorCutoff t - evenIndicatorCutoff s =
        (evenIndicatorCutoff t - evenIndicatorCutoff s) * evenTwoPolarizationShell s t -
          (evenIndicatorCutoff t - evenIndicatorCutoff s) *
            (evenFourierCutoff t - evenFourierCutoff s) := by
      rw [hexpand]
      abel
    rw [heq]
    exact h
  exact not_isCompactOperator_evenIndicatorShellDiff s t hs hst hshell

/-! ### Strictness: the pinch never absorbs -/

/-- **Pinch rigidity.**  If the middle scale is strictly below both outer scales, the
three-scale shell translation is not compactly equal to the two-scale mixed shell translation:
the middle scale leaves a permanent shell defect. -/
theorem evenSoninTripleShellTranslation_not_compactEq_pair_of_pinch
    (a p q r : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hr : 1 < r)
    (hqp : q < p) (hqr : q < r) :
    ¬ (evenSoninTripleShellTranslation a p q r hp hr =ₖ
        evenSoninMixedShellTranslation a p r hp hr) := by
  intro hcontra
  have hp0 := zero_lt_one.trans hp
  have hq0 := zero_lt_one.trans hq
  have hr0 := zero_lt_one.trans hr
  have hmul := CompactOperatorEq.left_mul
    (evenSoninMixedShellTranslation a r p hr hp) hcontra
  have hshells :
      evenTwoPolarizationShell (max a ((r * p⁻¹) * max a ((p * q⁻¹) * a))) (r * a) =ₖ
        evenTwoPolarizationShell (max a ((r * p⁻¹) * a)) (r * a) :=
    ((evenSoninMixedShellTranslation_mul_triple_compactEq_shell
        a p q r ha hp hq hr).symm.trans hmul).trans
      (evenSoninMixedShellTranslation_mul_pair_compactEq_shell a p r ha hp hr)
  have hm2 : max a ((p * q⁻¹) * a) = (p * q⁻¹) * a := by
    apply max_eq_right
    have h1 : 1 ≤ p * q⁻¹ := by
      rw [← div_eq_mul_inv]
      exact (le_div_iff₀ hq0).mpr (by simpa using hqp.le)
    nlinarith
  have hf1 : max a ((r * p⁻¹) * max a ((p * q⁻¹) * a)) = (r * q⁻¹) * a := by
    rw [hm2]
    have hcomp : (r * p⁻¹) * ((p * q⁻¹) * a) = (r * q⁻¹) * a := by
      field_simp
    rw [hcomp]
    apply max_eq_right
    have h1 : 1 ≤ r * q⁻¹ := by
      rw [← div_eq_mul_inv]
      exact (le_div_iff₀ hq0).mpr (by simpa using hqr.le)
    nlinarith
  rw [hf1] at hshells
  have hf2lt : max a ((r * p⁻¹) * a) < (r * q⁻¹) * a := by
    apply max_lt
    · have h1 : 1 < r * q⁻¹ := by
        rw [← div_eq_mul_inv]
        exact (lt_div_iff₀ hq0).mpr (by simpa using hqr)
      nlinarith
    · have h1 : p⁻¹ ≤ q⁻¹ := by
        rw [inv_le_inv₀ hp0 hq0]
        exact hqp.le
      have h2 : p⁻¹ ≠ q⁻¹ := by
        simp only [ne_eq, inv_inj]
        exact fun h => (ne_of_gt hqp) h
      have h3 : p⁻¹ < q⁻¹ := lt_of_le_of_ne h1 h2
      have h4 : r * p⁻¹ < r * q⁻¹ := by nlinarith
      nlinarith
  have hf2pos : 0 < max a ((r * p⁻¹) * a) := lt_of_lt_of_le ha (le_max_left _ _)
  have hdiff : evenTwoPolarizationShell (max a ((r * p⁻¹) * a)) ((r * q⁻¹) * a) =ₖ 0 := by
    have heq : evenTwoPolarizationShell (max a ((r * p⁻¹) * a)) ((r * q⁻¹) * a) =
        evenTwoPolarizationShell (max a ((r * p⁻¹) * a)) (r * a) -
          evenTwoPolarizationShell ((r * q⁻¹) * a) (r * a) := by
      dsimp only [evenTwoPolarizationShell]
      abel
    rw [heq]
    have h1 := CompactOperatorEq.sub hshells.symm
      (CompactOperatorEq.refl (evenTwoPolarizationShell ((r * q⁻¹) * a) (r * a)))
    exact h1.trans (CompactOperatorEq.of_eq (sub_self _))
  exact not_isCompactOperator_evenTwoPolarizationShell
    (max a ((r * p⁻¹) * a)) ((r * q⁻¹) * a) hf2pos hf2lt
    (by simpa only [CompactOperatorEq, sub_zero] using hdiff)

/-- **Absorption dichotomy for the actual corners.**  A chain of two Sonin quadratic corners
through a middle scale collapses to the direct corner modulo compact operators exactly when the
middle scale dominates one of the outer scales. -/
theorem evenCentralSoninChainCorner_absorb_iff
    (a p q r : ℝ) (ha : 0 < a) (hp : 1 < p) (hq : 1 < q) (hr : 1 < r) :
    (evenCentralSoninQuadraticCorner a p q hp hq *
        evenCentralSoninQuadraticCorner a q r hq hr =ₖ
      evenCentralSoninQuadraticCorner a p r hp hr) ↔ min p r ≤ q := by
  constructor
  · intro h
    by_contra hlt
    have hlt' : q < min p r := not_le.mp hlt
    have hqp : q < p := hlt'.trans_le (min_le_left _ _)
    have hqr : q < r := hlt'.trans_le (min_le_right _ _)
    have htriple : evenSoninTripleShellTranslation a p q r hp hr =ₖ
        evenSoninMixedShellTranslation a p r hp hr :=
      ((evenCentralSoninQuadraticCorner_chain_compactEq_triple
          a p q r ha hp hq hr).symm.trans h).trans
        (evenCentralSoninQuadraticCorner_compactEq_shellTranslation a p r ha hp hr)
    exact evenSoninTripleShellTranslation_not_compactEq_pair_of_pinch
      a p q r ha hp hq hr hqp hqr htriple
  · intro h
    exact evenCentralSoninQuadraticCorner_chain_absorb a p q r ha hp hq hr h

end RHTower
