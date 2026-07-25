import GaloisForLFunctions.HTGeometry.GradedShiftInertness
import GaloisForLFunctions.HTGeometry.PolarShiftClassification
import Mathlib

/-!
# Leading-term inertness for an arbitrary graded coefficient ring

Let `K` be a field with a `C`-automorphism `sigma`, let `x` be transcendental with
`sigma x = x + 1`, and let `D` be a ring carrying a `GradedLead` structure realised inside `K` by an
injective ring map intertwining the two shifts and sending the frequency-zero part onto `C[x]`.

The leading-term map sends a quotient from `D` to the quotient of the two leading coefficients and
intertwines the shifts.  Consequently a rational function which is a translation defect of the
fraction field of the realisation is already a translation defect of `C(x)`:

`(sigma - 1) Frac (phi D) ∩ C(x) = (sigma - 1) C(x)`.

Only the character of the frequency group enters; nothing about the analytic nature of `D`.
-/

open Polynomial

namespace HTGeometry

variable {Λ : Type*} [AddCommGroup Λ] [LinearOrder Λ] [IsOrderedAddMonoid Λ]

/-- **Leading-term inertness.**  A rational function that is the translation defect of a quotient
from a graded shift ring is already the translation defect of a rational function. -/
theorem graded_rational_defect_inert
    {K : Type*} [Field K] [Algebra ℂ K] {x : K} (hx : Transcendental ℂ x)
    (sigma : K ≃ₐ[ℂ] K) (hsig : sigma x = x + 1)
    {D : Type*} [CommRing D] (Dat : GradedLead Λ D)
    (phi : D →+* K) (hinj : Function.Injective phi)
    (hphisigma : ∀ f : D, phi (Dat.sigma f) = sigma (phi f))
    (hphiemb : ∀ p : ℂ[X], phi (Dat.emb p) = Polynomial.aeval x p)
    {P Q : D} (hQ : Q ≠ 0) {v : K} (hv : v ∈ coordBase x)
    (hdef : sigma (phi P / phi Q) - phi P / phi Q = v) :
    ∃ R ∈ coordBase x, sigma R - R = v := by
  classical
  have hae : ∀ {p : ℂ[X]}, p ≠ 0 → Polynomial.aeval x p ≠ 0 := by
    intro p hp h
    exact hp (aeval_coord_injective hx (by simpa using h))
  obtain ⟨rn, rd, hrv⟩ := (IntermediateField.mem_adjoin_simple_iff ℂ v).mp hv
  rcases eq_or_ne rd 0 with rfl | hrd
  · exact ⟨0, zero_mem _, by rw [hrv]; simp⟩
  rcases eq_or_ne P 0 with rfl | hP
  · refine ⟨0, zero_mem _, ?_⟩
    rw [map_zero, zero_div, map_zero, sub_zero] at hdef
    rw [← hdef]
    simp
  have hphiQ : phi Q ≠ 0 := fun h => hQ (hinj (by simpa using h))
  have hsQ : Dat.sigma Q ≠ 0 := Dat.sigma_ne_zero hQ
  have hphisQ : phi (Dat.sigma Q) ≠ 0 := fun h => hsQ (hinj (by simpa using h))
  have hrdK : Polynomial.aeval x rd ≠ 0 := hae hrd
  have hsigphiQ : sigma (phi Q) ≠ 0 := by
    intro h
    exact hphiQ (sigma.injective (h.trans (map_zero sigma).symm))
  -- clear denominators on the realised side, then descend along injectivity
  have hclear : phi (Dat.emb rd * (Dat.sigma P * Q - P * Dat.sigma Q))
      = phi (Dat.emb rn * (Dat.sigma Q * Q)) := by
    simp only [map_mul, map_sub, hphiemb, hphisigma]
    rw [map_div₀] at hdef
    rw [hrv] at hdef
    field_simp at hdef
    linear_combination hdef
  have hpoly : Dat.emb rd * (Dat.sigma P * Q - P * Dat.sigma Q)
      = Dat.emb rn * (Dat.sigma Q * Q) := hinj hclear
  have hlead := Dat.lead_shift_identity hP hQ hrd hpoly
  set A : ℂ[X] := Dat.lead P with hA
  set B : ℂ[X] := Dat.lead Q with hB
  have hBne : B ≠ 0 := Dat.lead_ne_zero hQ
  have hBsne : B.comp (X + Polynomial.C 1) ≠ 0 := by
    intro h0
    refine hBne ?_
    have := congrArg (fun p : ℂ[X] => p.comp (X - Polynomial.C 1)) h0
    simpa [Polynomial.comp_assoc, Polynomial.add_comp, Polynomial.sub_comp] using this
  have hBK : Polynomial.aeval x B ≠ 0 := hae hBne
  have hBsK : Polynomial.aeval x (B.comp (X + Polynomial.C 1)) ≠ 0 := hae hBsne
  refine ⟨Polynomial.aeval x A / Polynomial.aeval x B, ?_, ?_⟩
  · exact div_mem (aeval_mem_coordBase x A) (aeval_mem_coordBase x B)
  · rw [hrv, map_div₀, sigma_aeval_coord sigma hsig, sigma_aeval_coord sigma hsig]
    have hK := congrArg (fun p : ℂ[X] => Polynomial.aeval x p) hlead
    simp only [map_mul, map_sub] at hK
    simp only [Polynomial.C_1] at hBsK hK ⊢
    rw [div_sub_div _ _ hBsK hBK, div_eq_div_iff (mul_ne_zero hBsK hBK) hrdK]
    linear_combination hK

end HTGeometry
