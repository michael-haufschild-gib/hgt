import GaloisForLFunctions.HTGeometry.ShiftMinpolyTranscendence
import Mathlib

/-!
# The descent engine phrased inside a fixed ambient field

`descentStep` and `transcendental_of_defect_unattainable` are stated for an abstract base field `E`
with an algebra map into `K`.  To run them up a tower of intermediate fields one wants everything
phrased inside the single ambient field `K`, with the admissible spans living in `K` as well.

This file supplies that form: the restriction of an automorphism to a stable intermediate field, and
the ambient-field versions of the descent step and of the terminal transcendence statement.
-/

open Polynomial IntermediateField

namespace HTGeometry

variable {K : Type*} [Field K] [Algebra ℂ K]

section Restrict

variable (sigma : K ≃+* K) (S : IntermediateField ℂ K)

/-- Restrict an automorphism to an intermediate field it stabilises. -/
noncomputable def restrictEquiv (h : ∀ u : K, sigma u ∈ S ↔ u ∈ S) : S ≃+* S where
  toFun u := ⟨sigma u.1, (h u.1).mpr u.2⟩
  invFun v := ⟨sigma.symm v.1, by
    have := (h (sigma.symm v.1)).mp (by simpa using v.2)
    exact this⟩
  left_inv u := by ext; simp
  right_inv v := by ext; simp
  map_mul' u v := by ext; simp
  map_add' u v := by ext; simp

@[simp] theorem restrictEquiv_coe (h : ∀ u : K, sigma u ∈ S ↔ u ∈ S) (u : S) :
    ((restrictEquiv sigma S h u : S) : K) = sigma (u : K) := rfl

end Restrict

section Ambient

variable {sigma : K ≃+* K} {S : IntermediateField ℂ K}

/-- The linear map realising an intermediate field inside the ambient field. -/
noncomputable def subVal (S : IntermediateField ℂ K) : S →ₗ[ℂ] K :=
  (IntermediateField.val S).toLinearMap

@[simp] theorem subVal_apply (S : IntermediateField ℂ K) (u : S) : subVal S u = (u : K) := rfl

/-- **Terminal transcendence, ambient form.**  If no element of `S` has `sigma`-defect a nonzero
constant multiple of `c`, no element with defect `c` is algebraic over `S`. -/
theorem transcendental_ambient
    (hstab : ∀ u : K, sigma u ∈ S ↔ u ∈ S)
    (hsigmaC : ∀ a : ℂ, sigma (algebraMap ℂ K a) = algebraMap ℂ K a)
    {y c : K} (hcS : c ∈ S) (hsy : sigma y = y + c)
    {T W : Submodule ℂ K}
    (hdefect : ∀ u ∈ S, ∀ v ∈ T, sigma u - u = v → v ∈ W)
    (hcT : c ∈ T) (hcW : c ∉ W) :
    Transcendental S y := by
  classical
  set sigmaS : S ≃+* S := restrictEquiv sigma S hstab with hsigmaS
  have hcompat : ∀ a : S, sigma (algebraMap S K a) = algebraMap S K (sigmaS a) := by
    intro a; rfl
  have hsy' : sigma y = y + algebraMap S K (⟨c, hcS⟩ : S) := hsy
  refine transcendental_of_defect_unattainable (Cst := ℂ) (sigma := sigma) (sigmaE := sigmaS)
    hcompat hsy' (T := T.comap (subVal S)) (W := W.comap (subVal S)) ?_ ?_ ?_
  · intro u v hv hdef
    have hu : (u : K) ∈ S := u.2
    have hvK : (v : K) ∈ T := hv
    have hdefK : sigma (u : K) - (u : K) = (v : K) := by
      have := congrArg (fun z : S => (z : K)) hdef
      simpa [hsigmaS] using this
    exact hdefect _ hu _ hvK hdefK
  · exact hcT
  · intro hmem
    exact hcW hmem

/-- Normalise a quotient of polynomials to lowest terms with monic denominator. -/
theorem exists_coprime_monic_repr {y : K} (htr : Transcendental S y) {b : K}
    (hb : b ∈ IntermediateField.adjoin S {y}) :
    ∃ N D : Polynomial S, D.Monic ∧ IsCoprime N D ∧ b = aeval y N / aeval y D := by
  classical
  obtain ⟨r, t, hrt⟩ := (IntermediateField.mem_adjoin_simple_iff S b).mp hb
  have hinj := aeval_injective_of_transcendental (E := S) htr
  rcases eq_or_ne t 0 with rfl | ht
  · exact ⟨0, 1, Polynomial.monic_one, isCoprime_one_right, by simp [hrt]⟩
  · set g : Polynomial S := GCDMonoid.gcd r t with hg
    have hgne : g ≠ 0 := gcd_ne_zero_of_right ht
    set r' : Polynomial S := r / g with hr'
    set t' : Polynomial S := t / g with ht'
    have hcop' : IsCoprime r' t' := isCoprime_div_gcd_div_gcd ht
    have hrmul : r' * g = r := by
      rw [hr', mul_comm]
      exact EuclideanDomain.mul_div_cancel' hgne (gcd_dvd_left r t)
    have htmul : t' * g = t := by
      rw [ht', mul_comm]
      exact EuclideanDomain.mul_div_cancel' hgne (gcd_dvd_right r t)
    have ht'ne : t' ≠ 0 := fun h => ht (by rw [← htmul, h, zero_mul])
    set u : S := (t'.leadingCoeff)⁻¹ with hu
    have hlead : t'.leadingCoeff ≠ 0 := Polynomial.leadingCoeff_ne_zero.mpr ht'ne
    have hune : u ≠ 0 := inv_ne_zero hlead
    refine ⟨r' * Polynomial.C u, t' * Polynomial.C u, ?_, ?_, ?_⟩
    · rw [Polynomial.Monic, Polynomial.leadingCoeff_mul, Polynomial.leadingCoeff_C, hu,
        mul_inv_cancel₀ hlead]
    · obtain ⟨p, q, hpq⟩ := hcop'
      refine ⟨p * Polynomial.C u⁻¹, q * Polynomial.C u⁻¹, ?_⟩
      have hCu : (Polynomial.C u⁻¹) * (Polynomial.C u) = (1 : Polynomial S) := by
        rw [← Polynomial.C_mul, inv_mul_cancel₀ hune, Polynomial.C_1]
      calc p * Polynomial.C u⁻¹ * (r' * Polynomial.C u)
            + q * Polynomial.C u⁻¹ * (t' * Polynomial.C u)
          = (p * r' + q * t') * (Polynomial.C u⁻¹ * Polynomial.C u) := by ring
        _ = 1 := by rw [hCu, hpq, mul_one]
    · have hgK : aeval y g ≠ 0 := fun h => hgne (hinj (by simpa using h))
      have huK : (algebraMap S K u) ≠ 0 :=
        (map_ne_zero_iff _ (algebraMap S K).injective).mpr hune
      rw [hrt, ← hrmul, ← htmul]
      simp only [map_mul, Polynomial.aeval_C]
      rw [mul_div_mul_right _ _ hgK, mul_div_mul_right _ _ huK]

/-- **Descent step, ambient form.**  The `sigma`-defect of an element of `S(y)` lies in the span of
the old admissible defects together with `c`. -/
theorem descentStep_ambient
    (hstab : ∀ u : K, sigma u ∈ S ↔ u ∈ S)
    {y c : K} (hcS : c ∈ S) (hsy : sigma y = y + c)
    (htr : Transcendental S y)
    {T W : Submodule ℂ K}
    (hfix : ∀ u ∈ S, sigma u = u → ∃ a : ℂ, u = algebraMap ℂ K a)
    (hdefect : ∀ u ∈ S, ∀ v ∈ T, sigma u - u = v → v ∈ W)
    (hcT : c ∈ T) (hcW : c ∉ W)
    {b w : K} (hb : b ∈ IntermediateField.adjoin S {y}) (hwS : w ∈ S) (hwT : w ∈ T)
    (hdef : sigma b - b = w) :
    w ∈ W ⊔ Submodule.span ℂ {c} := by
  classical
  obtain ⟨N, D, hD, hcop, hbeq⟩ := exists_coprime_monic_repr htr hb
  set sigmaS : S ≃+* S := restrictEquiv sigma S hstab with hsigmaS
  have hcompat : ∀ a : S, sigma (algebraMap S K a) = algebraMap S K (sigmaS a) := fun a => rfl
  have hsy' : sigma y = y + algebraMap S K (⟨c, hcS⟩ : S) := hsy
  have hfix' : ∀ v : S, sigmaS v = v → ∃ a : ℂ, v = algebraMap ℂ S a := by
    intro v hv
    have hvK : sigma (v : K) = (v : K) := congrArg (fun z : S => (z : K)) hv
    obtain ⟨a, ha⟩ := hfix _ v.2 hvK
    exact ⟨a, Subtype.ext (by simpa using ha)⟩
  have hdefect' : ∀ v : S, ∀ z ∈ T.comap (subVal S), sigmaS v - v = z → z ∈ W.comap (subVal S) := by
    intro v z hz hdz
    have hdK : sigma (v : K) - (v : K) = (z : K) :=
      congrArg (fun x : S => (x : K)) hdz
    exact hdefect _ v.2 _ hz hdK
  have hdefS : sigma (aeval y N / aeval y D) - aeval y N / aeval y D
      = algebraMap S K (⟨w, hwS⟩ : S) := by rw [← hbeq]; exact hdef
  have hres := descentStep_defect_mem (Cst := ℂ) (sigma := sigma) (sigmaE := sigmaS)
    hcompat hsy' htr hfix' hdefect' (T := T.comap (subVal S)) (W := W.comap (subVal S))
    hcT hcW hD hcop (w := (⟨w, hwS⟩ : S)) hwT hdefS
  have hmap := Submodule.mem_map_of_mem (f := subVal S) hres
  have hle : Submodule.map (subVal S)
      ((W.comap (subVal S)) ⊔ Submodule.span ℂ {(⟨c, hcS⟩ : S)})
      ≤ W ⊔ Submodule.span ℂ {c} := by
    rw [Submodule.map_le_iff_le_comap]
    refine sup_le (Submodule.comap_mono le_sup_left) ?_
    rw [Submodule.span_le]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self c)
  exact hle hmap

/-- **Fixed-point step, ambient form.**  A `sigma`-invariant element of `S(y)` is a constant. -/
theorem descentStep_fixed_ambient
    (hstab : ∀ u : K, sigma u ∈ S ↔ u ∈ S)
    {y c : K} (hcS : c ∈ S) (hsy : sigma y = y + c)
    (htr : Transcendental S y)
    {T W : Submodule ℂ K}
    (hfix : ∀ u ∈ S, sigma u = u → ∃ a : ℂ, u = algebraMap ℂ K a)
    (hdefect : ∀ u ∈ S, ∀ v ∈ T, sigma u - u = v → v ∈ W)
    (hcT : c ∈ T) (hcW : c ∉ W)
    {b : K} (hb : b ∈ IntermediateField.adjoin S {y}) (hdef : sigma b = b) :
    ∃ a : ℂ, b = algebraMap ℂ K a := by
  classical
  obtain ⟨N, D, hD, hcop, hbeq⟩ := exists_coprime_monic_repr htr hb
  set sigmaS : S ≃+* S := restrictEquiv sigma S hstab with hsigmaS
  have hcompat : ∀ a : S, sigma (algebraMap S K a) = algebraMap S K (sigmaS a) := fun a => rfl
  have hsy' : sigma y = y + algebraMap S K (⟨c, hcS⟩ : S) := hsy
  have hfix' : ∀ v : S, sigmaS v = v → ∃ a : ℂ, v = algebraMap ℂ S a := by
    intro v hv
    have hvK : sigma (v : K) = (v : K) := congrArg (fun z : S => (z : K)) hv
    obtain ⟨a, ha⟩ := hfix _ v.2 hvK
    exact ⟨a, Subtype.ext (by simpa using ha)⟩
  have hdefect' : ∀ v : S, ∀ z ∈ T.comap (subVal S), sigmaS v - v = z →
      z ∈ W.comap (subVal S) := by
    intro v z hz hdz
    exact hdefect _ v.2 _ hz (congrArg (fun x : S => (x : K)) hdz)
  have hdefS : sigma (aeval y N / aeval y D) = aeval y N / aeval y D := by
    rw [← hbeq]; exact hdef
  obtain ⟨a, ha⟩ := descentStep_fixed (Cst := ℂ) (sigma := sigma) (sigmaE := sigmaS)
    hcompat hsy' htr hfix' hdefect' (T := T.comap (subVal S)) (W := W.comap (subVal S))
    hcT hcW hD hcop hdefS
  refine ⟨a, ?_⟩
  rw [hbeq, ha, ← IsScalarTower.algebraMap_apply ℂ S K]

end Ambient

end HTGeometry
