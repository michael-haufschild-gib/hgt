import GaloisForLFunctions.RHTower.FieldOneFiniteStageThetaCoreEulerIdentification

/-!
# Finite Euler operator on the literal even-Schwartz source

This file identifies the abstract finite Euler operator with the exact
coefficient-faithful subset expansion on the dense even-Schwartz carrier.
It supplies the operator-side weld missing from the literal theta-core
calculation.
-/

namespace GaloisForLFunctions.RHTower

noncomputable section

open IsDedekindDomain
open scoped BigOperators

/-- One local Euler factor acting within Schwartz space. -/
def fieldOneFiniteStageThetaEulerSchwartzTerm
    (S : Finset (HeightOneSpectrum ℤ)) (v : ↥S)
    (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  f - ((Real.sqrt (fieldOneFinitePlacePrime v.1 : ℝ) : ℂ)⁻¹) •
    RHTower.ccmNormalizedSchwartzDilation
      (fieldOneFinitePlacePrime v.1 : ℝ)⁻¹
      (inv_pos.mpr (zero_lt_one.trans
        (fieldOneFinitePlacePrime_real_gt_one v.1))) f

/-- Finite Euler product acting within Schwartz space in the same order as
the bounded Euler operator. -/
def fieldOneFiniteStageThetaEulerSchwartz
    (S : Finset (HeightOneSpectrum ℤ))
    (f : SchwartzMap ℝ ℂ) : SchwartzMap ℝ ℂ :=
  S.attach.toList.foldr
    (fun v g => fieldOneFiniteStageThetaEulerSchwartzTerm S v g) f

/-- A normalized local factor is literally `f(x)-p⁻¹f(x/p)` pointwise. -/
theorem fieldOneFiniteStageThetaEulerSchwartzTerm_apply
    (S : Finset (HeightOneSpectrum ℤ)) (v : ↥S)
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    fieldOneFiniteStageThetaEulerSchwartzTerm S v f x =
      f x - ((fieldOneFinitePlacePrime v.1 : ℝ) : ℂ)⁻¹ *
        f (x * (fieldOneFinitePlacePrime v.1 : ℝ)⁻¹) := by
  let p : ℝ := fieldOneFinitePlacePrime v.1
  have hp : 0 < p := zero_lt_one.trans
    (fieldOneFinitePlacePrime_real_gt_one v.1)
  have hcoeffR : (Real.sqrt p)⁻¹ * Real.sqrt p⁻¹ = p⁻¹ := by
    rw [Real.sqrt_inv, ← mul_inv, Real.mul_self_sqrt hp.le]
  have hcoeffC :
      (Real.sqrt p : ℂ)⁻¹ * (Real.sqrt p⁻¹ : ℂ) = (p : ℂ)⁻¹ := by
    norm_cast
  unfold fieldOneFiniteStageThetaEulerSchwartzTerm
  rw [RHTower.ccmNormalizedSchwartzDilation_apply]
  change f x - (Real.sqrt p : ℂ)⁻¹ *
      ((Real.sqrt p⁻¹ : ℂ) * f (p⁻¹ * x)) =
    f x - (p : ℂ)⁻¹ * f (x * p⁻¹)
  rw [← mul_assoc, hcoeffC]
  congr 2
  ring

theorem fieldOneRationalPrimeUnit_real_coe
    (v : HeightOneSpectrum ℤ) :
    ((((fieldOneRationalPrimeUnit v : ℚˣ) : ℚ) : ℝ)) =
      (fieldOneFinitePlacePrime v : ℝ) := by
  rfl

theorem fieldOneFiniteStageSoninSubsetRationalScale_insert
    {S : Finset (HeightOneSpectrum ℤ)} (v : ↥S) (A : Finset ↥S)
    (hv : v ∉ A) :
    ((((fieldOneFiniteStageSoninSubsetRationalScale (insert v A) : ℚˣ) : ℚ) : ℝ)) =
      (fieldOneFinitePlacePrime v.1 : ℝ)⁻¹ *
        ((((fieldOneFiniteStageSoninSubsetRationalScale A : ℚˣ) : ℚ) : ℝ)) := by
  unfold fieldOneFiniteStageSoninSubsetRationalScale
  rw [Finset.prod_insert hv]
  push_cast
  rw [fieldOneRationalPrimeUnit_real_coe]

theorem fieldOneFiniteStageSoninSubsetCoefficient_insert
    {S : Finset (HeightOneSpectrum ℤ)} (v : ↥S) (A : Finset ↥S)
    (hv : v ∉ A) :
    fieldOneFiniteStageSoninSubsetCoefficient (insert v A) =
      -(((fieldOneFinitePlacePrime v.1 : ℝ) : ℂ)⁻¹) *
        fieldOneFiniteStageSoninSubsetCoefficient A := by
  unfold fieldOneFiniteStageSoninSubsetCoefficient
  rw [Finset.prod_insert hv]
  rfl

/-- Expanding any duplicate-free local-factor list preserves each subset,
prime scale, and coefficient exactly. -/
theorem fieldOneFiniteStageThetaEulerSchwartzList_apply
    (S : Finset (HeightOneSpectrum ℤ)) (l : List ↥S) (hl : l.Nodup)
    (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    l.foldr (fun v g => fieldOneFiniteStageThetaEulerSchwartzTerm S v g) f x =
      ∑ A ∈ l.toFinset.powerset,
        f (x *
            ((((fieldOneFiniteStageSoninSubsetRationalScale A : ℚˣ) : ℚ) : ℝ))) *
          fieldOneFiniteStageSoninSubsetCoefficient A := by
  induction l generalizing f x with
  | nil =>
      simp [fieldOneFiniteStageSoninSubsetRationalScale,
        fieldOneFiniteStageSoninSubsetCoefficient]
  | cons v l ih =>
      rcases List.nodup_cons.mp hl with ⟨hv, hl⟩
      have hvfin : v ∉ l.toFinset := by simpa using hv
      have hdisjoint : Disjoint l.toFinset.powerset
          (l.toFinset.powerset.image (insert v)) := by
        rw [Finset.disjoint_left]
        intro A hA hAi
        rcases Finset.mem_image.mp hAi with ⟨B, hB, rfl⟩
        exact (Finset.notMem_of_mem_powerset_of_notMem hA hvfin)
          (Finset.mem_insert_self v B)
      have hinjective : ∀ A ∈ l.toFinset.powerset,
          ∀ B ∈ l.toFinset.powerset,
            insert v A = insert v B → A = B := by
        intro A hA B hB h
        have hvA := Finset.notMem_of_mem_powerset_of_notMem hA hvfin
        have hvB := Finset.notMem_of_mem_powerset_of_notMem hB hvfin
        have he := congrArg (fun C : Finset ↥S => C.erase v) h
        simpa [hvA, hvB] using he
      have hinsert :
          (∑ A ∈ l.toFinset.powerset,
            f (x *
                ((((fieldOneFiniteStageSoninSubsetRationalScale
                  (insert v A) : ℚˣ) : ℚ) : ℝ))) *
              fieldOneFiniteStageSoninSubsetCoefficient (insert v A)) =
            -(((fieldOneFinitePlacePrime v.1 : ℝ) : ℂ)⁻¹) *
              ∑ A ∈ l.toFinset.powerset,
                f ((x * (fieldOneFinitePlacePrime v.1 : ℝ)⁻¹) *
                    ((((fieldOneFiniteStageSoninSubsetRationalScale A : ℚˣ) : ℚ) : ℝ))) *
                  fieldOneFiniteStageSoninSubsetCoefficient A := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro A hA
        have hvA := Finset.notMem_of_mem_powerset_of_notMem hA hvfin
        rw [fieldOneFiniteStageSoninSubsetRationalScale_insert v A hvA,
          fieldOneFiniteStageSoninSubsetCoefficient_insert v A hvA]
        rw [show x * ((fieldOneFinitePlacePrime v.1 : ℝ)⁻¹ *
            ((((fieldOneFiniteStageSoninSubsetRationalScale A : ℚˣ) : ℚ) : ℝ))) =
              (x * (fieldOneFinitePlacePrime v.1 : ℝ)⁻¹) *
                ((((fieldOneFiniteStageSoninSubsetRationalScale A : ℚˣ) : ℚ) : ℝ)) by
          ring]
        ring
      rw [List.foldr_cons,
        fieldOneFiniteStageThetaEulerSchwartzTerm_apply,
        ih hl, ih hl, List.toFinset_cons, Finset.powerset_insert,
        Finset.sum_union hdisjoint, Finset.sum_image hinjective, hinsert]
      ring

/-- One bounded local factor and its literal Schwartz representative agree
on the dense source carrier. -/
theorem fieldOneFiniteStageThetaEulerTerm_ccmEvenSchwartzSource
    (S : Finset (HeightOneSpectrum ℤ)) (v : ↥S)
    (f : SchwartzMap ℝ ℂ) :
    fieldOneFiniteStageThetaEulerTerm S v (RHTower.ccmEvenSchwartzSource f) =
      RHTower.ccmEvenSchwartzSource
        (fieldOneFiniteStageThetaEulerSchwartzTerm S v f) := by
  unfold fieldOneFiniteStageThetaEulerSchwartzTerm
  let p : ℝ := fieldOneFinitePlacePrime v.1
  have hp : 0 < p := zero_lt_one.trans
    (fieldOneFinitePlacePrime_real_gt_one v.1)
  have hsymm :
      (RHTower.evenDilationUnitary p hp).symm
          (RHTower.ccmEvenSchwartzSource f) =
        RHTower.ccmEvenSchwartzSource
          (RHTower.ccmNormalizedSchwartzDilation p⁻¹
            (inv_pos.mpr hp) f) := by
    rw [RHTower.ccmEvenSchwartzSource_normalizedDilation]
    rfl
  unfold fieldOneFiniteStageThetaEulerTerm RHTower.evenPrimeLocalFactor
  simp only [sub_apply, one_apply_eq_self, smul_apply]
  change RHTower.ccmEvenSchwartzSource f - (Real.sqrt p : ℂ)⁻¹ •
      (RHTower.evenDilationUnitary p hp).symm
        (RHTower.ccmEvenSchwartzSource f) = _
  rw [hsymm]
  change RHTower.ccmEvenSchwartzSource f - (Real.sqrt p : ℂ)⁻¹ •
      RHTower.ccmEvenSchwartzSource
        (RHTower.ccmNormalizedSchwartzDilation p⁻¹ (inv_pos.mpr hp) f) =
    RHTower.ccmEvenSchwartzSource
      (f - (Real.sqrt p : ℂ)⁻¹ •
        RHTower.ccmNormalizedSchwartzDilation p⁻¹ (inv_pos.mpr hp) f)
  calc
    RHTower.ccmEvenSchwartzSource f - (Real.sqrt p : ℂ)⁻¹ •
        RHTower.ccmEvenSchwartzSource
          (RHTower.ccmNormalizedSchwartzDilation p⁻¹ (inv_pos.mpr hp) f) =
      RHTower.ccmEvenSchwartzSourceCLM f - (Real.sqrt p : ℂ)⁻¹ •
        RHTower.ccmEvenSchwartzSourceCLM
          (RHTower.ccmNormalizedSchwartzDilation p⁻¹ (inv_pos.mpr hp) f) := by
        rw [RHTower.ccmEvenSchwartzSourceCLM_apply,
          RHTower.ccmEvenSchwartzSourceCLM_apply]
    _ = RHTower.ccmEvenSchwartzSourceCLM
        (f - (Real.sqrt p : ℂ)⁻¹ •
          RHTower.ccmNormalizedSchwartzDilation p⁻¹ (inv_pos.mpr hp) f) := by
      rw [map_sub, map_smul]
    _ = RHTower.ccmEvenSchwartzSource
        (f - (Real.sqrt p : ℂ)⁻¹ •
          RHTower.ccmNormalizedSchwartzDilation p⁻¹ (inv_pos.mpr hp) f) := by
      rw [RHTower.ccmEvenSchwartzSourceCLM_apply]

/-- Any finite product of local factors agrees with the corresponding
Schwartz fold on the dense source carrier. -/
theorem fieldOneFiniteStageThetaEulerList_ccmEvenSchwartzSource
    (S : Finset (HeightOneSpectrum ℤ)) (l : List ↥S)
    (f : SchwartzMap ℝ ℂ) :
    (l.map (fieldOneFiniteStageThetaEulerTerm S)).prod
        (RHTower.ccmEvenSchwartzSource f) =
      RHTower.ccmEvenSchwartzSource
        (l.foldr
          (fun v g => fieldOneFiniteStageThetaEulerSchwartzTerm S v g) f) := by
  induction l with
  | nil => simp
  | cons v l ih =>
      simp only [List.map_cons, List.prod_cons, List.foldr_cons,
        mul_apply_eq_comp]
      rw [ih, fieldOneFiniteStageThetaEulerTerm_ccmEvenSchwartzSource]

/-- The Schwartz Euler product is pointwise the literal subset expansion. -/
theorem fieldOneFiniteStageThetaEulerSchwartz_apply
    (S : Finset (HeightOneSpectrum ℤ)) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    fieldOneFiniteStageThetaEulerSchwartz S f x =
      fieldOneFiniteStageThetaSubsetEulerValue S f x := by
  unfold fieldOneFiniteStageThetaEulerSchwartz
  unfold fieldOneFiniteStageThetaSubsetEulerValue
  simpa [Finset.attach_eq_univ] using
    fieldOneFiniteStageThetaEulerSchwartzList_apply
      S S.attach.toList S.attach.nodup_toList f x

/-- The same value in exponent-cube coordinates. -/
theorem fieldOneFiniteStageThetaEulerSchwartz_apply_eq_positiveEulerValue
    (S : Finset (HeightOneSpectrum ℤ)) (f : SchwartzMap ℝ ℂ) (x : ℝ) :
    fieldOneFiniteStageThetaEulerSchwartz S f x =
      fieldOneFiniteStageThetaPositiveEulerValue S f x := by
  rw [fieldOneFiniteStageThetaEulerSchwartz_apply,
    fieldOneFiniteStageThetaPositiveEulerValue_eq_subset]

/-- **Coefficient-faithful operator/source identification.**  The candidate
finite Euler operator acts on every dense even-Schwartz source as the literal
prime-labelled Euler expansion, before passing to any quotient or divisor
scalarization. -/
theorem fieldOneFiniteStageThetaEulerOperator_ccmEvenSchwartzSource
    (S : Finset (HeightOneSpectrum ℤ)) (f : SchwartzMap ℝ ℂ) :
    fieldOneFiniteStageThetaEulerOperator S
        (RHTower.ccmEvenSchwartzSource f) =
      RHTower.ccmEvenSchwartzSource
        (fieldOneFiniteStageThetaEulerSchwartz S f) := by
  exact fieldOneFiniteStageThetaEulerList_ccmEvenSchwartzSource
    S S.attach.toList f

end

end GaloisForLFunctions.RHTower
