import GaloisForLFunctions.HTGeometry.SkewLaurentOperatorDivision

/-!
# Explicit cyclic traces on skew Laurent division rings

An additive coefficient functional invariant under the automorphism extends
to a cyclic trace by reading outer coefficient zero. The proof uses the
finite support antidiagonal at that coefficient and reverses its two indices.

For the quantum Laurent parameter `c`, construct the inner scaling
automorphism on `F((v))` coefficientwise. Inner coefficient zero is invariant,
so this yields an actual normalized cyclic trace on `F((v))((u;σ))`.
Its value on an ordered Laurent word is exactly the constant coefficient.

No normalized trace existence, Xi source construction, C*-completion
compatibility, or Riemann-hypothesis premise is assumed or supplied here.
-/

open HahnSeries
open scoped Classical

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {K : Type*} [Field K]

/-- Read a scalar from its twisted multiplication operator by applying it to one. -/
def skewLaurentScalarCoefficient (σ : K ≃+* K) (n : ℤ) :
    skewLaurentOperatorRing σ →+ K where
  toFun f := f.val.coeff n 1
  map_zero' := rfl
  map_add' _ _ := rfl

theorem skewLaurentCoefficient_normalForm (σ : K ≃+* K)
    (f : skewLaurentOperatorRing σ) (n : ℤ) :
    skewLaurentCoefficient σ n (skewLaurentScalarCoefficient σ n f) =
      f.val.coeff n := by
  obtain ⟨a, ha⟩ := f.property n
  change skewLaurentCoefficient σ n (f.val.coeff n 1) = f.val.coeff n
  rw [← ha, skewLaurentCoefficient_apply_one]

/-- The concrete multiplication has the expected skew convolution coefficients. -/
theorem skewLaurentScalarCoefficient_mul (σ : K ≃+* K)
    (f g : skewLaurentOperatorRing σ) (n : ℤ) :
    skewLaurentScalarCoefficient σ n (f * g) =
      ∑ ij ∈ Finset.antidiagonal f.val.isPWO_support g.val.isPWO_support n,
        skewLaurentScalarCoefficient σ ij.1 f *
          (σ ^ ij.1) (skewLaurentScalarCoefficient σ ij.2 g) := by
  let ev : AddMonoid.End K →+ K :=
    { toFun := fun T => T 1
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  change ev ((f.val * g.val).coeff n) = _
  rw [HahnSeries.coeff_mul, map_sum]
  apply Finset.sum_congr rfl
  intro ij _
  rw [← skewLaurentCoefficient_normalForm σ f ij.1,
    ← skewLaurentCoefficient_normalForm σ g ij.2, skewLaurentCoefficient_mul]
  exact skewLaurentCoefficient_apply_one σ (ij.1 + ij.2) _

@[simp] theorem skewLaurentScalarCoefficient_one (σ : K ≃+* K) :
    skewLaurentScalarCoefficient σ 0 1 = 1 := by
  change (1 : HahnSeries ℤ (AddMonoid.End K)).coeff 0 1 = 1
  simp

@[simp] theorem skewLaurentScalarCoefficient_constant (σ : K ≃+* K) (x : K) :
    skewLaurentScalarCoefficient σ 0 (skewLaurentConstant σ x) = x := by
  change (HahnSeries.single 0 (skewLaurentCoefficient σ 0 x)).coeff 0 1 = x
  simp

/-- Outer coefficient zero followed by a coefficient-field additive functional. -/
def skewLaurentCoefficientTrace (σ : K ≃+* K) {A : Type*} [AddCommGroup A]
    (ε : K →+ A) : skewLaurentOperatorRing σ →+ A :=
  ε.comp (skewLaurentScalarCoefficient σ 0)

theorem skewLaurentCoefficientTrace_cyclic (σ : K ≃+* K)
    {A : Type*} [AddCommGroup A] (ε : K →+ A)
    (hε : ∀ (n : ℤ) (x : K), ε ((σ ^ n) x) = ε x)
    (f g : skewLaurentOperatorRing σ) :
    skewLaurentCoefficientTrace σ ε (f * g) =
      skewLaurentCoefficientTrace σ ε (g * f) := by
  change ε (skewLaurentScalarCoefficient σ 0 (f * g)) =
    ε (skewLaurentScalarCoefficient σ 0 (g * f))
  rw [skewLaurentScalarCoefficient_mul, skewLaurentScalarCoefficient_mul,
    map_sum, map_sum]
  refine Finset.sum_bij (fun ij _ => ij.swap) ?_ ?_ ?_ ?_
  · intro ij hij
    exact Finset.swap_mem_antidiagonal.mpr hij
  · intro ij _ kl _ h
    exact Prod.swap_injective h
  · intro ij hij
    exact ⟨ij.swap, Finset.swap_mem_antidiagonal.mpr hij, by simp⟩
  · rintro ⟨i, j⟩ hij
    have hij' := (Finset.mem_antidiagonal.mp hij).2.2
    have hj : j = -i := by dsimp at hij'; omega
    subst j
    dsimp
    have h := hε (-i)
      (skewLaurentScalarCoefficient σ i f *
        (σ ^ i) (skewLaurentScalarCoefficient σ (-i) g))
    simpa [map_mul, mul_comm] using h.symm

@[simp] theorem skewLaurentCoefficientTrace_one (σ : K ≃+* K)
    {A : Type*} [AddCommGroup A] (ε : K →+ A) :
    skewLaurentCoefficientTrace σ ε 1 = ε 1 := by
  change ε (skewLaurentScalarCoefficient σ 0 1) = ε 1
  rw [skewLaurentScalarCoefficient_one]

section Quantum

variable {F : Type*} [Field F]

/-- Rescale a Laurent variable by a nonzero field element. -/
def quantumLaurentScaleSeries (c : Fˣ) (f : HahnSeries ℤ F) : HahnSeries ℤ F where
  coeff n := (↑(c ^ n) : F) * f.coeff n
  isPWO_support' := f.isPWO_support.mono (by
    intro n hn
    change (↑(c ^ n) : F) * f.coeff n ≠ 0 at hn
    exact (mul_ne_zero_iff.mp hn).2)

@[simp] theorem quantumLaurentScaleSeries_coeff (c : Fˣ) (f : HahnSeries ℤ F) (n : ℤ) :
    (quantumLaurentScaleSeries c f).coeff n = (↑(c ^ n) : F) * f.coeff n := rfl

@[simp] theorem quantumLaurentScaleSeries_support (c : Fˣ) (f : HahnSeries ℤ F) :
    (quantumLaurentScaleSeries c f).support = f.support := by
  ext n
  simp only [HahnSeries.mem_support, quantumLaurentScaleSeries_coeff, mul_ne_zero_iff]
  exact ⟨And.right, fun h => ⟨Units.ne_zero (c ^ n), h⟩⟩

theorem quantumLaurentScaleSeries_mul (c : Fˣ) (f g : HahnSeries ℤ F) :
    quantumLaurentScaleSeries c (f * g) =
      quantumLaurentScaleSeries c f * quantumLaurentScaleSeries c g := by
  ext n
  have ha :
      Finset.antidiagonal (quantumLaurentScaleSeries c f).isPWO_support
        (quantumLaurentScaleSeries c g).isPWO_support n =
      Finset.antidiagonal f.isPWO_support g.isPWO_support n := by
    ext ij
    simp only [Finset.mem_antidiagonal, quantumLaurentScaleSeries_support]
  rw [quantumLaurentScaleSeries_coeff, HahnSeries.coeff_mul, HahnSeries.coeff_mul, ha,
    Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro ij hij
  rw [quantumLaurentScaleSeries_coeff, quantumLaurentScaleSeries_coeff,
    ← (Finset.mem_antidiagonal.mp hij).2.2, zpow_add, Units.val_mul]
  ring

/-- The scaling automorphism is constructed coefficientwise with inverse scaling. -/
def quantumLaurentScaleAut (c : Fˣ) : HahnSeries ℤ F ≃+* HahnSeries ℤ F where
  toFun := quantumLaurentScaleSeries c
  invFun := quantumLaurentScaleSeries c⁻¹
  left_inv f := by
    ext n
    simp only [quantumLaurentScaleSeries_coeff, ← mul_assoc, ← Units.val_mul,
      inv_zpow, inv_mul_cancel, Units.val_one, one_mul]
  right_inv f := by
    ext n
    simp only [quantumLaurentScaleSeries_coeff, ← mul_assoc, ← Units.val_mul,
      inv_zpow, mul_inv_cancel, Units.val_one, one_mul]
  map_add' f g := by ext n; simp [HahnSeries.coeff_add, mul_add]
  map_mul' := quantumLaurentScaleSeries_mul c

/-- Scaling is an action of the field's units on its Laurent series field. -/
def quantumLaurentScaleHom : Fˣ →* RingAut (HahnSeries ℤ F) where
  toFun := quantumLaurentScaleAut
  map_one' := by
    ext f n
    simp [quantumLaurentScaleAut]
  map_mul' c d := by
    ext f n
    change (↑((c * d) ^ n) : F) * f.coeff n =
      (↑(c ^ n) : F) * ((↑(d ^ n) : F) * f.coeff n)
    rw [mul_zpow, Units.val_mul, mul_assoc]

/-- The inner constant coefficient, as an additive functional. -/
def quantumLaurentInnerTrace : HahnSeries ℤ F →+ F where
  toFun f := f.coeff 0
  map_zero' := rfl
  map_add' _ _ := rfl

theorem quantumLaurentInnerTrace_invariant (c : Fˣ) (n : ℤ) (f : HahnSeries ℤ F) :
    quantumLaurentInnerTrace ((quantumLaurentScaleAut c ^ n) f) =
      quantumLaurentInnerTrace f := by
  change quantumLaurentInnerTrace ((quantumLaurentScaleHom c ^ n) f) = _
  rw [← map_zpow]
  change (quantumLaurentScaleSeries (c ^ n) f).coeff 0 = f.coeff 0
  simp

/-- A concrete quantum Laurent division ring at a nonzero parameter. -/
abbrev QuantumLaurentDivisionRing (c : Fˣ) :=
  skewLaurentOperatorRing (quantumLaurentScaleAut c)

/-- The actual iterated coefficient trace, with no trace-existence premise. -/
def quantumLaurentTrace (c : Fˣ) : QuantumLaurentDivisionRing c →+ F :=
  skewLaurentCoefficientTrace (quantumLaurentScaleAut c) quantumLaurentInnerTrace

theorem quantumLaurentTrace_cyclic (c : Fˣ) (f g : QuantumLaurentDivisionRing c) :
    quantumLaurentTrace c (f * g) = quantumLaurentTrace c (g * f) :=
  skewLaurentCoefficientTrace_cyclic _ _ (quantumLaurentInnerTrace_invariant c) f g

@[simp] theorem quantumLaurentTrace_one (c : Fˣ) : quantumLaurentTrace c 1 = 1 := by
  rw [quantumLaurentTrace, skewLaurentCoefficientTrace_one]
  change (1 : HahnSeries ℤ F).coeff 0 = 1
  simp

/-- Quantum Laurent words in their explicit ordered normal form. -/
def quantumLaurentWord (c : Fˣ) (a b : ℤ) : QuantumLaurentDivisionRing c :=
  skewLaurentMonomial (quantumLaurentScaleAut c) a (HahnSeries.single b 1)

theorem quantumLaurentTrace_word (c : Fˣ) (a b : ℤ) :
    quantumLaurentTrace c (quantumLaurentWord c a b) =
      if a = 0 ∧ b = 0 then 1 else 0 := by
  change ((HahnSeries.single a
    (skewLaurentCoefficient (quantumLaurentScaleAut c) a (HahnSeries.single b 1))).coeff
      0 1).coeff 0 = _
  by_cases ha : a = 0
  · subst a
    simp [HahnSeries.coeff_single, eq_comm]
  · simp [ha, eq_comm]

end Quantum

end
end GaloisForLFunctions.HTGeometry
