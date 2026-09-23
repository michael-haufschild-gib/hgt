import GaloisForLFunctions.HTGeometry.MovingCanonicalProduct
import GaloisForLFunctions.HTGeometry.NormalizedProjectiveCauchyDensityControl

open Polynomial

namespace GaloisForLFunctions.HTGeometry

open Complex
open scoped ComplexConjugate

noncomputable section

/-- One real inverse-square coordinate adjoined to a finite Cauchy-jet column. -/
def inverseSquareCauchyJetColumn
    {ι κ : Type*} (x : ι → ℂ) (n : ι → ℕ) (t : κ → ℝ) (a : κ) :
    ℝ × ((Σ i, Fin (n i)) → ℂ) :=
  (1 / (t a) ^ (2 : ℕ), cauchyJetColumn x n (fun b => (t b : ℂ)) a)

/-- Finite real combinations controlling one inverse-square coordinate and a Cauchy packet. -/
def inverseSquareCauchyJetRealLinearCombination
    {ι κ : Type*} (x : ι → ℂ) (n : ι → ℕ) (t : κ → ℝ) :
    (κ →₀ ℝ) →ₗ[ℝ] (ℝ × ((Σ i, Fin (n i)) → ℂ)) :=
  Finsupp.linearCombination ℝ (inverseSquareCauchyJetColumn x n t)

/-- Dual reduction: real inverse-square/Cauchy controllability follows from rigidity of its explicit
real rational annihilator. -/
theorem inverseSquareCauchyJetRealLinearCombination_surjective_of_real_rigidity
    {ι κ : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (n : ι → ℕ) (t : κ → ℝ)
    (hrigid : ∀ (r : ℝ) (c : (i : ι) → Fin (n i) → ℂ),
      (∀ a, r * (1 / (t a) ^ (2 : ℕ)) +
        (∑ i, ∑ j : Fin (n i),
          c i j * (((t a : ℂ) - x i)⁻¹) ^ (j.1 + 1)).re = 0) →
      r = 0 ∧ ∀ i j, c i j = 0) :
    Function.Surjective
      (inverseSquareCauchyJetRealLinearCombination x n t) := by
  rw [← LinearMap.dualMap_injective_iff]
  intro φ ψ hφψ
  let r : ℝ := φ (1, 0) - ψ (1, 0)
  let A : (i : ι) → Fin (n i) → ℝ := fun i j =>
    φ (0, Pi.single ⟨i, j⟩ 1) - ψ (0, Pi.single ⟨i, j⟩ 1)
  let B : (i : ι) → Fin (n i) → ℝ := fun i j =>
    φ (0, Pi.single ⟨i, j⟩ Complex.I) -
      ψ (0, Pi.single ⟨i, j⟩ Complex.I)
  let c : (i : ι) → Fin (n i) → ℂ := fun i j =>
    (A i j : ℂ) - Complex.I * (B i j : ℂ)
  have hreal : ∀ a, r * (1 / (t a) ^ (2 : ℕ)) +
      (∑ i, ∑ j : Fin (n i),
        c i j * (((t a : ℂ) - x i)⁻¹) ^ (j.1 + 1)).re = 0 := by
    intro a
    have ha := LinearMap.congr_fun hφψ (Finsupp.single a 1)
    change φ ((inverseSquareCauchyJetRealLinearCombination x n t)
        (Finsupp.single a 1)) =
      ψ ((inverseSquareCauchyJetRealLinearCombination x n t)
        (Finsupp.single a 1)) at ha
    have hcol : (inverseSquareCauchyJetRealLinearCombination x n t)
        (Finsupp.single a 1) = inverseSquareCauchyJetColumn x n t a := by
      simp [inverseSquareCauchyJetRealLinearCombination]
    rw [hcol] at ha
    let v := cauchyJetColumn x n (fun b => (t b : ℂ)) a
    have hexpand : inverseSquareCauchyJetColumn x n t a =
        (1 / (t a) ^ (2 : ℕ)) • (1, 0) +
          (∑ s, (v s).re • (0, Pi.single s (1 : ℂ))) +
            ∑ s, (v s).im • (0, Pi.single s Complex.I) := by
      apply Prod.ext
      · simp only [inverseSquareCauchyJetColumn, Prod.fst_add, Prod.fst_sum,
          Prod.smul_fst]
        simp
      · funext s
        simp only [inverseSquareCauchyJetColumn, Prod.snd_add, Prod.snd_sum,
          Prod.smul_snd]
        simp [v, Pi.single_apply, Complex.re_add_im]
    change φ (inverseSquareCauchyJetColumn x n t a) =
      ψ (inverseSquareCauchyJetColumn x n t a) at ha
    rw [hexpand] at ha
    simp only [map_sum, map_add, map_smul] at ha
    have ha0 : r * (1 / (t a) ^ (2 : ℕ)) +
        ∑ s, ((v s).re * A s.1 s.2 + (v s).im * B s.1 s.2) = 0 := by
      simp only [r, A, B]
      rw [Finset.sum_add_distrib]
      calc
        _ = ((1 / (t a) ^ (2 : ℕ)) * φ (1, 0) +
              ((∑ s, (v s).re * φ (0, Pi.single s 1)) +
                ∑ s, (v s).im * φ (0, Pi.single s Complex.I))) -
            ((1 / (t a) ^ (2 : ℕ)) * ψ (1, 0) +
              ((∑ s, (v s).re * ψ (0, Pi.single s 1)) +
                ∑ s, (v s).im * ψ (0, Pi.single s Complex.I))) := by
          simp only [mul_sub, Finset.sum_sub_distrib]
          ring
        _ = 0 := sub_eq_zero.mpr (by simpa [add_assoc] using ha)
    rw [Complex.re_sum]
    simp_rw [Complex.re_sum]
    rw [← Fintype.sum_sigma (fun s : (Σ i, Fin (n i)) =>
      (c s.1 s.2 * (((t a : ℂ) - x s.1)⁻¹) ^ (s.2.1 + 1)).re)]
    rw [← ha0]
    congr 1
    apply Finset.sum_congr rfl
    intro s hs
    have hcre : (c s.1 s.2).re = A s.1 s.2 := by
      simp [c, A, B, Complex.mul_re]
    have hcim : (c s.1 s.2).im = -B s.1 s.2 := by
      simp [c, A, B, Complex.mul_im]
    rw [Complex.mul_re, hcre, hcim]
    simp only [v, cauchyJetColumn]
    ring
  obtain ⟨hr, hc⟩ := hrigid r c hreal
  apply LinearMap.ext
  intro p
  rcases p with ⟨u, f⟩
  have hexpand : (u, f) = u • (1, 0) +
      (∑ s, (f s).re • (0, Pi.single s (1 : ℂ))) +
        ∑ s, (f s).im • (0, Pi.single s Complex.I) := by
    apply Prod.ext
    · simp only [Prod.fst_add, Prod.fst_sum, Prod.smul_fst]
      simp
    · funext s
      simp only [Prod.snd_add, Prod.snd_sum, Prod.smul_snd]
      simp [Pi.single_apply, Complex.re_add_im]
  have hAeq (s : Σ i, Fin (n i)) :
      φ (0, Pi.single s (1 : ℂ)) = ψ (0, Pi.single s (1 : ℂ)) := by
    have hcre := congrArg Complex.re (hc s.1 s.2)
    simp only [c, A, B, Complex.sub_re, Complex.ofReal_re, Complex.mul_re,
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul,
      sub_zero, Complex.zero_re] at hcre
    exact sub_eq_zero.mp hcre
  have hBeq (s : Σ i, Fin (n i)) :
      φ (0, Pi.single s Complex.I) = ψ (0, Pi.single s Complex.I) := by
    have hcim := congrArg Complex.im (hc s.1 s.2)
    simp only [c, A, B, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul,
      zero_add, Complex.zero_im] at hcim
    apply sub_eq_zero.mp
    linarith
  rw [hexpand]
  simp only [map_sum, map_add, map_smul]
  simp_rw [sub_eq_zero.mp hr, hAeq, hBeq]


/-- Joint controllability of a real inverse-square coordinate and every finite complex Cauchy
packet.  The extra coordinate is the real pole at zero needed by location differentiation. -/
theorem inverseSquareCauchyJetRealLinearCombination_surjective
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Infinite κ]
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (t : κ → ℝ) (ht : Function.Injective t)
    (ht0 : ∀ a, t a ≠ 0) :
    Function.Surjective
      (inverseSquareCauchyJetRealLinearCombination x n t) := by
  apply inverseSquareCauchyJetRealLinearCombination_surjective_of_real_rigidity
  intro r c hreal
  let ι₂ := ι ⊕ ι
  let x₂ : ι₂ → ℂ := Sum.elim x (fun i => star (x i))
  let n₂ : ι₂ → ℕ := Sum.elim n n
  let c₂ : (i : ι₂) → Fin (n₂ i) → ℂ := fun i =>
    match i with
    | Sum.inl q => fun j => c q j
    | Sum.inr q => fun j => star (c q j)
  have hx₂ : Function.Injective x₂ := by
    intro i j hij
    rcases i with i | i <;> rcases j with j | j
    · exact congrArg Sum.inl (hx hij)
    · exfalso
      have him := congrArg Complex.im hij
      simp [x₂] at him
      linarith [hupper i, hupper j]
    · exfalso
      have him := congrArg Complex.im hij
      simp [x₂] at him
      linarith [hupper i, hupper j]
    · apply congrArg Sum.inr
      apply hx
      have h := congrArg star hij
      simpa [x₂] using h
  let ι₃ := ι₂ ⊕ Fin 1
  let x₃ : ι₃ → ℂ := Sum.elim x₂ (fun _ => 0)
  let n₃ : ι₃ → ℕ := Sum.elim n₂ (fun _ => 2)
  let c₃ : (i : ι₃) → Fin (n₃ i) → ℂ := fun i =>
    match i with
    | Sum.inl q => fun j => c₂ q j
    | Sum.inr _ => fun j => if j.1 = 1 then ((2 * r : ℝ) : ℂ) else 0
  have hx₃ : Function.Injective x₃ := by
    intro i j hij
    rcases i with i | i <;> rcases j with j | j
    · exact congrArg Sum.inl (hx₂ hij)
    · exfalso
      have him := congrArg Complex.im hij
      rcases i with i | i <;> simp [x₃, x₂] at him <;>
        linarith [hupper i]
    · exfalso
      have him := congrArg Complex.im hij
      rcases j with j | j <;> simp [x₃, x₂] at him <;>
        linarith [hupper j]
    · apply congrArg Sum.inr
      exact Subsingleton.elim _ _
  have htC : Function.Injective (fun a => (t a : ℂ)) := fun a b hab =>
    ht (Complex.ofReal_injective hab)
  have hsep₃ : ∀ a i, (t a : ℂ) ≠ x₃ i := by
    intro a i h
    rcases i with i | i
    · rcases i with i | i
      · have him := congrArg Complex.im h
        simp [x₃, x₂] at him
        linarith [hupper i]
      · have him := congrArg Complex.im h
        simp [x₃, x₂] at him
        linarith [hupper i]
    · apply ht0 a
      exact Complex.ofReal_injective (by simpa [x₃] using h)
  have hzero₃ : ∀ a, ∑ i, ∑ j : Fin (n₃ i),
      c₃ i j * (((t a : ℂ) - x₃ i)⁻¹) ^ (j.1 + 1) = 0 := by
    intro a
    rw [Fintype.sum_sum_type]
    change
      (∑ q : ι₂, ∑ j : Fin (n₂ q),
          c₂ q j * (((t a : ℂ) - x₂ q)⁻¹) ^ (j.1 + 1)) +
        (∑ _q : Fin 1, ∑ j : Fin 2,
          (if j.1 = 1 then ((2 * r : ℝ) : ℂ) else 0) *
            (((t a : ℂ) - 0)⁻¹) ^ (j.1 + 1)) = 0
    rw [Fin.sum_univ_one]
    have hpole :
        (∑ j : Fin 2,
          (if j.1 = 1 then ((2 * r : ℝ) : ℂ) else 0) *
            (((t a : ℂ) - 0)⁻¹) ^ (j.1 + 1)) =
          ((2 * r : ℝ) : ℂ) * (((t a : ℂ) - 0)⁻¹) ^ (2 : ℕ) := by
      rw [Fin.sum_univ_two]
      simp
    rw [hpole]
    rw [Fintype.sum_sum_type]
    change
      ((∑ i, ∑ j : Fin (n i),
          c i j * (((t a : ℂ) - x i)⁻¹) ^ (j.1 + 1)) +
        (∑ i, ∑ j : Fin (n i),
          star (c i j) * (((t a : ℂ) - star (x i))⁻¹) ^ (j.1 + 1))) +
        ((2 * r : ℝ) : ℂ) * (((t a : ℂ) - 0)⁻¹) ^ (2 : ℕ) = 0
    let R : ℂ := ∑ i, ∑ j : Fin (n i),
      c i j * (((t a : ℂ) - x i)⁻¹) ^ (j.1 + 1)
    have hconj : (∑ i, ∑ j : Fin (n i),
        star (c i j) * (((t a : ℂ) - star (x i))⁻¹) ^ (j.1 + 1)) =
        star R := by
      simp [R]
    change (R + (∑ i, ∑ j : Fin (n i),
      star (c i j) * (((t a : ℂ) - star (x i))⁻¹) ^ (j.1 + 1))) +
        ((2 * r : ℝ) : ℂ) * (((t a : ℂ) - 0)⁻¹) ^ (2 : ℕ) = 0
    rw [hconj]
    have hqC : (((t a : ℂ) - 0)⁻¹) ^ (2 : ℕ) =
        ((1 / (t a) ^ (2 : ℕ) : ℝ) : ℂ) := by
      simp only [sub_zero, ← Complex.ofReal_inv, ← Complex.ofReal_pow]
      congr 1
      simp [one_div, inv_pow]
    rw [hqC]
    have hstarre : (star R).re = R.re := by simp
    have hstarim : (star R).im = -R.im := by simp
    apply Complex.ext
    · simp only [Complex.add_re]
      rw [hstarre]
      simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.zero_re, zero_mul, sub_zero]
      linarith [hreal a]
    · simp only [Complex.add_im]
      rw [hstarim]
      simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.zero_im, mul_zero, zero_mul, add_zero]
      ring
  have hc₃ := cauchyJet_coeff_eq_zero_of_infinite x₃ hx₃ n₃
    (fun a => (t a : ℂ)) htC hsep₃ c₃ hzero₃
  have hr : r = 0 := by
    have h := hc₃ (Sum.inr 0) (1 : Fin 2)
    simp [c₃] at h
    exact h
  have hc : ∀ i j, c i j = 0 := fun i j =>
    hc₃ (Sum.inl (Sum.inl i)) j
  exact ⟨hr, hc⟩

/-- Real-linear extraction of location-variation jets from one inverse-square coordinate and the
one-order-longer Cauchy packet. -/
def inverseSquareCauchyToLocationJet
    {ι : Type*} (n : ι → ℕ) :
    (ℝ × ((Σ i, Fin (n i + 1)) → ℂ)) →ₗ[ℝ]
      ((Σ i, Fin (n i)) → ℂ) where
  toFun p s :=
    ((if s.2.1 = 0 then p.1 else 0 : ℝ) : ℂ) -
      (Nat.factorial (s.2.1 + 1) : ℂ) *
        p.2 ⟨s.1, Fin.succ s.2⟩
  map_add' p q := by
    funext s
    by_cases hs : s.2.1 = 0
    · simp [hs, mul_add]
      abel
    · simp [hs, mul_add]
      abel
  map_smul' r p := by
    funext s
    by_cases hs : s.2.1 = 0
    · simp [hs, Complex.ofReal_mul]
      ring
    · simp [hs]
      ring

/-- The factorial-shift extraction loses no finite jet directions. -/
theorem inverseSquareCauchyToLocationJet_surjective
    {ι : Type*} (n : ι → ℕ) :
    Function.Surjective (inverseSquareCauchyToLocationJet n) := by
  intro y
  let f : (Σ i, Fin (n i + 1)) → ℂ := fun s =>
    Fin.cases 0
      (fun j => -y ⟨s.1, j⟩ / (Nat.factorial (j.1 + 1) : ℂ)) s.2
  refine ⟨(0, f), ?_⟩
  funext s
  have hfac : (Nat.factorial (s.2.1 + 1) : ℂ) ≠ 0 := by
    exact_mod_cast Nat.factorial_ne_zero (s.2.1 + 1)
  simp only [inverseSquareCauchyToLocationJet, LinearMap.coe_mk,
    AddHom.coe_mk]
  rw [show (if s.2.1 = 0 then (0 : ℝ) else 0) = 0 by simp]
  simp only [f, Fin.cases_succ, Complex.ofReal_zero, zero_sub]
  field_simp

/-- Exact finite location-variation jet map for the regularized pole terms
`(t - z)⁻¹ - t⁻¹`. -/
def movingPoleLocationJetRealLinearCombination
    {ι κ : Type*} (x : ι → ℂ) (n : ι → ℕ) (t : κ → ℝ) :
    (κ →₀ ℝ) →ₗ[ℝ] ((Σ i, Fin (n i)) → ℂ) :=
  (inverseSquareCauchyToLocationJet n).comp
    (inverseSquareCauchyJetRealLinearCombination x (fun i => n i + 1) t)

/-- A unit location variation has the exact regularized-pole derivative:
zero-th coordinate `t⁻² - (t-x)⁻²`, and higher coordinate
`-(j+1)! (t-x)⁻(j+2)`. -/
theorem movingPoleLocationJetRealLinearCombination_single_apply
    {ι κ : Type*} (x : ι → ℂ) (n : ι → ℕ) (t : κ → ℝ)
    (a : κ) (s : Σ i, Fin (n i)) :
    movingPoleLocationJetRealLinearCombination x n t
        (Finsupp.single a 1) s =
      ((if s.2.1 = 0 then 1 / (t a) ^ (2 : ℕ) else 0 : ℝ) : ℂ) -
        (Nat.factorial (s.2.1 + 1) : ℂ) *
          (((t a : ℂ) - x s.1)⁻¹) ^ (s.2.1 + 2) := by
  simp [movingPoleLocationJetRealLinearCombination,
    inverseSquareCauchyJetRealLinearCombination,
    inverseSquareCauchyJetColumn, inverseSquareCauchyToLocationJet,
    cauchyJetColumn]

/-- Arbitrary finite real pole-location variations realize every finite complex regularized-pole
jet packet at distinct upper-half-plane nodes. -/
theorem movingPoleLocationJetRealLinearCombination_surjective
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Infinite κ]
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (t : κ → ℝ) (ht : Function.Injective t)
    (ht0 : ∀ a, t a ≠ 0) :
    Function.Surjective
      (movingPoleLocationJetRealLinearCombination x n t) := by
  exact (inverseSquareCauchyToLocationJet_surjective n).comp
    (inverseSquareCauchyJetRealLinearCombination_surjective
      x hx hupper (fun i => n i + 1) t ht ht0)

/-- Location-variation jet map on the exact moving canonical divisor. -/
def movingCanonicalLocationJetRealLinearCombination
    {ι : Type*} (x : ι → ℂ) (n : ι → ℕ)
    (θ : BoundedRealSequence) :
    (ℕ →₀ ℝ) →ₗ[ℝ] ((Σ i, Fin (n i)) → ℂ) :=
  movingPoleLocationJetRealLinearCombination x n (movingCanonicalZero θ)

theorem movingCanonicalLocationJetRealLinearCombination_single_apply
    {ι : Type*} (x : ι → ℂ) (n : ι → ℕ)
    (θ : BoundedRealSequence) (a : ℕ) (s : Σ i, Fin (n i)) :
    movingCanonicalLocationJetRealLinearCombination x n θ
        (Finsupp.single a 1) s =
      ((if s.2.1 = 0 then 1 / (movingCanonicalZero θ a) ^ (2 : ℕ) else 0 : ℝ) : ℂ) -
        (Nat.factorial (s.2.1 + 1) : ℂ) *
          ((((movingCanonicalZero θ a : ℝ) : ℂ) - x s.1)⁻¹) ^
            (s.2.1 + 2) := by
  exact movingPoleLocationJetRealLinearCombination_single_apply
    x n (movingCanonicalZero θ) a s

/-- Exact canonical-divisor location variations span every finite complex jet packet. -/
theorem movingCanonicalLocationJetRealLinearCombination_surjective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (θ : BoundedRealSequence) :
    Function.Surjective
      (movingCanonicalLocationJetRealLinearCombination x n θ) := by
  exact movingPoleLocationJetRealLinearCombination_surjective
    x hx hupper n (movingCanonicalZero θ)
      (movingCanonicalZero_injective θ)
      (fun a => ne_of_gt (movingCanonicalZero_pos θ a))

/-- Coordinatewise multiplication by a prescribed speed. -/
def positiveSpeedFinsuppLinearMap (s : ℕ → ℝ) :
    (ℕ →₀ ℝ) →ₗ[ℝ] (ℕ →₀ ℝ) :=
  Finsupp.linearCombination ℝ (fun a => Finsupp.single a (s a))

@[simp]
theorem positiveSpeedFinsuppLinearMap_single (s : ℕ → ℝ) (a : ℕ) (r : ℝ) :
    positiveSpeedFinsuppLinearMap s (Finsupp.single a r) =
      Finsupp.single a (s a * r) := by
  ext b
  simp [positiveSpeedFinsuppLinearMap, mul_comm]

/-- Nonvanishing coordinate speeds make the diagonal parameter-to-location map onto. -/
theorem positiveSpeedFinsuppLinearMap_surjective {s : ℕ → ℝ} (hs : ∀ a, s a ≠ 0) :
    Function.Surjective (positiveSpeedFinsuppLinearMap s) := by
  intro y
  induction y using Finsupp.induction with
  | zero =>
      exact ⟨0, map_zero _⟩
  | @single_add a r y ha hr ih =>
      obtain ⟨p, hp⟩ := ih
      refine ⟨p + Finsupp.single a (r / s a), ?_⟩
      rw [map_add, hp, positiveSpeedFinsuppLinearMap_single]
      change y + Finsupp.single a (s a * (r / s a)) = Finsupp.single a r + y
      rw [mul_div_cancel₀ r (hs a)]
      exact add_comm _ _

/-- Coordinatewise multiplication by the exact positive speed of the moving canonical divisor. -/
def movingCanonicalSpeedFinsuppLinearMap
    (θ : BoundedRealSequence) :
    (ℕ →₀ ℝ) →ₗ[ℝ] (ℕ →₀ ℝ) :=
  positiveSpeedFinsuppLinearMap (fun a => canonicalZeroSpeed (θ a))

@[simp]
theorem movingCanonicalSpeedFinsuppLinearMap_single
    (θ : BoundedRealSequence) (a : ℕ) (r : ℝ) :
    movingCanonicalSpeedFinsuppLinearMap θ (Finsupp.single a r) =
      Finsupp.single a (canonicalZeroSpeed (θ a) * r) :=
  positiveSpeedFinsuppLinearMap_single _ a r

/-- Positive coordinate speeds make the diagonal parameter-to-location map onto. -/
theorem movingCanonicalSpeedFinsuppLinearMap_surjective
    (θ : BoundedRealSequence) :
    Function.Surjective (movingCanonicalSpeedFinsuppLinearMap θ) :=
  positiveSpeedFinsuppLinearMap_surjective
    (fun a => ne_of_gt (canonicalZeroSpeed_pos (θ a)))

/-- Exact first-order jet map for variations of the bounded canonical parameter `θ`. -/
def movingCanonicalParameterJetRealLinearCombination
    {ι : Type*} (x : ι → ℂ) (n : ι → ℕ)
    (θ : BoundedRealSequence) :
    (ℕ →₀ ℝ) →ₗ[ℝ] ((Σ i, Fin (n i)) → ℂ) :=
  (movingCanonicalLocationJetRealLinearCombination x n θ).comp
    (movingCanonicalSpeedFinsuppLinearMap θ)

/-- A unit parameter variation is the location-variation column multiplied by the exact derivative
`(1/4) cosh(θₐ)⁻²`. -/
theorem movingCanonicalParameterJetRealLinearCombination_single
    {ι : Type*} (x : ι → ℂ) (n : ι → ℕ)
    (θ : BoundedRealSequence) (a : ℕ) :
    movingCanonicalParameterJetRealLinearCombination x n θ
        (Finsupp.single a 1) =
      canonicalZeroSpeed (θ a) •
        movingCanonicalLocationJetRealLinearCombination x n θ
          (Finsupp.single a 1) := by
  rw [movingCanonicalParameterJetRealLinearCombination,
    LinearMap.comp_apply, movingCanonicalSpeedFinsuppLinearMap_single]
  have hsingle :
      Finsupp.single a (canonicalZeroSpeed (θ a) * 1) =
        canonicalZeroSpeed (θ a) • Finsupp.single a (1 : ℝ) := by
    ext b
    simp [mul_comm]
  rw [hsingle, map_smul]

/-- The actual bounded-sequence parameter derivative spans every finite complex jet packet. -/
theorem movingCanonicalParameterJetRealLinearCombination_surjective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (θ : BoundedRealSequence) :
    Function.Surjective
      (movingCanonicalParameterJetRealLinearCombination x n θ) :=
  (movingCanonicalLocationJetRealLinearCombination_surjective
    x hx hupper n θ).comp
      (movingCanonicalSpeedFinsuppLinearMap_surjective θ)

end

end GaloisForLFunctions.HTGeometry
