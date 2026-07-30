import GaloisForLFunctions.HTGeometry.ProjectiveCauchyDensityControl
import GaloisForLFunctions.HTGeometry.ProjectiveFiniteConstraintCarrierAperture
import GaloisForLFunctions.HTGeometry.ProjectiveNevanlinnaGenericity

/-!
# Normalized projective Cauchy and Nevanlinna density control

The constant density functional is adjoined to a finite Cauchy-jet packet.  Partial-fraction
uniqueness then says that mass together with every finite jet packet is exactly controllable on
any infinite real support.  This is the missing normalized tangent in the positive carrier chart:
target jets remain onto after both total mass and a disjoint frozen jet packet are fixed exactly.
-/

open Polynomial

namespace GaloisForLFunctions.HTGeometry

open Complex MeasureTheory
open scoped ENNReal OnePoint

noncomputable section

/-- A constant plus a finite confluent Cauchy packet cannot vanish on an infinite separated set
unless both the constant and every principal-part coefficient vanish. -/
theorem cauchyJet_constant_coeff_eq_zero_of_infinite
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Infinite κ]
    (x : ι → ℂ) (hx : Function.Injective x) (n : ι → ℕ)
    (t : κ → ℂ) (ht : Function.Injective t) (hsep : ∀ a i, t a ≠ x i)
    (c0 : ℂ) (c : (i : ι) → Fin (n i) → ℂ)
    (hzero : ∀ a, c0 + ∑ i, ∑ j : Fin (n i),
      c i j * ((t a - x i)⁻¹) ^ (j.1 + 1) = 0) :
    c0 = 0 ∧ ∀ i j, c i j = 0 := by
  let Q : ℂ[X] := C c0 * ∏ i, (X - C (x i)) ^ n i +
    clearedCauchyJetPolynomial x n c
  have hroot : Set.range t ⊆ {z | Q.IsRoot z} := by
    rintro z ⟨a, rfl⟩
    dsimp [Polynomial.IsRoot, Q]
    rw [eval_add, eval_mul, eval_C, eval_prod,
      eval_clearedCauchyJetPolynomial_eq_mul_sum x n c (t a) (hsep a)]
    simp only [eval_pow, eval_sub, eval_X]
    simp only [eval_C]
    calc
      c0 * ∏ i, (t a - x i) ^ n i +
          (∏ i, (t a - x i) ^ n i) *
            (∑ i, ∑ j : Fin (n i), c i j * ((t a - x i)⁻¹) ^ (j.1 + 1)) =
        (∏ i, (t a - x i) ^ n i) *
          (c0 + ∑ i, ∑ j : Fin (n i),
            c i j * ((t a - x i)⁻¹) ^ (j.1 + 1)) := by ring
      _ = 0 := by rw [hzero a, mul_zero]
  have hQ : Q = 0 := Polynomial.eq_zero_of_infinite_isRoot Q
    ((Set.infinite_range_of_injective ht).mono hroot)
  let g : ι → ℂ[X] := fun i => X - C (x i)
  let r₁ : (i : ι) → Fin (n i) → ℂ[X] := fun i j => C (c i j.rev)
  let r₂ : (i : ι) → Fin (n i) → ℂ[X] := fun _ _ => 0
  have hg : ∀ i ∈ (Finset.univ : Finset ι), (g i).Monic := by
    intro i hi
    exact monic_X_sub_C (x i)
  have hcop : Set.Pairwise (↑(Finset.univ : Finset ι)) fun i j =>
      IsCoprime (g i) (g j) := by
    intro i hi j hj hij
    exact pairwise_coprime_X_sub_C hx hij
  have hr₁ : ∀ i ∈ (Finset.univ : Finset ι), ∀ j,
      (r₁ i j).degree < (g i).degree := by
    intro i hi j
    by_cases hc : c i j.rev = 0 <;> simp [r₁, g, hc]
  have hr₂ : ∀ i ∈ (Finset.univ : Finset ι), ∀ j,
      (r₂ i j).degree < (g i).degree := by
    intro i hi j
    simp [r₂, g]
  have hf : C c0 * (∏ i ∈ (Finset.univ : Finset ι), g i ^ n i) +
        ∑ i ∈ (Finset.univ : Finset ι), ∑ j,
          r₁ i j * g i ^ j.1 * ∏ k ∈ Finset.univ.erase i, g k ^ n k =
      (0 : ℂ[X]) * (∏ i ∈ (Finset.univ : Finset ι), g i ^ n i) +
        ∑ i ∈ (Finset.univ : Finset ι), ∑ j,
          r₂ i j * g i ^ j.1 * ∏ k ∈ Finset.univ.erase i, g k ^ n k := by
    simpa [Q, clearedCauchyJetPolynomial, g, r₁, r₂] using hQ
  have hu := Polynomial.quo_mul_prod_pow_add_sum_rem_mul_prod_pow_unique
    hg hcop hr₁ hr₂ hf
  constructor
  · have hquot := congrArg (fun P : ℂ[X] => P.coeff 0) hu.1
    simpa using hquot
  · intro i j
    have hij := congrFun (hu.2 i (Finset.mem_univ i)) j.rev
    simpa [r₁, r₂] using congrArg (fun P : ℂ[X] => P.coeff 0) hij

/-- One real mass coordinate adjoined to a finite Cauchy-jet column. -/
def normalizedCauchyJetColumn
    {ι κ : Type*} (x : ι → ℂ) (n : ι → ℕ) (t : κ → ℝ) (a : κ) :
    ℝ × ((Σ i, Fin (n i)) → ℂ) :=
  (1, cauchyJetColumn x n (fun b => (t b : ℂ)) a)

/-- Finite real mass combinations controlling normalization and a Cauchy-jet packet jointly. -/
def normalizedCauchyJetRealLinearCombination
    {ι κ : Type*} (x : ι → ℂ) (n : ι → ℕ) (t : κ → ℝ) :
    (κ →₀ ℝ) →ₗ[ℝ] (ℝ × ((Σ i, Fin (n i)) → ℂ)) :=
  Finsupp.linearCombination ℝ (normalizedCauchyJetColumn x n t)

/-- **Normalized real Cauchy controllability.** Finitely supported real masses on any infinite
injective real support realize an arbitrary total mass and arbitrary finite upper-half-plane jet
packet simultaneously. -/
theorem normalizedCauchyJetRealLinearCombination_surjective
    {ι κ : Type*} [Fintype ι] [DecidableEq ι] [Infinite κ]
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ) (t : κ → ℝ) (ht : Function.Injective t) :
    Function.Surjective (normalizedCauchyJetRealLinearCombination x n t) := by
  rw [← LinearMap.dualMap_injective_iff]
  intro φ ψ hφψ
  let r : ℝ := φ (1, 0) - ψ (1, 0)
  let A : (i : ι) → Fin (n i) → ℝ := fun i j =>
    φ (0, Pi.single ⟨i, j⟩ 1) - ψ (0, Pi.single ⟨i, j⟩ 1)
  let B : (i : ι) → Fin (n i) → ℝ := fun i j =>
    φ (0, Pi.single ⟨i, j⟩ Complex.I) - ψ (0, Pi.single ⟨i, j⟩ Complex.I)
  let c : (i : ι) → Fin (n i) → ℂ := fun i j =>
    (A i j : ℂ) - Complex.I * (B i j : ℂ)
  have hreal : ∀ a, r + (∑ i, ∑ j : Fin (n i),
      c i j * (((t a : ℂ) - x i)⁻¹) ^ (j.1 + 1)).re = 0 := by
    intro a
    have ha := LinearMap.congr_fun hφψ (Finsupp.single a 1)
    change φ ((normalizedCauchyJetRealLinearCombination x n t)
        (Finsupp.single a 1)) =
      ψ ((normalizedCauchyJetRealLinearCombination x n t)
        (Finsupp.single a 1)) at ha
    have hcol : (normalizedCauchyJetRealLinearCombination x n t)
        (Finsupp.single a 1) = normalizedCauchyJetColumn x n t a := by
      simp [normalizedCauchyJetRealLinearCombination]
    rw [hcol] at ha
    let v := cauchyJetColumn x n (fun b => (t b : ℂ)) a
    have hexpand : (normalizedCauchyJetColumn x n t a) =
        (1, 0) + (∑ s, (v s).re • (0, Pi.single s (1 : ℂ))) +
          ∑ s, (v s).im • (0, Pi.single s Complex.I) := by
      apply Prod.ext
      · simp only [normalizedCauchyJetColumn, Prod.fst_add, Prod.fst_sum,
          Prod.smul_fst]
        simp
      · funext s
        simp only [normalizedCauchyJetColumn, Prod.snd_add, Prod.snd_sum,
          Prod.smul_snd]
        simp [v, Pi.single_apply, Complex.re_add_im]
    change φ (normalizedCauchyJetColumn x n t a) =
      ψ (normalizedCauchyJetColumn x n t a) at ha
    rw [hexpand] at ha
    simp only [map_sum, map_add, map_smul] at ha
    have ha0 : r + ∑ s, ((v s).re * A s.1 s.2 + (v s).im * B s.1 s.2) = 0 := by
      simp only [r, A, B]
      rw [Finset.sum_add_distrib]
      calc
        _ = (φ (1, 0) +
              ((∑ s, (v s).re * φ (0, Pi.single s 1)) +
                ∑ s, (v s).im * φ (0, Pi.single s Complex.I))) -
            (ψ (1, 0) +
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
  have htC : Function.Injective (fun a => (t a : ℂ)) := fun a b hab =>
    ht (Complex.ofReal_injective hab)
  have hsep₂ : ∀ a i, (t a : ℂ) ≠ x₂ i := by
    intro a i h
    rcases i with i | i
    · have him := congrArg Complex.im h
      simp [x₂] at him
      linarith [hupper i]
    · have him := congrArg Complex.im h
      simp [x₂] at him
      linarith [hupper i]
  have hzero₂ : ∀ a, ((2 * r : ℝ) : ℂ) + ∑ i, ∑ j : Fin (n₂ i),
      c₂ i j * (((t a : ℂ) - x₂ i)⁻¹) ^ (j.1 + 1) = 0 := by
    intro a
    rw [Fintype.sum_sum_type]
    simp only [c₂, n₂, x₂, Sum.elim_inl, Sum.elim_inr]
    let R : ℂ := ∑ i, ∑ j : Fin (n i),
      c i j * (((t a : ℂ) - x i)⁻¹) ^ (j.1 + 1)
    have hconj : (∑ i, ∑ j : Fin (n i),
        star (c i j) * (((t a : ℂ) - star (x i))⁻¹) ^ (j.1 + 1)) = star R := by
      simp [R]
    change ((2 * r : ℝ) : ℂ) + (R + (∑ i, ∑ j : Fin (n i),
      star (c i j) * (((t a : ℂ) - star (x i))⁻¹) ^ (j.1 + 1))) = 0
    rw [hconj]
    apply Complex.ext
    · simp only [Complex.add_re, Complex.ofReal_re, Complex.zero_re]
      have hstarre : (star R).re = R.re := by simp
      rw [hstarre]
      linarith [hreal a]
    · simp
  have hc₂ := cauchyJet_constant_coeff_eq_zero_of_infinite x₂ hx₂ n₂
    (fun a => (t a : ℂ)) htC hsep₂ (((2 * r : ℝ) : ℂ)) c₂ hzero₂
  have hr : r = 0 := by
    have hre := congrArg Complex.re hc₂.1
    simpa using hre
  have hc : ∀ i j, c i j = 0 := fun i j => hc₂.2 (Sum.inl i) j
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
      Complex.I_re, Complex.I_im, Complex.ofReal_im, zero_mul, one_mul, sub_zero,
      Complex.zero_re] at hcre
    exact sub_eq_zero.mp hcre
  have hBeq (s : Σ i, Fin (n i)) :
      φ (0, Pi.single s Complex.I) = ψ (0, Pi.single s Complex.I) := by
    have hcim := congrArg Complex.im (hc s.1 s.2)
    simp only [c, A, B, Complex.sub_im, Complex.ofReal_im, Complex.mul_im,
      Complex.I_re, Complex.I_im, Complex.ofReal_re, zero_mul, one_mul, zero_add,
      Complex.zero_im] at hcim
    apply sub_eq_zero.mp
    linarith
  rw [hexpand]
  simp only [map_sum, map_add, map_smul]
  simp_rw [sub_eq_zero.mp hr, hAeq, hBeq]

/-- The mass functional and one projective Cauchy-jet packet as a single continuous control. -/
def normalizedProjectiveCauchyJetLinftyContinuousControl
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (n : ι → ℕ)
    (mu : Measure (OnePoint ℝ)) [IsProbabilityMeasure mu]
    (hupper : ∀ i, 0 < (x i).im) :
    Lp ℝ (⊤ : ENNReal) mu →L[ℝ] (ℝ × ((Σ i, Fin (n i)) → ℂ)) :=
  (linftyIntegralCLM mu).prod
    (linftyBochnerControl mu (projectiveCauchyJetColumn x n)
      (memLp_projectiveCauchyJetColumn x (fun i => (hupper i).ne') n mu))

/-- On every density, the normalized projective control is literally total mass paired with the
ordinary projective Cauchy-jet control. -/
@[simp] theorem normalizedProjectiveCauchyJetLinftyContinuousControl_apply
    {ι : Type*} [Fintype ι]
    (x : ι → ℂ) (n : ι → ℕ)
    (mu : Measure (OnePoint ℝ)) [IsProbabilityMeasure mu]
    (hupper : ∀ i, 0 < (x i).im)
    (w : Lp ℝ (⊤ : ENNReal) mu) :
    normalizedProjectiveCauchyJetLinftyContinuousControl x n mu hupper w =
      (linftyIntegralCLM mu w,
        linftyBochnerControl mu (projectiveCauchyJetColumn x n)
          (memLp_projectiveCauchyJetColumn x (fun i => (hupper i).ne') n mu) w) := by
  rfl

/-- Infinite projective support makes mass plus every finite upper-half-plane Cauchy packet
jointly controllable by genuine bounded densities. -/
theorem normalizedProjectiveCauchyJetLinftyContinuousControl_surjective
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (x : ι → ℂ) (hx : Function.Injective x) (hupper : ∀ i, 0 < (x i).im)
    (n : ι → ℕ)
    (mu : Measure (OnePoint ℝ)) [IsProbabilityMeasure mu]
    (hmu : mu.support.Infinite) :
    Function.Surjective
      (normalizedProjectiveCauchyJetLinftyContinuousControl x n mu hupper) := by
  let K : OnePoint ℝ → (ℝ × ((Σ i, Fin (n i)) → ℂ)) := fun t =>
    (1, projectiveCauchyJetColumn x n t)
  have hKcont : Continuous K :=
    continuous_const.prodMk
      (continuous_projectiveCauchyJetColumn x (fun i => (hupper i).ne') n)
  have hKlp : MemLp K 1 mu :=
    hKcont.memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  letI : Infinite (finiteProjectiveSupport mu) :=
    infinite_finiteProjectiveSupport mu hmu
  have hfinite : Function.Surjective
      (Finsupp.linearCombination ℝ
        (fun t : finiteProjectiveSupport mu => K (t.1 : OnePoint ℝ))) := by
    simpa [K, normalizedCauchyJetRealLinearCombination,
      normalizedCauchyJetColumn, projectiveCauchyJetColumn,
      projectiveCauchyPower, cauchyJetColumn] using!
      (normalizedCauchyJetRealLinearCombination_surjective
        x hx hupper n (fun t : finiteProjectiveSupport mu => t.1)
          (fun _ _ h => Subtype.ext h))
  have hbochner : Function.Surjective (linftyBochnerControl mu K hKlp) :=
    linftyBochnerControl_surjective_of_support_finsupp mu K hKlp hKcont
      (fun t : finiteProjectiveSupport mu => (t.1 : OnePoint ℝ))
      (fun t => t.2) hfinite
  have heq : linftyBochnerControl mu K hKlp =
      normalizedProjectiveCauchyJetLinftyContinuousControl x n mu hupper := by
    apply ContinuousLinearMap.ext
    intro w
    have hpair : Integrable (fun y => (w y) • K y) mu := by
      exact (ContinuousLinearMap.lsmul ℝ ℝ :
        ℝ →L[ℝ] (ℝ × ((Σ i, Fin (n i)) → ℂ)) →L[ℝ]
          (ℝ × ((Σ i, Fin (n i)) → ℂ))).integrable_of_bilin_of_bdd_left
            ‖w‖ (Lp.memLp w).1 (linfty_ae_abs_le_norm mu w)
            (hKlp.integrable (by norm_num))
    apply Prod.ext
    · rw [normalizedProjectiveCauchyJetLinftyContinuousControl_apply,
        linftyBochnerControl_apply, linftyIntegralCLM_apply]
      let fstCLM : (ℝ × ((Σ i, Fin (n i)) → ℂ)) →L[ℝ] ℝ :=
        ContinuousLinearMap.fst ℝ ℝ ((Σ i, Fin (n i)) → ℂ)
      change fstCLM (∫ y, (w y) • K y ∂mu) = ∫ y, w y ∂mu
      rw [← fstCLM.integral_comp_comm hpair]
      apply integral_congr_ae
      filter_upwards [] with y
      simp [fstCLM, K]
    · rw [normalizedProjectiveCauchyJetLinftyContinuousControl_apply,
        linftyBochnerControl_apply, linftyBochnerControl_apply]
      let sndCLM : (ℝ × ((Σ i, Fin (n i)) → ℂ)) →L[ℝ]
          ((Σ i, Fin (n i)) → ℂ) :=
        ContinuousLinearMap.snd ℝ ℝ ((Σ i, Fin (n i)) → ℂ)
      change sndCLM (∫ y, (w y) • K y ∂mu) =
        ∫ y, (w y) • projectiveCauchyJetColumn x n y ∂mu
      rw [← sndCLM.integral_comp_comm hpair]
      apply integral_congr_ae
      filter_upwards [] with y
      simp [sndCLM, K]
  rw [← heq]
  exact hbochner

/-- Target projective Cauchy jets remain onto after both total mass and a disjoint frozen packet
are fixed exactly. -/
theorem constrainedNormalizedProjectiveCauchyJet_linftyControl_surjective
    {ιf ιt : Type*} [Fintype ιf] [DecidableEq ιf]
    [Fintype ιt] [DecidableEq ιt]
    (xf : ιf → ℂ) (hxf : Function.Injective xf)
    (xt : ιt → ℂ) (hxt : Function.Injective xt)
    (hcross : ∀ i j, xf i ≠ xt j)
    (hupperf : ∀ i, 0 < (xf i).im) (huppert : ∀ i, 0 < (xt i).im)
    (nf : ιf → ℕ) (nt : ιt → ℕ)
    (mu : Measure (OnePoint ℝ)) [IsProbabilityMeasure mu]
    (hmu : mu.support.Infinite) :
    let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
      xf nf mu hupperf
    let target := linftyBochnerControl mu (projectiveCauchyJetColumn xt nt)
      (memLp_projectiveCauchyJetColumn xt (fun i => (huppert i).ne') nt mu)
    Function.Surjective (target.toLinearMap.domRestrict
      (LinearMap.ker frozen.toLinearMap)) := by
  dsimp only
  let x : ιf ⊕ ιt → ℂ := Sum.elim xf xt
  let n : ιf ⊕ ιt → ℕ := Sum.elim nf nt
  have hx : Function.Injective x := by
    intro a b hab
    rcases a with i | i <;> rcases b with j | j
    · exact congrArg Sum.inl (hxf hab)
    · exact False.elim (hcross i j hab)
    · exact False.elim (hcross j i hab.symm)
    · exact congrArg Sum.inr (hxt hab)
  have hupper : ∀ i, 0 < (x i).im := by
    intro i
    rcases i with i | i
    · exact hupperf i
    · exact huppert i
  have hsurj := normalizedProjectiveCauchyJetLinftyContinuousControl_surjective
    x hx hupper n mu hmu
  intro y
  let z : ℝ × ((Σ i, Fin (n i)) → ℂ) :=
    (0, fun q => match q with
      | ⟨Sum.inl _, _⟩ => 0
      | ⟨Sum.inr i, j⟩ => y ⟨i, j⟩)
  obtain ⟨w, hw⟩ := hsurj z
  have hmass : linftyIntegralCLM mu w = 0 := by
    exact congrArg Prod.fst hw
  have hwf : linftyBochnerControl mu (projectiveCauchyJetColumn xf nf)
      (memLp_projectiveCauchyJetColumn xf (fun i => (hupperf i).ne') nf mu) w = 0 := by
    funext q
    have hq := congrFun (congrArg Prod.snd hw) ⟨Sum.inl q.1, q.2⟩
    rw [normalizedProjectiveCauchyJetLinftyContinuousControl_apply] at hq
    change (linftyBochnerControl mu (projectiveCauchyJetColumn x n)
      (memLp_projectiveCauchyJetColumn x (fun i => (hupper i).ne') n mu) w)
        ⟨Sum.inl q.1, q.2⟩ = z.2 ⟨Sum.inl q.1, q.2⟩ at hq
    rw [linftyBochnerControl_apply_pi] at hq
    rw [linftyBochnerControl_apply_pi]
    simpa [x, n, z, projectiveCauchyJetColumn] using hq
  have hwker : (normalizedProjectiveCauchyJetLinftyContinuousControl
      xf nf mu hupperf).toLinearMap w = 0 := by
    apply Prod.ext
    · simpa using hmass
    · simpa using hwf
  refine ⟨⟨w, hwker⟩, ?_⟩
  funext q
  have hq := congrFun (congrArg Prod.snd hw) ⟨Sum.inr q.1, q.2⟩
  rw [normalizedProjectiveCauchyJetLinftyContinuousControl_apply] at hq
  change (linftyBochnerControl mu (projectiveCauchyJetColumn x n)
    (memLp_projectiveCauchyJetColumn x (fun i => (hupper i).ne') n mu) w)
      ⟨Sum.inr q.1, q.2⟩ = z.2 ⟨Sum.inr q.1, q.2⟩ at hq
  change linftyBochnerControl mu (projectiveCauchyJetColumn xt nt)
    (memLp_projectiveCauchyJetColumn xt (fun i => (huppert i).ne') nt mu) w q = y q
  rw [linftyBochnerControl_apply_pi]
  rw [linftyBochnerControl_apply_pi] at hq
  simpa [x, n, z, projectiveCauchyJetColumn] using hq

/-- **Mixed constrained controllability.**  A disjoint genuine Nevanlinna target packet remains
onto when the exact frozen constraints are imposed in projective Cauchy coordinates.  In
particular, no noncriticality or nonvanishing-amplitude hypothesis is needed at the frozen
points; those hypotheses occur only at the movable target nodes. -/
theorem constrainedNormalizedProjectiveCauchyFrozenNevanlinnaTarget_linftyControl_surjective
    {ιf ιt : Type*} [Fintype ιf] [DecidableEq ιf]
    [Fintype ιt] [DecidableEq ιt]
    (a q : ℂ → ℂ)
    (xf : ιf → ℂ) (hxf_inj : Function.Injective xf)
    (zt : ιt → ℂ) (hqt_inj : Function.Injective (fun i => q (zt i)))
    (hcross : ∀ i j, xf i ≠ q (zt j))
    (hupperf : ∀ i, 0 < (xf i).im) (huppert : ∀ i, 0 < (q (zt i)).im)
    (nf : ιf → ℕ) (nt : ιt → ℕ)
    (hat : ∀ i, a (zt i) ≠ 0) (hqdt : ∀ i, deriv q (zt i) ≠ 0)
    (mu : Measure (OnePoint ℝ)) [IsProbabilityMeasure mu]
    (hmu : mu.support.Infinite) :
    let frozen := normalizedProjectiveCauchyJetLinftyContinuousControl
      xf nf mu hupperf
    let target := projectiveNevanlinnaJetLinftyContinuousControl
      a q zt nt hat hqdt mu huppert
    Function.Surjective (target.toLinearMap.domRestrict
      (LinearMap.ker frozen.toLinearMap)) := by
  dsimp only
  let frozenCauchy := normalizedProjectiveCauchyJetLinftyContinuousControl
    xf nf mu hupperf
  let targetCauchy := linftyBochnerControl mu
    (projectiveCauchyJetColumn (fun i => q (zt i)) nt)
    (memLp_projectiveCauchyJetColumn (fun i => q (zt i))
      (fun i => (huppert i).ne') nt mu)
  let targetEquiv :=
    (nevanlinnaJetPacketLinearEquiv a q zt nt hat hqdt).restrictScalars ℝ
  have hsurj : Function.Surjective
      (targetCauchy.toLinearMap.domRestrict
        (LinearMap.ker frozenCauchy.toLinearMap)) := by
    exact constrainedNormalizedProjectiveCauchyJet_linftyControl_surjective
      xf hxf_inj (fun i => q (zt i)) hqt_inj hcross
      hupperf huppert nf nt mu hmu
  have hconverted := constrainedControl_surjective_of_linearEquiv
    frozenCauchy.toLinearMap targetCauchy.toLinearMap
    (LinearEquiv.refl ℝ _) targetEquiv hsurj
  simpa [frozenCauchy, targetCauchy, targetEquiv,
    projectiveNevanlinnaJetLinftyContinuousControl,
    projectiveNevanlinnaJetLinftyControl,
    projectiveNevanlinnaJetLinftyContinuousControl_toLinearMap] using! hconverted

/-- The normalized genuine Nevanlinna frozen control: total mass together with a finite analytic
Nevanlinna-jet packet. -/
def normalizedProjectiveNevanlinnaJetLinftyContinuousControl
    {ι : Type*} [Fintype ι]
    (a q : ℂ → ℂ) (z : ι → ℂ) (n : ι → ℕ)
    (ha : ∀ i, a (z i) ≠ 0) (hq : ∀ i, deriv q (z i) ≠ 0)
    (mu : Measure (OnePoint ℝ)) [IsProbabilityMeasure mu]
    (hupper : ∀ i, 0 < (q (z i)).im) :
    Lp ℝ (⊤ : ENNReal) mu →L[ℝ]
      (ℝ × ((Σ i, Fin (n i)) → ℂ)) :=
  (linftyIntegralCLM mu).prod
    (projectiveNevanlinnaJetLinftyContinuousControl
      a q z n ha hq mu hupper)

/-- **Normalized constrained genuine Nevanlinna controllability.** Every disjoint finite target
packet remains onto on the exact tangent that annihilates both total mass and the frozen genuine
Nevanlinna packet. -/
theorem constrainedNormalizedProjectiveNevanlinnaJet_linftyControl_surjective
    {ιf ιt : Type*} [Fintype ιf] [DecidableEq ιf]
    [Fintype ιt] [DecidableEq ιt]
    (a q : ℂ → ℂ)
    (zf : ιf → ℂ) (zt : ιt → ℂ)
    (hqf_inj : Function.Injective (fun i => q (zf i)))
    (hqt_inj : Function.Injective (fun i => q (zt i)))
    (hcross : ∀ i j, q (zf i) ≠ q (zt j))
    (hupperf : ∀ i, 0 < (q (zf i)).im) (huppert : ∀ i, 0 < (q (zt i)).im)
    (nf : ιf → ℕ) (nt : ιt → ℕ)
    (haf : ∀ i, a (zf i) ≠ 0) (hat : ∀ i, a (zt i) ≠ 0)
    (hqdf : ∀ i, deriv q (zf i) ≠ 0) (hqdt : ∀ i, deriv q (zt i) ≠ 0)
    (mu : Measure (OnePoint ℝ)) [IsProbabilityMeasure mu]
    (hmu : mu.support.Infinite) :
    let frozen := normalizedProjectiveNevanlinnaJetLinftyContinuousControl
      a q zf nf haf hqdf mu hupperf
    let target := projectiveNevanlinnaJetLinftyContinuousControl
      a q zt nt hat hqdt mu huppert
    Function.Surjective (target.toLinearMap.domRestrict
      (LinearMap.ker frozen.toLinearMap)) := by
  dsimp only
  let frozenCauchy := normalizedProjectiveCauchyJetLinftyContinuousControl
    (fun i => q (zf i)) nf mu hupperf
  let targetCauchy := linftyBochnerControl mu
    (projectiveCauchyJetColumn (fun i => q (zt i)) nt)
    (memLp_projectiveCauchyJetColumn (fun i => q (zt i))
      (fun i => (huppert i).ne') nt mu)
  let frozenEquiv :
      (ℝ × ((Σ i, Fin (nf i)) → ℂ)) ≃ₗ[ℝ]
        (ℝ × ((Σ i, Fin (nf i)) → ℂ)) :=
    LinearEquiv.prodCongr (LinearEquiv.refl ℝ ℝ)
      ((nevanlinnaJetPacketLinearEquiv a q zf nf haf hqdf).restrictScalars ℝ)
  let targetEquiv :=
    (nevanlinnaJetPacketLinearEquiv a q zt nt hat hqdt).restrictScalars ℝ
  have hsurj : Function.Surjective
      (targetCauchy.toLinearMap.domRestrict
        (LinearMap.ker frozenCauchy.toLinearMap)) := by
    exact constrainedNormalizedProjectiveCauchyJet_linftyControl_surjective
      (fun i => q (zf i)) hqf_inj (fun i => q (zt i)) hqt_inj hcross
      hupperf huppert nf nt mu hmu
  have hconverted := constrainedControl_surjective_of_linearEquiv
    frozenCauchy.toLinearMap targetCauchy.toLinearMap frozenEquiv targetEquiv hsurj
  simpa [frozenCauchy, targetCauchy, frozenEquiv, targetEquiv,
    normalizedProjectiveCauchyJetLinftyContinuousControl,
    normalizedProjectiveNevanlinnaJetLinftyContinuousControl,
    projectiveNevanlinnaJetLinftyContinuousControl,
    projectiveNevanlinnaJetLinftyControl,
    projectiveNevanlinnaJetLinftyContinuousControl_toLinearMap] using! hconverted

end

end GaloisForLFunctions.HTGeometry
