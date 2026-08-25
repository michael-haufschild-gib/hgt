import GaloisForLFunctions.HTGeometry.CyclotomicRelativeBoxBasis
import GaloisForLFunctions.HTGeometry.BoundedRelationLogMagnitudeHypertranscendence
import GaloisForLFunctions.HTGeometry.PrimeCyclotomicEntireHypertranscendence

/-!
# Cyclotomic tail phases force hypertranscendence

Bounded-total-degree cyclotomic tail freedom separates the phase monomials in every normalized
formal algebraic differential relation. Lindemann--Weierstrass separates their algebraic
log-magnitude valuations. The resulting formal survival theorem is realized analytically for
positive-radius and entire series, including every algebraic rational-power log profile.
-/

open PowerSeries MvPolynomial Finset
open Filter
open scoped ENNReal Topology

namespace GaloisForLFunctions

noncomputable section

def atomTotalDegree (ν : ℕ →₀ ℕ) : ℕ := ν.sum fun _ k => k

def tailExponent (M : ℕ) (ν : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  ν.filter fun i => M ≤ i

def prefixExponent (M : ℕ) (ν : ℕ →₀ ℕ) : ℕ →₀ ℕ :=
  ν.filter fun i => i < M

def BoundedTailExponent (M D : ℕ) :=
  {ν : ℕ →₀ ℕ // (∀ i ∈ ν.support, M ≤ i) ∧ atomTotalDegree ν ≤ D}

instance (M D : ℕ) : DecidableEq (BoundedTailExponent M D) := Classical.decEq _

def BoundedTotalDegreeTailFreedom (u : ℕ → ℂ) : Prop :=
  ∀ D, 0 < D → ∃ M,
    LinearIndependent (HTGeometry.cyclotomicAdjoin (Finset.range M) u)
      (fun ν : BoundedTailExponent M D => atomPhase u ν.1)

theorem support_tailExponent (M : ℕ) (ν : ℕ →₀ ℕ) :
    (tailExponent M ν).support = ν.support.filter fun i => M ≤ i := by
  rw [tailExponent]
  exact Finsupp.support_filter (fun i : ℕ => M ≤ i) ν

theorem support_prefixExponent (M : ℕ) (ν : ℕ →₀ ℕ) :
    (prefixExponent M ν).support = ν.support.filter fun i => i < M := by
  rw [prefixExponent]
  exact Finsupp.support_filter (fun i : ℕ => i < M) ν

theorem atomTotalDegree_tailExponent_le (M : ℕ) (ν : ℕ →₀ ℕ) :
    atomTotalDegree (tailExponent M ν) ≤ atomTotalDegree ν := by
  rw [atomTotalDegree, atomTotalDegree, Finsupp.sum, Finsupp.sum]
  rw [support_tailExponent]
  have heq : (∑ i ∈ ν.support.filter (fun i => M ≤ i), (tailExponent M ν) i) =
      ∑ i ∈ ν.support.filter (fun i => M ≤ i), ν i := by
    apply Finset.sum_congr rfl
    intro i hi
    rw [Finset.mem_filter] at hi
    simp [tailExponent, hi.2]
  rw [heq]
  exact Finset.sum_le_sum_of_subset
    (Finset.filter_subset (fun i : ℕ => M ≤ i) ν.support)

theorem tailExponent_support_ge (M : ℕ) (ν : ℕ →₀ ℕ) :
    ∀ i ∈ (tailExponent M ν).support, M ≤ i := by
  intro i hi
  rw [support_tailExponent, Finset.mem_filter] at hi
  exact hi.2

theorem prefixExponent_support_lt (M : ℕ) (ν : ℕ →₀ ℕ) :
    ∀ i ∈ (prefixExponent M ν).support, i < M := by
  intro i hi
  rw [support_prefixExponent, Finset.mem_filter] at hi
  exact hi.2

theorem prefixExponent_add_tailExponent (M : ℕ) (ν : ℕ →₀ ℕ) :
    prefixExponent M ν + tailExponent M ν = ν := by
  ext i
  simp only [prefixExponent, tailExponent, Finsupp.add_apply, Finsupp.filter_apply]
  by_cases hi : i < M
  · rw [if_pos hi, if_neg (not_le.mpr hi)]
    simp
  · rw [if_neg hi, if_pos (le_of_not_gt hi)]
    simp

theorem atomPhase_add (u : ℕ → ℂ) (ν μ : ℕ →₀ ℕ) :
    atomPhase u (ν + μ) = atomPhase u ν * atomPhase u μ := by
  classical
  rw [atomPhase, atomPhase, atomPhase]
  apply Finsupp.prod_add_index
  · intro i hi
    simp
  · intro i hi a b
    exact pow_add (u i) a b

theorem atomTotalDegree_add (ν μ : ℕ →₀ ℕ) :
    atomTotalDegree (ν + μ) = atomTotalDegree ν + atomTotalDegree μ := by
  classical
  rw [atomTotalDegree, atomTotalDegree, atomTotalDegree]
  apply Finsupp.sum_add_index
  · intro i hi
    rfl
  · intro i hi a b
    rfl

theorem atomPhase_prefix_mul_tail (u : ℕ → ℂ) (M : ℕ) (ν : ℕ →₀ ℕ) :
    atomPhase u ν = atomPhase u (prefixExponent M ν) * atomPhase u (tailExponent M ν) := by
  rw [← atomPhase_add, prefixExponent_add_tailExponent]

theorem atomPhase_prefix_mem (u : ℕ → ℂ) (M : ℕ) (ν : ℕ →₀ ℕ) :
    atomPhase u (prefixExponent M ν) ∈
      HTGeometry.cyclotomicAdjoin (Finset.range M) u := by
  classical
  rw [atomPhase, Finsupp.prod]
  apply (HTGeometry.cyclotomicAdjoin (Finset.range M) u).prod_mem
  intro i hi
  apply (HTGeometry.cyclotomicAdjoin (Finset.range M) u).toSubalgebra.pow_mem
  apply IntermediateField.subset_adjoin ℚ _
  refine ⟨i, ?_, rfl⟩
  rw [Finset.mem_coe, Finset.mem_range]
  exact prefixExponent_support_lt M ν i hi

theorem tailExponent_eq_self_of_support_ge
    {M : ℕ} {ν : ℕ →₀ ℕ} (hν : ∀ i ∈ ν.support, M ≤ i) :
    tailExponent M ν = ν := by
  ext i
  by_cases hi : ν i = 0
  · simp only [tailExponent, Finsupp.filter_apply]
    split <;> simp [hi]
  · have himem : i ∈ ν.support := Finsupp.mem_support_iff.mpr hi
    simp [tailExponent, hν i himem]

theorem prefixExponent_eq_zero_of_support_ge
    {M : ℕ} {ν : ℕ →₀ ℕ} (hν : ∀ i ∈ ν.support, M ≤ i) :
    prefixExponent M ν = 0 := by
  ext i
  by_cases hi : ν i = 0
  · simp only [prefixExponent, Finsupp.filter_apply]
    split <;> simp [hi]
  · have himem : i ∈ ν.support := Finsupp.mem_support_iff.mpr hi
    simp [prefixExponent, not_lt.mpr (hν i himem)]

theorem tailExponent_unique_of_fullDegree
    {M D : ℕ} {νstar μ : ℕ →₀ ℕ}
    (hstarDegree : atomTotalDegree νstar = D)
    (hμDegree : atomTotalDegree μ ≤ D)
    (htail : tailExponent M μ = νstar) : μ = νstar := by
  have hsplit := congrArg atomTotalDegree (prefixExponent_add_tailExponent M μ)
  rw [atomTotalDegree_add, htail, hstarDegree] at hsplit
  have hprefixDegree : atomTotalDegree (prefixExponent M μ) = 0 := by omega
  have hprefix : prefixExponent M μ = 0 := by
    ext i
    by_cases hi : i ∈ (prefixExponent M μ).support
    · rw [atomTotalDegree, Finsupp.sum] at hprefixDegree
      exact (Finset.sum_eq_zero_iff.mp hprefixDegree i hi)
    · by_contra hne
      exact hi (Finsupp.mem_support_iff.mpr hne)
  calc
    μ = prefixExponent M μ + tailExponent M μ :=
      (prefixExponent_add_tailExponent M μ).symm
    _ = 0 + tailExponent M μ := by rw [hprefix]
    _ = νstar := by rw [zero_add, htail]

theorem sum_atomPhase_ne_zero_of_full_tail
    {u : ℕ → ℂ} {M D : ℕ}
    (hLI : LinearIndependent (HTGeometry.cyclotomicAdjoin (Finset.range M) u)
      (fun ν : BoundedTailExponent M D => atomPhase u ν.1))
    (A : Finset (ℕ →₀ ℕ)) (w : (ℕ →₀ ℕ) → ℂ)
    (hdegree : ∀ ν ∈ A, atomTotalDegree ν ≤ D)
    (hw : ∀ ν ∈ A, w ν ∈ HTGeometry.cyclotomicAdjoin (Finset.range M) u)
    {νstar : ℕ →₀ ℕ} (hstarMem : νstar ∈ A)
    (hstarTail : ∀ i ∈ νstar.support, M ≤ i)
    (hstarDegree : atomTotalDegree νstar = D)
    (hstarWeight : w νstar ≠ 0) :
    ∑ ν ∈ A, atomPhase u ν * w ν ≠ 0 := by
  classical
  let νtail : {ν // ν ∈ A} → BoundedTailExponent M D := fun ν =>
    ⟨tailExponent M ν.1, tailExponent_support_ge M ν.1,
      (atomTotalDegree_tailExponent_le M ν.1).trans (hdegree ν.1 ν.2)⟩
  let T : Finset (BoundedTailExponent M D) := A.attach.image νtail
  let C : {τ : BoundedTailExponent M D // τ ∈ T} →
      HTGeometry.cyclotomicAdjoin (Finset.range M) u := fun τ =>
    ∑ ν ∈ A.attach.filter (fun ν => νtail ν = τ.1),
      ⟨atomPhase u (prefixExponent M ν.1) * w ν.1,
        (HTGeometry.cyclotomicAdjoin (Finset.range M) u).mul_mem
          (atomPhase_prefix_mem u M ν.1) (hw ν.1 ν.2)⟩
  have hLI' : LinearIndependent
      (HTGeometry.cyclotomicAdjoin (Finset.range M) u)
      (fun τ : {τ : BoundedTailExponent M D // τ ∈ T} => atomPhase u τ.1.1) := by
    change LinearIndependent (HTGeometry.cyclotomicAdjoin (Finset.range M) u)
      ((fun ν : BoundedTailExponent M D => atomPhase u ν.1) ∘
        (fun τ : {τ : BoundedTailExponent M D // τ ∈ T} => τ.1))
    exact hLI.comp (fun τ : {τ : BoundedTailExponent M D // τ ∈ T} => τ.1)
      Subtype.val_injective
  have hregroup :
      ∑ ν ∈ A, atomPhase u ν * w ν =
        ∑ τ ∈ T,
          (∑ ν ∈ A.attach.filter (fun ν => νtail ν = τ),
            atomPhase u (prefixExponent M ν.1) * w ν.1) * atomPhase u τ.1 := by
    calc
      ∑ ν ∈ A, atomPhase u ν * w ν =
          ∑ ν ∈ A.attach, atomPhase u ν.1 * w ν.1 := by
            exact (Finset.sum_attach A (fun ν => atomPhase u ν * w ν)).symm
      _ = ∑ ν ∈ A.attach,
          (atomPhase u (prefixExponent M ν.1) *
            atomPhase u (tailExponent M ν.1)) * w ν.1 := by
            apply Finset.sum_congr rfl
            intro ν hν
            rw [atomPhase_prefix_mul_tail]
      _ = ∑ τ ∈ T, ∑ ν ∈ A.attach.filter (fun ν => νtail ν = τ),
          (atomPhase u (prefixExponent M ν.1) *
            atomPhase u (tailExponent M ν.1)) * w ν.1 := by
            rw [Finset.sum_fiberwise_of_maps_to
              (fun ν hν => Finset.mem_image_of_mem _ hν)]
      _ = ∑ τ ∈ T,
          (∑ ν ∈ A.attach.filter (fun ν => νtail ν = τ),
            atomPhase u (prefixExponent M ν.1) * w ν.1) * atomPhase u τ.1 := by
            apply Finset.sum_congr rfl
            intro τ hτ
            rw [Finset.sum_mul]
            apply Finset.sum_congr rfl
            intro ν hν
            have hmap := (Finset.mem_filter.mp hν).2
            have htail : tailExponent M ν.1 = τ.1 := by
              simpa [νtail] using congrArg Subtype.val hmap
            rw [htail]
            ring
  intro hsum
  have hCcoe (τ : {τ : BoundedTailExponent M D // τ ∈ T}) :
      (C τ : ℂ) =
        ∑ ν ∈ A.attach.filter (fun ν => νtail ν = τ.1),
          atomPhase u (prefixExponent M ν.1) * w ν.1 := by
    simp [C]
  have hrel : ∑ τ : {τ : BoundedTailExponent M D // τ ∈ T},
      C τ • atomPhase u τ.1.1 = 0 := by
    change ∑ τ : {τ : BoundedTailExponent M D // τ ∈ T},
      (C τ : ℂ) * atomPhase u τ.1.1 = 0
    change ∑ τ ∈ T.attach, (C τ : ℂ) * atomPhase u τ.1.1 = 0
    simp_rw [hCcoe]
    let g : BoundedTailExponent M D → ℂ := fun τ =>
      (∑ ν ∈ A.attach.filter (fun ν => νtail ν = τ),
        atomPhase u (prefixExponent M ν.1) * w ν.1) * atomPhase u τ.1
    change ∑ τ ∈ T.attach, g τ.1 = 0
    rw [Finset.sum_attach T g]
    dsimp only [g]
    rw [← hregroup]
    exact hsum
  have hallzero : ∀ τ : {τ : BoundedTailExponent M D // τ ∈ T}, C τ = 0 :=
    (Fintype.linearIndependent_iff.mp hLI') C hrel
  let νstarA : {ν // ν ∈ A} := ⟨νstar, hstarMem⟩
  have hstarSelf : tailExponent M νstar = νstar :=
    tailExponent_eq_self_of_support_ge hstarTail
  have hstarT : νtail νstarA ∈ T := by
    exact Finset.mem_image_of_mem νtail (Finset.mem_attach A νstarA)
  let τstar : {τ : BoundedTailExponent M D // τ ∈ T} :=
    ⟨νtail νstarA, hstarT⟩
  have hfiber :
      A.attach.filter (fun ν => νtail ν = τstar.1) = {νstarA} := by
    ext ν
    rw [Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨hνA, htailEq⟩
      apply Subtype.ext
      apply tailExponent_unique_of_fullDegree hstarDegree
        (hdegree ν.1 ν.2)
      have := congrArg Subtype.val htailEq
      simpa [τstar, νtail, νstarA, hstarSelf] using this
    · rintro rfl
      exact ⟨Finset.mem_attach A νstarA, rfl⟩
  have hprefixStar : prefixExponent M νstar = 0 :=
    prefixExponent_eq_zero_of_support_ge hstarTail
  have hCstar : C τstar ≠ 0 := by
    dsimp [C]
    rw [hfiber, Finset.sum_singleton]
    intro hzero
    apply hstarWeight
    have hzero' := congrArg Subtype.val hzero
    simpa [νstarA, hprefixStar, atomPhase] using hzero'
  exact hCstar (hallzero τstar)

theorem exists_coeff_ne_zero_of_phaseTail_exponential
    {b : ℕ → ℝ} {u : ℕ → ℂ} {F : PowerSeries ℂ}
    (hF : ∀ i, PowerSeries.coeff i F =
      u i * Complex.exp (-(b i : ℂ)))
    (hbAlg : ∀ i, IsAlgebraic ℚ (b i))
    (htailFreedom : BoundedTotalDegreeTailFreedom u)
    (huAlg : ∀ i, IsAlgebraic ℚ (u i))
    {n : ℕ} (Q : MvPolynomial (Fin (n + 2)) ℂ)
    (hQint : ∀ m, ∃ z : ℤ, MvPolynomial.coeff m Q = (z : ℂ))
    (hDpos : 0 < magnitudeMaxJetDegree n Q) :
    ∃ N, PowerSeries.coeff N
      (MvPolynomial.aeval (formalJets n F) Q) ≠ 0 := by
  classical
  let D := magnitudeMaxJetDegree n Q
  have hD : 0 < D := by simpa [D] using hDpos
  have hsupport : Q.support.Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    have hDz : D = 0 := by simp [D, magnitudeMaxJetDegree, hempty]
    omega
  obtain ⟨anchor, ha, haSup⟩ :=
    Finset.exists_mem_eq_sup Q.support hsupport (fun m => jetMonomialDegree n m)
  have haD : jetMonomialDegree n anchor = D := by
    dsimp [D]
    rw [magnitudeMaxJetDegree, jetMonomialDegree]
    exact haSup.symm
  have haPos : 0 < jetMonomialDegree n anchor := by omega
  obtain ⟨δ, _hδ, Q₀, hbalanced⟩ :=
    exists_eventually_balanced_nonzero_aevalWeight ha haPos
  obtain ⟨M, hLI⟩ := htailFreedom D hD
  let q := max Q₀ M
  have hqQ₀ : Q₀ ≤ q := le_max_left _ _
  have hqM : M ≤ q := le_max_right _ _
  let s : Fin (jetMonomialDegree n anchor) → ℕ := fun i => q + δ i
  let N := (∑ i, s i) + anchor 0 - jetMonomialOrder n anchor
  have hbalancedq := hbalanced q hqQ₀
  have hstarMem : key s ∈ (sigmaIdx n N Q).image (atomKeyOf n) := by
    simpa [s, N] using hbalancedq.1
  have hstarWeight : aevalWeight n N Q (key s) ≠ 0 := by
    simpa [s, N] using hbalancedq.2.1
  have hstarCount : atomTotalDegree (key s) = D := by
    rw [atomTotalDegree, key_total_count, haD]
  have hstarTail : ∀ i ∈ (key s).support, M ≤ i := by
    intro i hi
    have hi0 : key s i ≠ 0 := Finsupp.mem_support_iff.mp hi
    have hex : ∃ j, s j = i := by
      by_contra hno
      push Not at hno
      apply hi0
      simp [key, hno]
    obtain ⟨j, rfl⟩ := hex
    dsimp [s]
    omega
  let A := (sigmaIdx n N Q).image (atomKeyOf n)
  refine ⟨N, ?_⟩
  intro hcoeff
  have hsumzero :
      ∑ ν ∈ A,
          ν.prod (fun i k => (PowerSeries.coeff i F) ^ k) *
            aevalWeight n N Q ν = 0 := by
    rw [← coeff_aeval_regrouped_weight n N F Q]
    exact hcoeff
  have hgroupzero :
      ∑ v ∈ A.image (boundedAtomValuation b),
          (∑ ν ∈ A.filter (fun ν => boundedAtomValuation b ν = v),
            atomPhase u ν * aevalWeight n N Q ν) *
              Complex.exp (-((v : ℝ) : ℂ)) = 0 := by
    rw [← sum_atom_products_regrouped_by_valuation hF A
      (aevalWeight n N Q)]
    exact hsumzero
  let V := A.image (boundedAtomValuation b)
  let I := {v : ℝ // v ∈ V}
  let E : I → ℂ := fun v => -((v.1 : ℝ) : ℂ)
  let C : I → ℂ := fun v =>
    ∑ ν ∈ A.filter (fun ν => boundedAtomValuation b ν = v.1),
      atomPhase u ν * aevalWeight n N Q ν
  have hEalg : ∀ v, IsAlgebraic ℚ (E v) := by
    intro v
    obtain ⟨ν, hν, hval⟩ := Finset.mem_image.mp v.2
    simpa [E, hval] using (boundedAtomValuation_coe_isAlgebraic hbAlg ν).neg
  have hEinj : Function.Injective E := by
    intro v w hvw
    apply Subtype.ext
    dsimp [E] at hvw
    exact Complex.ofReal_injective (neg_injective hvw)
  have hCAlg : ∀ v, IsAlgebraic ℚ (C v) := by
    intro v
    rw [← Subalgebra.mem_algebraicClosure]
    dsimp [C]
    apply Subalgebra.sum_mem
    intro ν hν
    rw [Subalgebra.mem_algebraicClosure]
    apply (atomPhase_isAlgebraic huAlg ν).mul
    obtain ⟨z, hz⟩ := aevalWeight_isInt n N Q ν hQint
    rw [hz]
    simpa using (isAlgebraic_algebraMap (R := ℚ) (A := ℂ) (z : ℚ))
  have hrel : ∑ v : I, C v * Complex.exp (E v) = 0 := by
    change (∑ v ∈ V.attach, C v * Complex.exp (E v)) = 0
    simp only [C, E]
    rw [Finset.sum_attach V (fun v : ℝ =>
      (∑ ν ∈ A.filter (fun ν => boundedAtomValuation b ν = v),
        atomPhase u ν * aevalWeight n N Q ν) *
          Complex.exp (-((v : ℝ) : ℂ)))]
    simpa [V] using hgroupzero
  have hallzero := GaloisForLFunctions.RHTower.exp_algebraic_relation_eq_zero
    E C hEalg hEinj hCAlg hrel
  have hvstar : boundedAtomValuation b (key s) ∈ V := by
    apply Finset.mem_image.mpr
    exact ⟨key s, hstarMem, rfl⟩
  let vstar : I := ⟨boundedAtomValuation b (key s), hvstar⟩
  have hstarFiber : key s ∈
      A.filter (fun ν => boundedAtomValuation b ν = (vstar : I).1) := by
    exact Finset.mem_filter.mpr ⟨hstarMem, rfl⟩
  have hdegreeFiber : ∀ ν ∈
      A.filter (fun μ => boundedAtomValuation b μ = (vstar : I).1),
      atomTotalDegree ν ≤ D := by
    intro ν hν
    have hνA := (Finset.mem_filter.mp hν).1
    simpa [atomTotalDegree, D] using appearing_atom_count_le Q hνA
  have hweightMem : ∀ ν ∈
      A.filter (fun μ => boundedAtomValuation b μ = (vstar : I).1),
      aevalWeight n N Q ν ∈ HTGeometry.cyclotomicAdjoin (Finset.range M) u := by
    intro ν hν
    obtain ⟨z, hz⟩ := aevalWeight_isInt n N Q ν hQint
    rw [hz]
    exact
      (HTGeometry.cyclotomicAdjoin (Finset.range M) u).toSubalgebra.algebraMap_mem
        (z : ℚ)
  have hCstar : C vstar ≠ 0 := by
    dsimp [C, vstar]
    exact sum_atomPhase_ne_zero_of_full_tail hLI
      (A.filter (fun ν => boundedAtomValuation b ν = boundedAtomValuation b (key s)))
      (aevalWeight n N Q) hdegreeFiber hweightMem hstarFiber hstarTail
      hstarCount hstarWeight
  exact hCstar (hallzero vstar)

theorem no_formal_relation_of_phaseTail_exponential
    {b : ℕ → ℝ} {u : ℕ → ℂ} {F : PowerSeries ℂ}
    (hF : ∀ i, PowerSeries.coeff i F =
      u i * Complex.exp (-(b i : ℂ)))
    (hbAlg : ∀ i, IsAlgebraic ℚ (b i))
    (htailFreedom : BoundedTotalDegreeTailFreedom u)
    (huAlg : ∀ i, IsAlgebraic ℚ (u i))
    (huNorm : ∀ i, ‖u i‖ = 1)
    {n : ℕ} (P : MvPolynomial (Fin (n + 2)) ℂ) (hP : P ≠ 0) :
    MvPolynomial.aeval (formalJets n F) P ≠ 0 := by
  intro hann
  obtain ⟨n', Q, hQ, hQint, hQrel⟩ :=
    formal_mahler_integer_normalization hP hann
  have hnorm : ∀ i, ‖PowerSeries.coeff i F‖ = Real.exp (-b i) := by
    intro i
    rw [hF, norm_mul, huNorm, one_mul, Complex.norm_exp]
    simp
  have hDpos := magnitudeMaxJetDegree_pos_of_integer_relation
    F hnorm Q hQ hQint hQrel
  obtain ⟨N, hN⟩ := exists_coeff_ne_zero_of_phaseTail_exponential
    hF hbAlg htailFreedom huAlg Q hQint hDpos
  rw [hQrel, map_zero] at hN
  exact hN rfl

theorem finsupp_coordinate_le_atomTotalDegree (ν : ℕ →₀ ℕ) (i : ℕ) :
    ν i ≤ atomTotalDegree ν := by
  rw [atomTotalDegree, Finsupp.sum]
  by_cases hi : i ∈ ν.support
  · exact Finset.single_le_sum (fun j hj => Nat.zero_le (ν j)) hi
  · have hi0 : ν i = 0 := by
      by_contra hne
      exact hi (Finsupp.mem_support_iff.mpr hne)
    simp [hi0]

theorem linearIndependent_boundedTailExponent_prime
    {q : ℕ → ℕ} {u : ℕ → ℂ} (M D : ℕ)
    (hprime : ∀ i, Nat.Prime (q i))
    (hqinj : Function.Injective q)
    (hu : ∀ i, IsPrimitiveRoot (u i) (q i))
    (hlarge : ∀ i, M ≤ i → D + 1 < q i) :
    LinearIndependent (HTGeometry.cyclotomicAdjoin (Finset.range M) u)
      (fun ν : BoundedTailExponent M D => atomPhase u ν.1) := by
  classical
  rw [linearIndependent_iff]
  intro l hl
  let S : Finset ℕ := l.support.biUnion fun ν => ν.1.support
  have hSge : ∀ i ∈ S, M ≤ i := by
    intro i hi
    obtain ⟨ν, hνl, hiν⟩ := Finset.mem_biUnion.mp hi
    exact ν.2.1 i hiν
  have hdisj : Disjoint (Finset.range M) S := by
    rw [Finset.disjoint_left]
    intro i hip hiS
    exact (Nat.not_lt_of_ge (hSge i hiS)) (Finset.mem_range.mp hip)
  have hqpos : ∀ i ∈ Finset.range M ∪ S, 0 < q i := by
    intro i hi
    exact (hprime i).pos
  have huall : ∀ i ∈ Finset.range M ∪ S, IsPrimitiveRoot (u i) (q i) := by
    intro i hi
    exact hu i
  have hcop : ∀ i ∈ Finset.range M ∪ S, ∀ j ∈ Finset.range M ∪ S,
      i ≠ j → Nat.Coprime (q i) (q j) := by
    intro i hi j hj hij
    exact (Nat.coprime_primes (hprime i) (hprime j)).mpr
      (fun hq => hij (hqinj hq))
  have hbox := HTGeometry.linearIndependent_cyclotomicBox_over_prefix
    (Finset.range M) S hdisj q u hqpos huall hcop
  let encode : {ν // ν ∈ l.support} → HTGeometry.CyclotomicBox S q := fun ν i =>
    ⟨ν.1.1 i.1, by
      rw [Nat.totient_prime (hprime i.1)]
      have hcoord := finsupp_coordinate_le_atomTotalDegree ν.1.1 i.1
      have hdegree := ν.1.2.2
      have horder := hlarge i.1 (hSge i.1 i.2)
      omega⟩
  have hencode : Function.Injective encode := by
    intro ν μ hνμ
    apply Subtype.ext
    apply Subtype.ext
    ext i
    by_cases hi : i ∈ S
    · let iS : {i // i ∈ S} := ⟨i, hi⟩
      have hcoord := congrFun hνμ iS
      exact congrArg Fin.val hcoord
    · have hν0 : ν.1.1 i = 0 := by
        by_contra hne
        apply hi
        apply Finset.mem_biUnion.mpr
        exact ⟨ν.1, ν.2, Finsupp.mem_support_iff.mpr hne⟩
      have hμ0 : μ.1.1 i = 0 := by
        by_contra hne
        apply hi
        apply Finset.mem_biUnion.mpr
        exact ⟨μ.1, μ.2, Finsupp.mem_support_iff.mpr hne⟩
      rw [hν0, hμ0]
  have hphase (ν : {ν // ν ∈ l.support}) :
      HTGeometry.cyclotomicBoxMonomial S q u (encode ν) = atomPhase u ν.1.1 := by
    let ν0 : ℕ →₀ ℕ := ν.1.1
    rw [atomPhase, Finsupp.prod]
    change (∏ i : {i // i ∈ S}, u i.1 ^ ν0 i.1) =
      ∏ i ∈ ν0.support, u i ^ ν0 i
    calc
      (∏ i : {i // i ∈ S}, u i.1 ^ ν0 i.1) =
          ∏ i ∈ S, u i ^ ν0 i := Finset.prod_attach S (fun i => u i ^ ν0 i)
      _ = ∏ i ∈ ν0.support, u i ^ ν0 i := by
        symm
        apply Finset.prod_subset
        · intro i hi
          exact Finset.mem_biUnion.mpr ⟨ν.1, ν.2, hi⟩
        · intro i hiS hiNot
          have hi0 : ν0 i = 0 := by
            by_contra hne
            exact hiNot (Finsupp.mem_support_iff.mpr hne)
          simp [hi0]
  have hLI := hbox.comp encode hencode
  change LinearIndependent (HTGeometry.cyclotomicAdjoin (Finset.range M) u)
    (HTGeometry.cyclotomicBoxMonomial S q u ∘ encode) at hLI
  have hsum : ∑ ν : {ν // ν ∈ l.support},
      l ν.1 • HTGeometry.cyclotomicBoxMonomial S q u (encode ν) = 0 := by
    simp_rw [hphase]
    let f : BoundedTailExponent M D → ℂ := fun ν =>
      l ν • atomPhase u ν.1
    change ∑ ν ∈ l.support.attach, f ν.1 = 0
    calc
      ∑ ν ∈ l.support.attach, f ν.1 = ∑ ν ∈ l.support, f ν :=
        Finset.sum_attach l.support f
      _ = 0 := by
        rw [Finsupp.linearCombination_apply] at hl
        exact hl
  have hallzero := (Fintype.linearIndependent_iff.mp hLI)
    (fun ν : {ν // ν ∈ l.support} => l ν.1) hsum
  apply Finsupp.ext
  intro ν
  by_cases hν : ν ∈ l.support
  · exact hallzero ⟨ν, hν⟩
  · by_contra hne
    exact hν (Finsupp.mem_support_iff.mpr hne)

theorem boundedTotalDegreeTailFreedom_of_prime_orders
    {q : ℕ → ℕ} {u : ℕ → ℂ}
    (hprime : ∀ i, Nat.Prime (q i))
    (hqinj : Function.Injective q)
    (hu : ∀ i, IsPrimitiveRoot (u i) (q i))
    (hqtop : Filter.Tendsto q Filter.atTop Filter.atTop) :
    BoundedTotalDegreeTailFreedom u := by
  intro D hD
  have hev : ∀ᶠ i in Filter.atTop, D + 1 < q i := by
    exact (Filter.tendsto_atTop.1 hqtop (D + 2))
  obtain ⟨M, hM⟩ := (Filter.eventually_atTop.1 hev)
  exact ⟨M, linearIndependent_boundedTailExponent_prime M D
    hprime hqinj hu (fun i hi => hM i hi)⟩

/-- A smooth function with phase-tail-free exponential Taylor coefficients is
hypertranscendental. -/
theorem hypertranscendental_of_phaseTail_exponential_taylor
    {f : ℂ → ℂ} (hf : ContDiff ℂ (⊤ : ℕ∞) f)
    {b : ℕ → ℝ} {u : ℕ → ℂ}
    (hcoeff : ∀ i, PowerSeries.coeff i (taylorPS f) =
      u i * Complex.exp (-(b i : ℂ)))
    (hbAlg : ∀ i, IsAlgebraic ℚ (b i))
    (htailFreedom : BoundedTotalDegreeTailFreedom u)
    (huAlg : ∀ i, IsAlgebraic ℚ (u i))
    (huNorm : ∀ i, ‖u i‖ = 1) :
    Hypertranscendental f := by
  apply hypertranscendental_of_aeval_survives hf
  intro n P hP
  exact no_formal_relation_of_phaseTail_exponential
    hcoeff hbAlg htailFreedom huAlg huNorm P hP

/-- Superlinear algebraic log magnitudes and phase-tail freedom give an entire
hypertranscendental scalar series. -/
theorem hypertranscendental_phaseTailExponentialFunction
    {b : ℕ → ℝ} {u : ℕ → ℂ}
    (hgrowth : Tendsto (fun n => b n / (n : ℝ)) atTop atTop)
    (hbAlg : ∀ n, IsAlgebraic ℚ (b n))
    (htailFreedom : BoundedTotalDegreeTailFreedom u)
    (huAlg : ∀ n, IsAlgebraic ℚ (u n))
    (huNorm : ∀ n, ‖u n‖ = 1) :
    Hypertranscendental (boundedRelationExponentialFunction b u) := by
  apply hypertranscendental_of_phaseTail_exponential_taylor
    (contDiff_boundedRelationExponentialFunction hgrowth huNorm)
    (b := b) (u := u)
  · intro n
    rw [taylorPS_boundedRelationExponentialFunction hgrowth huNorm]
    rfl
  · exact hbAlg
  · exact htailFreedom
  · exact huAlg
  · exact huNorm

/-- Primitive roots of injective prime orders tending to infinity give the explicit entire
phase-tail family. -/
theorem hypertranscendental_primePhaseTailExponentialFunction
    {q : ℕ → ℕ} {u : ℕ → ℂ} {b : ℕ → ℝ}
    (hprime : ∀ i, Nat.Prime (q i))
    (hqinj : Function.Injective q)
    (hu : ∀ i, IsPrimitiveRoot (u i) (q i))
    (hqtop : Tendsto q atTop atTop)
    (hgrowth : Tendsto (fun n => b n / (n : ℝ)) atTop atTop)
    (hbAlg : ∀ n, IsAlgebraic ℚ (b n)) :
    Hypertranscendental (boundedRelationExponentialFunction b u) := by
  apply hypertranscendental_phaseTailExponentialFunction hgrowth hbAlg
    (boundedTotalDegreeTailFreedom_of_prime_orders hprime hqinj hu hqtop)
  · intro n
    exact HTGeometry.primitiveRoot_isAlgebraic (hprime n).pos (hu n)
  · intro n
    exact HTGeometry.norm_eq_one_of_isPrimitiveRoot_complex (hprime n).pos (hu n)

/-- Eventual lower boundedness of `b n / n` gives positive convergence radius for the exact
unit-phase exponential series. -/
theorem phaseTailExponentialSeries_radius_ne_zero_of_eventually_ratio_ge
    {b : ℕ → ℝ} {u : ℕ → ℂ}
    (hlower : ∃ c : ℝ, ∀ᶠ n in atTop, c ≤ b n / (n : ℝ))
    (huNorm : ∀ n, ‖u n‖ = 1) :
    (FormalMultilinearSeries.ofScalars ℂ
      (boundedRelationExponentialCoeff b u)).radius ≠ 0 := by
  obtain ⟨c, hc⟩ := hlower
  obtain ⟨N, hN⟩ := eventually_atTop.1 hc
  let N₁ := max N 1
  let r : NNReal := ⟨Real.exp (c - 1), Real.exp_nonneg _⟩
  let p := FormalMultilinearSeries.ofScalars ℂ
    (boundedRelationExponentialCoeff b u)
  have hgeom : Summable (fun n : ℕ => Real.exp (-1) ^ n) := by
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.exp_lt_one_iff]
    norm_num
  have hgeomShift : Summable (fun n : ℕ => Real.exp (-1) ^ (n + N₁)) :=
    (summable_nat_add_iff N₁).mpr hgeom
  have hterm (n : ℕ) :
      ‖p (n + N₁)‖ * (r : ℝ) ^ (n + N₁) ≤ Real.exp (-1) ^ (n + N₁) := by
    have hmN : N ≤ n + N₁ := by dsimp [N₁]; omega
    have hmposNat : 0 < n + N₁ := by simp [N₁]
    have hmpos : (0 : ℝ) < (n + N₁ : ℕ) := by exact_mod_cast hmposNat
    have hbc := (le_div_iff₀ hmpos).mp (hN (n + N₁) hmN)
    rw [FormalMultilinearSeries.ofScalars_norm,
      norm_boundedRelationExponentialCoeff huNorm]
    change Real.exp (-b (n + N₁)) * Real.exp (c - 1) ^ (n + N₁) ≤
      Real.exp (-1) ^ (n + N₁)
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    norm_num [Nat.cast_add] at hbc ⊢
    nlinarith
  have hsShift : Summable (fun n : ℕ =>
      ‖p (n + N₁)‖ * (r : ℝ) ^ (n + N₁)) := by
    apply Summable.of_nonneg_of_le
    · intro n
      positivity
    · exact hterm
    · exact hgeomShift
  have hs : Summable (fun n : ℕ => ‖p n‖ * (r : ℝ) ^ n) :=
    (summable_nat_add_iff N₁).mp hsShift
  have hrle : (r : ENNReal) ≤ p.radius := p.le_radius_of_summable_norm hs
  intro hrzero
  have hrzero' : p.radius = 0 := by simpa [p] using hrzero
  have hrpos : (0 : ENNReal) < (r : ENNReal) := by
    apply ENNReal.coe_pos.mpr
    change 0 < Real.exp (c - 1)
    exact Real.exp_pos _
  rw [hrzero'] at hrle
  exact (not_le_of_gt hrpos) hrle

/-- Exact rational-power logarithmic profile, with arbitrary algebraic initial value. -/
def rationalPowerLogProfile (b0 B : ℝ) (β : ℚ) (n : ℕ) : ℝ :=
  if n = 0 then b0 else B * (n : ℝ) ^ (β : ℝ)

/-- A positive rational power of a natural number is algebraic. -/
theorem isAlgebraic_natCast_rpow_rat {β : ℚ} (hβ : 0 < β) (n : ℕ) :
    IsAlgebraic ℚ ((n : ℝ) ^ (β : ℝ)) := by
  let a : ℕ := β.num.natAbs
  let d : ℕ := β.den
  have hnum : 0 < β.num := Rat.num_pos.mpr hβ
  have hden : 0 < d := by exact β.den_pos
  have hnumCast : (a : ℤ) = β.num := by
    exact Int.natAbs_of_nonneg (le_of_lt hnum)
  have hβcast : (β : ℝ) = (a : ℝ) / (d : ℝ) := by
    rw [Rat.cast_def]
    congr 1
    exact_mod_cast hnumCast.symm
  apply IsAlgebraic.of_pow hden
  have hpow : (((n : ℝ) ^ (β : ℝ)) ^ d) = (n : ℝ) ^ a := by
    rw [← Real.rpow_mul_natCast (Nat.cast_nonneg n)]
    rw [hβcast]
    have hd0 : (d : ℝ) ≠ 0 := by positivity
    rw [div_mul_cancel₀ _ hd0, Real.rpow_natCast]
  rw [hpow]
  exact (isAlgebraic_algebraMap (R := ℚ) (A := ℝ) (n : ℚ)).pow a

theorem rationalPowerLogProfile_isAlgebraic
    {b0 B : ℝ} {β : ℚ}
    (hb0 : IsAlgebraic ℚ b0) (hB : IsAlgebraic ℚ B) (hβ : 0 < β) (n : ℕ) :
    IsAlgebraic ℚ (rationalPowerLogProfile b0 B β n) := by
  by_cases hn : n = 0
  · simp [rationalPowerLogProfile, hn, hb0]
  · rw [rationalPowerLogProfile, if_neg hn]
    exact hB.mul (isAlgebraic_natCast_rpow_rat hβ n)

theorem tendsto_rationalPowerLogProfile_div
    {b0 B : ℝ} {β : ℚ} (hB : 0 < B) (hβ : 1 < β) :
    Tendsto (fun n => rationalPowerLogProfile b0 B β n / (n : ℝ)) atTop atTop := by
  have hexp : (0 : ℝ) < (β : ℝ) - 1 := by
    rw [sub_pos]
    exact_mod_cast hβ
  have hrpow : Tendsto (fun n : ℕ => (n : ℝ) ^ ((β : ℝ) - 1)) atTop atTop :=
    (tendsto_rpow_atTop hexp).comp tendsto_natCast_atTop_atTop
  have hmul : Tendsto (fun n : ℕ => B * (n : ℝ) ^ ((β : ℝ) - 1)) atTop atTop :=
    hrpow.const_mul_atTop hB
  apply hmul.congr'
  filter_upwards [eventually_gt_atTop 0] with n hn
  have hn0 : n ≠ 0 := Nat.ne_of_gt hn
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  symm
  rw [rationalPowerLogProfile, if_neg hn0]
  calc
    B * (n : ℝ) ^ (β : ℝ) / (n : ℝ) =
        B * ((n : ℝ) ^ (β : ℝ) / (n : ℝ)) := by ring
    _ = B * (n : ℝ) ^ ((β : ℝ) - 1) := by
      rw [Real.rpow_sub hnR]
      simp

/-- Exact smooth-profile corollary: every algebraic `B > 0`, rational `β > 1`, and arbitrary
algebraic initial log magnitude gives an entire hypertranscendental prime-phase series. -/
theorem hypertranscendental_primePhaseTail_rationalPower
    {q : ℕ → ℕ} {u : ℕ → ℂ}
    (hprime : ∀ i, Nat.Prime (q i))
    (hqinj : Function.Injective q)
    (hu : ∀ i, IsPrimitiveRoot (u i) (q i))
    (hqtop : Tendsto q atTop atTop)
    {b0 B : ℝ} (hb0 : IsAlgebraic ℚ b0)
    (hBAlg : IsAlgebraic ℚ B) (hB : 0 < B)
    {β : ℚ} (hβ : 1 < β) :
    Hypertranscendental
      (boundedRelationExponentialFunction (rationalPowerLogProfile b0 B β) u) := by
  apply hypertranscendental_primePhaseTailExponentialFunction
    hprime hqinj hu hqtop (tendsto_rationalPowerLogProfile_div hB hβ)
  intro n
  exact rationalPowerLogProfile_isAlgebraic hb0 hBAlg (lt_trans zero_lt_one hβ) n

end

end GaloisForLFunctions
