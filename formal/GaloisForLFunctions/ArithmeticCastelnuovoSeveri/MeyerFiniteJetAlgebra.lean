import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.FaithfulPositiveMeyerDegrees
import GaloisForLFunctions.ArithmeticCastelnuovoSeveri.MeyerSharpConvolutionAlgebra

/-!
# The exact finite jet algebra inside genuine Poisson cohomology

Factorial-scaled actual causal sources realize individual Hasse coordinates.
Their products are the truncated polynomial products, and arithmetic sharp
reflects each block with the exact parity sign. Every identity is an equality
in the original quotient, proved by full arithmetic jet separation.
-/

noncomputable section
open Complex RHTower
open scoped ComplexConjugate
namespace GaloisForLFunctions.ArithmeticCastelnuovoSeveri

/-- An actual source realizing one Hasse coordinate rather than one raw derivative. -/
def meyerHasseJetSource (rho : XiDivisorSupport) (j : DeningerArithmeticJetIndex rho) :
    DeningerMeyerStrongLogTarget := (j.val.factorial : ℂ) • meyerSingleJetSource rho j

/-- The factorial normalization realizes the exact coordinate vector. -/
theorem meyerHasseJetSource_moment (rho : XiDivisorSupport)
    (j : DeningerArithmeticJetIndex rho) (sigma : XiDivisorSupport)
    (i : DeningerArithmeticJetIndex sigma) :
    deningerMeyerHasseMoment (meyerHasseJetSource rho j) i.val (sigma : ℂ) =
      if sigma = rho ∧ i.val = j.val then 1 else 0 := by
  simp only [meyerHasseJetSource, deningerMeyerHasseMoment, map_smul, smul_eq_mul,
    meyerSingleJetSource_jet]
  split_ifs with h
  · rw [h.2, mul_one, div_self]
    exact_mod_cast Nat.factorial_ne_zero j.val
  · rw [mul_zero, zero_div]

/-- Full Hasse readings determine the actual quotient class. -/
theorem meyerSourceClass_eq_of_hasse_moments_eq
    (g h : DeningerMeyerStrongLogTarget)
    (he : ∀ (rho : XiDivisorSupport) (j : DeningerArithmeticJetIndex rho),
      deningerMeyerHasseMoment g j.val (rho : ℂ) =
        deningerMeyerHasseMoment h j.val (rho : ℂ)) :
    (Submodule.Quotient.mk g : DeningerMeyerStrongLogCohomology) = Submodule.Quotient.mk h := by
  apply deningerMeyerCohomology_eq_of_XiJets_eq
  intro rho j
  rw [deningerMeyerXiSupportJetEvaluationLM_mk, deningerMeyerXiSupportJetEvaluationLM_mk]
  have hf : (j.val.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j.val
  have hm := congrArg (fun z : ℂ => z * (j.val.factorial : ℂ)) (he rho j)
  simpa only [deningerMeyerHasseMoment, div_mul_cancel₀ _ hf] using hm

/-- Actual source multiplication is coordinatewise truncated polynomial multiplication. -/
theorem meyerHasseJetSource_product_moment
    (rho sigma : XiDivisorSupport) (j : DeningerArithmeticJetIndex rho)
    (k : DeningerArithmeticJetIndex sigma) (tau : XiDivisorSupport)
    (i : DeningerArithmeticJetIndex tau) :
    deningerMeyerHasseMoment
      (deningerMeyerSourceConvolution (meyerHasseJetSource rho j) (meyerHasseJetSource sigma k))
      i.val (tau : ℂ) =
        if tau = rho ∧ tau = sigma ∧ i.val = j.val + k.val then 1 else 0 := by
  rw [deningerMeyerHasseMoment_convolution]
  by_cases h : tau = rho ∧ tau = sigma ∧ i.val = j.val + k.val
  · rw [if_pos h, Finset.sum_eq_single j.val]
    · have hj : j.val < xiSupportMultiplicity tau := by
        rw [h.1]
        exact j.isLt
      have hk : i.val - j.val < xiSupportMultiplicity tau :=
        lt_of_le_of_lt (Nat.sub_le _ _) i.isLt
      have hsub : i.val - j.val = k.val := by omega
      rw [meyerHasseJetSource_moment rho j tau ⟨j.val, hj⟩,
        meyerHasseJetSource_moment sigma k tau ⟨i.val - j.val, hk⟩,
        if_pos ⟨h.1, rfl⟩, if_pos ⟨h.2.1, hsub⟩, one_mul]
    · intro a ha hne
      have halt : a < xiSupportMultiplicity tau :=
        lt_of_le_of_lt (Nat.le_of_lt_succ (Finset.mem_range.mp ha)) i.isLt
      rw [meyerHasseJetSource_moment rho j tau ⟨a, halt⟩,
        if_neg (fun he => hne he.2), zero_mul]
    · intro hj
      exact False.elim (hj (Finset.mem_range.mpr (by omega)))
  · rw [if_neg h]
    apply Finset.sum_eq_zero
    intro a ha
    have hai : a ≤ i.val := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    have halt : a < xiSupportMultiplicity tau := lt_of_le_of_lt hai i.isLt
    have hslt : i.val - a < xiSupportMultiplicity tau :=
      lt_of_le_of_lt (Nat.sub_le _ _) i.isLt
    rw [meyerHasseJetSource_moment rho j tau ⟨a, halt⟩,
      meyerHasseJetSource_moment sigma k tau ⟨i.val - a, hslt⟩]
    by_cases hfirst : tau = rho ∧ a = j.val
    · have hsecond : ¬ (tau = sigma ∧ i.val - a = k.val) := by
        rintro ⟨hs, hk⟩
        exact h ⟨hfirst.1, hs, by omega⟩
      rw [if_pos hfirst, if_neg hsecond, mul_zero]
    · rw [if_neg hfirst, zero_mul]

/-- The normalized source class is a basis monomial in its genuine finite jet block. -/
def meyerHasseJetClass (rho : XiDivisorSupport) (j : DeningerArithmeticJetIndex rho) :
    DeningerMeyerStrongLogCohomology := Submodule.Quotient.mk (meyerHasseJetSource rho j)

/-- Distinct divisor blocks have zero product in genuine cohomology. -/
theorem meyerHasseJetClass_product_distinct
    (rho sigma : XiDivisorSupport) (hne : rho ≠ sigma)
    (j : DeningerArithmeticJetIndex rho) (k : DeningerArithmeticJetIndex sigma) :
    deningerMeyerCohomologyConvolution (meyerHasseJetClass rho j) (meyerHasseJetClass sigma k) = 0 := by
  change (Submodule.Quotient.mk
    (deningerMeyerSourceConvolution (meyerHasseJetSource rho j) (meyerHasseJetSource sigma k)) :
      DeningerMeyerStrongLogCohomology) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  apply (meyerSource_boundary_iff_jets_zero _).mpr
  intro tau i
  have hm := meyerHasseJetSource_product_moment rho sigma j k tau i
  have hn : ¬ (tau = rho ∧ tau = sigma ∧ i.val = j.val + k.val) := by
    rintro ⟨hr, hs, _⟩
    exact hne (hr.symm.trans hs)
  rw [if_neg hn] at hm
  have hf : (i.val.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i.val
  have he := congrArg (fun z : ℂ => z * (i.val.factorial : ℂ)) hm
  simpa only [deningerMeyerHasseMoment, div_mul_cancel₀ _ hf, zero_mul] using he

/-- Products below the local multiplicity add Hasse orders without any coefficient. -/
theorem meyerHasseJetClass_product_same
    (rho : XiDivisorSupport) (j k : DeningerArithmeticJetIndex rho)
    (hlt : j.val + k.val < xiSupportMultiplicity rho) :
    deningerMeyerCohomologyConvolution (meyerHasseJetClass rho j) (meyerHasseJetClass rho k) =
      meyerHasseJetClass rho ⟨j.val + k.val, hlt⟩ := by
  apply meyerSourceClass_eq_of_hasse_moments_eq
    (deningerMeyerSourceConvolution (meyerHasseJetSource rho j) (meyerHasseJetSource rho k))
    (meyerHasseJetSource rho ⟨j.val + k.val, hlt⟩)
  intro tau i
  rw [meyerHasseJetSource_product_moment, meyerHasseJetSource_moment]
  by_cases h : tau = rho <;> simp only [h, true_and, false_and, ↓reduceIte]

/-- Products at or above the local multiplicity are genuinely principal. -/
theorem meyerHasseJetClass_product_truncated
    (rho : XiDivisorSupport) (j k : DeningerArithmeticJetIndex rho)
    (hge : xiSupportMultiplicity rho ≤ j.val + k.val) :
    deningerMeyerCohomologyConvolution (meyerHasseJetClass rho j) (meyerHasseJetClass rho k) = 0 := by
  change (Submodule.Quotient.mk
    (deningerMeyerSourceConvolution (meyerHasseJetSource rho j) (meyerHasseJetSource rho k)) :
      DeningerMeyerStrongLogCohomology) = 0
  rw [Submodule.Quotient.mk_eq_zero]
  apply (meyerSource_boundary_iff_jets_zero _).mpr
  intro tau i
  have hm := meyerHasseJetSource_product_moment rho rho j k tau i
  have hn : ¬ (tau = rho ∧ tau = rho ∧ i.val = j.val + k.val) := by
    rintro ⟨rfl, _, hi⟩
    have hib := i.isLt
    omega
  rw [if_neg hn] at hm
  have hf : (i.val.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i.val
  have he := congrArg (fun z : ℂ => z * (i.val.factorial : ℂ)) hm
  simpa only [deningerMeyerHasseMoment, div_mul_cancel₀ _ hf, zero_mul] using he

/-- The zeroth Hasse class is an identity on its own finite jet block. -/
theorem meyerHasseJetClass_product_unit
    (rho : XiDivisorSupport) (j : DeningerArithmeticJetIndex rho) :
    deningerMeyerCohomologyConvolution (meyerHasseJetClass rho j)
      (meyerHasseJetClass rho ⟨0, xiSupportMultiplicity_pos rho⟩) = meyerHasseJetClass rho j := by
  have h := meyerHasseJetClass_product_same rho j ⟨0, xiSupportMultiplicity_pos rho⟩
    (by simpa only [add_zero] using j.isLt)
  simpa only [add_zero] using h

/-- Hasse moments retain the same scalar law as the underlying raw jets. -/
theorem meyerHasseMoment_smul (c : ℂ) (g : DeningerMeyerStrongLogTarget) (k : ℕ) (s : ℂ) :
    deningerMeyerHasseMoment (c • g) k s = c * deningerMeyerHasseMoment g k s := by
  simp only [deningerMeyerHasseMoment, map_smul, smul_eq_mul, mul_div_assoc]

/-- Arithmetic sharp reflects Hasse coordinates with their parity sign. -/
theorem meyerHasseMoment_sharp (g : DeningerMeyerStrongLogTarget) (k : ℕ)
    (rho : XiDivisorSupport) :
    deningerMeyerHasseMoment (deningerMeyerSourceSharp g) k (rho : ℂ) =
      (-1 : ℂ) ^ k * conj (deningerMeyerHasseMoment g k (meyerLineReflect rho : ℂ)) := by
  rw [deningerMeyerHasseMoment, meyerSourceSharp_jet]
  change (-1 : ℂ) ^ k * conj
      (deningerMeyerStrongLogMellinJetLM k (meyerLineReflect rho : ℂ) g) /
      (k.factorial : ℂ) =
    (-1 : ℂ) ^ k * conj
      (deningerMeyerStrongLogMellinJetLM k (meyerLineReflect rho : ℂ) g / (k.factorial : ℂ))
  rw [map_div₀, map_natCast, mul_div_assoc]

/-- Sharp reflects the actual local polynomial block and signs each monomial by its order. -/
theorem meyerHasseJetClass_sharp (rho : XiDivisorSupport) (j : DeningerArithmeticJetIndex rho) :
    meyerCohomologySharp (meyerHasseJetClass rho j) =
      (-1 : ℂ) ^ j.val • meyerHasseJetClass (meyerLineReflect rho)
        ⟨j.val, by rw [meyerLineReflect_multiplicity]; exact j.isLt⟩ := by
  change (Submodule.Quotient.mk (deningerMeyerSourceSharp (meyerHasseJetSource rho j)) :
    DeningerMeyerStrongLogCohomology) =
      Submodule.Quotient.mk ((-1 : ℂ) ^ j.val • meyerHasseJetSource (meyerLineReflect rho)
        ⟨j.val, by rw [meyerLineReflect_multiplicity]; exact j.isLt⟩)
  apply meyerSourceClass_eq_of_hasse_moments_eq
  intro tau i
  have hi : i.val < xiSupportMultiplicity (meyerLineReflect tau) := by
    rw [meyerLineReflect_multiplicity]
    exact i.isLt
  have heq : meyerLineReflect tau = rho ↔ tau = meyerLineReflect rho := by
    constructor
    · intro h
      rw [← h, meyerLineReflect_sq]
    · intro h
      rw [h, meyerLineReflect_sq]
  rw [meyerHasseMoment_sharp,
    meyerHasseJetSource_moment rho j (meyerLineReflect tau) ⟨i.val, hi⟩,
    meyerHasseMoment_smul, meyerHasseJetSource_moment]
  simp only [heq]
  by_cases ht : tau = meyerLineReflect rho
  · by_cases hij : i.val = j.val
    · simp only [ht, hij, and_self, ↓reduceIte, map_one, mul_one]
    · simp only [ht, hij, and_false, ↓reduceIte, map_zero, mul_zero]
  · simp only [ht, false_and, ↓reduceIte, map_zero, mul_zero]

/-- Raw jets of the normalized class have exactly the corresponding factorial. -/
theorem meyerHasseJetClass_raw_jet (rho : XiDivisorSupport)
    (j : DeningerArithmeticJetIndex rho) (sigma : XiDivisorSupport)
    (i : DeningerArithmeticJetIndex sigma) :
    deningerMeyerXiSupportJetEvaluationLM sigma i (meyerHasseJetClass rho j) =
      if sigma = rho ∧ i.val = j.val then (j.val.factorial : ℂ) else 0 := by
  simp only [meyerHasseJetClass, deningerMeyerXiSupportJetEvaluationLM_mk,
    meyerHasseJetSource, map_smul, smul_eq_mul, meyerSingleJetSource_jet]
  split_ifs <;> simp only [mul_one, mul_zero]

private theorem finite_jet_slot_ext {S : Finset XiDivisorSupport}
    (q r : DeningerMeyerFiniteXiJetSlot S) (hr : q.1.1 = r.1.1)
    (hj : q.2.val = r.2.val) : q = r := by
  obtain ⟨⟨rho, hS⟩, i⟩ := q
  obtain ⟨⟨sigma, hT⟩, j⟩ := r
  dsimp only at hr hj ⊢
  subst sigma
  have hi : i = j := Fin.ext hj
  subst j
  rfl

/-- Every canonical finite causal section is its exact finite Hasse expansion. -/
theorem meyerFiniteXiCausalSection_eq_hasse_sum (S : Finset XiDivisorSupport)
    (c : DeningerMeyerFiniteXiJetPacket S) :
    deningerMeyerFiniteXiCausalSection S c =
      ∑ q : DeningerMeyerFiniteXiJetSlot S,
        (c q / (q.2.val.factorial : ℂ)) • meyerHasseJetClass q.1.1 q.2 := by
  apply deningerMeyerCohomology_eq_of_XiJets_eq
  intro rho i
  simp only [map_sum, map_smul, smul_eq_mul, meyerHasseJetClass_raw_jet]
  by_cases hS : rho ∈ S
  · let q : DeningerMeyerFiniteXiJetSlot S := ⟨⟨rho, hS⟩, i⟩
    have he := congrFun (deningerMeyerFiniteXiCausalSection_jets S c) q
    change deningerMeyerXiSupportJetEvaluationLM rho i
      (deningerMeyerFiniteXiCausalSection S c) = c q at he
    rw [he, Finset.sum_eq_single q]
    · have hf : (i.val.factorial : ℂ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero i.val
      simp only [q, and_self, ↓reduceIte, div_mul_cancel₀ _ hf]
    · intro r _ hr
      have hn : ¬ (rho = r.1.1 ∧ i.val = r.2.val) := by
        rintro ⟨hri, hji⟩
        exact hr (finite_jet_slot_ext r q hri.symm hji.symm)
      rw [if_neg hn, mul_zero]
    · intro hq
      exact False.elim (hq (Finset.mem_univ q))
  · rw [deningerMeyerFiniteXiCausalSection_other_jet_zero S rho hS i]
    symm
    apply Finset.sum_eq_zero
    intro q _
    have hn : ¬ (rho = q.1.1 ∧ i.val = q.2.val) := by
      rintro ⟨hr, _⟩
      exact hS (hr.symm ▸ q.1.2)
    rw [if_neg hn, mul_zero]

end GaloisForLFunctions.ArithmeticCastelnuovoSeveri
