import GaloisForLFunctions.HilbertMetric.QuantumInformation.Recovery.ChainErasureMask
import GaloisForLFunctions.HTGeometry.HermitianTraceNorm

/-!
# The conditional state of one site in a sequential qubit chain

Two runs of ones have equal erased words and differ at the retained site
only for the pair of consecutive run lengths straddling that site.
This gives the off-diagonal term in Kanno and Soda (arXiv:2611.26368,
Eq. 7.7) for arbitrary complex amplitudes.
-/

open scoped BigOperators ComplexOrder Matrix MatrixOrder

namespace GaloisForLFunctions.HilbertMetric.QuantumInformation.ReadyBranch

open GaloisForLFunctions.HTGeometry

noncomputable section

private theorem extend_eq_sum {J X : Type*} [Fintype J] [DecidableEq X]
    (f : J ↪ X) (A : J → ℂ) (x : X) :
    Function.extend f A (0 : X → ℂ) x = ∑ j, if f j = x then A j else 0 := by
  by_cases hx : ∃ j, f j = x
  · obtain ⟨j, rfl⟩ := hx
    rw [f.injective.extend_apply, Finset.sum_eq_single j]
    · simp only [if_true]
    · intro k _ hk
      exact if_neg (fun he => hk (f.injective he))
    · exact fun h => (h (Finset.mem_univ _)).elim
  · rw [Function.extend_apply' A (0 : X → ℂ) x hx, Pi.zero_apply]
    exact (Finset.sum_eq_zero fun j _ => if_neg (fun hj => hx ⟨j, hj⟩)).symm

/-- Partial trace of a pure state whose nonzero coordinates lie in the image
of a given embedding into lost and available words. -/
def sparseReduction {J L F : Type*} [Fintype L]
    (f : J ↪ L × F) (A : J → ℂ) : Matrix F F ℂ :=
  fun x y => ∑ l, Function.extend f A 0 (l, x) * star (Function.extend f A 0 (l, y))

/-- The trace keeps exactly the amplitude pairs with equal erased coordinates. -/
theorem sparseReduction_entry {J L F : Type*} [Fintype J] [Fintype L]
    [DecidableEq L] [DecidableEq F] (f : J ↪ L × F) (A : J → ℂ) (x y : F) :
    sparseReduction f A x y =
      ∑ j, ∑ k, if (f j).1 = (f k).1 ∧ (f j).2 = x ∧ (f k).2 = y then A j * star (A k) else 0 := by
  let t (j k : J) (l : L) :=
    (if f j = (l, x) then A j else 0) * star (if f k = (l, y) then A k else 0)
  calc
    _ = ∑ l, ∑ j, ∑ k, t j k l := by
      simp only [sparseReduction, extend_eq_sum, star_sum, Finset.sum_mul, Finset.mul_sum, t]
      exact Finset.sum_congr rfl fun l _ => Finset.sum_comm
    _ = ∑ j, ∑ k, ∑ l, t j k l := by
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_comm
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j _
      apply Finset.sum_congr rfl
      intro k _
      rw [Finset.sum_eq_single (f j).1]
      · have hj : f j = ((f j).1, x) ↔ (f j).2 = x :=
          ⟨fun h => congrArg Prod.snd h, fun h => Prod.ext rfl h⟩
        have hk : f k = ((f j).1, y) ↔ (f j).1 = (f k).1 ∧ (f k).2 = y :=
          ⟨fun h => ⟨(congrArg Prod.fst h).symm, congrArg Prod.snd h⟩,
            fun h => Prod.ext h.1.symm h.2⟩
        simp only [t, hj, hk]
        by_cases hl : (f j).1 = (f k).1 <;> by_cases hx : (f j).2 = x <;>
          by_cases hy : (f k).2 = y <;> simp [hl, hx, hy]
      · intro l _ hl
        have hj : f j ≠ (l, x) := fun h => hl (congrArg Prod.fst h).symm
        simp only [t, if_neg hj, zero_mul]
      · exact fun h => (h (Finset.mem_univ _)).elim

/-- The observed diagonal is the distribution of the available label. -/
theorem sparseReduction_diag {J L F : Type*} [Fintype J] [Fintype L]
    [DecidableEq L] [DecidableEq F] (f : J ↪ L × F) (A : J → ℂ) (x : F) :
    sparseReduction f A x x =
      ∑ j, if (f j).2 = x then ((‖A j‖ ^ 2 : ℝ) : ℂ) else 0 := by
  rw [sparseReduction_entry]
  apply Finset.sum_congr rfl
  intro j _
  rw [Finset.sum_eq_single j]
  · simp [Complex.mul_conj, Complex.sq_norm]
  · intro k _ hkj
    apply if_neg
    intro h
    exact hkj (f.injective (Prod.ext h.1.symm (h.2.2.trans h.2.1.symm)))
  · exact fun h => (h (Finset.mem_univ _)).elim

private theorem sparseReduction_star_swap {J L F : Type*} [Fintype L]
    (f : J ↪ L × F) (A : J → ℂ) (x y : F) :
    star (sparseReduction f A x y) = sparseReduction f A y x := by
  simp only [sparseReduction, star_sum, star_mul, star_star]

variable {n : ℕ}

/-- Restrict the full erased-word embedding to a single retained site. -/
def singleSiteSignature (s : Fin n) : Fin (n + 1) ↪
    RunLost ({s} : Finset (Fin n)) × Bool :=
  (runSignature {s}).trans
    { toFun := fun p => (p.1, p.2 ⟨s, Finset.mem_singleton_self s⟩)
      inj' := by
        intro p q h
        obtain ⟨hl, hb⟩ := Prod.mk.inj h
        refine Prod.ext hl (funext fun i => ?_)
        have hi : i = ⟨s, Finset.mem_singleton_self s⟩ :=
          Subtype.ext (Finset.mem_singleton.mp i.2)
        rw [hi]
        exact hb }

private theorem singleSiteSignature_lost_eq_iff (s : Fin n) (j k : Fin (n + 1))
    (hjk : j.val ≤ k.val) :
    (singleSiteSignature s j).1 = (singleSiteSignature s k).1 ↔
      ∀ i : Fin n, j.val ≤ i.val → i.val < k.val → i = s := by
  constructor
  · intro he i hij hik
    by_contra his
    let t : {i : Fin n // i ∉ ({s} : Finset (Fin n))} :=
      ⟨i, fun h => his (Finset.mem_singleton.mp h)⟩
    have ht := congrFun he t
    change decide (i.val < j.val) = decide (i.val < k.val) at ht
    rw [decide_eq_false (not_lt_of_ge hij), decide_eq_true hik] at ht
    exact Bool.false_ne_true ht
  · intro h
    funext t
    change decide (t.val.val < j.val) = decide (t.val.val < k.val)
    congr 1
    exact propext ⟨fun ht => ht.trans_le hjk, fun ht => by
      by_contra hnot
      exact t.2 (Finset.mem_singleton.mpr (h t.val (le_of_not_gt hnot) ht))⟩

/-- The only retained/off-diagonal pair with an identical lost word is
a run ending at the site and the run ending one step earlier. -/
theorem singleSiteSignature_cross_iff (s : Fin n) (j k : Fin (n + 1)) :
    (singleSiteSignature s j).1 = (singleSiteSignature s k).1 ∧
      (singleSiteSignature s j).2 = true ∧ (singleSiteSignature s k).2 = false ↔
      j = s.succ ∧ k = s.castSucc := by
  constructor
  · rintro ⟨he, hj, hk⟩
    have hj' : s.val < j.val := of_decide_eq_true hj
    have hk' : k.val ≤ s.val := le_of_not_gt (of_decide_eq_false hk)
    have hinterval := (singleSiteSignature_lost_eq_iff s k j (hk'.trans hj'.le)).mp he.symm
    let i : Fin n := ⟨k.val, hk'.trans_lt s.isLt⟩
    have hfirst : k.val = s.val := congrArg Fin.val
      (hinterval i le_rfl (hk'.trans_lt hj'))
    let i' : Fin n := ⟨j.val - 1, by have := j.isLt; omega⟩
    have hk_i : k.val ≤ i'.val := by change k.val ≤ j.val - 1; omega
    have hi_j : i'.val < j.val := by change j.val - 1 < j.val; omega
    have hlast : j.val - 1 = s.val := congrArg Fin.val (hinterval i' hk_i hi_j)
    exact ⟨Fin.ext (show j.val = s.val + 1 by omega), Fin.ext hfirst⟩
  · rintro ⟨rfl, rfl⟩
    have he := (singleSiteSignature_lost_eq_iff s s.castSucc s.succ
      (Nat.le_succ s.val)).mpr (fun i hi₁ hi₂ => Fin.ext (by
        change s.val ≤ i.val at hi₁
        change i.val < s.val + 1 at hi₂
        omega))
    exact ⟨he.symm, decide_eq_true (Nat.lt_succ_self s.val), decide_eq_false (Nat.lt_irrefl _)⟩

/-- The input-one reduced density matrix of the single retained qubit. -/
def siteConditionalDensity (A : RunAmplitudes n) (s : Fin n) : Matrix Bool Bool ℂ :=
  sparseReduction (singleSiteSignature s) A.1

theorem siteConditionalDensity_posSemidef (A : RunAmplitudes n) (s : Fin n) :
    (siteConditionalDensity A s).PosSemidef := by
  let v (l : RunLost ({s} : Finset (Fin n))) (b : Bool) :=
    Function.extend (singleSiteSignature s) A.1 0 (l, b)
  have he : siteConditionalDensity A s = ∑ l, Matrix.vecMulVec (v l) (star (v l)) := by
    ext i j
    simp only [siteConditionalDensity, sparseReduction, Matrix.sum_apply, Matrix.vecMulVec,
      Matrix.of_apply, Pi.star_apply, v]
  rw [he]
  exact Matrix.posSemidef_sum _ (fun l _ => Matrix.posSemidef_vecMulVec_self_star (v l))

/-- Excited population of the retained site. -/
def siteExcitedPopulation (A : RunAmplitudes n) (s : Fin n) : ℝ :=
  ∑ j, if s.val < j.val then ‖A.1 j‖ ^ 2 else 0

theorem siteConditionalDensity_true_true (A : RunAmplitudes n) (s : Fin n) :
    siteConditionalDensity A s true true = (siteExcitedPopulation A s : ℂ) := by
  unfold siteConditionalDensity siteExcitedPopulation
  rw [sparseReduction_diag, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro j _
  change (if decide (s.val < j.val) = true then ((‖A.1 j‖ ^ 2 : ℝ) : ℂ) else 0) =
    ((if s.val < j.val then ‖A.1 j‖ ^ 2 else 0 : ℝ) : ℂ)
  by_cases h : s.val < j.val <;> simp [h]

/-- The coherence is the product of the two consecutive run amplitudes. -/
theorem siteConditionalDensity_true_false (A : RunAmplitudes n) (s : Fin n) :
    siteConditionalDensity A s true false = A.1 s.succ * star (A.1 s.castSucc) := by
  classical
  unfold siteConditionalDensity
  rw [sparseReduction_entry]
  simp only [singleSiteSignature_cross_iff]
  rw [Finset.sum_eq_single s.succ]
  · rw [Finset.sum_eq_single s.castSucc]
    · simp
    · intro k _ hk
      simp [hk]
    · exact fun h => (h (Finset.mem_univ _)).elim
  · intro j _ hj
    simp [hj]
  · exact fun h => (h (Finset.mem_univ _)).elim

theorem siteConditionalDensity_false_true (A : RunAmplitudes n) (s : Fin n) :
    siteConditionalDensity A s false true =
      star (A.1 s.succ * star (A.1 s.castSucc)) := by
  rw [← siteConditionalDensity_true_false]
  exact (sparseReduction_star_swap (singleSiteSignature s) A.1 true false).symm

theorem siteConditionalDensity_false_false (A : RunAmplitudes n) (s : Fin n) :
    siteConditionalDensity A s false false = 1 - (siteExcitedPopulation A s : ℂ) := by
  apply eq_sub_of_add_eq
  rw [← siteConditionalDensity_true_true]
  unfold siteConditionalDensity
  rw [sparseReduction_diag, sparseReduction_diag, ← Finset.sum_add_distrib]
  calc
    _ = ∑ j, ((‖A.1 j‖ ^ 2 : ℝ) : ℂ) := by
      apply Finset.sum_congr rfl
      intro j _
      cases (singleSiteSignature s j).2 <;> simp
    _ = 1 := by
      rw [← Complex.ofReal_sum, ← show cnormSq A.1 = ∑ j, ‖A.1 j‖ ^ 2 from rfl, A.2]
      exact Complex.ofReal_one

theorem siteConditionalDensity_trace (A : RunAmplitudes n) (s : Fin n) :
    (siteConditionalDensity A s).trace = 1 := by
  rw [Matrix.trace, Fintype.sum_bool]
  change siteConditionalDensity A s true true + siteConditionalDensity A s false false = 1
  rw [siteConditionalDensity_true_true, siteConditionalDensity_false_false]
  ring

/-- A later site can carry a perfect population record while its erased
prefix destroys all coherence available for recovery from that site. -/
theorem exists_perfectSiteRecord_zero_ready_mass (s : Fin n) (hs : s.val ≠ 0) :
    ∃ A : RunAmplitudes n,
      siteConditionalDensity A s true true = 1 ∧ maskedRunMass ({s} : Finset (Fin n)) A = 0 := by
  let a (j : Fin (n + 1)) : ℂ := if j = s.succ then 1 else 0
  have ha : cnormSq a = 1 := by
    unfold cnormSq
    rw [Finset.sum_eq_single s.succ]
    · simp [a]
    · intro j _ hj
      simp [a, hj]
    · exact fun h => (h (Finset.mem_univ _)).elim
  let A : RunAmplitudes n := ⟨a, ha⟩
  refine ⟨A, ?_, ?_⟩
  · rw [siteConditionalDensity_true_true, siteExcitedPopulation, Finset.sum_eq_single s.succ]
    · simp [A, a]
    · intro j _ hj
      simp [A, a, hj]
    · exact fun h => (h (Finset.mem_univ _)).elim
  · let i : Fin n := ⟨0, (Nat.zero_le s.val).trans_lt s.isLt⟩
    have hm : i ∉ ({s} : Finset (Fin n)) :=
      fun h => hs (congrArg Fin.val (Finset.mem_singleton.mp h)).symm
    have hi : accessiblePrefixLength ({s} : Finset (Fin n)) = 0 :=
      Nat.le_zero.mp (accessiblePrefixLength_le_of_missing hm)
    unfold maskedRunMass
    rw [hi]
    apply Finset.sum_eq_zero
    intro j _
    by_cases hj : j = s.succ
    · subst j
      simp
    · simp [A, a, hj]

/-- The reference branch puts the retained site in its zero state. -/
def siteReferenceDensity : Matrix Bool Bool ℂ := Matrix.diagonal (fun b => if b then 0 else 1)

/-- The input-zero density minus the input-one density of the retained site. -/
def siteRecordDifference (A : RunAmplitudes n) (s : Fin n) : Matrix Bool Bool ℂ :=
  siteReferenceDensity - siteConditionalDensity A s

private def qubitRecordDifference (p : ℝ) (z : ℂ) : Matrix Bool Bool ℂ
  | false, false => p
  | true, true => -(p : ℂ)
  | true, false => -z
  | false, true => -star z

private theorem siteRecordDifference_eq (A : RunAmplitudes n) (s : Fin n) :
    siteRecordDifference A s =
      qubitRecordDifference (siteExcitedPopulation A s) (A.1 s.succ * star (A.1 s.castSucc)) := by
  ext i j
  cases i <;> cases j <;>
    simp [siteRecordDifference, siteReferenceDensity, qubitRecordDifference, Matrix.sub_apply,
      siteConditionalDensity_true_true, siteConditionalDensity_true_false,
      siteConditionalDensity_false_true, siteConditionalDensity_false_false]

private theorem qubitRecordDifference_isHermitian (p : ℝ) (z : ℂ) :
    (qubitRecordDifference p z).IsHermitian := by
  apply Matrix.ext
  intro i j
  cases i <;> cases j <;>
    simp [qubitRecordDifference, Matrix.conjTranspose_apply]

private theorem qubitRecordDifference_square (p : ℝ) (z : ℂ) :
    qubitRecordDifference p z * qubitRecordDifference p z =
      (p ^ 2 + ‖z‖ ^ 2) • (1 : Matrix Bool Bool ℂ) := by
  have hz₁ : z * (starRingEnd ℂ) z = ((‖z‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.sq_norm]
  have hz₂ : (starRingEnd ℂ) z * z = ((‖z‖ ^ 2 : ℝ) : ℂ) :=
    (mul_comm _ _).trans hz₁
  ext i j
  rw [Matrix.mul_apply, Fintype.sum_bool]
  cases i <;> cases j <;>
    simp [qubitRecordDifference, Matrix.smul_apply, Complex.real_smul,
      Complex.ofReal_add, Complex.ofReal_pow, hz₁, hz₂] <;> ring

/-- The distance of the two conditional site states, with arbitrary complex amplitudes. -/
def siteReadoutDistance (A : RunAmplitudes n) (s : Fin n) : ℝ :=
  Real.sqrt (siteExcitedPopulation A s ^ 2 + ‖A.1 s.succ * star (A.1 s.castSucc)‖ ^ 2)

/-- Half the trace norm combines the population with the two-run coherence in quadrature. -/
theorem siteRecordDifference_half_trace_norm (A : RunAmplitudes n) (s : Fin n) :
    finiteMatrixNuclearNorm (siteRecordDifference A s) / 2 = siteReadoutDistance A s := by
  let r := siteReadoutDistance A s
  let D := siteRecordDifference A s
  have hD : D.IsHermitian := by
    rw [show D = siteRecordDifference A s from rfl, siteRecordDifference_eq]
    exact qubitRecordDifference_isHermitian _ _
  have hr : 0 ≤ r := Real.sqrt_nonneg _
  have hs : r ^ 2 = siteExcitedPopulation A s ^ 2 + ‖A.1 s.succ * star (A.1 s.castSucc)‖ ^ 2 :=
    Real.sq_sqrt (add_nonneg (sq_nonneg _) (sq_nonneg _))
  have hD₂ : D * D = r ^ 2 • (1 : Matrix Bool Bool ℂ) := by
    rw [show D = siteRecordDifference A s from rfl, siteRecordDifference_eq, hs]
    exact qubitRecordDifference_square _ _
  have hroot : (r • (1 : Matrix Bool Bool ℂ)).PosSemidef := Matrix.PosSemidef.one.smul hr
  have hroot₂ : (r • (1 : Matrix Bool Bool ℂ)) * (r • 1) = Dᴴ * D := by
    rw [hD.eq, hD₂, smul_mul_assoc, Matrix.one_mul, smul_smul, pow_two]
  change finiteMatrixNuclearNorm D / 2 = r
  rw [finiteMatrixNuclearNorm_eq_trace_sqrt_re, CFC.sqrt_unique hroot₂ hroot.nonneg,
    Matrix.trace_smul, Matrix.trace_one]
  simp [Fintype.card_bool, Complex.real_smul, Complex.mul_re]

/-- Equal-prior success probability from the two Born weights for the
effects (1 + Y)/2 and (1 - Y)/2. -/
def siteRecordMeasurementSuccess (A : RunAmplitudes n) (s : Fin n) (Y : Matrix Bool Bool ℂ) : ℝ :=
  ((siteReferenceDensity * ((1 / 2 : ℝ) • (1 + Y))).trace.re +
    (siteConditionalDensity A s * ((1 / 2 : ℝ) • (1 - Y))).trace.re) / 2

/-- A Hermitian contraction defines two positive effects summing to the identity. -/
theorem siteRecordMeasurement_effects {Y : Matrix Bool Bool ℂ} (hY : IsHermContraction Y) :
    (((1 / 2 : ℝ) • (1 + Y)).PosSemidef) ∧ (((1 / 2 : ℝ) • (1 - Y)).PosSemidef) ∧
      (1 / 2 : ℝ) • (1 + Y) + (1 / 2 : ℝ) • (1 - Y) = (1 : Matrix Bool Bool ℂ) := by
  have hp : (1 + Y).PosSemidef := by
    simpa only [sub_neg_eq_add, add_comm] using Matrix.le_iff.mp hY.neg_one_le
  refine ⟨hp.smul (by positivity), (Matrix.le_iff.mp hY.le_one).smul (by positivity), ?_⟩
  rw [← smul_add]
  have he : (1 + Y) + (1 - Y) = (2 : ℝ) • (1 : Matrix Bool Bool ℂ) := by
    rw [two_smul]
    abel
  rw [he, smul_smul]
  norm_num

theorem siteRecordMeasurementSuccess_eq (A : RunAmplitudes n) (s : Fin n)
    (Y : Matrix Bool Bool ℂ) :
    siteRecordMeasurementSuccess A s Y = (1 + ((siteRecordDifference A s * Y).trace).re / 2) / 2 := by
  have h₀ : siteReferenceDensity.trace = 1 := by
    simp [siteReferenceDensity, Matrix.trace]
  unfold siteRecordMeasurementSuccess siteRecordDifference
  rw [mul_smul_comm, mul_smul_comm, Matrix.mul_add, Matrix.mul_sub, Matrix.sub_mul,
    Matrix.mul_one, Matrix.mul_one, Matrix.trace_smul, Matrix.trace_smul,
    Matrix.trace_add, Matrix.trace_sub, Matrix.trace_sub, h₀, siteConditionalDensity_trace]
  simp only [Complex.real_smul, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    zero_mul, sub_zero, Complex.add_re, Complex.sub_re, Complex.one_re]
  ring

/-- The equal-prior binary readout has an attained Helstrom optimum.
The observable Y describes a binary measurement with effects (1 ± Y)/2. -/
theorem siteRecord_optimal_readout (A : RunAmplitudes n) (s : Fin n) :
    (∀ Y : Matrix Bool Bool ℂ, IsHermContraction Y →
      siteRecordMeasurementSuccess A s Y ≤ (1 + siteReadoutDistance A s) / 2) ∧
    ∃ Y : Matrix Bool Bool ℂ, IsHermContraction Y ∧
      siteRecordMeasurementSuccess A s Y = (1 + siteReadoutDistance A s) / 2 := by
  have hD : (siteRecordDifference A s).IsHermitian := by
    rw [siteRecordDifference_eq]
    exact qubitRecordDifference_isHermitian _ _
  have hd := siteRecordDifference_half_trace_norm A s
  constructor
  · intro Y hY
    rw [siteRecordMeasurementSuccess_eq]
    have h := re_trace_mul_le_nuclearNorm hD hY
    linarith only [h, hd]
  · obtain ⟨Y, hY, he⟩ := exists_isHermContraction_re_trace_eq hD
    exact ⟨Y, hY, by rw [siteRecordMeasurementSuccess_eq]; linarith only [he, hd]⟩

#print axioms sparseReduction_entry
#print axioms siteConditionalDensity_true_false
#print axioms siteConditionalDensity_false_false
#print axioms exists_perfectSiteRecord_zero_ready_mass
#print axioms siteRecordDifference_half_trace_norm
#print axioms siteRecord_optimal_readout

end

end GaloisForLFunctions.HilbertMetric.QuantumInformation.ReadyBranch
