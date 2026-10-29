import GaloisForLFunctions.SignedArithmeticHodgeTheory.GeneratorCutoffsAreLogarithmicBlockAverages
import GaloisForLFunctions.ArithmeticIndexDescent.TheCenteredSquareSourceHasAGammaMassBound

/-!
# Actual finite generator heads preserve the source mean

The whole-orbit cutoff acts on a finite real cell source as a finite real
compact BV profile. Its integral is unchanged. Its discarded profile has
zero mean and is orthogonal to the head in ordinary square mass. Both
centering corrections in the square-prime mixed source therefore cancel
on the literal physical profiles.
-/

noncomputable section
open MeasureTheory Set Filter RHTower
open scoped InnerProductSpace

namespace GaloisForLFunctions.SignedArithmeticHodgeTheory
open HTGeometry ArithmeticCastelnuovoSeveri.LogCells BiarithmeticGaugeGeometry
open ArithmeticIndexDescent

local notation "CellH" => lp (fun _ : ℕ+ => ℂ) 2
local notation "LineH" => Lp ℂ 2 (volume : Measure ℝ)
local notation "U" => wholeLineLogCellEmbedding
local notation "P" => logCellGeneratorHead
local notation "e" => fun n : ℕ+ => (lp.single 2 n (1 : ℂ) : CellH)

private theorem bv_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hv : ∀ i, BoundedVariationOn (f i) univ) :
    BoundedVariationOn (fun x => ∑ i ∈ s, f i x) univ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simpa only [Finset.sum_empty] using
      ((monotone_const : Monotone (fun _ : ℝ => (0 : ℝ))).monotoneOn univ).boundedVariationOn
        (C := 0) (fun _ _ => by simp)
  | insert i s hi ih =>
    have h := boundedVariationOn_sub (hv i) (bv_const_mul (-1) ih)
    simpa only [Finset.sum_insert hi, neg_one_mul, sub_neg_eq_add] using h

private theorem compact_finset_sum {ι : Type*} (s : Finset ι) (f : ι → ℝ → ℝ)
    (hc : ∀ i, HasCompactSupport (f i)) : HasCompactSupport (fun x => ∑ i ∈ s, f i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa only [Finset.sum_empty] using (HasCompactSupport.zero : HasCompactSupport (0 : ℝ → ℝ))
  | insert i s hi ih => simpa only [Finset.sum_insert hi] using (hc i).add ih

variable {ι : Type*} [Fintype ι]

/-- A finite family of original real cell heights; repeated labels are allowed. -/
def finiteLogCellProfile (n : ι → ℕ+) (c : ι → ℝ) (x : ℝ) : ℝ :=
  ∑ i, c i * rawCell (n i) x

/-- The same source in the original orthonormal cell coordinates. -/
def finiteLogCellVector (n : ι → ℕ+) (c : ι → ℝ) : CellH :=
  ∑ i, ((c i * Real.sqrt (logCell (n i)) : ℝ) : ℂ) • e (n i)

theorem finiteLogCellProfile_bv (n : ι → ℕ+) (c : ι → ℝ) :
    BoundedVariationOn (finiteLogCellProfile n c) univ :=
  bv_finset_sum _ _ (fun i => bv_const_mul _ (rawCell_bv _))

theorem finiteLogCellProfile_compact (n : ι → ℕ+) (c : ι → ℝ) :
    HasCompactSupport (finiteLogCellProfile n c) :=
  compact_finset_sum _ _ (fun i => (rawCell_compact (n i)).mul_left)

theorem integrable_finiteLogCellProfile (n : ι → ℕ+) (c : ι → ℝ) :
    Integrable (finiteLogCellProfile n c) :=
  integrable_finset_sum _ (fun i _ => (integrable_rawCell (n i)).const_mul (c i))

/-- The actual source integral is its logarithmic cell mass. -/
theorem integral_finiteLogCellProfile (n : ι → ℕ+) (c : ι → ℝ) :
    (∫ x, finiteLogCellProfile n c x) = ∑ i, c i * logCell (n i) := by
  rw [finiteLogCellProfile, integral_finsetSum _ (fun i _ => (integrable_rawCell (n i)).const_mul (c i))]
  apply Finset.sum_congr rfl
  intro i _
  rw [integral_const_mul, integral_rawCell (n i).pos]
  rfl

private theorem finiteLogCellProfile_zero_neg (n : ι → ℕ+) (c : ι → ℝ) {x : ℝ} (hx : x < 0) :
    finiteLogCellProfile n c x = 0 := by
  apply Finset.sum_eq_zero
  intro i _
  have hi : x ∉ Ico (Real.log (n i)) (Real.log ((n i : ℕ) + 1)) := by
    intro h
    have hn := Real.log_nonneg (by exact_mod_cast (n i).pos : (1 : ℝ) ≤ (n i))
    exact (not_le_of_gt hx) (hn.trans h.1)
  rw [rawCell, indicator_of_notMem hi, mul_zero]

private theorem halfLine_finiteLogCellProfile (n : ι → ℕ+) (c : ι → ℝ) :
    ((∑ i, (c i : ℂ) • cellAtom (n i) : Lp ℂ 2 halfLineMeasure) : ℝ → ℂ) =ᵐ[halfLineMeasure]
      fun x => (finiteLogCellProfile n c x : ℂ) := by
  have hs := coeFn_finset_sum_smul Finset.univ (fun i => (c i : ℂ)) (fun i => cellAtom (n i))
  have ha := ae_all_iff.mpr (fun i : ι => cellAtom_coeFn (n i))
  filter_upwards [hs, ha] with x hx ha
  rw [hx, finiteLogCellProfile, Complex.ofReal_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [ha i, Complex.ofReal_mul]
  congr 1
  simp only [rawCell, indicator_apply]
  split_ifs <;> rfl

/-- Finite real cell coordinates realize the literal compact BV profile. -/
theorem realSourceLp_finiteLogCellProfile (n : ι → ℕ+) (c : ι → ℝ) :
    realSourceLp (finiteLogCellProfile n c) (finiteLogCellProfile_bv n c)
        (finiteLogCellProfile_compact n c) = U (finiteLogCellVector n c) := by
  have hu : U (finiteLogCellVector n c) = halfLineExtend (∑ i, (c i : ℂ) • cellAtom (n i)) := by
    change halfLineExtend (logCellEmbedding (finiteLogCellVector n c)) = _
    congr 1
    rw [finiteLogCellVector, map_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Complex.ofReal_mul, ← smul_smul, map_smul, logCellEmbedding_weighted_single]
  rw [hu]
  apply Lp.ext
  refine (realSourceLp_coeFn _ _ _).trans ?_
  symm
  refine (halfLineExtend_coeFn _).trans
    ((indicator_ae_eq_of_halfLine (halfLine_finiteLogCellProfile n c)).trans (Eventually.of_forall ?_))
  intro x
  by_cases hx : x ∈ Ici (0 : ℝ)
  · exact indicator_of_mem hx _
  · rw [indicator_of_notMem hx, finiteLogCellProfile_zero_neg n c (lt_of_not_ge hx), Complex.ofReal_zero]

/-- Canonical positive labels for the original horizon-indexed complete-cell profile. -/
def wholeCellSourceLabel (X : ℕ) (i : ↥(Finset.Icc 1 X)) : ℕ+ :=
  ⟨i.1, (Finset.mem_Icc.mp i.2).1⟩

/-- Every original complete-cell source is a literal instance of the finite physical interface. -/
theorem finiteLogCellProfile_wholeCell (c : ℕ → ℝ) (X : ℕ) :
    finiteLogCellProfile (wholeCellSourceLabel X) (fun i => c i.1) = wholeCellProfile c X := by
  funext x
  exact Finset.sum_coe_sort (Finset.Icc 1 X) (fun i => c i * rawCell i x)

/-- The finite interface has exactly the original physical logarithmic-cell coordinates. -/
theorem finiteLogCellVector_wholeCell (c : ℕ → ℝ) (X : ℕ) :
    finiteLogCellVector (wholeCellSourceLabel X) (fun i => c i.1) =
      logCellEmbedding.adjoint (cellSection c 1 X) := by
  have h := realSourceLp_finiteLogCellProfile (wholeCellSourceLabel X) (fun i => c i.1)
  rw [finiteLogCellProfile_wholeCell, realSourceLp_wholeCellProfile] at h
  have he := congrArg wholeLineLogCellEmbedding.adjoint h
  simpa only [wholeLineLogCellEmbedding_adjoint_self] using he.symm

/-- The finite original-cell labels in all stopping blocks of the source. -/
def stoppedLogCellLabel (A : ℕ+) (n : ι → ℕ+)
    (i : Σ k : ι, Fin (2 ^ (logCellStoppingAncestor A (n k)).1)) : ℕ+ :=
  logCellDyadicBlockCell (logCellStoppingAncestor A (n i.1)).1
    (logCellStoppingAncestor A (n i.1)).2 i.2

/-- Every cell in the explicit head stays below twice the label of its source cell. -/
theorem stoppedLogCellLabel_lt_twice (A : ℕ+) (n : ι → ℕ+)
    (i : Σ k : ι, Fin (2 ^ (logCellStoppingAncestor A (n k)).1)) :
    (stoppedLogCellLabel A n i : ℕ) < 2 * (n i.1 : ℕ) :=
  lt_twice_of_logCellStopping_block A (n i.1) _ (logCellDyadicBlockCell_div _ _ _)

/-- A source cell contributes its logarithmic mass divided by its stopping-block length. -/
def stoppedLogCellHeight (A : ℕ+) (n : ι → ℕ+) (c : ι → ℝ)
    (i : Σ k : ι, Fin (2 ^ (logCellStoppingAncestor A (n k)).1)) : ℝ :=
  c i.1 * (logCell (n i.1) / logCell (logCellStoppingAncestor A (n i.1)).2)

/-- The actual finite real profile of the whole-orbit generator head. -/
def actualGeneratorHeadProfile (A : ℕ+) (n : ι → ℕ+) (c : ι → ℝ) : ℝ → ℝ :=
  finiteLogCellProfile (stoppedLogCellLabel A n) (stoppedLogCellHeight A n c)

/-- The discarded physical profile, with no cutoff on translation levels. -/
def actualGeneratorTailProfile (A : ℕ+) (n : ι → ℕ+) (c : ι → ℝ) : ℝ → ℝ :=
  finiteLogCellProfile n c - actualGeneratorHeadProfile A n c

theorem actualGeneratorHeadProfile_bv (A : ℕ+) (n : ι → ℕ+) (c : ι → ℝ) :
    BoundedVariationOn (actualGeneratorHeadProfile A n c) univ :=
  finiteLogCellProfile_bv _ _

theorem actualGeneratorHeadProfile_compact (A : ℕ+) (n : ι → ℕ+) (c : ι → ℝ) :
    HasCompactSupport (actualGeneratorHeadProfile A n c) :=
  finiteLogCellProfile_compact _ _

theorem actualGeneratorTailProfile_bv (A : ℕ+) (n : ι → ℕ+) (c : ι → ℝ) :
    BoundedVariationOn (actualGeneratorTailProfile A n c) univ :=
  boundedVariationOn_sub (finiteLogCellProfile_bv n c) (actualGeneratorHeadProfile_bv A n c)

theorem actualGeneratorTailProfile_compact (A : ℕ+) (n : ι → ℕ+) (c : ι → ℝ) :
    HasCompactSupport (actualGeneratorTailProfile A n c) :=
  (finiteLogCellProfile_compact n c).sub (actualGeneratorHeadProfile_compact A n c)

/-- The explicit finite block source is precisely the original Hilbert generator projection. -/
theorem finiteLogCellVector_stopped (A : ℕ+) (n : ι → ℕ+) (c : ι → ℝ) :
    finiteLogCellVector (stoppedLogCellLabel A n) (stoppedLogCellHeight A n c) =
      P A (finiteLogCellVector n c) := by
  classical
  rw [finiteLogCellVector, Fintype.sum_sigma, finiteLogCellVector, map_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Complex.ofReal_mul, ← smul_smul, map_smul,
    logCellGeneratorHead_weighted_single, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro r _
  simp only [stoppedLogCellLabel, stoppedLogCellHeight, smul_smul, Complex.ofReal_mul]
  congr 1
  ring

/-- The actual head has the intended physical realization. -/
theorem realSourceLp_actualGeneratorHead (A : ℕ+) (n : ι → ℕ+) (c : ι → ℝ) :
    realSourceLp (actualGeneratorHeadProfile A n c) (actualGeneratorHeadProfile_bv A n c)
        (actualGeneratorHeadProfile_compact A n c) = U (P A (finiteLogCellVector n c)) := by
  rw [actualGeneratorHeadProfile, realSourceLp_finiteLogCellProfile, finiteLogCellVector_stopped]

/-- Every source cell preserves its literal integral through the all-level cutoff. -/
theorem integral_actualGeneratorHead (A : ℕ+) (n : ι → ℕ+) (c : ι → ℝ) :
    (∫ x, actualGeneratorHeadProfile A n c x) = ∫ x, finiteLogCellProfile n c x := by
  rw [actualGeneratorHeadProfile, integral_finiteLogCellProfile, Fintype.sum_sigma,
    integral_finiteLogCellProfile]
  apply Finset.sum_congr rfl
  intro i _
  simp only [stoppedLogCellHeight, stoppedLogCellLabel, ← Finset.mul_sum]
  have hs : (∑ r : Fin (2 ^ (logCellStoppingAncestor A (n i)).1),
      logCell (logCellDyadicBlockCell (logCellStoppingAncestor A (n i)).1
        (logCellStoppingAncestor A (n i)).2 r)) = logCell (logCellStoppingAncestor A (n i)).2 :=
    sum_logCell_block (by positivity) (logCellStoppingAncestor A (n i)).2.pos
  rw [hs]
  field_simp [(logCell_pos (logCellStoppingAncestor A (n i)).2.pos).ne']

/-- The discarded all-level profile has exactly zero ordinary mean. -/
theorem integral_actualGeneratorTail (A : ℕ+) (n : ι → ℕ+) (c : ι → ℝ) :
    (∫ x, actualGeneratorTailProfile A n c x) = 0 := by
  change (∫ x, finiteLogCellProfile n c x - actualGeneratorHeadProfile A n c x) = 0
  rw [integral_sub (integrable_finiteLogCellProfile n c) (integrable_finiteLogCellProfile _ _),
    integral_actualGeneratorHead, sub_self]

/-- The discarded real profile realizes the exact orthogonal Hilbert tail. -/
theorem realSourceLp_actualGeneratorTail (A : ℕ+) (n : ι → ℕ+) (c : ι → ℝ) :
    realSourceLp (actualGeneratorTailProfile A n c) (actualGeneratorTailProfile_bv A n c)
        (actualGeneratorTailProfile_compact A n c) =
      U (finiteLogCellVector n c - P A (finiteLogCellVector n c)) := by
  rw [map_sub, ← realSourceLp_finiteLogCellProfile, ← realSourceLp_actualGeneratorHead]
  apply Lp.ext
  filter_upwards [realSourceLp_coeFn (actualGeneratorTailProfile A n c) _ _,
    realSourceLp_coeFn (finiteLogCellProfile n c) _ _,
    realSourceLp_coeFn (actualGeneratorHeadProfile A n c) _ _, Lp.coeFn_sub
      (realSourceLp (finiteLogCellProfile n c) _ _)
      (realSourceLp (actualGeneratorHeadProfile A n c) _ _)] with x ht hf hh hs
  rw [ht, hs, Pi.sub_apply, hf, hh]
  exact Complex.ofReal_sub _ _

private theorem inner_realSourceLp_eq_integral (f g : ℝ → ℝ)
    (hfv : BoundedVariationOn f univ) (hfc : HasCompactSupport f)
    (hgv : BoundedVariationOn g univ) (hgc : HasCompactSupport g) :
    inner ℂ (realSourceLp f hfv hfc) (realSourceLp g hgv hgc) =
      ((∫ x, f x * g x : ℝ) : ℂ) := by
  rw [L2.inner_def]
  calc
    _ = ∫ x, ((f x * g x : ℝ) : ℂ) := by
      apply integral_congr_ae
      filter_upwards [realSourceLp_coeFn f hfv hfc, realSourceLp_coeFn g hgv hgc] with x hf hg
      rw [hf, hg, RCLike.inner_apply, Complex.conj_ofReal, ← Complex.ofReal_mul, mul_comm]
    _ = _ := integral_complex_ofReal

/-- The head and discarded profile are orthogonal on the original real source space. -/
theorem integral_actualGeneratorHead_mul_tail (A : ℕ+) (n : ι → ℕ+) (c : ι → ℝ) :
    (∫ x, actualGeneratorHeadProfile A n c x * actualGeneratorTailProfile A n c x) = 0 := by
  have h := inner_realSourceLp_eq_integral (actualGeneratorHeadProfile A n c)
    (actualGeneratorTailProfile A n c) (actualGeneratorHeadProfile_bv A n c)
    (actualGeneratorHeadProfile_compact A n c) (actualGeneratorTailProfile_bv A n c)
    (actualGeneratorTailProfile_compact A n c)
  rw [realSourceLp_actualGeneratorHead, realSourceLp_actualGeneratorTail,
    ← wholeLineLogCellEmbedding.adjoint_inner_right, wholeLineLogCellEmbedding_adjoint_self,
    inner_logCellGeneratorHead_tail] at h
  exact Complex.ofReal_injective (by simpa only [Complex.ofReal_zero] using h.symm)

/-- The literal square mass splits into head and tail square masses. -/
theorem integral_finiteLogCellProfile_sq_split (A : ℕ+) (n : ι → ℕ+) (c : ι → ℝ) :
    (∫ x, finiteLogCellProfile n c x ^ 2) =
      (∫ x, actualGeneratorHeadProfile A n c x ^ 2) +
        ∫ x, actualGeneratorTailProfile A n c x ^ 2 := by
  have hh := memLp_compact_bv (actualGeneratorHeadProfile_bv A n c) (actualGeneratorHeadProfile_compact A n c)
  have ht := memLp_compact_bv (actualGeneratorTailProfile_bv A n c) (actualGeneratorTailProfile_compact A n c)
  have hht := hh.integrable_mul ht
  have he : (fun x => finiteLogCellProfile n c x ^ 2) = fun x =>
      (actualGeneratorHeadProfile A n c x ^ 2 +
        2 * (actualGeneratorHeadProfile A n c x * actualGeneratorTailProfile A n c x)) +
          actualGeneratorTailProfile A n c x ^ 2 := by
    funext x
    change _ = (_ + 2 * (_ * (finiteLogCellProfile n c x - actualGeneratorHeadProfile A n c x))) +
      (finiteLogCellProfile n c x - actualGeneratorHeadProfile A n c x) ^ 2
    ring
  rw [he, integral_add (hh.integrable_sq.add (hht.const_mul 2)) ht.integrable_sq,
    integral_add hh.integrable_sq (hht.const_mul 2), integral_const_mul,
    integral_actualGeneratorHead_mul_tail, mul_zero, add_zero]

/-- Both square-source centering corrections cancel on the actual all-level head and tail. -/
theorem actualGenerator_square_mixed_eq_centered (A : ℕ+) (n : ι → ℕ+) (c : ι → ℝ) :
    squarePrimeSource (finiteLogCellProfile n c) - squarePrimeSource (actualGeneratorHeadProfile A n c) -
        squarePrimeSource (actualGeneratorTailProfile A n c) =
      centeredSquarePrimeSource (finiteLogCellProfile n c) -
        centeredSquarePrimeSource (actualGeneratorHeadProfile A n c) -
          centeredSquarePrimeSource (actualGeneratorTailProfile A n c) := by
  simp only [centeredSquarePrimeSource, ← integral_actualGeneratorHead A n c,
    integral_finiteLogCellProfile_sq_split A n c, integral_actualGeneratorTail,
    zero_pow (by norm_num : 2 ≠ 0), mul_zero]
  ring

private theorem norm_realSourceLp_sq (f : ℝ → ℝ)
    (hv : BoundedVariationOn f univ) (hc : HasCompactSupport f) :
    ‖realSourceLp f hv hc‖ ^ 2 = ∫ x, f x ^ 2 := by
  have h := inner_realSourceLp_eq_integral f f hv hc hv hc
  rw [inner_self_eq_norm_sq_to_K] at h
  have he := congrArg Complex.re h
  simpa only [← Complex.ofReal_pow, Complex.ofReal_re, ← pow_two] using he

/-- Original Gamma controls the square mass of the literal discarded BV profile. -/
theorem integral_actualGeneratorTail_sq_le (A : ℕ+) (n : ι → ℕ+) (c : ι → ℝ) :
    (∫ x, actualGeneratorTailProfile A n c x ^ 2) ≤
      32 * levyEnergy (finiteLogCellProfile n c) / (1 + Real.log (A : ℝ)) := by
  have h := norm_physical_cell_component_sub_head_sq_le (finiteLogCellProfile n c)
    (finiteLogCellProfile_bv n c) (finiteLogCellProfile_compact n c) (A := (A : ℕ)) A.pos
  dsimp only at h
  rw [realSourceLp_finiteLogCellProfile, wholeLineLogCellEmbedding_adjoint_self, ← map_sub] at h
  rw [← norm_realSourceLp_sq _ (actualGeneratorTailProfile_bv A n c)
    (actualGeneratorTailProfile_compact A n c), realSourceLp_actualGeneratorTail]
  exact h

/-- Signed square compensation transfers to literal all-level profiles; the remaining Gamma costs stay explicit. -/
theorem exists_actualGenerator_square_mixed_bound {ε : ℝ} (hε : 0 < ε) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (A : ℕ+) (κ : Type) [Fintype κ] (n : κ → ℕ+) (c : κ → ℝ),
      |squarePrimeSource (finiteLogCellProfile n c) - squarePrimeSource (actualGeneratorHeadProfile A n c) -
          squarePrimeSource (actualGeneratorTailProfile A n c)| ≤
        ε * (levyEnergy (actualGeneratorHeadProfile A n c) +
          levyEnergy (actualGeneratorTailProfile A n c)) +
            C * (32 * levyEnergy (finiteLogCellProfile n c) / (1 + Real.log (A : ℝ))) := by
  obtain ⟨C, hC, hb⟩ := exists_centeredSquareSource_gamma_mass_bv hε
  refine ⟨C, hC, ?_⟩
  intro A κ _ n c
  rw [actualGenerator_square_mixed_eq_centered]
  have h := hb (actualGeneratorHeadProfile A n c) (actualGeneratorTailProfile A n c)
    (actualGeneratorHeadProfile_bv A n c) (actualGeneratorHeadProfile_compact A n c)
    (actualGeneratorTailProfile_bv A n c) (actualGeneratorTailProfile_compact A n c)
  have he : (fun x => actualGeneratorHeadProfile A n c x + actualGeneratorTailProfile A n c x) =
      finiteLogCellProfile n c := by
    funext x
    change actualGeneratorHeadProfile A n c x +
      (finiteLogCellProfile n c x - actualGeneratorHeadProfile A n c x) = _
    ring
  rw [he] at h
  exact h.trans (add_le_add le_rfl (mul_le_mul_of_nonneg_left (integral_actualGeneratorTail_sq_le A n c) hC))

end GaloisForLFunctions.SignedArithmeticHodgeTheory

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.realSourceLp_actualGeneratorHead
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.integral_actualGeneratorHead
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.integral_actualGeneratorTail

#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.actualGenerator_square_mixed_eq_centered
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.integral_actualGeneratorTail_sq_le
#print axioms GaloisForLFunctions.SignedArithmeticHodgeTheory.exists_actualGenerator_square_mixed_bound
