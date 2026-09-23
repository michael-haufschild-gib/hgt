import GaloisForLFunctions.RHTower.GibbsParityEnergyCovariance

/-!
# Signed covariance accumulation under prime insertion

A scalar recurrence of the form `ψ_{j+1} = α_j ψ_j - f_j` unrolls with the
future contraction product attached to every signed forcing term.  For the
squarefree Gibbs gas, `α_j` is the exact partition-mass contraction and
`f_j` is the exact parity--energy covariance integral across the prime-dilation
interval.

The accumulated forcing minus the baseline product has exactly the absolute
value of the endpoint.  Thus an estimate of that difference is an endpoint
estimate, not an independent source bound.  The module also proves the exact
retained-mass law when the forcing coefficient is `(1 - α_j) / 2` and the
order-gauge identity forced by a common endpoint.  Squaring only after signed
insertion gives a second exact law: normalized-current energy loses precisely
the nonnegative same-sign coherence across the dilation pair.
-/

namespace RHTower.GibbsGas

structure SignedRecurrenceStep where
  contraction : ℝ
  forcing : ℝ

def signedRecurrenceBaseline : List SignedRecurrenceStep → ℝ
  | [] => 1
  | step :: tail => step.contraction * signedRecurrenceBaseline tail

def signedRecurrenceAccumulation : List SignedRecurrenceStep → ℝ
  | [] => 0
  | step :: tail =>
      step.forcing * signedRecurrenceBaseline tail +
        signedRecurrenceAccumulation tail

def signedRecurrenceEndpoint (initial : ℝ) : List SignedRecurrenceStep → ℝ
  | [] => initial
  | step :: tail =>
      signedRecurrenceEndpoint (step.contraction * initial - step.forcing) tail

theorem signedRecurrenceEndpoint_eq (initial : ℝ) (steps : List SignedRecurrenceStep) :
    signedRecurrenceEndpoint initial steps =
      signedRecurrenceBaseline steps * initial -
        signedRecurrenceAccumulation steps := by
  induction steps generalizing initial with
  | nil => simp [signedRecurrenceEndpoint, signedRecurrenceBaseline,
      signedRecurrenceAccumulation]
  | cons step tail ih =>
      rw [signedRecurrenceEndpoint, ih]
      simp only [signedRecurrenceBaseline, signedRecurrenceAccumulation]
      ring

theorem abs_signedRecurrenceAccumulation_sub_baseline (steps : List SignedRecurrenceStep) :
    |signedRecurrenceAccumulation steps - signedRecurrenceBaseline steps| =
      |signedRecurrenceEndpoint 1 steps| := by
  rw [signedRecurrenceEndpoint_eq]
  simp only [mul_one]
  exact abs_sub_comm _ _

theorem signedRecurrence_accumulation_bound_iff
    (steps : List SignedRecurrenceStep) (η : ℝ) :
    |signedRecurrenceAccumulation steps - signedRecurrenceBaseline steps| ≤ η ↔
      |signedRecurrenceEndpoint 1 steps| ≤ η := by
  rw [abs_signedRecurrenceAccumulation_sub_baseline]

theorem signedRecurrenceAccumulation_sub_eq_of_endpoint_eq
    (steps₁ steps₂ : List SignedRecurrenceStep)
    (hendpoint : signedRecurrenceEndpoint 1 steps₁ =
      signedRecurrenceEndpoint 1 steps₂) :
    signedRecurrenceAccumulation steps₁ -
        signedRecurrenceAccumulation steps₂ =
      signedRecurrenceBaseline steps₁ - signedRecurrenceBaseline steps₂ := by
  rw [signedRecurrenceEndpoint_eq, signedRecurrenceEndpoint_eq] at hendpoint
  simp only [mul_one] at hendpoint
  linarith

noncomputable def signedRecurrenceRetainedMass : List ℝ → ℝ
  | [] => 0
  | contraction :: tail =>
      ((1 - contraction) / 2) * tail.prod +
        signedRecurrenceRetainedMass tail

theorem signedRecurrenceRetainedMass_eq (contractions : List ℝ) :
    signedRecurrenceRetainedMass contractions = (1 - contractions.prod) / 2 := by
  induction contractions with
  | nil => simp [signedRecurrenceRetainedMass]
  | cons contraction tail ih =>
      simp only [signedRecurrenceRetainedMass, List.prod_cons, ih]
      ring

noncomputable def gibbsContractionWeight (p : ℕ) (S : Finset ℕ) (x : ℝ) : ℝ :=
  (gibbsDiag S x 1 - gibbsDiag S ((p : ℝ) * x) 1) /
    (gibbsDiag S x 1 + gibbsDiag S ((p : ℝ) * x) 1)

noncomputable def gibbsForcingWeight (p : ℕ) (S : Finset ℕ) (x : ℝ) : ℝ :=
  gibbsDiag S ((p : ℝ) * x) 1 /
    (gibbsDiag S x 1 + gibbsDiag S ((p : ℝ) * x) 1)

theorem normalized_current_insert_covariance_recurrence
    (p : ℕ) (S : Finset ℕ) (hp : p ∉ S) (x : ℝ) :
    gibbsDiag (insert p S) x (-1) / gibbsDiag (insert p S) x 1 =
      gibbsContractionWeight p S x *
          (gibbsDiag S x (-1) / gibbsDiag S x 1) -
        gibbsForcingWeight p S x *
          (∫ t in x..(p : ℝ) * x, -gibbsParityEnergyCovariance S t) := by
  rw [integral_neg_covariance_eq_normalized_current_sub,
    gibbs_current_insert p S hp, gibbs_partition_insert p S hp]
  have hZx : gibbsDiag S x 1 ≠ 0 := ne_of_gt (gibbs_partition_pos S x)
  have hZpx : gibbsDiag S ((p : ℝ) * x) 1 ≠ 0 :=
    ne_of_gt (gibbs_partition_pos S ((p : ℝ) * x))
  have hZsum : gibbsDiag S x 1 + gibbsDiag S ((p : ℝ) * x) 1 ≠ 0 :=
    ne_of_gt (add_pos (gibbs_partition_pos S x)
      (gibbs_partition_pos S ((p : ℝ) * x)))
  unfold gibbsContractionWeight gibbsForcingWeight
  field_simp
  ring

theorem gibbsContractionWeight_eq_one_sub_two_mul_forcingWeight
    (p : ℕ) (S : Finset ℕ) (x : ℝ) :
    gibbsContractionWeight p S x = 1 - 2 * gibbsForcingWeight p S x := by
  have hZsum : gibbsDiag S x 1 + gibbsDiag S ((p : ℝ) * x) 1 ≠ 0 :=
    ne_of_gt (add_pos (gibbs_partition_pos S x)
      (gibbs_partition_pos S ((p : ℝ) * x)))
  unfold gibbsContractionWeight gibbsForcingWeight
  field_simp
  ring

theorem gibbs_recurrence_weights_mem_open_unit
    (p : ℕ) (S : Finset ℕ) (x : ℝ) (hp : 2 ≤ p) (hx : 0 < x) :
    0 < gibbsContractionWeight p S x ∧
      gibbsContractionWeight p S x < 1 ∧
      0 < gibbsForcingWeight p S x ∧
      gibbsForcingWeight p S x < 1 / 2 := by
  have hpReal : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
  have hxlt : x < (p : ℝ) * x := by nlinarith
  have hZlt := gibbs_partition_strict_anti S hxlt
  have hZx := gibbs_partition_pos S x
  have hZpx := gibbs_partition_pos S ((p : ℝ) * x)
  have hsum : 0 < gibbsDiag S x 1 + gibbsDiag S ((p : ℝ) * x) 1 := add_pos hZx hZpx
  constructor
  · exact div_pos (sub_pos.mpr hZlt) hsum
  constructor
  · unfold gibbsContractionWeight
    rw [div_lt_one hsum]
    linarith
  constructor
  · exact div_pos hZpx hsum
  · unfold gibbsForcingWeight
    rw [div_lt_iff₀ hsum]
    linarith

noncomputable def normalizedGibbsCurrent (S : Finset ℕ) (x : ℝ) : ℝ :=
  gibbsDiag S x (-1) / gibbsDiag S x 1

noncomputable def gibbsSignedRecurrenceStep
    (p : ℕ) (S : Finset ℕ) (x : ℝ) : SignedRecurrenceStep where
  contraction := gibbsContractionWeight p S x
  forcing := gibbsForcingWeight p S x *
    (∫ t in x..(p : ℝ) * x, -gibbsParityEnergyCovariance S t)

noncomputable def gibbsPrimeInsertionSteps
    (S : Finset ℕ) : List ℕ → ℝ → List SignedRecurrenceStep
  | [], _ => []
  | p :: tail, x =>
      gibbsSignedRecurrenceStep p S x ::
        gibbsPrimeInsertionSteps (insert p S) tail x

theorem normalizedGibbsCurrent_insert_recurrence
    (p : ℕ) (S : Finset ℕ) (hp : p ∉ S) (x : ℝ) :
    normalizedGibbsCurrent (insert p S) x =
      (gibbsSignedRecurrenceStep p S x).contraction *
          normalizedGibbsCurrent S x -
        (gibbsSignedRecurrenceStep p S x).forcing := by
  simpa only [normalizedGibbsCurrent, gibbsSignedRecurrenceStep] using
    normalized_current_insert_covariance_recurrence p S hp x

theorem normalizedGibbsCurrent_insert_list_eq_endpoint
    (S : Finset ℕ) (ps : List ℕ) (x : ℝ)
    (hps : ps.Nodup) (hdisjoint : ∀ p ∈ ps, p ∉ S) :
    normalizedGibbsCurrent (S ∪ ps.toFinset) x =
      signedRecurrenceEndpoint (normalizedGibbsCurrent S x)
        (gibbsPrimeInsertionSteps S ps x) := by
  induction ps generalizing S with
  | nil =>
      simp [gibbsPrimeInsertionSteps, signedRecurrenceEndpoint]
  | cons p tail ih =>
      have hpS : p ∉ S := hdisjoint p (by simp)
      have hpnmem : p ∉ tail := (List.nodup_cons.mp hps).1
      have htailNodup : tail.Nodup := (List.nodup_cons.mp hps).2
      have htailDisjoint : ∀ q ∈ tail, q ∉ insert p S := by
        intro q hq
        rw [Finset.mem_insert, not_or]
        constructor
        · intro hqp
          subst q
          exact hpnmem hq
        · exact hdisjoint q (by simp [hq])
      calc
        normalizedGibbsCurrent (S ∪ (p :: tail).toFinset) x =
            normalizedGibbsCurrent (insert p S ∪ tail.toFinset) x := by
              apply congrArg (fun U => normalizedGibbsCurrent U x)
              ext q
              simp
        _ = signedRecurrenceEndpoint (normalizedGibbsCurrent (insert p S) x)
              (gibbsPrimeInsertionSteps (insert p S) tail x) :=
            ih (insert p S) htailNodup htailDisjoint
        _ = signedRecurrenceEndpoint
              ((gibbsSignedRecurrenceStep p S x).contraction *
                  normalizedGibbsCurrent S x -
                (gibbsSignedRecurrenceStep p S x).forcing)
              (gibbsPrimeInsertionSteps (insert p S) tail x) := by
            rw [normalizedGibbsCurrent_insert_recurrence p S hpS x]
        _ = signedRecurrenceEndpoint (normalizedGibbsCurrent S x)
              (gibbsPrimeInsertionSteps S (p :: tail) x) := rfl

theorem normalizedGibbsCurrent_insert_list_eq_baseline_sub_accumulation
    (S : Finset ℕ) (ps : List ℕ) (x : ℝ)
    (hps : ps.Nodup) (hdisjoint : ∀ p ∈ ps, p ∉ S) :
    normalizedGibbsCurrent (S ∪ ps.toFinset) x =
      signedRecurrenceBaseline (gibbsPrimeInsertionSteps S ps x) *
          normalizedGibbsCurrent S x -
        signedRecurrenceAccumulation (gibbsPrimeInsertionSteps S ps x) := by
  rw [normalizedGibbsCurrent_insert_list_eq_endpoint S ps x hps hdisjoint,
    signedRecurrenceEndpoint_eq]

theorem normalizedGibbsCurrent_empty (x : ℝ) :
    normalizedGibbsCurrent ∅ x = 1 := by
  simp [normalizedGibbsCurrent, gibbsDiag_empty]

theorem normalizedGibbsCurrent_toFinset_eq_baseline_sub_accumulation
    (ps : List ℕ) (x : ℝ) (hps : ps.Nodup) :
    normalizedGibbsCurrent ps.toFinset x =
      signedRecurrenceBaseline (gibbsPrimeInsertionSteps ∅ ps x) -
        signedRecurrenceAccumulation (gibbsPrimeInsertionSteps ∅ ps x) := by
  simpa [normalizedGibbsCurrent_empty] using
    normalizedGibbsCurrent_insert_list_eq_baseline_sub_accumulation
      ∅ ps x hps (by simp)

theorem gibbsPrimeInsertion_accumulation_bound_iff_current_bound
    (ps : List ℕ) (x η : ℝ) (hps : ps.Nodup) :
    |signedRecurrenceAccumulation (gibbsPrimeInsertionSteps ∅ ps x) -
        signedRecurrenceBaseline (gibbsPrimeInsertionSteps ∅ ps x)| ≤ η ↔
      |normalizedGibbsCurrent ps.toFinset x| ≤ η := by
  rw [normalizedGibbsCurrent_toFinset_eq_baseline_sub_accumulation ps x hps]
  exact ⟨fun h => by simpa only [abs_sub_comm] using h,
    fun h => by simpa only [abs_sub_comm] using h⟩

theorem gibbsPrimeInsertion_order_gauge
    (ps qs : List ℕ) (x : ℝ) (hps : ps.Nodup) (hqs : qs.Nodup)
    (hset : ps.toFinset = qs.toFinset) :
    signedRecurrenceAccumulation (gibbsPrimeInsertionSteps ∅ ps x) -
        signedRecurrenceAccumulation (gibbsPrimeInsertionSteps ∅ qs x) =
      signedRecurrenceBaseline (gibbsPrimeInsertionSteps ∅ ps x) -
        signedRecurrenceBaseline (gibbsPrimeInsertionSteps ∅ qs x) := by
  have hpsEndpoint :
      signedRecurrenceEndpoint 1 (gibbsPrimeInsertionSteps ∅ ps x) =
        normalizedGibbsCurrent ps.toFinset x := by
    symm
    simpa [normalizedGibbsCurrent_empty] using
      normalizedGibbsCurrent_insert_list_eq_endpoint ∅ ps x hps (by simp)
  have hqsEndpoint :
      signedRecurrenceEndpoint 1 (gibbsPrimeInsertionSteps ∅ qs x) =
        normalizedGibbsCurrent qs.toFinset x := by
    symm
    simpa [normalizedGibbsCurrent_empty] using
      normalizedGibbsCurrent_insert_list_eq_endpoint ∅ qs x hqs (by simp)
  apply signedRecurrenceAccumulation_sub_eq_of_endpoint_eq
  rw [hpsEndpoint, hqsEndpoint, hset]

/-- The normalized-current quadratic energy, with one partition mass retained. -/
noncomputable def gibbsNormalizedCurrentEnergy (S : Finset ℕ) (x : ℝ) : ℝ :=
  gibbsDiag S x (-1) ^ (2 : ℕ) / gibbsDiag S x 1

/-- Positive loss created by same-sign coherence across one prime-dilation interval. -/
noncomputable def gibbsSameSignDissipation
    (p : ℕ) (S : Finset ℕ) (x : ℝ) : ℝ :=
  (gibbsDiag S x 1 * gibbsDiag S ((p : ℝ) * x) 1) /
      (gibbsDiag S x 1 + gibbsDiag S ((p : ℝ) * x) 1) *
    (normalizedGibbsCurrent S x +
      normalizedGibbsCurrent S ((p : ℝ) * x)) ^ (2 : ℕ)

/-- **Exact signed-energy polarization.**  Prime insertion loses precisely the positive
same-sign coherence between normalized currents at the two dilated couplings. -/
theorem gibbsNormalizedCurrentEnergy_insert_add_dissipation
    (p : ℕ) (S : Finset ℕ) (hp : p ∉ S) (x : ℝ) :
    gibbsNormalizedCurrentEnergy (insert p S) x +
        gibbsSameSignDissipation p S x =
      gibbsNormalizedCurrentEnergy S x +
        gibbsNormalizedCurrentEnergy S ((p : ℝ) * x) := by
  unfold gibbsNormalizedCurrentEnergy gibbsSameSignDissipation normalizedGibbsCurrent
  rw [gibbs_current_insert p S hp, gibbs_partition_insert p S hp]
  have hZx : gibbsDiag S x 1 ≠ 0 := ne_of_gt (gibbs_partition_pos S x)
  have hZpx : gibbsDiag S ((p : ℝ) * x) 1 ≠ 0 :=
    ne_of_gt (gibbs_partition_pos S ((p : ℝ) * x))
  have hZsum : gibbsDiag S x 1 + gibbsDiag S ((p : ℝ) * x) 1 ≠ 0 :=
    ne_of_gt (add_pos (gibbs_partition_pos S x)
      (gibbs_partition_pos S ((p : ℝ) * x)))
  field_simp
  ring

/-- Same-sign dilation coherence dissipates nonnegative normalized-current energy. -/
theorem gibbsSameSignDissipation_nonneg (p : ℕ) (S : Finset ℕ) (x : ℝ) :
    0 ≤ gibbsSameSignDissipation p S x := by
  unfold gibbsSameSignDissipation
  have hZx := (gibbs_partition_pos S x).le
  have hZpx := (gibbs_partition_pos S ((p : ℝ) * x)).le
  have hsum :=
    (add_pos (gibbs_partition_pos S x)
      (gibbs_partition_pos S ((p : ℝ) * x))).le
  exact mul_nonneg (div_nonneg (mul_nonneg hZx hZpx) hsum) (sq_nonneg _)

/-- Discarding the exact positive loss gives the unconditional two-scale energy ceiling. -/
theorem gibbsNormalizedCurrentEnergy_insert_le
    (p : ℕ) (S : Finset ℕ) (hp : p ∉ S) (x : ℝ) :
    gibbsNormalizedCurrentEnergy (insert p S) x ≤
      gibbsNormalizedCurrentEnergy S x +
        gibbsNormalizedCurrentEnergy S ((p : ℝ) * x) := by
  rw [← gibbsNormalizedCurrentEnergy_insert_add_dissipation p S hp x]
  exact le_add_of_nonneg_right (gibbsSameSignDissipation_nonneg p S x)

end RHTower.GibbsGas
