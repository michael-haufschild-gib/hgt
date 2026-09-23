import GaloisForLFunctions.HTGeometry.ComponentSpectralFormFactorProduct
import GaloisForLFunctions.HTGeometry.ReplicaCrowdingCentralLimitFloor
import GaloisForLFunctions.HTGeometry.EndpointChirpGlue

/-!
# The large-dimension limit of the component collision coefficients

The collision coefficient `a_{d,m}` is the average multinomial coefficient of the histogram of a
uniform random tuple.  Every multinomial coefficient of total mass `m` is at most `m!`, with
equality exactly on injective tuples, so `a_{d,m}` is squeezed between `m! (d-m)^m/d^m` and `m!`.
Hence `a_{d,m} → m!` for every fixed replica order, and a fixed number of components gives the
product limit `(m!)^c`.
-/

open scoped BigOperators

namespace GaloisForLFunctions.HTGeometry

noncomputable section

variable {X : Type*} [Fintype X] [DecidableEq X]

/-! ## The collision count as an average multinomial coefficient -/

theorem histogramCollisionCount_eq_sum_multinomial (m : ℕ) :
    histogramCollisionCount X m
      = ∑ f : Fin m → X, (Nat.multinomial Finset.univ (tupleHistogram f) : ℝ) := by
  classical
  rw [histogramCollisionCount_eq_sum_tuple]
  refine Finset.sum_congr rfl fun f _ => ?_
  rw [Finset.sum_boole]
  have hfilter : (Finset.univ.filter fun g : Fin m → X => tupleHistogram f = tupleHistogram g)
      = Finset.univ.filter fun g : Fin m → X => tupleHistogram g = tupleHistogram f := by
    ext g
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, eq_comm]
  rw [hfilter, card_tupleHistogram_fiber m (tupleHistogram f) (sum_tupleHistogram f)]

/-! ## The two-sided bound -/

theorem histogramCollisionCount_nonneg (m : ℕ) : 0 ≤ histogramCollisionCount X m :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem histogramCollisionCount_le (m : ℕ) :
    histogramCollisionCount X m ≤ (m.factorial : ℝ) * (Fintype.card X : ℝ) ^ m := by
  classical
  rw [histogramCollisionCount_eq_sum_multinomial]
  calc ∑ f : Fin m → X, (Nat.multinomial Finset.univ (tupleHistogram f) : ℝ)
      ≤ ∑ _f : Fin m → X, (m.factorial : ℝ) :=
        Finset.sum_le_sum fun f _ => by
          exact_mod_cast multinomial_le_factorial (sum_tupleHistogram f)
    _ = (m.factorial : ℝ) * (Fintype.card X : ℝ) ^ m := by
        rw [Finset.sum_const, nsmul_eq_mul, Finset.card_univ, Fintype.card_fun, Fintype.card_fin]
        push_cast
        ring

theorem multinomial_tupleHistogram_of_injective {m : ℕ} {f : Fin m → X}
    (hf : Function.Injective f) :
    Nat.multinomial Finset.univ (tupleHistogram f) = m.factorial := by
  classical
  have hle : ∀ i, tupleHistogram f i ≤ 1 := by
    intro i
    rw [tupleHistogram]
    refine Finset.card_le_one.mpr fun a ha b hb => ?_
    rw [Finset.mem_filter] at ha hb
    exact hf (ha.2.trans hb.2.symm)
  have hprod : ∏ i, (tupleHistogram f i).factorial = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    rcases Nat.lt_or_ge (tupleHistogram f i) 1 with h | h
    · rw [Nat.lt_one_iff.mp h]
      rfl
    · rw [le_antisymm (hle i) h]
      rfl
  have hspec := Nat.multinomial_spec (Finset.univ : Finset X) (tupleHistogram f)
  rw [hprod, one_mul, sum_tupleHistogram] at hspec
  exact hspec

theorem card_injective_filter (m : ℕ) :
    (Finset.univ.filter fun f : Fin m → X => Function.Injective f).card
      = (Fintype.card X).descFactorial m := by
  classical
  rw [← Fintype.card_subtype, Fintype.card_congr (Equiv.subtypeInjectiveEquivEmbedding (Fin m) X),
    Fintype.card_embedding_eq, Fintype.card_fin]

theorem le_histogramCollisionCount (m : ℕ) :
    (m.factorial : ℝ) * ((Fintype.card X).descFactorial m : ℝ) ≤ histogramCollisionCount X m := by
  classical
  rw [histogramCollisionCount_eq_sum_multinomial]
  have hstep : (m.factorial : ℝ) * ((Fintype.card X).descFactorial m : ℝ)
      = ∑ f ∈ Finset.univ.filter fun f : Fin m → X => Function.Injective f,
          (Nat.multinomial Finset.univ (tupleHistogram f) : ℝ) := by
    rw [Finset.sum_congr rfl fun f hf => by
      rw [multinomial_tupleHistogram_of_injective (Finset.mem_filter.mp hf).2]]
    rw [Finset.sum_const, nsmul_eq_mul, card_injective_filter]
    ring
  rw [hstep]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
    fun f _ _ => Nat.cast_nonneg _

/-! ## The dimension asymptotics -/

theorem pow_sub_le_descFactorial_componentFormFactorExponentialLimit (d : ℕ) : ∀ m : ℕ, (d - m) ^ m ≤ d.descFactorial m
  | 0 => by simp
  | (m + 1) => by
      rw [Nat.descFactorial_succ]
      calc (d - (m + 1)) ^ (m + 1) = (d - (m + 1)) * (d - (m + 1)) ^ m := by ring
        _ ≤ (d - m) * (d - m) ^ m :=
            Nat.mul_le_mul (by omega) (Nat.pow_le_pow_left (by omega) m)
        _ ≤ (d - m) * d.descFactorial m :=
            Nat.mul_le_mul_left _ (pow_sub_le_descFactorial_componentFormFactorExponentialLimit d m)

/-- The collision coefficient of a `d`-dimensional component. -/
def replicaFormFactorCoeff (d m : ℕ) : ℝ := replicaFormFactorCoefficient (Fin d) m

theorem replicaFormFactorCoeff_le (d m : ℕ) : replicaFormFactorCoeff d m ≤ (m.factorial : ℝ) := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [replicaFormFactorCoeff, replicaFormFactorCoefficient, histogramCollisionCount]
    · have hmne : m ≠ 0 := by omega
      have hzero : ((Fintype.card (Fin 0) : ℝ)) ^ m = 0 := by simp [hmne]
      rw [replicaFormFactorCoeff, replicaFormFactorCoefficient, hzero, div_zero]
      exact Nat.cast_nonneg _
  · have hpos : (0 : ℝ) < (Fintype.card (Fin d) : ℝ) ^ m := by
      rw [Fintype.card_fin]
      exact pow_pos (by exact_mod_cast hd) m
    rw [replicaFormFactorCoeff, replicaFormFactorCoefficient, div_le_iff₀ hpos]
    exact histogramCollisionCount_le m

theorem le_replicaFormFactorCoeff (d m : ℕ) :
    (m.factorial : ℝ) * ((d.descFactorial m : ℝ) / (d : ℝ) ^ m) ≤ replicaFormFactorCoeff d m := by
  rcases Nat.eq_zero_or_pos d with rfl | hd
  · rcases Nat.eq_zero_or_pos m with rfl | hm
    · simp [replicaFormFactorCoeff, replicaFormFactorCoefficient, histogramCollisionCount]
    · have hmne : m ≠ 0 := by omega
      have hzero : ((0 : ℕ) : ℝ) ^ m = 0 := by simp [hmne]
      rw [hzero, div_zero, mul_zero, replicaFormFactorCoeff, replicaFormFactorCoefficient]
      exact div_nonneg (histogramCollisionCount_nonneg m) (by positivity)
  · have hpos : (0 : ℝ) < (d : ℝ) ^ m := pow_pos (by exact_mod_cast hd) m
    rw [replicaFormFactorCoeff, replicaFormFactorCoefficient, Fintype.card_fin,
      le_div_iff₀ hpos, mul_assoc, div_mul_cancel₀ _ (ne_of_gt hpos)]
    have := le_histogramCollisionCount (X := Fin d) m
    rwa [Fintype.card_fin] at this

/-- The descending-factorial ratio tends to one, in real form. -/
theorem tendsto_natDescFactorial_div_pow (m : ℕ) :
    Filter.Tendsto (fun d : ℕ => (d.descFactorial m : ℝ) / (d : ℝ) ^ m) Filter.atTop (nhds 1) := by
  have h := tendsto_descFactorial_div_pow_endpointChirpGlue 0 m
  have hre := (Complex.continuous_re.tendsto (1 : ℂ)).comp h
  simp only [Function.comp_def, Complex.one_re] at hre
  refine hre.congr fun d => ?_
  have hcast : (((d + 0).descFactorial m : ℕ) : ℂ) / ((d : ℂ) ^ m)
      = (((d.descFactorial m : ℝ) / (d : ℝ) ^ m : ℝ) : ℂ) := by
    rw [Nat.add_zero]
    push_cast
    ring
  rw [hcast, Complex.ofReal_re]

/-- **The component collision coefficient tends to `m!`.** -/
theorem tendsto_replicaFormFactorCoeff (m : ℕ) :
    Filter.Tendsto (fun d : ℕ => replicaFormFactorCoeff d m) Filter.atTop
      (nhds (m.factorial : ℝ)) := by
  have hlow : Filter.Tendsto
      (fun d : ℕ => (m.factorial : ℝ) * ((d.descFactorial m : ℝ) / (d : ℝ) ^ m))
      Filter.atTop (nhds (m.factorial : ℝ)) := by
    simpa using (tendsto_natDescFactorial_div_pow m).const_mul (m.factorial : ℝ)
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds
    (Filter.Eventually.of_forall fun d => le_replicaFormFactorCoeff d m)
    (Filter.Eventually.of_forall fun d => replicaFormFactorCoeff_le d m)

/-- **Fixed-component product-exponential limit `(12)`.**  With a fixed number of components whose
dimensions all grow, the completed form-factor moment tends to `(m!)^c`. -/
theorem tendsto_prod_replicaFormFactorCoeff {c : ℕ} (D : Fin c → ℕ → ℕ)
    (hD : ∀ r, Filter.Tendsto (D r) Filter.atTop Filter.atTop) (m : ℕ) :
    Filter.Tendsto (fun n => ∏ r, replicaFormFactorCoeff (D r n) m) Filter.atTop
      (nhds ((m.factorial : ℝ) ^ c)) := by
  have hfac : ∀ r : Fin c, Filter.Tendsto (fun n => replicaFormFactorCoeff (D r n) m)
      Filter.atTop (nhds (m.factorial : ℝ)) :=
    fun r => (tendsto_replicaFormFactorCoeff m).comp (hD r)
  have h := tendsto_finsetProd (Finset.univ : Finset (Fin c))
    (f := fun r n => replicaFormFactorCoeff (D r n) m)
    (a := fun _ => (m.factorial : ℝ)) fun r _ => hfac r
  simpa using h

end

end GaloisForLFunctions.HTGeometry
