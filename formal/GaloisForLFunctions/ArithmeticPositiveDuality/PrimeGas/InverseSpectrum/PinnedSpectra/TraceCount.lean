import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.PinnedSpectra.Support
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.PinnedSpectra.Insertion
import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.MomentResponse.OperatorTrace

/-! # First occupation read from ordinary traces under quantum composition -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing

open Filter Topology ContinuousLinearMap

/-- Reciprocal root of the measured trace deficit at order (m+2). -/
def inverseTraceRoot (v : MissingWave) (m : ℕ) : ℝ :=
  (((riemannZeta ((m+2:ℕ):ℂ)).re-(opTrace (projected (omitLine v.val)^(2*(m+2)))).re) ^
    (ordinaryMomentOrder m).val⁻¹)⁻¹

/-- The limiting ordinary trace measurement of one fixed omission. -/
def traceCount (v : MissingWave) : ℝ := limUnder atTop (inverseTraceRoot v)

def LowestLabel (v : MissingWave) (n : ℕ+) : Prop := (∀ k < n, v.val k = 0) ∧ v.val n ≠ 0

private theorem lowest_number_iff (v : MissingWave) (j : ℕ) :
    LowestLabel v (number j) ↔ FirstOccupied v j := by
  apply and_congr_left
  intro _
  constructor
  · intro h k hk
    exact h (number k) (show k+1 < j+1 by omega)
  · intro h n hn
    obtain ⟨k,rfl⟩ := number_surjective n
    exact h k (by change k+1 < j+1 at hn; omega)

theorem exists_lowest_label (v : MissingWave) : ∃ n, LowestLabel v n := by
  obtain ⟨j,hj⟩ := physical_first_move (missingSpectrum_physical v)
  exact ⟨number j,(lowest_number_iff v j).mpr ((first_move_iff_first_occupied v j).mp hj)⟩

private theorem ordinary_orders_cofinal : Tendsto ordinaryMomentOrder atTop atTop := by
  refine tendsto_atTop.mpr fun q => ?_
  filter_upwards [eventually_ge_atTop ⌈q.val⌉₊] with m hm
  change q.val ≤ ((m+2:ℕ):ℝ)
  exact (Nat.le_ceil q.val).trans (Nat.cast_le.mpr (hm.trans (Nat.le_add_right m 2)))

/-- The reciprocal ordinary trace roots converge to the least occupied integer label. -/
theorem inverseTraceRoot_tendsto {v : MissingWave} {n : ℕ+} (hn : LowestLabel v n) :
    Tendsto (inverseTraceRoot v) atTop (𝓝 (n.val:ℝ)) := by
  obtain ⟨j,rfl⟩ := number_surjective n
  have hj := (first_move_iff_first_occupied v j).mpr ((lowest_number_iff v j).mp hn)
  have h := ((moment_root_tendsto_first_change (missingSpectrum v) j hj.1 hj.2).comp
    ordinary_orders_cofinal).inv₀ (occupationWeight_pos j).ne'
  have hd : MissingDimension (omitLine v.val) 1 := (missingDimension_one_iff _).mpr ⟨_,missingWave_ne_zero v,rfl⟩
  have hc := ((nonzero_line_conserves_iff _).mpr v.property).2
  have hr (m : ℕ) : inverseTraceRoot v m =
      ((momentLoss (ordinaryMomentOrder m) (missingSpectrum v))^(ordinaryMomentOrder m).val⁻¹)⁻¹ := by
    rw [inverseTraceRoot,missingSpectrum,momentLoss_ordinary_eq_operator_deficit _ hd hc]
  have hlabel : ((number j).val:ℝ) = (j:ℝ)+1 := by
    change ((j+1:ℕ):ℝ) = _
    rw [Nat.cast_add,Nat.cast_one]
  rw [show inverseTraceRoot v = _ from funext hr,hlabel]
  simpa only [Function.comp_apply,occupationWeight_eq,inv_inv] using h

theorem traceCount_eq_lowest {v : MissingWave} {n : ℕ+} (h : LowestLabel v n) : traceCount v = (n.val:ℝ) :=
  (inverseTraceRoot_tendsto h).limUnder_eq

theorem lowestLabel_insert (a : ℕ+) {v : MissingWave} {n : ℕ+} (hn : LowestLabel v n) :
    LowestLabel (insertMissing a v) (a*n) := by
  refine ⟨fun k hk => ?_,?_⟩
  · by_cases hm : k ∈ Set.range (insertLabels a)
    · obtain ⟨l,rfl⟩ := hm
      exact (insertWave_at a v.val l).trans (hn.1 l (Nat.lt_of_mul_lt_mul_left (show a.val*l.val < a.val*n.val from hk)))
    · exact insertWave_off a v.val k hm
  · exact (insertWave_at a v.val n).trans_ne hn.2

/-- Ordinary traces measure multiplication by the inserted label on every missing wave. -/
theorem traceCount_insert (a : ℕ+) (v : MissingWave) : traceCount (insertMissing a v) = (a.val:ℝ)*traceCount v := by
  obtain ⟨n,hn⟩ := exists_lowest_label v
  rw [traceCount_eq_lowest (lowestLabel_insert a hn),traceCount_eq_lowest hn]
  exact Nat.cast_mul a.val n.val

/-- The first occupied energy measured by ordinary traces increases by the Hamiltonian energy of the inserted label. -/
theorem traceCount_energy_insert (a : ℕ+) (v : MissingWave) :
    Real.log (traceCount (insertMissing a v)) = energy a+Real.log (traceCount v) := by
  obtain ⟨n,hn⟩ := exists_lowest_label v
  rw [traceCount_insert,traceCount_eq_lowest hn,Real.log_mul (Nat.cast_ne_zero.mpr a.ne_zero)
    (Nat.cast_ne_zero.mpr n.ne_zero),energy]

/-- The first occupied label squared times the fourth-trace loss is invariant under every insertion. -/
theorem scaled_fourth_loss_invariant (a : ℕ+) (v : MissingWave) :
    traceCount (insertMissing a v)^2*traceLoss (projected (omitLine (insertMissing a v).val)) =
      traceCount v^2*traceLoss (projected (omitLine v.val)) := by
  have hscale : (a.val:ℝ)^2*attenuation a^4 = 1 := by
    rw [attenuation,inv_pow,show (4:ℕ) = 2*2 from rfl,pow_mul,gain_sq,
      mul_inv_cancel₀ (pow_ne_zero _ (Nat.cast_ne_zero.mpr a.ne_zero))]
  rw [traceCount_insert,show (insertMissing a v).val = insertWave a v.val from rfl,fourth_loss_insert,mul_pow]
  calc _ = ((a.val:ℝ)^2*attenuation a^4)*(traceCount v^2*traceLoss (projected (omitLine v.val))) := by ring
       _ = _ := by rw [hscale,one_mul]

/-- Conservation of the Born-weighted trace count after one prime insertion selects precisely global split isometry. -/
theorem prime_insertion_count_conservation (p : Nat.Primes) (v : MissingWave) (s : ℂ) :
    let a : ℕ+ := ⟨(p:ℕ),p.property.pos⟩
    traceCount (insertMissing a v)*‖heat s a‖^2 = traceCount v ↔
      ∃ V : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, V f x = split s f x := by
  let a : ℕ+ := ⟨(p:ℕ),p.property.pos⟩
  change traceCount (insertMissing a v)*‖heat s a‖^2 = traceCount v ↔ _
  obtain ⟨n,hn⟩ := exists_lowest_label v
  have hpos : traceCount v ≠ 0 := (traceCount_eq_lowest hn).trans_ne (Nat.cast_ne_zero.mpr n.ne_zero)
  have he : energy a ≠ 0 := (Real.log_pos (show (1:ℝ) < (a.val:ℝ) by exact_mod_cast p.property.one_lt)).ne'
  rw [traceCount_insert,mul_right_comm,← shellMass_eq,split_isometric_iff]
  constructor
  · intro h
    have hm : shellMass s a = 1 := mul_right_cancel₀ hpos (h.trans (one_mul _).symm)
    have hz := ((Real.exp_eq_one_iff _).mp hm)
    have hhalf := (mul_eq_zero.mp hz).resolve_right he
    linarith only [hhalf]
  · intro h
    simp only [shellMass,h]
    norm_num

#print axioms exists_lowest_label
#print axioms inverseTraceRoot_tendsto
#print axioms traceCount_eq_lowest
#print axioms lowestLabel_insert
#print axioms traceCount_insert
#print axioms traceCount_energy_insert
#print axioms scaled_fourth_loss_invariant
#print axioms prime_insertion_count_conservation

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.InverseSpectrum.ShellMixing
