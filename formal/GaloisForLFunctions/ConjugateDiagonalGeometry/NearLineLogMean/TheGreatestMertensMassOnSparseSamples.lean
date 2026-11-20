import GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean.ThePowerSpectrumOfReciprocalMertensMass

/-!
# Largest reciprocal Mertens mass available at a given sample size

Samples may be selected arbitrarily far out on the positive integers.
Their maximal mass at cardinality m has exponent Θ, already attained
by the first m indices. Thus the cardinality exponent continues to
detect the zero abscissa when the locations of the samples are free.
-/
noncomputable section
open Finset Filter Topology
open _root_.RHTower GaloisForLFunctions.ArithmeticPowerMass
namespace GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean

private theorem weight_le_one (k : ℕ) : reciprocalMertensWeight k ≤ 1 := by
  cases k with
  | zero => simp [reciprocalMertensWeight]
  | succ k =>
    rw [reciprocalMertensWeight,div_le_one (Nat.cast_pos.mpr (Nat.succ_pos k)),
      norm_mobiusMertensPartialSum_eq_abs_shiftedMertensReal]
    exact abs_shiftedMertensReal_le _

/-- Only cardinality enters the bound. In particular the largest
sampled index may grow arbitrarily fast compared with the budget. -/
theorem sparse_mertens_mass_bound {v : ℝ} (hv : zetaZeroAbscissa < v) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ S : Finset ℕ,
      ∑ k ∈ S, reciprocalMertensWeight k ≤ C*((S.card:ℝ)+1)^v := by
  have hv0 := ((by norm_num : (0:ℝ) < 1/2).trans_le half_le_zetaZeroAbscissa).trans hv
  by_cases h1 : 1 ≤ v
  · refine ⟨1,zero_le_one,fun S => ?_⟩
    have h := sum_le_sum (s:=S) (fun k _ => weight_le_one k)
    simp only [sum_const,nsmul_eq_mul,mul_one] at h
    have hx : 1 ≤ (S.card:ℝ)+1 := le_add_of_nonneg_left (Nat.cast_nonneg _)
    rw [one_mul]
    exact h.trans ((le_add_of_nonneg_right zero_le_one).trans
      ((Real.rpow_one _).symm.le.trans (Real.rpow_le_rpow_of_exponent_le hx h1)))
  obtain ⟨A,hA,hM⟩ := mobiusMertens_subpower_zetaZeroAbscissa (v-zetaZeroAbscissa) (sub_pos.mpr hv)
  rw [show zetaZeroAbscissa+(v-zetaZeroAbscissa)=v by ring] at hM
  have row (k : ℕ) : reciprocalMertensWeight k ≤ (2*A)*((k:ℝ)+1)^(v-1) := by
    cases k with
    | zero => simp [reciprocalMertensWeight,hA]
    | succ k =>
      let x : ℝ := (k+1:ℕ)
      have hx : 1 ≤ x := Nat.one_le_cast.mpr (Nat.succ_pos k)
      have hp : 0 < x := zero_lt_one.trans_le hx
      have hp1 : 0 < x+1 := by positivity
      have hcap : x+1 ≤ 2*x := by linarith only [hx]
      have hfactor := mul_le_mul_of_nonneg_left hcap (mul_nonneg hA (Real.rpow_nonneg hp1.le (v-1)))
      change ‖mobiusMertensPartialSum (k+1)‖/x ≤ (2*A)*(x+1)^(v-1)
      apply (div_le_iff₀ hp).mpr
      refine (hM (k+1)).trans ?_
      change A*(x+1)^v ≤ _
      calc _ = (A*(x+1)^(v-1))*(x+1) := by rw [Real.rpow_sub_one hp1.ne']; field_simp
           _ ≤ _ := hfactor.trans_eq (by ring)
  let e : ℕ ↪ ℕ := ⟨Nat.succ, Nat.succ_injective⟩
  refine ⟨2*A*(1+1/v),by positivity,fun S => ?_⟩
  have hpack := packed_power hv0 (lt_of_not_ge h1).le (S.map e) (by
    intro n hn; obtain ⟨k,_,rfl⟩ := mem_map.mp hn; exact Nat.succ_pos k)
  simp only [sum_map,card_map] at hpack
  change (∑ k ∈ S,((k.succ:ℕ):ℝ)^(v-1)) ≤ _ at hpack
  simp only [Nat.cast_succ] at hpack
  have hh := sum_le_sum (s:=S) (fun k _ => row k)
  rw [←mul_sum] at hh
  exact hh.trans ((mul_le_mul_of_nonneg_left hpack (by positivity : 0 ≤ 2*A)).trans_eq (by ring))

/-- Supremum of all sampled masses, with no ceiling on the indices. -/
def sparseMertensMass (m : ℕ) : ℝ :=
  sSup {x : ℝ | ∃ S : Finset ℕ, S.card ≤ m ∧ (∑ k ∈ S,reciprocalMertensWeight k) = x}

private theorem sample_member (m : ℕ) :
    (0:ℝ) ∈ {x : ℝ | ∃ S : Finset ℕ, S.card ≤ m ∧ (∑ k ∈ S,reciprocalMertensWeight k) = x} :=
  ⟨∅,by simp,by simp⟩

private theorem sample_bounded (m : ℕ) :
    BddAbove {x : ℝ | ∃ S : Finset ℕ, S.card ≤ m ∧ (∑ k ∈ S,reciprocalMertensWeight k) = x} := by
  refine ⟨(m:ℝ),?_⟩
  rintro _ ⟨S,hS,rfl⟩
  have h := sum_le_sum (s:=S) (fun k _ => weight_le_one k)
  simp only [sum_const,nsmul_eq_mul,mul_one] at h
  exact h.trans (Nat.cast_le.mpr hS)

/-- The initial segment realizes the lower comparison for every
budget, even when a more distant sample has strictly larger mass. -/
theorem prefix_mass_le_sparse_mertens_mass (m : ℕ) : mertensAbelMass m ≤ sparseMertensMass m := by
  apply le_csSup (sample_bounded m)
  refine ⟨Icc 1 m,by simp [Nat.card_Icc],?_⟩
  exact (mertens_abel_mass_eq m).symm

/-- The best mass obtainable at m unrestricted locations has ordinary
logarithmic order Θ, equal to that of the first m locations. -/
theorem sparse_mertens_mass_log_order :
    Tendsto (fun m : ℕ => Real.log (1+sparseMertensMass m)/Real.log ((m:ℝ)+1))
      atTop (𝓝 zetaZeroAbscissa) := by
  apply log_order_of_power_envelope ((by norm_num : (0:ℝ)<1/2).trans_le half_le_zetaZeroAbscissa)
    (fun m => le_csSup (sample_bounded m) (sample_member m))
  · intro b hb hbΘ
    filter_upwards [eventually_large_mertens_abel_mass hb hbΘ 1] with m h
    rw [one_mul] at h
    exact h.trans_le (prefix_mass_le_sparse_mertens_mass m)
  · intro v hv
    obtain ⟨C,hC,h⟩ := sparse_mertens_mass_bound hv
    refine ⟨C,hC,fun m => csSup_le ⟨0,sample_member m⟩ ?_⟩
    rintro _ ⟨S,hm,rfl⟩
    exact (h S).trans (mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
      (add_le_add_right (Nat.cast_le.mpr hm) 1)
      ((by norm_num : (0:ℝ) ≤ 1/2).trans (half_le_zetaZeroAbscissa.trans hv.le))) hC)

/-- Square-root growth on arbitrary samples, measured purely by
their cardinality, characterizes the critical-line configuration. -/
theorem rh_iff_cardinality_bound_for_every_mertens_sample :
    RiemannHypothesis ↔ ∀ ε : ℝ, 0 < ε → ∃ C : ℝ, 0 ≤ C ∧ ∀ S : Finset ℕ,
      ∑ k ∈ S,reciprocalMertensWeight k ≤ C*((S.card:ℝ)+1)^(1/2+ε) := by
  rw [←zetaZeroAbscissa_eq_half_iff_riemannHypothesis]
  constructor
  · intro h ε hε; exact sparse_mertens_mass_bound (by linarith only [h,hε])
  · intro h
    apply le_antisymm _ half_le_zetaZeroAbscissa
    by_contra! hw
    obtain ⟨b,hb,hb'⟩ := exists_between hw
    obtain ⟨C,_,hc⟩ := h (b-1/2) (sub_pos.mpr hb)
    obtain ⟨m,hm⟩ := (eventually_large_mertens_abel_mass
      ((by norm_num : (0:ℝ) ≤ 1/2).trans hb.le) hb' C).exists
    have hz := hc (Icc 1 m)
    simp only [show (1/2:ℝ)+(b-1/2)=b by ring,Nat.card_Icc,Nat.add_sub_cancel] at hz
    rw [mertens_abel_mass_eq] at hm
    exact hm.not_ge hz

#print axioms sparse_mertens_mass_bound
#print axioms sparse_mertens_mass_log_order
#print axioms rh_iff_cardinality_bound_for_every_mertens_sample
end GaloisForLFunctions.ConjugateDiagonalGeometry.NearLineLogMean
