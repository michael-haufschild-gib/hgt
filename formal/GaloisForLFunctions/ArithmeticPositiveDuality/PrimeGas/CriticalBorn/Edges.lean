import GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn.Classification

/-! # Loss of probability at both ends of the elementary energy spectrum -/

noncomputable section

namespace GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn

open Filter Finset Real MeasureTheory
open GaloisForLFunctions.HTGeometry
open scoped Topology

/-- Probability of the lowest nonvacuum elementary excitation. -/
def lowestProbability (σ x : ℝ) := (2:ℝ)^(-(2*σ)) / powerMass (1-2*σ) x

/-- Probability carried by labels strictly above the fractional cutoff c. -/
def terminalProbability (σ c x : ℝ) := windowMass (1-2*σ) c x / powerMass (1-2*σ) x

private theorem mass_exponent (σ x : ℝ) : powerMass (1-2*σ) x = bornMass σ (cutoff x) := by
  simp only [powerMass,bornMass,bornWeight,show 1-2*σ-1 = -(2*σ) by ring]

/-- Born distribution on elementary labels before a phase is measured. -/
def labelLaw (σ x : ℝ) : ProbabilityMeasure ℕ :=
  ⟨(normalizedFiniteRealAtomicMeasure (primes (cutoff x)) id (bornWeight σ) : Measure ℕ),
    isProbabilityMeasure_normalizedFiniteRealAtomicMeasure _ _ _
      (fun p _ => Real.rpow_nonneg (Nat.cast_nonneg p) _)
      (show 0 < bornMass σ (cutoff x) from mass_exponent σ x ▸ powerMass_pos (1-2*σ) x)⟩

private theorem label_event (σ x : ℝ) (B : Set ℕ) [DecidablePred (fun p => p∈B)] :
    (labelLaw σ x : Measure ℕ).real B =
      (∑ p ∈ (primes (cutoff x)).filter (fun p => p∈B), bornWeight σ p)/powerMass (1-2*σ) x := by
  change (finiteRealAtomicMeasure (primes (cutoff x)) id
    (fun p => bornWeight σ p / bornMass σ (cutoff x)) : Measure ℕ).real B = _
  rw [real_finiteRealAtomicMeasure_apply (primes (cutoff x)) id
    (fun p => bornWeight σ p / bornMass σ (cutoff x))
    (fun p _ => div_nonneg (Real.rpow_nonneg (Nat.cast_nonneg p) _)
      (mass_exponent σ x ▸ (powerMass_pos (1-2*σ) x).le)) (Set.to_countable B).measurableSet,
    ←Finset.sum_div,mass_exponent]
  apply congrArg (fun v : ℝ => v / bornMass σ (cutoff x))
  apply sum_congr _ (fun _ _ => rfl)
  ext p
  simp only [mem_filter,id_eq]

/-- A lower energy cutoff measures the ratio of the two elementary masses. -/
theorem initial_measured (σ : ℝ) {x y : ℝ} (hy : 2≤y) (hyx : y≤x) :
    (labelLaw σ x : Measure ℕ).real {p : ℕ | (p:ℝ)≤y} =
      powerMass (1-2*σ) y / powerMass (1-2*σ) x := by
  classical
  rw [label_event]
  have filt : (primes (cutoff x)).filter (fun p : ℕ => p∈{q : ℕ | (q:ℝ)≤y}) =
      primes (cutoff y) := by
    ext p
    simp only [mem_filter,mem_cutoff (hy.trans hyx),mem_cutoff hy,Set.mem_setOf_eq]
    exact ⟨fun h => ⟨h.1.1,h.2⟩,fun h => ⟨⟨h.1,h.2.trans hyx⟩,h.2⟩⟩
  rw [filt]
  simp only [powerMass,bornWeight,show 1-2*σ-1 = -(2*σ) by ring]

theorem lowest_measured (σ x : ℝ) :
    (labelLaw σ x : Measure ℕ).real {2} = lowestProbability σ x := by
  classical
  rw [label_event]
  have two : 2 ∈ primes (cutoff x) := Nat.mem_primesBelow.mpr ⟨by omega,Nat.prime_two⟩
  have filt : (primes (cutoff x)).filter (fun p => p∈({2}:Set ℕ)) = {2} := by
    ext p
    simp only [mem_filter,Set.mem_singleton_iff,Finset.mem_singleton]
    exact ⟨And.right,fun h => ⟨h ▸ two,h⟩⟩
  rw [filt,sum_singleton]
  rfl

theorem terminal_measured {c x : ℝ} (hx : 2≤x) (hcx : 2≤c*x) (σ : ℝ) :
    (labelLaw σ x : Measure ℕ).real {p : ℕ | c*x < p} = terminalProbability σ c x := by
  classical
  rw [label_event]
  have filt : (primes (cutoff x)).filter (fun p => p∈{q : ℕ | c*x < q}) = window c x := by
    ext p
    rw [Finset.mem_filter,mem_cutoff hx,mem_window hx hcx]
    exact ⟨fun h => ⟨h.1.1,h.2,h.1.2⟩,fun h => ⟨⟨h.1,h.2.2⟩,h.2.1⟩⟩
  rw [filt]
  simp only [terminalProbability,windowMass,bornWeight,show 1-2*σ-1 = -(2*σ) by ring]

private theorem harmonic_mass (x : ℝ) : powerMass 0 x = mass (cutoff x) := by
  simp only [powerMass,mass,weight,zero_sub,rpow_neg_one]

private theorem harmonic_growth : Tendsto (powerMass 0) atTop atTop := by
  exact (mass_diverges.comp cutoff_atTop).congr (fun x => (harmonic_mass x).symm)

private theorem harmonic_window_bound {c x : ℝ} (hc : 0<c) (hx : 2≤x) (hcx : 2≤c*x) :
    windowMass 0 c x ≤ 2/c := by
  have xp : 0<x := by linarith only [hx]
  have sub : window c x ⊆ range (⌊x⌋₊+1) := by
    intro p hp
    exact mem_range.mpr (Nat.lt_succ_of_le ((Nat.le_floor_iff xp.le).mpr ((mem_window hx hcx).mp hp).2.2))
  have card : ((window c x).card:ℝ) ≤ x+1 := by
    have hn := Finset.card_le_card sub
    rw [card_range] at hn
    calc
      _ ≤ (⌊x⌋₊:ℝ)+1 := by exact_mod_cast hn
      _ ≤ _ := by linarith only [Nat.floor_le xp.le]
  calc
    windowMass 0 c x ≤ ∑ p ∈ window c x, (c*x)⁻¹ := by
      simp only [windowMass,zero_sub,rpow_neg_one]
      apply sum_le_sum
      intro p hp
      exact inv_anti₀ (mul_pos hc xp) ((mem_window hx hcx).mp hp).2.1.le
    _ = ((window c x).card:ℝ)*(c*x)⁻¹ := by rw [sum_const,nsmul_eq_mul]
    _ ≤ (x+1)*(c*x)⁻¹ := mul_le_mul_of_nonneg_right card (inv_nonneg.mpr (mul_pos hc xp).le)
    _ ≤ 2/c := by
      rw [←div_eq_mul_inv,div_le_div_iff₀ (mul_pos hc xp) hc]
      nlinarith only [mul_nonneg (sub_nonneg.mpr (show 1≤x by linarith only [hx])) hc.le]

/-- Every fixed terminal energy width loses its probability at criticality. -/
theorem critical_terminal {c : ℝ} (hc : 0<c) :
    Tendsto (terminalProbability (1/2) c) atTop (𝓝 0) := by
  have upper := harmonic_growth.const_div_atTop (2/c)
  have cX := _root_.RHTower.tendsto_const_mul_atTop_of_pos hc
  apply tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds upper
  · exact Eventually.of_forall fun x => div_nonneg
      (sum_nonneg fun p _ => rpow_nonneg (Nat.cast_nonneg p) _) (powerMass_pos _ x).le
  · filter_upwards [eventually_ge_atTop (2:ℝ),cX.eventually_ge_atTop 2] with x hx hcx
    simp only [terminalProbability,show (1:ℝ)-2*(1/2)=0 by norm_num]
    exact div_le_div_of_nonneg_right (harmonic_window_bound hc hx hcx) (powerMass_pos _ x).le

/-- Every fixed initial packet loses its probability. For sufficiently
large x the numerator is the mass of a subset of the sampled packet. -/
theorem critical_initial (y : ℝ) : Tendsto (fun x => powerMass 0 y / powerMass 0 x)
    atTop (𝓝 0) := harmonic_growth.const_div_atTop _

theorem critical_lowest : Tendsto (lowestProbability (1/2)) atTop (𝓝 0) := by
  change Tendsto (fun x => (2:ℝ)^(-(2*(1/2:ℝ))) / powerMass (1-2*(1/2)) x) _ _
  rw [show (1:ℝ)-2*(1/2)=0 by norm_num]
  exact harmonic_growth.const_div_atTop _

private theorem supercritical_lowest {σ : ℝ} (hσ : 1/2<σ) :
    ¬ Tendsto (lowestProbability σ) atTop (𝓝 0) := by
  let f := fun n : ℕ => (n:ℝ)^(-(2*σ))
  have summable : Summable f := Real.summable_nat_rpow.mpr (by linarith only [hσ])
  have bound (x : ℝ) : powerMass (1-2*σ) x ≤ ∑' n, f n := by
    simp only [powerMass,show 1-2*σ-1 = -(2*σ) by ring]
    exact summable.sum_le_tsum _ fun n _ => rpow_nonneg (Nat.cast_nonneg _) _
  have positive := (powerMass_pos (1-2*σ) 2).trans_le (bound 2)
  have w : 0<(2:ℝ)^(-(2*σ)) := rpow_pos_of_pos (by norm_num) _
  intro h
  have lim := ge_of_tendsto h (Eventually.of_forall fun x =>
    div_le_div_of_nonneg_left w.le (powerMass_pos (1-2*σ) x) (bound x))
  exact (div_pos w positive).not_ge lim

private theorem subcritical_terminal {σ c : ℝ} (hσ : σ<1/2) (hc : 0<c) (hc' : c<1) :
    ¬Tendsto (terminalProbability σ c) atTop (𝓝 0) := by
  obtain ⟨d,hd,share⟩ := positive_window_share (by linarith only [hσ] : 0<1-2*σ) hc hc'
  intro h
  have lim := ge_of_tendsto h (share.mono fun x hx => (le_div_iff₀ (powerMass_pos _ x)).mpr hx)
  exact hd.not_ge lim

/-- Two occupation counts, the lowest excitation and the last fixed-width
energy interval, detect the critical exponent without reading any phase. -/
theorem two_edge_iff (σ : ℝ) {c : ℝ} (hc : 0<c) (hc' : c<1) :
    (Tendsto (lowestProbability σ) atTop (𝓝 0) ∧
      Tendsto (terminalProbability σ c) atTop (𝓝 0)) ↔ σ=1/2 := by
  constructor
  · rintro ⟨lo,hi⟩
    exact le_antisymm (not_lt.mp (fun h => supercritical_lowest h lo))
      (not_lt.mp (fun h => subcritical_terminal h hc hc' hi))
  · rintro rfl
    exact ⟨critical_lowest,critical_terminal hc⟩

/-- The bottom prime and the top octave detect isometric divisor splitting. -/
theorem two_edges_iff_split (s : ℂ) :
    (Tendsto (lowestProbability s.re) atTop (𝓝 0) ∧
      Tendsto (terminalProbability s.re (1/2)) atTop (𝓝 0)) ↔
    ∃ T : Gas →ₗᵢ[ℂ] PairGas, ∀ f x, T f x = split s f x :=
  (two_edge_iff s.re (by norm_num) (by norm_num)).trans (split_isometric_iff s).symm

#print axioms lowest_measured
#print axioms initial_measured
#print axioms terminal_measured
#print axioms critical_terminal
#print axioms critical_initial
#print axioms critical_lowest
#print axioms two_edge_iff
#print axioms two_edges_iff_split

end GaloisForLFunctions.ArithmeticPositiveDuality.PrimeGas.CriticalBorn
